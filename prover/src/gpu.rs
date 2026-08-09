//! `[PROVER-fri-wgsl]` — wgpu dispatch of the bundled native FRI fold kernel
//! (`shaders/fri_fold.wgsl`).
//!
//! This is UNVERIFIED COMPUTE. The WGSL selects a concrete Montgomery BabyBear
//! representation, `X^4 = 11` quotient, halve/beta/twiddle formula, and
//! bit-reversed layout modeled after a breadstuffs experiment. No compiled
//! generated adapter currently pins that profile or gives the WGSL trusted
//! semantics. The only implementation evidence is empirical native agreement:
//! `fold_gpu` matches the independently unverified CPU kernel `fri::fold` on
//! exercised inputs in `tests/gpu_fold_conformance.rs`.
//!
//! Layout seam: `fri::fold` is natural-order; the kernel works bit-reversed
//! (this module's convention: pairs adjacent, one shared bitrev twiddle table whose
//! per-round tables are its prefixes). This module permutes in and out with
//! `fri::bit_reverse_permute`, so callers only ever see natural order.
//! Arities beyond the kernel's 32-slot local window (`log_arity > 5`) chain
//! dispatches through the identity `fold(cw, b, j+k) = fold(fold(cw, b, j),
//! b^(2^j), k)` — the same beta-squaring schedule as the CPU fold.

use wgpu::util::DeviceExt;

use crate::field4::{Ext4, P};
use crate::fri::{self, bit_reverse_permute, halve_inv_powers_bitrev};

/// Error prefix for "this machine has no usable GPU adapter" — the marker the
/// conformance test uses to SKIP (loudly) instead of falsely passing.
pub const NO_ADAPTER: &str = "no-gpu-adapter";

/// The kernel's local fold window is 32 slots: at most 5 rounds per dispatch.
const MAX_LOG_ARITY_PER_DISPATCH: usize = 5;

/// Threads per workgroup — must match `@workgroup_size` in the shader.
const WORKGROUP_SIZE: u32 = 256;

/// Uniform block mirroring the shader's `Params` (size 32, beta at offset 16).
#[repr(C)]
#[derive(Clone, Copy, bytemuck::Pod, bytemuck::Zeroable)]
struct Params {
    n_out: u32,
    log_arity: u32,
    _pad: [u32; 2],
    beta: [u32; 4],
}

/// A ready GPU fold context: adapter + device + compiled pipeline, reusable
/// across folds (setup is the expensive part; keep it out of hot loops).
pub struct GpuFold {
    device: wgpu::Device,
    queue: wgpu::Queue,
    pipeline: wgpu::ComputePipeline,
    adapter_name: String,
}

impl GpuFold {
    /// Acquire a high-performance adapter (Metal on ember's Mac), build the
    /// pipeline. `Err` starting with [`NO_ADAPTER`] when no adapter exists.
    pub fn new() -> Result<GpuFold, String> {
        let instance = wgpu::Instance::default();
        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            compatible_surface: None,
            force_fallback_adapter: false,
        }))
        .ok_or_else(|| format!("{NO_ADAPTER}: no wgpu adapter on this machine"))?;
        let adapter_name = {
            let info = adapter.get_info();
            format!("{} ({:?})", info.name, info.backend)
        };
        let (device, queue) =
            pollster::block_on(adapter.request_device(&wgpu::DeviceDescriptor::default(), None))
                .map_err(|e| format!("request_device on {adapter_name}: {e}"))?;
        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("fri_fold"),
            source: wgpu::ShaderSource::Wgsl(include_str!("shaders/fri_fold.wgsl").into()),
        });
        let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: Some("fri_fold"),
            layout: None,
            module: &shader,
            entry_point: Some("fold"),
            compilation_options: Default::default(),
            cache: None,
        });
        Ok(GpuFold {
            device,
            queue,
            pipeline,
            adapter_name,
        })
    }

    /// The adapter this context runs on, e.g. `Apple M2 Max (Metal)`.
    pub fn adapter_name(&self) -> &str {
        &self.adapter_name
    }

    /// The arity-`2^log_arity` native fold on the GPU — natural-order in and
    /// out, with the same API and intended arithmetic as `fri::fold`.
    /// Agreement is empirical, not semantic. Chains dispatches for
    /// `log_arity > 5` with this module's beta-squaring schedule.
    pub fn fold(
        &self,
        codeword: &[Ext4],
        beta: Ext4,
        log_arity: usize,
    ) -> Result<Vec<Ext4>, String> {
        if !codeword.len().is_power_of_two() {
            return Err(format!(
                "fold_gpu: length {} not a power of two",
                codeword.len()
            ));
        }
        if log_arity as u32 > codeword.len().trailing_zeros() {
            return Err(format!(
                "fold_gpu: arity 2^{log_arity} exceeds codeword length {}",
                codeword.len()
            ));
        }
        if log_arity == 0 {
            return Ok(codeword.to_vec());
        }
        let mut word: Vec<Ext4> = codeword.to_vec();
        let mut b = beta;
        let mut remaining = log_arity;
        while remaining > 0 {
            let k = remaining.min(MAX_LOG_ARITY_PER_DISPATCH);
            word = self.dispatch_fold(&word, b, k)?;
            for _ in 0..k {
                b = b.square();
            }
            remaining -= k;
        }
        Ok(word)
    }

    /// One kernel launch: `k <= 5` fold rounds over the whole word.
    fn dispatch_fold(&self, word: &[Ext4], beta: Ext4, k: usize) -> Result<Vec<Ext4>, String> {
        debug_assert!((1..=MAX_LOG_ARITY_PER_DISPATCH).contains(&k));
        let n = word.len();
        let log_n = n.trailing_zeros();
        let n_out = n >> k;
        let workgroups = (n_out as u32).div_ceil(WORKGROUP_SIZE).max(1);
        if workgroups > 65535 {
            return Err(format!(
                "fold_gpu: {n_out} outputs exceed the 1-D dispatch limit"
            ));
        }

        // natural -> bitrev (the kernel's working layout), canonical u32 lanes
        let src: Vec<[u32; 4]> = bit_reverse_permute(word).iter().map(pack).collect();
        // one shared bitrev twiddle table, Montgomery form (x * 2^32 mod P)
        let twiddles: Vec<u32> = halve_inv_powers_bitrev(log_n)
            .iter()
            .map(|&t| ((u128::from(t) << 32) % u128::from(P)) as u32)
            .collect();
        let params = Params {
            n_out: n_out as u32,
            log_arity: k as u32,
            _pad: [0; 2],
            beta: pack(&beta),
        };

        let src_buf = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("fri_fold src"),
                contents: bytemuck::cast_slice(&src),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let twid_buf = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("fri_fold twiddles"),
                contents: bytemuck::cast_slice(&twiddles),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let params_buf = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("fri_fold params"),
                contents: bytemuck::bytes_of(&params),
                usage: wgpu::BufferUsages::UNIFORM,
            });
        let out_bytes = (n_out * 16) as u64;
        let dst_buf = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("fri_fold dst"),
            size: out_bytes,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });
        let staging = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("fri_fold staging"),
            size: out_bytes,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let bind_group = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("fri_fold"),
            layout: &self.pipeline.get_bind_group_layout(0),
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: src_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: twid_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: params_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 3,
                    resource: dst_buf.as_entire_binding(),
                },
            ],
        });

        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("fri_fold"),
            });
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("fri_fold"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.pipeline);
            pass.set_bind_group(0, &bind_group, &[]);
            pass.dispatch_workgroups(workgroups, 1, 1);
        }
        encoder.copy_buffer_to_buffer(&dst_buf, 0, &staging, 0, out_bytes);
        self.queue.submit(Some(encoder.finish()));

        let slice = staging.slice(..);
        let (tx, rx) = std::sync::mpsc::channel();
        slice.map_async(wgpu::MapMode::Read, move |r| {
            let _ = tx.send(r);
        });
        self.device.poll(wgpu::Maintain::Wait);
        rx.recv()
            .map_err(|_| "fold_gpu: map_async callback dropped".to_string())?
            .map_err(|e| format!("fold_gpu: buffer map failed: {e}"))?;
        let folded_rev: Vec<Ext4> = {
            let data = slice.get_mapped_range();
            bytemuck::cast_slice::<u8, [u32; 4]>(&data)
                .iter()
                .map(unpack)
                .collect()
        };
        staging.unmap();

        // bitrev -> natural (an involution)
        Ok(bit_reverse_permute(&folded_rev))
    }
}

/// Canonical `Ext4` -> 4 canonical u32 lanes (lanes are `< P < 2^32`).
fn pack(x: &Ext4) -> [u32; 4] {
    debug_assert!(x.c.iter().all(|&c| c < P));
    [x.c[0] as u32, x.c[1] as u32, x.c[2] as u32, x.c[3] as u32]
}

fn unpack(w: &[u32; 4]) -> Ext4 {
    Ext4 {
        c: [
            u64::from(w[0]),
            u64::from(w[1]),
            u64::from(w[2]),
            u64::from(w[3]),
        ],
    }
}

/// One-shot GPU fold: build a context, fold, tear down. `Err` starting with
/// [`NO_ADAPTER`] when the machine has no GPU. For hot loops build one
/// [`GpuFold`] and reuse it.
pub fn fold_gpu(codeword: &[Ext4], beta: Ext4, log_arity: usize) -> Result<Vec<Ext4>, String> {
    GpuFold::new()?.fold(codeword, beta, log_arity)
}

/// The fold with a CPU fallback: GPU when an adapter exists, otherwise
/// `fri::fold` (the same function the GPU is conformance-gated against).
pub fn fold_auto(codeword: &[Ext4], beta: Ext4, log_arity: usize) -> Vec<Ext4> {
    match fold_gpu(codeword, beta, log_arity) {
        Ok(folded) => folded,
        Err(_) => fri::fold(codeword, beta, log_arity),
    }
}
