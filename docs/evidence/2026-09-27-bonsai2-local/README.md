# Local Bonsai 2 qualification (hbox, 2026-09-27)

This is a private inference service qualification, not a deployed Hermes provider or a paid-model call. The service listens only on hbox loopback. Its bearer key is in a mode-0600 file at `/tank/dregg-build/bonsai2-local-20260927/evidence/api-key`; the key is not in this record.

## Source and hardware

- Official runtime: [PrismML Bonsai demo](https://github.com/PrismML-Eng/Bonsai-demo) and its [backend support matrix](https://github.com/PrismML-Eng/Bonsai-demo/blob/main/BACKEND-SUPPORT.md). Bonsai 2 needs the PrismML llama.cpp fork. The matrix lists a Vulkan PTQ1_0 path and no Vulkan PQ2_0 kernels, so this installation uses PTQ1_0 rather than the demo's PQ2_0 default.
- Runtime release: [`prism-b10743-adfffbe`](https://github.com/PrismML-Eng/llama.cpp/releases/tag/prism-b10743-adfffbe). Linux x64 Vulkan archive SHA-256 `95a3d082629643642842bc2195e0730880273005171517cf857804702f693edc` matches the GitHub release digest. Extracted `llama-server` SHA-256 `f0321669b20397593e3ac09972bf6f4b7a0684954906565353b7ca84b4b0320f`; `--version` reports build 10743, commit `adfffbe41`.
- Official [GGUF repository](https://huggingface.co/prism-ml/Ternary-Bonsai-2-27B-gguf), revision `b072e1d3b35a0a630cece372c2127528e0994386`: `Ternary-Bonsai-2-27B-PTQ1_0.gguf`, 5,946,648,928 bytes. SHA-256 `53107f530aa52eb00912263ab1ee29bd199261c87cd7b4ad4ca1318c1fe33ee3` matches the Hugging Face LFS digest.
- hbox has an AMD Radeon RX 6750 XT with 12 GiB VRAM and Vulkan 1.4.313 / AMD LLPC driver. The pinned runtime identifies it as `Vulkan0`. No NVIDIA device, ROCm compiler, preexisting model server, or GGUF was found. At the inventory point, hbox had roughly 64 GiB available RAM and 741 GiB free under `/tank`. The existing FN/SBCL workloads were left running.

## Private service

Files are under `/tank/dregg-build/bonsai2-local-20260927`. The bounded user unit is `bonsai2-ptq1-local-v2.service` (initial v1 was stopped before model load to add authentication). Its launch arguments are:

```text
llama-server --model /tank/dregg-build/bonsai2-local-20260927/model/Ternary-Bonsai-2-27B-PTQ1_0.gguf
  --alias bonsai2-27b-ptq1 --host 127.0.0.1 --port 18080
  --device Vulkan0 --n-gpu-layers 99 --ctx-size 8192 --parallel 1
  --threads 2 --jinja --reasoning-budget 512 --no-webui
  --api-key-file /tank/dregg-build/bonsai2-local-20260927/evidence/api-key
  --cors-origins http://127.0.0.1:18080
```

The unit has `CPUQuota=200%` and `MemoryMax=24G`; `ss` confirmed only `127.0.0.1:18080` listening. Unauthenticated `/v1/models` returned HTTP 401. Authenticated `/v1/models` reported `bonsai2-27b-ptq1`. AMD VRAM use rose from about 1.1 GiB before launch to about 7.7 GiB after load, corroborating GPU offload. No driver or system package was changed. A controller on another host would need a private loopback tunnel; the server itself has no non-loopback listener.

## OpenAI-compatible wire smoke

All requests used harmless local test content. Request and response files remain on hbox under `evidence/`; no key appears in them. The [official tool-calling guide](https://github.com/PrismML-Eng/Bonsai-demo/blob/main/TOOLS.md) requires `--jinja`, which is enabled here.

- Non-streaming `/v1/chat/completions`: `2+2` returned content `4`, model echo `bonsai2-27b-ptq1`, finish `stop`, and usage 65 prompt / 40 completion tokens. Wall 5.87 s; server timings 22.96 prompt tok/s and 13.60 generated tok/s. This was one cold request, not a throughput guarantee.
- Required `add_numbers` tool call: returned structured `tool_calls` with `{"a":2,"b":3}`, finish `tool_calls`, model echo, and usage 338 prompt / 63 completion tokens. Wall 8.48 s; generation 14.03 tok/s.
- The same request with `stream=true` and `stream_options.include_usage=true` emitted 36 SSE `data:` events, seven tool-call delta events, a final usage event (338 prompt / 64 completion tokens), and `[DONE]`. Wall 4.81 s.
- Sending the tool result `5` back with the original call ID returned a normal final assistant message with `5`, finish `stop`, and usage 392 prompt / 35 completion tokens. Wall 3.60 s.

The service has not been attached to a signed provider grain or exercised through the Hermes gateway. The gateway contract expects `/v1/chat/completions`, structured function tools, `stream_options.include_usage`, bounded `max_tokens`, and a pinned model string; these direct API probes cover that wire shape only. One slot and an 8,192-token context are deliberately conservative while hbox carries other workloads.

## Retained file digests

```text
7b4fabb4357c25cc4e0ecae028dfa062e584f2800d698a27da47047a52bffb5d  evidence/nonstream-request.json
9f1c2b72917f08663c1405e4771854e09ee5daa55b3d1ddf111fc6f7d3edac97  evidence/nonstream-response.json
6fe791f651599a15daf622f502c7746f2f85f0fd1e9bff4ced5ef0b6e21cbc11  evidence/tool-request.json
382bf4c683dba4ec88ae9c90525d1b4f28adff4ff52bb0f7ca5a150cff335084  evidence/tool-response.json
e68ca0057f3c3d7d9de1459c9d3d15efec8746475b22b6ee0c98978194452d3e  evidence/tool-stream-request.json
efb66836745f6209616952a3393fa8ae79ecbedca9dd4cfc09dc057fb4ecaa02  evidence/tool-stream.sse
5a90e6bc8ac98c91c4af2cf6d96139cd799638bcf2cf2d7fe562acf2dd124f27  evidence/tool-roundtrip-request.json
8176761aa29697f13b9a5850aca9a5beaf5823cc85f5c0d361a099248040ab5e  evidence/tool-roundtrip-response.json
```
