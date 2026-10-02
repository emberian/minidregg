//! Physical placement adapter. Mini reserve and send-boundary checks stay in Runtime.
use minidregg_inference_scheduler::{
    self as scheduler,
    core::{Job, Outcome, Request, State},
    Command,
};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::time::Duration;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Config {
    pub socket: PathBuf,
    pub controller: String,
    pub domain: String,
    pub principal: String,
    pub pool: String,
    /// Names from the same root-owned Mini provider table. Every destination
    /// must still be a homelab row supporting this exact pinned model.
    pub backends: Vec<String>,
    pub queue_timeout_ms: u64,
}

#[derive(Clone, Debug)]
pub struct Plan {
    pub config: Config,
    pub request: Request,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Placement {
    pub config: Config,
    pub request: Request,
    pub lease: u64,
    pub endpoint: String,
}

impl Plan {
    pub fn wait(mut self, active: impl Fn() -> bool) -> Result<Guard, String> {
        let id = self.request.id.clone();
        let mut job = scheduler::request(
            &self.config.socket,
            &Command::Enqueue {
                controller: self.config.controller.clone(),
                job: self.request.clone(),
            },
        ).map_err(|error| if error == "scheduler refused: scheduler-draining" {
            "provider-refused:homelab-draining".into()
        } else { error })?;
        // Exact re-enqueue keeps the first durable queue deadline; it cannot
        // extend a waiting operation by repeatedly reconnecting.
        if job.request.queue_deadline_ms > self.request.queue_deadline_ms {
            return Err("retained queue deadline exceeds current controller pin".into());
        }
        self.request.queue_deadline_ms = job.request.queue_deadline_ms;
        loop {
            self.check(&job)?;
            if !active() {
                let _ = scheduler::request(
                    &self.config.socket,
                    &Command::Cancel {
                        controller: self.config.controller.clone(),
                        id,
                    },
                );
                return Err("provider prompt stopped while waiting for homelab capacity".into());
            }
            match &job.state {
                State::Placed {
                    lease, endpoint, ..
                } => {
                    return Ok(Guard {
                        placement: Placement {
                            config: self.config,
                            request: self.request,
                            lease: *lease,
                            endpoint: endpoint.clone(),
                        },
                        outcome: Outcome::NotSent,
                    })
                }
                State::Terminal { outcome: Outcome::Drained, .. } => return Err(
                    "provider-refused:homelab-drained-before-send".into()),
                State::Queued => {}
                _ => {
                    return Err(
                        "homelab job is terminal or uncertain; reconcile retained operation".into(),
                    )
                }
            }
            std::thread::sleep(Duration::from_millis(100));
            job = scheduler::request(
                &self.config.socket,
                &Command::Inspect {
                    controller: self.config.controller.clone(),
                    id: id.clone(),
                },
            )?;
        }
    }

    fn check(&self, job: &Job) -> Result<(), String> {
        if job.controller != self.config.controller
            || job.principal != self.config.principal
            || job.pool != self.config.pool
            || job.request != self.request
        {
            return Err("scheduler reply differs from controller-pinned job/principal/pool".into());
        }
        Ok(())
    }
}

impl Placement {
    pub fn verify(&self, body: &[u8]) -> Result<(), String> {
        if self.request.request_digest != scheduler::digest(body) {
            return Err("placement body digest differs".into());
        }
        let job = scheduler::request(
            &self.config.socket,
            &Command::Inspect {
                controller: self.config.controller.clone(),
                id: self.request.id.clone(),
            },
        )?;
        Plan {
            config: self.config.clone(),
            request: self.request.clone(),
        }
        .check(&job)?;
        match job.state {
            State::Placed {
                lease, endpoint, ..
            } if lease == self.lease && endpoint == self.endpoint => Ok(()),
            _ => Err("homelab placement is not the exact unsent lease".into()),
        }
    }

    pub fn dispatch(&self, attempt: String) -> Result<(), String> {
        let job = scheduler::request(
            &self.config.socket,
            &Command::Dispatch {
                controller: self.config.controller.clone(),
                id: self.request.id.clone(),
                lease: self.lease,
                attempt: attempt.clone(),
            },
        )?;
        match job.state {
            State::Dispatched {
                lease,
                attempt: actual,
                ..
            } if lease == self.lease && actual == attempt => Ok(()),
            _ => Err("scheduler did not acknowledge exact dispatch".into()),
        }
    }

    pub fn finish(&self, outcome: Outcome) -> Result<(), String> {
        scheduler::request(
            &self.config.socket,
            &Command::Finish {
                controller: self.config.controller.clone(),
                id: self.request.id.clone(),
                lease: self.lease,
                outcome,
            },
        )
        .map(|_| ())
    }
}

/// All exits before physical send release an unsent allocation. Once the physical
/// edge starts, the default becomes uncertain and capacity remains quarantined.
pub struct Guard {
    pub placement: Placement,
    pub outcome: Outcome,
}

impl Drop for Guard {
    fn drop(&mut self) {
        // Failed reconciliation retains the broker's last durable state. It must
        // not be interpreted as a physical capacity release or permission to resend.
        if let Err(error) = self.placement.finish(self.outcome) {
            eprintln!("homelab allocation requires reconciliation: {error}");
        }
    }
}
