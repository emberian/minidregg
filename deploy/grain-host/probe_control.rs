// Component probe: compile next to grain-runtime's exact src/control.rs and
// exercise its Unix listener through the real grain-runtime connect command.
#[path = "control.rs"]
mod control;

use std::fs::OpenOptions;
use std::io::Write;
use std::path::PathBuf;
use std::sync::Arc;

fn log(path: &PathBuf, line: &str) {
    let mut file = OpenOptions::new().create(true).append(true).open(path).unwrap();
    file.write_all(format!("{line}\n").as_bytes()).unwrap();
    file.sync_all().unwrap();
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(args.len(), 3, "usage: probe-control SOCKET LOG");
    let socket = PathBuf::from(&args[1]);
    let logfile = PathBuf::from(&args[2]);
    let interrupt_log = logfile.clone();
    let interrupt: control::HardInterrupt = Arc::new(move |id| {
        log(&interrupt_log, &format!("hard-interrupt:{id}"));
    });
    let server = control::start(&socket, interrupt).unwrap();
    let mut detach_count = 0;
    while detach_count < 3 {
        match server.events.recv().unwrap() {
            control::Event::Attached { id, soft } => {
                log(&logfile, &format!("attached:{id}:soft={soft}"));
                log(&logfile, &format!("attached-output:{id}:{}", server.output_handle().try_output(format!("attached:{id}\n"))));
            }
            control::Event::Line { id, text } => {
                log(&logfile, &format!("line:{id}:{text}"));
                log(&logfile, &format!("line-output:{id}:{}", server.output_handle().try_output(format!("line:{text}\n"))));
            }
            control::Event::Detached { id, hard } => {
                log(&logfile, &format!("detached:{id}:hard={hard}"));
                detach_count += 1;
            }
        }
    }
}
