//! Physical browser ingress bounds. No resource view or admission is cached here.
use std::io::{self, Read, Write};
use std::net::TcpStream;
use std::sync::{Arc, atomic::{AtomicUsize, Ordering}};
use std::time::{Duration, Instant};

pub(super) const MAX_CONNECTIONS: usize = 16;
pub(super) const INGRESS_DEADLINE: Duration = Duration::from_secs(10);

/// One permit spans ingress, current Host work and response delivery. Readers
/// cannot create an unbounded queue behind a slow Host or a stalled browser.
pub(super) struct Pool {
    live: Arc<AtomicUsize>,
    limit: usize,
}

struct Permit(Arc<AtomicUsize>);
impl Drop for Permit {
    fn drop(&mut self) { self.0.fetch_sub(1, Ordering::AcqRel); }
}

impl Pool {
    pub(super) fn new(limit: usize) -> Self {
        assert!(limit > 0);
        Self { live: Arc::new(AtomicUsize::new(0)), limit }
    }

    /// Overflow refuses before invoking the handler. A detached worker owns
    /// its permit; completion or panic releases it without retaining handles.
    pub(super) fn dispatch(
        &self,
        mut stream: TcpStream,
        handler: Arc<dyn Fn(TcpStream, Instant) + Send + Sync>,
    ) -> io::Result<bool> {
        let accepted = Instant::now();
        if self.live.fetch_update(Ordering::AcqRel, Ordering::Acquire,
            |count| (count < self.limit).then_some(count + 1)).is_err() {
            stream.set_write_timeout(Some(Duration::from_secs(1)))?;
            stream.write_all(b"HTTP/1.1 503 Service Unavailable\r\nContent-Length: 4\r\nConnection: close\r\nRetry-After: 1\r\n\r\nbusy")?;
            return Ok(false);
        }
        let permit = Permit(self.live.clone());
        std::thread::Builder::new().name("mini-web-client".into()).spawn(move || {
            let _permit = permit;
            handler(stream, accepted + INGRESS_DEADLINE);
        })?;
        Ok(true)
    }
}

/// The complete header AND form body share one deadline from acceptance.
/// Refreshing a socket's relative timeout after each byte would let a
/// trickling client occupy a worker forever.
pub(super) fn read_ingress(stream: &mut TcpStream, buffer: &mut [u8], deadline: Instant) -> io::Result<usize> {
    let remaining = deadline.checked_duration_since(Instant::now())
        .filter(|remaining| !remaining.is_zero())
        .ok_or_else(|| io::Error::new(io::ErrorKind::TimedOut, "browser ingress deadline"))?;
    stream.set_read_timeout(Some(remaining))?;
    stream.read(buffer)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::{TcpListener, Shutdown};
    use std::sync::mpsc;

    fn pair() -> (TcpStream, TcpStream) {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let client = TcpStream::connect(listener.local_addr().unwrap()).unwrap();
        (client, listener.accept().unwrap().0)
    }

    #[test]
    fn idle_browser_does_not_block_other_work_and_capacity_recovers() {
        let pool = Pool::new(2);
        let (entered, seen) = mpsc::channel();
        let handler = Arc::new(move |mut stream: TcpStream, deadline| {
            entered.send(()).unwrap();
            let mut byte = [0];
            let _ = read_ingress(&mut stream, &mut byte, deadline);
        });
        let (idle, server) = pair();
        assert!(pool.dispatch(server, handler.clone()).unwrap());
        seen.recv_timeout(Duration::from_secs(1)).unwrap();
        let (mut ready, server) = pair();
        assert!(pool.dispatch(server, handler.clone()).unwrap());
        seen.recv_timeout(Duration::from_secs(1)).unwrap();
        let (mut overflow, server) = pair();
        assert!(!pool.dispatch(server, handler.clone()).unwrap());
        let mut response = String::new();
        overflow.read_to_string(&mut response).unwrap();
        assert!(response.starts_with("HTTP/1.1 503"));
        ready.write_all(b"x").unwrap();
        idle.shutdown(Shutdown::Both).unwrap();
        let deadline = Instant::now() + Duration::from_secs(1);
        while pool.live.load(Ordering::Acquire) != 0 {
            assert!(Instant::now() < deadline);
            std::thread::yield_now();
        }
        let (mut next, server) = pair();
        assert!(pool.dispatch(server, handler).unwrap());
        seen.recv_timeout(Duration::from_secs(1)).unwrap();
        next.write_all(b"x").unwrap();
    }

    #[test]
    fn trickle_does_not_extend_absolute_ingress_deadline() {
        let (mut client, mut server) = pair();
        let deadline = Instant::now() + Duration::from_millis(60);
        client.write_all(b"a").unwrap();
        let mut byte = [0];
        assert_eq!(read_ingress(&mut server, &mut byte, deadline).unwrap(), 1);
        std::thread::sleep(Duration::from_millis(80));
        client.write_all(b"b").unwrap();
        assert_eq!(read_ingress(&mut server, &mut byte, deadline).unwrap_err().kind(), io::ErrorKind::TimedOut);
    }
}
