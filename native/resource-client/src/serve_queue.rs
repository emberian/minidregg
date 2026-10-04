//! The queue between `mini serve`'s connection threads and its one Host
//! thread. Bounded like the channel it replaces, but fair between peers: the
//! Host thread takes one job from each waiting peer in turn, and when the
//! queue is full a peer holding more than its share gives up its newest
//! queued job to a peer holding less, instead of the newcomer being refused.
//!
//! A displaced job was never written to the Host, so the caller answers it
//! with a certain refusal (`busy: ...`), exactly as for `queue_residence`.
//!
//! The peer key is whatever the caller can attest about the connecting
//! process. `mini serve` uses the kernel's peer uid. Where every public
//! client arrives as one uid (an ssh proxy account) they are one peer and the
//! queue is first-in first-out, as before; the per-operation body bounds and
//! Host-time budgets are what limit one client there.
use std::collections::{BTreeMap, VecDeque};
use std::sync::{Arc, Condvar, Mutex, MutexGuard, PoisonError};

/// A peer whose credentials could not be read. All such peers share one share.
pub(crate) const UNKNOWN_PEER: u32 = u32::MAX;

#[derive(Debug)]
pub(crate) enum TrySendError<T> {
    /// The queue is at capacity and the sender already holds its fair share.
    Full(T),
    /// The receiving side is gone.
    Disconnected(T),
}

struct State<T> {
    queues: BTreeMap<u32, VecDeque<T>>,
    /// Peers with a non-empty queue, in the order the Host thread serves them.
    order: VecDeque<u32>,
    len: usize,
    senders: usize,
    receiver_alive: bool,
}

struct Shared<T> {
    state: Mutex<State<T>>,
    ready: Condvar,
    capacity: usize,
}

impl<T> Shared<T> {
    fn lock(&self) -> MutexGuard<'_, State<T>> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

pub(crate) struct Sender<T>(Arc<Shared<T>>);
pub(crate) struct Receiver<T>(Arc<Shared<T>>);

pub(crate) fn fair_queue<T>(capacity: usize) -> (Sender<T>, Receiver<T>) {
    let shared = Arc::new(Shared {
        state: Mutex::new(State {
            queues: BTreeMap::new(),
            order: VecDeque::new(),
            len: 0,
            senders: 1,
            receiver_alive: true,
        }),
        ready: Condvar::new(),
        capacity,
    });
    (Sender(shared.clone()), Receiver(shared))
}

impl<T> Sender<T> {
    /// Queue `item` for `peer`. `Ok(Some(displaced))` means the queue was full,
    /// `peer` held fewer than half of the heaviest peer's jobs plus one, and the
    /// heaviest peer's newest job was removed to make room: the caller owes
    /// that job a refusal. Never blocks.
    pub(crate) fn try_send(&self, peer: u32, item: T) -> Result<Option<T>, TrySendError<T>> {
        let mut state = self.0.lock();
        if !state.receiver_alive {
            return Err(TrySendError::Disconnected(item));
        }
        let mut displaced = None;
        if state.len >= self.0.capacity {
            let own = state.queues.get(&peer).map_or(0, VecDeque::len);
            let heaviest = state
                .queues
                .iter()
                .max_by_key(|(key, queue)| (queue.len(), std::cmp::Reverse(**key)))
                .map(|(key, queue)| (*key, queue.len()));
            match heaviest {
                Some((key, len)) if key != peer && len > own + 1 => {
                    let queue = state.queues.get_mut(&key).expect("heaviest peer has a queue");
                    displaced = queue.pop_back();
                    let emptied = queue.is_empty();
                    if emptied {
                        state.queues.remove(&key);
                        state.order.retain(|queued| *queued != key);
                    }
                    state.len -= 1;
                }
                _ => return Err(TrySendError::Full(item)),
            }
        }
        let queue = state.queues.entry(peer).or_default();
        let first = queue.is_empty();
        queue.push_back(item);
        if first {
            state.order.push_back(peer);
        }
        state.len += 1;
        drop(state);
        self.0.ready.notify_one();
        Ok(displaced)
    }
}

impl<T> Clone for Sender<T> {
    fn clone(&self) -> Self {
        self.0.lock().senders += 1;
        Sender(self.0.clone())
    }
}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        let mut state = self.0.lock();
        state.senders -= 1;
        let last = state.senders == 0;
        drop(state);
        if last {
            self.0.ready.notify_all();
        }
    }
}

impl<T> Drop for Receiver<T> {
    fn drop(&mut self) {
        self.0.lock().receiver_alive = false;
    }
}

/// Blocks for the next job, one peer at a time in turn; ends when the queue is
/// empty and every `Sender` is gone.
impl<T> Iterator for Receiver<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        let mut state = self.0.lock();
        loop {
            if let Some(peer) = state.order.pop_front() {
                let queue = state.queues.get_mut(&peer).expect("ordered peer has a queue");
                let item = queue.pop_front().expect("ordered peer has a job");
                if queue.is_empty() {
                    state.queues.remove(&peer);
                } else {
                    state.order.push_back(peer);
                }
                state.len -= 1;
                return Some(item);
            }
            if state.senders == 0 {
                return None;
            }
            state = self.0.ready.wait(state).unwrap_or_else(PoisonError::into_inner);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn drain<T>(receiver: &mut Receiver<T>, count: usize) -> Vec<T> {
        (0..count).map(|_| receiver.next().expect("a queued job")).collect()
    }

    /// One peer's backlog does not delay another peer's job past one turn.
    #[test]
    fn peers_are_served_in_turn() {
        let (sender, mut receiver) = fair_queue::<&str>(16);
        for job in ["a1", "a2", "a3", "a4"] {
            assert!(sender.try_send(1, job).unwrap().is_none());
        }
        assert!(sender.try_send(2, "b1").unwrap().is_none());
        assert!(sender.try_send(3, "c1").unwrap().is_none());
        assert_eq!(drain(&mut receiver, 6), ["a1", "b1", "c1", "a2", "a3", "a4"]);
    }

    /// With a single peer the queue is first-in first-out.
    #[test]
    fn one_peer_is_first_in_first_out() {
        let (sender, mut receiver) = fair_queue::<u8>(8);
        for job in 0..5 {
            assert!(sender.try_send(UNKNOWN_PEER, job).unwrap().is_none());
        }
        assert_eq!(drain(&mut receiver, 5), [0, 1, 2, 3, 4]);
    }

    /// A full queue refuses a peer that already holds its share, and does not
    /// disturb the jobs it holds.
    #[test]
    fn a_full_queue_refuses_the_peer_that_filled_it() {
        let (sender, mut receiver) = fair_queue::<u8>(3);
        for job in 0..3 {
            assert!(sender.try_send(1, job).unwrap().is_none());
        }
        assert!(matches!(sender.try_send(1, 9), Err(TrySendError::Full(9))));
        assert_eq!(drain(&mut receiver, 3), [0, 1, 2]);
    }

    /// A newcomer holding less than the heaviest peer takes a slot from it: the
    /// heaviest peer's newest job is handed back for refusal, and a peer already
    /// at its share cannot displace anyone.
    #[test]
    fn a_full_queue_gives_a_light_peer_the_heaviest_peers_newest_slot() {
        let (sender, mut receiver) = fair_queue::<&str>(4);
        for job in ["a1", "a2", "a3", "a4"] {
            assert!(sender.try_send(1, job).unwrap().is_none());
        }
        assert_eq!(sender.try_send(2, "b1").unwrap(), Some("a4"));
        // a holds 3, b holds 1: b may take one more slot, then the shares are 2/2.
        assert_eq!(sender.try_send(2, "b2").unwrap(), Some("a3"));
        // 2/2: neither may displace the other.
        assert!(matches!(sender.try_send(2, "b3"), Err(TrySendError::Full("b3"))));
        assert!(matches!(sender.try_send(1, "a5"), Err(TrySendError::Full("a5"))));
        assert_eq!(drain(&mut receiver, 4), ["a1", "b1", "a2", "b2"]);
    }

    /// The Host thread's iteration ends only once the queue is empty and every
    /// sender, clones included, is gone: the operator drain's closure proof.
    #[test]
    fn iteration_ends_after_the_last_sender_and_the_last_job() {
        let (sender, mut receiver) = fair_queue::<u8>(4);
        let clone = sender.clone();
        sender.try_send(1, 1).unwrap();
        drop(sender);
        assert_eq!(receiver.next(), Some(1));
        let waiting = std::thread::spawn(move || receiver.next());
        std::thread::sleep(std::time::Duration::from_millis(100));
        assert!(!waiting.is_finished(), "a live sender must keep the receiver waiting");
        drop(clone);
        assert_eq!(waiting.join().unwrap(), None);
    }

    #[test]
    fn a_dropped_receiver_disconnects_senders() {
        let (sender, receiver) = fair_queue::<u8>(2);
        drop(receiver);
        assert!(matches!(sender.try_send(1, 7), Err(TrySendError::Disconnected(7))));
    }
}
