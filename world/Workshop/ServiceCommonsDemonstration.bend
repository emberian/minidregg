# Named source-execution witnesses; these are not physical provider receipts.
# Real receiving must instantiate roots and native operation/result observations
# from current signed resources, then admit the source-proposed common Plan.
import Base
import ./ResidentServiceCommons.bend as Service
import ./CanonicalBookSettlement.bend as Book

def method() -> Service.Method:
  Service.Method{[1n], [2n], [3n], [4n], [5n]}

def identity() -> Service.Identity:
  Service.Identity{[20n], method(), [21n], [22n]}

def request(+root: List<&2, Nat>) -> Service.Request:
  Service.Request{identity(), Service.Pin{10n, root}, Service.Pin{11n, root},
    [7n], [7n], [8n], [1n], [9n], method(), 100n, 2n, 8n,
    Service.Payment{9n, root, 1n, 4n, 5n, 8n, 20n}}

def offer(root: List<&2, Nat>) -> Service.Offer:
  Service.Offer{identity(), [6n], Service.Pin{12n, root}, 5n, 3n, 90n, [55n]}

def sponsor(root: List<&2, Nat>) -> Service.Sponsorship:
  Service.Sponsorship{identity(), [6n], Service.Pin{14n, root}, 8n, True{}}

def reservation(+root: List<&2, Nat>) -> Service.Reservation:
  Service.Reservation{request(root), offer(root), sponsor(root), 6n}

def run(root: List<&2, Nat>) -> Service.Run:
  Service.Run{[31n], 17n, 2n, 7n, [31n], Service.Pin{13n, root}, 4n, identity()}

def completion(+root: List<&2, Nat>, output: List<&2, Nat>) -> Service.Completion:
  Service.Completion{run(root), [6n], output, [7n], [8n], [1n], Service.Pin{15n, root}}

def review(output: List<&2, Nat>) -> Service.Review:
  Service.Review{[31n], output, method(), [9n], True{}}

law reserves_exact_budget_and_capacity:
  for +root: List<&2, Nat>
  {Service.reserve(request(root), offer(root), sponsor(root), 80n) ==
    Service.Proposed{Service.Vacant{}, Service.Held{reservation(root)},
      [Service.Money{9n, root, Book.Transfer{1n, 4n, 8n, 6n}},
       Service.Capacity{Service.Pin{12n, root}, 5n, 3n}]} : Service.Transition}

def reserves_exact_budget_and_capacity(root):
  {==}

law retains_before_dispatch:
  for +root: List<&2, Nat>
  {Service.start(Service.Held{reservation(root)}, run(root), 80n) ==
    Service.Proposed{Service.Held{reservation(root)}, Service.Running{reservation(root), run(root)},
      [Service.PublishRequest{Service.Pin{10n, root}, Service.Pin{11n, root}, request(root), run(root)}]}
    : Service.Transition}

def retains_before_dispatch(root):
  {==}

law expired_unstarted_cannot_dispatch:
  for +root: List<&2, Nat>
  {Service.start(Service.Held{reservation(root)}, run(root), 101n) ==
    Service.Refused{Service.Held{reservation(root)}} : Service.Transition}

def expired_unstarted_cannot_dispatch(root):
  {==}

# A true finite continuation response retains the observed completion, with no
# monetary effect or claim that sponsor approved its factual contents.
law completion_is_not_payment:
  {Service.resume_after_status(Service.Running{reservation([40n]), run([40n])},
    completion([40n], [41n]), True{}) ==
    Service.Proposed{Service.Running{reservation([40n]), run([40n])},
      Service.Delivered{reservation([40n]), run([40n]), completion([40n], [41n])},
      [Service.RetainCompletion{run([40n]), completion([40n], [41n])}]} : Service.Transition}

def completion_is_not_payment():
  {==}

law reviewed_result_pays_once:
  for +currentRoot: List<&2, Nat>
  {Service.accept(Service.Delivered{reservation([40n]), run([40n]), completion([40n], [41n])},
    review([41n]), Service.Pin{12n, currentRoot}, 3n, currentRoot) ==
    Service.Proposed{Service.Delivered{reservation([40n]), run([40n]), completion([40n], [41n])},
      Service.Finished{reservation([40n]), run([40n]), completion([40n], [41n]), review([41n])},
      [Service.Money{9n, currentRoot, Book.Transfer{4n, 5n, 8n, 6n}},
       Service.Capacity{Service.Pin{12n, currentRoot}, 3n, 5n},
       Service.ReturnResult{[7n], [8n], [1n], [41n]}]} : Service.Transition}

def reviewed_result_pays_once(currentRoot):
  {==}
