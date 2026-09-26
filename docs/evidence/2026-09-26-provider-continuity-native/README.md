# Provider reserve continuity: isolated native acceptance

The certified Linux Mini host (`41647562c7dd1fe6cdf41836aa62c61fd7b24314f883b2bb14cb38779707c49a`) and public `mini` client (`128bd81cb5876f2cf0071767b8022b5d961ce94956cfd2d550e7d34fc54e7703`) exercised read-only op17 through an owner-only persistent socket. The host source is the committed op17/18 checkpoint with the selected bbf evidence profile. Full private attempts remain on persvati at `/tmp/mga-op17-acceptance-20260926`; this directory contains copied Stores and signatures and is not copied into the repository.

The starting point was a copy of the direct-provider fixture. Its original Store had ten accepted records: the provider reserve was record 9 and a later parent hard trip was record 10. A separate scratch Store was cut to the exact first nine canonical accepted records and re-opened with native replay before any case ran. The cut log at `cut-prefix.log` records acceptedCount 9 and boundary `12291667401736583122827621767387130038929061505188795592955923008144953934646`. The original fixture Store was never mutated by these checks.

| Case (private attempt) | Result | Typed reply SHA-256 |
| --- | --- | --- |
| Exact reserve at tip (`tip-case/positive`) | `continuous:true`, provider 7004, count 9 | `7c30ca077d335eef4e544607c332f0e88fca4984f3e690b987be19c869ac478a` |
| Wrong confirmed anchor (`tip-negative/wrong-anchor`) | Refused: receipt differs from admitted prefix | `71d2deeacddeba20935ba626894919e23535c3302c8e5acb1796fe6316b00f8c` |
| Wrong original call (`tip-negative/wrong-call`) | Refused: call differs from admitted history | `7290e76837c12ab7283545482dcd4a201744d4aac0dfc29fd979f6ba856f95bd` |
| Unrelated ordinary parent suffix (`unrelated-suffix/result`) | `continuous:true`, count 10; checked boundary advanced | `eeced1fd91555c4b51d158273a95265c43904b35a7e10eb92728dc21e7e21eed` |
| Wrong operator-pinned provider 7999 (`wrong-provider/result`) | Refused: original call did not write provider | `a0c845e8db79d833161d86dd610eaa63b070b17c1bc5ea63ff88951b1003ec7a` |
| Accepted same-value provider write (`provider-same-value-write/check`) | Refused after a separate signed `input` write to provider 7004 at count 10 | `62a38f2fe73e26b3862314af0de59d7f20b795d88a637818b13b7d8794fc748d` |

The same-value write reused the exact provider state coordinates and was accepted under the current grant, so the refusal tests **write continuity**, not merely a changed final value. Op17 establishes a refreshed, verifier-minted Mini history check at the time of the read. It is not an atomic lease over a later external send. Runtime must still check the fresh signed parent/provider status, generation, amount, and exact original reserve receipt, and compare the returned provider resource ID with its independently configured task.
