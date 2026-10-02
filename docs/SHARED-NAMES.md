# Shared room names

A room's `ROOM/NAME` reads its current index, rather than treating the local
address book as the public namespace. Give another member the room invitation;
that member does not need a separate local hint for each entry.

```
room new lab
doc new map index --in lab
doc new board --in lab
room index attach-map lab map
room bind name-board lab board board
room resolve lab/board
doc show lab/board
room rename rename-board lab board tasks
```

`room bind ID ROOM NAME TARGET` adds a binding. `room rename ID ROOM OLD NEW`
atomically retires the old link and creates the new one. `room unbind ID ROOM
NAME` retires it. These commands submit ordinary admitted turns and keep the
command ID, resolved object references, authored request and signed attempt.
Repeating an ID with the same command recovers that exact attempt; using the
ID for a different command refuses. No rename rewrites an already opened or
signed object identity.

`ROOM/index` is the reserved name for the map itself. Names contain ASCII
letters, digits and hyphens, with case preserved; dots and slashes are not name
characters. Thus private `lab.board.json` is unambiguously the custody file for
`lab/board`; it is not a second spelling of a name.

The room's declared field 1010 holds its index cell ID. An absent or zero
pointer means no index is configured. Existing rooms whose finite declaration
excludes 1010 need a checked carry or an explicitly new room; this feature does
not hot-expand old declarations or claim data migration by fresh genesis.

The index is a normal hyperdocument. An ordinary external link with scheme
`mini-name`, authority equal to the exact name bytes, path `KIND/ID`, relation
zero and no source range is a binding. KIND is explicitly object, account or
program. The resolver rejects malformed reserved links and duplicate live
names. Text, HTML and JSON render these as internal bindings, never outbound
browser URLs. Private-room binding metadata is not encrypted by this convention;
the private-content mutation guard continues to apply.

The `index` document law requires the source-derived `content/names/unique`
slot to equal one on content mutation. The slot examines all live reserved
links in the final store, including links created by the same command. Retired
links do not reserve names forever. Other document laws can choose differently;
clients still refuse an ambiguous index. This projection changes runtime
semantics (content projection v4), though LinkRecord and content bytes have
not changed format.

Discovery uses current signed capability and resource views. The room read
must cover field1010; the index read must cover annotations. Their world root
and height must agree. Narrowed reads cannot prove absence of an invisible
field. Failure, revocation, malformed records, duplicate names and moved
snapshots all refuse instead of falling back to a private hint. Only an
authenticated absent pointer or absent name allows the private fallback.

A binding conveys no authority. The opened reference uses the room capability
or an existing direct capability on that exact kind and target; the target's
current policy and capability are checked by the ordinary signed-read and
admission path. The first read refuses if discovery moved. Exact retry uses
retained signed bytes without consulting names.

`JNAMES` in the existing journey runner checks two-client lookup from only a
room invitation, map rendering, duplicate-law refusal, rename, exact command
recovery after a later rename, outside-target refusal, and ambiguity refusal
when an authorized operator deliberately relaxes the index law. Rust unit tests
cover malformed bindings, spelling aliases, narrowed reads and moved snapshots.
Native execution is required on a source-matched Host before qualification;
Rust tests alone do not prove admission or deployed naming.
