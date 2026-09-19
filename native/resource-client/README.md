# Mini resource client

`mini` is the physical custody and evidence client for `minidregg-host`. The
Lean host remains the only author of semantic binary values and the only
receiver that decides admission. The Rust process generates and holds raw
Ed25519 keys, signs the host's exact inspected headers, and retains every byte
needed to recover from an uncertain response.

Build it with:

```sh
CARGO_BUILD_JOBS=2 cargo build --manifest-path native/resource-client/Cargo.toml
```

Generate a fresh signer. The secret file is created with mode `0600` on Unix
and existing files are never replaced:

```sh
mini keygen --secret alice.key --public alice.pub
```

The command prints the raw public key as lowercase hex for a source-authored
genesis enrollment. Bootstrap retains the exact source, canonical source
binary, genesis image, pinned config, profile, and post-bootstrap description:

```sh
mini bootstrap \
  --host .lake/build/bin/minidregg-host \
  --config operator.json \
  --source genesis.json \
  --dir deployment
```

`submit` accepts a source-owned observation intent whose purpose is `prepare`.
Its attempt directory contains the observation challenge, signatures, signed
observation, finalized signing plan, transaction signatures, exact signed call,
a retained pinned config, and decoded outcome:

```sh
mini submit --host .lake/build/bin/minidregg-host \
  --config deployment/pinned-config.json \
  --intent birth-intent.json --intent-kind birth-intent \
  --key alice.key --dir attempts/birth-1
```

For a standard birth, pass `--intent-kind birth-intent`. The Lean builder takes
the exact genesis source and native factory template, derives absent cell roots,
neutral declared/content cells, root owner and policy-control grants, policy
addresses, transaction identity, authority nullifier, and the quoted fee. A
resource entry chooses `"storage":"declared"` or `"storage":"content"`; content
birth is an empty canonical content page. Rust never calculates these fields.

Ordinary transaction intents use `purpose.draft.type = "invoke"`. Its command
has one shared `subject`, `expectedAuthorityRoot`, and `nonce`, plus a nonempty
`targets` array. Each target has `kind`, `target`, mutation `capability`,
nullable `observeCapability`, `schemaVersion`, `expectedTargetRoot`, and a
tagged payload:

```json
{
  "type": "content",
  "actions": [
    {"type": "createAtom", "atom": "7001", "kind": {"type": "text"}, "payload": "68656c6c6f"}
  ]
}
```

The sibling payload type `scalar` carries the existing create/write/move
actions. One command may mix scalar and content targets; Lean constructs the
single flat transaction and requires distinct physical target IDs. Every
target of a command with more than one target must name an actual current read
grant in `observeCapability`. The host obtains and checks those read signatures
again at submission before any resource policy can inspect another target. A
singleton uses `null` because it has no foreign participant to observe.

After a lost or uncertain response, this command reuses `call.bin` byte for
byte. Each response gets a new evidence filename and earlier evidence is kept:

```sh
mini retry --attempt attempts/birth-1 --mode submit
mini retry --attempt attempts/birth-1 --mode lookup
```

Authorized inspection follows the same challenge/sign/query path:

```sh
mini query --host .lake/build/bin/minidregg-host \
  --config deployment/pinned-config.json \
  --intent inspect-resource.json --key alice.key --view resource \
  --dir attempts/query-1
```

New source families use the generic author bridge, including `birth`,
`policy-install`, `delegation`, `joint`, `content`, and `revocation` as their
corresponding host author kinds land. Rust passes the JSON to Lean unchanged:

```sh
mini author --host .lake/build/bin/minidregg-host \
  --config deployment/pinned-config.json \
  --kind content --input content-operation.json --output content-operation.bin
```

The `*-draft` kinds return canonical `NativeHostCodec.Draft` bytes. They are
useful for inspecting or integrating with another transport; normal `submit`
accepts an `intent` JSON that embeds the corresponding friendly source form.
The friendly `purpose.draft` constructors are:

| `type` | Source fields |
| --- | --- |
| `invoke` | `command` with shared subject/root/nonce and typed targets |
| `install-source` | `subject`, `control`, and a policy `declaration` |
| `delegate-source` | source-owned delegation `command` |
| `revoke-source` | source-owned revocation `command` |

A policy declaration supplies `expectedPreRoot`, nullable current `expected`
head, `nonce`, and a full policy record. Delegation supplies `kind`, `domain`,
`semantics`, `subject`, `nonce`, `expectedTargetRoot`, the complete child
capability, `parentId`, `target`, and `expectedPreRoot`; Lean derives its
operation marker. Revocation supplies the actual target `kind`, `subject`,
`nonce`, `target`, `victimKind`, victim `capability`, `controlCapability`, and
both expected roots. Program control grants use distinct `installPolicy` and
`revokeCapability` verbs.

Content payload actions are `createDocument`, `createAtom`, `createRun`,
`editAtom`, and `link`. Byte payloads are lowercase or uppercase even-length
hex; identifiers and unbounded integers are canonical decimal strings. Atom
edits carry the complete observed old record, so the source receiver can reject
a stale replacement without trusting a Rust-side reconstruction.

The bounded acceptance journey creates a new signer and deployment, authors a
canonical content birth, submits a typed singleton content mutation, performs
authorized queries, and checks byte-identical submit and receipt retries. It
requires `jq` plus the already-built native storage and signature helpers, and
refuses to reuse its evidence directory:

```sh
native/resource-client/acceptance.sh .lake/build/bin/minidregg-host /tmp/mini-acceptance
```
