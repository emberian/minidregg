//! A0: the structured command grammar (docs/WEB-FRONTEND-2026-10-27.md §6; DEMO-EXPERIENCE A0).
//! ONE description of a verb, as data, that the shell's parsing, `help`, Tab completion and the
//! web body's forms all consume: its leaves (`doc append`), each leaf's typed positional
//! arguments, its flags (and which ones are dangerous and need an explicit confirmation), its
//! effect (local, a read, a proposal, a transition) and the words of its operation. The `usage`
//! and `operation` strings the rest of the shell still reads are RENDERED from here, by one
//! printer, so help cannot drift from the parser; the parser arm of a converted verb takes typed
//! values from [`parse`] instead of counting words. Verbs land here one by one (`doc` first);
//! until a verb is here its hand-written `Verb` row and arity checks stand.

use crate::workspace::validate_ref_name;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Kind {
    /// A proposal or attempt id: 1..64 letters, digits or hyphens.
    Id,
    /// A reference name of this workspace (`lab/index` allowed).
    Ref,
    /// A subject number.
    Subject,
    /// A decimal number (a line, a height, a count, a relation).
    Number,
    /// Text given inline or as `@FILE` under `HOME/requests` (1..4096 bytes).
    TextOrFile,
    /// `@FILE` under `HOME/requests`, only.
    File,
    /// A plain file name under HOME/keys (`mini.key`, `next.key`): no path, no leading dot.
    KeyFile,
    /// `@FILE` or `@-` (standard input).
    FileOrStdin,
    /// A law: a quoted clause list, predicate JSON, `@FILE`, or a stock name.
    Law,
    /// One of these literal words.
    Choice(&'static [&'static str]),
    /// Any single word.
    Word,
    /// The rest of the raw line, untouched (free text: apostrophes and `#` need no quoting; the
    /// verb removes one pair of outer quotes). Always the last argument; parsed by [`parse_line`].
    Rest,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Effect {
    /// Decided by the client alone: no Host call.
    Local,
    /// A signed read or view: an answer, never an admission.
    Read,
    /// A proposal, retained under its id; `submit ID` is the transition.
    Propose,
    /// A world transition the client submits itself.
    Transition,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Arg {
    pub name: &'static str,
    pub kind: Kind,
    pub optional: bool,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Flag {
    pub name: &'static str,
    /// The leaf refuses without it (`room welcome … --template T`, `room seal … --freeze-roster`);
    /// the usage prints it unbracketed and the form marks the field required.
    pub required: bool,
    /// A flag with a value names its placeholder and kind; without one it is a switch.
    pub value: Option<(&'static str, Kind)>,
    /// A dangerous switch (`--i-know`, `--freeze-roster`): the form asks for an explicit tick.
    pub dangerous: bool,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Leaf {
    /// The literal words that name the leaf, the verb first.
    pub path: &'static [&'static str],
    pub args: &'static [Arg],
    pub flags: &'static [Flag],
    pub effect: Effect,
    /// The words of the operation (what `help VERB` prints after `=`).
    pub about: &'static str,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Grammar {
    pub verb: &'static str,
    pub leaves: &'static [Leaf],
}

const fn arg(name: &'static str, kind: Kind) -> Arg {
    Arg { name, kind, optional: false }
}
const fn opt(name: &'static str, kind: Kind) -> Arg {
    Arg { name, kind, optional: true }
}
const fn switch(name: &'static str) -> Flag {
    Flag { name, required: false, value: None, dangerous: false }
}
const fn valued(name: &'static str, placeholder: &'static str, kind: Kind) -> Flag {
    Flag { name, required: false, value: Some((placeholder, kind)), dangerous: false }
}
/// The same flag, required.
const fn req(f: Flag) -> Flag {
    Flag { required: true, ..f }
}

const JSON_OR_HTML: &[Flag] = &[switch("--json"), switch("--html")];

/// `doc`: the forty leaves of the document verb.
pub static DOC: Grammar = Grammar {
    verb: "doc",
    leaves: &[
        Leaf { path: &["doc", "app-export", "capture"], args: &[arg("ID", Kind::Id), arg("@FILE", Kind::File)], flags: &[], effect: Effect::Transition, about: "mini workspace --action app-document --op capture (the app's export binding from HOME/requests)" },
        Leaf { path: &["doc", "app-export"], args: &[arg("publish|status|recover", Kind::Choice(&["publish", "status", "recover"])), arg("ID", Kind::Id)], flags: &[], effect: Effect::Transition, about: "mini workspace --action app-document --op publish|status|recover" },
        Leaf { path: &["doc", "app-export", "rebase"], args: &[arg("ID", Kind::Id), arg("NEXT", Kind::Id)], flags: &[], effect: Effect::Transition, about: "mini workspace --action app-document --op rebase --next NEXT" },
        Leaf { path: &["doc", "search"], args: &[arg("QUERY", Kind::Word), arg("NAME[,NAME...]|@held", Kind::Word), opt("OFFSET", Kind::Number), opt("CURSOR", Kind::Word)], flags: &[], effect: Effect::Read, about: "mini workspace --action doc-search (OFFSET and CURSOR together continue a page)" },
        Leaf { path: &["doc", "hit"], args: &[arg("NAME", Kind::Ref), arg("DOCUMENT", Kind::Word), arg("ATOM", Kind::Number), arg("REVISION", Kind::Number)], flags: &[], effect: Effect::Read, about: "mini workspace --action doc-search-follow" },
        Leaf { path: &["doc", "device"], args: &[], flags: &[], effect: Effect::Local, about: "mini workspace --action doc-device" },
        Leaf { path: &["doc", "share"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Ref), arg("SUBJECT", Kind::Subject), arg("@DEVICE", Kind::File), arg("@INVITATION", Kind::File)], flags: &[], effect: Effect::Transition, about: "mini workspace --action doc-share (the device record and the invitation under HOME/requests)" },
        Leaf { path: &["doc", "accept"], args: &[arg("NAME", Kind::Ref), arg("CATALOG", Kind::Ref), arg("@INVITATION", Kind::File)], flags: &[], effect: Effect::Transition, about: "mini workspace --action doc-accept" },
        Leaf { path: &["doc", "revoke"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Ref), arg("SUBJECT", Kind::Subject)], flags: &[], effect: Effect::Transition, about: "mini workspace --action doc-revoke" },
        Leaf { path: &["doc", "membership-recover"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Ref), opt("@INVITATION", Kind::File)], flags: &[], effect: Effect::Transition, about: "mini workspace --action doc-membership-recover" },
        Leaf { path: &["doc", "protect"], args: &[arg("NAME", Kind::Ref)], flags: &[], effect: Effect::Transition, about: "mini workspace --action doc-protect" },
        Leaf { path: &["doc", "protect-current"], args: &[arg("NAME", Kind::Ref)], flags: &[], effect: Effect::Transition, about: "mini workspace --action doc-protect-current" },
        Leaf { path: &["doc", "protect-recover"], args: &[arg("NAME", Kind::Ref)], flags: &[], effect: Effect::Transition, about: "mini workspace --action doc-protect-recover" },
        Leaf { path: &["doc", "epoch-export"], args: &[arg("NAME", Kind::Ref), arg("@FILE", Kind::File)], flags: &[], effect: Effect::Local, about: "mini workspace --action doc-epoch-export (the bundle to HOME/requests/FILE)" },
        Leaf { path: &["doc", "epoch-import"], args: &[arg("NAME", Kind::Ref), arg("CATALOG", Kind::Ref), arg("@FILE", Kind::File)], flags: &[], effect: Effect::Transition, about: "mini workspace --action doc-epoch-import" },
        Leaf { path: &["doc", "context"], args: &[arg("NAME", Kind::Ref), opt("MAX-ROWS", Kind::Number), opt("MAX-BYTES", Kind::Number)], flags: &[], effect: Effect::Read, about: "mini workspace --action doc-context (a bounded context of the document for a reviewer)" },
        Leaf { path: &["doc", "review"], args: &[arg("ID", Kind::Id), arg("@CONTEXT", Kind::File), arg("@REQUEST", Kind::File)], flags: &[], effect: Effect::Transition, about: "mini workspace --action context-review" },
        Leaf { path: &["doc", "new"], args: &[arg("NAME", Kind::Ref), opt("draft|note|index|LAW", Kind::Law)], flags: &[valued("--in", "ROOM", Kind::Ref)], effect: Effect::Transition, about: "mini workspace --action doc-new (a content cell and its document; the law stock or your own)" },
        Leaf { path: &["doc", "show"], args: &[arg("NAME", Kind::Ref)], flags: &[valued("--at", "H", Kind::Number), switch("--raw"), switch("--json"), switch("--html")], effect: Effect::Read, about: "doc-show [--at H] [--format raw|json|html]" },
        Leaf { path: &["doc", "outline"], args: &[arg("NAME", Kind::Ref)], flags: &[], effect: Effect::Read, about: "doc-outline" },
        Leaf { path: &["doc", "history"], args: &[arg("NAME", Kind::Ref)], flags: JSON_OR_HTML, effect: Effect::Read, about: "doc-history" },
        Leaf { path: &["doc", "diff"], args: &[arg("NAME", Kind::Ref), arg("H1", Kind::Number), arg("H2", Kind::Number)], flags: JSON_OR_HTML, effect: Effect::Read, about: "doc-diff" },
        Leaf { path: &["doc", "pull"], args: &[arg("NAME", Kind::Ref)], flags: &[], effect: Effect::Read, about: "doc-pull (the document to HOME, line by line, for a later push)" },
        Leaf { path: &["doc", "push"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Ref), arg("@FILE|@-", Kind::FileOrStdin)], flags: &[], effect: Effect::Transition, about: "doc-push (propose payload document: push, then submit)" },
        Leaf { path: &["doc", "append"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Ref), arg("TEXT|@FILE", Kind::TextOrFile)], flags: &[], effect: Effect::Propose, about: "propose (payload document: append)" },
        Leaf { path: &["doc", "edit"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Ref), arg("LINE", Kind::Number), arg("TEXT|@FILE", Kind::TextOrFile)], flags: &[], effect: Effect::Propose, about: "propose (payload document: edit)" },
        Leaf { path: &["doc", "insert"], args: &[arg("NAME", Kind::Ref), arg("N", Kind::Number), arg("TEXT|@FILE", Kind::TextOrFile)], flags: &[], effect: Effect::Transition, about: "doc-insert" },
        Leaf { path: &["doc", "move"], args: &[arg("NAME", Kind::Ref), arg("FROM", Kind::Number), arg("TO", Kind::Number)], flags: &[], effect: Effect::Transition, about: "doc-move" },
        Leaf { path: &["doc", "remove"], args: &[arg("NAME", Kind::Ref), arg("N", Kind::Number)], flags: &[], effect: Effect::Transition, about: "doc-remove" },
        Leaf { path: &["doc", "mark"], args: &[arg("NAME", Kind::Ref), arg("LINE", Kind::Number), arg("bold|italic|code|heading", Kind::Choice(&["bold", "italic", "code", "heading"]))], flags: &[], effect: Effect::Transition, about: "mark (a style on one line)" },
        Leaf { path: &["doc", "mark"], args: &[arg("NAME", Kind::Ref), arg("LINE", Kind::Number), arg("link", Kind::Choice(&["link"])), arg("TARGET", Kind::Word)], flags: &[], effect: Effect::Transition, about: "mark (a link on one line to TARGET)" },
        Leaf { path: &["doc", "unmark"], args: &[arg("NAME", Kind::Ref), arg("MARK|LINE", Kind::Number), opt("KIND", Kind::Choice(&["bold", "italic", "code", "heading", "link"]))], flags: &[], effect: Effect::Transition, about: "unmark (MARK, or LINE KIND)" },
        Leaf { path: &["doc", "annotate"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Ref), arg("LINE", Kind::Number), arg("TEXT|@FILE", Kind::TextOrFile)], flags: &[], effect: Effect::Propose, about: "propose (payload document: annotate)" },
        Leaf { path: &["doc", "link"], args: &[arg("ID", Kind::Id), arg("FROM", Kind::Ref), arg("TO", Kind::Ref), opt("RELATION", Kind::Number)], flags: &[], effect: Effect::Propose, about: "propose (payload document: link)" },
        Leaf { path: &["doc", "links"], args: &[arg("NAME", Kind::Ref)], flags: &[], effect: Effect::Read, about: "doc-links (the Host's link index)" },
        Leaf { path: &["doc", "backlinks"], args: &[arg("NAME", Kind::Ref)], flags: &[], effect: Effect::Read, about: "doc-backlinks (the Host's link index)" },
        Leaf { path: &["doc", "range"], args: &[arg("NAME", Kind::Ref), arg("FROM", Kind::Number), arg("TO", Kind::Number)], flags: &[], effect: Effect::Transition, about: "doc-range (createRun)" },
        Leaf { path: &["doc", "transclude"], args: &[arg("NAME", Kind::Ref), arg("SOURCE", Kind::Ref), arg("FROM", Kind::Number), arg("TO", Kind::Number), opt("snapshot|live", Kind::Choice(&["snapshot", "live"])), opt("at", Kind::Choice(&["at"])), opt("N", Kind::Number)], flags: &[], effect: Effect::Transition, about: "transclude (--from-line --to-line)" },
        Leaf { path: &["doc", "transclusions"], args: &[arg("NAME", Kind::Ref)], flags: &[], effect: Effect::Read, about: "transclusions" },
        Leaf { path: &["doc", "follow"], args: &[arg("NAME", Kind::Ref), arg("T", Kind::Number)], flags: &[], effect: Effect::Read, about: "follow" },
    ],
};

const fn dangerous(name: &'static str) -> Flag {
    Flag { name, required: false, value: None, dangerous: true }
}

/// `room`: a room's names, its birth, its roster, its keys (private rooms), its economy.
pub static ROOM: Grammar = Grammar {
    verb: "room",
    leaves: &[
        Leaf { path: &["room", "index"], args: &[arg("ID", Kind::Id), arg("ROOM", Kind::Ref), arg("INDEX-DOC", Kind::Ref)], flags: &[], effect: Effect::Transition, about: "mini workspace --action shared-name --op attach (the room's index document)" },
        Leaf { path: &["room", "bind"], args: &[arg("ID", Kind::Id), arg("ROOM", Kind::Ref), arg("NAME", Kind::Id), arg("TARGET", Kind::Word)], flags: &[], effect: Effect::Transition, about: "shared-name --op bind" },
        Leaf { path: &["room", "rename"], args: &[arg("ID", Kind::Id), arg("ROOM", Kind::Ref), arg("NAME", Kind::Id), arg("NEW-NAME", Kind::Word)], flags: &[], effect: Effect::Transition, about: "shared-name --op rename" },
        Leaf { path: &["room", "unbind"], args: &[arg("ID", Kind::Id), arg("ROOM", Kind::Ref), arg("NAME", Kind::Id)], flags: &[], effect: Effect::Transition, about: "shared-name --op unbind" },
        Leaf { path: &["room", "resolve"], args: &[arg("ROOM/NAME", Kind::Ref)], flags: &[], effect: Effect::Read, about: "shared-name --op resolve" },
        Leaf { path: &["room", "new"], args: &[arg("NAME", Kind::Ref)], flags: &[valued("--law", "open|realm", Kind::Choice(&["open", "realm"])), valued("--referee", "SUBJECT", Kind::Subject), valued("--in", "PARENT", Kind::Ref), switch("--private"), valued("--template", "T|@FILE", Kind::Word), valued("--concierge", "SUBJECT", Kind::Subject), valued("--period", "N", Kind::Number)], effect: Effect::Transition, about: "mini workspace --action create (storage declared, the room's law, --room-template LAW); --private: the private room's law, its keys cell and your own wrap [DEVNET QUALITY; PRIVACY NOT AUDITED]; --template: the template's lines, each one typed line, in order; --concierge: the room's lines, then `room concierge`" },
        Leaf { path: &["room", "welcome"], args: &[arg("NAME", Kind::Id), arg("SUBJECT", Kind::Subject)], flags: &[req(valued("--template", "T|@FILE", Kind::Word))], effect: Effect::Transition, about: "the template's member lines" },
        Leaf { path: &["room", "template", "list"], args: &[], flags: &[], effect: Effect::Local, about: "local: the room templates" },
        Leaf { path: &["room", "template", "show"], args: &[arg("T|@FILE", Kind::Word), opt("member", Kind::Choice(&["member"]))], flags: &[], effect: Effect::Local, about: "local: print the template file (its room lines, or its member lines)" },
        Leaf { path: &["room", "invite"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Ref), arg("SUBJECT", Kind::Subject)], flags: &[valued("--verbs", "V,...", Kind::Word), valued("--fields", "F,...", Kind::Word), valued("--max-delta", "F=N,...", Kind::Word), valued("--max-cost", "N", Kind::Number)], effect: Effect::Propose, about: "propose (action delegate on the room: an open room's invitation)" },
        Leaf { path: &["room", "invite"], args: &[arg("ID", Kind::Id), arg("PRIVATE-ROOM", Kind::Ref), arg("SUBJECT", Kind::Subject), arg("DECLARATION|KEY-ID|@FILE", Kind::Word)], flags: &[switch("--past"), dangerous("--i-know"), valued("--verbs", "V,...", Kind::Word), valued("--fields", "F,...", Kind::Word), valued("--max-delta", "F=N,...", Kind::Word), valued("--max-cost", "N", Kind::Number)], effect: Effect::Propose, about: "propose (action delegate, room: true; private: room-key --op invite, which also releases the room key to the invitee's hybrid X25519 + ML-KEM-768 key in one keys write)" },
        Leaf { path: &["room", "kick"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Ref), arg("SUBJECT", Kind::Subject)], flags: &[], effect: Effect::Propose, about: "room-kick: one revoke per standing grant SUBJECT holds under NAME (the Host's signed who view), proposed; `submit ID` submits them all (private: room-key --op kick = every revoke + rotate + rewrap, submitted)" },
        Leaf { path: &["room", "seal"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Ref)], flags: &[req(dangerous("--freeze-roster"))], effect: Effect::Propose, about: "propose (action install-policy, `sealed`): sealing a room freezes its membership forever, so it needs --freeze-roster" },
        Leaf { path: &["room", "rotate"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Id)], flags: &[], effect: Effect::Transition, about: "room-key --op rotate" },
        Leaf { path: &["room", "transition"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Id), arg("NEXTFILE", Kind::KeyFile)], flags: &[], effect: Effect::Transition, about: "room-key --op transition (founder: hand the room to your next signing key before rotate-key)" },
        Leaf { path: &["room", "register"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Id)], flags: &[], effect: Effect::Transition, about: "room-key --op register (publish my current encryption key as my record)" },
        Leaf { path: &["room", "rewrap"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Id), arg("SUBJECT", Kind::Subject)], flags: &[], effect: Effect::Transition, about: "room-key --op rewrap" },
        Leaf { path: &["room", "keys"], args: &[arg("NAME", Kind::Id)], flags: &[], effect: Effect::Local, about: "room-key --op list (local)" },
        Leaf { path: &["room", "leave"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Id)], flags: &[], effect: Effect::Propose, about: "propose (action renounce, leave: your room grant)" },
        Leaf { path: &["room", "members"], args: &[arg("NAME", Kind::Ref)], flags: &[], effect: Effect::Read, about: "who" },
        Leaf { path: &["room", "list"], args: &[], flags: &[], effect: Effect::Local, about: "local: references that are rooms" },
        Leaf { path: &["room", "ls"], args: &[opt("ROOM", Kind::Ref)], flags: &[valued("--since", "H", Kind::Number), switch("--import"), switch("--json")], effect: Effect::Read, about: "chat: the Host's signed since view under the room grant, with the roster's streams and my names (--import names the rest ROOM-cell-ID)" },
        Leaf { path: &["room", "law"], args: &[arg("NAME", Kind::Ref)], flags: &[], effect: Effect::Read, about: "describe" },
        Leaf { path: &["room", "status"], args: &[arg("NAME", Kind::Ref)], flags: &[], effect: Effect::Read, about: "mini credit --action status (my window, the tariff, the till; adopts a newer window from HOME/inbox)" },
        Leaf { path: &["room", "renew"], args: &[arg("NAME", Kind::Ref), arg("SUBJECT", Kind::Subject)], flags: &[valued("--for", "N", Kind::Number), valued("--until", "H", Kind::Number)], effect: Effect::Transition, about: "mini credit --action renew (one delegation under the room with notAfter; copy in HOME/outbox/SUBJECT)" },
        Leaf { path: &["room", "concierge"], args: &[arg("NAME", Kind::Id), arg("SUBJECT", Kind::Subject)], flags: &[valued("--period", "N", Kind::Number), valued("--fund", "N", Kind::Number)], effect: Effect::Transition, about: "mini credit --action install (the till, the runner account, the tariff's account fields, the concierge's grants; program in HOME/concierge/NAME.json)" },
    ],
};

const PROPOSAL: &str = "minidregg-workspace-proposal-v1";
const _: &str = PROPOSAL;

pub static DELEGATE: Grammar = Grammar { verb: "delegate", leaves: &[
    Leaf { path: &["delegate"], args: &[arg("ID", Kind::Id), arg("REF", Kind::Ref), arg("RECIPIENT", Kind::Subject), arg("VERB[,VERB...]", Kind::Word), arg("MAX-COST", Kind::Number)], flags: &[valued("--until", "H", Kind::Number)], effect: Effect::Propose, about: "mini workspace --action propose (action delegate; --until H: the grant's notAfter height)" },
] };
pub static REVOKE: Grammar = Grammar { verb: "revoke", leaves: &[
    Leaf { path: &["revoke"], args: &[arg("ID", Kind::Id), arg("REF", Kind::Ref), arg("RECIPIENT", Kind::Subject)], flags: &[], effect: Effect::Propose, about: "mini workspace --action propose (action revoke: the capability this workspace delegated on REF to RECIPIENT)" },
] };
pub static RENOUNCE: Grammar = Grammar { verb: "renounce", leaves: &[
    Leaf { path: &["renounce"], args: &[arg("ID", Kind::Id), arg("REF", Kind::Ref)], flags: &[], effect: Effect::Propose, about: "mini workspace --action propose (action renounce: give up a capability you hold, and with it everything delegated from it)" },
    Leaf { path: &["renounce"], args: &[arg("ID", Kind::Id), arg("CAPABILITY", Kind::Subject), arg("object|account|program", Kind::Choice(&["object", "account", "program"]))], flags: &[], effect: Effect::Propose, about: "propose (action renounce, by capability id and kind; the kind is required: without it the number reads as a reference name)" },
] };
pub static LAW: Grammar = Grammar { verb: "law", leaves: &[
    Leaf { path: &["law", "show"], args: &[arg("REF", Kind::Ref)], flags: &[], effect: Effect::Read, about: "the installed law from the signed policy view, as the Host prints it" },
    Leaf { path: &["law", "export", "show"], args: &[arg("REF", Kind::Ref)], flags: &[], effect: Effect::Read, about: "mini workspace --action law-export-show" },
    Leaf { path: &["law", "export"], args: &[arg("ID", Kind::Id), arg("REF", Kind::Ref), arg("COMPONENT-JSON|@FILE|none", Kind::Word)], flags: &[], effect: Effect::Propose, about: "propose (action install-export: the law component descendants inherit)" },
    Leaf { path: &["law", "check"], args: &[arg("\"CLAUSE; …\"|PREDICATE-JSON|@FILE|-", Kind::Law)], flags: &[], effect: Effect::Read, about: "mini workspace --action law-check: whether the law can ever pass (Host op 150), nothing installed" },
    Leaf { path: &["law"], args: &[arg("ID", Kind::Id), arg("REF", Kind::Ref), arg("\"CLAUSE; CLAUSE; …\"|PREDICATE-JSON|@FILE", Kind::Law)], flags: &[dangerous("--allow-unsatisfiable"), dangerous("--i-lock-myself-out"), dangerous("--freeze-roster")], effect: Effect::Propose, about: "mini workspace --action propose (action install-policy), after asking the Host whether the law can ever pass (op 150); the three switches are explicit consent to an unsatisfiable law, to locking yourself out, to freezing a room's roster" },
] };
pub static PAY: Grammar = Grammar { verb: "pay", leaves: &[
    Leaf { path: &["pay", "address"], args: &[opt("ACCOUNT-REF", Kind::Id)], flags: &[], effect: Effect::Read, about: "mini pay --action address" },
    Leaf { path: &["pay", "status"], args: &[opt("ACCOUNT-REF", Kind::Id)], flags: &[], effect: Effect::Read, about: "mini pay --action status" },
    Leaf { path: &["pay", "audit"], args: &[], flags: &[], effect: Effect::Read, about: "mini pay --action audit" },
    Leaf { path: &["pay"], args: &[arg("ROOM", Kind::Ref), arg("week|N", Kind::Word), opt("again", Kind::Choice(&["again"]))], flags: &[valued("--account", "REF", Kind::Id)], effect: Effect::Transition, about: "mini credit --action pay --room ROOM [--amount N] (one fleet turn: N, or the room's week, to its till, publishing renew; a free room files a request in HOME/outbox; `again` pays once more)" },
] };
pub static CREDIT: Grammar = Grammar { verb: "credit", leaves: &[
    Leaf { path: &["credit"], args: &[opt("ACCOUNT-REF", Kind::Id)], flags: &[], effect: Effect::Read, about: "mini credit --action balance (a signed read of my account)" },
] };
pub static TARIFF: Grammar = Grammar { verb: "tariff", leaves: &[
    Leaf { path: &["tariff"], args: &[arg("ROOM", Kind::Ref)], flags: &[], effect: Effect::Read, about: "mini credit --action tariff --room ROOM (a signed read of the room cell's tariff fields)" },
    Leaf { path: &["tariff"], args: &[arg("ROOM", Kind::Ref), arg("set", Kind::Choice(&["set"])), arg("week|birth|hermes/turn|period|open|hermes/provider|hermes/tools|hermes/compute", Kind::Choice(&["week", "birth", "hermes/turn", "period", "open", "hermes/provider", "hermes/tools", "hermes/compute"])), arg("N", Kind::Number)], flags: &[], effect: Effect::Transition, about: "mini credit --action tariff --set FIELD --value N (one scalar turn on the room cell: only its founder holds write)" },
] };
pub static TOPUP: Grammar = Grammar { verb: "topup", leaves: &[
    Leaf { path: &["topup"], args: &[arg("ROOM", Kind::Ref), arg("N", Kind::Number), opt("hermes|concierge", Kind::Choice(&["hermes", "concierge"])), opt("again", Kind::Choice(&["again"]))], flags: &[valued("--account", "REF", Kind::Id)], effect: Effect::Transition, about: "mini credit --action topup --room ROOM --amount N [--to hermes|concierge] (one fleet transfer to Hermes's budget account when the room has a Hermes, else to the concierge's runner account)" },
] };
pub static MARKET: Grammar = Grammar { verb: "market", leaves: &[
    Leaf { path: &["market", "open"], args: &[arg("NAME", Kind::Id), arg("CLOSE", Kind::Number), arg("REVEAL-END", Kind::Number), arg("SUPPLY", Kind::Number)], flags: &[], effect: Effect::Transition, about: "mini workspace --action market-open" },
    Leaf { path: &["market", "settle"], args: &[arg("MARKET", Kind::Id), opt("ID", Kind::Id)], flags: &[], effect: Effect::Transition, about: "mini workspace --action market-settle" },
] };
pub static BID: Grammar = Grammar { verb: "bid", leaves: &[
    Leaf { path: &["bid"], args: &[arg("MARKET", Kind::Id), arg("PRICE", Kind::Number), arg("QTY", Kind::Number), opt("ID", Kind::Id)], flags: &[], effect: Effect::Transition, about: "mini workspace --action market-bid (a sealed bid)" },
] };
pub static REVEAL: Grammar = Grammar { verb: "reveal", leaves: &[
    Leaf { path: &["reveal"], args: &[arg("MARKET", Kind::Id), opt("ID", Kind::Id)], flags: &[], effect: Effect::Transition, about: "mini workspace --action market-reveal" },
] };
pub static BIDS: Grammar = Grammar { verb: "bids", leaves: &[
    Leaf { path: &["bids"], args: &[arg("MARKET", Kind::Id)], flags: &[], effect: Effect::Read, about: "mini workspace --action market-bids: a signed read, sealed bids shown as commitments" },
] };
const JOB_ACCOUNT: Flag = valued("--account", "REF", Kind::Word);
const JOB_NAME: Flag = valued("--name", "NAME", Kind::Word);
pub static JOB: Grammar = Grammar { verb: "job", leaves: &[
    Leaf { path: &["job", "post"], args: &[arg("ROOM", Kind::Word), arg("PROGRAM", Kind::Word)], flags: &[valued("--input", "N", Kind::Number), valued("--price", "P", Kind::Number), valued("--deadline", "SECONDS", Kind::Number), JOB_ACCOUNT, valued("--window", "SECONDS", Kind::Number), JOB_NAME], effect: Effect::Transition, about: "mini job --action post" },
    Leaf { path: &["job", "claim"], args: &[arg("JOB", Kind::Word)], flags: &[valued("--room", "ROOM", Kind::Word), valued("--bond", "B", Kind::Number), JOB_ACCOUNT, JOB_NAME], effect: Effect::Transition, about: "mini job --action claim" },
    Leaf { path: &["job", "answer"], args: &[arg("NAME", Kind::Word), opt("OUTPUT", Kind::Word)], flags: &[], effect: Effect::Transition, about: "mini job --action answer" },
    Leaf { path: &["job", "check"], args: &[arg("NAME", Kind::Word)], flags: &[], effect: Effect::Read, about: "mini job --action check" },
    Leaf { path: &["job", "settle"], args: &[arg("NAME", Kind::Word)], flags: &[], effect: Effect::Transition, about: "mini job --action settle" },
    Leaf { path: &["job", "show"], args: &[arg("NAME", Kind::Word)], flags: &[], effect: Effect::Read, about: "mini job --action show" },
    Leaf { path: &["job", "fund"], args: &[arg("NAME", Kind::Word)], flags: &[JOB_ACCOUNT], effect: Effect::Transition, about: "mini job --action fund" },
    Leaf { path: &["job", "truth"], args: &[arg("NAME", Kind::Word)], flags: &[], effect: Effect::Read, about: "mini job --action truth" },
] };
pub static BEND: Grammar = Grammar { verb: "bend", leaves: &[
    Leaf { path: &["bend", "publish"], args: &[arg("NAME", Kind::Id), arg("@FILE", Kind::File)], flags: &[valued("--entry", "DEF", Kind::Word), valued("--account", "REF", Kind::Word), dangerous("--lose-reply-once")], effect: Effect::Transition, about: "mini bend --action publish: the Objective Bend source in HOME/requests, captured and lowered by the Host's own front end, then published (one activity turn) from my account; NAME is the bend, DEF its entry definition (default NAME)" },
    Leaf { path: &["bend", "run"], args: &[arg("NAME", Kind::Id), arg("OBJECT", Kind::Ref)], flags: &[valued("--seed", "JSON", Kind::Word), valued("--input", "JSON", Kind::Word), valued("--deposit", "N", Kind::Number), valued("--state-type", "JSON", Kind::Word), valued("--account", "REF", Kind::Word), dangerous("--lose-reply-once")], effect: Effect::Transition, about: "mini bend --action run: create OBJECT pinning the published bend when it has no record, then birth its activity under a full envelope (INPUT: the program's start value, default the Tally's; DEPOSIT: the activity's purse, default four envelope prices: each await escrows a pair, each delivered reply spends one, and one covers the record's storage, so the default carries one answer through to the end; a program answered more often needs a larger deposit, and the unspent purse returns when it ends)" },
    Leaf { path: &["bend", "lookup"], args: &[arg("NAME", Kind::Id)], flags: &[], effect: Effect::Read, about: "mini bend --action lookup: the receipt-only lookup (Host op 213) of the retained ingress of NAME's last publish or run attempt; absence never submits (--lose-reply-once on publish or run: a client-side fault that writes the exact call and never reads the answer)" },
    Leaf { path: &["bend", "retry"], args: &[arg("NAME", Kind::Id)], flags: &[], effect: Effect::Transition, about: "mini bend --action retry: the exact retained bytes of NAME's last attempt submitted again (a replay, never a new nonce)" },
    Leaf { path: &["bend", "show"], args: &[arg("OBJECT", Kind::Ref)], flags: &[], effect: Effect::Read, about: "mini bend --action show: the public view of OBJECT (its pin, declared state, activity record and purse)" },
    Leaf { path: &["bend", "await"], args: &[arg("OBJECT", Kind::Word), arg("TRANSACTION", Kind::Word)], flags: &[], effect: Effect::Read, about: "mini bend --action await: the activity a birth TRANSACTION made on object cell OBJECT, as JSON: its phase and, while it awaits a reply, the answer slot, its decider and deadline, and the object's declared state; `height` is the height the next turn is judged at, the clock the deadline and every receipt's height are on (an answer is admitted while it is at most the deadline)" },
    Leaf { path: &["bend", "answer"], args: &[arg("SLOT", Kind::Word), arg("@FILE", Kind::File)], flags: &[], effect: Effect::Transition, about: "mini bend --action answer: decide answer slot SLOT with the answer in HOME/requests/FILE ({\"reply\": DATA} | {\"refused\": REASON}), one resolve turn signed by me; only the slot's decider is admitted (notDecider), once (a decided slot refuses)" },
    Leaf { path: &["bend", "deliver"], args: &[arg("OBJECT", Kind::Word), arg("TRANSACTION", Kind::Word)], flags: &[valued("--account", "REF", Kind::Word)], effect: Effect::Transition, about: "mini bend --action deliver: resume the activity a birth TRANSACTION made on object cell OBJECT with the settled outcome of its await (the decider's answer, or timedOut past the deadline), one deliver turn paid from my account; anyone may deliver, once per await" },
    Leaf { path: &["bend", "settle"], args: &[], flags: &[valued("--account", "REF", Kind::Word)], effect: Effect::Transition, about: "mini bend --action settle: deliver every activity I ran whose await is past its deadline (timedOut, or the answer decided in time), so it reaches its end and its purse returns; one deliver turn each, paid from my account; the door runs it for every member on its tick" },
] };
pub static JOBS: Grammar = Grammar { verb: "jobs", leaves: &[
    Leaf { path: &["jobs"], args: &[arg("ROOM", Kind::Id)], flags: &[], effect: Effect::Read, about: "mini job --action list --dir WS --room ROOM" },
] };

// The attempt lifecycle, the reads and the local verbs.
pub static PROPOSE: Grammar = Grammar { verb: "propose", leaves: &[
    Leaf { path: &["propose"], args: &[arg("ID", Kind::Id), arg("REQUEST-JSON|@FILE", Kind::Word)], flags: &[], effect: Effect::Propose, about: "mini workspace --action propose --request (the request as JSON or @FILE in HOME/requests); `submit ID` is the transition" },
] };
pub static SUBMIT: Grammar = Grammar { verb: "submit", leaves: &[
    Leaf { path: &["submit"], args: &[arg("ID", Kind::Id)], flags: &[dangerous("--lose-reply-once")], effect: Effect::Transition, about: "mini workspace --action submit --intent proposals/ID/intent.json --attempt attempts/ID (--lose-reply-once: a client-side fault that writes the exact call and never reads the answer; the attempt is retained undecided and `lookup`/`retry` ask for the same decided outcome)" },
] };
pub static LOOKUP: Grammar = Grammar { verb: "lookup", leaves: &[
    Leaf { path: &["lookup"], args: &[arg("ID", Kind::Id)], flags: &[], effect: Effect::Transition, about: "mini workspace --action recover --attempt attempts/ID (the decided outcome of the exact call, never a second write)" },
] };
pub static RETRY: Grammar = Grammar { verb: "retry", leaves: &[
    Leaf { path: &["retry"], args: &[arg("ID", Kind::Id)], flags: &[], effect: Effect::Transition, about: "mini retry --attempt attempts/ID --mode submit (the exact retry of the retained call)" },
] };
pub static ATTEMPT: Grammar = Grammar { verb: "attempt", leaves: &[
    Leaf { path: &["attempt"], args: &[arg("ID", Kind::Id)], flags: &[], effect: Effect::Local, about: "local: mini attempt-state --attempt attempts/ID --json (the retained answers, the record's phase and the standing; no Host call)" },
] };
pub static PUBLISH: Grammar = Grammar { verb: "publish", leaves: &[
    Leaf { path: &["publish"], args: &[arg("ID", Kind::Id)], flags: &[], effect: Effect::Transition, about: "mini workspace --action publish-delegation --proposal-id ID --attempt attempts/ID (writes the recipient's reference)" },
] };
pub static HISTORY: Grammar = Grammar { verb: "history", leaves: &[
    Leaf { path: &["history"], args: &[opt("all", Kind::Choice(&["all"]))], flags: &[], effect: Effect::Local, about: "local: retained attempts and their last Host outcome" },
] };
pub static CAN: Grammar = Grammar { verb: "can", leaves: &[
    Leaf { path: &["can"], args: &[opt("REF", Kind::Ref)], flags: &[switch("--all"), switch("--any")], effect: Effect::Read, about: "mini workspace --action can [--name REF] [--all true]: each verb my grants cover, prepared and dry-run (Host op 130), never submitted; --any REF: one write REF's law admits from its current values, as a line to paste, or the clauses that rule every write out (Host op 150)" },
] };
pub static INSPECT: Grammar = Grammar { verb: "inspect", leaves: &[
    Leaf { path: &["inspect", "caps"], args: &[opt("REF", Kind::Ref)], flags: &[switch("--json")], effect: Effect::Read, about: "mini workspace --action inspect --view caps (the capability tree over bytes this workspace holds or reads with its own signed views)" },
    Leaf { path: &["inspect", "law"], args: &[arg("REF", Kind::Ref)], flags: &[switch("--json")], effect: Effect::Read, about: "inspect --view law (the installed law and the current value of each slot it names)" },
    Leaf { path: &["inspect", "receipt"], args: &[arg("ID", Kind::Id)], flags: &[switch("--json")], effect: Effect::Read, about: "inspect --view receipt (a Lean view of the retained receipt)" },
    Leaf { path: &["inspect", "turn"], args: &[arg("ID", Kind::Id)], flags: &[switch("--json")], effect: Effect::Read, about: "inspect --view turn (dry-runs the retained turn, op 130; nothing is submitted)" },
] };
pub static WHY: Grammar = Grammar { verb: "why", leaves: &[
    Leaf { path: &["why"], args: &[opt("ATTEMPT", Kind::Id)], flags: &[switch("--json")], effect: Effect::Local, about: "mini workspace --action inspect --view why --refusals HOME/refusals: the last refusal held, explained from the Host's own frame (clause, slot values, the request value that passes it)" },
] };
pub static REFS: Grammar = Grammar { verb: "refs", leaves: &[
    Leaf { path: &["refs"], args: &[], flags: &[], effect: Effect::Local, about: "mini workspace --action list" },
] };
pub static READ: Grammar = Grammar { verb: "read", leaves: &[
    Leaf { path: &["read"], args: &[arg("REF", Kind::Ref)], flags: &[], effect: Effect::Read, about: "mini workspace --action read --name REF (a signed read)" },
] };
pub static DESCRIBE: Grammar = Grammar { verb: "describe", leaves: &[
    Leaf { path: &["describe"], args: &[arg("REF", Kind::Ref)], flags: &[], effect: Effect::Read, about: "mini workspace --action describe --name REF" },
] };
pub static IMPORT: Grammar = Grammar { verb: "import", leaves: &[
    Leaf { path: &["import"], args: &[arg("NAME", Kind::Ref), arg("REFERENCE-JSON|@FILE", Kind::Word)], flags: &[], effect: Effect::Local, about: "mini workspace --action import --from-ref (a delegated reference, as JSON or @FILE)" },
    Leaf { path: &["import"], args: &[arg("NAME", Kind::Ref), arg("KIND", Kind::Word), arg("TARGET", Kind::Subject), arg("OBSERVE", Kind::Subject), opt("OPERATION|-", Kind::Word), opt("CONTROL", Kind::Subject)], flags: &[], effect: Effect::Local, about: "mini workspace --action import --kind --target --observe-capability [--operation-capability] [--control-capability]" },
] };
pub static EXPORT: Grammar = Grammar { verb: "export", leaves: &[
    Leaf { path: &["export"], args: &[arg("ID", Kind::Id)], flags: &[], effect: Effect::Local, about: "local: print proposals/ID/recipient-reference.json" },
    Leaf { path: &["export", "world"], args: &[opt("NAME", Kind::Word)], flags: &[], effect: Effect::Read, about: "mini export-world: your world as one tar at HOME/exports/NAME (default world.tar): every document as the Host renders it to you now and its signed view, every retained attempt with its standing, your room state, your public key and the custody statement, and a manifest with the world root; reads only; one per member per 10 minutes, shared with the web /export (HOME/exports/.last-export)" },
] };
pub static INBOX: Grammar = Grammar { verb: "inbox", leaves: &[
    Leaf { path: &["inbox"], args: &[], flags: &[], effect: Effect::Local, about: "local: the delegated references in HOME/inbox, whether addressed to this subject and whether imported" },
] };
pub static HOME: Grammar = Grammar { verb: "home", leaves: &[
    Leaf { path: &["home"], args: &[opt("REF", Kind::Ref)], flags: &[switch("--json")], effect: Effect::Read, about: "mini member --dir WORKSPACE [--name REF]: your resources and exact recovery actions; REF checks current Mini authority" },
] };
pub static WHOAMI: Grammar = Grammar { verb: "whoami", leaves: &[
    Leaf { path: &["whoami"], args: &[], flags: &[], effect: Effect::Local, about: "local: this session's workspace, home, subject and encryption key id (names the hybrid key an inviter to a private room releases the room key to; private rooms: devnet quality; privacy not audited)" },
] };
pub static HELP: Grammar = Grammar { verb: "help", leaves: &[
    Leaf { path: &["help"], args: &[opt("VERB|guide", Kind::Word)], flags: &[], effect: Effect::Local, about: "local; `help guide` prints the friends' guide" },
] };
pub static EXIT: Grammar = Grammar { verb: "exit", leaves: &[
    Leaf { path: &["exit"], args: &[], flags: &[], effect: Effect::Local, about: "local" },
] };

// The chat verbs (chat.rs), Hermes (hermes.rs) and the story (story.rs): raw-line grammars.
pub static SAY: Grammar = Grammar { verb: "say", leaves: &[
    Leaf { path: &["say"], args: &[opt("TEXT", Kind::Rest)], flags: &[valued("--to", "NAME", Kind::Word), valued("--re", "N", Kind::Number), valued("--in", "ROOM", Kind::Word), valued("--operation-record", "ABS_PATH", Kind::Word), valued("--file", "FILE", Kind::Word), valued("--status", "STATE", Kind::Word), valued("--expect-re-cell", "CELL", Kind::Number), valued("--expect-re-sequence", "N", Kind::Number), valued("--via", "NETWORK", Kind::Word), valued("--via-id", "ID", Kind::Number), valued("--via-name", "NAME", Kind::Word)], effect: Effect::Transition, about: "append {\"type\":\"say\",\"text\":TEXT} to my stream in the current room (propose + submit); --file FILE says the file's text; --status, --expect-re-* and --via are a resident's and a bridge's typed entries" },
] };
pub static TAIL: Grammar = Grammar { verb: "tail", leaves: &[
    Leaf { path: &["tail"], args: &[], flags: &[valued("-n", "N", Kind::Number), valued("--since", "HEIGHT", Kind::Number), switch("--follow"), switch("-f"), switch("--json"), switch("--held"), valued("--in", "ROOM", Kind::Word), valued("--entry", "CELL:SEQUENCE", Kind::Word), valued("--discover", "FILE", Kind::Word), valued("--discover-json", "-", Kind::Word)], effect: Effect::Read, about: "a signed tail of every member stream in the current room, merged by (height, author, cell, sequence)" },
] };
pub static TOPIC: Grammar = Grammar { verb: "topic", leaves: &[
    Leaf { path: &["topic"], args: &[opt("TEXT", Kind::Rest)], flags: &[], effect: Effect::Transition, about: "show the room topic, or append {\"type\":\"topic\"} (the founder's counts)" },
] };
pub static PIN: Grammar = Grammar { verb: "pin", leaves: &[
    Leaf { path: &["pin"], args: &[arg("N", Kind::Word)], flags: &[], effect: Effect::Transition, about: "append {\"type\":\"pin\"} with ref = entry #N (the founder's count)" },
] };
pub static UNPIN: Grammar = Grammar { verb: "unpin", leaves: &[
    Leaf { path: &["unpin"], args: &[], flags: &[], effect: Effect::Transition, about: "append {\"type\":\"unpin\"} in the current room (the founder's counts)" },
] };
pub static REACT: Grammar = Grammar { verb: "react", leaves: &[
    Leaf { path: &["react"], args: &[arg("N", Kind::Word), arg("EMOJI", Kind::Word)], flags: &[], effect: Effect::Transition, about: "append {\"type\":\"react\",\"emoji\":EMOJI} with ref = entry #N" },
] };
pub static CHAT: Grammar = Grammar { verb: "chat", leaves: &[
    Leaf { path: &["chat", "new"], args: &[arg("ROOM", Kind::Word)], flags: &[switch("--private")], effect: Effect::Transition, about: "a chat room (its roster, its streams); --private: a private room (devnet quality; privacy not audited)" },
    Leaf { path: &["chat", "adopt"], args: &[arg("ROOM", Kind::Word)], flags: &[], effect: Effect::Transition, about: "the founder gives a room it already controls the chat roster" },
    Leaf { path: &["chat", "invite"], args: &[arg("ROOM", Kind::Word), arg("SUBJECT", Kind::Subject), opt("NAME", Kind::Word)], flags: &[valued("--enc", "ENC-PUB|@FILE", Kind::Word), dangerous("--i-know"), valued("--verbs", "V,...", Kind::Word), switch("--roster-only")], effect: Effect::Propose, about: "the room grant for SUBJECT (observe, append; --verbs widens it), a petname; --enc releases a private room's key; --roster-only: the stream and roster row alone (the grant is SUBJECT's concierge window)" },
    Leaf { path: &["chat", "join"], args: &[arg("ROOM", Kind::Word), arg("INVITE-JSON|@FILE", Kind::Rest)], flags: &[], effect: Effect::Local, about: "import the invitation" },
    Leaf { path: &["chat", "enter"], args: &[arg("ROOM", Kind::Word)], flags: &[], effect: Effect::Local, about: "make ROOM the current room" },
    Leaf { path: &["chat", "rooms"], args: &[], flags: &[], effect: Effect::Local, about: "local: the rooms this session holds" },
    Leaf { path: &["chat", "name"], args: &[arg("SUBJECT", Kind::Subject), arg("NAME", Kind::Word)], flags: &[], effect: Effect::Local, about: "local: a petname for a subject" },
] };
/// `feedback`: one report from the member, a signed turn in the member's own feedback room (the operator
/// founds that room and holds the only other seat; chat.rs `Line::Feedback`). `reports` is the
/// operator's reading of every such room, newest context included.
pub static FEEDBACK: Grammar = Grammar { verb: "feedback", leaves: &[
    Leaf { path: &["feedback"], args: &[arg("TEXT", Kind::Rest)], flags: &[valued("--from", "ATTEMPT", Kind::Id), valued("--clause", "CLAUSE", Kind::Word), valued("--page", "PATH", Kind::Word), valued("--via", "NETWORK", Kind::Word)], effect: Effect::Transition, about: "append {\"type\":\"feedback\",\"text\":TEXT,\"client\":VERSION,\"sha\":CANDIDATE} to my stream in my feedback room (propose + submit); --from ATTEMPT, --clause and --page record where the problem was met" },
] };
pub static REPORTS: Grammar = Grammar { verb: "reports", leaves: &[
    Leaf { path: &["reports"], args: &[], flags: &[valued("--since", "HEIGHT", Kind::Number), valued("-n", "N", Kind::Number), switch("--digest"), switch("--json")], effect: Effect::Read, about: "signed tails of every feedback-NAME room this session founded, merged by height (a member: their own feedback room, what they reported); --digest: one line per report (height, member, first 120 characters)" },
] };
pub static SUMMON: Grammar = Grammar { verb: "summon", leaves: &[
    Leaf { path: &["summon"], args: &[arg("ROOM", Kind::Word), arg("as", Kind::Choice(&["as"])), arg("librarian|gm|runner", Kind::Choice(&["librarian", "gm", "runner"]))], flags: &[valued("--budget", "N", Kind::Number), valued("--every", "N", Kind::Number), valued("--program", "@FILE", Kind::Word), valued("--hermes", "SUBJECT", Kind::Subject), dangerous("--i-know")], effect: Effect::Transition, about: "a member, in a room whose founder already summoned Hermes (the lobby): says it is there and how to ask it, funding and granting nothing; the founder: the till (if none), Hermes's budget account funded N from mine, Hermes on the roster (chat invite), the role's documents and grants, the program document ROOM-hermes-ROLE, the room's hermes fields, the hand-off in HOME/outbox/H" },
] };
pub static ASK: Grammar = Grammar { verb: "ask", leaves: &[
    Leaf { path: &["ask"], args: &[arg("[ROOM] TEXT", Kind::Rest)], flags: &[], effect: Effect::Transition, about: "say --to HERMES in the room (Hermes is the room cell's `hermes` field, a signed read); the first word is the room when this session holds one by that name" },
] };
pub static HERMES: Grammar = Grammar { verb: "hermes", leaves: &[
    Leaf { path: &["hermes", "status"], args: &[opt("ROOM", Kind::Word)], flags: &[], effect: Effect::Read, about: "a signed read of the room's streams; each of my requests to Hermes with Hermes's latest typed status for it" },
    Leaf { path: &["hermes", "cancel"], args: &[arg("N", Kind::Number), opt("ROOM", Kind::Word)], flags: &[], effect: Effect::Transition, about: "append {\"type\":\"withdraw\"} for my request #N" },
] };
pub static DISMISS: Grammar = Grammar { verb: "dismiss", leaves: &[
    Leaf { path: &["dismiss"], args: &[arg("ROOM", Kind::Word)], flags: &[], effect: Effect::Transition, about: "founder: revoke the room grant and the role's delegations to Hermes, zero the room's hermes fields, ask Hermes to return the unspent budget (HOME/outbox/H/dismiss-ROOM.json)" },
] };
pub static STORY: Grammar = Grammar { verb: "story", leaves: &[
    Leaf { path: &["story", "new"], args: &[arg("NAME", Kind::Word)], flags: &[req(valued("--from", "tale|@FILE", Kind::Word)), valued("--gm", "SUBJECT", Kind::Subject)], effect: Effect::Transition, about: "the table and its scenes under the sealed story law (--from a built-in tale or @FILE)" },
    Leaf { path: &["story", "seal"], args: &[arg("NAME", Kind::Word)], flags: &[], effect: Effect::Transition, about: "seal the story's law" },
    Leaf { path: &["story", "invite"], args: &[arg("NAME", Kind::Word), arg("SUBJECT", Kind::Subject), opt("gm", Kind::Choice(&["gm"]))], flags: &[], effect: Effect::Propose, about: "a player's (or the GM's) grant" },
    Leaf { path: &["story", "join"], args: &[arg("NAME", Kind::Word), arg("INVITATION|@FILE", Kind::Rest)], flags: &[], effect: Effect::Local, about: "import the invitation" },
    Leaf { path: &["story", "enter"], args: &[arg("NAME", Kind::Word)], flags: &[], effect: Effect::Local, about: "make NAME the current story" },
    Leaf { path: &["story", "list"], args: &[], flags: &[], effect: Effect::Local, about: "local: the stories this session holds" },
    Leaf { path: &["story", "law"], args: &[arg("NAME|tale", Kind::Word), opt("SUBJECT", Kind::Subject)], flags: &[], effect: Effect::Read, about: "the story law, as a player (SUBJECT) would be judged by it" },
] };
pub static LOOK: Grammar = Grammar { verb: "look", leaves: &[
    Leaf { path: &["look"], args: &[], flags: &[], effect: Effect::Read, about: "signed reads: the table, my cell and both their laws; print my scene, its exits, items and the GM's last words" },
] };
pub static GO: Grammar = Grammar { verb: "go", leaves: &[
    Leaf { path: &["go"], args: &[arg("EXIT|SCENE", Kind::Word)], flags: &[], effect: Effect::Transition, about: "one write to my cell: scene := the exit's scene, turn + 1 (the sealed law judges it)" },
] };
pub static TAKE: Grammar = Grammar { verb: "take", leaves: &[
    Leaf { path: &["take"], args: &[arg("ITEM", Kind::Word)], flags: &[], effect: Effect::Transition, about: "one write to my cell: carries/ITEM := 1, turn + 1" },
] };
pub static ACT: Grammar = Grammar { verb: "act", leaves: &[
    Leaf { path: &["act"], args: &[arg("VERB", Kind::Word)], flags: &[], effect: Effect::Transition, about: "one write to my cell: scene := the act's scene, turn + 1" },
] };
pub static NARRATE: Grammar = Grammar { verb: "narrate", leaves: &[
    Leaf { path: &["narrate"], args: &[arg("TEXT", Kind::Rest)], flags: &[], effect: Effect::Transition, about: "append {\"type\":\"say\",\"text\":TEXT} to the story's scenes stream (the GM's)" },
] };

pub static APPS: Grammar = Grammar { verb: "apps", leaves: &[
    Leaf { path: &["apps", "search"], args: &[opt("TERM", Kind::Word)], flags: &[valued("--category", "C", Kind::Word), switch("--json")], effect: Effect::Read, about: "the Sandstorm app market index: the publisher's claims beside the box's verdict (signature, signed app id, size against the profile)" },
    Leaf { path: &["apps", "show"], args: &[arg("APP-ID|PACKAGE-ID", Kind::Word)], flags: &[switch("--json")], effect: Effect::Read, about: "one entry whole, and the refusals an install can meet" },
    Leaf { path: &["apps", "install"], args: &[arg("APP-ID|PACKAGE-ID", Kind::Word)], flags: &[valued("--class", "S|M|L", Kind::Choice(&["S", "M", "L"]))], effect: Effect::Transition, about: "one member turn: the app birth under your key, the hosting delegation, the package choice under law.apps, then the worker's install and start; refused by name (unknownApp, sizeOverProfile, unverifiedSignature, unsupportedBridge, funding, classRefused) or undecided with `apps retry REQUEST-ID`" },
    Leaf { path: &["apps", "retry"], args: &[arg("REQUEST-ID", Kind::Word)], flags: &[], effect: Effect::Transition, about: "the exact retry of an install whose reply was lost; a second install is never issued" },
    Leaf { path: &["apps", "list"], args: &[], flags: &[switch("--json")], effect: Effect::Read, about: "the grains you own or were shared, with the v1 identity notice" },
    Leaf { path: &["apps", "status"], args: &[arg("GRAIN", Kind::Word)], flags: &[switch("--json")], effect: Effect::Read, about: "state, generation, origin, the routes you hold, the identities the grain holds" },
    Leaf { path: &["apps", "open"], args: &[arg("GRAIN", Kind::Word)], flags: &[switch("--json")], effect: Effect::Transition, about: "your route's one-time bootstrap token for the grain's own origin (used once)" },
    Leaf { path: &["apps", "stop"], args: &[arg("GRAIN", Kind::Word)], flags: &[switch("--json")], effect: Effect::Transition, about: "STOP through the lifecycle; undecided with `apps status GRAIN` while it runs" },
    Leaf { path: &["apps", "start"], args: &[arg("GRAIN", Kind::Word)], flags: &[switch("--json")], effect: Effect::Transition, about: "START through the lifecycle" },
    Leaf { path: &["apps", "renew"], args: &[arg("GRAIN", Kind::Word)], flags: &[switch("--json")], effect: Effect::Transition, about: "re-enroll your grain's routes against the generation it now serves (a restart starts a new one; START renews on its own, this is the explicit form; says so and submits nothing when nothing is stale)" },
    Leaf { path: &["apps", "share"], args: &[arg("GRAIN", Kind::Word), arg("MEMBER", Kind::Word)], flags: &[switch("--json")], effect: Effect::Transition, about: "a route on your grain for MEMBER (v1: members of a shared grain look like one user to the app)" },
    Leaf { path: &["apps", "export"], args: &[arg("GRAIN", Kind::Word), arg("FILE", Kind::Word)], flags: &[switch("--json")], effect: Effect::Transition, about: "the grain's data as a package you keep" },
    Leaf { path: &["apps", "delete"], args: &[arg("GRAIN", Kind::Word)], flags: &[switch("--json")], effect: Effect::Transition, about: "DELETE through the lifecycle" },
    Leaf { path: &["apps", "identities"], args: &[arg("GRAIN", Kind::Word)], flags: &[switch("--json")], effect: Effect::Read, about: "the saved identities the grain holds (who, since, revoked)" },
    Leaf { path: &["apps", "revoke-identity"], args: &[arg("GRAIN", Kind::Word), arg("TOKEN", Kind::Word)], flags: &[switch("--json")], effect: Effect::Transition, about: "revoke one saved identity" },
] };

// Keys, identity, births and the rest.
pub static KEY: Grammar = Grammar { verb: "key", leaves: &[
    Leaf { path: &["key", "set"], args: &[arg("PROVIDER", Kind::Word), arg("-|@FILE", Kind::Word)], flags: &[], effect: Effect::Local, about: "mini key --action set (the provider key from stdin or @FILE in HOME/keys, never on the line; hosted custody)" },
    Leaf { path: &["key", "grant"], args: &[arg("PROVIDER", Kind::Word), arg("RUNNER", Kind::Word)], flags: &[req(valued("--per-call", "TOKENS", Kind::Number)), req(valued("--per-day", "CALLS", Kind::Number)), req(valued("--until", "HEIGHT", Kind::Number)), valued("--model", "MODEL", Kind::Word)], effect: Effect::Transition, about: "mini key --action grant: a runner's bounded use of the provider key (per call, per day, until a height)" },
    Leaf { path: &["key", "revoke"], args: &[arg("PROVIDER", Kind::Word), opt("RUNNER", Kind::Word)], flags: &[], effect: Effect::Transition, about: "mini key --action revoke" },
    Leaf { path: &["key", "ls"], args: &[], flags: &[], effect: Effect::Local, about: "mini key --action ls" },
    Leaf { path: &["key", "providers"], args: &[], flags: &[], effect: Effect::Local, about: "mini key --action providers" },
    Leaf { path: &["key", "choose"], args: &[arg("PROVIDER", Kind::Word), arg("MODEL", Kind::Word), arg("RUNNER", Kind::Word), arg("TASK", Kind::Word)], flags: &[], effect: Effect::Local, about: "mini key --action choose" },
] };
pub static KEYGEN: Grammar = Grammar { verb: "keygen", leaves: &[
    Leaf { path: &["keygen"], args: &[arg("FILE", Kind::KeyFile)], flags: &[], effect: Effect::Local, about: "mini keygen --secret HOME/keys/FILE --public HOME/keys/FILE.pub (also the NEXT key HOME/keys/FILE.next: move it off this box)" },
] };
pub static KEY_STATUS: Grammar = Grammar { verb: "key-status", leaves: &[
    Leaf { path: &["key-status"], args: &[], flags: &[], effect: Effect::Local, about: "mini key-status --workspace WORKSPACE: key epoch, whether a next key is committed, whether the recorded next public key matches it" },
] };
pub static ADOPT_NEXT_KEY: Grammar = Grammar { verb: "adopt-next-key", leaves: &[
    Leaf { path: &["adopt-next-key", "lookup"], args: &[arg("ATTEMPT", Kind::Word)], flags: &[], effect: Effect::Transition, about: "recover a retained adoption attempt without signing again" },
    Leaf { path: &["adopt-next-key"], args: &[arg("NEXTFILE", Kind::KeyFile)], flags: &[], effect: Effect::Transition, about: "commit a next key for an existing identity" },
] };
pub static ROTATE_KEY: Grammar = Grammar { verb: "rotate-key", leaves: &[
    Leaf { path: &["rotate-key"], args: &[arg("NEXTFILE", Kind::KeyFile)], flags: &[], effect: Effect::Transition, about: "mini rotate-key --workspace WORKSPACE --next-key HOME/keys/NEXTFILE: rotate to the committed next key; NEXTFILE then holds the key after it" },
] };
pub static INIT: Grammar = Grammar { verb: "init", leaves: &[
    Leaf { path: &["init"], args: &[arg("KEYFILE", Kind::KeyFile), arg("SUBJECT", Kind::Subject)], flags: &[dangerous("--no-prerotation")], effect: Effect::Local, about: "mini workspace --action init --key HOME/keys/KEYFILE --subject SUBJECT --birth-context HOME/provision/birth-context.json --namespace-root HOME/namespace (refuses a subject whose committed next key is not HOME/keys/KEYFILE.next.pub)" },
] };
pub static ENROLL: Grammar = Grammar { verb: "enroll", leaves: &[
    Leaf { path: &["enroll", "plan"], args: &[arg("NAME", Kind::Id), arg("KEYFILE|PUBLIC-KEY-HEX", Kind::Word), opt("NEXT-PUBLIC-KEY-HEX", Kind::Word), opt("COSIGN-HEX", Kind::Word), opt("FACTORY-REF", Kind::Ref)], flags: &[dangerous("--no-prerotation")], effect: Effect::Local, about: "mini enroll --action plan --dir HOME/enroll/NAME (a hex public key plans with --new-public-key: the newcomer's secret never enters this home; the record commits to the newcomer's next key, or --no-prerotation says so)" },
    Leaf { path: &["enroll", "offer"], args: &[arg("NAME", Kind::Id)], flags: &[], effect: Effect::Local, about: "mini enroll --action offer" },
    Leaf { path: &["enroll", "seal"], args: &[arg("NAME", Kind::Id), opt("SIGNATURE-HEX", Kind::Word)], flags: &[], effect: Effect::Local, about: "mini enroll --action seal (with the newcomer's possession signature when given)" },
    Leaf { path: &["enroll", "submit"], args: &[arg("NAME", Kind::Id)], flags: &[], effect: Effect::Transition, about: "mini enroll --action submit" },
    Leaf { path: &["enroll", "lookup"], args: &[arg("NAME", Kind::Id)], flags: &[], effect: Effect::Transition, about: "mini enroll --action lookup" },
    Leaf { path: &["enroll", "welcome"], args: &[arg("NAME", Kind::Id)], flags: &[], effect: Effect::Local, about: "mini enroll --action welcome (the newcomer's birth context, when this workspace provisioned them)" },
] };
pub static PROVISION: Grammar = Grammar { verb: "provision", leaves: &[
    Leaf { path: &["provision"], args: &[arg("NAME", Kind::Id), arg("HOLDER", Kind::Subject), arg("FUNDING", Kind::Number), arg("PREDICATE-JSON|@FILE", Kind::Word), opt("FACTORY-REF", Kind::Id)], flags: &[], effect: Effect::Transition, about: "mini workspace --action provision --name NAME --holder HOLDER --funding FUNDING --account-predicate HOME/requests/provision-NAME.json" },
] };
pub static CREATE: Grammar = Grammar { verb: "create", leaves: &[
    Leaf { path: &["create"], args: &[arg("NAME", Kind::Ref), arg("STORAGE", Kind::Word), arg("LAW|PREDICATE-JSON|@FILE", Kind::Word), opt("FIELDS|open", Kind::Word)], flags: &[valued("--in", "ROOM", Kind::Ref), valued("--owner", "SUBJECT", Kind::Subject), valued("--from", "KIND", Kind::Ref)], effect: Effect::Transition, about: "mini workspace --action create (--fields: the fields a declared cell may hold) [--in ROOM] [--owner SUBJECT]; --from KIND births a world-resident kind's instance" },
] };
pub static INVOKE: Grammar = Grammar { verb: "invoke", leaves: &[
    Leaf { path: &["invoke"], args: &[arg("ID", Kind::Id), arg("REF", Kind::Ref), arg("create", Kind::Choice(&["create"])), arg("FIELD", Kind::Number), arg("VALUE", Kind::Word)], flags: &[], effect: Effect::Propose, about: "mini workspace --action propose (action invoke: one scalar create)" },
    Leaf { path: &["invoke"], args: &[arg("ID", Kind::Id), arg("REF", Kind::Ref), arg("write", Kind::Choice(&["write"])), arg("FIELD", Kind::Number), arg("VALUE", Kind::Word), arg("EXPECTED", Kind::Word)], flags: &[], effect: Effect::Propose, about: "mini workspace --action propose (action invoke: one scalar write, compare-and-set against EXPECTED)" },
] };
pub static KIND: Grammar = Grammar { verb: "kind", leaves: &[
    Leaf { path: &["kind", "create"], args: &[arg("NAME", Kind::Ref), arg("DEFINITION-JSON|@FILE", Kind::Word), arg("LAW", Kind::Word)], flags: &[valued("--in", "ROOM", Kind::Ref)], effect: Effect::Transition, about: "world-resident definition create" },
    Leaf { path: &["kind", "show"], args: &[arg("NAME", Kind::Ref)], flags: &[], effect: Effect::Read, about: "signed read of the definition" },
    Leaf { path: &["kind", "revise"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Ref), arg("DEFINITION-JSON|@FILE", Kind::Word)], flags: &[], effect: Effect::Propose, about: "guarded revision (propose)" },
    Leaf { path: &["kind", "construct"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Ref), arg("PROGRAM-ID", Kind::Subject), arg("PARENTS-JSON|@FILE", Kind::Word)], flags: &[], effect: Effect::Transition, about: "authenticated source construction" },
] };
pub static PROGRAM: Grammar = Grammar { verb: "program", leaves: &[
    Leaf { path: &["program", "create"], args: &[arg("NAME", Kind::Ref), arg("SOURCE-JSON|@FILE", Kind::Word), arg("LAW", Kind::Word)], flags: &[valued("--in", "ROOM", Kind::Ref)], effect: Effect::Transition, about: "register canonical code and ABI with the existing evaluator, then birth its immutable program cell" },
] };
pub static INSTANCE: Grammar = Grammar { verb: "instance", leaves: &[
    Leaf { path: &["instance", "show"], args: &[arg("NAME", Kind::Ref)], flags: &[], effect: Effect::Read, about: "signed descriptor and entry read" },
    Leaf { path: &["instance", "call"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Ref), arg("METHOD", Kind::Word)], flags: &[valued("--fund", "ACCOUNT", Kind::Ref), valued("--max-compute-credits", "N", Kind::Number)], effect: Effect::Transition, about: "a method call with compute consent (--fund and --max-compute-credits together)" },
    Leaf { path: &["instance", "set"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Ref), arg("FIELD", Kind::Word), arg("KEY", Kind::Number), arg("VALUE", Kind::Word)], flags: &[], effect: Effect::Propose, about: "named guarded edit using the last displayed values (propose)" },
    Leaf { path: &["instance", "erase"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Ref), arg("FIELD", Kind::Word), arg("KEY", Kind::Number)], flags: &[], effect: Effect::Propose, about: "named guarded erase (propose)" },
] };
pub static APP: Grammar = Grammar { verb: "app", leaves: &[
    Leaf { path: &["app", "status"], args: &[arg("NAME", Kind::Ref)], flags: &[switch("--json")], effect: Effect::Read, about: "current app admission (mini member --action app-status)" },
    Leaf { path: &["app", "delegate-lifecycle", "prepare"], args: &[arg("ID", Kind::Id), arg("NAME", Kind::Ref)], flags: &[req(valued("--package", "PKG", Kind::Ref)), req(valued("--snapshot", "SNAP", Kind::Ref)), req(valued("--manager", "SUBJECT", Kind::Subject))], effect: Effect::Transition, about: "member-signed lifecycle management delegation, prepared with retained exact recovery" },
    Leaf { path: &["app", "delegate-lifecycle"], args: &[arg("prepare|submit|recover|status", Kind::Choice(&["prepare", "submit", "recover", "status"])), arg("ID", Kind::Id)], flags: &[], effect: Effect::Transition, about: "the delegation's lifecycle by request id" },
] };
pub static FORGET: Grammar = Grammar { verb: "forget", leaves: &[
    Leaf { path: &["forget"], args: &[arg("ROOM", Kind::Id), opt("EPOCH", Kind::Number)], flags: &[], effect: Effect::Local, about: "mini workspace --action room-key --op forget: delete this client's copies of a private room's keys (all epochs, or one). A promise of this client only: the wraps stay in the room's keys cell, so your encryption key could still open them until the room is rotated (room rotate). Private rooms: devnet quality; privacy not audited" },
] };

pub static BOARD: Grammar = Grammar { verb: "board", leaves: &[
    Leaf { path: &["board", "new"], args: &[arg("NAME", Kind::Ref)], flags: &[], effect: Effect::Transition, about: "mini workspace --action create (storage declared, the board law: tasks 0 and 1, fields 2-5)" },
    Leaf { path: &["board", "add"], args: &[arg("ID", Kind::Id), arg("BOARD", Kind::Ref), arg("TASK", Kind::Number)], flags: &[], effect: Effect::Propose, about: "propose (action invoke: task TASK's state field 2*TASK+2 := 0)" },
    Leaf { path: &["board", "move"], args: &[arg("ID", Kind::Id), arg("BOARD", Kind::Ref), arg("TASK", Kind::Number), arg("FROM", Kind::Choice(&["todo", "doing", "done"])), arg("TO", Kind::Choice(&["todo", "doing", "done"]))], flags: &[], effect: Effect::Propose, about: "propose (action invoke: the task's state FROM -> TO, compare-and-set)" },
    Leaf { path: &["board", "take"], args: &[arg("ID", Kind::Id), arg("BOARD", Kind::Ref), arg("TASK", Kind::Number)], flags: &[], effect: Effect::Propose, about: "propose (action invoke: the task's owner field 2*TASK+3 := me)" },
] };

/// `private-compute`: the research-labelled in-process four-party computation (private-backend R1).
/// A local computation: no Host call, no admission. The label is part of the operation words, so
/// help, the web form and the page all carry it.
pub static PRIVATE_COMPUTE: Grammar = Grammar { verb: "private-compute", leaves: &[
    Leaf { path: &["private-compute"], args: &[arg("LEFT", Kind::Number), arg("RIGHT", Kind::Number)], flags: &[], effect: Effect::Local, about: "local: RESEARCH DEMONSTRATION, single process, n = 4, static f = 1, no simulator, no GOD: four holders in one process add LEFT and RIGHT (each 0..255), none seeing either input, and one curious holder's log is shown as the evidence (about 15 seconds; never an admission, never a service)" },
] };

pub static GRAMMARS: &[&Grammar] = &[&PRIVATE_COMPUTE, &BOARD, &KEY, &KEYGEN, &KEY_STATUS, &ADOPT_NEXT_KEY, &ROTATE_KEY, &INIT, &ENROLL, &PROVISION, &CREATE, &INVOKE, &KIND, &PROGRAM, &INSTANCE, &APP, &FORGET, &APPS, &DOC, &ROOM, &DELEGATE, &REVOKE, &RENOUNCE, &LAW, &PAY, &CREDIT, &TARIFF, &TOPUP, &MARKET, &BID, &REVEAL, &BIDS, &JOB, &JOBS, &BEND,
    &PROPOSE, &SUBMIT, &LOOKUP, &RETRY, &ATTEMPT, &PUBLISH, &HISTORY, &CAN, &INSPECT, &WHY, &REFS, &READ, &DESCRIBE, &IMPORT, &EXPORT, &INBOX, &HOME, &WHOAMI, &HELP, &EXIT,
    &SAY, &TAIL, &TOPIC, &PIN, &UNPIN, &REACT, &CHAT, &FEEDBACK, &REPORTS, &SUMMON, &ASK, &HERMES, &DISMISS, &STORY, &LOOK, &GO, &TAKE, &ACT, &NARRATE];

pub fn grammar(verb: &str) -> Option<&'static Grammar> {
    GRAMMARS.iter().copied().find(|g| g.verb == verb)
}

/// The usage line, rendered: one alternative per leaf, in the table's own notation.
pub fn usage(g: &Grammar) -> String {
    g.leaves.iter().map(leaf_usage).collect::<Vec<_>>().join(" | ")
}

pub fn leaf_usage(leaf: &Leaf) -> String {
    let mut words: Vec<String> = leaf.path.iter().map(|w| w.to_string()).collect();
    for a in leaf.args {
        words.push(if a.optional { format!("[{}]", a.name) } else { a.name.to_owned() });
    }
    for f in leaf.flags {
        let shown = match f.value {
            Some((placeholder, _)) => format!("{} {placeholder}", f.name),
            None => f.name.to_owned(),
        };
        words.push(if f.required { shown } else { format!("[{shown}]") });
    }
    words.join(" ")
}

/// A leaf's path followed by one word per positional argument, each from `value(arg)`: the pure
/// render of a line a caller has already decided (e.g. the write a law's witness names). Flags
/// are not rendered; an optional argument whose value is empty is left out.
pub fn compose(leaf: &Leaf, value: &dyn Fn(&Arg) -> String) -> String {
    let mut words: Vec<String> = leaf.path.iter().map(|w| w.to_string()).collect();
    for a in leaf.args {
        let v = value(a);
        if v.is_empty() && a.optional {
            continue;
        }
        words.push(v);
    }
    words.join(" ")
}

/// The leaf of `g` whose literal path is exactly `path`.
pub fn leaf(g: &'static Grammar, path: &[&str]) -> Option<&'static Leaf> {
    g.leaves.iter().find(|l| l.path == path)
}

/// The operation words, rendered: one segment per leaf, aligned with the usage.
pub fn operation(g: &Grammar) -> String {
    g.leaves.iter().map(|l| l.about).collect::<Vec<_>>().join(" | ")
}

/// A leaf's words, typed: positional values by argument index (None when an optional one was
/// not given), and the flags that were present with their values.
#[derive(Debug)]
pub struct Parsed {
    pub leaf: &'static Leaf,
    pub args: Vec<Option<String>>,
    pub flags: Vec<(&'static str, Option<String>)>,
}

impl Parsed {
    pub fn arg(&self, i: usize) -> &str {
        self.args.get(i).and_then(|a| a.as_deref()).unwrap_or("")
    }
    pub fn opt(&self, i: usize) -> Option<&str> {
        self.args.get(i).and_then(|a| a.as_deref())
    }
    pub fn flag(&self, name: &str) -> Option<Option<&str>> {
        self.flags.iter().find(|(n, _)| *n == name).map(|(_, v)| v.as_deref())
    }
    pub fn has(&self, name: &str) -> bool {
        self.flag(name).is_some()
    }
    /// The value of a required valued flag (the parser refused the line without it).
    pub fn required(&self, name: &str) -> &str {
        self.flag(name).flatten().unwrap_or("")
    }
    /// Every value a repeatable valued flag was given (`--referee 9 --referee 12`).
    pub fn values(&self, name: &str) -> Vec<&str> {
        self.flags.iter().filter(|(n, _)| *n == name).filter_map(|(_, v)| v.as_deref()).collect()
    }
    /// How many leaves of the verb share this leaf's path (an arity- or kind-chosen shape).
    pub fn index_in(&self, g: &Grammar) -> usize {
        g.leaves.iter().position(|l| std::ptr::eq(l, self.leaf)).unwrap_or(0)
    }
}

/// The leaf the words name (the longest literal path that matches), its arguments checked by
/// kind and count, its flags recognized. A wrong shape (no leaf, a missing or extra word, an
/// unknown flag) answers the verb's whole usage, as the shell's `usage:` ending has always
/// done; a word of the wrong kind answers the typed message that names the argument.
pub fn parse(g: &'static Grammar, words: &[String]) -> Result<Parsed, String> {
    // The longest literal path first; when none of its shapes accepts the words, a shorter path
    // may (`law show fish open` is the proposal `show` on `fish`, not `law show` with a stray
    // word). Leaves that share a path are the shapes of one subcommand (an arity, a kind): the
    // first that accepts the words wins; the longest path's first error stands when none does.
    let mut candidates: Vec<&'static Leaf> = g
        .leaves
        .iter()
        .filter(|l| l.path.len() <= words.len() && l.path.iter().zip(words).all(|(p, w)| p == w))
        .collect();
    if candidates.is_empty() {
        return Err(usage(g));
    }
    candidates.sort_by_key(|l| std::cmp::Reverse(l.path.len()));
    // When no shape accepts the words, the refusal is the one from the shape that got furthest
    // (the longest path, then the most leading words of the right kind): `doc mark p 2 link`
    // is the link shape missing its TARGET, not the style shape refusing the word `link`.
    let mut best: Option<((usize, usize), String)> = None;
    for leaf in candidates {
        let rest = &words[leaf.path.len()..];
        match parse_leaf(g, leaf, rest) {
            Ok(parsed) => return Ok(parsed),
            Err(e) => {
                let rank = (leaf.path.len(), progress(leaf, rest));
                if best.as_ref().is_none_or(|(r, _)| rank > *r) {
                    best = Some((rank, e));
                }
            }
        }
    }
    Err(best.map(|(_, e)| e).unwrap_or_else(|| usage(g)))
}

/// How many leading words pass the leaf's positional kinds in order (flags not counted).
fn progress(leaf: &Leaf, rest: &[String]) -> usize {
    leaf.args.iter().zip(rest).take_while(|(a, w)| check(a.kind, w, a.name).is_ok()).count()
}

fn parse_leaf(g: &Grammar, leaf: &'static Leaf, rest: &[String]) -> Result<Parsed, String> {
    let mut args: Vec<Option<String>> = Vec::new();
    let mut flags: Vec<(&'static str, Option<String>)> = Vec::new();
    let mut i = 0;
    while i < rest.len() {
        let w = rest[i].as_str();
        if let Some(f) = leaf.flags.iter().find(|f| f.name == w) {
            match f.value {
                Some((placeholder, kind)) => {
                    let v = rest.get(i + 1).map(String::as_str).ok_or_else(|| usage(g))?;
                    check(kind, v, placeholder)?;
                    flags.push((f.name, Some(v.to_owned())));
                    i += 2;
                }
                None => {
                    flags.push((f.name, None));
                    i += 1;
                }
            }
            continue;
        }
        if w.starts_with("--") && w.len() > 2 {
            return Err(usage(g));
        }
        let position = args.len();
        let Some(a) = leaf.args.get(position) else {
            return Err(usage(g));
        };
        // A law is written as words (`any [ field 2 monotone ]`): it takes every remaining word
        // that is not one of the leaf's flags.
        if a.kind == Kind::Law {
            let mut taken = Vec::new();
            while i < rest.len() && !leaf.flags.iter().any(|f| f.name == rest[i]) {
                taken.push(rest[i].as_str());
                i += 1;
            }
            let value = taken.join(" ");
            check(a.kind, &value, a.name)?;
            args.push(Some(value));
            continue;
        }
        // An optional literal choice (`at`) that does not match lets the next argument take the word.
        if a.optional && matches!(a.kind, Kind::Choice(_)) && check(a.kind, w, a.name).is_err() {
            args.push(None);
            continue;
        }
        check(a.kind, w, a.name)?;
        args.push(Some(w.to_owned()));
        i += 1;
    }
    for a in &leaf.args[args.len()..] {
        if !a.optional {
            return Err(usage(g));
        }
        args.push(None);
    }
    required_flags(leaf, &flags)?;
    Ok(Parsed { leaf, args, flags })
}

/// A leaf's required flags must all be present; the refusal names the first that is not.
fn required_flags(leaf: &Leaf, flags: &[(&'static str, Option<String>)]) -> Result<(), String> {
    match leaf.flags.iter().find(|f| f.required && !flags.iter().any(|(n, _)| *n == f.name)) {
        Some(f) => Err(format!("{} needs {}: {}", leaf.path.join(" "), f.name, leaf.about)),
        None => Ok(()),
    }
}

/// [`parse`] over a RAW line: the leading words are split on whitespace only (no quote or
/// JSON-word processing), flags are read anywhere before the free text, and a [`Kind::Rest`]
/// argument takes the untouched remainder of the line. The chat, Hermes and story verbs parse
/// this way so that `say it's #1, isn't it` is the text it looks like.
pub fn parse_line(g: &'static Grammar, line: &str) -> Result<Parsed, String> {
    let mut candidates: Vec<&'static Leaf> = Vec::new();
    let head: Vec<&str> = line.split_whitespace().collect();
    for leaf in g.leaves {
        if leaf.path.len() <= head.len() && leaf.path.iter().zip(&head).all(|(p, w)| p == w) {
            candidates.push(leaf);
        }
    }
    if candidates.is_empty() {
        return Err(usage(g));
    }
    candidates.sort_by_key(|l| std::cmp::Reverse(l.path.len()));
    let mut first_error = None;
    for leaf in candidates {
        // The raw remainder after the leaf's path words.
        let mut rest = line.trim_start();
        for _ in leaf.path {
            rest = rest.trim_start();
            let end = rest.find(char::is_whitespace).unwrap_or(rest.len());
            rest = &rest[end..];
        }
        match parse_rest(g, leaf, rest) {
            Ok(parsed) => return Ok(parsed),
            Err(e) => {
                first_error.get_or_insert(e);
            }
        }
    }
    Err(first_error.unwrap_or_else(|| usage(g)))
}

fn parse_rest(g: &Grammar, leaf: &'static Leaf, mut rest: &str) -> Result<Parsed, String> {
    let mut args: Vec<Option<String>> = Vec::new();
    let mut flags: Vec<(&'static str, Option<String>)> = Vec::new();
    let next_word = |text: &str| -> Option<(String, usize)> {
        let trimmed = text.trim_start();
        if trimmed.is_empty() {
            return None;
        }
        let skipped = text.len() - trimmed.len();
        let end = trimmed.find(char::is_whitespace).unwrap_or(trimmed.len());
        Some((trimmed[..end].to_owned(), skipped + end))
    };
    // A flag's value is one word, or a double-quoted string with `\\` and `\"` escapes (the
    // web forms quote every value that is not a plain word, `web::body::quote`).
    let next_value = |text: &str| -> Option<(String, usize)> {
        let trimmed = text.trim_start();
        let skipped = text.len() - trimmed.len();
        let Some(inner) = trimmed.strip_prefix('"') else { return next_word(text) };
        let mut out = String::new();
        let mut chars = inner.char_indices();
        while let Some((i, c)) = chars.next() {
            match c {
                '\\' => match chars.next() {
                    Some((_, e @ ('\\' | '"'))) => out.push(e),
                    _ => return None,
                },
                '"' => return Some((out, skipped + 1 + i + 1)),
                c => out.push(c),
            }
        }
        None
    };
    loop {
        let position = args.len();
        if let Some(a) = leaf.args.get(position) {
            if a.kind == Kind::Rest {
                // Flags may still precede the text; the first non-flag word starts it.
                while let Some((w, used)) = next_word(rest) {
                    let Some(f) = leaf.flags.iter().find(|f| f.name == w) else { break };
                    rest = &rest[used..];
                    match f.value {
                        Some((placeholder, kind)) => {
                            let (v, used) = next_value(rest).ok_or_else(|| usage(g))?;
                            check(kind, &v, placeholder)?;
                            flags.push((f.name, Some(v)));
                            rest = &rest[used..];
                        }
                        None => flags.push((f.name, None)),
                    }
                }
                let text = rest.trim();
                if text.is_empty() {
                    if !a.optional {
                        return Err(usage(g));
                    }
                    args.push(None);
                } else {
                    args.push(Some(text.to_owned()));
                }
                rest = "";
                break;
            }
        }
        let Some((w, used)) = next_word(rest) else { break };
        if let Some(f) = leaf.flags.iter().find(|f| f.name == w) {
            rest = &rest[used..];
            match f.value {
                Some((placeholder, kind)) => {
                    let (v, used) = next_value(rest).ok_or_else(|| usage(g))?;
                    check(kind, &v, placeholder)?;
                    flags.push((f.name, Some(v)));
                    rest = &rest[used..];
                }
                None => flags.push((f.name, None)),
            }
            continue;
        }
        if w.starts_with("--") && w.len() > 2 {
            return Err(usage(g));
        }
        let position = args.len();
        let Some(a) = leaf.args.get(position) else { return Err(usage(g)) };
        if a.optional && matches!(a.kind, Kind::Choice(_)) && check(a.kind, &w, a.name).is_err() {
            args.push(None);
            continue;
        }
        check(a.kind, &w, a.name)?;
        args.push(Some(w));
        rest = &rest[used..];
    }
    for a in &leaf.args[args.len()..] {
        if !a.optional {
            return Err(usage(g));
        }
        args.push(None);
    }
    required_flags(leaf, &flags)?;
    Ok(Parsed { leaf, args, flags })
}

/// One value against its kind; the message names the argument.
pub fn check(kind: Kind, value: &str, name: &str) -> Result<(), String> {
    let ok = match kind {
        Kind::Id => !value.is_empty() && value.len() <= 64 && value.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-'),
        Kind::Ref => validate_ref_name(value).is_ok(),
        Kind::Subject | Kind::Number => value.len() <= 40 && mini_sdk::decimal::is_digits(value),
        Kind::TextOrFile => !value.is_empty() && (!value.starts_with('@') || is_session_file(&value[1..])),
        Kind::File => value.strip_prefix('@').is_some_and(is_session_file),
        Kind::KeyFile => is_session_file(value),
        Kind::FileOrStdin => value == "@-" || value.strip_prefix('@').is_some_and(is_session_file),
        Kind::Law | Kind::Rest => !value.is_empty(),
        Kind::Choice(options) => options.contains(&value),
        Kind::Word => !value.is_empty(),
    };
    if ok {
        Ok(())
    } else {
        Err(match kind {
            Kind::Id => format!("{name} must be 1..64 ASCII letters, digits or hyphens"),
            Kind::Ref => format!("{name} must be 1..64 ASCII letters, digits or hyphens, or such segments joined by '/' (lab/index)"),
            Kind::Subject | Kind::Number => format!("{name} must be a decimal number"),
            Kind::TextOrFile => format!("{name}: text, or @FILE naming a file in HOME/requests"),
            Kind::File => format!("{name} must be @FILE, a file in HOME/requests"),
            Kind::KeyFile => format!("{name} must be a plain file name in HOME/keys (letters, digits, '-', '_', '.'; no leading dot)"),
            Kind::FileOrStdin => format!("{name} must be @FILE (HOME/requests) or @- (standard input)"),
            Kind::Choice(options) => format!("{name} must be one of {}, not {value:?}", options.join("|")),
            Kind::Law | Kind::Word | Kind::Rest => format!("{name} is required"),
        })
    }
}

/// `session_file`'s rule: a bare file name under HOME/requests.
pub fn is_session_file(value: &str) -> bool {
    !value.is_empty() && value.len() <= 64 && !value.starts_with('.') && value.bytes().all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.'))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn words(line: &str) -> Vec<String> {
        line.split(' ').map(str::to_owned).collect()
    }

    #[test]
    fn apps_renew_is_a_transition_leaf_taking_one_grain() {
        let renew = leaf(&APPS, &["apps", "renew"]).expect("the apps grammar has renew");
        assert_eq!(renew.args.len(), 1);
        assert!(matches!(renew.effect, Effect::Transition));
        let parsed = parse(&APPS, &words("apps renew a4501 --json")).unwrap();
        assert_eq!(parsed.leaf.path, ["apps", "renew"]);
        assert_eq!(parsed.arg(0), "a4501");
        assert!(parse(&APPS, &words("apps renew")).is_err(), "a grain is required");
    }

    #[test]
    fn a_line_composes_from_a_leaf_and_the_caller_s_values() {
        let append = leaf(&DOC, &["doc", "append"]).unwrap();
        let line = compose(append, &|a| match a.name { "ID" => "ID".into(), "NAME" => "paper".into(), _ => "'hello'".into() });
        assert_eq!(line, "doc append ID paper 'hello'");
        let remove = leaf(&DOC, &["doc", "remove"]).unwrap();
        assert_eq!(compose(remove, &|a| if a.name == "NAME" { "paper".into() } else { "1".into() }), "doc remove paper 1");
    }

    #[test]
    fn a_required_flag_is_printed_bare_and_refused_by_name_when_missing() {
        assert!(usage(&ROOM).contains("room welcome NAME SUBJECT --template T|@FILE"));
        assert!(usage(&ROOM).contains("room seal ID NAME --freeze-roster"));
        let e = parse(&ROOM, &words("room seal s1 lab")).unwrap_err();
        assert!(e.starts_with("room seal needs --freeze-roster"), "{e}");
        assert!(parse(&ROOM, &words("room seal s1 lab --freeze-roster")).is_ok());
        let e = parse(&STORY, &words("story new tavern")).unwrap_err();
        assert!(e.contains("--from"), "{e}");
        assert_eq!(parse(&KEYGEN, &words("keygen mini.key")).unwrap().arg(0), "mini.key");
        assert!(parse(&KEYGEN, &words("keygen @x.txt")).unwrap_err().contains("HOME/keys"));
        assert!(parse(&BOARD, &words("board move m1 tasks 0 todo sideways")).unwrap_err().contains("todo|doing|done"));
    }

    #[test]
    fn the_doc_usage_renders_every_leaf_once_and_parses_its_own_examples() {
        let u = usage(&DOC);
        assert_eq!(u.split(" | ").count(), DOC.leaves.len());
        assert!(u.starts_with("doc app-export capture ID @FILE | doc app-export publish|status|recover ID | doc app-export rebase ID NEXT"));
        assert!(u.contains("doc append ID NAME TEXT|@FILE") && u.contains("doc show NAME [--at H] [--raw] [--json] [--html]"));
        assert_eq!(operation(&DOC).split(" | ").count(), DOC.leaves.len());
        let w = words("doc append w-1 paper hello");
        let p = parse(&DOC, &w).unwrap();
        assert_eq!(p.leaf.path, ["doc", "append"]);
        assert_eq!((p.arg(0), p.arg(1), p.arg(2)), ("w-1", "paper", "hello"));
        let _ = &words;
        assert_eq!(p.leaf.effect, Effect::Propose);
        let w = words("doc show paper --at 7 --json");
        let p = parse(&DOC, &w).unwrap();
        assert_eq!(p.flag("--at"), Some(Some("7")));
        assert!(p.has("--json") && !p.has("--html"));
        let w = words("doc transclude page wall 1 3 live at 9");
        let p = parse(&DOC, &w).unwrap();
        assert_eq!((p.arg(4), p.arg(5), p.arg(6)), ("live", "at", "9"));
        let w = words("doc transclude page wall 1 3");
        let p = parse(&DOC, &w).unwrap();
        assert_eq!(p.args[4], None);
        let w = words("doc app-export capture op-1 @binding.json");
        let p = parse(&DOC, &w).unwrap();
        assert_eq!(p.leaf.path, ["doc", "app-export", "capture"]);
        let w = words("doc app-export status op-1");
        let p = parse(&DOC, &w).unwrap();
        assert_eq!(p.leaf.path, ["doc", "app-export"]);
        assert_eq!(p.arg(0), "status");
        // A wrong shape answers the whole usage; a wrong kind names the argument.
        assert_eq!(parse(&DOC, &words("doc append w-1")).unwrap_err(), usage(&DOC));
        assert_eq!(parse(&DOC, &words("doc append w-1 paper a b")).unwrap_err(), usage(&DOC));
        assert_eq!(parse(&DOC, &words("doc nothing")).unwrap_err(), usage(&DOC));
        assert_eq!(parse(&DOC, &words("doc show paper --bogus")).unwrap_err(), usage(&DOC));
        assert!(parse(&DOC, &words("doc mark paper 2 underline")).unwrap_err().contains("not \"underline\""));
        assert!(parse(&DOC, &words("doc edit w-1 paper x text")).unwrap_err().contains("LINE must be a decimal"));
        assert!(parse(&DOC, &words("doc push w-1 paper plain")).unwrap_err().contains("@FILE"));
        // room: one leaf for `room new` with its switches and repeatable flags; dangerous switches.
        let w = words("room new tide --law realm --referee 9 --referee 12 --in lab");
        let p = parse(&ROOM, &w).unwrap();
        assert_eq!(p.values("--referee"), ["9", "12"]);
        assert_eq!(p.flag("--law"), Some(Some("realm")));
        let w = words("room seal s1 lab --freeze-roster");
        assert!(parse(&ROOM, &w).unwrap().has("--freeze-roster"));
        assert!(ROOM.leaves.iter().any(|l| l.flags.iter().any(|f| f.dangerous && f.name == "--i-know")));
        let w = words("room template show workroom member");
        let p = parse(&ROOM, &w).unwrap();
        assert_eq!((p.leaf.path, p.arg(0), p.arg(1)), (&["room", "template", "show"][..], "workroom", "member"));
        assert_eq!(parse(&ROOM, &words("room leave lab")).unwrap_err(), usage(&ROOM));
        // Shapes that share a path: the first that accepts the words wins.
        let w = words("renounce r1 77 account");
        let p = parse(&RENOUNCE, &w).unwrap();
        assert_eq!((p.index_in(&RENOUNCE), p.arg(1), p.arg(2)), (1, "77", "account"));
        let w = words("renounce r2 lab");
        assert_eq!(parse(&RENOUNCE, &w).unwrap().index_in(&RENOUNCE), 0);
        assert_eq!(parse(&RENOUNCE, &words("renounce r3 lab object")).unwrap_err(), usage(&RENOUNCE));
        let w = words("tariff lab set week 7");
        assert_eq!(parse(&TARIFF, &w).unwrap().index_in(&TARIFF), 1);
        let w = words("tariff lab");
        assert_eq!(parse(&TARIFF, &w).unwrap().index_in(&TARIFF), 0);
        // A law takes the remaining words; its switches still parse.
        let w = words("law l2 shared any [ field 2 monotone, not (verb == write) ] --freeze-roster");
        let p = parse(&LAW, &w).unwrap();
        assert_eq!(p.arg(2), "any [ field 2 monotone, not (verb == write) ]");
        assert!(p.has("--freeze-roster"));
        let w = words("law show fish open");
        assert_eq!(parse(&LAW, &w).unwrap().leaf.path, ["law"]);
        let w = words("law check -");
        assert_eq!(parse(&LAW, &w).unwrap().arg(0), "-");
        let w = words("pay lab week --account acc again");
        let p = parse(&PAY, &w).unwrap();
        assert_eq!((p.arg(0), p.arg(1), p.arg(2), p.flag("--account")), ("lab", "week", "again", Some(Some("acc"))));
        let w = words("pay status");
        assert_eq!(parse(&PAY, &w).unwrap().leaf.path, ["pay", "status"]);
        let w = words("job post lab prog --input 3 --price 5 --deadline 60 --account acc");
        let p = parse(&JOB, &w).unwrap();
        assert_eq!((p.arg(0), p.flag("--price")), ("lab", Some(Some("5"))));
        let w = words("import stolen object 15 11");
        assert_eq!(parse(&IMPORT, &w).unwrap().index_in(&IMPORT), 1);
        let w = words("import stolen @ref.json");
        assert_eq!(parse(&IMPORT, &w).unwrap().index_in(&IMPORT), 0);
        let w = words("inspect caps");
        assert_eq!(parse(&INSPECT, &w).unwrap().leaf.path, ["inspect", "caps"]);
        let w = words("can --any shared");
        assert!(parse(&CAN, &w).unwrap().has("--any"));
        // Raw lines: flags before the free text, the text untouched.
        let p = parse_line(&SAY, "say --to @bob --re 12 'yes, agreed'").unwrap();
        assert_eq!((p.flag("--to"), p.flag("--re"), p.arg(0)), (Some(Some("@bob")), Some(Some("12")), "'yes, agreed'"));
        assert_eq!(parse_line(&SAY, "say it's #1, isn't it").unwrap().arg(0), "it's #1, isn't it");
        assert_eq!(parse_line(&SAY, "say --file d-1.txt").unwrap().opt(0), None);
        assert_eq!(parse_line(&SAY, "say --re zero hi").unwrap_err(), "N must be a decimal number");
        let p = parse_line(&CHAT, r#"chat join commons {"a": "b c"}"#).unwrap();
        assert_eq!((p.leaf.path, p.arg(1)), (&["chat", "join"][..], r#"{"a": "b c"}"#));
        let p = parse_line(&CHAT, "chat invite den 1234 --i-know --enc ab12 bob").unwrap();
        assert_eq!((p.arg(2), p.flag("--enc"), p.has("--i-know")), ("bob", Some(Some("ab12")), true));
        let p = parse_line(&SUMMON, "summon lab as runner --program @prog.md --hermes 42 --i-know").unwrap();
        assert_eq!((p.arg(0), p.arg(2), p.flag("--program")), ("lab", "runner", Some(Some("@prog.md"))));
        assert!(parse_line(&SUMMON, "summon lab librarian").is_err());
        assert_eq!(parse_line(&TAIL, "tail -n 5 --since 30 --follow").unwrap().flag("-n"), Some(Some("5")));
        assert_eq!(parse_line(&HERMES, "hermes cancel 3 lab").unwrap().arg(1), "lab");
        let w = words("app delegate-lifecycle prepare r1");
        assert_eq!(parse(&APP, &w).unwrap().leaf.path, ["app", "delegate-lifecycle"]);
        let w = words("app delegate-lifecycle prepare r1 myapp --package pkg --snapshot snap --manager 9");
        assert_eq!(parse(&APP, &w).unwrap().leaf.path, ["app", "delegate-lifecycle", "prepare"]);
        let w = words("invoke x shared write 2 5 1");
        assert_eq!(parse(&INVOKE, &w).unwrap().index_in(&INVOKE), 1);
        assert!(parse(&INVOKE, &words("invoke x shared delete 2")).is_err());
        let w = words("adopt-next-key lookup a1");
        assert_eq!(parse(&ADOPT_NEXT_KEY, &w).unwrap().leaf.path, ["adopt-next-key", "lookup"]);
        let w = words("topup lab 5 again");
        let p = parse(&TOPUP, &w).unwrap();
        assert_eq!((p.opt(2), p.opt(3)), (None, Some("again")));
    }

    #[test]
    fn a_flag_value_may_be_a_quoted_string() {
        let p = parse_line(&FEEDBACK, r#"feedback --clause "a b \"c\" \\ d" --from w-1 text here"#).unwrap();
        assert_eq!(p.flag("--clause").flatten(), Some(r#"a b "c" \ d"#));
        assert_eq!(p.flag("--from").flatten(), Some("w-1"));
        assert_eq!(p.arg(0), "text here");
        assert!(parse_line(&FEEDBACK, r#"feedback --clause "unterminated text"#).is_err());
        assert!(parse_line(&FEEDBACK, "feedback --from").is_err());
    }
}
