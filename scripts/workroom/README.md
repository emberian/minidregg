# Mini content workroom fixture

`provision.sh HOST NEW_DIRECTORY` creates a fresh Mini deployment using the
ordinary source-authored birth and delegation path. It births parent grain
7101, tool grain 7102, scalar publication object 7003, and a separate empty
kernel content object 8001. The tool receives object 8001 mutation/observe
capability 95 and distinct read-only observe capability 96. Its owner has
capability 89; the policy-control capability is 90. Object 8001 avoids the
separate provider grain 7004. The script refuses an existing directory and
leaves `runtime-config.base.json` with both named reads and publication
allowlists. The provider owner adds the actual Hermes command to `commands`
and starts the controller in a fresh process; this script makes no provider
request and creates no application data store.
Set `WORKROOM_PARENT_TASK` and `WORKROOM_TOOL_TASK` to distinct canonical
positive IDs when another live deployment uses the defaults; the fixture
retains the same capability and subject map. It rejects collisions with its
fixed objects and control resources. The separate upstream Hermes workroom
run uses 7301 and 7302 to avoid the retained scalar 7101 controller.

`probe-content.sh HOST PINNED_CONFIG TOOL_KEY NEW_DIRECTORY` exercises that
fresh workroom through the native signed Mini client. It queries with read
capability 96, creates text atom 7401 using mutation capability 95, queries
the accepted page, edits the same atom with its complete observed old record,
and queries the revised page. It refuses a nonempty starting page. The two
fixed note strings are untrusted text bytes; Host.Json and ContentResource
own authoring and admission. This singleton probe tests the content cell and
the grant split. The later Hermes `mini_publish` run must make a separate
grain-settlement/content joint call; a singleton content probe cannot stand
in for that result.

Both scripts retain their exact intents, signed attempts, outcomes, and
resource views in their private evidence directories. A fn transfer of a
joint content publication carries the accepted A receipt and signed command
to B's content inbox; it does not apply A's object 8001 edits as B effects.
