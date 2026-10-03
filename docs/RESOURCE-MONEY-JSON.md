# Canonical Book command authoring

A native invocation account target uses payload `moneyConsent` with exactly four fields: `type`, `batch`, `positions`, `funding`. `batch` is null except for one signed carrier, where it has `expectedBookRoot` and an ordered `operations` array. `positions` lists the zero-based operation source positions consented by this containing account. Destination accounts also have their own signed account targets. A payer may merge its actual compute funding consent in the final account target.

Every integer is a canonical decimal string. Funding is null or `{asset,credits,expectedPayerBalance,expectedBookRoot}`. Operations are exact typed JSON objects: transfer/fee `{type,source,destination,asset,amount}`; mint `{type,asset,destination,amount}`; burn `{type,source,asset,amount}`; lease `{type,leaseId,holder,lessor,asset,rate,epochs,startsAt}`. Unknown, missing or noncanonical fields refuse. JSON authoring constructs actual canonical Operation values and uses the native codec, rather than accepting a caller-supplied Book post.

Authoring is not admission. The receiver binds exact original Book/root, fee-first intermediate balances, ordered solvency, source-position coverage, current account metadata and law, signed capability/observe grants and both net changes and gross debit bounds. Mint and burn additionally require their distinct existing capability verbs. Room/return effects share the same native atomic intent. Inspection exposes the complete typed declaration; account metadata has no authored content publication.

This interface is WIP pending the merged Host and actual signed native receiving checks. Foundation preparation and its named proof gates passed a separate scoped check; that alone is not a native settlement acceptance claim.
