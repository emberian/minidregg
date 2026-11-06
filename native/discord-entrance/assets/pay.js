// The door's wallet payment, isomorphic like passwap.js: pass in the solpay namespace (assets/solpay.js), the quote the
// status page embeds (recipient, mint, tokenProgram, decimals, amountAtomic, memo, id, rpc), and the page's
// connection and fetch. Nothing here decides anything: the quote is the processor's, the transaction is the
// wallet's to sign, the cluster's to admit, and the door's observer matches what landed.
//
//   const pay = makeDoorPay(solpay, quote, { conn, fetch })
//   pay.instructions(owner, createRecipientAta)
//                                -> [createAtaIdempotent(recipient's ATA) when it is missing,
//                                    transferChecked(owner's ATA -> recipient's ATA, amount, decimals), memo(exact bytes)]
//   await pay.pay(provider, say, onSent)   (provider.signTransaction takes the unsigned transaction's wire bytes
//                                   and returns the signed wire bytes: the Wallet Standard shape)
//                                -> { signature, status, tx }: connect, check the payer's token account (the
//                                   recipient's is created in the same transaction if absent), build, sign; refuse a
//                                   signed transaction that is not exactly
//                                   the one built; send from the browser; hand the signature to onSent at once (the
//                                   payer holds it before anything else can fail); post it to /join/paid (the paste
//                                   path's field) and throw, naming the signature, unless the door accepted it.
//   pay.stale()                  -> null: a payment after the quote's expiry hour is a pending claim the door
//                                   processor accepts with the hosted account's key (`mini pay-claim`)
(function (root, factory) {
  if (typeof module === "object" && module.exports) module.exports = factory();
  else root.makeDoorPay = factory();
})(typeof self !== "undefined" ? self : this, function () {
  return function makeDoorPay(sol, quote, deps) {
    const { PublicKey, ATA_PROGRAM, MEMO_PROGRAM } = sol; // SPL Memo v2 is the one to write (the watcher reads both memo programs)
    for (const k of ["recipient", "mint", "tokenProgram", "decimals", "amountAtomic", "memo", "id"]) {
      if (quote[k] === undefined || quote[k] === null || quote[k] === "") throw new Error("the quote lacks " + k);
    }
    const mint = new PublicKey(quote.mint), tokenProgram = new PublicKey(quote.tokenProgram), recipient = new PublicKey(quote.recipient);
    const amount = BigInt(quote.amountAtomic), decimals = Number(quote.decimals);
    if (!(decimals >= 0 && decimals <= 38)) throw new Error("the quote's decimals are not a token's");
    const memoBytes = new TextEncoder().encode(quote.memo); // the exact bytes `mini join` expects: the memo string, UTF-8, nothing added
    const ata = (owner) => sol.ata(owner, tokenProgram, mint);
    const now = deps.now || (() => Date.now());

    // The door processor holds the hosted account's mini.key and auto-accepts a late payment
    // (pendingV2) via `mini pay-claim`, so the browser never refuses a quote after expiryHour.
    function stale() {
      return null;
    }

    // The wallet must sign exactly what was built: the same instructions, accounts, flags and data,
    // and the payer as fee payer, compared as the wire carries them (the fee payer is writable there). A wallet (or an extension in between) that changed the recipient,
    // the amount or the memo is refused before anything is sent.
    function sameAsBuilt(signed, owner, builtWire) {
      const want = sol.decodeWire(builtWire).instructions;
      const got = signed.instructions || [];
      if (got.length !== want.length) return "the wallet returned " + got.length + " instructions where " + want.length + " were built";
      for (let i = 0; i < want.length; i++) {
        const a = want[i], b = got[i];
        if (!a.programId.equals(b.programId)) return "instruction " + i + " names another program";
        if (a.keys.length !== b.keys.length || a.keys.some((k, j) => !k.pubkey.equals(b.keys[j].pubkey) || k.isSigner !== b.keys[j].isSigner || k.isWritable !== b.keys[j].isWritable)) return "instruction " + i + " names other accounts";
        const da = Uint8Array.from(a.data), db = Uint8Array.from(b.data);
        if (da.length !== db.length || da.some((x, j) => x !== db[j])) return "instruction " + i + " carries other data";
      }
      if (!signed.feePayer || !signed.feePayer.equals(owner)) return "the fee payer is not your wallet";
      return null;
    }

    function instructions(owner, createRecipientAta) {
      const ixs = [sol.transferChecked({ tokenProgram, source: ata(owner), mint, destination: ata(recipient), owner, amount, decimals }), sol.memo(owner, memoBytes)];
      if (createRecipientAta) {
        ixs.unshift(sol.createAtaIdempotent({ payer: owner, ata: ata(recipient), owner: recipient, mint, tokenProgram }));
      }
      return ixs;
    }

    async function pay(provider, say, onSent) {
      say = say || (() => {});
      onSent = onSent || (() => {});
      const late = stale();
      if (late) throw new Error(late);
      say("connecting to " + (provider.name || "the wallet"));
      const connected = await provider.connect();
      const owner = new PublicKey(((connected && connected.publicKey) || provider.publicKey).toString());
      say("checking the token accounts");
      const to = ata(recipient);
      const createRecipientAta = !(await deps.conn.getAccountInfo(to));
      const from = ata(owner);
      const balance = await deps.conn.getTokenAccountBalance(from).catch(() => null);
      if (!balance) {
        throw new Error("your wallet " + owner.toBase58() + " has no associated token account " + from.toBase58() + " for this mint (this page pays from the associated account only: move the tokens there in your wallet, or pay from any account and paste the transaction signature below)");
      }
      if (BigInt(balance.value.amount) < amount) {
        throw new Error("your wallet " + owner.toBase58() + " holds " + balance.value.amount + " of this token in its associated account; the quote needs " + quote.amountAtomic + " atomic units.");
      }
      const { blockhash } = await deps.conn.getLatestBlockhash("confirmed");
      const message = sol.compileMessage({ feePayer: owner, recentBlockhash: blockhash, instructions: instructions(owner, createRecipientAta) });
      say("the wallet is signing");
      const builtWire = sol.unsignedWire(message);
      const signedBytes = Uint8Array.from(await provider.signTransaction(builtWire));
      let signed;
      try { signed = sol.decodeWire(signedBytes); } catch (e) { throw new Error("refused, nothing was sent: the wallet returned a transaction this page cannot read (" + e.message + "). Pay by the paste path below with a wallet you trust."); }
      const changed = sameAsBuilt(signed, owner, builtWire);
      if (changed) throw new Error("refused, nothing was sent: " + changed + ". Pay by the paste path below with a wallet you trust.");
      const lateNow = stale();
      if (lateNow) throw new Error(lateNow);
      say("sending from this browser to " + (quote.rpc || "the cluster"));
      const signature = await deps.conn.sendRawTransaction(signedBytes, { skipPreflight: false });
      onSent(signature);
      say("sent " + signature + "; posting it to the door");
      const body = new URLSearchParams({ id: quote.id, transaction: signature }).toString();
      let res;
      try {
        res = await deps.fetch("/join/paid", { method: "POST", headers: { "Content-Type": "application/x-www-form-urlencoded" }, body, credentials: "same-origin", redirect: "follow" });
      } catch (e) {
        throw new Error("your payment was sent (" + signature + ") but the door could not be reached: paste that signature below; do not pay again. (" + String(e && e.message || e) + ")");
      }
      if (!res.ok) {
        const page = res.text ? await res.text().catch(() => "") : "";
        const why = page.replace(/<[^>]*>/g, " ").replace(/\s+/g, " ").replace(/^\s*Not accepted\s*/, "").replace(/\s*Back\s*$/, "").trim().slice(0, 300);
        throw new Error("your payment was sent (" + signature + ") but the door did not accept it (" + res.status + (why ? ": " + why : "") + "). Do not pay again: paste that signature below once the door accepts posts.");
      }
      return { signature, status: res.status, tx: signed };
    }
    return { ATA_PROGRAM, MEMO_PROGRAM, ata, instructions, pay, stale, sameAsBuilt };
  };
});
