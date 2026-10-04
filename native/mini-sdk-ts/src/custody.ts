// Attempt custody: the same state machine as native/mini-sdk/src/custody.rs.
// A lost reply → lookup of the SAME call; a successor only after definite non-admission, with fresh nonces.
import { equalBytes, sha256, SdkError } from "./bytes.ts";
import type { Json } from "./contracts.ts";

export const CONFIRMATIONS = ["installed", "replayed", "recoveredAfterUncertainResponse"];

export interface Receipt { confirmation: string; transactionId: string; eventId: string; acceptedCount: string; worldRoot: string }
export type Outcome = { kind: "confirmed"; receipt: Receipt } | { kind: "refused"; refusal: Json } | { kind: "undecided"; value: Json };

const field = (v: Json, k: string): string | undefined => {
  if (typeof v !== "object" || v === null || Array.isArray(v)) return undefined;
  const x = v[k];
  return typeof x === "string" ? x : undefined;
};

export function outcomeOf(v: Json): Outcome {
  const type = field(v, "type");
  if (type === "confirmed") {
    const [confirmation, transactionId, eventId, acceptedCount, worldRoot] =
      ["confirmation", "transactionId", "eventId", "acceptedCount", "worldRoot"].map((k) => field(v, k));
    if (confirmation && CONFIRMATIONS.includes(confirmation) && transactionId !== undefined && eventId !== undefined
      && acceptedCount !== undefined && worldRoot !== undefined) {
      return { kind: "confirmed", receipt: { confirmation, transactionId, eventId, acceptedCount, worldRoot } };
    }
    return { kind: "undecided", value: v };
  }
  if (type === "refused") return { kind: "refused", refusal: v };
  return { kind: "undecided", value: v };
}

/** Any confirmation wins; otherwise the newest outcome decides. */
export function classify(history: Json[]): Outcome | null {
  for (let i = history.length - 1; i >= 0; i--) {
    const o = outcomeOf(history[i]);
    if (o.kind === "confirmed") return o;
  }
  return history.length ? outcomeOf(history[history.length - 1]) : null;
}

export type Transmission = { kind: "answered"; outcome: Json } | { kind: "unsent"; detail: string } | { kind: "uncertain"; detail: string };

export type Phase =
  | { kind: "drafted" } | { kind: "prepared" }
  | { kind: "sealed"; call: Uint8Array }
  | { kind: "uncertain"; call: Uint8Array; detail: string }
  | { kind: "confirmed"; call: Uint8Array; receipt: Receipt }
  | { kind: "refused"; call: Uint8Array; refusal: Json }
  | { kind: "neverSent"; call: Uint8Array; detail: string };

export class Attempt {
  phase: Phase = { kind: "drafted" };
  readonly invocation: string;
  readonly number: number;
  readonly intentNonce: string;
  readonly commandNonce: string;
  constructor(invocation: string, number: number, intentNonce: string, commandNonce: string) {
    this.invocation = invocation;
    this.number = number;
    this.intentNonce = intentNonce;
    this.commandNonce = commandNonce;
  }

  static first(invocation: string, intentNonce: string, commandNonce: string): Attempt {
    return new Attempt(invocation, 1, intentNonce, commandNonce);
  }
  prepared(): void {
    if (this.phase.kind !== "drafted") throw this.refuse("prepare");
    this.phase = { kind: "prepared" };
  }
  sealed(call: Uint8Array): void {
    if (this.phase.kind !== "prepared") throw this.refuse("seal");
    this.phase = { kind: "sealed", call: sha256(call) };
  }
  /** The SHA-256 of the one call this attempt may (re)transmit or look up. */
  call(): Uint8Array | null {
    return this.phase.kind === "sealed" || this.phase.kind === "uncertain" ? this.phase.call : null;
  }
  record(call: Uint8Array, t: Transmission): Phase {
    const sha = this.call();
    if (!sha) throw this.refuse("transmit or look up");
    if (!equalBytes(sha256(call), sha)) throw new SdkError("these are not the attempt's retained call bytes; never transmit another call under this attempt");
    const wasUncertain = this.phase.kind === "uncertain";
    if (t.kind === "answered") {
      const o = outcomeOf(t.outcome);
      this.phase = o.kind === "confirmed" ? { kind: "confirmed", call: sha, receipt: o.receipt }
        : o.kind === "refused" ? { kind: "refused", call: sha, refusal: o.refusal }
        : { kind: "uncertain", call: sha, detail: JSON.stringify(o.value) };
    } else if (t.kind === "unsent") {
      this.phase = wasUncertain ? { kind: "uncertain", call: sha, detail: t.detail } : { kind: "neverSent", call: sha, detail: t.detail };
    } else {
      this.phase = { kind: "uncertain", call: sha, detail: t.detail };
    }
    return this.phase;
  }
  successor(intentNonce: string, commandNonce: string): Attempt {
    switch (this.phase.kind) {
      case "sealed": case "uncertain": throw new SdkError("the retained call may be admitted: look it up (same bytes) instead of a new attempt");
      case "confirmed": throw new SdkError("the invocation is confirmed; there is no successor");
    }
    if (intentNonce === this.intentNonce || commandNonce === this.commandNonce) throw new SdkError("a successor attempt needs fresh nonces");
    return new Attempt(this.invocation, this.number + 1, intentNonce, commandNonce);
  }
  private refuse(step: string): SdkError {
    return new SdkError(`attempt ${this.number} of ${this.invocation} cannot ${step} from ${this.phase.kind}`);
  }
}
