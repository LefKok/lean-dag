import LeanDag.Barnacle.Model.Run
/-!
# The segmented adaptive run

A run whose next configuration takes force at the round the
reconfiguration fell due rather than at the anchor's round: the shape the
Hammerhead paper's `ORDERHISTORY` gives it (`adaptive-leaders.md` §9). A
configuration governs a fixed span of rounds, decisions are taken under
it as far as the anchor that closes the span, and **output stops at the
span's own boundary**.

That is the only difference from Barnacle, and it is one field:
`Boundary.atThreshold` against `Boundary.atAnchor` (D19, D21). Naming an
anchor may run past the boundary, because that is how the switch is
detected and every validator detects it at the same anchor; ordering
never does. The two bounds are what make the mechanism
asynchrony-tolerant — `closed` reaches the anchor, whose round moves with
the network, while `rangeLedger` reads only `(start k, start (k + 1)]`,
fixed before the anchor is looked for.

Everything else — the run, its ledger, agreement, the ledger laws,
conservativity, validity and progress — is `Barnacle.Run` and its
theorems at this boundary, and is not restated here.
-/

namespace LeanDag

namespace Adaptive

open Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A segmented run closed up to height `K`**: `Barnacle.Run` at the
boundary that takes force where the reconfiguration fell due. -/
abbrev SegRun (R : BaseRule Validator BlockId Payload) (P : Params)
    (upd : UpdateRule R) (C₀ : Config Validator) (U : R.Universe) (V : R.View U)
    (K : ℕ) : Type :=
  Run R P Boundary.atThreshold upd C₀ U V K

end Adaptive

end LeanDag
