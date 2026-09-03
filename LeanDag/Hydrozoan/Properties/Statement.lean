import LeanDag.Hydrozoan.Helpers.Locality
import LeanDag.Hydrozoan.Helpers.Truncation

/-!
# Hydrozoan conforms to the target properties — statement

**HZ9.** Hydrozoan's universes are block DAGs, and its verdicts survive
a growing DAG **unconditionally**, a truncation, and a renumbering.

The second half is the claim `docs/target-properties.md` §3.2 predicts
for this protocol and not for the core. Hydrozoan's direct skip counts
blames at the slot; the core's quantifies over candidates and so is
vacuous where a slot has no candidate, which an extension can supply. A
count of blocks that are still present does not move, so no side
condition is needed here — `Persist.Unconditional` rather than
`Persist` at some `Ok`.

`Local` says a verdict at a slot reads nothing below that slot's round,
and `Reindex` that verdicts move with a consistent renumbering of rounds
and slots. Together they are what garbage collection consumes, at every
admissible horizon rather than at one.

What conformance is worth: any mechanism stated against these
properties applies to Hydrozoan without further proof. Crash recovery
is the first (`Properties/Arcs/SafeSkip.lean`) and garbage collection
the second (`Properties/Arcs/GC.lean`); the mechanisms that follow cost
this arc nothing more.

Statement only; the proof lives in `Proof.lean`.
-/

namespace LeanDag

namespace Hydrozoan

namespace Properties

/-- **HZ9.** Hydrozoan is a lawful carrier; it persists under every
extension, reads nothing below a slot's round, and commutes with a
renumbering. -/
def Statement : Prop :=
  ∀ (Replica : Type) [Fintype Replica] [DecidableEq Replica]
    (BlockId : Type) [DecidableEq BlockId] [LinearOrder BlockId]
    [LeanDag.Hydrozoan.Faults Replica],
    LeanDag.Properties.Causal (rule (Replica := Replica) (BlockId := BlockId)) ∧
    LeanDag.Properties.Persist.Unconditional
      (rule (Replica := Replica) (BlockId := BlockId)) ∧
    LeanDag.Properties.Local (rule (Replica := Replica) (BlockId := BlockId)) ∧
    LeanDag.Properties.LocalTruncate (rule (Replica := Replica) (BlockId := BlockId))

end Properties

end Hydrozoan

end LeanDag
