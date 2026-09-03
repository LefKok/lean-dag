import LeanDag.Properties.Truncate

/-!
# Garbage collection, for any protocol with `LocalTruncate`

`docs/target-properties.md` G2, the garbage-collection half.

**This file is thin on purpose, and it was not always going to be.** An
earlier version composed a locality property with a re-indexing one and
looked like it was doing work; the composition had hypotheses nothing
could satisfy, because restriction and renumbering are not separately
realisable (`Properties/Truncate.lean` records why). What replaced it
is a single property, so garbage collection *is* that property applied,
and the two corollaries below are the directions a deployment uses.

The depth sits in the per-protocol proof of `LocalTruncate`: one
induction, paid once, serving every horizon and every base slot.
-/

namespace LeanDag

namespace Properties

namespace Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}
variable {S S' : Slots Validator} {U U' : R.Universe} {G d : ℕ}
variable {V : R.View U} {V' : R.View U'}

/-- **A verdict survives the cut**, at the replica's own numbering. -/
theorem decided_of_truncate (h : LocalTruncate R) (ht : Truncates R U U' S S' G d)
    (hv : ViewTruncates R V V' G) {k : ℕ} {v : Option BlockId}
    (hd : R.Decided S V (d + k) v) : R.Decided S' V' k v :=
  (h S S' U U' G d ht V V' hv k v).mp hd

/-- **And a verdict of the truncation is a verdict of the whole DAG**,
which is what lets a pruned replica be compared with one that never
pruned. -/
theorem decided_of_truncated (h : LocalTruncate R) (ht : Truncates R U U' S S' G d)
    (hv : ViewTruncates R V V' G) {k : ℕ} {v : Option BlockId}
    (hd : R.Decided S' V' k v) : R.Decided S V (d + k) v :=
  (h S S' U U' G d ht V V' hv k v).mpr hd

end Arcs

end Properties

end LeanDag
