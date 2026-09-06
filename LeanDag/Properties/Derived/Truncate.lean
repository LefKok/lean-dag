import LeanDag.Properties.Truncate
import LeanDag.Properties.Compose
import LeanDag.Properties.Band

/-!
# Truncation invariance

`docs/target-properties.md` §3.4b. No longer an obligation: it follows
from the band, once the band carries an offset.

A truncation moves rounds, and the band once compared them by equality,
which is why this was a separate obligation for as long as it was. With
`AgreeBand` reading both universes in a common frame, a cut is the
instance `g = 0`, `g' = G`, and reading it backwards is the instance
with the pairs swapped. Both directions of the `↔` are therefore
instances of one property, which is what the two offsets were for.

What the band was already right about is the horizon's references: its
clause is guarded strictly above the floor, which is exactly the licence
a cut needs when it empties its bottom layer.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **Truncation invariance.** A replica that has pruned below the
horizon reaches exactly the verdicts it would have reached with its
whole history, at its own numbering.

An `↔`, because both directions are consumed: a joiner needs verdicts
to survive the cut, and cross-cut agreement needs them to come back. -/
def LocalTruncate (R : DagRule Validator BlockId Payload) : Prop :=
  ∀ (S S' : Slots Validator) (U U' : R.Universe) (G d : ℕ),
    Truncates R U U' S S' G d →
    ∀ (V : R.View U) (V' : R.View U'), ViewAgreeAbove R V V' G →
    ∀ (k : ℕ) (v : Option BlockId), R.Decided S V (d + k) v ↔ R.Decided S' V' k v

/-- **Truncation invariance falls out of the band** — `decided_of_rebased`
at a cut, whose settling round is its horizon. -/
theorem LocalTruncate.of_banded (h : Banded R) : LocalTruncate R :=
  fun S S' U U' G d ht V V' hv k v =>
    decided_of_rebased h (Rebased.of_truncates ht) hv k
      (le_trans ht.base (S.mono (Nat.le_add_right d k))) v

end Properties

end LeanDag
