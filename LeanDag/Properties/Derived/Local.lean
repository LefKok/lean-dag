import LeanDag.Properties.Agreement

/-!
# Locality

`docs/target-properties.md` §11.4b. Like `Persist`, a statement a
mechanism reads which no protocol proves directly any more: both
instances obtain it from `Banded` (`Derived/FromBand.lean`).

*If two DAGs agree above round `r`, they decide alike at every slot
whose round is at least `r`.* Stated as agreement rather than
existence, which is what makes it worth having: a protocol proving it
gets garbage collection at **every** admissible horizon, not at one.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **Locality.** A verdict at a slot whose round is at or above `r`
depends on the DAG and the view only above `r`. -/
def Local (R : DagRule Validator BlockId Payload) : Prop :=
  ∀ (S : Slots Validator) (U U' : R.Universe) (r : ℕ), AgreeAbove R U U' r →
    ∀ (V : R.View U) (V' : R.View U'), ViewAgreeAbove R V V' r →
    ∀ (k : ℕ), r ≤ S.slotRound k →
    ∀ (v : Option BlockId), R.Decided S V k v → R.Decided S V' k v

/-- Locality in both directions, which is what agreement gives: the
hypothesis is symmetric, so a protocol proving `Local` decides the same
on either side. -/
theorem Local.iff (hl : Local R) {S : Slots Validator} {U U' : R.Universe} {r : ℕ}
    (h : AgreeAbove R U U' r) {V : R.View U} {V' : R.View U'}
    (hv : ViewAgreeAbove R V V' r) {k : ℕ} (hk : r ≤ S.slotRound k)
    {v : Option BlockId} :
    R.Decided S V k v ↔ R.Decided S V' k v :=
  ⟨hl S U U' r h V V' hv k hk v,
    hl S U' U r h.symm V' V (ViewAgreeAbove.symm h hv) k hk v⟩

end Properties

end LeanDag
