import LeanDag.Properties.Carrier

/-!
# Locality: a verdict reads nothing below its own slot

`docs/target-properties.md` §3.1, the property garbage collection rests
on.

*If two DAGs agree above round `r`, they decide alike at every slot
whose round is at least `r`.*

Stated as agreement rather than existence, which is what makes it worth
having: a protocol proving it gets garbage collection at **every**
admissible horizon, not at one. The indirect rule's recursion runs
upward from the slot — an anchor sits above what it decides — so the
region the hypothesis covers is closed under the recursion, which is
`Causal.refs_above`. The chain is unbounded above, so no window
formulation would serve; the condition has to be a genuine lower bound.

**What locality does not cover.** A truncation restricts *and* rebases:
it drops what lies below the horizon and renumbers what remains to
start at zero. Locality is about the restriction alone, and the
renumbering is `Reindex.lean`. The two compose only through the
universe that has been restricted and not yet renumbered, which
`Arcs/GC.lean` takes as a parameter and a protocol must exhibit.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **Two views agree above a round.** Read at the source universe's
rounds, which `AgreeAbove` makes the same as the target's wherever the
question arises. -/
def ViewAgreeAbove (R : DagRule Validator BlockId Payload) {U U' : R.Universe}
    (V : R.View U) (V' : R.View U') (r : ℕ) : Prop :=
  ∀ b, b ∈ R.ids U → r ≤ (R.block U b).round →
    (b ∈ R.viewIds V ↔ b ∈ R.viewIds V')

/-- **Locality.** A verdict at a slot whose round is at or above `r`
depends on the DAG and the view only above `r`. -/
def Local (R : DagRule Validator BlockId Payload) : Prop :=
  ∀ (S : Slots Validator) (U U' : R.Universe) (r : ℕ), AgreeAbove R U U' r →
    ∀ (V : R.View U) (V' : R.View U'), ViewAgreeAbove R V V' r →
    ∀ (k : ℕ), r ≤ S.slotRound k →
    ∀ (v : Option BlockId), R.Decided S V k v → R.Decided S V' k v

namespace AgreeAbove

variable {U U' : R.Universe} {r : ℕ}

/-- **Causal history above the horizon is the same history.** A path
from `A` descends one round at a time, so if it ends at or above `r`
every block on it sits above `r` — strictly, except at the end, which
is exactly where `AgreeAbove` stops comparing references. -/
theorem reaches_of (hc : Causal R) (h : AgreeAbove R U U' r)
    {A : BlockId} (hA : A ∈ R.ids U) :
    ∀ {C : BlockId}, ReachesFrom (R.block U) A C → r ≤ (R.block U C).round →
      ReachesFrom (R.block U') A C := by
  intro C hre
  induction hre with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | @tail b c hAb hstep ih =>
      intro hcr
      have hb : b ∈ R.ids U := (hc U).mem_ids_of_reaches hA hAb
      have hstep' : c ∈ (R.block U b).refs := hstep
      have hround := (hc U).refs_round b hb c hstep'
      refine (ih (by omega)).tail ?_
      show c ∈ (R.block U' b).refs
      rw [h.refs b hb (by omega)]
      exact hstep'

/-- And so it agrees in both directions. -/
theorem reaches_iff (hc : Causal R) (h : AgreeAbove R U U' r)
    {A C : BlockId} (hA : A ∈ R.ids U) (hAr : r ≤ (R.block U A).round)
    (hC : C ∈ R.ids U) (hCr : r ≤ (R.block U C).round) :
    ReachesFrom (R.block U') A C ↔ ReachesFrom (R.block U) A C := by
  refine ⟨fun hre => ?_, fun hre => reaches_of hc h hA hre hCr⟩
  exact reaches_of hc h.symm ((h.mem A).mp ⟨hA, hAr⟩).1 hre
    (by rw [h.round C hC hCr]; exact hCr)

end AgreeAbove

namespace ViewAgreeAbove

variable {U U' : R.Universe} {V : R.View U} {V' : R.View U'} {r : ℕ}

/-- Agreement of views is symmetric, given agreement of the universes
that fixes the rounds. -/
theorem symm (h : AgreeAbove R U U' r) (hv : ViewAgreeAbove R V V' r) :
    ViewAgreeAbove R V' V r := by
  intro b hb hr
  have hU : b ∈ R.ids U ∧ r ≤ (R.block U b).round := (h.mem b).mpr ⟨hb, hr⟩
  exact (hv b hU.1 hU.2).symm

end ViewAgreeAbove

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
