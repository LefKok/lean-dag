import LeanDag.Properties.Carrier
/-!
# Agreement: two views decide alike

`docs/target-properties.md` §4. The safety theorem every protocol has
(the core's M6, `decided_agree`), as a property of the carrier: under one
schedule, over one universe, two views cannot hold different verdicts at
a slot.

Nothing built before the schedule family needed it — persistence,
locality and truncation each compare a verdict with a verdict, never two
views at one slot — and the adaptive fixpoint's uniqueness is nothing
but this property applied through `DecidedBelow.reschedule`.
`Barnacle.Laws.agree`
states the same thing over `BaseRule`.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **Agreement.** Under one schedule and over one universe, any two
views' verdicts at a slot coincide. -/
def Agree (R : DagRule Validator BlockId Payload) : Prop :=
  ∀ (S : Slots Validator) {U : R.Universe} (V₁ V₂ : R.View U) (k : ℕ)
    (v₁ v₂ : Option BlockId), R.Decided S V₁ k v₁ → R.Decided S V₂ k v₂ → v₁ = v₂

end Properties

end LeanDag
