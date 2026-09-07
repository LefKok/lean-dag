import LeanDag.FinWhale.Model.Decision

/-!
# FinWhale — a validator's view, and the rules relative to one

A **view** is part of the universe closed under references, and it is a
`Dag` in its own right: validity and non-equivocation are inherited from
the universe, and the view's completeness is its closure. `IsView` states
that and `restrict` builds the DAG.

`viewCommit` and `viewSkip` are the direct rules as a validator with that
view evaluates them, which is how the protocol actually runs — every
count of the rule taken over the blocks the validator holds. `View.lean`
proves what transports between a view and the universe and what does not.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}
variable {S : Slots Validator}

/-! **A view** is the record's (`BlockRecord.View`): part of the universe,
closed under references. **A view is a DAG** by `View.toRecord`: validity
and non-equivocation are inherited, and the view's completeness is its
closure. -/

/-! ## The exclusions, on two views -/

/-- The direct commit rule as a validator with view `V` evaluates it. -/
def viewCommit (S : Slots Validator) (D : Dag Validator BlockId Payload) (V : D.View)
    (r : ℕ) (l : BlockId) : Prop :=
  l ∈ slotBlocks S V.toRecord r ∧ DirectCommit V.toRecord l

/-- And the direct skip rule. -/
def viewSkip (S : Slots Validator) (D : Dag Validator BlockId Payload) (V : D.View)
    (r : ℕ) : Prop :=
  DirectSkip S V.toRecord r

end FinWhale

end LeanDag
