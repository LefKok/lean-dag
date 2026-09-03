import LeanDag.Barnacle.Model.Rule
import LeanDag.Properties.Carrier

/-!
# A Barnacle rule is a `DagRule`

Not part of the audit surface. The coercion that lets the six existing
`BaseRule` instantiations — Mysticeti, Odontoceti, Nemo, Hybrid,
Hydrozoan, Optimal-Hydrozoan — serve as carriers for
`docs/target-properties.md` without being restated.

**The dependency runs this way on purpose.** Barnacle is a mechanism,
and `Properties` is what mechanisms are stated against; a coercion
living in `Properties` would make every other mechanism depend on the
adaptive leader count. So it lives here, and `Properties` imports
nothing of Barnacle.

The eventual tidier form is for `BaseRule` to `extend DagRule`. That
edits a frozen `Model/` file, so it is not done here; the coercion is
additive and settles the same question.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **Every Barnacle rule is a carrier.** The fields `DagRule` asks for
are a sub-record of `BaseRule`'s. -/
def BaseRule.toDagRule (R : BaseRule Validator BlockId Payload) :
    Properties.DagRule Validator BlockId Payload where
  Universe := R.Universe
  View := R.View
  block := R.block
  ids := R.ids
  viewIds := R.viewIds
  Decided := R.Decided

@[simp] theorem toDagRule_ids (R : BaseRule Validator BlockId Payload) :
    R.toDagRule.ids = R.ids := rfl

@[simp] theorem toDagRule_block (R : BaseRule Validator BlockId Payload) :
    R.toDagRule.block = R.block := rfl

end Barnacle

end LeanDag
