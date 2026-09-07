import LeanDag.Barnacle.Model.Rule
import LeanDag.Properties.Carrier
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
/-!
# A Barnacle rule is a `DagRule`

Not part of the audit surface. How Barnacle's `BaseRule` instantiations
share the protocols' carriers.

`BaseRule` extends `Properties.DagRule`, so `toDagRule` is the parent
projection and every Barnacle instance names the protocol's own carrier
for it: `Barnacle.mysticeti.toDagRule` *is*
`MysticetiProperties.mysticetiRule`, by `rfl`. One carrier per rule,
and the properties a protocol proves at it are Barnacle's with no
bridge. The two `Laws` that are properties under another name — `agree`
and `candidates` — used to be bridged the other way here; every
consumer now reads the property at the protocol's carrier directly.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

@[simp] theorem toDagRule_ids (R : BaseRule Validator BlockId Payload) :
    R.toDagRule.ids = R.ids := rfl

@[simp] theorem toDagRule_block (R : BaseRule Validator BlockId Payload) :
    R.toDagRule.block = R.block := rfl

end Barnacle

end LeanDag
