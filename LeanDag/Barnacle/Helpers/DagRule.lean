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
bridge. What remains below is the other direction: the two laws that
are properties under another name.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

@[simp] theorem toDagRule_ids (R : BaseRule Validator BlockId Payload) :
    R.toDagRule.ids = R.ids := rfl

@[simp] theorem toDagRule_block (R : BaseRule Validator BlockId Payload) :
    R.toDagRule.block = R.block := rfl

/-! ## What the laws already say

Two of the six required properties are `Laws` under another name, so
every Barnacle rule has them the moment it has a carrier. That is six
rules at once (`docs/target-properties.md` §11.2), and it is why
`BaseRule.toDagRule` was worth taking before adding carriers one at a
time.

The carrier's `causal` law is a field of `BaseRule` under the same
name, so the coercion carries it. `Banded` is not a law and would not
be: it is the induction each protocol owes. -/

/-- **A4 is `Agree`.** The law and the property are the same statement. -/
theorem agree_toDagRule (R : BaseRule Validator BlockId Payload) (L : BaseRule.Laws R) :
    Properties.Agree R.toDagRule :=
  fun S _ V₁ V₂ k v₁ v₂ h₁ h₂ => L.agree S V₁ V₂ k v₁ v₂ h₁ h₂

/-- **And `candidates` is `CommitsCandidate`.** `BaseRule.IsLeaderBlock`
and `DagRule.IsCandidate` are the same three conjuncts — present, at the
slot's round, by the slot's leader — so this is the law verbatim. -/
theorem commitsCandidate_toDagRule (R : BaseRule Validator BlockId Payload)
    (L : BaseRule.Laws R) : Properties.CommitsCandidate R.toDagRule :=
  fun S _ V k lead h => L.candidates S V k lead h

/-- **And `decided_of_directCommitIn` is `CommitsDirect`**, at the
rule's own direct predicate. The clause had no consumer; the property
does (`Barnacle/Healthy/`). -/
theorem commitsDirect_toDagRule (R : BaseRule Validator BlockId Payload)
    (L : BaseRule.Laws R) :
    Properties.CommitsDirect R.toDagRule (fun {_} V => R.DirectCommitIn V) :=
  fun S _ V k lead hc hd => L.decided_of_directCommitIn S V k lead hc hd

end Barnacle

end LeanDag
