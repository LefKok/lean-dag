import LeanDag.Barnacle.Model.Rule
import LeanDag.Properties.Carrier
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct

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
are a sub-record of `BaseRule`'s, view soundness included, so the
coercion needs no laws: a rule is a carrier before it has proved
anything, which is what lets the properties be the hypotheses of
Barnacle's own theorems rather than a parallel interface. -/
def BaseRule.toDagRule (R : BaseRule Validator BlockId Payload) :
    Properties.DagRule Validator BlockId Payload where
  Universe := R.Universe
  View := R.View
  block := R.block
  ids := R.ids
  viewIds := R.viewIds
  viewSound := R.viewSound
  viewComplete := R.viewComplete
  Decided := R.Decided

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

`Causal` is not among them: `Laws` states the structural facts for
*views* — `view_complete` — and not for universes, so it gives neither
completeness nor the round condition on references. `Banded` is not
either, and would not be: it is the induction each protocol owes. -/

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
