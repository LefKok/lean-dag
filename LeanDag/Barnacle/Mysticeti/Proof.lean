import LeanDag.Barnacle.Mysticeti.Statement
import LeanDag.Mysticeti.Liveness
import LeanDag.Mysticeti.Properties
/-!
# Barnacle over Mysticeti — proof

Generated proof layer; not part of the audit surface. Every law is a
**property** applied: the view structure's own fields, `rfl` for the two
id equations, then `Agree`, `CommitsDirect` and `CommitsCandidate`.
`MysticetiProperties` is where M6, `Decided.directCommit` and
`isLeaderBlock_of_decided` are read; this file does not reach past it.
-/

namespace LeanDag

namespace Barnacle

namespace Mysticeti

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _
  exact
    {
      full_ids := fun _ => rfl
      historyView_ids := fun _ _ _ => rfl
      agree := fun S {_} V₁ V₂ k v₁ v₂ h₁ h₂ =>
        MysticetiProperties.agree S V₁ V₂ k v₁ v₂ h₁ h₂
      decided_of_directCommitIn := fun S {_} V k L hL hdc =>
        MysticetiProperties.commitsDirect S _ V k L hL hdc
      candidates := fun S {_} V k L h =>
        MysticetiProperties.commitsCandidate S _ V k L h }

end Mysticeti

end Barnacle

end LeanDag
