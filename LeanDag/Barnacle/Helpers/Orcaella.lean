import LeanDag.Barnacle.Orcaella.Statement
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.Hybrid.Properties
/-!
# Orcaella instance helpers

Not part of the audit surface. The laws are the hybrid agreement
theorem — consuming the bundled `HonestNoEquiv` and the admissibility
of the threshold — with the direct constructor and
`isLeaderBlock_of_decided`; the descent laws are H7a
(`directCommit_of_leader_mem`, at the fully-correct quorum) and the two
indirect constructors, the commit one at the least candidate with a
`k`-thick link. Descent consumes no admissibility: the constructors are
unconditional, and the reliable set alone carries the direct commit.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- The laws, for Orcaella at an admissible threshold. -/
theorem orcaella_laws [HybridFaults Validator] {k : ℕ} (hk : Hybrid.Admissible Validator k) :
    BaseRule.Laws
      (orcaella (Validator := Validator) (BlockId := BlockId) (Payload := Payload) k) where
  full_ids := fun _ => rfl
  historyView_ids := fun _ _ _ => rfl
  agree := fun S {U} V₁ V₂ s v₁ v₂ h₁ h₂ =>
    HybridProperties.agree hk S V₁ V₂ s v₁ v₂ h₁ h₂
  decided_of_directCommitIn := fun S {U} V s L hL hdc =>
    HybridProperties.commitsDirect k S U V s L hL hdc
  candidates := fun S {U} V s L h => HybridProperties.commitsCandidate k S U V s L h


/-- **A good DAG is good in the properties' terms.** -/
theorem orcaellaLive_goodOf [H : HybridFaults Validator] {k : ℕ} :
    ∀ U Rnd N, (orcaellaLive (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) k).Good U Rnd N →
      GoodOf (orcaellaLive (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload) k).toBaseRule.toDagRule (coreReliability Validator) U Rnd N := by
  rintro U Rnd N ⟨T, hT, hcard, hs, hpop⟩
  refine ⟨T, ⟨hT, ?_⟩, hs, hpop⟩
  change Fintype.card Validator - Faults.f Validator ≤ T.card
  rw [hybrid_f]; exact hcard

/-- **The descent laws, for Orcaella at slack `fb + fc`** — from its
support. -/
theorem orcaellaLive_descent [H : HybridFaults Validator] {k : ℕ} :
    (orcaellaLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload) k).Descent
      (H.fb + H.fc) :=
  descent_of_support (orcaellaLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload) k)
    (Properties.voteSupport _) (Timed.voteSupport_ofCoverage _)
    (HybridProperties.voteSupport_commits k) (HybridProperties.indirect k) (by change 1 ≤ 2; omega)
    orcaellaLive_goodOf

end Barnacle

end LeanDag
