import LeanDag.Barnacle.Orcaella.Statement
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.HybridProperties

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

/-- **A good DAG meets Hybrid's precondition.** `Good` and `hybridLive`
name the same three facts about the same quorum, at Hybrid's own
wavelength — the horizon sits one round above the slot. -/
theorem orcaellaLive_goodGives [H : HybridFaults Validator] {k : ℕ} :
    (orcaellaLive (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) k).GoodGives (H.fb + H.fc)
      (fun S {U} V T lo K => HybridProperties.hybridLive S (U := U) V T lo K) := by
  intro U Rnd N hgood
  obtain ⟨T, -, hcard, hsync, hpop⟩ := hgood
  have hcard' : Fintype.card Validator - (H.fb + H.fc) ≤ T.card := hcard
  refine ⟨T, by omega, ?_⟩
  intro S V κ hcov hRnd hN hlead
  change S.slotRound κ + 2 ≤ N at hN
  refine ⟨hcard, Rnd, N, hsync, hRnd, hpop, hcov, ?_⟩
  intro m hm
  have := S.mono (Nat.lt_succ_iff.mp hm)
  omega

/-- **The descent laws, for Orcaella at slack `fb + fc`** — from the
properties, with no argument about `Decided` here. -/
theorem orcaellaLive_descent [H : HybridFaults Validator] {k : ℕ} :
    (orcaellaLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload) k).Descent
      (H.fb + H.fc) :=
  descent_of_properties _ (HybridProperties.leaderCommits k) (HybridProperties.indirect k)
    orcaellaLive_goodGives

end Barnacle

end LeanDag
