import LeanDag.Properties.Arcs.Quality
import LeanDag.FinWhale.Carrier
import LeanDag.Hydrozoan.Helpers.Commit

/-!
# Chain quality for a second and third rule

`docs/target-properties.md` §11.4's last item, checked. The arc is
stated once over `Properties.DagRule`
(`LeanDag/Properties/Arcs/Quality.lean`); the core instantiates it in
`LeanDag/Quality/`. What this file checks is that a rule which never had
the arc gets it by application — no induction, no density proof of its
own, and nothing about its decision relation beyond
`CommitsCandidate`.

**FinWhale** takes the whole of it, including the "at least half"
packaging: its committee is `n = 3f + 2p − 1` with `p ≥ 1`, so
`|Correct| ≥ 2f + 1` and `2f ≤ |Correct|` as CQ2 asks.

**Hydrozoan** takes the coverage bound and the backbone. It does *not*
take CQ2 in general, and the reason is a real feature of its committee
rather than a gap in the arc: the slack is `f + c` and the bound is
`n ≥ 3f + 2c + k + 1`, which gives `2(f + c) ≤ |Correct|` only when
`c ≤ k + 1`. `card_coveredAt_ge` is the statement that holds at every
configuration, and CQ2 takes the extra condition as a hypothesis for
exactly this reason.
-/

namespace LeanDagTest

open LeanDag LeanDag.Properties LeanDag.Properties.Arcs

section FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : LeanDag.FinWhale.Params Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **CQ1 for FinWhale.** A committed leader's flush covers all but `f`
of the correct validators at every round below it. -/
theorem finWhale_card_coveredAt_ge_of_decided (S : Slots Validator)
    {D : LeanDag.FinWhale.Dag Validator BlockId Payload}
    {V : (LeanDag.FinWhaleProperties.finWhaleRule (Payload := Payload)).View D}
    {k : ℕ} {L : BlockId} {δ : ℕ}
    (h : (LeanDag.FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V k (some L))
    (hδ : δ < (D.block L).round) :
    (Correct : Finset Validator).card - F.f ≤
      (coveredAt (LeanDag.FinWhaleProperties.finWhaleRule (Payload := Payload))
        (coreReliability Validator) D L δ).card :=
  card_coveredAt_ge_of_decided LeanDag.FinWhaleProperties.causal
    LeanDag.FinWhaleProperties.quorate LeanDag.FinWhaleProperties.commitsCandidate h hδ

/-- **CQ2 for FinWhale.** At least half the correct validators, every
round below every commit. -/
theorem finWhale_card_correct_le_two_mul (S : Slots Validator)
    {D : LeanDag.FinWhale.Dag Validator BlockId Payload}
    {V : (LeanDag.FinWhaleProperties.finWhaleRule (Payload := Payload)).View D}
    {k : ℕ} {L : BlockId} {δ : ℕ}
    (h : (LeanDag.FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V k (some L))
    (hδ : δ < (D.block L).round) :
    (Correct : Finset Validator).card ≤
      2 * (coveredAt (LeanDag.FinWhaleProperties.finWhaleRule (Payload := Payload))
        (coreReliability Validator) D L δ).card :=
  card_correct_le_two_mul_coveredAt_of_decided LeanDag.FinWhaleProperties.causal
    LeanDag.FinWhaleProperties.quorate LeanDag.FinWhaleProperties.commitsCandidate
    (by
      simp only [coreReliability_correct, coreReliability_slack]
      have := two_f_add_one_le_card_correct (Validator := Validator)
      omega) h hδ

end FinWhale

section Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable [F : LeanDag.Hydrozoan.Faults Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]

/-- **CQ1 for Hydrozoan**, at its own fault model: all but `f + c` of
the reliable replicas, at every round below a commit. -/
theorem hydrozoan_card_coveredAt_ge_of_decided (S : Slots Replica)
    {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    {V : LeanDag.Hydrozoan.View U} {k : ℕ} {L : BlockId} {δ : ℕ}
    (h : (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).Decided S V k (some L))
    (hδ : δ < (U.block L).round) :
    (LeanDag.Hydrozoan.Correct : Finset Replica).card - (F.f + F.c) ≤
      (coveredAt (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
        (LeanDag.Hydrozoan.hzReliability Replica) U L δ).card :=
  card_coveredAt_ge_of_decided LeanDag.Hydrozoan.causal LeanDag.Hydrozoan.quorate
    LeanDag.Hydrozoan.commitsCandidate h hδ

end Hydrozoan

#print axioms LeanDagTest.finWhale_card_coveredAt_ge_of_decided
#print axioms LeanDagTest.finWhale_card_correct_le_two_mul
#print axioms LeanDagTest.hydrozoan_card_coveredAt_ge_of_decided

end LeanDagTest
