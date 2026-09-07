import LeanDag.Barnacle.Nemo.Statement
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.Nemo.Properties
/-!
# Nemo instance helpers — the laws

Not part of the audit surface. Every law here is a **property**: `Agree`,
`CommitsDirect` and `CommitsCandidate` for the base laws, and
`voteSupport`'s `Commits` with `Indirect` for the descent, assembled by
`descent_of_support`. `Nemo/Carrier.lean` and `NemoProperties.lean`
are where `Nemo.decided_agree`, the direct constructor,
`isLeaderBlock_of_decided` and `decided_of_leader_mem` are read; this
file does not reach past them (`docs/porting-plan.md` step 1).

What is left of the descent is the one-line fact that Nemo's good DAG
is `GoodOf` at its fault model, where the reliable set is everyone. Nemo's
slack is `n − majority`, not `f`: the strength is in the weaker `Good`,
and that is unchanged.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- The laws, for Nemo-Nemo. -/
theorem nemo_laws :
    BaseRule.Laws (nemo (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) where
  full_ids := fun _ => rfl
  historyView_ids := fun _ _ _ => rfl
  agree := fun S {_} V₁ V₂ k v₁ v₂ h₁ h₂ => NemoProperties.agree S V₁ V₂ k v₁ v₂ h₁ h₂
  decided_of_directCommitIn := fun S {_} V k L hL hdc =>
    NemoProperties.commitsDirect S _ V k L hL hdc
  candidates := fun S {_} V k L h => NemoProperties.commitsCandidate S _ V k L h


/-- Nemo's committee is non-empty: at least `2f + 1` validators. -/
theorem nemo_card_pos [C : Nemo.CrashFaults Validator] : 0 < Fintype.card Validator := by
  have := C.card_validators; omega

/-- **A good DAG is good in the properties' terms**: the reliable set is
everyone, so any majority is a quorum of it. -/
theorem nemoLive_goodOf [Nemo.CrashFaults Validator] :
    ∀ U Rnd N, (nemoLive (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)).Good U Rnd N →
      GoodOf (nemoLive (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload)).toBaseRule.toDagRule (NemoProperties.nemoReliability Validator nemo_card_pos)
        U Rnd N := by
  rintro U Rnd N ⟨T, -, hcard, hs, hpop⟩
  refine ⟨T, ⟨Finset.subset_univ _, ?_⟩, hs, hpop⟩
  change Fintype.card Validator - (Fintype.card Validator - Nemo.majority Validator) ≤ T.card
  have hpos := nemo_card_pos (Validator := Validator)
  have : Nemo.majority Validator ≤ Fintype.card Validator := by
    unfold Nemo.majority; omega
  omega

/-- **The descent laws, for Nemo at the slack a majority may miss** —
from its support. -/
theorem nemoLive_descent [Nemo.CrashFaults Validator] :
    (nemoLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent
      (Fintype.card Validator - Nemo.majority Validator) :=
  descent_of_support (nemoLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
    (Properties.voteSupport _) (Timed.voteSupport_ofCoverage _)
    (NemoProperties.voteSupport_commits nemo_card_pos) NemoProperties.indirect (by change 1 ≤ 2; omega)
    nemoLive_goodOf

/-- The pigeonhole's committee bound holds for the majority slack at
every `n`: `2 · (n − majority) + 1 ≤ n`. -/
theorem majority_bound (n : ℕ) (hn : 0 < n) :
    2 * (n - Nemo.majority (Fin n)) + 1 ≤ n := by
  unfold Nemo.majority
  rw [Fintype.card_fin]
  omega

end Barnacle

end LeanDag
