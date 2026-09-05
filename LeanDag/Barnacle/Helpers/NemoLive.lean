import LeanDag.Barnacle.Nemo.Statement
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Barnacle.Helpers.Descent
import LeanDag.NemoProperties

/-!
# Nemo instance helpers — the laws

Not part of the audit surface. Every law here is a **property**: `Agree`,
`CommitsDirect` and `CommitsCandidate` for the base laws, and
`LeaderCommits` with `Indirect` for the descent, assembled by
`descent_of_properties`. `Nemo/Carrier.lean` and `NemoProperties.lean`
are where `Nemo.decided_agree`, the direct constructor,
`isLeaderBlock_of_decided` and `decided_of_leader_mem` are read; this
file does not reach past them (`docs/porting-plan.md` step 1).

What is left of the descent is the bridge from Nemo's notion of a good
DAG to its own liveness precondition, which mentions no verdict. Nemo's
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

/-- **A good DAG meets Nemo's precondition.** `Good` and `nemoLive` name
the same three facts about the same set; the window is the single slot,
and its rounds fit because the wave does. -/
theorem nemoLive_goodGives [Nemo.CrashFaults Validator] :
    (nemoLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).GoodGives
      (Fintype.card Validator - Nemo.majority Validator)
      (fun S {U} V T lo K => NemoProperties.nemoLive S (U := U) V T lo K) := by
  intro U Rnd N hgood
  obtain ⟨T, -, hcard, hsync, hpop⟩ := hgood
  refine ⟨T, ?_, ?_⟩
  · have := Nat.sub_le (Fintype.card Validator) (Nemo.majority Validator)
    omega
  intro S V κ hcov hRnd hN hlead
  change S.slotRound κ + 2 ≤ N at hN
  refine ⟨hcard, Rnd, N, hsync, hRnd, hpop, hcov, ?_⟩
  intro k hk
  have := S.mono (Nat.lt_succ_iff.mp hk)
  omega

/-- **The descent laws, for Nemo at the slack a majority may miss** —
from the properties, with no argument about `Decided` here. -/
theorem nemoLive_descent [Nemo.CrashFaults Validator] :
    (nemoLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent
      (Fintype.card Validator - Nemo.majority Validator) :=
  descent_of_properties _ NemoProperties.leaderCommits NemoProperties.indirect
    nemoLive_goodGives

/-- The pigeonhole's committee bound holds for the majority slack at
every `n`: `2 · (n − majority) + 1 ≤ n`. -/
theorem majority_bound (n : ℕ) (hn : 0 < n) :
    2 * (n - Nemo.majority (Fin n)) + 1 ≤ n := by
  unfold Nemo.majority
  rw [Fintype.card_fin]
  omega

end Barnacle

end LeanDag
