import LeanDag.Reactive.Mysticeti
import LeanDag.MysticetiProperties

/-!
# Reactive Mysticeti conforms to the schedule family

`docs/target-properties.md` §4. The reactive discipline changes no
rule: `Decided` and the bounded relation are the core's, so `Agree`,
`Bounded` and `SchedLocal` are inherited without a word. What changes is
the liveness precondition, and `LeaderCommits` was stated with the
precondition as a parameter for exactly this case: the same rule, a
second `Live`.

`reactiveLive` is the reactive execution's clauses over a slot window
— a `ReactiveM` under the schedule, past GST with the timeout clearing
`2Δ + proc`, on a view caught up to the horizon. Unlike `coreLive` it
**reads the schedule's leaders**, through `cert_or_wait` and
`vote_or_wait`, which is why `Live` carries the schedule and why the
adaptive existence theorem consumes it stage by stage: the clauses hold
only under the schedule the validators actually followed, and an
adaptive schedule is only determined so far.
-/

namespace LeanDag

namespace MysticetiProperties

open Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **The reactive liveness precondition**, over a slot window: a
correct quorum `T`, a reactive execution under the schedule with its GST
at or below the window's first slot and its timeout clearing
`2Δ + proc` from there, the view caught up to the horizon, and every slot
of the window two rounds under it. -/
def reactiveLive (S : Slots Validator) {U : BlockUniverse Validator BlockId Payload}
    (V : View Validator BlockId Payload U) (T : Finset Validator) (lo K : ℕ) : Prop :=
  T ⊆ (Correct : Finset Validator) ∧ quorumCard Validator ≤ T.card ∧
    ∃ (N R₀ : ℕ) (rm : ReactiveM (S := S) U T N),
      rm.gst ≤ R₀ ∧ (∀ n, R₀ ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n) ∧
      R₀ ≤ S.slotRound lo ∧ V.CoversUpto N ∧ ∀ k, k < K → S.slotRound k + 2 ≤ N

/-- **Reactive Mysticeti commits its reliable leaders** — `ReactiveM.decided`
as the property, on any view caught up to the horizon. -/
theorem leaderCommits_reactive :
    LeaderCommits (mysticetiBounded (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (fun S {U} V T lo K => reactiveLive S (U := U) V T lo K) := by
  intro S U V T lo K hlive k hlo hK hlead
  obtain ⟨hT, hcard, N, R₀, rm, hgst, hto, hR, hcov, hN⟩ := hlive
  have hRk : R₀ ≤ S.slotRound k := le_trans hR (S.mono hlo)
  have hNk := hN k hK
  obtain ⟨L, hLmem, hLc, hLr⟩ :=
    rm.toPaceCore.populatedOn hcard (S.slotRound k) (by omega) (S.leader k) hlead
  have hL : IsLeaderBlock (S := S) U k L := ⟨hLmem, hLr, hLc⟩
  exact ⟨L, DecidedWithin.directCommit (S := S) (U := U) (by omega) hL
    (directCommitIn_of_coversUpto (rm.directCommit hT hcard hgst hto hRk hNk hlead hL)
      (hcov.mono hNk))⟩

end MysticetiProperties

end LeanDag
