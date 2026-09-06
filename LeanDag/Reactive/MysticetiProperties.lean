import LeanDag.Reactive.Mysticeti
import LeanDag.MysticetiProperties

/-!
# Reactive Mysticeti conforms to the schedule family

`docs/target-properties.md` §4. The reactive discipline changes no
rule: `Decided` and the bounded relation are the core's, so `Agree`,
the safety side is inherited without a word. What changes is
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

/-- **The reactive discipline is the other bridge.** `cert_or_wait`
certifies every candidate of a reliably-led slot past GST, and the
trunk's derived production supplies the blocks — which is `certLive`,
the same precondition coverage reaches by a different road. The two
execution models now meet at one predicate.

The clause coverage has and this does not is the point of the
discipline: a reactive builder omits whatever had not arrived, so
`SynchronisedOn` is false here, and only what the commit rule counts
survives. -/
theorem certLive_of_reactiveLive {S : Slots Validator}
    {U : BlockUniverse Validator BlockId Payload} {V : View Validator BlockId Payload U}
    {T : Finset Validator} {lo K : ℕ} (h : reactiveLive S (U := U) V T lo K) :
    certLive S (U := U) V T lo K := by
  obtain ⟨hT, hcard, N, R₀, rm, hgst, hto, hR, hcov, hN⟩ := h
  refine ⟨hcard, N, hcov, hN, ?_⟩
  intro k hlo hK hlead
  have hRk : R₀ ≤ S.slotRound k := le_trans hR (S.mono hlo)
  have hNk : S.slotRound k + 2 ≤ N := hN k hK
  exact ⟨rm.toPaceCore.populatedOn hcard _ (by omega),
    rm.toPaceCore.populatedOn hcard _ (by omega),
    fun L hL => rm.certifies hT hcard hgst hto hRk hNk hlead hL⟩

/-- **The reactive discipline reaches the core's support precondition**
(`Properties/Support.lean`): a reactive execution past GST is a quorum
certifying every candidate of every reliably-led slot in the window,
which is `Support.live` and the socket every mechanism reads. -/
theorem coreSupport_live_of_reactiveLive {S : Slots Validator}
    {U : BlockUniverse Validator BlockId Payload} {V : View Validator BlockId Payload U}
    {T : Finset Validator} {lo K : ℕ} (h : reactiveLive S (U := U) V T lo K) :
    (coreSupport (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).live
      (coreReliability Validator) S (U := U) V T lo K := by
  obtain ⟨hT, hcard, N, R₀, rm, hgst, hto, hR, hcov, hN⟩ := h
  refine ⟨⟨hT, hcard⟩, N, hcov, hN, ?_⟩
  intro k hlo hK hlead
  have hRk : R₀ ≤ S.slotRound k := le_trans hR (S.mono hlo)
  have hNk : S.slotRound k + 2 ≤ N := hN k hK
  refine ⟨fun n _ h2 => rm.toPaceCore.populatedOn hcard n
    (by change n ≤ S.slotRound k + 2 at h2; omega), ?_⟩
  rintro L ⟨hLmem, hLr, hLc⟩
  exact rm.certifies hT hcard hgst hto hRk hNk hlead ⟨hLmem, hLr, hLc⟩

/-- **Reactive Mysticeti commits its reliable leaders.** The statement is
unchanged; the proof is now the bridge composed with the core's single
`LeaderCommits`, where it was a second proof of the same shape. -/
theorem leaderCommits_reactive :
    LeaderCommits (mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (fun S {U} V T lo K => reactiveLive S (U := U) V T lo K) :=
  fun S _ V T lo K hlive => leaderCommits_cert S V T lo K (certLive_of_reactiveLive hlive)

end MysticetiProperties

end LeanDag
