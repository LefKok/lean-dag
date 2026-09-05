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

/-- **Reactive Mysticeti commits its reliable leaders** — `ReactiveM.decided`
as the property, on any view caught up to the horizon. -/
theorem leaderCommits_reactive :
    LeaderCommits (mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (fun S {U} V T lo K => reactiveLive S (U := U) V T lo K) := by
  intro S U V T lo K hlive k hlo hK hlead
  obtain ⟨hT, hcard, N, R₀, rm, hgst, hto, hR, hcov, hN⟩ := hlive
  have hRk : R₀ ≤ S.slotRound k := le_trans hR (S.mono hlo)
  have hNk := hN k hK
  obtain ⟨L, hLmem, hLc, hLr⟩ :=
    rm.toPaceCore.populatedOn hcard (S.slotRound k) (by omega) (S.leader k) hlead
  have hL : IsLeaderBlock (S := S) U k L := ⟨hLmem, hLr, hLc⟩
  have hin : DirectCommitIn U V L (S.slotRound k) :=
    directCommitIn_of_coversUpto (rm.directCommit hT hcard hgst hto hRk hNk hlead hL)
      (hcov.mono hNk)
  refine ⟨L, by omega, Decided.directCommit hL hin, ?_⟩
  intro S' hround hlead'
  refine Decided.directCommit (S := S') ⟨hLmem, by rw [hround]; exact hLr,
    by rw [hlead' k (by omega)]; exact hLc⟩ ?_
  rw [hround]; exact hin

/-! ## What a mechanism needs from a reactive execution

`LiveReachable` asks a rule's precondition to follow from coverage, and
a reactive execution does not have coverage — `SynchronisedOn` is false
in one by design. That antecedent is the strongest fact statable in
`ids`, `block` and `refs` alone, which is why the properties use it; it
is not what a *mechanism* needs.

What a mechanism needs is weaker and is already named: `CertifiesAt`,
the certificates the commit rule counts. The reactive discipline
delivers it — that is what `cert_or_wait` is for — and
`MysticetiProperties.directCommit_of_sustains` consumes it, carrying the
commit to the transformed DAG with no pacing structure transported.
Certificates are made of references, and `Sustains` preserves
references.
-/

/-- **The reactive commit survives any sustaining mechanism.** The
reactive execution supplies the certificates and the production; the
mechanism supplies `Sustains`; neither knows about the other. -/
theorem directCommit_of_reactive_sustains [S : Slots Validator]
    {U U' : BlockUniverse Validator BlockId Payload} {T : Finset Validator} {N : ℕ}
    {G R₀ : ℕ} (hsus : Sustains (mysticetiRule (Payload := Payload)) U U' G R₀)
    (rm : ReactiveM (S := S) U T N) {R k : ℕ} {L : BlockId}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hR₀ : R₀ ≤ S.slotRound k) (hG : G ≤ S.slotRound k)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    DirectCommit U' L (S.slotRound k - G) :=
  MysticetiProperties.directCommit_of_sustains hsus hR₀ hG hcard
    (rm.toPaceCore.populatedOn hcard (S.slotRound k + 2) hN)
    (rm.certifies hT hcard hgst hto hR hN hlead hL)

end MysticetiProperties

end LeanDag
