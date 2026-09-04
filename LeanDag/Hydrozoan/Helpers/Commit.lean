import LeanDag.Hydrozoan.Helpers.Banded
import LeanDag.Hydrozoan.Helpers.IndirectLiveness
import LeanDag.Hydrozoan.IndirectLiveness.Statement
import LeanDag.Hydrozoan.DirectLiveness.Proof
import LeanDag.Hydrozoan.SlotAgreement.Proof
import LeanDag.Properties.Commit
import LeanDag.Properties.Candidate

/-!
# Hydrozoan's liveness obligations

`docs/target-properties.md` §4. `Agree`, `LeaderCommits` and `Descends`
for this protocol, each resting on an arc result that was already
proved: slot agreement, direct liveness, and the graded rule's totality
with the committed-run descent.

What has to be added is the **bound**. `DecidedBelow` records that a
verdict survives any reassignment of the leaders at or above a slot
bound, and an opaque `Decided` cannot supply that, so each verdict is
rebuilt here from the constructor the arc result hands over: the slow
commit for a reliable leader, and the graded trichotomy for a slot under
an anchor. Both read the schedule only at the slot they decide, which is
what makes the bound tight.
-/

namespace LeanDag

namespace Hydrozoan

open LeanDag.Properties

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]

/-- **Slot agreement as a property.** -/
theorem agree : Agree (rule (Replica := Replica) (BlockId := BlockId)) := by
  intro S U V₁ V₂ k v₁ v₂ h₁ h₂
  letI : LeanDag.Hydrozoan.Slots Replica := ofCoreSlots S
  exact SlotAgreement.holds Replica BlockId U V₁ V₂ k v₁ v₂ h₁ h₂

/-- **Hydrozoan's liveness precondition**, over a slot window: a correct
DAG quorum synchronised from a round at or below the window's first
slot, filling every round to a horizon the view is caught up to, with
every slot of the window two rounds under it. It names no leader, so it
holds under every schedule with the same rounds. -/
def hzLive (S : LeanDag.Slots Replica) {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    (V : LeanDag.Hydrozoan.View U) (T : Finset Replica) (lo K : ℕ) : Prop :=
  T ⊆ (Correct : Finset Replica) ∧ LeanDag.Hydrozoan.q Replica ≤ T.card ∧
    ∃ R₀ N, LeanDag.Hydrozoan.SynchronisedOn U T R₀ ∧ R₀ ≤ S.slotRound lo ∧
      (∀ r, R₀ ≤ r → r ≤ N → LeanDag.Hydrozoan.PopulatedOn U T r) ∧
      LeanDag.Hydrozoan.View.CoversUpto V N ∧
      ∀ k, k < K → S.slotRound k + 2 ≤ N

/-- **Direct liveness as a property**: a slot led by a member of the
reliable quorum commits, and the commit reads that one leader, so its
bound is one above the slot. -/
theorem leaderCommits :
    LeaderCommits (rule (Replica := Replica) (BlockId := BlockId))
      (fun S {U} V T lo K => hzLive S (U := U) V T lo K) := by
  intro S U V T lo K hlive k hlo hK hlead
  obtain ⟨hT, hcard, R₀, N, hs, hR, hpop, hcov, hN⟩ := hlive
  letI : LeanDag.Hydrozoan.Slots Replica := ofCoreSlots S
  have hRk : R₀ ≤ S.slotRound k := le_trans hR ((ofCoreSlots S).mono hlo)
  have hNk : S.slotRound k + 2 ≤ N := hN k hK
  have hp0 : LeanDag.Hydrozoan.PopulatedOn U T (S.slotRound k) :=
    hpop _ hRk (by omega)
  have hp1 : LeanDag.Hydrozoan.PopulatedOn U T (S.slotRound k + 1) :=
    hpop _ (by omega) (by omega)
  have hp2 : LeanDag.Hydrozoan.PopulatedOn U T (S.slotRound k + 2) :=
    hpop _ (by omega) (by omega)
  obtain ⟨L, hL, hslow, -⟩ :=
    DirectLiveness.holds Replica BlockId U T R₀ k hT hcard hs hRk hp0 hp1 hp2 hlead V
      (hcov.mono hNk)
  have hin : LeanDag.Hydrozoan.SlowCommitInView U V L (S.slotRound k) :=
    slowCommitInView_of_coversUpto hslow (hcov.mono hNk)
  refine ⟨L, by omega, LeanDag.Hydrozoan.Decided.directSlow hL hin, ?_⟩
  intro S' hround hlead'
  refine LeanDag.Hydrozoan.Decided.directSlow (S := ofCoreSlots S') ⟨hL.1, ?_, ?_⟩ ?_
  · change (U.block L).round = S'.slotRound k
    rw [hround]; exact hL.2.1
  · change (U.block L).author = S'.leader k
    rw [hlead' k (by omega)]; exact hL.2.2
  · change LeanDag.Hydrozoan.SlowCommitInView U V L (S'.slotRound k)
    rw [hround]; exact hin


/-! ## The descent, at a bound -/

theorem eligibleAsAnchor_sched {S S' : LeanDag.Slots Replica}
    (hround : S'.slotRound = S.slotRound) {x y : ℕ} :
    LeanDag.Hydrozoan.EligibleAsAnchor (S := ofCoreSlots S') Replica x y ↔
      LeanDag.Hydrozoan.EligibleAsAnchor (S := ofCoreSlots S) Replica x y := by
  unfold LeanDag.Hydrozoan.EligibleAsAnchor LeanDag.Hydrozoan.decisionRound
  change S'.slotRound x + 2 < S'.slotRound y ↔ S.slotRound x + 2 < S.slotRound y
  rw [hround]

/-- **The graded rule is total, at a bound.** `decided_of_anchor` with
the schedule dependence tracked: every rung reads the leaders at the
slot it decides and at no other, so a verdict anchored below `B`
survives reassignment at or above `B`. -/
theorem decidedBelow_of_anchor {S : LeanDag.Slots Replica}
    {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {V : LeanDag.Hydrozoan.View U}
    {k j B : ℕ} {A : BlockId} (hkB : k < B)
    (helig : LeanDag.Hydrozoan.EligibleAsAnchor (S := ofCoreSlots S) Replica k j)
    (hj : DecidedBelow rule S B V j (some A))
    (hmid : ∀ i, k < i → i < j →
      LeanDag.Hydrozoan.EligibleAsAnchor (S := ofCoreSlots S) Replica k i →
      DecidedBelow rule S B V i none) :
    ∃ v, DecidedBelow rule S B V k v := by
  classical
  have hkj : k < j := lt_of_eligibleAsAnchor (S := ofCoreSlots S) helig
  have hmidD : ∀ i, k < i → i < j →
      LeanDag.Hydrozoan.EligibleAsAnchor (S := ofCoreSlots S) Replica k i →
      LeanDag.Hydrozoan.Decided (S := ofCoreSlots S) U V i none :=
    fun i h1 h2 h3 => (hmid i h1 h2 h3).2.1
  by_cases hc : ∃ L, LeanDag.Hydrozoan.IsLeaderBlock (S := ofCoreSlots S) U k L ∧
      LeanDag.Hydrozoan.CertifiedIn U A L ((ofCoreSlots S).slotRound k)
  · obtain ⟨L, hL, hcert⟩ := hc
    refine ⟨some L, hkB, LeanDag.Hydrozoan.Decided.indirectCert (S := ofCoreSlots S) hkj helig hj.2.1
      hmidD hL hcert, ?_⟩
    intro S' hround hlead
    exact LeanDag.Hydrozoan.Decided.indirectCert (S := ofCoreSlots S') hkj
      ((eligibleAsAnchor_sched hround).mpr helig) (hj.2.2 S' hround hlead)
      (fun i h1 h2 h3 => (hmid i h1 h2 ((eligibleAsAnchor_sched hround).mp h3)).2.2
        S' hround hlead)
      (isLeaderBlock_sched (S₁ := ofCoreSlots S) (S₂ := ofCoreSlots S')
        (by change S.slotRound k = S'.slotRound k; rw [hround])
        (by change S.leader k = S'.leader k; rw [hlead k hkB]) hL)
      (by change LeanDag.Hydrozoan.CertifiedIn U A L (S'.slotRound k); rw [hround]; exact hcert)
  · push Not at hc
    by_cases hw : ∃ L, LeanDag.Hydrozoan.IsLeaderBlock (S := ofCoreSlots S) U k L ∧
        LeanDag.Hydrozoan.WeakLinked U A L ((ofCoreSlots S).slotRound k)
    · obtain ⟨L₀, hL₀, hw₀, hleast⟩ := exists_least_weak_candidate (S := ofCoreSlots S) hw
      refine ⟨some L₀, hkB, LeanDag.Hydrozoan.Decided.indirectWeak (S := ofCoreSlots S) hkj helig hj.2.1
        hmidD hc hL₀ hw₀ hleast, ?_⟩
      intro S' hround hlead
      have hls : ∀ L', LeanDag.Hydrozoan.IsLeaderBlock (S := ofCoreSlots S') U k L' →
          LeanDag.Hydrozoan.IsLeaderBlock (S := ofCoreSlots S) U k L' := fun L' hL' =>
        isLeaderBlock_sched (S₁ := ofCoreSlots S') (S₂ := ofCoreSlots S)
          (by change S'.slotRound k = S.slotRound k; rw [hround])
          (by change S'.leader k = S.leader k; rw [hlead k hkB]) hL'
      refine LeanDag.Hydrozoan.Decided.indirectWeak (S := ofCoreSlots S') hkj
        ((eligibleAsAnchor_sched hround).mpr helig) (hj.2.2 S' hround hlead)
        (fun i h1 h2 h3 => (hmid i h1 h2 ((eligibleAsAnchor_sched hround).mp h3)).2.2
          S' hround hlead) ?_
        (isLeaderBlock_sched (S₁ := ofCoreSlots S) (S₂ := ofCoreSlots S')
          (by change S.slotRound k = S'.slotRound k; rw [hround])
          (by change S.leader k = S'.leader k; rw [hlead k hkB]) hL₀) ?_ ?_
      · intro L' hL' hc'
        refine hc L' (hls L' hL') ?_
        change LeanDag.Hydrozoan.CertifiedIn U A L' (S'.slotRound k) at hc'
        rw [hround] at hc'; exact hc'
      · change LeanDag.Hydrozoan.WeakLinked U A L₀ (S'.slotRound k)
        rw [hround]; exact hw₀
      · intro L' hL' hw'
        refine hleast L' (hls L' hL') ?_
        change LeanDag.Hydrozoan.WeakLinked U A L' (S'.slotRound k) at hw'
        rw [hround] at hw'; exact hw'
    · push Not at hw
      refine ⟨none, hkB, LeanDag.Hydrozoan.Decided.indirectSkip (S := ofCoreSlots S) hkj helig hj.2.1
        hmidD hc hw, ?_⟩
      intro S' hround hlead
      have hls : ∀ L', LeanDag.Hydrozoan.IsLeaderBlock (S := ofCoreSlots S') U k L' →
          LeanDag.Hydrozoan.IsLeaderBlock (S := ofCoreSlots S) U k L' := fun L' hL' =>
        isLeaderBlock_sched (S₁ := ofCoreSlots S') (S₂ := ofCoreSlots S)
          (by change S'.slotRound k = S.slotRound k; rw [hround])
          (by change S'.leader k = S.leader k; rw [hlead k hkB]) hL'
      refine LeanDag.Hydrozoan.Decided.indirectSkip (S := ofCoreSlots S') hkj
        ((eligibleAsAnchor_sched hround).mpr helig) (hj.2.2 S' hround hlead)
        (fun i h1 h2 h3 => (hmid i h1 h2 ((eligibleAsAnchor_sched hround).mp h3)).2.2
          S' hround hlead) ?_ ?_
      · intro L' hL' hc'
        refine hc L' (hls L' hL') ?_
        change LeanDag.Hydrozoan.CertifiedIn U A L' (S'.slotRound k) at hc'
        rw [hround] at hc'; exact hc'
      · intro L' hL' hw'
        refine hw L' (hls L' hL') ?_
        change LeanDag.Hydrozoan.WeakLinked U A L' (S'.slotRound k) at hw'
        rw [hround] at hw'; exact hw'

open Classical in
/-- **A committed run decides everything below it, at a bound.** The
existing descent with `DecidedBelow` in place of `Decided`: the nearest
eligible committed anchor is found the same way, and totality closes
each slot with `decidedBelow_of_anchor`. -/
theorem decidedBelow_of_committed_run {S : LeanDag.Slots Replica}
    {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {V : LeanDag.Hydrozoan.View U}
    {b n B : ℕ} (hbn : b ≤ n) (hnB : n < B)
    (hspan : ∀ i, i < b → LeanDag.Hydrozoan.EligibleAsAnchor (S := ofCoreSlots S) Replica i n)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ A, DecidedBelow rule S B V j (some A)) :
    ∀ i, i < b → ∃ v, DecidedBelow rule S B V i v := by
  have key : ∀ d i, i < b → b - i ≤ d → ∃ v, DecidedBelow rule S B V i v := by
    intro d
    induction d with
    | zero => intro i hi hd; omega
    | succ d ih =>
      intro i hi hd
      have hex : ∃ j, LeanDag.Hydrozoan.EligibleAsAnchor (S := ofCoreSlots S) Replica i j ∧
          ∃ A, DecidedBelow rule S B V j (some A) :=
        ⟨n, hspan i hi, hrun n hbn (le_refl n)⟩
      have hle : Nat.find hex ≤ n :=
        Nat.find_le ⟨hspan i hi, hrun n hbn (le_refl n)⟩
      obtain ⟨helig, A, hA⟩ := Nat.find_spec hex
      have hmid : ∀ i', i < i' → i' < Nat.find hex →
          LeanDag.Hydrozoan.EligibleAsAnchor (S := ofCoreSlots S) Replica i i' →
          DecidedBelow rule S B V i' none := by
        intro i' h1 h2 h3
        have hnc : ¬ ∃ C, DecidedBelow rule S B V i' (some C) :=
          fun hcom => Nat.find_min hex h2 ⟨h3, hcom⟩
        have hi'b : i' < b := by
          by_contra he
          exact hnc (hrun i' (by omega) (by omega))
        obtain ⟨v, hv⟩ := ih i' hi'b (by omega)
        cases v with
        | none => exact hv
        | some C => exact absurd ⟨C, hv⟩ hnc
      exact decidedBelow_of_anchor (by omega) helig hA hmid
  intro i hi
  exact key (b - i) i hi (le_refl _)

/-- **The descent as a property.** -/
theorem descends {S : LeanDag.Slots Replica} {c : ℕ} (hc : 0 < c)
    (hspans : LeanDag.Hydrozoan.IndirectLiveness.SpansEligible
      (S := ofCoreSlots S) Replica c) :
    Descends (rule (Replica := Replica) (BlockId := BlockId)) S c := by
  intro U V b hrun i hi
  have hrun' : ∀ j, b ≤ j → j ≤ b + c - 1 →
      ∃ A, DecidedBelow rule S (b + c) V j (some A) :=
    fun j h1 h2 => hrun j h1 (by omega)
  exact decidedBelow_of_committed_run (by omega) (by omega)
    (fun i hi => hspans b i hi) hrun' i hi

/-- **A commit names the slot's candidate.** Hydrozoan's
`isLeaderBlock_of_decided` under the property's name. Four commit
constructors, each carrying the premise; the discharge is the
coercion. -/
theorem commitsCandidate :
    CommitsCandidate (rule (Replica := Replica) (BlockId := BlockId)) :=
  fun S _ _ _ _ hd =>
    LeanDag.Hydrozoan.isLeaderBlock_of_decided (S := ofCoreSlots S) hd

end Hydrozoan

end LeanDag
