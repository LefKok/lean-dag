import LeanDag.Hydrozoan.Helpers.Banded
import LeanDag.Hydrozoan.Helpers.IndirectLiveness
import LeanDag.Hydrozoan.IndirectLiveness.Statement
import LeanDag.Hydrozoan.DirectLiveness.Proof
import LeanDag.Hydrozoan.SlotAgreement.Proof
import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Support
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Derived.Descent
import LeanDag.Properties.Candidate
import LeanDag.Properties.Deliver

import LeanDag.Timed.Coverage

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
open LeanDag.Timed (SynchronisedOn CoversToward OfCoverage coversToward_of_synchronisedOn)

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]

/-- **Slot agreement as a property.** -/
theorem agree : Agree (rule (Replica := Replica) (BlockId := BlockId)) := by
  intro S U V₁ V₂ k v₁ v₂ h₁ h₂
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

/-! ## Hydrozoan's support shape

`Properties/Support.lean`. The slow path: certificates two rounds above
the candidate, each a block whose voting refs number `q_cert`. The
fast path is latency and is not a liveness shape. -/

omit [LinearOrder BlockId] in
/-- **A quorum's certificates are a slow commit.** The certificate half
of `slowCommit_of_synchronised`, with the coverage argument factored
out so that Optimal-Hydrozoan can take it at its own universe. -/
theorem slowCommit_of_certifiesAt {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    {T : Finset Replica} {r : ℕ} {L : BlockId}
    (hcard : LeanDag.Hydrozoan.q Replica ≤ T.card)
    (hpop2 : ∀ v ∈ T, ∃ C ∈ U.ids, (U.block C).creator = v ∧ (U.block C).round = r + 2)
    (hcert : ∀ v ∈ T, ∀ C, C ∈ U.ids → (U.block C).creator = v → (U.block C).round = r + 2 →
      LeanDag.Hydrozoan.IsCertificate U C L) :
    LeanDag.Hydrozoan.SlowCommit U L r := by
  have hsub : T ⊆ LeanDag.Hydrozoan.certifiers U L r := by
    intro v hv
    obtain ⟨C, hC, hCa, hCr⟩ := hpop2 v hv
    exact LeanDag.mem_creatorsOf.mpr
      ⟨C, LeanDag.Hydrozoan.mem_certificates.mpr ⟨hC, hCr, hcert v hv C hC hCa hCr⟩, hCa⟩
  exact le_trans LeanDag.Hydrozoan.qSlow_le_q (le_trans hcard (Finset.card_le_card hsub))

/-- **Hydrozoan's support**: wavelength two, certification the rule's own. -/
def hzSupport : Support (rule (Replica := Replica) (BlockId := BlockId)) where
  wave := 2
  Certifies := fun U C L => LeanDag.Hydrozoan.IsCertificate U C L

/-- **Law 1.** A certifier two rounds above the settling round keeps its
refs, and each parent keeps its refs and its creator. -/
theorem hzSupport_local :
    Support.Local (R := rule (Replica := Replica) (BlockId := BlockId)) hzSupport := by
  intro U U' G R₀ h c L hc hcr _ _
  change R₀ + 2 ≤ (U.block c).round at hcr
  have hrefs : (U'.block c).refs = (U.block c).refs :=
    h.refs c hc (by change R₀ < (U.block c).round; omega)
  have hpar : ∀ b ∈ (U.block c).refs,
      (U'.block b).refs = (U.block b).refs ∧ (U'.block b).creator = (U.block b).creator := by
    intro b hb
    have hbU := U.complete c hc b hb
    have hbr := (U.valid c hc).predecessor b hb
    exact ⟨h.refs b hbU (by change R₀ < (U.block b).round; omega),
      h.creator b hbU (by change R₀ ≤ (U.block b).round; omega)⟩
  change LeanDag.Hydrozoan.IsCertificate U' c L ↔ LeanDag.Hydrozoan.IsCertificate U c L
  unfold LeanDag.Hydrozoan.IsCertificate LeanDag.Hydrozoan.voteBlocks LeanDag.creatorsOf
  rw [hrefs, Finset.filter_congr (fun b hb => by
      unfold LeanDag.Hydrozoan.IsVote; rw [(hpar b hb).1]),
    Finset.image_congr (fun b hb => (hpar b (Finset.mem_of_mem_filter b hb)).2)]

/-- **Law 2.** Coverage toward the candidate over two layers makes every
quorum block two rounds up a certificate: `isCertificate_of_synchronised`
with its antecedent cut to what it reads. -/
theorem hzSupport_ofCoverage :
    Timed.OfCoverage (R := rule (Replica := Replica) (BlockId := BlockId)) hzSupport
      (hzReliability Replica) := by
  intro U T hq r L hpop hct hL hLr hLc C hC hCc hCr
  have hcard : LeanDag.Hydrozoan.q Replica ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Replica - (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica) ≤ T.card at h2
    unfold LeanDag.Hydrozoan.q; omega
  exact isCertificate_of_coversToward hcard
    (hpop (r + 1) (by omega) (by change r + 1 ≤ r + 2; omega)) hct hL hLr hLc hC hCc hCr

/-- **Law 3.** A quorum's certificates at the slot's candidate are a
slow commit, which a view caught up to the decision round sees. -/
theorem hzSupport_commits :
    Support.Commits (R := rule (Replica := Replica) (BlockId := BlockId)) hzSupport
      (hzReliability Replica) := by
  intro S U V T k hq hpop hcert hcov hlead
  have hcard : LeanDag.Hydrozoan.q Replica ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Replica - (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica) ≤ T.card at h2
    unfold LeanDag.Hydrozoan.q; omega
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 2; omega) (S.leader k) hlead
  have hL : LeanDag.Hydrozoan.IsLeaderBlock U k L := ⟨hLmem, hLr, hLc⟩
  have hslow : LeanDag.Hydrozoan.SlowCommit U L (S.slotRound k) :=
    slowCommit_of_certifiesAt hcard
      (hpop (S.slotRound k + 2) (by omega) (by change S.slotRound k + 2 ≤ S.slotRound k + 2; omega))
      (hcert L ⟨hLmem, hLr, hLc⟩)
  have hin : LeanDag.Hydrozoan.SlowCommitInView U V L (S.slotRound k) :=
    slowCommitInView_of_coversUpto hslow hcov
  refine ⟨L, by omega, LeanDag.Hydrozoan.Decided.directSlow hL hin, ?_⟩
  intro S' hround hlead'
  refine LeanDag.Hydrozoan.Decided.directSlow (S := S') ⟨hL.1, ?_, ?_⟩ ?_
  · change (U.block L).round = S'.slotRound k
    rw [hround]; exact hL.2.1
  · change (U.block L).creator = S'.leader k
    rw [hlead' k (by omega)]; exact hL.2.2
  · change LeanDag.Hydrozoan.SlowCommitInView U V L (S'.slotRound k)
    rw [hround]; exact hin

/-- **Hydrozoan's precondition is the support's.** Coverage from `R₀`
is coverage toward every candidate, and the quorum is inside the
correct set, so `hzLive` is `Support.live` at every slot of the window. -/
theorem hzSupport_live_of_hzLive {S : LeanDag.Slots Replica}
    {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {V : LeanDag.Hydrozoan.View U}
    {T : Finset Replica} {lo K : ℕ} (h : hzLive S (U := U) V T lo K) :
    Support.live (R := rule (Replica := Replica) (BlockId := BlockId)) hzSupport
      (hzReliability Replica) S (U := U) V T lo K := by
  obtain ⟨hT, hcard, R₀, N, hs, hR, hpop, hcov, hN⟩ := h
  have hq : (hzReliability Replica).IsQuorum T := ⟨hT, by
    change Fintype.card Replica -
      (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica) ≤ T.card
    unfold LeanDag.Hydrozoan.q at hcard; omega⟩
  have hpop' : ∀ n, R₀ ≤ n → n ≤ N →
      Properties.PopulatedOn (rule (Replica := Replica) (BlockId := BlockId)) U T n := by
    intro n h1 h2 v hv
    obtain ⟨b, hb, hbr, hba⟩ := hpop n h1 h2 v hv
    exact ⟨b, hb, hba, hbr⟩
  refine ⟨hq, N, hcov, hN, ?_⟩
  intro k hlo hK hlead
  have hRk : R₀ ≤ S.slotRound k := le_trans hR (S.mono hlo)
  have hNk : S.slotRound k + 2 ≤ N := hN k hK
  refine ⟨fun n h1 h2 => hpop' n (by omega) (by change n ≤ S.slotRound k + 2 at h2; omega), ?_⟩
  rintro L ⟨hLmem, hLr, hLc⟩ v hv c hc hcc hcr
  exact hzSupport_ofCoverage U T hq (S.slotRound k) L
    (fun n h1 h2 => hpop' n (by omega) (by change n ≤ S.slotRound k + 2 at h2; omega))
    (Timed.coversToward_of_synchronisedOn hs hRk) hLmem hLr (by rw [hLc]; exact hlead)
    c hc (by rw [hcc]; exact hv) hcr

/-- **Direct liveness as a property**, now a corollary: the bridge
composed with the one `LeaderCommits` every support has. -/
theorem leaderCommits :
    LeaderCommits (rule (Replica := Replica) (BlockId := BlockId))
      (fun S {U} V T lo K => hzLive S (U := U) V T lo K) :=
  fun S _ V T lo K h =>
    Support.leaderCommits hzSupport hzSupport_commits S V T lo K (hzSupport_live_of_hzLive h)

/-! ## Hydrozoan's fast path

A second `Support` for the same rule, which is what the parameter form
is for. The fast path is `voteSupport`: one round up, certifying is
referencing, so Laws 1 and 2 are the generic ones. What it costs is the
fault model: `q_fast = n − p` votes, and a reliable set that large exists
only when at most `p` replicas are faulty. `hzFastReliability` is that
model, and Law 3 holds under it. -/

/-- **The fast path's fault model**: at most `p` replicas Byzantine or
crashed, so the correct set carries `q_fast`. -/
def hzFastReliability (Replica : Type) [Fintype Replica] [DecidableEq Replica]
    [F : LeanDag.Hydrozoan.Faults Replica]
    (h : (F.byzantine ∪ F.crashed).card ≤ LeanDag.Hydrozoan.p Replica) :
    LeanDag.Reliability Replica where
  correct := (LeanDag.Hydrozoan.Correct : Finset Replica)
  slack := LeanDag.Hydrozoan.p Replica
  covers := by
    have hc : (LeanDag.Hydrozoan.Correct : Finset Replica)ᶜ = F.byzantine ∪ F.crashed := by
      simp [LeanDag.Hydrozoan.Correct]
    rw [hc]; exact h
  minority := by
    have := F.card_replicas
    unfold LeanDag.Hydrozoan.p; omega

omit [LinearOrder BlockId] in
/-- A view caught up to the voting round holds every vote, so a fast
commit in the universe is a fast commit in that view. -/
theorem fastCommitInView_of_coversUpto {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    {V : LeanDag.Hydrozoan.View U} {L : BlockId} {r : ℕ}
    (h : LeanDag.Hydrozoan.FastCommit U L r) (hcov : V.CoversUpto (r + 1)) :
    LeanDag.Hydrozoan.FastCommitInView U V L r := by
  have hsub : (LeanDag.Hydrozoan.blocksAt U (r + 1)).filter
      (fun b => LeanDag.Hydrozoan.IsVote U b L) ⊆ V.ids := by
    intro b hb
    obtain ⟨hbA, -⟩ := Finset.mem_filter.mp hb
    obtain ⟨hbU, hbr⟩ := LeanDag.Hydrozoan.mem_blocksAt.mp hbA
    exact hcov b hbU (le_of_eq hbr)
  unfold LeanDag.Hydrozoan.FastCommitInView LeanDag.Hydrozoan.supportersInView
  rw [Finset.inter_eq_left.2 hsub]
  exact h

/-- **Law 3 of `voteSupport`, for Hydrozoan's fast path**, under the fast
fault model: `q_fast` votes one round up are a fast commit, and a view
caught up to the voting round sees it. -/
theorem voteSupport_fast_commits
    (h : (LeanDag.Hydrozoan.Faults.byzantine ∪ LeanDag.Hydrozoan.Faults.crashed :
      Finset Replica).card ≤ LeanDag.Hydrozoan.p Replica) :
    Support.Commits (R := rule (Replica := Replica) (BlockId := BlockId))
      (voteSupport (rule (Replica := Replica) (BlockId := BlockId)))
      (hzFastReliability Replica h) := by
  intro S U V T k hq hpop hcert hcov hlead
  have hcard : LeanDag.Hydrozoan.qFast Replica ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Replica - LeanDag.Hydrozoan.p Replica ≤ T.card at h2
    exact h2
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 1; omega) (S.leader k) hlead
  have hL : LeanDag.Hydrozoan.IsLeaderBlock U k L := ⟨hLmem, hLr, hLc⟩
  have hfast : LeanDag.Hydrozoan.FastCommit U L (S.slotRound k) := by
    have hsub : T ⊆ LeanDag.Hydrozoan.supporters U L (S.slotRound k + 1) := by
      intro v hv
      obtain ⟨b, hb, hba, hbr⟩ := hpop (S.slotRound k + 1) (by omega)
        (by change S.slotRound k + 1 ≤ S.slotRound k + 1; omega) v hv
      exact LeanDag.Hydrozoan.mem_supporters.mpr
        ⟨b, hb, hbr, hcert L ⟨hLmem, hLr, hLc⟩ v hv b hb hba hbr, hba⟩
    exact le_trans hcard (Finset.card_le_card hsub)
  have hin : LeanDag.Hydrozoan.FastCommitInView U V L (S.slotRound k) :=
    fastCommitInView_of_coversUpto hfast hcov
  refine ⟨L, by omega, LeanDag.Hydrozoan.Decided.directFast hL hin, ?_⟩
  intro S' hround hlead'
  refine LeanDag.Hydrozoan.Decided.directFast (S := S') ⟨hL.1, ?_, ?_⟩ ?_
  · change (U.block L).round = S'.slotRound k
    rw [hround]; exact hL.2.1
  · change (U.block L).creator = S'.leader k
    rw [hlead' k (by omega)]; exact hL.2.2
  · change LeanDag.Hydrozoan.FastCommitInView U V L (S'.slotRound k)
    rw [hround]; exact hin



/-! ## The descent, at a bound -/

theorem eligibleAsAnchor_sched {S S' : LeanDag.Slots Replica}
    (hround : S'.slotRound = S.slotRound) {x y : ℕ} :
    LeanDag.Hydrozoan.EligibleAsAnchor (S := S') Replica x y ↔
      LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica x y := by
  unfold LeanDag.Hydrozoan.EligibleAsAnchor LeanDag.Hydrozoan.decisionRound
  change S'.slotRound x + 2 < S'.slotRound y ↔ S.slotRound x + 2 < S.slotRound y
  rw [hround]

open Classical in
/-- **HZ6 as a property.** The graded rule is total: an eligible
committed anchor, with the eligible slots between skipped, decides the
slot. Three rungs, tried in order — a certified candidate, else the
least weak-linked one, else a skip — and each rung reads the leaders at
the slot it decides and at no other, which is why the same verdict
stands under any schedule naming the same rounds and the same leader
there. That clause is what `Descends` needs and what a mechanism
tracking bounds consumes.

The totality lemma this replaced was stated over `DecidedBelow` on both
sides; the property takes plain verdicts per schedule instead, which is
the same argument with the bookkeeping moved out to
`Derived/Descent.lean`. -/
theorem indirect :
    Indirect (rule (Replica := Replica) (BlockId := BlockId))
      (fun sr i j => sr i + 3 ≤ sr j) := by
  classical
  intro S U V k j A helig hj hmid
  have hea : LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k j := by
    change S.slotRound k + 2 < S.slotRound j; omega
  have hmidE : ∀ i, k < i → i < j →
      LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k i →
      S.slotRound k + 3 ≤ S.slotRound i := by
    intro i _ _ h3
    change S.slotRound k + 2 < S.slotRound i at h3; omega
  have hkj : k < j := lt_of_eligibleAsAnchor (S := S) hea
  have hmidD : ∀ i, k < i → i < j →
      LeanDag.Hydrozoan.EligibleAsAnchor (S := S) Replica k i →
      LeanDag.Hydrozoan.Decided (S := S) U V i none :=
    fun i h1 h2 h3 => hmid i h1 h2 (hmidE i h1 h2 h3)
  by_cases hc : ∃ L, LeanDag.Hydrozoan.IsLeaderBlock (S := S) U k L ∧
      LeanDag.Hydrozoan.CertifiedIn U A L (S.slotRound k)
  · obtain ⟨L, hL, hcert⟩ := hc
    refine ⟨some L, fun S' hround hlead hj' hmid' => ?_⟩
    exact LeanDag.Hydrozoan.Decided.indirectCert (S := S') hkj
      ((eligibleAsAnchor_sched hround).mpr hea) hj'
      (fun i h1 h2 h3 => hmid' i h1 h2 (hmidE i h1 h2 ((eligibleAsAnchor_sched hround).mp h3)))
      (isLeaderBlock_sched (S₁ := S) (S₂ := S')
        (by change S.slotRound k = S'.slotRound k; rw [hround])
        (by change S.leader k = S'.leader k; rw [hlead]) hL)
      (by change LeanDag.Hydrozoan.CertifiedIn U A L (S'.slotRound k); rw [hround]; exact hcert)
  · push Not at hc
    by_cases hw : ∃ L, LeanDag.Hydrozoan.IsLeaderBlock (S := S) U k L ∧
        LeanDag.Hydrozoan.WeakLinked U A L (S.slotRound k)
    · obtain ⟨L₀, hL₀, hw₀, hleast⟩ := exists_least_weak_candidate (S := S) hw
      refine ⟨some L₀, fun S' hround hlead hj' hmid' => ?_⟩
      have hls : ∀ L', LeanDag.Hydrozoan.IsLeaderBlock (S := S') U k L' →
          LeanDag.Hydrozoan.IsLeaderBlock (S := S) U k L' := fun L' hL' =>
        isLeaderBlock_sched (S₁ := S') (S₂ := S)
          (by change S'.slotRound k = S.slotRound k; rw [hround])
          (by change S'.leader k = S.leader k; rw [hlead]) hL'
      refine LeanDag.Hydrozoan.Decided.indirectWeak (S := S') hkj
        ((eligibleAsAnchor_sched hround).mpr hea) hj'
        (fun i h1 h2 h3 => hmid' i h1 h2
          (hmidE i h1 h2 ((eligibleAsAnchor_sched hround).mp h3))) ?_
        (isLeaderBlock_sched (S₁ := S) (S₂ := S')
          (by change S.slotRound k = S'.slotRound k; rw [hround])
          (by change S.leader k = S'.leader k; rw [hlead]) hL₀) ?_ ?_
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
      refine ⟨none, fun S' hround hlead hj' hmid' => ?_⟩
      have hls : ∀ L', LeanDag.Hydrozoan.IsLeaderBlock (S := S') U k L' →
          LeanDag.Hydrozoan.IsLeaderBlock (S := S) U k L' := fun L' hL' =>
        isLeaderBlock_sched (S₁ := S') (S₂ := S)
          (by change S'.slotRound k = S.slotRound k; rw [hround])
          (by change S'.leader k = S.leader k; rw [hlead]) hL'
      refine LeanDag.Hydrozoan.Decided.indirectSkip (S := S') hkj
        ((eligibleAsAnchor_sched hround).mpr hea) hj'
        (fun i h1 h2 h3 => hmid' i h1 h2
          (hmidE i h1 h2 ((eligibleAsAnchor_sched hround).mp h3))) ?_ ?_
      · intro L' hL' hc'
        refine hc L' (hls L' hL') ?_
        change LeanDag.Hydrozoan.CertifiedIn U A L' (S'.slotRound k) at hc'
        rw [hround] at hc'; exact hc'
      · intro L' hL' hw'
        refine hw L' (hls L' hL') ?_
        change LeanDag.Hydrozoan.WeakLinked U A L' (S'.slotRound k) at hw'
        rw [hround] at hw'; exact hw'

/-- **The descent as a property.** Was two lemmas — the graded rule at a
bound and a downward induction over the run; both are now
`Descends.of_indirect`. -/
theorem descends {S : LeanDag.Slots Replica} {c : ℕ} (hc : 0 < c)
    (hspans : LeanDag.Hydrozoan.IndirectLiveness.SpansEligible
      (S := S) Replica c) :
    Descends (rule (Replica := Replica) (BlockId := BlockId)) S c :=
  Descends.of_indirect indirect hc (fun b i hi => by
    have := hspans b i hi
    change S.slotRound i + 2 < S.slotRound (b + c - 1) at this
    omega)


/-- **A commit names the slot's candidate.** Hydrozoan's
`isLeaderBlock_of_decided` under the property's name. Four commit
constructors, each carrying the premise; the discharge is the
coercion. -/
theorem commitsCandidate :
    CommitsCandidate (rule (Replica := Replica) (BlockId := BlockId)) :=
  fun S _ _ _ _ hd =>
    LeanDag.Hydrozoan.isLeaderBlock_of_decided (S := S) hd

/-- **A direct commit is a verdict**, at Hydrozoan's own direct
predicate — which is a *disjunction*, the fast path or the slow one.
The two constructors under the property's name.

Hydrozoan had no `CommitsDirect` until `scripts/audit-bespoke.py` found
`Barnacle.Hydrozoan.holds` reaching past the properties for it: the law
it discharges, `Laws.decided_of_directCommitIn`, is this property, and
was being proved from the constructors a second time. -/
theorem commitsDirect :
    Properties.CommitsDirect (rule (Replica := Replica) (BlockId := BlockId))
      (fun {U} V L r => LeanDag.Hydrozoan.FastCommitInView U V L r ∨
        LeanDag.Hydrozoan.SlowCommitInView U V L r) := by
  intro S U V k L hL hc
  exact hc.elim (LeanDag.Hydrozoan.Decided.directFast hL)
    (LeanDag.Hydrozoan.Decided.directSlow hL)

/-- The carrier's coverage predicate is Hydrozoan's. -/
theorem coversUpto_eq {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    {V : LeanDag.Hydrozoan.View U} {N : ℕ} :
    Properties.CoversUpto (rule (Replica := Replica) (BlockId := BlockId)) V N ↔
      V.CoversUpto N := Iff.rfl

/-- **A caught-up replica reaches every verdict**, at the band's own
ceiling rather than a rule-specific round. What a view-level mechanism
has to deliver, for this protocol. -/
theorem exists_coversUpto_decides {S : LeanDag.Slots Replica}
    {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    {W : LeanDag.Hydrozoan.View U} {k : ℕ} {v : Option BlockId}
    (hW : LeanDag.Hydrozoan.Decided (S := S) U W k v) :
    ∃ N, ∀ V : LeanDag.Hydrozoan.View U, V.CoversUpto N →
      LeanDag.Hydrozoan.Decided (S := S) U V k v :=
  Properties.exists_coversUpto_decides banded (S := S) hW

end Hydrozoan

end LeanDag
