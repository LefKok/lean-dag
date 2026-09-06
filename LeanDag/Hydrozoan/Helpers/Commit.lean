import LeanDag.Hydrozoan.Helpers.Banded
import LeanDag.Hydrozoan.Helpers.IndirectLiveness
import LeanDag.Hydrozoan.IndirectLiveness.Statement
import LeanDag.Hydrozoan.DirectLiveness.Proof
import LeanDag.Hydrozoan.SlotAgreement.Proof
import LeanDag.Properties.Commit
import LeanDag.Properties.Live
import LeanDag.Properties.Support
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Derived.Descent
import LeanDag.Properties.Candidate
import LeanDag.Properties.Deliver

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

/-! ## Hydrozoan's support shape

`Properties/Support.lean`. The slow path: certificates two rounds above
the candidate, each a block whose voting parents number `q_cert`. The
fast path is latency and is not a liveness shape. -/

/-- **A quorum's certificates are a slow commit.** The certificate half
of `slowCommit_of_synchronised`, with the coverage argument factored
out so that Optimal-Hydrozoan can take it at its own universe. -/
theorem slowCommit_of_certifiesAt {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    {T : Finset Replica} {r : ℕ} {L : BlockId}
    (hcard : LeanDag.Hydrozoan.q Replica ≤ T.card)
    (hpop2 : ∀ v ∈ T, ∃ C ∈ U.ids, (U.block C).author = v ∧ (U.block C).round = r + 2)
    (hcert : ∀ v ∈ T, ∀ C, C ∈ U.ids → (U.block C).author = v → (U.block C).round = r + 2 →
      LeanDag.Hydrozoan.IsCertificate U C L) :
    LeanDag.Hydrozoan.SlowCommit U L r := by
  have hsub : T ⊆ LeanDag.Hydrozoan.certifiers U L r := by
    intro v hv
    obtain ⟨C, hC, hCa, hCr⟩ := hpop2 v hv
    exact LeanDag.Hydrozoan.mem_authorsOf.mpr
      ⟨C, LeanDag.Hydrozoan.mem_certificates.mpr ⟨hC, hCr, hcert v hv C hC hCa hCr⟩, hCa⟩
  exact le_trans LeanDag.Hydrozoan.qSlow_le_q (le_trans hcard (Finset.card_le_card hsub))

/-- **Hydrozoan's support**: wavelength two, certification the rule's own. -/
def hzSupport : Support (rule (Replica := Replica) (BlockId := BlockId)) where
  wave := 2
  Certifies := fun U C L => LeanDag.Hydrozoan.IsCertificate U C L

/-- **Law 1.** A certifier two rounds above the settling round keeps its
parents, and each parent keeps its parents and its author. -/
theorem hzSupport_local :
    Support.Local (R := rule (Replica := Replica) (BlockId := BlockId)) hzSupport := by
  intro U U' G R₀ h c L hc hcr _ _
  change R₀ + 2 ≤ (U.block c).round at hcr
  have hrefs : (U'.block c).parents = (U.block c).parents :=
    h.refs c hc (by change R₀ < (U.block c).round; omega)
  have hpar : ∀ b ∈ (U.block c).parents,
      (U'.block b).parents = (U.block b).parents ∧ (U'.block b).author = (U.block b).author := by
    intro b hb
    have hbU := U.complete c hc b hb
    have hbr := (U.valid c hc).predecessor b hb
    exact ⟨h.refs b hbU (by change R₀ < (U.block b).round; omega),
      h.creator b hbU (by change R₀ ≤ (U.block b).round; omega)⟩
  change LeanDag.Hydrozoan.IsCertificate U' c L ↔ LeanDag.Hydrozoan.IsCertificate U c L
  unfold LeanDag.Hydrozoan.IsCertificate LeanDag.Hydrozoan.voteBlocks LeanDag.Hydrozoan.authorsOf
  rw [hrefs, Finset.filter_congr (fun b hb => by
      unfold LeanDag.Hydrozoan.IsVote; rw [(hpar b hb).1]),
    Finset.image_congr (fun b hb => (hpar b (Finset.mem_of_mem_filter b hb)).2)]

/-- **Law 2.** Coverage toward the candidate over two layers makes every
quorum block two rounds up a certificate: `isCertificate_of_synchronised`
with its antecedent cut to what it reads. -/
theorem hzSupport_ofCoverage :
    Support.OfCoverage (R := rule (Replica := Replica) (BlockId := BlockId)) hzSupport
      (hzReliability Replica) := by
  intro U T hq r L hpop hct hL hLr hLc C hC hCc hCr
  have hcard : LeanDag.Hydrozoan.q Replica ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Replica - (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica) ≤ T.card at h2
    unfold LeanDag.Hydrozoan.q; omega
  have hLr' : (U.block L).round = r := hLr
  have hLc' : (U.block L).author ∈ T := hLc
  have hCr' : (U.block C).round = r + 2 := hCr
  have hCc' : (U.block C).author ∈ T := hCc
  change LeanDag.Hydrozoan.IsCertificate U C L
  have hsub : T ⊆ LeanDag.Hydrozoan.authorsOf U.block (LeanDag.Hydrozoan.voteBlocks U C L) := by
    intro v hv
    obtain ⟨b, hb, hba, hbr⟩ := hpop (r + 1) (by omega) (by change r + 1 ≤ r + 2; omega) v hv
    have hba' : (U.block b).author = v := hba
    have hbr' : (U.block b).round = r + 1 := hbr
    have hbT : (U.block b).author ∈ T := by rw [hba']; exact hv
    have hvote : L ∈ (U.block b).parents :=
      hct r le_rfl (by change r < r + 2; omega) b hb hbT hbr' L hL hLc' hLr'
        Relation.ReflTransGen.refl
    have href : b ∈ (U.block C).parents :=
      hct (r + 1) (by omega) (by change r + 1 < r + 2; omega) C hC hCc'
        (by change (U.block C).round = r + 1 + 1; rw [hCr']) b hb hbT hbr'
        (Relation.ReflTransGen.single (show RefStepFrom (rule.block U) b L from hvote))
    exact LeanDag.Hydrozoan.mem_authorsOf.mpr ⟨b, Finset.mem_filter.mpr ⟨href, hvote⟩, hba'⟩
  exact le_trans LeanDag.Hydrozoan.qCert_le_q (le_trans hcard (Finset.card_le_card hsub))

/-- **Law 3.** A quorum's certificates at the slot's candidate are a
slow commit, which a view caught up to the decision round sees. -/
theorem hzSupport_commits :
    Support.Commits (R := rule (Replica := Replica) (BlockId := BlockId)) hzSupport
      (hzReliability Replica) := by
  intro S U V T k hq hpop hcert hcov hlead
  letI : LeanDag.Hydrozoan.Slots Replica := ofCoreSlots S
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
  refine LeanDag.Hydrozoan.Decided.directSlow (S := ofCoreSlots S') ⟨hL.1, ?_, ?_⟩ ?_
  · change (U.block L).round = S'.slotRound k
    rw [hround]; exact hL.2.1
  · change (U.block L).author = S'.leader k
    rw [hlead' k (by omega)]; exact hL.2.2
  · change LeanDag.Hydrozoan.SlowCommitInView U V L (S'.slotRound k)
    rw [hround]; exact hin

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
  letI : LeanDag.Hydrozoan.Slots Replica := ofCoreSlots S
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
  refine LeanDag.Hydrozoan.Decided.directFast (S := ofCoreSlots S') ⟨hL.1, ?_, ?_⟩ ?_
  · change (U.block L).round = S'.slotRound k
    rw [hround]; exact hL.2.1
  · change (U.block L).author = S'.leader k
    rw [hlead' k (by omega)]; exact hL.2.2
  · change LeanDag.Hydrozoan.FastCommitInView U V L (S'.slotRound k)
    rw [hround]; exact hin

/-- **Hydrozoan's precondition is reachable** (`Properties/Live.lean`).
The reliable set is `Correct`, which carries the quorum, and the
wavelength is two. -/
theorem liveReachable :
    LiveReachable (rule (Replica := Replica) (BlockId := BlockId))
      (hzReliability Replica) 2
      (fun S {U} V T lo K => hzLive S (U := U) V T lo K) := by
  intro U Rnd N hs hpop S V k hcov hRnd hN
  refine ⟨Finset.Subset.rfl, q_le_card_correct, Rnd, N, hs, hRnd, ?_, hcov, ?_⟩
  · intro r h1 h2 v hv
    obtain ⟨b, hb, hbc, hbr⟩ := hpop r h1 h2 v hv
    exact ⟨b, hb, hbr, hbc⟩
  · intro j hj
    have := S.mono (Nat.lt_succ_iff.mp hj)
    omega

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
  have hea : LeanDag.Hydrozoan.EligibleAsAnchor (S := ofCoreSlots S) Replica k j := by
    change S.slotRound k + 2 < S.slotRound j; omega
  have hmidE : ∀ i, k < i → i < j →
      LeanDag.Hydrozoan.EligibleAsAnchor (S := ofCoreSlots S) Replica k i →
      S.slotRound k + 3 ≤ S.slotRound i := by
    intro i _ _ h3
    change S.slotRound k + 2 < S.slotRound i at h3; omega
  have hkj : k < j := lt_of_eligibleAsAnchor (S := ofCoreSlots S) hea
  have hmidD : ∀ i, k < i → i < j →
      LeanDag.Hydrozoan.EligibleAsAnchor (S := ofCoreSlots S) Replica k i →
      LeanDag.Hydrozoan.Decided (S := ofCoreSlots S) U V i none :=
    fun i h1 h2 h3 => hmid i h1 h2 (hmidE i h1 h2 h3)
  by_cases hc : ∃ L, LeanDag.Hydrozoan.IsLeaderBlock (S := ofCoreSlots S) U k L ∧
      LeanDag.Hydrozoan.CertifiedIn U A L ((ofCoreSlots S).slotRound k)
  · obtain ⟨L, hL, hcert⟩ := hc
    refine ⟨some L, fun S' hround hlead hj' hmid' => ?_⟩
    exact LeanDag.Hydrozoan.Decided.indirectCert (S := ofCoreSlots S') hkj
      ((eligibleAsAnchor_sched hround).mpr hea) hj'
      (fun i h1 h2 h3 => hmid' i h1 h2 (hmidE i h1 h2 ((eligibleAsAnchor_sched hround).mp h3)))
      (isLeaderBlock_sched (S₁ := ofCoreSlots S) (S₂ := ofCoreSlots S')
        (by change S.slotRound k = S'.slotRound k; rw [hround])
        (by change S.leader k = S'.leader k; rw [hlead]) hL)
      (by change LeanDag.Hydrozoan.CertifiedIn U A L (S'.slotRound k); rw [hround]; exact hcert)
  · push Not at hc
    by_cases hw : ∃ L, LeanDag.Hydrozoan.IsLeaderBlock (S := ofCoreSlots S) U k L ∧
        LeanDag.Hydrozoan.WeakLinked U A L ((ofCoreSlots S).slotRound k)
    · obtain ⟨L₀, hL₀, hw₀, hleast⟩ := exists_least_weak_candidate (S := ofCoreSlots S) hw
      refine ⟨some L₀, fun S' hround hlead hj' hmid' => ?_⟩
      have hls : ∀ L', LeanDag.Hydrozoan.IsLeaderBlock (S := ofCoreSlots S') U k L' →
          LeanDag.Hydrozoan.IsLeaderBlock (S := ofCoreSlots S) U k L' := fun L' hL' =>
        isLeaderBlock_sched (S₁ := ofCoreSlots S') (S₂ := ofCoreSlots S)
          (by change S'.slotRound k = S.slotRound k; rw [hround])
          (by change S'.leader k = S.leader k; rw [hlead]) hL'
      refine LeanDag.Hydrozoan.Decided.indirectWeak (S := ofCoreSlots S') hkj
        ((eligibleAsAnchor_sched hround).mpr hea) hj'
        (fun i h1 h2 h3 => hmid' i h1 h2
          (hmidE i h1 h2 ((eligibleAsAnchor_sched hround).mp h3))) ?_
        (isLeaderBlock_sched (S₁ := ofCoreSlots S) (S₂ := ofCoreSlots S')
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
      have hls : ∀ L', LeanDag.Hydrozoan.IsLeaderBlock (S := ofCoreSlots S') U k L' →
          LeanDag.Hydrozoan.IsLeaderBlock (S := ofCoreSlots S) U k L' := fun L' hL' =>
        isLeaderBlock_sched (S₁ := ofCoreSlots S') (S₂ := ofCoreSlots S)
          (by change S'.slotRound k = S.slotRound k; rw [hround])
          (by change S'.leader k = S.leader k; rw [hlead]) hL'
      refine LeanDag.Hydrozoan.Decided.indirectSkip (S := ofCoreSlots S') hkj
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
      (S := ofCoreSlots S) Replica c) :
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
    LeanDag.Hydrozoan.isLeaderBlock_of_decided (S := ofCoreSlots S) hd

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
  letI : LeanDag.Hydrozoan.Slots Replica := ofCoreSlots S
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
    (hW : LeanDag.Hydrozoan.Decided (S := ofCoreSlots S) U W k v) :
    ∃ N, ∀ V : LeanDag.Hydrozoan.View U, V.CoversUpto N →
      LeanDag.Hydrozoan.Decided (S := ofCoreSlots S) U V k v :=
  Properties.exists_coversUpto_decides banded (S := S) hW

end Hydrozoan

end LeanDag
