import LeanDag.OptimalHydrozoan.SlotAgreement.Proof
import LeanDag.OptimalHydrozoan.Helpers.Banded
import LeanDag.Barnacle.Helpers.OptimalHydrozoan
import LeanDag.Hydrozoan.Helpers.Carrier
import LeanDag.Hydrozoan.Helpers.Commit
import LeanDag.OptimalHydrozoan.DirectLiveness.Proof
import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Support
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Optional.Quorate

import LeanDag.Timed.Coverage

import LeanDag.Properties.Arcs.Headline

/-!
# Optimal-Hydrozoan as a carrier, and the three properties its rules give

`docs/porting-plan.md` step 3. The carrier and the properties whose
proof is a single Optimal theorem apiece.

**The universe looked as though it could not be a carrier, and the way
out is a fact about the rule rather than about the interface.**
`OptUniverse` is *indexed by the schedule*: its `leader_excluded` field
reads `S.leader k` and `decisionRound k`, so `OptUniverse` at `S` and at
`S'` are different types. `DagRule.Universe` is one type, and
`Properties.Banded` compares verdicts across schedules — so a carrier
over `OptUniverse` could not state the band at all, and the cut's own
`optChopHZ` lands in a *different* universe type from the one it starts
in.

`LeaderExcludedAll` is the escape, and it was already in the
development: the same exclusion quantified over rounds and validators
rather than over slots, hence schedule-free, with `optUniverseOf`
rebuilding the indexed universe at whatever schedule is wanted. The
carrier's universe is the subtype it cuts out, exactly as Hybrid's is
the subtype `HonestNoEquiv` cuts out, and the schedule re-enters where
`DagRule` puts it — in `Decided`.
-/

namespace LeanDag

namespace OptimalHydrozoanProperties

open LeanDag.Properties
open LeanDag.Timed (SynchronisedOn CoversToward OfCoverage coversToward_of_synchronisedOn)

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId]
variable [O : LeanDag.OptimalHydrozoan.OptimalFaults Replica]

/-- **Optimal-Hydrozoan as a carrier.** -/
def optimalRule : DagRule Replica BlockId Unit where
  Universe := {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId //
    Barnacle.OptimalHydrozoan.LeaderExcludedAll U}
  View := fun U => LeanDag.Hydrozoan.View U.val
  block := fun U i => LeanDag.Hydrozoan.adaptBlock (U.val.block i)
  ids := fun U => U.val.ids
  viewIds := fun V => V.ids
  viewSound := fun V => V.subset_ids
  viewComplete := fun V => V.complete
  causal := fun U =>
    { complete := fun i hi j hj => U.val.complete i hi j hj
      refs_round := fun i hi j hj => (U.val.valid i hi).predecessor j hj }
  Decided := fun S U V k v =>
    letI := LeanDag.Hydrozoan.ofCoreSlots S
    LeanDag.OptimalHydrozoan.DecidedOpt
      (Barnacle.OptimalHydrozoan.optUniverseOf U.val U.property) V k v

/-- **Optimal-Hydrozoan's universes are quorate.** The underlying
universe is Hydrozoan's, so the clause and the fault model are
Hydrozoan's. -/
theorem quorate : Quorate (optimalRule (Replica := Replica) (BlockId := BlockId))
    (LeanDag.Hydrozoan.hzReliability Replica) := by
  intro U b hb hr
  have h := (U.val.valid b hb).quorum hr
  have hq : LeanDag.Hydrozoan.q Replica
      = Fintype.card Replica - (LeanDag.Hydrozoan.hzReliability Replica).slack := by
    show LeanDag.Hydrozoan.q Replica = Fintype.card Replica - (_ + _)
    unfold LeanDag.Hydrozoan.q; omega
  rw [hq] at h
  exact h

/-- **Two views decide alike.** OH5 under the property's name, and
unconditional because the exclusion invariant is a field of the
universe. -/
theorem agree : Agree (optimalRule (Replica := Replica) (BlockId := BlockId)) :=
  fun S U V₁ V₂ _ _ _ h₁ h₂ =>
    letI := LeanDag.Hydrozoan.ofCoreSlots S
    LeanDag.OptimalHydrozoan.SlotAgreement.decided_unique h₁ V₂ _ h₂

/-- **A commit names the slot's candidate.** -/
theorem commitsCandidate :
    CommitsCandidate (optimalRule (Replica := Replica) (BlockId := BlockId)) :=
  fun S _ _ _ _ hd =>
    letI := LeanDag.Hydrozoan.ofCoreSlots S
    LeanDag.OptimalHydrozoan.isLeaderBlock_of_decidedOpt hd

set_option maxHeartbeats 1000000 in
/-- **And a direct commit is a verdict**, at Optimal's own direct
predicate — a *disjunction*, the fast path or the slow one. -/
theorem commitsDirect :
    CommitsDirect (optimalRule (Replica := Replica) (BlockId := BlockId))
      (fun {U} V L r => LeanDag.OptimalHydrozoan.FastCommitOptInView U.val V L r ∨
        LeanDag.Hydrozoan.SlowCommitInView U.val V L r) := by
  intro S U V k L hL hc
  letI := LeanDag.Hydrozoan.ofCoreSlots S
  rcases hc with h | h
  · exact LeanDag.OptimalHydrozoan.DecidedOpt.directFast hL h
  · exact LeanDag.OptimalHydrozoan.DecidedOpt.directSlow hL h

/-! ## The band

`Banded` was the property this carrier was built for and the one it
could not state until `LeaderExcludedAll` made the universe
schedule-free. The induction is `bandedOpt_aux`, over `DecidedOpt`'s six
constructors; what is left here is reading the band at Optimal's carrier
as a band at Hydrozoan's, which is what lets the whole of
`Hydrozoan/Helpers/Banded.lean` be reused. -/

/-- **A band at this carrier is a band at Hydrozoan's.** The subtype's
projections are the underlying universe's, so the two statements are the
same statement. -/
theorem band_of [LinearOrder BlockId]
    {U U' : (optimalRule (Replica := Replica) (BlockId := BlockId)).Universe}
    {lo hi g g' : ℕ} (hab : AgreeBand (optimalRule (Replica := Replica) (BlockId := BlockId))
      U U' lo hi g g') :
    AgreeBand (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
      U.val U'.val lo hi g g' where
  mem := hab.mem
  block := hab.block
  refs := hab.refs

/-- **Optimal-Hydrozoan reads a band.** -/
theorem banded [LinearOrder BlockId] :
    Banded (optimalRule (Replica := Replica) (BlockId := BlockId)) := by
  intro S U V k v hd
  obtain ⟨top, -, ht⟩ :=
    LeanDag.OptimalHydrozoan.bandedOpt_aux (S := LeanDag.Hydrozoan.ofCoreSlots S)
      (Barnacle.OptimalHydrozoan.optUniverseOf_leader_excluded
        (S := LeanDag.Hydrozoan.ofCoreSlots S) U.val U.property) hd
  refine ⟨top, fun g g' d d' S' U' V' k' hkd hsch hlead hab hV => ?_⟩
  exact ht g g' d d' (LeanDag.Hydrozoan.ofCoreSlots S') U'.val
    (Barnacle.OptimalHydrozoan.optUniverseOf_leader_excluded
      (S := LeanDag.Hydrozoan.ofCoreSlots S') U'.val U'.property) V' k'
    hkd hsch hlead (band_of hab) hV

/-! ## The two liveness properties

`Descends` is not among them: it follows from `Indirect` by the generic
induction of `Properties/Derived/Descent.lean`. -/

/-- **Optimal-Hydrozoan's liveness precondition**, over a slot window.
Hydrozoan's, unchanged: the slow path is the one that carries the
guarantee, and Optimal leaves it alone — the fast path is about
latency, not liveness. -/
def optLive (S : LeanDag.Slots Replica)
    {U : (optimalRule (Replica := Replica) (BlockId := BlockId)).Universe}
    (V : LeanDag.Hydrozoan.View U.val) (T : Finset Replica) (lo K : ℕ) : Prop :=
  T ⊆ (LeanDag.Hydrozoan.Correct : Finset Replica) ∧
    LeanDag.Hydrozoan.q Replica ≤ T.card ∧
    ∃ R₀ N, LeanDag.Hydrozoan.SynchronisedOn U.val T R₀ ∧ R₀ ≤ S.slotRound lo ∧
      (∀ r, R₀ ≤ r → r ≤ N → LeanDag.Hydrozoan.PopulatedOn U.val T r) ∧
      LeanDag.Hydrozoan.View.CoversUpto V N ∧
      ∀ k, k < K → S.slotRound k + 2 ≤ N

/-! ## Optimal-Hydrozoan's support shape

Hydrozoan's, at the underlying universe: Optimal changes the fast path
and the skip, and the slow path is what liveness runs on. Laws 1 and 2
are Hydrozoan's applied — the carrier projects to the same blocks — and
Law 3 is Hydrozoan's slow commit wrapped in `DecidedOpt`. -/

/-- **Optimal-Hydrozoan's support.** -/
def optSupport : Support (optimalRule (Replica := Replica) (BlockId := BlockId)) where
  wave := 2
  Certifies := fun U C L => LeanDag.Hydrozoan.IsCertificate U.val C L

/-- **Law 1**, Hydrozoan's at the underlying universe. -/
theorem optSupport_local [LinearOrder BlockId] :
    Support.Local (R := optimalRule (Replica := Replica) (BlockId := BlockId)) optSupport := by
  intro U U' G R₀ h c L hc hcr hL hLr
  exact LeanDag.Hydrozoan.hzSupport_local (U := U.val) (U' := U'.val)
    ⟨h.mem, h.round, h.creator, h.refs⟩ c L hc hcr hL hLr

/-- **Law 2**, Hydrozoan's at the underlying universe. -/
theorem optSupport_ofCoverage :
    Timed.OfCoverage (R := optimalRule (Replica := Replica) (BlockId := BlockId)) optSupport
      (LeanDag.Hydrozoan.hzReliability Replica) := by
  intro U T hq r L hpop hct hL hLr hLc c hc hcc hcr
  have hcard : LeanDag.Hydrozoan.q Replica ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Replica -
      (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica) ≤ T.card at h2
    unfold LeanDag.Hydrozoan.q; omega
  exact LeanDag.Hydrozoan.isCertificate_of_coversToward hcard
    (hpop (r + 1) (by omega) (by change r + 1 ≤ r + 2; omega)) hct hL hLr hLc hc hcc hcr

/-- **Law 3**: the slow commit, in `DecidedOpt`. -/
theorem optSupport_commits :
    Support.Commits (R := optimalRule (Replica := Replica) (BlockId := BlockId)) optSupport
      (LeanDag.Hydrozoan.hzReliability Replica) := by
  intro S U V T k hq hpop hcert hcov hlead
  letI : LeanDag.Hydrozoan.Slots Replica := LeanDag.Hydrozoan.ofCoreSlots S
  have hcard : LeanDag.Hydrozoan.q Replica ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Replica - (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica) ≤ T.card at h2
    unfold LeanDag.Hydrozoan.q; omega
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 2; omega) (S.leader k) hlead
  have hL : LeanDag.Hydrozoan.IsLeaderBlock U.val k L := ⟨hLmem, hLr, hLc⟩
  have hslow : LeanDag.Hydrozoan.SlowCommit U.val L (S.slotRound k) :=
    LeanDag.Hydrozoan.slowCommit_of_certifiesAt hcard
      (hpop (S.slotRound k + 2) (by omega) (by change S.slotRound k + 2 ≤ S.slotRound k + 2; omega))
      (hcert L ⟨hLmem, hLr, hLc⟩)
  have hin : LeanDag.Hydrozoan.SlowCommitInView U.val V L (S.slotRound k) :=
    LeanDag.Hydrozoan.slowCommitInView_of_coversUpto hslow hcov
  refine ⟨L, by omega, LeanDag.OptimalHydrozoan.DecidedOpt.directSlow hL hin, ?_⟩
  intro S' hround hlead'
  refine LeanDag.OptimalHydrozoan.DecidedOpt.directSlow
    (S := LeanDag.Hydrozoan.ofCoreSlots S') ⟨hL.1, ?_, ?_⟩ ?_
  · change (U.val.block L).round = S'.slotRound k
    rw [hround]; exact hL.2.1
  · change (U.val.block L).author = S'.leader k
    rw [hlead' k (by omega)]; exact hL.2.2
  · change LeanDag.Hydrozoan.SlowCommitInView U.val V L (S'.slotRound k)
    rw [hround]; exact hin

/-- **Optimal-Hydrozoan's precondition is the support's.** -/
theorem optSupport_live_of_optLive {S : LeanDag.Slots Replica}
    {U : (optimalRule (Replica := Replica) (BlockId := BlockId)).Universe}
    {V : LeanDag.Hydrozoan.View U.val} {T : Finset Replica} {lo K : ℕ}
    (h : optLive S (U := U) V T lo K) :
    Support.live (R := optimalRule (Replica := Replica) (BlockId := BlockId)) optSupport
      (LeanDag.Hydrozoan.hzReliability Replica) S (U := U) V T lo K := by
  obtain ⟨hT, hcard, R₀, N, hs, hR, hpop, hcov, hN⟩ := h
  have hq : (LeanDag.Hydrozoan.hzReliability Replica).IsQuorum T := ⟨hT, by
    change Fintype.card Replica -
      (LeanDag.Hydrozoan.Faults.f Replica + LeanDag.Hydrozoan.Faults.c Replica) ≤ T.card
    unfold LeanDag.Hydrozoan.q at hcard; omega⟩
  have hpop' : ∀ n, R₀ ≤ n → n ≤ N →
      Properties.PopulatedOn (optimalRule (Replica := Replica) (BlockId := BlockId)) U T n := by
    intro n h1 h2 v hv
    obtain ⟨b, hb, hbr, hba⟩ := hpop n h1 h2 v hv
    exact ⟨b, hb, hba, hbr⟩
  refine ⟨hq, N, hcov, hN, ?_⟩
  intro k hlo hK hlead
  have hRk : R₀ ≤ S.slotRound k := le_trans hR (S.mono hlo)
  have hNk : S.slotRound k + 2 ≤ N := hN k hK
  refine ⟨fun n h1 h2 => hpop' n (by omega) (by change n ≤ S.slotRound k + 2 at h2; omega), ?_⟩
  rintro L ⟨hLmem, hLr, hLc⟩ v hv c hc hcc hcr
  exact optSupport_ofCoverage U T hq (S.slotRound k) L
    (fun n h1 h2 => hpop' n (by omega) (by change n ≤ S.slotRound k + 2 at h2; omega))
    (Timed.coversToward_of_synchronisedOn hs hRk) hLmem hLr (by rw [hLc]; exact hlead)
    c hc (by rw [hcc]; exact hv) hcr

/-- **A reliably-led slot commits**, now a corollary of the support. -/
theorem leaderCommits :
    LeaderCommits (optimalRule (Replica := Replica) (BlockId := BlockId))
      (fun S {U} V T lo K => optLive S (U := U) V T lo K) :=
  fun S _ V T lo K h =>
    Support.leaderCommits optSupport optSupport_commits S V T lo K (optSupport_live_of_optLive h)

/-! ## Optimal-Hydrozoan's fast path

`voteSupport` again — one round up, certifying is referencing — at the
optimised threshold `q_fast = n − pOpt`, under a fault model with at
most `pOpt` faults of either kind. -/

/-- **The fast path's fault model.** `pOpt` faults is a minority at every
committee but the degenerate corner `f = 0`, `c = 1`, `k` odd, where
`2·pOpt = n` exactly; the committee equation does not exclude it, so
strict minority is a hypothesis rather than a consequence. -/
def optFastReliability (Replica : Type) [Fintype Replica] [DecidableEq Replica]
    [O : LeanDag.OptimalHydrozoan.OptimalFaults Replica]
    (h : (O.byzantine ∪ O.crashed).card ≤ LeanDag.OptimalHydrozoan.pOpt Replica)
    (hmin : 2 * LeanDag.OptimalHydrozoan.pOpt Replica < Fintype.card Replica) :
    LeanDag.Reliability Replica where
  correct := (LeanDag.Hydrozoan.Correct : Finset Replica)
  slack := LeanDag.OptimalHydrozoan.pOpt Replica
  covers := by
    have hc : (LeanDag.Hydrozoan.Correct : Finset Replica)ᶜ = O.byzantine ∪ O.crashed := by
      simp [LeanDag.Hydrozoan.Correct]
    rw [hc]; exact h
  minority := hmin

/-- **Law 3 of `voteSupport`, for Optimal-Hydrozoan's fast path.** -/
theorem voteSupport_fast_commits
    (h : (O.byzantine ∪ O.crashed).card ≤ LeanDag.OptimalHydrozoan.pOpt Replica)
    (hmin : 2 * LeanDag.OptimalHydrozoan.pOpt Replica < Fintype.card Replica) :
    Support.Commits (R := optimalRule (Replica := Replica) (BlockId := BlockId))
      (voteSupport (optimalRule (Replica := Replica) (BlockId := BlockId)))
      (optFastReliability Replica h hmin) := by
  intro S U V T k hq hpop hcert hcov hlead
  letI : LeanDag.Hydrozoan.Slots Replica := LeanDag.Hydrozoan.ofCoreSlots S
  have hcard : LeanDag.OptimalHydrozoan.qFastOpt Replica ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Replica - LeanDag.OptimalHydrozoan.pOpt Replica ≤ T.card at h2
    exact h2
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + 1; omega) (S.leader k) hlead
  have hL : LeanDag.Hydrozoan.IsLeaderBlock U.val k L := ⟨hLmem, hLr, hLc⟩
  have hfast : LeanDag.OptimalHydrozoan.FastCommitOpt U.val L (S.slotRound k) := by
    have hsub : T ⊆ LeanDag.Hydrozoan.supporters U.val L (S.slotRound k + 1) := by
      intro v hv
      obtain ⟨b, hb, hba, hbr⟩ := hpop (S.slotRound k + 1) (by omega)
        (by change S.slotRound k + 1 ≤ S.slotRound k + 1; omega) v hv
      exact LeanDag.Hydrozoan.mem_supporters.mpr
        ⟨b, hb, hbr, hcert L ⟨hLmem, hLr, hLc⟩ v hv b hb hba hbr, hba⟩
    exact le_trans hcard (Finset.card_le_card hsub)
  have hin : LeanDag.OptimalHydrozoan.FastCommitOptInView U.val V L (S.slotRound k) := by
    have hsub : (LeanDag.Hydrozoan.blocksAt U.val (S.slotRound k + 1)).filter
        (fun b => LeanDag.Hydrozoan.IsVote U.val b L) ⊆ V.ids := by
      intro b hb
      obtain ⟨hbA, -⟩ := Finset.mem_filter.mp hb
      obtain ⟨hbU, hbr⟩ := LeanDag.Hydrozoan.mem_blocksAt.mp hbA
      exact hcov b hbU (le_of_eq hbr)
    unfold LeanDag.OptimalHydrozoan.FastCommitOptInView LeanDag.Hydrozoan.supportersInView
    rw [Finset.inter_eq_left.2 hsub]
    exact hfast
  refine ⟨L, by omega, LeanDag.OptimalHydrozoan.DecidedOpt.directFast hL hin, ?_⟩
  intro S' hround hlead'
  refine LeanDag.OptimalHydrozoan.DecidedOpt.directFast
    (S := LeanDag.Hydrozoan.ofCoreSlots S') ⟨hL.1, ?_, ?_⟩ ?_
  · change (U.val.block L).round = S'.slotRound k
    rw [hround]; exact hL.2.1
  · change (U.val.block L).author = S'.leader k
    rw [hlead' k (by omega)]; exact hL.2.2
  · change LeanDag.OptimalHydrozoan.FastCommitOptInView U.val V L (S'.slotRound k)
    rw [hround]; exact hin

open Classical in
/-- **The graded rule is total, at a bound.** Three rungs and three
cases: an anchor-linked certificate, an anchor-linked evidence quorum,
or neither, in which case the slot skips. Every clause reads slot `k`'s
own candidates and the anchor's history, and neither moves when the
leaders of other slots are reassigned — which is the second quantifier.

Shorter than Hydrozoan's by one clause: the evidence rung carries no
tie-break, two candidates being unable to clear it at once (decision
D3), so no least candidate has to be chosen. -/
theorem indirect :
    Indirect (optimalRule (Replica := Replica) (BlockId := BlockId))
      (fun sr i j => sr i + 3 ≤ sr j) := by
  classical
  intro S U V k j A helig hj hmid
  have hea : LeanDag.Hydrozoan.EligibleAsAnchor
      (S := LeanDag.Hydrozoan.ofCoreSlots S) Replica k j := by
    change S.slotRound k + 2 < S.slotRound j; omega
  have hmidE : ∀ i, k < i → i < j →
      LeanDag.Hydrozoan.EligibleAsAnchor (S := LeanDag.Hydrozoan.ofCoreSlots S) Replica k i →
      S.slotRound k + 3 ≤ S.slotRound i := by
    intro i _ _ h3
    change S.slotRound k + 2 < S.slotRound i at h3; omega
  have hkj : k < j :=
    LeanDag.Hydrozoan.lt_of_eligibleAsAnchor (S := LeanDag.Hydrozoan.ofCoreSlots S) hea
  by_cases hc : ∃ L, LeanDag.Hydrozoan.IsLeaderBlock
      (S := LeanDag.Hydrozoan.ofCoreSlots S) U.val k L ∧
      LeanDag.Hydrozoan.CertifiedIn U.val A L (S.slotRound k)
  · obtain ⟨L, hL, hcert⟩ := hc
    refine ⟨some L, fun S' hround hlead hj' hmid' => ?_⟩
    exact LeanDag.OptimalHydrozoan.DecidedOpt.indirectCert
      (S := LeanDag.Hydrozoan.ofCoreSlots S') hkj
      ((LeanDag.Hydrozoan.eligibleAsAnchor_sched hround).mpr hea) hj'
      (fun i h1 h2 h3 => hmid' i h1 h2
        (hmidE i h1 h2 ((LeanDag.Hydrozoan.eligibleAsAnchor_sched hround).mp h3)))
      (LeanDag.Hydrozoan.isLeaderBlock_sched
        (S₁ := LeanDag.Hydrozoan.ofCoreSlots S) (S₂ := LeanDag.Hydrozoan.ofCoreSlots S')
        (by change S.slotRound k = S'.slotRound k; rw [hround])
        (by change S.leader k = S'.leader k; rw [hlead]) hL)
      (by change LeanDag.Hydrozoan.CertifiedIn U.val A L (S'.slotRound k)
          rw [hround]; exact hcert)
  · push Not at hc
    by_cases hw : ∃ L, LeanDag.Hydrozoan.IsLeaderBlock
        (S := LeanDag.Hydrozoan.ofCoreSlots S) U.val k L ∧
        LeanDag.OptimalHydrozoan.EvidenceLinked
          (S := LeanDag.Hydrozoan.ofCoreSlots S) U.val A L k
    · obtain ⟨L₀, hL₀, hw₀⟩ := hw
      refine ⟨some L₀, fun S' hround hlead hj' hmid' => ?_⟩
      have hsk : S.slotRound k = S'.slotRound k := by rw [hround]
      have hlk : S.leader k = S'.leader k := by rw [hlead]
      have hls : ∀ L', LeanDag.Hydrozoan.IsLeaderBlock
          (S := LeanDag.Hydrozoan.ofCoreSlots S') U.val k L' →
          LeanDag.Hydrozoan.IsLeaderBlock
            (S := LeanDag.Hydrozoan.ofCoreSlots S) U.val k L' := fun L' hL' =>
        LeanDag.Hydrozoan.isLeaderBlock_sched
          (S₁ := LeanDag.Hydrozoan.ofCoreSlots S') (S₂ := LeanDag.Hydrozoan.ofCoreSlots S)
          (by change S'.slotRound k = S.slotRound k; rw [hround])
          (by change S'.leader k = S.leader k; rw [hlead]) hL'
      refine LeanDag.OptimalHydrozoan.DecidedOpt.indirectEvidence
        (S := LeanDag.Hydrozoan.ofCoreSlots S') hkj
        ((LeanDag.Hydrozoan.eligibleAsAnchor_sched hround).mpr hea) hj'
        (fun i h1 h2 h3 => hmid' i h1 h2
          (hmidE i h1 h2 ((LeanDag.Hydrozoan.eligibleAsAnchor_sched hround).mp h3))) ?_
        (LeanDag.Hydrozoan.isLeaderBlock_sched
          (S₁ := LeanDag.Hydrozoan.ofCoreSlots S) (S₂ := LeanDag.Hydrozoan.ofCoreSlots S')
          (by exact hsk) (by exact hlk) hL₀) ?_
      · intro L' hL' hc'
        refine hc L' (hls L' hL') ?_
        change LeanDag.Hydrozoan.CertifiedIn U.val A L' (S'.slotRound k) at hc'
        rw [← hsk] at hc'; exact hc'
      · exact (LeanDag.OptimalHydrozoan.evidenceLinked_sched (U := U.val)
          (by exact hsk) (by exact hlk)).mp hw₀
    · push Not at hw
      refine ⟨none, fun S' hround hlead hj' hmid' => ?_⟩
      have hsk : S.slotRound k = S'.slotRound k := by rw [hround]
      have hlk : S.leader k = S'.leader k := by rw [hlead]
      have hls : ∀ L', LeanDag.Hydrozoan.IsLeaderBlock
          (S := LeanDag.Hydrozoan.ofCoreSlots S') U.val k L' →
          LeanDag.Hydrozoan.IsLeaderBlock
            (S := LeanDag.Hydrozoan.ofCoreSlots S) U.val k L' := fun L' hL' =>
        LeanDag.Hydrozoan.isLeaderBlock_sched
          (S₁ := LeanDag.Hydrozoan.ofCoreSlots S') (S₂ := LeanDag.Hydrozoan.ofCoreSlots S)
          (by change S'.slotRound k = S.slotRound k; rw [hround])
          (by change S'.leader k = S.leader k; rw [hlead]) hL'
      refine LeanDag.OptimalHydrozoan.DecidedOpt.indirectSkip
        (S := LeanDag.Hydrozoan.ofCoreSlots S') hkj
        ((LeanDag.Hydrozoan.eligibleAsAnchor_sched hround).mpr hea) hj'
        (fun i h1 h2 h3 => hmid' i h1 h2
          (hmidE i h1 h2 ((LeanDag.Hydrozoan.eligibleAsAnchor_sched hround).mp h3))) ?_ ?_
      · intro L' hL' hc'
        refine hc L' (hls L' hL') ?_
        change LeanDag.Hydrozoan.CertifiedIn U.val A L' (S'.slotRound k) at hc'
        rw [← hsk] at hc'; exact hc'
      · intro L' hL' he'
        refine hw L' (hls L' hL') ?_
        exact (LeanDag.OptimalHydrozoan.evidenceLinked_sched (U := U.val)
          (by exact hsk.symm) (by exact hlk.symm)).mp he'

/-! ## The headlines -/

theorem safety [LinearOrder BlockId] :
    Properties.Safe (optimalRule (Replica := Replica) (BlockId := BlockId)) :=
  Properties.safety banded agree commitsCandidate

theorem progress : Properties.Support.Progresses
    (optSupport (Replica := Replica) (BlockId := BlockId)) (LeanDag.Hydrozoan.hzReliability Replica) :=
  Properties.Support.progress optSupport_commits

end OptimalHydrozoanProperties

end LeanDag
