import LeanDag.OptimalHydrozoan.SlotAgreement.Proof
import LeanDag.OptimalHydrozoan.Helpers.Banded
import LeanDag.Barnacle.Helpers.OptimalHydrozoan
import LeanDag.Hydrozoan.Helpers.Carrier
import LeanDag.Hydrozoan.Helpers.Commit
import LeanDag.OptimalHydrozoan.DirectLiveness.Proof
import LeanDag.Properties.Commit
import LeanDag.Properties.Live
import LeanDag.Properties.Support
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Optional.Quorate

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
  Decided := fun S U V k v =>
    letI := LeanDag.Hydrozoan.ofCoreSlots S
    LeanDag.OptimalHydrozoan.DecidedOpt
      (Barnacle.OptimalHydrozoan.optUniverseOf U.val U.property) V k v

/-- Optimal's universes are block DAGs — Hydrozoan's argument, the
underlying universe being Hydrozoan's. -/
theorem causal : Causal (optimalRule (Replica := Replica) (BlockId := BlockId)) :=
  fun U =>
    { complete := fun i hi j hj => U.val.complete i hi j hj
      refs_round := fun i hi j hj => (U.val.valid i hi).predecessor j hj }

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
theorem optSupport_ofCoverage [LinearOrder BlockId] :
    Support.OfCoverage (R := optimalRule (Replica := Replica) (BlockId := BlockId)) optSupport
      (LeanDag.Hydrozoan.hzReliability Replica) := by
  intro U T hq r L hpop hct hL hLr hLc c hc hcc hcr
  exact LeanDag.Hydrozoan.hzSupport_ofCoverage (U := U.val) T hq r L hpop hct hL hLr hLc
    c hc hcc hcr

/-- **Law 3**: the slow commit, in `DecidedOpt`. -/
theorem optSupport_commits [LinearOrder BlockId] :
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

/-- **Optimal-Hydrozoan's precondition is reachable**
(`Properties/Live.lean`). Optimal leaves the slow path alone, so the
reachability is Hydrozoan's, at the same reliable set and wavelength. -/
theorem liveReachable :
    LiveReachable (optimalRule (Replica := Replica) (BlockId := BlockId))
      (LeanDag.Hydrozoan.hzReliability Replica) 2
      (fun S {U} V T lo K => optLive S (U := U) V T lo K) := by
  intro U Rnd N hs hpop S V k hcov hRnd hN
  refine ⟨Finset.Subset.rfl, LeanDag.Hydrozoan.q_le_card_correct, Rnd, N, hs, hRnd,
    ?_, hcov, ?_⟩
  · intro r h1 h2 v hv
    obtain ⟨b, hb, hbc, hbr⟩ := hpop r h1 h2 v hv
    exact ⟨b, hb, hbr, hbc⟩
  · intro j hj
    have := S.mono (Nat.lt_succ_iff.mp hj)
    omega

/-- **A reliably-led slot commits**, at a bound one above the slot: the
slow commit reads that one leader, so a reassignment of the others
leaves it standing. -/
theorem leaderCommits :
    LeaderCommits (optimalRule (Replica := Replica) (BlockId := BlockId))
      (fun S {U} V T lo K => optLive S (U := U) V T lo K) := by
  intro S U V T lo K hlive k hlo hK hlead
  obtain ⟨hT, hcard, R₀, N, hs, hR, hpop, hcov, hN⟩ := hlive
  letI : LeanDag.Hydrozoan.Slots Replica := LeanDag.Hydrozoan.ofCoreSlots S
  have hRk : R₀ ≤ S.slotRound k :=
    le_trans hR ((LeanDag.Hydrozoan.ofCoreSlots S).mono hlo)
  have hNk : S.slotRound k + 2 ≤ N := hN k hK
  have hp0 : LeanDag.Hydrozoan.PopulatedOn U.val T (S.slotRound k) := hpop _ hRk (by omega)
  have hp1 : LeanDag.Hydrozoan.PopulatedOn U.val T (S.slotRound k + 1) :=
    hpop _ (by omega) (by omega)
  have hp2 : LeanDag.Hydrozoan.PopulatedOn U.val T (S.slotRound k + 2) :=
    hpop _ (by omega) (by omega)
  obtain ⟨L, hL, hslow, -⟩ :=
    (LeanDag.OptimalHydrozoan.DirectLiveness.holds Replica BlockId
      (Barnacle.OptimalHydrozoan.optUniverseOf U.val U.property)).1
      T R₀ k hT hcard hs hRk hp0 hp1 hp2 hlead V (hcov.mono hNk)
  have hin : LeanDag.Hydrozoan.SlowCommitInView U.val V L (S.slotRound k) :=
    LeanDag.Hydrozoan.slowCommitInView_of_coversUpto hslow (hcov.mono hNk)
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

end OptimalHydrozoanProperties

end LeanDag
