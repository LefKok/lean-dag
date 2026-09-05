import LeanDag.Integration.Hydrozoan.OptimalTransport
import LeanDag.OptimalHydrozoan.Carrier
import LeanDag.Integration.Hydrozoan.ViaProperties

/-!
# HI7 for `DecidedOpt` — the rules Optimal-Hydrozoan reads, across the cut

P7's second half. `ChopDecided.lean` carries Hydrozoan's rules through a
truncation; this file carries the three that differ, and
`Properties.LocalTruncate` carries the verdicts.

Optimal-Hydrozoan applies every rule predicate to `U.toBlockUniverse`,
so the shared rules — candidacy, anchor eligibility, the slow path, and
rung 1's `CertifiedIn` — are transported by the lemmas already in
`ChopDecided.lean`, with nothing to add. What is new is the fast path's
threshold, the skip's no-evidence half, and rung 2:

* `FastCommitOptInView` counts the same supporters at a different
  threshold, so `supportersInView_chopHZ` gives it;
* `SkippedLeaderOptInView` adds `NoEvidenceQuorumInView` to
  Hydrozoan's blame count, and that rests on `IsNoFastEvidence`;
* `EvidenceLinked` counts anchor-linked decision-round blocks that are
  fast evidence, so it rests on `IsFastEvidence` and `Reaches`.

Both of the last two bottom out in `IsFastEvidence`, which reads the
universe through `WitnessesEquivocation`, `votesFor` and candidacy —
each of which the cut preserves above the horizon.

**The round guard is `G + 1 < round`, not `G < round`.** A vote is read
from a *parent* of the block in question, and the cut empties the
references of the layer it retains at the bottom; so a block one round
above the horizon has its own references intact but reads nothing from
them. Every use site supplies the stronger guard, decision-round blocks
sitting two rounds above the propose round.

`OptimalFaults` is the only fault instance in scope. It extends
`Faults`, and declaring both would leave which one a `BlockUniverse` is
indexed by to the elaborator — the diamond
`Barnacle/Helpers/OptimalHydrozoan.lean` documents.
-/

namespace LeanDag

namespace Integration

namespace Hydrozoan

open LeanDag.OptimalHydrozoan LeanDag.Barnacle.OptimalHydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId]
variable [O : LeanDag.OptimalHydrozoan.OptimalFaults Replica]
variable [Fact (HybridCommittee Replica)]
variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
variable {hsp : SelfParenting U} {G : ℕ}
variable [S : LeanDag.Hydrozoan.Slots Replica] {d : ℕ}

/-! ## Witnessing an equivocation

The same shape as `Barnacle.OptimalHydrozoan.WitnessesAt`, with the
slot's candidacy in place of a `(round, author)` pair. -/

/-- Witnessing is preserved, at the re-indexed slot. The guard is two
rounds above the horizon because a vote is read from a parent. -/
theorem witnessesEquivocation_chopHZ (hd : G ≤ S.slotRound d) {b : BlockId}
    (hbm : b ∈ U.ids) (hb : G + 1 < (U.block b).round) (k : ℕ) :
    WitnessesEquivocation (S := slotsChopHZ hd) (chopHZ U hsp G) k b
      ↔ WitnessesEquivocation U (d + k) b := by
  have hpar : ∀ j ∈ (U.block b).parents, G < (U.block j).round := by
    intro j hj
    have := (U.valid b hbm).predecessor j hj
    omega
  unfold WitnessesEquivocation
  rw [chopHZ_parents_of_lt (U := U) (hsp := hsp) (by omega)]
  constructor
  · rintro ⟨L₁, L₂, h1, h2, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩
    exact ⟨L₁, L₂, (isLeaderBlockHZ_chop hd).mp h1, (isLeaderBlockHZ_chop hd).mp h2, hne,
      ⟨j₁, hj₁, (isVote_chopHZ (hpar j₁ hj₁)).mp hv₁⟩,
      ⟨j₂, hj₂, (isVote_chopHZ (hpar j₂ hj₂)).mp hv₂⟩⟩
  · rintro ⟨L₁, L₂, h1, h2, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩
    exact ⟨L₁, L₂, (isLeaderBlockHZ_chop hd).mpr h1, (isLeaderBlockHZ_chop hd).mpr h2, hne,
      ⟨j₁, hj₁, (isVote_chopHZ (hpar j₁ hj₁)).mpr hv₁⟩,
      ⟨j₂, hj₂, (isVote_chopHZ (hpar j₂ hj₂)).mpr hv₂⟩⟩

/-! ## Fast evidence -/

omit S in
/-- The vote count a block casts is unchanged above the cut. -/
theorem votesFor_chopHZ {C L : BlockId} (hC : C ∈ U.ids)
    (h : G + 1 < (U.block C).round) :
    votesFor (chopHZ U hsp G) C L = votesFor U C L := by
  unfold votesFor
  rw [authorsOf_chopHZ, voteBlocks_chopHZ hC h]

/-- **Fast evidence is preserved.** Both branches of the definition read
only the witnessing test, the vote count, and the slot's candidates. -/
theorem isFastEvidence_chopHZ (hd : G ≤ S.slotRound d) {C L : BlockId}
    (hC : C ∈ U.ids) (h : G + 1 < (U.block C).round) (k : ℕ) :
    IsFastEvidence (S := slotsChopHZ hd) (chopHZ U hsp G) k C L
      ↔ IsFastEvidence U (d + k) C L := by
  simp only [IsFastEvidence, witnessesEquivocation_chopHZ hd hC h k,
    votesFor_chopHZ hC h, isLeaderBlockHZ_chop hd]

/-- And so is being evidence for nothing. -/
theorem isNoFastEvidence_chopHZ (hd : G ≤ S.slotRound d) {C : BlockId}
    (hC : C ∈ U.ids) (h : G + 1 < (U.block C).round) (k : ℕ) :
    IsNoFastEvidence (S := slotsChopHZ hd) (chopHZ U hsp G) k C
      ↔ IsNoFastEvidence U (d + k) C := by
  simp only [IsNoFastEvidence, isLeaderBlockHZ_chop hd, isFastEvidence_chopHZ hd hC h]

/-! ## The decision round, and what sits at it -/

omit [Fintype Replica] [DecidableEq Replica] O [Fact (HybridCommittee Replica)] in
/-- The decision round re-indexes by the horizon, like every other
round the rules name. -/
theorem decisionRound_chopHZ (hd : G ≤ S.slotRound d) (k : ℕ) :
    G + LeanDag.Hydrozoan.decisionRound Replica (S := slotsChopHZ hd) k
      = LeanDag.Hydrozoan.decisionRound Replica (d + k) := by
  have := horizon_le_slotRoundHZ (S := S) hd k
  unfold LeanDag.Hydrozoan.decisionRound
  simp only [slotsChopHZ_slotRound]
  omega

/-- A decision-round block of the truncation is a decision-round block
of the original, and sits far enough above the cut to read its votes. -/
theorem blocksAt_decision_chopHZ (hd : G ≤ S.slotRound d) (k : ℕ) :
    LeanDag.Hydrozoan.blocksAt (chopHZ U hsp G)
        (LeanDag.Hydrozoan.decisionRound Replica (S := slotsChopHZ hd) k)
      = LeanDag.Hydrozoan.blocksAt U (LeanDag.Hydrozoan.decisionRound Replica (d + k)) := by
  rw [blocksAt_chopHZ, decisionRound_chopHZ hd k]

omit [DecidableEq BlockId] [Fact (HybridCommittee Replica)] in
/-- What membership at the decision round supplies: presence, and the
round guard every lemma above needs. -/
theorem decision_block_guards (hd : G ≤ S.slotRound d) {k : ℕ} {b : BlockId}
    (hb : b ∈ LeanDag.Hydrozoan.blocksAt U
      (LeanDag.Hydrozoan.decisionRound Replica (d + k))) :
    b ∈ U.ids ∧ G + 1 < (U.block b).round := by
  have hG := horizon_le_slotRoundHZ (S := S) hd k
  simp only [LeanDag.Hydrozoan.blocksAt, Finset.mem_filter,
    LeanDag.Hydrozoan.decisionRound] at hb
  exact ⟨hb.1, by omega⟩

/-! ## The three rules that differ -/

variable {V : LeanDag.Hydrozoan.View U}

/-- **Rung 2 is preserved.** The witness set is the same set of blocks:
each sits at the decision round, is fast evidence, and lies in the
anchor's history, and the cut moves none of the three. -/
theorem evidenceLinked_chopHZ (hd : G ≤ S.slotRound d) {A L : BlockId}
    (hA : A ∈ U.ids) (k : ℕ) :
    EvidenceLinked (S := slotsChopHZ hd) (chopHZ U hsp G) A L k
      ↔ EvidenceLinked U A L (d + k) := by
  constructor
  · rintro ⟨s, hs, hcard⟩
    refine ⟨s, fun b hb => ?_, by rwa [authorsOf_chopHZ] at hcard⟩
    obtain ⟨hbd, hfe, hre⟩ := hs b hb
    rw [blocksAt_decision_chopHZ hd] at hbd
    obtain ⟨hbm, hbg⟩ := decision_block_guards (S := S) hd hbd
    exact ⟨hbd, (isFastEvidence_chopHZ hd hbm hbg k).mp hfe, reaches_of_reaches_chopHZ hre⟩
  · rintro ⟨s, hs, hcard⟩
    refine ⟨s, fun b hb => ?_, by rw [authorsOf_chopHZ]; exact hcard⟩
    obtain ⟨hbd, hfe, hre⟩ := hs b hb
    obtain ⟨hbm, hbg⟩ := decision_block_guards (S := S) hd hbd
    exact ⟨by rw [blocksAt_decision_chopHZ hd]; exact hbd,
      (isFastEvidence_chopHZ hd hbm hbg k).mpr hfe,
      (reaches_chopHZ hA (by omega)).mpr hre⟩

/-- **The skip's no-evidence half is preserved**, by the same witness
set, with the view's membership carried by `mem_viewChopHZ`. -/
theorem noEvidenceQuorumInView_chopHZ (hd : G ≤ S.slotRound d) (k : ℕ) :
    NoEvidenceQuorumInView (S := slotsChopHZ hd) (chopHZ U hsp G)
        (View.chopHZ V hsp G) k
      ↔ NoEvidenceQuorumInView U V (d + k) := by
  constructor
  · rintro ⟨s, hs, hcard⟩
    refine ⟨s, fun b hb => ?_, by rwa [authorsOf_chopHZ] at hcard⟩
    obtain ⟨hbd, hbV, hne⟩ := hs b hb
    rw [blocksAt_decision_chopHZ hd] at hbd
    obtain ⟨hbm, hbg⟩ := decision_block_guards (S := S) hd hbd
    exact ⟨hbd, (mem_viewChopHZ (V := V) (by omega)).mp hbV,
      (isNoFastEvidence_chopHZ hd hbm hbg k).mp hne⟩
  · rintro ⟨s, hs, hcard⟩
    refine ⟨s, fun b hb => ?_, by rw [authorsOf_chopHZ]; exact hcard⟩
    obtain ⟨hbd, hbV, hne⟩ := hs b hb
    obtain ⟨hbm, hbg⟩ := decision_block_guards (S := S) hd hbd
    exact ⟨by rw [blocksAt_decision_chopHZ hd]; exact hbd,
      (mem_viewChopHZ (V := V) (by omega)).mpr hbV,
      (isNoFastEvidence_chopHZ hd hbm hbg k).mpr hne⟩

omit S in
/-- **The fast path is preserved.** It counts the same supporters as
Hydrozoan's at a lower threshold, so the transfer is the same one. -/
theorem fastCommitOptInView_chopHZ (L : BlockId) (r : ℕ) :
    FastCommitOptInView (chopHZ U hsp G) (View.chopHZ V hsp G) L r
      ↔ FastCommitOptInView U V L (G + r) := by
  unfold FastCommitOptInView
  have hr : G + (r + 1) = G + r + 1 := by omega
  rw [supportersInView_chopHZ (V := V) L (r + 1) (by omega), hr]

/-- **And the skip is**, being the blame count and the no-evidence
quorum together. -/
theorem skippedLeaderOptInView_chopHZ (hd : G ≤ S.slotRound d) (k : ℕ) :
    SkippedLeaderOptInView (S := slotsChopHZ hd) (chopHZ U hsp G)
        (View.chopHZ V hsp G) k
      ↔ SkippedLeaderOptInView U V (d + k) := by
  unfold SkippedLeaderOptInView
  rw [blamesInView_chopHZ (V := V) hd k, noEvidenceQuorumInView_chopHZ hd k]

/-! ## HI7 for `DecidedOpt`

`optUniverseOf` rebuilds the Optimal universe on each side from the
schedule-free clause, at that side's own schedule — which is what §4.1's
resolution exists to allow, and what makes the two `OptUniverse`s
statable in one theorem at all.

**Two inductions over `DecidedOpt`'s six constructors stood here**, the
third and last hand-written pair in this arc. They are gone. What
survives above is the statement of what the cut preserves, rule by rule
and biconditionally, which is the content; the verdicts follow from
`Properties.LocalTruncate.of_banded` over the band
`OptimalHydrozoanProperties.banded` supplies, and that theorem knows
nothing about Optimal-Hydrozoan. -/

section Induction

variable {hle : LeaderExcludedAll U}

/-- The Optimal universe the truncation carries, at the truncation's
own schedule. -/
abbrev optChopHZ (hd : G ≤ S.slotRound d) (hle : LeaderExcludedAll U) :
    OptUniverse Replica BlockId (S := slotsChopHZ hd) :=
  LeanDag.Barnacle.OptimalHydrozoan.optUniverseOf (S := slotsChopHZ hd)
    (chopHZ U hsp G) (leaderExcludedAll_chopHZ hle)

/-- **Optimal's carrier reads Hydrozoan's sustaining.** The subtype's
projections are the underlying universe's, so a `Sustains` at one rule
is a `Sustains` at the other, field for field. -/
theorem sustains_opt [LinearOrder BlockId] {g g' : ℕ}
    {W W' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    {hW : LeaderExcludedAll W} {hW' : LeaderExcludedAll W'}
    (h : Properties.Sustains LeanDag.Hydrozoan.rule W W' g g') :
    Properties.Sustains
      (LeanDag.OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := BlockId))
      ⟨W, hW⟩ ⟨W', hW'⟩ g g' where
  mem := h.mem
  round := h.round
  creator := h.creator
  refs := h.refs

/-- **The cut is a truncation of Optimal's carrier.** The block half is
Hydrozoan's `sustains_chopHZ`, read through `sustains_opt`; the three
schedule clauses are `truncates_chopHZ`'s. -/
theorem truncates_chopOpt [LinearOrder BlockId] (hd : G ≤ S.slotRound d)
    (hle : LeaderExcludedAll U) :
    Properties.Truncates
      (LeanDag.OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := BlockId))
      ⟨U, hle⟩ ⟨chopHZ U hsp G, leaderExcludedAll_chopHZ hle⟩
      (LeanDag.Hydrozoan.toCoreSlots S)
      (LeanDag.Hydrozoan.toCoreSlots (slotsChopHZ hd)) G d :=
  { sustains_opt (hW := hle) (hW' := leaderExcludedAll_chopHZ hle)
      (sustains_chopHZ (hsp := hsp) (G := G)) with
    slotRound := (truncates_chopHZ (hsp := hsp) (U := U) hd).slotRound
    leader := (truncates_chopHZ (hsp := hsp) (U := U) hd).leader
    base := hd }

/-- **HI7 for `DecidedOpt`, from OH9.** A replica running
Optimal-Hydrozoan that has pruned below the horizon reaches exactly the
verdicts it would have reached with its whole history, at the re-indexed
slot.

Two inductions over `DecidedOpt`'s six constructors stood here and are
gone; what survives above is the *statement* of what the cut preserves,
rule by rule, which is the content. `LocalTruncate.of_banded` supplies
the rest and knows nothing about Optimal-Hydrozoan.

`LinearOrder BlockId` enters through the band and nowhere else:
`Banded` for this rule is proved by reading Optimal's band as
Hydrozoan's, and Hydrozoan's carrier carries a tie-break. Every
committee this arc instantiates has one. -/
theorem decidedOpt_chopHZ [LinearOrder BlockId] (hd : G ≤ S.slotRound d)
    {k : ℕ} {v : Option BlockId} :
    DecidedOpt (S := slotsChopHZ hd) (optChopHZ (hsp := hsp) hd hle)
        (View.chopHZ V hsp G) k v
      ↔ DecidedOpt (S := S) (LeanDag.Barnacle.OptimalHydrozoan.optUniverseOf U hle) V (d + k) v :=
  (Properties.LocalTruncate.of_banded LeanDag.OptimalHydrozoanProperties.banded
    (LeanDag.Hydrozoan.toCoreSlots S) (LeanDag.Hydrozoan.toCoreSlots (slotsChopHZ hd))
    ⟨U, hle⟩ ⟨chopHZ U hsp G, leaderExcludedAll_chopHZ hle⟩ G d
    (truncates_chopOpt (hsp := hsp) hd hle) V (View.chopHZ V hsp G)
    (fun b hb hbr => by
      change b ∈ V.ids ↔ b ∈ (View.chopHZ V hsp G).ids
      exact (mem_viewChopHZ (V := V) hbr).symm) k v).symm

end Induction

/-! ## What a pruned Optimal deployment gets

The reader-facing statement for this arc, and the counterpart to
`Deployment.lean`. It sits here rather than there because that file
carries `Faults` and this one carries `OptimalFaults`, and the two in
one scope would leave which one a `BlockUniverse` is indexed by to the
elaborator.

**There is no recovery field, and its absence is the finding.**
`Deployment` bundles a horizon *and* a one-message recovery, because
Hydrozoan survives both. Optimal-Hydrozoan survives the horizon alone:
the recovery breaks its validity rule, witnessed in
`LeanDagTest/Integration/HydrozoanOptimal.lean` and recorded as §5 of
the design record. A structure with a `recovery` field would promise
what no theorem here can supply. -/

section Deployed

/-- **One replica's situation, running Optimal-Hydrozoan**: the DAG the
network built, and a horizon below which it retains nothing. -/
structure PrunedOpt (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LeanDag.OptimalHydrozoan.OptimalFaults Replica]
    [Fact (HybridCommittee Replica)] [S : LeanDag.Hydrozoan.Slots Replica] where
  /-- The DAG as the network built it, before this replica pruned. -/
  network : LeanDag.Hydrozoan.BlockUniverse Replica BlockId
  /-- Every block carries its author's previous block. -/
  selfParents : SelfParenting network
  /-- And the DAG-building layer enforced leader exclusion, in the
  schedule-free form. -/
  excluded : LeaderExcludedAll network
  /-- The horizon below which it retains nothing. -/
  horizon : ℕ
  /-- The slot its numbering restarts at. -/
  base : ℕ
  /-- The horizon does not reach past that slot. -/
  retains : horizon ≤ S.slotRound base

namespace PrunedOpt

variable (D : PrunedOpt Replica BlockId)

/-- **What the replica holds**, as an Optimal universe at its own
schedule — which is what the schedule-free clause exists to allow. -/
abbrev held : OptUniverse Replica BlockId (S := slotsChopHZ D.retains) :=
  optChopHZ (hsp := D.selfParents) D.retains D.excluded

/-- **The slot numbering it uses**, rebased at the horizon: its slot `k`
is the network's slot `base + k`. -/
abbrev numbering : LeanDag.Hydrozoan.Slots Replica := slotsChopHZ D.retains

/-- **The replica reaches exactly the verdicts it would have reached
with its whole history**, at its own numbering. Pruning below the
horizon is invisible to the decision rule. -/
theorem decides [LinearOrder BlockId] {V : LeanDag.Hydrozoan.View D.network} {k : ℕ}
    {v : Option BlockId} :
    DecidedOpt (S := D.numbering) D.held (View.chopHZ V D.selfParents D.horizon) k v
      ↔ DecidedOpt (S := S)
          (LeanDag.Barnacle.OptimalHydrozoan.optUniverseOf D.network D.excluded) V
          (D.base + k) v :=
  decidedOpt_chopHZ (hle := D.excluded) D.retains

end PrunedOpt

end Deployed

end Hydrozoan

end Integration

end LeanDag
