import LeanDag.OptimalHydrozoan.Carrier
import LeanDag.Integration.HydrozoanMechanisms

/-!
# Garbage collection and crash recovery for Optimal-Hydrozoan

Optimal-Hydrozoan's universes are Hydrozoan's with leader exclusion.
Its cut is `chopHZ` and its fill is `copyFillHZ`, each with the one
invariant carried: exclusion survives the cut because a block two rounds
above the horizon keeps its parents and its parents keep theirs, and
survives the copy fill because a filled block's parents are the
donor's and old blocks vote only for old blocks.

The fill cell is the one the skip-fill refutation had put out of
scope. That was a fact about the core's `skipFill`, whose self
reference grafts the anchor's parents onto the donor's; the copy fill
adds no edge, and the objection does not apply.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Properties.Arcs
open LeanDag.Barnacle.OptimalHydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable {S : Slots Replica} {G d : ℕ}

section HZ

variable [F : LeanDag.Hydrozoan.Faults Replica]
variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}

/-- **Leader exclusion survives the cut.** A block bound by exclusion
sits two rounds above the horizon, so it keeps its parents, its parents
keep theirs and their authors, and its candidates are old blocks at a
rebased round. -/
theorem leaderExcludedAll_chopHZ (hU : LeaderExcludedAll U) :
    LeaderExcludedAll (chopHZ U G) := by
  intro b hb v h2 hwit j hj
  rw [mem_chopHZ_ids] at hb
  have h2' : 2 ≤ (chopBlkHZ U.block G b).round := h2
  rw [chopBlkHZ_round] at h2'
  have hjb : j ∈ (chopBlkHZ U.block G b).parents := hj
  rw [chopBlkHZ_parents_of_lt (by omega)] at hjb
  have hjU := U.complete b hb.1 j hjb
  show (chopBlkHZ U.block G j).author ≠ v
  rw [chopBlkHZ_author]
  obtain ⟨L₁, L₂, hL₁, hL₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩ := hwit
  have hpar : ∀ j', j' ∈ ((chopHZ U G).block b).parents → j' ∈ (U.block b).parents := by
    intro j' hj'
    have := hj'
    rw [chopHZ_block, chopBlkHZ_parents_of_lt (by omega)] at this
    exact this
  have hcand : ∀ L j', j' ∈ (U.block b).parents →
      LeanDag.Hydrozoan.IsVote (chopHZ U G) j' L →
      IsCandidateAt (chopHZ U G) ((chopBlkHZ U.block G b).round - 2) v L →
      IsCandidateAt U ((U.block b).round - 2) v L ∧ LeanDag.Hydrozoan.IsVote U j' L := by
    intro L j' hj' hv hc
    have hj'U := U.complete b hb.1 j' hj'
    have hj'r := (U.valid b hb.1).predecessor j' hj'
    unfold LeanDag.Hydrozoan.IsVote at hv ⊢
    rw [chopHZ_block, chopBlkHZ_parents_of_lt (by omega)] at hv
    obtain ⟨hLm, hLr, hLa⟩ := hc
    rw [mem_chopHZ_ids] at hLm
    rw [chopHZ_block, chopBlkHZ_round] at hLr
    rw [chopHZ_block, chopBlkHZ_author] at hLa
    rw [chopBlkHZ_round] at hLr
    exact ⟨⟨hLm.1, by omega, hLa⟩, hv⟩
  obtain ⟨hc₁, hv₁'⟩ := hcand L₁ j₁ (hpar j₁ hj₁) hv₁ hL₁
  obtain ⟨hc₂, hv₂'⟩ := hcand L₂ j₂ (hpar j₂ hj₂) hv₂ hL₂
  exact hU b hb.1 v (by omega) ⟨L₁, L₂, hc₁, hc₂, hne, ⟨j₁, hpar j₁ hj₁, hv₁'⟩,
    ⟨j₂, hpar j₂ hj₂, hv₂'⟩⟩ j hjb

variable {sk : SkipData U.ids (hzBlk U)}

/-- A candidate voted for by an old block is old, and a candidate in the
old universe. -/
theorem isCandidateAt_of_old {r : ℕ} {v : Replica} {j L : BlockId} (hj : j ∈ U.ids)
    (hv : LeanDag.Hydrozoan.IsVote (copyFillHZ U sk) j L)
    (hc : IsCandidateAt (copyFillHZ U sk) r v L) : IsCandidateAt U r v L := by
  unfold LeanDag.Hydrozoan.IsVote at hv
  rw [copyFillHZ_block_old hj] at hv
  have hLU := U.complete j hj L hv
  obtain ⟨-, hLr, hLa⟩ := hc
  rw [copyFillHZ_block_old hLU] at hLr hLa
  exact ⟨hLU, hLr, hLa⟩

/-- **Leader exclusion survives the copy fill.** A filled block's parents
are the donor's; old blocks vote only for old blocks; so whatever a
block of the fill witnesses, a block of the old universe with the same
parents witnessed, and its parents were already excluded. -/
theorem leaderExcludedAll_copyFillHZ (hU : LeaderExcludedAll U) :
    LeaderExcludedAll (copyFillHZ U sk) := by
  intro b hb v h2 hwit j hj
  obtain ⟨L₁, L₂, hL₁, hL₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩ := hwit
  rcases Finset.mem_union.mp hb with ho | hf
  · -- an old block: parents, round and witnesses are the old universe's
    rw [copyFillHZ_block_old ho] at h2 hj hj₁ hj₂
    have hj₁U := U.complete b ho j₁ hj₁
    have hj₂U := U.complete b ho j₂ hj₂
    have hjU := U.complete b ho j hj
    rw [copyFillHZ_block_old hjU]
    refine hU b ho v h2 ⟨L₁, L₂, isCandidateAt_of_old hj₁U hv₁ ?_,
      isCandidateAt_of_old hj₂U hv₂ ?_, hne, ⟨j₁, hj₁, ?_⟩, ⟨j₂, hj₂, ?_⟩⟩ j hj
    · rw [copyFillHZ_block_old ho] at hL₁; exact hL₁
    · rw [copyFillHZ_block_old ho] at hL₂; exact hL₂
    · unfold LeanDag.Hydrozoan.IsVote at hv₁ ⊢
      rw [copyFillHZ_block_old hj₁U] at hv₁; exact hv₁
    · unfold LeanDag.Hydrozoan.IsVote at hv₂ ⊢
      rw [copyFillHZ_block_old hj₂U] at hv₂; exact hv₂
  · -- a filled block: everything is the donor's
    obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
    have hR0 : sk.r0 = (hzBlk U sk.B1).round := rfl
    have hB1 := hzBlk_round U sk.B1
    have hlm := sk.hline_mem k (by omega) hk2
    have hlr : (U.block (sk.line k)).round = k := sk.hline_round k (by omega) hk2
    rw [copyFillHZ_block_fresh] at h2 hj hj₁ hj₂ hL₁ hL₂
    simp only at h2 hj hj₁ hj₂ hL₁ hL₂
    have hj₁U := U.complete _ hlm j₁ hj₁
    have hj₂U := U.complete _ hlm j₂ hj₂
    have hjU := U.complete _ hlm j hj
    rw [copyFillHZ_block_old hjU]
    have h2' : 2 ≤ (U.block (sk.line k)).round := by omega
    have hr : k - 2 = (U.block (sk.line k)).round - 2 := by omega
    rw [hr] at hL₁ hL₂
    exact hU _ hlm v h2' ⟨L₁, L₂, isCandidateAt_of_old hj₁U hv₁ hL₁,
      isCandidateAt_of_old hj₂U hv₂ hL₂, hne,
      ⟨j₁, hj₁, by unfold LeanDag.Hydrozoan.IsVote at hv₁ ⊢
                   rw [copyFillHZ_block_old hj₁U] at hv₁; exact hv₁⟩,
      ⟨j₂, hj₂, by unfold LeanDag.Hydrozoan.IsVote at hv₂ ⊢
                   rw [copyFillHZ_block_old hj₂U] at hv₂; exact hv₂⟩⟩ j hj

end HZ

section Opt

variable [O : LeanDag.OptimalHydrozoan.OptimalFaults Replica]
variable {W : (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
  (BlockId := BlockId)).Universe}

/-! ### The cut -/

/-- **The cut, at Optimal-Hydrozoan's carrier.** -/
def chopOpt (W : (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
    (BlockId := BlockId)).Universe) (G : ℕ) :
    (OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := BlockId)).Universe :=
  ⟨chopHZ W.val G, leaderExcludedAll_chopHZ W.property⟩

/-- **The cut is a truncation of Optimal-Hydrozoan's carrier** —
Hydrozoan's witness, projected. -/
theorem truncates_chop_opt (hd : G ≤ S.slotRound d) :
    Truncates (OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := BlockId))
      W (chopOpt W G) S (S.chop G d hd) G d :=
  let h := truncates_chop_hz (U := W.val) hd
  { mem := h.mem, round := h.round, creator := h.creator, refs := h.refs,
    slotRound := h.slotRound, leader := h.leader, base := h.base }

theorem viewAgreeAbove_chop_opt {V : LeanDag.Hydrozoan.View W.val} :
    ViewAgreeAbove (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
      (BlockId := BlockId)) (U := W) (U' := chopOpt W G) V (chopViewHZ V G) G :=
  fun b hb hr => viewAgreeAbove_chop_hz (U := W.val) b hb hr

/-- **Verdict transport across the cut, for Optimal-Hydrozoan.** -/
theorem decided_chop_iff_opt (hd : G ≤ S.slotRound d) {V : LeanDag.Hydrozoan.View W.val}
    {k : ℕ} {v : Option BlockId} :
    (OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := BlockId)).Decided
      S V (d + k) v ↔
      (OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := BlockId)).Decided
        (S.chop G d hd) (U := chopOpt W G) (chopViewHZ V G) k v :=
  LocalTruncate.of_banded OptimalHydrozoanProperties.banded
    S (S.chop G d hd) W (chopOpt W G) G d (truncates_chop_opt hd) V (chopViewHZ V G)
    viewAgreeAbove_chop_opt k v

/-- **And cross-cut agreement.** -/
theorem decided_agree_chop_opt (hd : G ≤ S.slotRound d)
    {X : LeanDag.Hydrozoan.View (chopOpt W G).val} {V : LeanDag.Hydrozoan.View W.val}
    {k : ℕ} {w v : Option BlockId}
    (hW : (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
      (BlockId := BlockId)).Decided (S.chop G d hd) (U := chopOpt W G) X k w)
    (hV : (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
      (BlockId := BlockId)).Decided S V (d + k) v) : w = v :=
  decided_agree_truncate OptimalHydrozoanProperties.agree
    (LocalTruncate.of_banded OptimalHydrozoanProperties.banded)
    (truncates_chop_opt hd) viewAgreeAbove_chop_opt hW hV

/-! ### The fill -/


/-- **The fill, at Optimal-Hydrozoan's carrier**: the copy fill with
leader exclusion carried. -/
def copyFillOpt (W : (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
    (BlockId := BlockId)).Universe) (sk : SkipData W.val.ids (hzBlk W.val)) :
    (OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := BlockId)).Universe :=
  ⟨copyFillHZ W.val sk, leaderExcludedAll_copyFillHZ W.property⟩

variable {sk : SkipData W.val.ids (hzBlk W.val)}

/-- **The fill is an extension of Optimal-Hydrozoan's carrier.** -/
theorem extends_copyFill_opt :
    Extends (OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := BlockId))
      W (copyFillOpt W sk) where
  subset := fun _ h => Finset.mem_union_left _ h
  block := fun b hb => by
    show LeanDag.Hydrozoan.adaptBlock ((copyFillHZ W.val sk).block b) =
      LeanDag.Hydrozoan.adaptBlock (W.val.block b)
    rw [copyFillHZ_block_old hb]

/-- **What the fill sustains**: from the top of its gap. -/
theorem sustains_copyFill_opt :
    Sustains (OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := BlockId))
      W (copyFillOpt W sk) 0 (sk.r + 1) where
  mem := fun b => by
    show (b ∈ W.val.ids ∧ sk.r + 1 ≤ (W.val.block b).round) ↔
      (b ∈ (copyFillHZ W.val sk).ids ∧ sk.r + 1 ≤ ((copyFillHZ W.val sk).block b).round + 0)
    constructor
    · rintro ⟨hb, hr⟩
      exact ⟨Finset.mem_union_left _ hb, by rw [copyFillHZ_block_old hb]; omega⟩
    · rintro ⟨hb, hr⟩
      have hbU : b ∈ W.val.ids := by
        rcases Finset.mem_union.mp hb with ho | hfr
        · exact ho
        · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hfr
          rw [copyFillHZ_block_fresh] at hr
          simp only at hr
          omega
      exact ⟨hbU, by rw [copyFillHZ_block_old hbU] at hr; omega⟩
  round := fun b hb _ => by
    show ((copyFillHZ W.val sk).block b).round + 0 = (W.val.block b).round
    rw [copyFillHZ_block_old hb]; omega
  creator := fun b hb _ => by
    show ((copyFillHZ W.val sk).block b).author = (W.val.block b).author
    rw [copyFillHZ_block_old hb]
  refs := fun b hb _ => by
    show ((copyFillHZ W.val sk).block b).parents = (W.val.block b).parents
    rw [copyFillHZ_block_old hb]

/-- **Verdicts survive the recovery, for Optimal-Hydrozoan** — the cell
the skip-fill refutation had put out of scope, closed by the fill that
adds no edge. -/
theorem decided_copyFill_opt (S : Slots Replica) {V : LeanDag.Hydrozoan.View W.val}
    {V' : LeanDag.Hydrozoan.View (copyFillOpt W sk).val} (hsub : V.ids ⊆ V'.ids)
    {k : ℕ} {u : Option BlockId}
    (h : (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
      (BlockId := BlockId)).Decided S V k u) :
    (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
      (BlockId := BlockId)).Decided S V' k u :=
  Persist.of_banded OptimalHydrozoanProperties.banded S W _ extends_copyFill_opt V V' hsub k u h

/-- **And agreement across it.** -/
theorem decided_agree_copyFill_opt (S : Slots Replica) {V : LeanDag.Hydrozoan.View W.val}
    {V' V'' : LeanDag.Hydrozoan.View (copyFillOpt W sk).val} (hsub : V.ids ⊆ V'.ids)
    {k : ℕ} {u u' : Option BlockId}
    (h : (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
      (BlockId := BlockId)).Decided S V k u)
    (h' : (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
      (BlockId := BlockId)).Decided S V'' k u') : u = u' :=
  decided_agree_extends OptimalHydrozoanProperties.agree
    (Persist.of_banded OptimalHydrozoanProperties.banded) extends_copyFill_opt (V' := V')
    hsub h h'

end Opt

end Integration

end LeanDag
