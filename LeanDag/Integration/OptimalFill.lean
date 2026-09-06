import LeanDag.OptimalHydrozoan.Carrier
import LeanDag.SafeSkip.Basic
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Properties.Arcs.Liveness

/-!
# Crash recovery for Optimal-Hydrozoan

The cell `scripts/audit-mechanisms.py` recorded as out of scope, with
the reason `not_leaderExcludedAll_Ufill`: the core's `skipFill` adds a
self reference, which grafts the anchor's parents onto the donor's at
the boundary round, and leader exclusion is a condition on what a
block's parents jointly witness. That is a fact about `skipFill`, not
about fills. `SkipData.copyBlock` adds no edge — the filled block's
parents *are* the donor's — and then leader exclusion for a filled block
is the donor's own, verbatim: its parents are old, old blocks vote only
for old blocks, so whatever the filled block witnesses the donor
witnessed too, and the donor's parents were already excluded.

The fill is built at Hydrozoan's universe directly (`copyFillHZ`), not
through the core, so no self-parent clause is in play and no transport
is needed; Optimal-Hydrozoan's carrier is that with the invariant
(`copyFillOpt`). The witnesses follow and the transports are the generic
theorems, as for every other rule.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Properties.Arcs
open LeanDag.Barnacle.OptimalHydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]

section HZ

variable [F : LeanDag.Hydrozoan.Faults Replica]

/-- A Hydrozoan universe's blocks, read as core blocks with no payload —
the shape a Safe Skip message is stated over. -/
def hzBlk (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) :
    BlockId → Block Replica BlockId Unit :=
  fun i => LeanDag.Hydrozoan.adaptBlock (U.block i)

theorem hzBlk_round (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (i : BlockId) :
    (hzBlk U i).round = (U.block i).round := rfl

/-- **The copy fill, at Hydrozoan's universe.** One block per gap round,
by the recovering replica, carrying the donor's parents at that round. -/
def copyFillHZ (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (sk : SkipData U.ids (hzBlk U)) : LeanDag.Hydrozoan.BlockUniverse Replica BlockId where
  ids := U.ids ∪ sk.freshIds
  block b := if b ∈ U.ids then U.block b
    else ⟨sk.idx b, sk.v1, (U.block (sk.line (sk.idx b))).parents⟩
  complete := by
    intro i hi j hj
    rcases Finset.mem_union.mp hi with ho | hf
    · rw [if_pos ho] at hj
      exact Finset.mem_union_left _ (U.complete i ho j hj)
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (hzBlk U sk.B1).round := rfl
      have hB1 := hzBlk_round U sk.B1
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hj
      exact Finset.mem_union_left _
        (U.complete _ (sk.hline_mem k (by omega) hk2) j hj)
  valid := by
    intro i hi
    rcases Finset.mem_union.mp hi with ho | hf
    · rw [if_pos ho]
      have hv := U.valid i ho
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        rw [if_pos (U.complete i ho j hj)]
        exact hv.predecessor j hj
      · intro a ha b hb hab
        rw [if_pos (U.complete i ho a ha), if_pos (U.complete i ho b hb)] at hab
        exact hv.distinct_authors a ha b hb hab
      · intro hr
        refine le_trans (hv.quorum hr) (Finset.card_le_card ?_)
        intro c hc
        unfold LeanDag.Hydrozoan.authors LeanDag.Hydrozoan.authorsOf at hc ⊢
        obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
        refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
        simp only
        rw [if_pos (U.complete i ho j hj)]
        exact hjc
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (hzBlk U sk.B1).round := rfl
      have hB1 := hzBlk_round U sk.B1
      rw [if_neg (sk.hfresh_new k), sk.hidx]
      have hlm := sk.hline_mem k (by omega) hk2
      have hlv := U.valid _ hlm
      have hlr : (U.block (sk.line k)).round = k := sk.hline_round k (by omega) hk2
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        simp only at hj ⊢
        rw [if_pos (U.complete _ hlm j hj)]
        have := hlv.predecessor j hj
        omega
      · intro a ha b hb hab
        simp only at ha hb
        rw [if_pos (U.complete _ hlm a ha), if_pos (U.complete _ hlm b hb)] at hab
        exact hlv.distinct_authors a ha b hb hab
      · intro _
        have hq := hlv.quorum (by omega)
        refine le_trans hq (Finset.card_le_card ?_)
        intro c hc
        unfold LeanDag.Hydrozoan.authors LeanDag.Hydrozoan.authorsOf at hc ⊢
        obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
        refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
        simp only
        rw [if_pos (U.complete _ hlm j hj)]
        exact hjc
  no_equivocation := by
    intro i hi j hj hib hcc hrr
    rcases Finset.mem_union.mp hi with ho | hf <;>
      rcases Finset.mem_union.mp hj with ho' | hf'
    · rw [if_pos ho] at hib hcc hrr
      rw [if_pos ho'] at hcc hrr
      exact U.no_equivocation i ho j ho' hib hcc hrr
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf'
      have hR0 : sk.r0 = (hzBlk U sk.B1).round := rfl
      have hB1 := hzBlk_round U sk.B1
      rw [if_pos ho] at hcc hrr
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hcc hrr
      have hi := hzBlk_round U i
      exact (sk.hgap i ho hcc (by simp only at hrr; omega) (by simp only at hrr; omega)).elim
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (hzBlk U sk.B1).round := rfl
      have hB1 := hzBlk_round U sk.B1
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hcc hrr
      rw [if_pos ho'] at hcc hrr
      have hj := hzBlk_round U j
      exact (sk.hgap j ho' hcc.symm (by simp only at hrr; omega)
        (by simp only at hrr; omega)).elim
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      obtain ⟨l, hl1, hl2, rfl⟩ := sk.mem_freshIds.mp hf'
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hrr
      rw [if_neg (sk.hfresh_new l), sk.hidx] at hrr
      simp only at hrr
      exact hrr ▸ rfl

variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {sk : SkipData U.ids (hzBlk U)}

@[simp] theorem copyFillHZ_block_old {b : BlockId} (hb : b ∈ U.ids) :
    (copyFillHZ U sk).block b = U.block b := if_pos hb

@[simp] theorem copyFillHZ_block_fresh {k : ℕ} :
    (copyFillHZ U sk).block (sk.fresh k) =
      ⟨k, sk.v1, (U.block (sk.line k)).parents⟩ := by
  simp only [copyFillHZ, if_neg (sk.hfresh_new k), sk.hidx]

/-- An old block's parents are old. -/
theorem copyFillHZ_parents_old {b : BlockId} (hb : b ∈ U.ids) :
    ∀ j ∈ ((copyFillHZ U sk).block b).parents, j ∈ U.ids := by
  rw [copyFillHZ_block_old hb]
  exact U.complete b hb

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

/-! ## At Optimal-Hydrozoan's carrier -/

section Opt

variable [O : LeanDag.OptimalHydrozoan.OptimalFaults Replica]
variable {W : (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
  (BlockId := BlockId)).Universe}

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
`not_leaderExcludedAll_Ufill` had put out of scope, closed by the fill
that adds no edge. -/
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
