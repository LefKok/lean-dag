import LeanDag.Properties.Arcs.GC
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.NemoProperties

/-!
# Garbage collection and crash recovery for Nemo

`scripts/audit-mechanisms.py` asked for both. Nemo shows `Banded` and
`Agree`, so the two transformer arcs' theorems already held of it, and
nobody had applied them.

**This is the expensive end of the range that `HybridMechanisms.lean`
names.** Hybrid's universe is the core's up to an invariant, so its cut
and its fill are the core's with one discharge each. Nemo keeps its own
universe record — a majority parent quorum rather than `n − f`, and
non-equivocation for *every* validator rather than the correct ones — so
neither construction is available to it, and it builds its own.

What it does not build is the *data*. The cut's block operator is
`chopBlk` and the fill's message is `SkipData`, both stated over a bare
block assignment with no fault model, so what Nemo supplies is exactly
the part that differs: the invariant discharges. Nemo's two are the
majority quorum, which the cut leaves untouched and the fill inherits
from the donor, and universal non-equivocation, which the crash
hypothesis `hgap` protects.

**The fill copies the donor's references and adds nothing.**
`SkipData.fillBlock` inserts a self reference, which the core's
`ValidWrt.self_parent` demands; Nemo has no such clause, so it takes
`SkipData.copyBlock` instead and its validity is the donor's verbatim.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Properties.Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {S : Slots Validator} {G d : ℕ}
variable {U : Nemo.Universe Validator BlockId Payload}

/-! ## The cut -/

/-- **The cut, at Nemo's universe.** The blocks at or above the horizon,
rounds rebased by `−G`, the round-`G` layer as the new geneses — the
core's construction on the core's block operator, with Nemo's two
invariants discharged in place of the core's four.

The majority quorum survives because a block above the cut keeps its
references and its authors; the base layer has none and owes nothing.
Non-equivocation survives because the cut neither adds a block nor
changes an author, and rebasing rounds by a constant is injective on
what is left. -/
def chopNemo (U : Nemo.Universe Validator BlockId Payload) (G : ℕ) :
    Nemo.Universe Validator BlockId Payload where
  ids := U.ids.filter fun i => G ≤ (U.block i).round
  block := chopBlk U.block G
  complete := by
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    rcases Nat.lt_or_ge G (U.block i).round with h | h
    · rw [chopBlk_refs_of_lt h] at hj
      have hjr := U.round_of_mem_refs hi.1 hj
      exact Finset.mem_filter.mpr ⟨U.complete i hi.1 j hj, by omega⟩
    · rw [chopBlk_refs_of_le h] at hj
      exact absurd hj (Finset.notMem_empty j)
  valid := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have hv := U.valid i hi.1
    rcases Nat.lt_or_ge G (U.block i).round with h | h
    · refine ⟨?_, ?_⟩
      · intro j hj
        rw [chopBlk_refs_of_lt h] at hj
        have hjr := hv.predecessor j hj
        rw [chopBlk_round, chopBlk_round]
        omega
      · intro _
        have hcr : creators (chopBlk U.block G) (chopBlk U.block G i) =
            creators U.block (U.block i) := by
          unfold creators
          rw [chopBlk_refs_of_lt h, creatorsOf_chopBlk]
        rw [hcr]
        exact hv.quorum (by omega)
    · refine ⟨?_, ?_⟩
      · intro j hj
        rw [chopBlk_refs_of_le h] at hj
        exact absurd hj (Finset.notMem_empty j)
      · intro hr
        rw [chopBlk_round] at hr
        omega
  no_equivocation := by
    intro i hi j hj hcreator hround
    rw [Finset.mem_filter] at hi hj
    rw [chopBlk_creator, chopBlk_creator] at hcreator
    rw [chopBlk_round, chopBlk_round] at hround
    exact U.no_equivocation i hi.1 j hj.1 hcreator (by omega)

@[simp] theorem mem_chopNemo_ids {i : BlockId} :
    i ∈ (chopNemo U G).ids ↔ i ∈ U.ids ∧ G ≤ (U.block i).round :=
  Finset.mem_filter

@[simp] theorem chopNemo_block : (chopNemo U G).block = chopBlk U.block G := rfl

/-- The truncated view: keep what clears the cut. Closure survives — a
retained block's references sit one round below it, hence at or above
the cut, except at the base layer, where they are gone. -/
def chopViewNemo (V : Nemo.View Validator BlockId Payload U) (G : ℕ) :
    Nemo.View Validator BlockId Payload (chopNemo U G) where
  ids := V.ids.filter fun i => G ≤ (U.block i).round
  subset_ids := by
    intro i hi
    rw [Finset.mem_filter] at hi
    exact mem_chopNemo_ids.mpr ⟨V.subset_ids hi.1, hi.2⟩
  complete := by
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    have hj' : j ∈ (chopBlk U.block G i).refs := hj
    rcases Nat.lt_or_ge G (U.block i).round with h | h
    · rw [chopBlk_refs_of_lt h] at hj'
      have := U.round_of_mem_refs (V.subset_ids hi.1) hj'
      exact Finset.mem_filter.mpr ⟨V.complete i hi.1 j hj', by omega⟩
    · rw [chopBlk_refs_of_le h] at hj'
      exact absurd hj' (Finset.notMem_empty j)

/-- **The cut is a truncation of Nemo's carrier.** -/
theorem truncates_chop_nemo (hd : G ≤ S.slotRound d) :
    Truncates (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) U (chopNemo U G) S (S.chop G d hd) G d where
  mem := fun b => by
    show (b ∈ U.ids ∧ G ≤ (U.block b).round) ↔
      (b ∈ (chopNemo U G).ids ∧ G ≤ ((chopNemo U G).block b).round + G)
    rw [mem_chopNemo_ids, chopNemo_block, chopBlk_round]
    constructor
    · rintro ⟨hb, hr⟩; exact ⟨⟨hb, hr⟩, by omega⟩
    · rintro ⟨⟨hb, hr⟩, -⟩; exact ⟨hb, hr⟩
  round := fun b _ hr => by
    have hr' : G ≤ (U.block b).round := hr
    show ((chopNemo U G).block b).round + G = (U.block b).round
    rw [chopNemo_block, chopBlk_round]; omega
  creator := fun b _ _ => by
    show ((chopNemo U G).block b).creator = (U.block b).creator
    rw [chopNemo_block, chopBlk_creator]
  refs := fun b _ hr => by
    have hr' : G < (U.block b).round := hr
    show ((chopNemo U G).block b).refs = (U.block b).refs
    rw [chopNemo_block]
    exact chopBlk_refs_of_lt hr'
  slotRound := fun k => by
    have := horizon_le_slotRound hd k
    show S.slotRound (d + k) - G + G = S.slotRound (d + k)
    omega
  leader := fun _ => rfl
  base := hd

/-- **The chopped view agrees with the original above the cut.** -/
theorem viewAgreeAbove_chop_nemo {V : Nemo.View Validator BlockId Payload U} :
    ViewAgreeAbove (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) V (chopViewNemo V G) G :=
  fun b _ hr => by
    show b ∈ V.ids ↔ b ∈ (chopViewNemo V G).ids
    show b ∈ V.ids ↔ b ∈ V.ids.filter fun i => G ≤ (U.block i).round
    rw [Finset.mem_filter]
    exact ⟨fun h => ⟨h, hr⟩, fun h => h.1⟩

/-- **Verdict transport across the cut, for Nemo.** -/
theorem decided_chop_iff_nemo (hd : G ≤ S.slotRound d)
    {V : Nemo.View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId} :
    Nemo.Decided (S := S) U V (d + k) v ↔
      Nemo.Decided (S := S.chop G d hd) (chopNemo U G) (chopViewNemo V G) k v :=
  LocalTruncate.of_banded NemoProperties.banded
    S (S.chop G d hd) U (chopNemo U G) G d (truncates_chop_nemo hd) V (chopViewNemo V G)
    viewAgreeAbove_chop_nemo k v

/-- **And cross-cut agreement**, from an arbitrary view of the
truncation. -/
theorem decided_agree_chop_nemo (hd : G ≤ S.slotRound d)
    {W : Nemo.View Validator BlockId Payload (chopNemo U G)}
    {V : Nemo.View Validator BlockId Payload U} {k : ℕ} {w v : Option BlockId}
    (hW : Nemo.Decided (S := S.chop G d hd) (chopNemo U G) W k w)
    (hV : Nemo.Decided (S := S) U V (d + k) v) : w = v :=
  decided_agree_truncate NemoProperties.agree
    (LocalTruncate.of_banded NemoProperties.banded)
    (truncates_chop_nemo hd) viewAgreeAbove_chop_nemo hW hV

/-! ## The fill -/

/-- **The recovery, at Nemo's universe.** `U`, extended with one block
per gap round, authored by the recovering validator and carrying the
donor's references at that round — `SkipData.copyBlock`, the fill
without the self reference the core's `self_parent` clause demands.

Nemo's two invariants are discharged where they differ from the core's.
The majority quorum is the donor's, because the filled block's
references *are* the donor's and old ids are looked up unchanged.
Non-equivocation is universal here, with no Byzantine exemption, and
that is exactly what `hgap` supplies: the recovering validator authored
nothing in the gap, so no old block collides with a filled one, and the
filled ones are one per round. -/
def skipFillNemo (U : Nemo.Universe Validator BlockId Payload)
    (sk : SkipData U.ids U.block) : Nemo.Universe Validator BlockId Payload where
  ids := U.ids ∪ sk.freshIds
  block b := if b ∈ U.ids then U.block b else sk.copyBlock (sk.idx b)
  complete := by
    intro i hi j hj
    rcases Finset.mem_union.mp hi with ho | hf
    · rw [if_pos ho] at hj
      exact Finset.mem_union_left _ (U.complete i ho j hj)
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (U.block sk.B1).round := rfl
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hj
      simp only [SkipData.copyBlock] at hj
      exact Finset.mem_union_left _
        (U.complete _ (sk.hline_mem k (by omega) hk2) j hj)
  valid := by
    intro i hi
    rcases Finset.mem_union.mp hi with ho | hf
    · rw [if_pos ho]
      have hv := U.valid i ho
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [if_pos (U.complete i ho j hj)]
        exact hv.predecessor j hj
      · intro hr
        refine le_trans (hv.quorum hr) (Finset.card_le_card ?_)
        intro c hc
        unfold creators creatorsOf at hc ⊢
        obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
        refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
        simp only
        rw [if_pos (U.complete i ho j hj)]
        exact hjc
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (U.block sk.B1).round := rfl
      rw [if_neg (sk.hfresh_new k), sk.hidx]
      have hlm := sk.hline_mem k (by omega) hk2
      have hlv := U.valid _ hlm
      have hlr := sk.hline_round k (by omega) hk2
      refine ⟨?_, ?_⟩
      · intro j hj
        simp only [SkipData.copyBlock] at hj ⊢
        rw [if_pos (U.complete _ hlm j hj)]
        have := hlv.predecessor j hj
        omega
      · intro _
        have hq := hlv.quorum (by omega)
        refine le_trans hq (Finset.card_le_card ?_)
        intro c hc
        unfold creators creatorsOf at hc ⊢
        obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
        refine Finset.mem_image.mpr ⟨j, ?_, ?_⟩
        · simp only [SkipData.copyBlock]; exact hj
        · simp only
          rw [if_pos (U.complete _ hlm j hj)]
          exact hjc
  no_equivocation := by
    intro i hi j hj hcc hrr
    rcases Finset.mem_union.mp hi with ho | hf <;>
      rcases Finset.mem_union.mp hj with ho' | hf'
    · rw [if_pos ho] at hcc hrr
      rw [if_pos ho'] at hcc hrr
      exact U.no_equivocation i ho j ho' hcc hrr
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf'
      have hR0 : sk.r0 = (U.block sk.B1).round := rfl
      rw [if_pos ho] at hcc hrr
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hcc hrr
      exact (sk.hgap i ho hcc
        (by simp only [SkipData.copyBlock] at hrr; omega)
        (by simp only [SkipData.copyBlock] at hrr; omega)).elim
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (U.block sk.B1).round := rfl
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hcc hrr
      rw [if_pos ho'] at hcc hrr
      exact (sk.hgap j ho' hcc.symm
        (by simp only [SkipData.copyBlock] at hrr; omega)
        (by simp only [SkipData.copyBlock] at hrr; omega)).elim
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      obtain ⟨l, hl1, hl2, rfl⟩ := sk.mem_freshIds.mp hf'
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hrr
      rw [if_neg (sk.hfresh_new l), sk.hidx] at hrr
      simp only [SkipData.copyBlock] at hrr
      exact hrr ▸ rfl

variable {sk : SkipData U.ids U.block}

@[simp] theorem skipFillNemo_block_old {b : BlockId} (hb : b ∈ U.ids) :
    (skipFillNemo U sk).block b = U.block b := if_pos hb

@[simp] theorem skipFillNemo_block_fresh {k : ℕ} :
    (skipFillNemo U sk).block (sk.fresh k) = sk.copyBlock k := by
  simp only [skipFillNemo, if_neg (sk.hfresh_new k), sk.hidx]

/-- The pre-crash view, read in the repaired universe: the same ids,
and every one of them old. -/
def liftViewNemo (V : Nemo.View Validator BlockId Payload U) :
    Nemo.View Validator BlockId Payload (skipFillNemo U sk) where
  ids := V.ids
  subset_ids := fun _ hb => Finset.mem_union_left _ (V.subset_ids hb)
  complete := by
    intro i hi j hj
    rw [skipFillNemo_block_old (V.subset_ids hi)] at hj
    exact V.complete i hi j hj

/-- **The fill is an extension of Nemo's carrier.** -/
theorem extends_skipFill_nemo :
    Extends (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) U (skipFillNemo U sk) where
  subset := fun _ h => Finset.mem_union_left _ h
  block := fun b h => skipFillNemo_block_old h

/-- **What the fill sustains.** Above `sk.r` the fill added nothing, so
every block there is old and unchanged. Below it the claim would be
false, and deliberately: the blocks a fill adds stand in for blocks that
voted, and need not vote as they did. -/
theorem sustains_skipFill_nemo :
    Sustains (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) U (skipFillNemo U sk) 0 (sk.r + 1) where
  mem := fun b => by
    show (b ∈ U.ids ∧ sk.r + 1 ≤ (U.block b).round) ↔
      (b ∈ (skipFillNemo U sk).ids ∧ sk.r + 1 ≤ ((skipFillNemo U sk).block b).round + 0)
    constructor
    · rintro ⟨hb, hr⟩
      exact ⟨Finset.mem_union_left _ hb, by rw [skipFillNemo_block_old hb]; omega⟩
    · rintro ⟨hb, hr⟩
      have hbU : b ∈ U.ids := by
        rcases Finset.mem_union.mp hb with ho | hfr
        · exact ho
        · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hfr
          rw [skipFillNemo_block_fresh] at hr
          simp only [SkipData.copyBlock] at hr
          omega
      exact ⟨hbU, by rw [skipFillNemo_block_old hbU] at hr; omega⟩
  round := fun b hb _ => by
    show ((skipFillNemo U sk).block b).round + 0 = (U.block b).round
    rw [skipFillNemo_block_old hb]; omega
  creator := fun b hb _ => by
    show ((skipFillNemo U sk).block b).creator = (U.block b).creator
    rw [skipFillNemo_block_old hb]
  refs := fun b hb _ => by
    show ((skipFillNemo U sk).block b).refs = (U.block b).refs
    rw [skipFillNemo_block_old hb]

/-- **Verdicts survive the recovery, for Nemo.** The replica that
recovered reaches every verdict it reached before, so what it had
already output stands. -/
theorem decided_skipFill_nemo {V : Nemo.View Validator BlockId Payload U}
    {k : ℕ} {v : Option BlockId} (h : Nemo.Decided (S := S) U V k v) :
    Nemo.Decided (S := S) (skipFillNemo U sk) (liftViewNemo V) k v :=
  Persist.of_banded NemoProperties.banded S U (skipFillNemo U sk)
    extends_skipFill_nemo V (liftViewNemo V) (fun _ hb => hb) k v h

/-- **And agreement across it**: a validator that recovered agrees with
one that did not, from any view of the fill. -/
theorem decided_agree_skipFill_nemo {V : Nemo.View Validator BlockId Payload U}
    {W : Nemo.View Validator BlockId Payload (skipFillNemo U sk)}
    {k : ℕ} {v w : Option BlockId}
    (hV : Nemo.Decided (S := S) U V k v)
    (hW : Nemo.Decided (S := S) (skipFillNemo U sk) W k w) : v = w :=
  decided_agree_extends NemoProperties.agree
    (Persist.of_banded NemoProperties.banded) extends_skipFill_nemo
    (V' := liftViewNemo V) (fun _ hb => hb) hV hW

end Integration

end LeanDag
