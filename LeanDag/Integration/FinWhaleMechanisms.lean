import LeanDag.Properties.Arcs.GC
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.FinWhale.Carrier

/-!
# Garbage collection and crash recovery for FinWhale

`scripts/audit-mechanisms.py` asked for both. FinWhale shows `Banded`
and `Agree`, so the two transformer arcs' theorems already held of it,
and nobody had applied them.

Like Nemo, FinWhale keeps its own universe record, so it builds its own
cut and its own fill out of the shared block data — `chopBlk` and
`SkipData` — and discharges its own invariants. It has two the core does
not: `ValidHere.leader_clause`, which asks that the parents of a block
be consistent about every validator, and `Dag.correct_single`, which
exempts the faulty from non-equivocation.

**The leader clause is what decides the shape of both constructions.**
It is a condition on what a block's parents *jointly* reference, so it
survives any operation that leaves a block's two-step cone alone and is
broken by any operation that grafts one cone onto another.

* The cut leaves it alone. Above `G + 1` nothing moves; at `G + 1` every
  parent has lost its references, so the clause holds with nothing to
  check; below the cut a block has no parents at all.
* The fill would break it if it took `SkipData.fillBlock`, whose added
  self reference grafts the anchor's parents onto the donor's at the
  boundary round, where nothing bounds the two together. It takes
  `SkipData.copyBlock` instead — FinWhale has no self-parent clause to
  satisfy — and then the filled block's parents *are* the donor's and
  the clause is the donor's verbatim.

That is the same obstruction that puts Optimal-Hydrozoan's fill out of
scope (`not_leaderExcludedAll_Ufill`), met by choosing the fill that
adds no edge rather than by weakening the rule.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Properties.Arcs
open LeanDag.FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : LeanDag.FinWhale.Params Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {S : Slots Validator} {G d : ℕ}
variable {D : Dag Validator BlockId Payload}

/-! ## The cut -/

/-- **The cut, at FinWhale's DAG.** The blocks at or above the horizon,
rounds rebased by `−G`, the round-`G` layer as the new geneses. -/
def chopFinWhale (D : Dag Validator BlockId Payload) (G : ℕ) :
    Dag Validator BlockId Payload where
  ids := D.ids.filter fun i => G ≤ (D.block i).round
  block := chopBlk D.block G
  complete := by
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    rcases Nat.lt_or_ge G (D.block i).round with h | h
    · rw [chopBlk_refs_of_lt h] at hj
      have hjr := (D.valid i hi.1).predecessor j hj
      exact Finset.mem_filter.mpr ⟨D.complete i hi.1 j hj, by omega⟩
    · rw [chopBlk_refs_of_le h] at hj
      exact absurd hj (Finset.notMem_empty j)
  valid := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have hv := D.valid i hi.1
    rcases Nat.lt_or_ge G (D.block i).round with h | h
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro j hj
        rw [chopBlk_refs_of_lt h] at hj
        have := hv.predecessor j hj
        rw [chopBlk_round, chopBlk_round]
        omega
      · intro a ha b hb hab
        rw [chopBlk_refs_of_lt h] at ha hb
        rw [chopBlk_creator, chopBlk_creator] at hab
        exact hv.distinct_creators a ha b hb hab
      · intro _
        have hcr : creators (chopBlk D.block G) (chopBlk D.block G i) =
            creators D.block (D.block i) := by
          unfold creators
          rw [chopBlk_refs_of_lt h, creatorsOf_chopBlk]
        rw [hcr]
        exact hv.quorum (by omega)
      · -- the leader clause, at `G + 1` and above it
        intro v
        rcases Nat.lt_or_ge (G + 1) (D.block i).round with h1 | h1
        · -- above the boundary: parents and grandparents are untouched
          rcases hv.leader_clause v with hl | hr
          · refine Or.inl ?_
            intro a ha b hb x hx y hy hxv hyv
            rw [chopBlk_refs_of_lt h] at ha hb
            have har := hv.predecessor a ha
            have hbr := hv.predecessor b hb
            rw [chopBlk_refs_of_lt (by omega)] at hx
            rw [chopBlk_refs_of_lt (by omega)] at hy
            rw [chopBlk_creator] at hxv hyv
            exact hl a ha b hb x hx y hy hxv hyv
          · refine Or.inr ?_
            intro a ha
            rw [chopBlk_refs_of_lt h] at ha
            rw [chopBlk_creator]
            exact hr a ha
        · -- the boundary round: every parent is a new genesis
          refine Or.inl ?_
          intro a ha b _ x hx
          rw [chopBlk_refs_of_lt h] at ha
          have har := hv.predecessor a ha
          rw [chopBlk_refs_of_le (by omega)] at hx
          exact absurd hx (Finset.notMem_empty x)
    · -- the new base layer, and junk below it: no references
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j hj
        rw [chopBlk_refs_of_le h] at hj
        exact absurd hj (Finset.notMem_empty j)
      · intro a ha
        rw [chopBlk_refs_of_le h] at ha
        exact absurd ha (Finset.notMem_empty a)
      · intro hr
        rw [chopBlk_round] at hr
        omega
      · intro v
        refine Or.inr ?_
        intro a ha
        rw [chopBlk_refs_of_le h] at ha
        exact absurd ha (Finset.notMem_empty a)
  correct_single := by
    intro i hi j hj hcorrect hcreator hround
    rw [Finset.mem_filter] at hi hj
    rw [chopBlk_creator] at hcorrect hcreator
    rw [chopBlk_creator] at hcreator
    rw [chopBlk_round, chopBlk_round] at hround
    exact D.correct_single i hi.1 j hj.1 hcorrect hcreator (by omega)

@[simp] theorem mem_chopFinWhale_ids {i : BlockId} :
    i ∈ (chopFinWhale D G).ids ↔ i ∈ D.ids ∧ G ≤ (D.block i).round :=
  Finset.mem_filter

@[simp] theorem chopFinWhale_block :
    (chopFinWhale D G).block = chopBlk D.block G := rfl

/-- The truncated view: keep what clears the cut. -/
def chopViewFinWhale (V : {V : Finset BlockId // IsView D V}) (G : ℕ) :
    {V : Finset BlockId // IsView (chopFinWhale D G) V} :=
  ⟨V.val.filter fun i => G ≤ (D.block i).round, by
    constructor
    · intro i hi
      rw [Finset.mem_filter] at hi
      exact mem_chopFinWhale_ids.mpr ⟨V.property.subset hi.1, hi.2⟩
    · intro i hi j hj
      rw [Finset.mem_filter] at hi
      have hj' : j ∈ (chopBlk D.block G i).refs := hj
      rcases Nat.lt_or_ge G (D.block i).round with h | h
      · rw [chopBlk_refs_of_lt h] at hj'
        have := (D.valid i (V.property.subset hi.1)).predecessor j hj'
        exact Finset.mem_filter.mpr ⟨V.property.closed i hi.1 j hj', by omega⟩
      · rw [chopBlk_refs_of_le h] at hj'
        exact absurd hj' (Finset.notMem_empty j)⟩

/-- **The cut is a truncation of FinWhale's carrier.** -/
theorem truncates_chop_finwhale (hd : G ≤ S.slotRound d) :
    Truncates (FinWhaleProperties.finWhaleRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload)) D (chopFinWhale D G) S
      (S.chop G d hd) G d where
  mem := fun b => by
    show (b ∈ D.ids ∧ G ≤ (D.block b).round) ↔
      (b ∈ (chopFinWhale D G).ids ∧ G ≤ ((chopFinWhale D G).block b).round + G)
    rw [mem_chopFinWhale_ids, chopFinWhale_block, chopBlk_round]
    constructor
    · rintro ⟨hb, hr⟩; exact ⟨⟨hb, hr⟩, by omega⟩
    · rintro ⟨⟨hb, hr⟩, -⟩; exact ⟨hb, hr⟩
  round := fun b _ hr => by
    have hr' : G ≤ (D.block b).round := hr
    show ((chopFinWhale D G).block b).round + G = (D.block b).round
    rw [chopFinWhale_block, chopBlk_round]; omega
  creator := fun b _ _ => by
    show ((chopFinWhale D G).block b).creator = (D.block b).creator
    rw [chopFinWhale_block, chopBlk_creator]
  refs := fun b _ hr => by
    have hr' : G < (D.block b).round := hr
    show ((chopFinWhale D G).block b).refs = (D.block b).refs
    rw [chopFinWhale_block]
    exact chopBlk_refs_of_lt hr'
  slotRound := fun k => by
    have := horizon_le_slotRound hd k
    show S.slotRound (d + k) - G + G = S.slotRound (d + k)
    omega
  leader := fun _ => rfl
  base := hd

/-- **The chopped view agrees with the original above the cut.** -/
theorem viewAgreeAbove_chop_finwhale {V : {V : Finset BlockId // IsView D V}} :
    ViewAgreeAbove (FinWhaleProperties.finWhaleRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload)) V (chopViewFinWhale V G) G :=
  fun b _ hr => by
    show b ∈ V.val ↔ b ∈ V.val.filter fun i => G ≤ (D.block i).round
    rw [Finset.mem_filter]
    exact ⟨fun h => ⟨h, hr⟩, fun h => h.1⟩

/-- **Verdict transport across the cut, for FinWhale.** -/
theorem decided_chop_iff_finwhale (hd : G ≤ S.slotRound d)
    {V : {V : Finset BlockId // IsView D V}} {k : ℕ} {v : Option BlockId} :
    (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V (d + k) v ↔
      (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided (S.chop G d hd)
        (chopViewFinWhale V G) k v :=
  LocalTruncate.of_banded FinWhaleProperties.banded
    S (S.chop G d hd) D (chopFinWhale D G) G d (truncates_chop_finwhale hd)
    V (chopViewFinWhale V G) viewAgreeAbove_chop_finwhale k v

/-- **And cross-cut agreement**, from an arbitrary view of the
truncation. -/
theorem decided_agree_chop_finwhale (hd : G ≤ S.slotRound d)
    {W : {W : Finset BlockId // IsView (chopFinWhale D G) W}}
    {V : {V : Finset BlockId // IsView D V}} {k : ℕ} {w v : Option BlockId}
    (hW : (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided
      (S.chop G d hd) W k w)
    (hV : (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V (d + k) v) :
    w = v :=
  decided_agree_truncate FinWhaleProperties.agree
    (LocalTruncate.of_banded FinWhaleProperties.banded)
    (truncates_chop_finwhale hd) viewAgreeAbove_chop_finwhale hW hV

/-! ## The fill -/

/-- **The recovery, at FinWhale's DAG.** `D`, extended with one block
per gap round, authored by the recovering validator and carrying the
donor's references at that round.

`SkipData.copyBlock` rather than `SkipData.fillBlock`: FinWhale has no
self-parent clause to satisfy, and the self reference the core's fill
adds is exactly what `ValidHere.leader_clause` would object to. With the
donor's references copied and nothing added, all four validity clauses
are the donor's, read through lookups that agree on every old id. -/
def skipFillFinWhale (D : Dag Validator BlockId Payload)
    (sk : SkipData D.ids D.block) : Dag Validator BlockId Payload where
  ids := D.ids ∪ sk.freshIds
  block b := if b ∈ D.ids then D.block b else sk.copyBlock (sk.idx b)
  complete := by
    intro i hi j hj
    rcases Finset.mem_union.mp hi with ho | hf
    · rw [if_pos ho] at hj
      exact Finset.mem_union_left _ (D.complete i ho j hj)
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (D.block sk.B1).round := rfl
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hj
      simp only [SkipData.copyBlock] at hj
      exact Finset.mem_union_left _
        (D.complete _ (sk.hline_mem k (by omega) hk2) j hj)
  valid := by
    intro i hi
    rcases Finset.mem_union.mp hi with ho | hf
    · rw [if_pos ho]
      have hv := D.valid i ho
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j hj
        rw [if_pos (D.complete i ho j hj)]
        exact hv.predecessor j hj
      · intro a ha b hb hab
        rw [if_pos (D.complete i ho a ha), if_pos (D.complete i ho b hb)] at hab
        exact hv.distinct_creators a ha b hb hab
      · intro hr
        refine le_trans (hv.quorum hr) (Finset.card_le_card ?_)
        intro c hc
        unfold creators creatorsOf at hc ⊢
        obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
        refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
        simp only
        rw [if_pos (D.complete i ho j hj)]
        exact hjc
      · intro v
        rcases hv.leader_clause v with hl | hr
        · refine Or.inl ?_
          intro a ha b hb x hx y hy hxv hyv
          rw [if_pos (D.complete i ho a ha)] at hx
          rw [if_pos (D.complete i ho b hb)] at hy
          rw [if_pos (D.complete _ (D.complete i ho a ha) x hx)] at hxv
          rw [if_pos (D.complete _ (D.complete i ho b hb) y hy)] at hyv
          exact hl a ha b hb x hx y hy hxv hyv
        · refine Or.inr ?_
          intro a ha
          rw [if_pos (D.complete i ho a ha)]
          exact hr a ha
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (D.block sk.B1).round := rfl
      rw [if_neg (sk.hfresh_new k), sk.hidx]
      have hlm := sk.hline_mem k (by omega) hk2
      have hlv := D.valid _ hlm
      have hlr := sk.hline_round k (by omega) hk2
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j hj
        simp only [SkipData.copyBlock] at hj ⊢
        rw [if_pos (D.complete _ hlm j hj)]
        have := hlv.predecessor j hj
        omega
      · intro a ha b hb hab
        simp only [SkipData.copyBlock] at ha hb
        rw [if_pos (D.complete _ hlm a ha), if_pos (D.complete _ hlm b hb)] at hab
        exact hlv.distinct_creators a ha b hb hab
      · intro _
        have hq := hlv.quorum (by omega)
        refine le_trans hq (Finset.card_le_card ?_)
        intro c hc
        unfold creators creatorsOf at hc ⊢
        obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
        refine Finset.mem_image.mpr ⟨j, ?_, ?_⟩
        · simp only [SkipData.copyBlock]; exact hj
        · simp only
          rw [if_pos (D.complete _ hlm j hj)]
          exact hjc
      · intro v
        rcases hlv.leader_clause v with hl | hr
        · refine Or.inl ?_
          intro a ha b hb x hx y hy hxv hyv
          simp only [SkipData.copyBlock] at ha hb
          rw [if_pos (D.complete _ hlm a ha)] at hx
          rw [if_pos (D.complete _ hlm b hb)] at hy
          rw [if_pos (D.complete _ (D.complete _ hlm a ha) x hx)] at hxv
          rw [if_pos (D.complete _ (D.complete _ hlm b hb) y hy)] at hyv
          exact hl a ha b hb x hx y hy hxv hyv
        · refine Or.inr ?_
          intro a ha
          simp only [SkipData.copyBlock] at ha
          rw [if_pos (D.complete _ hlm a ha)]
          exact hr a ha
  correct_single := by
    intro i hi j hj _ hcc hrr
    rcases Finset.mem_union.mp hi with ho | hfr <;>
      rcases Finset.mem_union.mp hj with ho' | hfr'
    · rw [if_pos ho] at hcc hrr
      rw [if_pos ho'] at hcc hrr
      exact D.correct_single i ho j ho' (by rwa [if_pos ho] at *) hcc hrr
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hfr'
      have hR0 : sk.r0 = (D.block sk.B1).round := rfl
      rw [if_pos ho] at hcc hrr
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hcc hrr
      exact (sk.hgap i ho hcc
        (by simp only [SkipData.copyBlock] at hrr; omega)
        (by simp only [SkipData.copyBlock] at hrr; omega)).elim
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hfr
      have hR0 : sk.r0 = (D.block sk.B1).round := rfl
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hcc hrr
      rw [if_pos ho'] at hcc hrr
      exact (sk.hgap j ho' hcc.symm
        (by simp only [SkipData.copyBlock] at hrr; omega)
        (by simp only [SkipData.copyBlock] at hrr; omega)).elim
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hfr
      obtain ⟨l, hl1, hl2, rfl⟩ := sk.mem_freshIds.mp hfr'
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hrr
      rw [if_neg (sk.hfresh_new l), sk.hidx] at hrr
      simp only [SkipData.copyBlock] at hrr
      exact hrr ▸ rfl

variable {sk : SkipData D.ids D.block}

@[simp] theorem skipFillFinWhale_block_old {b : BlockId} (hb : b ∈ D.ids) :
    (skipFillFinWhale D sk).block b = D.block b := if_pos hb

@[simp] theorem skipFillFinWhale_block_fresh {k : ℕ} :
    (skipFillFinWhale D sk).block (sk.fresh k) = sk.copyBlock k := by
  simp only [skipFillFinWhale, if_neg (sk.hfresh_new k), sk.hidx]

/-- The pre-crash view, read in the repaired DAG: the same ids, and
every one of them old. -/
def liftViewFinWhale (V : {V : Finset BlockId // IsView D V}) :
    {V : Finset BlockId // IsView (skipFillFinWhale D sk) V} :=
  ⟨V.val, by
    constructor
    · exact fun _ hb => Finset.mem_union_left _ (V.property.subset hb)
    · intro i hi j hj
      rw [skipFillFinWhale_block_old (V.property.subset hi)] at hj
      exact V.property.closed i hi j hj⟩

/-- **The fill is an extension of FinWhale's carrier.** -/
theorem extends_skipFill_finwhale :
    Extends (FinWhaleProperties.finWhaleRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload)) D (skipFillFinWhale D sk) where
  subset := fun _ h => Finset.mem_union_left _ h
  block := fun b h => skipFillFinWhale_block_old h

/-- **What the fill sustains.** Above `sk.r` the fill added nothing, so
every block there is old and unchanged. -/
theorem sustains_skipFill_finwhale :
    Sustains (FinWhaleProperties.finWhaleRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload)) D (skipFillFinWhale D sk) 0 (sk.r + 1) where
  mem := fun b => by
    show (b ∈ D.ids ∧ sk.r + 1 ≤ (D.block b).round) ↔
      (b ∈ (skipFillFinWhale D sk).ids ∧
        sk.r + 1 ≤ ((skipFillFinWhale D sk).block b).round + 0)
    constructor
    · rintro ⟨hb, hr⟩
      exact ⟨Finset.mem_union_left _ hb, by rw [skipFillFinWhale_block_old hb]; omega⟩
    · rintro ⟨hb, hr⟩
      have hbD : b ∈ D.ids := by
        rcases Finset.mem_union.mp hb with ho | hfr
        · exact ho
        · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hfr
          rw [skipFillFinWhale_block_fresh] at hr
          simp only [SkipData.copyBlock] at hr
          omega
      exact ⟨hbD, by rw [skipFillFinWhale_block_old hbD] at hr; omega⟩
  round := fun b hb _ => by
    show ((skipFillFinWhale D sk).block b).round + 0 = (D.block b).round
    rw [skipFillFinWhale_block_old hb]; omega
  creator := fun b hb _ => by
    show ((skipFillFinWhale D sk).block b).creator = (D.block b).creator
    rw [skipFillFinWhale_block_old hb]
  refs := fun b hb _ => by
    show ((skipFillFinWhale D sk).block b).refs = (D.block b).refs
    rw [skipFillFinWhale_block_old hb]

/-- **Verdicts survive the recovery, for FinWhale.** -/
theorem decided_skipFill_finwhale {V : {V : Finset BlockId // IsView D V}}
    {k : ℕ} {v : Option BlockId}
    (h : (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V k v) :
    (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S
      (liftViewFinWhale (sk := sk) V) k v :=
  Persist.of_banded FinWhaleProperties.banded S D (skipFillFinWhale D sk)
    extends_skipFill_finwhale V (liftViewFinWhale V) (fun _ hb => hb) k v h

/-- **And agreement across it**: a validator that recovered agrees with
one that did not, from any view of the fill. -/
theorem decided_agree_skipFill_finwhale {V : {V : Finset BlockId // IsView D V}}
    {W : {W : Finset BlockId // IsView (skipFillFinWhale D sk) W}}
    {k : ℕ} {v w : Option BlockId}
    (hV : (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V k v)
    (hW : (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S W k w) :
    v = w :=
  decided_agree_extends FinWhaleProperties.agree
    (Persist.of_banded FinWhaleProperties.banded) extends_skipFill_finwhale
    (V' := liftViewFinWhale V) (fun _ hb => hb) hV hW

end Integration

end LeanDag
