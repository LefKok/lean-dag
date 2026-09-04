import LeanDag.Hydrozoan.Properties.Proof
import LeanDag.Integration.Hydrozoan.FillDecided
import LeanDag.Properties.Sustain

/-!
# The fill, re-derived through the target properties

`docs/target-properties.md` G3's test, and the reason to believe the
arc pays. `FillDecided.lean` proves `decided_fillHZ` by a
six-constructor induction over Hydrozoan's decision relation, with
transfer lemmas threaded through it for that one transformer. HZ9
proves the same protocol persists under **every** extension, once.

Below, the fill is shown to be an extension — two fields, each a simp
lemma the arc already had — and the original theorem follows with **no
induction of its own**. Any further extension-shaped mechanism costs
Hydrozoan nothing beyond what HZ9 already established.

The same is done for the cut. `TruncatesHZ` is exhibited by `chopHZ` —
which is the satisfiability check `Shifted` never got, and would have
failed — and `decided_chopHZ`, a further two inductions in
`ChopDecided.lean`, follows from HZ9's `LocalTruncate` with none of its
own.

The bespoke proofs stay where they are: `Stack.lean` and `Liveness.lean`
consume them, and `integration.md` §4.2 prescribes generalising with the
old statements kept as corollaries.
-/

namespace LeanDag

namespace Integration

namespace Hydrozoan

open LeanDag.Properties

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica] [Fact (HybridCommittee Replica)]
variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {hsp : SelfParenting U}

/-- **The fill is an extension.** It holds every block the original held
and denotes each of them unchanged. -/
theorem extends_skipFillHZ (sk : SkipMsg (toCore U hsp)) :
    Extends LeanDag.Hydrozoan.rule U (skipFillHZ U hsp sk) where
  subset := fun b hb => by
    change b ∈ (skipFillHZ U hsp sk).ids
    simp only [skipFillHZ, transport_ids, SkipMsg.skipFill]
    exact Finset.mem_union_left _ hb
  block := fun b hb => by
    change LeanDag.Hydrozoan.adaptBlock ((skipFillHZ U hsp sk).block b)
       = LeanDag.Hydrozoan.adaptBlock (U.block b)
    congr 1
    exact skipFillHZ_block_old hb

/-- **HI9's transport, from HZ9.** The same statement as
`decided_fillHZ`, reached without an induction: persistence is proved
once for the protocol, and the fill is one extension among others. -/
theorem decided_fillHZ_of_persist (sk : SkipMsg (toCore U hsp))
    [S : LeanDag.Hydrozoan.Slots Replica] {V : LeanDag.Hydrozoan.View U}
    {k : ℕ} {v : Option BlockId} (h : LeanDag.Hydrozoan.Decided U V k v) :
    LeanDag.Hydrozoan.Decided (skipFillHZ U hsp sk) (liftViewHZ U hsp sk V) k v :=
  LeanDag.Hydrozoan.Properties.persist_aux (extends_skipFillHZ sk)
    (by
      intro b hb
      simpa using hb) h

/-! ## The cut -/

/-- **The truncation is a truncation**, in the carrier's vocabulary.
This is the check the failed re-indexing property never received: a
relation with no models proves nothing, and exhibiting a witness before
proving anything about it is the discipline that catches it. -/
theorem truncatesHZ_chopHZ [S : LeanDag.Hydrozoan.Slots Replica] {G d : ℕ}
    (hd : G ≤ S.slotRound d) :
    LeanDag.Hydrozoan.TruncatesHZ U (chopHZ U hsp G) S (slotsChopHZ hd) G d where
  mem := fun b => mem_chopHZ_ids
  round := fun b hb => by
    have := (mem_chopHZ_ids.mp hb).2
    rw [chopHZ_round]; omega
  author := fun b _ => chopHZ_author b
  parents := fun b hb hm => by
    refine chopHZ_parents_of_lt ?_
    have hr := (mem_chopHZ_ids.mp hb).2
    rw [chopHZ_round] at hm
    omega
  slotRound := fun k => by have := chopRound_add hd k; omega
  leader := fun k => slotsChopHZ_leader hd k
  base := hd

/-- **HI7's transport, from HZ9.** The same statement as
`decided_chopHZ`, reached without an induction. -/
theorem decided_chopHZ_of_localTruncate [S : LeanDag.Hydrozoan.Slots Replica] {G d : ℕ}
    (hd : G ≤ S.slotRound d) {V : LeanDag.Hydrozoan.View U} {k : ℕ} {v : Option BlockId} :
    LeanDag.Hydrozoan.Decided (S := slotsChopHZ hd) (chopHZ U hsp G)
        (View.chopHZ V hsp G) k v
      ↔ LeanDag.Hydrozoan.Decided U V (d + k) v :=
  (LeanDag.Hydrozoan.TruncatesHZ.decided_iff (truncatesHZ_chopHZ (hsp := hsp) hd)
    (fun b hb hbr => by
      change b ∈ V.ids ↔ b ∈ (View.chopHZ V hsp G).ids
      exact (mem_viewChopHZ (V := V) hbr).symm)).symm

/-! ## What the two mechanisms sustain

The satisfiability witnesses for `Properties.Sustains`, and they got
*shorter* when the obligation was restated over blocks rather than over
named predicates: each is now four facts the arc already had. Both
settling rounds are the ones the bespoke liveness transport threads by
hand. -/

/-- **A truncation sustains from its horizon.** At and above the cut a
block keeps its author and, strictly above, its references. -/
theorem sustains_chopHZ {G : ℕ} :
    Sustains LeanDag.Hydrozoan.rule U (chopHZ U hsp G) G G where
  mem := fun b => by
    change (b ∈ U.ids ∧ G ≤ (U.block b).round) ↔
      (b ∈ (chopHZ U hsp G).ids ∧ G ≤ ((chopHZ U hsp G).block b).round + G)
    have h1 : b ∈ (chopHZ U hsp G).ids ↔ b ∈ U.ids ∧ G ≤ (U.block b).round := mem_chopHZ_ids
    have h2 : ((chopHZ U hsp G).block b).round = (U.block b).round - G := chopHZ_round b
    constructor
    · rintro ⟨hb, hr⟩
      refine ⟨h1.mpr ⟨hb, hr⟩, ?_⟩
      rw [h2, Nat.sub_add_cancel hr]; exact hr
    · rintro ⟨hb, _⟩
      exact h1.mp hb
  round := fun b hb hr => by
    have hr' : G ≤ (U.block b).round := hr
    change ((chopHZ U hsp G).block b).round + G = (U.block b).round
    rw [chopHZ_round]; omega
  creator := fun b _ _ => chopHZ_author b
  refs := fun b _ hr => chopHZ_parents_of_lt hr

/-- **A fill sustains from the top of its gap.** Above it the fill added
nothing, so every block is old and unchanged; below it the claim would
be false, since the blocks a fill adds stand in for blocks that voted
and need not vote as they did. -/
theorem sustains_skipFillHZ (sk : SkipMsg (toCore U hsp)) :
    Sustains LeanDag.Hydrozoan.rule U (skipFillHZ U hsp sk) 0 (sk.r + 1) where
  mem := fun b => by
    change (b ∈ U.ids ∧ sk.r + 1 ≤ (U.block b).round) ↔
      (b ∈ (skipFillHZ U hsp sk).ids ∧ sk.r + 1 ≤ ((skipFillHZ U hsp sk).block b).round + 0)
    constructor
    · rintro ⟨hb, hr⟩
      refine ⟨?_, ?_⟩
      · simp only [skipFillHZ, transport_ids, SkipMsg.skipFill]
        exact Finset.mem_union_left _ hb
      · rw [skipFillHZ_block_old hb]; omega
    · rintro ⟨hb, hr⟩
      have hbU : b ∈ U.ids := by
        by_contra hno
        have hfresh : b ∈ sk.freshIds := by
          have hu : b ∈ (toCore U hsp).ids ∪ sk.freshIds := hb
          rcases Finset.mem_union.mp hu with h | h
          · exact absurd h hno
          · exact h
        obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hfresh
        have hk : ((skipFillHZ U hsp sk).block (sk.fresh k)).round = k := by
          change (sk.skipFill.block (sk.fresh k)).round = k
          rw [sk.skipFill_block_fresh]; rfl
        rw [hk] at hr; omega
      refine ⟨hbU, ?_⟩
      rw [skipFillHZ_block_old hbU] at hr; omega
  round := fun b hb _ => by
    change ((skipFillHZ U hsp sk).block b).round + 0 = (U.block b).round
    rw [skipFillHZ_block_old hb]; omega
  creator := fun b hb _ => by
    change ((skipFillHZ U hsp sk).block b).author = (U.block b).author
    rw [skipFillHZ_block_old hb]
  refs := fun b hb _ => by
    change ((skipFillHZ U hsp sk).block b).parents = (U.block b).parents
    rw [skipFillHZ_block_old hb]

end Hydrozoan

end Integration

end LeanDag
