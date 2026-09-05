import LeanDag.Hydrozoan.Properties.Proof
import LeanDag.Integration.Hydrozoan.FillDecided
import LeanDag.Properties.Sustain
import LeanDag.Properties.Derived.Truncate
import LeanDag.Properties.Arcs.GC
import LeanDag.Properties.Arcs.SafeSkip

/-!
# The fill, re-derived through the target properties

`docs/target-properties.md` G3's test, and the reason to believe the
arc pays. `FillDecided.lean` proved verdict transport across the fill
by a six-constructor induction over Hydrozoan's decision relation, with
transfer lemmas threaded through it for that one transformer. HZ9
proves the same protocol persists under **every** extension, once.

Below, the fill is shown to be an extension — two fields, each a simp
lemma the arc already had — and the original theorem follows with **no
induction of its own**. Any further extension-shaped mechanism costs
Hydrozoan nothing beyond what HZ9 already established.

The same is done for the cut. `TruncatesHZ` is exhibited by `chopHZ` —
which is the satisfiability check `Shifted` never got, and would have
failed — and the transport, a further two inductions in
`ChopDecided.lean`, follows from HZ9's `LocalTruncate` with none of its
own.

**The bespoke proofs are gone.** They stayed for a while as
corollaries, per `integration.md` §4.2 — generalise first, delete
later. Later is here: `Stack.lean` and the two witness files now
consume the theorems below, and `ChopDecided.lean` and
`FillDecided.lean` state what the two transformers preserve without
proving anything about verdicts. Hydrozoan's decision relation is
inducted over in its own development and nowhere else.
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

/-- **HI9's transport, from HZ9.** Verdicts survive the fill, reached
without an induction: persistence is proved once for the protocol, and
the fill is one extension among others. `FillDecided.lean` proved this
by a six-constructor induction until the induction was deleted. -/
theorem decided_fillHZ_of_persist (sk : SkipMsg (toCore U hsp))
    [S : LeanDag.Hydrozoan.Slots Replica] {V : LeanDag.Hydrozoan.View U}
    {k : ℕ} {v : Option BlockId} (h : LeanDag.Hydrozoan.Decided U V k v) :
    LeanDag.Hydrozoan.Decided (skipFillHZ U hsp sk) (liftViewHZ U hsp sk V) k v :=
  Properties.Persist.of_banded LeanDag.Hydrozoan.banded
    (LeanDag.Hydrozoan.toCoreSlots S) U (skipFillHZ U hsp sk) (extends_skipFillHZ sk)
    V (liftViewHZ U hsp sk V) (fun b hb => by simpa using hb) k v h

/-- **HI9's cross-fill agreement, from HZ9 and HZ3.** A verdict reached
before the recovery and one reached after it agree. The deleted bespoke
version composed its induction with slot agreement by hand; this is
`Arcs.decided_agree_extends`, which every rule with `Agree` and
`Persist` has. -/
theorem decided_fill_agreeHZ_of_properties (sk : SkipMsg (toCore U hsp))
    [S : LeanDag.Hydrozoan.Slots Replica] {V : LeanDag.Hydrozoan.View U}
    {W : LeanDag.Hydrozoan.View (skipFillHZ U hsp sk)} {k : ℕ} {v w : Option BlockId}
    (hV : LeanDag.Hydrozoan.Decided U V k v)
    (hW : LeanDag.Hydrozoan.Decided (skipFillHZ U hsp sk) W k w) : v = w :=
  Properties.Arcs.decided_agree_extends LeanDag.Hydrozoan.agree
    (Properties.Persist.of_banded LeanDag.Hydrozoan.banded) (extends_skipFillHZ sk)
    (V' := liftViewHZ U hsp sk V) (fun b hb => by simpa using hb) hV hW

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

/-! ## The cut -/

/-- **The truncation is a truncation**, in the carrier's vocabulary.
This is the check the failed re-indexing property never received: a
relation with no models proves nothing, and exhibiting a witness before
proving anything about it is the discipline that catches it.

The block half is `sustains_chopHZ` below, since `Truncates` is
`RebasedAbove` at `R₀ = G` plus the schedule; only the three schedule
clauses are proved here. -/
theorem truncates_chopHZ [S : LeanDag.Hydrozoan.Slots Replica] {G d : ℕ}
    (hd : G ≤ S.slotRound d) :
    Properties.Truncates LeanDag.Hydrozoan.rule U (chopHZ U hsp G)
      (LeanDag.Hydrozoan.toCoreSlots S)
      (LeanDag.Hydrozoan.toCoreSlots (slotsChopHZ hd)) G d :=
  { sustains_chopHZ (hsp := hsp) (G := G) with
    slotRound := fun k => by
      show (slotsChopHZ hd).slotRound k + G = S.slotRound (d + k)
      have := chopRound_add hd k; omega
    leader := fun k => slotsChopHZ_leader hd k
    base := hd }

/-- **HI7's transport, from HZ9.** A replica that has pruned below the
horizon reaches exactly the verdicts it would have reached with its
whole history, at the re-indexed slot — without an induction, and
without a Hydrozoan-specific truncation relation. `ChopDecided.lean`
proved this by two inductions until they were deleted. -/
theorem decided_chopHZ_of_localTruncate [S : LeanDag.Hydrozoan.Slots Replica] {G d : ℕ}
    (hd : G ≤ S.slotRound d) {V : LeanDag.Hydrozoan.View U} {k : ℕ} {v : Option BlockId} :
    LeanDag.Hydrozoan.Decided (S := slotsChopHZ hd) (chopHZ U hsp G)
        (View.chopHZ V hsp G) k v
      ↔ LeanDag.Hydrozoan.Decided U V (d + k) v :=
  (Properties.LocalTruncate.of_banded LeanDag.Hydrozoan.banded
    (LeanDag.Hydrozoan.toCoreSlots S) (LeanDag.Hydrozoan.toCoreSlots (slotsChopHZ hd))
    U (chopHZ U hsp G) G d (truncates_chopHZ (hsp := hsp) hd) V (View.chopHZ V hsp G)
    (fun b hb hbr => by
      change b ∈ V.ids ↔ b ∈ (View.chopHZ V hsp G).ids
      exact (mem_viewChopHZ (V := V) hbr).symm) k v).symm

/-- **HI8's cross-cut agreement, from HZ9.** A replica that has pruned
below the horizon and one that has not cannot disagree about a slot,
and the pruned replica's view is an arbitrary view of the truncation
rather than a truncated full-history view. The deleted bespoke version
played slot agreement inside the truncation and moved across the cut by
induction; this is `Agree` and `LocalTruncate` composed, which every
rule with a band has. -/
theorem decided_agree_chopHZ_of_properties [S : LeanDag.Hydrozoan.Slots Replica]
    {G d : ℕ} (hd : G ≤ S.slotRound d)
    {V : LeanDag.Hydrozoan.View U} {W : LeanDag.Hydrozoan.View (chopHZ U hsp G)}
    {k : ℕ} {v w : Option BlockId}
    (hV : LeanDag.Hydrozoan.Decided U V (d + k) v)
    (hW : LeanDag.Hydrozoan.Decided (S := slotsChopHZ hd) (chopHZ U hsp G) W k w) :
    v = w :=
  (Properties.Arcs.decided_agree_truncate LeanDag.Hydrozoan.agree
    (Properties.LocalTruncate.of_banded LeanDag.Hydrozoan.banded)
    (truncates_chopHZ (hsp := hsp) hd) (V' := View.chopHZ V hsp G)
    (fun b hb hbr => by
      change b ∈ V.ids ↔ b ∈ (View.chopHZ V hsp G).ids
      exact (mem_viewChopHZ (V := V) hbr).symm)
    hW hV).symm


end Hydrozoan

end Integration

end LeanDag
