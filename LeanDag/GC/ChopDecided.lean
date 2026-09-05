import LeanDag.GC.Chop
import LeanDag.Liveness

/-!
# Decisions survive the cut

`garbage.md` **G3** and **G4** used to be proved here, by structural
induction over the decision relation; they are now
`Properties/Arcs/GC.lean`, from `Banded` and `Agree`. What remains is
the construction the witness needs. The per-slot verdicts
(`directCommit_chop` and friends) said each *rule* reads only the window
above the horizon; this file lifts that to the full decision relation — the
recursion through anchors and intermediate skips included — and closes with
the cross-cut agreement theorem: a validator that joined from the truncation
and never saw the pruned prefix decides every slot exactly as a full-history
validator does.

Three pieces of transport, then the theorem:

* **`View.chop`** — a validator's view, truncated at the horizon. Downward
  closure survives because a retained block's references sit one round below
  it, hence at or above the cut — except at the base layer, where `chop`
  emptied them.
* **`Slots.chop`** — the induced schedule: slots re-indexed from a base slot
  `d` whose round clears the horizon, rounds rebased by `−G`. Monotonicity,
  unboundedness and keying all descend from the original schedule; keying
  needs the base-slot condition `G ≤ slotRound d`, which pins the rebased
  rounds above zero where subtraction is faithful.
* **the rule correspondences** — `IsLeaderBlock`, `Eligible`,
  `DirectCommitIn`, `DirectSkipIn` and the indirect test, each computed in
  the truncation against the truncated view, agree with the original. The
  view-relative ones ride on the fact that everything a rule counts lives
  strictly above the cut, so the view filter is invisible to it.

**`decided_chop`** then follows by structural induction both ways: the
derivation trees match constructor for constructor, with anchors and
intermediate slots re-indexed by `d`. The slot-`d` premise is the *only*
condition — no synchrony, no fairness, no liveness.

**`decided_agree_chop`** is the payoff (G4), and it is deliberately
asymmetric: the joiner's view `W` is an **arbitrary** view of the
truncation — not a truncated full-history view. A joiner's view is never of
the form `V.chop`: lifted to `U` it would not be downward closed, its base
layer having lost its references. The theorem instead plays `decided_unique`
*inside the truncation* against a truncated view, and moves across the cut
through `decided_chop`. So the two validators need share nothing but the
truncation itself.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {G : ℕ}

/-! ## The truncated view -/

/-- A validator's view, truncated at the horizon: keep what clears the cut.
Closure survives: a retained block's references sit one round below it,
hence at or above the cut — except at the base layer, where they are gone. -/
def View.chop (V : View Validator BlockId Payload U) (G : ℕ) :
    View Validator BlockId Payload (chop U G) where
  ids := V.ids.filter fun i => G ≤ (U.block i).round
  subset_ids := by
    intro i hi
    rw [Finset.mem_filter] at hi
    exact mem_chop_ids.mpr ⟨V.subset_ids hi.1, hi.2⟩
  complete := by
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    rw [chop_block_eq] at hj
    rcases Nat.lt_or_ge G (U.block i).round with hlt | hge
    · rw [chopBlock_refs_of_lt hlt] at hj
      have := U.round_of_mem_refs (V.subset_ids hi.1) hj
      exact Finset.mem_filter.mpr ⟨V.complete i hi.1 j hj, by omega⟩
    · rw [chopBlock_refs_of_le hge] at hj
      simp at hj

theorem View.chop_ids (V : View Validator BlockId Payload U) :
    (V.chop G).ids = V.ids.filter fun i => G ≤ (U.block i).round := rfl

/-! ## The induced schedule -/

/-- The truncation's slot schedule: slots re-indexed from a base slot `d`
whose round clears the horizon, rounds rebased by `−G`. The base-slot
condition keeps subtraction faithful, which is what keying needs. -/
@[reducible]
def Slots.chop (S : Slots Validator) (G d : ℕ) (hd : G ≤ S.slotRound d) :
    Slots Validator where
  slotRound k := S.slotRound (d + k) - G
  leader k := S.leader (d + k)
  mono _ _ h := Nat.sub_le_sub_right (S.mono (Nat.add_le_add_left h d)) G
  unbounded := by
    intro n
    obtain ⟨k, hk⟩ := S.unbounded (G + n)
    rcases Nat.le_total k d with hkd | hdk
    · refine ⟨0, ?_⟩
      have := S.mono hkd
      simp only [Nat.add_zero]
      omega
    · refine ⟨k - d, ?_⟩
      have hcancel : d + (k - d) = k := by omega
      simp only [hcancel]
      omega
  keyed := by
    intro k₁ k₂ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hr, hl⟩ := h
    have h₁ := hd.trans (S.mono (Nat.le_add_right d k₁))
    have h₂ := hd.trans (S.mono (Nat.le_add_right d k₂))
    have hpair : (S.slotRound (d + k₁), S.leader (d + k₁))
        = (S.slotRound (d + k₂), S.leader (d + k₂)) := by
      have : S.slotRound (d + k₁) = S.slotRound (d + k₂) := by omega
      rw [this, hl]
    have := S.keyed hpair
    omega

@[simp]
theorem Slots.chop_slotRound (S : Slots Validator) {d : ℕ}
    (hd : G ≤ S.slotRound d) (k : ℕ) :
    (S.chop G d hd).slotRound k = S.slotRound (d + k) - G := rfl

@[simp]
theorem Slots.chop_leader (S : Slots Validator) {d : ℕ}
    (hd : G ≤ S.slotRound d) (k : ℕ) :
    (S.chop G d hd).leader k = S.leader (d + k) := rfl

variable [S : Slots Validator] {d : ℕ}

/-- Every slot from the base slot on clears the horizon. -/
theorem horizon_le_slotRound (hd : G ≤ S.slotRound d) (k : ℕ) :
    G ≤ S.slotRound (d + k) :=
  hd.trans (S.mono (Nat.le_add_right d k))

/-! ## Where the rest of this file went

`isLeaderBlock_chop` and seven more transport lemmas stood here, and
above them G3 — `decided_chop`, both directions by structural induction
over the decision relation — and G4, cross-cut agreement. All of it is
now `Properties/Arcs/GC.lean`: `decided_chop_iff` and
`decided_agree_chop` are the same statements, reached from `Banded` and
`Agree` for any rule with a band, and `truncates_chop` is the witness
that the cut stands in the relation they read.

What stays here is the *construction* — `chop`, `Slots.chop`,
`View.chop` and the facts relating their fields — which the witness
needs and which no property can supply. After this file no theorem of
the garbage-collection mechanism mentions `Decided`.

`docs/target-properties.md` §11.4c records why the duplicates went: two
proofs of one statement is redundancy rather than a cross-check, since
Lean already guarantees the types agree. -/

end LeanDag
