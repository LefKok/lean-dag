import LeanDag.Properties.Truncate
import LeanDag.Properties.Sustain

/-!
# Transport composes

`docs/target-properties.md` §11.3, the third part of the goal: the
mechanisms compose with one another through the properties,
automatically.

**What a mechanism owes is a rebase** (`Properties/Carrier.lean`): above
a settling round the transformed DAG holds the same blocks, at rounds
some offset apart, with the same authors and — strictly above — the same
references. A validator that runs two mechanisms has applied two
rebases, and the whole claim of this file is that two rebases are one.

The arithmetic is the content. Offsets add; the settling round of the
composite is the higher of the two, **read in the source's frame**, so
the second mechanism's round has the first's offset added to it before
the comparison. Get that wrong and the composite claims agreement over a
band the second mechanism never promised.

`Extends.trans` is the same fact for the relation that adds blocks
rather than moving them, and it lives beside `Extends`; these live here
because the offset is what makes them worth stating together.

**The consumer is `Integration/Stack.lean`**, which transports honest
non-equivocation, coverage and production across a fill followed by a
cut, one lemma per invariant. `sustains_stack` there is this file
applied, and the reactive commit crossing the whole stack is what it
buys that the hand-written chain did not have.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

namespace RebasedAbove

/-- **Two rebases are one.** The offsets add. The settling round is the
later of the two in `U`'s frame: `R₂` is a round of `U'`, so it is
compared against `R₁` only after `G₁` is added back. -/
theorem trans {U U' U'' : R.Universe} {G₁ R₁ G₂ R₂ : ℕ}
    (h : RebasedAbove R U U' G₁ R₁) (h' : RebasedAbove R U' U'' G₂ R₂) :
    RebasedAbove R U U'' (G₁ + G₂) (max R₁ (R₂ + G₁)) where
  mem := fun b => by
    constructor
    · rintro ⟨hb, hr⟩
      have h1 := (h.mem b).mp ⟨hb, le_trans (le_max_left _ _) hr⟩
      have hro := h.round b hb (le_trans (le_max_left _ _) hr)
      have h2 := (h'.mem b).mp ⟨h1.1, by have := le_max_right R₁ (R₂ + G₁); omega⟩
      have hro' := h'.round b h1.1 (by omega)
      exact ⟨h2.1, by omega⟩
    · rintro ⟨hb, hr⟩
      have h2 := (h'.mem b).mpr ⟨hb, by omega⟩
      have hro' := h'.round b h2.1 h2.2
      have h1 := (h.mem b).mpr ⟨h2.1, by omega⟩
      exact ⟨h1.1, by have := h.round b h1.1 h1.2; omega⟩
  round := fun b hb hr => by
    have h1 := (h.mem b).mp ⟨hb, le_trans (le_max_left _ _) hr⟩
    have hro := h.round b hb (le_trans (le_max_left _ _) hr)
    have hro' := h'.round b h1.1 (by have := le_max_right R₁ (R₂ + G₁); omega)
    omega
  creator := fun b hb hr => by
    have h1 := (h.mem b).mp ⟨hb, le_trans (le_max_left _ _) hr⟩
    have hro := h.round b hb (le_trans (le_max_left _ _) hr)
    rw [h'.creator b h1.1 (by have := le_max_right R₁ (R₂ + G₁); omega)]
    exact h.creator b hb (le_trans (le_max_left _ _) hr)
  refs := fun b hb hr => by
    have h1 := (h.mem b).mp ⟨hb, le_of_lt (lt_of_le_of_lt (le_max_left _ _) hr)⟩
    have hro := h.round b hb (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hr))
    rw [h'.refs b h1.1 (by have := le_max_right R₁ (R₂ + G₁); omega)]
    exact h.refs b hb (lt_of_le_of_lt (le_max_left _ _) hr)

/-- A mechanism that rebases from a round rebases from any later one,
which is what lets two settling rounds be compared at all. -/
theorem mono {U U' : R.Universe} {G R₀ R₁ : ℕ}
    (h : RebasedAbove R U U' G R₀) (hR : R₀ ≤ R₁) : RebasedAbove R U U' G R₁ where
  mem := fun b => by
    constructor
    · rintro ⟨hb, hr⟩
      have hm := (h.mem b).mp ⟨hb, le_trans hR hr⟩
      exact ⟨hm.1, by have := h.round b hb (le_trans hR hr); omega⟩
    · rintro ⟨hb, hr⟩
      have hm := (h.mem b).mpr ⟨hb, le_trans hR hr⟩
      exact ⟨hm.1, by have := h.round b hm.1 hm.2; omega⟩
  round := fun b hb hr => h.round b hb (le_trans hR hr)
  creator := fun b hb hr => h.creator b hb (le_trans hR hr)
  refs := fun b hb hr => h.refs b hb (lt_of_le_of_lt hR hr)

/-- Doing nothing rebases by nothing, from round zero. -/
theorem refl {U : R.Universe} : RebasedAbove R U U 0 0 where
  mem := fun _ => by simp
  round := fun _ _ _ => rfl
  creator := fun _ _ _ => rfl
  refs := fun _ _ _ => rfl

end RebasedAbove

namespace Rebases

variable {S S' S'' : Slots Validator} {G₁ d₁ G₂ d₂ : ℕ}

/-- **And two schedule rebases are one.** Offsets and base slots both
add, which is what makes a stack of truncations a truncation. -/
theorem trans (h : Rebases S S' G₁ d₁) (h' : Rebases S' S'' G₂ d₂) :
    Rebases S S'' (G₁ + G₂) (d₁ + d₂) where
  slotRound := fun k => by
    have h1 := h.slotRound (d₂ + k)
    have h2 := h'.slotRound k
    have e : d₁ + (d₂ + k) = d₁ + d₂ + k := by omega
    rw [e] at h1; omega
  leader := fun k => by
    have e : d₁ + (d₂ + k) = d₁ + d₂ + k := by omega
    rw [h'.leader k, h.leader (d₂ + k), e]
  base := by
    have h1 := h.slotRound d₂
    have h2 := h'.base
    omega

end Rebases

/-- **A stack of truncations is a truncation.** Both halves compose, and
the settling round of the composite is `G₁ + G₂` because a cut settles at
its own horizon. -/
theorem Truncates.trans {U U' U'' : R.Universe} {S S' S'' : Slots Validator}
    {G₁ d₁ G₂ d₂ : ℕ} (h : Truncates R U U' S S' G₁ d₁)
    (h' : Truncates R U' U'' S' S'' G₂ d₂) :
    Truncates R U U'' S S'' (G₁ + G₂) (d₁ + d₂) :=
  { (h.toRebasedAbove.trans h'.toRebasedAbove).mono
      (by omega : max G₁ (G₂ + G₁) ≤ G₁ + G₂),
    h.toRebases.trans h'.toRebases with }

end Properties

end LeanDag
