import LeanDag.Hydrozoan.Helpers.Banded
import LeanDag.Properties.Truncate

/-!
# Hydrozoan's rules across a truncation

Not part of the audit surface. The transfer lemmas
`Properties.LocalTruncate` needs of this protocol: a truncation prunes
below a horizon **and** renumbers what remains from it, and every
predicate Hydrozoan reads moves by the horizon exactly once.

**The guards read cleanly in the truncation's own numbering.** A block
of the truncation at round `m` sits at round `m + G` in the original, so
the horizon guard `G < round` becomes `0 < m`: the block is not in the
retained bottom layer. A certificate counts votes cast by its own
refs, so it needs `1 < m`. Both are supplied at every use site —
votes sit one round above a slot and certificates two, so in the
truncation's numbering they are at `slotRound k + 1 ≥ 1` and
`slotRound k + 2 ≥ 2`.

**The dead end, kept as a record.** `no_base_of_naive_shift` below is
why this file states one relation rather than two. A *pure* renumbering
— every block kept, every round lower by `G` — puts the bottom layer at
round zero carrying the references it had at round `G`, and validity
allows a round-zero block none. Any non-empty valid universe has a
round-zero block, by descending the predecessor condition from any block
at all. So a pure shift by a positive horizon has no non-empty model,
and a property quantified over such shifts is vacuous. Only the
combination below has models.
-/

namespace LeanDag

namespace Hydrozoan

open LeanDag.Properties

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]
variable {U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
variable {S S' : LeanDag.Slots Replica} {G d : ℕ}

/-! ## The dead end -/

/-- A pure renumbering: every block kept, every round lower by `G`. -/
structure NaiveShift (U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (G : ℕ) :
    Prop where
  mem : ∀ b, b ∈ U.ids ↔ b ∈ U'.ids
  round : ∀ b, b ∈ U.ids → (U'.block b).round + G = (U.block b).round
  refs : ∀ b, b ∈ U.ids → (U'.block b).refs = (U.block b).refs

/-- A block at round zero has no refs: the predecessor condition is
unsatisfiable there. -/
theorem refs_empty_of_round_zero {b : BlockId} (hb : b ∈ U.ids)
    (hr : (U.block b).round = 0) : (U.block b).refs = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  have := (U.valid b hb).predecessor j hj
  omega

/-- **A pure shift by a positive horizon admits no round-zero block**,
and a non-empty valid universe must have one. So the naive factoring of
a truncation into a restriction and a renumbering has no models, and a
property quantified over it is vacuously true. -/
theorem no_base_of_naive_shift (h : NaiveShift U U' G) (hG : 0 < G)
    (hq : 0 < LeanDag.Hydrozoan.q Replica)
    (b : BlockId) (hb : b ∈ U'.ids) : (U'.block b).round ≠ 0 := by
  intro hr
  have hbU : b ∈ U.ids := (h.mem b).mpr hb
  have hround : (U.block b).round = G := by have := h.round b hbU; omega
  have hparU : (U.block b).refs = ∅ := by
    rw [← h.refs b hbU]; exact refs_empty_of_round_zero hb hr
  have hqq := (U.valid b hbU).quorum (by omega)
  simp only [LeanDag.creators, LeanDag.creatorsOf, hparU,
    Finset.image_empty, Finset.card_empty, Nat.le_zero] at hqq
  omega

/-! ## The relation that does have models

`Properties.Truncates`, in `Properties/Truncate.lean`. This file used to
hold a Hydrozoan copy of it, `TruncatesHZ`, field for field, and a
`decided_iff` that re-proved `Properties.LocalTruncate.of_banded` in
Hydrozoan's own vocabulary. Both are gone: the generic relation is
stated over `rule`, whose projections are Hydrozoan's by `rfl`, and
`Integration/Hydrozoan/ViaProperties.lean` exhibits the cut as a witness
for it directly. -/

end Hydrozoan

end LeanDag
