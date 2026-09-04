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
parents, so it needs `1 < m`. Both are supplied at every use site —
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
variable {S S' : LeanDag.Hydrozoan.Slots Replica} {G d : ℕ}

/-! ## The dead end -/

/-- A pure renumbering: every block kept, every round lower by `G`. -/
structure NaiveShift (U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (G : ℕ) :
    Prop where
  mem : ∀ b, b ∈ U.ids ↔ b ∈ U'.ids
  round : ∀ b, b ∈ U.ids → (U'.block b).round + G = (U.block b).round
  parents : ∀ b, b ∈ U.ids → (U'.block b).parents = (U.block b).parents

/-- A block at round zero has no parents: the predecessor condition is
unsatisfiable there. -/
theorem parents_empty_of_round_zero {b : BlockId} (hb : b ∈ U.ids)
    (hr : (U.block b).round = 0) : (U.block b).parents = ∅ := by
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
  have hparU : (U.block b).parents = ∅ := by
    rw [← h.parents b hbU]; exact parents_empty_of_round_zero hb hr
  have hqq := (U.valid b hbU).quorum (by omega)
  simp only [LeanDag.Hydrozoan.authors, LeanDag.Hydrozoan.authorsOf, hparU,
    Finset.image_empty, Finset.card_empty, Nat.le_zero] at hqq
  omega

/-! ## The relation that does have models -/

/-- The truncation, in Hydrozoan's vocabulary. -/
structure TruncatesHZ (U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (S S' : LeanDag.Hydrozoan.Slots Replica) (G d : ℕ) : Prop where
  mem : ∀ b, b ∈ U'.ids ↔ (b ∈ U.ids ∧ G ≤ (U.block b).round)
  round : ∀ b, b ∈ U'.ids → (U'.block b).round + G = (U.block b).round
  author : ∀ b, b ∈ U'.ids → (U'.block b).author = (U.block b).author
  parents : ∀ b, b ∈ U'.ids → 0 < (U'.block b).round →
    (U'.block b).parents = (U.block b).parents
  slotRound : ∀ k, S'.slotRound k + G = S.slotRound (d + k)
  leader : ∀ k, S'.leader k = S.leader (d + k)
  base : G ≤ S.slotRound d

namespace TruncatesHZ

theorem memU (h : TruncatesHZ U U' S S' G d) {b : BlockId} (hb : b ∈ U'.ids) :
    b ∈ U.ids := ((h.mem b).mp hb).1

theorem roundU (h : TruncatesHZ U U' S S' G d) {b : BlockId} (hb : b ∈ U'.ids) :
    (U.block b).round = (U'.block b).round + G := (h.round b hb).symm

/-- **Verdict transport across the cut**, in Hydrozoan's own schedule
vocabulary. Was two inductions over the six constructors with a family
of shifted transport lemmas beneath them, about 380 lines. The band now
carries an offset (`Properties.AgreeBand`), so a truncation is one of
its instances and reading it backwards is another, and both directions
of this are `banded_aux` applied. -/
theorem decided_iff (h : TruncatesHZ U U' S S' G d)
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ U.ids → G ≤ (U.block b).round → (b ∈ V.ids ↔ b ∈ V'.ids))
    {k : ℕ} {v : Option BlockId} :
    LeanDag.Hydrozoan.Decided (S := S) U V (d + k) v ↔
      LeanDag.Hydrozoan.Decided (S := S') U' V' k v := by
  have hbase : G ≤ S.slotRound d := h.base
  have hdk : G ≤ S.slotRound (d + k) := le_trans hbase (S.mono (Nat.le_add_right d k))
  constructor
  · intro hdec
    obtain ⟨top, -, htop⟩ := banded_aux (S := S) hdec
    refine htop 0 G d 0 S' U' V' k (by omega) ?_ ?_ ?_ ?_
    · intro m m' hm
      have hmm : m = m' + d := by omega
      subst hmm
      have := h.slotRound m'
      have hc : d + m' = m' + d := by omega
      rw [hc] at this; omega
    · intro m m' hm _
      have hmm : m = m' + d := by omega
      subst hmm
      have hc : m' + d = d + m' := by omega
      rw [hc]; exact (h.leader m').symm
    · refine ⟨?_, ?_, ?_⟩
      · intro b hb h1 h2
        have hlink : (rule.block U b).round = (U.block b).round := rfl
        exact (h.mem b).mpr ⟨hb, by omega⟩
      · intro b hb hband
        have hlink : (rule.block U b).round = (U.block b).round := rfl
        have hlink' : (rule.block U' b).round = (U'.block b).round := rfl
        have hbU' : b ∈ U'.ids := by
          rcases hband with ⟨h1, h2⟩ | ⟨hm, -, -⟩
          · exact (h.mem b).mpr ⟨hb, by omega⟩
          · exact hm
        exact ⟨by have := h.round b hbU'; omega, h.author b hbU'⟩
      · intro b hb h1 h2
        have hlink : (rule.block U b).round = (U.block b).round := rfl
        have hbU' : b ∈ U'.ids := (h.mem b).mpr ⟨hb, by omega⟩
        exact h.parents b hbU' (by have := h.round b hbU'; omega)
    · intro b hbV h1 h2
      have hlink : (rule.block U b).round = (U.block b).round := rfl
      exact (hv b (V.subset_ids hbV) (by omega)).mp hbV
  · intro hdec
    obtain ⟨top, -, htop⟩ := banded_aux (S := S') hdec
    refine htop G 0 0 d S U V (d + k) (by omega) ?_ ?_ ?_ ?_
    · intro m m' hm
      have hmm : m' = m + d := by omega
      subst hmm
      have := h.slotRound m
      have hc : d + m = m + d := by omega
      rw [hc] at this; omega
    · intro m m' hm _
      have hmm : m' = m + d := by omega
      subst hmm
      have hc : m + d = d + m := by omega
      rw [hc]; exact h.leader m
    · refine ⟨?_, ?_, ?_⟩
      · intro b hb h1 h2
        exact h.memU hb
      · intro b hb hband
        have hlink : (rule.block U' b).round = (U'.block b).round := rfl
        have hlink' : (rule.block U b).round = (U.block b).round := rfl
        have := h.round b hb
        exact ⟨by omega, (h.author b hb).symm⟩
      · intro b hb h1 h2
        have hlink : (rule.block U' b).round = (U'.block b).round := rfl
        have hr := h.round b hb
        exact (h.parents b hb (by omega)).symm
    · intro b hbV h1 h2
      have hbU' : b ∈ U'.ids := V'.subset_ids hbV
      have hlink : (rule.block U' b).round = (U'.block b).round := rfl
      exact (hv b (h.memU hbU') (by have := h.round b hbU'; omega)).mpr hbV

end TruncatesHZ

end Hydrozoan

end LeanDag
