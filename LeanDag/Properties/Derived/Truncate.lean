import LeanDag.Properties.Truncate
import LeanDag.Properties.Witness

/-!
# Truncation invariance

`docs/target-properties.md` §3.4b. No longer an obligation: it follows
from the band, once the band carries an offset.

A truncation moves rounds, and the band once compared them by equality,
which is why this was a separate obligation for as long as it was. With
`AgreeBand` reading both universes in a common frame, a cut is the
instance `g = 0`, `g' = G`, and reading it backwards is the instance
with the pairs swapped. Both directions of the `↔` are therefore
instances of one property, which is what the two offsets were for.

What the band was already right about is the horizon's references: its
clause is guarded strictly above the floor, which is exactly the licence
a cut needs when it empties its bottom layer.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **Truncation invariance.** A replica that has pruned below the
horizon reaches exactly the verdicts it would have reached with its
whole history, at its own numbering.

An `↔`, because both directions are consumed: a joiner needs verdicts
to survive the cut, and cross-cut agreement needs them to come back. -/
def LocalTruncate (R : DagRule Validator BlockId Payload) : Prop :=
  ∀ (S S' : Slots Validator) (U U' : R.Universe) (G d : ℕ),
    Truncates R U U' S S' G d →
    ∀ (V : R.View U) (V' : R.View U'), ViewTruncates R V V' G →
    ∀ (k : ℕ) (v : Option BlockId), R.Decided S V (d + k) v ↔ R.Decided S' V' k v

/-- **Truncation invariance falls out of the band.** -/
theorem LocalTruncate.of_banded (hvs : ViewSound R) (h : Banded R) : LocalTruncate R := by
  intro S S' U U' G d ht V V' hv k v
  have hbase : G ≤ S.slotRound d := ht.base
  have hdk : G ≤ S.slotRound (d + k) := le_trans hbase (S.mono (Nat.le_add_right d k))
  constructor
  · intro hdec
    obtain ⟨top, htop⟩ := h S U V (d + k) v hdec
    refine htop 0 G d 0 S' U' V' k (by omega) ?_ ?_ ?_ ?_
    · intro m m' hm
      have hmm : m = m' + d := by omega
      subst hmm
      have := ht.slotRound m'
      have hc : d + m' = m' + d := by omega
      rw [hc] at this
      omega
    · intro m m' hm _
      have hmm : m = m' + d := by omega
      subst hmm
      have hc : m' + d = d + m' := by omega
      rw [hc]
      exact (ht.leader m').symm
    · refine ⟨?_, ?_, ?_⟩
      · intro b hb h1 h2
        exact (ht.mem b).mpr ⟨hb, by omega⟩
      · intro b hb hband
        have hbU' : b ∈ R.ids U' := by
          rcases hband with ⟨h1, h2⟩ | ⟨hm, -, -⟩
          · exact (ht.mem b).mpr ⟨hb, by omega⟩
          · exact hm
        exact ⟨by have := ht.round b hbU'; omega, ht.creator b hbU'⟩
      · intro b hb h1 h2
        have hbU' : b ∈ R.ids U' := (ht.mem b).mpr ⟨hb, by omega⟩
        exact ht.refs b hbU' (by omega)
    · intro b hbV h1 h2
      exact (hv b (hvs V hbV) (by omega)).mp hbV
  · intro hdec
    obtain ⟨top, htop⟩ := h S' U' V' k v hdec
    refine htop G 0 0 d S U V (d + k) (by omega) ?_ ?_ ?_ ?_
    · intro m m' hm
      have hmm : m' = m + d := by omega
      subst hmm
      have := ht.slotRound m
      have hc : d + m = m + d := by omega
      rw [hc] at this
      omega
    · intro m m' hm _
      have hmm : m' = m + d := by omega
      subst hmm
      have hc : m + d = d + m := by omega
      rw [hc]
      exact ht.leader m
    · refine ⟨?_, ?_, ?_⟩
      · intro b hb h1 h2
        exact ((ht.mem b).mp hb).1
      · intro b hb hband
        have := ht.round b hb
        exact ⟨by omega, (ht.creator b hb).symm⟩
      · intro b hb h1 h2
        have hmem := (ht.mem b).mp hb
        have hr := ht.round b hb
        exact (ht.refs b hb (by omega)).symm
    · intro b hbV h1 h2
      have hbU' : b ∈ R.ids U' := hvs V' hbV
      have hmem := (ht.mem b).mp hbU'
      exact (hv b hmem.1 hmem.2).mpr hbV

end Properties

end LeanDag
