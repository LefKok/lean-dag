import LeanDag.Properties.Truncate
import LeanDag.Properties.Sustain
import LeanDag.GC.Chop
import LeanDag.GC.ChopDecided
import LeanDag.MysticetiProperties
import LeanDag.Properties.Witness
import LeanDag.Properties.Derived.Truncate

/-!
# Garbage collection, for any protocol with a band

`docs/target-properties.md` G2, the garbage-collection half.

**This file is thin on purpose, and it was not always going to be.** An
earlier version composed a locality property with a re-indexing one and
looked like it was doing work; the composition had hypotheses nothing
could satisfy, because restriction and renumbering are not separately
realisable (`Properties/Truncate.lean` records why). What replaced it
is a single statement, `LocalTruncate`, so garbage collection *is* that
statement applied, and the two corollaries below are the directions a
deployment uses.

A protocol no longer proves `LocalTruncate`. Once the band carries a
round offset, `Properties.LocalTruncate.of_banded` derives it from
`Banded` and `ViewSound`, so the depth sits in the band a protocol was
already proving for persistence and locality. What a mechanism still
owes is the witness that its cut stands in the `Truncates` relation.
-/

namespace LeanDag

namespace Properties

namespace Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}
variable {S S' : Slots Validator} {U U' : R.Universe} {G d : ℕ}
variable {V : R.View U} {V' : R.View U'}

/-- **A verdict survives the cut**, at the replica's own numbering. -/
theorem decided_of_truncate (h : LocalTruncate R) (ht : Truncates R U U' S S' G d)
    (hv : ViewAgreeAbove R V V' G) {k : ℕ} {v : Option BlockId}
    (hd : R.Decided S V (d + k) v) : R.Decided S' V' k v :=
  (h S S' U U' G d ht V V' hv k v).mp hd

/-- **And a verdict of the truncation is a verdict of the whole DAG**,
which is what lets a pruned replica be compared with one that never
pruned. -/
theorem decided_of_truncated (h : LocalTruncate R) (ht : Truncates R U U' S S' G d)
    (hv : ViewAgreeAbove R V V' G) {k : ℕ} {v : Option BlockId}
    (hd : R.Decided S' V' k v) : R.Decided S V (d + k) v :=
  (h S S' U U' G d ht V V' hv k v).mpr hd

/-! ## The liveness half, for the core

Garbage collection is a mechanism, so on the liveness side it *owes*
`Sustains` rather than consuming it, and the core's carrier is where the
obligation can be discharged against a real consumer. This section
imports the mechanism it is about and the protocol it serves, and no
other mechanism. -/

section Core

variable [Faults Validator] {U : BlockUniverse Validator BlockId Payload} {G : ℕ}

/-- **The cut sustains the core from its horizon.** -/
theorem sustains_chop :
    Sustains (MysticetiProperties.mysticetiRule (Payload := Payload)) U (chop U G) G G where
  mem := fun b => by
    show (b ∈ U.ids ∧ G ≤ (U.block b).round) ↔
      (b ∈ (chop U G).ids ∧ G ≤ ((chop U G).block b).round + G)
    rw [mem_chop_ids, chop_block_eq, chopBlock_round]
    constructor
    · rintro ⟨hb, hr⟩
      refine ⟨⟨hb, hr⟩, ?_⟩
      rw [Nat.sub_add_cancel hr]; exact hr
    · rintro ⟨⟨hb, hr⟩, _⟩; exact ⟨hb, hr⟩
  round := fun b _ hr => by
    have hr' : G ≤ (U.block b).round := hr
    show ((chop U G).block b).round + G = (U.block b).round
    rw [chop_block_eq, chopBlock_round]; omega
  creator := fun b _ _ => by
    show ((chop U G).block b).creator = (U.block b).creator
    rw [chop_block_eq, chopBlock_creator]
  refs := fun b _ hr => by
    show ((chop U G).block b).refs = (U.block b).refs
    rw [chop_block_eq, chopBlock_refs_of_lt hr]

/-- **The reactive commit survives the cut** — the consumer test, from
the obligation rather than from `chop` directly. -/
theorem directCommit_chop {T : Finset Validator} {r : ℕ} {L : BlockId}
    (hr : G ≤ r) (hcard : quorumCard Validator ≤ T.card)
    (hpop : LeanDag.PopulatedOn U T (r + 2)) (hc : CertifiesAt U T r L) :
    DirectCommit (chop U G) L (r - G) :=
  MysticetiProperties.directCommit_of_sustains sustains_chop hr hr hcard hpop hc

end Core


/-! ## The canonical cut is a truncation, and the arc's theorems follow

With the band carrying an offset, truncation invariance is no longer an
obligation: `Properties.LocalTruncate.of_banded` derives it for any rule
with a band. What is left for this file is the **witness** — that the
cut the mechanism builds stands in the `Truncates` relation — and the
observation that the arc's own two transport theorems come back out of
the property with no induction.

That is the consumer test the arc asks for, and it measures what the
offset removed: `GC/ChopDecided.lean` proves those two by structural
induction over the decision relation, and here they are again, from a
property proved once for other reasons. -/

section CoreTruncate

variable [Faults Validator] {U : BlockUniverse Validator BlockId Payload}
variable {S : Slots Validator} {G d : ℕ}

/-- **The cut is a truncation.** The witness `Truncates` was written to
have, exhibited before anything is proved from it. -/
theorem truncates_chop (hd : G ≤ S.slotRound d) :
    Truncates (MysticetiProperties.mysticetiRule (Payload := Payload))
      U (chop U G) S (S.chop G d hd) G d where
  mem := fun b => by
    show (b ∈ U.ids ∧ G ≤ (U.block b).round) ↔
      (b ∈ (chop U G).ids ∧ G ≤ ((chop U G).block b).round + G)
    rw [mem_chop_ids, chop_block_eq, chopBlock_round]
    constructor
    · rintro ⟨hb, hr⟩; exact ⟨⟨hb, hr⟩, by omega⟩
    · rintro ⟨⟨hb, hr⟩, -⟩; exact ⟨hb, hr⟩
  round := fun b hb hr => by
    have hr' : G ≤ (U.block b).round := hr
    show ((chop U G).block b).round + G = (U.block b).round
    rw [chop_block_eq, chopBlock_round]; omega
  creator := fun b _ _ => by
    show ((chop U G).block b).creator = (U.block b).creator
    rw [chop_block_eq, chopBlock_creator]
  refs := fun b _ hr => by
    show ((chop U G).block b).refs = (U.block b).refs
    rw [chop_block_eq, chopBlock_refs_of_lt hr]
  slotRound := fun k => by
    have := horizon_le_slotRound hd k
    show S.slotRound (d + k) - G + G = S.slotRound (d + k)
    omega
  leader := fun _ => rfl
  base := hd

/-- **G3 re-derived, with no induction of its own.** Both directions of
the cut's verdict transport, from the band. -/
theorem decided_chop_iff (hd : G ≤ S.slotRound d)
    {V : View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId} :
    Decided U V (d + k) v ↔ Decided (S := S.chop G d hd) (chop U G) (V.chop G) k v :=
  LocalTruncate.of_banded MysticetiProperties.banded
    S (S.chop G d hd) U (chop U G) G d (truncates_chop hd) V (V.chop G)
    (fun b hb hr => by
      show b ∈ V.ids ↔ b ∈ (V.chop G).ids
      rw [View.chop_ids, Finset.mem_filter]
      exact ⟨fun h => ⟨h, hr⟩, fun h => h.1⟩) k v

end CoreTruncate


end Arcs

end Properties

end LeanDag
