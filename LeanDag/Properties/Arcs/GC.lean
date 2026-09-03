import LeanDag.Properties.Truncate
import LeanDag.Properties.Sustain
import LeanDag.GC.Chop
import LeanDag.MysticetiProperties

/-!
# Garbage collection, for any protocol with `LocalTruncate`

`docs/target-properties.md` G2, the garbage-collection half.

**This file is thin on purpose, and it was not always going to be.** An
earlier version composed a locality property with a re-indexing one and
looked like it was doing work; the composition had hypotheses nothing
could satisfy, because restriction and renumbering are not separately
realisable (`Properties/Truncate.lean` records why). What replaced it
is a single property, so garbage collection *is* that property applied,
and the two corollaries below are the directions a deployment uses.

The depth sits in the per-protocol proof of `LocalTruncate`: one
induction, paid once, serving every horizon and every base slot.
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
    (hv : ViewTruncates R V V' G) {k : ℕ} {v : Option BlockId}
    (hd : R.Decided S V (d + k) v) : R.Decided S' V' k v :=
  (h S S' U U' G d ht V V' hv k v).mp hd

/-- **And a verdict of the truncation is a verdict of the whole DAG**,
which is what lets a pruned replica be compared with one that never
pruned. -/
theorem decided_of_truncated (h : LocalTruncate R) (ht : Truncates R U U' S S' G d)
    (hv : ViewTruncates R V V' G) {k : ℕ} {v : Option BlockId}
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

end Arcs

end Properties

end LeanDag
