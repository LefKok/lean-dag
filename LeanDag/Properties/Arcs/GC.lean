import LeanDag.Properties.Truncate
import LeanDag.Properties.Sustain
import LeanDag.GC.Chop
import LeanDag.GC.ChopDecided
import LeanDag.MysticetiProperties
import LeanDag.Properties.Witness

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


/-! ## The core's `LocalTruncate`, from the cut and the band

The last obligation the core was short of, and it lives here rather than
in `MysticetiProperties.lean` because half of it is the mechanism's.

The split is worth naming. `GC/ChopDecided.lean` already proves both
directions for the **canonical** truncation, the one `chop` builds. What
`LocalTruncate` asks for is any universe standing in the `Truncates`
relation, and the gap between the two is pure agreement: such a universe
holds exactly the blocks `chop` holds, at exactly the rounds and authors
`chop` gives them, and above the horizon with the same references. So
the band carries verdicts between them, and the schedule clauses of
`Truncates` pin `S'` to be the chopped schedule outright.

**The offset the band does not need.** A band compares rounds by
equality, and a truncation moves them, so the natural thought is to give
`AgreeBand` an offset and derive `LocalTruncate` generically. That is a
real generalisation and it is not needed here: the *renumbering* is
already done by `chop`, and what remains between `chop U G` and an
arbitrary `Truncates` target is a shift of zero. The offset would buy a
generic derivation, at the cost of threading a shift through every band
lemma of every protocol; this buys the core's instance for thirty lines.
`LocalTruncate` therefore stays an obligation, and is now discharged by
both protocols. -/

section CoreTruncate

variable [Faults Validator] {U W : BlockUniverse Validator BlockId Payload}
variable {S S' : Slots Validator} {G d : ℕ}

/-- The schedule clauses of `Truncates` determine the schedule: it is
the chopped one, on the nose. -/
theorem slots_eq_chop (ht : Truncates (MysticetiProperties.mysticetiRule (Payload := Payload))
    U W S S' G d) (hbase : G ≤ S.slotRound d) : S' = S.chop G d hbase := by
  obtain ⟨sr, ld, hm, hu, hk⟩ := S'
  have h1 : sr = fun k => S.slotRound (d + k) - G := by
    funext m
    have := ht.slotRound m
    simp only at this
    omega
  have h2 : ld = fun k => S.leader (d + k) := funext ht.leader
  subst h1; subst h2
  rfl

/-- A `Truncates` target and the canonical cut agree on every band: the
same blocks, at the same rounds, with the same authors, and above the
horizon the same references. -/
theorem agreeBand_chop (ht : Truncates (MysticetiProperties.mysticetiRule (Payload := Payload))
    U W S S' G d) (lo hi : ℕ) :
    AgreeBand MysticetiProperties.mysticetiRule (chop U G) W lo hi ∧
      AgreeBand MysticetiProperties.mysticetiRule W (chop U G) lo hi := by
  have hmem : ∀ b, b ∈ (chop U G).ids ↔ b ∈ W.ids := by
    intro b
    rw [mem_chop_ids]
    exact (ht.mem b).symm
  have hround : ∀ b, b ∈ W.ids → ((chop U G).block b).round = (W.block b).round := by
    intro b hb
    have h1 : (W.block b).round + G = (U.block b).round := ht.round b hb
    have h2 : b ∈ U.ids ∧ G ≤ (U.block b).round := (ht.mem b).mp hb
    show (chopBlock U G b).round = (W.block b).round
    rw [chopBlock_round]; omega
  have hcr : ∀ b, b ∈ W.ids → ((chop U G).block b).creator = (W.block b).creator := by
    intro b hb
    have h1 : (W.block b).creator = (U.block b).creator := ht.creator b hb
    show (chopBlock U G b).creator = (W.block b).creator
    rw [chopBlock_creator]; exact h1.symm
  have hrefs : ∀ b, b ∈ W.ids → 0 < ((chop U G).block b).round →
      ((chop U G).block b).refs = (W.block b).refs := by
    intro b hb hpos
    have h1 : (W.block b).round + G = (U.block b).round := ht.round b hb
    have h2 : b ∈ U.ids ∧ G ≤ (U.block b).round := (ht.mem b).mp hb
    have hr : ((chop U G).block b).round = (U.block b).round - G := by
      show (chopBlock U G b).round = _; rw [chopBlock_round]
    have hgt : G < (U.block b).round := by omega
    have h3 : (W.block b).refs = (U.block b).refs := ht.refs b hb hgt
    show (chopBlock U G b).refs = (W.block b).refs
    rw [chopBlock_refs_of_lt hgt, h3]
  constructor
  · exact { mem := fun b hb _ _ => (hmem b).mp hb
            block := fun b hb hband => by
              have hb' : b ∈ W.ids := (hmem b).mp hb
              exact ⟨(hround b hb').symm, (hcr b hb').symm⟩
            refs := fun b hb h1 _ => by
              have hb' : b ∈ W.ids := (hmem b).mp hb
              have hlink : (MysticetiProperties.mysticetiRule.block (chop U G) b).round
                  = ((chop U G).block b).round := rfl
              exact (hrefs b hb' (by omega)).symm }
  · exact { mem := fun b hb _ _ => (hmem b).mpr hb
            block := fun b hb _ => ⟨hround b hb, hcr b hb⟩
            refs := fun b hb h1 _ => by
              have hlink : (MysticetiProperties.mysticetiRule.block W b).round
                  = (W.block b).round := rfl
              refine hrefs b hb ?_
              rw [hround b hb]; omega }

/-- **The core truncates locally.** A verdict at slot `d + k` of the
full DAG is a verdict at slot `k` of any truncation, and back. -/
theorem localTruncate : LocalTruncate
    (MysticetiProperties.mysticetiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) := by
  intro S S' U W G d ht V V' hv k v
  have hbase : G ≤ S.slotRound d := ht.base
  have hVeq : V'.ids = (V.chop G).ids := by
    ext b
    rw [View.chop_ids, Finset.mem_filter]
    constructor
    · intro hb
      have hbW : b ∈ W.ids := V'.subset_ids hb
      have h2 : b ∈ U.ids ∧ G ≤ (U.block b).round := (ht.mem b).mp hbW
      exact ⟨(hv b h2.1 h2.2).mpr hb, h2.2⟩
    · rintro ⟨hbV, hbr⟩
      exact (hv b (V.subset_ids hbV) hbr).mp hbV
  have hAB := fun lo hi => (agreeBand_chop ht lo hi).1
  have hBA := fun lo hi => (agreeBand_chop ht lo hi).2
  have hS := slots_eq_chop ht hbase
  subst hS
  constructor
  · intro h
    have h1 := decided_chop_of_decided hbase h k rfl
    obtain ⟨top, htop⟩ := MysticetiProperties.banded _ (chop U G) (V.chop G) k v h1
    refine htop _ W V' rfl (fun _ _ => rfl) (hAB _ _) (fun b hb _ _ => ?_)
    show b ∈ V'.ids
    rw [hVeq]; exact hb
  · intro h
    obtain ⟨top, htop⟩ := MysticetiProperties.banded _ W V' k v h
    have h1 := htop _ (chop U G) (V.chop G) rfl (fun _ _ => rfl) (hBA _ _)
      (fun b hb _ _ => show b ∈ (V.chop G).ids from by rw [← hVeq]; exact hb)
    exact decided_of_decided_chop hbase h1

end CoreTruncate

end Arcs

end Properties

end LeanDag
