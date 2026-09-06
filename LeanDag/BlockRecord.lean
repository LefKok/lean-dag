import LeanDag.Block

/-!
# The block record

**One universe shape for every rule.** A universe is a set of
identifiers, a block map, closure under references, validity of every
block against a rule's own predicate, and one block per author per
round for the authors the rule's fault model constrains. The core, Nemo
and FinWhale *are* this record at their own validity predicate and
honest set; Hydrozoan is it through its block adapter
(`Hydrozoan/Helpers/Record.lean`); Orcaella and Optimal-Hydrozoan are a
neighbour's record under one further invariant.

**What a validity predicate owes the mechanisms** is `Validity.Mechanised`:
references sit one round below, the predicate reads only referenced
blocks, a reference-free round-zero block is valid, and validity
survives the cut strictly above the horizon. With those four facts the
cut (`Record/Chop.lean`), the fill (`Record/Fill.lean`) and re-genesis
(`Record/Genesis.lean`) are built once, and a rule's mechanism cell is
the generic construction at its instance. A predicate that does not
read the author (`Validity.CopyStable`) also gets the copy fill's
validity for free; the core's fill adds a self reference for its
self-parent clause and proves that block valid itself.

The block-level cut `chopBlk` lives here because it is what the
`chops` obligation is stated against.
-/

namespace LeanDag

variable {Validator : Type*} {BlockId : Type*} {Payload : Type*}

/-- A validity predicate: what a rule asks of one block, read against
the block map. -/
abbrev Validity (Validator BlockId Payload : Type*) :=
  (BlockId → Block Validator BlockId Payload) → Block Validator BlockId Payload → Prop

/-- **The block record**: every universe type in the development, at a
validity predicate `P` and an honest set. `block` is total, with junk
outside `ids`; every clause quantifies over `i ∈ ids`, so the junk is
never observed. -/
structure BlockRecord (Validator BlockId Payload : Type*)
    (P : Validity Validator BlockId Payload) (honest : Finset Validator) where
  /-- Which blocks exist. -/
  ids : Finset BlockId
  /-- What each id denotes. -/
  block : BlockId → Block Validator BlockId Payload
  /-- Every referenced block is present. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (block i).refs, j ∈ ids
  /-- Every block present is valid. -/
  valid : ∀ i ∈ ids, P block (block i)
  /-- An honest author has at most one block per round. -/
  no_equivocation : ∀ i ∈ ids, ∀ j ∈ ids,
    (block i).creator ∈ honest →
    (block i).creator = (block j).creator →
    (block i).round = (block j).round → i = j

namespace BlockRecord

variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-- **A view**: a reference-closed part of the universe. Views share
`U.block`, so they disagree about *which* blocks they hold, never about
what an id denotes. -/
structure View (U : BlockRecord Validator BlockId Payload P honest) where
  /-- The ids this validator holds. -/
  ids : Finset BlockId
  /-- A view holds only blocks that exist. -/
  subset_ids : ids ⊆ U.ids
  /-- A view is closed under references. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (U.block i).refs, j ∈ ids

variable {U : BlockRecord Validator BlockId Payload P honest}

/-- Completeness, as a subset statement. -/
theorem refs_subset {i : BlockId} (hi : i ∈ U.ids) : (U.block i).refs ⊆ U.ids :=
  fun _ hj => U.complete i hi _ hj

end BlockRecord

/-! ## The cut, over raw block data

The *data* of a cut is the same for every rule: the round is rebased by
`−G`, and blocks at or below the cut — the new base layer, plus junk —
lose their references. -/

section Chop

variable {G : ℕ} {i : BlockId} {blk : BlockId → Block Validator BlockId Payload}

/-- One block of the truncation, over the raw block assignment. -/
def chopBlk (blk : BlockId → Block Validator BlockId Payload) (G : ℕ)
    (i : BlockId) : Block Validator BlockId Payload :=
  if (blk i).round ≤ G then
    { blk i with round := (blk i).round - G, refs := ∅ }
  else
    { blk i with round := (blk i).round - G }

@[simp] theorem chopBlk_creator :
    (chopBlk blk G i).creator = (blk i).creator := by unfold chopBlk; split <;> rfl

@[simp] theorem chopBlk_round :
    (chopBlk blk G i).round = (blk i).round - G := by unfold chopBlk; split <;> rfl

@[simp] theorem chopBlk_payload :
    (chopBlk blk G i).payload = (blk i).payload := by unfold chopBlk; split <;> rfl

theorem chopBlk_refs_of_le
    (h : (blk i).round ≤ G) : (chopBlk blk G i).refs = ∅ := by
  unfold chopBlk; rw [if_pos h]

theorem chopBlk_refs_of_lt
    (h : G < (blk i).round) : (chopBlk blk G i).refs = (blk i).refs := by
  unfold chopBlk; rw [if_neg (by omega)]

theorem chopBlk_of_lt (h : G < (blk i).round) :
    chopBlk blk G i = { blk i with round := (blk i).round - G } := by
  unfold chopBlk; rw [if_neg (by omega)]

theorem chopBlk_refs_subset : (chopBlk blk G i).refs ⊆ (blk i).refs := by
  rcases Nat.lt_or_ge G (blk i).round with h | h
  · rw [chopBlk_refs_of_lt h]
  · rw [chopBlk_refs_of_le h]; exact Finset.empty_subset _

theorem creatorsOf_chopBlk [DecidableEq Validator] (s : Finset BlockId) :
    creatorsOf (chopBlk blk G) s = creatorsOf blk s := by
  simp only [creatorsOf, chopBlk_creator]

end Chop

/-! ## What a validity predicate owes -/

namespace Validity

variable (P : Validity Validator BlockId Payload)

/-- **The four facts the mechanisms consume of a validity predicate.**
Every predicate in the development has them; a rule proves them once and
its cut, fill and re-genesis are the generic constructions. -/
class Mechanised : Prop where
  /-- References sit one round below. -/
  pred : ∀ (blk : BlockId → Block Validator BlockId Payload) (b : Block Validator BlockId Payload),
    P blk b → ∀ j ∈ b.refs, (blk j).round + 1 = b.round
  /-- Validity reads only referenced blocks: two maps agreeing on a
  reference-closed set holding `b`'s references judge `b` alike. -/
  reads : ∀ (blk blk' : BlockId → Block Validator BlockId Payload) (ids : Finset BlockId)
    (b : Block Validator BlockId Payload),
    (∀ i ∈ ids, ∀ j ∈ (blk i).refs, j ∈ ids) → (∀ j ∈ b.refs, j ∈ ids) →
    (∀ j ∈ ids, blk' j = blk j) → P blk b → P blk' b
  /-- A reference-free block at round zero is valid. -/
  base : ∀ (blk : BlockId → Block Validator BlockId Payload) (b : Block Validator BlockId Payload),
    b.round = 0 → b.refs = ∅ → P blk b
  /-- Validity survives the cut strictly above the horizon. -/
  chops : ∀ (blk : BlockId → Block Validator BlockId Payload) (G : ℕ)
    (b : Block Validator BlockId Payload),
    P blk b → G < b.round → P (chopBlk blk G) { b with round := b.round - G }

/-- **The author is not read.** What the copy fill needs: a rule with no
self-parent clause judges a re-authored block as it judged the original. -/
class CopyStable : Prop where
  copy : ∀ (blk : BlockId → Block Validator BlockId Payload) (b : Block Validator BlockId Payload)
    (v : Validator), P blk b → P blk { b with creator := v }

end Validity

end LeanDag
