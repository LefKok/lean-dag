import LeanDag.Quality.Inclusion
import LeanDag.Quality.Capstone
import LeanDagTest.DoS.Exclusion
import LeanDagTest.Quantitative

/-!
# Chain quality, witnessed

`chain-quality.md` §5, CQP0. Two models carry the whole story.

**`Ucens` — tightness and censorship in one universe.** Four validators
at `f = 1` (Byzantine `{0}`, so `Correct = {1,2,3}`); validators
`0, 1, 2` reference only each other, validator `3` builds validly —
self-parent plus two of the others — but is **never referenced by
anyone**. Slot 1 commits directly (leader block 13 at round 3, the full
certificate pattern present), and the committed cone misses author 3 at
**every** layer: `missingAt = {3}`, exactly `f` — CQ1's bound is tight —
and `coveredAt = {1,2}`, exactly `|Correct| − f`, which is still at
least half of `Correct` (CQ2 on data). Every validity, delivery and
liveness clause is satisfiable over this universe, and coverage
(`Synchronised`) fails at every round — commits recur while the same
correct validator is censored from every flush. Aggregate coverage is
not individual inclusion; this is why CQ6 needs `R`, exhibited.

**`Uexcl` — inclusion on data.** The synchronised model of the DoS arc:
CQ5 applied puts a correct round-1 block in the slot-1 commit's cone,
and the ledger membership is checked by `decide` against a concrete
verdict assignment.
-/

namespace LeanDagTest

open LeanDag

/-! ## The censorship model -/

/-- Six rounds of four: `{0,1,2}` reference each other; `3` self-parents
and references two of the others; nobody references `3`. -/
def censBlk : Fin 24 → Block (Fin 4) (Fin 24) Unit := fun i =>
  { round := (i : ℕ) / 4,
    creator := ⟨(i : ℕ) % 4, by omega⟩,
    refs :=
      if (i : ℕ) / 4 = 0 then ∅
      else if (i : ℕ) % 4 = 3 then
        { ⟨4 * ((i : ℕ) / 4 - 1) + 3, by have := i.isLt; omega⟩,
          ⟨4 * ((i : ℕ) / 4 - 1), by have := i.isLt; omega⟩,
          ⟨4 * ((i : ℕ) / 4 - 1) + 1, by have := i.isLt; omega⟩ }
      else
        { ⟨4 * ((i : ℕ) / 4 - 1), by have := i.isLt; omega⟩,
          ⟨4 * ((i : ℕ) / 4 - 1) + 1, by have := i.isLt; omega⟩,
          ⟨4 * ((i : ℕ) / 4 - 1) + 2, by have := i.isLt; omega⟩ },
    payload := () }

def Ucens : BlockUniverse (Fin 4) (Fin 24) Unit where
  ids := Finset.univ
  block := censBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- Slot 1 (round 3, leader 1): block 13, directly committed — the full
-- certificate pattern is present.
example : IsLeaderBlock Ucens 1 13 := by decide
example : DirectCommit Ucens 13 3 := by decide

theorem ucens_slot1 : Decided Ucens (View.full Ucens) 1 (some 13) :=
  Decided.directCommit (by decide) (by decide)

/-! ## CQ1/CQ2 on data — tight, and still half -/

-- The committed cone misses author 3 at every layer: exactly `f`.
example : missingAt Ucens 13 0 = {3} := by decide
example : missingAt Ucens 13 1 = {3} := by decide
example : missingAt Ucens 13 2 = {3} := by decide
example : (missingAt Ucens 13 0).card = Faults.f (Fin 4) := by decide

-- Covered: exactly `|Correct| − f = 2` of the three correct validators.
example : coveredAt Ucens 13 1 = {1, 2} := by decide

-- CQ1 applied, and CQ2 applied: 3 ≤ 2·2.
example : (Correct : Finset (Fin 4)).card - Faults.f (Fin 4) ≤
    (coveredAt Ucens 13 1).card :=
  card_coveredAt_ge_of_decided ucens_slot1 (by decide)

example : (Correct : Finset (Fin 4)).card ≤ 2 * (coveredAt Ucens 13 1).card :=
  card_correct_le_two_mul_coveredAt_of_decided ucens_slot1 (by decide)

/-! ## The censorship, exhibited -/

-- No block of author 3 is in the committed cone…
example : ∀ i ∈ Ucens.ids, (Ucens.block i).creator = 3 →
    i ∉ history Ucens 13 := by decide

-- …and coverage fails at every round it could be tested: the round-3
-- block of author 1 does not reference author 3's round-2 block.
example : ¬ Synchronised Ucens 0 := by
  intro h
  exact absurd
    (h 2 (by omega) 13 (by decide) (by decide) (by decide)
      11 (by decide) (by decide) (by decide))
    (by decide)

example : ¬ Synchronised Ucens 2 := by
  intro h
  exact absurd
    (h 2 (by omega) 13 (by decide) (by decide) (by decide)
      11 (by decide) (by decide) (by decide))
    (by decide)

/-! ## The ledger, on data -/

/-- A concrete verdict assignment: slot 1 commits block 13. -/
def gcens : ℕ → Option (Fin 24) := fun k => if k = 1 then some 13 else none

-- A correct-authored cone block is in the ledger…
example : (5 : Fin 24) ∈ ledgerSet Ucens gcens 2 :=
  ⟨1, by omega, 13, rfl, (mem_history_iff (by decide)).mp (by decide)⟩

-- …and the censored validator's block is not.
example : (7 : Fin 24) ∉ ledgerSet Ucens gcens 2 := by
  rintro ⟨k, hk, L, hL, hr⟩
  interval_cases k
  · simp [gcens] at hL
  · rw [show L = 13 from ((by simpa [gcens] using hL : (13 : Fin 24) = L)).symm] at hr
    exact absurd ((mem_history_iff (by decide)).mpr hr) (by decide)

-- CQ3 applied: at least two correct validators have round-1 blocks in
-- the ledger.
example : ∃ S : Finset (Fin 4), S ⊆ (Correct : Finset (Fin 4)) ∧
    (Correct : Finset (Fin 4)).card - Faults.f (Fin 4) ≤ S.card ∧
    ∀ v ∈ S, ∃ i ∈ ledgerSet Ucens gcens 2,
      (Ucens.block i).creator = v ∧ (Ucens.block i).round = 1 :=
  ledger_coverage ucens_slot1 rfl (by omega) (by decide)

/-! ## CQ5/CQ6 on data — inclusion, from self-reference -/

theorem uexcl_slot1_commit : Decided Uexcl (View.full Uexcl) 1 (some 11) :=
  Decided.directCommit (by decide) (by decide)

-- CQ5 applied: every block by the slot-1 leader's author at or below its
-- round is in the commit's cone — and the same fact confirmed on the data.
example : ∀ b ∈ Uexcl.ids, (Uexcl.block b).creator = (Uexcl.block 11).creator →
    (Uexcl.block b).round ≤ (Uexcl.block 11).round → b ∈ history Uexcl 11 :=
  fun b hb hbc hle => mem_history_of_decided_commit uexcl_slot1_commit (by decide) hb hbc hle

example : ∀ b ∈ Uexcl.ids, (Uexcl.block b).creator = (Uexcl.block 11).creator →
    (Uexcl.block b).round ≤ (Uexcl.block 11).round → b ∈ history Uexcl 11 := by
  decide

-- CQ6's schedule side, instantiated: `fairSlots` returns to validator
-- `1` at every slot, and the theorem produces a slot `1` leads at or
-- above round 1.
example : ∃ k', 1 ≤ fairSlots.slotRound k' ∧ fairSlots.leader k' = 1 := by
  obtain ⟨k', hk', hlead, -⟩ :=
    committed_of_correct_block (S := fairSlots) (BlockId := Fin 20) (Payload := Unit)
      (T := {1}) (by decide)
      (fun v hv k => ⟨k, le_refl k, by rw [fairSlots_leader]; exact (Finset.mem_singleton.mp hv).symm⟩)
      1 (Finset.mem_singleton_self 1)
  exact ⟨k', hk', hlead⟩

/-! ## CQ7 on data — the windowed bound instantiated -/

/-- Round-robin over four validators is windowed-fair to each at `w = 4`. -/
theorem rrSlots_fairToEachWithin :
    FairToEachWithin (S := rrSlots) ({1, 2, 3} : Finset (Fin 4)) 4 := by
  intro v _ k
  have hv := v.isLt
  refine ⟨k + (v.val + 4 - k % 4) % 4, by omega, by omega, ?_⟩
  apply Fin.ext
  rw [rrSlots_leader_val]
  omega

-- Under the round-robin schedule, the committing slot for validator
-- `1`'s round-`1` blocks is pinned to a four-slot window.
example : ∃ k', slotAt (Fin 4) (S := rrSlots) 1 ≤ k' ∧
    k' < slotAt (Fin 4) (S := rrSlots) 1 + 4 := by
  obtain ⟨k', h1, h2, -⟩ :=
    committed_of_correct_block_within (S := rrSlots) (BlockId := Fin 20)
      (Payload := Unit) (by decide) rrSlots_fairToEachWithin 1 (v := 1) (by decide)
  exact ⟨k', h1, h2⟩

#print axioms chain_quality
#print axioms committed_of_correct_block_within
#print axioms committed_of_correct_block_by_round
#print axioms card_coveredAt_ge_of_decided
#print axioms card_correct_le_two_mul_coveredAt_of_decided
#print axioms ledger_coverage
#print axioms mem_history_of_decided_commit
#print axioms committed_of_correct_block

end LeanDagTest
