import LeanDag.CausalHistory

/-!
# The ledger

What a validator outputs, from a slot-to-verdict assignment `g` and
nothing else: the committed leaders in slot order (`commitSeq`), the
blocks flushed with them — everything in a committed leader's causal
history — as a set (`ledgerSet`), and the slot at which a block enters
(`OutputAt`).

**No retraction, stated without an order on ids.** Ordering *within*
one flush needs a tie-break the development deliberately does not
assume, but **whether** and **when** a block is output needs no order
at all, and that is what retraction would violate: `ledgerSet_mono`
says nothing already output is ever dropped, `outputAt_unique` that a
block enters at exactly one slot, and the `_of` theorems that two
assignments agreeing below `n` — which is what a rule's agreement
across views gives — output the same blocks at the same slots.

Every rule's ledger is this one at its record. A rule states its
agreement theorems as the `_of` forms at its own `decided_agree`.
-/

namespace LeanDag

variable {Validator : Type*} {BlockId : Type*} {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- The blocks committed at slots `0, …, n-1`, in slot order, with skipped
slots dropped. `g` is a validator's verdict assignment. -/
def commitSeq (g : ℕ → Option BlockId) (n : ℕ) : List BlockId :=
  (List.range n).filterMap g

/-- Two assignments that agree below `n` read off the same list. -/
theorem commitSeq_agree_of {g₁ g₂ : ℕ → Option BlockId} {n : ℕ}
    (hg : ∀ k, k < n → g₁ k = g₂ k) : commitSeq g₁ n = commitSeq g₂ n := by
  simp only [commitSeq]
  exact List.filterMap_congr fun k hk => hg k (List.mem_range.mp hk)

/-- The blocks output after settling slots `0, …, n-1`: everything in the
causal history of a committed leader. -/
def ledgerSet (U : BlockRecord Validator BlockId Payload P honest)
    (g : ℕ → Option BlockId) (n : ℕ) : Set BlockId :=
  {b | ∃ k, k < n ∧ ∃ L, g k = some L ∧ Reaches U L b}

/-- **Nothing is ever dropped.** The ledger only grows as more slots settle. -/
theorem ledgerSet_mono {g : ℕ → Option BlockId} {n m : ℕ} (h : n ≤ m) :
    ledgerSet U g n ⊆ ledgerSet U g m := by
  rintro b ⟨k, hk, hrest⟩
  exact ⟨k, by omega, hrest⟩

/-- Two assignments that agree below `n` output the same blocks. -/
theorem ledgerSet_agree_of {g₁ g₂ : ℕ → Option BlockId} {n : ℕ}
    (hg : ∀ k, k < n → g₁ k = g₂ k) : ledgerSet U g₁ n = ledgerSet U g₂ n := by
  ext b
  constructor
  · rintro ⟨k, hk, L, hL, hr⟩
    exact ⟨k, hk, L, (hg k hk) ▸ hL, hr⟩
  · rintro ⟨k, hk, L, hL, hr⟩
    exact ⟨k, hk, L, (hg k hk).symm ▸ hL, hr⟩

/-- `b` enters the ledger at slot `k`: the first committed slot whose leader
reaches it. -/
def OutputAt (U : BlockRecord Validator BlockId Payload P honest)
    (g : ℕ → Option BlockId) (b : BlockId) (k : ℕ) : Prop :=
  (∃ L, g k = some L ∧ Reaches U L b) ∧
    ∀ j, j < k → ∀ L, g j = some L → ¬ Reaches U L b

/-- **A block enters the ledger once.** Its position is not merely stable
over time — there is no second slot it could have entered at. -/
theorem outputAt_unique {g : ℕ → Option BlockId} {b : BlockId} {k₁ k₂ : ℕ}
    (h₁ : OutputAt U g b k₁) (h₂ : OutputAt U g b k₂) : k₁ = k₂ := by
  rcases lt_trichotomy k₁ k₂ with h | h | h
  · obtain ⟨L, hL, hr⟩ := h₁.1
    exact absurd hr (h₂.2 k₁ h L hL)
  · exact h
  · obtain ⟨L, hL, hr⟩ := h₂.1
    exact absurd hr (h₁.2 k₂ h L hL)

/-- **A committed leader's cone is in the ledger** from the next horizon
on: the link between an assignment and what it delivers. -/
theorem mem_ledgerSet_of_some {g : ℕ → Option BlockId} {k : ℕ} {L b : BlockId}
    (hg : g k = some L) (hb : Reaches U L b) : b ∈ ledgerSet U g (k + 1) :=
  ⟨k, by omega, L, hg, hb⟩

/-- Two assignments that agree below `n` concur on the slot a block enters at. -/
theorem outputAt_agree_of {g₁ g₂ : ℕ → Option BlockId} {n : ℕ} {b : BlockId} {k : ℕ}
    (hg : ∀ j, j < n → g₁ j = g₂ j) (hk : k < n) (ho : OutputAt U g₁ b k) :
    OutputAt U g₂ b k := by
  refine ⟨?_, ?_⟩
  · obtain ⟨L, hL, hr⟩ := ho.1
    exact ⟨L, (hg k hk) ▸ hL, hr⟩
  · intro j hj L hL hr
    exact ho.2 j hj L ((hg j (by omega)).symm ▸ hL) hr

end LeanDag
