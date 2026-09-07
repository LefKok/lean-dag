import LeanDag.Common.History
import LeanDag.Common.Density
/-!
# Density: histories are almost all of the correct past

`dos-equivocation-and-growth.md` §5, **D25**.

The quorum condition says a block's references carry `2f+1` distinct
creators, of which at most `f` are Byzantine — so at least `2f+1 - β`
correct, where `β := |byzantine|`. Since the correct validators number
exactly `3f+1 - β`, a block *misses* at most
`(3f+1-β) - (2f+1-β) = f` of the correct validators of the round below —
independent of `β`. And missing is monotone through any correct reference:
what `b`'s history lacks at a deep round, its references' histories lack
too. Inducting through any one correct reference:

> **D25 (density).** A valid block's history contains a block by all but at
> most `f` of the correct validators, at *every* round strictly below it.

This is T3/L0 sharpened from "a quorum of authors appears" to "almost
everyone appears", and it is the model's strongest expression of the fact
the DoS analysis leans on: **cones cannot be selectively blind**. A block
may curate its `≤ f` misses, but it swallows everything else — including
everything those correct blocks had already swallowed. Nothing here needs
`DoSValid` or self-parents; it is pure validity.

**The induction moved.** It read `U.valid`, `U.complete` and
`U.round_of_mem_refs` and nothing else, which is `CausalStructure` plus
one counting law, so it is stated over the raw block data in
`LeanDag/Density.lean` and this file names the core's instance of it.
Every other rule in the development has the same validity clause, and
`Properties.Quorate` is how a rule hands it over
(`Properties/Optional/Quorate.lean`); what was one arc's lemma is now
the whole development's.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

section History

variable [DecidableEq BlockId]

/-- The correct validators with no block at round `δ` in `b`'s history. -/
def missingAt (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (δ : ℕ) :
    Finset Validator :=
  missingAtFrom U.block (coreReliability Validator) b δ

/-- Membership in `missingAt`, unfolded: a correct validator is missing at depth `δ` when the history contains none of its blocks there. -/
theorem mem_missingAt {b : BlockId} {δ : ℕ} {v : Validator} :
    v ∈ missingAt U b δ ↔ v ∈ (Correct : Finset Validator) ∧
      ∀ i ∈ history U b, ¬ ((U.block i).creator = v ∧ (U.block i).round = δ) :=
  mem_missingAtFrom

/-- Missing is monotone through references: what `b` lacks, its references
lack. -/
theorem missingAt_subset_of_mem_refs {b p : BlockId} (hb : b ∈ U.ids)
    (hp : p ∈ (U.block b).refs) {δ : ℕ} :
    missingAt U b δ ⊆ missingAt U p δ :=
  missingAtFrom_subset_of_mem_refs U.causal hb hp

/-- **D25 (density).** A valid block's history contains a block by all but
at most `f` of the correct validators at every round strictly below it. -/
theorem card_missingAt_le {b : BlockId} (hb : b ∈ U.ids) {δ : ℕ}
    (hδ : δ < (U.block b).round) : (missingAt U b δ).card ≤ F.f :=
  card_missingAtFrom_le U.causal U.quorateOn hb hδ

end History

end LeanDag
