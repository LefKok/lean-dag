import LeanDag.Properties.Carrier

/-!
# What a mechanism owes a protocol, so liveness survives

`docs/target-properties.md` §3.6. The obligations here run the
*opposite* way to the safety ones, and the asymmetry is structural.

**Safety transports a derivation**, the protocol's inductive object, so
only the protocol can carry it: `Persist` and `LocalTruncate` are proved
once per protocol and consumed by every mechanism.

**Liveness transports a DAG.** What the DAG becomes is the mechanism's
doing, and a protocol's liveness theorem is universally quantified over
universes — it applies to the transformed one unchanged, with no
transport at all. `Integration/Hydrozoan/Liveness.lean` shows both
halves: `commitLiveness_stackHZ` is a single application of the
protocol's own theorem, while `synchronisedOn_stackHZ` carries four side
conditions. All the work is on the mechanism's side, and `Sustains`
names it.

**What the mechanism promises is the blocks, not any predicate.** A
first version of this file transported `VotesAt` and `PopulatedOn` by
name, and left certification out because each protocol has its own
certificate predicate. Fed to a real consumer it failed: the reactive
commit (`Reactive/Mysticeti.directCommit`) runs through
`directCommit_of_certifiesAt`, whose input is `CertifiesAt`, which
nothing transported. The repair is to promise less and get more. Above
a settling round `R₀`, an old block keeps its membership, its author,
its references, and its round shifted by `G` — and then **every**
predicate computed from those transports: votes, production, the core's
`Certifies`, Hydrozoan's `IsCertificate`, and whatever a later protocol
defines. `votesAt_of` and `populatedOn_of` below are the two the
mechanism side can state; a protocol derives its own certificate layer
the same way in a few lines.

**The settling round is where the content sits.** A truncation settles
at its horizon. A fill settles at the top of its gap, because below it
the blocks it adds stand in for blocks that voted and need not vote as
they did. References are compared **strictly** above `R₀`, as
`AgreeAbove` and `Truncates` do, so a truncation's emptied bottom layer
is admitted.

**The discipline this file records.** A witness catches a relation with
no models; it does not catch one that has models and helps nobody. So a
mechanism obligation is not done until a real consumer has been fed from
it. `Properties/Arcs/GC.lean` feeds this one to the reactive commit.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **What the commit rules count**: every `T`-authored block one round
above `r` references `L`. The carrier's reading of `LeanDag.VotesAt`. -/
def VotesAt (R : DagRule Validator BlockId Payload) (U : R.Universe)
    (T : Finset Validator) (r : ℕ) (L : BlockId) : Prop :=
  ∀ v ∈ T, ∀ c, c ∈ R.ids U → (R.block U c).creator = v →
    (R.block U c).round = r + 1 → L ∈ (R.block U c).refs

/-- **Production**: every member of `T` has a block at round `r`. -/
def PopulatedOn (R : DagRule Validator BlockId Payload) (U : R.Universe)
    (T : Finset Validator) (r : ℕ) : Prop :=
  ∀ v ∈ T, ∃ b, b ∈ R.ids U ∧ (R.block U b).round = r ∧ (R.block U b).creator = v

/-- **A mechanism sustains from round `R₀`**, re-indexing by `G`: at and
above the settling round the two universes hold the same blocks, at
rounds `G` apart, with the same authors; and strictly above it, the same
references.

`mem` pairs presence with the round condition on each side, as
`AgreeAbove` does, so the relation can be read from either universe.
Nothing is said below `R₀`, which is where a mechanism does its work. -/
structure Sustains (R : DagRule Validator BlockId Payload) (U U' : R.Universe)
    (G R₀ : ℕ) : Prop where
  /-- The same blocks at and above the settling round. -/
  mem : ∀ b, (b ∈ R.ids U ∧ R₀ ≤ (R.block U b).round) ↔
    (b ∈ R.ids U' ∧ R₀ ≤ (R.block U' b).round + G)
  /-- At rounds `G` apart. Additive, so no truncated subtraction. -/
  round : ∀ b, b ∈ R.ids U → R₀ ≤ (R.block U b).round →
    (R.block U' b).round + G = (R.block U b).round
  /-- With the same author. -/
  creator : ∀ b, b ∈ R.ids U → R₀ ≤ (R.block U b).round →
    (R.block U' b).creator = (R.block U b).creator
  /-- And, strictly above, the same references. -/
  refs : ∀ b, b ∈ R.ids U → R₀ < (R.block U b).round →
    (R.block U' b).refs = (R.block U b).refs

namespace Sustains

variable {R : DagRule Validator BlockId Payload} {U U' : R.Universe} {G R₀ : ℕ}

/-- A block of the target at or above the settling round is a block of
the source, at the shifted round. -/
theorem of_mem' (h : Sustains R U U' G R₀) {b : BlockId} (hb : b ∈ R.ids U')
    (hr : R₀ ≤ (R.block U' b).round + G) :
    b ∈ R.ids U ∧ (R.block U' b).round + G = (R.block U b).round := by
  have hU := (h.mem b).mpr ⟨hb, hr⟩
  exact ⟨hU.1, h.round b hU.1 hU.2⟩

/-- **Votes survive.** A `T`-block one round above `r` is old, keeps its
author and its references, so a vote it cast it casts still. -/
theorem votesAt_of (h : Sustains R U U' G R₀) {T : Finset Validator} {r : ℕ} {L : BlockId}
    (hr : R₀ ≤ r) (hG : G ≤ r) (hv : VotesAt R U T r L) : VotesAt R U' T (r - G) L := by
  intro v hvT c hc hcc hcr
  obtain ⟨hcU, hround⟩ := h.of_mem' hc (by omega)
  have hUr : (R.block U c).round = r + 1 := by omega
  have hcc' : (R.block U c).creator = v := by rw [← h.creator c hcU (by omega)]; exact hcc
  rw [h.refs c hcU (by omega)]
  exact hv v hvT c hcU hcc' hUr

/-- **Production survives.** -/
theorem populatedOn_of (h : Sustains R U U' G R₀) {T : Finset Validator} {r : ℕ}
    (hr : R₀ ≤ r) (hG : G ≤ r) (hp : PopulatedOn R U T r) : PopulatedOn R U' T (r - G) := by
  intro v hvT
  obtain ⟨b, hb, hbr, hbc⟩ := hp v hvT
  have hb' := ((h.mem b).mp ⟨hb, by omega⟩).1
  refine ⟨b, hb', ?_, ?_⟩
  · have := h.round b hb (by omega); omega
  · rw [h.creator b hb (by omega)]; exact hbc

/-- A mechanism that sustains from a round sustains from any later one. -/
theorem mono (h : Sustains R U U' G R₀) {R₁ : ℕ} (hR : R₀ ≤ R₁) : Sustains R U U' G R₁ where
  mem := fun b => by
    constructor
    · rintro ⟨hb, hr⟩
      have := (h.mem b).mp ⟨hb, le_trans hR hr⟩
      exact ⟨this.1, by have := h.round b hb (le_trans hR hr); omega⟩
    · rintro ⟨hb, hr⟩
      have := (h.mem b).mpr ⟨hb, le_trans hR hr⟩
      exact ⟨this.1, by have := h.round b this.1 this.2; omega⟩
  round := fun b hb hr => h.round b hb (le_trans hR hr)
  creator := fun b hb hr => h.creator b hb (le_trans hR hr)
  refs := fun b hb hr => h.refs b hb (lt_of_le_of_lt hR hr)

/-- Doing nothing sustains everything. -/
theorem refl : Sustains R U U 0 0 where
  mem := fun _ => by simp
  round := fun _ _ _ => rfl
  creator := fun _ _ _ => rfl
  refs := fun _ _ _ => rfl

end Sustains

end Properties

end LeanDag
