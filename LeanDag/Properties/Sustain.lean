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
they did. References are compared **strictly** above `R₀`, so a truncation's
emptied bottom layer is admitted.

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

/-- **A mechanism sustains from round `R₀`**, re-indexing by `G`: this
is `RebasedAbove`, under the name the obligation is owed in. The
relation is the same one a truncation and a plain agreement satisfy
(`Properties/Carrier.lean`); what differs is who owes it. -/
abbrev Sustains (R : DagRule Validator BlockId Payload) (U U' : R.Universe)
    (G R₀ : ℕ) : Prop := RebasedAbove R U U' G R₀

namespace RebasedAbove

variable {R : DagRule Validator BlockId Payload} {U U' : R.Universe} {G R₀ : ℕ}

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

end RebasedAbove

end Properties

end LeanDag
