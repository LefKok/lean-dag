import LeanDag.Properties.Carrier

/-!
# What a mechanism owes a protocol, so liveness survives

`docs/target-properties.md`'s liveness half. The obligations here run
the *opposite* way to the safety ones, and the asymmetry is structural.

**Safety transports a derivation**, which is the protocol's inductive
object, so only the protocol can carry it: `Persist` and
`LocalTruncate` are proved once per protocol and consumed by every
mechanism.

**Liveness transports a DAG.** What the DAG becomes is the mechanism's
doing, and a protocol's liveness theorem is universally quantified over
universes — it applies to the transformed one unchanged, with no
transport at all. `Integration/Hydrozoan/Liveness.lean` shows both
halves of this: `commitLiveness_stackHZ` is a single application of the
protocol's own theorem, while `synchronisedOn_stackHZ` carries four side
conditions. All the work is on the mechanism's side, and `Sustains`
names it.

**The interface is the votes, not the coverage.** `LeanDag.VotesAt`
exists in the core for exactly this reason — full coverage implies it
(`votesAt_of_synchronisedOn`) and the reactive exit supplies it directly
(`ReactivePace.votes`), so it is what the commit arguments are stated
against, round-indexed and schedule-free. Choosing it here is what lets
one obligation serve every pacing discipline: a mechanism never has to
transport a reactive pacing structure, because what a reactive schedule
produces is a vote like any other.

**Certification is deliberately absent.** It names a protocol's own
notion of a certificate, so a mechanism cannot owe it. The mechanism
owes votes and production; the protocol derives its certificate layer
from those, which is the core's own layering.

**And this does not cover everything.** A mechanism can preserve every
vote and every producer and still cost a protocol its progress, by
adding a *candidate* the protocol can neither commit nor skip — which
is what a fill does to Hydrozoan and not to Optimal-Hydrozoan
(`hydrozoan-integration.md` §5.1). That residue is a protocol-side
obligation and is not stated here.
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

/-- **A mechanism sustains `T` from round `R₀`**, re-indexing rounds by
`G`: above that round it destroys no vote and silences no producer.

`R₀` is where the content sits. A truncation settles at its horizon. A
fill settles above its gap, because the blocks it adds need not vote for
what the blocks they stand in for voted for — so below the gap it may
break a vote, and above it cannot. -/
structure Sustains (R : DagRule Validator BlockId Payload) (U U' : R.Universe)
    (T : Finset Validator) (G R₀ : ℕ) : Prop where
  /-- A vote that was cast is cast still. -/
  votes : ∀ r L, R₀ ≤ r → VotesAt R U T r L → VotesAt R U' T (r - G) L
  /-- And a producer produces still. -/
  produces : ∀ r, R₀ ≤ r → PopulatedOn R U T r → PopulatedOn R U' T (r - G)

namespace Sustains

variable {R : DagRule Validator BlockId Payload} {U U' U'' : R.Universe}
variable {T : Finset Validator} {G G' R₀ R₁ : ℕ}

/-- A mechanism that sustains from a round sustains from any later one. -/
theorem mono (h : Sustains R U U' T G R₀) (hR : R₀ ≤ R₁) : Sustains R U U' T G R₁ where
  votes := fun r L hr => h.votes r L (le_trans hR hr)
  produces := fun r hr => h.produces r (le_trans hR hr)

/-- Doing nothing sustains everything. -/
theorem refl : Sustains R U U T 0 0 where
  votes := fun r L _ hv => by simpa using hv
  produces := fun r _ hp => by simpa using hp

end Sustains

end Properties

end LeanDag
