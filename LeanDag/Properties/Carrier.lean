import LeanDag.Causality
import LeanDag.Schedule

/-!
# The carrier a target property talks about

`docs/target-properties.md` G0. Before locality can be *stated* there
must be a way to say "two DAGs agree above round `r`", and the
protocols' carriers differ — the core's universe has a payload,
Hydrozoan's has none, Nemo's is a different structure again.

**The shape was already discovered once**, by `Barnacle.BaseRule`: a
universe type, a view type dependent on it, projections into the shared
`Block` vocabulary, and the decision relation as a field. Six protocols
instantiate it, and `Barnacle/Helpers/DagRule.lean` coerces any of them
into the `DagRule` below.

`DagRule` is nonetheless stated here rather than imported, and the
reason is the arc's layering rule. **Mechanisms depend on properties;
properties depend on nothing.** Barnacle is one of the mechanisms this
arc serves, so a `Properties` that imported it would invert the
dependency and tie every other mechanism — garbage collection, crash
recovery, chain quality — to the adaptive leader count. A protocol
shows conformance to `DagRule`; each mechanism reads only `DagRule` and
the properties; no mechanism refers to another.

**Why a record of uses is enough here, when `hydrozoan-integration.md`
§9 says it is not.** That section argues no `BaseRule`-shaped interface
can carry `decided_chop`, because `BaseRule.Decided` is a field with no
constructors while the transport proof is a structural induction over
derivations. The argument is correct and it does not apply to this arc,
because **nothing here inducts on `Decided`**. Locality and persistence
are *hypotheses*; a protocol discharges them by induction over its own
relation, where the constructors are available, and the mechanism
theorems then consume them without induction. §9 blocks deriving the
properties from the interface, not assuming them over it.

Three things this file supplies:

* `DagRule` — the carrier: what a mechanism may read of a protocol.
* `Causal` — that a rule's universes are closed under references and
  respect the predecessor condition. `Barnacle.Laws` states both of
  these for *views* and neither for universes, though every instance
  has them.
* `AgreeAbove` — the agreement notion locality is stated against.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **What a mechanism may read of a protocol.** A universe type, views
over it, the projections into the shared `Block` vocabulary, and the
decision relation. Deliberately smaller than `Barnacle.BaseRule`, which
adds what its own mechanism needs — a wave length, a direct-commit
predicate and its decidability, the full and history views. -/
structure DagRule (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    (BlockId : Type) [DecidableEq BlockId] (Payload : Type) where
  /-- The universe type of the base development. -/
  Universe : Type
  /-- The view type, indexed by universe. -/
  View : Universe → Type
  /-- The block an id denotes: round, creator and references. -/
  block : Universe → BlockId → Block Validator BlockId Payload
  /-- The ids of the universe. -/
  ids : Universe → Finset BlockId
  /-- The ids a view holds. -/
  viewIds : ∀ {U : Universe}, View U → Finset BlockId
  /-- The decision relation under a schedule. -/
  Decided : Slots Validator → ∀ {U : Universe}, View U → ℕ → Option BlockId → Prop

/-- **A rule's universes are block DAGs.** The structural facts
`CausalStructure` names, which `Barnacle.Laws` states for views and not
for universes. -/
def Causal (R : DagRule Validator BlockId Payload) : Prop :=
  ∀ U : R.Universe, CausalStructure (R.block U) (R.ids U)

/-- **Two universes agree above round `r`.** Everything a rule can read
of a block — its presence, round, author and references — is the same
in both, for blocks at round `r` and above.

`mem` pairs presence with the round condition rather than stating them
separately, which is what makes the relation symmetric: without it,
"present and above `r`" could be read in one universe and not the
other, and the definition would name a direction it does not mean.

References are compared **strictly** above `r`: a truncation retains
its bottom layer's blocks but empties their references, since what they
referenced is gone. Every rule reads a vote from a *parent*, so a block
at exactly `r` contributes its presence and its author but no vote,
which is what the clause says. -/
structure AgreeAbove (R : DagRule Validator BlockId Payload)
    (U U' : R.Universe) (r : ℕ) : Prop where
  /-- The same blocks are present at and above `r`. -/
  mem : ∀ b, (b ∈ R.ids U ∧ r ≤ (R.block U b).round) ↔
    (b ∈ R.ids U' ∧ r ≤ (R.block U' b).round)
  /-- At and above `r`, a block sits at the same round. -/
  round : ∀ b, b ∈ R.ids U → r ≤ (R.block U b).round →
    (R.block U' b).round = (R.block U b).round
  /-- And has the same author. -/
  creator : ∀ b, b ∈ R.ids U → r ≤ (R.block U b).round →
    (R.block U' b).creator = (R.block U b).creator
  /-- Strictly above `r`, it references the same blocks. -/
  refs : ∀ b, b ∈ R.ids U → r < (R.block U b).round →
    (R.block U' b).refs = (R.block U b).refs

namespace AgreeAbove

variable {R : DagRule Validator BlockId Payload} {U U' : R.Universe} {r : ℕ}

/-- Agreement is reflexive. -/
theorem refl : AgreeAbove R U U r :=
  { mem := fun _ => Iff.rfl
    round := fun _ _ _ => rfl
    creator := fun _ _ _ => rfl
    refs := fun _ _ _ => rfl }

/-- And symmetric — which the paired `mem` clause is what secures. -/
theorem symm (h : AgreeAbove R U U' r) : AgreeAbove R U' U r where
  mem := fun b => (h.mem b).symm
  round := fun b hb hr =>
    have hU := (h.mem b).mpr ⟨hb, hr⟩
    (h.round b hU.1 hU.2).symm
  creator := fun b hb hr =>
    have hU := (h.mem b).mpr ⟨hb, hr⟩
    (h.creator b hU.1 hU.2).symm
  refs := fun b hb hr =>
    have hU := (h.mem b).mpr ⟨hb, le_of_lt hr⟩
    have hround := h.round b hU.1 hU.2
    (h.refs b hU.1 (by omega)).symm

end AgreeAbove

/-- **What a block above the cut references is itself above the cut** —
a fact about causal structure alone, and the step an induction over a
derivation's anchors needs, since it says the region agreement covers
is closed under the recursion. -/
theorem Causal.refs_above {R : DagRule Validator BlockId Payload}
    (hc : Causal R) {U : R.Universe} {r : ℕ}
    {b : BlockId} (hb : b ∈ R.ids U) (hr : r < (R.block U b).round)
    {j : BlockId} (hj : j ∈ (R.block U b).refs) :
    j ∈ R.ids U ∧ r ≤ (R.block U j).round := by
  refine ⟨(hc U).complete b hb j hj, ?_⟩
  have := (hc U).refs_round b hb j hj
  omega

end Properties

end LeanDag
