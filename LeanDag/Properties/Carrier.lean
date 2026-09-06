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
* the `causal` law — that a rule's universes are closed under
  references and respect the predecessor condition, carried by the
  carrier as `viewSound` and `viewComplete` are.
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
  /-- A view holds only blocks the universe has. A law rather than a
  property: every protocol's view type carries this proof already, so
  asking for it here costs an instance nothing and spares every
  consumer a hypothesis. -/
  viewSound : ∀ {U : Universe} (V : View U), viewIds V ⊆ ids U
  /-- A view is closed under references: it holds what its blocks point
  at. The second law every view type already carries, and the one a
  window count needs — a validator holding a block holds its whole
  causal history, so a window measured on that history is the same
  window whoever measures it (`Barnacle/Window/`). -/
  viewComplete : ∀ {U : Universe} (V : View U),
    ∀ i ∈ viewIds V, ∀ j ∈ (block U i).refs, j ∈ viewIds V
  /-- **A universe is a block DAG**: every reference is present and sits
  one round below. The third law, for the reason the other two are laws:
  every universe type in the development carries it in its validity
  record, and it is a fact about the DAG model rather than about any
  rule. It was a property (`Causal`) that nine carriers proved with the
  same four lines. -/
  causal : ∀ U : Universe, CausalStructure (block U) (ids U)
  /-- The decision relation under a schedule. -/
  Decided : Slots Validator → ∀ {U : Universe}, View U → ℕ → Option BlockId → Prop

/-- **One DAG is another above a round, rebased.** At and above `R₀`
the two universes hold the same blocks, at rounds `G` apart, with the
same authors; and strictly above `R₀`, the same references. Nothing is
said below `R₀`, which is where a mechanism does its work.

**This one relation is what every mechanism here delivers.** A
truncation rebases by its horizon (`Truncates`, at `R₀ = G`); a fill or
an extension rebases by nothing and settles at the top of its gap
(`Sustains`); plain agreement above a round is the zero offset
(`AgreeAbove`). They were three structures with the same four clauses
until the clauses were compared.

`mem` pairs presence with the round condition rather than stating them
separately, which is what lets the relation be read from either
universe: without it, "present and above `R₀`" could hold in one and
not the other, and the definition would name a direction it does not
mean.

References are compared **strictly** above `R₀`: a truncation retains
its bottom layer's blocks but empties their references, since what they
referenced is gone. Every rule reads a vote from a *parent*, so a block
at exactly `R₀` contributes its presence and its author but no vote,
which is what the clause says. -/
structure RebasedAbove (R : DagRule Validator BlockId Payload)
    (U U' : R.Universe) (G R₀ : ℕ) : Prop where
  /-- The same blocks at and above `R₀`. -/
  mem : ∀ b, (b ∈ R.ids U ∧ R₀ ≤ (R.block U b).round) ↔
    (b ∈ R.ids U' ∧ R₀ ≤ (R.block U' b).round + G)
  /-- At rounds `G` apart. Additive, so truncated subtraction never
  appears. -/
  round : ∀ b, b ∈ R.ids U → R₀ ≤ (R.block U b).round →
    (R.block U' b).round + G = (R.block U b).round
  /-- With the same author. -/
  creator : ∀ b, b ∈ R.ids U → R₀ ≤ (R.block U b).round →
    (R.block U' b).creator = (R.block U b).creator
  /-- And, strictly above, the same references. -/
  refs : ∀ b, b ∈ R.ids U → R₀ < (R.block U b).round →
    (R.block U' b).refs = (R.block U b).refs

/-- **Two universes agree above a round**: `RebasedAbove` at no
offset. -/
abbrev AgreeAbove (R : DagRule Validator BlockId Payload)
    (U U' : R.Universe) (r : ℕ) : Prop := RebasedAbove R U U' 0 r

namespace RebasedAbove

variable {R : DagRule Validator BlockId Payload} {U U' : R.Universe} {G R₀ : ℕ}

/-- A block of the target at or above the settling round is a block of
the source, at the shifted round. -/
theorem of_mem' (h : RebasedAbove R U U' G R₀) {b : BlockId} (hb : b ∈ R.ids U')
    (hr : R₀ ≤ (R.block U' b).round + G) :
    b ∈ R.ids U ∧ (R.block U' b).round + G = (R.block U b).round := by
  have hU := (h.mem b).mpr ⟨hb, hr⟩
  exact ⟨hU.1, h.round b hU.1 hU.2⟩

end RebasedAbove

/-- **What a block above the cut references is itself above the cut** —
a fact about causal structure alone, and the step an induction over a
derivation's anchors needs, since it says the region agreement covers
is closed under the recursion. -/
theorem DagRule.causal_refs_above {R : DagRule Validator BlockId Payload}
    {U : R.Universe} {r : ℕ}
    {b : BlockId} (hb : b ∈ R.ids U) (hr : r < (R.block U b).round)
    {j : BlockId} (hj : j ∈ (R.block U b).refs) :
    j ∈ R.ids U ∧ r ≤ (R.block U j).round := by
  refine ⟨(R.causal U).complete b hb j hj, ?_⟩
  have := (R.causal U).refs_round b hb j hj
  omega

end Properties

end LeanDag
