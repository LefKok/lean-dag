import LeanDag.Properties.Agree

/-!
# The bounded decision relation, and locality in the schedule

`docs/target-properties.md` §4. What an adaptive leader schedule
consumes from a protocol, on the safety side.

An adaptive schedule computes the leaders of high slots from the
verdicts of low ones, and a verdict may be anchored arbitrarily far
above the slot it decides. For the fixpoint to be stratified, a verdict
has to come with a **bound**: every slot its derivation mentions — the
slot, the anchor, the intermediates — lies strictly below it. That
bound cannot be recovered from a `Decided` derivation, which is a proof
of a `Prop`, so the protocol supplies the bounded family itself:
`BoundedRule` is a `DagRule` with `DecidedWithin` alongside `Decided`.

Two properties are stated over it.

* `Bounded` — the bounded family embeds in `Decided`, decides only slots
  under its bound, and relaxes upward.
* `SchedLocal` — **locality in the schedule**, the twin of `Local`. A
  verdict within bound `B` reads the schedule's leaders only below `B`,
  so two schedules with the same round structure agreeing on those
  leaders derive the same bounded verdicts. `Local` says a verdict reads
  the DAG only above its round; this says it reads the schedule only
  below its bound.

With `Agree`, these three are the whole of what the adaptive fixpoint's
uniqueness consumes.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A rule with a bounded decision relation.** `DecidedWithin S B V k v`
is meant as: the verdict `v` at slot `k` is derivable with every slot the
derivation mentions strictly below `B`. -/
structure BoundedRule (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    (BlockId : Type) [DecidableEq BlockId] (Payload : Type)
    extends DagRule Validator BlockId Payload where
  /-- The decision relation with a bound on the slots it mentions. -/
  DecidedWithin : Slots Validator → ℕ → ∀ {U : Universe}, View U → ℕ → Option BlockId → Prop

variable {R : BoundedRule Validator BlockId Payload}

/-- **The bounded family is a family of derivations.** -/
structure Bounded (R : BoundedRule Validator BlockId Payload) : Prop where
  /-- Forgetting the bound yields an ordinary verdict. -/
  toDecided : ∀ (S : Slots Validator) (B : ℕ) {U : R.Universe} (V : R.View U)
    (k : ℕ) (v : Option BlockId), R.DecidedWithin S B V k v → R.Decided S V k v
  /-- The decided slot lies below the bound. -/
  lt_bound : ∀ (S : Slots Validator) (B : ℕ) {U : R.Universe} (V : R.View U)
    (k : ℕ) (v : Option BlockId), R.DecidedWithin S B V k v → k < B
  /-- The bound relaxes upward. -/
  mono : ∀ (S : Slots Validator) (B B' : ℕ) {U : R.Universe} (V : R.View U)
    (k : ℕ) (v : Option BlockId), R.DecidedWithin S B V k v → B ≤ B' →
    R.DecidedWithin S B' V k v

/-- Two bounded verdicts agree, at any bounds — `Agree` through the
embedding. -/
theorem Bounded.agree (hb : Bounded R) (ha : Agree R.toDagRule) {S : Slots Validator}
    {U : R.Universe} {V₁ V₂ : R.View U} {B₁ B₂ k : ℕ} {v₁ v₂ : Option BlockId}
    (h₁ : R.DecidedWithin S B₁ V₁ k v₁) (h₂ : R.DecidedWithin S B₂ V₂ k v₂) : v₁ = v₂ :=
  ha S V₁ V₂ k v₁ v₂ (hb.toDecided S B₁ V₁ k v₁ h₁) (hb.toDecided S B₂ V₂ k v₂ h₂)

/-- **Locality in the schedule.** Two schedules with the same round
structure, agreeing on the leaders of every slot below `B`, derive the
same verdicts within `B`. -/
def SchedLocal (R : BoundedRule Validator BlockId Payload) : Prop :=
  ∀ (S S' : Slots Validator), S.slotRound = S'.slotRound →
    ∀ (B : ℕ), (∀ m, m < B → S.leader m = S'.leader m) →
    ∀ {U : R.Universe} (V : R.View U) (k : ℕ) (v : Option BlockId),
      R.DecidedWithin S B V k v → R.DecidedWithin S' B V k v

end Properties

end LeanDag
