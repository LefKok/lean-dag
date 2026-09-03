import Mathlib.Order.Defs.LinearOrder
import Mathlib.Data.Fin.Basic

/-!
# One decision relation, parameterised

`docs/target-properties.md` §7. **This is a convenience, not a
foundation**: the properties of that document's §3 are what the
mechanisms need, and a protocol may discharge them directly. What this
file offers is a way to discharge them once, for every protocol whose
rule fits the schema below. FinWhale's does not — its commitment is a
decision function constrained by laws — which is why nothing depends on
this file.
 This development carries
**nine** inductive decision relations — Mysticeti, Odontoceti, Nemo,
Mahi-Mahi, Hybrid, Hydrozoan, Optimal-Hydrozoan, and `Adaptive`'s two
`DecidedWithin` copies — and every result that must be proved *about* a
decision relation is currently proved nine times, or, more often,
proved once and left unproved for the other eight. Exactly one has any
transformer invariance.

They differ less than their constructor counts suggest. Each has some
number of direct commit paths, a direct skip, and an ordered list of
indirect rungs anchored on the nearest eligible committed slot, where a
rung fires only when every rung below it is empty for every candidate,
some rungs carrying a least-candidate tie-break. `RuleSpec` is those
parameters and `Decided` below is the relation, in four constructors.

**The universe and the view do not appear.** They are fixed
throughout a derivation, so an instance closes over them when it builds
its spec, and the relation is a predicate on slots and verdicts alone.
This is what lets one schema serve carriers as different as
Hydrozoan's payload-free universe and Nemo's, with no coercion between
them and no dependent view parameter. Rounds do not appear either:
every predicate is indexed by the *slot*, and an instance applies its
own schedule when it supplies them. The order the tie-break uses is a
field rather than a `LinearOrder` instance, because
Optimal-Hydrozoan's rungs are unique without one and requiring the
instance would take that property away from anything routed through
here.

**The four constructors against the nine relations.** One direct
commit constructor covers protocols with two commit paths, the spec's
`Direct` being their disjunction. One skip constructor covers both the
per-candidate form (`∀ L, Cand → DirectSkip L`, the core's) and the
slot-level form (Hydrozoan's blame count), since both are a predicate
of the slot alone, once the spec has closed over the universe and the
view. `Nemo` has no direct skip at
all and sets `Skip` to `False`. `Adaptive`'s bound is `Dom`.

Nothing here is proved *about* the relation yet; this file is the
statement of what the nine have in common, and the equivalences that
justify the claim live beside each protocol.
-/

namespace LeanDag

namespace RuleSpec

universe u

/-- **The parameters of a decision relation.** `m` is the number of
indirect rungs, ordered: rung `i` fires only when every rung below it is
empty for every candidate of the slot. -/
structure Spec (BlockId : Type u) (m : ℕ) where
  /-- The slots the relation may decide. `fun _ => True` for every
  protocol but `Adaptive`, whose bound this is. -/
  Dom : ℕ → Prop
  /-- A block is the slot's candidate. -/
  Cand : ℕ → BlockId → Prop
  /-- A slot may anchor another. Reads the schedule alone. -/
  Elig : ℕ → ℕ → Prop
  /-- The direct commit rule, in view. Where a protocol has several
  commit paths this is their disjunction. -/
  Direct : BlockId → ℕ → Prop
  /-- The direct skip, in view — per candidate or at the slot, as the
  protocol states it, and `False` for a protocol with no direct
  skip. -/
  Skip : ℕ → Prop
  /-- Rung `i`'s test: `L` is in reach of the anchor `A`. -/
  Rung : Fin m → BlockId → BlockId → ℕ → Prop
  /-- Which rungs carry a least-candidate tie-break. -/
  Tie : Fin m → Prop
  /-- The order the tie-break uses. A field rather than an instance, so
  that a protocol whose rungs are unique need not carry one. -/
  lt : BlockId → BlockId → Prop

variable {BlockId : Type u} {m : ℕ}

/-- **The verdicts a replica may reach.** Four constructors
for all nine relations: commit directly, skip directly, commit through
a rung, or skip because every rung is empty. -/
inductive Decided (S : Spec BlockId m) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate. -/
  | direct {k : ℕ} {L : BlockId} :
      S.Dom k → S.Cand k L → S.Direct L k → Decided S k (some L)
  /-- The direct rule skips the slot. -/
  | skip {k : ℕ} :
      S.Dom k → S.Skip k → Decided S k none
  /-- Anchored on the nearest eligible committed slot, rung `i` reaches
  `L` and no lower rung reaches anything. -/
  | indirect {k j : ℕ} {A L : BlockId} (i : Fin m) :
      S.Dom k → S.Dom j → k < j → S.Elig k j →
      Decided S j (some A) →
      (∀ i', k < i' → i' < j → S.Elig k i' → Decided S i' none) →
      (∀ i' : Fin m, i' < i → ∀ L', S.Cand k L' → ¬ S.Rung i' A L' k) →
      S.Cand k L → S.Rung i A L k →
      (S.Tie i → ∀ L', S.Cand k L' → S.Rung i A L' k → ¬ S.lt L' L) →
      Decided S k (some L)
  /-- Anchored likewise, and every rung is empty for every candidate. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      S.Dom k → S.Dom j → k < j → S.Elig k j →
      Decided S j (some A) →
      (∀ i', k < i' → i' < j → S.Elig k i' → Decided S i' none) →
      (∀ i' : Fin m, ∀ L', S.Cand k L' → ¬ S.Rung i' A L' k) →
      Decided S k none

/-- Every verdict is reached at a slot the spec admits — the one fact
about `Dom` that every consumer needs, and `Adaptive`'s `lt_bound`. -/
theorem dom_of_decided {S : Spec BlockId m}
    {k : ℕ} {v : Option BlockId} (h : Decided S k v) : S.Dom k := by
  cases h with
  | direct hd _ _ => exact hd
  | skip hd _ => exact hd
  | indirect _ hd _ _ _ _ _ _ _ _ _ => exact hd
  | indirectSkip hd _ _ _ _ _ _ => exact hd

/-- A committed verdict is a candidate of its slot — every protocol's
`isLeaderBlock_of_decided`, proved once. -/
theorem cand_of_decided {S : Spec BlockId m}
    {k : ℕ} {L : BlockId} (h : Decided S k (some L)) : S.Cand k L := by
  cases h with
  | direct _ hc _ => exact hc
  | indirect _ _ _ _ _ _ _ _ hc _ _ => exact hc

end RuleSpec

end LeanDag
