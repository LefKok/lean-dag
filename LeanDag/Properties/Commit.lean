import LeanDag.Properties.Bounded

/-!
# What a protocol provides for a schedule mechanism's liveness

`docs/target-properties.md` §4, the liveness side. `Sustains` is what a
DAG-transforming mechanism owes a protocol; a *schedule* mechanism
transforms no DAG, and its liveness theorem is the one that needs
feeding. Two properties, both proved by the protocol.

* `LeaderCommits` — under the protocol's own liveness precondition
  `Live`, a slot led by a member of the reliable set `T` is committed
  with a bound one above the slot. `Live` is a parameter, not a field:
  the same rule under two execution models — the timed core and the
  reactive discipline — has two preconditions and one relation, and the
  property is stated once for each.

  `Live S V T lo K` is indexed by the schedule, because a reactive
  execution's clauses read the schedule's leaders, and by a slot window
  `[lo, K)`: an adaptive schedule is only determined so far, and what a
  protocol can promise about an execution is confined to the slots
  whose leaders that execution followed.

* `Descends` — a run of `c` consecutive committed slots decides every
  slot below it, inside the run's bound. The indirect rule's descent;
  `c` is the protocol's, as is the hypothesis on the round structure
  under which it holds, so the property is indexed by the schedule too.

Both produce a verdict at a **tight** bound, which is why they are
protocol obligations rather than corollaries of the band: the band's
top names every slot its rounds can hold, and a direct commit at slot
`k` depends on one leader, not on all of them.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A reliable leader's slot commits**, within a bound one above it,
wherever the protocol's precondition `Live` holds over a slot window
containing the slot. -/
def LeaderCommits (R : DagRule Validator BlockId Payload)
    (Live : Slots Validator → ∀ {U : R.Universe}, R.View U → Finset Validator → ℕ → ℕ → Prop) :
    Prop :=
  ∀ (S : Slots Validator) {U : R.Universe} (V : R.View U) (T : Finset Validator) (lo K : ℕ),
    Live S V T lo K → ∀ k, lo ≤ k → k < K → S.leader k ∈ T →
      ∃ L, DecidedBelow R S (k + 1) V k (some L)

/-- **A committed run decides everything below it.** `c` consecutive
slots from `b`, each committed within `b + c`, decide every slot below
`b` within `b + c`. -/
def Descends (R : DagRule Validator BlockId Payload) (S : Slots Validator) (c : ℕ) : Prop :=
  ∀ {U : R.Universe} (V : R.View U) (b : ℕ),
    (∀ j, b ≤ j → j < b + c → ∃ L, DecidedBelow R S (b + c) V j (some L)) →
    ∀ i, i < b → ∃ v, DecidedBelow R S (b + c) V i v

/-- **The indirect rule.** An anchor eligible for slot `i`, committed,
with every eligible slot strictly between them skipped, decides `i`.

`Elig` is a parameter and reads the **round structure alone**: every
rule here makes an anchor eligible when it sits a wave above the slot,
and the property does not care which wave. Reading only `slotRound`
also means eligibility is unchanged by a reassignment of leaders, which
the second quantifier needs.

**The second quantifier is what makes this carry a bound.** A protocol
that proves the indirect rule by cases on the evidence at slot `i` —
which is how all of them prove it — proves this stronger form without
extra work: the case split reads slot `i`'s own candidate and the
anchor's history, and a schedule that renames leaders elsewhere changes
neither. `Descends` is the payoff, derived in `Derived/Descent.lean`
where it was three protocol-specific inductions.

Taking `S' := S` gives the plain rule, which is what a mechanism that
does not track bounds consumes. -/
def Indirect (R : DagRule Validator BlockId Payload)
    (Elig : (ℕ → ℕ) → ℕ → ℕ → Prop) : Prop :=
  ∀ (S : Slots Validator) {U : R.Universe} (V : R.View U) (i j : ℕ) (A : BlockId),
    Elig S.slotRound i j → R.Decided S V j (some A) →
    (∀ i', i < i' → i' < j → Elig S.slotRound i i' → R.Decided S V i' none) →
    ∃ v, ∀ S' : Slots Validator, S'.slotRound = S.slotRound → S'.leader i = S.leader i →
      R.Decided S' V j (some A) →
      (∀ i', i < i' → i' < j → Elig S.slotRound i i' → R.Decided S' V i' none) →
      R.Decided S' V i v

/-- **The plain indirect rule**, at the schedule it was given. -/
theorem Indirect.decided {R : DagRule Validator BlockId Payload}
    {Elig : (ℕ → ℕ) → ℕ → ℕ → Prop} (h : Indirect R Elig)
    (S : Slots Validator) {U : R.Universe} (V : R.View U) {i j : ℕ} {A : BlockId}
    (he : Elig S.slotRound i j) (hj : R.Decided S V j (some A))
    (hmid : ∀ i', i < i' → i' < j → Elig S.slotRound i i' → R.Decided S V i' none) :
    ∃ v, R.Decided S V i v := by
  obtain ⟨v, hv⟩ := h S V i j A he hj hmid
  exact ⟨v, hv S rfl rfl hj hmid⟩

end Properties

end LeanDag
