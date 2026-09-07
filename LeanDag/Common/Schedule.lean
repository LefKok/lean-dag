import LeanDag.Mysticeti.Rule
import Mathlib.Data.Finset.Prod

/-!
# Leader schedules

`Slots` is the interface every downstream theorem indexes by: slots are
numbered by `ℕ`, and `slotRound`/`leader` say where each one sits and who
proposes it. It is not, however, what anyone wants to *write*. This file
supplies the constructor that concrete schedules are built from.

Every deployed schedule is **uniform**: `m` leaders in every `p`-th round.
That case has a closed form, `slotRound k = p * (k / m)`, and needs no
flattening machinery — `Slots.uniform` proves the three class fields once so
that no instance ever faces them.

| | `p` | `m` | `slotRound k` |
|---|---|---|---|
| the original single-leader schedule | 3 | 1 | `3k` |
| pipelined, one leader per round | 1 | 1 | `k` |
| pipelined, `m` leaders per round | 1 | `m` | `k / m` |

The first row is the conservativity check: `uniformSingle 3` satisfies the old
three-round spacing condition (`uniformSingle_spacing`), and under it every
later slot is eligible to anchor every earlier one
(`uniformSingle_eligible_of_lt`), so the generalised `Decided` has exactly the
old constructors available and no derivation is lost.

An irregular schedule — an arbitrary assignment of validators to rounds — is
not covered here; it needs the flattening of a per-round `List Validator`,
which is left for later.
-/

namespace LeanDag

namespace Slots

variable {Validator : Type*}

/-! ### Conservativity

`uniformSingle 3` is the schedule the development had before pipelining. The
two results below are what "the generalisation loses nothing" means
concretely. -/

variable (elect : ℕ → Validator)

/-- **The old `spacing` field, recovered.** Consecutive slots of
`uniformSingle 3` really are three rounds apart, so the schedule the
development used before pipelining is an instance of the weakened class. -/
theorem uniformSingle_spacing (k : ℕ) :
    (uniformSingle 3 (by omega) elect).slotRound k + 3 ≤
      (uniformSingle 3 (by omega) elect).slotRound (k + 1) := by
  simp only [uniformSingle_slotRound]
  omega

/-- Feeding `uniformSingle_spacing` to `eligibleAt_of_lt_of_spacing` gives the
other half of conservativity — under this schedule every later slot may anchor
an earlier one, so the generalised `Decided` offers exactly the constructors
the old one did. Stated for an *instance* of the schedule rather than for the
term, which is how callers meet it. -/
example [S : Slots Validator] (hsp : ∀ k, S.slotRound k = 3 * k) {k j : ℕ} (h : k < j) :
    EligibleAt (S := S) 2 k j :=
  eligibleAt_of_lt_of_spacing (fun k => by simp [hsp]; omega) h

/-- **Slot indices do not outrun rounds.** `keyed` makes
`k ↦ (slotRound k, leader k)` injective and `mono` makes the slots at
round `N` or below an initial segment, so with finitely many validators
those slots inject into `range (N + 1) ×ˢ univ` and their indices stop
below `(N + 1) * card Validator`.

A reverse pass is indexed by slot and a DAG is bounded by round, so
without this there is no horizon to start such a pass from: a round
bound on the blocks says nothing about how many slots sit under it. The
bound is crude — every validator leading every round — and only its
existence is used. -/
theorem slot_lt_of_slotRound_le {Validator : Type*} [Fintype Validator]
    [S : Slots Validator] {N k : ℕ} (h : S.slotRound k ≤ N) :
    k < (N + 1) * Fintype.card Validator := by
  classical
  have hsub : ∀ j ∈ Finset.range (k + 1),
      (S.slotRound j, S.leader j) ∈
        (Finset.range (N + 1)) ×ˢ (Finset.univ : Finset Validator) := by
    intro j hj
    have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hj
    have := S.mono hjk
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
    omega
  have hinj : Set.InjOn (fun j => (S.slotRound j, S.leader j)) (Finset.range (k + 1)) :=
    fun _ _ _ _ hab => S.keyed hab
  have := Finset.card_le_card_of_injOn _ hsub hinj
  simpa [Finset.card_product, Nat.lt_iff_add_one_le] using this

end Slots

end LeanDag
