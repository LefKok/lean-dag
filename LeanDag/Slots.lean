import Mathlib.Order.Monotone.Basic
import Mathlib.Logic.Function.Basic

/-!
# The slot schedule

Which validator proposes at which round, as a class so that a schedule
is fixed once per development and every rule reads the same one. Stated
here, below every protocol, because every protocol runs on it: the
core, Odontoceti, Mahi-Mahi, Nemo, Orcaella, FinWhale, Hydrozoan and
Optimal-Hydrozoan all take `[S : Slots Validator]`.
-/

namespace LeanDag

/-- The leader schedule: which validator proposes at which round, as a
sequence of slots.

Slots need **not** be three rounds apart. Under pipelining consecutive slots
are one round apart, and under multiple leaders per round they share a round,
so all that is required of `slotRound` is that it be monotone. The three-round
separation M4's commit half needs is no longer a property of *consecutive*
slots and is therefore not derivable here; it is required instead of the
particular pairs that use it, by `Eligible` below.

`unbounded` was a theorem under three-round spacing (`3 * k ≤
slotRound k`) and is underivable from `mono` alone — a schedule parking every
slot at one round is monotone. Liveness needs it, so it is assumed.

`keyed` says distinct slots differ in round or in leader. It too held under three-round spacing, which makes `slotRound` injective outright. Under
multiple leaders it is a real condition on the schedule: the proposers of a
round must be distinct validators. Without it one block would be the candidate
for two slots, and the ledger would deliver it twice. -/
class Slots (Validator : Type*) where
  /-- The round at which slot `k` is proposed. -/
  slotRound : ℕ → ℕ
  /-- The validator whose block is the slot-`k` candidate. -/
  leader : ℕ → Validator
  /-- Slots are enumerated in round order. -/
  mono : Monotone slotRound
  /-- Slot rounds are unbounded. -/
  unbounded : ∀ n, ∃ k, n ≤ slotRound k
  /-- Distinct slots differ in round or in leader. -/
  keyed : Function.Injective (fun k => (slotRound k, leader k))

end LeanDag
