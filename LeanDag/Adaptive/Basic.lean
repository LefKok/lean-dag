import LeanDag.Schedule

/-!
# Adaptive leaders: epochs and induced schedules

The groundwork for the adaptive-leaders arc (`adaptive-leaders.md`): a
Hammerhead-style schedule recomputes the leaders ahead from the agreed
prefix, and the question is whether safety and liveness survive.

This file holds the two notions that belong to no protocol: the epoch
structure, and `slotsOf`, the `Slots` instance a leader assignment
induces over a fixed round structure. One leader per round —
`slotRound` injective — is assumed for the whole arc: it makes the
`keyed` clause a lemma, where under multi-leader rounds a reassignment
could collide two slots of one round onto one validator and the policy
would owe the distinctness clause itself.

The bounded decision relation the fixpoint needs is a *property of the
protocol* — `Properties/Bounded.lean` states it, `MysticetiProperties`
proves it for the core — and the mechanism reads only the property.
-/

namespace LeanDag

variable {Validator : Type*}

/-- The epoch of slot `k` at width `W`: epoch `e` is slots
`[W·e, W·(e+1))`. -/
def epochOf (W k : ℕ) : ℕ := k / W

theorem epochOf_lt_iff {W k e : ℕ} (hW : 0 < W) :
    epochOf W k < e ↔ k < W * e := by
  unfold epochOf
  rw [Nat.div_lt_iff_lt_mul hW, Nat.mul_comm]

theorem epochOf_mono (W : ℕ) {j k : ℕ} (h : j ≤ k) :
    epochOf W j ≤ epochOf W k :=
  Nat.div_le_div_right h

section Slots

variable [S : Slots Validator]

/-- The `Slots` instance a leader assignment induces: the base round
structure, the given leaders. `keyed` is where one-leader-per-round
enters: with `slotRound` injective, distinct slots differ in round
whatever the assignment names. -/
@[reducible] def slotsOf (hinj : Function.Injective S.slotRound) (a : ℕ → Validator) :
    Slots Validator where
  slotRound := S.slotRound
  leader := a
  mono := S.mono
  unbounded := S.unbounded
  keyed := fun _ _ h => hinj (congrArg Prod.fst h)

@[simp] theorem slotsOf_slotRound (hinj : Function.Injective S.slotRound)
    (a : ℕ → Validator) (k : ℕ) : (slotsOf hinj a).slotRound k = S.slotRound k := rfl

@[simp] theorem slotsOf_leader (hinj : Function.Injective S.slotRound)
    (a : ℕ → Validator) (k : ℕ) : (slotsOf hinj a).leader k = a k := rfl

/-- The base schedule is its own induced instance — the anchor for
conservativity: a constant policy reassigns nothing. -/
theorem slotsOf_base (hinj : Function.Injective S.slotRound) :
    slotsOf hinj S.leader = S := by
  cases S; rfl

end Slots

end LeanDag
