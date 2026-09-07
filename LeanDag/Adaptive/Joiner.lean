import LeanDag.Adaptive.Run
import LeanDag.Properties.Compose
/-!
# The joiner: an adaptive schedule across a cut

An adaptive schedule is a function of the committed verdicts, and a cut
prunes the verdicts below a horizon. A validator that joins from the
truncation may therefore not hold what the policy reads, and if it
computes a different schedule, `run_agree` does not reach it: that
theorem quantifies over runs of one policy over **one** universe, and
the joiner's run is over another, under a re-indexed schedule.

The answer has two halves, and both are generic.

**The schedule half is arithmetic.** A cut rebases the schedule
(`Properties.Rebases`), and rebasing commutes with replacing the
leaders by an assignment: the truncation of an adaptive schedule is the
adaptation of the truncated one by the assignment shifted past the base
slot (`Rebases.slotsOf`). So the joiner and the network do not disagree
about who leads, provided the joiner can *produce* the shifted
assignment.

**Whether it can is a restriction on policies**, `HorizonStable`: the
joiner's rule, run on the truncation with its own slot numbering,
returns what the network's policy returns on the full history at the
corresponding slot. A policy that reads arbitrarily far back into
committed history cannot satisfy it, which is the content: such a
policy is incompatible with garbage collection.

**The verdict half is cross-cut agreement**, `decided_agree_rebased` at
the adaptive schedule. Nothing about adaptivity enters: `Agree` and
`Banded` hold at every schedule, so one that varies with the verdicts
is no harder than a fixed one. `joiner_run_decided_agree` puts the
halves together: pruning does not split the ledger, even when the
schedule is derived from it.

The obligation is stated on the joiner's *rule*, a bare `pick`-shaped
function, rather than on a `Policy`: a policy is indexed by its `Slots`
instance, so a joiner's inhabits a different type from the network's,
while `pick`'s type mentions no schedule and can be compared across the
re-indexing.

A cut is also read here through `RebasedAbove R U U' G G` alone, the
universe half of `Truncates`, because horizon-stability is about what
the two validators hold and not about how their slots are numbered.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

omit [Fintype Validator] [DecidableEq Validator] in
/-- A rebase preserves one-leader-per-round: the rebased rounds are the
original's, shifted and offset, so distinct slots keep distinct rounds. -/
theorem Rebases.injective {S S' : Slots Validator} {G d : ℕ} (h : Rebases S S' G d)
    (hinj : Function.Injective S.slotRound) : Function.Injective S'.slotRound := by
  intro k₁ k₂ hk
  have h₁ := h.slotRound k₁
  have h₂ := h.slotRound k₂
  have : S.slotRound (d + k₁) = S.slotRound (d + k₂) := by omega
  have := hinj this
  omega

/-- **Rebasing commutes with adapting.** Rebase a schedule and then
install an assignment shifted past the base slot, or install the
assignment first and rebase: the same rounds, the same leaders. -/
theorem Rebases.slotsOf {S S' : Slots Validator} {G d : ℕ} (h : Rebases S S' G d)
    (hinj : Function.Injective S.slotRound) (a : ℕ → Validator) :
    Rebases (slotsOf (S := S) hinj a)
      (slotsOf (S := S') (h.injective hinj) (fun m => a (d + m))) G d where
  slotRound := h.slotRound
  leader := fun _ => rfl
  base := h.base

/-- And so a cut at the base schedule is a cut at the adaptive one. -/
theorem Truncates.slotsOf {U U' : R.Universe} {S S' : Slots Validator} {G d : ℕ}
    (h : Truncates R U U' S S' G d) (hinj : Function.Injective S.slotRound)
    (a : ℕ → Validator) :
    Truncates R U U' (slotsOf (S := S) hinj a)
      (slotsOf (S := S') (h.toRebases.injective hinj) (fun m => a (d + m))) G d :=
  { h.toRebasedAbove, h.toRebases.slotsOf hinj a with }

end Properties

namespace Adaptive

open Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/- `S'` is declared before the instance `S` so that instance resolution,
which prefers the most recent local, finds the base schedule. -/
variable {S' : Slots Validator} [S : Slots Validator]

/-- **Horizon-stability.** The joiner's rule, run on a cut of the
universe with the joiner's own slot indices, returns what the network's
policy returns on the full history at the corresponding slot.

Read as a deployment obligation: *a validator that pruned below `G` and
re-indexed from `d` must still compute the leaders everyone else is
using.* -/
def HorizonStable (P : Policy R) (G d : ℕ)
    (pick' : (U' : R.Universe) → R.View U' → (ℕ → Option BlockId) → ℕ → Validator) : Prop :=
  ∀ (U U' : R.Universe), RebasedAbove R U U' G G →
    ∀ (V : R.View U) (V' : R.View U') (v : ℕ → Option BlockId) (k : ℕ),
      pick' U' V' (fun m => v (d + m)) k = P.pick U V v (d + k)

variable {P : Policy R} {G d : ℕ}
variable {pick' : (U' : R.Universe) → R.View U' → (ℕ → Option BlockId) → ℕ → Validator}

/-- **The assignment half.** Under a horizon-stable rule a joiner
computes exactly the leaders the network is using: its assignment at
its own slot `k` is the full run's assignment at slot `d + k`. -/
theorem joiner_assign_agree (hs : HorizonStable P G d pick')
    {U U' : R.Universe} (h : RebasedAbove R U U' G G)
    {V : R.View U} (A : Run P U V) (V' : R.View U') (k : ℕ) :
    pick' U' V' (fun m => A.vdct (d + m)) k = A.assign (d + k) := by
  rw [hs U U' h V V' A.vdct k, A.coherent (d + k)]

/-- The joiner's schedule *is* the network's, seen from another origin. -/
theorem joiner_leader_agree (hs : HorizonStable P G d pick')
    {U U' : R.Universe} (ht : Truncates R U U' S S' G d)
    {V : R.View U} (A : Run P U V) (V' : R.View U') (k : ℕ) :
    (slotsOf (S := S') (ht.toRebases.injective P.inj)
        (fun m => pick' U' V' (fun j => A.vdct (d + j)) m)).leader k
      = (slotsOf P.inj A.assign).leader (d + k) := by
  simp only [slotsOf_leader]
  exact joiner_assign_agree hs ht.toRebasedAbove A V' k

/-- **The verdict half.** Across a cut, the truncation under the shifted
assignment and the original under the assignment agree on every shared
slot, from any view of the truncation. `decided_agree_rebased` at the
adaptive schedule; nothing about adaptivity enters. -/
theorem joiner_decided_agree (ha : Agree R) (hb : Banded R)
    {U U' : R.Universe} (ht : Truncates R U U' S S' G d)
    (hinj : Function.Injective S.slotRound) (a : ℕ → Validator)
    {V : R.View U} {V' : R.View U'} (hv : ViewAgreeAbove R V V' G)
    {W : R.View U'} {k : ℕ} {w v : Option BlockId}
    (hW : R.Decided (slotsOf (S := S') (ht.toRebases.injective hinj) (fun m => a (d + m))) W k w)
    (hV : R.Decided (slotsOf (S := S) hinj a) V (d + k) v) : w = v :=
  decided_agree_rebased ha hb (Rebased.of_truncates (ht.slotsOf hinj a)) hv
    (by have := ht.slotRound k; change G ≤ S.slotRound (d + k); omega) hW hV

/-- **The joiner, whole.** A joiner that computed its own schedule from
its own view `V'` of the truncation, under a horizon-stable rule,
agrees with the network's run on every shared slot. The agreement is
read through some view `V₀` of the truncation agreeing with the
network's above the horizon, which a cut supplies. -/
theorem joiner_run_decided_agree (ha : Agree R) (hb : Banded R)
    (hs : HorizonStable P G d pick')
    {U U' : R.Universe} (ht : Truncates R U U' S S' G d)
    {V : R.View U} (A : Run P U V) (V' : R.View U')
    {V₀ : R.View U'} (hv : ViewAgreeAbove R V V₀ G)
    {W : R.View U'} {k : ℕ} {w v : Option BlockId}
    (hW : R.Decided (slotsOf (S := S') (ht.toRebases.injective P.inj)
            (fun m => pick' U' V' (fun j => A.vdct (d + j)) m)) W k w)
    (hV : R.Decided (slotsOf P.inj A.assign) V (d + k) v) : w = v := by
  have hassign : (fun m => pick' U' V' (fun j => A.vdct (d + j)) m)
      = fun m => A.assign (d + m) := by
    funext m; exact joiner_assign_agree hs ht.toRebasedAbove A V' m
  rw [hassign] at hW
  exact joiner_decided_agree ha hb ht P.inj A.assign hv hW hV

/-- The constant policy is horizon-stable exactly when the base slot is
the origin, which is the degenerate case, and the point is the
contrast: a rule that ignores verdicts still has to be *re-indexed* to
survive a cut. Horizon-stability is not only about how far back a
policy reads, but about whether it is stated relative to the reader's
own slot numbering. -/
theorem horizonStable_const_zero {W : ℕ} {hW : 0 < W}
    {hinj : Function.Injective S.slotRound} :
    HorizonStable (Policy.const (R := R) W hW hinj) G 0 (fun _ _ _ k => S.leader k) := by
  intro _ _ _ _ _ _ k
  change S.leader k = S.leader (0 + k)
  rw [Nat.zero_add]

end Adaptive

end LeanDag
