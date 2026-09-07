import LeanDag.Adaptive.Policy
import LeanDag.Properties.Derived.Bounded
/-!
# The adaptive run, and safety as uniqueness of the fixpoint

A `Run` is a schedule-and-verdict pair coherent with a policy: every
slot's verdict is derivable with anchors inside its epoch window,
against the schedule the policy computes from the verdicts themselves.
Existence and uniqueness are deliberately separated, mirroring the base
development's split between the `Decided` relation and `decided_unique`:
**uniqueness is the safety theorem, existence is the liveness theorem.**

The safety argument (`run_agree`) is a strong induction on epochs in
which nothing about counting is ever re-proved. At epoch `e` the verdict
prefixes of both runs agree below by hypothesis, so `adapted` forces the
two assignments to agree through epoch `e + 1`, so `DecidedBelow.reschedule` places
both runs' epoch-`e` derivations in the *same* `Slots` instance — where
agreement is `Agree`, through `Bounded`. The theorem carries **no
fairness, synchrony or view hypothesis of any kind**: adaptivity is safe
unconditionally, for arbitrary — even adversarial — adapted policies,
and only liveness prices the policy's choices.

Everything here is stated over a `Properties.DagRule` and one property,
`Agree`; no protocol is named. The bound a run carries is
`Properties.DecidedBelow`, a definition rather than a second relation
the carrier supplies, so its laws are theorems and a protocol proves
none of them.
The induction is stated over *partial* runs — closed up to an epoch
height — so that two validators that have not decided equally far agree
on their common prefix; total runs are the special case at every height.
Conservativity (`Policy.const_run_decided`) anchors the definitions:
under the constant policy a run's verdicts are ordinary `Decided`
verdicts of the base schedule.
-/

namespace LeanDag

namespace Adaptive

open Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}
variable [S : Slots Validator]

/-- A run closed up to epoch height `E`: verdicts derived for every slot
of epochs `< E`, the schedule coherent as far as those derivations read
it (epochs `< E + 1`). What a validator holds mid-execution. -/
structure PartialRun (P : Policy R) (U : R.Universe) (V : R.View U) (E : ℕ) where
  /-- The leader assignment. -/
  assign : ℕ → Validator
  /-- The verdicts. -/
  vdct : ℕ → Option BlockId
  /-- Every slot of a closed epoch is decided inside its window: anchors
  strictly below the start of epoch `e + 2`. -/
  closed : ∀ k, epochOf P.W k < E →
    DecidedBelow R (slotsOf P.inj assign) (P.W * (epochOf P.W k + 2)) V k (vdct k)
  /-- The assignment is the policy's, computed on this view, as far as
  the derivations read it. -/
  coherent : ∀ m, epochOf P.W m < E + 1 → assign m = P.pick U V vdct m

/-- A total run: the adaptive fixpoint itself. -/
structure Run (P : Policy R) (U : R.Universe) (V : R.View U) where
  /-- The leader assignment. -/
  assign : ℕ → Validator
  /-- The verdicts. -/
  vdct : ℕ → Option BlockId
  /-- Every slot is decided inside its epoch window. -/
  closed : ∀ k, DecidedBelow R (slotsOf P.inj assign)
    (P.W * (epochOf P.W k + 2)) V k (vdct k)
  /-- The assignment is the policy's, computed on this view, everywhere. -/
  coherent : ∀ m, assign m = P.pick U V vdct m

variable {P : Policy R} {U : R.Universe}

/-- A total run is partial at every height. -/
def Run.toPartial {V : R.View U} (A : Run P U V) (E : ℕ) : PartialRun P U V E where
  assign := A.assign
  vdct := A.vdct
  closed := fun k _ => A.closed k
  coherent := fun m _ => A.coherent m

section Agreement

variable (ha : Agree R)
include ha

/-- **The master agreement lemma.** Two partial runs over one universe —
whatever views, each computing its schedule on its own, whatever heights
— agree on the verdicts of their common epochs and on the assignments
those verdicts determine.

The strong induction the module docstring describes: verdict agreement
below an epoch forces assignment agreement through the epoch above it
(`adapted`), which forces verdict agreement at the epoch itself
(`DecidedBelow.reschedule`, then `Agree`). -/
theorem partialRun_agree {V₁ V₂ : R.View U} {E₁ E₂ : ℕ}
    (A₁ : PartialRun P U V₁ E₁) (A₂ : PartialRun P U V₂ E₂) :
    ∀ k, epochOf P.W k < min E₁ E₂ → A₁.vdct k = A₂.vdct k := by
  -- Strong induction on the epoch of the slot.
  suffices main : ∀ e k, epochOf P.W k = e → epochOf P.W k < min E₁ E₂ →
      A₁.vdct k = A₂.vdct k by
    intro k hk; exact main _ k rfl hk
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro k hke hk
    -- The assignments agree below this epoch's window.
    have hassign : ∀ m, m < P.W * (epochOf P.W k + 2) →
        A₁.assign m = A₂.assign m := by
      intro m hm
      have hme : epochOf P.W m < epochOf P.W k + 2 :=
        (epochOf_lt_iff P.W_pos).mpr hm
      rw [A₁.coherent m (by omega), A₂.coherent m (by omega)]
      refine P.adapted U V₁ V₂ A₁.vdct A₂.vdct m (fun j hj => ?_)
      exact ih (epochOf P.W j) (by omega) j rfl (by omega)
    -- Both derivations live in one instance; agreement is `Agree`.
    have h₁ := A₁.closed k (by omega)
    have h₂ := A₂.closed k (by omega)
    exact DecidedBelow.agree ha (h₁.reschedule (S' := slotsOf P.inj A₂.assign) rfl
      (fun m hm => (hassign m hm).symm)) h₂

/-- Assignments agree wherever the common verdicts determine them. -/
theorem partialRun_assign_agree {V₁ V₂ : R.View U} {E₁ E₂ : ℕ}
    (A₁ : PartialRun P U V₁ E₁) (A₂ : PartialRun P U V₂ E₂) :
    ∀ m, epochOf P.W m < min E₁ E₂ + 1 → A₁.assign m = A₂.assign m := by
  intro m hm
  rw [A₁.coherent m (by omega), A₂.coherent m (by omega)]
  refine P.adapted U V₁ V₂ A₁.vdct A₂.vdct m (fun j hj => ?_)
  exact partialRun_agree ha A₁ A₂ j (by omega)

/-- **Safety: the adaptive fixpoint is unique.** Two total runs over one
universe — derived from any two views, under no synchrony or fairness
hypothesis — hold the same verdicts and run the same schedule. Adaptive
validators cannot diverge, whatever the policy adapts to. -/
theorem run_agree {V₁ V₂ : R.View U} (A₁ : Run P U V₁) (A₂ : Run P U V₂) :
    (∀ k, A₁.vdct k = A₂.vdct k) ∧ (∀ m, A₁.assign m = A₂.assign m) := by
  constructor
  · intro k
    exact partialRun_agree ha (A₁.toPartial (epochOf P.W k + 1))
      (A₂.toPartial (epochOf P.W k + 1)) k (by omega)
  · intro m
    exact partialRun_assign_agree ha (A₁.toPartial (epochOf P.W m + 1))
      (A₂.toPartial (epochOf P.W m + 1)) m (by omega)

end Agreement

/-- **Conservativity.** Under the constant policy a run's verdicts are
ordinary `Decided` verdicts of the base schedule — the adaptive
development instantiates to the base one, per the house rule that a new
relation must collapse onto the old. With `Agree` this also pins each
`vdct k` to the unique base verdict. -/
theorem Policy.const_run_decided
    {W : ℕ} {hW : 0 < W} {hinj : Function.Injective S.slotRound} {V : R.View U}
    (A : Run (Policy.const (R := R) W hW hinj) U V) (k : ℕ) :
    R.Decided S V k (A.vdct k) := by
  have h := (A.closed k).reschedule (S' := slotsOf hinj S.leader) rfl
    (fun m _ => (A.coherent m).symm)
  rw [slotsOf_base hinj] at h
  exact h.toDecided

end Adaptive

end LeanDag
