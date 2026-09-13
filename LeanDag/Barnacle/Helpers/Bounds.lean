import LeanDag.Barnacle.Model.Run
/-!
# The two rounds a boundary lies between

Not part of the audit surface. `Boundary` says the next configuration
takes force somewhere between the round the reconfiguration falls due and
the round the anchor is found at, and a run's `anchor_commits` supplies
the hypothesis both clauses want. These are those two facts at a run,
which is the only form the rest of the development uses them in.

The pair relates the two bounds of a run: `boundary_le_anchor` says the
output never outruns the decisions, `threshold_le_boundary` that a
configuration governs at least its interval. A consumer wanting a verdict
for a slot the configuration *output* goes through `closed_on_range`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : BaseRule Validator BlockId Payload} {P : Params} {B : Boundary Validator}
variable {upd : UpdateRule R} {C₀ : Config Validator} {U : R.Universe} {V : R.View U}
variable {K : ℕ}

/-- **A configuration governs at least its interval**: the next one does
not take force before the reconfiguration falls due, wherever the
boundary is put. A deployer reading `interval` as "how long a
configuration lasts" is reading a lower bound, not an equality. -/
theorem threshold_le_boundary (Rn : Run R P B upd C₀ U V K) {k : ℕ} (hk : k < K) :
    Rn.start k + (Rn.cfg k).interval ≤ Rn.start (k + 1) := by
  rw [Rn.start_succ k hk]
  exact B.ge_threshold _ _ _ (Rn.anchor_commits k hk).2

/-- **And it decides at least what it outputs**: the boundary is at or
below the anchor's round, which is how far `closed` reaches. The two
together are the whole of what a `Boundary` gives a run. -/
theorem boundary_le_anchor (Rn : Run R P B upd C₀ U V K) {k : ℕ} (hk : k < K) :
    Rn.start (k + 1) ≤ (Rn.cfg k).roundOf (Rn.anchor k) := by
  rw [Rn.start_succ k hk]
  exact B.le_anchor _ _ _ (Rn.anchor_commits k hk).2

/-- `start` grows strictly across a closed configuration: the interval is
positive, so the boundary moves. -/
theorem start_lt_succ (Rn : Run R P B upd C₀ U V K) {k : ℕ} (hk : k < K) :
    Rn.start k < Rn.start (k + 1) := by
  have := (Rn.bounds k).2.1
  have := threshold_le_boundary Rn hk
  omega

/-- `start` is monotone over the determined configurations. -/
theorem start_mono (Rn : Run R P B upd C₀ U V K) {k k' : ℕ} (h : k ≤ k')
    (hK : k' ≤ K) : Rn.start k ≤ Rn.start k' := by
  induction h with
  | refl => exact le_rfl
  | @step m _ ih => exact le_trans (ih (by omega)) (start_lt_succ Rn (by omega)).le

/-- **Every slot a configuration outputs is decided by it.** A run
records decisions to the anchor and output to the boundary; this is the
half a ledger needs. -/
theorem closed_on_range (Rn : Run R P B upd C₀ U V K) {k : ℕ} (hk : k < K) {κ : ℕ}
    (hlo : Rn.start k < (Rn.cfg k).roundOf κ)
    (hhi : (Rn.cfg k).roundOf κ ≤ Rn.start (k + 1)) :
    R.Decided (Rn.cfg k).sched V κ (Rn.vdct k κ) :=
  Rn.closed k hk κ hlo (le_trans hhi (boundary_le_anchor Rn hk))

/-- **The rule is applied to exactly the range's verdicts.** `Run.spanOf`
and the structure's own `update` field name one function, so a reader
chasing what a reputation rule sees can read `spanOf` and stop. -/
theorem update_spanOf (Rn : Run R P B upd C₀ U V K) (k : ℕ) (hk : k < K)
    (A : BlockId) (hA : Rn.vdct k (Rn.anchor k) = some A) :
    (Rn.cfg (k + 1), Rn.backoff (k + 1))
      = upd (Rn.cfg k) (Rn.backoff k) U V (Rn.spanOf k) A :=
  Rn.update k hk A hA

end Barnacle

end LeanDag
