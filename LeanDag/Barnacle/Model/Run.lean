import LeanDag.Barnacle.Model.Window
/-!
# Barnacle: the run

Configuration `k` (`barnacle.md` §5) is in force above round `start k`,
and its range runs to the next anchor's round; every slot of the range
is decided against the configuration's own schedule `(cfg k).sched`,
which is what makes the dependency on `k` well-founded. A configuration
carries its leaders, its slots per round and its interval together
(`Model/Config.lean`), so a reconfiguration replaces all three at once.
`PartialRun` closes configurations `0, …, K` from a genesis
configuration `C₀`: their ranges decided in full, `K` itself only determined — there is no total run, since a
universe holds finitely many blocks. The run starts after round `0`, so
round `0` lies in no range, matching Algorithm 2.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A run closed up to height `K`.** Configurations `0, …, K` are
determined, and the ranges of configurations below `K` are decided in
full.

**The ranges partition the rounds, and the schedule above a range names
anchors only.** Configuration `k` governs the rounds
`(start k, start (k + 1)]`, and `start (k + 1)` is the anchor's own
round, so consecutive ranges abut and no round belongs to two of them.
`rangeLedger` reads exactly the range, and `round_of_mem_ledgerUpto`
says the ledger to any height stops at that height's start round.

`(cfg k).sched` is nevertheless total, and names a leader at every round
above the range as well as inside it. That is deliberate and it is what
the algorithm does: a validator settles configuration `k`'s range while
`cfg k` is still its active schedule at every round, reading slots above
the range as anchors when an indirect decision needs them, and only then
finds the anchor that closes the range and switches. So the extension is
the schedule in force when those derivations are performed, and the
anchors it names are agreed for the same reason the range's verdicts
are. What is never done is to *output* a slot above the range under
`cfg k`; that slot belongs to configuration `k + 1`'s range and is
decided again, under `cfg (k + 1)`, for the ledger.

`closed` is the paper's `TryDecide`: every slot of the range — the
rounds after `start k`, through the anchor's round `start (k + 1)` —
decided against the configuration's schedule. `anchor_commits`
and `anchor_least` are `TryCommit`'s trigger: the anchor is the least
committed slot whose round exceeds `start k + (cfg k).interval`.
`update` is `UpdateLeaders`, for an arbitrary rule. `bounds` is a clause
of the run because the rule is arbitrary; for the AIMD rule it is a
theorem. -/
structure Run (R : BaseRule Validator BlockId Payload) (P : Params)
    (B : Boundary Validator) (upd : UpdateRule R) (C₀ : Config Validator)
    (U : R.Universe) (V : R.View U) (K : ℕ) where
  /-- The round after which configuration `k` is in force. -/
  start : ℕ → ℕ
  /-- Configuration `k`: its leaders, its slots per round, its interval. -/
  cfg : ℕ → Config Validator
  /-- The back-off of configuration `k`. -/
  backoff : ℕ → ℕ
  /-- The slot, in `(cfg k).sched`, of the anchor that closes
  configuration `k`. -/
  anchor : ℕ → ℕ
  /-- `vdct k κ`: the verdict of slot `κ` of `(cfg k).sched`. -/
  vdct : ℕ → ℕ → Option BlockId
  /-- The run starts after round `0`, in the genesis configuration. -/
  init : start 0 = 0 ∧ cfg 0 = C₀ ∧ backoff 0 = 0
  /-- Every configuration is within the parameters. -/
  bounds : ∀ k, (cfg k).InBounds P
  /-- **Decisions run to the anchor** (`TryDecide`): every slot after
  `start k` and at or below the anchor's round is decided against the
  configuration's schedule — the schedule in force throughout, since the
  anchor has not been found and the switch has not happened. -/
  closed : ∀ k, k < K → ∀ κ, start k < (cfg k).roundOf κ →
    (cfg k).roundOf κ ≤ (cfg k).roundOf (anchor k) →
      R.Decided (cfg k).sched V κ (vdct k κ)
  /-- The anchor is committed, past the round the reconfiguration falls
  due … (`TryCommit`) -/
  anchor_commits : ∀ k, k < K →
    (∃ A, vdct k (anchor k) = some A) ∧
      start k + (cfg k).interval < (cfg k).roundOf (anchor k)
  /-- … and is the least such slot. -/
  anchor_least : ∀ k, k < K → ∀ κ, κ < anchor k →
    start k + (cfg k).interval < (cfg k).roundOf κ → vdct k κ = none
  /-- The next configuration takes force where the boundary says
  (`UpdateLeaders`). This is the **only** field the two mechanisms differ
  in: `Boundary.atAnchor` takes the anchor's round, `Boundary.atThreshold`
  the round the reconfiguration fell due. -/
  start_succ : ∀ k, k < K → start (k + 1) = B.next (cfg k) (start k) (anchor k)
  /-- The next configuration is the rule's, on the anchor's block and the
  verdicts of the range just output. -/
  update : ∀ k, k < K → ∀ A, vdct k (anchor k) = some A →
    (cfg (k + 1), backoff (k + 1)) = upd (cfg k) (backoff k) U V
      (spanVdct (cfg k) (start k) (start (k + 1)) (vdct k)) A

/-- **Barnacle's run**: the next configuration in force at the anchor's
own round, so the range it orders is the range it decided. -/
abbrev PartialRun (R : BaseRule Validator BlockId Payload) (P : Params)
    (upd : UpdateRule R) (C₀ : Config Validator) (U : R.Universe) (V : R.View U)
    (K : ℕ) : Type :=
  Run R P Boundary.atAnchor upd C₀ U V K

variable {R : BaseRule Validator BlockId Payload} {P : Params} {B : Boundary Validator}
variable {upd : UpdateRule R} {C₀ : Config Validator} {U : R.Universe} {V : R.View U}

/-- The schedule of configuration `k`. -/
abbrev Run.sched {K : ℕ} (Rn : Run R P B upd C₀ U V K) (k : ℕ) :
    Slots Validator :=
  (Rn.cfg k).sched

/-! ## The ledger -/

/-- **The verdicts configuration `k`'s update rule is handed**: the range
it decided, `(start k, start (k + 1)]`, and `none` outside. The `update`
field names this function; `spanVdct_agree` is why two validators name
one function. -/
def Run.spanOf {K : ℕ} (Rn : Run R P B upd C₀ U V K) (k : ℕ) :
    ℕ → Option BlockId :=
  spanVdct (Rn.cfg k) (Rn.start k) (Rn.start (k + 1)) (Rn.vdct k)

/-- The committed blocks of the slots `[lo, hi)`, in slot order. -/
def ledgerOf (v : ℕ → Option BlockId) (lo hi : ℕ) : List BlockId :=
  (List.range' lo (hi - lo)).filterMap v

/-- The ledger of configuration `k`: its range's committed blocks, from
the first slot after `start k` to the last slot of round `start (k + 1)`.
Meaningful for the closed configurations, `k < K`. -/
def Run.rangeLedger {K : ℕ} (Rn : Run R P B upd C₀ U V K) (k : ℕ) :
    List BlockId :=
  ledgerOf (Rn.vdct k) ((Rn.cfg k).cum (Rn.start k + 1))
    ((Rn.cfg k).cum (Rn.start (k + 1) + 1))

/-- The ledger through configuration `K' − 1`: the ranges' ledgers,
concatenated in configuration order. Meaningful for `K' ≤ K`. -/
def Run.ledgerUpto {K : ℕ} (Rn : Run R P B upd C₀ U V K) (K' : ℕ) :
    List BlockId :=
  (List.range K').flatMap Rn.rangeLedger

end Barnacle

end LeanDag
