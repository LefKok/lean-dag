import LeanDag.Barnacle.Model.Window
/-!
# The run, at any boundary

Configuration `k` (`barnacle.md` §5) is in force above round `start k`.
It **decides** every slot through the round its anchor sits at, and
**outputs** the rounds `(start k, start (k + 1)]`. Where `start (k + 1)`
falls between those two is the `Boundary` the run is taken at, and it is
the only thing the two mechanisms of this development disagree about
(`adaptive-leaders.md` D19, D21): Barnacle switches at the anchor's own
round, so the range it outputs is the range it decided; HammerHead
switches where the reconfiguration fell due, and re-derives the rounds
between under the next configuration.

A configuration carries its leaders, its slots per round and its interval
together (`Model/Config.lean`), so a reconfiguration replaces all three
at once. A run closes configurations `0, …, K` from a genesis
configuration `C₀`: their ranges decided in full, `K` itself only
determined — there is no total run, since a universe holds finitely many
blocks. The run starts after round `0`, so round `0` lies in no range,
matching Algorithm 2.

**The ranges partition the rounds.** Consecutive ranges abut by
construction — configuration `k + 1` starts where `k` stopped — so no
round is output twice, whatever the boundary. `rangeLedger` reads exactly
the range and `round_of_mem_ledgerUpto` says the ledger to any height
stops at that height's start round.

**The schedule above a range names anchors only.** `(cfg k).sched` is
total, and names a leader at every round above the range as well as
inside it. That is deliberate and it is what the algorithm does: a
validator settles configuration `k` while `cfg k` is still its active
schedule at every round, reading slots above the range as anchors when an
indirect decision needs them, and only then finds the anchor and
switches. So the extension is the schedule in force when those
derivations are performed, and the anchors it names are agreed for the
same reason the range's verdicts are. What is never done is to *output* a
slot above the range under `cfg k`; that slot belongs to a later range
and is decided again for the ledger.

**Trusted core of the arc: definitions only.**
-/


namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A run closed up to height `K`**, at the boundary `B`.
Configurations `0, …, K` are determined, and the spans of configurations
below `K` are decided in full.

`closed` is the paper's `TryDecide` and `anchor_commits`/`anchor_least`
are `TryCommit`'s trigger: the anchor is the least committed slot whose
round exceeds `start k + (cfg k).interval`, the round the reconfiguration
falls due. `start_succ` is the only field the two mechanisms differ in.
`update` is `UpdateLeaders`, for an arbitrary rule, handed the verdicts
of the range just output. `bounds` is a clause of the run because the
rule is arbitrary; for the AIMD rule it is a theorem. -/
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
