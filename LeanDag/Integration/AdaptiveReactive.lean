import LeanDag.Adaptive.Mysticeti
import LeanDag.Reactive.MysticetiProperties

/-!
# Adaptive leaders over reactive Mysticeti

`docs/target-properties.md` §4. The first result the schedule family
produces that the bespoke development did not have: Hammerhead-style
adaptive leaders over the *reactive* Mysticeti execution.

Safety is `adaptiveRun_agree` unchanged — the rule is the core's, and
the reactive discipline changes no verdict. Liveness is the generic
`Adaptive.run_exists` fed with `leaderCommits_reactive` in place of the
timed `leaderCommits`; nothing else moves. The precondition is staged,
as the generic theorem states it: at every height `E`, the reactive
clauses hold under the schedule the policy computes from a height-`E`
partial run's verdicts, over the slots `[W, W·(E+2))` that schedule has
determined. Any two height-`E` runs compute the same leaders there
(`partialRun_agree` and `adapted`), so the hypothesis names one
schedule prefix per height — the one the validators followed.
-/

namespace LeanDag

namespace Integration

open Properties MysticetiProperties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {P : AdaptivePolicy Validator BlockId Payload} {T : Finset Validator} {c : ℕ}

/-- **Partial runs exist at every height, reactively.** -/
theorem exists_partialRun_reactive (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : SpansEligible (Validator := Validator) c)
    (V : View Validator BlockId Payload U) (E : ℕ)
    (hlive : ∀ (E' : ℕ), E' < E → ∀ (A : PartialRun P U V E'),
      reactiveLive (slotsOf P.inj (fun m => P.pick U V A.vdct m)) V T P.W (P.W * (E' + 2))) :
    Nonempty (PartialRun P U V E) :=
  Adaptive.exists_partialRun bounded schedLocal leaderCommits_reactive
    (descends_slotsOf (P := P) hc hspans) hruns V E hlive

/-- **The adaptive fixpoint exists over reactive Mysticeti.** Under a
policy that places runs, with the reactive clauses holding at every
height under the schedule that height computes, a total adaptive run
exists; with `adaptiveRun_agree` it is unique. -/
theorem adaptiveRun_exists_reactive (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : SpansEligible (Validator := Validator) c)
    (V : View Validator BlockId Payload U)
    (hlive : ∀ (E : ℕ) (A : PartialRun P U V E),
      reactiveLive (slotsOf P.inj (fun m => P.pick U V A.vdct m)) V T P.W (P.W * (E + 2))) :
    Nonempty (AdaptiveRun P U V) :=
  Adaptive.run_exists bounded agree schedLocal leaderCommits_reactive
    (descends_slotsOf (P := P) hc hspans) hruns V hlive

end Integration

end LeanDag
