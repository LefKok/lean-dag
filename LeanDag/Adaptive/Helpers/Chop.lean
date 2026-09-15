import LeanDag.Barnacle.Chop
import LeanDag.Properties.Compose
/-!
# The joiner, at a configuration

I5 for the segmented arc (`adaptive-leaders.md` §9). A validator that
joins from a universe pruned below round `G` renumbers its slots from
`C.cum G`, and runs the same score on what it holds. Two halves, as
before:

* **the verdicts** — across the cut, the joiner's derivation and the
  network's agree on every shared slot. Nothing about adaptivity enters:
  `Config.rebases_chop` makes the cut a truncation at the configuration's
  own schedule, and cross-cut agreement holds at any schedule.
* **the schedule** — `HorizonStable` is what a score owes: from views
  agreeing above the cut it returns the same configuration the network
  installs, chopped. A score that only reassigns leaders has it at every
  cut (`horizonStable_relabel`), which is AL11's whole family; what the
  condition rules out is a score whose *choice* of reassignment is read
  from rounds the horizon has removed.

What a cut re-indexes is the configuration, and `Config.chop` is that
re-indexing.
-/

namespace LeanDag

namespace Adaptive

open Barnacle Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-! ## The verdict half -/

section Verdicts

variable {R : DagRule Validator BlockId Payload}

/-- **Across the cut the verdicts agree.** The joiner, deriving at the
chopped configuration's schedule on any view of the truncation, and the
network, deriving at the configuration's own, give one verdict to every
shared slot. -/
theorem joiner_decided_agree (ha : Agree R) (hb : Banded R)
    {U U' : R.Universe} {G : ℕ} {C : Config Validator}
    (ht : Truncates R U U' C.sched (C.chop G).sched G (C.cum G))
    {V : R.View U} {V' : R.View U'} (hv : ViewAgreeAbove R V V' G)
    {W : R.View U'} {k : ℕ} {w v : Option BlockId}
    (hW : R.Decided (C.chop G).sched W k w)
    (hV : R.Decided C.sched V (C.cum G + k) v) : w = v :=
  decided_agree_rebased ha hb (Rebased.of_truncates ht) hv
    (by have := ht.slotRound k; omega) hW hV

end Verdicts

/-! ## The schedule half

`HorizonStable` is stated on the bare score-shaped function over a
`DagRule` rather than on `Score R`: the cut re-indexes, and a statement
tied to the interface a score is installed through would have to be
transported across that re-indexing. An `Adaptive.Score R` has exactly
this shape at `R.toDagRule`. -/

section Schedule

variable {R : DagRule Validator BlockId Payload}

/-- **Horizon-stability.** A score is horizon-stable at `G` when, from
two views agreeing above `G`, it installs the same configuration on the
cut that it installs on the whole — re-indexed by `Config.chop`.

**Both of the score's readings are re-indexed, not just the
configuration.** A joiner numbers its slots from the first slot of round
`G`, so where the network's score reads verdict `v κ`, the joiner reads
`v (C.cum G + κ)`: it holds the same verdicts, at its own indices. Giving
both sides the same `v` would ask the joiner for a function over slots it
does not have.

The condition rules out scores incompatible with pruning. A score that
only relabels who leads meets it at every cut; one that reads the DAG to
choose the relabelling meets it as long as it reads above the cut, where
`ViewAgreeAbove` gives it the same answer; and one that names an absolute
slot of the verdict function does not meet it at all, which
`LeanDagTest/Adaptive/Asynchronous.lean` exhibits. -/
def HorizonStable
    (score : (U : R.Universe) → R.View U → (ℕ → Option BlockId) →
      Config Validator → Config Validator)
    (G : ℕ) : Prop :=
  ∀ (U U' : R.Universe) (V : R.View U) (V' : R.View U'), ViewAgreeAbove R V V' G →
    ∀ (C : Config Validator) (v : ℕ → Option BlockId),
      score U' V' (fun κ => v (C.cum G + κ)) (C.chop G) = (score U V v C).chop G

/-- **The joiner installs the network's configuration.** Under a
horizon-stable score, what a joiner computes from its own truncated view
is exactly what the network installed, with the pruned rounds dropped —
so the two run the same leaders on every round both have. -/
theorem joiner_config_agree
    {score : (U : R.Universe) → R.View U → (ℕ → Option BlockId) →
      Config Validator → Config Validator}
    {G : ℕ} (hs : HorizonStable score G)
    {U U' : R.Universe} {V : R.View U} {V' : R.View U'}
    (hv : ViewAgreeAbove R V V' G) (C : Config Validator)
    (v : ℕ → Option BlockId) :
    score U' V' (fun κ => v (C.cum G + κ)) (C.chop G) = (score U V v C).chop G :=
  hs U U' V V' hv C v

/-- And so the joiner's schedule is the network's, seen from the cut's
own origin. -/
theorem joiner_leader_agree
    {score : (U : R.Universe) → R.View U → (ℕ → Option BlockId) →
      Config Validator → Config Validator}
    {G : ℕ} (hs : HorizonStable score G)
    {U U' : R.Universe} {V : R.View U} {V' : R.View U'}
    (hv : ViewAgreeAbove R V V' G) (C : Config Validator)
    (v : ℕ → Option BlockId) (k : ℕ) :
    (score U' V' (fun κ => v (C.cum G + κ)) (C.chop G)).sched.leader k
      = (score U V v C).sched.leader ((score U V v C).cum G + k) := by
  rw [joiner_config_agree hs hv C v]
  exact ((score U V v C).rebases_chop G).leader k

/-- The score that installs what it was given is horizon-stable at every
cut: what it was given was already chopped. `Adaptive.Score.const` is
this one, and AL15's conservativity is its consequence. -/
theorem horizonStable_const (G : ℕ) :
    HorizonStable (R := R) (fun _ _ _ C => C) G := fun _ _ _ _ _ _ _ => rfl

/-- **A score that only reassigns leaders is horizon-stable**, at every
cut and with no condition on the cut. Relabelling who leads commutes with
dropping the rounds below a horizon, because both act on the leader
function pointwise and neither moves a round. This is the case the
obligation exists for — `Score.permute` is AL11's reassignment family, so
a joiner running a permuting score computes the network's leaders whatever
the horizon.

The condition bites for a score whose *choice* of reassignment is read
off the DAG or off the verdicts: it then has to make that choice from
what survives the cut, and at its own indices. `ViewAgreeAbove` gives it
the DAG above `G`; nothing gives it either below. -/
theorem horizonStable_relabel (σ : Validator → Validator)
    (hinj : ∀ (C : Config Validator) r i j, i < C.slotsAt r → j < C.slotsAt r →
      σ (C.lead r i) = σ (C.lead r j) → i = j) (G : ℕ) :
    HorizonStable (R := R)
      (fun _ _ _ C =>
        { slotsAt := C.slotsAt, slotsAt_pos := C.slotsAt_pos
          lead := fun r i => σ (C.lead r i)
          keyed := fun r i j hi hj h => hinj C r i j hi hj h
          interval := C.interval }) G :=
  fun _ _ _ _ _ _ _ => rfl

end Schedule

end Adaptive

end LeanDag
