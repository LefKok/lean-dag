import LeanDag.GC.ChopDecided
import LeanDag.Adaptive.Mysticeti
import LeanDag.Adaptive.Joiner
import LeanDag.Properties.Arcs.GC

/-!
# I5 — the joiner and the adaptive schedule, at the core

`Adaptive/Joiner.lean` at the core's cut. The schedule half is the
core's `Slots.chop` read as a `Rebases` witness; the verdict half is the
generic cross-cut agreement at `truncates_chop` with the chopped view.
The two constructions the generic theorem relates — truncating an
adaptive schedule and adapting a truncated one — are here
definitionally equal, so `slotsChop_slotsOf_eq` closes by `rfl`.

The deployment obligations are the generic file's: the policy's rule
must be horizon-stable (`Adaptive.HorizonStable`), and the base slot
must fall on an epoch boundary (`epochOf_add_of_dvd`).
-/

namespace LeanDag

namespace Integration

open Properties Adaptive

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator] {G d : ℕ}

/-! ## The schedule transformers commute -/

omit F in
/-- The cut rebases the schedule. A schedule fact with no universe in it. -/
theorem rebases_chop (hd : G ≤ S.slotRound d) : Rebases S (S.chop G d hd) G d where
  slotRound := fun k => by
    simp only [Slots.chop_slotRound]
    have := horizon_le_slotRound hd k
    omega
  leader := fun _ => rfl
  base := hd

omit F in
/-- Truncation preserves one-leader-per-round. -/
theorem injective_slotRound_chop (hd : G ≤ S.slotRound d)
    (hinj : Function.Injective S.slotRound) :
    Function.Injective (S.chop G d hd).slotRound :=
  (rebases_chop hd).injective hinj

omit F in
/-- **The transformers commute**, field by field: truncating an adaptive
schedule and adapting a truncated one give the same rounds and the
same leaders, provided the assignment used in the truncation is the
original one shifted past the base slot. -/
theorem slotsChop_slotsOf (hd : G ≤ S.slotRound d)
    (hinj : Function.Injective S.slotRound) (a : ℕ → Validator)
    (hd' : G ≤ (slotsOf hinj a).slotRound d) (k : ℕ) :
    ((slotsOf hinj a).chop G d hd').slotRound k
        = (slotsOf (S := S.chop G d hd)
            (injective_slotRound_chop hd hinj) (fun m => a (d + m))).slotRound k
      ∧ ((slotsOf hinj a).chop G d hd').leader k
        = (slotsOf (S := S.chop G d hd)
            (injective_slotRound_chop hd hinj) (fun m => a (d + m))).leader k :=
  ⟨rfl, rfl⟩

omit F in
/-- **And as schedules.** Both sides are rebases of `slotsOf hinj a` by
the same offset from the same base slot, so `Rebases.unique` would
settle it; at the core the two constructions are definitionally equal. -/
theorem slotsChop_slotsOf_eq (hd : G ≤ S.slotRound d)
    (hinj : Function.Injective S.slotRound) (a : ℕ → Validator)
    (hd' : G ≤ (slotsOf hinj a).slotRound d) :
    (slotsOf hinj a).chop G d hd'
      = slotsOf (S := S.chop G d hd) (injective_slotRound_chop hd hinj)
          (fun m => a (d + m)) := rfl

/-- **I5's verdict half**, at the core: the joiner and the network agree
on every shared slot, from an arbitrary view of the truncation. -/
theorem joiner_decided_agree (hd : G ≤ S.slotRound d)
    (hinj : Function.Injective S.slotRound) (a : ℕ → Validator)
    {W : View Validator BlockId Payload (chop U G)}
    {V : View Validator BlockId Payload U} {k : ℕ} {w v : Option BlockId}
    (hW : Decided (S := slotsOf (S := S.chop G d hd)
            (injective_slotRound_chop hd hinj) (fun m => a (d + m)))
          (chop U G) W k w)
    (hV : Decided (S := slotsOf hinj a) U V (d + k) v) : w = v :=
  Adaptive.joiner_decided_agree MysticetiProperties.agree MysticetiProperties.banded
    (Properties.Arcs.truncates_chop hd) hinj a
    (Properties.Arcs.viewAgreeAbove_chop (V := V)) hW hV

/-! ## The policy half, at the core -/

section Policy

variable {P : AdaptivePolicy Validator BlockId Payload}
variable {pick' : (U' : BlockUniverse Validator BlockId Payload) →
      View Validator BlockId Payload U' → (ℕ → Option BlockId) → ℕ → Validator}

/-- **I5, the assignment half.** Under a horizon-stable rule a joiner
computes exactly the leaders the network is using. -/
theorem joiner_assign_agree (hs : HorizonStable P G d pick')
    {V : View Validator BlockId Payload U} (R : AdaptiveRun P U V)
    (V' : View Validator BlockId Payload (chop U G)) (k : ℕ) :
    pick' (chop U G) V' (fun m => R.vdct (d + m)) k = R.assign (d + k) :=
  Adaptive.joiner_assign_agree hs (Properties.Arcs.sustains_chop (U := U) (G := G)) R V' k

/-- The joiner's schedule *is* the network's, seen from another origin. -/
theorem joiner_leader_agree (hd : G ≤ S.slotRound d) (hs : HorizonStable P G d pick')
    {V : View Validator BlockId Payload U} (R : AdaptiveRun P U V)
    (V' : View Validator BlockId Payload (chop U G)) (k : ℕ) :
    (slotsOf (S := S.chop G d hd) (injective_slotRound_chop hd P.inj)
        (fun m => pick' (chop U G) V' (fun j => R.vdct (d + j)) m)).leader k
      = (slotsOf P.inj R.assign).leader (d + k) :=
  Adaptive.joiner_leader_agree hs (Properties.Arcs.truncates_chop hd) R V' k

/-- **I5, whole.** A joiner that computed its own schedule from its own
truncated view, under a horizon-stable rule, agrees with the network's
run on every shared slot: *pruning does not split the ledger, even when
the schedule is derived from it.* -/
theorem joiner_run_decided_agree (hd : G ≤ S.slotRound d)
    (hs : HorizonStable P G d pick')
    {V : View Validator BlockId Payload U} (R : AdaptiveRun P U V)
    (V' : View Validator BlockId Payload (chop U G))
    {W : View Validator BlockId Payload (chop U G)} {k : ℕ} {w v : Option BlockId}
    (hW : Decided (S := slotsOf (S := S.chop G d hd)
            (injective_slotRound_chop hd P.inj)
            (fun m => pick' (chop U G) V' (fun j => R.vdct (d + j)) m))
          (chop U G) W k w)
    (hV : Decided (S := slotsOf P.inj R.assign) U V (d + k) v) : w = v :=
  Adaptive.joiner_run_decided_agree MysticetiProperties.agree MysticetiProperties.banded
    hs (Properties.Arcs.truncates_chop hd) R V'
    (Properties.Arcs.viewAgreeAbove_chop (V := V)) hW hV

end Policy

end Integration

end LeanDag
