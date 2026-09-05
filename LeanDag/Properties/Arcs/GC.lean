import LeanDag.Properties.Truncate
import LeanDag.Properties.Sustain
import LeanDag.GC.Chop
import LeanDag.GC.ChopDecided
import LeanDag.MysticetiProperties
import LeanDag.OdontocetiProperties
import LeanDag.Properties.Band
import LeanDag.Properties.Derived.Truncate

/-!
# Garbage collection, for any protocol with a band

`docs/target-properties.md` G2, the garbage-collection half.

**This file is thin on purpose, and it was not always going to be.** An
earlier version composed a locality property with a re-indexing one and
looked like it was doing work; the composition had hypotheses nothing
could satisfy, because restriction and renumbering are not separately
realisable (`Properties/Truncate.lean` records why). What replaced it
is a single statement, `LocalTruncate`, so garbage collection *is* that
statement applied, and the two corollaries below are the directions a
deployment uses.

A protocol no longer proves `LocalTruncate`. Once the band carries a
round offset, `Properties.LocalTruncate.of_banded` derives it from
`Banded` and `ViewSound`, so the depth sits in the band a protocol was
already proving for persistence and locality. What a mechanism still
owes is the witness that its cut stands in the `Truncates` relation.
-/

namespace LeanDag

namespace Properties

namespace Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}
variable {S S' : Slots Validator} {U U' : R.Universe} {G d : ℕ}
variable {V : R.View U} {V' : R.View U'}

/-- **A verdict survives the cut**, at the replica's own numbering. -/
theorem decided_of_truncate (h : LocalTruncate R) (ht : Truncates R U U' S S' G d)
    (hv : ViewAgreeAbove R V V' G) {k : ℕ} {v : Option BlockId}
    (hd : R.Decided S V (d + k) v) : R.Decided S' V' k v :=
  (h S S' U U' G d ht V V' hv k v).mp hd

/-- **And a verdict of the truncation is a verdict of the whole DAG**,
which is what lets a pruned replica be compared with one that never
pruned. -/
theorem decided_of_truncated (h : LocalTruncate R) (ht : Truncates R U U' S S' G d)
    (hv : ViewAgreeAbove R V V' G) {k : ℕ} {v : Option BlockId}
    (hd : R.Decided S' V' k v) : R.Decided S V (d + k) v :=
  (h S S' U U' G d ht V V' hv k v).mpr hd

/-! ## The agreement half

`decided_of_truncate` and its converse compare a verdict with *the same
validator's* verdict. What a deployment asks is different and stronger:
a validator that joined from the truncation holds an **arbitrary** view
of it, with no history below the cut and no relation to anyone's
full-history view, and must still agree.

`GC/ChopDecided.lean` proves that for the core (G4) and `GC/Horizon.lean`
across two horizons (G8), each by hand; `Integration/Hydrozoan` has its
own copy. None of that was necessary. `Agree` compares two views of one
universe, `LocalTruncate` puts the full-history verdict into the
truncation, and the two compose — so every rule with a band and
agreement has cross-cut agreement, and neither protocol needed to prove
it. -/

/-- **Cross-cut agreement.** A validator holding any view of the
truncation agrees, slot for slot, with a full-history validator. -/
theorem decided_agree_truncate (ha : Agree R) (hlt : LocalTruncate R)
    (ht : Truncates R U U' S S' G d) (hv : ViewAgreeAbove R V V' G)
    {W : R.View U'} {k : ℕ} {w v : Option BlockId}
    (hW : R.Decided S' W k w) (hV : R.Decided S V (d + k) v) : w = v :=
  ha S' W V' k w v hW ((hlt S S' U U' G d ht V V' hv k v).mp hV)

/-- **And across two horizons.** Validators cut at different depths
agree on every shared slot, matched through the absolute slot index.
Horizons need never be negotiated. -/
theorem decided_agree_horizons (ha : Agree R) (hlt : LocalTruncate R)
    {U₁ U₂ : R.Universe} {S₁ S₂ : Slots Validator} {G₁ d₁ G₂ d₂ : ℕ}
    (ht₁ : Truncates R U U₁ S S₁ G₁ d₁) (ht₂ : Truncates R U U₂ S S₂ G₂ d₂)
    {V₁ : R.View U₁} {V₂ : R.View U₂}
    (hv₁ : ViewAgreeAbove R V V₁ G₁) (hv₂ : ViewAgreeAbove R V V₂ G₂)
    {W₁ : R.View U₁} {W₂ : R.View U₂} {k₁ k₂ : ℕ}
    (halign : d₁ + k₁ = d₂ + k₂) {w₁ w₂ v : Option BlockId}
    (hW₁ : R.Decided S₁ W₁ k₁ w₁) (hW₂ : R.Decided S₂ W₂ k₂ w₂)
    (hV : R.Decided S V (d₁ + k₁) v) : w₁ = w₂ :=
  (decided_agree_truncate ha hlt ht₁ hv₁ hW₁ hV).trans
    (decided_agree_truncate ha hlt ht₂ hv₂ hW₂ (halign ▸ hV)).symm

/-! ## The liveness half, for the core

Garbage collection is a mechanism, so on the liveness side it *owes*
`Sustains` rather than consuming it, and the core's carrier is where the
obligation can be discharged against a real consumer. This section
imports the mechanism it is about and the protocol it serves, and no
other mechanism. -/

section Core

variable [Faults Validator] {U : BlockUniverse Validator BlockId Payload} {G : ℕ}

/-- **The cut sustains the core from its horizon.** -/
theorem sustains_chop :
    Sustains (MysticetiProperties.mysticetiRule (Payload := Payload)) U (chop U G) G G where
  mem := fun b => by
    show (b ∈ U.ids ∧ G ≤ (U.block b).round) ↔
      (b ∈ (chop U G).ids ∧ G ≤ ((chop U G).block b).round + G)
    rw [mem_chop_ids, chop_block_eq, chopBlock_round]
    constructor
    · rintro ⟨hb, hr⟩
      refine ⟨⟨hb, hr⟩, ?_⟩
      rw [Nat.sub_add_cancel hr]; exact hr
    · rintro ⟨⟨hb, hr⟩, _⟩; exact ⟨hb, hr⟩
  round := fun b _ hr => by
    have hr' : G ≤ (U.block b).round := hr
    show ((chop U G).block b).round + G = (U.block b).round
    rw [chop_block_eq, chopBlock_round]; omega
  creator := fun b _ _ => by
    show ((chop U G).block b).creator = (U.block b).creator
    rw [chop_block_eq, chopBlock_creator]
  refs := fun b _ hr => by
    show ((chop U G).block b).refs = (U.block b).refs
    rw [chop_block_eq, chopBlock_refs_of_lt hr]

/-- **The reactive commit survives the cut** — the consumer test, from
the obligation rather than from `chop` directly. -/
theorem directCommit_chop {T : Finset Validator} {r : ℕ} {L : BlockId}
    (hr : G ≤ r) (hcard : quorumCard Validator ≤ T.card)
    (hpop : LeanDag.PopulatedOn U T (r + 2)) (hc : CertifiesAt U T r L) :
    DirectCommit (chop U G) L (r - G) :=
  MysticetiProperties.directCommit_of_sustains sustains_chop hr hr hcard hpop hc

end Core


/-! ## The canonical cut is a truncation, and the arc's theorems follow

With the band carrying an offset, truncation invariance is no longer an
obligation: `Properties.LocalTruncate.of_banded` derives it for any rule
with a band. What is left for this file is the **witness** — that the
cut the mechanism builds stands in the `Truncates` relation — and the
observation that the arc's own two transport theorems come back out of
the property with no induction.

That is the consumer test the arc asks for, and it measures what the
offset removed: `GC/ChopDecided.lean` proves those two by structural
induction over the decision relation, and here they are again, from a
property proved once for other reasons. -/

section CoreTruncate

variable [Faults Validator] {U : BlockUniverse Validator BlockId Payload}
variable {S : Slots Validator} {G d : ℕ}

/-- **The cut is a truncation.** The witness `Truncates` was written to
have, exhibited before anything is proved from it. -/
theorem truncates_chop (hd : G ≤ S.slotRound d) :
    Truncates (MysticetiProperties.mysticetiRule (Payload := Payload))
      U (chop U G) S (S.chop G d hd) G d where
  mem := fun b => by
    show (b ∈ U.ids ∧ G ≤ (U.block b).round) ↔
      (b ∈ (chop U G).ids ∧ G ≤ ((chop U G).block b).round + G)
    rw [mem_chop_ids, chop_block_eq, chopBlock_round]
    constructor
    · rintro ⟨hb, hr⟩; exact ⟨⟨hb, hr⟩, by omega⟩
    · rintro ⟨⟨hb, hr⟩, -⟩; exact ⟨hb, hr⟩
  round := fun b hb hr => by
    have hr' : G ≤ (U.block b).round := hr
    show ((chop U G).block b).round + G = (U.block b).round
    rw [chop_block_eq, chopBlock_round]; omega
  creator := fun b _ _ => by
    show ((chop U G).block b).creator = (U.block b).creator
    rw [chop_block_eq, chopBlock_creator]
  refs := fun b _ hr => by
    show ((chop U G).block b).refs = (U.block b).refs
    rw [chop_block_eq, chopBlock_refs_of_lt hr]
  slotRound := fun k => by
    have := horizon_le_slotRound hd k
    show S.slotRound (d + k) - G + G = S.slotRound (d + k)
    omega
  leader := fun _ => rfl
  base := hd

/-- **G3 re-derived, with no induction of its own.** Both directions of
the cut's verdict transport, from the band. -/
theorem decided_chop_iff (hd : G ≤ S.slotRound d)
    {V : View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId} :
    Decided U V (d + k) v ↔ Decided (S := S.chop G d hd) (chop U G) (V.chop G) k v :=
  LocalTruncate.of_banded MysticetiProperties.banded
    S (S.chop G d hd) U (chop U G) G d (truncates_chop hd) V (V.chop G)
    (fun b hb hr => by
      show b ∈ V.ids ↔ b ∈ (V.chop G).ids
      rw [View.chop_ids, Finset.mem_filter]
      exact ⟨fun h => ⟨h, hr⟩, fun h => h.1⟩) k v

/-- **The chopped view agrees with the original above the cut**, which
is the view hypothesis the two theorems below need. -/
theorem viewAgreeAbove_chop {V : View Validator BlockId Payload U} :
    ViewAgreeAbove (MysticetiProperties.mysticetiRule (Payload := Payload))
      V (V.chop G) G :=
  fun b _ hr => by
    show b ∈ V.ids ↔ b ∈ (V.chop G).ids
    rw [View.chop_ids, Finset.mem_filter]
    exact ⟨fun h => ⟨h, hr⟩, fun h => h.1⟩

/-- **G4 re-derived.** `GC/ChopDecided.decided_agree_chop` proves this
by running the core's uniqueness inside the truncation and carrying the
verdict across by induction. Here it is two properties applied. -/
theorem decided_agree_chop (hd : G ≤ S.slotRound d)
    {W : View Validator BlockId Payload (chop U G)}
    {V : View Validator BlockId Payload U} {k : ℕ} {w v : Option BlockId}
    (hW : Decided (S := S.chop G d hd) (chop U G) W k w)
    (hV : Decided U V (d + k) v) : w = v :=
  decided_agree_truncate MysticetiProperties.agree
    (LocalTruncate.of_banded MysticetiProperties.banded)
    (truncates_chop hd) viewAgreeAbove_chop hW hV

/-- **G8 re-derived.** Validators at different horizons agree. -/
theorem decided_agree_horizons_chop {G₁ G₂ d₁ d₂ : ℕ}
    (hd₁ : G₁ ≤ S.slotRound d₁) (hd₂ : G₂ ≤ S.slotRound d₂)
    {W₁ : View Validator BlockId Payload (chop U G₁)}
    {W₂ : View Validator BlockId Payload (chop U G₂)}
    {V : View Validator BlockId Payload U}
    {k₁ k₂ : ℕ} (halign : d₁ + k₁ = d₂ + k₂) {w₁ w₂ v : Option BlockId}
    (hW₁ : Decided (S := S.chop G₁ d₁ hd₁) (chop U G₁) W₁ k₁ w₁)
    (hW₂ : Decided (S := S.chop G₂ d₂ hd₂) (chop U G₂) W₂ k₂ w₂)
    (hV : Decided U V (d₁ + k₁) v) : w₁ = w₂ :=
  decided_agree_horizons MysticetiProperties.agree
    (LocalTruncate.of_banded MysticetiProperties.banded)
    (truncates_chop hd₁) (truncates_chop hd₂)
    viewAgreeAbove_chop viewAgreeAbove_chop halign hW₁ hW₂ hV

/-- **Synchrony survives the cut, from the rebase.**
`Integration/Preservation.synchronisedOn_chop` proves this directly; it
is `Sustains` applied, as votes and production already were. -/
theorem synchronisedOn_chop {T : Finset Validator} {Rs R' : ℕ}
    (hs : LeanDag.SynchronisedOn U T Rs) (hGR : Rs ≤ G + R') :
    LeanDag.SynchronisedOn (chop U G) T R' := by
  have h := RebasedAbove.synchronisedOn_of (R := MysticetiProperties.mysticetiRule)
    (sustains_chop (U := U) (G := G)) (T := T) (r := G + R') (by omega) (by omega)
    (SynchronisedOn.mono ((MysticetiProperties.synchronisedOn_eq).mpr hs) hGR)
  exact MysticetiProperties.synchronisedOn_eq.mp (by simpa using h)

/-- **And so does non-equivocation**, from the truncation. -/
theorem noEquivOn_chop (hd : G ≤ S.slotRound d) {T : Finset Validator}
    (hne : NoEquivOn (MysticetiProperties.mysticetiRule (Payload := Payload)) U T) :
    NoEquivOn (MysticetiProperties.mysticetiRule (Payload := Payload)) (chop U G) T :=
  noEquivOn_of_truncates (truncates_chop hd) hne

end CoreTruncate


/-! ## The same cut, for a second protocol

Odontoceti gets garbage collection here with **no bespoke route in
existence**: it has no `ChopDecided` of its own and never had one. The
core's had to be deleted to make the point; this one makes it by
construction.

Nothing below is about Odontoceti's rule. The witness is the core's,
transported by the three-plus-three fields, because the two carriers
project identically; the transport and the agreement are the generic
theorems at Odontoceti's band. A third protocol with a band would take
the same lines. -/

section OdontocetiTruncate

variable [Faults5 Validator] {B : Type} [LinearOrder B]
variable {U : BlockUniverse Validator B Payload}
variable {S : Slots Validator} {G d : ℕ}

/-- **The cut is a truncation of Odontoceti's carrier too.** -/
theorem truncates_chop_odontoceti (hd : G ≤ S.slotRound d) :
    Truncates (OdontocetiProperties.odontocetiRule (BlockId := B) (Payload := Payload))
      U (chop U G) S (S.chop G d hd) G d :=
  let h := truncates_chop (Validator := Validator) (BlockId := B) (Payload := Payload)
    (U := U) (S := S) (G := G) (d := d) hd
  { mem := h.mem, round := h.round, creator := h.creator, refs := h.refs
    slotRound := h.slotRound, leader := h.leader, base := h.base }

/-- **Verdict transport across the cut, for Odontoceti.** -/
theorem decided_chop_iff_odontoceti (hd : G ≤ S.slotRound d)
    {V : View Validator B Payload U} {k : ℕ} {v : Option B} :
    Odontoceti.Decided U V (d + k) v ↔
      Odontoceti.Decided (S := S.chop G d hd) (chop U G) (V.chop G) k v :=
  LocalTruncate.of_banded OdontocetiProperties.banded
    S (S.chop G d hd) U (chop U G) G d (truncates_chop_odontoceti hd) V (V.chop G)
    viewAgreeAbove_chop k v

/-- **And cross-cut agreement**, from an arbitrary view of the
truncation. -/
theorem decided_agree_chop_odontoceti (hd : G ≤ S.slotRound d)
    {W : View Validator B Payload (chop U G)}
    {V : View Validator B Payload U} {k : ℕ} {w v : Option B}
    (hW : Odontoceti.Decided (S := S.chop G d hd) (chop U G) W k w)
    (hV : Odontoceti.Decided U V (d + k) v) : w = v :=
  decided_agree_truncate OdontocetiProperties.agree
    (LocalTruncate.of_banded OdontocetiProperties.banded)
    (truncates_chop_odontoceti hd) viewAgreeAbove_chop hW hV

end OdontocetiTruncate

end Arcs

end Properties

end LeanDag
