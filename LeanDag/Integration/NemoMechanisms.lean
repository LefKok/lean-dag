import LeanDag.Properties.Arcs.GC
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Properties.Record
import LeanDag.NemoProperties

/-!
# Garbage collection and crash recovery for Nemo

Nemo's universe is the block record at Nemo's validity — a majority
parent quorum rather than `n − f` — with non-equivocation asked of
every validator, since the crash model has no Byzantine ones. Its cut
and its fill are therefore the record's (`Record/`), and the witnesses
the properties read are the carrier bridge's (`Properties/Record.lean`).
What Nemo supplied is `Nemo.ValidWrt.mechanised` and
`Nemo.ValidWrt.copyStable`, in `Nemo/Basic.lean`.

**The fill copies the donor's references and adds nothing.** Nemo has
no self-parent clause, so it takes the copy reading and the filled
block's validity is the donor's verbatim.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Properties.Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {S : Slots Validator} {G d : ℕ}
variable {U : Nemo.Universe Validator BlockId Payload}

/-- **Nemo's carrier, on the record**: both maps the identity. -/
def nemoOnRecord :
    (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)).OnRecord Nemo.ValidWrt (Finset.univ : Finset Validator) where
  toRec := fun U => U
  ofRec := fun W => W
  ids_to := fun _ => rfl
  block_to := fun _ => rfl
  ids_of := fun _ => rfl
  block_of := fun _ => rfl

/-! ## The cut -/

/-- **The cut, at Nemo's universe**: the record's. -/
def chopNemo (U : Nemo.Universe Validator BlockId Payload) (G : ℕ) :
    Nemo.Universe Validator BlockId Payload :=
  BlockRecord.chop U G

@[simp] theorem mem_chopNemo_ids {i : BlockId} :
    i ∈ (chopNemo U G).ids ↔ i ∈ U.ids ∧ G ≤ (U.block i).round :=
  BlockRecord.mem_chop_ids

@[simp] theorem chopNemo_block : (chopNemo U G).block = chopBlk U.block G := rfl

/-- The truncated view: keep what clears the cut. -/
def chopViewNemo (V : Nemo.View Validator BlockId Payload U) (G : ℕ) :
    Nemo.View Validator BlockId Payload (chopNemo U G) :=
  BlockRecord.View.chop V G

/-- **The cut is a truncation of Nemo's carrier.** -/
theorem truncates_chop_nemo (hd : G ≤ S.slotRound d) :
    Truncates (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) U (chopNemo U G) S (S.chop G d hd) G d :=
  nemoOnRecord.truncates_chop U hd

/-- **The chopped view agrees with the original above the cut.** -/
theorem viewAgreeAbove_chop_nemo {V : Nemo.View Validator BlockId Payload U} :
    ViewAgreeAbove (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) V (chopViewNemo V G) G :=
  fun b _ hr => by
    change b ∈ V.ids ↔ b ∈ V.ids.filter fun i => G ≤ (U.block i).round
    rw [Finset.mem_filter]
    exact ⟨fun h => ⟨h, hr⟩, fun h => h.1⟩

/-- **Verdict transport across the cut, for Nemo.** -/
theorem decided_chop_iff_nemo (hd : G ≤ S.slotRound d)
    {V : Nemo.View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId} :
    Nemo.Decided (S := S) U V (d + k) v ↔
      Nemo.Decided (S := S.chop G d hd) (chopNemo U G) (chopViewNemo V G) k v :=
  LocalTruncate.of_banded NemoProperties.banded
    S (S.chop G d hd) U (chopNemo U G) G d (truncates_chop_nemo hd) V (chopViewNemo V G)
    viewAgreeAbove_chop_nemo k v

/-- **And cross-cut agreement**, from an arbitrary view of the
truncation. -/
theorem decided_agree_chop_nemo (hd : G ≤ S.slotRound d)
    {W : Nemo.View Validator BlockId Payload (chopNemo U G)}
    {V : Nemo.View Validator BlockId Payload U} {k : ℕ} {w v : Option BlockId}
    (hW : Nemo.Decided (S := S.chop G d hd) (chopNemo U G) W k w)
    (hV : Nemo.Decided (S := S) U V (d + k) v) : w = v :=
  decided_agree_truncate NemoProperties.agree
    (LocalTruncate.of_banded NemoProperties.banded)
    (truncates_chop_nemo hd) viewAgreeAbove_chop_nemo hW hV

/-! ## The fill -/

/-- **The recovery, at Nemo's universe**: the record's copy fill. -/
def skipFillNemo (U : Nemo.Universe Validator BlockId Payload)
    (sk : SkipData U.ids U.block) : Nemo.Universe Validator BlockId Payload :=
  BlockRecord.copyFill U sk

variable {sk : SkipData U.ids U.block}

@[simp] theorem skipFillNemo_block_old {b : BlockId} (hb : b ∈ U.ids) :
    (skipFillNemo U sk).block b = U.block b := if_pos hb

@[simp] theorem skipFillNemo_block_fresh {k : ℕ} :
    (skipFillNemo U sk).block (sk.fresh k) = sk.copyBlock k := SkipData.fillMap_fresh

/-- The pre-crash view, read in the repaired universe. -/
def liftViewNemo (V : Nemo.View Validator BlockId Payload U) :
    Nemo.View Validator BlockId Payload (skipFillNemo U sk) :=
  BlockRecord.View.liftCopy V

/-- **The fill is an extension of Nemo's carrier.** -/
theorem extends_skipFill_nemo :
    Extends (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) U (skipFillNemo U sk) :=
  nemoOnRecord.extends_copyFill U sk

/-- **What the fill sustains.** Above `sk.r` the fill added nothing. -/
theorem sustains_skipFill_nemo :
    Sustains (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) U (skipFillNemo U sk) 0 (sk.r + 1) :=
  nemoOnRecord.sustains_copyFill U sk

/-- **Verdicts survive the recovery, for Nemo.** -/
theorem decided_skipFill_nemo {V : Nemo.View Validator BlockId Payload U}
    {k : ℕ} {v : Option BlockId} (h : Nemo.Decided (S := S) U V k v) :
    Nemo.Decided (S := S) (skipFillNemo U sk) (liftViewNemo V) k v :=
  Persist.of_banded NemoProperties.banded S U (skipFillNemo U sk)
    extends_skipFill_nemo V (liftViewNemo V) (fun _ hb => hb) k v h

/-- **And agreement across it**: a validator that recovered agrees with
one that did not, from any view of the fill. -/
theorem decided_agree_skipFill_nemo {V : Nemo.View Validator BlockId Payload U}
    {W : Nemo.View Validator BlockId Payload (skipFillNemo U sk)}
    {k : ℕ} {v w : Option BlockId}
    (hV : Nemo.Decided (S := S) U V k v)
    (hW : Nemo.Decided (S := S) (skipFillNemo U sk) W k w) : v = w :=
  decided_agree_extends NemoProperties.agree
    (Persist.of_banded NemoProperties.banded) extends_skipFill_nemo
    (V' := liftViewNemo V) (fun _ hb => hb) hV hW

end Integration

end LeanDag
