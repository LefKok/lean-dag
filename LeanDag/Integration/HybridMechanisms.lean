import LeanDag.Properties.Arcs.GC
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Integration.Preservation
import LeanDag.HybridProperties

/-!
# Garbage collection and crash recovery for Hybrid

`scripts/audit-mechanisms.py` asked for both. Hybrid shows `Banded` and
`Agree`, so the two transformer arcs' theorems already held of it;
nobody had applied them, and no audit could say so, because a cell
nobody wrote leaves no code behind.

**The cost is the whole point of the file.** Hybrid's universe is a
*subtype* of the core's — `{U : BlockUniverse // HonestNoEquiv U}` — so
the cut is the core's `chop` and the fill is the core's `skipFill`, each
with one invariant discharge, and both discharges already existed —
`honestNoEquiv_chop` and `honestNoEquiv_skipFill`, written for the
integration arc. The `Truncates` witness is the core's projected field
by field, exactly as `truncates_chop_odontoceti` is, because the two
carriers read the underlying universe identically. What follows is two
applications of the generic theorems.

That is what "a rule showing the properties composes with the mechanism"
costs when the rule's universe is the core's up to an invariant, and it
is the cheap end of the range: a rule with its own universe record —
Nemo, FinWhale — would have to construct its own cut, since
`DagRule.Universe` is opaque and the property layer cannot build one
(`docs/target-properties.md` §11.4).
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Properties.Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {S : Slots Validator} {G d : ℕ} {kt : ℕ}

/-- **The cut, at Hybrid's carrier.** The core's `chop` with the
invariant its universe adds, which the cut preserves. -/
def chopHybrid (U : (HybridProperties.hybridRule (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) kt).Universe) (G : ℕ) :
    (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt).Universe :=
  ⟨chop U.val G, honestNoEquiv_chop U.property⟩

variable {U : (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
  (Payload := Payload) kt).Universe}

/-- **The cut is a truncation of Hybrid's carrier.** The core's witness,
projected: the subtype's `ids` and `block` are the underlying
universe's, so the seven fields are the same seven facts. -/
theorem truncates_chop_hybrid (hd : G ≤ S.slotRound d) :
    Truncates (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload) kt)
      U (chopHybrid U G) S (S.chop G d hd) G d :=
  let h := truncates_chop (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
    (U := U.val) (S := S) (G := G) (d := d) hd
  { mem := h.mem, round := h.round, creator := h.creator, refs := h.refs
    slotRound := h.slotRound, leader := h.leader, base := h.base }

/-- **Verdict transport across the cut, for Hybrid.** A validator that
has pruned below the horizon reaches exactly the verdicts it would have
reached with its whole history, at the re-indexed slot. -/
theorem decided_chop_iff_hybrid (hpos : 0 < kt) (hd : G ≤ S.slotRound d)
    {V : LeanDag.View Validator BlockId Payload U.val} {k : ℕ} {v : Option BlockId} :
    Hybrid.Decided (S := S) kt U.val V (d + k) v ↔
      Hybrid.Decided (S := S.chop G d hd) kt (chop U.val G) (V.chop G) k v :=
  LocalTruncate.of_banded (HybridProperties.banded hpos)
    S (S.chop G d hd) U (chopHybrid U G) G d (truncates_chop_hybrid hd) V (V.chop G)
    viewAgreeAbove_chop k v

/-- **And cross-cut agreement**, from an arbitrary view of the
truncation: a validator that joined from the cut and one that did not
cannot disagree. -/
theorem decided_agree_chop_hybrid (hpos : 0 < kt)
    (hk : Hybrid.Admissible Validator kt) (hd : G ≤ S.slotRound d)
    {W : LeanDag.View Validator BlockId Payload (chop U.val G)}
    {V : LeanDag.View Validator BlockId Payload U.val} {k : ℕ} {w v : Option BlockId}
    (hW : Hybrid.Decided (S := S.chop G d hd) kt (chop U.val G) W k w)
    (hV : Hybrid.Decided (S := S) kt U.val V (d + k) v) : w = v :=
  decided_agree_truncate (HybridProperties.agree hk)
    (LocalTruncate.of_banded (HybridProperties.banded hpos))
    (truncates_chop_hybrid hd) viewAgreeAbove_chop hW hV

/-! ## Crash recovery

The same shape with `Persist` going up where `LocalTruncate` went down.
The fill is the core's, the invariant discharge is
`honestNoEquiv_skipFill`, and what is left is `Extends` — which
`Arcs.extends_of_skipFill` states through four equations rather than a
type equality, exactly so that a rule whose universes *are* core block
universes up to an invariant can apply it with `rfl`. -/

/-- **The fill, at Hybrid's carrier.** -/
def skipFillHybrid (U : (HybridProperties.hybridRule (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) kt).Universe) (sk : SkipMsg U.val) :
    (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt).Universe :=
  ⟨sk.skipFill, honestNoEquiv_skipFill sk U.property⟩

/-- **The fill is an extension of Hybrid's carrier.** -/
theorem extends_skipFill_hybrid (sk : SkipMsg U.val) :
    Extends (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload) kt) U (skipFillHybrid U sk) :=
  extends_of_skipFill _ sk rfl rfl rfl rfl

/-- **What the fill sustains, for Hybrid** — the core's witness,
projected field by field. -/
theorem sustains_skipFill_hybrid (sk : SkipMsg U.val) :
    Sustains (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) U (skipFillHybrid U sk) 0 (sk.r + 1) :=
  let h := sustains_skipFill (Payload := Payload) sk
  { mem := h.mem, round := h.round, creator := h.creator, refs := h.refs }

/-- **Verdicts survive the recovery, for Hybrid.** The replica that
recovered reaches every verdict it reached before. -/
theorem decided_skipFill_hybrid (hpos : 0 < kt) (sk : SkipMsg U.val)
    {V : LeanDag.View Validator BlockId Payload U.val} {k : ℕ} {v : Option BlockId}
    (h : Hybrid.Decided (S := S) kt U.val V k v) :
    Hybrid.Decided (S := S) kt sk.skipFill (sk.liftView V) k v :=
  Persist.of_banded (HybridProperties.banded hpos) S U (skipFillHybrid U sk)
    (extends_skipFill_hybrid sk) V (sk.liftView V) (fun _ hb => hb) k v h

/-- **And agreement across it**: a validator that recovered agrees with
one that did not, from any view of the fill. -/
theorem decided_agree_skipFill_hybrid (hpos : 0 < kt)
    (hk : Hybrid.Admissible Validator kt) (sk : SkipMsg U.val)
    {V : LeanDag.View Validator BlockId Payload U.val}
    {W : LeanDag.View Validator BlockId Payload sk.skipFill} {k : ℕ} {v w : Option BlockId}
    (hV : Hybrid.Decided (S := S) kt U.val V k v)
    (hW : Hybrid.Decided (S := S) kt sk.skipFill W k w) : v = w :=
  decided_agree_extends (HybridProperties.agree hk)
    (Persist.of_banded (HybridProperties.banded hpos)) (extends_skipFill_hybrid sk)
    (V' := sk.liftView V) (fun _ hb => hb) hV hW

/-! ## Promptness: the fill cannot conjure a commit, for Hybrid -/

/-- **SS3 for Hybrid**, from its `SkipsUnsupported`: the slot the
recovering replica leads at a gap round is skipped at once. -/
theorem decided_none_fresh_hybrid {U : (HybridProperties.hybridRule (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) kt).Universe} (sk : SkipMsg U.val)
    {V : View Validator BlockId Payload U.val} {T : Finset Validator} {k : ℕ}
    (hq : Hybrid.q Validator ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) V T (S.slotRound k + 1)) :
    (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt).Decided S (U := skipFillHybrid U sk) (sk.liftView V) k none :=
  decided_none_of_novel (HybridProperties.skipsUnsupported kt) (extends_skipFill_hybrid sk) S hq
    (fun v hv => by
      obtain ⟨c, hcV, hcc, hcr⟩ := hpres v hv
      have hcU : c ∈ U.val.ids := V.subset_ids hcV
      refine ⟨c, hcV, ?_, ?_⟩
      · show (sk.skipFill.block c).creator = v
        rw [sk.skipFill_block_old hcU]; exact hcc
      · show (sk.skipFill.block c).round = S.slotRound k + 1
        rw [sk.skipFill_block_old hcU]; exact hcr)
    (fun L hL => candidates_fresh (S := S) sk hlead hk1 hk2 hL)
    (fun c hcV _ _ => V.subset_ids hcV)

/-- **And it conflicts with no verdict**, at an admissible threshold. -/
theorem decided_none_fresh_agree_hybrid {U : (HybridProperties.hybridRule (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) kt).Universe} (sk : SkipMsg U.val)
    (hpos : 0 < kt) (hk : Hybrid.Admissible Validator kt)
    {V : View Validator BlockId Payload U.val} {T : Finset Validator} {k : ℕ}
    (hq : Hybrid.q Validator ≤ T.card)
    (hlead : S.leader k = sk.v1) (hk1 : sk.r0 < S.slotRound k) (hk2 : S.slotRound k ≤ sk.r)
    (hpres : PresentAt (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) V T (S.slotRound k + 1))
    {U'' : (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt).Universe}
    (he' : Extends (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt) (skipFillHybrid U sk) U'')
    {V'' W : View Validator BlockId Payload U''.val} (hsub : (sk.liftView V).ids ⊆ V''.ids)
    {v : Option BlockId}
    (hW : (HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) kt).Decided S (U := U'') W k v) : v = none :=
  (decided_agree_extends (HybridProperties.agree hk)
    (Persist.of_banded (HybridProperties.banded hpos)) he' (V := sk.liftView V) (V' := V'') hsub
    (decided_none_fresh_hybrid sk hq hlead hk1 hk2 hpres) hW).symm

end Integration

end LeanDag
