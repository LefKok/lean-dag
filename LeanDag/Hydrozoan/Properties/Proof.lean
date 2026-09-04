import LeanDag.Hydrozoan.Properties.Statement
import LeanDag.Hydrozoan.Helpers.Banded
import LeanDag.Hydrozoan.Helpers.Commit
import LeanDag.Properties.Derived.FromBand
import LeanDag.Hydrozoan.Helpers.SlotAgreement

/-!
# Hydrozoan conforms to the target properties — proof

`Causal` is HI3's argument in the shared vocabulary and is discharged in
`Helpers/Carrier.lean`. What is proved here is persistence, and the
argument has one idea in it.

**Everything an old anchor can see is old.** `Properties.Extends`
guarantees only that the extension holds every old block and denotes it
unchanged, and from that `Extends.reaches_old` derives that nothing new
enters the causal history of anything old. Every premise a Hydrozoan
derivation carries is then either monotone — the fast and slow paths
count votes and certificates a view holds, and a larger view holds more
— or is read from the anchor's history, where the extension has changed
nothing. The negative premises of the graded rungs survive for the same
reason: a new candidate cannot be certified or weak-linked from an old
anchor, because the blocks that would witness it are not in the
anchor's history.

**The direct skip is where a protocol can fail this**, and Hydrozoan
does not. A blame is a voting-round block referencing no candidate of
the slot; an extension can add candidates, but an old block's references
are unchanged and old, so it references none of them and remains a
blame. The count does not move. The core's rule quantifies over
candidates instead, and a slot skipped because it had none is not
skipped once one appears — which is why the core will need a condition
where this arc needs none.
-/

namespace LeanDag

namespace Hydrozoan

namespace Properties

open LeanDag.Properties

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]
variable {U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}

/-! ## Persistence

Was an induction over the six constructors, with a family of
monotonicity lemmas beneath it. Both are gone: an extension carries
every band, so persistence is `banded_aux` applied, and the transfer
lemmas the induction needed live in `Helpers/Banded.lean` where the band
uses them. -/

/-- **Hydrozoan's verdicts survive every extension**, at Hydrozoan's own
schedule vocabulary, which is what the integration arc consumes. -/
theorem persist_aux [S : LeanDag.Hydrozoan.Slots Replica]
    (he : Extends rule U U') {V : LeanDag.Hydrozoan.View U}
    {V' : LeanDag.Hydrozoan.View U'} (hV : V.ids ⊆ V'.ids)
    {k : ℕ} {v : Option BlockId} (h : LeanDag.Hydrozoan.Decided U V k v) :
    LeanDag.Hydrozoan.Decided U' V' k v := by
  obtain ⟨top, -, ht⟩ := banded_aux (S := S) h
  refine ht 0 0 0 0 S U' V' k (by omega) ?_ ?_ (AgreeBand.of_extends he _ _)
    (fun b hb _ _ => hV hb)
  · intro m m' hm
    have : m = m' := by omega
    subst this; rfl
  · intro m m' hm _
    have : m = m' := by omega
    subst this; rfl

/-! ## The assembly -/


theorem holds : Statement := by
  intro Replica _ _ BlockId _ _ _
  refine ⟨causal, banded, agree, ?_, ?_⟩
  · exact LeanDag.Properties.Persist.of_banded banded
  · intro S U V T k hq hpres huns
    have hpres' : ∀ v ∈ T, ∃ c ∈ V.ids, (U.block c).author = v ∧
        (U.block c).round = S.slotRound k + 1 := fun v hv => by
      obtain ⟨c, hcV, hca, hcr⟩ := hpres v hv
      exact ⟨c, hcV, hca, hcr⟩
    have huns' : ∀ c ∈ V.ids, (U.block c).author ∈ T → (U.block c).round = S.slotRound k + 1 →
        ∀ L, @LeanDag.Hydrozoan.IsLeaderBlock _ _ _ _ _ (ofCoreSlots S) U k L →
          L ∉ (U.block c).parents :=
      fun c hcV hT hr L hL => huns c hcV hT hr L hL
    exact decided_none_of_unsupported (S := ofCoreSlots S) hq hpres' huns'

end Properties

end Hydrozoan

end LeanDag
