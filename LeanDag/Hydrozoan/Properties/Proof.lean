import LeanDag.Hydrozoan.Properties.Statement
import LeanDag.Hydrozoan.Helpers.Banded
import LeanDag.Hydrozoan.Helpers.Commit
import LeanDag.Hydrozoan.Helpers.Skippability
import LeanDag.Properties.Derived.FromBand
import LeanDag.Hydrozoan.Helpers.SlotAgreement

import LeanDag.Properties.Arcs.Headline

/-!
# Hydrozoan conforms to the target properties — proof

`Causal` is HI3's argument in the shared vocabulary and is discharged in
`Helpers/Carrier.lean`; the band is `Helpers/Banded.lean`, and
persistence is `Persist.of_banded` applied. The argument behind the band
has one idea in it.

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


/-! ## The assembly -/

theorem holds : Statement := by
  intro Replica _ _ BlockId _ _ _
  refine ⟨banded, agree, commitsCandidate, ?_⟩
  · exact skipsUnsupported

/-! ## The headlines

Hydrozoan's model has no self-parent clause, so it shows progress and
not inclusion. -/

theorem safety : LeanDag.Properties.Safe (rule (Replica := Replica) (BlockId := BlockId)) :=
  LeanDag.Properties.safety banded agree commitsCandidate

theorem progress : LeanDag.Properties.Support.Progresses
    (hzSupport (Replica := Replica) (BlockId := BlockId)) (hzReliability Replica) :=
  LeanDag.Properties.Support.progress hzSupport_commits

end Properties

end Hydrozoan

end LeanDag
