import LeanDag.Properties.Arcs.GC
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Integration.ReGenesis
import LeanDag.Reactive.MysticetiProperties

/-!
# The mechanisms over a reactive execution

The cell `Properties/Live.lean` could not reach. `LiveReachable` asks a
rule's liveness precondition to follow from coverage and production, and
a reactive execution has production but not coverage: a reactive builder
omits whatever had not arrived when its exit condition fired, so
`SynchronisedOn` is false in one by design (`Reactive/Basic.lean`). So
reactive Mysticeti's own precondition is guarded by a witness rather
than by `LiveReachable`, and the question left open was whether its
commits survive a mechanism.

**They do, and coverage was never what the mechanism needed.** The
mechanism reads `CertifiesAt` — the certificates the commit rule counts
— and carries them across `Sustains`, because a certificate is made of
references and `Sustains` preserves references. The reactive discipline
delivers `CertifiesAt` (`ReactiveM.certifies`, from `cert_or_wait`),
which is exactly what it is designed to deliver in place of coverage.
Nothing about the pacing structure is transported: no `ReactiveM` is
built for the truncation or the fill, and none is needed.

Three cells follow, one per DAG-transforming mechanism, each the same
two theorems composed at a different `Sustains` witness.

The reason this reaches further than `LiveReachable` does is worth
stating. `CertifiesAt` counts in the *rule's* vocabulary, and
`DagRule` has none — a carrier knows `ids`, `block` and `refs`, and
every rule's certificate is a different threshold over them. Coverage is
the strongest fact statable without that vocabulary, which is what makes
it the right antecedent for a property and the wrong one for a reactive
execution.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Properties.Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable [S : Slots Validator]
variable {U : BlockUniverse Validator BlockId Payload}
variable {T : Finset Validator} {N R k : ℕ} {L : BlockId}

/-- **The reactive commit survives the cut.** A validator that committed
reactively still holds the commit in the truncation, at the rebased
round. -/
theorem directCommit_chop_reactive {G : ℕ} (rm : ReactiveM (S := S) U T N)
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hG : G ≤ S.slotRound k) (hlead : S.leader k ∈ T)
    (hL : IsLeaderBlock U k L) :
    DirectCommit (chop U G) L (S.slotRound k - G) :=
  MysticetiProperties.directCommit_of_reactive_sustains sustains_chop rm hT hcard
    hgst hto hR hN hG hG hlead hL

/-- **And the fill.** A validator recovering by Safe Skip does not lose
a commit the reactive discipline reached. -/
theorem directCommit_skipFill_reactive (sk : SkipMsg U) (rm : ReactiveM (S := S) U T N)
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hr : sk.r + 1 ≤ S.slotRound k) (hlead : S.leader k ∈ T)
    (hL : IsLeaderBlock U k L) :
    DirectCommit sk.skipFill L (S.slotRound k - 0) :=
  MysticetiProperties.directCommit_of_reactive_sustains (sustains_skipFill sk) rm hT
    hcard hgst hto hR hN hr (Nat.zero_le _) hlead hL

/-- **And re-genesis.** A validator that rejoined with a fresh chain
holds every reactive commit it held before. -/
theorem directCommit_addGenesis_reactive {v : Validator} {g : BlockId} {p : Payload}
    {hg : g ∉ U.ids}
    {hsev : ∀ b ∈ U.ids, (U.block b).creator ≠ v}
    (rm : ReactiveM (S := S) U T N)
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hone : 1 ≤ S.slotRound k) (hlead : S.leader k ∈ T)
    (hL : IsLeaderBlock U k L) :
    DirectCommit (addGenesis U v g p hg hsev) L (S.slotRound k - 0) :=
  MysticetiProperties.directCommit_of_reactive_sustains sustains_addGenesis rm hT
    hcard hgst hto hR hN hone (Nat.zero_le _) hlead hL

end Integration

end LeanDag
