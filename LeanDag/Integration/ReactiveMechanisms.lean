import LeanDag.Properties.Arcs.GC
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Integration.ReGenesis
import LeanDag.Reactive.MysticetiProperties
import LeanDag.Properties.Arcs.Liveness

/-!
# The mechanisms over a reactive execution

The cell `Properties/Support.lean` could not reach. `Support.OfCoverage` asks a
rule's liveness precondition to follow from coverage and production, and
a reactive execution has production but not coverage: a reactive builder
omits whatever had not arrived when its exit condition fired, so
`SynchronisedOn` is false in one by design (`Reactive/Basic.lean`). So
reactive Mysticeti's own precondition is guarded by a witness rather
than by `Support.OfCoverage`, and the question left open was whether its
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

The reason this reaches further than `Support.OfCoverage` does is worth
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

/-! ## The precondition, across the three mechanisms

With `Support.live_of_sustains` and `Support.live_of_truncates` the
whole window carries, and everything downstream — `LeaderCommits`,
`decidedBelow_of_run`, chain quality — applies in the transformed
universe with no further argument. Reactive Mysticeti reaches
`Support.live` by its own bridge and needs nothing else. A slot-level
version of these, at the direct commit, stood here first and was
deleted when the window-level one arrived. -/

variable {V : View Validator BlockId Payload U} {lo K : ℕ}

/-- **The reactive precondition survives the cut**, as the support's,
at the re-indexed schedule. -/
theorem live_chop_reactive {G d : ℕ} (hd : G ≤ S.slotRound d)
    (h : MysticetiProperties.reactiveLive S (U := U) V T lo K) (hlo : d ≤ lo) (hK : lo < K) :
    MysticetiProperties.coreSupport.live (coreReliability Validator) (S.chop G d hd)
      (U := chop U G) (V.chop G) T (lo - d) (K - d) :=
  MysticetiProperties.coreSupport.live_of_truncates MysticetiProperties.coreSupport_local
    (truncates_chop hd) (MysticetiProperties.coreSupport_live_of_reactiveLive h) hlo hK
    (fun _ hGN hc => coversUpto_of_truncates (truncates_chop hd) viewAgreeAbove_chop hGN hc)

/-- **And the fill**, on any view of it caught up as far as the old one. -/
theorem live_skipFill_reactive (sk : SkipMsg U) {V' : View Validator BlockId Payload sk.skipFill}
    (h : MysticetiProperties.reactiveLive S (U := U) V T lo K) (hr : sk.r + 1 ≤ S.slotRound lo)
    (hV' : ∀ N, V.CoversUpto N → V'.CoversUpto N) :
    MysticetiProperties.coreSupport.live (coreReliability Validator) S
      (U := sk.skipFill) V' T lo K :=
  MysticetiProperties.coreSupport.live_of_sustains MysticetiProperties.coreSupport_local
    (sustains_skipFill sk) (MysticetiProperties.coreSupport_live_of_reactiveLive h) hr hV'

/-- **And re-genesis.** -/
theorem live_addGenesis_reactive {v : Validator} {g : BlockId} {p : Payload}
    {hg : g ∉ U.ids} {hsev : ∀ b ∈ U.ids, (U.block b).creator ≠ v}
    {V' : View Validator BlockId Payload (addGenesis U v g p hg hsev)}
    (h : MysticetiProperties.reactiveLive S (U := U) V T lo K) (hone : 1 ≤ S.slotRound lo)
    (hV' : ∀ N, V.CoversUpto N → V'.CoversUpto N) :
    MysticetiProperties.coreSupport.live (coreReliability Validator) S
      (U := addGenesis U v g p hg hsev) V' T lo K :=
  MysticetiProperties.coreSupport.live_of_sustains MysticetiProperties.coreSupport_local
    sustains_addGenesis (MysticetiProperties.coreSupport_live_of_reactiveLive h) hone hV'

/-- **Anchored liveness after the cut, for a reactive execution**: a run
of `c` reliably-led slots in the truncation decides everything below it
there. -/
theorem decidedBelow_of_run_chop_reactive {G d c b : ℕ} (hd : G ≤ S.slotRound d) (hc : 0 < c)
    (hspans : SpansEligible (Validator := Validator) (S := S.chop G d hd) c)
    (h : MysticetiProperties.reactiveLive S (U := U) V T (d + b) (d + b + c))
    (hlead : ∀ i, i < c → (S.chop G d hd).leader (b + i) ∈ T) :
    ∀ i, i < b → ∃ w, DecidedBelow (MysticetiProperties.mysticetiRule (Payload := Payload))
      (S.chop G d hd) (b + c) (V.chop G) i w :=
  MysticetiProperties.coreSupport.decidedBelow_of_run_truncates
    MysticetiProperties.coreSupport_local MysticetiProperties.coreSupport_commits hc
    (MysticetiProperties.descends hc hspans) (truncates_chop hd) (V.chop G)
    (MysticetiProperties.coreSupport_live_of_reactiveLive h)
    (fun _ hGN hcov => coversUpto_of_truncates (truncates_chop hd) viewAgreeAbove_chop hGN hcov) hlead

end Integration

end LeanDag
