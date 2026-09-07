import LeanDag.Hydrozoan.Model.Decided

/-!
# Statement: indirect liveness — the graded rule is total

Direct liveness commits a synchronised wave's slot; the ledger advances
only when *every* slot below gets a verdict, including slots whose
leader was faulty or whose wave predates synchrony. That is the indirect
rule's job (the paper's `TryIndirectDecide`), and this claim is that it
does that job. Two Props:

- `AnchoredTotality`: once a nearest eligible committed anchor exists,
  the three-rung ladder always returns a verdict — a certificate rung
  hit, else a weak-quorum hit with the deterministic least-candidate
  tie-break, else a skip. No rung combination leaves a slot underivable.
- `DecidedBelowRun`: a run of `c` consecutive committed slots, long
  enough that its last slot is an eligible anchor for everything below
  (the relation's `SpansEligible`; under the pipelined schedule, one
  slot per round, exactly when `c ≥ 3`), decides *every* slot below it. A single committed
  slot does not suffice — the slots immediately below it cannot use it
  as an anchor (it sits inside their decision rounds) — but a
  three-round run does: the slots just below the run have no eligible
  slots between themselves and the run's end, so they resolve outright,
  and everything lower descends onto them.

Both claims are pure decision-relation combinatorics: no synchrony, no
population, and no fault-count hypotheses appear. Those enter only when
committing the run itself, which is direct liveness's `CommitLiveness`;
the eventual-decision phase composes the two.
-/

namespace LeanDag

namespace Hydrozoan
namespace IndirectLiveness

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
  [S : Slots Replica]

/-- **The graded rule is total.** The premises are verbatim the shared
anchor prefix of the three indirect `Decided` constructors (minus
`k < j`, which follows from eligibility): an eligible committed anchor
whose eligible in-betweens all skipped. The conclusion: some rung fires
— slot `k` gets a verdict, commit or skip. -/
def AnchoredTotality (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (V : View U) (k j : ℕ) (A : BlockId),
    (hydrozoanAnchored Replica BlockId).Eligible k j →       -- j sits ≥ 3 rounds past k,
    Decided U V j (some A) →             -- slot j committed A,
    (∀ i, k < i → i < j →                -- and j is the NEAREST such slot:
      (hydrozoanAnchored Replica BlockId).Eligible k i →     -- every eligible slot in between
      Decided U V i none) →              -- skipped;
    ∃ v, Decided U V k v                 -- then slot k has a verdict.

/-- **A committed run decides everything below it.** `c` consecutive
committed slots, under the `SpansEligible` runway, force a verdict on
every earlier slot: each such slot anchors on its nearest eligible
committed successor — the run's end if nothing nearer — and the ladder's
totality does the rest. -/
def DecidedBelowRun (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (V : View U) (b c : ℕ),
    0 < c →                              -- a nonempty run
    (hydrozoanAnchored Replica BlockId).SpansEligible c →  -- long enough to anchor below it,
    (∀ j, b ≤ j → j ≤ b + c - 1 →        -- of committed slots b … b+c−1:
      ∃ B, Decided U V j (some B)) →
    ∀ i, i < b → ∃ v, Decided U V i v    -- then every slot below is decided.

/-- Indirect liveness, over every fault configuration, schedule,
tie-break order, and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LinearOrder BlockId] [LeanDag.Hydrozoan.Faults Replica]
    [Slots Replica] (U : BlockUniverse Replica BlockId),
    AnchoredTotality U ∧ DecidedBelowRun U

end IndirectLiveness
end Hydrozoan

end LeanDag
