# Porting the four remaining rules to the properties

`docs/bespoke-links.md` closed the protocol-to-mechanism gap for the four
rules that show the six properties. Fifteen links stand, and they stand
because their rule has no `Banded` to route through:

| rule | bespoke links | where |
|---|---|---|
| Optimal-Hydrozoan | 8 | carrier done; band open |
| Hybrid / Orcaella | ~~4~~ **0** | routed (`Hybrid/Carrier.lean`, `HybridProperties.lean`) |
| Nemo | ~~3~~ **0** | routed (`Nemo/Carrier.lean`, `NemoProperties.lean`) |
| FinWhale | 0 | — |

FinWhale has none, and that is itself the finding: nothing consumes
FinWhale's verdicts, because it has no slot-indexed decision relation for
a mechanism to consume. Porting it removes no bespoke code. What it supplies is the one
thing §11.4 says is still missing — evidence that the six obligations are
the right six, tested against the rule least like Mysticeti.

## What each rule already has

| | `Slots` | `Decided` | agreement | candidate | direct | eligibility |
|---|---|---|---|---|---|---|
| Nemo | yes | 5 ctors | `decided_unique` | `isLeaderBlock_of_decided` | `DirectCommitIn` | wave 2 |
| Hybrid | yes | 6 ctors, indexed by threshold `k` | `decided_unique`, **under `HonestNoEquiv`** | `isLeaderBlock_of_decided` | `DirectCommitIn` | wave 2 |
| Optimal-Hydrozoan | yes | 6 ctors, over `OptUniverse` | `decided_unique` | `isLeaderBlock_of_decidedOpt` | fast/slow | wave 3 |
| FinWhale | **no** | **none** — per-round predicates | Lemma 12 | — | `DirectCommit D l` | — |

So for three of the four the work is one `Banded` induction apiece plus a
carrier; for the fourth it is a modelling job first.

## Order, and why

**1. Nemo — done.** The cheapest and the pattern-setter: it has every ingredient,
five constructors, and a wave of two — its decision relation mirrors
Odontoceti's, whose `Banded` is the template (122 lines). If the port is
not routine here it will not be routine anywhere, so this is the one that
tests the estimate.

**2. Hybrid / Orcaella — done.** One real obstacle, and it has a known answer.
`Hybrid.decided_unique` is **conditional on `HonestNoEquiv U`**, so
`Properties.Agree` — which is unconditional — cannot hold at the bare
universe. Barnacle already solved this: its Orcaella carrier takes
`Universe := {U // HonestNoEquiv U}`, and the hypothesis becomes a field
of the object rather than a premise of the theorem. A native carrier does
the same, one per admissible threshold. Nothing else here is unusual.

**3. Optimal-Hydrozoan — carrier done, band open.** The biggest payoff, because four of its eight
links are `Integration/Hydrozoan/OptimalChopDecided.lean` — three
inductions carrying verdicts across the cut, which is precisely what
`LocalTruncate.of_banded` replaces. Expect the deletion cascade that
`GC/ChopDecided.lean` and `Integration/Hydrozoan/ChopDecided.lean` already
went through (§11.4e). The carrier is over `OptUniverse` with
`block := fun U => U.toBlockUniverse.block`; `DagRule.Universe` is an
arbitrary type, so nothing in the carrier resists this.

**4. FinWhale — carrier and three properties done; the band needs a rewrite.** Two blockers, and the first is not conformance work.

* **No slot layer.** Commits and skips are per-round predicates over a
  `Dag`, and verdicts are a `Verdict` inductive with `WellFormed`. There
  is no `Decided S V k v`. A carrier needs one, and the honest way to get
  it is an identity schedule — slot `k` at round `k` — with `Decided`
  assembled from `DirectCommit`, `DirectSkip` and the anchor rule.
* **An absolute round read.** `ExposesEquivocation` uses truncated
  subtraction on a round (`scripts/audit-rounds.py`, §3.4c), so the band
  is unprovable until that is restated as a comparison. This is
  independent of the slot layer and has to go first.

If either reshapes FinWhale's model rather than wraps it, the
right answer is to stop and record why — a rule that cannot carry the
obligations without being rewritten is *evidence about the obligations*,
which is what porting FinWhale is for.

## The shape of each port

Fixed by the three ports already done, so this is a checklist rather than
a design:

1. **`<Rule>/Carrier.lean`**, upstream of every mechanism — the carrier,
   `Causal`, `Agree`, `CommitsCandidate`, `CommitsDirect`. Upstream is not
   optional: Odontoceti's carrier sat downstream of the adaptive arc and
   no mechanism could reach it (`docs/bespoke-links.md`).
2. **`<Rule>Properties.lean`** — `Banded`, the one induction the rule
   owes, and then `Indirect`, `LeaderCommits`, `descends` on top of it.
   `Persist` and `LocalTruncate` follow from the band and are not stated.
3. **Convert the links.** `Laws` fields become the three properties;
   `Descent` becomes `descent_of_properties` plus a `GoodGives` bridge;
   any bespoke transport with a properties replacement is **deleted**
   rather than kept as a corollary.
4. **Re-run `scripts/audit-bespoke.py`.** It fails on an unrecorded link,
   so the conversion is checked rather than asserted.

## What would falsify the plan

Three things, each of which is worth more than the port succeeding:

* **A rule whose `Banded` is false.** The band forbids reading an absolute
  round. Odontoceti's attempt found a defect in its skip rule; a second
  such find would say more about the obligation than another success.
* **A property that has to be graded to fit.** `Agree` for Hybrid is the
  test case. If the subtype carrier does not work, the alternative is a
  conditional `Agree`, and that would mean the obligation as stated is
  wrong rather than the rule.
* **A mechanism law with no property at all.** Already seen once, in
  Hydrozoan's `CommitLiveness` and its slow threshold. A second instance
  would be a candidate for a new obligation rather than a gap.

## Nemo, done

The estimate held. What it took:

* **`Nemo/Carrier.lean`** — the carrier, `Causal`, `Agree`,
  `CommitsCandidate`, `CommitsDirect`. Nemo's agreement is
  hypothesis-free, because non-equivocation is a *field* of its
  `Universe` rather than a premise: the model is crash-only. That is why
  `Agree` holds at the bare universe here and will not for Hybrid.
* **`NemoProperties.lean`** — `Banded` (one induction, three cases),
  then `Indirect`, `LeaderCommits` and `descends` on top.
* **Five generic band helpers**, lifted into `Properties/Band.lean`. They
  existed only at the core's carrier, where they were written, and every
  rule's band proof needs them. Nemo needed local wrappers anyway,
  phrased in `U.block` rather than `R.block U` — the two are equal by
  definition and distinct atoms to `omega`, so saying it once per rule
  keeps the proofs in one vocabulary.
* **The three links**, converted: `Laws` reads the three properties, and
  `Descent` is `descent_of_properties` with a ten-line `GoodGives`.

**`SkipsUnsupported` is not owed and the table's dash is right.** Nemo
has three constructors and no direct skip: a slot with no candidate waits
for an anchor. That is exactly the case the property was made optional
for (§11.4c), and it is the first time a rule has exercised the
distinction rather than simply having the property.

**Nothing was falsified.** No graded property was needed, the band went
through as stated, and every mechanism law had a counterpart.

## Hybrid / Orcaella, done — and the plan's first falsification fired

Both predictions held, and one of them was the interesting kind.

**The subtype carrier works.** `Hybrid.decided_unique` is conditional on
`HonestNoEquiv`, and `Properties.Agree` is unconditional with no graded
form. Taking `Universe := {U // HonestNoEquiv U}` makes the hypothesis
part of the object, and `Agree` then holds outright — which is what
Barnacle's carrier already did and what the plan said to copy. No
property had to be weakened.

**The band was false, and the rule was wrong.** `Decided.directSkip`
quantified over the candidates a slot happens to have; a slot with none
satisfied it for nothing, and a mechanism adding one defeats it. This is
the *third* rule with that defect — the core (§3.2), Odontoceti (§3.12),
now Hybrid — and each time the band is what found it. The repair is the
same each time: `DirectSkipSlotIn`, a quorum of voting-round blocks
referencing no candidate at all, with the per-candidate form recovered
as a corollary so nothing stated over it changes.

Hybrid's quorum is its own, `q = n − fb − fc`, so unlike Odontoceti it
could not reuse the core's predicate verbatim — the shape transferred,
the threshold did not.

**One witness was vacuous and is now a refutation.** `uhyb4_slot3`
claimed the crashed validator's slot was skipped. Under the repaired
rule it is not: `Uhyb4` stops at round `3`, so no evidence exists and
the slot is undecided there. Saying that is worth more than the claim it
replaced. The Orcaella witness at `UL` survived, its DAG carrying the
round-`4` blocks, so the repair cost one vacuous theorem and no real
one.

**`SkipsUnsupported` came with it**, as it did for Odontoceti: the
liveness half, and the reason to believe the repair was a repair rather
than a tightening. A skip rule no quorum can trigger would be sound and
useless.

## Optimal-Hydrozoan, half done

**The carrier is built, and the obstacle it raised was the sharpest of
the four.** `OptUniverse` is *indexed by the schedule* — `leader_excluded`
reads `S.leader k` and `decisionRound k` — so `OptUniverse` at `S` and at
`S'` are different types. `DagRule.Universe` is one type and `Banded`
compares verdicts across schedules, so a carrier over `OptUniverse` could
not state the band at all. The cut says the same from the other side:
`optChopHZ` lands in a *different universe type* from the one it starts
in, which `Truncates` cannot relate.

The escape was already in the development. `LeaderExcludedAll`
quantifies the same exclusion over rounds and validators instead of over
slots, so it is schedule-free, and `optUniverseOf` rebuilds the indexed
universe at any schedule. The carrier's universe is the subtype it cuts
out — the shape Hybrid needed for `HonestNoEquiv` — and the schedule
re-enters in `Decided`, where `DagRule` puts it.

So neither the interface nor the rule had to change. What had to change
is reading the invariant in the vocabulary that does not mention the
schedule, and the rule already had it. That is worth more than the port:
it says a schedule-indexed universe is not a counterexample to the
carrier, provided the invariant can be stated schedule-free — and if one
ever cannot be, *that* is the counterexample.

**What is left.** `Banded`, and it is the largest of the four: six
constructors, and rules the other three do not have — fast evidence with
a threshold that depends on whether the block witnesses an equivocation,
`IsNoFastEvidence` quantified negatively over the slot's candidates, and
the anchor-linked evidence quorum. Most of it should come from
Hydrozoan's band helpers, which Optimal's universe shares; the
Optimal-specific part is roughly eight lemmas.

Two things checked ahead of writing it, because either would have
stopped it:

* **The skip needs no repair.** Unlike the core, Odontoceti and Hybrid,
  Optimal's `SkippedLeaderOptInView` already counts blames at the *slot*
  rather than per candidate. Its `IsNoFastEvidence` clause is the
  negative universal, and a candidate the band did not carry is fast
  evidence for nothing, since no old block votes for it — provided the
  thresholds are positive, which `tPlain_pos` gives.
* **Equivocation witnesses do not appear from nowhere.** A fresh
  candidate cannot be one of the two a decision block witnesses, because
  witnessing needs an old block to vote for it.

**Then the eight links**, four of which are
`Integration/Hydrozoan/OptimalChopDecided.lean` — three inductions
carrying verdicts across the cut, which is what `LocalTruncate.of_banded`
replaces. That deletion cascade is the payoff and is why this rule was
ordered third rather than last.

## FinWhale: what it has, and what the band actually costs

`FinWhale/Carrier.lean` has the carrier, `Causal`, `Agree`,
`CommitsCandidate`, and — the one that matters most here — a proof that
the relation is **inhabited**.

**Its `Decided` is existential, which is why inhabitation matters.**
FinWhale has no inductive decision relation. Every other rule derives
verdicts inductively; FinWhale assigns them by a *function*
`dec : ℕ → Verdict BlockId` constrained by `WellFormed`, the paper's
reverse pass read as a condition rather than a construction. So
`Decided S U V r v` says *some* well-formed assignment on this view gives
`v` at `r`, with two further conjuncts that are facts about a real
validator's assignment rather than inventions: it commits only blocks of
the slot, and it is finite.

An existential relation can be empty, and then `Agree` holds for nothing.
This arc has been caught by vacuity twice (§3.4, §3.6), so
`decided_of_directCommit` is proved: FinWhale's own reverse pass, run on
the view with the universe's tie-break, *is* an assignment — well formed,
committing only slot blocks, finite because a view is a finite set — and
`WellFormed.direct_commit` reads the commit off it.

**Two properties are blocked, and by one cause.** FinWhale reads its
leader schedule off the **`Dag`**, as a field, where every other rule
takes it from a `Slots` instance; and it indexes verdicts by **round**,
where the properties index by slot. So the carrier's `Decided` has to
*pin* the two together — slots are rounds, and the schedule's leaders are
the DAG's — and the pinning is a conjunct that has to be proved wherever
`Decided` is concluded.

* `CommitsCandidate` **can** have it, because `IsCandidate` is stated at
  the schedule, so the pinning is available as a hypothesis.
* `CommitsDirect` **cannot**: its direct predicate is passed a view, a
  block and a round, and never the schedule, so nothing can supply the
  pinning. The theorem it would have followed from is proved instead.
* `Banded` cannot either, and for the sharper reason: `AgreeBand`
  constrains ids, blocks and references, and says nothing about a DAG's
  `leader` field — so two DAGs in a band may name different leaders and
  decide differently. The band is *false* as the rule stands.

**What the fix is, and what it costs.** Not a property and not the
carrier: FinWhale's decision layer has to read the schedule from a
`Slots` instance rather than from the `Dag`, and index by slot rather
than by round. Concretely, `slotBlocks D r` becomes
`blocksAt D (S.slotRound k)` filtered by `S.leader k`, every `r + 2`
becomes `S.slotRound k + 2`, and `Anchor`'s `r + 2 < a` becomes a
condition on slot rounds. That reaches `Verdict`, `WellFormed`, `Anchor`,
the reverse pass, Lemma 12's downward induction and the ledger order —
about 5000 lines whose arithmetic is round arithmetic.

Worth noting what this does *not* say. The obligations are not wrong for
FinWhale, and no property needed weakening or grading. What the port
found is that a rule which puts its schedule inside its universe cannot
be related to another DAG by a band, because a band is a statement about
blocks. That is a fact about the rule's formalisation, and it is the
same fact §3.4c recorded from the other end when it said FinWhale has no
`Slots` layer.

**The absolute-round read is a second, smaller blocker** and is
unchanged: `ExposesEquivocation` uses truncated subtraction on a round,
so even after the slot-indexing it would need restating as a comparison.
