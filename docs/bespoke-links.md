# The bespoke links, and the plan to remove them

`docs/target-properties.md` part 2 claims that a rule showing the
properties composes with each mechanism **with no further proof**. That
claim is about the mechanisms the arc converted. Library-wide it did not
hold, and `scripts/audit-bespoke.py` says by how much.

## What the audit measures

Not whether a mechanism *mentions* a protocol — a theorem about garbage
collection over Hydrozoan must say `Hydrozoan.Decided`, and no
abstraction removes that. What it measures is whether a mechanism
theorem's **proof** reaches a protocol theorem *about verdicts* by a path
that avoids the properties. The dependency closure is taken with
`LeanDag.Properties.*` and each protocol's conformance file as barriers;
what is still reachable is borrowed reasoning.

Two exclusions, both deliberate:

* **Shared structure is not borrowing.** `mem_blocksAt`, `historyFrom_*`,
  `quorumCard_*`, `Faults.card_validators` live in protocol files and are
  facts about DAGs and committees. Counting them gives 382 links and
  measures nothing; restricting the targets to the 115 protocol theorems
  that name a decision relation gives 49 and measures the claim.
* **A rule with no `Banded` has nothing to route through.** Fourteen
  links for Optimal-Hydrozoan, Nemo and Hybrid/Orcaella are the instances
  gap of §11.4 seen from a third side, not a defect of the arc. The
  script reports them separately and they do not fail a run.

That leaves **35 links, for the four rules that show the six**. Each is
recorded below and struck off when routed. The script fails on an
unrecorded link *and* on a recorded one that is no longer bespoke, so
this table cannot drift from the code in either direction.

## B. A commit names a candidate — `Properties.CommitsCandidate` (5)

| theorem | file | borrows |
|---|---|---|
| `Integration.Hydrozoan.Simulates.decided` | `Integration/Hydrozoan/Simulation.lean` | `Hydrozoan.isLeaderBlock_of_decided` |
| `Integration.Hydrozoan.Simulates.decided_chop_of_simulates` | `Integration/Hydrozoan/Simulation.lean` | via the above |
| `Integration.Hydrozoan.Simulates.decided_fill_of_simulates` | `Integration/Hydrozoan/Simulation.lean` | via the above |
| `Integration.Hydrozoan.Simulates.decided_of_chop_of_simulates` | `Integration/Hydrozoan/Simulation.lean` | via the above |

## D. A reliable leader's slot commits — `Properties.LeaderCommits` (11)

The largest group and the one that needs work rather than substitution:
each consumer carries its synchrony hypotheses loose, and
`LeaderCommits` takes them packaged as the protocol's `Live`. The
repackaging is the same shape as `LiveRule.GoodGives` (§11.2b).

| theorem | file | borrows |
|---|---|---|
| `chain_quality` | `Quality/Capstone.lean` | `decided_of_leader_mem`, `decided_of_leader_of_populated` |
| `chain_quality_of_run` | `Quality/Capstone.lean` | as above |
| `committed_of_correct_block_within` | `Quality/Capstone.lean` | as above |
| `committed_of_correct_block_by_round` | `Quality/Capstone.lean` | as above |
| `committed_of_correct_block` | `Quality/Inclusion.lean` | as above |
| `committed_of_correct_block_correct` | `Quality/Inclusion.lean` | as above |
| `commits_recur_by_round` | `Quantitative.lean` | as above |
| `commits_recur_within` | `Quantitative.lean` | as above |
| `ViewPace.commits_recur_via_pace` | `ViewPace.lean` | as above |
| `Integration.Hydrozoan.Deployment.commits` | `Integration/Hydrozoan/Deployment.lean` | `Hydrozoan.DirectLiveness.holds` |
| `Integration.Hydrozoan.commitLiveness_stackHZ` | `Integration/Hydrozoan/Liveness.lean` | `Hydrozoan.DirectLiveness.holds` |

## E. The indirect descent — `Properties.Indirect`, `Descends` (2)

Both became routable only with §11.2b's `Indirect`.

| theorem | file | borrows |
|---|---|---|
| `Integration.Hydrozoan.Deployment.decidesBelow` | `Integration/Hydrozoan/Deployment.lean` | `Hydrozoan.IndirectLiveness.holds`, `decided_below_of_committed_run`, `decided_of_anchor` |
| `Integration.Hydrozoan.anchoredTotality_stackHZ` | `Integration/Hydrozoan/Liveness.lean` | as above |

## F. View monotonicity — free from `Banded` (1)

| theorem | file | borrows |
|---|---|---|
| `ViewPace.decided_of_local` | `ViewPace.lean` | `decided_full`, `decided_mono` |

## G. An unsupported slot is skipped — `Properties.SkipsUnsupported` (1)

| theorem | file | borrows |
|---|---|---|
| `Integration.lifecycle` | `Integration/Lifecycle.lean` | `decided_none_of_leader_absent`, `decided_none_of_no_candidate` |

## Routed so far

**A, agreement (10).** `Hydrozoan.agree` replaces `SlotAgreement.holds`
in `Stack.lean` and `ViaProperties.lean`, and `Deployment` follows.
`OdontocetiProperties.agree` replaces `Odontoceti.decided_unique` in the
adaptive arc. `SkipMsg.decided_fill_agree` was **deleted** rather than
rerouted: like the garbage-collection and Hydrozoan cases, the bespoke
transport it composed had a properties replacement already
(`Arcs.decided_fill_of_persist`), so the pair went and
`Arcs.decided_fill_agree_of_properties` took over. That took
`SkipMsg.decided_fill` from group B with it.

**C, Barnacle's `Laws` (5).** The circularity dissolved once
`CommitsDirect` was proved natively: the core already had one, Odontoceti's
moved into the new `Odontoceti/Carrier.lean`, and Hydrozoan's was
written for this — at a *disjunction*, the fast path or the slow one,
which is what Barnacle's `DirectCommitIn` is for that rule. All three
`Laws` proofs now read `Agree`, `CommitsDirect` and `CommitsCandidate`.

**One structural change was needed.** `OdontocetiProperties.lean` imports
the adaptive arc, for the bounded relation — so Odontoceti's carrier sat
*downstream of a mechanism*, and no mechanism could reach it. The
carrier, `Causal`, `Agree`, `CommitsCandidate` and `CommitsDirect` moved
to `LeanDag/Odontoceti/Carrier.lean`, upstream of everything, which is
the shape Hydrozoan has had since it was written. The audit script's
module classification was corrected to match: that file is conformance,
not protocol.
