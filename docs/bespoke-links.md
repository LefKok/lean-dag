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

## A. Agreement — `Properties.Agree` (10)

Each calls the protocol's own uniqueness theorem where the property says
the same thing. `Agree` is proved *from* those theorems, so the
substitution is exact.

| theorem | file | borrows |
|---|---|---|
| `Integration.Hydrozoan.decided_fill_agreeHZ_of_properties` | `Integration/Hydrozoan/ViaProperties.lean` | `Hydrozoan.SlotAgreement.holds` |
| `Integration.Hydrozoan.agree_stackHZ` | `Integration/Hydrozoan/Stack.lean` | `Hydrozoan.SlotAgreement.holds` |
| `Integration.Hydrozoan.decidedUnique_stackHZ` | `Integration/Hydrozoan/Stack.lean` | `Hydrozoan.SlotAgreement.holds` |
| `Integration.Hydrozoan.Deployment.agrees` | `Integration/Hydrozoan/Deployment.lean` | `Hydrozoan.SlotAgreement.holds` |
| `Integration.Hydrozoan.Deployment.safe` | `Integration/Hydrozoan/Deployment.lean` | `Hydrozoan.SlotAgreement.holds` |
| `SkipMsg.decided_fill_agree` | `SafeSkip/Invariance.lean` | `decided_agree` |
| `Odontoceti.DecidedWithin.agree` | `Adaptive/Odontoceti.lean` | `Odontoceti.decided_unique` |
| `Odontoceti.partialRun_agree` | `Adaptive/Odontoceti.lean` | via the above |
| `Odontoceti.adaptiveRun_agree` | `Adaptive/Odontoceti.lean` | via the above |
| `Odontoceti.adaptiveRun_exists` | `Adaptive/Odontoceti.lean` | via the above |

## B. A commit names a candidate — `Properties.CommitsCandidate` (5)

| theorem | file | borrows |
|---|---|---|
| `Integration.Hydrozoan.Simulates.decided` | `Integration/Hydrozoan/Simulation.lean` | `Hydrozoan.isLeaderBlock_of_decided` |
| `Integration.Hydrozoan.Simulates.decided_chop_of_simulates` | `Integration/Hydrozoan/Simulation.lean` | via the above |
| `Integration.Hydrozoan.Simulates.decided_fill_of_simulates` | `Integration/Hydrozoan/Simulation.lean` | via the above |
| `Integration.Hydrozoan.Simulates.decided_of_chop_of_simulates` | `Integration/Hydrozoan/Simulation.lean` | via the above |
| `SkipMsg.decided_fill` | `SafeSkip/Invariance.lean` | `isLeaderBlock_of_decided` |

## C. Barnacle's `Laws` — three properties (5)

`Laws.agree` **is** `Agree` and `Laws.candidates` **is**
`CommitsCandidate` (§11.2), so those two fields should cite the
properties. `Laws.decided_of_directCommitIn` is the one that cannot yet:
`CommitsDirect` is currently *derived from* `Laws` for these rules, so
using it here would be circular. Routing this group needs
`CommitsDirect` proved natively first — for the core at
`MysticetiProperties.mysticetiRule`, and for Hydrozoan and Odontoceti at
their own carriers.

| theorem | file | borrows |
|---|---|---|
| `Barnacle.Mysticeti.holds` | `Barnacle/Mysticeti/Proof.lean` | `decided_unique`, `isLeaderBlock_of_decided`, `certifiedIn_of_directCommitIn_at_anchor` |
| `Barnacle.odontoceti_laws` | `Barnacle/Helpers/Odontoceti.lean` | `Odontoceti.decided_unique`, `Odontoceti.isLeaderBlock_of_decided`, `Odontoceti.thickLink_of_directCommitIn_at_anchor` |
| `Barnacle.Odontoceti.holds` | `Barnacle/Odontoceti/Proof.lean` | via the above |
| `Barnacle.Hydrozoan.holds` | `Barnacle/Hydrozoan/Proof.lean` | `Hydrozoan.SlotAgreement.holds`, `Hydrozoan.isLeaderBlock_of_decided`, the two anchor lemmas |
| `Barnacle.Live.holds` | `Barnacle/Live/Proof.lean` | via the above |

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
