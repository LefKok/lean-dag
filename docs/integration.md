# lean-dag — Integration: the mechanisms at every rule, and what the properties do not say

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

`LeanDag/Integration/` is where the mechanisms of this development —
garbage collection, crash recovery, re-genesis, adaptive leaders — meet
each commit rule and one another. Two kinds of file live there, and the
distinction is the point of this document.

The first kind is a **mechanism cell**: a rule's own cut or fill, built
on the shared data, with the witness that puts it in the relation the
properties read, and the generic theorem applied. Nothing about verdicts
is proved in these files; that is done once, in `LeanDag/Properties/`,
and `docs/target-properties.md` (its opening part) is the current
statement of what a rule shows and what it gets. The composition of
mechanisms with one another is the same story: `Stack.safe_and_live`
reads any sequence of them as one, and the headlines `Properties.Safe`
and `Support.Lives` are what a rule instantiates.

The second kind is a **standing fact about a mechanism** that no
property states, because it is not about verdicts: whether coverage
survives a fill, where a horizon may be put, what a severed validator
can do, what a fill does to the exposure condition and the storage
budgets. Those are the I-labelled results, and they are collected in
§3 with the deployment conditions they yield.

## 1. The composition method, in one paragraph

A mechanism that transforms the DAG delivers one relation between the
universe it reads and the one it writes — `Properties.RebasedAbove`: the
same blocks at and above a settling round, at rounds `G` apart, with the
same authors and, strictly above, the same references. A cut is that
relation at settling round `G` with a rebase of the schedule
(`Truncates`); a fill or a re-genesis is it at no offset, settling at the
top of the gap (`Sustains`); an extension proper is the stronger
`Extends`. Verdicts cross a `Truncates` by `LocalTruncate.of_banded` and
an `Extends` by `Persist.of_banded`, both derived from the rule's
`Banded`; the liveness precondition `Support.live` crosses either from
the support's `Local` law. A `Stack` is a finite sequence of such steps
and is itself one step (`Stack.rebased`), which is the composition
theorem. A mechanism therefore owes a *witness* and nothing else, and
what the files below contain is witnesses.

## 2. The mechanism cells

Each rule with its own universe record builds its own cut and fill on
the shared data (`chopBlk`, `SkipData`), discharges the three or four
invariants its record carries, and applies the generic theorems. Rules
on the core's `BlockUniverse` (the core, Odontoceti, Mahi-Mahi) take the
core's `chop` and `skipFill` directly, in `Properties/Arcs/`.

| file | rule | cut | fill | what is applied |
|---|---|---|---|---|
| `NemoMechanisms.lean` | Nemo | `chopNemo`, `truncates_chop_nemo` | `skipFillNemo`, `extends_skipFill_nemo`, `sustains_skipFill_nemo` | `decided_chop_iff_nemo`, `decided_agree_chop_nemo`, `decided_skipFill_nemo`, `decided_agree_skipFill_nemo` |
| `FinWhaleMechanisms.lean` | FinWhale | `chopFinWhale`, `truncates_chop_finwhale` | `skipFillFinWhale`, the two witnesses | the four verdict theorems, `_finwhale` |
| `HybridMechanisms.lean` | Orcaella | `chopHybrid`, `truncates_chop_hybrid` | `skipFillHybrid`, the two witnesses | the four verdict theorems, `_hybrid`, and the prompt skip `decided_none_fresh_hybrid` with its agreement form |
| `HydrozoanMechanisms.lean` | Hydrozoan | `chopHZ` (`chopBlkHZ`, `chopViewHZ`), `truncates_chop_hz` | `copyFillHZ`, `extends_copyFillHZ`, `sustains_copyFillHZ` | the four verdict theorems, `_hz`, and `decided_none_fresh_hz` |
| `OptimalMechanisms.lean` | Optimal-Hydrozoan | `chopOpt`, with `leaderExcludedAll_chopHZ` | `copyFillOpt`, with `leaderExcludedAll_copyFillHZ` | the four verdict theorems, `_opt` |
| `ReGenesis.lean`, `ReGenesisRules.lean` | every rule | — | `addGenesis` and its per-rule forms (`addGenesisNemo`, `addGenesisFinWhale`, `addGenesisHybrid`, `addGenesisHZ`, `addGenesisOpt`) as `Extends` and `Sustains` witnesses | `decided_addGenesis*`, `decided_agree_addGenesis*` |
| `ReactiveMechanisms.lean` | reactive Mysticeti | — | — | `live_chop_reactive`, `live_skipFill_reactive`, `live_addGenesis_reactive`, `decidedBelow_of_run_chop_reactive`: the reactive precondition across each mechanism, through `coreSupport` |
| `StackRules.lean` | core, Nemo, FinWhale | fill then cut, as a `Stack` | | `stack_core`, `stack_nemo`, `stack_finwhale`; the headline `Properties.Safe` reads any of them |
| `AdaptiveHydrozoan.lean`, `AdaptiveReactive.lean` | Hydrozoan; reactive Mysticeti | — | — | the adaptive leader mechanism (`Adaptive.run_agree`, `run_exists`) at those rules' properties |

The Hydrozoan and Optimal cells are described in more detail in
`docs/hydrozoan-integration.md`. What every row has in common: the
witness is three clauses on a block record, the verdict theorems are
one line each, and the file proves nothing about the rule's decision
relation.

The two Optimal cells carry one invariant that is not a property, leader
exclusion, across the cut and the copy fill. Across the cut: a block
bound by exclusion sits two rounds above the horizon, so it keeps its
parents, its parents keep theirs and their authors, and its candidates
are old blocks at a rebased round. Across the fill: a filled block's
parents are the donor's, so it adds no edge and witnesses nothing new.

## 3. What the properties do not state

Everything below is a fact about a mechanism, not about a rule, and no
property reaches it. The labels are the report's (§16.3–§16.7).

### 3.1 Coverage under the fill (`Coverage.lean`)

Coverage behaves in three ways under the Safe Skip fill. It **fails**
for any reliable set that contains the recovering validator, at every
gap round: an old reliable block one round up references no fresh
identifier (`not_synchronisedOn_skipFill`, I4). This needs nothing
beyond what makes the fill worth doing, and it is the same fact that
makes the fill safe — no old block references a fresh id, so the fill
can manufacture neither a commit nor coverage. It is **preserved** for
any reliable set excluding the recovering validator
(`synchronisedOn_skipFill_of_notMem`), and it **returns** strictly above
the fill for any set (`synchronisedOn_skipFill_above`, from the fill's
`Sustains` witness). Coverage also survives the cut at a horizon offset
(`synchronisedOn_chop`, I2, from the cut's `Sustains`).

What the fill restores is *production*, which is what liveness reads,
and a recovering validator is outside every covered set for the
duration of its gap.

### 3.2 Where a horizon may be put (`Joiner.lean`, `Retention.lean`)

**The joiner** (I5). A validator joining from a truncation under an
adaptive schedule computes the same leaders as the network exactly when
the policy's rule is horizon-stable (`HorizonStable`,
`joiner_assign_agree`), and its verdicts agree with the network's by
cross-cut agreement at the adaptive schedule (`joiner_decided_agree`,
`joiner_run_decided_agree`). The two schedule transformers commute
(`slotsChop_slotsOf`). Epochs align only when the base slot is a
multiple of the epoch width (`epochOf_add_of_dvd`): **a
garbage-collection base slot must be a multiple of the adaptive epoch
width.**

**The anchor** (I6, I8). A recovery message needs its anchor retained,
and `chop` retains it exactly when the horizon has not passed the crash
round (`anchor_pruned`); with the anchor retained the whole message
rebases (`chopMsg`). Composed with the lag: **garbage collection at lag
`Λ` supports recovery from outages of up to `Λ` rounds and no more**
(`outage_bounded_by_lag`). Past that, a validator with no block in the
retained layer can produce nothing at all (`no_blocks_of_no_genesis`,
`severed_of_pruned_anchor`): P3′ walks every block down to genesis.

### 3.3 Re-genesis (`ReGenesis.lean`)

A severed validator restarts with a fresh chain at the cut. `addGenesis`
adds a reference-free block at round `0`; the truncation's base layer is
already such a layer, so the block needs no exemption from P3′ and is
unambiguous because the absence that stranded the validator is total
(I10). Verdicts survive it by `Persist` (`decided_addGenesis`), and the
validator is back in the genesis layer (`populatedOn_addGenesis`).
Heterogeneous horizons need no agreement: a validator's derived genesis
is pruned by any further cut, leaving exactly the base a more-truncated
validator holds (`regenesis_converges`, I11), and re-genesis is forced
rather than chosen — any block returning an absent validator to
production is such a block (`genesis_forced`). Bootstrap, re-genesis and
Safe Skip then compose into a full recovery (`recoveryMsg`,
`hB1uniq_of_addGenesis`, I12), the absence that licensed re-genesis
discharging both of the recovery message's crash clauses. Re-genesis
preserves the exposure condition (`dosValid_addGenesis`, I13), since a
block with no references cites nobody.

### 3.4 The exposure condition under the fill (`Exposure.lean`)

The fill's self reference makes a filled block's cone strictly larger
than the donor's (`history_B1_subset_fill`), so a citation innocuous in
the donor's cone can be a violation in the filled block's. The
disturbance is local: exposure at an old block is unchanged
(`exposedIn_skipFill_old`), and the condition decomposes into the old
universe's plus a clause on the fill's own blocks (`dosValid_skipFill`,
I14), which a recipient checks by computing the fill. When each donor
block already reaches the anchor the check reduces to reachability
(`dosValid_skipFill_of_covered`, I15), because the fill's cone then adds
only the recovering validator's own blocks (`fill_cone_subset`).

### 3.5 Storage under the fill (`DeliveryFill.lean`, `Margin.lean`, `CommonTarget.lean`)

The fill's delivery layer changes nothing, since nobody received the
fill at the time (`skipFillD`, `viewUpto_skipFillD`), so the author-blind
budget transfers at the same constant (`uniformBudget_skipFillD`, I16);
the reference discipline does not (`not_refsAccepted_skipFillD`),
because a filled block cites what the recovering validator never
accepted. The budget needs a donor, not the author
(`card_novelty_le_of_donor`, I17), so the storage bound holds whichever
clause a deployment states. A severed validator is a reader and not a
producer, so it belongs to no reliable set (`notMem_of_no_blocks`) and
at most `f` may be severed at once (`card_severed_le`, I18): **the
horizon lag is a liveness-margin parameter.** A donor line drawn from
the common core cites only what every recipient holds
(`exists_commonAt`, `fill_refs_available`, I19), so the message carries
nothing but the target's name.

`Preservation.lean` holds the one invariant of a carrier that is not a
property: Orcaella's `HonestNoEquiv` survives the cut and the fill
(`honestNoEquiv_chop`, `honestNoEquiv_skipFill`, I1), which is what lets
`HybridMechanisms.lean` build its universes.

## 4. Conditions for a deployment

Read off §3, these are the constraints a deployment of several
mechanisms must respect; none is visible from a single mechanism.

- Garbage collection at lag `Λ` bounds the outage a one-message
  recovery can span to `Λ` rounds; beyond it the validator re-genesises
  and catches up from the cut.
- A garbage-collection base slot under an adaptive schedule must fall
  on an epoch boundary, and the policy's rule must be horizon-stable.
- A fill is checked before it is accepted: its own blocks must satisfy
  the exposure condition, which reduces to one reachability query per
  gap round when the donor line reaches the anchor.
- Draw the donor line from the common core, so the message names its
  target and every recipient reconstructs the fill.
- A validator pruned past its own history counts against the fault
  budget until it re-genesises; at most `f` may be in that state.

## 5. Witnesses and audits

The standing facts are exercised on data in `LeanDagTest/Integration.lean`:
the coverage refutation on the crash
family, retention and the outage bound, re-genesis and its convergence,
the exposure check. The mechanism cells are checked by the build and by
`scripts/audit-mechanisms.py`, which reads the dependency graph and
prints, for every rule, which cells exist; `scripts/audit-bespoke.py`
checks that no cell reaches a rule's verdicts except through its
properties. Both run in CI and exit nonzero on a gap.
