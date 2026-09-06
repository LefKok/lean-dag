# Target properties: mechanisms that apply to any conforming protocol

A design record for an arc in progress. The aim is to state a small
number of properties of a DAG consensus rule such that **a protocol
proving them inherits the mechanisms** — garbage collection, crash
recovery, adaptive leader counts, adaptive leader schedules, reactive
scheduling, chain quality — instead of each mechanism being redeveloped
against each rule, and such that **the mechanisms compose** through the
same properties.

This supersedes §2 and §3 of `transformer-interface.md`, which posed the
same question in a narrower and, in one respect, wrong way. That
document's §1 remains the record of what is built.

Sections 3 and 4 were written before the properties they describe were
built and revised as each was instantiated; each says which checks have
been made. **§11 is the summary**: where the arc stands against the
goal, what it does not cover, and the next steps in order.

---

## 1. The shape of the problem

Mechanisms in this development are currently proved against protocols
one pair at a time. Seven mechanisms need something from a commit rule,
and seven rules carry a decision relation, so there are **49 pairs**.
About fifteen exist:

| Mechanism | Where | Rules covered (bespoke) | Through the properties |
|---|---|---|---|
| Garbage collection (`chop`) | `GC/` | Mysticeti, Hydrozoan, Optimal | core, Hydrozoan: both directions |
| Crash recovery (`skipFill`, `liftView`) | `SafeSkip/` | Mysticeti, Hydrozoan | core, Hydrozoan: both directions |
| Re-genesis | `Integration/ReGenesis.lean` | none | core: both directions (§3.10) |
| Adaptive leader schedule (Hammerhead) | `Adaptive/` | Mysticeti, Odontoceti | core, reactive core, Hydrozoan |
| Adaptive leader count (Barnacle) | `Barnacle/` | six | every theorem takes properties or nothing (§11.2) |
| Reactive schedule | `Reactive/` | Mysticeti, Odontoceti | as a second `Live` for the core |
| Rate limiting | `DoS/` | none | `DeliversOn`, with the paced discipline (§3.11) |
| Chain quality | `Quality/` | Mysticeti | `CommitsCandidate` (§3.9) |

The distribution was the argument, and it has changed. **Barnacle
covered six rules where every other mechanism covered one or two, and it
was the only one with a stated interface** — `BaseRule`, `Laws`,
`LiveRule`, `Descent`, which six protocols instantiate. That made it the
existence proof for this arc.

It is now also the sharpest comparison available. Barnacle's `Laws` are
validated against six rules; the properties here are validated against
two, and the part that is *not* Barnacle's — `Banded`, and everything
derived from it — is exactly the part with two instances. Where the two
collections overlap they now agree by construction: `Laws.agree` **is**
`Agree` and `Laws.candidates` **is** `CommitsCandidate`
(`Barnacle/Conformance.lean`). Where they do not,
`Laws.decided_of_directCommitIn` has no counterpart here — until it was
promoted to `CommitsDirect` — and `LiveRule.LiveOn` split into
`LeaderCommits` and `Descends` without being related to them, until
§11.2b related them. §11.2 records what follows.

One mechanism stays rule-independent as far as this survey goes: the
pacing and delivery layers. The denial-of-service arc left that
category when `DoS/Delivers.lean` gave `DeliversOn` its witness.

**On two entries.** Re-genesis is not an orphan: `integration.md` gives
it I10–I13, `Exposure.lean` consumes it, and it already composes with
the cut, the fill and the DoS arc in its own file. What it lacks is
verdict transport, and it should be an `Extends`, which would give it
`Persist` and `Sustains` from the instances already proved.
`SafeSkip/Jump.lean`'s `denote` was listed in this table before and does not
belong: the model excludes round-jumping outright
(report §4.1), and `denote` is the vehicle for showing a jump denotes a
fill (SS10), not a deployed mechanism.

---

## 2. Three families, needing three different things

The mechanisms do not all want the same thing of a rule, and treating
them as one problem was the earlier error.

**Transformer mechanisms** change the DAG under a replica: garbage
collection, crash recovery, re-genesis. A verdict reached
before the change must be reachable after it, and that is an induction
over derivations. These want §3's properties.

`hydrozoan-integration.md` §9 argues that no record of *uses* can
carry such a result, because `BaseRule.Decided` is a field with no
constructors while the transport proof inducts over derivations.
**That argument holds and does not obstruct this arc**, because nothing
here inducts on the interface's relation: locality and persistence are
*hypotheses*, discharged by each protocol over its own relation where
the constructors are available, and the mechanism theorems consume them
without induction. §9 blocks deriving the properties from a record of
uses, not assuming them over one. This is what lets `BaseRule` serve as
the carrier.

**Schedule mechanisms** change who leads when: Barnacle, Hammerhead,
reactive scheduling, pipelining, the wave-aligned rotation. They only
*consume* verdicts, so a record of uses is exactly right, and Barnacle
already has one. These want §4.

**Measurement mechanisms** say something about the output: chain
quality, quantitative liveness. They read the committed ledger and the
block production, not the derivation. These want §5.

---

## 3. Properties for the transformer mechanisms

### 3.1 Locality

*If two DAGs agree above round `r`, they decide alike at every slot
whose round is at least `r`.*

This is what makes a truncation invisible: everything the cut removed
lies below the verdicts it must preserve, and the indirect rule's
recursion runs upward, away from it. Stated as agreement rather than
existence, it gives garbage collection at **every** admissible horizon
rather than at one.

The recursion is unbounded above — an anchor chain has no ceiling — so
a window formulation will not serve. The condition has to be a genuine
lower bound.

### 3.2 Persistence

*Verdicts survive extension of the DAG.*

This is not a consequence of safety; it is the **prerequisite** for
safety to mean anything as a DAG grows. Every protocol's uniqueness
theorem is stated for two views of the *same* universe
(`Mysticeti.lean:708`). To compare a replica that decided on the DAG it
held against one deciding later on a larger DAG, the first derivation
must first be moved into the second universe, and that move is
persistence. Without it, uniqueness protects only replicas holding
identical DAGs, which is not the deployment situation.

**Persistence is conditional, and the condition is informative.** The
failure mode is not that a different verdict appears — that would be
plain unsafety — but that a derivation ceases to exist, leaving a slot
undecided. The core's direct skip is

```lean
| directSkip {k} : (∀ L, IsLeaderBlock U k L → DirectSkipIn U V L (S.slotRound k)) →
    Decided U V k none
```

so a slot whose leader published nothing is skipped **vacuously**. Add
a block by that leader and the premise acquires content: it now demands
a quorum at the voting round that declined to vote for the new
candidate. The core carries exactly that as `QuorateOverGap`, and the
hypothesis is the content of the safety argument rather than
bookkeeping.

Hydrozoan needs no such hypothesis, because its skip counts *blames at
the slot* rather than quantifying over candidates. The principle:

> A verdict justified by evidence survives extension. A verdict
> justified by the absence of evidence does not.

Evidence does not evaporate when blocks are added; absence does. That
predicts which protocols get the unconditional form — those whose
skips are slot-level counts — and which need a condition — those whose
skips quantify over candidates. Nemo has no direct skip and nothing to
break. **The prediction held, and then changed what it was about:** the
core was in the second group for a defect in its rule rather than for
anything true of the protocol. Odontoceti and
Hybrid are still in that group and have no instance.

**Both instances are now theorems, and both are unconditional.**
Hydrozoan proves `Persist` (HZ9). The core proves it too
(`MysticetiProperties.persist`) — but only after the property found
something wrong with the protocol's model, and that episode is the
substance of this section.

**The grade was a defect in the rule, not a property of the protocol.**
The core first proved `Persist` at a grade `Quorate`: at every slot the
extension gives a new candidate, the view must already hold a quorum at
the voting round. That was honest about the rule as written, and the
rule as written was wrong. `Decided.directSkip` quantified over the
candidates a universe holds, so a slot holding none was skipped by a
validator holding *no evidence at all* — `decided_none_of_leader_absent`
said exactly that — and the premise is not one a validator can check,
since it cannot tell "the leader published nothing" from "the block has
not reached me". A later block then supplies a candidate, another
validator commits the slot, and the two verdicts sit in different
universes where no uniqueness theorem compares them. The test suite
already contained the refutation: `ugrow_commits_recur` commits slots
that `ugrow_skip` let every view skip while the DAG was shorter.

The repair is in the protocol. A skip is now a **count of blockers** —
voting-round blocks in view whose references name no candidate of the
slot — as the reference implementation's `enough_leader_blame` has it,
and as Hydrozoan, Optimal and Mahi-Mahi already had it. Where a
candidate exists the two forms agree, so the safety development is
untouched; where none exists the count still asks for a quorum. The
grade then disappears: the same blockers blame the same slot after any
extension, because an old block's references are old.

Three consequences, none of them planned. The core's fill transport (SS5)
loses its counting hypothesis. `decided_none_of_leader_absent` (L5)
gains the quorum, and becomes checkable. And the witness universes must
tell the truth: `LeanDagTest/Adaptive.lean`'s total adaptive runs become
**partial** runs, because a finite DAG cannot decide slots past its
frontier and only the vacuous skip ever let it pretend otherwise.

**The property also found a defect in itself, earlier.** `Persist`'s
side condition was `Ok : Slots → Universe → Universe → Prop`, and the
core's condition was one on the **view**. The grade was not unproved; it
was unstatable, and `Ok` was widened to take the source view.

**The grade is now gone entirely.** It survived the repair above with no
instance using it, kept against a rule that decides on a block's absence
rather than on the contents of blocks present. Such a rule fails
`Banded` too — the band admits extra blocks inside itself — so the grade
could not rescue a protocol that proves the band, and every route to
persistence here runs through the band. `Persist` takes no `Ok`, and
`Quorate` is deleted (§11.4d).

### 3.3 Inertness, and what `Novel` is

The indirect rungs carry *negative* premises: no candidate is
certified, no candidate is weak-linked. A new candidate could falsify
one and destroy a skip derivation. `Simulates` handles this with a
parameter `Novel : BlockId → Prop`, naming the identifiers the
extension adds, and two fields saying that a novel identifier is not
reachable by any rung from an old anchor. For a truncation `Novel` is
empty and both are vacuous; for a fill it is "fresh", discharged
because no old block references a fresh identifier.

Generalised, `Novel` states that **blocks nothing references cannot
change a verdict**. It is the honest general form of "adding blocks is
harmless", and it is a separate obligation from §3.2's: inertness
protects the indirect rungs, the quorum condition protects the direct
skip. That is why the core's fill needs both and Hydrozoan's needs
neither.

**Two things changed when this was built.**

`Novel` is not a parameter. It was one in `Simulates` because that
interface covers truncations as well, where "novel" must be supplied as
empty. For an *extension* it is determined — the identifiers the target
has and the source lacks — so it is a definition, and one obligation
disappears from every instance.

Inertness is not an assumption either. `Extends` asks only that the
target hold every block the source held and denote them unchanged;
`Extends.old_refs_old` then **derives** that an old block references
only old blocks, because an old block's references were already inside
the source and causal completeness keeps them there. So "blocks nothing
references cannot change a verdict" is a theorem about extensions
rather than a condition on them, and no protocol pays for it.

### 3.4 Truncation

A truncation does two things: it drops what lies below a horizon, and it
renumbers what remains so the retained layer sits at round zero.

**They were stated as two properties, and that was wrong twice over.**
The record is kept because the second error is the instructive one.

*The intermediate does not exist.* Locality asks for equal rounds, so a
universe restricted but not yet renumbered keeps its bottom layer at
round `G`; a renumbering asks for equal references, which at that layer
are empty. A block with no references above round zero fails validity's
quorum clause. So the two could not be composed.

*And the renumbering half was vacuous.* A pure shift keeps every block,
so the bottom layer lands at round zero carrying the references it had
at round `G`, which validity forbids — and any non-empty valid universe
has a round-zero block, by descending the predecessor condition. So a
shift by a positive horizon has no non-empty model, and a property
quantified over such shifts is vacuously true.
`Hydrozoan/Helpers/Truncation.lean`'s `no_base_of_naive_shift` is the
witness, and it is four lines. **It was not written until after the
property had been stated, proved, and reported as retiring a risk.**

**So restriction and renumbering are not separately realisable**, and
only their combination has models. `Properties/Truncate.lean` states
that combination. Two clauses carry the difference from a pure shift:
membership keeps only what lies at or above the horizon, so what lies
below is legitimately gone; and references are compared only *strictly*
above the horizon, so the retained bottom layer may legitimately lose
what pointed below it.

`Local` survives unchanged, non-vacuous and proved. It states what a
verdict reads, which is the property this arc set out to name. It is
simply not what a mechanism that renumbers can consume.

**The discipline that follows, in two halves.** Exhibit a witness
before proving anything about a relation: `truncatesHZ_chopHZ` does it
for the combined form, and had the same been asked of the shift the
vacuity would have surfaced in minutes rather than after 321 lines. And
**name a consumer and feed it before calling an obligation done**: the
first `Sustains` had witnesses for both mechanisms and helped nobody,
because the reactive commit consumes `CertifiesAt` and it transported
`VotesAt` (§3.6). A witness catches a relation with no models; only a
consumer catches one that has models and serves no theorem.

#### 3.4b How the band absorbed truncation

The band tolerated more of a truncation than it looked. Its references
clause is guarded **strictly** above the floor, so two universes may
differ entirely on what the bottom layer of the band points at, which is
exactly what a cut does to its base layer. Nothing above the horizon
ever consults what the horizon points at, and the same holds of every
later verdict, whose own band has a floor at least as high.

What the band did not tolerate was the **renumbering**, and the
renumbering is forced by the model rather than by the rule. Validity
requires a block at a positive round to carry references from the round
below, so a universe pruned below `G` with its survivors left where they
sit has an invalid base layer. The cut must rebase to zero, and every
clause of `AgreeBand` used to compare rounds by equality.

**The generic fix, now taken.** `AgreeBand R U U' lo hi g g'` carries an
offset on each side and compares `round_U' b + g' = round_U b + g`. Two
offsets rather than one, because `LocalTruncate` is an *iff*: reading
the relation backwards has to be another instance of the same statement,
and it is, with the two offsets exchanged. `Banded` correspondingly
carries four naturals — `g` and `g'` on the round axis, `d` and `d'` on
the slot axis, with slots corresponding when `m + d' = m' + d`.

**Where the ceiling is read decided whether the statement was provable
at all.** `Banded` fixes the ceiling `top` before the offsets are
quantified, so the band's upper bound has to be stated in the source's
frame, `hi = top + g`. Stated in the target's frame it is satisfiable by
choosing a large `g`, which makes the hypothesis vacuous and the
property unprovable. The view clause is bounded in the source's frame
for the same reason.

`LocalTruncate` is then two instances of the band: `(g, g', d, d') = (0,
G, d, 0)` going down and `(G, 0, 0, d)` coming back.
`Properties/Derived/Truncate.lean` holds both directions, at `[propext,
Quot.sound]`, and the property has moved to `Derived/` with the rest of
what a band implies.

**What it removed.** Both protocols now prove the offset band and
neither proves truncation. Hydrozoan's truncation file lost its
induction and went from 528 lines to 176, keeping the `TruncatesHZ`
witness and the `no_base_of_naive_shift` record. The garbage-collection
arc's two transport theorems, which `GC/ChopDecided.lean` proved by
structural induction over the decision relation, come back out of
`LocalTruncate.of_banded` in one application — and that induction has
since been deleted (§11.4c). The cost was threading
four naturals through every band lemma of both protocols, paid once.

**What could still fail it.** A rule that reads an *absolute* round — a
genesis special case, a hardcoded first slot — has no offset band, and
would have to state its own truncation property or exclude the bottom of
the DAG from the offset. Neither protocol has such a rule today.

#### 3.4c Which rules can read a band with an offset

§3.4b leaves one thing to check. A rule satisfies `Banded` only if its
decision relation is invariant under adding a constant to every block
round and every `slotRound`, so every round it reads must be a slot's
round plus a constant, or a comparison between two rounds. A round
compared with a literal, or reached by truncated subtraction, is
neither.

`scripts/audit-rounds.py` recomputes the result below. It takes each
rule's decision relation, closes it over the dependency graph — 83
round-reading definitions across the eight rules — and flags the shapes
that break the invariance. The known findings sit in an `ALLOW` list, so
a genesis special case added later fails the script rather than silently
making that rule's band unprovable.

| rule | the rounds it reads | offset band |
|---|---|---|
| core Mysticeti | `slotRound k`, `+1`, `+2` | proved |
| Hydrozoan | `slotRound k`, `+1`, `+2` | proved |
| reactive Mysticeti | the core's relation, unchanged | inherited |
| Odontoceti | `slotRound k`, `+1` | proved (§3.12) |
| Nemo | `slotRound k`, `+1` | reachable |
| Hybrid | `slotRound k`, `+1` | reachable |
| Optimal-Hydrozoan | `slotRound k`, `+1`, `+2` | reachable |
| Mahi-Mahi | `slotRound k + w - 1`, `r + w - 2` | proved, under `2 ≤ w` (§3.16) |
| FinWhale | ~~`leader (round b - 2)`~~ **fixed** | the read is gone, and the band followed (§3.13) |

**Mahi-Mahi's wave rounds truncate.** `votingRound w r = r + w - 2`,
`decisionRoundAt w r = r + w - 1` and `decisionRound w k = slotRound k +
w - 1` are `ℕ` subtractions, and `(r + g) - 2 = (r - 2) + g` fails at
`r + w < 2`. It holds at `2 ≤ w`, and every Mahi-Mahi theorem already
carries that or more — safety `3 ≤ w`, counting `4 ≤ w` and `5 ≤ w` — so
the hypothesis is there to be used. What follows is that Mahi-Mahi's
carrier instance is per-width and its band is conditional, `Banded
(mahiMahiRule w)` under `2 ≤ w`, where both proved bands are
unconditional. `Banded R` is a predicate on the rule alone, so the width
has to be fixed before the property is stated rather than appear inside
it.

**FinWhale indexed its leader by an absolute round**, and no longer
does. `ExposesEquivocation D b` read `D.leader ((D.block b).round - 2)`:
it named the schedule *and* subtracted from a round, either of which
would defeat an offset band. It is now `ExposesEquivocationBy D b v`,
stated at a validator rather than at a leader, with `FPEvidence D b l`
reading it at `(D.block l).creator` — which is the same validator
wherever the rule is used, since the candidate's author *is* the slot's
leader. Both the schedule read and the subtraction went with one change,
and `scripts/audit-rounds.py` now reports FinWhale clean.

The band still needs the schedule out of the `Dag` and the verdicts
indexed by slot (`docs/porting-plan.md`); what this removes is the
smaller of the two blockers, and the one that was in the rule rather
than in its formalisation.

**A third difference, which is not a defect.** Odontoceti, Nemo,
Mahi-Mahi and Hybrid define causal history by a depth bound taken from a
block's own round: `historyFrom blk b = historyUptoFrom blk ((blk b).round
+ 1) b`, enough unfoldings to reach round zero. Under a truncation that
bound shrinks by the horizon, so the history is a shallower unfolding
and is *not* the same set. It agrees with the original everywhere the
rule looks, because a reference path drops one round per step and a
block above the floor is within the shorter depth, but that is an
argument those four bands will have to make. The core and Hydrozoan read
`Reaches`, an unbounded `ReflTransGen`, and make no such argument. The
difference is invisible in the rules as stated and appeared only in the
closure.

## 3.5 Composition

Transport should be a **relation that composes**: compose the slot
correspondences, take the union of the novel sets. Then a stack of
mechanisms follows from its parts, which is what
`Integration/Hydrozoan/Stack.lean` currently proves by hand, and any
future transformer stacks with the existing ones without further work.
That general form is not built. **One composition is**: the adaptive
fixpoint under growth of the DAG, `Persist` composed with the schedule
family (§4.4).

---

## 3.6 Liveness: the obligations run the other way

Safety transports a *derivation*, which is the protocol's inductive
object, so the protocol owes the theorem and every mechanism consumes
it. **Liveness transports a DAG**, which is the mechanism's doing, so
the mechanism owes the guarantee and the protocol consumes it. The two
interfaces point in opposite directions, and the existing code shows
why: `commitLiveness_stackHZ` is one line — a protocol's liveness
theorem is universally quantified over universes and applies to the
transformed one unchanged — while `synchronisedOn_stackHZ` carries four
side conditions.

`Properties/Sustain.lean` names the mechanism's side. `Sustains R U U' G
R₀` says that at and above the settling round `R₀`, re-indexing rounds
by `G`, the two universes hold the same blocks with the same authors,
and strictly above it the same references. Nothing is said below `R₀`,
which is where a mechanism does its work.

**The interface is the blocks, not any predicate — and this was got
wrong once.** The first statement transported `VotesAt` and
`PopulatedOn` by name, and left certification out because each protocol
has its own certificate predicate. It had a witness for both mechanisms,
and it was useless: fed to the reactive commit
(`Reactive/Mysticeti.directCommit`), which runs through
`directCommit_of_certifiesAt`, it failed at the `CertifiesAt` argument
that nothing transported. The repair is to promise less and get more.
Above the settling round an old block keeps its membership, author,
references and shifted round, and then **every** predicate computed
from those transports — votes, production, the core's `Certifies`,
Hydrozoan's `IsCertificate`, and whatever a later protocol defines.
`Sustains.votesAt_of` and `populatedOn_of` are the two the mechanism
side can state; `MysticetiProperties.certifiesAt_of_sustains` is the
core deriving its own certificate layer in a few lines.

**Why this serves the reactive discipline.** A reactive schedule has no
`PopulatedOn` at all — the string does not occur in `LeanDag/Reactive/`
— and `SynchronisedOn` is *false* there by construction, so an interface
built on coverage would have served the timed arcs and excluded the
reactive one. What the reactive exit produces is a certificate
(`cert_or_wait`), and a certificate is made of references. So
`MysticetiProperties.directCommit_of_sustains` takes exactly what the
reactive theorem establishes on the original DAG — `CertifiesAt` and
production — and returns the commit on the transformed one, **with no
pacing structure transported**. `Properties/Arcs/GC.lean`'s
`directCommit_chop` is that theorem fed from the cut's witness: the
consumer test, from the obligation rather than from `chop` directly.

**The settling round is where the content sits.** A truncation settles
at its horizon. A fill settles at the top of its gap, because the blocks
it adds stand in for blocks that voted and need not vote as they did.
Both are witnessed in `Integration/Hydrozoan/ViaProperties.lean`, before
anything is proved from the relation.

**And this does not cover everything.** A mechanism can preserve every
vote and every producer and still cost a protocol its progress, by
adding a *candidate* the protocol can neither commit nor skip — which is
what a fill does to Hydrozoan and not to Optimal-Hydrozoan (§5.1). That
residue is §3.7. It predicts that re-genesis carries the same question,
since it too adds a block with an author; nobody has looked.

## 3.7 Skippability: the residue, graded

`Properties/Skip.lean`. The question the residue asks is about the
**protocol's skip rule**, not about the mechanism, so the obligation sits
on the protocol side and is graded, as `Persist` is by `Ok`: *if every
block of `T` one round above a slot references none of that slot's
candidates, does the protocol skip it, and what does it need of `T`?*

`SkipsUnsupported R Ok` is that question. `unsupported_of_novel` is the
bridge from the mechanism's side: after an extension, a slot all of
whose candidates are novel is unsupported by any `T` whose voting-round
blocks are old, because an old block references only old blocks. So a
mechanism that adds candidates hands the protocol exactly this
hypothesis, and the protocol's grade says whether it can use it.

**Hydrozoan's grade is `qFast ≤ |T|`** (HZ9's fifth conjunct). Every
unsupporting `T`-block is a blame, so the blamers in view include all of
`T`, and the direct skip fires once `T` is large enough. A quorum of
correct replicas has `q = n − f − c` members against `qFast = n − p`, so
**a correct quorum skips an unsupported slot exactly when `f + c ≤ p`**
— the condition `hydrozoan-integration.md` §5.1 found by hand,
recovered here as the grade of a property rather than as a remark.
**The core's grade is `quorumCard ≤ |T|` — a correct quorum**
(`MysticetiProperties.skipsUnsupported`). Its skip counts, per
candidate, the voting-round blocks that do *not* reference it; if every
`T`-block references none of the slot's candidates, every one is a
blamer for every candidate at once.

**Set beside `Persist`, the grading looked like an inversion, and the
inversion was the symptom of a bug.** As first proved:

| | safety (`Persist`) | liveness (`SkipsUnsupported`) |
|---|---|---|
| core — per-candidate skip | conditional, `Quorate` | **correct quorum suffices** |
| Hydrozoan — slot-level `qFast` count | **unconditional** | `qFast ≤ |T|`; a correct quorum does not |

The reading offered was structural: a rule that skips per candidate has
fragile *vacuous* skips but blames any specific candidate trivially,
while a rule counting at the slot has durable skips and a higher bar to
skip at all. Half of that survives. The core's per-candidate skip was
not a design choice of Mysticeti but a mis-modelling of it (§3.2), and
once corrected the safety column is unconditional on both rows. What
remains is a threshold difference in the liveness column — `quorumCard`
against `qFast` — which is arithmetic, not structure.

**The general reading still holds** for a rule that genuinely skips per
candidate, and Odontoceti and Hybrid still do: such a rule blames any
specific unsupported candidate trivially, and pays for it with skips
that a later candidate can undo. Neither has an instance, so the claim
is read off the rules rather than proved.

**The consumer.** `Arcs/SafeSkip.decided_none_fresh` reaches SS3's
content from the properties: the fill is an extension, so its
candidates are unsupported by the old view (`unsupported_of_novel`), and
the core skips what nothing supports — so the slot the recovering
replica leads at a gap round is decided `none` on the lifted view. No
induction, and it lands as a *verdict* where SS3 (`directSkip_fresh`) is
a universe-level `DirectSkip`. SS3's hypothesis `v1 ∉ T` is not needed:
presence is asked of the pre-crash view, whose blocks are old, and
`hgap` says the recovering replica authored nothing in the gap.

Optimal-Hydrozoan's skip is `qCert` blames **and** a no-evidence quorum
at the decision round — two rounds of presence where `SkipsUnsupported`
supplies one. So its instance will likely reshape the property, as the
core's reshaped `Persist.Ok`; that is the right order, and it is not yet
built.

With this the liveness account closes: `Sustains` (mechanism side) keeps
votes and production; `SkipsUnsupported` (protocol side) decides the
slots a mechanism may have poisoned; the protocol's own liveness
theorem, universally quantified over universes, needs no transport.

**The arithmetic of the two directions.** Safety costs one induction per
protocol; liveness costs one obligation per mechanism, plus a few lines
per protocol to derive its certificate layer, plus the graded residue of
§3.7. That is `P + M + P` where the development currently pays `P × M`.

**A layering note.** `Arcs/GC.lean` imports the mechanism it is about
and, to discharge the obligation against a real consumer, the core's
carrier (`MysticetiProperties.lean`, which reaches no mechanism). Through
`GC.Chop`'s own imports it also reaches `DoS`; that is the GC arc's
existing dependency, not one this arc introduced, and it is recorded here
rather than left to be discovered.

---

## 3.8 The band: what `Local` and `Persist` are shadows of

`Properties/Band.lean`. Locality and persistence say one thing twice,
in different units and from opposite ends, and the statement they are
both shadows of is the one a reader reaches for first: *a verdict is
carried by a range of rounds*.

`Banded R` says that for every verdict at slot `k` there is a **top**
such that any universe carrying `U`'s blocks between the slot's own
round and that top, and any view holding those blocks, reaches the same
verdict. The floor is the slot's round, which is `Local`'s content. The
top is variable, as it must be, since an indirect verdict anchors on a
committed slot that may sit arbitrarily high and the anchor's own
derivation reaches higher; what the property claims is that the top
**exists**, so no verdict is a function of unboundedly much of the DAG.

The agreement it asks for, `AgreeBand`, is deliberately
**one-directional**: the larger universe may hold blocks the band did
not, in the band or out of it, which is what a fill does. A rule proving
`Banded` therefore has to cope with candidates that appear from nowhere,
and the core does, on two counts. The slot-level skip does not look for
them (§3.2). And the anchor cannot see them: an old block in the band
keeps the references it had, so the anchor's cone never leaves the
blocks the band already carried (`AgreeBand.reaches_old`).

**Three properties come out of one induction**, and both protocols now
take that route: the core in `MysticetiProperties.lean`, Hydrozoan in
`Hydrozoan/Helpers/Banded.lean`, whose band replaced two inductions and
one 389-line file with one of each.

| Corollary | The band applied to |
|---|---|
| `Persist` | an extension, which carries every band |
| `Local` | two DAGs agreeing above a round at or below the slot's |
| view monotonicity (L2) | one universe, which carries its own bands |

The core proves `banded` in a single induction over `Decided` and takes
all three (`persist_unconditional`, `local_`, `decided_mono_of_band`).
That closes the core's missing `Local`, which §11.2 had listed as a gap,
and it re-derives `decided_mono` — a four-case induction of
`Liveness.lean` — with none of its own, which is the consumer test.

**The band has three axes**, and the third was added after the first
two: a schedule with the same round structure, naming the same leaders
at every slot sitting in the band, decides alike. That is what makes the
band reach the bound the adaptive fixpoint needs, since the slots at or
below a round are finitely many. `Slots` carries `mono` and `unbounded`,
and those two alone force it: if infinitely many slots shared a round,
monotonicity would pin every earlier slot to that round and
unboundedness would fail. Many slots per round is no obstacle.

`exists_decidedBelow` is that conversion. The bound it produces is
**not tight** — it is every slot the band's rounds can hold, where a
derivation may have named fewer — which is why `LeaderCommits` and
`Descends` remain protocol obligations rather than corollaries: a direct
commit at slot `k` depends on one leader, not on all the leaders of its
round.

**What stays outside.** `LocalTruncate` renumbers rounds and slots as
well as restricting them, and no agreement hypothesis states a
renumbering; §3.4 records why the renumbering cannot be isolated. It is
not derived from agreement, then, but from the band, whose offsets state
the renumbering directly (§3.4b).

---

## 3.9 What a commit names

`Banded` says which DAGs a verdict cannot tell apart. It says nothing
about what the verdict's *payload* denotes, and a rule that committed an
id it had never seen would satisfy every band. So a consumer that
reasons about the committed block — rather than about the verdict —
gets nothing from the band, and needs a property of its own.

`CommitsCandidate R` is it: where a rule commits `L` at slot `k`, `L` is
a block the universe holds, at that slot's round, authored by that
slot's leader. `R.IsCandidate S U k L`, in the vocabulary the carrier
already had.

**Seven protocols proved this before it had a name.** Mysticeti,
Odontoceti, Nemo, Mahi-Mahi, Hybrid, Hydrozoan and Optimal-Hydrozoan
each carry an `isLeaderBlock_of_decided`, and
`Integration/Hydrozoan/ChopDecided.lean` carries an eighth copy for a
second schedule. Every one is the same two-case discharge: a commit
constructor carries its `IsLeaderBlock` premise, and a skip constructor
concludes `none`. Both carriers' instances are one line each.

**The consumer is chain quality, and it has exactly one dependence on
the rule.** `Quality/Coverage.card_coveredAt_ge` is about valid DAGs:
the quorum structure forces every layer of every valid cone to carry
blocks from all but `f` of the correct validators, with no rule, no
synchrony and no delivery model. What the committed case adds is that
the committed block is one of those blocks — and that is the whole of
it. `mem_ids_of_decided` now reads it from the property, and
`Quality/{Inclusion,Capstone}.lean` read it from there, so a second
protocol gets this arc without a second copy of the bridge.

**What it does not give.** The density bound needs a universe's
validity — that a block references a quorum of the round below — which
`DagRule` does not carry. Lifting chain quality itself to the carrier
would need that as a new law; this property is only its rule-dependent
step, and the step was the part that was duplicated.

## 3.10 Re-genesis, and what closure looks like

Re-genesis restarts a validator whose whole history fell below a
horizon, by seating it with a reference-free block at round zero
(`Integration/ReGenesis.lean`). It was the fourth DAG-transforming
mechanism to be put through the properties, and **it needed no new
property.** That is the first evidence in this branch that the
collection is complete for a class of mechanism rather than merely
adequate to the cases that motivated it.

What it owes is two witnesses, the same two any such mechanism owes:

| | witness | why |
|---|---|---|
| safety | `Extends rule V (addGenesis …)` | it only adds a block |
| liveness | `Sustains rule V (addGenesis …) 0 1` | the block it adds sits at round zero |

Everything else followed.

- **Verdicts survive re-genesis**, which this arc did not have in any
  form: before the witnesses `ReGenesis.lean` mentioned `Decided` zero
  times, so a validator that rejoined had no guarantee that what it had
  already output still stood. One application of `Persist`.
- **The reactive commit survives it**, from the rebase.
- **`reaches_addGenesis` collapses.** It was two nested inductions over
  `ReflTransGen`, twenty-nine lines, and it is
  `Properties.Extends.reaches_iff` — a lemma every extension already
  had, which this arc was re-proving for its own.
- **Rejoin-then-prune composes**, by `RebasedAbove.trans` on the two
  rebases, with the reactive commit crossing the pair. `chop_addGenesis`
  proves a related fact by hand as an equality of universes; this is the
  transportable form.

**The one thing that looked like a gap, and was not.** `Sustains` is a
*negative* promise — above the settling round the mechanism changed
nothing — and it is silent below, which is exactly where a fill and a
re-genesis do their work. The fill and re-genesis each carried their own
copy of the additive plumbing (`skipFill_populatedOn`,
`populatedOn_addGenesis`). That plumbing is derived from `Extends`
alone: `populatedOn_insert_of_extends` takes an extension and one
singleton `PopulatedOn U' {v} r` and gives the reliable set with the
author added. What each mechanism supplies is the singleton — the gap
block, the genesis block — which is its own content, not a property.

**What no property reaches.** A re-genesis block is valid *in the
truncation* and not in the universe it came from: at round `G > 0` of
the original, a reference-free block violates the predecessor rule. So
validators retaining more history must accept a block their own rules
reject. That is an agreement problem about per-validator horizons, not a
property of a rule or a promise of a mechanism, and the file header is
right to record it rather than formalise it here.

## 3.11 The view axis

`Sustains` is what a mechanism that transforms the **DAG** owes.
`LeanDag/DoS/` transforms no DAG: its one universe-shaped constructor is
`View.ofAccepted`, and a rate-limited validator differs from an
unlimited one only in what it holds. So does a joiner. That is a second
class of mechanism, and until now it had no obligation at all.

**Safety needed nothing.** A verdict reached on a smaller view is
reached on a larger one (`decided_mono_of_banded`), so a rate limiter
cannot make a validator decide wrongly. Already derived, for both
protocols.

**Liveness had nothing.** A mechanism that deferred a block forever
satisfied every obligation in this development. `Delivers R view` is the
statement it did not: for every round, one of the views the mechanism
produces is caught up to it.

**The protocol side is derived, which is the asymmetry §3.6 predicts.**
`exists_coversUpto_decides`: every verdict has a round it is settled by
— the band's ceiling — and any view covering to that round reaches it.
A protocol proves nothing new. `decided_of_delivers` composes the two:
a mechanism that delivers reaches every verdict, so deferring a block is
a delay and never a loss.

`CoversUpto` comes with it, lifting a definition the core, Hydrozoan,
Nemo and Barnacle each wrote out separately. Both carriers' bridges are
`Iff.rfl`.

**What this replaces in the liveness route.** The core's own coverage
hypothesis is `V.CoversUpto (r + 2)` — a rule-specific number, the
decision round of a direct commit. The generic form asks for coverage up
to *the verdict's own* ceiling, which is what the band already named, so
an indirect commit anchored far above gets the right bound rather than
the direct rule's.

**The witness weakened the obligation, which is what witnesses are
for.** `Delivers` asks the view to hold *every* block of the universe up
to a round, and `DoS/Delivers.lean` cannot supply it. Two reasons, and
the second is decisive: nothing forces a withheld Byzantine block into
anybody's view, since `Delivery.accepts_correct` constrains acceptance
for correct blocks alone; and `Delivery.accepted_inj` *requires* a
validator to drop one of an equivocating pair, so at a round where an
equivocator published twice **no admissible delivery covers the layer**.
The strong form's only model is `View.full` — the mechanism that does
nothing.

`CoversOn` and `DeliversOn` are the repair: the blocks of a **reliable
set**, over a window. `deliversOn_viewUpto` exhibits it for the novelty
budget, from `accepts_correct` and `EventuallyDelivers` — a correct
validator holds every correct block after the settling round, accepts
every one it holds, and its store keeps whole causal cones.

**The budget does not appear in the argument.** A rate limit that
deferred a *correct* block would violate `accepts_correct`, so
`Novelty.lean`'s theorems — which bound the *size* of `viewUpto` — are
not needed and not used. The novelty budget keeps the store small;
what makes it safe to deploy is that it never defers what a decision
reads, and those are separate facts.

**The reactive discipline is the second witness, and it answers the
obvious doubt.** A reactive validator advances as soon as a quorum has
arrived: it never waits for every correct validator, and its
*references* omit whatever was late — `Reactive/Mysticeti.lean` gives up
reference coverage deliberately. So it looks as though such a validator
cannot promise to cover the reliable set.

It can, because the early exit governs what a validator **references**
and not what it **holds**. `PaceCore.holds` is passive delivery, the
view is built from it, and `holds_roundBlocks` already says that after
GST a paced validator holds every reliable block of a round. What the
early exit costs is `Synchronised` — reference coverage, a property of
the *universe* — which is not what a view obligation asks for.
`PaceCore.deliversOn_viewAt` is the witness.

That the reactive arc had already stated its commit in this shape, years
before the obligation existed, is the strongest evidence that `CoversOn`
is the right predicate: `ViewPace.decided_local_of_certifiesAt` counts a
reliable quorum's certificates inside `viewAt`, which is the same
counting `Liveness.directCommitIn_of_certifiesAt` and
`DoS/Delivers.lean` do. Three arcs, one shape, arrived at
independently.

**The two forms have different consumers, and that is the finding.**
`decided_of_delivers` *transports* a verdict, so it needs everything the
deciding view held — the strong form. Liveness *produces* a verdict from
a quorum of correct evidence, so it needs the weak form.
`directCommitIn_of_certifiesAt` is the consumer that made this visible:
it counts a reliable quorum's certificates inside a view rather than in
the universe, where `directCommitIn_of_coversUpto` took a `DirectCommit`
and threw the certifier set away, forcing full coverage for no reason.
`DoS.directCommitIn_viewUpto` is the payoff — a rate-limited validator
commits.

## 3.12 The third rule, and what it found

Odontoceti was chosen as the third instance because it mirrors the core
constructor for constructor at a shorter wavelength —
`decisionRound k = slotRound k + 1`, no certificate round — so the
differences it does have should have been the only work.

**Four of the six came at once.** `Causal` is the core's argument at the
same universe type; `Agree` is O5; `CommitsCandidate` is
`isLeaderBlock_of_decided`; `CommitsDirect` is `Decided.directCommit`.
All four are one line each at a native carrier
(`LeanDag/OdontocetiProperties.lean`), and the carrier is native rather
than `Barnacle.odontocetiRule` because a protocol's conformance should
not route through a mechanism (§8).

**`Banded` is blocked, and not by the properties.** Odontoceti's
`Decided.directSkip` quantifies over the candidates the universe holds:

```lean
| directSkip {k} : (∀ L, IsLeaderBlock U k L → DirectSkipIn U V L (S.slotRound k)) →
    Decided U V k none
```

so a slot with no candidate is skipped *vacuously*. `AgreeBand`'s
membership clause runs one way — a block of `U` in the band is a block
of `U'` — because a band must admit universes holding more, which is
what makes `Persist` a corollary of it. So a candidate present in `U'`
and absent from `U` is beyond reach, and the skip does not transport.
The goal that cannot be closed is `L ∈ U.ids` from `L ∈ U'.ids`, and it
is unreachable from every hypothesis the band supplies.

**This is the core's own defect, found again.** §3.2 records it: the
core's skip once had this shape, a validator holding no evidence at all
could skip, and `ugrow_commits_recur` committed slots that `ugrow_skip`
had let every view skip. `Decided.directSkip` now takes
`DirectSkipSlotIn` — a count of voting-round blocks referencing *no*
candidate of the slot — which is a fact about blocks `U` already holds,
so it transports. Odontoceti's `DirectSkipIn` counts blames against one
candidate and has the shape the core's had.

**All six now hold**, and the rest of the section records what the
attempt cost and found.

**The repair, and what it cost.** Nothing new had to be defined.
Odontoceti's `DirectSkipIn` and the core's are the *same predicate* —
both count, against `quorumCard`, the creators of blocks at
`slotRound k + 1` in view that do not reference the candidate — because
both rules blame at the round above the proposal. Odontoceti already
imports `Mysticeti`, and `Faults5 extends Faults`, so the core's
repaired machinery applies verbatim: `Decided.directSkip` now takes
`DirectSkipSlotIn`, the count of voting-round blocks referencing *no*
candidate of the slot.

Four proof sites in `Decision.lean` consumed the old per-candidate
premise, and each is now `directSkipIn_of_directSkipSlotIn` applied —
the bridge that recovers a blame against a specific candidate from a
blame against the slot. `Adaptive/Odontoceti.lean`'s bounded relation
`DecidedWithin` mirrors the constructor and needed the same change,
with `directSkipSlotIn_congr` for the schedule-reassignment case, where
the old form used `isLeaderBlock_slotsOf_congr`. The safety development
is otherwise untouched, which is what the core's repair predicted:
where a candidate exists the two forms agree.

`Banded`'s `directSkip` case now closes, by the core's
`directSkipSlotIn_band` — the two carriers project identically, so the
band transfers between them by its three fields.

**Two protocols now share one skip rule**, which is a smaller
development than two. That was not the goal of the repair and is the
clearest sign it was the right one: the vacuous form was not Odontoceti
expressing something the core could not, it was the same rule stated
before anyone had asked what a skip must survive.

**The third instance did its job.** The point of a third rule was to
test whether the six obligations are the right six. They found a defect
in the third protocol immediately — the same defect, in the same clause,
that the second instance found in the first protocol — and the repair
was the first protocol's, reused without change. That is the strongest
evidence so far that `Banded` carries real content rather than
restating what each rule already knew.

**And then the six went through.** The band's induction is four
constructors, and what Odontoceti needed beyond the core's was transport
for its own two predicates: `supportersIn`, since the direct rule counts
supporters at `slotRound k + 1` where the core counts certificates two
rounds up, and `coneSupports`/`ThickLink`, the indirect test. The
minimality premise on `indirectCommit`, which the core has no analogue
of, needed `not_thickLink_band_novel` — a fresh candidate is
thick-linked from no old anchor, so it cannot undercut the least one.
That premise is the same *shape* as the skip rule that failed, a
negative clause quantified over candidates, and it transports for the
reason the skip rule did not: it is about what an old anchor can see,
not about what the universe happens to hold.

`LeaderCommits` and `Descends` followed from Odontoceti's own liveness
results and its bounded relation, with `decidedWithin_congr_of_slotRound`
added to `Adaptive/Odontoceti.lean` — the general schedule congruence
`DecidedBelow` reads, where the file had only the `slotsOf` case the
adaptive fixpoint uses.

**And the skip is still reachable.** Making it a count of blockers
rather than a vacuous quantification made it strictly *harder* to
satisfy, and a rule no quorum can ever trigger would be sound and
useless. `SkipsUnsupported` at `quorumCard ≤ |T|` is the liveness half
of the repair: a correct quorum whose voting-round blocks reference no
candidate skips the slot, without waiting for an anchor. The count is
the core's, so `subset_blamers` applies unchanged.

Recording it because the repair was not finished without it. Soundness
was checked when the band's case closed; that a rule can still fire is a
separate question, and one a repair that tightens a premise always
raises.

**Four rules now show the six**, and the band has three instances.
Odontoceti shows the optional two as well, so its row is full.

## 3.13 The rule with no induction

FinWhale was left until last because it is the only rule here whose
verdicts are not derived. Every other `Decided` is an inductive
definition and every other `Banded` is an induction over it, with the
constructors' premises monotone in the DAG. FinWhale assigns verdicts by
a *function* `dec : ℕ → Verdict BlockId` constrained by `WellFormed` —
the paper's reverse pass read as a condition rather than a construction
— so `Decided S V k v` is existential, and an existential has nothing to
induct on.

**What replaced the induction was a normal form.** `eq_of_wellFormed`
says two assignments over the *same* direct rules and the same tie-break
agree wherever *either* has decided — not merely where both have, which
is all Lemma 12 gives across two validators. The extra strength is paid
for by `Assignment.slot`: a commit names a block of its slot, so a
committed slot sits below the DAG's horizon, and the anchor a decision
came from is a committed slot. From it, `decided_iff`:

```lean
theorem decided_iff : finWhaleRule.Decided S V k v ↔ VerdictIs (passOf S D V.val V.property) k v
```

A verdict of this rule *is* the reverse pass's verdict. That is what the
remaining properties are proved about, and none of them mentions the
existential again.

**`Banded` is then a downward induction on slots**, the same shape as
Lemma 12's, with one transport lemma per rule at each step
(`LeanDag/FinWhale/Band.lean`). The rules split three ways under a band,
and the split is the content:

* **Anchored rules transport both ways.** `IndirectCommit S D A k b`
  says something about `A`'s causal history, and a band preserves a
  history in both directions — nothing new can enter it, because the
  blocks that would witness the entry are old and reference what they
  always did. So the tie-break is the same function on both sides, which
  is what comparing two passes needs.
* **Positive rules transport forwards.** A vote, a certificate, a fast
  quorum is evidence, and evidence survives a band.
* **The skip quantifies over the slot's candidates**, and a band may add
  one.

**The third is where the core (§3.2) and Odontoceti (§3.12) had to be
repaired, and FinWhale does not.** Its blames are counted against what a
block's *parents* reference. An old block's parents are old and
reference only old blocks, so a candidate the band adds collects no
votes at all — hence no FP-evidence, `f + p` being at least two — and
the old blamers' parents, a quorum of them by validity, are all
non-voters for it. The skip survives the new candidate instead of being
restated to ignore it. Three rules met this shape and the third one
escaped it, which locates the defect: it is not in quantifying over
candidates, it is in quantifying over candidates whose absence cannot be
witnessed.

**One case the band cannot settle**, and it is not a band question. The
larger DAG may decide directly a slot the smaller one decided from an
anchor. What settles it is FinWhale's own exclusion between a direct
commit and the tie-break — `commit_pins_choose`, `commit_forces_choose`,
`skip_bars_choose` — read inside the larger DAG alone, where
`exclusions_of_views` already supplies it.

**And a horizon had to be found.** A view bounds *rounds*; the pass
recurses over *slots*; nothing in `Slots` related the two.
`Slots.slot_lt_of_slotRound_le` does: `keyed` makes
`k ↦ (slotRound k, leader k)` injective and `mono` makes the slots below
a round an initial segment, so a finite validator set stops a schedule
from fitting unboundedly many slots under a round. Without it the pass
has nowhere to start, and `Decided` is not known to be inhabited at any
schedule but the identity one — which would have left `Agree` true
everywhere and non-vacuous in one place.

**Seven rules now show the six**, and FinWhale shows `CommitsDirect` as
well. Optimal-Hydrozoan is the only carrier left short, and its `Banded`
is the last source of bespoke links in `docs/bespoke-links.md`.

## 3.14 The last carrier, and the reuse it allowed

Optimal-Hydrozoan was the carrier left short: `Agree`,
`CommitsCandidate`, `Causal` and `CommitsDirect` from the day it was
written, and no `Banded`, `LeaderCommits` or `Indirect`. It was also the
last source of bespoke links — eight of them, against a rule with no
band to route them through.

**Its `Decided` is Hydrozoan's with the fast path substituted**, so the
question was how much of Hydrozoan's band could be reused rather than
rewritten. The answer is all of it: `AgreeBand` reads a rule's `ids` and
`block` and nothing else, and this carrier's universe is a subtype of
Hydrozoan's, so `band_of` turns a band at one rule into a band at the
other in four lines. `Hydrozoan/Helpers/Banded.lean` then carries the
blocks, votes, certificates, blames and rung 1 unchanged, and what had
to be written is the fast path: `votesFor`, `WitnessesEquivocation`,
`IsFastEvidence`, `IsNoFastEvidence`, `NoEvidenceQuorumInView`,
`SkippedLeaderOptInView` and the three directions of `EvidenceLinked`.

**The skip escapes §3.2's defect for the same reason FinWhale's does**
(§3.13), and the coincidence is worth naming. `IsNoFastEvidence`
quantifies over the slot's candidates and denies evidence for each; a
band may add a candidate. But fast evidence is counted over a block's
*parents*, an old block's parents are old, and an old block references
only old blocks — so a candidate the band added collects no votes at
all, and `t_plain` and `t_equiv` are both at least one. Three rules met
this shape and were repaired (§3.2, §3.12); two met it and did not need
to be. What separates them is not the quantifier, it is whether the
absence being asserted can be witnessed by evidence that a larger DAG
could contradict.

**`LeaderCommits` and `Indirect` were the cheap half.** Both come from
the fact that every rule Optimal applies at a slot reads the schedule at
that slot alone, which is the tightness `DecidedBelow` and `Indirect`'s
second quantifier ask for. `Indirect` is Hydrozoan's argument minus one
clause: the evidence rung carries no tie-break, two candidates being
unable to clear it at once.

**What it closed.** Every rule with a carrier now shows all six.
`docs/bespoke-links.md`'s second exclusion — links a rule with no band
has nothing to route through — is empty, and the audit's separate column
reports nothing. `Barnacle.OptimalHydrozoan.holds` reads the three
properties; `Barnacle.OptimalHydrozoanLive` is `descent_of_properties`;
and `Integration.Hydrozoan.decidedOpt_chopHZ` is
`LocalTruncate.of_banded`, which deleted the last two hand-written
inductions over a decision relation in the development.

**One hypothesis to record.** `Banded` for this rule carries
`[LinearOrder BlockId]`, which the rule itself does not need — it enters
only through Hydrozoan's carrier, whose `Decided` has a tie-break, and
which the band proof reads. The other six properties are free of it, so
Barnacle's laws and the liveness route, which quantify over `BlockId`
with decidable equality alone, are unaffected.

## 3.15 The last mechanism, and the law it needed

Chain quality was the one mechanism whose capstone was still written at
a single protocol. §11.4 recorded why and predicted the fix would be a
new *carrier field*: `card_coveredAt_ge` rests on density, density rests
on a block referencing a quorum of the round below, and `DagRule` has no
validity clause.

**It is a property, not a field.** `Causal` is the closer precedent —
a structural claim about the universe, stated once and discharged per
rule — and a field would oblige `Barnacle.BaseRule` too, which has no
validity clause either, and through it six more instances. The content
is the same; only the blast radius differs. `Properties.Quorate` sits in
`Properties/Optional/`, alongside `CommitsDirect` and
`SkipsUnsupported`, because a rule that shows the six composes with
every other mechanism without it.

**The fault model had to become a parameter.** Six fault classes are in
play — the core's `Faults`, Hydrozoan's with its crash set, Odontoceti's
`Faults5`, Nemo's crash-only, Hybrid's two thresholds, FinWhale's
`Params` — and density counts against whichever one a rule carries.
`LeanDag.Reliability` is what the count actually needs: a reliable set,
a slack bounding everything outside it, and that slack being a minority.
Every class in the development supplies one in a line, and the
alternative — density per fault model — is the duplication this arc
exists to remove.

**One induction where there were going to be several.** Density and the
correct backbone read `blk`, `ids`, `CausalStructure` and `QuorateOn`
and nothing else, so they are stated over the raw block data in
`LeanDag/Density.lean`; the DoS arc, which proved density first, now
names its instance of them, and `Properties/Arcs/Quality.lean` names
another. `DoS/Density.lean` and `DoS/Exclusion.lean` each lost an
induction to it.

**What a rule gets by showing `Quorate`.** CQ1 (a commit's flush covers
all but the slack, at every round below it), CQ2 (the half, where the
committee gives it), CQ3 (ledger coverage), CQ5 (post-synchrony, every
reliable block is in every later reliable commit's cone), CQ6 (a slot
the schedule fixes in advance whose commit carries a whole round), and
CQ7, all with no argument of its own. `LeanDagTest/Quality/Generic.lean`
checks it on two rules that never had the arc: FinWhale takes all of it,
and Hydrozoan takes everything but the half — which is a fact about its
committee, `2(f + c) ≤ |Correct|` holding only when `c ≤ k + 1`, and is
why CQ2 takes that condition as a hypothesis rather than assuming it.

**Every mechanism in the development is now generic.** Garbage
collection, crash recovery, adaptive leaders, Barnacle's liveness and
chain quality are all stated over `DagRule` and a subset of the
properties. What a protocol still supplies per mechanism is the witness
that its own construction is a `Truncates` or a `Sustains` — and that is
not a gap in the properties but a limit of the carrier, which has no way
to *build* a universe (§11.4).

## 3.16 The rule that was never asked

Mahi-Mahi had `--` in every column of every table, and the recorded
reason was `audit-conformance.py`'s note: *"no carrier; band conditional
on `2 ≤ w` (§3.4c), so it needs a carrier per width."*

**Both halves of that reason had already been answered by Hybrid.**
`hybridRule (k : ℕ)` is a carrier per indirect threshold, and
`HybridProperties.banded` takes `0 < kt` while its `agree` takes
`Admissible` — a conditional band at a per-index carrier is exactly what
Mahi-Mahi needed, and it had shipped. Nothing re-read the note.
`docs/porting-plan.md`'s table lists four rules to port and Mahi-Mahi is
not among them; that is the whole of why the row stayed empty.

This is §11.2d's finding one level up. The six audits check *written
code*; nothing checks a recorded reason for absence. "Needs a carrier
per width" stopped being a reason the day Hybrid shipped one, and three
arcs went by with the row still printing dashes.

**What the port actually cost.** The four properties that need no
induction are a line each — Mahi-Mahi's universe is the core's
`BlockUniverse` at the core's `Faults`, `decided_unique` is `Agree`,
`isLeaderBlock_of_decided` is `CommitsCandidate`, the direct constructor
is `CommitsDirect`. What is Mahi-Mahi's own is the band, and it has one
idea in it.

**Every Mahi-Mahi rule reads a cone.** A vote is the least block of its
author and round in the voting block's causal *history*; a blame is the
absence of any such block. `candidatesAt_band` is the whole transport,
and it settles that set as an **equality**, both directions at once —
`reaches_old` says a block inside an old cone is old, `reaches_of` says
an old one stays inside.

That has a consequence worth naming. §3.2's defect is a negative clause
a larger DAG can falsify, and it cost the core, Odontoceti and Hybrid a
repair each. **Mahi-Mahi's skip cannot have it**, because the skip
quantifies over a *cone* rather than over the universe's candidates, and
a candidate a band adds is in no old block's history. FinWhale (§3.13)
and Optimal-Hydrozoan (§3.14) escaped the same shape by an argument
about references; Mahi-Mahi escapes it by construction.

**One strengthening in the property layer.** `AgreeBand.reaches_of`
required `lo < round C + g` and now requires `lo ≤`. Mahi-Mahi forced
it: its votes are read from a cone at the slot's *propose* round, which
is the band's floor exactly. The proof needed no change — a path *into*
the floor reads the references of the layer above it, which the band
preserves — and every other rule's band is unaffected.

**And the mechanisms came free.** Because the universe is the core's,
garbage collection and crash recovery are the core's `chop` and
`skipFill` with four `rfl`s each, and chain quality is four lines.
`scripts/audit-mechanisms.py` went from four open cells for Mahi-Mahi to
none: adaptive leaders is out of scope, Mahi-Mahi having no `BaseRule`
instance, and the other three are collected.

**Nine rules of ten now show the six.** Black Marlin is the last, and it
is the one case where the recorded reason still holds: it commits by
round with no slot-indexed decision relation, so there is nothing to
state a property *at* until it has a schedule layer.

## 4. Properties for the schedule mechanisms

`Barnacle.BaseRule` and its `Laws` are one working interface: any two
verdicts agree, a direct commit yields a verdict, candidates are
identified. `LiveRule` and `Descent` add the liveness side. Six rules
instantiate it. It has no bounded relation, and it cannot host a
reactive execution, whose clauses read the schedule; the adaptive
fixpoint needs both, so the family below is stated separately and
shares `Agree` with it.

### 4.1 What the adaptive fixpoint consumes

Read off the proof bodies of `Adaptive/Run.lean` and
`Adaptive/Liveness.lean` before the generalisation, the fixpoint used
five facts about the underlying rule and nothing else. They are now the
five properties, in `Properties/{Agree,Bounded,Commit}.lean`.

Safety, proved by the protocol:

- `Agree` — two views over one universe, under one schedule, decide
  alike. M6 as a property. Nothing before the schedule family needed
  it: `Persist`, `Local` and `Truncates` compare a verdict with a
  verdict, never two views at one slot.
- `DecidedBelow R S B V k v` — the slot sits below `B`, the verdict
  holds, and it survives any reassignment of the leaders at or above
  `B`. A **definition** over `DagRule`, not a field of it: its four laws
  (`toDecided`, `lt_bound`, `mono`, `reschedule`) are theorems and a
  protocol proves none of them.

  This replaced `BoundedRule`, a carrier extended with a second decision
  relation, and the two properties `Bounded` and `SchedLocal` relating
  it to the first. The reasoning behind the field was that a `Decided`
  derivation is a proof of a `Prop` whose anchors cannot be recovered,
  which is sound about *derivations* and beside the point about
  *verdicts*: what the fixpoint needs is not which slots a derivation
  named but which leaders the verdict depends on.

Liveness, provided by the protocol for the mechanism's existence
theorem:

- `LeaderCommits R Live` — under the protocol's precondition `Live`, a
  slot led by a member of `T` commits within bound one above it. `Live`
  is a **parameter**, not a field, because the same rule under two
  execution models has two preconditions and one relation (§4.3).
  `Live S V T lo K` is indexed by the schedule and by a slot window
  `[lo, K)`.
- `Indirect R Elig` — an anchor eligible for slot `i`, committed, with
  every eligible slot strictly between them skipped, decides `i`, and
  the verdict is unchanged by a reassignment of leaders elsewhere.
  `Elig` is a parameter and reads the round structure alone: every rule
  here makes an anchor eligible a wave above the slot, and the property
  does not care which wave.
- `Descends R S c` — `c` consecutive slots committed within `b + c`
  decide everything below `b` within `b + c`. **No longer an
  obligation**: it is `Indirect` with a downward induction on top
  (`Properties/Derived/Descent.lean`, §11.2b), and what a protocol
  supplies for it is the round-structure hypothesis and `c`.

`Adaptive/{Policy,Run,Liveness}.lean` are stated over `DagRule` and
these, and name no protocol. `Adaptive.run_agree` uses `Agree` alone.

### 4.2 The staged precondition

The existence theorems ask for `Live` at every height `E`, under the
schedule the policy computes from a height-`E` partial run's verdicts,
over the slots `[W, W·(E+2))`. For the timed core this is a
restatement: `coreLive` reads no leader, and the global hypotheses of
the old `adaptiveRun_exists` produce it at every height, which is all
`Adaptive/Mysticeti.lean` does. For a reactive execution it is the
statement: `ReactiveM`'s `cert_or_wait` reads `S.leader k`, so its
clauses hold only under the schedule the validators followed, and an
adaptive schedule is only determined through epoch `E + 1` at height
`E`. Any two height-`E` runs compute the same leaders on that window
(`partialRun_agree` with `adapted`), so the hypothesis names one
schedule prefix per height.

What this does not yet say is that `reactiveLive` depends on the
schedule *only* through the leaders below `K`. That is true of the two
clauses by inspection and unproved. It is the congruence a deployment
needs in order to read the staged hypothesis as one execution's clauses
at increasing horizons, and it is a property of the reactive execution
model, not of the rule.

### 4.3 Instances

- **Core Mysticeti** (`MysticetiProperties.lean`): `agree`,
  `leaderCommits` under `coreLive`, and `descends` under
  `SpansEligible`. Two properties where there were five. The core keeps
  a `DecidedWithin` relation of its own, because `LeaderCommits` and
  `Descends` must produce a **tight** bound and the semantic form cannot
  recover one; `decidedBelow_of_decidedWithin` carries it across. It is
  the protocol's tool, not part of any interface.
- **Reactive Mysticeti** (`Reactive/MysticetiProperties.lean`): the
  same rule, so the safety side is inherited, and
  `leaderCommits_reactive` under `reactiveLive`, from
  `ReactiveM.directCommit`. This is the case `Live` was made a
  parameter for.
- **Consumers.** `Adaptive/Mysticeti.lean` restates every statement of
  the arc before the generalisation verbatim — `AdaptivePolicy`,
  `PartialRun`, `AdaptiveRun`, `partialRun_agree`, `adaptiveRun_agree`,
  `epoch_closes`, `exists_partialRun`, `adaptiveRun_exists`,
  `decidedWithin_congr` — each a corollary of the generic theorem at the
  core instance. `Integration/AdaptiveReactive.lean` is the result the
  bespoke development did not have: `adaptiveRun_exists_reactive`,
  Hammerhead over reactive Mysticeti, from `Adaptive.run_exists` fed
  with `leaderCommits_reactive` and nothing else changed.

### 4.4 Commits, and growth

Two theorems close gaps the family left open when first built.

**What the run commits.** Existence says every slot has a verdict.
`Adaptive.Run.commits` says which are commits: at a `T`-led slot inside
a live window of the run's own schedule the verdict is `some L`, by
`LeaderCommits` and `Agree` through `Bounded`; `Run.commits_in_epoch`
adds that under `PlacesRuns` every epoch past the first holds `c`
consecutive commits. `Run.live_of_staged` reads the staged precondition
at the total run's schedule, since that schedule is the policy's
(`Run.assign_eq`). For the core, `adaptiveRun_commits_in_epoch` is the
liveness statement AL5 was standing in for; for reactive Mysticeti,
`adaptiveRun_commits_reactive`.

**The fixpoint under growth** (`Adaptive/Growth.lean`). `run_agree` is
agreement over one universe; a running system's DAG grows.
`run_agree_extends`: a run on `U` and a run on an extension `U'`, from
views one contained in the other, hold the same verdicts and the same
schedule. This is the arc's first composition theorem — `Persist`
composed with the schedule family — and the proof is the strong
induction of `partialRun_agree` with one extra step per epoch: the
smaller run's verdict is carried to the larger view by `Persist` at the
smaller run's schedule, where the larger run's verdict also lives after
`SchedLocal`, and `Agree` closes. So `Ok` is asked for at the smaller
run's schedule; for the core that is `Quorate` there
(`adaptiveRun_agree_extends`).

It needed one clause the policy owes and nothing else does. `adapted`
says the leader of a slot reads the verdict prefix and not the view,
but it quantifies views over *one* universe; a policy that read the
size of the universe would satisfy it and reassign differently at `U'`.
`Policy.Stable` — the same leader for the same verdicts on an extension
— closes this. A reputation rule reading committed blocks satisfies it,
since extension preserves every old block (`Extends.block`); the
constant policy does by `rfl`. It is a hypothesis of the theorem rather
than a field of `Policy`, so no displayed statement changes and a
policy that is not stable still has `run_agree`.

Both are generic, and both depend on `propext` and `Quot.sound` only.

Not done: the Odontoceti mirror (`Adaptive/Odontoceti.lean`, 415
lines) still stands, now importing the core instance for the shared
names; collapsing it to an instance is the next step, and the first
test of whether `Live`'s shape is Mysticeti's or generic. Hydrozoan has
no bounded relation. `Reactive/Odontoceti.lean`'s duplication is
untouched.

### 4.5 Adaptive leaders over Hydrozoan

The arc's thesis at the point where it pays. Hydrozoan and the
adaptive-leader mechanism were developed independently and never met.
`Integration/AdaptiveHydrozoan.lean` marries them without either being
told about the other, and proves nothing that is not an application.

Hydrozoan supplies four properties. `Agree` is its slot-agreement arc
result. `Banded` is the induction of `Helpers/Banded.lean`.
`LeaderCommits` and `Descends` rest on its direct-liveness arc and on
the graded rule's totality with the committed-run descent, each rebuilt
at a **bound**, since an opaque verdict cannot say which leaders it
depends on.

| | Needs | Result |
|---|---|---|
| safety | `Agree` | `adaptiveRun_agree_hz` |
| liveness | `Agree`, `LeaderCommits`, `Descends`, `PlacesRuns` | `adaptiveRun_exists_hz` |

Safety holds under no synchrony, fairness or population hypothesis, for
any adapted policy including adversarial ones. Liveness adds the policy
clause that prices reassignment.

**And progress survives whatever a mechanism adds.**
`Properties/Derived/Progress.lean` composes `LeaderCommits` with
`Descends` into `decidedBelow_of_run`: every slot below a run of `c`
reliable-led slots has a verdict. That is the statement §11.4c said was
missing. Applied to Hydrozoan it says a candidate a fill put on a slot
nobody voted for does not stall the protocol, because the anchored rule
disposes of it. Hydrozoan needs no direct skip for this, and neither the
theorem nor its proof mentions the fill, which is the point: once the
skip rule counted blockers, the fill stopped being a special case.

---

**An open question worth stating.** Can a non-reactive protocol be made
reactive by proving a property, rather than by a fresh development?
`Reactive/Basic.lean` states the discipline as *what survives is
exactly what the commit rule counts*, with a `vote_or_wait` clause: at
the round above a reliable leader a block either references the leader,
or its builder waited the full timeout and would have referenced it.
The candidate property is that **a rule's direct-commit liveness needs
only the leader's vote to be counted, and never general reference
coverage** — a rule meeting it can be driven by evidence rather than by
a timer. Reactive schedules lose `SynchronisedOn` in general, so a rule
that needs full coverage cannot be made reactive; this property is
exactly the line between the two.

---

## 5. Properties for the measurement mechanisms

Chain quality should **not** be derived from full coverage.
`Reactive/Basic.lean` records that a reactive builder omits whatever had
not arrived when its exit fired, so `SynchronisedOn` fails in general —
a coverage-based chain quality argument therefore cannot hold for a
reactive protocol, which is the class the result is most wanted for.

The intended route is instead **a fair schedule together with
self-reference inclusion**: a correct validator's blocks reach the
committed sequence because the schedule places its slots and because
each of its blocks carries its predecessor, so committing any one of
them commits the chain behind it. `DoS/SelfParent.lean` and
`Integration/Hydrozoan/Universe.lean`'s `SelfParenting` already state
the self-reference clause; `WaveRobin.lean` states fairness without
premise. Both ingredients exist and have not been combined.

---

## 6. Protocols in scope

Seven rules carry a decision relation: **Mysticeti** (core),
**Odontoceti**, **Nemo**, **Mahi-Mahi**, **Hybrid**, **Hydrozoan**,
**Optimal-Hydrozoan**. The hybrid fault model is treated as a protocol
in its own right rather than as a mechanism.

**FinWhale** is in scope and has a different shape: its commitment is a
decision *function* `dec : ℕ → Verdict BlockId` constrained by a
`Verdicts` structure of laws, rather than an inductive relation. That
is already closer to a consumer interface than the others, and it is a
useful test — semantic properties are statable of a constrained
function as readily as of a relation, where a syntactic schema over
constructors would not be.

**Black Marlin and Minnow are out of scope**, being unsafe.

That FinWhale's rule is not inductive is a second reason to prefer
semantic properties over the generic inductive relation that
`transformer-interface.md` §2 proposed.

---

## 7. What this supersedes, and why

`transformer-interface.md` §2 proposed a generic inductive `Decided`
with a `RuleSpec` of parameters, each protocol proving an equivalence
to it. A partial build — since removed — showed the schema is
expressible in **four** constructors for all nine inductive relations,
and that `dom_of_decided` and `cand_of_decided` fall out of it, the
latter existing nine times in the repository. The shape, for the record
should it be wanted again: `Dom` a slot domain, `Cand`, `Elig`,
`Direct` as the disjunction of a protocol's commit paths, `Skip` as a
predicate of the slot covering both the per-candidate and slot-level
forms, `Rung : Fin m → …` ordered with a `Tie` flag per rung, and `lt`
as a field rather than a `LinearOrder` instance so that a protocol
whose rungs are unique need not carry one.

It is nonetheless the wrong foundation:

- It cannot describe FinWhale, whose rule is a function with laws.
- It makes the arc depend on a schema that a protocol might not fit,
  which was §2.4's own first risk.
- The properties are what the mechanisms need. The schema is one way to
  discharge them, not a thing worth depending on.

**The schema is therefore dropped, not merely demoted.** It was kept
briefly as an optional shortcut — prove the properties once for the
generic relation, and a conforming protocol inherits them — but nothing
exercised it, and an unreferenced file asserting a role nothing plays
is how a development rots. The idea survives here rather than in
`LeanDag/`. If §9's per-protocol proofs turn heavy, the shape above
reconstructs in an afternoon, and it should then be built against a
worked instance rather than ahead of one.

---

## 8. Layout

**The layering rule.** Mechanisms depend on properties; properties
depend on nothing but the core block and schedule vocabulary. Protocols
show conformance to the properties. **No mechanism refers to another.**

This is why the carrier is `Properties.DagRule` and not
`Barnacle.BaseRule`, though the two have the same shape and Barnacle
discovered it first. Barnacle is a mechanism — the adaptive leader
count — so a `Properties` importing it would tie garbage collection,
crash recovery and chain quality to the leader count for no reason.
`Barnacle/Helpers/DagRule.lean` supplies `BaseRule.toDagRule`, so the
six existing instantiations serve as carriers without being restated,
and the dependency runs from the mechanism to the properties. The
tidier form is for `BaseRule` to `extend DagRule`; that edits a frozen
`Model/` file and is deferred.

The rule is checkable: `Properties.Carrier` currently reaches nine
modules transitively and none of them belongs to a mechanism. A guard
script could enforce it if the arc grows.

Interfaces and their consequences in one place; conformance stated
beside each protocol, under whatever discipline that directory already
keeps.

```
LeanDag/Properties/
  Carrier.lean     the abstract DAG the properties talk about
  Band.lean        AgreeBand and Banded, the one safety obligation
  Candidate.lean   IsCandidate, and CommitsCandidate: what a commit names
  Extends.lean  Agreement.lean   vocabulary the derived properties use
  Derived/Persist.lean    Persist, and its route from the band
  Derived/Truncate.lean   LocalTruncate, and its route from the band
  Derived/FromBand.lean   the routes, and view monotonicity and the bound
  Derived/Bounded.lean    the laws of DecidedBelow
  Derived/Progress.lean   a committed run decides everything below it
  Optional/Skip.lean      SkipsUnsupported: promptness, not liveness
  Optional/Direct.lean    CommitsDirect: what a window count counts
  Truncate.lean   Truncates and Rebases, the schedule half
  Sustain.lean    Sustains, and what a mechanism's promise carries
  Agree.lean  Bounded.lean  Commit.lean        the schedule family (§4)
  Arcs/GC.lean          garbage collection, given a band
  Arcs/SafeSkip.lean    crash recovery, given Persist
  Arcs/Quality.lean     chain quality, given fairness and self-reference  (planned)
  Compose.lean          RebasedAbove/Rebases/Truncates compose

LeanDag/Adaptive/{Basic,Policy,Run,Liveness}.lean   the mechanism, over BoundedRule
LeanDag/Adaptive/Growth.lean             the fixpoint under Extends (§4.4)
LeanDag/Adaptive/Mysticeti.lean          the core instance; the old statements as corollaries
LeanDag/Integration/AdaptiveReactive.lean   Hammerhead over reactive Mysticeti

LeanDag/Hydrozoan/Properties/{Statement,Proof}.lean
LeanDag/OptimalHydrozoan/Properties/{Statement,Proof}.lean
LeanDag/MahiMahi/Properties/{Statement,Proof}.lean
LeanDag/FinWhale/Properties/{Statement,Proof}.lean
LeanDag/{Odontoceti,Nemo,Hybrid}/Properties.lean
LeanDag/MysticetiProperties.lean
LeanDag/Reactive/MysticetiProperties.lean
```

The adaptive mechanism has no `Arcs/` bridge file, unlike garbage
collection and crash recovery: those mechanisms are stated over
concrete universes and the bridge applies a property to them, whereas
`Adaptive/{Policy,Run,Liveness}.lean` are themselves stated over
`BoundedRule`, so the mechanism *is* the generic theorem and the bridge
is the instance file.

Conformance belongs with the protocol. For the six arcs in
`check-arc-holes.py`'s `ARCS` the statement/proof partition applies, and
it **suits** this work rather than constraining it: a conformance claim
is precisely a statement worth reading without its proof, the checker
then guarantees no hole hides in the discharge, and each protocol's
conformance earns an arc label in the report alongside its own results.
Conformance statements take the fault model and schedule as instance
arguments, never declarations, so the rule against instances in a
`Statement.lean` never applies. Mysticeti is a single file rather than a
directory, hence the one flat module.

---

## 9. Phases

- **G0** `Carrier.lean` (**done**). `DagRule` — a universe type, views
  over it, projections into the shared `Block` vocabulary, and the
  decision relation as a field — with `Causal`, the structural facts
  `Barnacle.Laws` states for views and not for universes, and
  `AgreeAbove`, the agreement notion locality is stated against. The
  shape was discovered by `Barnacle.BaseRule`, and
  `Barnacle/Helpers/DagRule.lean` coerces its six instantiations into
  the carrier, so no protocol restates anything.
- **G1** State `Local`, `Persist`, and `LocalTruncate` (**done**), with
  two findings on `Persist` in §3.3 and, in §3.4, the vacuity that
  replaced the re-indexing property with a combined one. All three are
  now consequences of the band rather than obligations (§3.8, §3.4b).
- **G2** Prove garbage collection and crash recovery once from them,
  and `Compose` (**not built**, §11). **Crash recovery done**
  (`Properties/Arcs/SafeSkip.lean`): the fill is an extension, so any
  protocol with `Persist` inherits it. Ordered before garbage
  collection deliberately, since persistence needs no renumbering and so
  banks one mechanism before the uncertain part is attempted.
  **Garbage collection done**
  (`Properties/Arcs/GC.lean`): both transport directions are
  `LocalTruncate` applied, and `LocalTruncate` is the band applied, so
  the arc holds the `Truncates` witness for the canonical cut and
  nothing else. Its consumer test is `decided_chop_iff`, which
  `GC/ChopDecided.lean` proved by induction and the arc re-derives in
  one application; the induction has since been deleted (§11.4e).
- **G3** Discharge them for Hydrozoan (**done**) — HZ9 states
  `Causal`, `Banded`, `Agree`, `Persist` and `SkipsUnsupported` at grade
  `qFast ≤ |T|` (§3.7). Persistence is unconditional, as §3.2 predicts
  for a rule whose skip counts blames at the slot. `Local` and
  `LocalTruncate` are not stated: both are the band applied (§11.4d). Two consumer tests passed with no induction
  of their own, both in `Integration/Hydrozoan/ViaProperties.lean`:
  `decided_fillHZ`, a six-constructor induction in `FillDecided.lean`,
  and `decided_chopHZ`, an induction in `ChopDecided.lean` — both since
  deleted, with the properties route their only route (§11.4e). **The
  protocol owes one induction**, the band in
  `Hydrozoan/Helpers/Banded.lean`, and no more, whatever mechanisms
  follow. It began as three, one each for persistence, locality and
  truncation.
- **G4** Discharge them for the core (**`Persist` done**, and
  *unconditional* once the second instance turned up a defect in the
  core's skip rule — §3.2 — with the core's fill transport re-derived as
  the consumer test and its counting hypothesis dropped). `Local` is
  done too, and both now fall out of `Banded` (§3.8), which also
  re-derives view monotonicity. The instance reshaped `Persist.Ok`
  before any proof was attempted, and `LocalTruncate` came out of the
  same band once it carried offsets (§3.4b). **`SkipsUnsupported`
  done** at grade `quorumCard ≤ |T|`, with SS3 re-derived as its
  consumer (§3.7). The core, like Hydrozoan, owes one induction.
- **G5** The schedule family (**built, for Mysticeti timed and
  reactive**): `BoundedRule`, `Agree`, `Bounded`, `SchedLocal`,
  `LeaderCommits`, `Descends`; `Adaptive/{Policy,Run,Liveness}` generic
  over them with the old statements as corollaries; the core and
  reactive instances; `adaptiveRun_exists_reactive`; `Run.commits` and
  `run_agree_extends` (§4.4). Remaining: collapse
  the `Adaptive` and `Reactive` Odontoceti mirrors onto instances;
  Hydrozoan's bounded relation.
- **G6** Chain quality from fairness and self-reference.
- **G7** The remaining protocols, and FinWhale as the non-inductive
  test.

---

## 10. Risks

- ~~Re-indexing may not generalise.~~ ~~Retired at G1 and G3.~~ **The
  retirement was wrong**: the property was vacuous, so proving it
  established nothing. What replaces it is `LocalTruncate`, whose
  satisfiability is witnessed (§3.4). The lesson is procedural rather
  than technical, and is recorded there.
- **The persistence grading is predicted, not checked** (§3.2).
- ~~`Carrier.lean` may need more than `CausalStructure` offers.~~
  **Retired at G0**: `BaseRule` already supplies the projection, and
  the addition is two definitions.
- **Locality is a property of the rule**, so each protocol pays one
  induction for it. The arc is worthwhile because that induction is
  paid once and serves every transformer, where today each pair of
  mechanism and protocol is a separate development — but a protocol
  meeting only one transformer gains nothing.
- **Agreement cannot be generic.** Uniqueness of verdicts turns on
  quorum intersection in a protocol's own fault model. No property here
  will produce it, and no mechanism below should be expected to.
- **Composition is the goal least served** (§11). One composition
  theorem exists, and it was possible only because both sides were
  already stated over the same carrier; `Truncates` and `Sustains`
  have not been composed with anything, and the shift of settling
  rounds under a stack is unstated.
- **Satisfiability beyond two protocols is untested.** `Descends` is
  shaped by an indirect rule with an anchoring descent, and `Live` by
  Mysticeti's preconditions. Six protocols have no instance of any
  property.

---

## 11. Where the arc stands

The goal, restated in three parts:

1. a set of properties that DAG consensus rules, and mechanisms, must
   show;
2. once a rule shows them, it composes safely and live with each
   mechanism, with no further proof;
3. the mechanisms compose with one another through the same
   properties, automatically.

**Where it stands.** Part 1 is nine obligations (§11.1). Part 2 holds
for two protocols and every mechanism in the development, in both
directions (§11.2). Part 3 holds on both axes — the DAG's, through
`RebasedAbove.trans`, and the schedule's, through `Rebases` (§11.3) —
and the last interaction proved by hand, the joiner, is closed.

What is not settled is whether nine is the right nine, and that is an
instance question rather than a design one: seven rules have none
(§11.4).

### 11.1 Against part 1: what is owed, and what follows

**Ten obligations, in the two directions §3.6 argues for.** Six fall on
the protocol unconditionally, two are optional — owed only when a
mechanism asks — and two fall on a mechanism —
which one depending on whether it transforms the DAG or a view.

| Direction | Property | Content |
|---|---|---|
| protocol | `Causal` | universes are block DAGs |
| | `Banded` | every verdict is carried by a band of rounds, with offsets on both axes |
| | `Agree` | two views of one universe under one schedule decide alike |
| | `CommitsCandidate` | a commit names a block the DAG holds, at the slot's round, by the slot's leader |
| | `LeaderCommits R Live` | under the protocol's own precondition, a reliably-led slot commits at a tight bound |
| | `Indirect R Elig` | a committed anchor with the eligible slots below it skipped decides the slot, at a tight bound |
| protocol, optional | `CommitsDirect R Direct` | a directly committed candidate is a commit verdict — owed when a mechanism counts the rule's direct predicate |
| | `SkipsUnsupported R Ok` | an unsupported slot is skipped without waiting for an anchor |
| mechanism, DAG | `Sustains R U U' G R₀` | above the settling round the transformed DAG holds the same blocks, at rounds `G` apart |
| mechanism, view | `DeliversOn R view T lo` | for every round, one of the views produced holds every `T`-block from `lo` up to it |

`ViewSound` was on this list and is now a field of `DagRule`: every
protocol's view type already carried the proof (§11.4d).

**And what follows from them, which no protocol proves.**

| Derived | From |
|---|---|
| `Persist`, `LocalTruncate` | `Banded` |
| `Descends R S c` | `Indirect` |
| view monotonicity, a slot bound, `exists_coversUpto_decides` | `Banded` |
| cross-cut and cross-horizon agreement | `Agree` + `LocalTruncate` |
| agreement across an extension | `Agree` + `Persist` |
| `decidedBelow_of_run` | `LeaderCommits` + `Descends` |
| `LiveRule.Descent`, and so Barnacle's `LiveOn` | `LeaderCommits` + `Indirect` |
| a commit's causal cone is real | `Causal` + `CommitsCandidate` |
| the three liveness predicates, and composition | `Sustains` |
| non-equivocation across a cut | `Truncates` |
| the additive half of production | `Extends` |
| `decided_of_delivers` | `Banded` + `Delivers` |

**The set a protocol proves is smaller than the set it satisfies**, and
keeping the two apart is what §11.4b's folder rule is for. `Persist` is
the clearest case: it is read by name by two mechanisms, so it stays a
named property, and it is proved by nobody.

Three were stated wrongly first and corrected once a witness was
demanded — the re-indexing property (§3.4), `Sustains` v1 (§3.6), and
`Delivers` (§3.11). Three more were stated twice over and found to be
one relation (§11.4d). Chain quality has no property of its own (§5).

### 11.2 Against part 2: two protocols, every mechanism

**Ten decision rules, eight carriers.** `scripts/audit-conformance.py`
recomputes this from `docs/decls.json`: a rule shows a property when
some theorem concludes it at one of the rule's carriers, or when its
conformance `Statement` lists it.

| rule | `Causal` | `Banded` | `Agree` | `CommitsCandidate` | `LeaderCommits` | `Indirect` | `CommitsDirect`* | `SkipsUnsupported`* |
|---|---|---|---|---|---|---|---|---|
| core Mysticeti | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| reactive Mysticeti | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Hydrozoan | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | — | ✓ |
| Optimal-Hydrozoan | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | — |
| Odontoceti | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Nemo | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | — |
| Hybrid / Orcaella | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Mahi-Mahi | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | — |
| FinWhale | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | — |
| Black Marlin | — | — | — | — | — | — | — | — |

\* optional (`Properties/Optional/`): owed when a mechanism counts the
rule's direct predicate, or when the rule skips without waiting for an
anchor. A dash there is not a gap.

`Persist` and `LocalTruncate` are not columns: they follow from `Banded`
for every rule that has it, so there is nothing per protocol to record.
`Descends` is no longer one either — it follows from `Indirect`, which
replaced it in the required set (§11.2b). Each protocol still states it,
because the round-structure hypothesis it needs is the protocol's, but
the statement is now three lines and no induction.

**Six rules show the six**, and `Banded` has five instances —
reactive Mysticeti shares the core's rule. Odontoceti is the third
(§3.12) and the first that was not written with the properties in view;
what it cost, and the defect it found on the way, are recorded there.

**Four carriers came at once, from `Barnacle.BaseRule.toDagRule`**
(`Barnacle/Conformance.lean`). Barnacle's instances are not further
protocols — they are Mysticeti, Odontoceti, Nemo, Hydrozoan,
Optimal-Hydrozoan and Orcaella under an interface whose fields are a
superset of `DagRule`'s — so the coercion carries them, and `Laws`,
which each already proved, is two of the six obligations verbatim:
`agree` **is** `Agree`, and `candidates` **is** `CommitsCandidate`.
Optimal-Hydrozoan and Orcaella had no other route: the first decides
over `OptUniverse`, the second is indexed by an admissible threshold, so
its carrier is one per `k`.

**What an interface leaves undone, which is the more useful half.**
`Causal` needs completeness and the round condition on references at the
*universe*, and `Laws` states those for views only. `Banded` is the
induction a protocol owes and no interface can supply it. So the four
new carriers gain two obligations of six, the honest reading being that
a shared interface hands over the laws a protocol already had, under new
names, and nothing deeper.

**One rule has two carriers, and the audit has to know.** Core Mysticeti
holds `MysticetiProperties.mysticetiRule` and `Barnacle.mysticetiRule`,
and its `CommitsDirect` is proved at the second. A first version of the
script matched carriers by their short name and so credited the core
with Barnacle's instances and *vice versa*; it now disambiguates by
module and takes a list of carriers per rule. Hydrozoan is deliberately
not carried twice — Barnacle instantiates it, so a second carrier could
be built and would prove two properties Hydrozoan already proves, which
is a way to make this table read better than the development is.

**Three rules had none** when this section was written, for reasons that
were not the same. Mahi-Mahi's decision relation is indexed by a wave
width and its band is conditional on `2 ≤ w` (§3.4c), so it needs a
carrier per width. FinWhale had no `Slots` layer at all and Black Marlin
commits by round with no slot-indexed relation — for those two the
carrier was not the first step, the schedule layer was. FinWhale has
since been given one and shows all six (§3.13), and Mahi-Mahi's
per-width carrier is four lines (§3.16). Black Marlin stands.

The consumer tests passed. Each is a former bespoke induction
re-derived with none — and the six named first have since had the
induction deleted (§11.4e): `decided_fillHZ`, `decided_chopHZ`,
`decided_fill_of_persist`, SS3 as a verdict (`decided_none_fresh`),
`directCommit_chop` for liveness, and the adaptive arc entire, AL3 and
AL5 standing verbatim as corollaries. One result the bespoke
development did not have: Hammerhead over reactive Mysticeti
(`adaptiveRun_exists_reactive`, `adaptiveRun_commits_reactive`).

What part 2 does not yet deliver:

- **Both protocols now have the full set**, and the set they prove is
  smaller than the set they satisfy: `Persist`, `Local`,
  `LocalTruncate` and view monotonicity are all `Banded` applied, so
  each protocol owes one induction (§3.8, §3.4b). Hydrozoan takes
  adaptive leaders through it (§4.5), safety and liveness both, and
  both protocols take garbage collection at any truncation rather than
  only at the canonical cut. No protocol is short of an obligation.
- **Seven rules have no instance of any property**, and this is now the
  dominant gap. Six obligations validated against two protocols is a
  thin basis for claiming they are the right six; whether `Descends` and
  `Live` are generic or Mysticeti's shape with the name removed stays
  unknown until a third rule takes them. Odontoceti and Nemo are the
  cheapest — same `IsLeaderBlock`, same `Eligible`, `decisionRound + 1`
  where the core has `+ 2`.
- **"Safe and live" here means the mechanism's own theorems**, at any
  rule with the properties. Ledger validity and chain quality are not
  among the properties, and the liveness preconditions — `PlacesRuns`,
  the staged `Live` — are hypotheses the deployment meets, not things
  the properties discharge.

### 11.2b Tier 3: Barnacle's liveness, through the properties

Barnacle's liveness mechanism runs on `LiveRule.Descent`: two laws, from
which `Heads/Proof.lean` derives the stretch descent, the heads
argument, and `LiveOn` under round-robin at every leader count. Six
rules proved `Descent` for themselves. Three now get it from the
properties, and the two laws land differently.

**`indirect` is a property that was missing.** It is the indirect rule —
a committed anchor a wave above the slot, with the eligible slots
between it and the slot skipped, decides the slot — and nothing in the
collection implied it. `Descends` is weaker: it asks for a *run* of
consecutive commits, which is what the descent produces after an
induction, not what the rule provides in one step. The three protocols
each carried that induction, and each carried the same case split at
the bottom of it.

`Properties.Indirect` is the case split. `Derived/Descent.lean` is the
induction, once. `Descends` is a corollary and no longer an obligation,
which is why the required set is still six: `Indirect` took its place.

**`goodLeaders` is `LeaderCommits` with the bound thrown away.** The
property is the stronger claim — it produces the commit at a *tight*
bound, which Barnacle's law never asked for — so the derivation is one
instantiation at the one-slot window `[κ, κ + 1)`.

**What could not be generic, and why that is the right answer.** A rule's
`Good` is a field of `LiveRule` and its `Live` is a parameter of
`LeaderCommits`; each rule chooses both, so the bridge between them is
rule-specific. `LiveRule.GoodGives` is that bridge, and the check that
it is not smuggling anything is that it never mentions `Decided`: for
all three rules it is the same repackaging of a synchronised, populated
quorum, with the horizon read off the wave.

**What it cost, per protocol.** One `Indirect` — for Mysticeti and
Odontoceti the case split lifted verbatim out of the deleted induction,
for Hydrozoan the three graded rungs likewise — and one `GoodGives`, ten
lines. What it removed: three `decidedBelow_of_committed_run`
inductions, Hydrozoan's `decidedBelow_of_anchor`, and the `Descent`
proofs in `Barnacle/Helpers/{MysticetiLive,Odontoceti}.lean` and
`Barnacle/HydrozoanLive/Proof.lean`. None of those three files now
argues about `Decided`.

**The three rules that keep bespoke `Descent` proofs** — Nemo, Orcaella
and Optimal-Hydrozoan — keep them because they have no `LeaderCommits`
and no `Indirect`, which is the instances gap of §11.4 seen from the
liveness side rather than the safety side. Nothing about tier 3 blocks
them; the band does.

### 11.2c The audit that closed the claim

§11.2 said four rules show the six properties. It did not say whether
the *mechanisms* took them, and they did not. `scripts/audit-bespoke.py`
measures it: with the properties and each conformance file as barriers,
which protocol theorems *about verdicts* can a mechanism theorem's proof
still reach? Thirty-five could, for the four conforming rules, and
`docs/bespoke-links.md` is the record of removing every one.

**The measurement needed two exclusions to mean anything.** Shared
structure is not borrowing — counting `mem_blocksAt` and
`card_validators` gives 382 links and measures nothing — so the targets
are the 115 protocol theorems that name a decision relation. And a rule
with no `Banded` has nothing to route through, so the fifteen links for
Optimal-Hydrozoan, Nemo and Hybrid/Orcaella are reported apart and do
not fail a run. They are §11.4's gap from a third side.

**Three of the thirty-five were not substitutions.** Group C was
*circular*: `Laws.decided_of_directCommitIn` is `CommitsDirect`, and
`CommitsDirect` was derived from `Laws`, so it took proving the property
natively for three rules first. Group D needed a bridge, the same shape
as `LiveRule.GoodGives`: the consumers carry synchrony loose and
`LeaderCommits` takes it packaged. And Hydrozoan's `CommitLiveness` had
a conjunct with no property at all — the slow threshold, direct evidence
in the DAG — so the deployment now claims the verdict and not the
evidence, which is what a recovered replica's liveness is about.

**Two costs, both worth naming.** Four files were `Type*` where
`Properties/` is `Type`, so they could not name a property; dropping
them took 27 files with them, through the pacing layer into FinWhale,
Black Marlin and Mahi-Mahi. And `OdontocetiProperties.lean` imports the
adaptive arc, so Odontoceti's carrier sat downstream of a mechanism and
no mechanism could reach it; it moved to `Odontoceti/Carrier.lean`. A
conformance layer has to be upstream of every mechanism or it cannot
serve one, and nothing before this audit had forced the point.

### 11.2d The audit that measured absence

§11.2c closed the claim that mechanisms *borrow* from protocols.
It did not close the claim that mechanisms *reach* them.
`scripts/audit-mechanisms.py` is the difference, and it exists because
of a question the other audits cannot answer.

**Every audit here checks written code.** `audit-conformance.py` reads
theorem conclusions and says which rules show which properties.
`audit-bespoke.py` walks the dependency closure and says which
mechanism proofs reach a protocol outside the properties. Both are
computed from declarations. A mechanism nobody ever applied to a rule
leaves **no declaration behind**, so neither audit sees it, and the two
together read as a claim they do not make: "Hybrid shows all six" plus
"no mechanism borrows" sounds like "Hybrid has every mechanism", and
did not mean it.

This is the same shape as the vacuity findings of §3.4 and §3.6 — a
statement that is true and empty — moved up a level. There the danger
was a property with no models; here it was a *claim* with no instances.

**What it measures.** For each mechanism, the generic theorems a
protocol instance applies; for each rule, whether any declaration
applies one of them at one of its carriers. A cell is `open` when the
rule shows everything the mechanism asks and no such declaration
exists: not a defect, but work the properties have already paid for and
nobody collected.

**The first run found thirteen open cells**, and eight were collected
the same day, which is the measurement worth keeping:

| what it took | cells |
|---|---|
| chain quality, four rules | 4 lines each, in a test file |
| garbage collection, Hybrid | the core's `chop` plus `honestNoEquiv_chop`, which already existed |
| crash recovery, Hybrid | the core's `skipFill` plus `honestNoEquiv_skipFill`, likewise |
| crash recovery, Odontoceti | four `rfl`s — its universe *is* the core's |
| crash recovery, Hydrozoan | it had the results and had hand-composed them; now `Persist.of_banded` and `decided_agree_extends` applied |

The Hydrozoan cell is the one to note: the mechanism was there, and the
docstring already *claimed* it was `Arcs.decided_agree_extends`, while
the proof inlined the same two steps. §11.3b's rule — an arc that
consumes a property is not finished until every theorem it states has
been asked for from the properties — had been stated and not enforced.
The audit enforces it.

**The remaining four cells were then collected too**, and the run now
reports none open. They were garbage collection and crash recovery for
Nemo and for FinWhale, the two rules that carry their own universe
*record* rather than the core's. `DagRule.Universe` is opaque, so
neither could reuse `chop` or `skipFill` as a whole; what each reused
instead is the mechanism's *data*, and what each supplied is its own
invariant discharge (§11.2e). A fifth cell is closed by a
counterexample rather than by work: Optimal-Hydrozoan's recovery breaks
its own leader-exclusion rule (`not_leaderExcludedAll_Ufill`), which is
why `skipFill` is out of scope for it and not owed.

### 11.2e What a rule with its own universe record supplies

Nemo and FinWhale close their four cells in
`Integration/NemoMechanisms.lean` and
`Integration/FinWhaleMechanisms.lean`. Two things were changed to make
that possible, and both are the same change.

**The cut's block operator moved off the universe.** `chopBlk blk G` is
stated over a bare block assignment; `chopBlock U G` is
`chopBlk U.block G`. **The fill's message moved off the universe too.**
`SkipData ids blk` carries the fields `SkipMsg U` carried, and
`SkipMsg U` abbreviates `SkipData U.ids U.block`, so every existing
statement about a core message reads unchanged. Neither change touches
a proof: the fields instantiate to the same propositions.

What each rule then writes is its own universe, and nothing else. Nemo's
`chopNemo` discharges a majority parent quorum and universal
non-equivocation; FinWhale's `chopFinWhale` discharges `ValidHere`'s
four clauses and `correct_single`. The four transports —
`decided_chop_iff`, `decided_agree_chop`, `decided_skipFill`,
`decided_agree_skipFill` — are then `LocalTruncate.of_banded`,
`decided_agree_truncate`, `Persist.of_banded` and
`decided_agree_extends` applied, with no induction of their own.

**The fill has a second form, and FinWhale needs it.**
`SkipData.fillBlock` inserts a self reference, because the core's
`ValidWrt.self_parent` demands a parent by the same author.
`SkipData.copyBlock` does not: it takes the donor's references at that
round and re-authors them. The distinction is not cosmetic. A self
reference at the boundary round grafts the anchor's parents onto the
donor's, and a validity clause that constrains what a block's parents
*jointly* reference — FinWhale's `ValidHere.leader_clause`,
Optimal-Hydrozoan's `LeaderExcludedAll` — is not preserved by that
graft: nothing bounds the anchor's grandparents and the donor's
together. With `copyBlock` the filled block's parents *are* the donor's,
and every clause is the donor's verbatim.

So the finding recorded against Optimal-Hydrozoan is a finding about
`skipFill`, not about fills. Whether `copyBlock` closes that cell too
has not been checked.

### 11.3 Against part 3: the mechanisms compose

**What a mechanism owes is a rebase, and rebases compose.**
`Properties/Compose.lean` states it: `RebasedAbove.trans` adds the
offsets and takes the later settling round **read in the source's
frame**, so the second mechanism's round has the first's offset added
before the comparison. `Rebases.trans` does the schedule axis, and
`Truncates.trans` the two together, so a stack of cuts is a cut.

The arithmetic is the whole content, and getting the frame wrong is the
way to get it wrong: a composite that compared the two settling rounds
in different frames would claim agreement over a band the second
mechanism never promised.

**The consumer test passed, and it needed a missing witness first.** The
core's fill had no `Sustains`, which §11.2's table recorded — so the
core's two mechanisms could not be composed through the properties even
though each transported verdicts on its own.
`Properties/Arcs/SafeSkip.sustains_skipFill` supplies it: above the gap
the fill added nothing, so it settles at `sk.r + 1` at no offset. Then
`Integration/Stack.sustains_stack` is `RebasedAbove.trans` applied, and
`directCommit_stack` is a result that file did not have — the reactive
commit crossing a fill *and* a cut, from one obligation rather than one
transport per invariant. I16a–c remain as the hand-written comparison.

`run_agree_extends` (§4.4) is the other composition: the adaptive
fixpoint under `Extends`.

**Adaptive leaders under garbage collection (I5) closed too.** The
joiner arc proved that a pruned validator computes the same *leaders* as
the network — the premise an agreement argument needs — and stopped
there. `adaptiveRun_agree` could not supply the argument, since it
quantifies over runs of one policy over **one** universe and the
joiner's run is over another under a re-indexed schedule.
`joiner_decided_agree` supplies it from `decided_agree_chop`,
instantiated at the adaptive schedule; nothing about adaptivity enters,
because `Agree` and `LocalTruncate` hold at every schedule.
`joiner_run_decided_agree` is the whole of I9: pruning does not split
the ledger, even when the schedule is derived from it.

`Rebases.unique` — a rebase determines the schedule it produces — is
what says the two schedule constructions agree without unfolding
either.

### 11.3b The agreement half, and why it was bespoke

The garbage-collection arc lifted verdict *transport* and stopped.
`decided_of_truncate` and its converse compare a verdict with the same
validator's verdict; what a deployment asks is stronger — a validator
that joined from the truncation holds an **arbitrary** view of it, with
no history below the cut and no relation to anyone's full-history view,
and must still agree.

`GC/ChopDecided.lean` proved that for the core (G4), `GC/Horizon.lean`
across two horizons (G8) — both since deleted (§11.4c) — and
`Integration/Hydrozoan/ChopDecided.lean`
again for Hydrozoan. **None of it was necessary.** `Agree` compares two
views of one universe; `LocalTruncate` puts the full-history verdict
into the truncation; the two compose. `Arcs/GC.decided_agree_truncate`
and `decided_agree_horizons` are those two lines, and every rule with a
band and agreement has them.

The extension side is the same shape with `Persist` going up where
`LocalTruncate` goes down — `Arcs/SafeSkip.decided_agree_extends`, which
the fill and re-genesis both take.

**The reason it was bespoke was order of construction, not structure.**
The arcs were written before the properties, and the lift when it came
took the transport half only. The same thing can happen again, so the
rule this suggests is: an arc that consumes a property is not finished
until every theorem it states about the mechanism has been asked for
from the properties.

**The one case that does not derive.** Two *sibling* transformations —
two validators recovering from one universe with different fill messages
— give universes neither of which extends the other, and `Agree`
compares two views of **one** universe. The carrier has no join, so
there is no common point to apply it at. The model does not pose that
case: `U` is the global DAG and a mechanism produces a new global DAG,
with validators as views. Adding machinery for it needs a reason first.

### 11.3c The three predicates a liveness route needs

`Sustains` promises blocks, so everything computed from blocks travels.
`votesAt_of` and `populatedOn_of` said so for two of the three
predicates a liveness precondition is built from. The third, **synchrony**,
was transported by hand three times — `Integration/Preservation.lean`,
`Integration/Coverage.lean`, `Integration/Stack.lean` — and it travels
for exactly the same reason: it is read from rounds, authors and
references. `RebasedAbove.synchronisedOn_of` states it once.

**Non-equivocation splits, as production did.** `NoEquivOn` is the one
member of the family a mechanism can *break*: a cut cannot, since it
only removes blocks, but a fill or a re-genesis adds one and must argue
that the author it speaks for was silent there. So the derivable half is
stated over `Truncates` rather than `Sustains` —
`noEquivOn_of_truncates`, since it is the *absence* of additions that
carries it — and the fill's `honestNoEquiv_skipFill` stays what it is,
the mechanism's own content.

### 11.4 What is left

Every mechanism in this development now has both directions through the
properties, and nothing is proved by hand. What remains is of four
kinds, and only the first is large. §11.4a records a fifth that was
looked for and is not there.

- **Instances.** Seven rules had none when this was written: Barnacle's
  six, Odontoceti, Nemo, Mahi-Mahi, Optimal-Hydrozoan, Hybrid and
  FinWhale. All seven have since been instantiated. That was the gap
  testing whether the six obligations are the right six, and the answer
  is that they are: nine rules of ten meet them, three needed a repair
  to do so (§3.2, §3.12, and Hybrid's), three met the same shape and did
  not (§3.13, §3.14, §3.16), and none needed a seventh property. Black
  Marlin is the last, and the reason it has none still holds: it commits
  by round with no slot-indexed relation to state a property at.
- ~~**A carrier law for chain quality**~~ (**done**, §3.15).
  `Properties.Quorate` is the clause, as a property rather than a field,
  and the whole arc moved to `Properties/Arcs/Quality.lean`. Every
  mechanism in the development is now stated over `DagRule`; what a
  protocol supplies per mechanism is a `Truncates` or `Sustains`
  witness, which is the carrier's inability to construct a universe
  rather than a missing property.
- ~~**Two dead statements**~~ (**deleted**). `Local` had no consumer and
  no need; `Delivers`, the full-coverage view obligation, had no witness
  beyond `View.full`. Both are gone, with `AgreeAbove.symm` and
  `ViewAgreeAbove.symm`, which existed only for `Local.iff`. A property
  whose only model is the mechanism that does nothing is the vacuity
  this arc has twice been caught by (§3.4, §3.6); keeping a third would
  invite someone to prove it for a real limiter and fail.
- ~~**Constructions, not properties**~~ (**done**, §11.2e). The four
  open cells — the cut and the fill for Nemo and for FinWhale — are
  closed, and `audit-mechanisms.py` reports none open. The limit they
  recorded is real and unchanged: `DagRule.Universe` is opaque, a
  property can read a universe and nothing in the carrier can make one,
  so a rule with its own universe record writes its own cut and its own
  fill. What the closure shows is how the residue splits. The
  *data* is shared — `chopBlk` and `SkipData` are stated over a bare
  block assignment with no fault model — and what is irreducible is the
  invariant discharge, which is small: Nemo's two clauses and FinWhale's
  five. It is also sometimes false, and `copyBlock` locates where.
  Optimal-Hydrozoan's fill breaks leader exclusion because `skipFill`
  adds a self reference, not because it fills; the same clause in
  FinWhale is discharged by the fill that adds no edge.
- **One structural limit.** Two *sibling* transformations — two
  validators recovering from one universe with different fill messages —
  give universes neither of which extends the other, and `Agree`
  compares two views of one universe. The carrier has no join. The model
  does not pose the case: `U` is the global DAG and validators are
  views (§11.3b).

### 11.4a Why the additive side has no property

`Sustains` is a purely *negative* promise: above the settling round the
mechanism changed nothing. Nothing in the collection says what a
mechanism does *below* it — what it adds. Two facts are proved twice
over, once for the fill and once for re-genesis, which is the
duplication signature that produced `CommitsCandidate` and
`CommitsDirect`:

| | fill | re-genesis |
|---|---|---|
| what the added blocks supply | `skipFill_populatedOn` | `populatedOn_addGenesis` |
| that they do not break the fault model | `honestNoEquiv_skipFill` | `hB1uniq_of_addGenesis` |

**No property was added, and the reason is general.** `Sustains` can be
one because *changed nothing above `R₀`* is uniform across mechanisms.
*Added exactly these blocks* is not: what a mechanism adds **is** the
mechanism, so any statement faithful to it is that mechanism with the
quantifiers rearranged. A four-clause obligation was drafted —
everything new is `v`'s, in a window; `v` was silent there; one block per
round; `v` seated at every round — and it had exactly two models, each
discharged by unfolding a definition. It named nothing the definitions
did not already say.

**Production needed no property.** The shared half is
`populatedOn_insert_of_extends` (`Properties/Sustain.lean`): an
extension plus one singleton `PopulatedOn U' {v} r` gives the reliable
set with the author added. What is left is the singleton — the gap
block, the genesis block — which is the mechanism's own content and has
nowhere else to live.

**Non-equivocation is a real obligation, and a narrow one.**
`PreservesNoEquiv R U U' T`, the implication `NoEquivOn R U T →
NoEquivOn R U' T`, is uniform: it names no validator and no window, and
each mechanism meets it however it can — the cut because it only
removes (`noEquivOn_of_truncates`), the fill because its validator was
silent in the gap, re-genesis because its validator had no block at all.

It is also **vacuous under the base fault model**. `BlockUniverse`
carries `no_equivocation` as a *field*, for `Correct`, so every universe
a mechanism constructs discharges it at construction. The three bespoke
lemmas exist only because the hybrid model widens the honest class to
`Honest = byzantineᶜ`, which includes the crash-prone validators the
carrier's field says nothing about. So the obligation is owed by a
mechanism **to a fault model**, not to a protocol, and only when that
model trusts more validators than the carrier does.

Naming it would replace three statements with one and make
`honestNoEquiv_stack` a composition rather than a chain. That is a small
gain against a line in the obligation list, and it has not been taken.
The three lemmas stay where they are.

**Two wrong turnings, since the method is the point.** The first
proposal was the four-clause structure above, written from the two
mechanisms rather than from their consumers — which is how `Reindex`
(§3.4) and `Sustains` v1 (§3.6) went wrong, and the third time the
pattern has appeared. The second was billing what survived as *the
additive counterpart to `Sustains`*; it is not a counterpart to
anything, being vacuous wherever the fault model and the carrier agree.

### 11.4e The mechanism stops carrying its own proof

The garbage-collection arc proved verdict transport and cross-cut
agreement twice: once by structural induction over the decision relation
in `GC/ChopDecided.lean` and `GC/Horizon.lean`, and once from `Banded`
and `Agree` in `Properties/Arcs/GC.lean`. The duplicates are gone.

**Why keeping them was not the safer choice.** The argument for keeping
was that they are the comparison — that a claim of the form *re-derived
with no induction of its own* is checkable only while the induction is
there. It does not survive inspection: `Arcs.decided_chop_iff` has
literally the same type as `GC.decided_chop`, and Lean guarantees that.
Two proofs of one statement is redundancy, not a cross-check; a
cross-check would need them to prove different things that ought to
agree. What the duplicates did offer was an invitation to the next
protocol author to copy them instead of proving the properties.

**What went, and what it took.** `bootstrap_agree` was the one live
consumer, and it routes through `Arcs.decided_agree_chop` — acyclic,
since `GC/Bootstrap.lean` is a sibling of `Arcs/GC.lean` rather than
upstream of it. With that moved and the dead `decided_agree_horizons`
dropped, a closed cluster of twelve declarations became unreachable:
G3 both directions, G4, and the eight transport lemmas that existed only
to feed them. `GC/ChopDecided.lean` went from 359 lines to 153.

**What stays, and why it must.** The *construction* — `chop`,
`Slots.chop`, `View.chop`, and the facts relating their fields. A
witness that the cut stands in the `Truncates` relation has to mention
the cut, and no property can supply that. The test is sharp: after this,
no theorem of the garbage-collection mechanism mentions `Decided`.

**What this does not touch.** The protocol. `Mysticeti.lean` and
`Liveness.lean` keep every direct argument, and must: the properties are
proved *from* them, so a protocol consuming its own conformance would be
an import cycle. The shape is protocol → properties → mechanisms, and
only the last arrow lost a duplicate.

**The same cut, for Hydrozoan.** `Integration/Hydrozoan/ChopDecided.lean`
and `FillDecided.lean` carried three inductions between them — the cut
both ways and the fill forwards — and two agreement theorems composed
onto them. All five are gone. `Stack.decided_stackHZ`, the one live
consumer, now composes `decided_fillHZ_of_persist` with
`decided_chopHZ_of_localTruncate`; the two witness files follow it.
`isLeaderBlock_of_decidedHZ` went as well, being a copy of the core's
`Hydrozoan.isLeaderBlock_of_decided`.

What did **not** go is larger than in the core's case, and the
difference is worth stating. Both files keep every rule transfer:
candidacy, anchor eligibility, the three direct rules in view, the two
rung tests, each moved across the transformer block by block and
biconditionally. Those are not proof scaffolding — they *are* the claim
that the transformer is a truncation or an extension, and
`ViaProperties.truncates_chopHZ` and `extends_skipFillHZ` assemble them
into exactly that. The negative clauses are the sharp ones:
`not_certifiedInHZ_fresh` and `not_weakLinkedHZ_fresh` say a fresh
candidate is invisible from an old anchor, which is why the fill is an
extension at all. Deleting the induction removes the second proof of
the verdict claim and leaves the first proof of the structural one.

**Odontoceti gets the cut with no bespoke route in existence.**
`Arcs.truncates_chop_odontoceti` transports the core's `Truncates`
witness across the two carriers — seven fields, each already proved —
and `decided_chop_iff_odontoceti` and `decided_agree_chop_odontoceti`
follow from `LocalTruncate.of_banded` at Odontoceti's band and its
`Agree`. Odontoceti has no `ChopDecided` file and never had one. This
is the arc's second claim tested in the only way that is not
retrospective: a protocol acquired a mechanism it was never written
for, and the cost was a transport of field projections.

**Two bespoke inductions over Hydrozoan's `Decided` remain, and
nothing consumes either.** `Integration/Hydrozoan/Simulation.lean`
generalises the three transports into one induction over what a rule
reads a universe *through*; that is a different question from the
properties arc's and it is kept as a study. `OptimalChopDecided.lean`
carries the cut for Optimal-Hydrozoan, which has no band yet — item 3
of §11.5 is where its band would come from, and until it has one the
induction is the only route it has.

### 11.4b Obligation or consequence

The properties divide four ways, and the folder follows the division.
The rule is **what a protocol proves directly stays at the root**;
`Properties/Derived/` holds what none does, statement and route
together; `Properties/Optional/` holds what a protocol may show and need
not.

That is not the rule this section first stated. It said `Derived/` holds
theorems and never statements, which its own contents contradicted the
day `Persist` moved there: `Persist`, `Local` and `LocalTruncate` are
statements, and they sit in `Derived/` because nobody proves them, not
because they are theorems. The distinction the folder tracks is who owes
the proof, which is the distinction a protocol author needs.

**Obligations. Someone must prove these, per protocol or per mechanism.**
`Causal`, `Agree`, `Banded`, `CommitsCandidate`, `LeaderCommits` and
`Descends` fall on the protocol; `Sustains` falls on the mechanism. Nothing derives them.
`ViewSound` was on this list and is now a field of `DagRule`: every
protocol's view type already carried the proof (§11.4d).

**Optional. A protocol may show these and need not.**
`Properties/Optional/` holds them, and there are two.
`SkipsUnsupported` — §11.4c records why it was demoted — and
`CommitsDirect`, which a rule owes for whatever direct predicate a
mechanism counts, and which a rule with no such mechanism over it owes
not at all. Both are parameterised, which is the mark of the category:
an optional property names the thing the consumer supplies.

**Statements no protocol proves directly.** `Persist` and
`LocalTruncate` are read by mechanisms and reached by both instances
through `Banded`, so they live in `Derived/` with their routes. They
stay named properties because that is what the crash-recovery and
garbage-collection arcs consume, and because a rule with no band could
prove either on its own.

**The condition on that.** A statement may sit in `Derived/` only while
its uses are downstream — mechanisms consuming it, other derived results
building on it. It may not appear where a protocol declares what it
owes, because there it reads as an obligation and there is none.
`Persist` was in HZ9's conjunction on the argument that mechanisms read
it by name; they do, and they can reach it from `Banded`, which HZ9
states. `scripts/check-arc-holes.py` now enforces this: no name defined
in `Properties/Derived/` may appear in an arc's conformance
`Statement.lean`.

HZ9 therefore states four things — `Causal`, `Banded`, `Agree` and
`SkipsUnsupported` — where it once stated seven, and satisfies the same
set as before.

`Local` is in `Derived/` too and **no mechanism reads it**. It was kept
on the ground that garbage collection consumed it, which stopped being
true when that arc moved to `LocalTruncate`. It is a corollary of the
band and nothing else, so neither protocol states it and neither
instantiates it (§11.4d).

**Vocabulary stays at the root** whether or not a protocol proves
anything about it, because the obligations are written in it:
`RebasedAbove` and its two settings, `Rebases`, `Truncates`, `AgreeBand`,
`Extends`, `DecidedBelow`. `AgreeBand` and `Banded` are in
`Properties/Band.lean`; the file was called `Witness.lean`, which named
the satisfiability discipline rather than what it holds.

**Derived theorems. Nothing proves these per protocol.**

| Theorem | Where | From |
|---|---|---|
| `Persist`, `Persist.of_banded` | `Derived/{Persist,FromBand}.lean` | `Banded` |
| `Local`, `Local.of_banded` | `Derived/{Local,FromBand}.lean` | `Banded` |
| `decided_mono_of_banded` | `Derived/FromBand.lean` | `Banded` |
| `exists_decidedBelow` | `Derived/FromBand.lean` | `Banded` |
| `LocalTruncate`, `LocalTruncate.of_banded` | `Derived/Truncate.lean` | `Banded` |
| `DecidedBelow`'s five laws | `Derived/Bounded.lean` | the definition, and `Agree` |

**Vocabulary. Statements the obligations are written in, proving
nothing.** `DagRule`, `RebasedAbove` and its two named settings
`AgreeAbove` and `Sustains`, `Rebases`, `AgreeBand`, `Extends`, `Novel`,
`Truncates`, `ViewAgreeAbove`, `Unsupported`,
`PresentAt`, and `DecidedBelow` itself, which is a definition and not a
property anyone shows. `Extends.lean` and `Agreement.lean` hold the two
families that used to sit beside the properties now in `Derived/`.

One obligation carries a note. `LeaderCommits` and `Descends` resist derivation
from `Banded` even though a *bound* is derivable, because they must
produce a **tight** one, where the band's is every slot its rounds can
hold.

### 11.4c Why `SkipsUnsupported` is optional

It asked a protocol to skip a slot none of whose candidates a quorum
supports, using evidence at the slot's own two rounds. A rule with no
direct skip cannot do that, and nothing in this setting says a rule must
have one. Nemo has none.

The property was introduced as the residue `Sustains` leaves: a fill
adds a candidate nothing old references, which cannot be committed, and
the worry was that for some rules it could not be skipped either,
leaving the slot dead. **That worry was inherited from the vacuous
direct skip.** Under the old rule a candidate-less slot was decided
`none` for no evidence, so a fill adding a candidate took a *decided*
slot back to undecided, and something had to restore the verdict. Since
the skip counts blockers (§3.2) the slot was never decided in the first
place. It is undecided until an anchor resolves it, which is ordinary
operation rather than a stall.

**The anchor does resolve it**, for two reasons both already proved.
Every rule's anchored case splits on whether some candidate is reachable
from the anchor, and the split is total, so a fresh candidate falls on
the negative side and the slot is skipped indirectly. And it cannot fall
on the positive side, because nothing old references it while the anchor
is old: `not_certifiedIn_band_novel` for both protocols, and
`not_weakLinked_bnd_novel` for Hydrozoan, which is what protects its
minimality tie-break.

So eventual decision after a fill rests on `Descends`, stated over the
anchored rule every protocol has, rather than on a direct rule only some
have. What `SkipsUnsupported` still gives is **promptness**: the slot is
settled at once instead of when an anchor arrives, and the grade states
a deployment condition, which is why it is kept rather than deleted.

**That statement is now written**, as `decidedBelow_of_run` in
`Derived/Progress.lean`: `LeaderCommits` for the run, `Descends` for
everything under it, and nothing else. It is not a composition of
mechanisms, which is §11.3's subject and still largely open. It is a
consequence of two properties, in the same sense that `Persist` is a
consequence of `Banded`, and it names no mechanism at all. Hydrozoan
instantiates it (§4.5).

### 11.4d The review of the property layer

Every property, every consumer, and every relation compared against
every other. Six things came out, four of them checked in Lean before
being acted on. The layer went from 1,950 lines to 1,872 while gaining
a schedule relation it did not have.

**1. Three relations were one.** `AgreeAbove r`, `Sustains G R₀` and the
four block clauses of `Truncates` had the same shape, and the shape is
`RebasedAbove R U U' G R₀`: at and above `R₀` the two universes hold the
same blocks, at rounds `G` apart, same authors, and strictly above `R₀`
the same references. `AgreeAbove r` is the zero offset,
`Sustains G R₀` is the relation under the name the obligation is owed
in, and `Truncates` is it at `R₀ = G` plus `Rebases`, a new three-clause
relation saying what became of the *schedule*. Both directions of the
`Truncates` collapse were proved before anything was deleted.

Separating the two axes is what the naming should have said all along:
`RebasedAbove` is what became of the DAG, `Rebases` what became of the
schedule, and a mechanism that touches one states one.

**2. `ViewTruncates` and `ViewAgreeAbove` were the same definition**,
`rfl`-equal, differing only in the name of the bound. One is gone.

**3. Hydrozoan carried a private copy of the truncation.**
`TruncatesHZ` was `Properties.Truncates` field for field, with `author`
and `parents` for `creator` and `refs`, and `decided_iff` re-proved
`LocalTruncate.of_banded` in Hydrozoan's vocabulary. Both are gone;
`Integration/Hydrozoan/ViaProperties.lean` exhibits the cut as a witness
for the generic relation and applies the generic derivation. The copy
existed because `rule`'s projections are Hydrozoan's by `rfl` but not
syntactically, which the proofs paid for in `hlink` bridges; `toCoreSlots`
closes the gap on the schedule side.

**4. `Local` was consumed by nothing.** It was kept on the ground that
garbage collection reads it, which stopped being true when that arc moved
to `LocalTruncate`. Both protocols listed it in their conformance
statement, which made it read as an obligation. It stays in `Derived/` as
a corollary of the band and is out of both statements.

**5. `Persist`'s grade `Ok` was dead.** Every instance was
`Unconditional`, `Persist.of_banded` produced only `Unconditional`, and
`MysticetiProperties.persist` existed to re-grade an unconditional proof
so `Adaptive/Growth.lean` would take it. The parameter was held against a
rule that decides on a block's *absence* — but such a rule fails `Banded`
too, since the band admits extra blocks inside itself, so the grade could
not rescue a protocol that proves the band. Gone, and with it `Quorate`,
`Persist.mono`, `Persist.of_unconditional`, `decided_skipFill_unconditional`,
`quorate_of_quorateOverGap`, and a hypothesis from three theorems in
`Growth`. `decided_fill_of_persist` no longer asks `QuorateOverGap`.

**6. `ViewSound` is a field of `DagRule`.** Both protocols' view type
already carried `subset_ids`, so the obligation cost an instance nothing
and cost every derivation a hypothesis. `Local.of_banded` and
`LocalTruncate.of_banded` each lost one. Barnacle's `BaseRule.toDagRule`
now takes no laws at all: `viewSound` became a field of `BaseRule`,
which is what lets a rule be a carrier before it has proved anything.

**What the review did not do.** `Banded` gives a *round* ceiling — the
verdict reads nothing above `top` — and `DecidedBelow B` gives a *slot*
ceiling — no leader from `B` on matters. They are one idea on the two
axes, and `exists_decidedBelow` converts between them while losing
tightness, which is why `LeaderCommits` and `Descends` stay obligations
and why `Hydrozoan/Helpers/Commit.lean` re-tracks the schedule dependence
rung by rung. Stating the band on both axes would let the protocol emit
both bounds from the induction it already runs. It would not make
`LeaderCommits` derivable, since that is an existence claim needing
protocol liveness, but it would leave that property supplying only
"∃ L, Decided". Scoped, not attempted.

**Two names that still mislead.** `top` is the **decision round**, the
highest round a verdict consults; every protocol already defines
`decisionRound k = slotRound k + 2` and the band's `top` is its
indirect-anchor generalisation. And `DecidedBelow B` reads as a range of
slots when it means a dependence bound — *the verdict is settled by slot
`B`*.

### 11.6 The guard on the liveness precondition

*Superseded by §11.8: `LiveReachable` has been folded into
`Support.OfCoverage` and deleted. The section stands as the record of
why the guard was needed.*

`LeaderCommits R Live` says that *wherever* the protocol's own
precondition holds, a slot led by a reliable validator commits. It does
not say the precondition ever holds, and `Live` is a parameter the rule
supplies, so a rule that chose an unsatisfiable one would prove
`LeaderCommits` with nothing in it — and `decidedBelow_of_run`, chain
quality (§3.15) and Barnacle's `LiveOn` would all inherit the emptiness.
That is the vacuity of §3.4 and §3.6 on the liveness side, and it was
unguarded.

`Properties/Live.lean` is the guard. The obligation is not to prove
`Live`, which is false on a DAG where the network stalled and should be.
It is the implication

    synchronised + populated + the view caught up   ⟹   Live

`LiveReachable R rel wave Live`, with the antecedent fixed to the three
predicates §11.3c names and no free predicate to hide in.
`exists_decided_of_reachable` is the consumer test: it concludes that a
reliably-led slot commits, and mentions `Live` nowhere.

**The shape existed and was in the wrong place.**
`Barnacle.LiveRule.GoodGives` is this implication, and six rules
discharged it. Two things are gained by stating it at the properties.
It becomes available to a rule with no `LiveRule` instance — FinWhale
and Mahi-Mahi have none, so neither could write `GoodGives` at all. And
it closes the vacuity rather than moving it: `GoodGives` quantifies over
`LiveRule.Good`, itself an opaque field, so a rule could satisfy it with
a `Good` nothing satisfies.

**Eight of the nine rules with a carrier discharge it.** Six are the
`GoodGives` argument at the properties, and two were new work:

| rule | what the discharge cost |
|---|---|
| core, Odontoceti, Nemo, Hybrid, Hydrozoan, Optimal-Hydrozoan | the record built: their `Live` *is* the conjunction of the three predicates and a window bound |
| Mahi-Mahi | `MM5a` applied. Its `Live` asks that the slot's leader be **good** — that a direct commit already stands — which is close to what `LeaderCommits` concludes, so the property alone said little until this was proved |
| FinWhale | a new theorem, `spCommitBy_of_synchronisedOn`: coverage and production give the slow path at every correct-led slot, with no clock |

Mahi-Mahi is the case that shows the guard is not a formality. Its
precondition assumes the commit, so `leaderCommits` is nearly a
projection; what carries the liveness is `good_of_synchronisedOn`, and
until `LiveReachable` there was nothing forcing the two to be joined.

FinWhale's is the case where the guard produced a theorem. Its
precondition asks for `CommitsCorrectLeaders`, which the arc supplied
only from a timing model — `commits_of_reactive` from the reactive wait
clauses, `commits_of_creation` from the block-creation conditions.
`spCommitBy_of_synchronisedOn` is a third route and the one the
properties want: every correct block one round above a correct leader
references it, so all of them vote; a correct block two rounds above
references all of those; and `n + 1 = 3f + 2p` with `p ≥ 1` puts the
slow-path quorum inside `Correct`.

**The ninth is reactive Mysticeti, and it is a finding rather than a
gap.** Its `reactiveLive` cannot meet this antecedent and is not meant
to: the point of the reactive discipline is to commit *without* waiting
for the main line, so `SynchronisedOn` is false in a reactive execution
by design (`Reactive/Basic.lean`). Its precondition is guarded the other
admissible way, by a witness — `ugrowReactiveLive` and
`ugrowReactive_leaderCommits` in `LeanDagTest/Reactive.lean` exhibit a
reactive execution that satisfies it and the verdict it yields.

### 11.6b One precondition for two execution models

§11.6a leaves coverage and the reactive discipline as two incomparable
antecedents, and asks whether the rule's precondition can be stated so
that both reach it. It can, and Mysticeti is the case that settles it,
because there the *same rule* runs under both.

`coreLive` asks for coverage; `reactiveLive` asks for a reactive
execution past GST. They were two preconditions and two `LeaderCommits`
proofs for one decision relation. `MysticetiProperties.certLive` is what
both deliver, stated in the vocabulary the commit rule counts in: a
quorum, a horizon the view is caught up to, production at the slot's
round and its certificate round, and the reliable set certifying every
candidate of every reliably-led slot in the window.

| | |
|---|---|
| `leaderCommits_cert` | the one `LeaderCommits` proof, against `certLive` |
| `certLive_of_coreLive` | coverage's bridge, `certifiesAt_of_synchronisedOn` at each slot |
| `certLive_of_reactiveLive` | the reactive bridge, `ReactiveM.certifies` from `cert_or_wait` |

`leaderCommits` and `leaderCommits_reactive` keep their statements and
become the two corollaries. Nothing downstream moved.

**What the substitution actually does is relocate the work.**
`LeaderCommits` becomes shape alone — read the leader block off
production, count the certificates, wrap the verdict — and the substance
goes into the bridges, which is where the two models genuinely differ.
The vacuity guard is unaffected: `LiveReachable`'s antecedent stays
coverage, so the chain from network facts to verdict is the same length,
and the reactive route is a second bridge rather than a weaker
obligation.

**The payoff is on the mechanism side.**
`directCommit_of_certLive_sustains` carries the commit across any
`Sustains` from *either* model, because `certLive` is stated in
references and counts and `Sustains` preserves both. A coverage-shaped
precondition transports only for a model that has coverage;
`Integration/ReactiveMechanisms.lean`'s three cells are now corollaries
of the one theorem rather than a reactive-only route.

**It does not unify every rule, and the reason is structural.**
The substitution works wherever a rule's commit is a count over two
reference layers — the core, and by the same argument Odontoceti,
Hydrozoan, Optimal-Hydrozoan and Hybrid at their own wavelengths.
Mahi-Mahi is different: its commit reads a *cone* a whole wave deep, so
what its precondition needs is reachability across `w` rounds, not
certificates two layers up, and `good_of_synchronisedOn` runs on
coverage for that reason. So the general statement is per rule — "what
this rule's commit counts" — and the unification is across *execution
models of one rule*, which is the case that was costing two proofs.

### 11.6a Coverage is the wrong antecedent for a mechanism

`LiveReachable` reads coverage because coverage is the strongest fact
statable in `ids`, `block` and `refs` alone, and a property may use no
other vocabulary. That makes it the right antecedent for an obligation
and the wrong one for a reactive execution, and the question it leaves
open is whether a reactive commit survives a mechanism.

**It does, and coverage was never what the mechanism needed.** What a
mechanism reads is `CertifiesAt` — the certificates the commit rule
counts — and `MysticetiProperties.directCommit_of_sustains` carries
those across any `Sustains`, because a certificate is made of references
and `Sustains` preserves references. The reactive discipline delivers
`CertifiesAt` (`ReactiveM.certifies`, from `cert_or_wait`), which is
precisely what it is designed to deliver in place of coverage. So the
composition needs no pacing structure on the far side: no `ReactiveM` is
built for the truncation or the fill, and none is wanted.

`Integration/ReactiveMechanisms.lean` writes the three cells —
`directCommit_chop_reactive`, `directCommit_skipFill_reactive`,
`directCommit_addGenesis_reactive` — each the same two theorems composed
at a different `Sustains` witness.

**Why the weaker interface cannot be the property.** `CertifiesAt`
counts in the *rule's* vocabulary, and `DagRule` has none: a carrier
knows `ids`, `block` and `refs`, and every rule's certificate is a
different threshold over them — the core's `quorumCard`, Nemo's
majority, FinWhale's `spQuorum`, Mahi-Mahi's cone. There is therefore no
rule-independent weakening of coverage that a reactive execution
satisfies, and the split is structural rather than an omission:
coverage is the antecedent a *property* can state, `CertifiesAt` is the
interface a *mechanism* consumes, and a rule supplies whichever of them
its execution model gives.

`audit-conformance.py` scores `LiveReachable` per *carrier*, so reactive
Mysticeti reads `yes` on the strength of the core's discharge — the two
share `mysticetiRule`. A second precondition on a shared carrier is not
measured, which the audit's legend says.

**One side effect.** `Properties.PopulatedOn` and the protocols'
`PopulatedOn` had the same two conjuncts in opposite orders, which cost
a bridge lemma per protocol. Both are now `PopulatedFrom` at the rule's
block assignment, as `SynchronisedOn` already was, so
`MysticetiProperties.populatedOn_ofCore` and its converse are the
identity.

### 11.7 Support: what a rule's commit counts

§11.6b unified two execution models of one rule by stating its
precondition in what its commit counts. §11.7 makes that shape the
generic one. Safety is generic because `Banded` names the one thing
every decision relation reads — a bounded window of references.
Liveness was not, because nothing named the one thing every *commit*
counts. `Properties/Support.lean` names it.

```lean
structure Support (R : DagRule …) where
  wave      : ℕ
  Certifies : R.Universe → BlockId → BlockId → Prop
```

**A parameter, not a field.** `Live` and `Elig` are parameters pinned by
the properties that consume them, and `Support` follows them, for a
reason fields cannot meet: a rule may have more than one — a fast-path
shape and a slow-path shape — and each earns its own bound. What stops a
parameter from being chosen vacuously is a pair of laws that squeeze it
from both sides.

| law | what it says | which way it pins |
|---|---|---|
| `Local` | across any `RebasedAbove`, a certifier whose window sits above the settling round certifies the same candidates | `Banded` for the support relation |
| `OfCoverage rel` | on a populated window with coverage toward a reliable candidate, every reliable block at the top certifies it | lower bound: a `Certifies` nothing satisfies is inadmissible |
| `Commits rel` | a quorum certifying every candidate of a slot commits it, on a caught-up view, within a bound one above | upper bound: a `Certifies` everything satisfies is inadmissible |

**`CoversToward`, not `SynchronisedOn`.** Full coverage says every
reliable block references every reliable block one round below. A
reactive execution does not have it and is not meant to. What it has is
coverage *toward the candidate* — every reliable block in the window
references every reliable block below it that reaches the candidate —
because that is what its wait clauses guarantee. `CoversToward` is that
restriction, full coverage implies it in one line, and it is the weakest
antecedent under which every rule here certifies. It is the predicate
§11.6a said could not be stated without a wavelength; with `wave` in the
structure, it can.

**What is now proved once.**

| theorem | what it replaces |
|---|---|
| `Support.leaderCommits` | `LeaderCommits` at `Support.live`, from Law 3 — no per-rule precondition |
| `Support.liveReachable` | the eight per-rule `liveReachable`s, from Law 2 |
| `Support.exists_decided_of_coverage` | a reliably-led slot commits on any covered, populated DAG |
| `Support.certifiesAt_of_rebased` | certification survives every mechanism, from Law 1 |
| `Support.exists_decided_of_sustains` | **the liveness column**: a commit survives any `Sustains`, for every rule with the laws, with no per-mechanism argument |

**What each rule supplies.** The one-round rules — Odontoceti, Nemo,
Hybrid — share `voteSupport`: wavelength one, certifying is referencing.
Its `Local` and `OfCoverage` are facts about references alone and are
proved once in `Properties/`; each rule owes `Commits`, one proof, which
is its old `directCommit_of_leader_mem` with the coverage hypothesis
replaced by the votes. The core supplies `coreSupport` — wavelength
two, certification the rule's own — and its three laws are
`certifies_of_sustains`, `certifies_of_synchronisedOn` cut down to the
two layers it reads, and `leaderCommits_cert` unpacked.

**Reactive rules enter the same socket.**
`coreSupport_live_of_reactiveLive` takes a reactive execution past GST
to `Support.live` directly — `cert_or_wait` delivers the certificates,
the trunk's production delivers the blocks — and from there every
theorem above applies unchanged, including liveness across every
mechanism. No pacing structure is transported, and the mechanism never
learns which execution model produced the certificates. That is what
"reactive rules are not a special case" means structurally: they differ
from coverage in which bridge they take to `Support.live`, and in
nothing after it.

**All nine rules with a carrier now have a `Support`**, and the
conformance table reads `supp yes` across the board.

| rule | support | Law 1 | Law 2 | Law 3 |
|---|---|---|---|---|
| core Mysticeti | `coreSupport`, wave 2 | `certifies_of_sustains` | two-layer coverage | `directCommit_of_certifiesAt` |
| reactive Mysticeti | the core's, by bridge | — | — | — |
| Odontoceti, Nemo, Hybrid | `voteSupport`, wave 1 | generic | generic | one proof each |
| Hydrozoan | `hzSupport`, wave 2 (slow path) | parents and grandparents kept | `isCertificate_of_synchronised` cut down | `slowCommit_of_certifiesAt` |
| Optimal-Hydrozoan | `optSupport`, Hydrozoan's at `U.val` | Hydrozoan's | Hydrozoan's | Hydrozoan's slow commit in `DecidedOpt` |
| FinWhale | `fwSupport`, wave 2 (slow path) | parents and grandparents kept | `spCommitBy_of_synchronisedOn` cut down | the SP-commit on the view, through the pass |
| Mahi-Mahi | `mmSupport w`, wave `w − 1` | `certifies_band` at the band a `RebasedAbove` is | see below | the cone certificates, in view |

**Mahi-Mahi was the test of `CoversToward`, and it passed without
change to the predicate.** Its certifier sits `w − 1` rounds up and
certifies through its cone, so what it needs of the candidate is
reachability from every block at the voting round — Byzantine blocks
included, since the certificate counts the certifier's parents whatever
their author. `CoversToward` gives only that *reliable* blocks reference
what reaches the candidate. The gap is closed the way the rule's own
liveness closes it: coverage toward the candidate at the first layer
puts every reliable block one round up on the candidate, and quorum
intersection carries every block after that (`reaches_of_votes`, which
is `reaches_of_synchronisedOn` with its coverage cut to the one layer it
reads). So the antecedent did not have to be strengthened; the rule had
the lemma that makes one layer of coverage enough.

**The two-path rules have both paths.** Hydrozoan's, Optimal's and
FinWhale's named supports are their slow-path certificates, and each
also discharges `Commits` for `voteSupport` — one round up, certifying
is referencing, Laws 1 and 2 generic — which is its fast path. What the
fast path costs is the fault model: `n − p` votes exist only when at
most `p` replicas are faulty, so each fast `Commits` is stated under a
tighter `Reliability` (`hzFastReliability`, `optFastReliability`,
`fwFastReliability`) that takes that bound as a hypothesis. This is the
case the parameter form was chosen for: two supports of one rule, each
with its own laws and its own bound, and the generic theorems apply to
both. Optimal's fast model takes strict minority as a further
hypothesis, since `2·pOpt = n` at the corner `f = 0`, `c = 1`, `k` odd
and the committee equation does not exclude it.

**What a rule owes, on the evidence of nine.** A one-round rule owes one
proof. A two-layer rule owes three, each an existing lemma with its
antecedent cut to what it reads. A cone rule owes three, one of them
new. And every rule then has `LeaderCommits`, `LiveReachable`, liveness
from coverage, and liveness across every `Sustains` from the generic
theorems, with no further argument.

### 11.8 The set, consolidated

§11.6 added `LiveReachable` as a guard on `LeaderCommits`, and §11.7
added `Support`. Once every rule had a support, both of the earlier two
were consequences of it, and the obligations were counted twice. This
section is the consolidation.

**What a protocol owes: five properties and a support.**

| | |
|---|---|
| `Causal` | its universes are block DAGs |
| `Banded` | its verdicts read a bounded window of references |
| `Agree` | two views of one universe do not disagree |
| `CommitsCandidate` | a commit names the slot's candidate |
| `Indirect` | the anchored rule, at a bound |
| `Support` with `Local`, `OfCoverage`, `Commits` | what its commit counts, and that coverage certifies and certificates commit |

Everything else is derived, and lives in `Derived/`:

| derived | from | where |
|---|---|---|
| `LeaderCommits` | `Support.Commits` | `Derived/LeaderCommits.lean` |
| `Persist`, `LocalTruncate` | `Banded` | `Derived/FromBand.lean`, `Derived/Truncate.lean` |
| `Descends` | `Indirect` | `Derived/Descent.lean` |

`LiveReachable` is deleted. It guarded `LeaderCommits` against an
unsatisfiable precondition, and `Support.OfCoverage` is that guard
stated once at the support rather than once per rule; its eight
per-rule discharges had no consumer. The three mechanism-side
consequences of a support — liveness on a covered DAG, certification
across every `RebasedAbove`, a commit across every `Sustains` — moved
to `Arcs/Liveness.lean`, beside the safety arcs they mirror.

**Which direct proofs went.** A rule keeps a direct `LeaderCommits`
proof only where it says strictly more than the support does.
Hydrozoan's and Optimal-Hydrozoan's preconditions already put the quorum
inside the correct set, so their `leaderCommits` are now the bridge to
`Support.live` composed with the derived theorem, and the direct proofs
are deleted. The core's `coreSupport_commits` is now a corollary of
`leaderCommits_cert`, the other way round, because `certLive` asks less
— any quorum by count — and the more general statement is the one to
keep.

**Which stay, and why.** The core's, Odontoceti's, Nemo's, Hybrid's and
Mahi-Mahi's `leaderCommits` are stated for any quorum by count, not one
inside the correct set, and that generality is consumed —
`Quantitative.lean`, `Quality/Capstone.lean`, the adaptive schedule and
Barnacle's `GoodGives` all supply such a quorum. `Support.Commits` asks
for `IsQuorum`, which puts the quorum inside the correct set because
Mahi-Mahi's certificate needs the *candidate's* author correct and the
uniform law cannot tell the rules apart. So those five direct proofs
say more than the derivation gives, and stay. FinWhale's stays for a
different reason: its precondition asks only that `spQuorum`
certifiers exist, where the support asks that every quorum member
certifies, so the direct theorem is the weaker-hypothesis one.

**Barnacle reads the support directly.** Its `LiveRule` layer restated
`OfCoverage` and `Commits` per rule as `GoodGives`, and assembled the
descent laws from `LeaderCommits`, `Indirect` and `GoodGives` in
`descent_of_properties`. Both are gone. `Barnacle.GoodOf` is a good DAG
in the properties' terms — some quorum of the fault model has covered
it and populated it — and `descent_of_support` builds `Descent` from a
support's `OfCoverage` and `Commits`, `Indirect`, a wave no longer than
the rule's, and the one-line fact that the rule's `Good` is `GoodOf` at
its quorum. A4 is `exists_decided_of_coverage` at the quorum a good DAG
names; no `LeaderCommits` and no precondition of the rule's own appear.
Every rule's `Good` was already that conjunction, so the six bridges
are the identity up to how each spells its quorum — Hydrozoan's `q`
against `n − (f + c)`, Nemo's majority against everyone's complement —
and the six `goodGives` proofs are deleted. `LiveRule.Good` stays: it is
how the heads argument names a good stretch of rounds, and a mechanism
may keep its own vocabulary as long as it reaches the protocol through
the properties.

### 11.5 Next steps, in order

1. **~~`Compose.lean`~~** (**done**, §11.3). The three composition
   lemmas, the core's missing fill witness, and `Integration/Stack.lean`
   given a theorem it did not have.
2. **~~Audit the rules for absolute round reads~~** (**done**, §3.4c).
   Six of the eight rules can carry an offset band as they stand;
   Mahi-Mahi can under `2 ≤ w`, and FinWhale could not until it had a
   `Slots` layer — which it now has, band included (§3.13).
   `scripts/audit-rounds.py` keeps the result.
3. **~~`Banded` for a third rule~~** (**done**, §3.12). Odontoceti has
   all six, and the attempt found a defect in its skip rule first — the
   core's own, repaired with the core's fix. Nemo, Hybrid and FinWhale
   followed; FinWhale is the one with no induction to run, and §3.13
   records what took its place. Optimal-Hydrozoan closed it (§3.14), so
   every rule with a carrier now has a band.
4. **~~A commit names the slot's candidate~~** (**done**, §3.9).
   `CommitsCandidate`, which seven protocols had proved separately.
5. **~~Re-genesis as an `Extends`~~** (**done**, §3.10). Two witnesses
   and no new property — the first DAG-transforming mechanism added to
   this development without one.
6. **~~A view-level `Sustains`~~** (**done**, §3.11).
   `Properties/Deliver.lean`, with the witness in `DoS/Delivers.lean`.
   The witness forced the weakening §3.11 predicted: the strong form has
   no model but `View.full`, and the reliable-set form is what a rate
   limiter can promise and does.
7. **~~The joiner~~** (**done**, §11.3). I9's verdict half, from
   cross-cut agreement instantiated at the adaptive schedule. This was
   the last mechanism interaction proved by hand.
8. **A validity law on `DagRule`**, which is what lifting chain quality
   to the carrier needs and the only remaining call for a new carrier
   field.
9. **Delete `Local`, and decide about `Delivers`** (§11.4).
10. **~~Barnacle, through `BaseRule.toDagRule`~~** (**done**, §11.2).
    Four new carriers — Odontoceti, Nemo, Optimal-Hydrozoan and
    Orcaella — each with `Agree` and `CommitsCandidate` from `Laws`.
    What it did not give is what item 3 is now for: `Causal` and
    `Banded` are per-rule, and `Banded` is the one that matters.
