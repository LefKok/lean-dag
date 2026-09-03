# Target properties: mechanisms that apply to any conforming protocol

A design record for an arc not yet built. The aim is to state a small
number of properties of a DAG consensus rule such that **a protocol
proving them inherits the mechanisms** — garbage collection, crash
recovery, adaptive leader counts, adaptive leader schedules, reactive
scheduling, chain quality — instead of each mechanism being redeveloped
against each rule.

This supersedes §2 and §3 of `transformer-interface.md`, which posed the
same question in a narrower and, in one respect, wrong way. That
document's §1 remains the record of what is built.

Nothing here is proved. Every claim below is a conjecture until
instantiated, and the sections say which checks have been made.

---

## 1. The shape of the problem

Mechanisms in this development are currently proved against protocols
one pair at a time. Seven mechanisms need something from a commit rule,
and seven rules carry a decision relation, so there are **49 pairs**.
About fifteen exist:

| Mechanism | Where | Rules covered |
|---|---|---|
| Garbage collection (`chop`) | `GC/` | Mysticeti, Hydrozoan, Optimal |
| Crash recovery (`skipFill`, `liftView`) | `SafeSkip/` | Mysticeti, Hydrozoan |
| Re-genesis | `Integration/ReGenesis.lean` | none |
| Adaptive leader schedule (Hammerhead) | `Adaptive/` | Mysticeti, Odontoceti |
| Adaptive leader count (Barnacle) | `Barnacle/` | six |
| Reactive schedule | `Reactive/` | Mysticeti, Odontoceti |
| Chain quality | `Quality/` | Mysticeti |

The distribution is the argument. **Barnacle covers six rules and every
other mechanism covers one or two, and Barnacle is the only one with a
stated interface** — `BaseRule`, `Laws`, `LiveRule`, `Descent`, which
five protocols instantiate. `Adaptive` and `Reactive` each carry two
hand-written per-protocol copies instead. Barnacle is the existence
proof for this arc, and the others are the work.

Two mechanisms are rule-independent as far as this survey goes and are
not in scope: the denial-of-service arc (`DoS/`, including
`Novelty.lean`, the novelty budget that rate-limits block production)
and the pacing and delivery layers.

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
predicts which protocols get the unconditional form — Hydrozoan,
Optimal and Mahi-Mahi, whose skips are slot-level counts — and which
need the condition — Mysticeti, Odontoceti, Hybrid and Adaptive, whose
skips quantify over candidates. Nemo has no direct skip and nothing to
break.

**Two of those predictions are now theorems.** Hydrozoan proves
`Persist.Unconditional` (HZ9). The core proves `Persist` at grade
`Quorate` (`MysticetiProperties.persist`): at every slot the extension
gives a new candidate, the view already holds a quorum at the voting
round — and every one of those blocks blames the newcomer, since an old
block references only old blocks. The condition is consumed in exactly
one of the four cases, `directSkip`, for exactly the candidates the
extension introduced. `SafeSkip.QuorateOverGap` implies it for the fill
(`Arcs/SafeSkip.quorate_of_quorateOverGap`), and `SafeSkip.decided_fill`
— a four-constructor induction — is re-derived from `persist` with none
of its own (`decided_fill_of_persist`). The other five predictions
remain read off the survey.

**And the second instance found a defect in the property.** `Persist`'s
side condition was `Ok : Slots → Universe → Universe → Prop`, and the
core's actual condition, `QuorateOverGap`, is a condition on the
**view** — a quorum of voting-round blocks *held*. The grade was not
unproved for the core; it was unstatable. `Ok` now takes the source view.
Hydrozoan's `Unconditional` ignores it and was unaffected. This is the
third error the arc has caught, after the vacuous `Shifted` and the
unfeedable `Sustains`, and the first caught by inspection rather than by
a failed check — which is what a second instance is for.

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

### 3.5 Composition

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

**Set beside `Persist`, the grading inverts, from one root cause:**

| | safety (`Persist`) | liveness (`SkipsUnsupported`) |
|---|---|---|
| core — per-candidate skip | conditional, `Quorate` | **correct quorum suffices** |
| Hydrozoan — slot-level `qFast` count | **unconditional** | `qFast ≤ |T|`; a correct quorum does not |

A rule that skips per candidate has fragile *vacuous* skips — a new
candidate needs a quorum already in view to blame it — but any
*specific* unsupported candidate is trivially blamed. A rule that
counts blames at the slot has skips that survive any extension, and a
bar to skip at all that a correct quorum does not reach. One mechanism,
opposite grades on the two properties; four theorems of thirty lines.

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
- `Bounded` — the protocol supplies a bounded family `DecidedWithin S B`
  alongside `Decided`, embedding in it, deciding only slots under `B`,
  monotone in `B`. The bound cannot be derived from `Decided`: an
  indirect verdict's anchors are hidden inside a proof of a `Prop`, so
  `BoundedRule` extends `DagRule` with the family as a field.
- `SchedLocal` — a verdict within `B` reads the schedule's leaders only
  below `B`. The twin of `Local` on the other axis: `Local` bounds what
  a verdict reads of the DAG from below, `SchedLocal` bounds what it
  reads of the schedule from above.

Liveness, provided by the protocol for the mechanism's existence
theorem:

- `LeaderCommits R Live` — under the protocol's precondition `Live`, a
  slot led by a member of `T` commits within bound one above it. `Live`
  is a **parameter**, not a field, because the same rule under two
  execution models has two preconditions and one relation (§4.3).
  `Live S V T lo K` is indexed by the schedule and by a slot window
  `[lo, K)`.
- `Descends R S c` — `c` consecutive slots committed within `b + c`
  decide everything below `b` within `b + c`. The indirect rule's
  descent; `c` and the round-structure hypothesis it needs are the
  protocol's.

`Adaptive/{Policy,Run,Liveness}.lean` are now stated over `BoundedRule`
and these five, and name no protocol. `Adaptive.run_agree` uses the
three safety properties and depends on `propext` and `Quot.sound`
only; `Adaptive.run_exists` uses all five.

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

- **Core Mysticeti** (`MysticetiProperties.lean`): `mysticetiBounded`,
  with `DecidedWithin` moved there from `Adaptive/Basic.lean` — it is
  the protocol's relation. `agree`, `bounded`, `schedLocal` (the
  congruence proved for any two schedules with one round structure, by
  destructuring both), `leaderCommits` under `coreLive`, `descends`
  under `SpansEligible`.
- **Reactive Mysticeti** (`Reactive/MysticetiProperties.lean`): the
  same `mysticetiBounded`, so the three safety properties are
  inherited, and `leaderCommits_reactive` under `reactiveLive`, from
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
  Local.lean  Persist.lean  Truncate.lean  Sustain.lean  Skip.lean
  Agree.lean  Bounded.lean  Commit.lean        the schedule family (§4)
  Arcs/GC.lean          garbage collection, given LocalTruncate
  Arcs/SafeSkip.lean    crash recovery, given Persist
  Arcs/Quality.lean     chain quality, given fairness and self-reference  (planned)
  Compose.lean          transport composes                               (planned)

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
  replaced the re-indexing property with a combined one.
- **G2** Prove garbage collection and crash recovery once from them,
  and `Compose`. **Crash recovery done**
  (`Properties/Arcs/SafeSkip.lean`): the fill is an extension, so any
  protocol with `Persist` inherits it. Ordered before garbage
  collection deliberately, since persistence needs no `Reindex` and so
  banks one mechanism before the uncertain part is attempted.
  **Garbage collection done as far as the properties reach**
  (`Properties/Arcs/GC.lean`): `decided_truncate` composes `Local` and
  `Reindex` in three lines, and takes the restricted-not-yet-renumbered
  universe as a parameter, which §3.4 explains.
- **G3** Discharge them for Hydrozoan (**done**) — HZ9 proves all
  four: `Causal`, `Persist.Unconditional`, `Local` and `Reindex`.
  Persistence
  (`Hydrozoan/Properties/`) proves the *unconditional* grade, as §3.2
  predicts for a rule whose skip counts blames at the slot. The test
  passed: `Integration/Hydrozoan/ViaProperties.lean` re-derives
  `decided_fillHZ` — a six-constructor induction in `FillDecided.lean`
  — from HZ9 **with no induction of its own**, the fill being an
  extension by two of the arc's own simp lemmas. `Local` and `Reindex`
  are each their own induction over the six constructors, in
  `Hydrozoan/Helpers/{Locality,Truncation}.lean`, and `LocalTruncate`
  yields `decided_chopHZ` with no induction of its own
  (`ViaProperties.lean`). HZ9 also carries `SkipsUnsupported` at grade
  `qFast ≤ |T|` (§3.7), which is no induction at all. The protocol owes
  three inductions in total — persistence, locality, truncation — and no
  more, whatever mechanisms follow.
- **G4** Discharge them for the core (**`Persist` done**, at grade
  `Quorate`, with `SafeSkip.decided_fill` re-derived as the consumer
  test). The second instance reshaped `Persist.Ok` before any proof was
  attempted (§3.2). **`SkipsUnsupported` done** at grade
  `quorumCard ≤ |T|`, with SS3 re-derived as its consumer (§3.7).
  `Local` and `LocalTruncate` for the core remain.
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
