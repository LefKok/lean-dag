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
| Garbage collection (`chop`) | `GC/` | Mysticeti, Hydrozoan, Optimal | Hydrozoan (safety); core (liveness) |
| Crash recovery (`skipFill`, `liftView`) | `SafeSkip/` | Mysticeti, Hydrozoan | Hydrozoan, core |
| Re-genesis | `Integration/ReGenesis.lean` | none | **none** |
| Adaptive leader schedule (Hammerhead) | `Adaptive/` | Mysticeti, Odontoceti | core, reactive core |
| Adaptive leader count (Barnacle) | `Barnacle/` | six | **none** |
| Reactive schedule | `Reactive/` | Mysticeti, Odontoceti | as a second `Live` for the core |
| Chain quality | `Quality/` | Mysticeti | **none** |

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

Three consequences, none of them planned. `SafeSkip.decided_fill` (SS5)
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
arc's two transport theorems, which `GC/ChopDecided.lean` proves by
structural induction over the decision relation, come back out of
`LocalTruncate.of_banded` in one application. The cost was threading
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
| Odontoceti | `slotRound k`, `+1` | reachable |
| Nemo | `slotRound k`, `+1` | reachable |
| Hybrid | `slotRound k`, `+1` | reachable |
| Optimal-Hydrozoan | `slotRound k`, `+1`, `+2` | reachable |
| Mahi-Mahi | `slotRound k + w - 1`, `r + w - 2` | reachable, under `2 ≤ w` |
| FinWhale | `leader (round b - 2)` | not as the rule stands |

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

**FinWhale indexes its leader by an absolute round**, in
`ExposesEquivocation`: `D.leader ((D.block b).round - 2)`. The
subtraction is the smaller half. `Dag.leader : ℕ → Validator` is indexed
by round rather than by slot, and FinWhale's model has no `Slots`, so
the band's slot-correspondence hypothesis has nothing to attach to.
FinWhale needs the schedule layer before it can have a band, and that is
a carrier gap rather than an offset one.

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

**The obligation has no witness, and that is the next step.**
`DoS/Novelty.lean` bounds the *size* of a rate-limited view — that is
what the novelty budget is for — and proves nothing about its coverage.
Recording that plainly matters, because the first `Sustains` had
witnesses for both mechanisms and served no theorem (§3.6); this is the
opposite failure and the same discipline catches it. `Delivers` is
stated because `decided_of_delivers` consumes it, not because anything
satisfies it.

**And a witness may show it wants weakening.** `Delivers` asks for
coverage of everything the universe holds. A limiter that permanently
drops Byzantine spam does not satisfy that, and should not have to: a
verdict is reached because a quorum of *correct* blocks suffices, not
because every block arrives. The weaker obligation naming only the
correct blocks is the likely repair, and stating it needs a consumer
that asks for it.

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
- `Descends R S c` — `c` consecutive slots committed within `b + c`
  decide everything below `b` within `b + c`. The indirect rule's
  descent; `c` and the round-structure hypothesis it needs are the
  protocol's.

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
  Derived/Persist.lean  Derived/Local.lean   the two statements
  Derived/Truncate.lean   LocalTruncate, and its route from the band
  Derived/FromBand.lean   the routes, and view monotonicity and the bound
  Derived/Bounded.lean    the laws of DecidedBelow
  Derived/Progress.lean   a committed run decides everything below it
  Optional/Skip.lean      SkipsUnsupported: promptness, not liveness
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
  `GC/ChopDecided.lean` proves by induction and the arc re-derives in
  one application.
- **G3** Discharge them for Hydrozoan (**done**) — HZ9 states
  `Causal`, `Banded`, `Agree`, `Persist` and `SkipsUnsupported` at grade
  `qFast ≤ |T|` (§3.7). Persistence is unconditional, as §3.2 predicts
  for a rule whose skip counts blames at the slot. `Local` and
  `LocalTruncate` are not stated: both are the band applied (§11.4d). Two consumer tests passed with no induction
  of their own, both in `Integration/Hydrozoan/ViaProperties.lean`:
  `decided_fillHZ`, a six-constructor induction in `FillDecided.lean`,
  and `decided_chopHZ`, an induction in `Truncation.lean`. **The
  protocol owes one induction**, the band in
  `Hydrozoan/Helpers/Banded.lean`, and no more, whatever mechanisms
  follow. It began as three, one each for persistence, locality and
  truncation.
- **G4** Discharge them for the core (**`Persist` done**, and
  *unconditional* once the second instance turned up a defect in the
  core's skip rule — §3.2 — with `SafeSkip.decided_fill` re-derived as
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

### 11.1 Against part 1: the properties exist

Twelve, in `LeanDag/Properties/`, in the two directions §3.6 argues
for. The protocol proves the safety side and one graded liveness
residue; the mechanism owes one liveness property. It was fourteen until
§11.4d compared them.

| Direction | Property | Content |
|---|---|---|
| protocol, safety | `Causal` | universes are block DAGs |
| | `Banded` | a verdict is carried by a range of rounds, and `Persist`, `Local` and view monotonicity are its corollaries |
| | `Persist` | a verdict survives extension of the DAG |
| | `Local` | a verdict at round ≥ r reads the DAG only above r |
| | `LocalTruncate` | a verdict survives restriction with renumbering, both ways; a corollary of the band's offsets |
| | `Agree` | two views decide alike |
| | `CommitsCandidate` | a commit names a block the DAG holds, at the slot's round, by the slot's leader |
| | `DecidedBelow` | a verdict below a slot bound, surviving reassignment above it; a definition, so its laws are theorems |
| protocol, optional | `SkipsUnsupported R Ok` | an unsupported slot is skipped without waiting for an anchor, at grade `Ok` |
| | `LeaderCommits R Live`, `Descends R S c` | a reliable leader commits; a committed run decides everything below |
| mechanism, liveness | `Sustains R U U' G R₀` | above the settling round the transformed DAG holds the same blocks |

Two were stated wrongly first and corrected once a witness was
demanded (the re-indexing property, §3.4; `Sustains` v1, §3.6). Three
more were stated twice over and found to be one relation (§11.4d). Chain
quality has no property (§5).

### 11.2 Against part 2: two protocols, three mechanisms

| | Hydrozoan | core Mysticeti | reactive Mysticeti | Odontoceti, Nemo, Mahi-Mahi, Hybrid, Optimal-Hydrozoan, FinWhale |
|---|---|---|---|---|
| `Causal` | ✓ | ✓ | inherited | — |
| `Persist` | ✓, from `Banded`, unconditional | ✓, from `Banded`, unconditional | inherited | — |
| `Banded` | ✓ | ✓ | inherited | — |
| `Local` | ✓, from `Banded` | ✓, from `Banded` | inherited | — |
| `LocalTruncate` | ✓, from `Banded` | ✓, from `Banded` | inherited | — |
| `ViewSound` | a law of `DagRule` | a law of `DagRule` | — | — |
| `SkipsUnsupported` | ✓ at `qFast ≤ |T|` | ✓ at a correct quorum | — | — |
| `Agree` | ✓ | ✓ | inherited | — |
| `CommitsCandidate` | ✓ | ✓ | inherited | — |
| `LeaderCommits`, `Descends` | ✓ | ✓ | ✓, a second `Live` | — |
| `Sustains` witnesses | chop, fill | chop, fill | — | — |

The consumer tests passed. Each is a former bespoke induction
re-derived with none: `decided_fillHZ`, `decided_chopHZ`,
`SafeSkip.decided_fill`, SS3 as a verdict (`decided_none_fresh`),
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
- **Six protocols have no instance of any property.** Whether
  `Descends` and `Live` are generic or Mysticeti's shape with the name
  removed is unknown until the Odontoceti mirror is collapsed.
- **"Safe and live" here means the mechanism's own theorems**, at any
  rule with the properties. Ledger validity and chain quality are not
  among the properties, and the liveness preconditions — `PlacesRuns`,
  the staged `Live` — are hypotheses the deployment meets, not things
  the properties discharge.

### 11.3 Against part 3: the DAG axis composes

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

**What is still bespoke.** The schedule axis composes as arithmetic but
has no consumer yet, and adaptive leaders under garbage collection (I5)
is still proved by hand. A view-level mechanism — rate limiting, the
joiner — has no transport obligation at all, since `Sustains` is about
universes; §11.5 records it.

### 11.3b The agreement half, and why it was bespoke

The garbage-collection arc lifted verdict *transport* and stopped.
`decided_of_truncate` and its converse compare a verdict with the same
validator's verdict; what a deployment asks is stronger — a validator
that joined from the truncation holds an **arbitrary** view of it, with
no history below the cut and no relation to anyone's full-history view,
and must still agree.

`GC/ChopDecided.lean` proved that for the core (G4), `GC/Horizon.lean`
across two horizons (G8), and `Integration/Hydrozoan/ChopDecided.lean`
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

### 11.4 Not covered at all

- **Composition**, beyond the one theorem above.
- **Chain quality** (§5, G6): no property, nothing built.
- **Barnacle**: six bespoke instances of its own interface, and no
  connection to the properties beyond `BaseRule.toDagRule`. The shared
  `Agree` is the natural first bridge and has not been made.
- **DoS and rate limiting** (`DoS/`, `Novelty.lean`): declared
  rule-independent in §1 and untouched; whether that survives contact
  with `Sustains` — the novelty budget removes blocks — has not been
  asked.
- **Re-genesis**: §1 says it should be an `Extends` and would then
  inherit `Persist` and `Sustains`; nothing has been proved.

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
`Properties/Optional/` holds them. `SkipsUnsupported` is the only one
so far, and §11.4c records why it was demoted.

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
now takes its `Laws`, which carry `view_subset`.

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

### 11.5 Next steps, in order

1. **~~`Compose.lean`~~** (**done**, §11.3). The three composition
   lemmas, the core's missing fill witness, and `Integration/Stack.lean`
   given a theorem it did not have.
2. **~~Audit the rules for absolute round reads~~** (**done**, §3.4c).
   Six of the eight rules can carry an offset band as they stand;
   Mahi-Mahi can under `2 ≤ w`, and FinWhale cannot until it has a
   `Slots` layer. `scripts/audit-rounds.py` keeps the result.
3. **Collapse the Odontoceti mirrors** (`Adaptive/`, `Reactive/`) onto
   instances. `Live` and `Descends` now have two instances each and
   survived both, so the shape is no longer in doubt.
4. **~~A commit names the slot's candidate~~** (**done**, §3.9).
   `CommitsCandidate`, which seven protocols had proved separately.
5. **~~Re-genesis as an `Extends`~~** (**done**, §3.10). Two witnesses
   and no new property — the first DAG-transforming mechanism added to
   this development without one.
6. **~~A view-level `Sustains`~~** (**stated**, §3.11).
   `Properties/Deliver.lean`. The protocol side is derived; the
   obligation falls on the mechanism, and **no mechanism here exhibits
   it yet** — `DoS/Novelty.lean` bounds the size of a rate-limited view
   and says nothing about its coverage. The next step is a witness, and
   it may show the obligation wants weakening (§3.11).
7. **Chain quality** from fairness and self-reference (§5), on item 4.
8. **Barnacle**, starting from `Agree`.
