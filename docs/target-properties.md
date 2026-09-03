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
| Crash recovery (`skipFill`, `liftView`, `Jump.denote`) | `SafeSkip/` | Mysticeti, Hydrozoan |
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

---

## 2. Three families, needing three different things

The mechanisms do not all want the same thing of a rule, and treating
them as one problem was the earlier error.

**Transformer mechanisms** change the DAG under a replica: garbage
collection, crash recovery, re-genesis, `denote`. A verdict reached
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
break. The prediction is read off the survey and is not yet checked.

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

### 3.4 Re-indexing

A truncation does not only restrict; it rebases rounds to start at the
cut. Locality covers the restriction, and the rebasing is a schedule
shift. Every piece of arithmetic in `Integration/Hydrozoan/ChopDecided.lean`
lives in the shift, and it needs its own property or the generic
theorem will not close.

**This is the least certain part of the proposal.** Locality and
persistence are statements about consensus; the shift is arithmetic
threaded through each predicate, and whether it generalises is unknown.
If it does not, crash recovery goes fully generic and garbage
collection stays partly bespoke.

### 3.5 Composition

Transport should be a **relation that composes**: compose the slot
correspondences, take the union of the novel sets. Then a stack of
mechanisms follows from its parts, which is what
`Integration/Hydrozoan/Stack.lean` currently proves by hand, and any
future transformer stacks with the existing ones without further work.

---

## 4. Properties for the schedule mechanisms

`Barnacle.BaseRule` and its `Laws` are the working interface: any two
verdicts agree, a direct commit yields a verdict, candidates are
identified. `LiveRule` and `Descent` add the liveness side. Six rules
instantiate it.

The work here is not to design an interface but to bring two
mechanisms to the one that exists:

- **Hammerhead / `Adaptive`.** Its bounded relation `DecidedWithin`
  exists in two copies differing only in the indirect test, of which
  `Adaptive/Odontoceti.lean` repeats 285 of its 362 non-blank lines.
  The bound is a **slot domain** — a predicate the decided slot and its
  anchor satisfy — and the two copies collapse if the relation is
  parameterised by one.
- **Reactive.** `Reactive/{Mysticeti,Odontoceti}.lean` is the same
  duplication a second time, and the same interface fixes both.

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
  Local.lean  Persist.lean  Reindex.lean
  Arcs/GC.lean          garbage collection, given Local and Reindex
  Arcs/SafeSkip.lean    crash recovery, given Persist
  Arcs/Adaptive.lean    bounded relations, given the consumer laws
  Arcs/Quality.lean     chain quality, given fairness and self-reference
  Compose.lean          transport composes

LeanDag/Hydrozoan/Properties/{Statement,Proof}.lean
LeanDag/OptimalHydrozoan/Properties/{Statement,Proof}.lean
LeanDag/MahiMahi/Properties/{Statement,Proof}.lean
LeanDag/FinWhale/Properties/{Statement,Proof}.lean
LeanDag/{Odontoceti,Nemo,Hybrid,Adaptive}/Properties.lean
LeanDag/MysticetiProperties.lean
```

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
- **G1** State `Local`, `Persist` with `Novel`, and `Reindex`.
- **G2** Prove garbage collection and crash recovery once from them,
  and `Compose`.
- **G3** Discharge them for Hydrozoan, and re-derive `decided_chopHZ`
  and `decided_fillHZ` through the generic route. Two existing theorems
  re-obtained with no new induction is the test that the abstraction is
  real.
- **G4** Discharge them for the core, giving the second instance.
  **Reassess here.**
- **G5** The schedule family: the slot domain, collapsing both the
  `Adaptive` and the `Reactive` duplications.
- **G6** Chain quality from fairness and self-reference.
- **G7** The remaining protocols, and FinWhale as the non-inductive
  test.

---

## 10. Risks

- **Re-indexing may not generalise** (§3.4). The largest single risk.
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
