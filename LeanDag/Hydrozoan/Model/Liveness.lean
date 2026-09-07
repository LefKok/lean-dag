import LeanDag.Hydrozoan.Model.View
import LeanDag.Participation

/-!
# Liveness hypotheses

Trusted core: the structural rendering of "after GST". Safety assumed
nothing about the network; every liveness theorem is exactly as strong
as the hypotheses here, so this file is the liveness arc's audit center
of gravity.

The derivation of these hypotheses from delivery primitives (received
sets, timeouts, view convergence) is deliberately out of scope: they
are **assumed**, with the fidelity argument recorded on each
definition.
-/

namespace LeanDag

namespace Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [F : LeanDag.Hydrozoan.Faults Replica]

/-! **`PopulatedOn U T r`** (`Participation.lean`): every replica in `T`
authors a round-`r` block in `U`. Nothing here constrains `T`: the
requirements `T ⊆ Correct` and `q ≤ T.card` are explicit hypotheses of
the consuming theorems (the subset condition alone would admit
`T = ∅`) — asserting this predicate for a `T` containing a Byzantine
replica is asserting Byzantine behavior, which no theorem does. -/

/-- The all-of-`Correct` case. -/
abbrev Populated (U : BlockUniverse Replica BlockId) (r : ℕ) : Prop :=
  PopulatedOn U (Correct : Finset Replica) r

/-! **`SynchronisedOn U T R`** (`Participation.lean`): from round `R`
on, every `T`-authored block references every `T`-authored block of
the round below. Precisely: the constrained
blocks are those at rounds `≥ R + 1` — a round-`R` block owes nothing
to round `R − 1`.

**An assumption, not a theorem.** A block's references are frozen when
it is built: a replica that builds on the first quorum it holds can
miss a slow correct block forever, even under perfect view convergence.
What makes this true of the deployed system in good periods is the
protocol's waiting rule — a correct replica builds a full timeout after
entering a round, never as soon as a quorum arrives — together with
timely post-stabilization delivery. Deriving it from those primitives
is future work; here it is assumed.

**`R` is not GST.** It is a round index — stabilization plus however
long catch-up ran. No clock and no `Δ` appear anywhere in the model.

`T` is a parameter, not a defined notion: it is instantiated as a
quorum of correct replicas participating steadily through the window —
authoring every round from `R` on and receiving peers' blocks in time —
and those properties are exactly what the hypotheses about `T` assert.

**Both quantifiers are `T`-restricted, deliberately.** A Byzantine
replica may publish nothing, or reveal blocks to only some replicas, so
assuming its blocks get referenced would assume Byzantine replicas
behave; and no crashed replica is mentioned — the hybrid model's
`Correct` pool is exactly the population liveness may lean on.

Compatibility with validity: when round `n` is `T`-populated, a block
referencing all of a quorum-sized `T`'s round-`n` blocks carries ≥ `q`
distinct creators, so `ValidWrt.quorum` is satisfiable alongside — the
witness models prove it.

**Known limitation — round-jumping recovery is not modeled.** `T` is
fixed across the whole suffix from `R`, so a correct replica that
recovers by jumping to the frontier round (authoring nothing for the
rounds it skipped) must sit outside `T` permanently, even after it has
rejoined the steady quorum. A finer, wave-scoped form (a per-round-pair
`SynchronisedAt` with a per-wave `T`) would readmit such a replica for
every wave it actually participates in; deliberately deferred. -/

/-- The all-of-`Correct` case. -/
abbrev Synchronised (U : BlockUniverse Replica BlockId) (R : ℕ) : Prop :=
  SynchronisedOn U (Correct : Finset Replica) R

/-! **The eventual view** is the record's `View.full`, and **a view
caught up to round `N`** the record's `View.CoversUpto`
(`BlockRecord.lean`): decision monotonicity transports any view's
verdicts into the full view, and it discharges every `CoversUpto`
hypothesis (`View.coversUpto_full`). -/

end Hydrozoan

end LeanDag
