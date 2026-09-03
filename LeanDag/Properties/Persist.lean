import LeanDag.Properties.Carrier

/-!
# Persistence: verdicts survive a growing DAG

`docs/target-properties.md` §3.2 and §3.3, the property the crash-recovery
mechanisms rest on.

**Why this is a property and not a corollary of safety.** Every
protocol's uniqueness theorem is stated for two views of the *same*
universe (`Mysticeti.lean:708`). To compare a replica that decided on
the DAG it held against one deciding later on a larger DAG, the first
derivation must first be moved into the second universe — and that move
is what this file names. Without it, uniqueness protects only replicas
holding identical DAGs, which is not the deployment situation.

**Why it is graded rather than absolute.** The failure mode is not that
a different verdict appears; that would be plain unsafety. It is that a
derivation ceases to exist, leaving a slot undecided. The core's direct
skip quantifies over candidates, so a slot whose leader published
nothing is skipped *vacuously*; add a block by that leader and the
premise acquires content it cannot discharge. Hydrozoan's skip counts
blames at the slot, and a count does not move when the blocks it counts
are still there.

> A verdict justified by evidence survives extension. A verdict
> justified by the absence of evidence does not.

So `Persist` carries a side condition `Ok` on the extension, and **which
condition a protocol needs is a fact about its skip rule** rather than
an artefact. A protocol whose verdicts are evidence-backed proves
`Persist R fun _ _ _ => True`; one whose skip is vacuous proves it only
under a condition, and the condition is the content of its safety
argument rather than bookkeeping.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **A slot's candidate**, in the vocabulary the carrier supplies: the
right round, the right author, present. Every protocol's
`IsLeaderBlock` is this. -/
def DagRule.IsCandidate (R : DagRule Validator BlockId Payload)
    (S : Slots Validator) (U : R.Universe) (k : ℕ) (L : BlockId) : Prop :=
  L ∈ R.ids U ∧ (R.block U L).round = S.slotRound k ∧
    (R.block U L).creator = S.leader k

/-- **`U'` extends `U`**: it holds everything `U` held, and denotes
those blocks the same way. Nothing is said about what it adds — that is
`Novel` below, which the two fields already determine. -/
structure Extends (R : DagRule Validator BlockId Payload) (U U' : R.Universe) : Prop where
  /-- Every block of `U` is a block of `U'`. -/
  subset : ∀ b, b ∈ R.ids U → b ∈ R.ids U'
  /-- And denotes the same block: same round, author and references. -/
  block : ∀ b, b ∈ R.ids U → R.block U' b = R.block U b

/-- **What an extension adds.** A parameter in
`Integration/Hydrozoan/Simulation.lean`, because that interface covers
truncations too and there "novel" has to be supplied as empty. For an
extension it is determined, so it is a definition here. -/
def Novel (R : DagRule Validator BlockId Payload) (U U' : R.Universe) (b : BlockId) : Prop :=
  b ∈ R.ids U' ∧ b ∉ R.ids U

namespace Extends

/-- **An old block references only old blocks**, so nothing that was
already present can reach what the extension added. This is the formal
content of "blocks nothing references cannot change a verdict", and it
is *derived* rather than assumed: an extension leaves old blocks alone,
and an old block's references were already inside `U`. -/
theorem old_refs_old (hc : Causal R) (he : Extends R U U')
    {b : BlockId} (hb : b ∈ R.ids U) {j : BlockId} (hj : j ∈ (R.block U' b).refs) :
    j ∈ R.ids U := by
  rw [he.block b hb] at hj
  exact (hc U).complete b hb j hj

/-- Restated: an old block never references a novel identifier. -/
theorem not_novel_of_mem_refs (hc : Causal R) (he : Extends R U U')
    {b : BlockId} (hb : b ∈ R.ids U) {j : BlockId} (hj : j ∈ (R.block U' b).refs) :
    ¬ Novel R U U' j :=
  fun hn => hn.2 (old_refs_old hc he hb hj)

/-- **Nothing an old block reaches is new.** The reference lemma
propagated along causal history: an extension can add blocks, but none
of them enters the history of a block that was already there.

This is what every protocol's persistence proof turns on. A rung test
asks whether something is in reach of the *anchor*, and the anchor of a
derivation over the old universe is old — so the extension cannot
supply a new certificate, a new vote, or a new candidate to any rung,
and the negative premises that would otherwise be destroyed survive. -/
theorem reaches_old (hc : Causal R) (he : Extends R U U')
    {A B : BlockId} (hA : A ∈ R.ids U) (h : ReachesFrom (R.block U') A B) :
    ReachesFrom (R.block U) A B ∧ B ∈ R.ids U := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hA⟩
  | @tail c b _ hstep ih =>
      have hc' : c ∈ R.ids U := ih.2
      have hb : b ∈ R.ids U := old_refs_old hc he hc' hstep
      refine ⟨ih.1.tail ?_, hb⟩
      have hstep' : b ∈ (R.block U' c).refs := hstep
      rw [he.block c hc'] at hstep'
      exact hstep'

/-- And so reachability from an old block is the same relation in both
universes. -/
theorem reaches_iff (hc : Causal R) (he : Extends R U U')
    {A B : BlockId} (hA : A ∈ R.ids U) :
    ReachesFrom (R.block U') A B ↔ ReachesFrom (R.block U) A B := by
  refine ⟨fun h => (reaches_old hc he hA h).1, fun h => ?_⟩
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c b hAc hstep ih =>
      have hc' : c ∈ R.ids U := (hc U).mem_ids_of_reaches hA hAc
      refine ih.tail ?_
      have hstep' : b ∈ (R.block U c).refs := hstep
      show b ∈ (R.block U' c).refs
      rw [he.block c hc']; exact hstep'

/-- Extension is reflexive. -/
theorem refl {U : R.Universe} : Extends R U U :=
  { subset := fun _ h => h, block := fun _ _ => rfl }

/-- And transitive, so a sequence of extensions is one. -/
theorem trans {U U' U'' : R.Universe} (h : Extends R U U') (h' : Extends R U' U'') :
    Extends R U U'' where
  subset := fun b hb => h'.subset b (h.subset b hb)
  block := fun b hb => by rw [h'.block b (h.subset b hb), h.block b hb]

/-- An old block keeps its round. -/
theorem round (he : Extends R U U') {b : BlockId} (hb : b ∈ R.ids U) :
    (R.block U' b).round = (R.block U b).round := by rw [he.block b hb]

/-- And a candidate of `U` is a candidate of `U'` at the same slot. -/
theorem isCandidate {S : Slots Validator} (he : Extends R U U') {k : ℕ} {L : BlockId}
    (h : R.IsCandidate S U k L) : R.IsCandidate S U' k L := by
  obtain ⟨hm, hr, hc⟩ := h
  refine ⟨he.subset L hm, ?_, ?_⟩ <;> rw [he.block L hm] <;> assumption

end Extends

/-- **Persistence, under a condition on the extension.** A verdict
reached on `V` is reached again on any larger view of any extension the
condition admits.

`Ok` is where the grading lives. A protocol whose skip counts evidence
at the slot proves this at `fun _ _ _ => True`; one whose skip
quantifies over candidates cannot, and states the condition its
vacuous skips need. -/
def Persist (R : DagRule Validator BlockId Payload)
    (Ok : Slots Validator → R.Universe → R.Universe → Prop) : Prop :=
  ∀ (S : Slots Validator) (U U' : R.Universe), Extends R U U' → Ok S U U' →
    ∀ (V : R.View U) (V' : R.View U'), R.viewIds V ⊆ R.viewIds V' →
    ∀ (k : ℕ) (v : Option BlockId), R.Decided S V k v → R.Decided S V' k v

namespace Persist

variable {Ok Ok' : Slots Validator → R.Universe → R.Universe → Prop}

/-- A protocol proving persistence under a weaker condition proves it
under a stronger one, so the grades are comparable. -/
theorem mono (h : Persist R Ok) (himp : ∀ S U U', Ok' S U U' → Ok S U U') :
    Persist R Ok' :=
  fun S U U' he hok V V' hV k v hd => h S U U' he (himp S U U' hok) V V' hV k v hd

/-- **The unconditional grade**, which is what an evidence-backed rule
should reach: verdicts survive every extension. -/
abbrev Unconditional (R : DagRule Validator BlockId Payload) : Prop :=
  Persist R fun _ _ _ => True

/-- An unconditional rule persists under any condition whatsoever. -/
theorem of_unconditional (h : Unconditional R) : Persist R Ok :=
  mono h fun _ _ _ _ => trivial

end Persist

end Properties

end LeanDag
