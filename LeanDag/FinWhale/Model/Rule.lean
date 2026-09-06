import LeanDag.FinWhale.Model.Params
import LeanDag.Causality
import LeanDag.BlockRecord

/-!
# FinWhale — the fast path, as the paper defines it

The counting of `Counting.lean` is Lemma 4's arithmetic. This file is the
vocabulary the paper states Lemma 4 in: votes, leader-consistency, the
two branches of FP-evidence, and the direct decision rules. Only what the
fast path needs is modelled; the slow path is Mysticeti's and unchanged.

**Why the paper's gloss on "exposes equivocation" is exact.** The paper
writes that a block `b′` of round `r+2` exposes equivocation by `Lr` if
"its parent set is not leader-consistent, i.e., its causal history
contains multiple conflicting versions of `Lr`'s block". The two halves
are stated as if interchangeable, and at this depth they are, for a
reason worth naming: `b′`'s parents sit at round `r+1` and their
references at round `r`, so the round-`r` blocks in `b′`'s causal history
are exactly the blocks its parents vote for. Validity gives each parent
at most one edge per validator, so no single parent votes for two
versions. Two versions below `b′` therefore means two parents voting
differently, which is what a parent set failing to be leader-consistent
is.

The equivalence is what lets Lemma 4 use block validity the way it does.
Validity's leader clause is stated over the parent set — a round-`r`
block's parents are leader-consistent with respect to `Lr₋₂` or exclude
its block — and Lemma 4's equivocating branch reads the causal-history
side. `ExposesEquivocation` is the parent-set condition, the one the
validity rule constrains, and the one every count here is taken against.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- **Validity, as FinWhale extends Mysticeti's.** Every edge sits in the
round below, at most one edge per validator, a non-genesis block carries
`n − f` of them by distinct validators, and the parent set is either
leader-consistent with respect to the leader two rounds down or excludes
that leader's block. The last clause is FinWhale's addition and is what
the fast path's counting rests on. -/
structure ValidHere (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop where
  /-- Every edge points to the round immediately below. -/
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  /-- No two edges share a validator. -/
  distinct_creators : ∀ i ∈ b.refs, ∀ j ∈ b.refs, (blk i).creator = (blk j).creator → i = j
  /-- A non-genesis block carries `n − f` edges by distinct validators. -/
  quorum : 0 < b.round → quorumCard Validator ≤ (creators blk b).card
  /-- **FinWhale's clause, at every validator.** Either the parent set is
  consistent about `v` — the parents vote for at most one of `v`'s blocks
  — or `v`'s block is not among the parents. Consistency is a condition
  on what the parents *reference*, not on who authored them.

  **Stated at every validator rather than at the leader**, which is what
  makes it schedule-free, and what lets a `Dag` be a `Properties.DagRule`
  universe: a rule whose validity mentions the schedule cannot be
  related to another DAG by a band, since a band is a statement about
  blocks (`docs/porting-plan.md`).

  It is a genuine strengthening of the paper's rule, and a harmless one:
  a validator can check it locally, and it drops at most the `f` visibly
  equivocating validators' blocks, leaving the `n − f` its quorum needs.
  The same shape as Optimal-Hydrozoan's `LeaderExcludedAll`, and adopted
  for the same reason. -/
  leader_clause : ∀ v : Validator,
    (∀ i ∈ b.refs, ∀ j ∈ b.refs, ∀ x ∈ (blk i).refs, ∀ y ∈ (blk j).refs,
      (blk x).creator = v → (blk y).creator = v → x = y)
    ∨ (∀ i ∈ b.refs, (blk i).creator ≠ v)

/-- **FinWhale's validity is mechanised.** -/
instance ValidHere.mechanised :
    Validity.Mechanised (ValidHere (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) where
  pred := fun _ _ h => h.predecessor
  reads := by
    intro blk blk' ids b hcl hb hagree h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj; rw [hagree j (hb j hj)]; exact h.predecessor j hj
    · intro j hj l hl
      rw [hagree j (hb j hj), hagree l (hb l hl)]
      exact h.distinct_creators j hj l hl
    · intro hr
      refine le_trans (h.quorum hr) (Finset.card_le_card ?_)
      intro c hc
      unfold creators creatorsOf at hc ⊢
      obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
      exact Finset.mem_image.mpr ⟨j, hj, by rw [hagree j (hb j hj)]; exact hjc⟩
    · intro v
      rcases h.leader_clause v with h1 | h2
      · left
        intro i hi j hj x hx y hy hxv hyv
        rw [hagree i (hb i hi)] at hx
        rw [hagree j (hb j hj)] at hy
        rw [hagree x (hcl i (hb i hi) x hx)] at hxv
        rw [hagree y (hcl j (hb j hj) y hy)] at hyv
        exact h1 i hi j hj x hx y hy hxv hyv
      · right
        intro i hi
        rw [hagree i (hb i hi)]
        exact h2 i hi
  base := by
    intro blk b h0 hr
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj; rw [hr] at hj; exact absurd hj (Finset.notMem_empty j)
    · intro j hj; rw [hr] at hj; exact absurd hj (Finset.notMem_empty j)
    · intro h; omega
    · intro v; right; intro i hi; rw [hr] at hi; exact absurd hi (Finset.notMem_empty i)
  chops := by
    intro blk G b h hG
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj
      have := h.predecessor j hj
      change (chopBlk blk G j).round + 1 = b.round - G
      rw [chopBlk_round]; omega
    · intro j hj l hl hjl
      simp only [chopBlk_creator] at hjl
      exact h.distinct_creators j hj l hl hjl
    · intro hr
      change quorumCard Validator ≤ (creatorsOf (chopBlk blk G) b.refs).card
      rw [creatorsOf_chopBlk]
      exact h.quorum (by change 0 < b.round - G at hr; omega)
    · intro v
      rcases h.leader_clause v with h1 | h2
      · left
        intro i hi j hj x hx y hy hxv hyv
        simp only [chopBlk_creator] at hxv hyv
        exact h1 i hi j hj x (chopBlk_refs_subset hx) y (chopBlk_refs_subset hy) hxv hyv
      · right
        intro i hi
        rw [chopBlk_creator]
        exact h2 i hi

/-- **And does not read the author**, so the copy fill is valid. -/
instance ValidHere.copyStable :
    Validity.CopyStable (ValidHere (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) where
  copy := fun _ _ _ h => ⟨h.predecessor, h.distinct_creators, h.quorum, h.leader_clause⟩

/-- **A DAG the communication component can build**: the block record
at FinWhale's validity, with non-equivocation asked of the correct
validators. Equivocating blocks are admitted, of faulty validators
only. -/
abbrev Dag (Validator BlockId Payload : Type*) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] :=
  BlockRecord Validator BlockId Payload ValidHere (Correct : Finset Validator)

variable {D : Dag Validator BlockId Payload}

/-- **A schedule**: which round a slot proposes at, and who leads it.

FinWhale runs one slot per round, so `round` is the identity in every
execution here. It is a *parameter* rather than an identity because the
properties index by slot and supply the map (`Properties.Slots`), and a
rule that reads absolute rounds cannot carry an offset band
(`docs/target-properties.md` §3.4c). Keeping it abstract is what lets
FinWhale's carrier take the schedule it is given instead of pinning one.

It is FinWhale's own record rather than `LeanDag.Slots` so that the
model stays independent of Mysticeti's; the carrier maps one to the
other. -/
structure Sched (Validator : Type*) where
  /-- The round a slot's candidate proposes at. -/
  round : ℕ → ℕ
  /-- Who leads the slot. -/
  leader : ℕ → Validator

/-- **Which slots may anchor which.** The reverse pass reads an earlier
slot's verdict off a later one, and the rules that let it do so live two
rounds above the candidate, so the anchor's own candidate must sit at
least three rounds up. Under the identity schedule this is `r + 2 < a`,
which is the shape the protocol's runs meet it in.

The pass is stated over an arbitrary eligibility and this is the one
FinWhale supplies. Keeping it here, rather than at the conformance
file, is what lets the protocol and the carrier run the same pass. -/
def Sched.Elig (S : Sched Validator) (r a : ℕ) : Prop := S.round r + 3 ≤ S.round a

instance (S : Sched Validator) : DecidableRel S.Elig :=
  fun _ _ => inferInstanceAs (Decidable (_ ≤ _))

/-- The blocks of a round. -/
def blocksAt (D : Dag Validator BlockId Payload) (r : ℕ) : Finset BlockId :=
  D.ids.filter (fun b => (D.block b).round = r)

/-- The validators whose round-`(r+1)` block references `l`: `l`'s voters. -/
def voters (D : Dag Validator BlockId Payload) (l : BlockId) : Finset Validator :=
  creatorsOf D.block ((blocksAt D ((D.block l).round + 1)).filter
    (fun q => l ∈ (D.block q).refs))

/-- The parents of `b`, as validators. -/
def parentSet (D : Dag Validator BlockId Payload) (b : BlockId) : Finset Validator :=
  creatorsOf D.block ((D.block b).refs)

/-- The parents of `b` that vote for the leader block `l`. -/
def parentsVoting (D : Dag Validator BlockId Payload) (b l : BlockId) : Finset Validator :=
  creatorsOf D.block (((D.block b).refs).filter (fun q => l ∈ (D.block q).refs))

/-- Two blocks of the same slot: one leader, one round, not equal. -/
def Conflicting (D : Dag Validator BlockId Payload) (l l' : BlockId) : Prop :=
  l ≠ l' ∧ (D.block l).round = (D.block l').round ∧
    (D.block l).creator = (D.block l').creator

instance (D : Dag Validator BlockId Payload) (l l' : BlockId) :
    Decidable (Conflicting D l l') := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **Exposing a validator's equivocation, the parent-set reading.** Two
parents of `b` vote for two different blocks of `v`.

**Stated at a validator rather than at a leader**, which is what makes it
schedule-free: the old form read `ld ((D.block b).round - 2)`, and
so both named the schedule and subtracted from a round. The subtraction
was `scripts/audit-rounds.py`'s one FinWhale finding, and the leader read
is what keeps FinWhale from a band
(`docs/porting-plan.md`). `ExposesEquivocation` below is this at the
leader, so nothing downstream changes meaning. -/
def ExposesEquivocationBy (D : Dag Validator BlockId Payload) (b : BlockId)
    (v : Validator) : Prop :=
  ∃ l ∈ (D.ids : Finset BlockId), ∃ l' ∈ (D.ids : Finset BlockId),
    Conflicting D l l' ∧ (D.block l).creator = v ∧
      (parentsVoting D b l).Nonempty ∧ (parentsVoting D b l').Nonempty

instance (D : Dag Validator BlockId Payload) (b : BlockId) (v : Validator) :
    Decidable (ExposesEquivocationBy D b v) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, ∃ _ ∈ _, _))

/-- **FP-evidence**, the two branches of the paper's definition. A block
that has seen the equivocation must carry `f + p` parents voting for `l`
and fewer than `f + p` for anything conflicting; one that has not needs
only `f + p − 1` voting for `l`. -/
def FPEvidence (D : Dag Validator BlockId Payload) (b l : BlockId) : Prop :=
  if ExposesEquivocationBy D b (D.block l).creator then
    F.f + P.p ≤ (parentsVoting D b l).card ∧
      ∀ l' ∈ (D.ids : Finset BlockId), Conflicting D l l' →
        (parentsVoting D b l').card + 1 ≤ F.f + P.p
  else
    F.f + P.p ≤ (parentsVoting D b l).card + 1

instance (D : Dag Validator BlockId Payload) (b l : BlockId) :
    Decidable (FPEvidence D b l) := by
  unfold FPEvidence; infer_instance

/-- **An SP-certificate**, Mysticeti's, at this committee's quorum. -/
def SPCertificate (D : Dag Validator BlockId Payload) (b l : BlockId) : Prop :=
  spQuorum Validator ≤ (parentsVoting D b l).card

instance (D : Dag Validator BlockId Payload) (b l : BlockId) :
    Decidable (SPCertificate D b l) := inferInstanceAs (Decidable (_ ≤ _))

/-- **The fast direct commit**: `n − p` distinct validators vote for `l`
one round up. -/
def FastCommit (D : Dag Validator BlockId Payload) (l : BlockId) : Prop :=
  fastCard Validator ≤ (voters D l).card

instance (D : Dag Validator BlockId Payload) (l : BlockId) :
    Decidable (FastCommit D l) := inferInstanceAs (Decidable (_ ≤ _))

end FinWhale

end LeanDag
