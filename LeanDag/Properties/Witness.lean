import LeanDag.Properties.Agreement
import LeanDag.Properties.Derived.Local
import LeanDag.Properties.Extends
import LeanDag.Properties.Derived.Persist
import LeanDag.Properties.Bounded

/-!
# The band a verdict reads

`docs/target-properties.md` §3.8. Locality and persistence say the same
thing twice, in different units and from different ends, and this is the
statement they are both shadows of.

*Given a verdict at slot `k`, there is a **range of rounds** — from the
slot's own round up to some finite top — such that the blocks the view
holds in that range already carry the verdict. Any universe and any view
agreeing there decide the slot the same way.*

The top is variable, as it must be: an indirect verdict anchors on a
committed slot that may sit arbitrarily high, and the anchor's own
derivation reaches higher still. What the property claims is that the
top **exists**, so a verdict is never a function of unboundedly much of
the DAG.

**What follows from it** is in `Derived/FromBand.lean`: persistence,
locality, monotonicity in the view, and the slot bound the adaptive
fixpoint reads. One induction per protocol, four consequences out.

**What does not.** Truncation (`Truncate.lean`) renumbers rounds and
slots as well as restricting them, and no agreement hypothesis states a
renumbering; `LocalTruncate` stays separate, and
`Truncate.lean` records why the renumbering cannot be isolated. The
slot-level bound the adaptive fixpoint needs (`Bounded.lean`) is a bound
in **slots**, which a bound in rounds does not supply when a round
carries several slots.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **Views hold blocks of their universe.** `Barnacle.Laws` states this
as `view_subset`; `DagRule` does not, so the derivations below take it. -/
def ViewSound (R : DagRule Validator BlockId Payload) : Prop :=
  ∀ {U : R.Universe} (V : R.View U), R.viewIds V ⊆ R.ids U

/-- **`U'` carries `U`'s band.** Every block `U` holds between `lo` and
`hi` is a block of `U'`, at the same round and with the same author, and
above the floor with the same references.

Deliberately **one-directional**: `U'` may hold blocks `U` does not, in
the band or out of it, which is what a fill does. A rule proving
`Banded` must therefore cope with candidates that appear from nowhere,
and the core does, because nothing old references them.

The references clause stops at the floor rather than including it. A
truncation empties the references of its bottom layer, and a rule reads
a vote from a *parent*, so the floor contributes presence and authorship
but no vote. `AgreeAbove` draws the line in the same place. -/
structure AgreeBand (R : DagRule Validator BlockId Payload) (U U' : R.Universe)
    (lo hi : ℕ) : Prop where
  /-- A block of the band is a block of `U'`. -/
  mem : ∀ b, b ∈ R.ids U → lo ≤ (R.block U b).round → (R.block U b).round ≤ hi →
    b ∈ R.ids U'
  /-- A block sitting in the band on either side keeps its round and author. -/
  block : ∀ b, b ∈ R.ids U →
    ((lo ≤ (R.block U b).round ∧ (R.block U b).round ≤ hi) ∨
      (b ∈ R.ids U' ∧ lo ≤ (R.block U' b).round ∧ (R.block U' b).round ≤ hi)) →
    (R.block U' b).round = (R.block U b).round ∧
      (R.block U' b).creator = (R.block U b).creator
  /-- Strictly above the floor, its references too. -/
  refs : ∀ b, b ∈ R.ids U → lo < (R.block U b).round → (R.block U b).round ≤ hi →
    (R.block U' b).refs = (R.block U b).refs

namespace AgreeBand

/-- An extension carries every band, since it moves nothing. -/
theorem of_extends {U U' : R.Universe} (he : Extends R U U') (lo hi : ℕ) :
    AgreeBand R U U' lo hi where
  mem := fun b hb _ _ => he.subset b hb
  block := fun b hb _ => by rw [he.block b hb]; exact ⟨rfl, rfl⟩
  refs := fun b hb _ _ => by rw [he.block b hb]

/-- Agreement above a round carries every band whose floor is at or
above it. -/
theorem of_agreeAbove {U U' : R.Universe} {r lo hi : ℕ} (h : AgreeAbove R U U' r)
    (hr : r ≤ lo) : AgreeBand R U U' lo hi where
  mem := fun b hb hlo _ => ((h.mem b).mp ⟨hb, by omega⟩).1
  block := fun b hb hband => by
    have hU : r ≤ (R.block U b).round := by
      rcases hband with ⟨h1, -⟩ | ⟨hmem', h1, -⟩
      · omega
      · exact ((h.mem b).mpr ⟨hmem', by omega⟩).2
    exact ⟨h.round b hb hU, h.creator b hb hU⟩
  refs := fun b hb hlo _ => h.refs b hb (by omega)

/-- A universe carries its own bands. -/
theorem refl {U : R.Universe} {lo hi : ℕ} : AgreeBand R U U lo hi where
  mem := fun _ hb _ _ => hb
  block := fun _ _ _ => ⟨rfl, rfl⟩
  refs := fun _ _ _ _ => rfl

/-- Agreement on a band gives agreement on any narrower one. -/
theorem mono {U U' : R.Universe} {lo hi lo' hi' : ℕ} (h : AgreeBand R U U' lo hi)
    (hlo : lo ≤ lo') (hhi : hi' ≤ hi) : AgreeBand R U U' lo' hi' where
  mem := fun b hb h1 h2 => h.mem b hb (by omega) (by omega)
  block := fun b hb hband => by
    refine h.block b hb ?_
    rcases hband with ⟨h1, h2⟩ | ⟨hm, h1, h2⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr ⟨hm, by omega, by omega⟩
  refs := fun b hb h1 h2 => h.refs b hb (by omega) (by omega)

variable {U U' : R.Universe} {lo hi : ℕ}

/-- **Causal history inside the band is the same history.** A path that
starts in the band and ends strictly above its floor keeps every step
inside, since a reference sits one round below its referrer. -/
theorem reaches_of (hc : Causal R) (h : AgreeBand R U U' lo hi)
    {A : BlockId} (hA : A ∈ R.ids U) (hAhi : (R.block U A).round ≤ hi) :
    ∀ {C : BlockId}, ReachesFrom (R.block U) A C → lo < (R.block U C).round →
      ReachesFrom (R.block U') A C := by
  intro C hre
  induction hre with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | @tail b c hAb hstep ih =>
      intro hcr
      have hb : b ∈ R.ids U := (hc U).mem_ids_of_reaches hA hAb
      have hstep' : c ∈ (R.block U b).refs := hstep
      have hround := (hc U).refs_round b hb c hstep'
      have hbhi : (R.block U b).round ≤ hi :=
        le_trans ((hc U).round_le_of_reaches hA hAb) hAhi
      refine (ih (by omega)).tail ?_
      show c ∈ (R.block U' b).refs
      rw [h.refs b hb (by omega) hbhi]
      exact hstep'

/-- **And a path of `U'` that stays above the floor is a path of `U`.**
Nothing the band adds is reachable from a block the band already had:
the references of an old block in the band are the references it had,
and those are blocks of `U`. This is what lets a rule prove `Banded`
without knowing whether the candidates it must rule out are new. -/
theorem reaches_old (hc : Causal R) (h : AgreeBand R U U' lo hi)
    {A : BlockId} (hA : A ∈ R.ids U) (hAlo : lo ≤ (R.block U A).round)
    (hAhi : (R.block U A).round ≤ hi) :
    ∀ {C : BlockId}, ReachesFrom (R.block U') A C → lo ≤ (R.block U' C).round →
      C ∈ R.ids U ∧ ReachesFrom (R.block U) A C ∧
        (R.block U C).round = (R.block U' C).round := by
  intro C hre
  induction hre with
  | refl =>
      intro _
      exact ⟨hA, Relation.ReflTransGen.refl, (h.block A hA (Or.inl ⟨hAlo, hAhi⟩)).1.symm⟩
  | @tail b c hAb hstep ih =>
      intro hcr
      have hstep' : c ∈ (R.block U' b).refs := hstep
      have hbU' : b ∈ R.ids U' :=
        (hc U').mem_ids_of_reaches (h.mem A hA hAlo hAhi) hAb
      have hround' := (hc U').refs_round b hbU' c hstep'
      obtain ⟨hbU, hbre, hbeq⟩ := ih (by omega)
      have hbhi : (R.block U b).round ≤ hi :=
        le_trans ((hc U).round_le_of_reaches hA hbre) hAhi
      have hrefs : (R.block U' b).refs = (R.block U b).refs :=
        h.refs b hbU (by omega) hbhi
      rw [hrefs] at hstep'
      have hroundU := (hc U).refs_round b hbU c hstep'
      exact ⟨(hc U).complete b hbU c hstep', hbre.tail hstep', by omega⟩

end AgreeBand

/-- **Every verdict reads a band of rounds.** From the slot's own round
up to some top, the blocks the view holds and the leaders of the slots
sitting there already carry the verdict: any universe carrying the
band, any view holding those blocks, and any schedule with the same
round structure naming the same leaders inside the band, decides the
slot the same way.

Three axes, one top. The DAG axis gives `Persist` and `Local`, the view
axis gives monotonicity, and the schedule axis gives the bound the
adaptive fixpoint needs, since the slots sitting at or below a round are
finitely many (`Slots.mono` with `Slots.unbounded`). -/
def Banded (R : DagRule Validator BlockId Payload) : Prop :=
  ∀ (S : Slots Validator) (U : R.Universe) (V : R.View U) (k : ℕ) (v : Option BlockId),
    R.Decided S V k v →
      ∃ top : ℕ, ∀ (S' : Slots Validator) (U' : R.Universe) (V' : R.View U'),
        S'.slotRound = S.slotRound →
        (∀ m, S.slotRound m ≤ top → S'.leader m = S.leader m) →
        AgreeBand R U U' (S.slotRound k) top →
        (∀ b, b ∈ R.viewIds V → S.slotRound k ≤ (R.block U b).round →
          (R.block U b).round ≤ top → b ∈ R.viewIds V') →
        R.Decided S' V' k v

end Properties

end LeanDag
