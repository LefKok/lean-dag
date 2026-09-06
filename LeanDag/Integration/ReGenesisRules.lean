import LeanDag.Integration.ReGenesis
import LeanDag.Integration.HybridMechanisms
import LeanDag.Integration.NemoMechanisms
import LeanDag.Integration.FinWhaleMechanisms
import LeanDag.Hydrozoan.Helpers.Commit
import LeanDag.OdontocetiProperties
import LeanDag.MahiMahiProperties
import LeanDag.OptimalHydrozoan.Carrier
import LeanDag.Properties.Arcs.Liveness
import LeanDag.Hydrozoan.Helpers.Record

/-!
# Re-genesis, for every rule with a carrier

`scripts/audit-mechanisms.py`'s re-genesis column, which the extension
column had hidden: `addGenesis` had a witness at the core only. The
construction is the simplest of the three transformers — one
reference-free block at round zero for a validator that has none — so
every rule's invariant discharge is either vacuous or the identity, and
the file is long only because there are seven of them.

Odontoceti and Mahi-Mahi take the core's construction verbatim, their
universes being the core's. Hybrid takes it with its one invariant,
`honestNoEquiv_addGenesis`. Nemo, FinWhale, Hydrozoan and
Optimal-Hydrozoan keep their own universe records and build their own,
on the same data. Optimal's is the one with content: leader exclusion
survives because the new block is the only block of its author, so it
can witness no equivocation and be no second candidate.

Each rule then has `Extends` and `Sustains` witnesses, and from those
verdict transport, cross-universe agreement, and — through
`Arcs/Liveness.lean` — the liveness precondition, all from the generic
theorems.
-/

namespace LeanDag

namespace Integration

open LeanDag.Properties LeanDag.Properties.Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-! ## Odontoceti and Mahi-Mahi: the core's universe -/

section Odontoceti

variable [Faults5 Validator] {B : Type} [LinearOrder B]
variable {W : BlockUniverse Validator B Payload} {v : Validator} {g : B} {p : Payload}
variable {hg : g ∉ W.ids} {hsev : ∀ b ∈ W.ids, (W.block b).creator ≠ v}

/-- **Re-genesis extends Odontoceti's carrier** — the core's witness, projected. -/
theorem extends_addGenesis_odontoceti :
    Extends (OdontocetiProperties.odontocetiRule (Validator := Validator) (BlockId := B)
      (Payload := Payload)) W (addGenesis W v g p hg hsev) :=
  let h := extends_addGenesis (V := W) (v := v) (g := g) (p := p) (hg := hg) (hsev := hsev)
  { subset := h.subset, block := h.block }

/-- **And sustains it from round one.** -/
theorem sustains_addGenesis_odontoceti :
    Sustains (OdontocetiProperties.odontocetiRule (Validator := Validator) (BlockId := B)
      (Payload := Payload)) W (addGenesis W v g p hg hsev) 0 1 :=
  let h := sustains_addGenesis (V := W) (v := v) (g := g) (p := p) (hg := hg) (hsev := hsev)
  { mem := h.mem, round := h.round, creator := h.creator, refs := h.refs }

/-- **Verdicts survive re-genesis, for Odontoceti.** -/
theorem decided_addGenesis_odontoceti [S : Slots Validator] {V : View Validator B Payload W}
    {V' : View Validator B Payload (addGenesis W v g p hg hsev)} (hsub : V.ids ⊆ V'.ids)
    {k : ℕ} {u : Option B} (h : Odontoceti.Decided W V k u) :
    Odontoceti.Decided (addGenesis W v g p hg hsev) V' k u :=
  Persist.of_banded OdontocetiProperties.banded S W _ extends_addGenesis_odontoceti V V' hsub k u h

/-- **And agreement across it.** -/
theorem decided_agree_addGenesis_odontoceti [S : Slots Validator] {V : View Validator B Payload W}
    {V' V'' : View Validator B Payload (addGenesis W v g p hg hsev)} (hsub : V.ids ⊆ V'.ids)
    {k : ℕ} {u u' : Option B} (h : Odontoceti.Decided W V k u)
    (h' : Odontoceti.Decided (addGenesis W v g p hg hsev) V'' k u') : u = u' :=
  decided_agree_extends OdontocetiProperties.agree (Persist.of_banded OdontocetiProperties.banded)
    extends_addGenesis_odontoceti (V' := V') hsub h h'

end Odontoceti

section MahiMahi

variable [Faults Validator] {B : Type} [LinearOrder B] {w : ℕ}
variable {W : BlockUniverse Validator B Payload} {v : Validator} {g : B} {p : Payload}
variable {hg : g ∉ W.ids} {hsev : ∀ b ∈ W.ids, (W.block b).creator ≠ v}

/-- **Re-genesis extends Mahi-Mahi's carrier.** -/
theorem extends_addGenesis_mahimahi :
    Extends (MahiMahiProperties.mahiMahiRule (Validator := Validator) (BlockId := B)
      (Payload := Payload) w) W (addGenesis W v g p hg hsev) :=
  let h := extends_addGenesis (V := W) (v := v) (g := g) (p := p) (hg := hg) (hsev := hsev)
  { subset := h.subset, block := h.block }

/-- **And sustains it from round one.** -/
theorem sustains_addGenesis_mahimahi :
    Sustains (MahiMahiProperties.mahiMahiRule (Validator := Validator) (BlockId := B)
      (Payload := Payload) w) W (addGenesis W v g p hg hsev) 0 1 :=
  let h := sustains_addGenesis (V := W) (v := v) (g := g) (p := p) (hg := hg) (hsev := hsev)
  { mem := h.mem, round := h.round, creator := h.creator, refs := h.refs }

/-- **Verdicts survive re-genesis, for Mahi-Mahi.** -/
theorem decided_addGenesis_mahimahi [S : Slots Validator] (hw : 2 ≤ w)
    {V : View Validator B Payload W}
    {V' : View Validator B Payload (addGenesis W v g p hg hsev)} (hsub : V.ids ⊆ V'.ids)
    {k : ℕ} {u : Option B} (h : MahiMahi.Decided w W V k u) :
    MahiMahi.Decided w (addGenesis W v g p hg hsev) V' k u :=
  Persist.of_banded (MahiMahiProperties.banded hw) S W _ extends_addGenesis_mahimahi V V' hsub
    k u h

/-- **And agreement across it.** -/
theorem decided_agree_addGenesis_mahimahi [S : Slots Validator] (hw : 2 ≤ w)
    {V : View Validator B Payload W}
    {V' V'' : View Validator B Payload (addGenesis W v g p hg hsev)} (hsub : V.ids ⊆ V'.ids)
    {k : ℕ} {u u' : Option B} (h : MahiMahi.Decided w W V k u)
    (h' : MahiMahi.Decided w (addGenesis W v g p hg hsev) V'' k u') : u = u' :=
  decided_agree_extends (MahiMahiProperties.agree hw)
    (Persist.of_banded (MahiMahiProperties.banded hw)) extends_addGenesis_mahimahi (V' := V')
    hsub h h'

end MahiMahi

/-! ## Hybrid: the core's universe with one invariant -/

section Hybrid

variable [H : HybridFaults Validator] {B : Type} [LinearOrder B] {kt : ℕ}

/-- **Re-genesis cannot make an honest validator equivocate**: the new
block's author has no other block. -/
theorem honestNoEquiv_addGenesis {U : BlockUniverse Validator B Payload} (hne : HonestNoEquiv U)
    {v : Validator} {g : B} {p : Payload} {hg : g ∉ U.ids}
    {hsev : ∀ b ∈ U.ids, (U.block b).creator ≠ v} :
    HonestNoEquiv (addGenesis U v g p hg hsev) := by
  intro i hi j hj hib hij hround
  rcases Finset.mem_insert.mp hi with rfl | ho <;>
    rcases Finset.mem_insert.mp hj with rfl | ho'
  · rfl
  · rw [addGenesis_block_new (v := v) (p := p) (hg := hg) (hsev := hsev),
      addGenesis_block_old (v := v) (g := i) (p := p) (hg := hg) (hsev := hsev) ho'] at hij
    exact absurd hij.symm (hsev j ho')
  · rw [addGenesis_block_old (v := v) (g := j) (p := p) (hg := hg) (hsev := hsev) ho,
      addGenesis_block_new (v := v) (p := p) (hg := hg) (hsev := hsev)] at hij
    exact absurd hij (hsev i ho)
  · rw [addGenesis_block_old (v := v) (g := g) (p := p) (hg := hg) (hsev := hsev) ho]
      at hib hij hround
    rw [addGenesis_block_old (v := v) (g := g) (p := p) (hg := hg) (hsev := hsev) ho']
      at hij hround
    exact hne i ho j ho' hib hij hround

variable {U : (HybridProperties.hybridRule (Validator := Validator) (BlockId := B)
  (Payload := Payload) kt).Universe}
variable {v : Validator} {g : B} {p : Payload}
variable {hg : g ∉ U.val.ids} {hsev : ∀ b ∈ U.val.ids, (U.val.block b).creator ≠ v}

/-- **Re-genesis, at Hybrid's carrier.** -/
def addGenesisHybrid (U : (HybridProperties.hybridRule (Validator := Validator) (BlockId := B)
    (Payload := Payload) kt).Universe) (v : Validator) (g : B) (p : Payload)
    (hg : g ∉ U.val.ids) (hsev : ∀ b ∈ U.val.ids, (U.val.block b).creator ≠ v) :
    (HybridProperties.hybridRule (Validator := Validator) (BlockId := B)
      (Payload := Payload) kt).Universe :=
  ⟨addGenesis U.val v g p hg hsev, honestNoEquiv_addGenesis U.property⟩

theorem extends_addGenesis_hybrid :
    Extends (HybridProperties.hybridRule (Validator := Validator) (BlockId := B)
      (Payload := Payload) kt) U (addGenesisHybrid U v g p hg hsev) :=
  let h := extends_addGenesis (V := U.val) (v := v) (g := g) (p := p) (hg := hg) (hsev := hsev)
  { subset := h.subset, block := h.block }

theorem sustains_addGenesis_hybrid :
    Sustains (HybridProperties.hybridRule (Validator := Validator) (BlockId := B)
      (Payload := Payload) kt) U (addGenesisHybrid U v g p hg hsev) 0 1 :=
  let h := sustains_addGenesis (V := U.val) (v := v) (g := g) (p := p) (hg := hg) (hsev := hsev)
  { mem := h.mem, round := h.round, creator := h.creator, refs := h.refs }

/-- **Verdicts survive re-genesis, for Hybrid.** -/
theorem decided_addGenesis_hybrid [S : Slots Validator] (hpos : 0 < kt)
    {V : View Validator B Payload U.val}
    {V' : View Validator B Payload (addGenesisHybrid U v g p hg hsev).val} (hsub : V.ids ⊆ V'.ids)
    {k : ℕ} {u : Option B} (h : Hybrid.Decided (S := S) kt U.val V k u) :
    Hybrid.Decided (S := S) kt (addGenesisHybrid U v g p hg hsev).val V' k u :=
  Persist.of_banded (HybridProperties.banded hpos) S U _ extends_addGenesis_hybrid V V' hsub k u h

end Hybrid

/-! ## Nemo: its own universe record -/

section Nemo

/-- **Re-genesis, at Nemo's universe.** One reference-free block at round
zero: the majority quorum is owed only above round zero, and universal
non-equivocation is kept because the author has no other block. -/
def addGenesisNemo (U : Nemo.Universe Validator BlockId Payload) (v : Validator)
    (g : BlockId) (p : Payload) (hg : g ∉ U.ids)
    (hsev : ∀ b ∈ U.ids, (U.block b).creator ≠ v) :
    Nemo.Universe Validator BlockId Payload :=
  BlockRecord.addGenesis U v g p hg hsev

variable {U : Nemo.Universe Validator BlockId Payload} {v : Validator} {g : BlockId} {p : Payload}
variable {hg : g ∉ U.ids} {hsev : ∀ b ∈ U.ids, (U.block b).creator ≠ v}

@[simp] theorem addGenesisNemo_block_old {b : BlockId} (hb : b ∈ U.ids) :
    (addGenesisNemo U v g p hg hsev).block b = U.block b := if_pos hb

@[simp] theorem addGenesisNemo_block_new :
    (addGenesisNemo U v g p hg hsev).block g = ⟨0, v, ∅, p⟩ := if_neg hg

theorem extends_addGenesis_nemo :
    Extends (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) U (addGenesisNemo U v g p hg hsev) :=
  nemoOnRecord.extends_addGenesis (U := U) (v := v) (g := g) (p := p) (hg := hg) (hsev := hsev)

/-- **And it sustains Nemo's carrier from round one.** -/
theorem sustains_addGenesis_nemo :
    Sustains (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) U (addGenesisNemo U v g p hg hsev) 0 1 :=
  nemoOnRecord.sustains_addGenesis (U := U) (v := v) (g := g) (p := p) (hg := hg) (hsev := hsev)

theorem decided_addGenesis_nemo [S : Slots Validator] {V : Nemo.View Validator BlockId Payload U}
    {V' : Nemo.View Validator BlockId Payload (addGenesisNemo U v g p hg hsev)}
    (hsub : V.ids ⊆ V'.ids) {k : ℕ} {u : Option BlockId} (h : Nemo.Decided (S := S) U V k u) :
    Nemo.Decided (S := S) (addGenesisNemo U v g p hg hsev) V' k u :=
  Persist.of_banded NemoProperties.banded S U _ extends_addGenesis_nemo V V' hsub k u h

/-- **And agreement across it.** -/
theorem decided_agree_addGenesis_nemo [S : Slots Validator]
    {V : Nemo.View Validator BlockId Payload U}
    {V' V'' : Nemo.View Validator BlockId Payload (addGenesisNemo U v g p hg hsev)}
    (hsub : V.ids ⊆ V'.ids) {k : ℕ} {u u' : Option BlockId}
    (h : Nemo.Decided (S := S) U V k u)
    (h' : Nemo.Decided (S := S) (addGenesisNemo U v g p hg hsev) V'' k u') : u = u' :=
  decided_agree_extends NemoProperties.agree (Persist.of_banded NemoProperties.banded)
    extends_addGenesis_nemo (V' := V') hsub h h'

end Nemo

/-! ## FinWhale: its own DAG record -/

section FinWhale

open LeanDag.FinWhale

variable [F : Faults Validator] [P : LeanDag.FinWhale.Params Validator]
variable {B : Type} [LinearOrder B]

/-- **Re-genesis, at FinWhale's DAG.** Every validity clause of a block
with no parents is vacuous — the leader clause by its second disjunct —
and non-equivocation is kept because the author has no other block. -/
def addGenesisFinWhale (D : Dag Validator B Payload) (v : Validator) (g : B) (p : Payload)
    (hg : g ∉ D.ids) (hsev : ∀ b ∈ D.ids, (D.block b).creator ≠ v) :
    Dag Validator B Payload :=
  BlockRecord.addGenesis D v g p hg hsev

variable {D : Dag Validator B Payload} {v : Validator} {g : B} {p : Payload}
variable {hg : g ∉ D.ids} {hsev : ∀ b ∈ D.ids, (D.block b).creator ≠ v}

@[simp] theorem addGenesisFinWhale_block_old {b : B} (hb : b ∈ D.ids) :
    (addGenesisFinWhale D v g p hg hsev).block b = D.block b := if_pos hb

@[simp] theorem addGenesisFinWhale_block_new :
    (addGenesisFinWhale D v g p hg hsev).block g = ⟨0, v, ∅, p⟩ := if_neg hg

theorem extends_addGenesis_finwhale :
    Extends (FinWhaleProperties.finWhaleRule (Validator := Validator) (BlockId := B)
      (Payload := Payload)) D (addGenesisFinWhale D v g p hg hsev) :=
  finWhaleOnRecord.extends_addGenesis (U := D) (v := v) (g := g) (p := p) (hg := hg) (hsev := hsev)

/-- **And it sustains FinWhale's carrier from round one.** -/
theorem sustains_addGenesis_finwhale :
    Sustains (FinWhaleProperties.finWhaleRule (Validator := Validator) (BlockId := B)
      (Payload := Payload)) D (addGenesisFinWhale D v g p hg hsev) 0 1 :=
  finWhaleOnRecord.sustains_addGenesis (U := D) (v := v) (g := g) (p := p) (hg := hg) (hsev := hsev)

theorem decided_addGenesis_finwhale [S : Slots Validator]
    {V : {V : Finset B // IsView D V}}
    {V' : {V' : Finset B // IsView (addGenesisFinWhale D v g p hg hsev) V'}}
    (hsub : V.val ⊆ V'.val) {k : ℕ} {u : Option B}
    (h : (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V k u) :
    (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V' k u :=
  Persist.of_banded FinWhaleProperties.banded S D _ extends_addGenesis_finwhale V V' hsub k u h

/-- **And agreement across it.** -/
theorem decided_agree_addGenesis_finwhale [S : Slots Validator]
    {V : {V : Finset B // IsView D V}}
    {V' V'' : {V' : Finset B // IsView (addGenesisFinWhale D v g p hg hsev) V'}}
    (hsub : V.val ⊆ V'.val) {k : ℕ} {u u' : Option B}
    (h : (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V k u)
    (h' : (FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V'' k u') : u = u' :=
  decided_agree_extends FinWhaleProperties.agree (Persist.of_banded FinWhaleProperties.banded)
    extends_addGenesis_finwhale (V' := V') hsub h h'

end FinWhale

/-! ## Hydrozoan and Optimal-Hydrozoan: their own universe record -/

section Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {B : Type} [DecidableEq B] [LinearOrder B]
variable [LeanDag.Hydrozoan.Faults Replica]

/-- **Re-genesis, at Hydrozoan's universe.** -/
def addGenesisHZ (U : LeanDag.Hydrozoan.BlockUniverse Replica B) (v : Replica) (g : B)
    (hg : g ∉ U.ids) (hsev : ∀ b ∈ U.ids, (U.block b).author ≠ v) :
    LeanDag.Hydrozoan.BlockUniverse Replica B :=
  LeanDag.Hydrozoan.onRecord.addGenesis U v g () hg hsev

variable {U : LeanDag.Hydrozoan.BlockUniverse Replica B} {v : Replica} {g : B}
variable {hg : g ∉ U.ids} {hsev : ∀ b ∈ U.ids, (U.block b).author ≠ v}

@[simp] theorem addGenesisHZ_block_old {b : B} (hb : b ∈ U.ids) :
    (addGenesisHZ U v g hg hsev).block b = U.block b := by
  change LeanDag.Hydrozoan.unadapt (if b ∈ U.ids then _ else _) = U.block b
  rw [if_pos hb]; rfl

@[simp] theorem addGenesisHZ_block_new :
    (addGenesisHZ U v g hg hsev).block g = ⟨0, v, ∅⟩ := by
  change LeanDag.Hydrozoan.unadapt (if g ∈ U.ids then _ else _) = _
  rw [if_neg hg]; rfl

theorem extends_addGenesisHZ :
    Extends (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := B))
      U (addGenesisHZ U v g hg hsev) :=
  LeanDag.Hydrozoan.onRecord.extends_addGenesis (U := U) (v := v) (g := g) (p := ())
    (hg := hg) (hsev := hsev)

/-- **And it sustains Hydrozoan's carrier from round one.** -/
theorem sustains_addGenesisHZ :
    Sustains (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := B))
      U (addGenesisHZ U v g hg hsev) 0 1 :=
  LeanDag.Hydrozoan.onRecord.sustains_addGenesis (U := U) (v := v) (g := g) (p := ())
    (hg := hg) (hsev := hsev)

theorem decided_addGenesisHZ (S : Slots Replica) {V : LeanDag.Hydrozoan.View U}
    {V' : LeanDag.Hydrozoan.View (addGenesisHZ U v g hg hsev)} (hsub : V.ids ⊆ V'.ids)
    {k : ℕ} {u : Option B}
    (h : (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := B)).Decided S V k u) :
    (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := B)).Decided S V' k u :=
  Persist.of_banded LeanDag.Hydrozoan.banded S U _ extends_addGenesisHZ V V' hsub k u h

/-- **And agreement across it.** -/
theorem decided_agree_addGenesisHZ (S : Slots Replica) {V : LeanDag.Hydrozoan.View U}
    {V' V'' : LeanDag.Hydrozoan.View (addGenesisHZ U v g hg hsev)} (hsub : V.ids ⊆ V'.ids)
    {k : ℕ} {u u' : Option B}
    (h : (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := B)).Decided S V k u)
    (h' : (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := B)).Decided S V'' k u') :
    u = u' :=
  decided_agree_extends LeanDag.Hydrozoan.agree (Persist.of_banded LeanDag.Hydrozoan.banded)
    extends_addGenesisHZ (V' := V') hsub h h'

end Hydrozoan

section Optimal

open LeanDag.Barnacle.OptimalHydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {B : Type} [DecidableEq B] [LinearOrder B]
variable [O : LeanDag.OptimalHydrozoan.OptimalFaults Replica]

/-- **Leader exclusion survives re-genesis.** The new block is at round
zero, so it is bound by no exclusion; and it is its author's only
block, so it can be no second candidate of a witnessed equivocation and
no parent of anything old. Every old block's witnesses and parents are
unchanged. -/
theorem leaderExcludedAll_addGenesisHZ {U : LeanDag.Hydrozoan.BlockUniverse Replica B}
    (hU : LeaderExcludedAll U) {v : Replica} {g : B} {hg : g ∉ U.ids}
    {hsev : ∀ b ∈ U.ids, (U.block b).author ≠ v} :
    LeaderExcludedAll (addGenesisHZ U v g hg hsev) := by
  intro b hb u h2 hwit j hj
  rcases Finset.mem_insert.mp hb with rfl | hbU
  · rw [addGenesisHZ_block_new] at h2
    simp at h2
  · rw [addGenesisHZ_block_old hbU] at h2 hwit hj
    have hjU := U.complete b hbU j hj
    rw [addGenesisHZ_block_old hjU]
    obtain ⟨L₁, L₂, hL₁, hL₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩ := hwit
    have hj₁' : j₁ ∈ (U.block b).parents := by rwa [addGenesisHZ_block_old hbU] at hj₁
    have hj₂' : j₂ ∈ (U.block b).parents := by rwa [addGenesisHZ_block_old hbU] at hj₂
    by_cases huv : u = v
    · subst huv
      have hc : ∀ L, IsCandidateAt (addGenesisHZ U u g hg hsev) ((U.block b).round - 2) u L →
          L = g := by
        rintro L ⟨hLm, -, hLa⟩
        rcases Finset.mem_insert.mp hLm with rfl | hLU
        · rfl
        · rw [addGenesisHZ_block_old hLU] at hLa
          exact absurd hLa (hsev L hLU)
      exact absurd ((hc L₁ hL₁).trans (hc L₂ hL₂).symm) hne
    · have hcand : ∀ L, IsCandidateAt (addGenesisHZ U v g hg hsev) ((U.block b).round - 2) u L →
          IsCandidateAt U ((U.block b).round - 2) u L := by
        rintro L ⟨hLm, hLr, hLa⟩
        rcases Finset.mem_insert.mp hLm with rfl | hLU
        · rw [addGenesisHZ_block_new] at hLa
          exact absurd hLa.symm huv
        · rw [addGenesisHZ_block_old hLU] at hLr hLa
          exact ⟨hLU, hLr, hLa⟩
      have hvote : ∀ j ∈ (U.block b).parents, ∀ L,
          LeanDag.Hydrozoan.IsVote (addGenesisHZ U v g hg hsev) j L →
          LeanDag.Hydrozoan.IsVote U j L := by
        intro j hj L hv
        have hjU := U.complete b hbU j hj
        unfold LeanDag.Hydrozoan.IsVote at hv ⊢
        rw [addGenesisHZ_block_old hjU] at hv
        exact hv
      exact hU b hbU u h2 ⟨L₁, L₂, hcand L₁ hL₁, hcand L₂ hL₂, hne,
        ⟨j₁, hj₁', hvote j₁ hj₁' L₁ hv₁⟩, ⟨j₂, hj₂', hvote j₂ hj₂' L₂ hv₂⟩⟩ j hj

variable {U : (OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := B)).Universe}
variable {v : Replica} {g : B}
variable {hg : g ∉ U.val.ids} {hsev : ∀ b ∈ U.val.ids, (U.val.block b).author ≠ v}

/-- **Re-genesis, at Optimal-Hydrozoan's carrier.** -/
def addGenesisOpt (U : (OptimalHydrozoanProperties.optimalRule (Replica := Replica)
    (BlockId := B)).Universe) (v : Replica) (g : B)
    (hg : g ∉ U.val.ids) (hsev : ∀ b ∈ U.val.ids, (U.val.block b).author ≠ v) :
    (OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := B)).Universe :=
  ⟨addGenesisHZ U.val v g hg hsev, leaderExcludedAll_addGenesisHZ U.property⟩

theorem extends_addGenesis_opt :
    Extends (OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := B))
      U (addGenesisOpt U v g hg hsev) :=
  let h := extends_addGenesisHZ (U := U.val) (v := v) (g := g) (hg := hg) (hsev := hsev)
  { subset := h.subset, block := h.block }

theorem sustains_addGenesis_opt :
    Sustains (OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := B))
      U (addGenesisOpt U v g hg hsev) 0 1 :=
  let h := sustains_addGenesisHZ (U := U.val) (v := v) (g := g) (hg := hg) (hsev := hsev)
  { mem := h.mem, round := h.round, creator := h.creator, refs := h.refs }

/-- **Verdicts survive re-genesis, for Optimal-Hydrozoan** — the cell
the fill could not have, because re-genesis adds no edge. -/
theorem decided_addGenesis_opt (S : Slots Replica) {V : LeanDag.Hydrozoan.View U.val}
    {V' : LeanDag.Hydrozoan.View (addGenesisOpt U v g hg hsev).val} (hsub : V.ids ⊆ V'.ids)
    {k : ℕ} {u : Option B}
    (h : (OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := B)).Decided
      S V k u) :
    (OptimalHydrozoanProperties.optimalRule (Replica := Replica) (BlockId := B)).Decided
      S V' k u :=
  Persist.of_banded OptimalHydrozoanProperties.banded S U _ extends_addGenesis_opt V V' hsub k u h

end Optimal

end Integration

end LeanDag
