import LeanDag.GC.Bootstrap

/-!
# The horizon policy: heterogeneous cuts, one truth

`garbage.md` **G8** and **G9** — what "slightly different horizons are
fine" means as theorems, in a model with no per-validator clocks.

The design resisted running consensus on `G`: horizons need not be equal,
only admissible. Three facts make that safe, and they are what this file
proves:

* **`chop_chop`** — the composition law: a deeper cut is just another
  cut, `chop (chop U G₁) (G₂ − G₁) = chop U G₂`. Validators at different
  admissible horizons do not inhabit incomparable worlds; the deeper
  validator's universe is a further truncation of the shallower one's,
  and every transfer theorem composes along the tower. This is the
  model's form of the skew story (G8): the *relation* between two
  horizons is always the one operator, whatever the offsets.
* **`decided_agree_horizons`** — G8's agreement content: validators
  truncated at *different* horizons `G₁, G₂`, holding arbitrary views of
  their respective truncations, agree on every shared slot. Each agrees
  with the full history (`decided_agree_chop`), and slots are matched
  through their absolute index `d₁ + k₁ = d₂ + k₂`. The full-history
  verdict the two are compared against exists under liveness — L8/L10
  (`all_decided_below_of_fairRun`) decide every slot below a committed
  run, which is also what discharges admissibility invariant A1.
* **`viewUpto_subset_viewUpto_succ`** — G9's engine, the depth rule:
  post-`R`, everything **any** correct validator retains by round `m` is
  in **every** correct validator's store by `m + 1`. Possession is
  universal one round deep, so a horizon trailing a correct frontier by
  `Λ ≥ 1` discards nothing any correct peer still lacks —
  `pruned_subset_peer_store` states the pruned set's containment
  explicitly. A validator outside the envelope — partitioned, crashed,
  joining — is by definition on the bootstrap path, where the attested
  base (G10–G12) takes over.

**A deviation, recorded.** The prose G8 promised "frontiers differ by at
most the commit lag". This model is round-synchronous — `Populated` gives
every correct validator a block each round, and views are static
snapshots with no clock — so a quantitative clock-skew constant has no
carrier here. What the model *can* say, it says exactly: verdicts are
horizon-independent (agreement), horizons compose (`chop_chop`), and
possession universalises in one round (the depth bound). The timing
constant lives where timing lives: in `liveness.md`'s discussion of `R`.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {D : Delivery U} {v w : Validator} {G : ℕ}

/-! ## G8 — the composition law -/

private theorem block_eq_of {b₁ b₂ : Block Validator BlockId Payload}
    (hr : b₁.round = b₂.round) (hc : b₁.creator = b₂.creator)
    (hf : b₁.refs = b₂.refs) (hp : b₁.payload = b₂.payload) : b₁ = b₂ := by
  cases b₁; cases b₂
  simp_all

private theorem universe_eq_of {U₁ U₂ : BlockUniverse Validator BlockId Payload}
    (hids : U₁.ids = U₂.ids) (hblock : U₁.block = U₂.block) : U₁ = U₂ := by
  cases U₁; cases U₂
  cases hids; cases hblock
  rfl

theorem chopBlk_chop {G₁ G₂ : ℕ} (hG : G₁ ≤ G₂) (i : BlockId) :
    chopBlk (chop U G₁).block (G₂ - G₁) i = chopBlk U.block G₂ i := by
  refine block_eq_of ?_ ?_ ?_ ?_
  · rw [chopBlk_round, chopBlk_round, chop_block_eq, chopBlk_round]
    omega
  · rw [chopBlk_creator, chopBlk_creator, chop_block_eq, chopBlk_creator]
  · rcases Nat.lt_or_ge G₂ (U.block i).round with h2 | h2
    · rw [chopBlk_refs_of_lt (by rw [chop_block_eq, chopBlk_round]; omega),
        chopBlk_refs_of_lt h2, chop_block_eq,
        chopBlk_refs_of_lt (by omega)]
    · rw [chopBlk_refs_of_le (by rw [chop_block_eq, chopBlk_round]; omega),
        chopBlk_refs_of_le h2]
  · rw [chopBlk_payload, chopBlk_payload, chop_block_eq, chopBlk_payload]

/-- **G8, the composition law.** A deeper cut is just another cut: two
admissible horizons are always related by the one operator, so every
transfer theorem composes along the tower of truncations. -/
theorem chop_chop {G₁ G₂ : ℕ} (hG : G₁ ≤ G₂) :
    chop (chop U G₁) (G₂ - G₁) = chop U G₂ := by
  refine universe_eq_of ?_ (funext (chopBlk_chop hG))
  ext i
  rw [mem_chop_ids, mem_chop_ids, mem_chop_ids, chop_block_eq, chopBlk_round]
  constructor
  · rintro ⟨⟨hi, h1⟩, h2⟩
    exact ⟨hi, by omega⟩
  · rintro ⟨hi, h2⟩
    exact ⟨⟨hi, by omega⟩, by omega⟩

/-! ## G8 — agreement across heterogeneous horizons

`decided_agree_horizons` stood here, chaining G4 twice. It is now
`Properties.Arcs.decided_agree_horizons_chop`, the same statement from
`Agree` and `LocalTruncate`, and holds for any rule with a band rather
than for the core alone. -/

/-! ## G9 — the depth rule -/

/-- **G9, the engine.** Post-`R`, everything **any** correct validator
retains by round `m` is in **every** correct validator's store by
`m + 1`: the keeper's round-`(m + 1)` block carries its whole store
(`viewUpto_subset_history`, S10 + `includes`), and post-`R` that block is
delivered to and accepted by every correct validator. Possession is
universal one round deep. -/
theorem viewUpto_subset_viewUpto_succ {R m : ℕ}
    (hED : EventuallyDelivers D R) (hcar : Populated U (m + 1))
    (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) (hR : R ≤ m + 1) :
    viewUpto D v m ⊆ viewUpto D w (m + 1) := by
  obtain ⟨b, hb, hbc, hbr⟩ := hcar v hv
  have hacc : b ∈ D.accepted w (m + 1) :=
    D.accepts_correct w hw (m + 1) b
      (hED (m + 1) hR w hw b hb hbr (by rw [hbc]; exact hv))
      (by rw [hbc]; exact hv)
  exact (viewUpto_subset_history hv hb hbc hbr).trans
    (history_subset_viewUpto (le_refl _) hacc)

/-- **G9 (no desync).** What a validator prunes at any horizon, every
correct peer already holds one round later: pruning below a correct
frontier at depth `Λ ≥ 1` discards nothing a correct peer still lacks.
A validator outside the envelope is on the bootstrap path, where the
attested base takes over (G10–G12). -/
theorem pruned_subset_peer_store {R m : ℕ}
    (hED : EventuallyDelivers D R) (hcar : Populated U (m + 1))
    (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) (hR : R ≤ m + 1) :
    (viewUpto D v m).filter (fun i => (U.block i).round < G) ⊆
      viewUpto D w (m + 1) :=
  (Finset.filter_subset _ _).trans
    (viewUpto_subset_viewUpto_succ hED hcar hv hw hR)

end LeanDag
