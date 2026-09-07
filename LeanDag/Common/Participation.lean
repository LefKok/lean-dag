import LeanDag.Common.BlockRecord
/-!
# Participation predicates

`PopulatedFrom` and `SynchronisedFrom`, stated over the raw block assignment
and id population — the fault-agnostic data every universe type carries.
Neither predicate mentions validity, quorums, or a fault model, so pinning
them to a universe type would only thread an unused instance through their
statements; stated over the data, the Byzantine `BlockUniverse` and the
crash `Nemo.Universe` instantiate one definition instead of restating it.
-/

namespace LeanDag

variable {Validator : Type*} {BlockId : Type*} {Payload : Type*}
variable {blk : BlockId → Block Validator BlockId Payload} {ids : Finset BlockId}

/-- Every validator in `T` authors a block at round `r` among `ids`. -/
def PopulatedFrom (blk : BlockId → Block Validator BlockId Payload)
    (ids : Finset BlockId) (T : Finset Validator) (r : ℕ) : Prop :=
  ∀ v ∈ T, ∃ b ∈ ids, (blk b).creator = v ∧ (blk b).round = r

/-- Decidable on concrete data: a bounded quantifier over two `Finset`s, so a
model can settle it by `decide`. -/
instance decidablePopulatedFrom [DecidableEq Validator]
    (T : Finset Validator) (r : ℕ) : Decidable (PopulatedFrom blk ids T r) :=
  inferInstanceAs (Decidable (∀ v ∈ T, ∃ b ∈ ids,
    (blk b).creator = v ∧ (blk b).round = r))

/-- Population is antitone: a smaller set is easier to populate. -/
theorem PopulatedFrom.mono {T T' : Finset Validator} {r : ℕ} (hsub : T ⊆ T')
    (h : PopulatedFrom blk ids T' r) : PopulatedFrom blk ids T r :=
  fun v hv => h v (hsub hv)

/-- From round `R` on, every `T`-authored block references every `T`-authored
block of the round below. Both quantifiers restricted to `T`, deliberately. -/
def SynchronisedFrom (blk : BlockId → Block Validator BlockId Payload)
    (ids : Finset BlockId) (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ ids, (blk b).round = n + 1 → (blk b).creator ∈ T →
    ∀ a ∈ ids, (blk a).round = n → (blk a).creator ∈ T → a ∈ (blk b).refs

/-- Coverage is antitone too: mutual coverage among a larger set implies it
among any subset. -/
theorem SynchronisedFrom.mono {T T' : Finset Validator} {R : ℕ} (hsub : T ⊆ T')
    (h : SynchronisedFrom blk ids T' R) : SynchronisedFrom blk ids T R :=
  fun n hn b hb hbr hbc a ha har hac => h n hn b hb hbr (hsub hbc) a ha har (hsub hac)

/-! ## At the record

The two predicates at a block record's data, which is how every rule's
liveness hypotheses state them. `T` is a set of validators rather than
all of the honest ones: a liveness result counts to a quorum and never
higher, and demanding every honest validator would make it lapse when
one misses one round. -/

section Record

variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- Every validator in `T` has a block at round `r`. -/
def PopulatedOn (U : BlockRecord Validator BlockId Payload P honest)
    (T : Finset Validator) (r : ℕ) : Prop :=
  PopulatedFrom U.block U.ids T r

/-- Decidable on concrete data, so a model can settle it by `decide`. -/
instance decidablePopulatedOn [DecidableEq Validator] (T : Finset Validator) (r : ℕ) :
    Decidable (PopulatedOn U T r) :=
  inferInstanceAs (Decidable (PopulatedFrom U.block U.ids T r))

/-- Population is antitone: a smaller set is easier to populate. -/
theorem PopulatedOn.mono {T T' : Finset Validator} {r : ℕ} (hsub : T ⊆ T')
    (h : PopulatedOn U T' r) : PopulatedOn U T r :=
  PopulatedFrom.mono hsub h

/-- From round `R` on, every `T`-authored block references every
`T`-authored block of the round below. An assumption about the network
after stabilisation, not a theorem: a block's references are frozen
when it is built. -/
def SynchronisedOn (U : BlockRecord Validator BlockId Payload P honest)
    (T : Finset Validator) (R : ℕ) : Prop :=
  SynchronisedFrom U.block U.ids T R

/-- Coverage is antitone too. -/
theorem SynchronisedOn.mono {T T' : Finset Validator} {R : ℕ} (hsub : T ⊆ T')
    (h : SynchronisedOn U T' R) : SynchronisedOn U T R :=
  SynchronisedFrom.mono hsub h

end Record

end LeanDag
