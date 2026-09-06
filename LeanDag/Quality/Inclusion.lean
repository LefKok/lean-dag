import LeanDag.Quality.Coverage
import LeanDag.DoS.Exclusion
import LeanDag.MysticetiProperties

/-!
# Chain quality: post-synchrony inclusion

`chain-quality.md` §4, CQP2 — **CQ5**, **CQ6**. The aggregate coverage
of `Coverage.lean` upgrades to an *individual* guarantee — every correct
block enters the agreed ledger — at the price of the synchrony round
`R`, and only at that price: the witness file carries a model in which
commits recur for ever while the same correct validator is missing from
every flushed layer, so the upgrade is genuinely conditional, not a
proof gap.

The engine is the backbone (`mem_history_of_correct`): post-`R`, a
correct block is in the cone of every correct block at every later
round. Composition with commit recurrence (L6) then puts it in the
ledger, with the committing slot supplied by the fair schedule.

A scoping note, recorded in the design document: the schedule side is
`T ⊆ Correct`-relative, but the backbone consumes Correct-wide
coverage, so the theorems here take full `Synchronised U R`. A
`T`-relative variant would need a `T`-relative backbone lemma — possible
but not attempted in this arc.

**Both results are instances.** `Properties/Arcs/Quality.lean` states
them for any rule with `Causal`, `Quorate`, `CommitsCandidate` and
`LeaderCommits`; what is left here is the bridge from the core's
populated-and-synchronous hypotheses to its own `coreLive`, which is the
same shape `Barnacle.GoodOf` has for Barnacle and mentions no
verdict.
-/

namespace LeanDag

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {T : Finset Validator} {b L : BlockId} {R m : ℕ}

/-- **CQ5.** Post-`R`, every correct block is in the cone of **every**
committed leader block with a correct author at a later round — any
commit route, any view. The backbone does all the work. -/
theorem mem_history_of_decided_commit (hs : Synchronised U R)
    {V : View Validator BlockId Payload U} {k : ℕ}
    (hdec : Decided U V k (some L))
    (hLc : (U.block L).creator ∈ (Correct : Finset Validator))
    (hb : b ∈ U.ids) (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    (hR : R ≤ (U.block b).round)
    (hlt : (U.block b).round < (U.block L).round) :
    b ∈ history U L :=
  Properties.Arcs.mem_history_of_decided_commit
    (R := MysticetiProperties.mysticetiRule) MysticetiProperties.quorate MysticetiProperties.commitsCandidate hs hdec hLc hb hbc hR hlt

/-- **A slot whose commit carries a whole round into the ledger.**

The conclusion CQ6 and its refinements share: in any sufficiently grown
synchronous execution, slot `k` commits a leader whose history contains
every correct round-`m` block, and every such block is in the agreed
ledger from any later position. Naming it keeps the quantifier order
visible — `k` is fixed by the schedule before an execution is named — as
`CommitsAt` does for the recurrence results. -/
def IncludesAt (BlockId : Type) [DecidableEq BlockId] (Payload : Type)
    [S : Slots Validator] (R m k : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
    (∀ r ≤ N, Populated U r) → Synchronised U R →
    S.slotRound k + 2 ≤ N →
    ∃ L, Decided U (View.full U) k (some L) ∧
      ∀ b ∈ U.ids,
        (U.block b).creator ∈ (Correct : Finset Validator) →
        (U.block b).round = m →
        b ∈ history U L ∧
        ∀ (g : ℕ → Option BlockId) (n : ℕ), g k = some L → k < n →
          b ∈ ledgerSet U g n

/-- **CQ6 (inclusion liveness).** Under a fair schedule over reliable
validators and post-`R` synchrony, for every round `m ≥ R` there is a
committed slot — above `m`, led by a correct validator — whose flush
contains **every** correct round-`m` block; hence every such block is
in the agreed ledger of any verdict assignment covering that slot.

The slot is produced *before* the universe is quantified, exactly as in
L6: the schedule fixes it, and any sufficiently grown synchronous DAG
then commits it. -/
theorem committed_of_correct_block (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R m : ℕ) (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧
      IncludesAt (Validator := Validator) BlockId Payload R m k' := by
  obtain ⟨k', hm, hRk', hbody⟩ :=
    Properties.Arcs.committed_of_correct_block
      (R := MysticetiProperties.mysticetiRule (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload))
      MysticetiProperties.quorate
      MysticetiProperties.commitsCandidate MysticetiProperties.leaderCommits S hT fair R m hRm
  refine ⟨k', hm, hRk', ?_⟩
  intro U N hpop hs hN
  have hwin : ∀ j, j < k' + 1 → S.slotRound j + 2 ≤ N := by
    intro j hj
    have := S.mono (Nat.lt_succ_iff.mp hj)
    omega
  exact hbody U (View.full U)
    ⟨hcard, R, N, hs.mono hT, hRk',
      (fun r _ hr => PopulatedOn.mono hT (hpop r hr)), View.coversUpto_full U N, hwin⟩ hs

/-- **CQ6 at `T := Correct`.** -/
theorem committed_of_correct_block_correct
    (fair : FairScheduleOn (Correct : Finset Validator)) (R m : ℕ)
    (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧
      IncludesAt (Validator := Validator) BlockId Payload R m k' :=
  committed_of_correct_block Finset.Subset.rfl card_correct fair R m hRm

end LeanDag
