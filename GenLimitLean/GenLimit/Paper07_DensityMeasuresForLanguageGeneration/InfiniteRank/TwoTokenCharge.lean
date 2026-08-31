import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfiniteRank.PrefixCharge

/-!
# Two-token consumption gives strict prefix dominance

The infinite-rank Kleinberg--Wei argument reserves two physical strings for
each retained long-run position.  A reservation can disappear in exactly two
ways: a generator output consumes it, or an adversary input consumes it and
the output at that round receives the charge.

This module isolates the exact finite counting principle.  Physical tokens
are globally unique, every token hits an earlier output position, and the hit
map is injective separately within the two consumption classes.  Although an
output can therefore receive one hit from each class, the two tokens owned by
every retained position compensate for that capacity two.  The resulting
strict prefix dominance feeds the canonical rank matching in `PrefixCharge`.

The classwise hit-injectivity fields are semantic obligations of the dynamic
algorithm; they are not inferred merely from freshness of the reservation
ledger.
-/

open Set

namespace GenLimit.KleinbergWei.DensityMeasures.InfiniteRank

/-- The two ways in which a reserved token can cease to be available. -/
inductive TokenConsumption
  | output
  | input
  deriving DecidableEq

/-- Positions of a set that occur strictly before `n`. -/
noncomputable def positionPrefix (S : Set ℕ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (· ∈ S)

/-- Two abstract slots owned by every member of `source`. -/
def twoTokenPairs {α : Type*} [DecidableEq α] (source : Finset α) :
    Finset (α × Bool) :=
  source.product Finset.univ

/-- Pure finite counting core.

Each source element owns two slots.  Every slot hits the target, and the hit
map is injective separately on output-consumed and input-consumed slots.
Consequently a target can be hit at most twice, once from each class. -/
theorem card_le_of_two_token_consumption
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (source : Finset α) (target : Finset β)
    (consumption : α × Bool → TokenConsumption)
    (hit : α × Bool → β)
    (hit_mem :
      ∀ p ∈ twoTokenPairs source, hit p ∈ target)
    (output_injective :
      Set.InjOn hit
        ((twoTokenPairs source).filter
          (fun p => consumption p = .output)))
    (input_injective :
      Set.InjOn hit
        ((twoTokenPairs source).filter
          (fun p => consumption p = .input))) :
    source.card ≤ target.card := by
  let pairs := twoTokenPairs source
  let outputPairs := pairs.filter (fun p => consumption p = .output)
  let inputPairs := pairs.filter (fun p => consumption p = .input)
  have houtput_maps : Set.MapsTo hit outputPairs target := by
    intro p hp
    exact hit_mem p (Finset.mem_filter.mp hp).1
  have hinput_maps : Set.MapsTo hit inputPairs target := by
    intro p hp
    exact hit_mem p (Finset.mem_filter.mp hp).1
  have houtput_card : outputPairs.card ≤ target.card :=
    Finset.card_le_card_of_injOn hit houtput_maps output_injective
  have hinput_card : inputPairs.card ≤ target.card :=
    Finset.card_le_card_of_injOn hit hinput_maps input_injective
  have hpairs_partition :
      outputPairs.card + inputPairs.card = pairs.card := by
    classical
    simp only [outputPairs, inputPairs, pairs]
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext p
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hp, -⟩ | ⟨hp, -⟩)
        · exact hp
        · exact hp
      · intro hp
        cases hclass : consumption p with
        | output => exact Or.inl ⟨hp, by simp⟩
        | input => exact Or.inr ⟨hp, by simp⟩
    · refine Finset.disjoint_left.mpr ?_
      intro p hpOutput hpInput
      have hOutput := (Finset.mem_filter.mp hpOutput).2
      have hInput := (Finset.mem_filter.mp hpInput).2
      rw [hOutput] at hInput
      cases hInput
  have hpairs_card : pairs.card = 2 * source.card := by
    simp [pairs, twoTokenPairs, Nat.mul_comm]
  omega

/-- Physical tokens owned by retained positions. -/
def ownedTokens
    {Token : Type*} (retained : Set ℕ) (token : ℕ → Bool → Token) :
    Set Token :=
  {x | ∃ i ∈ retained, ∃ side, token i side = x}

/-- A backward two-token charge certificate.

The two reservations of each retained position are globally distinct.
Every reservation is consumed either by a generator output or by an
adversary input; in the latter case `hit` is the output paired with that input
round.  The two classwise injectivity fields state exactly that an output can
be charged at most once in each way. -/
structure TwoTokenCharge
    (retained output : Set ℕ) (Token : Type*) where
  token : ℕ → Bool → Token
  token_injective :
    ∀ ⦃i j : ℕ⦄, i ∈ retained → j ∈ retained →
      ∀ ⦃side side' : Bool⦄,
        token i side = token j side' → i = j ∧ side = side'
  consumption : Token → TokenConsumption
  hit : Token → ℕ
  hit_output :
    ∀ ⦃i : ℕ⦄, i ∈ retained → ∀ side, hit (token i side) ∈ output
  hit_earlier :
    ∀ ⦃i : ℕ⦄, i ∈ retained → ∀ side, hit (token i side) < i
  output_hit_injective :
    Set.InjOn hit
      (ownedTokens retained token ∩ {x | consumption x = .output})
  input_hit_injective :
    Set.InjOn hit
      (ownedTokens retained token ∩ {x | consumption x = .input})

namespace TwoTokenCharge

/-- Every retained prefix through position `n` fits in the strictly preceding
output prefix. -/
theorem strict_positionPrefix_card_le
    {retained output : Set ℕ} {Token : Type*}
    (C : TwoTokenCharge retained output Token) (n : ℕ) :
    (positionPrefix retained (n + 1)).card ≤
      (positionPrefix output n).card := by
  classical
  let source := positionPrefix retained (n + 1)
  let target := positionPrefix output n
  let pairToken : ℕ × Bool → Token := fun p => C.token p.1 p.2
  let pairConsumption : ℕ × Bool → TokenConsumption :=
    fun p => C.consumption (pairToken p)
  let pairHit : ℕ × Bool → ℕ := fun p => C.hit (pairToken p)
  have source_mem_retained {i : ℕ} (hi : i ∈ source) : i ∈ retained := by
    have hi' : i ∈ positionPrefix retained (n + 1) := by
      simpa [source] using hi
    exact (Finset.mem_filter.mp hi').2
  have source_le_n {i : ℕ} (hi : i ∈ source) : i ≤ n := by
    have hi' : i ∈ positionPrefix retained (n + 1) := by
      simpa [source] using hi
    exact Nat.le_of_lt_succ
      (by
        simpa [Nat.succ_eq_add_one] using
          Finset.mem_range.mp (Finset.mem_filter.mp hi').1)
  have hpairs_mem :
      ∀ p ∈ twoTokenPairs source, pairHit p ∈ target := by
    intro p hp
    have hpSource : p.1 ∈ source := (Finset.mem_product.mp hp).1
    have hpRetained : p.1 ∈ retained := source_mem_retained hpSource
    have hhitOutput : pairHit p ∈ output :=
      C.hit_output hpRetained p.2
    have hhitLt : pairHit p < p.1 :=
      C.hit_earlier hpRetained p.2
    have : pairHit p ∈ positionPrefix output n :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr
            (lt_of_lt_of_le hhitLt (source_le_n hpSource)),
          hhitOutput⟩
    simpa [target] using this
  have lift_injective
      (which : TokenConsumption)
      (hphysical :
        Set.InjOn C.hit
          (ownedTokens retained C.token ∩
            {x | C.consumption x = which})) :
      Set.InjOn pairHit
        ((twoTokenPairs source).filter
          (fun p => pairConsumption p = which)) := by
    intro p hp q hq heq
    have hpPair : p ∈ twoTokenPairs source :=
      (Finset.mem_filter.mp hp).1
    have hqPair : q ∈ twoTokenPairs source :=
      (Finset.mem_filter.mp hq).1
    have hpSource : p.1 ∈ source := (Finset.mem_product.mp hpPair).1
    have hqSource : q.1 ∈ source := (Finset.mem_product.mp hqPair).1
    have hpRetained : p.1 ∈ retained := source_mem_retained hpSource
    have hqRetained : q.1 ∈ retained := source_mem_retained hqSource
    have hpOwned : pairToken p ∈ ownedTokens retained C.token :=
      ⟨p.1, hpRetained, p.2, rfl⟩
    have hqOwned : pairToken q ∈ ownedTokens retained C.token :=
      ⟨q.1, hqRetained, q.2, rfl⟩
    have hpClass : C.consumption (pairToken p) = which :=
      (Finset.mem_filter.mp hp).2
    have hqClass : C.consumption (pairToken q) = which :=
      (Finset.mem_filter.mp hq).2
    have htoken : pairToken p = pairToken q :=
      hphysical ⟨hpOwned, hpClass⟩ ⟨hqOwned, hqClass⟩ heq
    obtain ⟨hindex, hside⟩ :=
      C.token_injective hpRetained hqRetained htoken
    exact Prod.ext hindex hside
  exact card_le_of_two_token_consumption
    source target pairConsumption pairHit hpairs_mem
    (lift_injective .output C.output_hit_injective)
    (lift_injective .input C.input_hit_injective)

/-- Two-token consumption supplies the exact strict-prefix inequality used by
the canonical rank matching. -/
theorem strictPrefixDominance
    {retained output : Set ℕ} {Token : Type*}
    (C : TwoTokenCharge retained output Token) :
    StrictPrefixDominance retained output := by
  intro i _
  simpa [positionPrefix, positionPrefixCount] using
    C.strict_positionPrefix_card_le i

end TwoTokenCharge

/-- Package run thinning and a two-token consumption certificate as the
injective long-run charge consumed by the one-eighth endgame. -/
noncomputable def LongBadCharge.ofRunThinningOfTwoTokenCharge
    (K : OrderedLanguage) (Output Long : Language)
    (retained : Set ℕ)
    (C :
      RunThinning.Certificate
        (RunThinning.orderedPositions K Long) retained)
    (exceptions : Finset ℕ)
    {Token : Type*}
    (tokens :
      TwoTokenCharge
        (retained \ (exceptions : Set ℕ))
        (RunThinning.orderedPositions K Output)
        Token) :
    LongBadCharge K Output Long :=
  LongBadCharge.ofRunThinningOfPrefixDominance
    K Output Long retained C exceptions
    tokens.strictPrefixDominance

end GenLimit.KleinbergWei.DensityMeasures.InfiniteRank
