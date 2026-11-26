import GenLimit.Paper32_InfinitelyManyHallucinations.RawValidity
import GenLimit.Paper32_InfinitelyManyHallucinations.PartialRace
import GenLimit.Paper15_PartialEnumeration.Results.Overview
import GenLimit.Paper32_InfinitelyManyHallucinations.BoundedPrecision
import GenLimit.Paper32_InfinitelyManyHallucinations.Diagnostics
import GenLimit.Paper32_InfinitelyManyHallucinations.NoNovelty
import GenLimit.Paper32_InfinitelyManyHallucinations.NoNoveltyExploration

/-! # Supporting statements and earlier certificate interfaces for P32 -/

namespace GenLimit.InfinitelyManyHallucinations.Results

alias lemma_2_2 :=
  GenLimit.InfinitelyManyHallucinations.lemma_2_2

alias proposition_2_4_single_step :=
  GenLimit.InfinitelyManyHallucinations.proposition_2_4_singleStep

alias proposition_2_4_constant_step :=
  GenLimit.InfinitelyManyHallucinations.proposition_2_4_constantStep

alias proposition_3_3 :=
  GenLimit.InfinitelyManyHallucinations.proposition_3_3

alias lemma_4_7 :=
  GenLimit.InfinitelyManyHallucinations.lemma_4_7

alias lemma_4_5_of_trace_certificate :=
  GenLimit.InfinitelyManyHallucinations.lemma_4_5_of_certificate

alias theorem_4_8_of_trace_certificate :=
  GenLimit.InfinitelyManyHallucinations.theorem_4_8_of_certificate

alias theorem_4_9_of_trace_certificate :=
  GenLimit.InfinitelyManyHallucinations.theorem_4_9_of_certificate

alias theorem_3_5_fixed_pod_endgame :=
  GenLimit.KleinbergWei.PartialEnumeration.Results.theorem_3_5_fixed_pod_endgame

alias appendix_valid_generation_without_novelty :=
  GenLimit.InfinitelyManyHallucinations.valid_generation_without_novelty

alias gamma_admissible_exploration_exists :=
  GenLimit.InfinitelyManyHallucinations.exists_gammaAdmissible_explorationSet

alias tail_precision_one_finite_guess_counterexample :=
  GenLimit.InfinitelyManyHallucinations.tail_precision_one_finite_guess_counterexample

alias appendix_lemma_D_1_of_limit_infinite :=
  GenLimit.InfinitelyManyHallucinations.appendix_lemma_D_1_of_limit_infinite

alias theorem_E_1_copying := GenLimit.InfinitelyManyHallucinations.valid_generation_without_novelty

open Set
open KleinbergWei.PartialEnumeration.Sharpness (natural)

/-- One full presentation of a smaller infinite language has the prescribed
recall inside the whole universe. The same presentation gives the sharp
upper bound for every generator with a finite batch cap and perfect tail
precision on the smaller target. -/
theorem theorem_E_1_I_3_upper {α : ℝ} (hα : α ∈ Icc 0 1) :
    ∃ A : Exhaustion, A.IsSingleStep ∧ A.limit.Infinite ∧ lowerRecall natural A.limit = α ∧
      ∀ (G : BatchGenerator) (c : ℕ), (generatedExhaustion G A).BoundedBy (fun _ => c) →
        lowerTailPrecision A.limit (generatedExhaustion G A) = 1 →
        lowerRecall natural (generatedExhaustion G A).limit ≤ α := by
  obtain ⟨A,hs,hi,ha,_⟩ := BatchedRace.lemma_4_6 hα.1 hα.2 1 (by decide) (fun _ _ _ => ∅)
  exact ⟨A,hs,hi,ha,fun G _ hb ht => (bounded_tail_recall_upper G A natural hb ht).trans_eq ha⟩

end GenLimit.InfinitelyManyHallucinations.Results
