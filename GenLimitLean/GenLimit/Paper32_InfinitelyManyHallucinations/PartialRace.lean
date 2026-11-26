import GenLimit.Paper32_InfinitelyManyHallucinations.BatchedRace
import GenLimit.Paper32_InfinitelyManyHallucinations.ValidRepetition
import Mathlib.Data.Finset.Preimage
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.VanishingBreadth

/-! # Batched upper bound on a partially revealed target

Run the full adversary in the ranks of a language of density α. The
simulated generator reports exactly the original increments falling inside
that language. Perfect tail precision on the smaller target permits only
finitely many extra outputs on the common transcript.
-/

namespace GenLimit.InfinitelyManyHallucinations.BatchedRace
open Set Filter KleinbergWei KleinbergWei.PartialEnumeration.Sharpness
open scoped Classical Topology

private def embed (f : ℕ ↪ ℕ) (A : Exhaustion) : Exhaustion where
  stage n := (A.stage n).map f
  stage_zero := by simp [A.stage_zero]
  monotone_stage := fun _ _ h => Finset.map_subset_map.mpr (A.monotone_stage h)

private theorem embed_limit (f : ℕ ↪ ℕ) (A : Exhaustion) :
    (embed f A).limit = f '' A.limit := by
  ext x
  constructor
  · rintro ⟨n,h⟩
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp h
    exact ⟨y,⟨n,hy⟩,rfl⟩
  · rintro ⟨y,⟨n,hy⟩,rfl⟩
    exact ⟨n,Finset.mem_map.mpr ⟨y,hy,rfl⟩⟩

private theorem embed_bound (f : ℕ ↪ ℕ) {A : Exhaustion} {k : ℕ}
    (h : A.BoundedBy (fun _ => k)) : (embed f A).BoundedBy (fun _ => k) := by
  intro n
  simpa [Exhaustion.increment,embed,← Finset.map_sdiff] using h n

private noncomputable def projection (f : ℕ ↪ ℕ) (G : BatchGenerator) : StageRule :=
  fun A n _ => ((generatedExhaustion G (embed f A)).increment n).preimage f f.injective.injOn

private theorem projection_causal (f : ℕ ↪ ℕ) (G : BatchGenerator) : (projection f G).Causal := by
  intro A B n hp _
  have h := increment_prefix G (A := embed f A) (B := embed f B)
    (n := n) (fun i hi => congrArg (Finset.map f) (hp i hi))
  simp only [projection,h]

private theorem projected_stage (f : ℕ ↪ ℕ) (G : BatchGenerator) (A : Exhaustion) (n x : ℕ) :
    x ∈ (generatedExhaustion (projection f G).toBatch A).stage n ↔
      f x ∈ (generatedExhaustion G (embed f A)).stage n := by
  induction n with
  | zero => simp [Exhaustion.stage_zero]
  | succ n ih =>
    change x ∈ generatedStages _ A n ∪ (projection f G).toBatch (n+1) _ _ ↔ _
    rw [StageRule.toBatch_apply (projection_causal f G) A,
      (generatedExhaustion G (embed f A)).stage_succ_eq_stage_union_increment]
    simp only [Finset.mem_union,projection,Finset.mem_preimage]
    exact or_congr ih Iff.rfl

private theorem projected_increment (f : ℕ ↪ ℕ) (G : BatchGenerator) (A : Exhaustion) (n x : ℕ) :
    x ∈ (generatedExhaustion (projection f G).toBatch A).increment n ↔
      f x ∈ (generatedExhaustion G (embed f A)).increment n := by
  cases n with
  | zero => simp
  | succ n => simp only [Exhaustion.increment,Finset.mem_sdiff,projected_stage]

private theorem projection_novel (f : ℕ ↪ ℕ) (G : BatchGenerator) (A : Exhaustion)
    (h : GeneratorNovel G (embed f A)) : Novel A (generatedExhaustion (projection f G).toBatch A) := by
  intro n
  rw [Finset.disjoint_left]
  intro x hx ha
  exact Finset.disjoint_left.mp (h.traceNovel n) ((projected_increment f G A n x).mp hx)
    (Finset.mem_map.mpr ⟨x,ha,rfl⟩)

private theorem projection_single (f : ℕ ↪ ℕ) (G : BatchGenerator) (A : Exhaustion)
    (h : (generatedExhaustion G (embed f A)).IsSingleStep) :
    (generatedExhaustion (projection f G).toBatch A).IsSingleStep := by
  intro n
  apply Finset.card_le_one.mpr
  intro x hx y hy
  exact f.injective (Finset.card_le_one.mp (h n) _ ((projected_increment f G A _ x).mp hx)
    _ ((projected_increment f G A _ y).mp hy))

private theorem image_upper {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1) {D : Set ℕ} (k : ℕ)
    (hk : 0 < k) (bound : ∀ n, (k+1)*natural.prefixCount D n ≤ n+n.sqrt+1) :
    natural.upperDensity (thin α '' D) ≤ α/((k:ℝ)+1) := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun n => natural.prefixRatio_nonneg _ n))
  filter_upwards [small_error 0 hδ,eventually_ge_atTop 1] with n he hn
  let m := ⌈(n : ℝ)*α⌉₊
  have hm : m ≤ n := Nat.ceil_le.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hceil : (m : ℝ) < (n : ℝ)*α+1 := Nat.ceil_lt_add_one (by positivity)
  have hsq : (m.sqrt : ℝ) ≤ n.sqrt := by exact_mod_cast Nat.sqrt_le_sqrt hm
  rw [OrderedLanguage.prefixRatio,if_neg (by omega),prefix_image ha ha1]
  apply (div_le_iff₀ hpos).mpr
  have hc : ((k:ℝ)+1) * (natural.prefixCount D m : ℝ) ≤ m + m.sqrt + 1 := by
    exact_mod_cast bound m
  change (natural.prefixCount D m : ℝ) ≤ _
  have two : (2:ℝ) ≤ (k:ℝ)+1 := by exact_mod_cast (show 2 ≤ k+1 by omega)
  have eps := mul_le_mul_of_nonneg_right two (mul_nonneg hδ.le hpos.le)
  have den : 0 < (k:ℝ)+1 := by positivity
  have cancel := div_mul_cancel₀ α den.ne'
  apply (mul_le_mul_iff_right₀ den).mp
  nlinarith [congrArg (fun v : ℝ => v*n) cancel]

private theorem thin_recall {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1) :
    lowerRecall natural (Set.range (thin α)) = α := by
  let D := Set.range (thin α)
  have ratio (n : ℕ) (hn : 0 < n) : natural.prefixRatio D n ≤ α+1/(n:ℝ) := by
    rw [OrderedLanguage.prefixRatio, if_neg hn.ne']
    change (natural.prefixCount (Set.range (thin α)) n : ℝ) / n ≤ _
    rw [← Set.image_univ,prefix_image ha ha1]
    simp only [Set.mem_univ,Finset.filter_true,Finset.card_range]
    have hp : 0 < (n:ℝ) := by exact_mod_cast hn
    apply (div_le_iff₀ hp).mpr
    have := Nat.ceil_lt_add_one (by positivity : 0 ≤ (n:ℝ)*α)
    rw [add_mul,div_mul_cancel₀ _ hp.ne']
    linarith
  have lim : Tendsto (fun n : ℕ => α+1/(n:ℝ)) atTop (𝓝 α) := by
    simpa using (tendsto_const_nhds (x := α)).add (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
  refine le_antisymm ?_ (thin_density_ge ha ha1)
  change liminf (natural.prefixRatio D) atTop ≤ α
  rw [← lim.liminf_eq]
  exact liminf_le_liminf (eventually_atTop.mpr ⟨1,fun n hn => ratio n hn⟩)
    (isBoundedUnder_of ⟨0,natural.prefixRatio_nonneg D⟩) lim.isCoboundedUnder_ge

/-- Lemma 4.6 on partial inputs of any prescribed positive density threshold.
The same adversarial history is valid for both targets. -/
theorem batched_partial_upper {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1)
    (k : ℕ) (hk : 0 < k) (G : BatchGenerator) :
    ∃ A : Exhaustion, A.BoundedBy (fun _ => k) ∧ A.limit.Infinite ∧
      lowerRecall natural A.limit = α ∧
      (GeneratorNovel G A → (generatedExhaustion G A).IsSingleStep →
       lowerTailPrecision A.limit (generatedExhaustion G A) = 1 →
       upperRecall natural (generatedExhaustion G A).limit ≤ α/((k:ℝ)+1)) := by
  let f : ℕ ↪ ℕ := ⟨thin α,(thin_strict ha ha1).injective⟩
  let P := (projection f G).toBatch
  let B := adversary k P
  let A := embed f B
  have full : B.limit = Set.univ := (block_limit hk _).trans (presents _)
  have image : A.limit = Set.range f := by rw [embed_limit,full,Set.image_univ]
  refine ⟨A,embed_bound f (block_bound k _),image ▸ Set.infinite_range_of_injective f.injective,
    image ▸ thin_recall ha ha1, ?_⟩
  intro hn hs ht
  let g := generatedExhaustion G A
  let r := generatedExhaustion P B
  have sub : g.limit \ (g.limit \ A.limit) ⊆ f '' r.limit := by
    rintro x ⟨⟨n,hx⟩,remain⟩
    have hxA : x ∈ A.limit := by
      by_contra hh
      exact remain ⟨⟨n,hx⟩,hh⟩
    rw [image] at hxA
    obtain ⟨y,rfl⟩ := hxA
    exact ⟨y,⟨n,(projected_stage f G B n y).mpr hx⟩,rfl⟩
  have cap := image_upper ha ha1 k hk (prefix_bound_batched k hk P
    (projection_novel f G B hn) (projection_single f G B hs))
  have bound := (natural.upperDensity_mono sub).trans cap
  rwa [natural.upperDensity_diff_finite _ (bounded_tail_finite_errors G A hs ht)] at bound

/-- A family containing the revealed language and the whole universe
gives the sharp upper bound at every input recall, including zero. -/
theorem lemma_4_6 {α : ℝ} (ha : 0 ≤ α) (ha1 : α ≤ 1)
    (k : ℕ) (hk : 0 < k) (G : BatchGenerator) :
    ∃ A : Exhaustion, A.BoundedBy (fun _ => k) ∧ A.limit.Infinite ∧
      lowerRecall natural A.limit = α ∧
      (GeneratorNovel G A → (generatedExhaustion G A).IsSingleStep →
       lowerTailPrecision A.limit (generatedExhaustion G A) = 1 →
       upperRecall natural (generatedExhaustion G A).limit ≤ α/((k:ℝ)+1)) := by
  rcases ha.eq_or_lt with h | h
  · subst α
    let A := blocks k (fun n => n*n)
    have sq : A.limit = DensityMeasures.SquareTower.squares := by
      rw [block_limit hk]; ext x
      rfl
    have zero : natural.upperDensity A.limit = 0 := sq ▸ DensityMeasures.SquareTower.squares_upperDensity
    have low : lowerRecall natural A.limit = 0 := by
      refine le_antisymm (le_trans ?_ zero.le) (lowerRecall_nonneg ..)
      exact liminf_le_limsup (isBoundedUnder_of ⟨1,natural.prefixRatio_le_one _⟩)
        (isBoundedUnder_of ⟨0,natural.prefixRatio_nonneg _⟩)
    refine ⟨A,block_bound k _,sq ▸ DensityMeasures.SquareTower.squares_infinite,low,?_⟩
    intro _ hs ht
    let g := generatedExhaustion G A
    have sub : g.limit \ (g.limit \ A.limit) ⊆ A.limit := by
      intro x hx
      by_contra h
      exact hx.2 ⟨hx.1,h⟩
    have cap := natural.upperDensity_mono sub
    rwa [natural.upperDensity_diff_finite _ (bounded_tail_finite_errors G A hs ht),zero,
      ← zero_div ((k:ℝ)+1)] at cap
  · exact batched_partial_upper h ha1 k hk G

end GenLimit.InfinitelyManyHallucinations.BatchedRace
