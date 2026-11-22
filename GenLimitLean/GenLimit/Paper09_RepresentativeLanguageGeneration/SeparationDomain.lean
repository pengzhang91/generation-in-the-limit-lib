import GenLimit.Paper09_RepresentativeLanguageGeneration.Results.Overview
import GenLimit.Paper09_RepresentativeLanguageGeneration.Results.Supporting

/-! # Corollary 3.6 on a prescribed example space -/
namespace GenLimit.RepresentativeGeneration.Published

/-- The separation exists on precisely the infinite countable example
spaces. The countable class omits one point from the second infinite group.
Any sample entirely in this group makes all its unobserved points unavailable. -/
theorem corollary_3_6_iff_infinite (α : Type*) [Countable α] :
    (∃ H : Generic.LanguageClass α, ∃ groups : Fin 2 → Set α,
      H.Countable ∧ Generic.UUS H ∧ IsFinitePartition groups ∧
      Generic.UniformlyGeneratable H ∧
      ¬ RepresentativelyUniformlyGeneratable H (extendFinitePartition groups)) ↔ Infinite α := by
  classical
  constructor
  · rintro ⟨H,g,_,_,hp,hu,hn⟩
    by_contra h
    letI := not_infinite_iff_finite.mp h
    exact hn (no_corollary_3_6_separation_on_finite H g hp hu)
  · intro hα
    letI := hα
    let e := Infinite.natEmbedding α
    let R : Set α := Set.range (fun n : ℕ ↦ e (2*n))
    have hr : R.Infinite := Set.infinite_range_of_injective (fun a b he ↦ by
      have := e.injective he; omega)
    have hl : Rᶜ.Infinite := by
      refine (Set.infinite_range_of_injective (f := fun n ↦ e (2*n+1)) ?_).mono ?_
      · intro a b he
        have := e.injective he
        omega
      · rintro _ ⟨a,rfl⟩ ⟨b,hb⟩
        have := e.injective hb
        omega
    let H : Generic.LanguageClass α := (fun x : α ↦ ({x} : Set α)ᶜ) '' R
    let groups : Fin 2 → Set α := fun i ↦ if i = 0 then R else Rᶜ
    have hp : IsFinitePartition groups := by
      apply isFinitePartition_of_pairwise_iUnion
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [groups] <;> exact Set.disjoint_left.mpr (by aesop)
      · ext x
        simpa [groups, Fin.exists_fin_succ] using em (x ∈ R)
    have inside (L : Set α) (hL : L ∈ H) : Rᶜ ⊆ L := by
      obtain ⟨x,hx,rfl⟩ := hL
      intro y hy he
      exact hy ((Set.mem_singleton_iff.mp he).symm ▸ hx)
    have hf (t : ℕ) (xs : Fin t → α) := hl.exists_notMem_finset (Generic.sequenceSample xs)
    let G : Generic.Generator α := fun t xs ↦ (hf t xs).choose
    refine ⟨H,groups,(Set.to_countable R).image _,fun L hL ↦ hl.mono (inside L hL),
      hp,⟨G,0,?_⟩,?_⟩
    · intro L hL s _ t _ u _
      refine ⟨inside L hL (hf u _).choose_spec.1, ?_⟩
      simpa only [Generic.output, G, Generic.sequenceSample_prefix] using
        (hf u (fun i ↦ s i)).choose_spec.2
    · intro hg
      obtain ⟨d,hd⟩ := (alphaRepresentativeUniformlyGeneratable_iff_finite_groupClosureDimension
        (groups := extendFinitePartition groups) hp (by norm_num : (0 : ℝ) < 1/2)).1
        (hg _ (by norm_num) (by norm_num))
      obtain ⟨S,hS,hcard⟩ := hr.exists_subset_card_eq (d+1)
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      have hgroup : extendFinitePartition groups 0 = R := by simp [extendFinitePartition,groups]
      obtain ⟨y,hy,hfresh⟩ := hr.exists_notMem_finset S
      have hcon (y : α) (hy : y ∈ R) (hfresh : y ∉ S) :
          ({y} : Set α)ᶜ ∈ consistentHypotheses H S :=
        ⟨⟨y,hy,rfl⟩, fun x hx he ↦ hfresh ((Set.mem_singleton_iff.mp he) ▸ hx)⟩
      have hbad : 0 ∈ unavailableGroups H (extendFinitePartition groups) S := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨⟨hcore,hfresh⟩,hx⟩
        rw [hgroup] at hx
        exact hcore _ (hcon x hx hfresh) (Set.mem_singleton x)
      have hem : empiricalGroupProbability S (extendFinitePartition groups) 0 = 1 := by
        rw [empiricalGroupProbability, if_pos hne, hgroup,
          Finset.filter_true_of_mem (fun x hx ↦ hS hx)]
        exact div_self (by exact_mod_cast hne.card_pos.ne')
      have hb := hd S ⟨hne, ⟨_,hcon y hy hfresh⟩, Or.inl ⟨0,hbad,by rw [hem]; norm_num⟩⟩
      omega

end GenLimit.RepresentativeGeneration.Published
