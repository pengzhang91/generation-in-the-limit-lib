import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankGeneration

/-! Transport of the finite-rank guarantee to an arbitrary prescribed
enumeration of the universe, as in Corollary 4.7. -/
namespace GenLimit.KleinbergWei.Banach
open Set DensityMeasures DensityMeasures.FiniteRankParent
open scoped Classical ENNReal
noncomputable section

private theorem successor_at (C : LanguageFamily) (z n : ℕ) :
    familyPoint C z ∈ TowerTopology.cbDerivative (range C) (n+1) ↔
      familyPoint C z ∈ TowerTopology.cbDerivative (range C) n ∧
        ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ C z →
          ∃ i, familyPoint C i ∈ TowerTopology.cbDerivative (range C) n ∧
            C i ≠ C z ∧ (↑F : Set ℕ) ⊆ C i ∧ C i ⊆ C z := by
  constructor
  · rintro ⟨previous,limit⟩
    refine ⟨previous,fun F inside => ?_⟩
    obtain ⟨⟨_,i,rfl⟩,mem,ne,contains,sub⟩ := limit F inside
    exact ⟨i,mem,fun eq => ne (Subtype.ext eq),contains,sub⟩
  · rintro ⟨previous,limit⟩
    refine ⟨previous,fun F inside => ?_⟩
    obtain ⟨i,mem,ne,contains,sub⟩ := limit F inside
    exact ⟨familyPoint C i,mem,fun eq => ne (congrArg Subtype.val eq),contains,sub⟩

theorem finiteRank_reorder (C : LanguageFamily) (e : ℕ ≃ ℕ) {R : ℕ}
    (hr : TowerTopology.FiniteRankAtMost (range C) R) :
    TowerTopology.FiniteRankAtMost (range fun i => e ⁻¹' C i) R := by
  let D : LanguageFamily := fun i => e ⁻¹' C i
  have transport (n z : ℕ) : familyPoint D z ∈ TowerTopology.cbDerivative (range D) n →
      familyPoint C z ∈ TowerTopology.cbDerivative (range C) n := by
    induction n generalizing z with
    | zero => simp
    | succ n ih =>
      rw [successor_at,successor_at]
      rintro ⟨mem,limit⟩
      refine ⟨ih z mem, fun F inside => ?_⟩
      have inside' : (↑(F.image e.symm) : Set ℕ) ⊆ D z := by
        intro x hx
        obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
        simpa [D] using inside ha
      obtain ⟨i,old,ne,contains,sub⟩ := limit _ inside'
      refine ⟨i,ih i old,fun eq => ne (congrArg (fun S => e ⁻¹' S) eq),?_,
        e.surjective.preimage_subset_preimage_iff.mp sub⟩
      intro a ha
      have hit := contains (Finset.mem_image_of_mem e.symm ha)
      simpa [D] using hit
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ⟨_,i,rfl⟩ mem
  exact Set.eq_empty_iff_forall_notMem.mp hr _ (transport R i mem)

/-- Generate original words while measuring ranks in the prescribed order e. -/
theorem reordered_generation (C : LanguageFamily) (inf : ∀ z, (C z).Infinite)
    {R : ℕ} (hr : TowerTopology.FiniteRankAtMost (range C) R) (e : ℕ ≃ ℕ) :
    ∃ A : List ℕ → ℕ, ∀ z s, Presents s (C z) →
      OrderedFocus.ElementValid s (OrderedFocus.play A s) (C z) ∧
      ENNReal.ofReal (1/2) ≤ lowerBanachDensity
        ((OrderedLanguage.increasing (e ⁻¹' C z) ((inf z).preimage (fun x _ => e.surjective x))).rankSet
          (e ⁻¹' range (OrderedFocus.play A s))) := by
  let D : LanguageFamily := fun i => e ⁻¹' C i
  obtain ⟨G,spec⟩ := finite_rank_generation D (fun z => (inf z).preimage (fun x _ => e.surjective x))
    (finiteRank_reorder C e hr)
  let A (h : List ℕ) := e (G (h.map e.symm))
  refine ⟨A,fun z s pres => ?_⟩
  let r := e.symm ∘ s
  have pr : Presents r (D z) := by
    change range (e.symm ∘ s) = e ⁻¹' C z
    rw [range_comp,show range s = C z from pres]
    ext x; constructor
    · rintro ⟨a,ha,rfl⟩
      simpa using ha
    · intro h
      exact ⟨e x,h,e.symm_apply_apply x⟩
  have play (t) : OrderedFocus.play A s t = e (OrderedFocus.play G r t) := by
    simp [OrderedFocus.play,A,r,textPrefix,List.map_map]
  obtain ⟨⟨T,good⟩,density⟩ := spec z r pr
  refine ⟨⟨T,fun t ht => ?_⟩,?_⟩
  · obtain ⟨inK,fresh,new⟩ := good t ht
    rw [play]
    refine ⟨inK,fun i hi eq => fresh i hi ?_,fun i hi eq => new i hi ?_⟩
    · simpa [r] using congrArg e.symm eq
    · rw [play] at eq
      exact e.injective eq
  · have same : e ⁻¹' range (OrderedFocus.play A s) = range (OrderedFocus.play G r) := by
      ext x; constructor
      · rintro ⟨t,h⟩
        exact ⟨t,e.injective ((play t).symm.trans h)⟩
      · rintro ⟨t,rfl⟩
        exact ⟨t,play t⟩
    simpa only [same] using density

end
end GenLimit.KleinbergWei.Banach
