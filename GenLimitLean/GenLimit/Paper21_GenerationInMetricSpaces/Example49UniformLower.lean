import GenLimit.Paper21_GenerationInMetricSpaces.Example49Negative

/-!
# Example 4.9: finite second-family samples exclude a uniform threshold

The orthogonal covering estimate supplies an arbitrarily large finite
sample. Two disjoint completions force the generator's output into that
already observed finite common part.
-/

namespace GenLimit.MetricSpaces.HilbertAxisReservoir.Example49

open GenLimit.Generic GenLimit.Support

noncomputable section

def finiteTarget (ε : ℝ) (J : Set ℕ) : Set Hilbert2 :=
  {0} ∪ {x | ∃ k ∈ J, x = B ε k}

def finiteFamily (ε : ℝ) : LanguageClass Hilbert2 :=
  {L | ∃ J : Set ℕ, J.Finite ∧ J ⊆ indices ∧ L = finiteTarget ε J}

theorem finite_completions {r ε₁ ε₂ ε' : ℝ} {L : Set Hilbert2}
    (hL : L ∈ finiteFamily ε₂) (i : Fin 2) :
    L ∪ twoCompletions r ε₁ ε' i ∈ family r ε₁ ε₂ ε' := by
  obtain ⟨J, hJ, hJK, rfl⟩ := hL
  refine ⟨primePowers i.val, primePowers i.val, J,
    Example48Rows.powers_infinite _, Example48Rows.powers_infinite _, hJ,
    primePowers_subset _, primePowers_subset _, hJK, ?_⟩
  ext x
  simp only [finiteTarget, twoCompletions, completion, target, Set.mem_union, Set.mem_setOf_eq]
  aesop

theorem not_uniform_of_small_adversary {r ε₁ ε₂ ε' γ γ' : ℝ}
    (hr : 0 < r) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hε' : 0 < ε')
    (hγ : 0 ≤ γ) (hγε₂ : γ < ε₂) (hγ' : 0 ≤ γ') :
    ¬ UniformlyGeneratableAt dist γ γ' (family r ε₁ ε₂ ε') := by
  classical
  rintro ⟨gen, d, hgen⟩
  have hfinite : IsUniformGeneratorAt dist γ γ' gen (finiteFamily ε₂) d :=
    uniform_threshold_transfer (by decide : 0 < 2) (twoCompletions r ε₁ ε')
      (twoCompletions_empty hr hε₁ hε') (fun _ hL i => finite_completions hL i) hgen
  let C : Set Hilbert2 := Set.range (fun k : ℕ => B ε₂ (k + 2))
  have hC : C.Infinite := axis_range_infinite hε₂.ne' (fun k => 4 * (k + 2) + 2)
    (by intro m n hmn; dsimp only at hmn; omega)
  obtain ⟨S, hSC, hSlarge⟩ := infinite_orthogonal_has_large_finite_sample hC hε₂ hγ hγε₂
    (axis_range_norm hε₂.le _) (axis_range_orthogonal ε₂ _) d
  have hBinj : Function.Injective (B ε₂) := by
    intro i j hij
    have hc := (axisPoint_eq_axisPoint_of_left_ne_zero hε₂.ne' hij).2
    omega
  let J : Set ℕ := (B ε₂) ⁻¹' (S : Set Hilbert2)
  have hJ : J.Finite := S.finite_toSet.preimage hBinj.injOn
  have hJK : J ⊆ indices := by
    intro k hk
    obtain ⟨n, hn⟩ := hSC hk
    have heq : n + 2 = k := hBinj hn
    change 2 ≤ k
    omega
  have htarget : finiteTarget ε₂ J = ({0} : Set Hilbert2) ∪ (S : Set Hilbert2) := by
    ext x
    constructor
    · rintro (hz | ⟨k, hk, rfl⟩)
      · exact Or.inl hz
      · exact Or.inr hk
    · rintro (hz | hx)
      · exact Or.inl hz
      · obtain ⟨n, hn⟩ := hSC hx
        change B ε₂ (n + 2) = x at hn
        exact Or.inr ⟨n + 2, show B ε₂ (n + 2) ∈ S from hn.symm ▸ hx, hn.symm⟩
  let xs := 0 :: S.toList
  let stream : Stream Hilbert2 := prependStream xs (fun _ => 0)
  have hstream : StreamIn stream (finiteTarget ε₂ J) := by
    rw [htarget]
    intro x hx
    rw [range_prependStream] at hx
    rcases hx with hx | ⟨n, rfl⟩
    · simpa [xs] using hx
    · exact Or.inl rfl
  have hseen : finiteTarget ε₂ J ⊆ (sample stream xs.length : Set Hilbert2) := by
    rw [htarget]
    intro x hx
    have hxs : x ∈ xs := by simpa [xs] using hx
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hxs
    exact mem_sample_iff.mpr ⟨i, i.isLt,
      (prependStream_apply_of_lt xs (fun _ => 0) i.isLt).trans hi⟩
  have hCN : CoveringNumberAtLeast dist γ (sample stream xs.length : Set Hilbert2) d :=
    coveringNumberAtLeast_mono_set (fun x hx => hseen (by rw [htarget]; exact Or.inr hx)) hSlarge
  have hcorrect := hfinite _ ⟨J, hJ, hJK, rfl⟩ stream hstream xs.length hCN xs.length le_rfl
  apply hcorrect.2
  intro η hη
  exact ⟨output gen stream xs.length, hseen hcorrect.1, by
    rw [dist_self]
    exact hγ'.trans_lt hη⟩

end
end GenLimit.MetricSpaces.HilbertAxisReservoir.Example49
