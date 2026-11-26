import GenLimit.Paper25_PrivateGenerationAndIdentification.PackingFamily
import GenLimit.Paper25_PrivateGenerationAndIdentification.EpochGeneration

/-! A corrected order lower bound for Theorem 1.3, valid at every collection
size k ≥ 2. Marginal bit success suffices; no simultaneous-success assumption
is imposed on compatible target languages. -/
namespace GenLimit.PrivateLimit.Packing

open Privacy Set MeasureTheory
open scoped Classical ENNReal
noncomputable section

def UniformFrom (M : ContinualRelease ℕ ℕ) (C : Set (Set ℕ)) (m : ℕ) : Prop :=
  ∀ K ∈ C, ∀ s : ℕ → ℕ, Function.Injective s → range s = K →
    2/3 ≤ (M.law s).real (Epoch.failsAfter K s (m-1))ᶜ

private def labelAt (h d t : ℕ) (y : ℕ → ℕ) := decode h d (y t)

private theorem label_measurable (h d t : ℕ) (F : Set (Cube h)) :
    MeasurableSet (labelAt h d t ⁻¹' F) := by
  have ev : Measurable (fun y : ℕ → ℕ => y t) := measurable_pi_apply t
  exact ev (show MeasurableSet ((decode h d) ⁻¹' F) from .of_discrete)

private def mass {h : ℕ} (M : ContinualRelease ℕ ℕ) (d t : ℕ) (s : ℕ → ℕ) (w : Cube h) :=
  (M.law s).real (labelAt h d t ⁻¹' {w})

private theorem mass_event {h : ℕ} (M : ContinualRelease ℕ ℕ) (d t : ℕ) (s : ℕ → ℕ)
    (F : Finset (Cube h)) :
    (∑ w ∈ F, mass M d t s w) = (M.law s).real (labelAt h d t ⁻¹' (↑F : Set (Cube h))) := by
  letI := M.probability s
  exact sum_measureReal_preimage_singleton F (fun w _ => label_measurable _ _ _ {w})

private theorem mass_unit {h : ℕ} (M : ContinualRelease ℕ ℕ) (d t : ℕ) (s : ℕ → ℕ) :
    ∑ w : Cube h, mass M d t s w = 1 := by
  letI := M.probability s
  rw [mass_event]; simp

private theorem compatible_bit {h d m n : ℕ} {odd : Bool} (M : ContinualRelease ℕ ℕ)
    (ok : UniformFrom M (family h d odd) m) (hn : 0 < n) (hm : m ≤ n) (hd : d ≤ n)
    (z : Cube h) (i : Fin h) :
    2/3 ≤ ∑ w : Cube h, if z i = w i then mass M d (n-1) (columnText d z) w else 0 := by
  let K := language d (i,z i)
  obtain ⟨full,cert,agree⟩ := NoiseLossFeedback.exactEnumeration_extending_prefix
    (infinite_language d (i,z i)) ⟨column_injective d z,column_legal z i⟩ n
  let F := Finset.univ.filter fun w : Cube h => z i = w i
  have e : (∑ w ∈ F, mass M d (n-1) (columnText d z) w) =
      ∑ w : Cube h, if z i = w i then mass M d (n-1) (columnText d z) w else 0 := Finset.sum_filter ..
  rw [←e,mass_event]
  let B := (decode h d) ⁻¹' (↑F : Set (Cube h))
  have transfer := M.marginal_congr (n-1) (u := full) (v := columnText d z)
    (fun j hj => agree ⟨j,by omega⟩) (B := B) MeasurableSet.of_discrete
  change 2/3 ≤ (M.law (columnText d z)).real {y | y (n-1) ∈ B}
  rw [Measure.real_def,←transfer]
  letI := M.probability full
  apply (ok K (language_mem ..) full cert.1 cert.2).trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro y hy
  have good : y (n-1) ∉ Epoch.badWord K full n := by
    intro bad
    apply hy
    refine mem_iUnion.mpr ⟨(n-1)-(m-1),?_⟩
    rw [Nat.add_sub_of_le (by omega : m-1 ≤ n-1),show n-1+1=n by omega]
    exact bad
  have member : y (n-1) ∈ K := Classical.not_not.mp (fun H => good (Or.inl H))
  have outside : ¬ y (n-1) < d := by
    intro small
    let j := y (n-1)
    have a := agree (⟨j,by dsimp [j]; omega⟩ : Fin n)
    have seen : full j = y (n-1) := by simpa [j,columnText,small] using a
    exact good (Or.inr (Epoch.mem_observations.mpr ⟨j,by dsimp [j]; omega,seen⟩))
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(member.resolve_left outside).symm⟩

private theorem atom_domination {h d n : ℕ} {ε : ℝ} (M : ContinualRelease ℕ ℕ)
    (dp : DifferentiallyPrivate ε 0 M.law) (hn : 0 < n) (z v w : Cube h) :
    mass M d (n-1) (columnText d z) w ≤
      Real.exp ((n-d:ℕ)*ε)*mass M d (n-1) (columnText d v) w := by
  let mixed j := if j < n then columnText d z j else columnText d v j
  let edits := Finset.Ico d n
  let B := (decode h d) ⁻¹' {w}
  let E := labelAt h d (n-1) ⁻¹' {w}
  have same (a) (ha : a ∉ edits) : mixed a = columnText d v a := by
    by_cases before : a < n
    · have small : a < d := by
        by_contra! ge
        exact ha (Finset.mem_Ico.mpr ⟨ge,before⟩)
      simp [mixed,before,columnText,small]
    · simp [mixed,before]
  have pr := group_privacy dp edits same (E := E) (label_measurable ..)
  have tr : M.law (columnText d z) E = M.law mixed E :=
    M.marginal_congr (n-1) (fun j hj => (if_pos (by omega : j < n)).symm) (B := B) MeasurableSet.of_discrete
  letI := M.probability (columnText d v)
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (measure_ne_top _ _)) pr
  change (M.law (columnText d z) E).toReal ≤ _; rw [tr]
  simpa only [mass,Measure.real_def,edits,Nat.card_Ico,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (Real.exp_pos ε).le,Real.exp_nat_mul] using ht

theorem family_lower {h d : ℕ} (hh : 0 < h) (odd : Bool) {ε : ℝ} (he : 0 < ε)
    (M : ContinualRelease ℕ ℕ) (dp : DifferentiallyPrivate ε 0 M.law) (m : ℕ) (hm : 0 < m)
    (ok : UniformFrom M (family h d odd) m) : d+coefficient*h/ε ≤ (m:ℝ) := by
  let n := max d m
  have dn : d ≤ n := le_max_left ..; have mn : m ≤ n := le_max_right ..
  let v : Cube h := fun _ => false
  let p (z w : Cube h) := mass M d (n-1) (columnText d z) w
  let q (w : Cube h) := mass M d (n-1) (columnText d v) w
  have lower := marginal_packing p q ((n-d:ℕ)*ε) (fun _ _ => measureReal_nonneg)
    (fun _ => mass_unit ..) (mass_unit ..) (compatible_bit M ok (hm.trans_le mn) mn dn)
    (fun z w => atom_domination M dp (hm.trans_le mn) z v w)
  have md : d ≤ m := by
    by_contra! small
    have eq : n-d = 0 := by dsimp [n]; omega
    rw [eq,Nat.cast_zero,zero_mul] at lower
    exact (mul_pos coefficient_pos (by exact_mod_cast hh)).not_ge lower
  rw [show n=m from max_eq_right md,Nat.cast_sub md] at lower
  apply (le_sub_iff_add_le'.mp ((div_le_iff₀ he).mpr lower))

/-- The corrected size range includes both even and odd k. The exact
dimension is witnessed by intersecting the whole family. -/
theorem corrected_lower (k d : ℕ) (hk : 2 ≤ k) :
    ∃ C : Set (Set ℕ), C.Finite ∧ C.ncard = k ∧ (∀ L ∈ C, L.Infinite) ∧
      SubcollectionClosureBound C d ∧ (⋂₀ C).Finite ∧ (⋂₀ C).ncard = d ∧
      ∀ (ε : ℝ), 0 < ε → ∀ M : ContinualRelease ℕ ℕ, DifferentiallyPrivate ε 0 M.law →
        ∀ m : ℕ, 0 < m → UniformFrom M C m → d+(coefficient/3)*k/ε ≤ (m:ℝ) := by
  let h := k/2
  let odd := decide (k%2=1)
  have hh : 0 < h := by dsimp [h]; omega
  refine ⟨family h d odd,family_finite ..,?_,fun _ => family_infinite h d odd,family_bound h d odd,?_,?_,?_⟩
  · rw [family_size]; dsimp [h,odd]; split <;> simp_all <;> omega
  · rw [full_intersection hh]; exact finite_Iio _
  · rw [full_intersection hh,←Finset.coe_range,ncard_coe_finset,Finset.card_range]
  · intro ε he M dp m hm ok
    apply le_trans _ (family_lower hh odd he M dp m hm ok)
    have ratio : (k:ℝ) ≤ 3*(h:ℝ) := by exact_mod_cast (show k ≤ 3*h by dsimp [h]; omega)
    have le : coefficient/3*k ≤ coefficient*h := by nlinarith [mul_le_mul_of_nonneg_left ratio coefficient_pos.le]
    gcongr

end
end GenLimit.PrivateLimit.Packing
