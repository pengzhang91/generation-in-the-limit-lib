import GenLimit.Paper17_InfiniteContamination.ActivePrefixes
import GenLimit.Paper17_InfiniteContamination.BoundedDisplacement
import GenLimit.Core.CanonicalDensity

/-! # Sharp noise threshold for finite families (Theorem B.3)

The initial k common words keep every prefix noise fraction below or equal
to 1/k, including prefixes whose lengths are not multiples of k.
-/

namespace GenLimit.InfiniteContamination
open Filter

private def residueLanguage (k i : ℕ) : Set ℕ := {x | x < k ∨ x % k ≠ i}

private theorem residue_noiseCount_le (k : ℕ) (hk : 0 < k) (i n : ℕ) :
    noiseCount id (residueLanguage k i) n ≤ n / k := by
  classical
  unfold noiseCount
  rw [← Finset.card_range (n/k)]
  apply Finset.card_le_card_of_injOn (fun x : ℕ ↦ x / k - 1)
  · intro x hx
    obtain ⟨hx, hbad⟩ := Finset.mem_filter.mp hx
    have hle : x/k ≤ n/k := Nat.div_le_div_right (Finset.mem_range.mp hx).le
    have hxk : k ≤ x := Nat.le_of_not_gt (fun h ↦ hbad (Or.inl h))
    have hpos : 0 < x/k := Nat.div_pos hxk hk
    apply Finset.mem_range.mpr
    change x / k - 1 < n / k
    omega
  · intro x hx y hy he
    obtain ⟨_,hbx⟩ := Finset.mem_filter.mp hx
    obtain ⟨_,hby⟩ := Finset.mem_filter.mp hy
    have hx' : k ≤ x := Nat.le_of_not_gt (fun h ↦ hbx (Or.inl h))
    have hy' : k ≤ y := Nat.le_of_not_gt (fun h ↦ hby (Or.inl h))
    have hmodx : x % k = i := by by_contra h; exact hbx (Or.inr h)
    have hmody : y % k = i := by by_contra h; exact hby (Or.inr h)
    have hd : x/k = y/k := by
      have := Nat.div_pos hx' hk
      have := Nat.div_pos hy' hk
      change x/k-1 = y/k-1 at he
      omega
    have ex := Nat.mod_add_div x k
    have ey := Nat.mod_add_div y k
    rw [hmodx,hd] at ex
    rw [hmody] at ey
    exact ex.symm.trans ey

private theorem residue_constantNoise (k : ℕ) (hk : 0 < k) (i : ℕ) :
    ConstantNoise id (residueLanguage k i) (1/k) := by
  refine ⟨1,fun n hn ↦ ?_⟩
  simp only [empiricalNoiseRate, if_neg (Nat.ne_of_gt hn)]
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [div_le_div_iff₀ hn' hk', one_mul]
  exact_mod_cast (Nat.mul_le_mul_right k (residue_noiseCount_le k hk i n)).trans (Nat.div_mul_le_self n k)

/-- Even at the equality endpoint, one full enumeration is admissible for
all k distinct targets but their common core is finite. -/
private theorem residue_class_obstruction (k : ℕ) (hk : 2 ≤ k) :
    ∃ family : Fin k → Set ℕ, Function.Injective family ∧ (∀ i, (family i).Infinite) ∧
      (∀ i, ConstantNoiseEnumeration id (family i) (1/k)) ∧
        ¬∃ gen : Generic.Generator ℕ, ∀ i, GeneratesElementInLimitOn gen (family i) id := by
  classical
  let f := fun i : Fin k ↦ residueLanguage k i
  have hpos : 0 < k := by omega
  refine ⟨f,?_,?_,fun i ↦ ⟨Function.injective_id, fun x _ ↦ ⟨x,rfl⟩, residue_constantNoise k hpos i⟩,?_⟩
  · intro i j he
    by_contra hij
    have hmod : (k + i.val) % k = i.val := by simp [Nat.mod_eq_of_lt i.isLt]
    have hnot : k+i.val ∉ f i := by simp [f, residueLanguage, hmod]
    apply hnot
    rw [he]
    exact Or.inr (fun h ↦ hij (Fin.ext (hmod.symm.trans h)))
  · intro i
    obtain ⟨r,hr,hrne⟩ : ∃ r : ℕ, r < k ∧ r ≠ i.val := by
      by_cases hz : i.val = 0
      · exact ⟨1,by omega,by omega⟩
      · exact ⟨0,hpos,Ne.symm hz⟩
    let seq := fun n : ℕ ↦ r + k*n
    have hinj : Function.Injective seq := fun x y he ↦
      Nat.eq_of_mul_eq_mul_left hpos (Nat.add_left_cancel he)
    apply (Set.infinite_range_of_injective hinj).mono
    rintro _ ⟨n,rfl⟩
    exact Or.inr (by simpa [seq, Nat.add_mod, Nat.mod_eq_of_lt hr] using hrne)
  · rintro ⟨gen,hgen⟩
    let F := Finset.univ.image f
    let i : Fin k := ⟨0,hpos⟩
    have hi : (finiteCommonCore F).Infinite := simultaneous_fresh_generation_infinite_core gen id F
      ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩ (by
        rintro L hL
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hL
        exact hgen j)
    apply hi
    apply (Set.finite_Iio k).subset
    intro x hx
    let j : Fin k := ⟨x%k, Nat.mod_lt _ hpos⟩
    exact (hx (f j) (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)).resolve_right (by simp [j])

open GenLimit.KleinbergWei

/-- Corrected Theorem 7.7. The same full stream defeats every generator
even with displacement factor one, hence also at Example 7.2's factor
one plus one over k. -/
theorem finiteClass_bounded_obstruction (k : ℕ) (hk : 2 ≤ k) (M : ℝ) (hM : 1 ≤ M) :
    ∃ K : Fin k → OrderedLanguage, Function.Injective (fun i ↦ (K i).carrier) ∧
      ∃ s : Generic.Stream ℕ, (∀ i, ConstantNoiseEnumeration s (K i).carrier (1/k) ∧
        BoundedDisplacement (K i) s (K i).carrier M) ∧
        ¬∃ gen : Generic.Generator ℕ, ∀ i, GeneratesElementInLimitOn gen (K i).carrier s := by
  obtain ⟨f,hf,hinf,henum,hbad⟩ := residue_class_obstruction k hk
  let K := fun i ↦ OrderedLanguage.canonical (f i) (hinf i)
  refine ⟨K,hf,id,fun i ↦ ⟨henum i,0,fun n _ ↦ ?_⟩,hbad⟩
  have hn : (canonicalRank (K i) (K i).carrier n : ℝ) ≤ n+1 := by
    by_cases hx : n ∈ (K i).carrier
    · rw [canonicalRank_carrier _ hx]
      have hh := (OrderedLanguage.canonical_strictMono (f i) (hinf i)).id_le (canonicalIndex (K i) n)
      change canonicalIndex (K i) n ≤ (K i).enumeration (canonicalIndex (K i) n) at hh
      rw [enumeration_canonicalIndex _ hx] at hh
      exact_mod_cast Nat.succ_le_succ hh
    · simp [canonicalRank_of_not_mem _ _ hx] <;> positivity
  exact hn.trans (le_mul_of_one_le_left (by positivity) hM)

/-- The positive half uses one generator for all rates strictly below the
threshold, including when the rate is specified only by a limsup. -/
theorem finiteClass_limsup (k : ℕ) (hk : 0 < k) (f : Fin k → Set ℕ) :
    ∃ gen : Generic.Generator ℕ, ∀ z s, Function.Injective s →
      limsup (empiricalNoiseRate s (f z)) atTop < 1/k →
      GeneratesElementInLimitOn gen (f z) s := by
  let family := fun j ↦ if h : j < k then f ⟨j,h⟩ else ∅
  obtain ⟨g,hg⟩ := finiteClass_below_reciprocal k hk family
  refine ⟨g,fun z s hinj hlim ↦ ?_⟩
  obtain ⟨c,hl,hc⟩ := exists_between hlim
  have hev := eventually_lt_of_limsup_lt hl (isBoundedUnder_of ⟨1,empiricalNoiseRate_le_one s (f z)⟩)
  obtain ⟨n,hn⟩ := eventually_atTop.mp hev
  have hrate : ConstantNoise s (f z) c := ⟨n,fun j hj ↦ (hn j hj).le⟩
  simpa [family,z.isLt] using hg c hc z.val z.isLt s hinj (by simpa [family,z.isLt] using hrate)

/-- The two sides of Theorem B.3 with exact cardinality and the equality
endpoint. The hard stream has no omissions. -/
theorem finiteClass_threshold (k : ℕ) (hk : 2 ≤ k) (c : ℝ) :
    (1/k ≤ c → ∃ f : Fin k → Set ℕ, Function.Injective f ∧ (∀ i, (f i).Infinite) ∧
      ∃ s : Generic.Stream ℕ, (∀ i, ConstantNoiseEnumeration s (f i) c) ∧
        ¬∃ g : Generic.Generator ℕ, ∀ i, GeneratesElementInLimitOn g (f i) s) ∧
    (c < 1/k → ∀ f : Fin k → Set ℕ, ∃ g : Generic.Generator ℕ,
      ∀ i s, Function.Injective s → ConstantNoise s (f i) c → GeneratesElementInLimitOn g (f i) s) := by
  constructor
  · intro hc
    obtain ⟨f,hi,hf,he,hbad⟩ := residue_class_obstruction k hk
    refine ⟨f,hi,hf,id,fun i ↦ ⟨(he i).1,(he i).2.1,?_⟩,hbad⟩
    obtain ⟨n,hn⟩ := (he i).2.2
    exact ⟨n,fun t ht ↦ (hn t ht).trans hc⟩
  · intro hc f
    let family := fun j ↦ if h : j < k then f ⟨j,h⟩ else ∅
    obtain ⟨g,hg⟩ := finiteClass_below_reciprocal k (by omega) family
    exact ⟨g,fun i s hi h ↦ by
      simpa [family,i.isLt] using hg c hc i.val i.isLt s hi (by simpa [family,i.isLt] using h)⟩

end GenLimit.InfiniteContamination
