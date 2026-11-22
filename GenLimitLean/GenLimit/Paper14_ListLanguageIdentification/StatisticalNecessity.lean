import GenLimit.Paper14_ListLanguageIdentification.Statistical

/-! # No vanishing statistical rate without the k-Angluin condition

For each candidate a Baire argument extends any prescribed prefix to one
that forces small error on *all* continuations in that language. Descending
to strict sublanguages preserves earlier constraints. A list of width k
cannot meet k+1 such constraints simultaneously. -/
namespace GenLimit.ListIdentification.Statistical
open DiscreteIID Filter
open scoped Topology

private theorem continuous_error {F : Generic.LanguageFamily α} (A : Kernel α k)
    (K : Generic.Language α) (e : ℕ → α) (n : ℕ) :
    Continuous (fun s : ℕ → ℕ ↦ error F A (sequenceLaw (e ∘ s)) K n) := by
  have h (s : ℕ → ℕ) : sequenceLaw (e ∘ s) = (sequenceLaw s).map e := by
    simp [sequenceLaw,PMF.map_comp]
  simp only [error,h,samples_map,PMF.bind_map]
  exact continuous_sequence_experiment n (fun xs ↦ A (xs.map e)) _

/-- Extend an arbitrary legal prefix, preserving the fixed target's error
bound even on continuations whose support is a proper sublanguage. -/
private theorem lock [Countable α] (F : Generic.LanguageFamily α) (A : Kernel α k)
    (i : ℕ) (hne : (F i).Nonempty) (ε : ℝ)
    (small : ∀ p : PMF α, p.support = F i → ∃ b : ℕ, ∀ᶠ n : ℕ in atTop,
      error F A p (F i) n ≤ ε - 1 / ((b : ℝ)+1))
    (v : ℕ → α) (m : ℕ) (hv : ∀ a < m, v a ∈ F i) :
    ∃ (w : ℕ → α) (l : ℕ), m ≤ l ∧ (∀ a < m, w a = v a) ∧
      (∀ a, w a ∈ F i) ∧ ∀ u : ℕ → α, (∀ a < l, u a = w a) →
        (∀ a, u a ∈ F i) → ∀ᶠ n : ℕ in atTop, error F A (sequenceLaw u) (F i) n < ε := by
  classical
  letI := baire_natSequences
  letI : Nonempty (F i) := hne.to_subtype
  obtain ⟨enum,hen⟩ := exists_surjective_nat (F i)
  let e (a : ℕ) := (enum a).1
  have surj (x : α) (hx : x ∈ F i) : ∃ a, e a = x := by
    obtain ⟨a,ha⟩ := hen ⟨x,hx⟩
    exact ⟨a,congrArg Subtype.val ha⟩
  let inc (x : α) := if hx : x ∈ F i then (surj x hx).choose else 0
  have einc (x : α) (hx : x ∈ F i) : e (inc x) = x := by
    simpa [inc,hx] using (surj x hx).choose_spec
  let D (N : ℕ × ℕ) : Set (ℕ → ℕ) :=
    {s | ∀ n ≥ N.1, error F A (sequenceLaw (e ∘ s)) (F i) n ≤ ε - 1 / ((N.2 : ℝ)+1)}
  have closed (N : ℕ × ℕ) : IsClosed (D N) := by
    have hd : D N = ⋂ n : ℕ, ⋂ (_ : N.1 ≤ n),
        {s | error F A (sequenceLaw (e ∘ s)) (F i) n ≤ ε - 1 / ((N.2 : ℝ)+1)} := by ext s; simp [D]
    rw [hd]
    exact isClosed_iInter (fun n ↦ isClosed_iInter (fun _ ↦ isClosed_le (continuous_error A _ e n) continuous_const))
  have hc : {s : ℕ → ℕ | Function.Surjective s} ⊆ ⋃ N, D N := by
    intro s hs
    have hsupport : (sequenceLaw (e ∘ s)).support = F i := by
      rw [sequenceLaw_support,Set.range_comp,hs.range_eq,Set.image_univ]
      exact Set.ext (fun x ↦ ⟨fun ⟨a,_⟩ ↦ by subst x; exact (enum a).2,surj x⟩)
    obtain ⟨b,hb⟩ := small _ hsupport
    obtain ⟨N,hN⟩ := eventually_atTop.mp hb
    exact Set.mem_iUnion.mpr ⟨(N,b),hN⟩
  have dense := surjective_sequences_dense_gdelta.1.dense_iUnion_interior_of_closed
    surjective_sequences_dense_gdelta.2 closed hc
  let t := inc ∘ v
  obtain ⟨s,hs,hs0⟩ := dense.exists_mem_open (PiNat.isOpen_cylinder _ t m)
    ⟨t,PiNat.self_mem_cylinder t m⟩
  obtain ⟨N,hN⟩ := Set.mem_iUnion.mp hs
  obtain ⟨_,⟨r,b,rfl⟩,hsr,hr⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ ↦ ℕ)).exists_subset_of_mem_open hN isOpen_interior
  refine ⟨e ∘ s,max m b,le_max_left _ _,fun a ha ↦ ?_,fun a ↦ (enum (s a)).2,?_⟩
  · change e (s a) = v a
    rw [PiNat.mem_cylinder_iff.mp hs0 a ha]
    exact einc _ (hv a ha)
  · intro u he hu
    let q (a : ℕ) := if a < max m b then s a else inc (u a)
    have hq : q ∈ PiNat.cylinder r b := PiNat.mem_cylinder_iff.mpr (fun a ha ↦
      (if_pos (ha.trans_le (le_max_right m b))).trans (PiNat.mem_cylinder_iff.mp hsr a ha))
    have equ : e ∘ q = u := by
      funext a
      change e (if a < max m b then s a else inc (u a)) = u a
      by_cases h : a < max m b
      · rw [if_pos h]; exact (he a h).symm
      · rw [if_neg h]; exact einc (u a) (hu a)
    have hD := interior_subset (hr hq)
    change ∀ n ≥ N.1, error F A (sequenceLaw (e ∘ q)) (F i) n ≤ ε - 1 / ((N.2 : ℝ)+1) at hD
    rw [equ] at hD
    exact eventually_atTop.mpr ⟨N.1,fun n hn ↦ (hD n hn).trans_lt (sub_lt_self _ (by positivity))⟩

/-- Small error for every target-support law forces the full recursive
list tell-tale condition. The threshold depends only on the list width. -/
private theorem condition_of_local_bounds [Countable α] (F : Generic.LanguageFamily α) (A : Kernel α k)
    (hne : ∀ i, (F i).Nonempty)
    (small : ∀ i (p : PMF α), p.support = F i → ∃ b : ℕ, ∀ᶠ n : ℕ in atTop,
      error F A p (F i) n ≤ 1 / ((k : ℝ) + 1) - 1 / ((b : ℝ)+1)) : KAngluinCondition F k := by
  classical
  let ε : ℝ := 1 / ((k : ℝ) + 1)
  have step (d : ℕ) (S : Finset (Generic.Language α)) (hc : S.card + d = k)
      (i : ℕ) (hs : ∀ K ∈ S, F i ⊂ K) (v : ℕ → α) (m : ℕ) (hv : ∀ a < m, v a ∈ F i)
      (locked : ∀ K ∈ S, ∀ u : ℕ → α, (∀ a < m, u a = v a) → (∀ a, u a ∈ F i) →
        ∀ᶠ n : ℕ in atTop, error F A (sequenceLaw u) K n < ε) : Psi F i d := by
    induction d generalizing S i v m with
    | zero =>
      obtain ⟨w,l,hl,hv',hw,hlock⟩ := lock F A i (hne i) ε (small i) v m hv
      let U := insert (F i) S
      have hiS : F i ∉ S := fun h ↦ (hs _ h).ne rfl
      have hcard : U.card = k+1 := by simp [U,hiS] at *; omega
      have allLocks : ∀ K ∈ U, ∀ᶠ n : ℕ in atTop, error F A (sequenceLaw w) K n < ε := by
        intro K hK
        rcases Finset.mem_insert.mp hK with rfl | h
        · exact hlock w (fun _ _ ↦ rfl) hw
        · exact locked K h w hv' hw
      obtain ⟨n,hn⟩ := ((U.eventually_all).2 allLocks).exists
      have lower := miss_sum F ((samples (sequenceLaw w) n).bind A) U (by omega)
      have hi := Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (by omega : 0 < U.card)) hn
      change 1 ≤ ∑ K ∈ U, error F A (sequenceLaw w) K n at lower
      have contra := lower.trans_lt hi
      simp [ε,hcard,show (k : ℝ)+1 ≠ 0 by positivity] at contra
    | succ d ih =>
      obtain ⟨w,l,hl,he,hw,hlock⟩ := lock F A i (hne i) ε (small i) v m hv
      let T := (Finset.range l).image w
      refine ⟨T,?_,?_⟩
      · rintro x hx
        obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
        exact hw a
      · intro j ht hji
        have hiS : F i ∉ S := fun h ↦ (hs _ h).ne rfl
        refine ih (insert (F i) S) (by rw [Finset.card_insert_of_notMem hiS]; omega)
          j ?_ w l (fun a ha ↦ ht (Finset.mem_image.mpr ⟨a,Finset.mem_range.mpr ha,rfl⟩)) ?_
        · intro K hK
          rcases Finset.mem_insert.mp hK with rfl | h
          · exact hji
          · exact hji.trans (hs _ h)
        · intro K hK u hu huj
          rcases Finset.mem_insert.mp hK with rfl | h
          · exact hlock u hu (fun a ↦ hji.1 (huj a))
          · exact locked K h u (fun a ha ↦ (hu a (ha.trans_le hl)).trans (he a ha))
              (fun a ↦ hji.1 (huj a))
  intro i
  exact step k ∅ (by simp) i (by simp) (fun _ ↦ (hne i).choose) 0 (by simp) (by simp)

/-- Theorem 11. Even for randomized identifiers there is a law with limsup
error at least 1/(k+1). The closed cover in the locking proof allows the
gap below this threshold to depend on the individual law. -/
theorem theorem_11 [Countable α] (F : Generic.LanguageFamily α) (hne : ∀ i, (F i).Nonempty)
    (h : ¬ KAngluinCondition F k) (A : Kernel α k) :
    ∃ (i : ℕ) (p : PMF α), p.support = F i ∧
      1 / ((k : ℝ)+1) ≤ limsup (error F A p (F i)) atTop := by
  by_contra! hh
  apply h (condition_of_local_bounds F A hne ?_)
  intro i p hp
  have ht := hh i p hp
  obtain ⟨b,hb⟩ := exists_nat_one_div_lt (sub_pos.mpr ht)
  refine ⟨b,?_⟩
  apply (eventually_lt_of_limsup_lt (by linarith : limsup (error F A p (F i)) atTop <
    1 / ((k : ℝ)+1) - 1 / ((b : ℝ)+1)) ?_).mono (fun _ hlt ↦ hlt.le)
  exact isBoundedUnder_of ⟨1,fun _ ↦ probability_le_one _ _⟩

/-- Theorem 8, in a stronger frequently-positive-error form for randomized kernels. -/
theorem theorem_8 [Countable α] (F : Generic.LanguageFamily α) (hne : ∀ i, (F i).Nonempty)
    (h : ¬ KAngluinCondition F k) (A : Kernel α k) :
    ∃ (i : ℕ) (p : PMF α), p.support = F i ∧ ∃ᶠ n : ℕ in atTop,
      1 / ((k : ℝ)+2) < error F A p (F i) n := by
  obtain ⟨i,p,hp,hl⟩ := theorem_11 F hne h A
  refine ⟨i,p,hp,?_⟩
  have lt : 1 / ((k : ℝ)+2) < 1 / ((k : ℝ)+1) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  exact frequently_lt_of_lt_limsup (isCoboundedUnder_le_of_le atTop
    (fun _ ↦ probability_nonneg _ _)) (lt.trans_le hl)

end GenLimit.ListIdentification.Statistical
