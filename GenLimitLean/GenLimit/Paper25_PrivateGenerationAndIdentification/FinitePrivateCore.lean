import GenLimit.Paper25_PrivateGenerationAndIdentification.ClosureGeneration
import GenLimit.Paper24_PriceOfPrivacy.ExponentialSelection
import GenLimit.Paper24_PriceOfPrivacy.Resampling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The finite-sample exponential mechanism of Appendix C.1 of P25. A
subcollection is scored by its number of jointly covered observations and a
reward for each selected language. The output is a finite set of indices. -/
namespace GenLimit.PrivateLimit.FiniteCore

open Set DiscreteIID PriceOfPrivacy
open scoped Classical ENNReal
noncomputable section

def core {k : ℕ} (C : Fin k → Set ℕ) (S : Finset (Fin k)) : Set ℕ := {x | ∀ j ∈ S, x ∈ C j}

theorem core_bound {k : ℕ} (C : Fin k → Set ℕ) {d : ℕ} (bound : SubcollectionClosureBound (range C) d)
    (S : Finset (Fin k)) (fin : (core C S).Finite) : (core C S).ncard ≤ d := by
  have eq : ⋂₀ (C '' (S : Set (Fin k))) = core C S := by ext x; simp [core]
  simpa only [eq] using bound (C '' (S : Set (Fin k))) (Set.image_subset_range ..) (eq ▸ fin)

def hits {k : ℕ} (C : Fin k → Set ℕ) (S : Finset (Fin k)) (xs : List ℕ) :=
  xs.filter fun x => decide (x ∈ core C S)

def score {k : ℕ} (C : Fin k → Set ℕ) (f : ℝ) (xs : List ℕ) (S : Finset (Fin k)) : ℝ :=
  (hits C S xs).length + f*S.card

def reward (k d n : ℕ) (a : ℝ) := ((n:ℝ)-d)/k - Real.log 2/a

def select {k : ℕ} (C : Fin k → Set ℕ) (d n : ℕ) (ε : ℝ) (xs : List ℕ) :=
  Exponential.law (score C (reward k d n (ε/2)) xs) (ε/2)

theorem sensitivity {k : ℕ} (C : Fin k → Set ℕ) (f : ℝ) (pre : List ℕ) (x y : ℕ)
    (post : List ℕ) (S : Finset (Fin k)) :
    |score C f (pre ++ x::post) S-score C f (pre ++ y::post) S| ≤ 1 := by
  by_cases hx : x ∈ core C S <;> by_cases hy : y ∈ core C S <;>
    simp [score,hits,hx,hy]

theorem privateAt {k : ℕ} (C : Fin k → Set ℕ) (d n : ℕ) {ε : ℝ} (he : 0 < ε) :
    PrivateAt ε 0 n (select C d n ε) := by
  intro pre x y post _ F
  have pr := Exponential.event_private _ _ (ε/2) 1 (by positivity)
    (sensitivity C (reward k d n (ε/2)) pre x y post) F
  simpa only [select,show 2*(ε/2)*1 = ε by ring,add_zero] using pr

def safe {k : ℕ} (C : Fin k → Set ℕ) (z : Fin k) (S : Finset (Fin k)) : Prop :=
  (core C S).Infinite ∧ core C S ⊆ C z

private theorem hits_insert {k : ℕ} (C : Fin k → Set ℕ) {z : Fin k} (S : Finset (Fin k))
    {xs : List ℕ} (inK : ∀ x ∈ xs, x ∈ C z) : hits C (insert z S) xs = hits C S xs := by
  apply List.filter_congr
  intro x hx
  simp [core,inK x hx]

private theorem hits_finite {k : ℕ} (C : Fin k → Set ℕ) {d : ℕ}
    (bound : SubcollectionClosureBound (range C) d) (S : Finset (Fin k)) (fin : (core C S).Finite)
    {xs : List ℕ} (distinct : xs.Nodup) : (hits C S xs).length ≤ d := by
  have nd : (hits C S xs).Nodup := distinct.filter _
  rw [←List.toFinset_card_of_nodup nd]
  have sub : ((hits C S xs).toFinset : Set ℕ) ⊆ core C S := by
    intro x hx
    simpa using (List.mem_filter.mp (List.mem_toFinset.mp hx)).2
  have h := Set.ncard_le_ncard sub fin
  rw [Set.ncard_coe_finset] at h
  exact h.trans (core_bound C bound S fin)

/-- The source's pre-release failure term is exactly 4 exp(−ε(n−d)/(2k)).
Samples are distinct; the privacy statement also applies to repeated data. -/
theorem failure {k : ℕ} (C : Fin k → Set ℕ) {d : ℕ} (bound : SubcollectionClosureBound (range C) d)
    {ε : ℝ} (he : 0 < ε) (z : Fin k) (xs : List ℕ) (nd : xs.Nodup)
    (inK : ∀ x ∈ xs, x ∈ C z) :
    probability (select C d xs.length ε xs) {S | ¬safe C z S} ≤
      4*Real.exp (-ε*((xs.length:ℝ)-d)/(2*k)) := by
  let a := ε/2
  let n : ℝ := xs.length
  let f := reward k d xs.length a
  let A := Exponential.law (score C f xs) a
  have ha : 0 < a := half_pos he
  have hk : (0:ℝ) < k := by exact_mod_cast (Nat.zero_le _ |>.trans_lt z.isLt)
  have algebra : a*f = a*(n-d)/k - Real.log 2 := by
    dsimp only [f,reward,n]; field_simp
  have scale : Real.exp (-a*f) = 2*Real.exp (-ε*(n-d)/(2*k)) := by
    rw [show -a*f = Real.log 2 + (-ε*(n-d)/(2*k)) by dsimp [a] at algebra ⊢; field_simp at algebra ⊢; linarith,
      Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
  by_cases hf : 0 ≤ f
  · let missed : Set (Finset (Fin k)) := {S | z ∉ S}
    let small : Set (Finset (Fin k)) := {S | (core C S).Finite}
    have mp : probability A missed ≤ Real.exp (-a*f) := by
      refine Exponential.event_injection _ _ ha.le missed (insert z) ?_ f ?_
      · intro S hS T hT eq
        simpa only [Finset.erase_insert (show z ∉ S from hS),Finset.erase_insert (show z ∉ T from hT)] using congrArg (fun V : Finset (Fin k) => V.erase z) eq
      · intro S hS
        simp only [score,hits_insert C S inK,Finset.card_insert_of_notMem (show z ∉ S from hS)]
        push_cast; linarith
    have single : hits C {z} xs = xs := by
      apply List.filter_eq_self.mpr; intro x hx; simpa [core] using inK x hx
    have sp : probability A small ≤ Real.exp (-a*f) := by
      refine (Exponential.event_margin (score C f xs) a ha.le small {z} (n+f-(d+k*f)) ?_).trans_eq ?_
      · intro S hS
        have cnt : ((hits C S xs).length:ℝ) ≤ d := by exact_mod_cast hits_finite C bound S hS nd
        have card : (S.card:ℝ) ≤ k := by exact_mod_cast (S.card_le_univ.trans_eq (Fintype.card_fin k))
        simp only [score,single,Finset.card_singleton,Nat.cast_one,mul_one]
        dsimp [n]; linarith [mul_le_mul_of_nonneg_left card hf]
      · simp only [Fintype.card_finset,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
        have prod : (2:ℝ)^k = Real.exp (k*Real.log 2) := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
        rw [prod,←Real.exp_add]; congr 1
        have e := (eq_div_iff hk.ne').mp (show a*f+Real.log 2 = a*(n-d)/k by linarith)
        nlinarith
    have sub : {S | ¬safe C z S} ⊆ missed ∪ small := by
      intro S h; by_cases hz : z ∈ S
      · right; by_contra inf; exact h ⟨inf,fun x hx => hx z hz⟩
      · exact Or.inl hz
    change probability A _ ≤ _
    exact ((probability_mono A sub).trans (probability_union_le A missed small)).trans
      ((add_le_add mp sp).trans_eq (by rw [scale]; dsimp [n]; ring))
  · have one : 1 ≤ Real.exp (-a*f) := Real.one_le_exp_iff.mpr (by nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_ge hf)])
    rw [scale] at one
    exact (probability_le_one ..).trans (by dsimp [n] at one; linarith)

end
end GenLimit.PrivateLimit.FiniteCore
