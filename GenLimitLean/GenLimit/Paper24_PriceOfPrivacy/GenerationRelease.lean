import GenLimit.Paper24_PriceOfPrivacy.Resampling
import Mathlib.Data.Nat.Nth
import Mathlib.Probability.Distributions.Uniform

/-! The final release in Algorithm 1 is uniform on the first 2^n words of the
selected language, in the order of the public enumeration. -/
namespace GenLimit.PriceOfPrivacy.Generation

open DiscreteIID AgnosticLanguage Set
open scoped Classical ENNReal
noncomputable section

def word (u : ℕ ≃ X) (L : Set X) (j : ℕ) := u (Nat.nth (fun k => u k ∈ L) j)

private theorem positions_infinite (u : ℕ ≃ X) {L : Set X} (inf : L.Infinite) :
    {k | u k ∈ L}.Infinite := inf.preimage (fun x _ => u.surjective x)

def release (u : ℕ ≃ X) (C : Generic.LanguageFamily X) (n : ℕ) (A : Identifier X)
    (xs : List X) : PMF X :=
  (A xs).bind fun i => (PMF.uniformOfFintype (Fin (2^n))).map fun j => word u (C i) j.val

theorem release_private (u : ℕ ≃ X) (C : Generic.LanguageFamily X) {n : ℕ}
    {A : Identifier X} {ε δ : ℝ} (dp : PrivateAt ε δ n A) :
    PrivateAt ε δ n (release u C n A) :=
  privateAt_random_map dp (PMF.uniformOfFintype (Fin (2^n))) (fun i j => word u (C i) j.val)

theorem collision (u : ℕ ≃ X) {L : Set X} (inf : L.Infinite) (xs : List X)
    {m : ℕ} [NeZero m] :
    probability (PMF.uniformOfFintype (Fin m)) {j | word u L j.val ∈ xs} ≤ xs.length/(m:ℝ) := by
  let S := {j : Fin m | word u L j.val ∈ xs}
  let embed (j : S) : ↥xs.toFinset := ⟨word u L j.val.val,List.mem_toFinset.mpr j.property⟩
  have inject : Function.Injective embed := fun a b eq => Subtype.ext (Fin.ext
    (Nat.nth_injective (positions_infinite u inf) (u.injective (congrArg Subtype.val eq))))
  have hc := Fintype.card_le_of_injective embed inject
  rw [Fintype.card_coe] at hc
  have hr : (Fintype.card S : ℝ) ≤ xs.length := by exact_mod_cast hc.trans xs.toFinset_card_le
  change probability _ S ≤ _
  rw [probability,PMF.toOuterMeasure_uniformOfFintype_apply,ENNReal.toReal_div,
    ENNReal.toReal_natCast,ENNReal.toReal_natCast,Fintype.card_fin]
  exact div_le_div_of_nonneg_right hr (by positivity)

private theorem conditional_error (u : ℕ ≃ X) (C : Generic.LanguageFamily X)
    (inf : ∀ i, (C i).Infinite) (p : PMF X) (A : Identifier X) (xs : List X)
    {n : ℕ} (len : xs.length = n) :
    probability (release u C n A xs) {x | x ∉ p.support ∨ x ∈ xs} ≤
      probability (A xs) {i | ¬C i ⊆ p.support} + n/(2:ℝ)^n := by
  apply bind_event_off_exception _ _ _ _ (by positivity)
  intro i _ good
  have sub : C i ⊆ p.support := Classical.not_not.mp good
  have mem (j : Fin (2^n)) : word u (C i) j.val ∈ p.support :=
    sub (Nat.nth_mem_of_infinite (positions_infinite u (inf i)) j.val)
  have eq : (fun j : Fin (2^n) => word u (C i) j.val) ⁻¹' {x | x ∉ p.support ∨ x ∈ xs} =
      {j | word u (C i) j.val ∈ xs} := by
    ext j
    exact or_iff_right (not_not_intro (mem j))
  simpa only [probability,PMF.toOuterMeasure_map_apply,eq,len,Nat.cast_pow,Nat.cast_ofNat] using
    collision u (inf i) xs (m := 2^n)

/-- The error on a good sample is at most the conditional probability
of a bad index plus the uniform collision probability. -/
theorem generation_error (u : ℕ ≃ X) (C : Generic.LanguageFamily X)
    (inf : ∀ i, (C i).Infinite) (p : PMF X) (A : Identifier X) (n : ℕ)
    (B : Set (List X)) {b : ℝ} (hb : 0 ≤ b)
    (good : ∀ xs ∈ (samples p n).support, xs ∉ B → probability (A xs) {i | ¬ C i ⊆ p.support} ≤ b) :
    genErr (release u C n A) p n ≤ probability (samples p n) B + b + n/(2:ℝ)^n := by
  rw [genErr,add_assoc]
  apply bind_event_off_exception _ _ _ _ (by positivity)
  intro xs hx hxB
  have len := ((samples_support p n xs).mp hx).1
  have h := (conditional_error u C inf p A xs len).trans (add_le_add_right (good xs hx hxB) _)
  simpa only [probability,PMF.toOuterMeasure_map_apply] using h

end
end GenLimit.PriceOfPrivacy.Generation
