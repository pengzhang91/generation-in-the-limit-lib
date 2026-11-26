import GenLimit.Paper23_BanachDensityTopologyAndGeometry.TierGeometry
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RandomSigns

/-! A counterexample to the discrepancy inequality of Theorem 5.9 even
on rectangles that have a valid printed tier. In dimension 255, closed
unit boxes select arbitrary subsets of the 255 coordinate unit vectors.
For every two-coloring, 128 vectors have the same color, and a unit box
selects exactly those vectors. The printed constants give a bound below
128 for this genuine tier-zero rectangle. -/
namespace GenLimit.KleinbergWei.Banach.UnitBoxObstruction
open Finset Set Real TierGeometry TierWeights
open scoped Classical
noncomputable section

private def vector (i : Fin 255) : Lattice 255 := fun j => if j=i then 1 else 0

private theorem vectors_injective : Function.Injective vector := by
  intro i j eq
  by_contra ne
  have h := congrFun eq i
  simp [vector,ne] at h

private def cloud : Finset (Lattice 255) := Finset.univ.image vector

private def lower (S : Finset (Fin 255)) : Lattice 255 := fun i => if i ∈ S then 0 else -1
private def upper (S : Finset (Fin 255)) : Lattice 255 := fun i => if i ∈ S then 1 else 0

private theorem selects (S : Finset (Fin 255)) :
    Rectangles.box (↑cloud) (lower S) (upper S) = S.image vector := by
  ext x
  constructor
  · intro h
    obtain ⟨⟨_,hi⟩,mem⟩ := Rectangles.mem_box.mp h
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp mem
    refine Finset.mem_image_of_mem _ ?_
    by_contra outside
    have h := hi i
    simp [vector,upper,outside] at h
  · intro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    refine Rectangles.mem_box.mpr ⟨⟨?_,?_⟩,Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
    · intro j; simp only [lower,vector]; split <;> split <;> decide
    · intro j
      by_cases eq : j=i
      · subst j; simp [upper,vector,hi]
      · simp [upper,vector,eq]; split <;> decide

private theorem monochrome (color : Lattice 255 → Bool) :
    ∃ S : Finset (Fin 255), S.card = 128 ∧ ∃ b, ∀ i ∈ S, color (vector i) = b := by
  let A := Finset.univ.filter (fun i => color (vector i) = true)
  let B := Finset.univ \ A
  have colors (i) : i ∈ B → color (vector i) = false := by
    intro h
    have absent := (Finset.mem_sdiff.mp h).2
    simpa [A] using absent
  have cover : B.card + A.card = 255 := by
    simpa [B] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  by_cases big : 128 ≤ A.card
  · obtain ⟨S,sub,card⟩ := Finset.exists_subset_card_eq big
    exact ⟨S,card,true,fun i hi => (Finset.mem_filter.mp (sub hi)).2⟩
  · obtain ⟨S,sub,card⟩ := Finset.exists_subset_card_eq (show 128 ≤ B.card by omega)
    exact ⟨S,card,false,fun i hi => colors i (sub hi)⟩

private theorem constants :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ baseline ε 510 255 = 128 ∧
      threshold ε (scale 255 510) 128 0 < 128 := by
  let ε := π / sqrt 192
  have sq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 192)
  have pos : 0 < sqrt 192 := by positivity
  have small : ε < 1/4 := by
    apply (div_lt_iff₀ pos).mpr
    have h := Real.pi_lt_d2
    nlinarith
  have pow2 : (ε:ℝ)^2 = π^2/192 := by dsimp [ε]; rw [div_pow,sq]
  refine ⟨ε,div_pos Real.pi_pos pos,by linarith,?_,?_⟩
  · norm_num [baseline,pow2,Real.pi_ne_zero]
    field_simp [Real.pi_ne_zero]
    ring
  · have logtwo : log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    have lk : log 128 = 7*log 2 := by
      rw [show (128:ℝ)=2^7 by norm_num,Real.log_pow]; norm_num
    have lg : 0 ≤ 6*log 128+4*log 2 := by positivity
    have sqg := Real.sq_sqrt lg
    have gl : sqrt (6*log 128+4*log 2) ≤ 7 := by nlinarith
    have ml : sqrt 128 ≤ 12 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 128)]
    have bound := mul_le_mul gl ml (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 7)
    norm_num [threshold,scale] at bound ⊢
    linarith

/-- The point count is exactly the tier-zero lower endpoint. Every side
has geometric length one. The event violates the stated discrepancy
inequality with the paper's own constants and strictly positive volume. -/
theorem printed_coloring_fails :
    ∃ (ε : ℝ) (P : Finset (Lattice 255)), 0 < ε ∧ ε < 1 ∧
      baseline ε 510 255 = 128 ∧ P.card = 255 ∧
      ∀ color : Lattice 255 → Bool, ∃ l u : Lattice 255,
        (∀ i, u i-l i=1) ∧
        let T := Rectangles.box (↑P) l u
        T.card = 128 ∧
        baseline ε 510 255 * (1:ℝ)^(510:ℝ) ≤ T.card ∧
        (T.card:ℝ) < 2*baseline ε 510 255 * (1:ℝ)^(510:ℝ) ∧
        threshold ε (scale 255 510) T.card 0 < |∑ v ∈ T, RandomSigns.sign (color v)| := by
  obtain ⟨ε,hp,hs,base,limit⟩ := constants
  refine ⟨ε,cloud,hp,hs,base,by simp [cloud,Finset.card_image_of_injective _ vectors_injective],?_⟩
  intro color
  obtain ⟨S,hS,b,all⟩ := monochrome color
  refine ⟨lower S,upper S,fun i => by by_cases h : i ∈ S <;> simp [lower,upper,h],?_⟩
  simp only [selects,Finset.card_image_of_injective _ vectors_injective,hS,base,
    Real.one_rpow,Nat.cast_ofNat,mul_one]
  refine ⟨trivial,le_rfl,by norm_num,?_⟩
  rw [Finset.sum_image (fun i _ j _ h => vectors_injective h)]
  have same : ∑ i ∈ S, RandomSigns.sign (color (vector i)) = ∑ _ ∈ S, RandomSigns.sign b :=
    Finset.sum_congr rfl fun i hi => congrArg RandomSigns.sign (all i hi)
  rw [same,Finset.sum_const,hS]
  cases b <;> simpa [RandomSigns.sign] using limit

end
end GenLimit.KleinbergWei.Banach.UnitBoxObstruction
