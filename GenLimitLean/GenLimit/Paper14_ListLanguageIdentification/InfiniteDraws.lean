import GenLimit.Paper14_ListLanguageIdentification.Probabilistic
import Mathlib.Data.Nat.Pairing
import Mathlib.Probability.Independence.InfinitePi

/-! # Infinite draws for probabilistic list identification

A fixed enumeration and an infinite fair tape give independent draws by
using the first successful bit in each of countably many independent rows.
-/
namespace GenLimit.ListIdentification.InfiniteDraws
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

noncomputable def iid {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    Measure (ℕ → α) := Measure.infinitePi (fun _ : ℕ ↦ μ)

instance {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (iid μ) := by unfold iid; infer_instance

/-- Flattening independent rows of independent coordinates gives independent
coordinates. The finite-cylinder calculation uses the bounding rectangle
of a finite set of coordinate pairs. -/
theorem uncurry_iid {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun (x : ℕ → ℕ → α) (i : ℕ × ℕ) ↦ x i.1 i.2)
      (iid (iid μ)) (Measure.infinitePi (fun _ : ℕ × ℕ ↦ μ)) := by
  classical
  refine ⟨by fun_prop, Measure.eq_infinitePi _ fun s t ht ↦ ?_⟩
  let I := s.image Prod.fst
  let J := s.image Prod.snd
  let box (i j : ℕ) : Set α := if (i,j) ∈ s then t (i,j) else univ
  have box_m i j : MeasurableSet (box i j) := by
    by_cases h : (i,j) ∈ s <;> simp [box,h,ht]
  have pre : (fun (x : ℕ → ℕ → α) (i : ℕ × ℕ) ↦ x i.1 i.2) ⁻¹' (s : Set (ℕ × ℕ)).pi t =
      (I : Set ℕ).pi (fun i ↦ (J : Set ℕ).pi (box i)) := by
    ext x
    constructor
    · intro hx i _ j _
      by_cases h : (i,j) ∈ s
      · simpa [box,h] using hx (i := (i,j)) h
      · simp [box,h]
    · intro hx ij hij
      change ij ∈ s at hij
      have hrow := hx (i := ij.1) (Finset.mem_image_of_mem _ hij)
      simpa [box,hij] using hrow (i := ij.2) (Finset.mem_image_of_mem _ hij)
  rw [Measure.map_apply (by fun_prop) (.pi s.countable_toSet ht),pre]
  change Measure.infinitePi (fun _ : ℕ ↦ iid μ) _ = _
  rw [Measure.infinitePi_pi _ (fun i _ ↦ MeasurableSet.pi J.countable_toSet (fun j _ ↦ box_m i j))]
  calc
    _ = ∏ i ∈ I, ∏ j ∈ J, μ (box i j) := Finset.prod_congr rfl
      (fun i _ ↦ Measure.infinitePi_pi _ (fun j _ ↦ box_m i j))
    _ = ∏ z ∈ I ×ˢ J, μ (box z.1 z.2) := (Finset.prod_product I J (fun z : ℕ × ℕ ↦ μ (box z.1 z.2))).symm
    _ = ∏ z ∈ s, μ (box z.1 z.2) := by
      symm
      apply Finset.prod_subset
      · exact fun z hz ↦ Finset.mem_product.mpr
          ⟨Finset.mem_image_of_mem _ hz, Finset.mem_image_of_mem _ hz⟩
      · intro z _ hz
        simp [box,hz]
    _ = _ := Finset.prod_congr rfl fun z hz ↦ by simp [box,hz]

def rows {α : Type*} (s : ℕ → α) (i j : ℕ) : α := s (Nat.pair i j)

theorem rows_iid {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    MeasurePreserving (rows (α := α)) (iid μ) (iid (iid μ)) := by
  let flat : (ℕ → ℕ → α) → ℕ → α := fun x n ↦ x (Nat.unpair n).1 (Nat.unpair n).2
  have perm : MeasurePreserving (fun (x : ℕ × ℕ → α) (i : ℕ) ↦ x (Nat.unpair i))
      (Measure.infinitePi (fun _ : ℕ × ℕ ↦ μ)) (iid μ) :=
    ⟨by fun_prop, by
      convert Measure.infinitePi_map_piCongrLeft (fun _ : ℕ ↦ μ) Nat.pairEquiv using 2
      funext x i
      obtain ⟨z,rfl⟩ := Nat.pairEquiv.surjective i
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
      change x (Nat.pairEquiv.symm (Nat.pairEquiv z)) = x z
      exact congrArg x (Nat.pairEquiv.symm_apply_apply z)⟩
  have hf : MeasurePreserving flat (iid (iid μ)) (iid μ) := perm.comp (uncurry_iid μ)
  have hm : Measurable (rows (α := α)) := by unfold rows; fun_prop
  refine ⟨hm, ?_⟩
  conv_lhs => rw [← hf.map_eq,Measure.map_map hm hf.measurable]
  have inv : rows ∘ flat = id := by funext x i j; simp [rows,flat,Nat.unpair_pair]
  rw [inv,Measure.map_id]

end GenLimit.ListIdentification.InfiniteDraws
