import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RectangleLanguage
import Mathlib.Topology.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Int

/-! Local capacity with lattice side lengths and the finite-to-infinite
coloring step in 5.9. Each endpoint has at most b possible positions
relative to a specified point when a coordinate spans b lattice sites. -/
namespace GenLimit.KleinbergWei.Banach.DiscrepancyBoxes
open Set Finset
open scoped Classical
noncomputable section

theorem local_capacity {d b : ℕ} (P : Set (Fin d → ℤ)) (x : Fin d → ℤ)
    (F : Finset (Finset (Fin d → ℤ)))
    (boxes : ∀ T ∈ F, ∃ l u : Fin d → ℤ, Rectangles.box P l u = T ∧ l ≤ x ∧ x ≤ u ∧
      ∀ i, u i - l i < (b : ℤ)) :
    F.card ≤ b^(2*d) := by
  let Code := (Fin d → Fin b) × (Fin d → Fin b)
  have code (T : F) : ∃ c : Code, Rectangles.box P (fun i => x i - (c.1 i : ℕ))
      (fun i => x i + (c.2 i : ℕ)) = T.val := by
    obtain ⟨l,u,eq,lo,hi,width⟩ := boxes _ T.property
    have left (i) : 0 ≤ x i-l i := sub_nonneg.mpr (lo i)
    have right (i) : 0 ≤ u i-x i := sub_nonneg.mpr (hi i)
    have lm (i) : (x i-l i).toNat < b := by have := width i; have := right i; have := left i; omega
    have rm (i) : (u i-x i).toNat < b := by have := width i; have := right i; have := left i; omega
    refine ⟨⟨fun i => ⟨_,lm i⟩,fun i => ⟨_,rm i⟩⟩,?_⟩
    have left_eq : (fun i => x i - ((x i-l i).toNat : ℤ)) = l := by
      funext i
      rw [Int.toNat_of_nonneg (left i)]
      omega
    have right_eq : (fun i => x i + ((u i-x i).toNat : ℤ)) = u := by
      funext i
      rw [Int.toNat_of_nonneg (right i)]
      omega
    change Rectangles.box P (fun i => x i - ((x i-l i).toNat : ℤ))
      (fun i => x i + ((u i-x i).toNat : ℤ)) = T.val
    rw [left_eq,right_eq,eq]
  have inj : Function.Injective (fun T => (code T).choose) := by
    intro A B eq
    change (code A).choose = (code B).choose at eq
    apply Subtype.ext
    rw [←(code A).choose_spec,eq,(code B).choose_spec]
  have card := Fintype.card_le_of_injective _ inj
  simpa [Code,pow_add,two_mul] using card

/-- Compactness of two-colorings. A single global coloring satisfies
every finite-trace constraint if each finite collection of constraints
can be satisfied simultaneously. -/
theorem global_coloring {V I : Type*} (trace : I → Finset V)
    (ok : ∀ i, (trace i → Bool) → Prop)
    (finite : ∀ F : Finset I, ∃ color : V → Bool,
      ∀ i ∈ F, ok i (fun v => color v.val)) :
    ∃ color : V → Bool, ∀ i, ok i (fun v => color v.val) := by
  let good (i : I) : Set (V → Bool) := {c | ok i (fun v => c v.val)}
  have closed (i) : IsClosed (good i) := by
    have cont : Continuous (fun c : V → Bool => fun v : trace i => c v.val) :=
      continuous_pi fun v => continuous_apply v.val
    exact (isClosed_discrete (s := {p | ok i p})).preimage cont
  have possible (F : Finset I) : (⋂ i ∈ F, good i).Nonempty := by
    obtain ⟨c,h⟩ := finite F
    exact ⟨c,Set.mem_iInter₂.mpr h⟩
  obtain ⟨c,h⟩ := CompactSpace.iInter_nonempty closed possible
  exact ⟨c,Set.mem_iInter.mp h⟩

end
end GenLimit.KleinbergWei.Banach.DiscrepancyBoxes
