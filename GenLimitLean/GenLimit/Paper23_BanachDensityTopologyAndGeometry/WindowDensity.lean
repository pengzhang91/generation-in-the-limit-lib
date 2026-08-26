import GenLimit.Core.Basic
import Mathlib.Data.Nat.WithBot
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# #23 One-dimensional window densities

Definitions 3.1--3.2 and Claims 3.3 and 3.5 of Kleinberg--Wei,
*Validity, Sparse Holes, and Breadth in Language Generation: Banach Density,
Topology, and Geometry* (arXiv:2604.02385v2).

Ratios take values in the extended nonnegative reals, making every infimum
total. Actual finite-window ratios remain finite and lie in [0,1].
-/

namespace GenLimit.KleinbergWei.Banach

open Filter
open scoped ENNReal

/-- Number of elements of A in the length-k interval starting at m. -/
noncomputable def windowCount (A : Language) (m k : ℕ) : ℕ := by
  classical
  exact ((Finset.Ico m (m + k)).filter (· ∈ A)).card

/-- Finite-window proportion. Length zero is assigned value zero. -/
noncomputable def windowRatio (A : Language) (m k : ℕ) : ℝ≥0∞ :=
  if k = 0 then 0 else
    (windowCount A m k : ℝ≥0∞) / (k : ℝ≥0∞)

/-- Positive nondecreasing window bounds; top represents infinity. -/
def AdmissibleWindowBound (f : ℕ → WithTop ℕ) : Prop :=
  Monotone f ∧ ∀ k, (1 : WithTop ℕ) ≤ f k

/-- Inner minimum in Definition 3.2. -/
noncomputable def windowMinimum
    (f : ℕ → WithTop ℕ) (A : Language) (k : ℕ) : ℝ≥0∞ :=
  ⨅ m : ℕ,
    if 1 ≤ m ∧ (m : WithTop ℕ) ≤ f k then
      windowRatio A m k
    else ⊤

/-- Definition 3.2: lower f-window density. -/
noncomputable def lowerWindowDensity
    (f : ℕ → WithTop ℕ) (A : Language) : ℝ≥0∞ :=
  liminf (windowMinimum f A) atTop

/-- Unrestricted inner infimum over positive window starts. -/
noncomputable def banachMinimum
    (A : Language) (k : ℕ) : ℝ≥0∞ :=
  ⨅ m : ℕ, if 1 ≤ m then windowRatio A m k else ⊤

/-- Definition 3.1: one-dimensional lower Banach density. -/
noncomputable def lowerBanachDensity (A : Language) : ℝ≥0∞ :=
  liminf (banachMinimum A) atTop

theorem windowMinimum_anti
    {f g : ℕ → WithTop ℕ} {A : Language} {k : ℕ}
    (hfg : g k ≤ f k) :
    windowMinimum f A k ≤ windowMinimum g A k := by
  classical
  apply le_iInf
  intro m
  by_cases hg : 1 ≤ m ∧ (m : WithTop ℕ) ≤ g k
  · have hf : 1 ≤ m ∧ (m : WithTop ℕ) ≤ f k :=
      ⟨hg.1, hg.2.trans hfg⟩
    rw [if_pos hg]
    exact iInf_le_of_le m (by simp [hf])
  · simp [windowMinimum, hg]

/-- Claim 3.3: enlarging search windows can only decrease density. -/
theorem claim_3_3
    {f g : ℕ → WithTop ℕ} {A : Language}
    (_hf : AdmissibleWindowBound f)
    (_hg : AdmissibleWindowBound g)
    (hfg : ∀ k, g k ≤ f k) :
    lowerWindowDensity f A ≤ lowerWindowDensity g A := by
  apply Filter.liminf_le_liminf
  · exact Filter.Eventually.of_forall fun k => windowMinimum_anti (hfg k)
  · exact ⟨0, Filter.Eventually.of_forall fun _ => bot_le⟩
  · have hBound :
        atTop.IsBoundedUnder (· ≤ ·) (windowMinimum g A) :=
      ⟨⊤, Filter.Eventually.of_forall fun _ => le_top⟩
    exact hBound.isCoboundedUnder_ge

theorem windowMinimum_top (A : Language) (k : ℕ) :
    windowMinimum (fun _ => (⊤ : WithTop ℕ)) A k =
      banachMinimum A k := by
  simp only [windowMinimum, banachMinimum, le_top, and_true]

theorem lowerWindowDensity_top (A : Language) :
    lowerWindowDensity (fun _ => (⊤ : WithTop ℕ)) A =
      lowerBanachDensity A := by
  unfold lowerWindowDensity lowerBanachDensity
  have hfun :
      windowMinimum (fun _ => (⊤ : WithTop ℕ)) A = banachMinimum A :=
    funext fun k => windowMinimum_top A k
  rw [hfun]

theorem lowerBanachDensity_le_windowDensity
    {f : ℕ → WithTop ℕ} {A : Language}
    (hf : AdmissibleWindowBound f) :
    lowerBanachDensity A ≤ lowerWindowDensity f A := by
  rw [← lowerWindowDensity_top]
  exact claim_3_3
    (f := fun _ => (⊤ : WithTop ℕ)) (g := f)
    ⟨monotone_const, fun _ => le_top⟩ hf (fun _ => le_top)

/-- Claim 3.5: lower Banach density is the minimum over admissible window
bounds, attained by the constant-infinity bound. -/
theorem claim_3_5 (A : Language) :
    lowerBanachDensity A =
      ⨅ f : {f : ℕ → WithTop ℕ // AdmissibleWindowBound f},
        lowerWindowDensity f.1 A := by
  apply le_antisymm
  · apply le_iInf
    intro f
    exact lowerBanachDensity_le_windowDensity f.2
  · let topBound :
        {f : ℕ → WithTop ℕ // AdmissibleWindowBound f} :=
      ⟨fun _ => ⊤, monotone_const, fun _ => le_top⟩
    calc
      (⨅ f : {f : ℕ → WithTop ℕ // AdmissibleWindowBound f},
          lowerWindowDensity f.1 A)
          ≤ lowerWindowDensity topBound.1 A := iInf_le _ topBound
      _ = lowerBanachDensity A := lowerWindowDensity_top A

end GenLimit.KleinbergWei.Banach
