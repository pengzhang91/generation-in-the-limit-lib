import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.FiniteHistory
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Basic

/-! Coding integer lattice points shell by shell. The code may leave gaps in
the natural numbers, but every centered cube is exactly the pullback of a
finite initial segment. Gaps count neither in a target nor its generated subset. -/

namespace GenLimit.KleinbergWei.Banach

open Filter
open scoped Classical

abbrev Lattice (d : ℕ) := Fin d → ℤ

def centeredCube (d r : ℕ) : Finset (Lattice d) :=
  Finset.Icc (fun _ => -(r : ℤ)) (fun _ => (r : ℤ))

private def radius {d} (x : Lattice d) := Finset.univ.sup (fun j => (x j).natAbs)

private theorem mem_cube {d r} {x : Lattice d} : x ∈ centeredCube d r ↔ radius x ≤ r := by
  simp only [centeredCube, Finset.mem_Icc, Pi.le_def, radius, Finset.sup_le_iff,
    Finset.mem_univ, forall_const]
  constructor
  · rintro ⟨lo,hi⟩ j
    have h : |x j| ≤ (r : ℤ) := abs_le.mpr ⟨lo j,hi j⟩
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · intro h
    have b (j) : |x j| ≤ (r : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h j
    exact ⟨fun j => (abs_le.mp (b j)).1, fun j => (abs_le.mp (b j)).2⟩

private noncomputable def raw (d : ℕ) : Lattice d → ℕ :=
  @Encodable.encode _ (Encodable.ofCountable (Lattice d))

private theorem raw_injective (d : ℕ) : Function.Injective (raw d) :=
  @Encodable.encode_injective _ (Encodable.ofCountable (Lattice d))

/-- The first available code on shell r. -/
private noncomputable def offset (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | r+1 => offset d r + (centeredCube d r).sup (raw d) + 1

private noncomputable def shellCode {d} (x : Lattice d) := offset d (radius x) + raw d x

private theorem offset_strict (d : ℕ) : StrictMono (offset d) := by
  apply strictMono_nat_of_lt_succ
  intro r
  change _ < offset d r + _ + 1
  omega

private theorem code_below {d} (x : Lattice d) :
    shellCode x < offset d (radius x + 1) := by
  have h := Finset.le_sup (f := raw d) (mem_cube.mpr (le_refl (radius x)))
  change offset d (radius x) + raw d x < offset d (radius x) + _ + 1
  omega

private theorem code_in_range {d} (x : Lattice d) (r : ℕ) :
    shellCode x < offset d (r+1) ↔ x ∈ centeredCube d r := by
  rw [mem_cube]
  constructor
  · intro h
    by_contra! hn
    have hs : offset d (r+1) ≤ offset d (radius x) := (offset_strict d).monotone hn
    unfold shellCode at h
    omega
  · intro h
    exact (code_below x).trans_le ((offset_strict d).monotone (Nat.succ_le_succ h))

private theorem shell_injective (d : ℕ) : Function.Injective (shellCode (d := d)) := by
  intro x y h
  have comp (a b : Lattice d) (hab : shellCode a = shellCode b) : radius a ≤ radius b :=
    mem_cube.mp ((code_in_range a (radius b)).mp (hab ▸ code_below b))
  have e := le_antisymm (comp x y h) (comp y x h.symm)
  unfold shellCode at h
  rw [e] at h
  exact raw_injective d (Nat.add_left_cancel h)

/-- Counts actual target points in the centered cube, including its boundary. -/
noncomputable def cubeCount {d : ℕ} (K : Set (Lattice d)) (r : ℕ) : ℕ :=
  ((centeredCube d r).filter (· ∈ K)).card

noncomputable def centeredLowerDensity {d : ℕ} (S K : Set (Lattice d)) : ℝ :=
  liminf (fun r : ℕ => (cubeCount (S ∩ K) r : ℝ) / cubeCount K r) atTop

private theorem cube_count_code {d} (K : Set (Lattice d)) (r : ℕ) :
    cubeCount K r = Nat.count (· ∈ shellCode '' K) (offset d (r+1)) := by
  classical
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_bij (fun x _ => shellCode x)
  · intro x hx
    obtain ⟨h1,h2⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((code_in_range x r).mpr h1),x,h2,rfl⟩
  · exact fun _ _ _ _ h => shell_injective d h
  · intro y hy
    obtain ⟨hr,x,hx,rfl⟩ := Finset.mem_filter.mp hy
    exact ⟨x,Finset.mem_filter.mpr ⟨(code_in_range x r).mp (Finset.mem_range.mp hr),hx⟩,rfl⟩

open DensityMeasures.OrderedFocus

private theorem ratio_bound {d} (S K : Set (Lattice d)) (r : ℕ) :
    (cubeCount (S ∩ K) r : ℝ) / cubeCount K r ≤ 1 := by
  have h : cubeCount (S ∩ K) r ≤ cubeCount K r := by
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1,hx.2.2⟩
  rcases Nat.eq_zero_or_pos (cubeCount K r) with hz | hp
  · simp [hz]
  · exact (div_le_one (by exact_mod_cast hp)).mpr (by exact_mod_cast h)

/-- Restricting target-prefix ratios to the ends of shells can only increase
their lower limit. -/
private theorem cube_density_ge {d} (S K : Set (Lattice d)) (hK : K.Infinite) :
    (OrderedLanguage.increasing (shellCode '' K) (hK.image (shell_injective d).injOn)).lowerDensity
      (shellCode '' S) ≤ centeredLowerDensity S K := by
  classical
  let f := fun n : ℕ => (Nat.count (· ∈ (shellCode '' S) ∩ (shellCode '' K)) n : ℝ) /
    Nat.count (· ∈ shellCode '' K) n
  have eq (r : ℕ) : f (offset d (r+1)) = (cubeCount (S ∩ K) r : ℝ) / cubeCount K r := by
    simp only [f, cube_count_code, Set.image_inter (shell_injective d)]
  have tend : Tendsto (fun r => offset d (r+1)) atTop atTop :=
    (offset_strict d).tendsto_atTop.comp (strictMono_nat_of_lt_succ (f := fun r : ℕ => r+1)
      (fun _ => Nat.lt_succ_self _)).tendsto_atTop
  rw [OrderedLanguage.increasing_lowerDensity_eq_liminf,centeredLowerDensity]
  change liminf f atTop ≤ _
  simp_rw [← eq]
  change liminf f atTop ≤ liminf (f ∘ (fun r => offset d (r+1))) atTop
  rw [liminf_comp]
  apply liminf_le_liminf_of_le tend ?_ ?_
  · exact isBoundedUnder_of ⟨0,fun _ => by dsimp [f]; positivity⟩
  · apply isCoboundedUnder_ge_of_eventually_le _ (x := (1 : ℝ))
    exact Filter.eventually_map.mpr (.of_forall fun r => (eq r).trans_le (ratio_bound S K r))

/-- A speed-one element generator sees the whole input prefix through the present round. -/
def cubePlay {d} (A : List (Lattice d) → Lattice d) (s : ℕ → Lattice d) (t : ℕ) :=
  A (textPrefix s (t+1))

def cubeValid {d} (A : List (Lattice d) → Lattice d) (s : ℕ → Lattice d)
    (K : Set (Lattice d)) : Prop :=
  ∃ T, ∀ t ≥ T, cubePlay A s t ∈ K ∧ (∀ i ≤ t, s i ≠ cubePlay A s t) ∧
    ∀ i < t, cubePlay A s i ≠ cubePlay A s t

/-- The achievable half of Theorem 5.8 on actual lattice cubes. -/
theorem centered_generation {d} (C : ℕ → Set (Lattice d)) (hi : ∀ z, (C z).Infinite) :
    ∃ A : List (Lattice d) → Lattice d, ∀ z s, Set.range s = C z →
      cubeValid A s (C z) ∧ 1 / 2 ≤ centeredLowerDensity (Set.range (cubePlay A s)) (C z) := by
  classical
  let D := fun z => shellCode '' C z
  have inf (z) : (D z).Infinite := (hi z).image (shell_injective d).injOn
  let O := fun z => OrderedLanguage.increasing (D z) (inf z)
  have compat : Compatible O := by
    intro i j a b c e ha hb hab
    have h := OrderedLanguage.increasing_strictMono (D i) (inf i) hab
    change (O i).enumeration a < (O i).enumeration b at h
    rw [ha,hb] at h
    exact (OrderedLanguage.increasing_strictMono (D j) (inf j)).lt_iff_lt.mp h
  let decode := Function.invFun (@shellCode d)
  have inv : Function.LeftInverse decode shellCode := Function.leftInverse_invFun (shell_injective d)
  let A := fun xs : List (Lattice d) => decode (historyRule O (xs.map shellCode))
  refine ⟨A, fun z s hs => ?_⟩
  let ss := shellCode ∘ s
  have prs : Presents ss (O z).carrier := by
    change Set.range (shellCode ∘ s) = shellCode '' C z
    rw [Set.range_comp,hs]
  let g := play (historyRule O) ss
  have play_eq (t) : cubePlay A s t = decode (g t) := by
    simp [cubePlay, A, g, play, ss, textPrefix, List.map_map]
  have allcodes (t) : g t ∈ Set.range (@shellCode d) := by
    have h : generate O ss t ∈ (O (focus O ss t)).carrier := by
      rw [← (O _).range_enumeration]
      exact ⟨_,rfl⟩
    change generate O ss t ∈ D (focus O ss t) at h
    obtain ⟨x,_,hx⟩ := h
    exact ⟨x, hx.trans (congrFun (play_historyRule O ss).symm t)⟩
  have recode (t) : shellCode (cubePlay A s t) = g t := by
    rw [play_eq]; obtain ⟨x,hx⟩ := allcodes t; rw [← hx, inv]
  obtain ⟨⟨T,valid⟩,density⟩ := historyRule_density O compat (z := z) prs
  constructor
  · refine ⟨T,fun t ht => ?_⟩
    obtain ⟨hm, fresh, never⟩ := valid t ht
    obtain ⟨y,hy,he⟩ : g t ∈ D z := hm
    have ey := (shell_injective d) ((recode t).trans he.symm)
    refine ⟨ey ▸ hy,fun i hi heq => fresh i hi ((congrArg shellCode heq).trans (recode t)),?_⟩
    exact fun i hi heq => never i hi ((recode i).symm.trans ((congrArg shellCode heq).trans (recode t)))
  · have sub : generatedIn (historyRule O) ss (O z).carrier ⊆ shellCode '' Set.range (cubePlay A s) := by
      rintro _ ⟨⟨t,rfl⟩,_⟩
      exact ⟨_,⟨t,rfl⟩,recode t⟩
    exact (density.trans ((O z).lowerDensity_mono sub)).trans (cube_density_ge _ _ (hi z))

end GenLimit.KleinbergWei.Banach
