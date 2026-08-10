import GenLimit.Paper02_LearningTheory.EarlierSectionThreeExamples
import Mathlib.Data.Set.Countable

/-!
# #02 Learning Theory: generation versus prediction

Source: Jiaxun Li, Vinod Raman, and Ambuj Tewari, *Generation through the
Lens of Learning Theory*, arXiv:2410.13714v5, Theorem 4.1 and Appendix A.

This module formalizes the combinatorial core of Theorem 4.1.  The paper
cites the classical characterizations

* binary PAC learnability iff finite VC dimension, and
* binary online learnability iff finite Littlestone dimension.

Accordingly, `PACLearnableViaVC` and `OnlineLearnableViaLittlestone` below
are deliberately named characterization-level proxies.  They are not
formalizations of the probability space, iid sampling, sublinear regret, or
algorithms appearing in Definitions 2.8 and 2.10.

There is also a source-level universe issue.  The displayed Theorem 4.1 says
"let `X` be countable", but Appendix A immediately chooses `X = ℤ`; the
claim cannot hold for arbitrary finite `X` because its generation definitions
assume infinite supports.  The six results at the end therefore instantiate
the Appendix constructions on explicit countably infinite universes.  No
generic false finite-universe statement is asserted.
-/

namespace GenLimit.LiRamanTewari

/-! ## VC shattering and the cited PAC characterization -/

/-- Definition 2.9's sequence formulation of VC shattering. -/
def VCShatters
    (H : GenLimit.Generic.LanguageClass α) {d : ℕ}
    (xs : Fin d → α) : Prop :=
  ∀ labels : Fin d → Bool, ∃ L, L ∈ H ∧
    ∀ i, (xs i ∈ L ↔ labels i = true)

/-- The paper's statement `VC(H) < ∞`, without choosing the largest value. -/
def HasFiniteVCDimension
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ d : ℕ, ∀ xs : Fin (d + 1) → α, ¬VCShatters H xs

/-- The paper's statement `VC(H) = ∞`. -/
def HasInfiniteVCDimension
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ d : ℕ, ∃ xs : Fin d → α, VCShatters H xs

/-- PAC learnability through the finite-VC characterization cited immediately
after Definition 2.9.  This is not Definition 2.8's probabilistic model. -/
def PACLearnableViaVC
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  HasFiniteVCDimension H

theorem vcShatters_mono
    {H K : GenLimit.Generic.LanguageClass α} (hHK : H ⊆ K)
    {d : ℕ} {xs : Fin d → α} (h : VCShatters H xs) :
    VCShatters K xs := by
  intro labels
  obtain ⟨L, hLH, hlabels⟩ := h labels
  exact ⟨L, hHK hLH, hlabels⟩

/-- A pair of points realizes all four binary labelings in a class. -/
def PairShattered
    (H : GenLimit.Generic.LanguageClass α) (x y : α) : Prop :=
  ∀ bx byLabel : Bool, ∃ L, L ∈ H ∧
    (x ∈ L ↔ bx = true) ∧ (y ∈ L ↔ byLabel = true)

theorem pairShattered_of_vcShatters
    {H : GenLimit.Generic.LanguageClass α} {d : ℕ}
    {xs : Fin d → α} (h : VCShatters H xs)
    {i j : Fin d} (hij : i ≠ j) :
    PairShattered H (xs i) (xs j) := by
  intro bi bj
  let labels : Fin d → Bool :=
    fun k ↦ if k = i then bi else if k = j then bj else false
  obtain ⟨L, hLH, hL⟩ := h labels
  refine ⟨L, hLH, ?_, ?_⟩
  · simpa [labels] using hL i
  · simpa [labels, hij.symm] using hL j

theorem vcShatters_injective
    {H : GenLimit.Generic.LanguageClass α} {d : ℕ}
    {xs : Fin d → α} (h : VCShatters H xs) :
    Function.Injective xs := by
  intro i j hx
  by_contra hij
  have hp := pairShattered_of_vcShatters h hij true false
  obtain ⟨L, _hLH, hi, hj⟩ := hp
  have hxi : xs i ∈ L := hi.mpr rfl
  have hxj : xs j ∉ L := by
    intro hm
    have : false = true := hj.mp hm
    cases this
  exact hxj (hx ▸ hxi)

theorem not_pacViaVC_of_infinite
    {H : GenLimit.Generic.LanguageClass α}
    (h : HasInfiniteVCDimension H) :
    ¬PACLearnableViaVC H := by
  rintro ⟨d, hd⟩
  obtain ⟨xs, hxs⟩ := h (d + 1)
  exact hd xs hxs

/-! ## Littlestone shattering and the cited online characterization -/

/-- A complete binary Littlestone tree of a fixed depth.  At a node, `left`
is the edge labeled `0` and `right` is the edge labeled `1`. -/
inductive LittlestoneTree (α : Type*) : ℕ → Type _
  | leaf : LittlestoneTree α 0
  | node {d : ℕ} (x : α)
      (left right : LittlestoneTree α d) :
      LittlestoneTree α (d + 1)

/-- The subclass consistent with one labeled example. -/
def labelClass
    (H : GenLimit.Generic.LanguageClass α) (x : α) (b : Bool) :
    GenLimit.Generic.LanguageClass α :=
  {L | L ∈ H ∧ (x ∈ L ↔ b = true)}

/-- Definition 2.11's path-by-path shattering condition, written recursively
on a complete binary tree. -/
def LittlestoneShattered :
    {d : ℕ} → LittlestoneTree α d →
      GenLimit.Generic.LanguageClass α → Prop
  | 0, .leaf, H => H.Nonempty
  | _ + 1, .node x left right, H =>
      LittlestoneShattered left (labelClass H x false) ∧
      LittlestoneShattered right (labelClass H x true)

/-- There is a shattered Littlestone tree of depth `d`. -/
def HasShatteredLittlestoneTree
    (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop :=
  ∃ T : LittlestoneTree α d, LittlestoneShattered T H

/-- The paper's statement `L(H) < ∞`. -/
def HasFiniteLittlestoneDimension
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ d : ℕ, ¬HasShatteredLittlestoneTree H (d + 1)

/-- The paper's statement `L(H) = ∞`. -/
def HasInfiniteLittlestoneDimension
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ d : ℕ, HasShatteredLittlestoneTree H d

/-- Online learnability through the finite-Littlestone characterization cited
after Definition 2.10.  This is not the regret/algorithm quantifier of that
definition. -/
def OnlineLearnableViaLittlestone
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  HasFiniteLittlestoneDimension H

theorem littlestoneShattered_mono
    {H K : GenLimit.Generic.LanguageClass α} (hHK : H ⊆ K)
    {d : ℕ} {T : LittlestoneTree α d}
    (hT : LittlestoneShattered T H) :
    LittlestoneShattered T K := by
  induction T generalizing H K with
  | leaf =>
      obtain ⟨L, hLH⟩ := hT
      exact ⟨L, hHK hLH⟩
  | @node d x left right ihLeft ihRight =>
      exact ⟨
        ihLeft (H := labelClass H x false)
          (K := labelClass K x false) (by
          intro L hL
          exact ⟨hHK hL.1, hL.2⟩) hT.1,
        ihRight (H := labelClass H x true)
          (K := labelClass K x true) (by
          intro L hL
          exact ⟨hHK hL.1, hL.2⟩) hT.2⟩

theorem littlestoneShattered_nonempty
    {H : GenLimit.Generic.LanguageClass α}
    {d : ℕ} {T : LittlestoneTree α d}
    (hT : LittlestoneShattered T H) :
    H.Nonempty := by
  induction T generalizing H with
  | leaf => exact hT
  | @node d x left right ihLeft _ihRight =>
      obtain ⟨L, hL⟩ := ihLeft hT.1
      exact ⟨L, hL.1⟩

theorem no_depth_one_of_subsingleton
    {H : GenLimit.Generic.LanguageClass α}
    (hH : H.Subsingleton) (T : LittlestoneTree α 1) :
    ¬LittlestoneShattered T H := by
  intro hT
  cases T with
  | node x left right =>
      obtain ⟨L₀, hL₀⟩ := littlestoneShattered_nonempty hT.1
      obtain ⟨L₁, hL₁⟩ := littlestoneShattered_nonempty hT.2
      have hEq : L₀ = L₁ := hH hL₀.1 hL₁.1
      have hx₀ : x ∉ L₀ := by
        intro hx
        have : false = true := hL₀.2.mp hx
        cases this
      have hx₁ : x ∈ L₁ := hL₁.2.mpr rfl
      exact hx₀ (hEq ▸ hx₁)

theorem not_onlineViaLittlestone_of_infinite
    {H : GenLimit.Generic.LanguageClass α}
    (h : HasInfiniteLittlestoneDimension H) :
    ¬OnlineLearnableViaLittlestone H := by
  rintro ⟨d, hd⟩
  exact hd (h (d + 1))

/-! ## Generic generation lemmas for Appendix A -/

theorem uniformlyGeneratable_of_common_infinite_base
    [Nonempty α] [Countable α]
    {H : GenLimit.Generic.LanguageClass α} {B : Set α}
    (hB : B.Infinite) (hbase : ∀ L, L ∈ H → B ⊆ L) :
    UUS H ∧ UniformlyGeneratable H := by
  have hUUS : UUS H := by
    intro L hLH
    exact hB.mono (hbase L hLH)
  refine ⟨hUUS, (uniform_generatability_iff_finite_closure_dimension hUUS).2 ?_⟩
  refine ⟨0, ?_, Or.inl rfl⟩
  intro S _hcard _hVS
  apply hB.mono
  intro x hx L hL
  exact hbase L hL.1 hx

/-! ## Appendix A.1: uniformly generatable but infinite VC dimension -/

/-- The first Appendix A class: the fixed non-positive integer tail together
with an arbitrary finite set of positive integers. -/
def finiteAugmentationClass : GenLimit.Generic.LanguageClass ℤ :=
  {L | ∃ A : Set ℤ, A ⊆ paperPositiveIntegers ∧ A.Finite ∧
    L = paperNonpositiveIntegers ∪ A}

theorem finiteAugmentationClass_countable :
    finiteAugmentationClass.Countable := by
  have hFiniteSets :
      ({A : Set ℤ | A.Finite} : Set (Set ℤ)).Countable :=
    Set.Countable.setOf_finite
  have hImage :=
    hFiniteSets.image (fun A : Set ℤ ↦ paperNonpositiveIntegers ∪ A)
  apply hImage.mono
  intro L hL
  obtain ⟨A, _hAP, hAfin, rfl⟩ := hL
  exact ⟨A, hAfin, rfl⟩

theorem finiteAugmentationClass_uus_and_uniform :
    UUS finiteAugmentationClass ∧
      UniformlyGeneratable finiteAugmentationClass := by
  apply uniformlyGeneratable_of_common_infinite_base
    paperNonpositiveIntegers_infinite
  intro L hL
  obtain ⟨A, _hAP, _hAfin, rfl⟩ := hL
  exact Set.subset_union_left

private def positiveIntegerPoint (n : ℕ) : ℤ := (n : ℤ) + 1

private theorem positiveIntegerPoint_injective :
    Function.Injective positiveIntegerPoint := by
  intro m n h
  have : (m : ℤ) = (n : ℤ) := by
    simpa [positiveIntegerPoint] using
      congrArg (fun z : ℤ ↦ z - 1) h
  exact_mod_cast this

private theorem positiveIntegerPoint_mem (n : ℕ) :
    positiveIntegerPoint n ∈ paperPositiveIntegers := by
  change 0 < (n : ℤ) + 1
  omega

theorem finiteAugmentationClass_infiniteVC :
    HasInfiniteVCDimension finiteAugmentationClass := by
  intro d
  let xs : Fin d → ℤ := fun i ↦ positiveIntegerPoint i
  refine ⟨xs, ?_⟩
  intro labels
  let chosen : Set (Fin d) := {i | labels i = true}
  let A : Set ℤ :=
    (fun i : Fin d ↦ positiveIntegerPoint i) '' chosen
  have hAfin : A.Finite := by
    exact Set.toFinite chosen |>.image
      (fun i : Fin d ↦ positiveIntegerPoint i)
  have hAP : A ⊆ paperPositiveIntegers := by
    rintro z ⟨i, _hi, rfl⟩
    exact positiveIntegerPoint_mem i
  let L : Set ℤ := paperNonpositiveIntegers ∪ A
  refine ⟨L, ⟨A, hAP, hAfin, rfl⟩, ?_⟩
  intro i
  have hnotBase : positiveIntegerPoint i ∉ paperNonpositiveIntegers := by
    change ¬((i : ℤ) + 1 ≤ 0)
    omega
  have hA : positiveIntegerPoint i ∈ A ↔ labels i = true := by
    constructor
    · rintro ⟨j, hj, hji⟩
      have hij : j = i := by
        apply Fin.ext
        exact positiveIntegerPoint_injective hji
      simpa [chosen, hij] using hj
    · intro hi
      exact ⟨i, by simpa [chosen] using hi, rfl⟩
  change positiveIntegerPoint i ∈
      paperNonpositiveIntegers ∪ A ↔ labels i = true
  simpa [hnotBase] using hA

/-- The exact existential property in Theorem 4.1(i), at the paper's
finite-VC characterization boundary. -/
theorem theorem_4_1_i_combinatorial_core :
    ∃ H : GenLimit.Generic.LanguageClass ℤ,
      H.Countable ∧ UniformlyGeneratable H ∧
        ¬PACLearnableViaVC H := by
  refine ⟨finiteAugmentationClass,
    finiteAugmentationClass_countable,
    finiteAugmentationClass_uus_and_uniform.2, ?_⟩
  exact not_pacViaVC_of_infinite finiteAugmentationClass_infiniteVC

/-! ## Appendix A.2: online learnable but not uniformly generatable -/

private theorem mem_blockLanguage_inl_iff
    (b : Bool) (e d j : ℕ) :
    Sum.inl (d, j) ∈ blockLanguage b e ↔ e = d ∧ j < d := by
  simp [blockLanguage, blockSet, blockFinset, blockTail, and_comm]
  omega

private theorem mem_blockLanguage_inr_iff
    (b c : Bool) (e n : ℕ) :
    Sum.inr (b, n) ∈ blockLanguage c e ↔ c = b := by
  simp [blockLanguage, blockSet, blockFinset, blockTail]

private theorem block_cross_positive_subsingleton_left_right
    (d j : ℕ) (b : Bool) (n : ℕ) :
    (labelClass
      (labelClass blockSeparationClass (Sum.inl (d, j)) true)
      (Sum.inr (b, n)) true).Subsingleton := by
  intro L hL K hK
  obtain ⟨⟨c, e⟩, rfl⟩ := hL.1.1
  obtain ⟨⟨cK, eK⟩, rfl⟩ := hK.1.1
  have hLe : e = d :=
    (mem_blockLanguage_inl_iff c e d j).mp (hL.1.2.mpr rfl) |>.1
  have hLc : c = b :=
    (mem_blockLanguage_inr_iff b c e n).mp (hL.2.mpr rfl)
  have hKe : eK = d :=
    (mem_blockLanguage_inl_iff cK eK d j).mp (hK.1.2.mpr rfl) |>.1
  have hKc : cK = b :=
    (mem_blockLanguage_inr_iff b cK eK n).mp (hK.2.mpr rfl)
  simp [hLe, hLc, hKe, hKc]

private theorem block_cross_positive_subsingleton_right_left
    (b : Bool) (n d j : ℕ) :
    (labelClass
      (labelClass blockSeparationClass (Sum.inr (b, n)) true)
      (Sum.inl (d, j)) true).Subsingleton := by
  intro L hL K hK
  obtain ⟨⟨c, e⟩, rfl⟩ := hL.1.1
  obtain ⟨⟨cK, eK⟩, rfl⟩ := hK.1.1
  have hLc : c = b :=
    (mem_blockLanguage_inr_iff b c e n).mp (hL.1.2.mpr rfl)
  have hLe : e = d :=
    (mem_blockLanguage_inl_iff c e d j).mp (hL.2.mpr rfl) |>.1
  have hKc : cK = b :=
    (mem_blockLanguage_inr_iff b cK eK n).mp (hK.1.2.mpr rfl)
  have hKe : eK = d :=
    (mem_blockLanguage_inl_iff cK eK d j).mp (hK.2.mpr rfl) |>.1
  simp [hLe, hLc, hKe, hKc]

/-- Appendix A.2's claim `L(H) ≤ 2` for the typed block realization of the
Lemma 3.9 even/odd construction. -/
theorem blockSeparationClass_onlineViaLittlestone :
    OnlineLearnableViaLittlestone blockSeparationClass := by
  refine ⟨2, ?_⟩
  rintro ⟨T, hT⟩
  cases T with
  | node root left right =>
      cases right with
      | node second rightLeft rightRight =>
          have hRootOne := hT.2
          have hSecondZero := hRootOne.1
          have hSecondOne := hRootOne.2
          cases root with
          | inl rootData =>
              obtain ⟨d, j⟩ := rootData
              cases second with
              | inl secondData =>
                  obtain ⟨e, k⟩ := secondData
                  obtain ⟨L₀, hL₀⟩ :=
                    littlestoneShattered_nonempty hSecondZero
                  obtain ⟨L₁, hL₁⟩ :=
                    littlestoneShattered_nonempty hSecondOne
                  obtain ⟨⟨c₀, q₀⟩, rfl⟩ := hL₀.1.1
                  obtain ⟨⟨c₁, q₁⟩, rfl⟩ := hL₁.1.1
                  have hq₀ :
                      q₀ = d ∧ j < d :=
                    (mem_blockLanguage_inl_iff c₀ q₀ d j).mp
                      (hL₀.1.2.mpr rfl)
                  have hq₁ :
                      q₁ = d ∧ j < d :=
                    (mem_blockLanguage_inl_iff c₁ q₁ d j).mp
                      (hL₁.1.2.mpr rfl)
                  have hk₁ :
                      q₁ = e ∧ k < e :=
                    (mem_blockLanguage_inl_iff c₁ q₁ e k).mp
                      (hL₁.2.mpr rfl)
                  have hk₀ :
                      Sum.inl (e, k) ∉
                        blockLanguage c₀ q₀ := by
                    intro hm
                    have : false = true := hL₀.2.mp hm
                    cases this
                  apply hk₀
                  apply (mem_blockLanguage_inl_iff c₀ q₀ e k).mpr
                  exact ⟨hq₀.1.trans (hq₁.1.symm.trans hk₁.1),
                    hk₁.2⟩
              | inr secondData =>
                  obtain ⟨b, n⟩ := secondData
                  exact no_depth_one_of_subsingleton
                    (block_cross_positive_subsingleton_left_right d j b n)
                    rightRight hSecondOne
          | inr rootData =>
              obtain ⟨b, n⟩ := rootData
              cases second with
              | inl secondData =>
                  obtain ⟨d, j⟩ := secondData
                  exact no_depth_one_of_subsingleton
                    (block_cross_positive_subsingleton_right_left b n d j)
                    rightRight hSecondOne
              | inr secondData =>
                  obtain ⟨c, m⟩ := secondData
                  obtain ⟨L₀, hL₀⟩ :=
                    littlestoneShattered_nonempty hSecondZero
                  obtain ⟨L₁, hL₁⟩ :=
                    littlestoneShattered_nonempty hSecondOne
                  obtain ⟨⟨p₀, q₀⟩, rfl⟩ := hL₀.1.1
                  obtain ⟨⟨p₁, q₁⟩, rfl⟩ := hL₁.1.1
                  have hp₀ : p₀ = b :=
                    (mem_blockLanguage_inr_iff b p₀ q₀ n).mp
                      (hL₀.1.2.mpr rfl)
                  have hp₁ : p₁ = b :=
                    (mem_blockLanguage_inr_iff b p₁ q₁ n).mp
                      (hL₁.1.2.mpr rfl)
                  have hc₁ : p₁ = c :=
                    (mem_blockLanguage_inr_iff c p₁ q₁ m).mp
                      (hL₁.2.mpr rfl)
                  have hc₀ :
                      Sum.inr (c, m) ∉ blockLanguage p₀ q₀ := by
                    intro hm
                    have : false = true := hL₀.2.mp hm
                    cases this
                  apply hc₀
                  apply (mem_blockLanguage_inr_iff c p₀ q₀ m).mpr
                  exact hp₀.trans (hp₁.symm.trans hc₁)

theorem blockSeparationClass_not_uniform :
    ¬UniformlyGeneratable blockSeparationClass :=
  closure_dimension_necessity blockSeparationClass_uus
    blockSeparationClass_infinite_closure_dimension

/-- The exact existential property in Theorem 4.1(ii), at the paper's
finite-Littlestone characterization boundary. -/
theorem theorem_4_1_ii_combinatorial_core :
    ∃ H : GenLimit.Generic.LanguageClass BlockUniverse,
      H.Countable ∧ OnlineLearnableViaLittlestone H ∧
        ¬UniformlyGeneratable H :=
  ⟨blockSeparationClass, blockSeparationClass_countable,
    blockSeparationClass_onlineViaLittlestone,
    blockSeparationClass_not_uniform⟩

/-! ## Appendix A.3(iii): online and uniformly generatable -/

def singletonSpikeLanguage (a : ℕ) : Set ℤ :=
  paperNonpositiveIntegers ∪ {positiveIntegerPoint a}

/-- Appendix A.3's class
`{x ↦ 1{x = a or x ≤ 0} : a ∈ ℕ}`. -/
def singletonSpikeClass : GenLimit.Generic.LanguageClass ℤ :=
  Set.range singletonSpikeLanguage

theorem singletonSpikeClass_countable :
    singletonSpikeClass.Countable :=
  Set.countable_range _

theorem singletonSpikeClass_uus_and_uniform :
    UUS singletonSpikeClass ∧ UniformlyGeneratable singletonSpikeClass := by
  apply uniformlyGeneratable_of_common_infinite_base
    paperNonpositiveIntegers_infinite
  intro L hL
  obtain ⟨a, rfl⟩ := hL
  exact Set.subset_union_left

private theorem singletonSpike_positive_subsingleton
    (x : ℤ) (hx : x ∉ paperNonpositiveIntegers) :
    (labelClass singletonSpikeClass x true).Subsingleton := by
  intro L hL K hK
  obtain ⟨a, rfl⟩ := hL.1
  obtain ⟨b, rfl⟩ := hK.1
  have hxa : x = positiveIntegerPoint a := by
    have hxmem : x ∈ singletonSpikeLanguage a := hL.2.mpr rfl
    rcases hxmem with hxbase | hxsingle
    · exact False.elim (hx hxbase)
    · simpa using hxsingle
  have hxb : x = positiveIntegerPoint b := by
    have hxmem : x ∈ singletonSpikeLanguage b := hK.2.mpr rfl
    rcases hxmem with hxbase | hxsingle
    · exact False.elim (hx hxbase)
    · simpa using hxsingle
  have hab : a = b :=
    positiveIntegerPoint_injective (hxa.symm.trans hxb)
  simp [hab]

theorem singletonSpikeClass_onlineViaLittlestone :
    OnlineLearnableViaLittlestone singletonSpikeClass := by
  refine ⟨1, ?_⟩
  rintro ⟨T, hT⟩
  cases T with
  | node root left right =>
      obtain ⟨L₀, hL₀⟩ :=
        littlestoneShattered_nonempty hT.1
      have hrootNotL₀ : root ∉ L₀ := by
        intro hm
        have : false = true := hL₀.2.mp hm
        cases this
      have hrootNotBase :
          root ∉ paperNonpositiveIntegers := by
        intro hroot
        obtain ⟨a, rfl⟩ := hL₀.1
        exact hrootNotL₀ (Set.mem_union_left _ hroot)
      exact no_depth_one_of_subsingleton
        (singletonSpike_positive_subsingleton root hrootNotBase)
        right hT.2

/-- The exact existential property in Theorem 4.1(iii), at the paper's
finite-Littlestone characterization boundary. -/
theorem theorem_4_1_iii_combinatorial_core :
    ∃ H : GenLimit.Generic.LanguageClass ℤ,
      H.Countable ∧ OnlineLearnableViaLittlestone H ∧
        UniformlyGeneratable H :=
  ⟨singletonSpikeClass, singletonSpikeClass_countable,
    singletonSpikeClass_onlineViaLittlestone,
    singletonSpikeClass_uus_and_uniform.2⟩

/-! ## Appendix A.3(v): the threshold class -/

/-- The source's threshold support `{x | x ≥ a}`. -/
def thresholdLanguage (a : ℕ) : Set ℕ := {x | a ≤ x}

def thresholdClass : GenLimit.Generic.LanguageClass ℕ :=
  Set.range thresholdLanguage

@[simp] private theorem mem_thresholdLanguage_iff (a x : ℕ) :
    x ∈ thresholdLanguage a ↔ a ≤ x :=
  Iff.rfl

theorem thresholdClass_countable : thresholdClass.Countable :=
  Set.countable_range _

theorem thresholdLanguage_infinite (a : ℕ) :
    (thresholdLanguage a).Infinite := by
  apply (Set.infinite_range_of_injective
    (fun m n h ↦ Nat.add_left_cancel h :
      Function.Injective (fun n : ℕ ↦ a + n))).mono
  rintro x ⟨n, rfl⟩
  exact Nat.le_add_right a n

theorem thresholdClass_uus : UUS thresholdClass := by
  intro L hL
  obtain ⟨a, rfl⟩ := hL
  exact thresholdLanguage_infinite a

theorem thresholdClass_uniform :
    UniformlyGeneratable thresholdClass := by
  apply (uniform_generatability_iff_finite_closure_dimension
    thresholdClass_uus).2
  refine ⟨0, ?_, Or.inl rfl⟩
  intro S hcard _hVS
  have hSnonempty : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    subst S
    simp at hcard
  obtain ⟨x, hxS⟩ := hSnonempty
  apply (thresholdLanguage_infinite x).mono
  intro y hxy L hL
  obtain ⟨a, rfl⟩ := hL.1
  change x ≤ y at hxy
  change a ≤ y
  have hax : a ≤ x := hL.2 hxS
  exact hax.trans hxy

private theorem threshold_not_pairShattered_of_ne
    {x y : ℕ} (hxy : x ≠ y) :
    ¬PairShattered thresholdClass x y := by
  intro hPair
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · obtain ⟨L, hL, hx, hy⟩ := hPair true false
    obtain ⟨a, rfl⟩ := hL
    have hax : a ≤ x := hx.mpr rfl
    have hay : a ≤ y := hax.trans hlt.le
    have : false = true := hy.mp hay
    cases this
  · obtain ⟨L, hL, hx, hy⟩ := hPair false true
    obtain ⟨a, rfl⟩ := hL
    have hay : a ≤ y := hy.mpr rfl
    have hax : a ≤ x := hay.trans hgt.le
    have : false = true := hx.mp hax
    cases this

theorem thresholdClass_pacViaVC :
    PACLearnableViaVC thresholdClass := by
  refine ⟨1, ?_⟩
  intro xs hxs
  have hinj := vcShatters_injective hxs
  have hne : xs (0 : Fin 2) ≠ xs (1 : Fin 2) := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (hinj h)
  exact threshold_not_pairShattered_of_ne hne
    (pairShattered_of_vcShatters hxs (by decide))

/-- Thresholds whose parameters lie in a finite interval of length `2^d`. -/
private def thresholdIntervalClass (lo d : ℕ) :
    GenLimit.Generic.LanguageClass ℕ :=
  {L | ∃ a : ℕ, lo ≤ a ∧ a < lo + 2 ^ d ∧
    L = thresholdLanguage a}

/-- The complete binary-search tree used to witness unbounded Littlestone
dimension of thresholds. -/
private def thresholdTree (lo : ℕ) :
    (d : ℕ) → LittlestoneTree ℕ d
  | 0 => .leaf
  | d + 1 =>
      .node (lo + 2 ^ d - 1)
        (thresholdTree (lo + 2 ^ d) d)
        (thresholdTree lo d)

private theorem thresholdInterval_shatters
    (lo d : ℕ) :
    LittlestoneShattered (thresholdTree lo d)
      (thresholdIntervalClass lo d) := by
  induction d generalizing lo with
  | zero =>
      refine ⟨thresholdLanguage lo, ?_⟩
      exact ⟨lo, le_rfl, by simp, rfl⟩
  | succ d ih =>
      change
        LittlestoneShattered (thresholdTree (lo + 2 ^ d) d)
            (labelClass (thresholdIntervalClass lo (d + 1))
              (lo + 2 ^ d - 1) false) ∧
          LittlestoneShattered (thresholdTree lo d)
            (labelClass (thresholdIntervalClass lo (d + 1))
              (lo + 2 ^ d - 1) true)
      constructor
      · apply littlestoneShattered_mono
          (H := thresholdIntervalClass (lo + 2 ^ d) d)
          (K := labelClass (thresholdIntervalClass lo (d + 1))
            (lo + 2 ^ d - 1) false)
        · intro L hL
          obtain ⟨a, haLo, haHi, rfl⟩ := hL
          refine ⟨⟨a, ?_, ?_, rfl⟩, ?_⟩
          · omega
          · simp only [pow_succ]
            omega
          · simp only [mem_thresholdLanguage_iff, Bool.false_eq_true,
              iff_false]
            omega
        · exact ih (lo + 2 ^ d)
      · apply littlestoneShattered_mono
          (H := thresholdIntervalClass lo d)
          (K := labelClass (thresholdIntervalClass lo (d + 1))
            (lo + 2 ^ d - 1) true)
        · intro L hL
          obtain ⟨a, haLo, haHi, rfl⟩ := hL
          refine ⟨⟨a, haLo, ?_, rfl⟩, ?_⟩
          · simp only [pow_succ]
            omega
          · simp only [mem_thresholdLanguage_iff]
            have hpow : 0 < 2 ^ d := pow_pos (by decide) _
            have ha : a ≤ lo + 2 ^ d - 1 := by omega
            simp [ha]
        · exact ih lo

theorem thresholdClass_infiniteLittlestone :
    HasInfiniteLittlestoneDimension thresholdClass := by
  intro d
  refine ⟨thresholdTree 0 d, ?_⟩
  apply littlestoneShattered_mono
    (H := thresholdIntervalClass 0 d)
    (K := thresholdClass)
  · intro L hL
    obtain ⟨a, _haLo, _haHi, rfl⟩ := hL
    exact ⟨a, rfl⟩
  · exact thresholdInterval_shatters 0 d

theorem thresholdClass_not_onlineViaLittlestone :
    ¬OnlineLearnableViaLittlestone thresholdClass :=
  not_onlineViaLittlestone_of_infinite
    thresholdClass_infiniteLittlestone

/-- The exact existential property in Theorem 4.1(v), at the paper's
finite-VC/finite-Littlestone characterization boundary. -/
theorem theorem_4_1_v_combinatorial_core :
    ∃ H : GenLimit.Generic.LanguageClass ℕ,
      H.Countable ∧ PACLearnableViaVC H ∧
        UniformlyGeneratable H ∧
        ¬OnlineLearnableViaLittlestone H :=
  ⟨thresholdClass, thresholdClass_countable,
    thresholdClass_pacViaVC, thresholdClass_uniform,
    thresholdClass_not_onlineViaLittlestone⟩

/-! ## Appendix A.3(iv): threshold union the block obstruction -/

/-- Embed a language on the left summand, with no points on the right. -/
def liftLeftLanguage (L : Set α) : Set (α ⊕ β) :=
  {z | match z with
    | Sum.inl x => x ∈ L
    | Sum.inr _ => False}

/-- Embed a language on the right summand, with no points on the left. -/
def liftRightLanguage (L : Set β) : Set (α ⊕ β) :=
  {z | match z with
    | Sum.inl _ => False
    | Sum.inr y => y ∈ L}

def liftLeftClass (H : GenLimit.Generic.LanguageClass α) :
    GenLimit.Generic.LanguageClass (α ⊕ β) :=
  liftLeftLanguage '' H

def liftRightClass (H : GenLimit.Generic.LanguageClass β) :
    GenLimit.Generic.LanguageClass (α ⊕ β) :=
  liftRightLanguage '' H

abbrev ThresholdBlockUniverse := ℕ ⊕ BlockUniverse

/-- A typed disjoint-summand realization of the Appendix union
`H_thresh ∪ H_e ∪ H_o`.  The disjoint embedding preserves each component's
shattering and closure obstruction while making the source's two roles of
positive examples explicit. -/
def thresholdBlockClass :
    GenLimit.Generic.LanguageClass ThresholdBlockUniverse :=
  liftLeftClass thresholdClass ∪
    liftRightClass blockSeparationClass

theorem thresholdBlockClass_countable :
    thresholdBlockClass.Countable := by
  apply (thresholdClass_countable.image liftLeftLanguage).union
    (blockSeparationClass_countable.image liftRightLanguage)

theorem thresholdBlockClass_uus :
    UUS thresholdBlockClass := by
  intro L hL
  rcases hL with hLeft | hRight
  · obtain ⟨K, hK, rfl⟩ := hLeft
    obtain ⟨a, rfl⟩ := hK
    apply (Set.infinite_range_of_injective
      (fun m n h ↦ Nat.add_left_cancel (Sum.inl.inj h) :
        Function.Injective
          (fun n : ℕ ↦ Sum.inl (a + n) :
            ℕ → ThresholdBlockUniverse))).mono
    rintro z ⟨n, rfl⟩
    exact Nat.le_add_right a n
  · obtain ⟨K, hK, rfl⟩ := hRight
    obtain ⟨⟨b, d⟩, rfl⟩ := hK
    apply (Set.infinite_range_of_injective
      (fun m n h ↦ by
        have h₁ := Sum.inr.inj h
        have h₂ := Sum.inr.inj h₁
        exact Prod.mk.inj h₂ |>.2 :
        Function.Injective
          (fun n : ℕ ↦
            (Sum.inr (Sum.inr (b, n)) :
              ThresholdBlockUniverse)))).mono
    rintro z ⟨n, rfl⟩
    simp [liftRightLanguage, blockLanguage, blockTail]

private def liftedBlockFinset (d : ℕ) :
    Finset ThresholdBlockUniverse :=
  (blockFinset d).image Sum.inr

private theorem liftedBlockFinset_card (d : ℕ) :
    (liftedBlockFinset d).card = d := by
  unfold liftedBlockFinset
  rw [Finset.card_image_iff.mpr]
  · exact blockFinset_card d
  · intro x _hx y _hy hxy
    exact Sum.inr.inj hxy

private theorem commonCore_thresholdBlock_eq (d : ℕ) :
    commonCore thresholdBlockClass (liftedBlockFinset d) =
      liftRightLanguage (blockSet d) := by
  apply Set.Subset.antisymm
  · intro z hz
    cases z with
    | inl n =>
        have hRightFalse :
            liftRightLanguage (blockLanguage false d) ∈
              versionSpace thresholdBlockClass
                (liftedBlockFinset d) := by
          constructor
          · exact Or.inr
              ⟨blockLanguage false d,
                ⟨(false, d), rfl⟩, rfl⟩
          · intro y hy
            simp only [liftedBlockFinset, Finset.mem_coe,
              Finset.mem_image] at hy
            obtain ⟨u, hu, rfl⟩ := hy
            change u ∈ blockLanguage false d
            exact Set.subset_union_left hu
        exact False.elim (hz _ hRightFalse)
    | inr u =>
        have huCore :
            u ∈ commonCore blockSeparationClass
              (blockFinset d) := by
          intro K hK
          have hLifted :
              liftRightLanguage K ∈
                versionSpace thresholdBlockClass
                  (liftedBlockFinset d) := by
            constructor
            · exact Or.inr ⟨K, hK.1, rfl⟩
            · intro y hy
              simp only [liftedBlockFinset, Finset.mem_coe,
                Finset.mem_image] at hy
              obtain ⟨v, hv, rfl⟩ := hy
              exact hK.2 hv
          exact hz _ hLifted
        rw [commonCore_blockSeparationClass_eq] at huCore
        exact huCore
  · intro z hz
    cases z with
    | inl n => exact False.elim hz
    | inr u =>
        apply sample_subset_commonCore
        change Sum.inr u ∈ liftedBlockFinset d
        exact Finset.mem_image.mpr ⟨u, hz, rfl⟩

theorem thresholdBlockClass_infiniteClosure :
    HasInfiniteClosureDimension thresholdBlockClass := by
  intro d
  refine ⟨liftedBlockFinset d, (liftedBlockFinset_card d).ge, ?_⟩
  constructor
  · refine ⟨liftRightLanguage (blockLanguage false d), ?_, ?_⟩
    · exact Or.inr
        ⟨blockLanguage false d, ⟨(false, d), rfl⟩, rfl⟩
    · intro z hz
      simp only [liftedBlockFinset, Finset.mem_coe,
        Finset.mem_image] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      exact Set.subset_union_left hu
  · rw [show GenLimit.Generic.commonCore thresholdBlockClass
        (liftedBlockFinset d) = liftRightLanguage (α := ℕ) (blockSet d) from
        commonCore_thresholdBlock_eq d]
    have heq :
        liftRightLanguage (α := ℕ) (blockSet d) =
          (fun u : BlockUniverse ↦
            (Sum.inr u : ThresholdBlockUniverse)) ''
              (blockSet d) := by
      ext z
      cases z <;> simp [liftRightLanguage]
    rw [heq]
    exact (blockFinset d).finite_toSet.image
      (fun u : BlockUniverse ↦
        (Sum.inr u : ThresholdBlockUniverse))

theorem thresholdBlockClass_not_uniform :
    ¬UniformlyGeneratable thresholdBlockClass :=
  closure_dimension_necessity thresholdBlockClass_uus
    thresholdBlockClass_infiniteClosure

private theorem not_pairShattered_self
    (H : GenLimit.Generic.LanguageClass α) (x : α) :
    ¬PairShattered H x x := by
  intro h
  obtain ⟨L, _hL, hx, hx'⟩ := h true false
  have hm : x ∈ L := hx.mpr rfl
  have : false = true := hx'.mp hm
  cases this

private theorem thresholdBlock_left_not_pair
    {x y : ℕ} (hxy : x ≠ y) :
    ¬PairShattered thresholdBlockClass
      (Sum.inl x) (Sum.inl y) := by
  intro hPair
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · obtain ⟨L, hL, hx, hy⟩ := hPair true false
    rcases hL with hLeft | hRight
    · obtain ⟨K, hK, rfl⟩ := hLeft
      obtain ⟨a, rfl⟩ := hK
      have hax : a ≤ x := hx.mpr rfl
      have hay : a ≤ y := hax.trans hlt.le
      have : false = true := hy.mp hay
      cases this
    · obtain ⟨K, _hK, rfl⟩ := hRight
      exact False.elim (hx.mpr rfl)
  · obtain ⟨L, hL, hx, hy⟩ := hPair false true
    rcases hL with hLeft | hRight
    · obtain ⟨K, hK, rfl⟩ := hLeft
      obtain ⟨a, rfl⟩ := hK
      have hay : a ≤ y := hy.mpr rfl
      have hax : a ≤ x := hay.trans hgt.le
      have : false = true := hx.mp hax
      cases this
    · obtain ⟨K, _hK, rfl⟩ := hRight
      exact False.elim (hy.mpr rfl)

private theorem thresholdBlock_cross_not_pair
    (x : ℕ) (u : BlockUniverse) :
    ¬PairShattered thresholdBlockClass
      (Sum.inl x) (Sum.inr u) := by
  intro hPair
  obtain ⟨L, hL, hx, hu⟩ := hPair true true
  rcases hL with hLeft | hRight
  · obtain ⟨K, _hK, rfl⟩ := hLeft
    exact False.elim (hu.mpr rfl)
  · obtain ⟨K, _hK, rfl⟩ := hRight
    exact False.elim (hx.mpr rfl)

private theorem thresholdBlock_cross_not_pair'
    (u : BlockUniverse) (x : ℕ) :
    ¬PairShattered thresholdBlockClass
      (Sum.inr u) (Sum.inl x) := by
  intro hPair
  obtain ⟨L, hL, hu, hx⟩ := hPair true true
  rcases hL with hLeft | hRight
  · obtain ⟨K, _hK, rfl⟩ := hLeft
    exact False.elim (hu.mpr rfl)
  · obtain ⟨K, _hK, rfl⟩ := hRight
    exact False.elim (hx.mpr rfl)

private theorem thresholdBlock_right_inl_not_pair
    (p q : ℕ × ℕ) :
    ¬PairShattered thresholdBlockClass
      (Sum.inr (Sum.inl p)) (Sum.inr (Sum.inl q)) := by
  intro hPair
  by_cases hd : p.1 = q.1
  · obtain ⟨Lplus, hLplus, hpPlus, hqPlus⟩ :=
      hPair true true
    have hqValid : q.2 < q.1 := by
      rcases hLplus with hLeft | hRight
      · obtain ⟨K, _hK, rfl⟩ := hLeft
        exact False.elim (hpPlus.mpr rfl)
      · obtain ⟨K, hK, rfl⟩ := hRight
        obtain ⟨⟨b, e⟩, rfl⟩ := hK
        exact
          ((mem_blockLanguage_inl_iff b e q.1 q.2).mp
            (hqPlus.mpr rfl)).2
    obtain ⟨L, hL, hp, hq⟩ := hPair true false
    rcases hL with hLeft | hRight
    · obtain ⟨K, _hK, rfl⟩ := hLeft
      exact False.elim (hp.mpr rfl)
    · obtain ⟨K, hK, rfl⟩ := hRight
      obtain ⟨⟨b, e⟩, rfl⟩ := hK
      have hep :=
        (mem_blockLanguage_inl_iff b e p.1 p.2).mp
          (hp.mpr rfl)
      have hqmem :
          Sum.inl q ∈ blockLanguage b e :=
        (mem_blockLanguage_inl_iff b e q.1 q.2).mpr
          ⟨hep.1.trans hd, hqValid⟩
      have : false = true := hq.mp hqmem
      cases this
  · obtain ⟨L, hL, hp, hq⟩ := hPair true true
    rcases hL with hLeft | hRight
    · obtain ⟨K, _hK, rfl⟩ := hLeft
      exact False.elim (hp.mpr rfl)
    · obtain ⟨K, hK, rfl⟩ := hRight
      obtain ⟨⟨b, e⟩, rfl⟩ := hK
      have hep :=
        (mem_blockLanguage_inl_iff b e p.1 p.2).mp
          (hp.mpr rfl)
      have heq :=
        (mem_blockLanguage_inl_iff b e q.1 q.2).mp
          (hq.mpr rfl)
      exact hd (hep.1.symm.trans heq.1)

private theorem thresholdBlock_right_inr_not_pair
    (p q : Bool × ℕ) :
    ¬PairShattered thresholdBlockClass
      (Sum.inr (Sum.inr p)) (Sum.inr (Sum.inr q)) := by
  intro hPair
  by_cases hb : p.1 = q.1
  · obtain ⟨L, hL, hp, hq⟩ := hPair true false
    rcases hL with hLeft | hRight
    · obtain ⟨K, _hK, rfl⟩ := hLeft
      exact False.elim (hp.mpr rfl)
    · obtain ⟨K, hK, rfl⟩ := hRight
      obtain ⟨⟨b, e⟩, rfl⟩ := hK
      have hbp :=
        (mem_blockLanguage_inr_iff p.1 b e p.2).mp
          (hp.mpr rfl)
      have hqmem :
          Sum.inr q ∈ blockLanguage b e :=
        (mem_blockLanguage_inr_iff q.1 b e q.2).mpr
          (hbp.trans hb)
      have : false = true := hq.mp hqmem
      cases this
  · obtain ⟨L, hL, hp, hq⟩ := hPair true true
    rcases hL with hLeft | hRight
    · obtain ⟨K, _hK, rfl⟩ := hLeft
      exact False.elim (hp.mpr rfl)
    · obtain ⟨K, hK, rfl⟩ := hRight
      obtain ⟨⟨b, e⟩, rfl⟩ := hK
      have hbp :=
        (mem_blockLanguage_inr_iff p.1 b e p.2).mp
          (hp.mpr rfl)
      have hbq :=
        (mem_blockLanguage_inr_iff q.1 b e q.2).mp
          (hq.mpr rfl)
      exact hb (hbp.symm.trans hbq)

theorem thresholdBlockClass_pacViaVC :
    PACLearnableViaVC thresholdBlockClass := by
  refine ⟨2, ?_⟩
  intro xs hxs
  have hinj := vcShatters_injective hxs
  have h01 :
      PairShattered thresholdBlockClass
        (xs (0 : Fin 3)) (xs (1 : Fin 3)) :=
    pairShattered_of_vcShatters hxs (by decide)
  have h02 :
      PairShattered thresholdBlockClass
        (xs (0 : Fin 3)) (xs (2 : Fin 3)) :=
    pairShattered_of_vcShatters hxs (by decide)
  have h12 :
      PairShattered thresholdBlockClass
        (xs (1 : Fin 3)) (xs (2 : Fin 3)) :=
    pairShattered_of_vcShatters hxs (by decide)
  cases h0 : xs (0 : Fin 3) with
  | inl x =>
      cases h1 : xs (1 : Fin 3) with
      | inl y =>
          apply thresholdBlock_left_not_pair
              (by
                intro hxy
                apply (by decide : (0 : Fin 3) ≠ 1)
                apply hinj
                simpa [h0, h1] using hxy)
          simpa [h0, h1] using h01
      | inr u =>
          exact thresholdBlock_cross_not_pair x u
            (by simpa [h0, h1] using h01)
  | inr u =>
      cases h1 : xs (1 : Fin 3) with
      | inl x =>
          exact thresholdBlock_cross_not_pair' u x
            (by simpa [h0, h1] using h01)
      | inr v =>
          cases h2 : xs (2 : Fin 3) with
          | inl x =>
              exact thresholdBlock_cross_not_pair' u x
                (by simpa [h0, h2] using h02)
          | inr w =>
              cases u with
              | inl p =>
                  cases v with
                  | inl q =>
                      exact thresholdBlock_right_inl_not_pair p q
                        (by simpa [h0, h1] using h01)
                  | inr q =>
                      cases w with
                      | inl r =>
                          exact thresholdBlock_right_inl_not_pair p r
                            (by simpa [h0, h2] using h02)
                      | inr r =>
                          exact thresholdBlock_right_inr_not_pair q r
                            (by simpa [h1, h2] using h12)
              | inr p =>
                  cases v with
                  | inl q =>
                      cases w with
                      | inl r =>
                          exact thresholdBlock_right_inl_not_pair q r
                            (by simpa [h1, h2] using h12)
                      | inr r =>
                          exact thresholdBlock_right_inr_not_pair p r
                            (by simpa [h0, h2] using h02)
                  | inr q =>
                      exact thresholdBlock_right_inr_not_pair p q
                        (by simpa [h0, h1] using h01)

private def liftLeftTree :
    {d : ℕ} → LittlestoneTree α d →
      LittlestoneTree (α ⊕ β) d
  | 0, .leaf => .leaf
  | _ + 1, .node x left right =>
      .node (Sum.inl x) (liftLeftTree left) (liftLeftTree right)

private theorem liftLeftTree_shattered
    {H : GenLimit.Generic.LanguageClass α}
    {d : ℕ} {T : LittlestoneTree α d}
    (hT : LittlestoneShattered T H) :
    LittlestoneShattered (liftLeftTree (β := β) T)
      (liftLeftClass H) := by
  induction T generalizing H with
  | leaf =>
      obtain ⟨L, hL⟩ := hT
      exact ⟨liftLeftLanguage L, ⟨L, hL, rfl⟩⟩
  | @node d x left right ihLeft ihRight =>
      constructor
      · apply littlestoneShattered_mono
          (H := liftLeftClass (labelClass H x false))
          (K := labelClass (liftLeftClass H)
            (Sum.inl x) false)
        · intro L hL
          obtain ⟨K, hK, rfl⟩ := hL
          exact ⟨⟨K, hK.1, rfl⟩, hK.2⟩
        · exact ihLeft hT.1
      · apply littlestoneShattered_mono
          (H := liftLeftClass (labelClass H x true))
          (K := labelClass (liftLeftClass H)
            (Sum.inl x) true)
        · intro L hL
          obtain ⟨K, hK, rfl⟩ := hL
          exact ⟨⟨K, hK.1, rfl⟩, hK.2⟩
        · exact ihRight hT.2

theorem thresholdBlockClass_infiniteLittlestone :
    HasInfiniteLittlestoneDimension thresholdBlockClass := by
  intro d
  obtain ⟨T, hT⟩ := thresholdClass_infiniteLittlestone d
  refine ⟨liftLeftTree (β := BlockUniverse) T, ?_⟩
  apply littlestoneShattered_mono
    (H := liftLeftClass thresholdClass)
    (K := thresholdBlockClass)
  · exact fun _ h ↦ Or.inl h
  · exact liftLeftTree_shattered hT

theorem thresholdBlockClass_not_online :
    ¬OnlineLearnableViaLittlestone thresholdBlockClass :=
  not_onlineViaLittlestone_of_infinite
    thresholdBlockClass_infiniteLittlestone

/-- The exact existential property in Theorem 4.1(iv), at the paper's
finite-VC/finite-Littlestone characterization boundary. -/
theorem theorem_4_1_iv_combinatorial_core :
    ∃ H : GenLimit.Generic.LanguageClass ThresholdBlockUniverse,
      H.Countable ∧ PACLearnableViaVC H ∧
        ¬OnlineLearnableViaLittlestone H ∧
        ¬UniformlyGeneratable H :=
  ⟨thresholdBlockClass, thresholdBlockClass_countable,
    thresholdBlockClass_pacViaVC,
    thresholdBlockClass_not_online,
    thresholdBlockClass_not_uniform⟩

/-! ## Appendix A.3(vi): cofinite languages -/

/-- The source's cofinite class `{x ↦ 1{x ∉ A} : A ⊆ ℕ, |A| < ∞}`. -/
def cofiniteClass : GenLimit.Generic.LanguageClass ℕ :=
  {L | ∃ A : Set ℕ, A.Finite ∧ L = Aᶜ}

theorem cofiniteClass_countable : cofiniteClass.Countable := by
  have hFiniteSets :
      ({A : Set ℕ | A.Finite} : Set (Set ℕ)).Countable :=
    Set.Countable.setOf_finite
  have hImage := hFiniteSets.image (fun A : Set ℕ ↦ Aᶜ)
  apply hImage.mono
  intro L hL
  obtain ⟨A, hA, rfl⟩ := hL
  exact ⟨A, hA, rfl⟩

theorem cofiniteClass_uus : UUS cofiniteClass := by
  intro L hL
  obtain ⟨A, hA, rfl⟩ := hL
  simpa only [Set.compl_eq_univ_diff] using
    (Set.infinite_univ.diff hA : (Set.univ \ A).Infinite)

theorem cofiniteClass_infiniteVC :
    HasInfiniteVCDimension cofiniteClass := by
  intro d
  let xs : Fin d → ℕ := fun i ↦ i
  refine ⟨xs, ?_⟩
  intro labels
  let bad : Finset ℕ :=
    (Finset.univ.filter (fun i : Fin d ↦ labels i = false)).image
      (fun i : Fin d ↦ (i : ℕ))
  let A : Set ℕ := ↑bad
  let L : Set ℕ := Aᶜ
  refine ⟨L, ⟨A, bad.finite_toSet, rfl⟩, ?_⟩
  intro i
  change (i : ℕ) ∉ bad ↔ labels i = true
  constructor
  · intro hi
    cases hlabel : labels i with
    | false =>
        exfalso
        apply hi
        apply Finset.mem_image.mpr
        exact ⟨i, by simp [hlabel], rfl⟩
    | true => rfl
  · intro hi hbad
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hbad
    have hEq : j = i := Fin.ext hji
    subst j
    have : labels i = false := by
      simpa using (Finset.mem_filter.mp hj).2
    rw [hi] at this
    cases this

theorem commonCore_cofiniteClass_eq (S : Finset ℕ) :
    commonCore cofiniteClass S = (↑S : Set ℕ) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxS
    let L : Set ℕ := ({x} : Set ℕ)ᶜ
    have hLClass : L ∈ cofiniteClass :=
      ⟨{x}, Set.finite_singleton x, rfl⟩
    have hSL : (↑S : Set ℕ) ⊆ L := by
      intro y hy
      change y ∉ ({x} : Set ℕ)
      simpa only [Set.mem_singleton_iff] using
        (fun hyx : y = x ↦ hxS (hyx ▸ hy))
    have hxL := hx L ⟨hLClass, hSL⟩
    exact hxL (by simp)
  · exact sample_subset_commonCore

theorem cofiniteClass_infiniteClosure :
    HasInfiniteClosureDimension cofiniteClass := by
  intro d
  let S : Finset ℕ := Finset.range d
  refine ⟨S, by simp [S], ?_⟩
  constructor
  · refine ⟨Set.univ, ?_, Set.subset_univ _⟩
    exact ⟨∅, Set.finite_empty, by simp⟩
  · rw [show GenLimit.Generic.commonCore cofiniteClass S = (↑S : Set ℕ) from
        commonCore_cofiniteClass_eq S]
    exact S.finite_toSet

theorem cofiniteClass_not_uniform :
    ¬UniformlyGeneratable cofiniteClass :=
  closure_dimension_necessity cofiniteClass_uus
    cofiniteClass_infiniteClosure

theorem cofiniteClass_not_pacViaVC :
    ¬PACLearnableViaVC cofiniteClass :=
  not_pacViaVC_of_infinite cofiniteClass_infiniteVC

/-- The exact existential property in Theorem 4.1(vi), at the paper's
finite-VC characterization boundary. -/
theorem theorem_4_1_vi_combinatorial_core :
    ∃ H : GenLimit.Generic.LanguageClass ℕ,
      H.Countable ∧ ¬PACLearnableViaVC H ∧
        ¬UniformlyGeneratable H :=
  ⟨cofiniteClass, cofiniteClass_countable,
    cofiniteClass_not_pacViaVC, cofiniteClass_not_uniform⟩

/-! ## Six-way combinatorial landscape -/

/-- All six Appendix A separation regions, packaged together.

The universes are the explicit countably infinite realizations used above.
The prediction predicates remain the finite-VC and finite-Littlestone
characterization proxies; bridges to literal Definitions 2.8 and 2.10 are
not claimed. -/
theorem theorem_4_1_combinatorial_core :
    (∃ H : GenLimit.Generic.LanguageClass ℤ,
      H.Countable ∧ UniformlyGeneratable H ∧
        ¬PACLearnableViaVC H) ∧
    (∃ H : GenLimit.Generic.LanguageClass BlockUniverse,
      H.Countable ∧ OnlineLearnableViaLittlestone H ∧
        ¬UniformlyGeneratable H) ∧
    (∃ H : GenLimit.Generic.LanguageClass ℤ,
      H.Countable ∧ OnlineLearnableViaLittlestone H ∧
        UniformlyGeneratable H) ∧
    (∃ H : GenLimit.Generic.LanguageClass ThresholdBlockUniverse,
      H.Countable ∧ PACLearnableViaVC H ∧
        ¬OnlineLearnableViaLittlestone H ∧
        ¬UniformlyGeneratable H) ∧
    (∃ H : GenLimit.Generic.LanguageClass ℕ,
      H.Countable ∧ PACLearnableViaVC H ∧
        UniformlyGeneratable H ∧
        ¬OnlineLearnableViaLittlestone H) ∧
    (∃ H : GenLimit.Generic.LanguageClass ℕ,
      H.Countable ∧ ¬PACLearnableViaVC H ∧
        ¬UniformlyGeneratable H) :=
  ⟨theorem_4_1_i_combinatorial_core,
    theorem_4_1_ii_combinatorial_core,
    theorem_4_1_iii_combinatorial_core,
    theorem_4_1_iv_combinatorial_core,
    theorem_4_1_v_combinatorial_core,
    theorem_4_1_vi_combinatorial_core⟩

end GenLimit.LiRamanTewari
