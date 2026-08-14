import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.Breadth

/-!
# Charikar--Pabbaraju Claim 5.2

Source: Moses Charikar and Chirag Pabbaraju, *Exploring Facets of Language
Generation in the Limit*, arXiv:2411.15364v2, Claim 5.2
(`claim:breadth-exhaustive-gen-separation`).

The paper uses the class consisting of the whole integer universe and all
integer co-singletons.  The exact-breadth interface in this library uses
`Nat` as its string encoding, so this file gives the isomorphic class on
`Nat`: index zero denotes the whole universe and index `i + 1` omits `i`.

The printed proof builds a direct adaptive diagonal.  The preceding
source proposition already proves the stronger reusable fact that exact
breadth implies Angluin's Condition with Existence.  We therefore derive
Claim 5.2 from that checked proposition and the co-singleton class's
elementary finite-tell-tale obstruction.
-/

namespace GenLimit.CharikarPabbaraju

open GenLimit.Generic

/-! ## The encoded co-singleton class -/

/-- An explicit `Nat` indexing of the class in Example 9 and Claim 5.2:
index zero is the whole universe, while index `i + 1` omits exactly `i`. -/
def coSingletonNatFamily : Generic.LanguageFamily ℕ
  | 0 => Set.univ
  | i + 1 => Set.univ \ {i}

/-- Collection-valued form of the same class. -/
def coSingletonNatClass : Generic.LanguageClass ℕ :=
  {K | K = Set.univ ∨ ∃ i : ℕ, K = Set.univ \ {i}}

theorem range_coSingletonNatFamily :
    Set.range coSingletonNatFamily = coSingletonNatClass := by
  ext K
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | zero =>
        exact Or.inl rfl
    | succ i =>
        exact Or.inr ⟨i, rfl⟩
  · intro hK
    rcases hK with rfl | ⟨i, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨i + 1, rfl⟩

theorem coSingletonNatFamily_infinite (i : ℕ) :
    (coSingletonNatFamily i).Infinite := by
  cases i with
  | zero =>
      exact Set.infinite_univ
  | succ i =>
      exact Set.infinite_univ.diff (Set.finite_singleton i)

theorem coSingletonNatFamily_nonempty (i : ℕ) :
    (coSingletonNatFamily i).Nonempty :=
  (coSingletonNatFamily_infinite i).nonempty

/-! ## The tell-tale obstruction and Claim 5.2 -/

/-- No finite sample distinguishes the whole universe from all of its
co-singletons. -/
theorem coSingletonNatFamily_no_telltale_for_univ (T : Finset ℕ) :
    ¬ IsAngluinTellTale (Set.range coSingletonNatFamily) Set.univ T := by
  intro hTell
  obtain ⟨i, hiT⟩ := T.exists_notMem
  let L' : Set ℕ := Set.univ \ {i}
  have hL' : L' ∈ Set.range coSingletonNatFamily := by
    exact ⟨i + 1, by simp [coSingletonNatFamily, L']⟩
  have hTL' : (↑T : Set ℕ) ⊆ L' := by
    intro n hn
    simp only [L', Set.mem_diff, Set.mem_univ, true_and,
      Set.mem_singleton_iff]
    intro hni
    exact hiT (hni ▸ hn)
  have hproper : L' ⊂ (Set.univ : Set ℕ) := by
    apply Set.ssubset_univ_iff.mpr
    exact (Set.ne_univ_iff_exists_notMem L').2 ⟨i, by simp [L']⟩
  exact hTell.2 L' hL' hTL' hproper

/-- Claim 5.2: the co-singleton collection from Example 9 cannot be
generated with exact breadth in the limit. -/
theorem claim_5_2 :
    ¬ BreadthGeneratable coSingletonNatFamily := by
  intro hBreadth
  obtain ⟨T, hTell⟩ :=
    generation_with_breadth_implies_angluinExistence
      coSingletonNatFamily_nonempty hBreadth Set.univ ⟨0, rfl⟩
  exact coSingletonNatFamily_no_telltale_for_univ T hTell

end GenLimit.CharikarPabbaraju
