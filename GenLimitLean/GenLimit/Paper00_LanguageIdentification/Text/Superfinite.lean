import GenLimit.Paper00_LanguageIdentification.Text.Finite
import GenLimit.Paper00_LanguageIdentification.Text.Locking
import GenLimit.Core.FiniteTellTale

/-!
# The superfinite obstruction for arbitrary positive text

This file derives Gold's semantic arbitrary-text superfinite result
in Section 8: For arbitrary text, the finite-cardinality languages
are ineffectively identifiable, but every proper superclass is not.
The argument has two steps:

1. a language identified from every text has a finite tell-tale relative to
   any class identified by the same learner;
2. an infinite language in a class containing every finite language cannot
   have such a tell-tale.

No effectiveness assumption is used here. This file does not formalize
Theorems I.8 and I.9, which are Gold's stronger effectiveness-sensitive results.
-/

namespace GenLimit
namespace Gold
namespace Text

/-- `D` is a finite tell-tale for `L` inside `𝒞`: among class members below
`L`, no proper sublanguage contains all of `D`. -/
abbrev IsTellTale (𝒞 : Set Language) (L : Language) (D : Finset ℕ) : Prop :=
  Generic.IsFiniteTellTale 𝒞 L D

private theorem prefixedText_presents
    {K : Language} {ρ : List ℕ}
    (hρK : HistoryIn ρ K)
    {base : ℕ → ℕ} (hbase : Presents base K) :
    Presents
      (fun t =>
        if ht : t < ρ.length then ρ.get ⟨t, ht⟩
        else base (t - ρ.length))
      K := by
  let stream : ℕ → ℕ := fun t =>
    if ht : t < ρ.length then ρ.get ⟨t, ht⟩
    else base (t - ρ.length)
  change Presents stream K
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    by_cases ht : t < ρ.length
    · simp only [stream, dif_pos ht]
      exact hρK _ (List.get_mem ρ ⟨t, ht⟩)
    · simp only [stream, dif_neg ht]
      rw [← hbase]
      exact ⟨t - ρ.length, rfl⟩
  · intro x hx
    rw [← hbase] at hx
    obtain ⟨n, rfl⟩ := hx
    refine ⟨ρ.length + n, ?_⟩
    have hnot : ¬ ρ.length + n < ρ.length := by omega
    simp [stream, hnot]

private theorem prefixedText_prefix
    {ρ : List ℕ} {base : ℕ → ℕ} :
    textPrefix
      (fun t =>
        if ht : t < ρ.length then ρ.get ⟨t, ht⟩
        else base (t - ρ.length))
      ρ.length = ρ := by
  let stream : ℕ → ℕ := fun t =>
    if ht : t < ρ.length then ρ.get ⟨t, ht⟩
    else base (t - ρ.length)
  change textPrefix stream ρ.length = ρ
  apply List.ext_get
  · simp
  · intro i h₁ h₂
    simp only [textPrefix, List.get_eq_getElem, List.getElem_map,
      List.getElem_range, stream, dif_pos h₂]

private theorem target_eq_of_locking_and_class_identification
    {M : TextLearner Language} {𝒞 : Set Language}
    {L K : Language} {ρ : List ℕ}
    (hlock : IsLocking M L ρ)
    (hclass : SemanticallyIdentifiesClass M 𝒞)
    (hK𝒞 : K ∈ 𝒞)
    (hρK : HistoryIn ρ K)
    (hKL : K ⊆ L)
    (hK : K.Nonempty) :
    K = L := by
  obtain ⟨base, hbase⟩ := exists_presentation_of_nonempty hK
  let stream : ℕ → ℕ := fun t =>
    if ht : t < ρ.length then ρ.get ⟨t, ht⟩
    else base (t - ρ.length)
  have hstreamP : Presents stream K := by
    exact prefixedText_presents hρK hbase
  have hprefix : textPrefix stream ρ.length = ρ := by
    exact prefixedText_prefix
  obtain ⟨guess, hguess, T, hT⟩ := hclass K hK𝒞 stream hstreamP
  have hguess' : guess = K := by
    simpa [semanticNaming] using hguess
  let t := max T ρ.length
  have hρPrefix : ρ <+: textPrefix stream t := by
    rw [List.prefix_iff_eq_take]
    have hlen : ρ.length ≤ t := le_max_right _ _
    rw [← hprefix]
    rw [textPrefix, textPrefix, ← List.map_take]
    simp [hlen]
  obtain ⟨τ, hτ⟩ := hρPrefix
  have hτK : HistoryIn τ K := by
    have hall := historyIn_textPrefix hstreamP t
    rw [← hτ, historyIn_append] at hall
    exact hall.2
  have hτL : HistoryIn τ L := hτK.mono hKL
  have hML : M (textPrefix stream t) = L := by
    rw [← hτ]
    exact hlock.2.2 τ hτL
  have hMK : M (textPrefix stream t) = K :=
    (hT t (le_max_left _ _)).trans hguess'
  exact hMK.symm.trans hML

/-- **Finite tell-tale necessity.**  If one semantic learner identifies every
language in `𝒞`, then every infinite member of `𝒞` has a finite tell-tale.

The proof strengthens a locking sequence by one target element.  This makes
its finite content nonempty, avoiding the vacuity of exact stream
presentations for the empty language. -/
theorem finite_tellTale_of_semantic_identification
    {M : TextLearner Language} {𝒞 : Set Language} {L : Language}
    (hclass : SemanticallyIdentifiesClass M 𝒞)
    (hL𝒞 : L ∈ 𝒞)
    (hL : L.Infinite) :
    ∃ D : Finset ℕ, IsTellTale 𝒞 L D := by
  obtain ⟨x, hxL⟩ := hL.nonempty
  obtain ⟨σ, hσL, hMσ, hstable⟩ :=
    exists_locking_of_identifiesLanguage hL.nonempty (hclass L hL𝒞)
  let ρ := σ ++ [x]
  have hρL : HistoryIn ρ L := by
    dsimp [ρ]
    exact historyIn_append.mpr
      ⟨hσL, historyIn_singleton.mpr hxL⟩
  have hMρ : M ρ = L := by
    exact hstable [x] (historyIn_singleton.mpr hxL)
  have hρlock : IsLocking M L ρ := by
    refine ⟨hρL, hMρ, ?_⟩
    intro τ hτL
    have htail : HistoryIn ([x] ++ τ) L :=
      historyIn_append.mpr
        ⟨historyIn_singleton.mpr hxL, hτL⟩
    simpa only [ρ, List.append_assoc] using hstable ([x] ++ τ) htail
  refine ⟨ρ.toFinset, ?_⟩
  constructor
  · intro y hy
    exact hρL y (List.mem_toFinset.mp hy)
  · intro K hK𝒞 hDK hKL
    have hxD : x ∈ ρ.toFinset := by
      simp [ρ]
    have hxK : x ∈ K := hDK hxD
    have hρK : HistoryIn ρ K := by
      intro y hy
      exact hDK (List.mem_toFinset.mpr hy)
    exact target_eq_of_locking_and_class_identification
      hρlock hclass hK𝒞 hρK hKL ⟨x, hxK⟩

/-- Existence form of finite tell-tale necessity. -/
theorem finite_tellTale_of_semanticallyIdentifiable
    {𝒞 : Set Language} {L : Language}
    (hident : SemanticallyIdentifiable 𝒞)
    (hL𝒞 : L ∈ 𝒞)
    (hL : L.Infinite) :
    ∃ D : Finset ℕ, IsTellTale 𝒞 L D := by
  obtain ⟨M, hM⟩ := hident
  exact finite_tellTale_of_semantic_identification hM hL𝒞 hL

/-- A class contains all finite languages. -/
def ContainsAllFiniteLanguages (𝒞 : Set Language) : Prop :=
  finiteLanguages ⊆ 𝒞

/-- A class is superfinite when it contains every finite language and at least
one infinite language. -/
def IsSuperfinite (𝒞 : Set Language) : Prop :=
  ContainsAllFiniteLanguages 𝒞 ∧
    ∃ L, L ∈ 𝒞 ∧ L.Infinite

/-- **Gold's superfinite theorem, semantic arbitrary-text form.**  No
possibly noncomputable semantic learner identifies a class containing every
finite language and an infinite language from all exact positive texts. -/
theorem superfinite_not_semanticallyIdentifiable
    {𝒞 : Set Language} (h𝒞 : IsSuperfinite 𝒞) :
    ¬ SemanticallyIdentifiable 𝒞 := by
  rintro hident
  obtain ⟨L, hL𝒞, hL⟩ := h𝒞.2
  obtain ⟨D, hD⟩ :=
    finite_tellTale_of_semanticallyIdentifiable hident hL𝒞 hL
  have hDL : (↑D : Language) = L :=
    hD.2 (↑D : Language) (h𝒞.1 (by simp)) Set.Subset.rfl hD.1
  have hDfinite : (↑D : Language).Finite := D.finite_toSet
  exact hL (hDL ▸ hDfinite)

/-- Expanded-hypothesis form of the superfinite theorem. -/
theorem all_finite_and_infinite_not_semanticallyIdentifiable
    {𝒞 : Set Language}
    (hfinite : ∀ F : Finset ℕ, (↑F : Language) ∈ 𝒞)
    (hinfinite : ∃ L, L ∈ 𝒞 ∧ L.Infinite) :
    ¬ SemanticallyIdentifiable 𝒞 := by
  apply superfinite_not_semanticallyIdentifiable
  refine ⟨?_, hinfinite⟩
  intro L hL
  simpa using hfinite hL.toFinset

/-- The semantic impossibility transfers to every grammar-naming relation. -/
theorem superfinite_not_identifiableWith
    {Name : Type*} (N : Naming Name)
    {𝒞 : Set Language} (h𝒞 : IsSuperfinite 𝒞) :
    ¬ IdentifiableWith N 𝒞 := by
  intro h
  exact superfinite_not_semanticallyIdentifiable h𝒞
    (identifiableWith_implies_semanticallyIdentifiable h)

/-- Named corollary emphasizing Gold's positive-text learning model. -/
theorem superfinite_not_text_identifiable
    {Name : Type*} (N : Naming Name)
    {𝒞 : Set Language}
    (hfinite : ∀ F : Finset ℕ, (↑F : Language) ∈ 𝒞)
    (hinfinite : ∃ L, L ∈ 𝒞 ∧ L.Infinite) :
    ¬ IdentifiableWith N 𝒞 := by
  apply superfinite_not_identifiableWith N
  refine ⟨?_, hinfinite⟩
  intro L hL
  simpa using hfinite hL.toFinset

/-- **Gold's sharp arbitrary-text boundary, semantic form.**  The class of
finite languages is identifiable, while every proper superclass is not. -/
theorem finiteLanguages_maximal_semanticallyIdentifiable :
    SemanticallyIdentifiable finiteLanguages ∧
      ∀ 𝒞 : Set Language, finiteLanguages ⊂ 𝒞 →
        ¬ SemanticallyIdentifiable 𝒞 := by
  refine ⟨finiteLanguages_semanticallyIdentifiable, ?_⟩
  intro 𝒞 hproper
  obtain ⟨L, hL𝒞, hLfinite⟩ := Set.exists_of_ssubset hproper
  apply superfinite_not_semanticallyIdentifiable
  refine ⟨hproper.le, ⟨L, hL𝒞, ?_⟩⟩
  simpa using hLfinite

end Text
end Gold
end GenLimit
