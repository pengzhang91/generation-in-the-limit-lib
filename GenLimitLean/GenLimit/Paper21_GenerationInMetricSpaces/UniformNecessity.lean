import GenLimit.Paper21_GenerationInMetricSpaces.UniformSufficiency
import Mathlib.Topology.MetricSpace.Basic

/-!
# Uniform generation and internal closure dimension

Necessity and the full characterization in Theorem 3.1 of
Li--Raman--Tewari, *On Generation in Metric Spaces*, arXiv:2602.07710v2.
The internal cover centers are positive for every compatible target, so they
can be appended to the sample before testing the proposed generator.
-/

namespace GenLimit.MetricSpaces

private theorem coveringNumberAtLeast_of_eq_of_le
    {ρ : Distance α} {ε : ℝ} {A : Set α}
    {k d : ℕ} (hkd : k ≤ d)
    (hEq : CoveringNumberEq ρ ε A d) :
    CoveringNumberAtLeast ρ ε A k := by
  intro centers hcover
  exact hkd.trans (hEq.1 centers hcover)

private theorem positive_coveringNumber_forces_nonempty
    {ρ : Distance α} {ε : ℝ}
    {S : Finset α} {d : ℕ}
    (hd : 0 < d)
    (hEq :
      CoveringNumberEq ρ ε (S : Set α) d) :
    S.Nonempty := by
  classical
  by_contra hS
  have hSEmpty : S = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hS
  subst S
  have hd0 : d ≤ 0 :=
    hEq.1 ∅ (by
      intro x hx
      simp at hx)
  omega

/-- A large scale-closure witness with an internal same-radius cover defeats
the proposed generator at its proposed uniform threshold.

This is the sound mathematical core of source lemma `lem:closnecc`. -/
theorem internal_scaleClosureWitness_defeats_uniform_threshold
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    {gen : GenLimit.Generic.Generator α}
    {k d : ℕ} (hkd : k < d)
    {S : Finset α}
    (hversion : (versionSpace H S).Nonempty)
    (hEq :
      CoveringNumberEq ρ ε (S : Set α) d)
    (hinternal :
      HasFiniteInternalCover ρ ε' (commonCore H S)) :
    ¬ IsUniformGeneratorAt ρ ε ε' gen H k := by
  classical
  rintro hgen
  obtain ⟨centers, hcentersCore, hcoverCore⟩ :=
    hinternal
  let history : List α := S.toList ++ centers.toList
  have hhistoryFinset :
      history.toFinset = S ∪ centers := by
    simp [history]
  let xhat : α := gen history.length history.get
  obtain ⟨L, hLVersion, hbad⟩ :
      ∃ L, L ∈ versionSpace H S ∧
        (xhat ∈ commonCore H S ∨ xhat ∉ L) := by
    by_cases hx : xhat ∈ commonCore H S
    · obtain ⟨L, hL⟩ := hversion
      exact ⟨L, hL, Or.inl hx⟩
    · change
        ¬ ∀ K, K ∈ versionSpace H S → xhat ∈ K at hx
      push_neg at hx
      obtain ⟨L, hL, hxL⟩ := hx
      exact ⟨L, hL, Or.inr hxL⟩
  have hdPositive : 0 < d :=
    lt_of_le_of_lt (Nat.zero_le k) hkd
  have hSNonempty : S.Nonempty :=
    positive_coveringNumber_forces_nonempty hdPositive hEq
  let fallback : α := Classical.choose hSNonempty
  have hfallbackS : fallback ∈ S :=
    Classical.choose_spec hSNonempty
  have hfallbackL : fallback ∈ L :=
    hLVersion.2 hfallbackS
  let stream : GenLimit.Generic.Stream α :=
    GenLimit.Generic.historyThenFallback history fallback
  have hhistoryL :
      (history.toFinset : Set α) ⊆ L := by
    rw [hhistoryFinset]
    intro x hx
    rcases Finset.mem_union.mp hx with hxS | hxCenters
    · exact hLVersion.2 hxS
    · exact
        (show x ∈ commonCore H S from
          hcentersCore hxCenters) L hLVersion
  have hstream :
      GenLimit.Generic.StreamIn stream L := by
    rintro x ⟨n, rfl⟩
    by_cases hn : n < history.length
    · apply hhistoryL
      change stream n ∈ history.toFinset
      rw [List.mem_toFinset, List.mem_iff_get]
      exact ⟨⟨n, hn⟩,
        by
          simp [stream,
            GenLimit.Generic.historyThenFallback, hn]⟩
    · simpa [stream,
        GenLimit.Generic.historyThenFallback, hn]
        using hfallbackL
  have hfirstSample :
      GenLimit.Generic.sample stream S.card = S := by
    calc
      GenLimit.Generic.sample stream S.card =
          GenLimit.Generic.sample
            (GenLimit.Generic.historyThenFallback
              S.toList fallback) S.card := by
        apply GenLimit.Generic.sample_eq_of_eq_on_prefix
        intro n hn
        have hnS : n < S.toList.length := by
          simpa using hn
        have hnHistory : n < history.length := by
          simp only [history, List.length_append,
            Finset.length_toList]
          omega
        change
          GenLimit.Generic.historyThenFallback
              history fallback n =
            GenLimit.Generic.historyThenFallback
              S.toList fallback n
        simp only [GenLimit.Generic.historyThenFallback,
          dif_pos hnHistory, dif_pos hnS, history]
        exact List.getElem_append_left hnS
      _ = GenLimit.Generic.sample
          (GenLimit.Generic.historyThenFallback
            S.toList fallback) S.toList.length := by
        rw [Finset.length_toList]
      _ = S.toList.toFinset :=
        GenLimit.Generic.sample_historyThenFallback_length
          S.toList fallback
      _ = S := Finset.toList_toFinset S
  have hfullSample :
      GenLimit.Generic.sample stream history.length =
        S ∪ centers := by
    change
      GenLimit.Generic.sample
          (GenLimit.Generic.historyThenFallback
            history fallback) history.length =
        S ∪ centers
    rw [GenLimit.Generic.sample_historyThenFallback_length,
      hhistoryFinset]
  have htrigger :
      CoveringNumberAtLeast ρ ε
        (GenLimit.Generic.sample stream S.card :
          Set α) k := by
    rw [hfirstSample]
    exact coveringNumberAtLeast_of_eq_of_le
      (Nat.le_of_lt hkd) hEq
  have htime : S.card ≤ history.length := by
    simp [history]
  have hcorrect :=
    hgen L hLVersion.1 stream hstream
      S.card htrigger history.length htime
  have houtput :
      GenLimit.Generic.output gen stream history.length =
        xhat := by
    unfold GenLimit.Generic.output
    simp only [stream, xhat]
    congr 1
    funext i
    simp [GenLimit.Generic.historyThenFallback, i.isLt]
  rcases hbad with hxCore | hxL
  · apply hcorrect.2
    rw [houtput, hfullSample]
    apply inClosedNeighborhood_mono_centers
        (show (centers : Set α) ⊆
          (S ∪ centers : Finset α) from by
            intro x hx
            exact Finset.mem_union_right S hx)
    exact hcoverCore hxCore
  · apply hxL
    simpa only [houtput] using hcorrect.1

/-- Necessity in Theorem 3.1: the v2 internal-center convention supplies
exactly the positive continuation required by the adversarial argument. -/
theorem uniform_implies_finite_scaleClosureDimension
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hUniform : UniformlyGeneratableAt ρ ε ε' H) :
    HasFiniteScaleClosureDimension ρ ε ε' H := by
  obtain ⟨gen, k, hgen⟩ := hUniform
  refine ⟨k, ?_⟩
  intro d hkd
  rintro ⟨S, hS⟩
  exact (internal_scaleClosureWitness_defeats_uniform_threshold
    (gen := gen) hkd hS.1 hS.2.1 hS.2.2) hgen

/-- Theorem 3.1: uniform generation is equivalent to finite closure dimension.
The argument uses only reflexivity and a nonnegative adversary radius; the
paper's positive scales, metric laws, and UUS hypothesis imply this setting. -/
theorem uniformlyGeneratableAt_iff_finite_scaleClosureDimension
    [Nonempty α]
    {ρ : Distance α} {ε ε' : ℝ}
    {H : GenLimit.Generic.LanguageClass α}
    (hrefl : ∀ x, ρ x x = 0) (hε : 0 ≤ ε) :
    UniformlyGeneratableAt ρ ε ε' H ↔ HasFiniteScaleClosureDimension ρ ε ε' H :=
  ⟨uniform_implies_finite_scaleClosureDimension,
    finite_scaleClosureDimension_implies_uniform hrefl hε⟩

end GenLimit.MetricSpaces
