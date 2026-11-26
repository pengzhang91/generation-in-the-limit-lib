import GenLimit.Paper28_ContrastiveGeneration.DisjointHierarchy
import GenLimit.Paper02_LearningTheory.NonuniformCharacterization

/-! # Named ambiguity regimes and the four strict inclusions in the clean hierarchy -/

namespace GenLimit.ContrastiveGeneration

/-- The three cases N1, N2 and N3 of Theorem 4.3, for distinct supports. -/
theorem noneliminability_regimes [Countable α] {h g : Set α}
    (hh : h.Nonempty) (hg : gᶜ.Nonempty) (hne : h ≠ g) :
    NotEliminableFrom g h ↔ h ⊂ g ∨
      (Incomparable h g ∧ Disjoint h g) ∨
      (Incomparable h g ∧ (h ∩ g).Nonempty ∧ h ∪ g ≠ Set.univ) := by
  classical
  obtain ⟨x, hx⟩ := hh
  haveI : Nonempty α := ⟨x⟩
  obtain ⟨e, he⟩ := exists_surjective_nat α
  rw [proposition_4_2 x hx e (fun y _ => he y), theorem_4_3]
  constructor
  · rintro ⟨had, hbc⟩
    by_cases sub : h ⊆ g
    · exact Or.inl (ssubset_of_subset_of_ne sub hne)
    have hb : (hOnly h g).Nonempty := Set.not_subset.mp sub
    obtain ⟨z, hzg, hzh⟩ := hbc hb
    have inc : Incomparable h g := ⟨sub, fun s => hzh (s hzg)⟩
    by_cases inter : (h ∩ g).Nonempty
    · obtain ⟨w, hw⟩ := had inter
      exact Or.inr (Or.inr ⟨inc, inter, fun huniv => hw (huniv ▸ Set.mem_univ w)⟩)
    · exact Or.inr (Or.inl ⟨inc, Set.disjoint_left.mpr fun _ a b => inter ⟨_, a, b⟩⟩)
  · rintro (sub | ⟨inc, dis⟩ | ⟨inc, _, ncover⟩)
    · obtain ⟨y, hy⟩ := hg
      exact ⟨fun _ => ⟨y, fun hyu => hy (hyu.elim (fun v => sub.le v) id)⟩,
        fun ⟨_, a, b⟩ => (b (sub.le a)).elim⟩
    · exact ⟨fun ⟨_, a, b⟩ => (Set.disjoint_left.mp dis a b).elim,
        fun _ => incomparable_gOnly_nonempty inc⟩
    · exact ⟨fun _ => Set.nonempty_compl.mpr ncover, fun _ => incomparable_gOnly_nonempty inc⟩

alias Results.theorem_4_3_regimes := noneliminability_regimes

/-- Countably indexed families of infinite proper supports satisfying a learning property. -/
def cleanFamilies (P : Generic.LanguageFamily ℕ → Prop) : Set (Generic.LanguageFamily ℕ) :=
  {F | (∀ i, (F i).Infinite) ∧ AllProperNontrivial F ∧ P F}

private theorem countableTextGeneration {α : Type*} [Countable α] [Nonempty α]
    (F : Generic.LanguageFamily α) (h : ∀ i, (F i).Infinite) :
    Generic.GeneratableInLimit (Set.range F) := by
  have hu : Generic.UUS (Set.range F) := by
    rintro L ⟨i, rfl⟩
    exact h i
  exact Generic.nonuniform_implies_limit hu
    (LiRamanTewari.countable_classes_are_nonuniformly_generatable hu (Set.countable_range F))

private theorem punctured_clean :
    (∀ i, (puncturedFamily i).Infinite) ∧ AllProperNontrivial puncturedFamily := by
  have spine := Set.infinite_range_of_injective puncturedCore_injective
  have inf : ∀ i, (puncturedFamily i).Infinite := by
    rintro (_ | m)
    · exact spine
    · exact spine.diff (Set.finite_singleton _)
  refine ⟨inf, fun i => ⟨(inf i).nonempty, 1, ?_⟩⟩
  have out : 1 ∉ Set.range puncturedCore := by
    rintro ⟨n, h⟩
    simp [puncturedCore] at h
  cases i with
  | zero => exact out
  | succ m => exact fun hx => out hx.1

private theorem disjoint_clean : AllProperNontrivial disjointFamily := by
  intro i
  refine ⟨(disjointFamily_infinite i).nonempty, ?_⟩
  cases i with
  | zero =>
    obtain ⟨y, hy⟩ := oddSupport_infinite.nonempty
    exact ⟨y, fun he => Set.disjoint_left.mp evenSupport_disjoint_oddSupport he hy⟩
  | succ k =>
    obtain ⟨y, hy⟩ := evenSupport_infinite.nonempty
    exact ⟨y, fun ho => Set.disjoint_left.mp evenSupport_disjoint_oddSupport hy ho⟩

-- Keep the witness names used by the statement audit.
alias Results.theorem_5_13_disjoint_witness := theorem_5_13_5_14_disjoint_witness
alias Results.theorem_5_13_punctured_witness := theorem_5_13_5_14_punctured_witness

/-- Theorem 5.13. All four proper inclusions use the same space of families. -/
theorem clean_strict_diamond :
    let CI := cleanFamilies ContrastivelyIdentifiable
    let TI := cleanFamilies TextIdentifiable
    let CG := cleanFamilies (fun F => ContrastivelyGeneratable (Set.range F))
    let TG := cleanFamilies (fun F => Generic.GeneratableInLimit (Set.range F))
    CI ⊂ CG ∧ CG ⊂ TG ∧ CI ⊂ TI ∧ TI ⊂ TG := by
  dsimp only
  obtain ⟨pc, pn, pi⟩ := theorem_5_13_5_14_punctured_witness
  obtain ⟨dt, dg, dn⟩ := theorem_5_13_5_14_disjoint_witness
  have p := punctured_clean
  have d := disjoint_clean
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro F ⟨h, hp, hi⟩
    exact ⟨h, hp, contrastiveIdentification_implies_generation F h hi⟩
  · intro back
    exact pi ((back (a := puncturedFamily) ⟨p.1, p.2, pc⟩).2.2)
  · rintro F ⟨h, hp, _⟩
    exact ⟨h, hp, countableTextGeneration F h⟩
  · intro back
    exact dn ((back (a := disjointFamily) ⟨disjointFamily_infinite, d, dg⟩).2.2)
  · rintro F ⟨h, hp, hi⟩
    exact ⟨h, hp, lemma_4_6_inclusion F hp hi⟩
  · intro back
    have hi := (back (a := disjointFamily) ⟨disjointFamily_infinite, d, dt⟩).2.2
    exact dn (contrastiveIdentification_implies_generation _ disjointFamily_infinite hi)
  · rintro F ⟨h, hp, hi⟩
    exact ⟨h, hp, textIdentification_implies_generation F h hi⟩
  · intro back
    exact pn ((back (a := puncturedFamily)
      ⟨p.1, p.2, countableTextGeneration _ p.1⟩).2.2)

/-- Theorem 5.14. Contrastive generation and text identification are incomparable
on the same families as in Theorem 5.13. -/
theorem clean_generation_text_identification_incomparable :
    let CG := cleanFamilies (fun F => ContrastivelyGeneratable (Set.range F))
    let TI := cleanFamilies TextIdentifiable
    ¬ (CG ⊆ TI) ∧ ¬ (TI ⊆ CG) := by
  constructor
  · intro inclusion
    have h := inclusion (a := puncturedFamily)
      ⟨punctured_clean.1, punctured_clean.2, punctured_contrastivelyGeneratable⟩
    exact punctured_not_textIdentifiable h.2.2
  · intro inclusion
    have h := inclusion (a := disjointFamily)
      ⟨disjointFamily_infinite, disjoint_clean, disjoint_textIdentifiable⟩
    exact disjoint_not_contrastivelyGeneratable h.2.2

end GenLimit.ContrastiveGeneration
