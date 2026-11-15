import GenLimit.NoRegretLanguageGeneration.Rows
import GenLimit.NoRegretLanguageGeneration.Transversal

set_option maxHeartbeats 1000000

namespace PredictionToGeneration

inductive GenerationCriterion where
  | uniform | mistakeBounded | nonuniform | noRegret | limit | zeroRate
  deriving DecidableEq

def GenerationCriterion.Holds : GenerationCriterion → HypothesisClass X → Prop
  | .uniform, H => UniformGeneration H
  | .mistakeBounded, H => UniformMistakeBounded H
  | .nonuniform, H => NonuniformGeneration H
  | .noRegret, H => RealizableNoRegret H
  | .limit, H => GenerationInLimit H
  | .zeroRate, H => ZeroRateGeneration H

/-- Reflexive directed-path relation of the manuscript's implication diagram. -/
def GenerationCriterion.Reaches : GenerationCriterion → GenerationCriterion → Prop
  | .uniform, _ => True
  | .mistakeBounded, .mistakeBounded | .mistakeBounded, .noRegret |
      .mistakeBounded, .limit | .mistakeBounded, .zeroRate => True
  | .nonuniform, .nonuniform | .nonuniform, .limit | .nonuniform, .zeroRate => True
  | .noRegret, .noRegret | .noRegret, .zeroRate => True
  | .limit, .limit | .limit, .zeroRate => True
  | .zeroRate, .zeroRate => True
  | _, _ => False

theorem criterion_implication_of_path (a b : GenerationCriterion) (hr : a.Reaches b)
    (H : HypothesisClass X) : a.Holds H → b.Holds H := by
  have h1 := uniform_implies_nonuniform H
  have h2 := uniform_implies_mistake_bounded H
  have h3 := mistake_bounded_implies_no_regret H
  have h4 := mistake_bounded_implies_limit H
  have h5 := nonuniform_implies_limit H
  have h6 := no_regret_implies_zero_rate H
  have h7 := limit_implies_zero_rate H
  cases a <;> cases b <;> simp only [GenerationCriterion.Reaches, GenerationCriterion.Holds] at hr ⊢ <;> tauto

/-- Every missing directed path has a concrete nonempty UUS counterexample. -/
theorem criterion_counterexample_of_no_path (a b : GenerationCriterion) (hn : ¬ a.Reaches b) :
    ∃ X : Type, ∃ H : HypothesisClass X, UUS H ∧ (∃ h, H h) ∧ a.Holds H ∧ ¬ b.Holds H := by
  have hc := cofinite_comparison_witness
  have hcof : ∃ h, Cofinite.H h := ⟨Cofinite.hypothesis [], [], rfl⟩
  have hr := Rows.row_comparison_witness
  have hrn : ∃ h, Rows.H h := ⟨Rows.hypothesis Set.univ (fun _ => 0),
    Set.univ, ⟨0, Set.mem_univ 0⟩, (fun _ => 0), rfl⟩
  have hru : ¬ UniformGeneration Rows.H := fun hu => hr.2.1 (uniform_implies_nonuniform Rows.H hu)
  have hrz := no_regret_implies_zero_rate Rows.H hr.2.2.1
  have ht := Transversal.transversal_comparison_witness
  have htu : ¬ UniformGeneration Transversal.H := fun hu => ht.2.2
    (mistake_bounded_implies_limit Transversal.H (uniform_implies_mistake_bounded Transversal.H hu))
  have htm : ¬ UniformMistakeBounded Transversal.H := fun hm => ht.2.2
    (mistake_bounded_implies_limit Transversal.H hm)
  have htn : ¬ NonuniformGeneration Transversal.H := fun hnu => ht.2.2
    (nonuniform_implies_limit Transversal.H hnu)
  cases a <;> cases b <;> simp only [GenerationCriterion.Reaches] at hn
  all_goals first
    | solve | exact False.elim (hn trivial)
    | solve
      | refine ⟨Nat, Cofinite.H, Cofinite.uus, hcof, ?_, ?_⟩ <;>
          simp only [GenerationCriterion.Holds] <;> tauto
    | solve
      | refine ⟨Nat × Nat, Rows.H, Rows.uus, hrn, ?_, ?_⟩ <;>
          simp only [GenerationCriterion.Holds] <;> tauto
    | solve
      | refine ⟨Transversal.X, Transversal.H, Transversal.uus, Transversal.nonempty_class, ?_, ?_⟩ <;>
          simp only [GenerationCriterion.Holds] <;> tauto

/-- Completeness of the entire six-criterion implication diagram: universal
implication over nonempty UUS classes holds exactly along directed paths. -/
theorem comparison_diagram_complete (a b : GenerationCriterion) :
    (∀ (X : Type) (H : HypothesisClass X), UUS H → (∃ h, H h) → a.Holds H → b.Holds H) ↔
      a.Reaches b := by
  constructor
  · intro hi
    by_contra hn
    obtain ⟨X, H, hu, hne, ha, hb⟩ := criterion_counterexample_of_no_path a b hn
    exact hb (hi X H hu hne ha)
  · intro hr X H _ _
    exact criterion_implication_of_path a b hr H

/-- Every nontrivial directed implication is strict. -/
theorem comparison_path_strict (a b : GenerationCriterion) (hr : a.Reaches b) (hne : a ≠ b) :
    ∃ X : Type, ∃ H : HypothesisClass X, UUS H ∧ (∃ h, H h) ∧ b.Holds H ∧ ¬ a.Holds H := by
  apply criterion_counterexample_of_no_path b a
  cases a <;> cases b <;> simp_all [GenerationCriterion.Reaches]

end PredictionToGeneration
