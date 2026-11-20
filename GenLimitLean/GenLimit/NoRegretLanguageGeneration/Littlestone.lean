import GenLimit.NoRegretLanguageGeneration.Basic

/-!
# Sequential Sauer bound

Source: `lem:app-dynamic-sauer` in appendix_finite_ldim_upper.tex.
We bound nonempty leaves of every adaptive binary query tree. The bound is
represented by Pascal recursion; SauerBinomial proves its binomial-sum identity.
-/

namespace PredictionToGeneration

def restrict (H : HypothesisClass X) (x : X) (b : Bool) : HypothesisClass X :=
  fun h => H h ∧ h x = b

def Shatters (H : HypothesisClass X) : Nat → Prop
  | 0 => ∃ h, H h
  | n + 1 => ∃ x, Shatters (restrict H x false) n ∧ Shatters (restrict H x true) n

def LdimLE (H : HypothesisClass X) (d : Nat) : Prop := ¬ Shatters H (d + 1)

theorem shatters_mono {H K : HypothesisClass X} (hsub : ∀ h, H h → K h)
    (n : Nat) (hs : Shatters H n) : Shatters K n := by
  induction n generalizing H K with
  | zero => obtain ⟨h, hh⟩ := hs; exact ⟨h, hsub h hh⟩
  | succ n ih =>
    obtain ⟨x, h0, h1⟩ := hs
    exact ⟨x, ih (fun h hh => ⟨hsub h hh.1, hh.2⟩) h0,
      ih (fun h hh => ⟨hsub h hh.1, hh.2⟩) h1⟩

theorem ldimLE_restrict (H : HypothesisClass X) (d : Nat) (hd : LdimLE H d)
    (x : X) (b : Bool) : LdimLE (restrict H x b) d := by
  intro hs
  exact hd (shatters_mono (fun _ hh => hh.1) (d + 1) hs)

theorem dimension_drop (H : HypothesisClass X) (d : Nat) (hd : LdimLE H (d + 1))
    (x : X) : LdimLE (restrict H x false) d ∨ LdimLE (restrict H x true) d := by
  classical
  by_cases h0 : LdimLE (restrict H x false) d
  · exact Or.inl h0
  · apply Or.inr
    intro h1
    exact hd ⟨x, Classical.not_not.mp h0, h1⟩

inductive QueryTree (X : Type) : Nat → Type where
  | leaf : QueryTree X 0
  | node {n} (x : X) (left right : QueryTree X n) : QueryTree X (n + 1)

noncomputable def leafCount (H : HypothesisClass X) : {n : Nat} → QueryTree X n → Nat
  | 0, .leaf => @ite Nat (∃ h, H h) (Classical.propDecidable _) 1 0
  | _ + 1, .node x l r => leafCount (restrict H x false) l + leafCount (restrict H x true) r

def sauer : Nat → Nat → Nat
  | 0, _ => 1
  | _ + 1, 0 => 1
  | n + 1, d + 1 => sauer n (d + 1) + sauer n d

theorem leafCount_empty (H : HypothesisClass X) (he : ¬ ∃ h, H h)
    {n : Nat} (tree : QueryTree X n) : leafCount H tree = 0 := by
  induction tree generalizing H with
  | leaf => simp [leafCount, he]
  | node x l r ihl ihr =>
    have h0 : ¬ ∃ h, restrict H x false h := fun ⟨h, hh⟩ => he ⟨h, hh.1⟩
    have h1 : ¬ ∃ h, restrict H x true h := fun ⟨h, hh⟩ => he ⟨h, hh.1⟩
    simp [leafCount, ihl _ h0, ihr _ h1]

/-- The combinatorial step in the prediction-to-generation bound. -/
theorem sequential_sauer (H : HypothesisClass X) (d : Nat) (hd : LdimLE H d)
    {n : Nat} (tree : QueryTree X n) : leafCount H tree ≤ sauer n d := by
  classical
  induction tree generalizing H d with
  | leaf => simp [leafCount, sauer]; split <;> omega
  | @node n x l r ihl ihr =>
    have h0 := ldimLE_restrict H d hd x false
    have h1 := ldimLE_restrict H d hd x true
    cases d with
    | zero =>
      have b0 := ihl _ 0 h0
      have b1 := ihr _ 0 h1
      have s0 : sauer n 0 = 1 := by cases n <;> rfl
      by_cases e0 : ∃ h, restrict H x false h
      · have e1 : ¬ ∃ h, restrict H x true h := fun he => hd ⟨x, e0, he⟩
        have hz := leafCount_empty _ e1 r
        simp only [leafCount, sauer]
        omega
      · have hz := leafCount_empty _ e0 l
        simp only [leafCount, sauer]
        omega
    | succ d =>
      obtain hl | hr := dimension_drop H d hd x
      · have bl := ihl _ d hl
        have br := ihr _ (d + 1) h1
        simp only [leafCount, sauer]
        omega
      · have bl := ihl _ (d + 1) h0
        have br := ihr _ d hr
        simp only [leafCount, sauer]
        omega

end PredictionToGeneration

