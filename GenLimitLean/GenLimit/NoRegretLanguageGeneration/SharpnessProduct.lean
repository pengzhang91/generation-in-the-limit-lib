import GenLimit.NoRegretLanguageGeneration.SharpnessComponent

namespace PredictionToGeneration.SharpnessProduct
open Classical

abbrev Vector (q K : Nat) := Fin q → Fin K
abbrev Point (q K : Nat) := Sum (Fin q × Fin K) (Vector q K × Nat)

noncomputable def hypothesis {q K : Nat} (v : Vector q K) : Hypothesis (Point q K)
  | .inl (l,i) => decide (v l ≠ i)
  | .inr (w,_) => decide (v = w)

def H (q K : Nat) : HypothesisClass (Point q K) := fun h => ∃ v, h = hypothesis v

def Partial {q K : Nat} (known : Finset (Fin q)) (u : Vector q K) : HypothesisClass (Point q K) :=
  fun h => ∃ v, (∀ l ∈ known, v l = u l) ∧ h = hypothesis v

theorem shatters_pred (C : HypothesisClass X) (n : Nat) : Shatters C (n+1) → Shatters C n := by
  induction n generalizing C with
  | zero => rintro ⟨x,⟨h,hh,_⟩,_⟩; exact ⟨h,hh⟩
  | succ n ih => rintro ⟨x,h0,h1⟩; exact ⟨x,ih _ h0,ih _ h1⟩

theorem shatters_le (C : HypothesisClass X) {n k : Nat} (hkn : k ≤ n)
    (hs : Shatters C n) : Shatters C k := by
  induction n with
  | zero =>
    have hk : k=0 := by omega
    subst k
    exact hs
  | succ n ih =>
    by_cases he : k=n+1
    · subst k; exact hs
    · exact ih (by omega) (shatters_pred C n hs)

theorem partial_ldim {q K : Nat} (known : Finset (Fin q)) (u : Vector q K) (r : Nat)
    (hsize : q ≤ known.card+r) : LdimLE (Partial known u) r := by
  induction r generalizing known u with
  | zero =>
    apply fun hs => SharpnessComponent.singleton_ldim_zero (hypothesis u)
      (shatters_mono (n := 1) (hs := hs) ?_)
    rintro h ⟨v,hv,rfl⟩
    have hfull : known = Finset.univ := Finset.eq_univ_of_card known (by
      have := Finset.card_le_univ known
      simp only [Fintype.card_fin] at this ⊢
      omega)
    have he : v=u := funext (fun l => hv l (by simp [hfull]))
    rw [he]
  | succ r ih =>
    rintro ⟨x,h0,h1⟩
    cases x with
    | inl p =>
      by_cases hl : p.1 ∈ known
      · obtain ⟨h,⟨v,hv,rfl⟩,hf⟩ := shatters_le _ (Nat.zero_le _) h0
        obtain ⟨h,⟨w,hw,rfl⟩,ht⟩ := shatters_le _ (Nat.zero_le _) h1
        have hvp := hv p.1 hl
        have hwp := hw p.1 hl
        simp [hypothesis,hvp,hwp] at hf ht
        contradiction
      · let u' := Function.update u p.1 p.2
        apply ih (insert p.1 known) u' (by
          rw [Finset.card_insert_of_notMem hl]
          omega)
        apply shatters_mono (n := r+1) (hs := h0)
        rintro h ⟨⟨v,hv,rfl⟩,hf⟩
        have hvp : v p.1 = p.2 := by simpa [hypothesis] using hf
        refine ⟨v,?_,rfl⟩
        intro l hmem
        rcases Finset.mem_insert.mp hmem with rfl | hmem
        · simpa [u'] using hvp
        · have hne : l ≠ p.1 := fun he => hl (he ▸ hmem)
          simpa [u',hne] using hv l hmem
    | inr p =>
      apply SharpnessComponent.singleton_ldim_zero (hypothesis p.1)
      apply shatters_le _ (show 1≤r+1 by omega)
      apply shatters_mono (n := r+1) (hs := h1)
      rintro h ⟨⟨v,_,rfl⟩,hp⟩
      have hv : v=p.1 := by simpa [hypothesis] using hp
      rw [hv]

theorem partial_shatters {q K : Nat} (hK : 2 ≤ K) (n : Nat)
    (known : Finset (Fin q)) (u : Vector q K) (hsize : n+known.card≤q) :
    Shatters (Partial known u) n := by
  induction n generalizing known u with
  | zero => exact ⟨hypothesis u,u,by simp,rfl⟩
  | succ n ih =>
    have hnot : ∃ l : Fin q, l ∉ known := by
      by_contra hn
      have hfull : known=Finset.univ := by ext l; simp_all
      simp [hfull] at hsize
    obtain ⟨l,hl⟩ := hnot
    let a : Fin K := ⟨0,by omega⟩
    let b : Fin K := ⟨1,by omega⟩
    have hab : b ≠ a := by simp [a,b,Fin.ext_iff]
    have hrec (i : Fin K) := ih (insert l known) (Function.update u l i)
      (by rw [Finset.card_insert_of_notMem hl]; omega)
    have hsub (i : Fin K) (h : Hypothesis (Point q K))
        (hh : Partial (insert l known) (Function.update u l i) h) :
        Partial known u h ∧ h (.inl (l,a)) = decide (i≠a) := by
      obtain ⟨v,hv,rfl⟩ := hh
      have hvl : v l = i := by simpa using hv l (Finset.mem_insert_self _ _)
      refine ⟨⟨v,?_,rfl⟩,by simp [hypothesis,hvl]⟩
      intro k hk
      have hne : k≠l := fun he => hl (he ▸ hk)
      simpa [hne] using hv k (Finset.mem_insert_of_mem hk)
    refine ⟨.inl (l,a),?_,?_⟩
    · apply shatters_mono (n := n) (hs := hrec a)
      intro h hh
      simpa [restrict] using hsub a h hh
    · apply shatters_mono (n := n) (hs := hrec b)
      intro h hh
      simpa [restrict,hab] using hsub b h hh

theorem exact_dimension (q K : Nat) (hK : 2 ≤ K) : LdimLE (H q K) q ∧ Shatters (H q K) q := by
  let u : Vector q K := fun _ => ⟨0,by omega⟩
  have he : Partial ∅ u = H q K := by
    funext h
    simp [Partial,H]
  rw [← he]
  exact ⟨partial_ldim ∅ u q (by simp),partial_shatters hK q ∅ u (by simp)⟩

theorem uus (q K : Nat) : UUS (H q K) := by
  intro h hh seen
  obtain ⟨v,hv⟩ := hh
  subst h
  let ns := seen.filterMap (fun x => match x with | .inl _ => none | .inr (_,n) => some n)
  let n := ns.sum+1
  refine ⟨.inr (v,n),?_,by simp [hypothesis]⟩
  intro hm
  have hn : n∈ns := List.mem_filterMap.mpr ⟨.inr (v,n),hm,rfl⟩
  have hh := List.single_le_sum (fun a _ => Nat.zero_le a) n hn
  dsimp [n] at hh
  omega

theorem finite_class (q K : Nat) : Finite {h // H q K h} := by
  have hs : Function.Surjective (fun v : Vector q K => (⟨hypothesis v,⟨v,rfl⟩⟩ : {h // H q K h})) := by
    rintro ⟨h,v,rfl⟩
    exact ⟨v,rfl⟩
  exact Finite.of_surjective _ hs

end PredictionToGeneration.SharpnessProduct

