import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace PredictionToGeneration.SparseGraph

abbrev Edge := Nat × Nat

def Valid (V : Finset Nat) (E : Finset Edge) : Prop :=
  ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V ∧ e.1 < e.2

def Independent (E : Finset Edge) (I : Finset Nat) : Prop :=
  ∀ e ∈ E, ¬ (e.1 ∈ I ∧ e.2 ∈ I)

def incident (E : Finset Edge) (v : Nat) : Finset Edge :=
  E.filter (fun e => e.1 = v ∨ e.2 = v)

@[simp] theorem mem_incident (E : Finset Edge) (v : Nat) (e : Edge) :
    e ∈ incident E v ↔ e ∈ E ∧ (e.1 = v ∨ e.2 = v) := by simp [incident]

theorem incident_unique (E : Finset Edge) (v : Nat) (hd : (incident E v).card ≤ 1)
    (e f : Edge) (he : e ∈ incident E v) (hf : f ∈ incident E v) : e = f :=
  Finset.card_le_one.mp hd e he f hf

/-- Integer sparse-graph bound, sufficient for the paired-point separation.
It is slightly weaker than Caro--Wei but avoids real-valued averaging. -/
theorem independent_bound (V : Finset Nat) (E : Finset Edge) (hv : Valid V E) :
    ∃ I : Finset Nat, I ⊆ V ∧ Independent E I ∧ 2 * V.card ≤ 3 * I.card + E.card := by
  classical
  induction V using Finset.strongInductionOn generalizing E with
  | _ V ih =>
    by_cases hhigh : ∃ v ∈ V, 2 ≤ (incident E v).card
    · obtain ⟨v,hvV,hdeg⟩ := hhigh
      let E' := E \ incident E v
      have valid' : Valid (V.erase v) E' := by
        intro e he
        obtain ⟨heE,heI⟩ := Finset.mem_sdiff.mp he
        obtain ⟨ha,hb,hab⟩ := hv e heE
        have hne : e.1 ≠ v ∧ e.2 ≠ v := by simpa [incident,heE] using heI
        exact ⟨Finset.mem_erase.mpr ⟨hne.1,ha⟩,Finset.mem_erase.mpr ⟨hne.2,hb⟩,hab⟩
      obtain ⟨I,hi,hind,hbound⟩ := ih (V.erase v) (Finset.erase_ssubset hvV) E' valid'
      refine ⟨I,fun x hx => Finset.mem_of_mem_erase (hi hx),?_,?_⟩
      · intro e he hboth
        have ha := (Finset.mem_erase.mp (hi hboth.1)).1
        have hb := (Finset.mem_erase.mp (hi hboth.2)).1
        exact hind e (Finset.mem_sdiff.mpr ⟨he,by simp [incident,ha,hb]⟩) hboth
      · have hcV := Finset.card_erase_add_one hvV
        have hcE := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun e : Edge => e.1=v ∨ e.2=v) E)
        change E'.card + (incident E v).card = E.card at hcE
        omega
    · have low : ∀ v ∈ V, (incident E v).card ≤ 1 := by
        intro v hm
        have : ¬ 2 ≤ (incident E v).card := fun hd => hhigh ⟨v,hm,hd⟩
        omega
      by_cases hV : V.Nonempty
      · obtain ⟨v,hvV⟩ := hV
        by_cases hinc : (incident E v).Nonempty
        · obtain ⟨e,heI⟩ := hinc
          obtain ⟨heE,heV⟩ := (mem_incident E v e).mp heI
          obtain ⟨ha,hb,hab⟩ := hv e heE
          let w := if e.1 = v then e.2 else e.1
          have hwV : w ∈ V := by dsimp [w]; split <;> assumption
          have hvw : v ≠ w := by
            dsimp [w]
            split <;> rcases heV with heV | heV <;> omega
          have heW : e ∈ incident E w := by
            apply (mem_incident E w e).mpr
            refine ⟨heE,?_⟩
            dsimp [w]
            split
            · exact Or.inr rfl
            · exact Or.inl rfl
          have endpoints : (e.1 = v ∧ e.2 = w) ∨ (e.1 = w ∧ e.2 = v) := by
            dsimp [w]
            split <;> rcases heV with heV | heV <;> simp_all
          let V' := (V.erase v).erase w
          let E' := E.erase e
          have valid' : Valid V' E' := by
            intro f hf
            obtain ⟨hne,hfE⟩ := Finset.mem_erase.mp hf
            obtain ⟨hf1,hf2,hfo⟩ := hv f hfE
            have avoid (a : Nat) (haV : a ∈ V) (hea : e ∈ incident E a) :
                f.1 ≠ a ∧ f.2 ≠ a := by
              constructor <;> intro heq
              · have hfa : f ∈ incident E a := (mem_incident E a f).mpr ⟨hfE,Or.inl heq⟩
                exact hne (incident_unique E a (low a haV) f e hfa hea)
              · have hfa : f ∈ incident E a := (mem_incident E a f).mpr ⟨hfE,Or.inr heq⟩
                exact hne (incident_unique E a (low a haV) f e hfa hea)
            have av := avoid v hvV heI
            have aw := avoid w hwV heW
            exact ⟨by simp [V',av.1,aw.1,hf1],by simp [V',av.2,aw.2,hf2],hfo⟩
          have hsub : V' ⊂ V :=
            (Finset.erase_subset w (V.erase v)).trans_ssubset (Finset.erase_ssubset hvV)
          obtain ⟨I,hi,hind,hbound⟩ := ih V' hsub E' valid'
          have vnot : v ∉ I := by
            intro hm
            have := hi hm
            simp [V'] at this
          have wnot : w ∉ I := by
            intro hm
            have := hi hm
            simp [V'] at this
          refine ⟨insert v I,?_,?_,?_⟩
          · intro a haI
            rcases Finset.mem_insert.mp haI with rfl | haI
            · exact hvV
            · have := hi haI
              exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase this)
          · intro f hf hboth
            by_cases hfv : f.1 = v ∨ f.2 = v
            · have hfe := incident_unique E v (low v hvV) f e
                ((mem_incident E v f).mpr ⟨hf,hfv⟩) heI
              subst f
              rcases endpoints with ⟨he1,he2⟩ | ⟨he1,he2⟩
              · have := hboth.2
                simp [he2,hvw.symm,wnot] at this
              · have := hboth.1
                simp [he1,hvw.symm,wnot] at this
            · have f1 : f.1 ∈ I := by simpa [(not_or.mp hfv).1] using hboth.1
              have f2 : f.2 ∈ I := by simpa [(not_or.mp hfv).2] using hboth.2
              have hne : f ≠ e := by
                intro heq
                apply hfv
                simpa [heq] using heV
              exact hind f (Finset.mem_erase.mpr ⟨hne,hf⟩) ⟨f1,f2⟩
          · have hcI := Finset.card_insert_of_notMem vnot
            have hcE := Finset.card_erase_add_one heE
            have hcV := Finset.card_erase_add_one hvV
            have hw : w ∈ V.erase v := Finset.mem_erase.mpr ⟨hvw.symm,hwV⟩
            have hcW := Finset.card_erase_add_one hw
            change V'.card + 1 = (V.erase v).card at hcW
            change E'.card + 1 = E.card at hcE
            omega
        · have noedge : ∀ e ∈ E, e.1 ≠ v ∧ e.2 ≠ v := by
            intro e he
            constructor <;> intro heq
            · exact hinc ⟨e,(mem_incident E v e).mpr ⟨he,Or.inl heq⟩⟩
            · exact hinc ⟨e,(mem_incident E v e).mpr ⟨he,Or.inr heq⟩⟩
          have valid' : Valid (V.erase v) E := by
            intro e he
            obtain ⟨ha,hb,hab⟩ := hv e he
            exact ⟨Finset.mem_erase.mpr ⟨(noedge e he).1,ha⟩,
              Finset.mem_erase.mpr ⟨(noedge e he).2,hb⟩,hab⟩
          obtain ⟨I,hi,hind,hbound⟩ := ih (V.erase v) (Finset.erase_ssubset hvV) E valid'
          have vnot : v ∉ I := fun hm => (Finset.mem_erase.mp (hi hm)).1 rfl
          refine ⟨insert v I,?_,?_,?_⟩
          · intro a ha
            rcases Finset.mem_insert.mp ha with rfl | ha
            · exact hvV
            · exact Finset.mem_of_mem_erase (hi ha)
          · intro e he hboth
            have hav := (noedge e he).1
            have hbv := (noedge e he).2
            exact hind e he ⟨by simpa [hav] using hboth.1,by simpa [hbv] using hboth.2⟩
          · have hcI := Finset.card_insert_of_notMem vnot
            have hcV := Finset.card_erase_add_one hvV
            omega
      · have he : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hV
        subst V
        exact ⟨∅,Finset.empty_subset _,by simp [Independent],by simp⟩

end PredictionToGeneration.SparseGraph


