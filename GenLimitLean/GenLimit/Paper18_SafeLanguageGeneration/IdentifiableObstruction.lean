import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.Interval.Finset.Nat
import GenLimit.Paper18_SafeLanguageGeneration.MachineEncoding
import GenLimit.Paper18_SafeLanguageGeneration.IdentificationReduction

/-! # Effective obstruction for identifiable families (Corollary 6.1)

An accepting computation has a unique first fuel bound. Make one safe word
for each input at which a machine returns zero. A disjoint column names its
harmful language. On a computable presentation a putative safe generator
would eventually distinguish finitely many such inputs from infinitely many.
Kleene's recursion theorem gives a machine returning zero exactly on rounds
where that generator abstains. Both possible sizes lead to a contradiction.
-/

namespace GenLimit.SafeGeneration.IdentifiableObstruction

open Nat.Partrec Encodable Denumerable
abbrev Point := Bool × (ℕ × ℕ)

/-- The second coordinate stores the predecessor of the first successful fuel. -/
def Certificate (c : Code) (p : ℕ × ℕ) : Prop :=
  Code.evaln (p.2+1) c p.1 = some 0 ∧ Code.evaln p.2 c p.1 ≠ some 0

instance (c : Code) (p : ℕ × ℕ) : Decidable (Certificate c p) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem certificate_primrec : PrimrecPred (fun z : Code × (ℕ × ℕ) ↦ Certificate z.1 z.2) := by
  have step : Primrec (fun z : Code × (ℕ × ℕ) ↦ Code.evaln z.2.2 z.1 z.2.1) :=
    Code.primrec_evaln.comp (((Primrec.snd.comp Primrec.snd).pair Primrec.fst).pair
      (Primrec.fst.comp Primrec.snd))
  have next : Primrec (fun z : Code × (ℕ × ℕ) ↦ Code.evaln (z.2.2+1) z.1 z.2.1) :=
    Code.primrec_evaln.comp (((Primrec.succ.comp (Primrec.snd.comp Primrec.snd)).pair
      Primrec.fst).pair (Primrec.fst.comp Primrec.snd))
  exact (Primrec.eq.comp next (.const _)).and (Primrec.eq.comp step (.const _)).not

private theorem exists_certificate (c : Code) (x : ℕ) :
    (∃ n, Certificate c (x,n)) ↔ 0 ∈ c.eval x := by
  classical
  constructor
  · rintro ⟨n, h, _⟩
    exact Code.evaln_sound h
  · intro h
    have h' := Code.evaln_complete.mp h
    have hfound := Nat.find_spec h'
    generalize he : Nat.find h' = k at hfound
    cases k with
    | zero => simp [Code.evaln] at hfound
    | succ k =>
      refine ⟨k, hfound, fun hk ↦ ?_⟩
      have := Nat.find_min' h' (show 0 ∈ Code.evaln k c x from hk)
      omega

private theorem certificate_unique {c : Code} {x m n : ℕ}
    (hm : Certificate c (x,m)) (hn : Certificate c (x,n)) : m = n := by
  rcases lt_trichotomy m n with h | he | h
  · exact (hn.2 (Code.evaln_mono h hm.1)).elim
  · exact he
  · exact (hm.2 (Code.evaln_mono h hn.1)).elim

def target : Set Point := {x | x.1 = true}

/-- Marker words carry the index; all remaining harmful words exclude
exactly the first successful computations. -/
def harmful (j : ℕ) : Set Point := {x | if x.1 then
  ¬ Certificate (ofNat Code j) x.2 else x.2.1 = j}

theorem harmful_primrec : PrimrecPred (fun z : ℕ × Point ↦ z.2 ∈ harmful z.1) := by
  have htest : PrimrecPred (fun z : ℕ × Point ↦ z.2.1 = true) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (.const _)
  have hc := certificate_primrec.comp (((Primrec.ofNat Code).comp (Primrec.fst (α := ℕ) (β := Point))).pair
    (Primrec.snd.comp Primrec.snd))
  have hm : PrimrecPred (fun z : ℕ × Point ↦ z.2.2.1 = z.1) :=
    Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst
  exact ((htest.and hc.not).or (htest.not.and hm)).of_eq (fun z ↦ by
    rcases z with ⟨j,b,p⟩; cases b <;> simp [harmful])

private theorem finite_difference_iff (c : Code) :
    (target \ harmful (encode c)).Finite ↔ {x : ℕ | 0 ∈ c.eval x}.Finite := by
  let D := target \ harmful (encode c)
  let f := fun x : Point ↦ x.2.1
  have hmem (x : Point) : x ∈ D ↔ x.1 = true ∧ Certificate c x.2 := by
    rcases x with ⟨b,p⟩; cases b <;> simp [D, target, harmful]
  have himg : f '' D = {x : ℕ | 0 ∈ c.eval x} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (exists_certificate c _).mp ⟨_, (hmem y).mp hy |>.2⟩
    · intro hx
      obtain ⟨n, hn⟩ := (exists_certificate c x).mpr hx
      exact ⟨(true,x,n), (hmem _).mpr ⟨rfl,hn⟩, rfl⟩
  have hinj : Set.InjOn f D := by
    rintro ⟨b,x,m⟩ hb ⟨b',x',n⟩ hb' h
    obtain ⟨rfl,hm⟩ := (hmem _).mp hb
    obtain ⟨rfl,hn⟩ := (hmem _).mp hb'
    change x = x' at h
    subst x'
    rw [certificate_unique hm hn]
  exact (Set.finite_image_iff hinj).symm.trans (congrArg Set.Finite himg).to_iff


private def allowed (j : ℕ) (w : Tagged Point) : Prop :=
  if w.2 then w.1 ∈ target else w.1 ∈ harmful j

private instance (j : ℕ) (w : Tagged Point) : Decidable (allowed j w) := by
  unfold allowed target harmful
  split <;> dsimp <;> infer_instance

private def fallback : Tagged Point := ((true,0,0), true)

private def filterWord (j : ℕ) (w : Tagged Point) : Tagged Point :=
  if allowed j w then w else fallback

private def presentation (c : Code) (n : ℕ) :=
  filterWord (encode c) ((decode (α := Tagged Point) n).getD fallback)

private theorem presentation_correct (c : Code) :
    LabeledPresents (presentation c) target (harmful (encode c)) := by
  have hmem (n : ℕ) : allowed (encode c) (presentation c n) := by
    unfold presentation filterWord
    split <;> simp_all [allowed, fallback, target]
  have hsurj (w : Tagged Point) (h : allowed (encode c) w) :
      presentation c (encode w) = w := by simp [presentation, filterWord, h]
  constructor <;> ext x <;> constructor
  · rintro ⟨n,hn⟩
    have h := hmem n
    simpa [hn, allowed] using h
  · intro h
    exact ⟨_, hsurj (x,true) h⟩
  · rintro ⟨n,hn⟩
    have h := hmem n
    simpa [hn, allowed] using h
  · intro h
    exact ⟨_, hsurj (x,false) h⟩

private theorem presentation_primrec : Primrec₂ presentation := by
  have ht : PrimrecPred (fun p : ℕ × Tagged Point ↦ p.2.1.1 = true) :=
    Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) (.const _)
  have hb : PrimrecPred (fun p : ℕ × Tagged Point ↦ p.2.2 = true) :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (.const _)
  have hh := harmful_primrec.comp (Primrec.fst.pair (Primrec.fst.comp
    (Primrec.snd (α := ℕ) (β := Tagged Point))))
  have ha : PrimrecPred (fun z : ℕ × Tagged Point ↦ allowed z.1 z.2) :=
    ((hb.and ht).or (hb.not.and hh)).of_eq fun ⟨j,x,b⟩ ↦ by cases b <;> simp [allowed,target]
  have hf : Primrec₂ filterWord := Primrec.ite ha Primrec.snd (.const _)
  exact hf.comp (Primrec.encode.comp Primrec.fst)
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd) (.const _))

private theorem prefix_primrec : Primrec (fun p : Code × ℕ ↦ textPrefix (presentation p.1) p.2) :=
  Primrec.list_map (Primrec.list_range.comp Primrec.snd)
    (presentation_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

private theorem diagonal_failure (A : List (Tagged Point) → Option Point) (hA : Computable A) :
    ¬ SafelyGeneratesFamilies (fun _ xs ↦ A (List.ofFn xs)) (fun _ ↦ target) harmful := by
  intro hsafe
  let bit := fun (c : Code) (n : ℕ) ↦ bif (A (textPrefix (presentation c) n)).isSome then 1 else 0
  have hbit : Computable₂ bit :=
    Computable.cond (Primrec.option_isSome.to_comp.comp (hA.comp prefix_primrec.to_comp))
      (.const _) (.const _)
  obtain ⟨c, hc⟩ := Code.fixed_point₂ (f := fun c n ↦ Part.some (bit c n)) hbit.partrec₂
  let s := presentation c
  have hzero (n : ℕ) : 0 ∈ c.eval n ↔ A (textPrefix s n) = Option.none := by
    rw [hc]
    cases h : A (textPrefix s n) <;> simp [bit, ← show s = presentation c from rfl, h]
  specialize hsafe 0 (encode c) s (presentation_correct c)
  have hout (n : ℕ) :
      safeOutput (fun _ xs ↦ A (List.ofFn xs)) s n = A (textPrefix s n) := by
    rw [textPrefix_eq_ofFn]; rfl
  by_cases hf : (target \ harmful (encode c)).Finite
  · obtain ⟨T,hT⟩ := hsafe.2 hf
    have he : Set.Ici T ⊆ {x : ℕ | 0 ∈ c.eval x} :=
      fun n hn ↦ (hzero n).2 ((hout n).symm.trans (hT n hn).2)
    exact (Set.Ici_infinite T) (((finite_difference_iff c).mp hf).subset he)
  · obtain ⟨T,hT⟩ := hsafe.1 hf
    apply hf
    apply (finite_difference_iff c).mpr
    apply (Set.finite_Iio T).subset
    intro n hn
    by_contra! hlate
    obtain ⟨x,hx,_⟩ := hT n (Nat.le_of_not_gt hlate)
    have he := ((hout n).symm.trans hx)
    rw [(hzero n).mp hn] at he
    contradiction


/-- Read the first marker in a finite positive history. -/
private def markerLearner (xs : List Point) : ℕ :=
  xs.foldr (fun p rest ↦ bif p.1 then rest else p.2.1) 0

private theorem markerLearner_primrec : Primrec markerLearner :=
  Primrec.list_foldr (h := fun (_ : List Point) (p : Point × ℕ) ↦ bif p.1.1 then p.2 else p.1.2.1) Primrec.id (.const _) (Primrec.cond
    (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))

private theorem markerLearner_correct (j : ℕ) (xs : List Point)
    (valid : ∀ x ∈ xs, x ∈ harmful j)
    (seen : (false,j,0) ∈ xs) : markerLearner xs = j := by
  induction xs with
  | nil => simp at seen
  | cons x xs ih =>
    obtain ⟨b,n,k⟩ := x
    have hh := valid (b,n,k) (by simp)
    cases b with
    | false => simpa [markerLearner, harmful] using hh
    | true =>
      apply ih (fun x hx ↦ valid x (List.mem_cons_of_mem _ hx))
      simpa using seen

private theorem harmful_identified : Angluin.SemanticallyIdentifies markerLearner harmful := by
  intro j s hs
  have hmark : (false,j,0) ∈ harmful j := by simp [harmful]
  obtain ⟨k,hk⟩ := (show (false,j,0) ∈ Set.range s from hs.symm ▸ hmark)
  refine ⟨j,rfl,k+1, fun t ht ↦ markerLearner_correct j _ ?_ ?_⟩
  · intro x hx
    obtain ⟨i,_,hi⟩ := mem_textPrefix_iff.mp hx
    exact hs ▸ ⟨i,hi⟩
  · exact mem_textPrefix_iff.mpr ⟨k,by omega,hk⟩

/-- Corollary 6.1, effective version. Both families have uniform recursive
membership and computable positive-data identifiers. Every total computable
safe generator fails on a labeled presentation of a pair from these families. -/
theorem identifiable_families_no_computable_safe_generator :
    ∃ targets harmfuls : Generic.LanguageFamily Point,
      (∀ i, (targets i).Infinite ∧ (harmfuls i).Infinite) ∧
      ComputablePred (fun p : ℕ × Point ↦ p.2 ∈ targets p.1) ∧
      ComputablePred (fun p : ℕ × Point ↦ p.2 ∈ harmfuls p.1) ∧
      (∃ I, Computable I ∧ Angluin.SemanticallyIdentifies I targets) ∧
      (∃ I, Computable I ∧ Angluin.SemanticallyIdentifies I harmfuls) ∧
      ∀ A : List (Tagged Point) → Option Point, Computable A →
        ¬ SafelyGeneratesFamilies (fun _ xs ↦ A (List.ofFn xs)) targets harmfuls := by
  refine ⟨fun _ ↦ target, harmful, ?_, ?_, harmful_primrec.computablePred, ?_,
    ⟨markerLearner, markerLearner_primrec.to_comp, harmful_identified⟩, diagonal_failure⟩
  · intro i
    constructor
    · apply (Set.infinite_range_of_injective (f := fun n : ℕ ↦ (true,0,n)) (by
        intro x y h; simpa using h)).mono
      rintro _ ⟨n,rfl⟩
      rfl
    · apply (Set.infinite_range_of_injective (f := fun n : ℕ ↦ (false,i,n)) (by
        intro x y h; simpa using h)).mono
      rintro _ ⟨n,rfl⟩
      simp [harmful]
  · exact (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd (α := ℕ) (β := Point)))
      (.const true)).computablePred
  · exact ⟨fun _ ↦ 0, Computable.const 0, fun _ _ _ ↦ ⟨0,rfl,0,fun _ _ ↦ rfl⟩⟩

end GenLimit.SafeGeneration.IdentifiableObstruction
