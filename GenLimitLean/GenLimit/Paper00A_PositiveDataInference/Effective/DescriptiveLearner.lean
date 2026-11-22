import GenLimit.Paper00A_PositiveDataInference.Effective.InferenceMachine
import GenLimit.Support.Stabilization
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite

/-!
# Angluin's descriptive-index learner (Theorem 5)

Condition 5 is a partial recursive choice of a minimal compatible language
whenever such a language exists for a nonempty sample. Finite thickness gives
existence on every nonempty prefix of a valid text. The learner keeps its old
index whenever the new datum still agrees with it.
-/

namespace GenLimit.Angluin

/-- A descriptive index denotes an inclusion-minimal compatible language. -/
def Descriptive (F : EffectiveIndexedFamily) (S : Finset ℕ) (j : ℕ) : Prop :=
  IsTellTale F.language j S

/-- Condition 5. The partial function takes a finite set; computability is
tested on lists representing that set, independently of order and repetition. -/
def ConditionFive (F : EffectiveIndexedFamily) : Prop :=
  ∃ select : Finset ℕ →. ℕ, Partrec (fun h : List ℕ => select h.toFinset) ∧
    ∀ S, S.Nonempty → (∃ j, Descriptive F S j) → ∃ j ∈ select S, Descriptive F S j

namespace DescriptiveLearner

open Filter

variable {F : EffectiveIndexedFamily} {select : Finset ℕ →. ℕ}

private theorem exists_descriptive (h3 : ConditionThree F.language) {S : Finset ℕ}
    (hne : S.Nonempty) {i : ℕ} (hsub : (S : Set ℕ) ⊆ F.language i) :
    ∃ j, Descriptive F S j := by
  obtain ⟨L, ⟨⟨j, rfl⟩, hj⟩, hmin⟩ := (h3 S hne).exists_minimal ⟨_, ⟨i, rfl⟩, hsub⟩
  exact ⟨j, hj, fun k hk hkj => hmin ⟨⟨k, rfl⟩, hk⟩ hkj⟩

private def keep (F : EffectiveIndexedFamily) (old : Option ℕ) (x fresh : ℕ) : ℕ :=
  bif old.isSome && F.membership (old.getD 0) x then old.getD 0 else fresh

private def track (F : EffectiveIndexedFamily) (select : Finset ℕ →. ℕ) (s : ℕ → ℕ) :
    ℕ → Part (Option ℕ)
  | 0 => Part.some none
  | n + 1 => (track F select s n).bind fun old =>
      (select (textPrefix s (n + 1)).toFinset).map fun fresh => some (keep F old (s n) fresh)

private def readWord (h : List ℕ) (n : ℕ) := (h[n]?).getD 0

private def run (F : EffectiveIndexedFamily) (select : Finset ℕ →. ℕ) (h : List ℕ) :=
  track F select (readWord h) h.length

private theorem track_congr {s t : ℕ → ℕ} {n} (h : ∀ k < n, s k = t k) :
    track F select s n = track F select t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : textPrefix s (n + 1) = textPrefix t (n + 1) :=
      List.map_congr_left (fun k hk => h k (List.mem_range.mp hk))
    simp only [track, hp, h n (by omega), ih (fun k hk => h k (by omega))]

private theorem run_prefix (s : ℕ → ℕ) (n : ℕ) :
    run F select (textPrefix s n) = track F select s n := by
  unfold run
  rw [textPrefix_length]
  apply track_congr
  intro k hk
  simp [readWord, textPrefix, hk]

private theorem run_append_dom {h : List ℕ} {x : ℕ} (hd : (run F select (h++[x])).Dom) :
    (run F select h).Dom := by
  have heq : run F select h = track F select (readWord (h++[x])) h.length := by
    apply track_congr
    intro k hk
    simp [readWord, List.getElem?_append_left hk]
  rw [heq]
  obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp hd
  unfold run at ha
  rw [List.length_append] at ha
  change a ∈ (track F select (readWord (h ++ [x])) h.length).bind _ at ha
  obtain ⟨old, ho, _⟩ := Part.mem_bind_iff.mp ha
  exact ho.1

private theorem run_partrec (F : EffectiveIndexedFamily)
    (hsel : Partrec (fun h : List ℕ => select h.toFinset)) : Partrec (run F select) := by
  have hread : Computable₂ readWord :=
    (Computable.option_getD Computable.list_getElem? (Computable.const 0)).to₂
  let Pos := List ℕ × (ℕ × Option ℕ)
  have hh : Computable (fun p : Pos => p.1) := Computable.fst
  have hn : Computable (fun p : Pos => p.2.1) := Computable.fst.comp Computable.snd
  have ho : Computable (fun p : Pos => p.2.2) := Computable.snd.comp Computable.snd
  have hx := hread.comp hh hn
  have hprefix : Computable (fun p : Pos => textPrefix (readWord p.1) (p.2.1 + 1)) :=
    Primrec.list_map ((Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.to₂ (Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.fst)
        Primrec.snd) (Primrec.const 0))) |>.to_comp
  have hold := Computable.option_getD ho (Computable.const 0)
  have htest := Primrec.and.to_comp.comp (Primrec.option_isSome.to_comp.comp ho)
    (F.membership_computable.comp hold hx)
  have hnext : Partrec (fun p : Pos =>
      (select (textPrefix (readWord p.1) (p.2.1 + 1)).toFinset).map
        fun fresh => some (keep F p.2.2 (readWord p.1 p.2.1) fresh)) :=
    (hsel.comp hprefix).map ((Computable.option_some.comp
      ((htest.comp Computable.fst).cond (hold.comp Computable.fst) Computable.snd)).to₂)
  apply (Partrec.nat_rec Primrec.list_length.to_comp (Computable.const (none : Option ℕ)).partrec hnext.to₂).of_eq
  intro h
  unfold run
  induction h.length with
  | zero => rfl
  | succ n ih => simp only [track, ih]

/-- In each block, issue the computed guess (if any), then request one more
datum. Further positions in that same block are unreachable. -/
private def block (old : Option ℕ) (k : ℕ) : Option (Option ℕ) :=
  bif k == 0 then some old else bif k == 1 && old.isSome then some none else none

private theorem block_comp : Computable₂ block :=
  ((Primrec.beq.to_comp.comp Computable.snd (Computable.const 0)).cond
    (Computable.option_some.comp Computable.fst)
    ((Primrec.and.to_comp.comp (Primrec.beq.to_comp.comp Computable.snd (Computable.const 1))
      (Primrec.option_isSome.to_comp.comp Computable.fst)).cond
      (Computable.const (some none)) (Computable.const none))).to₂

private def machine (F : EffectiveIndexedFamily)
    (hsel : Partrec (fun h : List ℕ => select h.toFinset)) : InferenceMachine where
  event h k := (run F select h).bind fun old => Part.ofOption (block old k)
  effective := ((run_partrec F hsel).comp Computable.fst).bind
    ((block_comp.comp Computable.snd (Computable.snd.comp Computable.fst)).ofOption).to₂
  previous_guess := by
    intro h k a ha
    obtain ⟨old, ho, he⟩ := Part.mem_bind_iff.mp ha
    cases old with
    | none => simp [block] at he
    | some j =>
      cases k with
      | zero => exact ⟨j, Part.mem_bind_iff.mpr ⟨_, ho, by simp [block]⟩⟩
      | succ k => simp [block] at he
  previous_request := by
    intro h x k a ha
    obtain ⟨_, ho, _⟩ := Part.mem_bind_iff.mp ha
    obtain ⟨old, hp⟩ := Part.dom_iff_mem.mp (run_append_dom ho.1)
    cases old with
    | none => exact ⟨0, Part.mem_bind_iff.mpr ⟨_, hp, by simp [block]⟩⟩
    | some j => exact ⟨1, Part.mem_bind_iff.mpr ⟨_, hp, by simp [block]⟩⟩

private theorem guess_iff {hsel : Partrec (fun h : List ℕ => select h.toFinset)}
    {s n k j} : (machine F hsel).Guesses s n k j ↔ k = 0 ∧ some j ∈ track F select s n := by
  change some j ∈ (run F select _).bind _ ↔ _
  rw [run_prefix, Part.mem_bind_iff]
  constructor
  · rintro ⟨old, ho, he⟩
    by_cases hk : k = 0
    · subst k
      have hj : some j = old := by simpa [block] using he
      exact ⟨rfl, hj ▸ ho⟩
    · cases k with
      | zero => contradiction
      | succ k => cases k <;> cases old <;> simp [block] at he
  · rintro ⟨rfl, ho⟩
    exact ⟨_, ho, by simp [block]⟩

private abbrev DescriptiveOutputs (F : EffectiveIndexedFamily) (select : Finset ℕ →. ℕ)
    (s : ℕ → ℕ) := ∀ n, ∃ j ∈ select (textPrefix s (n + 1)).toFinset,
      Descriptive F (textPrefix s (n + 1)).toFinset j

private theorem valid_outputs (h3 : ConditionThree F.language)
    (hs : ∀ S, S.Nonempty → (∃ j, Descriptive F S j) → ∃ j ∈ select S, Descriptive F S j)
    {s i} (hp : Generic.Presents s (F.language i)) : DescriptiveOutputs F select s := by
  intro n
  have hne : (textPrefix s (n + 1)).toFinset.Nonempty :=
    ⟨s n, List.mem_toFinset.mpr (mem_textPrefix_iff.mpr ⟨n, by omega, rfl⟩)⟩
  apply hs _ hne (exists_descriptive h3 hne (i := i) ?_)
  intro x hx
  obtain ⟨k, _, rfl⟩ := mem_textPrefix_iff.mp (List.mem_toFinset.mp hx)
  exact hp ▸ Set.mem_range_self k

private theorem next_guess {s n old fresh}
    (ho : old ∈ track F select s n) (hf : fresh ∈ select (textPrefix s (n + 1)).toFinset) :
    some (keep F old (s n) fresh) ∈ track F select s (n + 1) :=
  Part.mem_bind_iff.mpr ⟨_, ho, Part.mem_map _ hf⟩

/-- A retained index remains minimal when the compatible sample grows. -/
private theorem tracks_descriptive {s}
    (hv : DescriptiveOutputs F select s) (n : ℕ) :
    ∃ j, some j ∈ track F select s (n + 1) ∧ Descriptive F (textPrefix s (n + 1)).toFinset j := by
  induction n with
  | zero =>
    obtain ⟨j, hj, hd⟩ := hv 0
    exact ⟨j, next_guess (old := none) (Part.mem_some _) hj, hd⟩
  | succ n ih =>
    obtain ⟨j, hj, hd⟩ := ih
    obtain ⟨fresh, hf, hdesc⟩ := hv (n + 1)
    have hnext := next_guess hj hf
    by_cases hx : s (n + 1) ∈ F.language j
    · refine ⟨j, by simpa [keep, (F.membership_spec _ _).2 hx] using hnext, ?_⟩
      constructor
      · intro y hy
        rw [Finset.mem_coe, List.mem_toFinset, textPrefix_succ, List.mem_append] at hy
        rcases hy with hy | hy
        · exact hd.1 (List.mem_toFinset.mpr hy)
        · simpa [List.mem_singleton.mp hy] using hx
      · intro k hk hkj
        apply hd.2 k _ hkj
        intro y hy
        apply hk
        rw [Finset.mem_coe, List.mem_toFinset, textPrefix_succ, List.mem_append]
        exact Or.inl (List.mem_toFinset.mp hy)
    · have hfalse : F.membership j (s (n + 1)) = false := by
        simpa [Bool.eq_false_iff, F.membership_spec] using hx
      exact ⟨fresh, by simpa [keep, hfalse] using hnext, hdesc⟩

private theorem persists {s} (hv : DescriptiveOutputs F select s) {n m j}
    (ho : some j ∈ track F select s n) (hnm : n ≤ m)
    (hkeep : ∀ t, n ≤ t → t < m → s t ∈ F.language j) :
    some j ∈ track F select s m := by
  induction m, hnm using Nat.le_induction with
  | base => exact ho
  | succ m hnm ih =>
    obtain ⟨fresh, hf, _⟩ := hv m
    have hprev := ih (fun t ht h => hkeep t ht (by omega))
    have hx := (F.membership_spec _ _).2 (hkeep m hnm (by omega))
    simpa [keep, hx] using next_guess hprev hf

private theorem machine_consistent {hsel : Partrec (fun h : List ℕ => select h.toFinset)}
    (hvalid : ∀ i s, Generic.Presents s (F.language i) → DescriptiveOutputs F select s) :
    (machine F hsel).Consistent F := by
  intro i s hp n k j hg t ht
  obtain ⟨_, h⟩ := guess_iff.mp hg
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨j', hj', hd⟩ := tracks_descriptive (hvalid i s hp) n
    obtain rfl := Option.some.inj (Part.mem_unique h hj')
    exact hd.1 (List.mem_toFinset.mpr (mem_textPrefix_iff.mpr ⟨t, ht, rfl⟩))

private theorem machine_responsive {hsel : Partrec (fun h : List ℕ => select h.toFinset)}
    (hvalid : ∀ i s, Generic.Presents s (F.language i) → DescriptiveOutputs F select s) :
    (machine F hsel).Responsive F := by
  intro i s hp n k hreq
  by_contra! hk
  obtain rfl : k = 0 := by omega
  obtain ⟨j, hj, _⟩ := tracks_descriptive (hvalid i s hp) n
  have hg := (guess_iff (hsel := hsel)).2 ⟨rfl, hj⟩
  exact Option.noConfusion (Part.mem_unique hreq hg)

private theorem machine_conservative {hsel : Partrec (fun h : List ℕ => select h.toFinset)}
    (hvalid : ∀ i s, Generic.Presents s (F.language i) → DescriptiveOutputs F select s) :
    (machine F hsel).Conservative F := by
  intro i s hp n k j m l g he hj hg hne
  by_contra! hall
  obtain ⟨hk, hjtrack⟩ := guess_iff.mp hj
  obtain ⟨hl, hgtrack⟩ := guess_iff.mp hg
  subst k; subst l
  have hle : n ≤ m := by rcases he with h | h <;> omega
  exact hne (Option.some.inj (Part.mem_unique hgtrack
    (persists (hvalid i s hp) hjtrack hle (fun t _ ht => hall t ht))))

/-- A single prefix eliminates all compatible candidates which omit any
target word. Finite thickness is needed only for the languages containing
the first datum. -/
private theorem separating_prefix (h3 : ConditionThree F.language) {s i}
    (hp : Generic.Presents s (F.language i)) :
    ∃ n, ∀ j, (↑(textPrefix s (n + 1)).toFinset : Set ℕ) ⊆ F.language j →
      F.language i ⊆ F.language j := by
  classical
  let A := {L : Set ℕ | L ∈ Set.range F.language ∧ s 0 ∈ L}
  have hfin : A.Finite := by simpa [A] using h3 {s 0} (Finset.singleton_nonempty _)
  have he : ∀ᶠ t in Filter.atTop, ∀ L ∈ A,
      (↑(Generic.sample s t) : Set ℕ) ⊆ L ↔ F.language i ⊆ L := by
    apply hfin.eventually_all.mpr
    intro L _
    exact Filter.eventually_atTop.mpr (Support.eventually_sample_subset_iff_presented_subset hp)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp he
  refine ⟨n, fun j hj => (hn (n + 1) (by omega) (F.language j) ⟨⟨j, rfl⟩, ?_⟩).1 ?_⟩
  · exact hj (List.mem_toFinset.mpr (mem_textPrefix_iff.mpr ⟨0, by omega, rfl⟩))
  · intro x hx
    exact hj (List.mem_toFinset.mpr (mem_textPrefix_iff.mpr (Generic.mem_sample_iff.mp hx)))

private theorem machine_identifies {hsel : Partrec (fun h : List ℕ => select h.toFinset)}
    (h3 : ConditionThree F.language)
    (hvalid : ∀ i s, Generic.Presents s (F.language i) → DescriptiveOutputs F select s) :
    (machine F hsel).Identifies F := by
  intro i s hp
  have hv := hvalid i s hp
  obtain ⟨n, hn⟩ := separating_prefix h3 hp
  obtain ⟨j, hj, hd⟩ := tracks_descriptive hv n
  have ht (k) : s k ∈ F.language i := hp ▸ Set.mem_range_self k
  have hsub := hn j hd.1
  have hcorrect : F.language j = F.language i := by
    apply Set.Subset.antisymm _ hsub
    apply hd.2 i _ hsub
    intro x hx
    obtain ⟨k, _, rfl⟩ := mem_textPrefix_iff.mp (List.mem_toFinset.mp hx)
    exact ht k
  refine ⟨n + 1, 0, j, guess_iff.mpr ⟨rfl, hj⟩, hcorrect, ?_⟩
  intro m l g he hg
  have hle : n + 1 ≤ m := by rcases he with h | h <;> omega
  exact Option.some.inj (Part.mem_unique (guess_iff.mp hg).2
    (persists hv hj hle (fun t _ _ => hsub (ht t))))

end DescriptiveLearner

/-- Angluin (1980), Theorem 5. The same effective machine has all four
operational properties. -/
theorem theoremFive (F : EffectiveIndexedFamily)
    (h3 : ConditionThree F.language) (h5 : ConditionFive F) :
    ∃ M : InferenceMachine, M.Identifies F ∧ M.Consistent F ∧ M.Responsive F ∧
      M.Conservative F := by
  obtain ⟨select, hsel, hs⟩ := h5
  have hv (i s) (hp : Generic.Presents s (F.language i)) :=
    DescriptiveLearner.valid_outputs h3 hs hp
  exact ⟨_, DescriptiveLearner.machine_identifies (hsel := hsel) h3 hv,
    DescriptiveLearner.machine_consistent hv, DescriptiveLearner.machine_responsive hv,
    DescriptiveLearner.machine_conservative hv⟩

end GenLimit.Angluin
