import GenLimit.NoRegretLanguageGeneration.FiniteMinimax
import GenLimit.NoRegretLanguageGeneration.Littlestone
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace PredictionToGeneration.SharpnessComponent
open Classical
open scoped BigOperators

abbrev Point (K : Nat) := Sum (Fin K) (Fin K × Nat)

def hypothesis {K : Nat} (i : Fin K) : Hypothesis (Point K)
  | .inl j => decide (i ≠ j)
  | .inr (j,_) => decide (i = j)

def H (K : Nat) : HypothesisClass (Point K) := fun h => ∃ i, h = hypothesis i

theorem singleton_ldim_zero (h : Hypothesis X) : LdimLE (fun g => g = h) 0 := by
  rintro ⟨x,⟨g,hg,h0⟩,⟨k,hk,h1⟩⟩
  subst g
  subst k
  simp_all

theorem ldim_one_upper (K : Nat) : LdimLE (H K) 1 := by
  rintro ⟨x,h0,h1⟩
  cases x with
  | inl i =>
    apply singleton_ldim_zero (hypothesis i)
    apply shatters_mono (n := 1) (hs := h0)
    rintro h ⟨⟨j,rfl⟩,he⟩
    have hj : j = i := by simpa [hypothesis] using he
    subst j
    rfl
  | inr p =>
    apply singleton_ldim_zero (hypothesis p.1)
    apply shatters_mono (n := 1) (hs := h1)
    rintro h ⟨⟨j,rfl⟩,he⟩
    have hj : j = p.1 := by simpa [hypothesis] using he
    subst j
    rfl

theorem ldim_one_lower (K : Nat) (hK : 2 ≤ K) : Shatters (H K) 1 := by
  let i : Fin K := ⟨0,by omega⟩
  let j : Fin K := ⟨1,by omega⟩
  refine ⟨.inl i,⟨hypothesis i,⟨i,rfl⟩,?_⟩,⟨hypothesis j,⟨j,rfl⟩,?_⟩⟩
  · simp [hypothesis]
  · simp [hypothesis,i,j,Fin.ext_iff]

theorem uus (K : Nat) : UUS (H K) := by
  intro h hh seen
  obtain ⟨i,hi⟩ := hh
  subst h
  let ns := seen.filterMap (fun x => match x with | .inl _ => none | .inr (_,n) => some n)
  let n := ns.sum + 1
  refine ⟨.inr (i,n),?_,by simp [hypothesis]⟩
  intro hm
  have hn : n ∈ ns := List.mem_filterMap.mpr ⟨.inr (i,n),hm,rfl⟩
  have hle := List.single_le_sum (fun a _ => Nat.zero_le a) n hn
  dsimp [n] at hle
  omega

theorem finite_class (K : Nat) : Finite {h // H K h} := by
  have hs : Function.Surjective (fun i : Fin K => (⟨hypothesis i,⟨i,rfl⟩⟩ : {h // H K h})) := by
    rintro ⟨h,i,rfl⟩
    exact ⟨i,rfl⟩
  exact Finite.of_surjective _ hs

def total {K : Nat} (S : Finset (Fin K)) (c : Fin K → Nat) : Nat := ∑ i ∈ S, 2 ^ c i

def updated {K : Nat} (c : Fin K → Nat) (z : Point K) (i : Fin K) : Nat :=
  c i + loss (hypothesis i) z

theorem power_doubling_bound (m c : Nat) (hc : c < m) : 2 * 2^c ≤ 2^m := by
  have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show c+1≤m by omega)
  simpa [Nat.pow_succ,Nat.mul_comm] using hh

theorem at_least_two {K : Nat} (m : Nat) (S : Finset (Fin K)) (c : Fin K → Nat)
    (hsmall : ∀ i ∈ S, c i < m) (hweight : 2^m ≤ total S c) : 2 ≤ S.card := by
  by_contra hc
  have hcard : S.card ≤ 1 := by omega
  rcases Finset.card_le_one.mp hcard with hh
  by_cases he : S.Nonempty
  · obtain ⟨i,hi⟩ := he
    have hS : S = {i} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hi,fun j hj => hh j hj i hi⟩
    have hs := hsmall i hi
    have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) hs
    have hb : 2^m ≤ 2^c i := by simpa [hS,total] using hweight
    omega
  · have hS := Finset.not_nonempty_iff_eq_empty.mp he
    have hp : 0 < 2^m := by positivity
    simp [hS,total] at hweight

/-- The binary divisibility argument for a unique smallest candidate. -/
theorem remove_unique_min {K : Nat} (m : Nat) (S : Finset (Fin K)) (c : Fin K → Nat)
    (i : Fin K) (hi : i ∈ S) (hci : c i < m)
    (hmin : ∀ j ∈ S.erase i, c i < c j) (hweight : 2^m ≤ total S c) :
    2^m ≤ total (S.erase i) c := by
  have hsum : total (S.erase i) c + 2^c i = total S c := by
    exact Finset.sum_erase_add _ _ hi
  have hpow : 2^(c i+1) ∣ 2^m := pow_dvd_pow 2 (by omega)
  have hrest : 2^(c i+1) ∣ total (S.erase i) c := by
    apply Finset.dvd_sum
    intro j hj
    exact pow_dvd_pow 2 (by have := hmin j hj; omega)
  have hp : 2^c i < 2^(c i+1) := Nat.pow_lt_pow_right (by decide) (by omega)
  apply Nat.le_of_lt_add_of_dvd (n := 2^(c i+1)) (by omega) hpow hrest




theorem core_weight {K : Nat} (c : Fin K → Nat) (i j : Fin K) :
    2 ^ updated c (.inl i) j = 2^c j + if j=i then 2^c j else 0 := by
  by_cases he : j=i <;> simp [updated,loss,hypothesis,he,Nat.pow_succ] <;> omega

theorem core_total {K : Nat} (S : Finset (Fin K)) (c : Fin K → Nat) (i : Fin K) :
    total S (updated c (.inl i)) = total S c + if i∈S then 2^c i else 0 := by
  simp only [total,core_weight,Finset.sum_add_distrib]
  simp

theorem tail_total {K : Nat} (S : Finset (Fin K)) (c : Fin K → Nat) (i : Fin K) (n : Nat)
    (hi : i ∉ S) : total S (updated c (.inr (i,n))) = 2*total S c := by
  unfold total
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := fun he => hi (he ▸ hj)
  simp [updated,loss,hypothesis,hji,Nat.pow_succ,Nat.mul_comm]

theorem response_preserves {K : Nat} (m : Nat) (S : Finset (Fin K)) (c : Fin K → Nat)
    (hsmall : ∀ i ∈ S, c i < m) (hweight : 2^m ≤ total S c) (z : Point K)
    (hcore : ∀ i, z = .inl i → i ∈ S) :
    ∃ j ∈ S, 2^m ≤ total (S.erase j) (updated c z) := by
  have htwo := at_least_two m S c hsmall hweight
  cases z with
  | inl i =>
    have hi := hcore i rfl
    by_cases hex : ∃ j ∈ S.erase i, c j ≤ c i
    · obtain ⟨j,hj,hcji⟩ := hex
      have hjS := Finset.mem_of_mem_erase hj
      have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
      have hiS : i ∈ S.erase j := Finset.mem_erase.mpr ⟨hij,hi⟩
      have hsum : total (S.erase j) c + 2^c j = total S c := Finset.sum_erase_add _ _ hjS
      have hp := Nat.pow_le_pow_right (by decide : 1≤2) hcji
      refine ⟨j,hjS,?_⟩
      rw [core_total,if_pos hiS]
      omega
    · have hmin : ∀ j ∈ S.erase i, c i < c j := by
        intro j hj
        have hh : ¬ c j ≤ c i := fun hh => hex ⟨j,hj,hh⟩
        omega
      refine ⟨i,hi,?_⟩
      rw [core_total,if_neg (Finset.notMem_erase i S),Nat.add_zero]
      exact remove_unique_min m S c i hi (hsmall i hi) hmin hweight
  | inr p =>
    by_cases hi : p.1 ∈ S
    · refine ⟨p.1,hi,?_⟩
      rw [tail_total _ _ _ _ (Finset.notMem_erase _ _)]
      have hsum : total (S.erase p.1) c + 2^c p.1 = total S c := Finset.sum_erase_add _ _ hi
      have hp := power_doubling_bound m (c p.1) (hsmall p.1 hi)
      omega
    · have hnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image S c hnonempty
      have hrest : (S.erase j).Nonempty := Finset.card_pos.mp (by
        have := Finset.card_erase_add_one hj
        omega)
      obtain ⟨k,hk⟩ := hrest
      have hc := hmin k (Finset.mem_of_mem_erase hk)
      have hp := Nat.pow_le_pow_right (by decide : 1≤2) hc
      have hle : 2^c k ≤ total (S.erase j) c := Finset.single_le_sum (f := fun i => 2^c i) (fun _ _ => Nat.zero_le _) hk
      have hsum : total (S.erase j) c + 2^c j = total S c := Finset.sum_erase_add _ _ hj
      refine ⟨j,hj,?_⟩
      rw [tail_total _ _ _ _ (fun h => hi (Finset.mem_of_mem_erase h))]
      omega




/-- Pad an already-realizable mistake witness to any longer horizon. -/
theorem pad_witness {X : Type} (C : HypothesisClass X) (hu : UUS C)
    (m n : Nat) (τ : Trajectory X) (h : Hypothesis X) (hh : C h)
    (hr : Realizes h τ) (hm : m ≤ mistakes h τ) : Forces (RealizableBad C m) n τ := by
  induction n generalizing τ with
  | zero => exact ⟨h,hh,hr,hm⟩
  | succ n ih =>
    intro z hz
    obtain ⟨x,hx,hpos⟩ := hu h hh (demonstrations τ)
    exact ⟨x,hx,ih ((z,x)::τ) ⟨hpos,hr⟩ (by simp only [mistakes]; omega)⟩

def CandidateInvariant {K : Nat} (S : Finset (Fin K)) (τ : Trajectory (Point K)) : Prop :=
  (∀ i, Sum.inl i ∈ demonstrations τ ↔ i ∉ S) ∧
  (∀ i ∈ S, Realizes (hypothesis i) τ)

theorem candidate_step {K : Nat} (S : Finset (Fin K)) (τ : Trajectory (Point K))
    (ha : CandidateInvariant S τ) (z : Point K) (j : Fin K) (hj : j ∈ S) :
    CandidateInvariant (S.erase j) ((z,.inl j)::τ) := by
  constructor
  · intro i
    simp only [demonstrations,List.map_cons,List.mem_cons,Sum.inl.injEq]
    change (i=j ∨ Sum.inl i ∈ demonstrations τ) ↔ i ∉ S.erase j
    rw [ha.1 i]
    simp only [Finset.mem_erase,not_and]
    tauto
  · intro i hi
    obtain ⟨hij,hiS⟩ := Finset.mem_erase.mp hi
    exact ⟨by simp [hypothesis,hij],ha.2 i hiS⟩

theorem component_forces_aux {K : Nat} (m n : Nat) (S : Finset (Fin K))
    (τ : Trajectory (Point K)) (ha : CandidateInvariant S τ)
    (hweight : 2^m ≤ total S (fun i => mistakes (hypothesis i) τ))
    (hcard : S.card ≤ n+1) : Forces (RealizableBad (H K) m) n τ := by
  by_cases hstop : ∃ i ∈ S, m ≤ mistakes (hypothesis i) τ
  · obtain ⟨i,hi,hm⟩ := hstop
    exact pad_witness (H K) (uus K) m n τ (hypothesis i) ⟨i,rfl⟩ (ha.2 i hi) hm
  · have hsmall : ∀ i ∈ S, mistakes (hypothesis i) τ < m := by
      intro i hi
      have hh : ¬ m ≤ mistakes (hypothesis i) τ := fun hm => hstop ⟨i,hi,hm⟩
      omega
    have htwo := at_least_two m S (fun i => mistakes (hypothesis i) τ) hsmall hweight
    cases n with
    | zero => omega
    | succ n =>
      intro z hz
      have hcore : ∀ i, z = .inl i → i ∈ S := by
        intro i he
        by_contra hi
        exact hz (he ▸ (ha.1 i).mpr hi)
      obtain ⟨j,hj,hw⟩ := response_preserves m S (fun i => mistakes (hypothesis i) τ) hsmall hweight z hcore
      have hjf : Fresh τ (.inl j) := fun hm => (ha.1 j).mp hm hj
      refine ⟨.inl j,hjf,?_⟩
      have hc := Finset.card_erase_add_one hj
      apply component_forces_aux m n (S.erase j) ((z,.inl j)::τ) (candidate_step S τ ha z j hj)
      · change 2^m ≤ total (S.erase j) (fun i => updated (fun i => mistakes (hypothesis i) τ) z i) at hw
        simpa [updated,mistakes,Nat.add_comm] using hw
      · omega
termination_by n

/-- Single-component forcing lemma, with its exact manuscript horizon. -/
theorem component_forces (m : Nat) : MFForces (H (2^m)) (2^m-1) m := by
  have ha : CandidateInvariant (Finset.univ : Finset (Fin (2^m))) [] := by
    simp [CandidateInvariant,demonstrations,Realizes]
  apply component_forces_aux m (2^m-1) Finset.univ [] ha
  · simp [total,mistakes]
  · simp only [Finset.card_univ,Fintype.card_fin]
    have hp : 0 < 2^m := by positivity
    omega

theorem component_lower (m : Nat) : m ≤ MF (H (2^m)) (2^m-1) := by
  have hne : ∃ h, H (2^m) h :=
    ⟨hypothesis (⟨0,by positivity⟩ : Fin (2^m)),⟨0,by positivity⟩,rfl⟩
  exact (mf_spec (H (2^m)) (uus _) hne _).2 m (component_forces m)

/-- Complete first sharpness lemma: finite UUS class of exact dimension one. -/
theorem single_component (m : Nat) (hm : 1 ≤ m) :
    Finite {h // H (2^m) h} ∧ UUS (H (2^m)) ∧
      LdimLE (H (2^m)) 1 ∧ Shatters (H (2^m)) 1 ∧ m ≤ MF (H (2^m)) (2^m-1) := by
  have hK : 2 ≤ 2^m := by simpa using Nat.pow_le_pow_right (by decide : 1≤2) hm
  exact ⟨finite_class _,uus _,ldim_one_upper _,ldim_one_lower _ hK,component_lower m⟩

end PredictionToGeneration.SharpnessComponent

