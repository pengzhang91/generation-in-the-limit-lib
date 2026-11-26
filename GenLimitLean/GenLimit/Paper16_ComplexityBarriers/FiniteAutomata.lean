import GenLimit.Paper16_ComplexityBarriers.Threshold
import Mathlib.Computability.NFA
import Mathlib.Data.Fintype.BigOperators

/-! # The sharp finite-language length bound for an NFA

Pump a repeated state on a single accepting path. This keeps the bound
linear in the state count before the family product is taken. -/
namespace GenLimit.ComplexityBarriers.Automata
open Generic Support List
open scoped Classical
noncomputable section

private def states {M : NFA α σ} {s t w} : M.Path s t w → List σ
  | .nil u => [u]
  | .cons _ u _ _ _ _ p => u :: states p

private theorem states_length {M : NFA α σ} {s t w} (p : M.Path s t w) : (states p).length = w.length + 1 := by
  induction p <;> simp [states, *]

private def pathAppend {M : NFA α σ} {s t v x y} (p : M.Path s t x) (q : M.Path t v y) : M.Path s v (x++y) :=
  match p with
  | .nil _ => q
  | .cons a b _ c d h r => .cons a b v c (d++y) h (pathAppend r q)

private theorem visit {M : NFA α σ} {s t w} (p : M.Path s t w) {v} (hv : v ∈ states p) :
    ∃ a b, w = a++b ∧ Nonempty (M.Path s v a) ∧ Nonempty (M.Path v t b) := by
  induction p with
  | nil u =>
    obtain rfl : v = u := by simpa [states] using hv
    exact ⟨[],[],rfl,⟨.nil _⟩,⟨.nil _⟩⟩
  | cons u s t c w h p ih =>
    rcases List.mem_cons.mp hv with rfl | hh
    · exact ⟨[],c::w,rfl,⟨.nil _⟩,⟨.cons _ _ _ _ _ h p⟩⟩
    · obtain ⟨a,b,rfl,⟨hp⟩,hq⟩ := ih hh
      exact ⟨c::a,b,rfl,⟨.cons _ _ _ _ _ h hp⟩,hq⟩

private theorem repeat_loop {M : NFA α σ} {s w} (p : M.Path s s w) (hw : w ≠ []) (n : ℕ) :
    ∃ z : List α, n ≤ z.length ∧ Nonempty (M.Path s s z) := by
  induction n with
  | zero => exact ⟨[],le_rfl,⟨.nil _⟩⟩
  | succ n ih =>
    obtain ⟨z,hz,⟨pp⟩⟩ := ih
    refine ⟨w++z,?_,⟨pathAppend p pp⟩⟩
    rw [length_append]; have := length_pos_iff.mpr hw; omega

private theorem pump_path {M : NFA α σ} {s t w} (p : M.Path s t w) (hrep : ¬ (states p).Nodup) (n : ℕ) :
    ∃ z : List α, n ≤ z.length ∧ Nonempty (M.Path s t z) := by
  induction p with
  | nil u => simp [states] at hrep
  | cons u s t c w h p ih =>
    by_cases hh : s ∈ states p
    · obtain ⟨a,b,rfl,⟨p₁⟩,⟨p₂⟩⟩ := visit p hh
      obtain ⟨z,hz,⟨pz⟩⟩ := repeat_loop (.cons _ _ _ c a h p₁) (by simp) n
      exact ⟨z++b,by simp; omega,⟨pathAppend pz p₂⟩⟩
    · have hn : ¬(states p).Nodup := fun hn ↦ hrep (nodup_cons.mpr ⟨hh,hn⟩)
      obtain ⟨z,hz,⟨pz⟩⟩ := ih hn
      exact ⟨c::z,by simp; omega,⟨.cons _ _ _ _ _ h pz⟩⟩

theorem short_of_finite [Fintype σ] (M : NFA α σ) (hf : M.accepts.Finite) (w) (hw : w ∈ M.accepts) :
    w.length < Fintype.card σ := by
  obtain ⟨s,hs,t,ht,⟨p⟩⟩ := NFA.accepts_iff_exists_path.mp hw
  by_contra! hlong
  have hrep : ¬ (states p).Nodup := by
    intro h
    have hh := (Finset.card_le_univ (states p).toFinset)
    rw [List.toFinset_card_of_nodup h,states_length] at hh
    omega
  let B := hf.toFinset.sup List.length
  obtain ⟨z,hz,hp⟩ := pump_path p hrep (B+1)
  have hmem := NFA.accepts_iff_exists_path.mpr ⟨s,hs,t,ht,hp⟩
  have hle : z.length ≤ B := Finset.le_sup (f := List.length) (hf.mem_toFinset.mpr hmem)
  omega

def product {ι : Type*} {Q : ι → Type*} (M : ∀ i, NFA α (Q i)) : NFA α (∀ i, Q i) where
  step q a := {r | ∀ i, r i ∈ (M i).step (q i) a}
  start := {q | ∀ i, q i ∈ (M i).start}
  accept := {q | ∀ i, q i ∈ (M i).accept}

private theorem product_eval {ι : Type*} {Q : ι → Type*} (M : ∀ i, NFA α (Q i))
    (w : List α) (S : ∀ i, Set (Q i)) :
    (product M).evalFrom {q | ∀ i, q i ∈ S i} w = {q | ∀ i, q i ∈ (M i).evalFrom (S i) w} := by
  induction w generalizing S with
  | nil => rfl
  | cons a w ih =>
    have hstep : (product M).stepSet {q | ∀ i, q i ∈ S i} a = {q | ∀ i, q i ∈ (M i).stepSet (S i) a} := by
      ext q
      rw [NFA.mem_stepSet]
      constructor
      · rintro ⟨v,hv,hr⟩ i; exact NFA.mem_stepSet.mpr ⟨v i,hv i,hr i⟩
      · intro h
        choose v hv hr using fun i ↦ NFA.mem_stepSet.mp (h i)
        exact ⟨v,hv,hr⟩
    rw [NFA.evalFrom_cons,hstep,ih]; rfl

theorem product_accepts {ι : Type*} {Q : ι → Type*} (M : ∀ i, NFA α (Q i)) (w : List α) :
    w ∈ (product M).accepts ↔ ∀ i, w ∈ (M i).accepts := by
  rw [NFA.mem_accepts]
  change (∃ q, (∀ i, q i ∈ (M i).accept) ∧ q ∈ (product M).evalFrom {q | ∀ i, q i ∈ (M i).start} w) ↔ _
  rw [product_eval]
  constructor
  · rintro ⟨q,ha,hr⟩ i; exact NFA.mem_accepts.mpr ⟨q i,ha i,hr i⟩
  · intro h
    choose q ha hr using fun i ↦ NFA.mem_accepts.mp (h i)
    exact ⟨q,ha,hr⟩

/-- A finite presentation of a language by an NFA of bounded size.
Unused states may be included. -/
def NFAAtMost (s : ℕ) (L : Set (List α)) :=
  ∃ q ≤ s, ∃ M : NFA α (Fin q), M.accepts = L

theorem regular_upper [Fintype α] (ha : 2 ≤ Fintype.card α) (F : Finset (Set (List α)))
    (s : ℕ) (hF : ∀ L ∈ F, NFAAtMost s L) :
    MGeneratable (F : Set (Set (List α))) ((Fintype.card α)^(s^F.card)) := by
  apply mGeneratable_of_small_intersections
  intro S hS hne hf
  let T := (F.finite_toSet.subset hS).toFinset
  have he : (T : Set (Set (List α))) = S := Set.Finite.coe_toFinset _
  choose q hq M hM using fun i : ↥T ↦ hF i (hS (he ▸ i.property))
  let A := product M
  have hA : A.accepts = classIntersection S := by
    ext w; rw [product_accepts]; simp_rw [hM]
    exact ⟨fun h L hL ↦ h ⟨L,(F.finite_toSet.subset hS).mem_toFinset.mpr hL⟩, fun h i ↦ h _ (he ▸ i.property)⟩
  apply ncard_lt_of_length_lt ha
  intro w hw
  have hlen := short_of_finite A (hA ▸ hf) w (hA ▸ hw)
  apply hlen.trans_le
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∏ _i : ↥T, s := Finset.prod_le_prod' (fun i _ ↦ hq i)
    _ = s ^ T.card := by simp
    _ ≤ s ^ F.card := by
      by_cases hs : s = 0
      · obtain ⟨L,hL⟩ := hne
        have ht : T.Nonempty := ⟨L,(F.finite_toSet.subset hS).mem_toFinset.mpr hL⟩
        have hFne : F.Nonempty := ⟨L,hS hL⟩
        simp [hs,zero_pow (Finset.card_ne_zero.mpr ht),zero_pow (Finset.card_ne_zero.mpr hFne)]
      · exact Nat.pow_le_pow_right (by omega) (Finset.card_le_card (fun L hL ↦ hS (he ▸ hL)))

end
end GenLimit.ComplexityBarriers.Automata
