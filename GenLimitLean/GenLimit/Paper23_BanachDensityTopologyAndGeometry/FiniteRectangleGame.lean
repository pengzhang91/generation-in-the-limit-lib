import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! A finite-board response rule for the filtered rectangular generation problem.
After the first input, the generator minimizes a weighted potential before the
next input arrives. The bound depends on the total weight of the finite tests. -/
namespace GenLimit.KleinbergWei.Banach.FiniteGame
open Finset Real
noncomputable section
variable {I V : Type*} [Fintype I] [DecidableEq V] (E : I → Finset V)

private def update (w : I → ℝ) (t : ℝ) (x : V) (i : I) :=
  if x ∈ E i then (1+t)*w i else w i

private def load (w : I → ℝ) (x : V) := ∑ i, if x ∈ E i then w i else 0

private theorem total_update (w : I → ℝ) (t : ℝ) (x : V) :
    ∑ i, update E w t x i = (∑ i, w i) + t*load E w x := by
  rw [load,Finset.mul_sum,← Finset.sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases h : x ∈ E i <;> simp [update,h]
  ring

private theorem load_le (w w' : I → ℝ) (h : ∀ i, w i ≤ w' i) (x : V) :
    load E w x ≤ load E w' x := by
  apply sum_le_sum
  intro i _
  split_ifs <;> first | apply h | rfl

/-- Weight of a test given the input and response histories (most recent first). -/
def weight (w : I → ℝ) (q : ℝ) (a g : List V) (i : I) : ℝ :=
  w i * (1+q)^(a.countP (fun x => decide (x ∈ E i))) *
    (1-q)^(g.countP (fun x => decide (x ∈ E i)))

omit [Fintype I] in
private theorem input_weight (w : I → ℝ) (q : ℝ) (a g : List V) (x : V) :
    weight E w q (x::a) g = update E (weight E w q a g) q x := by
  funext i
  by_cases h : x ∈ E i <;> simp [weight,update,h,pow_succ]
  ring

omit [Fintype I] in
private theorem reply_weight (w : I → ℝ) (q : ℝ) (a g : List V) (y : V) :
    weight E w q a (y::g) = update E (weight E w q a g) (-q) y := by
  funext i
  by_cases h : y ∈ E i <;> simp [weight,update,h,pow_succ]
  ring

/-- Choose a free word of maximum load, using only the current histories. -/
def reply (w : I → ℝ) (F : Finset V) (h : F.Nonempty) : V :=
  (F.exists_max_image (load E w) h).choose

theorem reply_mem (w : I → ℝ) (F : Finset V) (h : F.Nonempty) :
    reply E w F h ∈ F := (F.exists_max_image (load E w) h).choose_spec.1

private theorem pair_bound (w : I → ℝ) (wn : ∀ i, 0 ≤ w i) {q : ℝ} (hq : 0 ≤ q)
    (F : Finset V) (hf : F.Nonempty) {x : V} (hx : x ∈ F) :
    ∑ i, update E (update E w (-q) (reply E w F hf)) q x i ≤ ∑ i, w i := by
  let y := reply E w F hf
  have smaller (i : I) : update E w (-q) y i ≤ w i := by
    by_cases hy : y ∈ E i <;> simp [update,hy]
    nlinarith [mul_nonneg hq (wn i)]
  have maxload : load E w x ≤ load E w y :=
    (F.exists_max_image (load E w) hf).choose_spec.2 x hx
  have after := (load_le E _ _ smaller x).trans maxload
  change ∑ i, update E (update E w (-q) y) q x i ≤ _
  rw [total_update,total_update]
  linarith only [mul_le_mul_of_nonneg_left after hq]

/-- Positions immediately after an input. Each next input is free after
the actual greedy response is removed. The free board is tracked explicitly. -/
inductive AfterInput (w : I → ℝ) (q : ℝ) (board : Finset V) :
    List V → List V → Finset V → Prop
  | first (x : V) (hx : x ∈ board) : AfterInput w q board [x] [] (board.erase x)
  | next {a g F} (prior : AfterInput w q board a g F) (hf : F.Nonempty)
      (x : V) (hx : x ∈ F.erase (reply E (weight E w q a g) F hf)) :
      AfterInput w q board (x::a) ((reply E (weight E w q a g) F hf)::g)
        ((F.erase (reply E (weight E w q a g) F hf)).erase x)

omit [Fintype I] in
private theorem weights_nonneg (w : I → ℝ) (wn : ∀ i, 0 ≤ w i) {q : ℝ}
    (hq : 0 ≤ q) (h1 : q ≤ 1) (a g : List V) (i : I) : 0 ≤ weight E w q a g i := by
  unfold weight
  have hp : 0 ≤ 1+q := by linarith
  have hm : 0 ≤ 1-q := by linarith
  exact mul_nonneg (mul_nonneg (wn i) (pow_nonneg hp _)) (pow_nonneg hm _)

theorem potential {w : I → ℝ} (wn : ∀ i, 0 ≤ w i) {q : ℝ}
    (hq : 0 ≤ q) (h1 : q ≤ 1) {board : Finset V} {a g F}
    (played : AfterInput E w q board a g F) :
    ∑ i, weight E w q a g i ≤ (1+q) * ∑ i, w i := by
  induction played with
  | first x hx =>
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro i _
    by_cases hit : x ∈ E i <;> simp [weight,hit] <;> nlinarith [mul_nonneg hq (wn i)]
  | next prior hf x hx ih =>
    rw [input_weight,reply_weight]
    exact (pair_bound E _ (weights_nonneg E w wn hq h1 _ _) hq _ hf (mem_of_mem_erase hx)).trans ih

private theorem log_rates {q : ℝ} (hq : 0 < q) (h1 : q ≤ 1/2) :
    q-2*q^2 ≤ log (1+q) ∧ -q-2*q^2 ≤ log (1-q) := by
  constructor
  · apply le_trans _ (Real.one_sub_inv_le_log_of_pos (by linarith))
    rw [le_sub_iff_add_le,← le_sub_iff_add_le',inv_eq_one_div]
    apply (div_le_iff₀ (by linarith)).2
    nlinarith [sq_nonneg q,pow_nonneg hq.le 3]
  · apply le_trans _ (Real.one_sub_inv_le_log_of_pos (by linarith))
    rw [le_sub_iff_add_le,← le_sub_iff_add_le',inv_eq_one_div]
    apply (div_le_iff₀ (by linarith)).2
    nlinarith [mul_nonneg (sq_nonneg q) (show 0 ≤ 1-2*q by linarith)]

/-- At every played prefix, the excess of inputs over replies in each
test is bounded in terms of its own count and prior share of the weight.
The final reply on an even board can only reduce this excess. -/
theorem discrepancy {w : I → ℝ} (wp : ∀ i, 0 < w i) {q : ℝ}
    (hq : 0 < q) (h1 : q ≤ 1/2) {board : Finset V} {a g F}
    (played : AfterInput E w q board a g F) (i : I) :
    let A : ℝ := a.countP (fun x => decide (x ∈ E i))
    let G : ℝ := g.countP (fun x => decide (x ∈ E i))
    A-G ≤ 2*q*(A+G) + log ((1+q)*(∑ j, w j)/w i)/q := by
  dsimp only
  have wnn j := (wp j).le
  have small : q ≤ 1 := by linarith
  have hp : 0 < 1+q := by linarith
  have hm : 0 < 1-q := by linarith
  have one := (Finset.single_le_sum (fun j _ => weights_nonneg E w wnn hq.le small a g j)
    (Finset.mem_univ i)).trans (potential E wnn hq.le small played)
  let A := a.countP (fun x => decide (x ∈ E i))
  let G := g.countP (fun x => decide (x ∈ E i))
  change w i * (1+q)^A * (1-q)^G ≤ _ at one
  have factor : (1+q)^A * (1-q)^G ≤ (1+q)*(∑ j, w j)/w i := by
    apply (le_div_iff₀ (wp i)).2
    linarith only [one]
  have logs := Real.log_le_log (mul_pos (pow_pos hp _) (pow_pos hm _)) factor
  rw [Real.log_mul (pow_ne_zero _ hp.ne') (pow_ne_zero _ hm.ne'),Real.log_pow,Real.log_pow] at logs
  obtain ⟨plus,minus⟩ := log_rates hq h1
  change (A:ℝ)-G ≤ 2*q*(A+G) + _/q
  rw [add_comm (2*q*((A:ℝ)+G)) _,← sub_le_iff_le_add,le_div_iff₀ hq]
  nlinarith only [logs, mul_le_mul_of_nonneg_left plus (Nat.cast_nonneg (α := ℝ) A),
    mul_le_mul_of_nonneg_left minus (Nat.cast_nonneg (α := ℝ) G)]

/-- All rectangular tests in one board with L coordinate sites on each axis.
The loss term is uniform over the box endpoints and every adversarial play. -/
theorem cube_discrepancy {d L : ℕ} (pos : 0 < L) (origin : Fin d → ℤ)
    (board : Finset (Fin d → ℤ)) {q : ℝ} (hq : 0 < q) (h1 : q ≤ 1/2)
    {a g F} :
    let tests := fun (b : (Fin d → Fin L) × (Fin d → Fin L)) =>
      board.filter (fun v => ∀ j, origin j + b.1 j ≤ v j ∧ v j ≤ origin j + b.2 j)
    AfterInput tests (fun _ => 1) q board a g F → ∀ b,
      let A : ℝ := a.countP (fun x => decide (x ∈ tests b))
      let G : ℝ := g.countP (fun x => decide (x ∈ tests b))
      (1/2-q)*(A+G) - (log (1+q) + 2*d*log L)/(2*q) ≤ G := by
  intro tests played b
  have h := discrepancy tests (w := fun _ => 1) (fun _ => zero_lt_one) hq h1 played b
  have npos : (0:ℝ) < L := by exact_mod_cast pos
  have hp : 0 < 1+q := by linarith
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_pi,
    Fintype.card_fin,Finset.prod_const,nsmul_eq_mul,mul_one,div_one, Nat.cast_mul,
    Nat.cast_pow] at h
  rw [Real.log_mul hp.ne' (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_pow] at h
  dsimp only at h ⊢
  field_simp [hq.ne'] at h ⊢
  linarith

end
end GenLimit.KleinbergWei.Banach.FiniteGame
