import GenLimit.Paper25_PrivateGenerationAndIdentification.FiniteWordRelease
import GenLimit.Paper25_PrivateGenerationAndIdentification.EpochRelease
import GenLimit.Paper25_PrivateGenerationAndIdentification.VotingBlocks

/-! Continual generation by applying finite-family mechanisms to growing
prefixes. The families, sample lengths, and privacy budgets are public. -/
namespace GenLimit.PrivateLimit.Epoch

open Set Filter DiscreteIID PriceOfPrivacy MeasureTheory Privacy
open scoped Classical ENNReal
noncomputable section

def observations (s : ℕ → ℕ) (n : ℕ) := (List.range n).map s

theorem mem_observations {s : ℕ → ℕ} {n x : ℕ} : x ∈ observations s n ↔ ∃ i < n, s i = x := by
  simp [observations]

theorem private_prefix {n : ℕ} {ε : ℝ} (he : 0 ≤ ε) {A : List ℕ → PMF ℕ}
    (dp : PrivateAt ε 0 n A) {u v : ℕ → ℕ} (adj : Neighbors u v) (y : ℕ) :
    A (observations u n) y ≤ ENNReal.ofReal (Real.exp ε)*A (observations v n) y := by
  obtain ⟨j,h⟩ := adj
  have prob : probability (A (observations u n)) {y} ≤ Real.exp ε*probability (A (observations v n)) {y} := by
    by_cases hj : j ∈ List.range n
    · obtain ⟨pre,post,split⟩ := List.append_of_mem hj
      have nd : (pre ++ j :: post).Nodup := split ▸ List.nodup_range
      have h₁ : pre.map u = pre.map v := List.map_congr_left (fun i hi => h i
        ((List.nodup_append.mp nd).2.2 i hi j (List.mem_cons_self ..)))
      have h₂ : post.map u = post.map v := List.map_congr_left (fun i hi => h i
        (fun eq => (List.nodup_cons.mp (List.nodup_append.mp nd).2.1).1 (eq ▸ hi)))
      have len := congrArg List.length split
      simp only [List.length_range,List.length_append,List.length_cons] at len
      simpa only [observations,split,List.map_append,List.map_cons,h₁,h₂,add_zero] using
        dp (pre.map v) (u j) (v j) (post.map v) (by simp; omega) {y}
    · have eq : observations u n = observations v n := List.map_congr_left (fun i hi => h i (fun e => hj (e ▸ hi)))
      rw [eq]
      exact le_mul_of_one_le_left (probability_nonneg ..) (Real.one_le_exp_iff.mpr he)
  apply (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _))).mp
  simpa only [probability,PMF.toOuterMeasure_apply_singleton,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos ε).le] using prob

def cost (ε : ℝ) (j : ℕ) : ℝ := ε/((j+1:ℝ)*(j+2))

theorem cost_pos {ε : ℝ} (he : 0 < ε) (j : ℕ) : 0 < cost ε j := by unfold cost; positivity

theorem budget {ε : ℝ} (he : 0 < ε) (I : Finset ℕ) : ∑ j ∈ I, cost ε j ≤ ε := by
  obtain ⟨n,hn⟩ := I.exists_nat_subset_range
  apply (Finset.sum_le_sum_of_subset_of_nonneg hn (fun j _ _ => (cost_pos he j).le)).trans
  let f (j : ℕ) := ε/(j+1:ℝ)
  have diff (j : ℕ) : cost ε j = f j-f (j+1) := by
    dsimp [cost,f]; push_cast
    rw [show (j:ℝ)+1+1 = j+2 by ring]; field_simp; ring
  simp_rw [diff]; rw [Finset.sum_range_sub']
  have h : 0 ≤ f n := by dsimp [f]; positivity
  simpa [f] using (sub_le_self (f 0) h)

def horizon (finish : ℕ → ℕ) (k : ℕ) := max (k+1) (finish (k+1))

theorem before_horizon (finish : ℕ → ℕ) (t : ℕ) : t < horizon finish (latest finish t) := by
  by_contra! h
  have pair := max_le_iff.mp h
  have le : latest finish t+1 ≤ latest finish t := Nat.le_findGreatest pair.1 pair.2
  omega

structure Scheme where
  count : ℕ → ℕ
  family : (j : ℕ) → Fin (count j) → Set ℕ
  dim : ℕ → ℕ
  bound : ∀ j, SubcollectionClosureBound (range (family j)) (dim j)
  finish : ℕ → ℕ
  initial : finish 0 = 0

def sample (P : Scheme) (ε : ℝ) (s : ℕ → ℕ) (j : ℕ) :=
  FiniteCore.wordRelease (P.family j) (P.dim j) (P.finish j+1) (horizon P.finish j)
    (cost ε j) (observations s (P.finish j+1))

theorem sample_depends (P : Scheme) (ε : ℝ) (u v : ℕ → ℕ) (j : ℕ)
    (agree : ∀ i ≤ P.finish j, u i = v i) : sample P ε u j = sample P ε v j := by
  unfold sample; congr 1
  exact List.map_congr_left (fun i hi => agree i (Nat.le_of_lt_succ (List.mem_range.mp hi)))

def generator (P : Scheme) (ε : ℝ) := release P.finish P.initial _ (sample_depends P ε)

theorem generator_private (P : Scheme) {ε : ℝ} (he : 0 < ε) :
    DifferentiallyPrivate ε 0 (generator P ε).law := by
  apply release_private
  apply private_independent_releases
  intro u v adj
  refine ⟨cost ε,budget he,?_⟩
  intro j y
  exact private_prefix (cost_pos he j).le (FiniteCore.word_private _ _ _ _ (cost_pos he j)) adj y

def errorAt (P : Scheme) (ε : ℝ) (j : ℕ) :=
  5*FiniteCore.errorTerm (P.count j) (P.dim j) (P.finish j+1) (cost ε j)

def badWord (K : Set ℕ) (s : ℕ → ℕ) (n : ℕ) := {x | x ∉ K ∨ x ∈ observations s n}

def badEpoch (P : Scheme) (K : Set ℕ) (s : ℕ → ℕ) (j : ℕ) : Set (ℕ → ℕ) :=
  (Function.eval j) ⁻¹' badWord K s (horizon P.finish j)

theorem badEpoch_bound (P : Scheme) {ε : ℝ} (he : 0 < ε) (s : ℕ → ℕ) (nd : Function.Injective s)
    (j : ℕ) (z : Fin (P.count j)) (inK : range s ⊆ P.family j z) :
    (productLaw (sample P ε) s).real (badEpoch P (P.family j z) s j) ≤ errorAt P ε j := by
  let B := badWord (P.family j z) s (horizon P.finish j)
  have hm : MeasurableSet B := .of_discrete
  have h := measurePreserving_eval_infinitePi (fun i => (sample P ε s i).toMeasure) j
  change ((Measure.infinitePi (fun i => (sample P ε s i).toMeasure)) ((Function.eval j) ⁻¹' B)).toReal ≤ _
  rw [h.measure_preimage hm.nullMeasurableSet,PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm]
  have f := FiniteCore.word_failure (P.family j) (P.bound j) (cost_pos he j) z
    (observations s (P.finish j+1)) (observations s (horizon P.finish j))
    (List.nodup_range.map nd) (fun x hx => by obtain ⟨i,_,rfl⟩ := mem_observations.mp hx; exact inK (mem_range_self _))
  simpa only [observations,List.length_map,List.length_range] using f

def failsAfter (K : Set ℕ) (s : ℕ → ℕ) (t : ℕ) : Set (ℕ → ℕ) :=
  ⋃ n : ℕ, (Function.eval (t+n)) ⁻¹' badWord K s (t+n+1)

theorem measurable_failsAfter (K : Set ℕ) (s : ℕ → ℕ) (t : ℕ) : MeasurableSet (failsAfter K s t) :=
  MeasurableSet.iUnion (fun n => measurable_pi_apply (t+n) MeasurableSet.of_discrete)

theorem late_failure (P : Scheme) (K : Set ℕ) (s : ℕ → ℕ) {r t : ℕ}
    (available : max r (P.finish r) ≤ t) :
    playback P.finish ⁻¹' failsAfter K s t ⊆ ⋃ l, badEpoch P K s (r+l) := by
  intro y hy
  obtain ⟨n,hn⟩ := mem_iUnion.mp hy
  let j := latest P.finish (t+n)
  have hr : r ≤ j := Nat.le_findGreatest (by omega : r ≤ t+n) (by omega : P.finish r ≤ t+n)
  refine mem_iUnion.mpr ⟨j-r,?_⟩
  rw [Nat.add_sub_of_le hr]
  change y j ∉ K ∨ y j ∈ observations s (horizon P.finish j)
  change y j ∉ K ∨ y j ∈ observations s (t+n+1) at hn
  apply hn.imp_right
  intro hx
  obtain ⟨i,hi,eq⟩ := mem_observations.mp hx
  exact mem_observations.mpr ⟨i,lt_of_lt_of_le hi (before_horizon P.finish _),eq⟩

/-- Bound the probability of even one incorrect release at or after a public time. -/
theorem tail_bound (P : Scheme) (ε : ℝ) (K : Set ℕ) (s : ℕ → ℕ) {r t : ℕ}
    (ready : max r (P.finish r) ≤ t) (b : ℕ → ℝ) (hb : ∀ l, 0 ≤ b l) (sum : Summable b)
    (bound : ∀ l, (productLaw (sample P ε) s).real (badEpoch P K s (r+l)) ≤ b l) :
    ((generator P ε).law s).real (failsAfter K s t) ≤ ∑' l, b l := by
  let μ := productLaw (sample P ε) s
  change (((μ.map (playback P.finish)) (failsAfter K s t))).toReal ≤ _
  rw [Measure.map_apply (measurable_playback _) (measurable_failsAfter ..)]
  have h : μ (playback P.finish ⁻¹' failsAfter K s t) ≤ ENNReal.ofReal (∑' l, b l) := by
    apply (measure_mono (late_failure P K s ready)).trans
    apply (measure_iUnion_le _).trans
    rw [ENNReal.ofReal_tsum_of_nonneg hb sum]
    apply ENNReal.tsum_le_tsum
    intro l
    simpa only [Measure.real_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      (ENNReal.ofReal_le_ofReal (bound l))
  simpa only [ENNReal.toReal_ofReal (tsum_nonneg hb)] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

end
end GenLimit.PrivateLimit.Epoch
