import GenLimit.Paper25_PrivateGenerationAndIdentification.VotingBlocks
import GenLimit.Paper25_PrivateGenerationAndIdentification.EpochRelease
import GenLimit.Paper24_PriceOfPrivacy.ExponentialSelection

/-! An alternative construction for the existential identification theorem.
Each voter learns on its own IID block. A single exponential-mechanism
release aggregates their votes. Each input position serves at most one
voter in one epoch, so parallel composition applies to the full transcript. -/
namespace GenLimit.PrivateLimit.Voting

open MeasureTheory DiscreteIID Privacy Filter Set PriceOfPrivacy
open scoped ENNReal Classical Topology
noncomputable section

def score (C : LanguageFamily) (s : ℕ → ℕ) (k : ℕ) (j : Fin (k+1)) : ℝ :=
  ∑ i ∈ Finset.range (k+1), if vote C (ballot s k i) = j.val then 1 else 0

def poll (C : LanguageFamily) (ε : ℝ) (s : ℕ → ℕ) (k : ℕ) :=
  (Exponential.law (score C s k) (ε/2)).map Fin.val

private theorem ballot_eq {s t : ℕ → ℕ} {k i : ℕ}
    (h : ∀ j ≤ k, s (slot k i j) = t (slot k i j)) : ballot s k i = ballot t k i := by
  apply List.map_congr_left
  intro j hj
  exact h j (Nat.le_of_lt_succ (List.mem_range.mp hj))

private theorem same_poll (C : LanguageFamily) (ε : ℝ) {s t : ℕ → ℕ} {k : ℕ}
    (h : ∀ i ≤ k, ballot s k i = ballot t k i) : poll C ε s k = poll C ε t k := by
  have eq : score C s k = score C t k := by
    funext j
    apply Finset.sum_congr rfl
    intro i hi
    rw [h i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  rw [poll,poll,eq]

private theorem shift (C : LanguageFamily) {s t : ℕ → ℕ} {k i₀ : ℕ}
    (agree : ∀ i ≠ i₀, ballot s k i = ballot t k i) (j : Fin (k+1)) :
    score C s k j ≤ score C t k j+1 := by
  let f (s : ℕ → ℕ) (i : ℕ) : ℝ := if vote C (ballot s k i) = j.val then 1 else 0
  let I := Finset.range (k+1)
  change ∑ i ∈ I, f s i ≤ (∑ i ∈ I, f t i)+1
  have h (i : ℕ) : f s i ≤ f t i+(if i=i₀ then 1 else 0) := by
    by_cases hi : i = i₀
    · simp only [hi,if_true,f]; split <;> split <;> norm_num
    · simp [f,hi,agree i hi]
  calc
    _ ≤ ∑ i ∈ I, (f t i+(if i=i₀ then 1 else 0)) := Finset.sum_le_sum (fun i _ => h i)
    _ ≤ _ := by rw [Finset.sum_add_distrib]; by_cases hm : i₀ ∈ I <;> simp [hm]

private theorem poll_private (C : LanguageFamily) {ε : ℝ} (he : 0 < ε) :
    DifferentiallyPrivate ε 0 (Epoch.productLaw (poll C ε)) := by
  apply private_parallel_releases _ he.le
  rintro s t ⟨a,h⟩
  let k := a.unpair.1
  let i₀ := a.unpair.2.unpair.1
  have coords : slot k i₀ a.unpair.2.unpair.2 = a := by simp [slot,k,i₀]
  refine ⟨k,?_,?_⟩
  · intro l hl
    apply same_poll
    intro i _; apply ballot_eq; intro j _
    apply h
    intro eq
    exact hl (Nat.pair_eq_pair.mp (eq.trans coords.symm)).1
  · intro y
    have same (i) (hi : i ≠ i₀) : ballot s k i = ballot t k i := by
      apply ballot_eq; intro j _; apply h; intro eq
      exact hi (Nat.pair_eq_pair.mp (Nat.pair_eq_pair.mp (eq.trans coords.symm)).2).1
    have dh (j : Fin (k+1)) : |score C s k j-score C t k j| ≤ 1 :=
      abs_le.mpr ⟨by linarith [shift C (fun i hi => (same i hi).symm) j],by linarith [shift C same j]⟩
    let F : Set ℕ := {y}
    have pr := Exponential.event_private _ _ (ε/2) 1 (by positivity) dh (Fin.val ⁻¹' F)
    rw [show 2*(ε/2)*1 = ε by ring] at pr
    have atom (u : ℕ → ℕ) : ((poll C ε u k) y).toReal =
        probability (Exponential.law (score C u k) (ε/2)) (Fin.val ⁻¹' F) := by
      rw [← PMF.toOuterMeasure_apply_singleton (poll C ε u k) y,poll,PMF.toOuterMeasure_map_apply]
      rfl
    apply (ENNReal.toReal_le_toReal ((poll C ε s k).apply_ne_top _) (ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top ((poll C ε t k).apply_ne_top _))).mp
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos ε).le,atom,atom]; exact pr

def finish (k : ℕ) := slot k k k

private theorem depends (C : LanguageFamily) (ε : ℝ) (s t : ℕ → ℕ) (k : ℕ)
    (agree : ∀ j ≤ finish k, s j = t j) : poll C ε s k = poll C ε t k := by
  apply same_poll
  intro i hi; apply ballot_eq; intro j hj; apply agree
  have right (a : ℕ) : Monotone (Nat.pair a) := (show StrictMono (Nat.pair a) from fun _ _ h => Nat.pair_lt_pair_right a h).monotone
  have left (a : ℕ) : Monotone (fun b => Nat.pair b a) := (show StrictMono (fun b => Nat.pair b a) from fun _ _ h => Nat.pair_lt_pair_left a h).monotone
  exact right k (((left j) hi).trans (right k hj))

def identifier (C : LanguageFamily) (ε : ℝ) :=
  Epoch.release finish (by decide) (poll C ε) (depends C ε)

theorem identifier_private (C : LanguageFamily) {ε : ℝ} (he : 0 < ε) :
    DifferentiallyPrivate ε 0 (identifier C ε).law :=
  Epoch.release_private _ _ _ _ (poll_private C he)

private theorem miss_prob (C : LanguageFamily) (ε : ℝ) (he : 0 < ε) (s : ℕ → ℕ)
    (k z : ℕ) (hz : z ≤ k) (ok : ∀ i ≤ k, vote C (ballot s k i) = z) :
    (Epoch.productLaw (poll C ε) s).real {y | y k ≠ z} ≤ (k+1:ℝ)*(Real.exp (-ε/2))^k := by
  let F : Set ℕ := {z}ᶜ
  have eq : (Epoch.productLaw (poll C ε) s).real {y | y k ≠ z} =
      probability (Exponential.law (score C s k) (ε/2)) (Fin.val ⁻¹' F) := by
    change (((Epoch.productLaw (poll C ε) s) ((Function.eval k) ⁻¹' F))).toReal = _
    have h := measurePreserving_eval_infinitePi (fun i => (poll C ε s i).toMeasure) k
    have hF : MeasurableSet F := (measurableSet_singleton z).compl
    rw [Epoch.productLaw,h.measure_preimage hF.nullMeasurableSet,
      PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hF,poll,PMF.toOuterMeasure_map_apply]
    rfl
  have values (j : Fin (k+1)) : score C s k j = if z = j.val then (k+1:ℝ) else 0 := by
    unfold score
    calc
      _ = ∑ _i ∈ Finset.range (k+1), (if z = j.val then (1:ℝ) else 0) :=
        Finset.sum_congr rfl (fun i hi => by rw [ok i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))])
      _ = _ := by split <;> simp_all
  have gap (j : Fin (k+1)) (hj : j ∈ Fin.val ⁻¹' F) :
      (k:ℝ) ≤ score C s k ⟨z,by omega⟩ - score C s k j := by
    change j.val ≠ z at hj
    simp [values,hj.symm]
  rw [eq]
  apply (Exponential.event_margin _ _ (by positivity : 0 ≤ ε/2) _ ⟨z,by omega⟩ k gap).trans_eq
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,←Real.exp_nat_mul]
  congr 2
  ring

theorem identifier_correct (C : LanguageFamily) (hc : Angluin.ConditionTwo C) {ε : ℝ} (he : 0 < ε) :
    IdentifiesStochastically (identifier C ε) C := by
  intro z p hp
  filter_upwards [eventually_ballots C hc z p hp] with s hs
  let j := canon C z
  let r := Real.exp (-ε/2)
  have hr : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have bound : ∀ᶠ k : ℕ in atTop, (Epoch.productLaw (poll C ε) s).real {y | y k ≠ j} ≤ (k+1:ℝ)*r^k := by
    filter_upwards [eventually_ge_atTop j,hs] with k hk ok
    exact miss_prob C ε he s k j hk ok
  have h := eventually_avoid _ _ (summable_linear_geometric (Real.exp_pos _).le hr) bound
  have stable := Epoch.release_stabilizes finish (by decide) (poll C ε) (depends C ε) s j
    (by simpa only [mem_setOf_eq,not_not] using h)
  filter_upwards [stable] with y hy
  exact ⟨j,canon_spec C z,hy⟩

end
end GenLimit.PrivateLimit.Voting
