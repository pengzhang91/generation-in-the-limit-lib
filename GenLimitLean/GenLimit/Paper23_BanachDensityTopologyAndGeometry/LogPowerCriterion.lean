import GenLimit.Paper23_BanachDensityTopologyAndGeometry.SingletonReduction
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.ClaimGame
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Comparison of the filter in P23 Theorem 5.5 with the finite rectangle
bound in Kleinberg and Wei, arXiv:2611.14887v1, Lemma 8.1. We use P23's
positive-width rectangles and encode finite plays by permutations of the
board. The logarithm in the power threshold counts lattice sites. -/
namespace GenLimit.KleinbergWei.Banach.LogPowerCriterion
open BoardPermutations Finset Real Set
open scoped Classical
noncomputable section

private abbrev Box (d : ℕ) := Lattice d × Lattice d
def trace {d} (e : ℕ → Lattice d) (D : Finset ℕ) (r : Box d) :=
  D.filter fun x => e x ∈ Finset.Icc r.1 r.2

def logSites {d} (r : Lattice d × Lattice d) : ℝ :=
  log (2 + ((Finset.Icc r.1 r.2).card:ℝ))

/-- The common terminal condition for both finite games. -/
def PacketQuota {d} (e : ℕ → Lattice d) (q c τ : ℝ) (D : Finset ℕ)
    (packet : Finset (Lattice d × Lattice d)) (white : Set ℕ) : Prop :=
  ∀ r ∈ packet, (∀ i, r.1 i < r.2 i) →
    let X := trace e D r
    c*(logSites r)^(1+τ) ≤ X.card → (1/2-q)*(X.card:ℝ) ≤ (X.filter (· ∈ white)).card

/-- A common threshold constant for every positive exponent and every finite
packet. White's strategy may depend on the exponent, packet and board. -/
def UniformPowerResponse {d} (e : ℕ → Lattice d) (q : ℝ) : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ τ : ℝ, 0 < τ → ∀ (D : Finset ℕ) (packet : Finset (Lattice d × Lattice d)),
    ∃ move : Move, Legal D move ∧ ∀ h : List ℕ, h.Nodup → h.toFinset = D →
      PacketQuota e q c τ D packet (earned move h)

/-- Unused-point game with a constant independent of τ. Points of the finite
lattice board are named by their indices under the embedding e. -/
def UniformClaimResponse {d} (e : ℕ → Lattice d) (q : ℝ) : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ τ : ℝ, 0 < τ → ∀ (D : Finset ℕ) (packet : Finset (Lattice d × Lattice d)),
    ClaimGame.CanForce D (PacketQuota e q c τ D packet)

/-- Purely logarithmic eligibility in the alternating game. -/
def LogarithmicClaimResponse {d} (e : ℕ → Lattice d) (q : ℝ) : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ (D : Finset ℕ) (packet : Finset (Lattice d × Lattice d)),
    ClaimGame.CanForce D (PacketQuota e q c 0 D packet)

private theorem volume_comparison {d} (r : Box d) (wide : ∀ i, r.1 i < r.2 i) :
    0 < geometricVolume r.1 r.2 ∧
    geometricVolume r.1 r.2 ≤ (Finset.Icc r.1 r.2).card ∧
    (Finset.Icc r.1 r.2).card ≤ 2^d*geometricVolume r.1 r.2 := by
  have pos : 0 < geometricVolume r.1 r.2 := Finset.prod_pos fun i _ => by have := wide i; omega
  refine ⟨pos,?_,?_⟩
  · rw [Pi.card_Icc]
    apply Finset.prod_le_prod'
    intro i _
    rw [Int.card_Icc]; omega
  · simpa [Rectangles.box] using card_le_geometricVolume (Set.univ : Set (Lattice d)) wide

def factor (d : ℕ) : ℝ := 1+log (2+(2:ℝ)^d)

theorem log_comparison {d} (r : Box d) (wide : ∀ i, r.1 i < r.2 i) :
    1 ≤ logSites r ∧ 1+log (geometricVolume r.1 r.2) ≤ 2*logSites r ∧
    logSites r ≤ factor d*(1+log (geometricVolume r.1 r.2)) := by
  obtain ⟨p,lo,hi⟩ := volume_comparison r wide
  let V := geometricVolume r.1 r.2
  let N := (Finset.Icc r.1 r.2).card
  have vp : (1:ℝ) ≤ V := by exact_mod_cast p
  have np : (V:ℝ) ≤ N := by exact_mod_cast lo
  have up : (N:ℝ) ≤ (2:ℝ)^d*V := by exact_mod_cast hi
  have small : 1 ≤ log (2+(N:ℝ)) := (Real.le_log_iff_exp_le (by positivity)).mpr
    (by linarith [Real.exp_one_lt_d9])
  have vl : 0 ≤ log (V:ℝ) := Real.log_nonneg vp
  have scale : 0 ≤ log (2+(2:ℝ)^d) := Real.log_nonneg (by linarith [show 0 ≤ (2:ℝ)^d by positivity])
  have mid := Real.log_le_log (by linarith : 0 < (V:ℝ)) (show (V:ℝ) ≤ 2+N by linarith)
  refine ⟨small, by change 1+log (V:ℝ) ≤ 2*log (2+(N:ℝ)); linarith,?_⟩
  have h := Real.log_le_log (by positivity : 0 < 2+(N:ℝ))
    (show 2+(N:ℝ) ≤ (2+(2:ℝ)^d)*V by linarith)
  rw [Real.log_mul (by positivity) (by linarith : (V:ℝ) ≠ 0)] at h
  change log (2+(N:ℝ)) ≤ (1+log (2+(2:ℝ)^d))*(1+log (V:ℝ))
  nlinarith [mul_nonneg scale vl]

/-- A finite packet result extends to every rectangle in a prescribed
class on the same board. Choose one eligible rectangle per distinct trace. -/
theorem all_boxes_on {d} {e : ℕ → Lattice d} {q c τ : ℝ} (D : Finset ℕ)
    (test : (Lattice d × Lattice d) → Prop)
    (packetWin : ∀ packet : Finset (Lattice d × Lattice d), (∀ r ∈ packet, test r) →
      ClaimGame.CanForce D (PacketQuota e q c τ D packet)) :
    ClaimGame.CanForce D (fun W => ∀ r : Lattice d × Lattice d, test r →
      (∀ i, r.1 i < r.2 i) →
      let X := D.filter (fun x => e x ∈ Finset.Icc r.1 r.2)
      c*(logSites r)^(1+τ) ≤ X.card → (1/2-q)*(X.card:ℝ) ≤ (X.filter (· ∈ W)).card) := by
  let represents (X : Finset ℕ) (r : Box d) := trace e D r = X ∧ test r ∧
    (∀ i, r.1 i < r.2 i) ∧ c*(logSites r)^(1+τ) ≤ X.card
  let rep (X : Finset ℕ) : Box d := if h : ∃ r, represents X r then h.choose else 0
  let packet := (D.powerset.image rep).filter test
  obtain ⟨move,safe,win⟩ := packetWin packet (fun _ hr => (Finset.mem_filter.mp hr).2)
  refine ⟨move,safe,fun h legal done r tested wide large => ?_⟩
  let X := trace e D r
  have existsRep : ∃ r', represents X r' := ⟨r,rfl,tested,wide,large⟩
  have cert : represents X (rep X) := by simpa only [rep,dif_pos existsRep] using existsRep.choose_spec
  have mem : rep X ∈ D.powerset.image rep := Finset.mem_image_of_mem rep
    (Finset.mem_powerset.mpr (Finset.filter_subset _ D : X ⊆ D))
  have game := win h legal done (rep X) (Finset.mem_filter.mpr ⟨mem,cert.2.1⟩) cert.2.2.1
    (cert.1.symm ▸ cert.2.2.2)
  change (1/2-q)*((trace e D (rep X)).card:ℝ) ≤
    (((trace e D (rep X)).filter (· ∈ earned move h)).card:ℝ) at game
  rw [cert.1] at game
  exact game

/-- A finite board needs one representative of each eligible trace, even
when the terminal condition asks for all translated rectangles. -/
private theorem all_boxes {d} {e : ℕ → Lattice d} {q c τ : ℝ} (D : Finset ℕ)
    (packetWin : ∀ packet : Finset (Box d), ∃ move : Move, Legal D move ∧
      ∀ h : List ℕ, h.Nodup → h.toFinset = D → ∀ r ∈ packet,
        (∀ i, r.1 i < r.2 i) → c*(logSites r)^(1+τ) ≤ (trace e D r).card →
        (1/2-q)*((trace e D r).card:ℝ) ≤ ((trace e D r).filter (· ∈ earned move h)).card) :
    ∃ move : Move, Legal D move ∧ ∀ h : List ℕ, h.Nodup → h.toFinset = D → ∀ r : Box d,
      (∀ i, r.1 i < r.2 i) → c*(logSites r)^(1+τ) ≤ (trace e D r).card →
      (1/2-q)*((trace e D r).card:ℝ) ≤ ((trace e D r).filter (· ∈ earned move h)).card := by
  have win := (ClaimGame.canForce_iff ..).mp (all_boxes_on (e:=e) (q:=q) (c:=c) (τ:=τ)
    D (fun _ => True) (fun packet _ => (ClaimGame.canForce_iff ..).mpr (packetWin packet)))
  obtain ⟨move,safe,all⟩ := win
  exact ⟨move,safe,fun h nd full r => all h nd full r trivial⟩

/-- A board-dependent small exponent turns the uniform family of power
bounds into one logarithmic error bound, with a constant shared by all boards. -/
theorem finite_of_uniform {d} (e : ℕ → Lattice d) {q : ℝ} (hq : 0 < q)
    (H : UniformPowerResponse e q) : FiniteRectangleResponse e q := by
  obtain ⟨c,hc,packets⟩ := H
  have cp : 0 < c := by linarith
  have fp : 0 ≤ factor d := by
    unfold factor
    linarith [Real.log_nonneg (show 1 ≤ 2+(2:ℝ)^d by linarith [show (0:ℝ) ≤ 2^d by positivity])]
  apply (finite_response_iff ..).mpr
  refine ⟨2*c*factor d,by positivity,fun D => ?_⟩
  let T : ℝ := D.card+1
  have Tpos : 1 ≤ T := by dsimp [T]; linarith [Nat.cast_nonneg (α := ℝ) D.card]
  let τ := log 2/(1+log T)
  have den : 0 < 1+log T := by linarith [log_nonneg Tpos]
  have tp : 0 < τ := div_pos (log_pos (by norm_num)) den
  obtain ⟨move,safe,win⟩ := all_boxes D (packets τ tp D)
  refine ⟨move,safe,fun h nd full l u wide => ?_⟩
  let r : Box d := (l,u)
  let X := trace e D r
  let B := logSites r
  let V := geometricVolume l u
  obtain ⟨one,_,upper⟩ := log_comparison r wide
  change (1/2-q)*(X.card:ℝ) - (2*c*factor d)*(1+log V) ≤ (X.filter (· ∈ earned move h)).card
  have vp : 0 < V := (volume_comparison r wide).1
  have ln : 0 ≤ log (V:ℝ) := log_nonneg (by exact_mod_cast vp)
  by_cases mass : 2*c*B ≤ X.card
  · have card : (X.card:ℝ) ≤ D.card := by exact_mod_cast (Finset.card_filter_le .. : X.card ≤ D.card)
    have bound : B ≤ T := by dsimp [T]; nlinarith [show (1:ℝ) ≤ B from one]
    have bp : 0 < B := by linarith [show (1:ℝ) ≤ B from one]
    have small : B^τ ≤ 2 := by
      rw [Real.rpow_def_of_pos bp,←Real.exp_log (by norm_num : (0:ℝ)<2),Real.exp_le_exp]
      have logb := Real.log_le_log bp bound
      change log B*(log 2/(1+log T)) ≤ log 2
      rw [←mul_div_assoc,div_le_iff₀ den]
      exact (mul_le_mul_of_nonneg_right logb (log_nonneg (by norm_num))).trans
        (by nlinarith [log_pos (by norm_num : (1:ℝ) < 2)])
    have big : c*B^(1+τ) ≤ X.card := by
      rw [Real.rpow_add bp,Real.rpow_one]
      nlinarith [mul_le_mul_of_nonneg_left small (mul_nonneg cp.le bp.le)]
    have hit := win h nd full r wide big
    exact (sub_le_self _ (by positivity)).trans hit
  · have logCap : 2*c*B ≤ 2*c*factor d*(1+log V) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left upper (show 0 ≤ 2*c by positivity)
    have m : 0 ≤ (X.card:ℝ) := by positivity
    have hits : 0 ≤ ((X.filter (· ∈ earned move h)).card:ℝ) := by positivity
    push_neg at mass
    nlinarith [mul_nonneg hq.le m]

/-- A logarithmic loss can be absorbed in the tolerance already at exponent zero. -/
private theorem logarithmic_of_finite {d} (e : ℕ → Lattice d) {q : ℝ} (hq : 0 < q)
    (H : FiniteRectangleResponse e (q/2)) : LogarithmicClaimResponse e q := by
  obtain ⟨b,hb,boards⟩ := (finite_response_iff ..).mp H
  let c := max 1 (4*b/q)
  have cp : 1 ≤ c := le_max_left ..
  have large : 4*b ≤ c*q := (div_le_iff₀ hq).mp (le_max_right ..)
  refine ⟨c,cp,fun D packet => (ClaimGame.canForce_iff ..).mpr ?_⟩
  obtain ⟨move,legal,win⟩ := boards D
  refine ⟨move,legal,fun h nd full r _ width size => ?_⟩
  let X := trace e D r
  let B := logSites r
  obtain ⟨one,cap,_⟩ := log_comparison r width
  have m : c*B ≤ X.card := by simpa only [add_zero,Real.rpow_one] using size
  have cost := mul_le_mul_of_nonneg_left cap hb
  have hit := win h nd full r.1 r.2 width
  change (1/2-q/2)*(X.card:ℝ)-b*(1+log (geometricVolume r.1 r.2)) ≤
    ((X.filter (· ∈ earned move h)).card:ℝ) at hit
  change (1/2-q)*(X.card:ℝ) ≤ ((X.filter (· ∈ earned move h)).card:ℝ)
  change 1 ≤ B at one
  change b*(1+log (geometricVolume r.1 r.2)) ≤ b*(2*B) at cost
  nlinarith only [cost,hit,mul_le_mul_of_nonneg_right large (by linarith : 0 ≤ B),
    mul_le_mul_of_nonneg_right m hq.le]

private theorem uniform_of_logarithmic {d} (e : ℕ → Lattice d) {q : ℝ}
    (H : LogarithmicClaimResponse e q) : UniformPowerResponse e q := by
  obtain ⟨c,hc,packets⟩ := H
  refine ⟨c,hc,fun τ tp D packet => ?_⟩
  obtain ⟨move,safe,win⟩ := (ClaimGame.canForce_iff ..).mp (packets D packet)
  refine ⟨move,safe,fun h nd full r mem wide size => win h nd full r mem wide ?_⟩
  simp only [add_zero,Real.rpow_one]
  have one := (log_comparison r wide).1
  have power : logSites r ≤ (logSites r)^(1+τ) := by
    calc
      logSites r = (logSites r)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one (by linarith)
  exact (mul_le_mul_of_nonneg_left power (by linarith)).trans size

theorem uniform_of_finite {d} (e : ℕ → Lattice d) {q : ℝ} (hq : 0 < q)
    (H : FiniteRectangleResponse e (q/2)) : UniformPowerResponse e q :=
  uniform_of_logarithmic e (logarithmic_of_finite e hq H)

/-- Across dimensions and positive tolerances, the unrestricted P23
conclusion is equivalent to a uniform-in-exponent finite-packet bound in
the permutation formulation. The strategies themselves can vary with τ. -/
theorem generation_iff_uniform_power_response :
    (∀ d q, 0 < q → FiniteRankFilteredGuarantee d q) ↔
      ∀ d (e : ℕ → Lattice d), Function.Injective e →
        ∀ q : ℝ, 0 < q → q < 1/2 → UniformPowerResponse e q := by
  constructor
  · intro gen d e inj q hq small
    apply uniform_of_finite e hq
    apply BoardDiagonal.finite_response_of_singletons e inj (half_pos hq) (by linarith)
    exact singleton_of_finite_rank _ _ (gen _ _ (half_pos (half_pos hq)))
  · intro games d ε he e inj C inf R rank f grows
    let q := min ε (1/4)
    have pos : 0 < q := lt_min he (by norm_num)
    have small : q < 1/2 := (min_le_right ..).trans_lt (by norm_num)
    obtain ⟨A,hA⟩ := filtered_generation_of_finite_response e inj pos
      (finite_of_uniform e pos (games d e inj q pos small)) f grows C inf rank
    refine ⟨A,fun z s pres => ?_⟩
    obtain ⟨valid,half⟩ := hA z s pres
    exact ⟨valid,(ENNReal.ofReal_le_ofReal (sub_le_sub_left (min_le_left ..) _)).trans half⟩

/-- The criterion in the alternating rules of Lemma 8.1 of
arXiv:2611.14887v1, restricted to positive-width rectangles. -/
theorem generation_iff_uniform_claim_response :
    (∀ d q, 0 < q → FiniteRankFilteredGuarantee d q) ↔
      ∀ d (e : ℕ → Lattice d), Function.Injective e →
        ∀ q : ℝ, 0 < q → q < 1/2 → UniformClaimResponse e q := by
  simpa only [UniformClaimResponse,ClaimGame.canForce_iff,UniformPowerResponse]
    using generation_iff_uniform_power_response

/-- Extending the later finite-game lemma to τ = 0 is necessary and sufficient
for the full P23 filtered guarantee. The constant may depend on the tolerance. -/
theorem generation_iff_logarithmic_claim_response :
    (∀ d q, 0 < q → FiniteRankFilteredGuarantee d q) ↔
      ∀ d (e : ℕ → Lattice d), Function.Injective e →
        ∀ q : ℝ, 0 < q → q < 1/2 → LogarithmicClaimResponse e q := by
  constructor
  · intro gen d e inj q hq small
    apply logarithmic_of_finite e hq
    apply BoardDiagonal.finite_response_of_singletons e inj (half_pos hq) (by linarith)
    exact singleton_of_finite_rank _ _ (gen _ _ (half_pos (half_pos hq)))
  · intro games
    exact generation_iff_uniform_power_response.mpr fun d e inj q hq small =>
      uniform_of_logarithmic e (games d e inj q hq small)

end
end GenLimit.KleinbergWei.Banach.LogPowerCriterion
