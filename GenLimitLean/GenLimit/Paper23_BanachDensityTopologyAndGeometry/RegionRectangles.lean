import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RegionQuotas
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.LogPowerCriterion

/-! Local rectangular requirements and the logarithmic finite-game
criterion for Theorem 5.5. -/
namespace GenLimit.KleinbergWei.Banach.RegionGame
open Finset Real LogPowerCriterion
open scoped Classical
noncomputable section

private abbrev Box (d : ℕ) := Lattice d × Lattice d

def boardTrace {d} (e : ℕ → Lattice d) (D : Finset ℕ) (r : Lattice d × Lattice d) :=
  D.filter fun x => e x ∈ Finset.Icc r.1 r.2

private abbrev Endpoints (d : ℕ) (D : Finset ℕ) := (Fin d → D) × (Fin d → D)

private def spanned {d} (e : ℕ → Lattice d) (D : Finset ℕ) (p : Endpoints d D) :=
  boardTrace e D ((fun i => e (p.1 i) i),fun i => e (p.2 i) i)

/-- A nonempty trace is determined by at most two board points per axis,
even if their coordinates repeat or the board has arbitrarily large gaps. -/
private def traces {d} (e : ℕ → Lattice d) (D : Finset ℕ) :=
  insert ∅ (Finset.univ.image (spanned e D))

private theorem trace_mem {d} (e : ℕ → Lattice d) (D : Finset ℕ) (r : Box d) :
    boardTrace e D r ∈ traces e D := by
  let X := boardTrace e D r
  by_cases nonempty : X.Nonempty
  · have bounds (i : Fin d) : ∃ a b : D, (a:ℕ) ∈ X ∧ (b:ℕ) ∈ X ∧
        ∀ x ∈ X, e a i ≤ e x i ∧ e x i ≤ e b i := by
      obtain ⟨a,ha,lo⟩ := X.exists_min_image (fun x => e x i) nonempty
      obtain ⟨b,hb,hi⟩ := X.exists_max_image (fun x => e x i) nonempty
      exact ⟨⟨a,(Finset.mem_filter.mp ha).1⟩,⟨b,(Finset.mem_filter.mp hb).1⟩,ha,hb,
        fun x hx => ⟨lo x hx,hi x hx⟩⟩
    choose a b ha hb both using bounds
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨(a,b),Finset.mem_univ _,Finset.ext fun x => ?_⟩
    constructor
    · intro mem
      obtain ⟨onBoard,lo,hi⟩ := Finset.mem_filter.mp mem |>.imp_right Finset.mem_Icc.mp
      exact Finset.mem_filter.mpr ⟨onBoard,Finset.mem_Icc.mpr
        ⟨fun i => ((Finset.mem_Icc.mp (Finset.mem_filter.mp (ha i)).2).1 i).trans (lo i),
         fun i => (hi i).trans ((Finset.mem_Icc.mp (Finset.mem_filter.mp (hb i)).2).2 i)⟩⟩
    · intro mem
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp mem).1,Finset.mem_Icc.mpr
        ⟨fun i => (both i x mem).1,fun i => (both i x mem).2⟩⟩
  · have eq : boardTrace e D r = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    rw [eq]; exact Finset.mem_insert_self ..

private theorem card_traces {d} (e : ℕ → Lattice d) (D : Finset ℕ) :
    (traces e D).card ≤ 1 + D.card^(2*d) := by
  have card : Fintype.card (Endpoints d D) = D.card^(2*d) := by
    simp [Endpoints,Fintype.card_pi,two_mul,pow_add]
  have bound := Finset.card_insert_le ∅ (Finset.univ.image (spanned e D))
  have size := Finset.card_image_le (f:=spanned e D) (s:=Finset.univ)
  rw [Finset.card_univ,card] at size
  unfold traces
  omega

/-- A construction depending only on the trace inside a fixed region has at
most polynomially many distinct outputs there. -/
theorem card_clipped_image {d} (e : ℕ → Lattice d) (D B : Finset ℕ) (S : Finset (Box d))
    (g : Finset ℕ → Finset ℕ) (clip : ∀ X, g (X ∩ B) = g X) :
    ((S.image (boardTrace e D)).image g).card ≤ 1 + (D ∩ B).card^(2*d) := by
  have sub : (S.image (boardTrace e D)).image g ⊆ (traces e (D ∩ B)).image g := by
    intro Q mem
    obtain ⟨X,pre,rfl⟩ := Finset.mem_image.mp mem
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp pre
    have same : boardTrace e D r ∩ B = boardTrace e (D ∩ B) r := by
      ext x; simp [boardTrace]; tauto
    rw [←clip (boardTrace e D r),same]
    exact Finset.mem_image_of_mem _ (trace_mem e _ r)
  exact (Finset.card_le_card sub).trans (Finset.card_image_le.trans (card_traces e _))

/-- An unconditional causal strategy for every finite board and all rectangle
sizes at once. Its additive loss depends on the number of points on the
board, independently of its coordinate span or the gaps between points. -/
theorem population_bound {d} (e : ℕ → Lattice d) (D : Finset ℕ) {q : ℝ}
    (hq : 0 < q) (small : q ≤ 1/2) :
    ClaimGame.CanForce D (fun W => ∀ r : Lattice d × Lattice d,
      let X := boardTrace e D r
      (1/2-q) * (X.card:ℝ) - log ((1+q)*(1+(D.card:ℝ)^(2*d)))/(2*q) ≤
        (X.filter (· ∈ W)).card) := by
  let I := ↥(traces e D)
  let E (i : I) := (i : Finset ℕ)
  let w (_ : I) : ℝ := 1
  have sub (i : I) : E i ⊆ D := by
    obtain ⟨X,mem⟩ := i
    rcases Finset.mem_insert.mp mem with rfl | mem
    · exact Finset.empty_subset _
    · obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp mem
      exact Finset.filter_subset ..
  obtain ⟨move,safe,win⟩ := ClaimGame.weighted_tests D E sub w (fun _ => zero_lt_one) hq small
  refine ⟨move,safe,fun h play done r => ?_⟩
  · let X := boardTrace e D r
    let i : I := ⟨X,trace_mem e D r⟩
    have bound := win h play done i
    have mass : (∑ j, w j) = ((traces e D).card:ℝ) := by simp [w,I]
    rw [mass,show w i = 1 from rfl,div_one] at bound
    have size : ((traces e D).card:ℝ) ≤ 1+(D.card:ℝ)^(2*d) := by exact_mod_cast card_traces e D
    have pos : (0:ℝ) < (traces e D).card := by
      exact_mod_cast Finset.card_pos.mpr (show (traces e D).Nonempty from ⟨_,trace_mem e D r⟩)
    have hp : 0 < 1+q := by linarith
    have cost := div_le_div_of_nonneg_right
      (Real.log_le_log (mul_pos hp pos) (mul_le_mul_of_nonneg_left size hp.le))
      (by positivity : 0 ≤ 2*q)
    exact (sub_le_sub_left cost _).trans bound

variable {V : Type*} [PartialOrder V] (T : Hierarchy V) (γ α : V → ℝ)
variable {d : ℕ} (e : ℕ → Lattice d)

/-- The number of different retained requirements in a region depends
polynomially on its board population, independently of its side length. -/
theorem card_local_requests (packet : Finset (Lattice d × Lattice d)) (v : V) :
    (T.requests γ α (packet.image (boardTrace e T.board)) v).card ≤
      1 + (T.board ∩ T.region v).card^(2*d) := by
  exact (Finset.card_filter_le ..).trans (card_clipped_image e T.board (T.region v) packet
    (fun X => T.remainder γ X v) (fun X => remainder_clip T γ X v))

/-- Population-sensitive initialization for the exponential potential in
Appendix A. The cutoff can depend on the actual number of distinct labels. -/
theorem initial_weight_bound (packet : Finset (Lattice d × Lattice d)) (v : V) {s : ℝ} (hs : 0 ≤ s) :
    ∑ Q ∈ T.requests γ α (packet.image (boardTrace e T.board)) v, exp (-s*Q.card) ≤
      (1 + ((T.board ∩ T.region v).card:ℝ)^(2*d)) * exp (-s*α v) := by
  let req := T.requests γ α (packet.image (boardTrace e T.board)) v
  have per (Q : Finset ℕ) (mem : Q ∈ req) : exp (-s*Q.card) ≤ exp (-s*α v) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Finset.mem_filter.mp mem).2 (neg_nonpos.mpr hs))
  have total := Finset.sum_le_sum per
  rw [Finset.sum_const,nsmul_eq_mul] at total
  have size : (req.card : ℝ) ≤ 1 + ((T.board ∩ T.region v).card:ℝ)^(2*d) := by
    exact_mod_cast card_local_requests T γ α e packet v
  exact total.trans (mul_le_mul_of_nonneg_right size (Real.exp_pos _).le)

variable [Fintype V]

/-- One strategy for an entire finite packet at the pure logarithmic
threshold. The two geometric hypotheses bound the cutoff cost of covering
a rectangle and the mass actually discarded during its decomposition.
The local quotas can be won using `canForce_quotas`. -/
theorem logarithmic_packet (packet : Finset (Lattice d × Lattice d)) {q c : ℝ}
    (hq : 0 < q) (small : q ≤ 1/2) (nonneg : ∀ v, 0 ≤ γ v)
    (cover : ∀ r ∈ packet, (∀ i, r.1 i < r.2 i) →
      ∃ tiles : Finset V, (∀ x ∈ boardTrace e T.board r, ∃ v ∈ tiles, x ∈ T.region v) ∧
        ∑ v ∈ tiles, γ v ≤ q/2 * (c * logSites r))
    (discard : ∀ r ∈ packet, (∀ i, r.1 i < r.2 i) → c * logSites r ≤ (boardTrace e T.board r).card →
      ∑ v, T.discard γ α (boardTrace e T.board r) v ≤ q/2 * (boardTrace e T.board r).card)
    (localGame : ClaimGame.CanForce T.board (fun W => ∀ v,
      ∀ Q ∈ T.requests γ α (packet.image (boardTrace e T.board)) v,
        (1/2-q/2) * (Q.card:ℝ) ≤ (Q.filter (· ∈ W)).card)) :
    ClaimGame.CanForce T.board (PacketQuota e q c 0 T.board packet) := by
  obtain ⟨move,safe,win⟩ := canForce_packet T γ α _ localGame
  refine ⟨move,safe,fun h play exhausted r mem wide size => ?_⟩
  let X := boardTrace e T.board r
  have enough : c * logSites r ≤ X.card := by simpa only [add_zero,Real.rpow_one] using size
  obtain ⟨tiles,covered,cost⟩ := cover r mem wide
  have miss := (uncovered_bound T γ X tiles (fun v _ => nonneg v) covered).trans
    (cost.trans (mul_le_mul_of_nonneg_left enough (by linarith)))
  have lost := discard r mem wide enough
  have hits := win h play exhausted X (Finset.mem_image_of_mem _ mem)
  have retained : (1-q) * (X.card:ℝ) ≤ (X.card:ℝ) - (T.uncovered γ X).card - ∑ v, T.discard γ α X v := by
    change ∑ v, T.discard γ α X v ≤ q/2 * X.card at lost
    linarith
  have rate : 0 ≤ 1/2-q/2 := by linarith
  have cap := (mul_le_mul_of_nonneg_left retained rate).trans hits
  change (1/2-q) * (X.card:ℝ) ≤ ((X.filter (· ∈ BoardPermutations.earned move h)).card:ℝ)
  nlinarith only [cap,mul_nonneg (sq_nonneg q) (Nat.cast_nonneg (α:=ℝ) X.card)]

end
end GenLimit.KleinbergWei.Banach.RegionGame
