import GenLimit.Paper23_BanachDensityTopologyAndGeometry.CarriedRemainders

/-! An explicit laminar family for the pure logarithmic rectangle game.
The nodes are traces of aligned dyadic cubes on the board. Their cutoffs
depend only on the population of a node. Points assigned no requirement
at a small node remain available to every larger node. -/
namespace GenLimit.KleinbergWei.Banach.RegionGame.DyadicRequirements
open Finset Real LatticeTiles LogPowerCriterion
open scoped Classical
noncomputable section

abbrev Box (d : ℕ) := Lattice d × Lattice d
private def size {d} (r : Box d) := (Finset.Icc r.1 r.2).card
private def scale {d} (r : Box d) := Nat.log 2 (size r) + 1
private def side {d} (r : Box d) := 2^(scale r)
private def tile {d} (e : ℕ → Lattice d) (D : Finset ℕ) (j : ℕ) (k : Lattice d) :=
  D.filter (fun x => number (2^j) (e x) = k)

private theorem coarsen {d j t} {x y : Lattice d} (levels : j ≤ t)
    (eq : number (2^j) x = number (2^j) y) : number (2^t) x = number (2^t) y := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le levels
  funext i
  have h := congrFun eq i
  change x i / ((2^j:ℕ):ℤ) = y i / ((2^j:ℕ):ℤ) at h
  have quot := congrArg (fun z : ℤ => z / ((2^b:ℕ):ℤ)) h
  simp only [Int.ediv_ediv (show 0 ≤ ((2^j:ℕ):ℤ) by positivity)] at quot
  simpa only [number,pow_add,Nat.cast_mul] using quot

private theorem common_tile {d} (e : ℕ → Lattice d) (D : Finset ℕ) {x j t a b}
    (jle : j ≤ t) (left : x ∈ tile e D j a) (right : x ∈ tile e D t b) :
    tile e D j a ⊆ tile e D t b := by
  intro y hy
  obtain ⟨onBoard,loc⟩ := Finset.mem_filter.mp hy
  exact Finset.mem_filter.mpr ⟨onBoard,
    (coarsen jle (loc.trans (Finset.mem_filter.mp left).2.symm)).trans (Finset.mem_filter.mp right).2⟩

private def pieces {d} (e : ℕ → Lattice d) (D : Finset ℕ) (r : Box d) :=
  (indices (side r) r.1 r.2).image (tile e D (scale r))

private def family {d} (e : ℕ → Lattice d) (D : Finset ℕ) (S : Finset (Box d)) :=
  insert D (S.biUnion (pieces e D))

private theorem kind {d} {e : ℕ → Lattice d} {D : Finset ℕ} {S : Finset (Box d)}
    {A : Finset ℕ} (mem : A ∈ family e D S) : A = D ∨ ∃ j a, A = tile e D j a := by
  rcases Finset.mem_insert.mp mem with eq | rest
  · exact Or.inl eq
  · obtain ⟨r,_,pre⟩ := Finset.mem_biUnion.mp rest
    obtain ⟨a,_,eq⟩ := Finset.mem_image.mp pre
    exact Or.inr ⟨_,a,eq.symm⟩

private theorem within {d} {e : ℕ → Lattice d} {D : Finset ℕ} {S : Finset (Box d)}
    {A : Finset ℕ} (mem : A ∈ family e D S) : A ⊆ D := by
  rcases kind mem with rfl | ⟨_,_,rfl⟩
  · rfl
  · exact Finset.filter_subset ..

abbrev Node {d} (e : ℕ → Lattice d) (D : Finset ℕ) (S : Finset (Box d)) :=
  OrderDual ↥(family e D S)

/-- Coincident cube traces share a single node. Inclusion on board traces
is the ancestor order, with the whole board at the root. -/
def tree {d} (e : ℕ → Lattice d) (D : Finset ℕ) (S : Finset (Box d)) : Hierarchy (Node e D S) where
  board := D
  region u := (OrderDual.ofDual u).val
  root := OrderDual.toDual ⟨D,Finset.mem_insert_self ..⟩
  cover := Finset.Subset.rfl
  nested h := h
  path := by
    intro x u v hx hy
    let a := OrderDual.ofDual u
    let b := OrderDual.ofDual v
    change (b.val ⊆ a.val) ∨ (a.val ⊆ b.val)
    change x ∈ a.val at hx
    change x ∈ b.val at hy
    rcases kind a.property with eq | ⟨j,s,eq⟩
    · rw [eq]; exact Or.inl (within b.property)
    rcases kind b.property with eq' | ⟨t,k,eq'⟩
    · rw [eq']; exact Or.inr (within a.property)
    rw [eq,eq']
    rw [eq] at hx
    rw [eq'] at hy
    rcases le_total j t with le | le
    · exact Or.inr (common_tile e D le hx hy)
    · exact Or.inl (common_tile e D le hy hx)

/-- One cutoff serves both as the minimum size of a local requirement
and the maximum residual passed up from this node. -/
def cutoff {d} {e : ℕ → Lattice d} {D : Finset ℕ} {S : Finset (Box d)} (a : ℝ) (v : Node e D S) :=
  a*(1+log (1+((OrderDual.ofDual v).val.card:ℝ)))

private def tiles {d} {e : ℕ → Lattice d} {D : Finset ℕ} {S : Finset (Box d)}
    (r : Box d) (mem : r ∈ S) : Finset (Node e D S) :=
  (pieces e D r).attach.image (fun B => OrderDual.toDual ⟨B.val,
    Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨r,mem,B.property⟩)⟩)

private theorem covers {d} {e : ℕ → Lattice d} {D : Finset ℕ} {S : Finset (Box d)}
    (r : Box d) (mem : r ∈ S) : ∀ x ∈ boardTrace e D r, ∃ v ∈ tiles (e:=e) (D:=D) r mem,
      x ∈ (tree e D S).region v := by
  intro x hit
  obtain ⟨onBoard,inR⟩ := Finset.mem_filter.mp hit
  let k := number (side r) (e x)
  have idx : k ∈ indices (side r) r.1 r.2 := number_mem (by dsimp [side]; positivity) inR
  have piece : tile e D (scale r) k ∈ pieces e D r := Finset.mem_image_of_mem _ idx
  refine ⟨_,Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨_,piece⟩),?_⟩
  exact Finset.mem_filter.mpr ⟨onBoard,rfl⟩

private theorem tile_population {d} {e : ℕ → Lattice d} (inj : Function.Injective e)
    (D : Finset ℕ) (j : ℕ) (k : Lattice d) : (tile e D j k).card ≤ (2^j)^d := by
  let L : ℕ := 2^j
  have pos : 0 < L := by dsimp [L]; positivity
  have sub : (tile e D j k).image e ⊆ cell L k := by
    rintro x hx
    obtain ⟨y,inTile,rfl⟩ := Finset.mem_image.mp hx
    exact (cell_iff pos ..).mpr (Finset.mem_filter.mp inTile).2
  have cap := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ inj,cell,Pi.card_Icc] at cap
  have axis (i : Fin d) : (Finset.Icc (lower L k i) (upper L k i)).card = L := by
    rw [Int.card_Icc]
    dsimp [lower,upper]
    omega
  simpa only [axis,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using cap

private theorem num_tiles {d} {e : ℕ → Lattice d} {D : Finset ℕ} {S : Finset (Box d)}
    (r : Box d) (hr : r ∈ S) (wide : ∀ i, r.1 i < r.2 i) :
    (tiles (e:=e) (D:=D) r hr).card ≤ 2*3^d := by
  let L := side r
  have pos : 0 < L := by dsimp [L,side]; positivity
  have fits : unitVolume r.1 r.2 ≤ L := (unitVolume_le_card (fun i => (wide i).le)).trans
    (Nat.lt_pow_succ_log_self (b:=2) (by decide) (size r)).le
  have raw := (card_indices pos (fun i => (wide i).le)).trans
    (Nat.mul_le_mul_left (3^d) (Nat.add_le_add_left fits L))
  rw [show 3^d*(L+L) = L*(2*3^d) by ring] at raw
  have first : (tiles (e:=e) (D:=D) r hr).card ≤ (pieces e D r).card :=
    (Finset.card_image_le.trans_eq Finset.card_attach)
  exact first.trans (Finset.card_image_le.trans (Nat.le_of_mul_le_mul_left raw pos))

/-- One constant pays for the complete geometric cover on every board and
at every scale, with no condition on the distance of a rectangle. -/
theorem cover_cost {d} {e : ℕ → Lattice d} (inj : Function.Injective e) {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (D : Finset ℕ) (S : Finset (Box d)) (r : Box d), r ∈ S →
      (∀ i, r.1 i < r.2 i) → ∃ nodes : Finset (Node e D S),
      (∀ v ∈ nodes, 0 < cutoff a v) ∧ (∀ x ∈ boardTrace e D r, ∃ v ∈ nodes, x ∈ (tree e D S).region v) ∧
      ∑ v ∈ nodes, cutoff a v ≤ B*logSites r := by
  let B : ℝ := (2*3^d:ℕ)*a*(2+2*(d:ℝ))
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  intro D S r mem wide
  let N := size r
  have np : 0 < N := Finset.card_pos.mpr ⟨r.1,Finset.mem_Icc.mpr ⟨le_rfl,fun i => (wide i).le⟩⟩
  have Lpos : 0 < side r := by dsimp [side]; positivity
  have Lcap : side r ≤ 2*N := by
    dsimp only [side,scale]; rw [pow_succ,Nat.mul_comm 2 N]
    exact Nat.mul_le_mul_right 2 (Nat.pow_log_le_self _ np.ne')
  let Slog := logSites r
  have one : 1 ≤ Slog := (log_comparison r wide).1
  have twolog : log 2 ≤ Slog := Real.log_le_log (by norm_num)
    (show (2:ℝ) ≤ 2+(N:ℝ) by linarith [Nat.cast_nonneg (α:=ℝ) N])
  have Llog : log (side r) ≤ 2*Slog := by
    have lr : (side r:ℝ) ≤ 2*N := by exact_mod_cast Lcap
    have le : (side r:ℝ) ≤ (2+(N:ℝ))^2 := by nlinarith [sq_nonneg (N:ℝ)]
    have h := Real.log_le_log (by exact_mod_cast Lpos) le
    rwa [Real.log_pow,Nat.cast_ofNat] at h
  let nodes := tiles (e:=e) (D:=D) r mem
  refine ⟨nodes,?_,covers r mem,?_⟩
  · intro v _
    apply mul_pos ha
    have nn : 0 ≤ log (1+((OrderDual.ofDual v).val.card:ℝ)) := Real.log_nonneg (by simp)
    linarith
  have each (v : Node e D S) (hv : v ∈ nodes) : cutoff a v ≤ a*(2+2*(d:ℝ))*Slog := by
    obtain ⟨Bv,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨k,_,eq⟩ := Finset.mem_image.mp Bv.property
    have count : Bv.val.card ≤ (side r)^d := eq ▸ tile_population inj D (scale r) k
    have cp : (Bv.val.card:ℝ) ≤ (side r:ℝ)^d := by exact_mod_cast count
    have base : (1:ℝ) ≤ side r := by exact_mod_cast Lpos
    have le : 1+(Bv.val.card:ℝ) ≤ 2*(side r:ℝ)^d := by linarith [one_le_pow₀ base (n:=d)]
    have cap := Real.log_le_log (by positivity) le
    rw [Real.log_mul (by norm_num) (by positivity : (side r:ℝ)^d ≠ 0),Real.log_pow] at cap
    change a*(1+log (1+(Bv.val.card:ℝ))) ≤ _
    nlinarith only [mul_le_mul_of_nonneg_left cap ha.le,
      mul_le_mul_of_nonneg_left Llog (show 0 ≤ a*(d:ℝ) by positivity),
      mul_le_mul_of_nonneg_left twolog ha.le,mul_le_mul_of_nonneg_left one ha.le]
  have total := Finset.sum_le_sum each
  rw [Finset.sum_const,nsmul_eq_mul] at total
  have bound : (nodes.card:ℝ) ≤ (2*3^d:ℕ) := by exact_mod_cast num_tiles (e:=e) (D:=D) r mem wide
  apply total.trans
  calc
    _ ≤ ((2*3^d:ℕ):ℝ)*(a*(2+2*(d:ℝ))*Slog) := mul_le_mul_of_nonneg_right bound
      (mul_nonneg (by positivity) (zero_le_one.trans one))
    _ = B*logSites r := by dsimp [B,Slog]; ring

/-- A sufficient local game for the unrestricted endpoint. All board and
packet geometry in this criterion is fixed explicitly. Only the ability to
win the resulting simultaneous local quotas is a hypothesis. -/
theorem logarithmic_of_local_quotas {d} {e : ℕ → Lattice d} (inj : Function.Injective e)
    {a q : ℝ} (ha : 0 < a) (hq : 0 < q) (small : q ≤ 1/2)
    (game : ∀ (D : Finset ℕ) (S : Finset (Box d)), ClaimGame.CanForce D
      (fun W => ∀ v, ∀ Q ∈ CarriedRemainders.requests (tree e D S) (cutoff a)
        (S.image (boardTrace e D)) v, (1/2-q/2)*(Q.card:ℝ) ≤ (Q.filter (· ∈ W)).card)) :
    LogarithmicClaimResponse e q := by
  obtain ⟨B,bn,cover⟩ := cover_cost inj ha
  let c := max 1 (B/q)
  refine ⟨c,le_max_left ..,fun D S => ?_⟩
  apply CarriedRemainders.logarithmic_packet (tree e D S) (cutoff a) e S hq small _ (game D S)
  intro r mem wide
  obtain ⟨nodes,pos,all,cap⟩ := cover D S r mem wide
  refine ⟨nodes,pos,all,cap.trans ?_⟩
  have large : B ≤ c*q := (div_le_iff₀ hq).mp (le_max_right ..)
  have nn := zero_le_one.trans (log_comparison r wide).1
  calc
    _ ≤ (c*q)*logSites r := mul_le_mul_of_nonneg_right large nn
    _ = _ := by ring

end
end GenLimit.KleinbergWei.Banach.RegionGame.DyadicRequirements
