import GenLimit.Paper23_BanachDensityTopologyAndGeometry.BoardScale
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.BoardSlices
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.BoardSimulation
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.AdversarialPrefixes

/-! If the finite rectangle game fails, a single known infinite language
contains fresh copies of increasingly hard boards. A fair, injective text
finishes a bad rectangle on each board and prevents all later repairs. -/
namespace GenLimit.KleinbergWei.Banach.BoardDiagonal
open Set Finset Filter Real BoardPermutations BoardSlices BoardSimulation
open scoped Classical ENNReal
noncomputable section

private def cost (j : ℕ) : ℝ := ((j:ℝ)+1)^2

private theorem boards {d} (e : ℕ → Lattice d) {q : ℝ} (fail : ¬FiniteRectangleResponse e q) :
    ∃ D : ℕ → Finset ℕ, (∀ j, (D j).Nonempty) ∧ ∀ j move,
      BoardPermutations.Legal (D j) move → ¬ Wins e q (cost j) (D j) move := by
  have each (j : ℕ) : ∃ D : Finset ℕ, ∀ move, BoardPermutations.Legal D move →
      ¬ Wins e q (cost j) D move := by
    by_contra! none
    exact fail ((finite_response_iff e q).2 ⟨cost j,sq_nonneg _,none⟩)
  choose D hard using each
  refine ⟨D,fun j => ?_,hard⟩
  by_contra! empty
  have eq := Finset.not_nonempty_iff_eq_empty.mp empty
  apply hard j (fun _ _ => none) (by intro h x y hit; contradiction)
  intro h _ _ l u widths
  have v : 0 < geometricVolume l u := Finset.prod_pos (fun i _ => by
    change 0 < (u i-l i).toNat; have := widths i; omega)
  have logpos := Real.log_nonneg (by exact_mod_cast v : 1 ≤ (geometricVolume l u:ℝ))
  simp only [eq,Finset.filter_empty,Finset.card_empty,Nat.cast_zero,mul_zero,zero_sub,neg_nonpos]
  exact mul_nonneg (sq_nonneg _) (by linarith)

variable {d} (e : ℕ → Lattice d) (inj : Function.Injective e) (D : ℕ → Finset ℕ)
  {q : ℝ} (hq : 0 < q)
  (hard : ∀ j move, BoardPermutations.Legal (D j) move → ¬Wins e q (cost j) (D j) move)

private def Finished (A : List (Lattice (d+1)) → Lattice (d+1)) (n : ℕ)
    (p : List (Lattice (d+1))) : Prop :=
  ∃ l u, admissibleBox (BoardScale.scale fun i => (D i).card) (language e D) n (l,u) ∧
    (∀ v ∈ Rectangles.box (language e D) l u, v ∈ p) ∧
    (((Rectangles.box (language e D) l u).filter (· ∈ released A p)).card:ℝ) <
      (1/2-q)*(Rectangles.box (language e D) l u).card

include inj hq hard in
private theorem round (A : List (Lattice (d+1)) → Lattice (d+1)) (n : ℕ)
    (p : List (Lattice (d+1))) (hp : Adversary.Legal (language e D) p)
    (lock : ∀ k, p <+: k → Adversary.Legal (language e D) k → A k ∉ k) :
    ∃ r, p <+: r ∧ Adversary.Legal (language e D) r ∧ Finished e D (q:=q) A n r := by
  obtain ⟨j,large,out⟩ := unused e (p.toFinset ∪ released A p) (n+2^(d+1))
  let put := place e j
  let move := simulate (D j) put A p
  have bad := hard j move (safe (D j) put A p)
  unfold Wins at bad
  push_neg at bad
  obtain ⟨h,nd,full,l,u,positive,fails⟩ := bad
  let r := p++h.map put
  let X := BoardSlices.sample e D j l u
  have inside {x} (mem : x ∈ h) : x ∈ D j := full ▸ List.mem_toFinset.mpr mem
  have legal : Adversary.Legal (language e D) r := by
    refine ⟨List.nodup_append.mpr ⟨hp.1,nd.map (BoardSlices.inj e inj j),?_⟩,?_⟩
    · intro v hv w hw eq
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hw
      subst v
      exact out x (Finset.mem_union_left _ (List.mem_toFinset.mpr hv))
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hp.2 v hv
      · obtain ⟨x,mem,rfl⟩ := List.mem_map.mp hv
        exact member e D (inside mem)
  have fresh (k : List ℕ) (pre : k <+: h) : A (p++k.map put) ∉ p++k.map put := by
    have sub : p++k.map put <+: r := by obtain ⟨t,rfl⟩ := pre; exact ⟨t.map put,by simp [r]⟩
    exact lock _ (List.prefix_append ..) ⟨sub.sublist.nodup legal.1,fun x hx => legal.2 _ (sub.subset hx)⟩
  let l' := lower j l
  let u' := upper j u
  let T := Rectangles.box (language e D) l' u'
  let Y := X.filter (· ∈ earned move h)
  have iso : T = X.image put := isolate e D j l u
  have mass : T.card = X.card := count e D inj j l u
  have known (v) (mem : v ∈ T) : ∃ x ∈ X, put x = v :=
    Finset.mem_image.mp (iso ▸ mem)
  have allSeen (v) (mem : v ∈ T) : v ∈ r := by
    obtain ⟨x,hx,rfl⟩ := known v mem
    have hx' : x ∈ h := List.mem_toFinset.mp (full ▸ (Finset.mem_filter.mp hx).1)
    exact List.mem_append_right _ (List.mem_map_of_mem hx')
  have incl : T.filter (· ∈ released A r) ⊆ Y.image put := by
    intro v hv
    obtain ⟨mem,seen⟩ := Finset.mem_filter.mp hv
    obtain ⟨x,hx,rfl⟩ := known v mem
    have credit := recorded (D j) put (BoardSlices.inj e inj j) A p
      (fun y _ old => out y (Finset.mem_union_right _ old)) h (fun _ hx => inside hx) fresh
      (Finset.mem_filter.mp hx).1 seen
    exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,credit⟩,rfl⟩
  have hits := (Finset.card_le_card incl).trans Finset.card_image_le
  have loss : ((T.filter (· ∈ released A r)).card:ℝ) <
      (1/2-q)*(T.card:ℝ)-((j:ℝ)+1)^2*(1+log (geometricVolume l' u')) := by
    rw [mass,volume]
    exact (by exact_mod_cast hits : ((T.filter (· ∈ released A r)).card:ℝ) ≤ Y.card).trans_lt (lt_of_not_ge fails)
  have size : T.card ≤ (D j).card := mass.trans_le (Finset.card_filter_le ..)
  obtain ⟨adm,bound⟩ := BoardScale.admissible_of_loss (language e D) (fun i => (D i).card) n j
    large l' u' (widths positive j) (by linarith : 1/2-q ≤ 1) size loss
  exact ⟨r,List.prefix_append ..,legal,l',u',adm,allSeen,bound⟩


/-- Failure of the uniform finite-board estimate forces an obstruction even
for a known singleton language one dimension higher, on one fixed monotone
diverging filter. Every valid generator has an exact injective bad text. -/
theorem singleton_of_failure {d} (e : ℕ → Lattice d) (he : Function.Injective e)
    {q : ℝ} (positive : 0 < q) (fail : ¬FiniteRectangleResponse e q) :
    ∃ (K : Set (Lattice (d+1))) (f : ℕ → ℝ), K.Infinite ∧ Monotone f ∧
      (∀ v, 0 < f v) ∧ Tendsto f atTop atTop ∧
      ∀ A : List (Lattice (d+1)) → Lattice (d+1),
        (∀ s, Set.range s = K → Function.Injective s → cubeValid A s K) →
        ∃ s, Set.range s = K ∧ Function.Injective s ∧
          filteredRectangularDensity f (Set.range (cubePlay A s)) K ≤ ENNReal.ofReal (1/2-q) := by
  obtain ⟨D,inh,bad⟩ := boards e fail
  let K := language e D
  let f := BoardScale.scale (fun j => (D j).card)
  have inf := BoardSlices.infinite e D inh
  refine ⟨K,f,inf,BoardScale.monotone _,BoardScale.positive _,BoardScale.grows _,fun A valid => ?_⟩
  have fresh (s) (full : Set.range s = K) (ii : Function.Injective s) :
      ∃ T, ∀ t ≥ T, A (textPrefix s t) ∉ textPrefix s t := by
    obtain ⟨T,ok⟩ := valid s full ii
    refine ⟨T+1,fun t ht mem => ?_⟩
    obtain ⟨k,lt,hit⟩ := mem_textPrefix_iff.mp mem
    have succ : t-1+1=t := by omega
    exact (ok (t-1) (by omega)).2.1 k (by omega) (by simpa [cubePlay,succ] using hit)
  obtain ⟨p,_,hp,lock⟩ := Adversary.lock K inf (fun r => A r ∉ r) fresh [] (by simp [Adversary.Legal])
  obtain ⟨H,start,full,ii,done⟩ := Adversary.fair_chain K inf p hp (Finished e D (q:=q) A)
    (fun n r ext legal => round e he D positive bad A n r legal (fun k later => lock k (ext.trans later)))
  refine ⟨H.stream,full,ii,?_⟩
  apply iSup_le
  intro n
  let r := H.history (n+1)
  obtain ⟨l,u,adm,seen,bound⟩ := done n
  let T := Rectangles.box K l u
  let O := Set.range (cubePlay A H.stream)
  have incl : Rectangles.box (O ∩ K) l u ⊆ T.filter (· ∈ released A r) := by
    intro v hv
    obtain ⟨bounds,hit,inK⟩ := Rectangles.mem_box.mp hv
    have mem : v ∈ T := Rectangles.mem_box.mpr ⟨bounds,inK⟩
    refine Finset.mem_filter.mpr ⟨mem,?_⟩
    obtain ⟨i,rfl⟩ := hit
    have atEnd : textPrefix H.stream r.length = r := H.textPrefix_stream _
    by_cases early : i+1 ≤ r.length
    · refine mem_released.mpr ⟨i+1,early,?_⟩
      have eq := List.prefix_iff_eq_take.mp (textPrefix_prefix H.stream early)
      rw [textPrefix_length,atEnd] at eq
      exact congrArg A eq.symm
    · have later : r <+: textPrefix H.stream (i+1) :=
        atEnd ▸ textPrefix_prefix H.stream (by omega : r.length ≤ i+1)
      have ext : p <+: r := start ▸ H.prefix_of_le (Nat.zero_le _)
      have legal : Adversary.Legal K (textPrefix H.stream (i+1)) := by
        refine ⟨List.nodup_range.map ii,fun v hv => ?_⟩
        obtain ⟨k,_,rfl⟩ := mem_textPrefix_iff.mp hv
        exact full ▸ mem_range_self k
      exact (lock _ (ext.trans later) legal (later.subset (seen _ mem))).elim
  change ((T.filter (· ∈ released A r)).card:ℝ) < (1/2-q)*T.card at bound
  have le := (by exact_mod_cast Finset.card_le_card incl :
    ((Rectangles.box (O ∩ K) l u).card:ℝ) ≤ (T.filter (· ∈ released A r)).card).trans_lt bound
  have mp : 0 < (T.card:ℝ) := by
    by_contra! neg
    have zero : (T.card:ℝ)=0 := le_antisymm neg (Nat.cast_nonneg _)
    rw [zero,mul_zero] at le
    exact (not_lt_of_ge (Nat.cast_nonneg _) le).elim
  apply (iInf_le _ (⟨(l,u),adm⟩ : {r // admissibleBox f K n r})).trans
  have rat := (div_lt_iff₀ mp).mpr le
  simpa only [ENNReal.ofReal_div_of_pos mp,ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal rat.le

/-- To prove the filtered theorem for every finite-rank family in dimension
d, it suffices to solve the source's singleton problem in dimension d+1,
even if the singleton algorithm is only guaranteed on injective texts. -/
theorem finite_response_of_singletons {d} (e : ℕ → Lattice d) (he : Function.Injective e)
    {q : ℝ} (positive : 0 < q) (small : q < 1/2)
    (single : ∀ (K : Set (Lattice (d+1))), K.Infinite → ∀ f : ℕ → ℝ,
      Monotone f → (∀ v, 0 < f v) → Tendsto f atTop atTop →
      ∃ A : List (Lattice (d+1)) → Lattice (d+1), ∀ s, Set.range s = K → Function.Injective s →
        cubeValid A s K ∧ ENNReal.ofReal (1/2-q/2) ≤ filteredRectangularDensity f (Set.range (cubePlay A s)) K) :
    FiniteRectangleResponse e q := by
  by_contra fail
  obtain ⟨K,f,inf,mono,pos,grows,defeat⟩ := singleton_of_failure e he positive fail
  obtain ⟨A,complete⟩ := single K inf f mono pos grows
  obtain ⟨s,full,ii,low⟩ := defeat A (fun s full ii => (complete s full ii).1)
  have le := (complete s full ii).2.trans low
  exact (not_le_of_gt (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < 1/2-q/2) |>.mpr (by linarith))) le

end
end GenLimit.KleinbergWei.Banach.BoardDiagonal
