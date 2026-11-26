import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RectangleStages
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.StageRows

/-! The two-color case of Chen–Pach–Szegedy–Tardos used in P23 Theorem 5.1.
We use an integer stage-forest construction. Starting with k^k active
roots, each round keeps the red roots. Either a block of k consecutive
active roots is blue or one red root per block survives. A surviving root
at the last stage has a chain of k red ancestors. -/
namespace GenLimit.KleinbergWei.Banach.Stages
open Set
open scoped Classical
noncomputable section

def Monochromatic (P : Finset Point) (k : ℕ) (color : Point → Bool) : Prop :=
  ∃ lo hi : Point, ∃ c : Bool, k ≤ (trace P lo hi).card ∧ ∀ x ∈ trace P lo hi, color x = c

private theorem enough_red {n d k : ℕ} (color : Point → Bool) (none : ¬Monochromatic (points n d) k color)
    (s : History n) (hs : s.length ≤ d) (hk : 0 < k) (m : ℕ) (cap : m*k ≤ (active s).card) :
    m ≤ ((active s).filter fun r => color (point d s r) = true).card := by
  rcases row_alternative (active s) (fun r => color (point d s r)) hk cap with red | ⟨a,b,size,blue⟩
  · exact red
  · obtain ⟨lo,hi,box⟩ := row_box s hs a b
    let block := (active s).filter fun r => a ≤ r ∧ r ≤ b
    have mem (r : Fin n) (hr : r ∈ block) : point d s r ∈ trace (points n d) lo hi := by
      obtain ⟨act,bounds⟩ := Finset.mem_filter.mp hr
      exact mem_trace.mpr ⟨in_points.mpr ⟨s,hs,r,act,rfl⟩,(box s hs r).mpr ⟨rfl,bounds⟩⟩
    apply False.elim; apply none
    refine ⟨lo,hi,false,size.trans (Finset.card_le_card_of_injOn (point d s) mem
      (fun _ _ _ _ eq => (point_injective hs hs eq).2)),?_⟩
    intro x hx
    obtain ⟨hp,bounds⟩ := mem_trace.mp hx
    obtain ⟨t,ht,r,act,rfl⟩ := in_points.mp hp
    obtain ⟨rfl,al,ub⟩ := (box t ht r).mp bounds
    exact blue r act al ub

private theorem red_rectangle {n d k : ℕ} (color : Point → Bool) (s : History n) (r : Fin n)
    (hs : s.length ≤ d) (size : k ≤ s.length+1) (activeRoot : r ∈ active s)
    (red : ∀ t, t <+: s → color (point d t r) = true) : Monochromatic (points n d) k color := by
  obtain ⟨lo,hi,box⟩ := path_box s hs r
  let B := trace (points n d) lo hi
  let vertex (i : Fin k) := point d (s.take i.val) r
  have length_eq (i : Fin k) : (s.take i.val).length=i.val := by
    rw [List.length_take,Nat.min_eq_left (by omega)]
  have inside (i : Fin k) : vertex i ∈ B := by
    have pre := List.take_prefix i.val s
    exact mem_trace.mpr ⟨in_points.mpr ⟨_,pre.length_le.trans hs,r,active_mono pre activeRoot,rfl⟩,
      (box _ (pre.length_le.trans hs) r).mpr ⟨rfl,pre⟩⟩
  let placed (i : Fin k) : B := ⟨vertex i,inside i⟩
  have inj : Function.Injective placed := by
    intro i j e
    have eq : vertex i=vertex j := congrArg (fun a : B => a.val) e
    have same := (point_injective ((List.take_prefix i.val s).length_le.trans hs)
      ((List.take_prefix j.val s).length_le.trans hs) eq).1
    exact Fin.ext ((length_eq i).symm.trans ((congrArg List.length same).trans (length_eq j)))
  refine ⟨lo,hi,true,by simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective placed inj,?_⟩
  intro x hx
  obtain ⟨hp,bounds⟩ := mem_trace.mp hx
  obtain ⟨t,ht,v,_,rfl⟩ := in_points.mp hp
  obtain ⟨rfl,pre⟩ := (box t ht v).mp bounds
  exact red _ pre

/-- For every positive k one finite integer point set forces a monochromatic
axis-parallel rectangle with at least k points under every two-coloring. -/
theorem finite_rectangle (k : ℕ) (hk : 0 < k) : ∃ P : Finset Point, ∀ color, Monochromatic P k color := by
  let n := k^k
  refine ⟨points n k,?_⟩
  intro color
  by_contra none
  have reach (j : ℕ) (hj : j ≤ k) : ∃ s : History n, s.length=j ∧ k^(k-j) ≤ (active s).card ∧
      ∀ r ∈ active s, ∀ t, t <+: s → t.length < j → color (point k t r) = true := by
    induction j with
    | zero => exact ⟨[],rfl,by simp [n],by simp⟩
    | succ j ih =>
      obtain ⟨s,len,card,red⟩ := ih (by omega)
      let T := (active s).filter fun r => color (point k s r) = true
      have eq : k-j=(k-(j+1))+1 := by omega
      have cap : k^(k-(j+1))*k ≤ (active s).card := by rwa [←pow_succ,←eq]
      have count := enough_red color none s (by omega) hk _ cap
      have act : active (s++[T]) = T := by
        rw [active_next,Finset.inter_eq_right.mpr (Finset.filter_subset ..)]
      refine ⟨s++[T],by simp [len],act.symm ▸ count,?_⟩
      intro r hr t pre shorter
      have keep := Finset.mem_filter.mp (show r ∈ T from act ▸ hr)
      have lt : t.length ≤ s.length := by omega
      have old : t <+: s := by
        rw [List.prefix_iff_eq_take.mp pre,List.take_append_of_le_length lt]
        exact List.take_prefix ..
      by_cases equal : t.length=s.length
      · have same : t=s := old.eq_of_length equal
        exact same.symm ▸ keep.2
      · exact red r keep.1 t old (by omega)
  obtain ⟨u,len',card,allRed⟩ := reach k le_rfl
  have positive : 0 < (active u).card := by simpa using card
  obtain ⟨r,member⟩ := Finset.card_pos.mp positive
  let t := u.take (k-1)
  have pre := List.take_prefix (k-1) u
  have length_eq : t.length=k-1 := by simp [t,len']
  apply none
  exact red_rectangle color t r (by omega) (by omega) (active_mono pre member) (fun v h =>
    allRed r member v (h.trans pre) (by have := h.length_le; omega))

end
end GenLimit.KleinbergWei.Banach.Stages
