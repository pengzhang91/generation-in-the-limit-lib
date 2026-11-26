import GenLimit.Paper16_ComplexityBarriers.Profiles

/-! # Pumping finite intersections of locally threshold testable profiles

At a cut of a word, the longest matching suffix among prefixes of all tests
determines which tests finish on the next letter. While extending a word,
each occurrence count can be saturated one above its threshold. Equal
sums of these monotone counters at two cuts force every counter to agree. -/

namespace GenLimit.ComplexityBarriers.LTT
open List
open scoped Classical
noncomputable section

private def pool (ws : List (List α)) : Finset (List α) :=
  insert [] (ws.flatMap List.inits).toFinset

private theorem mem_pool {ws : List (List α)} {p : List α} :
    p ∈ pool ws ↔ p = [] ∨ ∃ w ∈ ws, p <+: w := by simp [pool,List.mem_inits]

private theorem in_pool {ws : List (List α)} {w : List α} (h : w ∈ ws) : w ∈ pool ws :=
  mem_pool.mpr (Or.inr ⟨w,h,List.prefix_rfl⟩)

private theorem prefix_mem_pool {ws : List (List α)} {p q : List α}
    (hp : p <+: q) (hq : q ∈ pool ws) : p ∈ pool ws := by
  rcases mem_pool.mp hq with rfl | ⟨w,hw,hqw⟩
  · exact mem_pool.mpr (Or.inl (by simpa using hp))
  · exact mem_pool.mpr (Or.inr ⟨w,hw,hp.trans hqw⟩)

private theorem pool_card (ws : List (List α)) :
    (pool ws).card ≤ 1 + (ws.map (fun w ↦ w.length+1)).sum := by
  have h : (ws.flatMap List.inits).length = (ws.map (fun w ↦ w.length+1)).sum := by
    induction ws with
    | nil => rfl
    | cons w ws ih => simp [List.length_inits,ih]
  have hc := (ws.flatMap List.inits).toFinset_card_le
  exact (Finset.card_insert_le ..).trans (by omega)

private theorem longest (ws : List (List α)) (x : List α) :
    ∃ q : ↥(pool ws), ∀ p ∈ pool ws, p <:+ x ↔ p <:+ q.val := by
  let T := (pool ws).filter (· <:+ x)
  have hn : T.Nonempty := ⟨[],Finset.mem_filter.mpr ⟨mem_pool.mpr (.inl rfl),List.nil_suffix⟩⟩
  obtain ⟨q,hq,hm⟩ := T.exists_max_image List.length hn
  obtain ⟨hq',hqx⟩ := Finset.mem_filter.mp hq
  exact ⟨⟨q,hq'⟩,fun p hp ↦ ⟨fun hx ↦ List.suffix_of_suffix_length_le hx hqx
    (hm p (Finset.mem_filter.mpr ⟨hp,hx⟩)),fun h ↦ h.trans hqx⟩⟩

private def capped (c : Constraint α) (w : List α) := min (occurrences c.word w) (c.bound+1)

private def Same (ws : List (List α)) (cs : List (Constraint α)) (u v : List α) : Prop :=
  (∀ p ∈ pool ws, p <:+ u ↔ p <:+ v) ∧ ∀ c ∈ cs, capped c u = capped c v

private theorem same_snoc {ws : List (List α)} {cs : List (Constraint α)}
    (hcs : ∀ c ∈ cs, c.word ∈ ws) {u v : List α} (h : Same ws cs u v) (a : α) :
    Same ws cs (u++[a]) (v++[a]) := by
  have hs : ∀ p ∈ pool ws, p <:+ u++[a] ↔ p <:+ v++[a] := by
    intro p
    induction p using List.reverseRecOn with
    | nil => simp
    | append_singleton p b _ =>
      intro hp
      rw [suffix_snoc,suffix_snoc,h.1 p (prefix_mem_pool (List.prefix_append ..) hp)]
  refine ⟨hs,?_⟩
  intro c hc
  have he := h.2 c hc
  have hi := hs c.word (in_pool (hcs c hc))
  unfold capped at *
  rw [occurrences_snoc,occurrences_snoc]
  by_cases hy : c.word <:+ u ++ [a]
  · simp only [if_pos hy,if_pos (hi.mp hy)]; omega
  · simp only [if_neg hy,if_neg (fun hz ↦ hy (hi.mpr hz)),Nat.add_zero]; exact he

private theorem same_append {ws : List (List α)} {cs : List (Constraint α)}
    (hcs : ∀ c ∈ cs, c.word ∈ ws) {u v : List α} (h : Same ws cs u v) (z : List α) :
    Same ws cs (u++z) (v++z) := by
  induction z using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton z a ih => simpa only [List.append_assoc] using same_snoc hcs ih a

private theorem capped_mono (c : Constraint α) {u v : List α} (h : u <+: v) :
    capped c u ≤ capped c v := by
  obtain ⟨z,rfl⟩ := h
  apply min_le_min_right
  induction z using List.reverseRecOn with
  | nil => simp
  | append_singleton z a ih =>
    rw [←List.append_assoc,occurrences_snoc]; omega

private def score (cs : List (Constraint α)) (u : List α) := (cs.map (fun c ↦ capped c u)).sum

private theorem score_le (cs : List (Constraint α)) (u : List α) :
    score cs u ≤ (cs.map (fun c ↦ c.bound+1)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    exact Nat.add_le_add (min_le_right ..) ih

private theorem score_mono (cs : List (Constraint α)) {u v : List α} (h : u <+: v) :
    score cs u ≤ score cs v := by
  induction cs with
  | nil => rfl
  | cons c cs ih => exact Nat.add_le_add (capped_mono c h) ih

private theorem capped_eq_of_score_eq (cs : List (Constraint α)) {u v : List α}
    (huv : u <+: v) (he : score cs u = score cs v) : ∀ c ∈ cs, capped c u = capped c v := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    change capped c u + score cs u = capped c v + score cs v at he
    have hc := capped_mono c huv
    have hs := score_mono cs huv
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · omega
    · exact ih (by omega) d hd

private theorem test_of_capped {c : Constraint α} {u v : List α} (h : capped c u = capped c v) :
    c.cmp.test (occurrences c.word u) c.bound ↔ c.cmp.test (occurrences c.word v) c.bound := by
  unfold capped at h
  cases c.cmp <;> simp only [Comparison.test] <;> omega

private def words (Ps : List (Profile α)) : List (List α) :=
  Ps.flatMap fun P ↦ P.back :: P.rules.map Constraint.word

private def rules (Ps : List (Profile α)) := Ps.flatMap Profile.rules

private def budget (Ps : List (Profile α)) := (Ps.map Profile.contentSize).sum

private def intersection (Ps : List (Profile α)) : Set (List α) :=
  {w | ∀ P ∈ Ps, w ∈ P.language}

private theorem rule_mem {Ps : List (Profile α)} {c : Constraint α} (hc : c ∈ rules Ps) :
    c.word ∈ words Ps := by
  obtain ⟨P,hP,hc⟩ := List.mem_flatMap.mp hc
  exact List.mem_flatMap.mpr ⟨P,hP,List.mem_cons_of_mem _ (List.mem_map_of_mem hc)⟩

private theorem word_cost (Ps : List (Profile α)) :
    ((words Ps).map (fun w ↦ w.length+1)).sum ≤ budget Ps := by
  induction Ps with
  | nil => rfl
  | cons P Ps ih =>
    have hr (cs : List (Constraint α)) :
        (cs.map (fun c ↦ c.word.length+1)).sum ≤ (cs.map (fun c ↦ 1+c.word.length+c.bound)).sum := by
      induction cs with
      | nil => rfl
      | cons c cs ih => exact Nat.add_le_add (by dsimp; omega) ih
    have hh := hr P.rules
    simp only [words,List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,
      List.map_map,Function.comp_def,budget,Profile.contentSize] at ih ⊢
    omega

private theorem counter_cost (Ps : List (Profile α)) :
    ((rules Ps).map (fun c ↦ c.bound+1)).sum ≤ budget Ps := by
  induction Ps with
  | nil => rfl
  | cons P Ps ih =>
    have hr (cs : List (Constraint α)) :
        (cs.map (fun c ↦ c.bound+1)).sum ≤ (cs.map (fun c ↦ 1+c.word.length+c.bound)).sum := by
      induction cs with
      | nil => rfl
      | cons c cs ih => exact Nat.add_le_add (by dsimp; omega) ih
    have hh := hr P.rules
    simp only [rules,List.flatMap_cons,List.map_append,List.sum_append,budget,List.map_cons,
      List.sum_cons,Profile.contentSize] at ih ⊢
    omega

private theorem size_le_budget {Ps : List (Profile α)} {P : Profile α} (hP : P ∈ Ps) :
    P.contentSize ≤ budget Ps := by
  induction Ps with
  | nil => cases hP
  | cons Q Ps ih =>
    rcases List.mem_cons.mp hP with rfl | hP
    · exact Nat.le_add_right _ _
    · exact (ih hP).trans (Nat.le_add_left _ _)

private theorem extend_word (Ps : List (Profile α)) {w : List α} (hw : w ∈ intersection Ps)
    (hlong : budget Ps + (budget Ps+1)^2 ≤ w.length) :
    ∃ w' ∈ intersection Ps, w.length < w'.length := by
  let r := budget Ps
  let ws := words Ps
  let cs := rules Ps
  let cuts := (r+1)^2
  let cut := fun i : Fin (cuts+1) ↦ w.take (r+i.val)
  have hlen (i : Fin (cuts+1)) : (cut i).length = r+i.val := by
    dsimp [cut]; rw [List.length_take,Nat.min_eq_left]; change r+cuts ≤ w.length at hlong; omega
  choose q hq using longest ws
  let f := fun i : Fin (cuts+1) ↦
    (q (cut i), (⟨score cs (cut i), Nat.lt_succ_of_le ((score_le ..).trans (counter_cost Ps))⟩ : Fin (r+1)))
  have hc : Fintype.card (↥(pool ws) × Fin (r+1)) < Fintype.card (Fin (cuts+1)) := by
    rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_fin,Fintype.card_coe]
    have hh := (pool_card ws).trans (Nat.add_le_add_left (word_cost Ps) 1)
    change (pool ws).card ≤ 1+r at hh
    change _ < (r+1)^2+1
    rw [pow_two]
    exact Nat.lt_succ_of_le (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨i,j,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt f hc
  wlog hij : i < j generalizing i j
  · exact this j i hne.symm he.symm (lt_of_le_of_ne (le_of_not_gt hij) hne.symm)
  have hpre : cut i <+: cut j := List.prefix_of_prefix_length_le (List.take_prefix ..) (List.take_prefix ..)
    (by rw [hlen,hlen]; exact Nat.add_le_add_left (Fin.le_of_lt hij) r)
  have hs : Same ws cs (cut i) (cut j) := by
    constructor
    · intro p hp
      have hh := congrArg Prod.fst he
      change q (cut i) = q (cut j) at hh
      rw [hq (cut i) p hp,hq (cut j) p hp,hh]
    · exact capped_eq_of_score_eq cs hpre (congrArg (fun t ↦ t.2.val) he)
  obtain ⟨x,hx⟩ := hpre
  let z := w.drop (r+j.val)
  have hz : cut j ++ z = w := List.take_append_drop ..
  have hse : Same ws cs w (cut j ++ x ++ z) := by
    have h := same_append (cs := cs) (fun _ h ↦ rule_mem h) hs x
    rw [hx] at h
    simpa only [hz] using same_append (cs := cs) (fun _ h ↦ rule_mem h) h z
  refine ⟨cut j ++ x ++ z,?_,?_⟩
  · intro P hP
    obtain ⟨hfront,hback,ht⟩ := hw P hP
    have hsize := size_le_budget hP
    have hp : P.front.length ≤ r := by unfold Profile.contentSize at hsize; omega
    have hfr := List.prefix_of_prefix_length_le hfront (List.take_prefix (r+j.val) w)
      (show P.front.length ≤ (cut j).length by rw [hlen]; omega)
    refine ⟨(hfr.trans (List.prefix_append _ x)).trans (List.prefix_append ..),?_,?_⟩
    · exact (hse.1 P.back (in_pool (List.mem_flatMap.mpr ⟨P,hP,List.mem_cons_self⟩))).mp hback
    · intro c hc'
      exact (test_of_capped (hse.2 c (List.mem_flatMap.mpr ⟨P,hP,hc'⟩))).mp (ht c hc')
  · have hxlen := congrArg List.length hx
    have hzlen := congrArg List.length hz
    have hij' : i.val < j.val := hij
    simp only [List.length_append,hlen] at hxlen hzlen ⊢
    omega

private theorem finite_intersection_bound {Ps : List (Profile α)} (hPs : Ps ≠ [])
    (hf : (intersection Ps).Finite) {w : List α} (hw : w ∈ intersection Ps) :
    w.length < 3*budget Ps*((budget Ps)^2+1)^2 := by
  obtain ⟨v,hv,hm⟩ := Set.exists_max_image _ List.length hf ⟨w,hw⟩
  have hs : v.length < budget Ps + (budget Ps+1)^2 := by
    by_contra! hh
    obtain ⟨v',hv',hl⟩ := extend_word Ps hv hh
    exact (Nat.not_lt_of_ge (hm v' hv')) hl
  have hr : 0 < budget Ps := by
    obtain ⟨P,hP⟩ := List.exists_mem_of_ne_nil Ps hPs
    have hp := size_le_budget hP
    unfold Profile.contentSize at hp
    omega
  let r := budget Ps
  have hr' : 1 ≤ r := hr
  have hpow : r ≤ r^2 := by simpa only [pow_two,one_mul] using Nat.mul_le_mul_right r hr'
  have hsq : (r+1)^2 ≤ (r^2+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hone : 1 ≤ (r^2+1)^2 := Nat.succ_le_of_lt (pow_pos (Nat.succ_pos _) _)
  have h₁ := Nat.mul_le_mul_left r hone
  have h₂ := Nat.mul_le_mul_right ((r^2+1)^2) hr'
  have hmul : 3*r*((r^2+1)^2) = 3*(r*((r^2+1)^2)) := Nat.mul_assoc ..
  apply (hm w hw).trans_lt (hs.trans_le ?_)
  change r+(r+1)^2 ≤ 3*r*((r^2+1)^2)
  rw [hmul]
  omega

/-- The upper bound in Theorem 5.1(a), including finite unions of profiles. -/
theorem profile_upper_content [Fintype α] (ha : 2 ≤ Fintype.card α) (F : Finset (Set (List α))) (s : ℕ)
    (hF : ∀ L ∈ F, ∃ Ps : List (Profile α), (Ps.map Profile.contentSize).sum ≤ s ∧
      L = {w | ∃ P ∈ Ps, w ∈ P.language}) :
    MGeneratable (F : Set (Set (List α))) ((Fintype.card α)^(3*(s*F.card)*((s*F.card)^2+1)^2)) := by
  apply mGeneratable_of_small_intersections
  intro S hS hne hf
  let T := (F.finite_toSet.subset hS).toFinset
  have he : (T : Set (Set (List α))) = S := Set.Finite.coe_toFinset _
  choose ps hps hL using fun i : ↥T ↦ hF i (hS (he ▸ i.property))
  apply ncard_lt_of_length_lt ha
  intro w hw
  have hw' (i : ↥T) : ∃ P ∈ ps i, w ∈ P.language := by
    have hh := hw i.val (he ▸ i.property)
    rwa [hL i] at hh
  choose p hp hwp using hw'
  let I := (Finset.univ : Finset ↥T).toList
  let Ps := I.map p
  have allI (i : ↥T) : i ∈ I := by simp [I]
  have hi (i : ↥T) : p i ∈ Ps := List.mem_map_of_mem (allI i)
  have hPs : Ps ≠ [] := by
    obtain ⟨L,hLS⟩ := hne
    have hh := hi ⟨L,(F.finite_toSet.subset hS).mem_toFinset.mpr hLS⟩
    intro h; rw [h] at hh; simp at hh
  have hsub : intersection Ps ⊆ Support.classIntersection S := by
    intro v hv L hLS
    let i : ↥T := ⟨L,(F.finite_toSet.subset hS).mem_toFinset.mpr hLS⟩
    change v ∈ i.val
    rw [hL i]
    exact ⟨p i,hp i,hv (p i) (hi i)⟩
  have hmem : w ∈ intersection Ps := by
    intro P hP
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hP
    exact hwp i
  have hh := finite_intersection_bound hPs (hf.subset hsub) hmem
  have hc (l : List ↥T) : budget (l.map p) ≤ s*l.length := by
    induction l with
    | nil => simp [budget]
    | cons i l ih =>
      have hsize := (size_le_budget (hp i)).trans (hps i)
      change (p i).contentSize + budget (l.map p) ≤ s*(l.length+1)
      rw [Nat.mul_add,Nat.mul_one,Nat.add_comm (s*l.length) s]
      exact Nat.add_le_add hsize ih
  have hb : budget Ps ≤ s*F.card := by
    apply (hc I).trans
    apply Nat.mul_le_mul_left
    simpa [I] using Finset.card_le_card (show T ⊆ F from fun _ hi ↦ hS (he ▸ hi))
  exact hh.trans_le (by gcongr)

theorem profile_upper [Fintype α] (ha : 2 ≤ Fintype.card α) (F : Finset (Set (List α))) (s : ℕ)
    (hF : ∀ L ∈ F, LTTAtMost s L) :
    MGeneratable (F : Set (Set (List α))) ((Fintype.card α)^(3*(s*F.card)*((s*F.card)^2+1)^2)) := by
  apply profile_upper_content ha F s
  intro L hL
  obtain ⟨Ps,hs,he⟩ := hF L hL
  have hle (l : List (Profile α)) : (l.map Profile.contentSize).sum ≤ (l.map Profile.size).sum := by
    induction l with
    | nil => rfl
    | cons P l ih => exact Nat.add_le_add (contentSize_le_size P) ih
  exact ⟨Ps,(hle Ps).trans hs,he⟩

end
end GenLimit.ComplexityBarriers.LTT
