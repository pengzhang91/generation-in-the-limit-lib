import GenLimit.Paper26_IdentificationWithComputationalTrace.StackParsing

namespace GenLimit.ComputationalTrace.PDA

private theorem sub_nil {u : Tree Label} (hs : u.Sub .nil) : u = .nil := by cases hs; rfl

/-- Cutting a subtree gives a context with a fixed instruction prefix and
suffix. Any derivation for the same stack symbol and endpoints fits the hole. -/
theorem Parse.context {P : Program ℕ} {u t : Tree Label} (hs : u.Sub t) (hu : u ≠ .nil)
    {p b z} (h : Parse P t p b z) :
    ∃ p' b' z' pre post, Parse P u p' b' z' ∧ t.items = pre ++ u.items ++ post ∧
      ∀ v, Parse P v p' b' z' → ∃ t', Parse P t' p b z ∧ t'.items = pre ++ v.items ++ post := by
  induction hs generalizing p b z with
  | refl => exact ⟨_,_,_,[],[],h,by simp,fun v hv => ⟨v,hv,by simp⟩⟩
  | @left a l r hs ih =>
    cases h with
    | pop => exact False.elim (hu (sub_nil hs))
    | keep h op hl =>
      obtain ⟨p',b',z',pre,post,hp,he,plug⟩ := ih hl
      refine ⟨p',b',z',a::pre,post,hp,by simp [Tree.items,he], fun v hv => ?_⟩
      obtain ⟨t',ht',hitems⟩ := plug v hv
      exact ⟨_,.keep h op ht',by simp [Tree.items,hitems]⟩
    | push h op hl hr =>
      obtain ⟨p',b',z',pre,post,hp,he,plug⟩ := ih hl
      refine ⟨p',b',z',a::pre,post ++ r.items,hp,by simp [Tree.items,he,List.append_assoc],fun v hv => ?_⟩
      obtain ⟨t',ht',hitems⟩ := plug v hv
      exact ⟨_,.push h op ht' hr,by simp [Tree.items,hitems,List.append_assoc]⟩
  | @right a l r hs ih =>
    cases h with
    | pop => exact False.elim (hu (sub_nil hs))
    | keep => exact False.elim (hu (sub_nil hs))
    | push h op hl hr =>
      obtain ⟨p',b',z',pre,post,hp,he,plug⟩ := ih hr
      refine ⟨p',b',z',a::(l.items ++ pre),post,hp,by simp [Tree.items,he,List.append_assoc],fun v hv => ?_⟩
      obtain ⟨t',ht',hitems⟩ := plug v hv
      exact ⟨_,.push h op hl ht',by simp [Tree.items,hitems,List.append_assoc]⟩

theorem Parse.last_vertex {P : Program ℕ} {t p b z} (h : Parse P t p b z) :
    (t.items.map Label.next).getLast? = some z := by
  have chain := congrArg List.getLast? h.chain
  obtain ⟨a,l,r,rfl⟩ := h.nonempty
  simpa [Tree.items,List.getLast?_cons] using chain.symm

def clip (S : Finset ℕ) (p : Vertex) : Option ℕ × Option Bool :=
  (if p.state ∈ S then some p.state else none,p.look)

def colour (S : Finset ℕ) (a : Label) := (clip S a.start,a.top,clip S a.stop)

def palette (S : Finset ℕ) :=
  let V := insert none (S.image some) ×ˢ (Finset.univ : Finset (Option Bool))
  V ×ˢ ((Finset.univ : Finset Bool) ×ˢ V)

theorem mem_palette (S : Finset ℕ) (a : Label) : colour S a ∈ palette S := by
  simp [colour,palette,clip]; tauto

def protect (S : Finset ℕ) (a : Label) : Bool :=
  a.selected || decide (a.start.state ∉ S) || decide (a.next.state ∉ S)

private theorem clip_inj {S : Finset ℕ} {p q : Vertex} (hp : p.state ∈ S)
    (he : clip S p = clip S q) : p = q := by
  rcases p with ⟨n,x⟩
  rcases q with ⟨m,y⟩
  change n ∈ S at hp
  by_cases hh : m ∈ S <;> simp_all [clip]

/-- A repeated clipped label restores the actual endpoints when the context
deletes only unprotected transitions. If an endpoint is hidden, a nonempty
deleted prefix or suffix touching it would have been protected. -/
theorem equal_key_of_unmarked_context {P : Program ℕ} {S : Finset ℕ}
    {a b : Label} {l r x y : Tree Label}
    (ha : Parse P (.node a l r) a.start a.top a.stop)
    (hb : Parse P (.node b x y) b.start b.top b.stop)
    {pre post : List Label} (eq : (Tree.node a l r).items = pre ++ (Tree.node b x y).items ++ post)
    (hp : pre.filter (protect S) = []) (hs : post.filter (protect S) = [])
    (hc : colour S a = colour S b) : a.key = b.key := by
  obtain ⟨cstart,ctop,cstop⟩ := Prod.mk.inj hc |>.imp_right Prod.mk.inj
  have start : a.start = b.start := by
    cases pre with
    | nil =>
      have he := congrArg List.head? eq
      have hab : a=b := by simpa [Tree.items] using he
      rw [hab]
    | cons first rest =>
      have he := congrArg List.head? eq
      have hab : a=first := by simpa [Tree.items] using he
      subst first
      have hn : protect S a = false := by cases hm : protect S a <;> simp_all
      exact clip_inj (by simpa [protect] using (show ¬ a.start.state ∉ S by
        intro h; simp [protect,h] at hn)) cstart
  have stop : a.stop = b.stop := by
    have va := ha.last_vertex
    have vb := hb.last_vertex
    rw [eq] at va
    cases he : post.getLast? with
    | none =>
      obtain rfl := List.getLast?_eq_none_iff.mp he
      simpa [vb] using va.symm
    | some e =>
      obtain ⟨u,rfl⟩ := List.getLast?_eq_some_iff.mp he
      have hend : e.next = a.stop := by simpa [List.append_assoc] using va
      have hn : e.next.state ∈ S := by
        by_contra hh
        simp [List.filter_append,protect,hh] at hs
      exact clip_inj (hend ▸ hn) cstop
  exact Prod.ext start (Prod.ext ctop stop)

end GenLimit.ComputationalTrace.PDA
