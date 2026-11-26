import GenLimit.Paper31_BoundedMemory.FixedOrderDensity

/-! # The fixed-order results on any enumerated word universe
An enumeration gives ranks e : α ≃ ℕ. Families and generators are relabelled
together. The buffer translation applies e to every stored example and to
the new observation, preserving the update and the no-synthesis constraint.
-/
namespace GenLimit.BoundedMemory.RankedUniverse
open Set Function KleinbergWei

structure Family (α : Type*) (k : ℕ) where
  lang : Fin k → Set α
  distinct : Injective lang
  infinite : ∀ i, (lang i).Infinite

def Family.map (e : α ≃ β) (L : Family α k) : Family β k where
  lang i := e '' L.lang i
  distinct := (Set.image_injective.mpr e.injective).comp L.distinct
  infinite i := (L.infinite i).image e.injective.injOn

private theorem Family.map_onto (e : α ≃ β) : Surjective (Family.map (k := k) e) := by
  intro L
  refine ⟨L.map e.symm,?_⟩
  cases L with
  | mk lang hd hi =>
    dsimp only [Family.map]
    congr 1
    funext i
    change e '' (e.symm '' lang i) = lang i
    ext x
    simp

def setRule (e : α ≃ β) (G : MemorylessSetGenerator α) : MemorylessSetGenerator β :=
  fun y => e '' G (e.symm y)

private theorem setRule_onto (e : α ≃ β) : Surjective (setRule e) := by
  intro G
  exact ⟨setRule e.symm G,funext (fun y => by ext x; simp [setRule])⟩

private def window (e : α ≃ β) (w : DistinctWindow α W) : DistinctWindow β W :=
  ⟨e ∘ w.val,e.injective.comp w.property⟩

private theorem window_roundtrip (e : α ≃ β) (w : DistinctWindow β W) :
    window e (window e.symm w) = w := by
  ext i
  exact e.apply_symm_apply _

def windowRule (e : α ≃ β) (G : WindowSetGenerator α W) : WindowSetGenerator β W where
  output w := e '' G (window e.symm w)
  output_infinite _ := (G.output_infinite _).image e.injective.injOn

private theorem windowRule_onto (e : α ≃ β) : Surjective (windowRule (W := W) e) := by
  intro G
  refine ⟨windowRule e.symm G,?_⟩
  cases G with
  | mk output hi =>
    dsimp only [windowRule]
    congr 1
    funext w
    change e '' (e.symm '' output (window e (window e.symm w))) = output w
    rw [window_roundtrip]
    ext x
    simp

def buffer (e : α ≃ β) (m : BufferState α b) : BufferState β b :=
  ⟨m.val.map e,by simpa using m.property⟩

private theorem buffer_roundtrip (e : α ≃ β) (m : BufferState β b) :
    buffer e (buffer e.symm m) = m := by
  apply Subtype.ext
  simp [buffer,List.map_map,Function.comp_def]

private theorem buffer_inverse (e : α ≃ β) (m : BufferState α b) :
    buffer e.symm (buffer e m) = m := by
  simpa only [Equiv.symm_symm] using buffer_roundtrip e.symm m

def bufferRule (e : α ≃ β) (G : BufferSetGenerator α b) : BufferSetGenerator β b where
  output m y := e '' G.output (buffer e.symm m) (e.symm y)
  output_infinite m y := (G.output_infinite _ _).image e.injective.injOn
  update m y := buffer e (G.update (buffer e.symm m) (e.symm y))
  update_supported m y v hv := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    rcases G.update_supported _ _ _ hx with hm|he
    · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hm
      exact Or.inl (by simpa using hz)
    · exact Or.inr (he ▸ e.apply_symm_apply y)

theorem buffer_state_map (e : α ≃ β) (G : BufferSetGenerator α b) (s : ℕ → α) (t : ℕ) :
    bufferState (bufferRule e G) (e ∘ s) t = buffer e (bufferState G s t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change buffer e (G.update (buffer e.symm (bufferState (bufferRule e G) (e ∘ s) t))
      (e.symm (e (s t)))) = _
    rw [ih,buffer_inverse, e.symm_apply_apply]
    rfl

theorem buffer_output_map (e : α ≃ β) (G : BufferSetGenerator α b) (s : ℕ → α) (t : ℕ) :
    bufferOutputAt (bufferRule e G) (e ∘ s) t = e '' bufferOutputAt G s t := by
  change e '' G.output (buffer e.symm (bufferState (bufferRule e G) (e ∘ s) t)) _ = _
  rw [buffer_state_map,buffer_inverse]
  simp [bufferOutputAt]

theorem window_output_map (e : α ≃ β) (G : WindowSetGenerator α W) (s : ℕ → α)
    (hs : Injective s) (t : ℕ) :
    (windowRule e G) (windowAt (e ∘ s) (e.injective.comp hs) t W) = e '' G (windowAt s hs t W) := by
  have h : window e.symm (windowAt (e ∘ s) (e.injective.comp hs) t W) = windowAt s hs t W := by
    ext i
    exact e.symm_apply_apply _
  change e '' G (window e.symm _) = _
  rw [h]

private theorem bufferRule_onto (e : α ≃ β) : Surjective (bufferRule (b := b) e) := by
  intro G
  refine ⟨bufferRule e.symm G,?_⟩
  cases G with
  | mk output hi update supported =>
    dsimp only [bufferRule]
    congr 1
    · funext m x
      change e '' (e.symm '' output (buffer e (buffer e.symm m)) (e (e.symm x))) = output m x
      rw [buffer_roundtrip,e.apply_symm_apply]
      ext y
      simp
    · funext m x
      change buffer e (buffer e.symm (update (buffer e (buffer e.symm m)) (e (e.symm x)))) = update m x
      rw [buffer_roundtrip,buffer_roundtrip,e.apply_symm_apply]

/-- Evaluate a native generator on a native family in the ranks of e. -/
def Uniform (e : α ≃ ℕ) (encode : M → N) (succeeds : Family ℕ k → N → Prop) : Prop :=
  ∀ L : Family α k, ∃ G : M, succeeds (L.map e) (encode G)

private theorem uniform_iff (e : α ≃ ℕ) (encode : M → N) (onto : Surjective encode)
    (succeeds : Family ℕ k → N → Prop) :
    Uniform e encode succeeds ↔ ∀ L, ∃ G, succeeds L G := by
  constructor
  · intro h L
    obtain ⟨A,rfl⟩ := Family.map_onto e L
    obtain ⟨g,hg⟩ := h A
    exact ⟨_,hg⟩
  · intro h L
    obtain ⟨g,hg⟩ := h (L.map e)
    obtain ⟨G,rfl⟩ := onto g
    exact ⟨G,hg⟩

def Memoryless (e : α ≃ ℕ) (k : ℕ) (σ : ℝ) : Prop :=
  Uniform (k := k) e (setRule e) fun L G =>
    (∀ x, (G x).Infinite) ∧ IsFinitelyRepeatingMemorylessGenerator G (range L.lang) ∧
    ∀ i s, Generic.Presents s (L.lang i) → FinitelyRepeating s →
      σ ≤ memorylessRunUpperDensity (OrderedLanguage.canonical (L.lang i) (L.infinite i)) G s

def Windows (e : α ≃ ℕ) (k W : ℕ) (σ : ℝ) : Prop :=
  Uniform (k := k) e (windowRule (W := W) e) fun L G =>
    (∀ i, IsRepetitionFreeWindowGeneratorOn G (L.lang i)) ∧ ∀ i s (hs : Injective s),
      Generic.Presents s (L.lang i) →
        σ ≤ windowRunUpperDensity (OrderedLanguage.canonical (L.lang i) (L.infinite i)) G s hs

def Buffers (e : α ≃ ℕ) (k b : ℕ) (σ : ℝ) : Prop :=
  Uniform (k := k) e (bufferRule (b := b) e) fun L G =>
    (∀ i, IsRepetitionFreeBufferGeneratorOn G (L.lang i)) ∧ ∀ i s, Injective s →
      Generic.Presents s (L.lang i) →
        σ ≤ bufferRunUpperDensity (OrderedLanguage.canonical (L.lang i) (L.infinite i)) G s

theorem memoryless_iff (e : α ≃ ℕ) (k : ℕ) (σ : ℝ) :
    Memoryless e k σ ↔ FixedMemorylessGuarantee k σ := by
  rw [Memoryless,uniform_iff _ _ (setRule_onto e)]
  exact ⟨fun h l hd hi => h ⟨l,hd,hi⟩,fun h L => h L.lang L.distinct L.infinite⟩

theorem windows_iff (e : α ≃ ℕ) (k W : ℕ) (σ : ℝ) :
    Windows e k W σ ↔ FixedWindowGuarantee k W σ := by
  rw [Windows,uniform_iff _ _ (windowRule_onto e)]
  exact ⟨fun h l hd hi => h ⟨l,hd,hi⟩,fun h L => h L.lang L.distinct L.infinite⟩

theorem buffers_iff (e : α ≃ ℕ) (k b : ℕ) (σ : ℝ) :
    Buffers e k b σ ↔ FixedBufferGuarantee k b σ := by
  rw [Buffers,uniform_iff _ _ (bufferRule_onto e)]
  exact ⟨fun h l hd hi => h ⟨l,hd,hi⟩,fun h L => h L.lang L.distinct L.infinite⟩

/-- One hard family on the original alphabet works for all its valid native
memoryless generators and all finitely repeating presentations. -/
theorem zero_lower_density (e : α ≃ ℕ) (k : ℕ) (hk : 3 ≤ k) :
    ∃ (L : Family α k) (i : Fin k), ∀ G : MemorylessSetGenerator α,
      IsFinitelyRepeatingMemorylessGenerator G (range L.lang) →
      ∀ s, Generic.Presents s (L.lang i) → FinitelyRepeating s →
        ∃ T, ∀ t ≥ T, (OrderedLanguage.canonical ((L.map e).lang i) ((L.map e).infinite i)).lowerDensity
          (e '' G (s t)) = 0 := by
  obtain ⟨langs,i,hd,hi,h⟩ := fixedOrder_zero_lowerDensity k hk
  obtain ⟨L,hL⟩ := Family.map_onto e (⟨langs,hd,hi⟩ : Family ℕ k)
  have he (j) : e '' L.lang j = langs j := congrArg (fun H : Family ℕ k => H.lang j) hL
  have presents {f : α ≃ ℕ} {s : ℕ → α} {K : Set α} (hp : Generic.Presents s K) :
      Generic.Presents (f ∘ s) (f '' K) := (Set.range_comp _ _).trans (congrArg _ hp)
  refine ⟨L,i,fun G hG s hs hr => ?_⟩
  have valid : IsFinitelyRepeatingMemorylessGenerator (setRule e G) (range langs) := by
    rintro _ ⟨j,rfl⟩ d hp hd
    have pyr : Generic.Presents (e.symm ∘ d) (L.lang j) := by
      change range (e.symm ∘ d) = _
      rw [Set.range_comp,hp,← he]; simp
    have repeatD : FinitelyRepeating (e.symm ∘ d) := by
      intro x
      simpa [Function.comp_def,Equiv.symm_apply_eq] using hd (e x)
    obtain ⟨T,hT⟩ := hG _ ⟨j,rfl⟩ _ pyr repeatD
    refine ⟨T,fun t ht => ?_⟩
    obtain ⟨inf,sub⟩ := hT t ht
    exact ⟨inf.image e.injective.injOn,(Set.image_mono sub).trans_eq (he j)⟩
  have re : FinitelyRepeating (e ∘ s) := by
    intro x
    simpa [Function.comp_def,Equiv.apply_eq_iff_eq_symm_apply] using hr (e.symm x)
  obtain ⟨T,hT⟩ := h (setRule e G) valid (e ∘ s) ((he i) ▸ presents hs) re
  refine ⟨T,fun t ht => ?_⟩
  have eqOrder : OrderedLanguage.canonical ((L.map e).lang i) ((L.map e).infinite i) =
      OrderedLanguage.canonical (langs i) (hi i) := by congr 1; exact he i
  rw [eqOrder]
  simpa [setRule,Function.comp_def] using hT t ht

end GenLimit.BoundedMemory.RankedUniverse
