import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.PrefixRealizability
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.WithoutAdversaryInput
import GenLimit.Support.HistoryChainText
import GenLimit.Support.StreamPrefixText
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.List.Nodup

/-! # Appendix A.2 and Remark A.3, the concrete column construction

Column zero encodes the special column called -1 in the paper. At phase n
the adversary inserts (0,n) and then presents the whole fresh column n+1.
After forcing a correct prediction it retains the finite prefix before that
prediction, and never returns to the column. The resulting limit has every
special marker and a finite fiber in each ordinary column.
-/
namespace GenLimit.UnionClosedness.ColumnSwitching

open Generic PrefixRealizability

abbrev Point := ℕ × ℕ
def fiber (L : Set Point) (i : ℕ) : Set ℕ := {k | (i,k) ∈ L}

def columnClass (n : ℕ) : LanguageClass Point :=
  {L | (∀ i ≤ n, (fiber L i).Finite) ∧ fiber L (n+1) = Set.univ ∧
    ∀ i > n+1, fiber L i = ∅}

def limitClass : LanguageClass Point :=
  {L | (fiber L 0)ᶜ.Finite ∧ ∀ n, (fiber L (n+1)).Finite}

def unionClass : LanguageClass Point := limitClass ∪ ⋃ n, columnClass n

theorem column_generatable (n : ℕ) : UniformlyGeneratableWithoutAdversaryInput (columnClass n) := by
  refine ⟨fun k ↦ (n+1,k),0,fun _ _ h ↦ congrArg Prod.snd h,?_⟩
  intro L hL t _
  exact (Set.eq_univ_iff_forall.mp hL.2.1 t)

theorem limit_generatable : NonuniformlyGeneratableWithoutAdversaryInput limitClass := by
  refine ⟨fun k ↦ (0,k),fun _ _ h ↦ congrArg Prod.snd h,?_⟩
  intro L hL
  obtain ⟨b,hb⟩ := Set.Finite.bddAbove (s := (fiber L 0)ᶜ) hL.1
  refine ⟨b+1,fun t ht ↦ ?_⟩
  by_contra hn
  have := hb (show t ∈ (fiber L 0)ᶜ from hn)
  omega

private def marked (xs : List Point) (n : ℕ) := xs ++ [(0,n)]
private def block (n j : ℕ) := textPrefix (fun k ↦ (n+1,k)) j
private def extend (n : ℕ) (xs : List Point) (j : ℕ) := marked xs n ++ block n j
private def admissible (n : ℕ) (xs : List Point) : Prop :=
  xs.Nodup ∧ ∀ x ∈ xs, x.1 ≤ n ∧ (x.1 = 0 → x.2 < n)

private theorem mem_block {n j : ℕ} {x : Point} :
    x ∈ block n j ↔ x.1 = n+1 ∧ x.2 < j := by
  rcases x with ⟨a,b⟩
  simp [block,mem_textPrefix_iff,Prod.ext_iff,eq_comm,and_comm]

private theorem marked_bounds {n xs} (h : admissible n xs) :
    (marked xs n).Nodup ∧ ∀ x ∈ marked xs n, x.1 ≤ n ∧ (x.1 = 0 → x.2 ≤ n) := by
  have hf : (0,n) ∉ xs := fun hx ↦ (Nat.lt_irrefl n) ((h.2 _ hx).2 rfl)
  refine ⟨by unfold marked; rw [List.nodup_append_comm]; simpa using And.intro hf h.1,?_⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact ⟨(h.2 x hx).1,fun he ↦ ((h.2 x hx).2 he).le⟩
  · obtain rfl := List.mem_singleton.mp hx
    exact ⟨Nat.zero_le _,fun _ ↦ le_rfl⟩

private theorem extend_admissible {n xs} (h : admissible n xs) (j : ℕ) :
    admissible (n+1) (extend n xs j) := by
  obtain ⟨hn,hb⟩ := marked_bounds h
  have hblock : (block n j).Nodup := streamPrefix_nodup (fun _ _ he ↦ congrArg Prod.snd he) j
  constructor
  · apply List.nodup_append'.mpr
    refine ⟨hn,hblock,?_⟩
    intro x hxm hxb
    have := (hb _ hxm).1
    have := (mem_block.mp hxb).1
    omega
  · intro x hx
    rcases List.mem_append.mp hx with hm | ho
    · exact ⟨(hb _ hm).1.trans (Nat.le_succ n), fun he ↦ Nat.lt_succ_of_le ((hb _ hm).2 he)⟩
    · have he := (mem_block.mp ho).1
      exact ⟨he.le,by omega⟩

private def simulation (n : ℕ) (xs : List Point) : ℕ → Point :=
  Support.prependStream (marked xs n) (fun k ↦ (n+1,k))

private theorem sim_prefix (n : ℕ) (xs : List Point) (j : ℕ) :
    textPrefix (simulation n xs) ((marked xs n).length+j) = extend n xs j :=
  Support.textPrefix_prependStream ..

private theorem injective_of_nodup_prefix {s : ℕ → Point}
    (h : ∀ i j, ∃ t, i < t ∧ j < t ∧ (textPrefix s t).Nodup) : Function.Injective s := by
  intro i j he
  obtain ⟨t,hi,hj,hn⟩ := h i j
  rw [textPrefix_eq_ofFn] at hn
  exact congrArg Fin.val ((List.nodup_ofFn.mp hn) (a₁ := ⟨i,hi⟩) (a₂ := ⟨j,hj⟩) he)

private theorem simulation_injective {n xs} (h : admissible n xs) : Function.Injective (simulation n xs) := by
  apply injective_of_nodup_prefix
  intro i j
  let u := max i j + 1
  refine ⟨(marked xs n).length+u,by dsimp [u]; omega,by dsimp [u]; omega,?_⟩
  rw [sim_prefix]
  exact (extend_admissible h u).1

private theorem simulation_mem {n xs} (h : admissible n xs) :
    Set.range (simulation n xs) ∈ columnClass n := by
  let M := marked xs n
  have hr : Set.range (simulation n xs) = (M.toFinset : Set Point) ∪ Set.range (fun k : ℕ ↦ (n+1,k)) :=
    Support.range_prependStream ..
  have hsmall (i) (hi : i ≤ n) : fiber (Set.range (simulation n xs)) i ⊆ Prod.snd '' (M.toFinset : Set Point) := by
    intro k hk
    change (i,k) ∈ Set.range (simulation n xs) at hk
    rw [hr] at hk
    rcases hk with hm | ⟨j,hj⟩
    · exact ⟨_,hm,rfl⟩
    · have := congrArg Prod.fst hj
      simp at this
      omega
  refine ⟨fun i hi ↦ (M.toFinset.finite_toSet.image _).subset (hsmall i hi),
    Set.eq_univ_iff_forall.mpr (fun k ↦ ?_), fun i hi ↦ Set.eq_empty_iff_forall_notMem.mpr (fun k hk ↦ ?_)⟩
  · change (n+1,k) ∈ Set.range (simulation n xs)
    rw [hr]
    exact Or.inr ⟨k,rfl⟩
  · change (i,k) ∈ Set.range (simulation n xs) at hk
    rw [hr] at hk
    rcases hk with hm | ⟨j,hj⟩
    · have := ((marked_bounds h).2 (i,k) (List.mem_toFinset.mp hm)).1
      dsimp at this
      omega
    · have := congrArg Prod.fst hj
      simp at this
      omega

/-- A prediction made after this prefix will never enter the ultimate
target when the adversary abandons the current column at this cutoff. -/
private def misses (G : Generator Point) (n : ℕ) (xs : List Point) (j : ℕ) : Prop :=
  let x := outputOnHistory G (extend n xs j)
  x.1 = n+1 ∧ j ≤ x.2

private theorem exists_cut {G : Generator Point} (hg : IsLimitGeneratorOnInjectivePresentations G unionClass)
    {n xs} (h : admissible n xs) : ∃ j, misses G n xs j := by
  let s := simulation n xs
  obtain ⟨T,hT⟩ := hg (Set.range s) (Or.inr (Set.mem_iUnion.mpr ⟨n,simulation_mem h⟩))
    s (simulation_injective h) rfl
  let t := (marked xs n).length + T
  have hc := hT t (Nat.le_add_left ..)
  have hout : outputOnHistory G (extend n xs T) = output G s t := by
    rw [← sim_prefix,outputOnHistory_streamPrefix]
  let x := output G s t
  have hf : x ∉ extend n xs T := by
    rw [← sim_prefix]
    intro hx
    exact hc.2 (Generic.mem_sample_iff.mpr (mem_textPrefix_iff.mp hx))
  have hm := hc.1
  rw [show Set.range s = _ from Support.range_prependStream (marked xs n) (fun k ↦ (n+1,k))] at hm
  refine ⟨T,?_⟩
  change (outputOnHistory G (extend n xs T)).1 = n+1 ∧ T ≤ (outputOnHistory G (extend n xs T)).2
  rw [hout]
  rcases hm with hm | ⟨k,hk⟩
  · exact (hf (List.mem_append_left _ (List.mem_toFinset.mp hm))).elim
  · have he : x.1 = n+1 := (congrArg Prod.fst hk).symm
    exact ⟨he, le_of_not_gt fun hlt ↦ hf (List.mem_append_right _ (mem_block.mpr ⟨he,hlt⟩))⟩

/-- Remark A.3. Each simulated phase has a legal injective completion in
column n+1, alternating between the odd and even indexed components.
The infinite switch sequence itself presents a member of the limit class. -/
theorem remark_A_3 : ¬ GeneratableInLimitOnInjectivePresentations unionClass := by
  classical
  rintro ⟨G,hG⟩
  let H (n : ℕ) := {xs : List Point // admissible n xs}
  let cut (n : ℕ) (xs : H n) := (exists_cut hG xs.property).choose
  let a : (n : ℕ) → H n := Nat.rec ⟨[],by simp [admissible]⟩
    (fun n xs ↦ ⟨extend n xs.val (cut n xs),extend_admissible xs.property _⟩)
  let c (n : ℕ) := cut n (a n)
  have hs (n : ℕ) : (a (n+1)).val = marked (a n).val n ++ block n (c n) := rfl
  have hlen (n : ℕ) : n ≤ (a n).val.length := by
    induction n with
    | zero => omega
    | succ n ih => rw [hs]; simp [marked]; omega
  let chain : Support.HistoryChain Point :=
    ⟨⟨fun n ↦ (a n).val,fun n ↦ (List.prefix_append ..).trans (List.prefix_append ..)⟩,hlen⟩
  let s := chain.stream
  have in_history {x : Point} : x ∈ Set.range s ↔ ∃ n, x ∈ (a n).val := by
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i+1,List.get_mem _ _⟩
    · rintro ⟨n,hn⟩
      exact chain.history_toFinset_subset_stream_range n (List.mem_toFinset.mpr hn)
  have hinj : Function.Injective s := by
    apply injective_of_nodup_prefix
    intro i j
    let n := max i j + 1
    refine ⟨(a n).val.length,by have := hlen n; dsimp [n] at *; omega,
      by have := hlen n; dsimp [n] at *; omega,?_⟩
    rw [show textPrefix s (a n).val.length = (a n).val from chain.textPrefix_stream n]
    exact (a n).property.1
  have hcol (n k m : ℕ) (hm : (n+1,k) ∈ (a m).val) : k < c n := by
    induction m with
    | zero => exact False.elim (List.not_mem_nil hm)
    | succ m ih =>
      rw [hs] at hm
      rcases List.mem_append.mp hm with hmark | hnew
      · rcases List.mem_append.mp hmark with hold | hmarker
        · exact ih hold
        · simp at hmarker
      · obtain ⟨he,hk⟩ := mem_block.mp hnew
        change n+1 = m+1 at he
        simpa [Nat.succ.inj he] using hk
  have hk : Set.range s ∈ limitClass := by
    constructor
    · have hfull : fiber (Set.range s) 0 = Set.univ := by
        apply Set.eq_univ_iff_forall.mpr
        intro k
        apply in_history.mpr
        exact ⟨k+1,by rw [hs]; simp [marked]⟩
      rw [hfull,Set.compl_univ]
      exact Set.finite_empty
    · intro n
      apply (Finset.range (c n)).finite_toSet.subset
      intro k hk
      obtain ⟨m,hm⟩ := in_history.mp hk
      exact Finset.mem_range.mpr (hcol n k m hm)
  obtain ⟨T,hT⟩ := hG _ (Or.inl hk) s hinj rfl
  let t := (a (T+1)).val.length
  have hout : outputOnHistory G (a (T+1)).val = output G s t := by
    rw [← outputOnHistory_streamPrefix, show streamPrefix s t = (a (T+1)).val from
      chain.textPrefix_stream (T+1)]
  have hm := (exists_cut hG (a T).property).choose_spec
  change (outputOnHistory G (a (T+1)).val).1 = T+1 ∧
    c T ≤ (outputOnHistory G (a (T+1)).val).2 at hm
  rw [hout] at hm
  have hc := (hT t ((Nat.le_succ _).trans (hlen _))).1
  obtain ⟨m,hmemb⟩ := in_history.mp hc
  have hp : (T+1,(output G s t).2) ∈ (a m).val := by simpa [← hm.1] using hmemb
  exact (Nat.not_lt_of_ge hm.2) (hcol T _ m hp)

end GenLimit.UnionClosedness.ColumnSwitching
