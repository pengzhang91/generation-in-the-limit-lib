import GenLimit.Paper32_InfinitelyManyHallucinations.Exploration
import GenLimit.Paper32_InfinitelyManyHallucinations.SingleStepInput
import GenLimit.Paper15_PartialEnumeration.SharpDensity

/-! # The batched adversary for P32

Group k successive moves of the least-unused-word adversary into a batch.
Only the last move of each group records a new generator output. On the
other moves the simulated output repeats the most recent adversarial word,
which leaves the used set unchanged. -/

namespace GenLimit.InfinitelyManyHallucinations.BatchedRace

open Set Filter KleinbergWei.PartialEnumeration.Sharpness
open scoped Classical Topology

def blocks (k : ℕ) (s : ℕ → ℕ) : Exhaustion where
  stage n := sample s (n*k)
  stage_zero := by simp [sample]
  monotone_stage := fun _ _ h => Finset.image_subset_image (Finset.range_mono (Nat.mul_le_mul_right _ h))

theorem block_mem {k : ℕ} {s : ℕ → ℕ} {n x : ℕ} :
    x ∈ (blocks k s).stage n ↔ ∃ i < n*k, s i = x := by
  simp [blocks,sample]

theorem block_limit {k : ℕ} (hk : 0 < k) (s : ℕ → ℕ) :
    (blocks k s).limit = Set.range s := by
  ext x
  constructor
  · rintro ⟨n,hn⟩
    obtain ⟨i,_,hi⟩ := block_mem.mp hn
    exact ⟨i,hi⟩
  · rintro ⟨i,rfl⟩
    exact ⟨i+1, block_mem.mpr ⟨i, (Nat.lt_succ_self i).trans_le
      (Nat.le_mul_of_pos_right _ hk),rfl⟩⟩

theorem block_bound (k : ℕ) (s : ℕ → ℕ) : (blocks k s).BoundedBy (fun _ => k) := by
  intro n
  have sub : (blocks k s).increment (n+1) ⊆ (Finset.Ico (n*k) ((n+1)*k)).image s := by
    intro x hx
    obtain ⟨hm,hn⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨i,hi,rfl⟩ := block_mem.mp hm
    exact Finset.mem_image.mpr ⟨i,Finset.mem_Ico.mpr ⟨le_of_not_gt
      (fun h => hn (block_mem.mpr ⟨i,h,rfl⟩)),hi⟩,rfl⟩
  exact (Finset.card_le_card sub).trans (Finset.card_image_le.trans (by simp [Nat.succ_mul]))

private theorem generated_prefix (G : BatchGenerator) {A B : Exhaustion} {n : ℕ}
    (h : ∀ i ≤ n, A.stage i = B.stage i) : generatedStages G A n = generatedStages G B n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hist : (fun i : Fin (n+1+1) => A.stage i) = (fun i : Fin (n+1+1) => B.stage i) :=
      funext fun i => h i (Nat.le_of_lt_succ i.isLt)
    simp only [generatedStages, hist, ih (fun i hi => h i (by omega))]

theorem increment_prefix (G : BatchGenerator) {A B : Exhaustion} {n : ℕ}
    (h : ∀ i ≤ n, A.stage i = B.stage i) :
    (generatedExhaustion G A).increment n = (generatedExhaustion G B).increment n := by
  cases n with
  | zero => rfl
  | succ n =>
    change (generatedStages _ _ _ \ generatedStages _ _ _) = _
    rw [generated_prefix G h,generated_prefix G (fun i (hi : i ≤ n) => h i (by omega))]
    rfl

private def padded (h : List ℕ) (i : ℕ) : ℕ := h[i]?.getD 0

private theorem padded_prefix (s : ℕ → ℕ) {n i : ℕ} (hi : i < n) :
    padded (textPrefix s n) i = s i := by simp [padded,textPrefix,hi]

private theorem block_prefix (s : ℕ → ℕ) {k n b : ℕ} (h : b*k ≤ n) :
    (blocks k (padded (textPrefix s n))).stage b = (blocks k s).stage b := by
  apply Finset.image_congr
  intro i hi
  exact padded_prefix s ((Finset.mem_range.mp hi).trans_le h)

noncomputable def action (k : ℕ) (G : BatchGenerator) (h : List ℕ) : ℕ :=
  let t := h.length
  let s := padded h
  if k ∣ t then
    Exhaustion.chooseWord ((generatedExhaustion G (blocks k s)).increment (t/k)) (s (t-1))
  else s (t-1)

noncomputable def adversary (k : ℕ) (G : BatchGenerator) :=
  blocks k (stream (action k G))

private theorem output_eq (k : ℕ) (G : BatchGenerator) (t : ℕ) :
    let a := action k G
    let g := generatedExhaustion G (adversary k G)
    output a t = if k ∣ t+1 then Exhaustion.chooseWord (g.increment ((t+1)/k)) (stream a t)
      else stream a t := by
  let a := action k G
  have h := history_eq a (t+1)
  change action k G ((run a (t+1)).history) = _
  rw [h]
  simp only [action, textPrefix_length, Nat.add_sub_cancel, padded_prefix _ (Nat.lt_succ_self t)]
  split
  · rw [increment_prefix G (fun i (hi : i ≤ (t+1)/k) => block_prefix (stream a)
      ((Nat.mul_le_mul_right k hi).trans (Nat.div_mul_le_self ..)))]
    rfl
  · rfl

private theorem block_end {k : ℕ} (hk : 0 < k) (b : ℕ) :
    (b+1)*k-1+1 = (b+1)*k := Nat.sub_add_cancel (Nat.mul_pos (by omega) hk)

private theorem end_output {k : ℕ} (hk : 0 < k) (G : BatchGenerator)
    (hstep : (generatedExhaustion G (adversary k G)).IsSingleStep) (b x : ℕ)
    (hx : x ∈ (generatedExhaustion G (adversary k G)).increment (b+1)) :
    output (action k G) ((b+1)*k-1) = x := by
  rw [output_eq,block_end hk, if_pos (dvd_mul_left ..),Nat.mul_div_cancel _ hk]
  exact Finset.card_le_one.mp (hstep b) _ (Exhaustion.chooseWord_mem ⟨x,hx⟩ _) _ hx

private theorem virtual_past {k : ℕ} (hk : 0 < k) (G : BatchGenerator)
    {u b : ℕ} (hu : u+1 < (b+1)*k) :
    output (action k G) u = stream (action k G) u ∨
      output (action k G) u ∈ (generatedExhaustion G (adversary k G)).stage b := by
  rw [output_eq]
  split
  · rename_i hd
    let g := generatedExhaustion G (adversary k G)
    by_cases he : (g.increment ((u+1)/k)).Nonempty
    · right
      apply g.monotone_stage (show (u+1)/k ≤ b by
        have := Nat.div_lt_iff_lt_mul hk |>.mpr hu
        omega)
      exact g.increment_subset_stage _ (Exhaustion.chooseWord_mem he _)
    · left
      simp only [← show g = generatedExhaustion G (adversary k G) from rfl, Exhaustion.chooseWord, dif_neg he]
  · exact Or.inl rfl

private theorem new_word_unused {k : ℕ} (hk : 0 < k) (G : BatchGenerator)
    (hn : Novel (adversary k G) (generatedExhaustion G (adversary k G))) {b x u : ℕ}
    (hx : x ∈ (generatedExhaustion G (adversary k G)).increment (b+1))
    (hu : u < (b+1)*k) : x ∉ (run (action k G) u).used := by
  let a := action k G
  let A := adversary k G
  let g := generatedExhaustion G A
  have ha : x ∉ A.stage (b+1) := Finset.disjoint_left.mp (hn _) hx
  have hg : x ∉ g.stage b := (Finset.mem_sdiff.mp hx).2
  have before (i) (hi : i < u) : stream a i ≠ x :=
    fun h => ha (block_mem.mpr ⟨i,hi.trans hu,h⟩)
  intro h
  rcases Finset.mem_union.mp h with hist | out
  · rw [history_eq,List.mem_toFinset,mem_textPrefix_iff] at hist
    obtain ⟨i,hi,he⟩ := hist
    exact before i hi he
  · obtain ⟨i,hi,he⟩ := (output_mem ..).mp out
    rcases virtual_past hk G (show i+1 < (b+1)*k by omega) with eqn | mem
    · exact before i hi (eqn.symm.trans he)
    · exact hg (he ▸ mem)

private theorem ordinary_excluded {k : ℕ} (hk : 0 < k) (G : BatchGenerator)
    (hn : Novel (adversary k G) (generatedExhaustion G (adversary k G)))
    (hs : (generatedExhaustion G (adversary k G)).IsSingleStep)
    {b u : ℕ} (hlo : b*k ≤ u) (hhi : u < (b+1)*k)
    (hord : ¬(run (action k G) u).special) {d x : ℕ}
    (hx : x ∈ (generatedExhaustion G (adversary k G)).increment (d+1)) :
    stream (action k G) u ≠ x := by
  let a := action k G
  intro eqn
  by_cases hb : b ≤ d
  · apply Finset.disjoint_left.mp (hn _) hx
    exact block_mem.mpr ⟨u, hhi.trans_le (Nat.mul_le_mul_right _ (by omega : b+1 ≤ d+1)), eqn⟩
  · have prev : (d+1)*k-1 < u := by
      have hpos : 0 < (d+1)*k := Nat.mul_pos (Nat.succ_pos d) hk
      have hle := Nat.mul_le_mul_right k (show d+1 ≤ b by omega)
      omega
    have mem := (output_mem a u x).mpr ⟨_,prev,end_output hk G hs d x hx⟩
    have played : stream a u = firstMissing (run a u).used := if_neg hord
    exact firstMissing_notMem _ ((played.symm.trans eqn).symm ▸
      Finset.mem_union_right (run a u).history.toFinset mem)

private theorem first_increment (g : Exhaustion) {x : ℕ} (hx : x ∈ g.limit) :
    ∃ b, x ∈ g.increment (b+1) := by
  obtain ⟨n,hn⟩ := hx
  induction n with
  | zero => simp [g.stage_zero] at hn
  | succ n ih =>
    by_cases old : x ∈ g.stage n
    · exact ih old
    · exact ⟨n, Finset.mem_sdiff.mpr ⟨hn,old⟩⟩

/-- Each of the k microturns preceding a first output is charged to its
distinct ordinary blocker, or to its unique sparse catch-up index. -/
theorem prefix_bound_batched (k : ℕ) (hk : 0 < k) (G : BatchGenerator)
    (hn : Novel (adversary k G) (generatedExhaustion G (adversary k G)))
    (hs : (generatedExhaustion G (adversary k G)).IsSingleStep) (n : ℕ) :
    (k+1)*natural.prefixCount (generatedExhaustion G (adversary k G)).limit n ≤ n+n.sqrt+1 := by
  classical
  let a := action k G
  let g := generatedExhaustion G (adversary k G)
  let S := (Finset.range n).filter fun x => x ∈ g.limit
  let V := (Finset.range n) \ S
  let when_ (x : ℕ) := if hx : x ∈ g.limit then (first_increment g hx).choose else 0
  have added {x : ℕ} (hx : x ∈ S) : x ∈ g.increment (when_ x + 1) := by
    have hg := (Finset.mem_filter.mp hx).2
    simpa only [when_,dif_pos hg] using (first_increment g hg).choose_spec
  let micro (p : ℕ × ℕ) := when_ p.1*k+p.2
  let slots := S ×ˢ Finset.range k
  have bounds {p : ℕ × ℕ} (h : p ∈ slots) :
      when_ p.1*k ≤ micro p ∧ micro p < (when_ p.1+1)*k := by
    have hj := Finset.mem_range.mp (Finset.mem_product.mp h).2
    simp only [micro,Nat.add_mul,one_mul]
    omega
  have micro_inj : Set.InjOn micro (↑slots : Set (ℕ × ℕ)) := by
    rintro ⟨x,j⟩ hx ⟨y,l⟩ hy he
    obtain ⟨hx,hj⟩ := Finset.mem_product.mp hx
    obtain ⟨hy,hl⟩ := Finset.mem_product.mp hy
    have hj' := Finset.mem_range.mp hj
    have hl' := Finset.mem_range.mp hl
    change when_ x*k+j = when_ y*k+l at he
    have htime : when_ x = when_ y := by
      rw [Nat.mul_comm (when_ x) k, Nat.mul_comm (when_ y) k] at he
      have := congrArg (fun n => n/k) he
      simpa [Nat.mul_add_div hk, Nat.div_eq_of_lt hj', Nat.div_eq_of_lt hl'] using this
    have hxy : x = y := Finset.card_le_one.mp (hs _) _ (added hx) _
      (htime.symm ▸ added hy)
    subst y
    exact Prod.ext rfl (Nat.add_left_cancel he)
  let charge (p : ℕ × ℕ) : ℕ ⊕ ℕ := if (run a (micro p)).special then
    .inl (run a (micro p)).catchups else .inr (stream a (micro p))
  have lands {p : ℕ × ℕ} (hp : p ∈ slots) :
      charge p ∈ (Finset.range (n.sqrt+1)).disjSum V := by
    obtain ⟨hlo,hhi⟩ := bounds hp
    have hx := (Finset.mem_product.mp hp).1
    have hsmall := (firstMissing_le (new_word_unused hk G hn (added hx) hhi)).trans_lt
      (Finset.mem_range.mp (Finset.mem_filter.mp hx).1)
    by_cases h : (run a (micro p)).special
    · have bound : (run a (micro p)).catchups ≤ n.sqrt := Nat.le_sqrt.mpr (h.trans hsmall.le)
      simpa [charge,h] using Nat.lt_succ_of_le bound
    · have ord : stream a (micro p) = (run a (micro p)).frontier := if_neg h
      have outside : stream a (micro p) ∉ S := by
        intro hm
        exact ordinary_excluded hk G hn hs hlo hhi h (added hm) rfl
      have hV : stream a (micro p) ∈ V :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (ord ▸ hsmall),outside⟩
      simpa [charge,h] using hV
  have inject : Set.InjOn charge (↑slots : Set (ℕ × ℕ)) := by
    intro p hp q hq he
    apply micro_inj hp hq
    by_cases h : (run a (micro p)).special <;> by_cases h' : (run a (micro q)).special <;>
      simp [charge,h,h'] at he
    · exact special_counts_injective a h h' he
    · exact stream_injective a he
  have hcount := Finset.card_le_card_of_injOn charge (fun _ h => lands h) inject
  have hdecomp := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun x => x ∈ g.limit) (Finset.range n))
  change V.card + S.card = (Finset.range n).card at hdecomp
  simp only [Finset.card_range] at hdecomp
  simp only [slots,Finset.card_product,Finset.card_disjSum,Finset.card_range] at hcount
  change (k+1)*S.card ≤ _
  rw [Nat.add_mul,one_mul,Nat.mul_comm k]
  omega

/-- Full adversarial presentation achieving the sharp batched upper bound
in the natural target order. The adversary is fixed for G before testing
G's novelty and its single-step output restriction on the resulting run. -/
theorem batched_full_upper (k : ℕ) (hk : 0 < k) (G : BatchGenerator) :
    ∃ A : Exhaustion, A.BoundedBy (fun _ => k) ∧ A.limit = Set.univ ∧
      (GeneratorNovel G A → (generatedExhaustion G A).IsSingleStep →
        natural.upperDensity (generatedExhaustion G A).limit ≤ 1/(k+1 : ℕ)) := by
  let A := adversary k G
  refine ⟨A, block_bound k _, (block_limit hk _).trans (presents _), ?_⟩
  intro hnov hsingle
  let g := generatedExhaustion G A
  have bound := prefix_bound_batched k hk G hnov.traceNovel hsingle
  have lim : Tendsto (fun n : ℕ => (1 + (n.sqrt : ℝ)/n + 1/n) / (k+1 : ℕ)) atTop
      (𝓝 (1/(k+1 : ℕ))) := by
    have h1 := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add
      GenLimit.InfinitelyManyHallucinations.tendsto_natSqrt_div_self_zero |>.add h1).div_const (k+1 : ℕ)
  change limsup (natural.prefixRatio g.limit) atTop ≤ _
  rw [← lim.limsup_eq]
  apply limsup_le_limsup
  · filter_upwards [eventually_gt_atTop 0] with n hn
    rw [KleinbergWei.OrderedLanguage.prefixRatio,if_neg hn.ne']
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    have hk' : 0 < ((k+1 : ℕ) : ℝ) := by positivity
    rw [le_div_iff₀ hk']
    field_simp [hn'.ne']
    have hc : ((k+1 : ℕ) : ℝ) * (natural.prefixCount g.limit n : ℝ) ≤
        n + (n.sqrt : ℝ) + 1 := by exact_mod_cast bound n
    push_cast at hc ⊢
    nlinarith only [hc]
  · exact isCoboundedUnder_le_of_le atTop fun n => natural.prefixRatio_nonneg g.limit n
  · exact lim.isBoundedUnder_le

end GenLimit.InfinitelyManyHallucinations.BatchedRace
