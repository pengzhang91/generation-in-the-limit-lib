import GenLimit.Paper32_InfinitelyManyHallucinations.PodSchedule

/-! # The generators of Algorithms 2, 6 and 7
At a safe round the machine adds a fresh pod of the prescribed size and
emits the least available member of the accumulated pool. Exploration
leaves the pool and its safe-round clock unchanged.
-/
namespace GenLimit.InfinitelyManyHallucinations.Pods

open Set KleinbergWei.PartialEnumeration.Sharpness
open scoped Classical

structure Config where
  family : LanguageFamily
  explore : Set ℕ
  repeatObserved : Bool
  size : ℕ → ℕ
  scan : Equiv.Perm ℕ := Equiv.refl ℕ

/-- Size uses the zero-based safe-round index (source pod number u+1). -/
noncomputable def pod (L : Language) (used : Finset ℕ) (size : ℕ) : Finset ℕ :=
  (Finset.range size).image (Nat.nth (fun x => x ∈ L ∧ x ∉ used))

theorem pod_spec {L : Language} (hi : L.Infinite) (used : Finset ℕ) (size : ℕ) :
    (pod L used size).card = size ∧ ∀ x ∈ pod L used size, x ∈ L ∧ x ∉ used := by
  have inf : (setOf fun x => x ∈ L ∧ x ∉ used).Infinite := hi.diff used.finite_toSet
  constructor
  · rw [pod,Finset.card_image_of_injective _ (Nat.nth_strictMono inf).injective,Finset.card_range]
  · intro x hx
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx
    exact Nat.nth_mem_of_infinite inf u

noncomputable def Config.newPod (c : Config) (A : Exhaustion) (t : ℕ) (pool prev : Finset ℕ) :=
  let u := Nat.count (safe c.explore) t
  pod (proposalSet (chains c.family A c.explore) u) (pool ∪ (A.stage (t+1) ∪ prev)) (c.size u)

noncomputable def Config.nextPool (c : Config) (A : Exhaustion) (t : ℕ) (pool prev : Finset ℕ) :=
  if safe c.explore t then pool ∪ c.newPod A t pool prev else pool

private noncomputable def leastAvailable (available blocked : Finset ℕ) :=
  if h : available.Nonempty then available.min' h else firstMissing blocked

/-- Scan in the exploration enumeration, which may differ from the order
used for pods. Earlier enumeration entries can be skipped permanently
because the unavailable set grows throughout the run. -/
noncomputable def scanWord (e : Equiv.Perm ℕ) (used : Finset ℕ) : ℕ :=
  e (firstMissing (used.image e.symm))

theorem scan_fresh (e : Equiv.Perm ℕ) (used : Finset ℕ) : scanWord e used ∉ used := by
  intro h
  exact firstMissing_notMem _ (Finset.mem_image.mpr ⟨_,h,e.symm_apply_apply _⟩)

theorem scan_le (e : Equiv.Perm ℕ) (used : Finset ℕ) {x : ℕ} (hx : x ∉ used) :
    e.symm (scanWord e used) ≤ e.symm x := by
  rw [scanWord,e.symm_apply_apply]
  apply firstMissing_le
  intro h
  obtain ⟨y,hy,he⟩ := Finset.mem_image.mp h
  exact hx (e.symm.injective he ▸ hy)

noncomputable def Config.output (c : Config) (A : Exhaustion) (t : ℕ) (pool prev : Finset ℕ) :=
  let blocked := A.stage (t+1) ∪ prev
  if safe c.explore t then leastAvailable (c.nextPool A t pool prev \ blocked) blocked
  else scanWord c.scan (if c.repeatObserved then prev else blocked)

structure State where
  pool : Finset ℕ
  words : Finset ℕ

noncomputable def Config.run (c : Config) (A : Exhaustion) : ℕ → State
  | 0 => ⟨∅,∅⟩
  | t+1 =>
    let old := c.run A t
    ⟨c.nextPool A t old.pool old.words, insert (c.output A t old.pool old.words) old.words⟩

private theorem nextPool_congr {c : Config} {A B : Exhaustion} {t : ℕ}
    (hR : (setOf (safe c.explore)).Infinite) (hp : ∀ i ≤ t+1, A.stage i = B.stage i)
    (pool prev : Finset ℕ) : c.nextPool A t pool prev = c.nextPool B t pool prev := by
  by_cases ht : safe c.explore t
  · simp only [Config.nextPool,if_pos ht,Config.newPod,
      proposal_at_safe_time (C := c.family) hR ht hp,hp _ le_rfl]
  · simp only [Config.nextPool,if_neg ht]

private theorem output_congr {c : Config} {A B : Exhaustion} {t : ℕ}
    (hR : (setOf (safe c.explore)).Infinite) (hp : ∀ i ≤ t+1, A.stage i = B.stage i)
    (pool prev : Finset ℕ) : c.output A t pool prev = c.output B t pool prev := by
  simp only [Config.output,nextPool_congr hR hp,hp _ le_rfl]

private theorem run_congr {c : Config} {A B : Exhaustion} {t : ℕ}
    (hR : (setOf (safe c.explore)).Infinite) (hp : ∀ i ≤ t, A.stage i = B.stage i) :
    c.run A t = c.run B t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Config.run,ih (fun i hi => hp i (by omega)),nextPool_congr hR hp,output_congr hR hp]

noncomputable def Config.rule (c : Config) : WordRule :=
  fun A t prev => c.output A t (c.run A t).pool prev

theorem rule_causal (c : Config) (hR : (setOf (safe c.explore)).Infinite) : c.rule.Causal := by
  intro A B t hp prev
  simp only [Config.rule,run_congr hR (fun i (hi : i ≤ t) => hp i (by omega)),output_congr hR hp]

theorem output_safe_fresh (c : Config) (A : Exhaustion) {t : ℕ} (ht : safe c.explore t)
    (pool prev : Finset ℕ) : c.output A t pool prev ∉ A.stage (t+1) ∪ prev := by
  simp only [Config.output,if_pos ht,leastAvailable]
  split
  · rename_i h
    exact (Finset.mem_sdiff.mp (Finset.min'_mem _ h)).2
  · exact firstMissing_notMem _

theorem rule_fresh (c : Config) (A : Exhaustion) (t : ℕ) (prev : Finset ℕ) :
    c.rule A t prev ∉ prev := by
  by_cases ht : safe c.explore t
  · exact fun h => output_safe_fresh c A ht _ _ (Finset.mem_union_right _ h)
  · simp only [Config.rule,Config.output,if_neg ht]
    cases c.repeatObserved <;> simp only [Bool.false_eq_true,if_false,if_true]
    · exact fun h => scan_fresh _ _ (Finset.mem_union_right _ h)
    · exact scan_fresh _ _

theorem stage_run (c : Config) (hR : (setOf (safe c.explore)).Infinite) (A : Exhaustion) (n : ℕ) :
    (generatedExhaustion c.rule.generator A).stage n = (c.run A n).words := by
  let r := c.rule.rounds (rule_causal c hR) (rule_fresh c) A
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [r.step]
    change insert (c.output A n (c.run A n).pool ((generatedExhaustion c.rule.generator A).stage n)) _ = _
    rw [ih]
    rfl

theorem newPod_spec (c : Config) (hi : ∀ i, (c.family i).Infinite)
    (A : Exhaustion) (t : ℕ) (pool prev : Finset ℕ) :
    let u := Nat.count (safe c.explore) t
    (c.newPod A t pool prev).card = c.size u ∧
    ∀ x ∈ c.newPod A t pool prev, x ∈ proposalSet (chains c.family A c.explore) u ∧
        x ∉ pool ∪ (A.stage (t+1) ∪ prev) :=
  pod_spec (proposal_infinite _ (fun _ => descending ..) (fun _ => first_infinite _ hi _) _) _ _

/-- On a legal family with positive pod sizes, the least-pool instruction
always has a candidate. -/
theorem output_safe_mem (c : Config) (hi : ∀ i, (c.family i).Infinite)
    (size_pos : ∀ u, 0 < c.size u) (A : Exhaustion) (t : ℕ) (ht : safe c.explore t)
    (pool prev : Finset ℕ) : c.output A t pool prev ∈ c.nextPool A t pool prev := by
  obtain ⟨card,mem⟩ := newPod_spec c hi A t pool prev
  have hn : (c.newPod A t pool prev).Nonempty := Finset.card_pos.mp (card ▸ size_pos _)
  obtain ⟨x,hx⟩ := hn
  have avail : (c.nextPool A t pool prev \ (A.stage (t+1) ∪ prev)).Nonempty := by
    refine ⟨x,Finset.mem_sdiff.mpr ⟨?_,fun h => (mem x hx).2 (Finset.mem_union_right _ h)⟩⟩
    simpa only [Config.nextPool,if_pos ht] using
      (Finset.mem_union_right pool hx)
  simp only [Config.output, if_pos ht, leastAvailable,dif_pos avail]
  exact (Finset.mem_sdiff.mp (Finset.min'_mem _ avail)).1

/-- After finitely many rounds, all actual safe outputs belong to the target.
An old invalid pod member may still be emitted later, but global freshness
limits all such emissions to the finite earlier pool. -/
theorem eventual_safe_outputs (c : Config) (hR : (setOf (safe c.explore)).Infinite)
    (hi : ∀ i, (c.family i).Infinite) (size_pos : ∀ u, 0 < c.size u)
    (A : Exhaustion) {z : ℕ} (hin : A.limit.Infinite) (hsub : A.limit ⊆ c.family z) :
    let g := generatedExhaustion c.rule.generator A
    ∃ T, ∀ t ≥ T, safe c.explore t → c.rule A t (g.stage t) ∈ c.family z := by
  let g := generatedExhaustion c.rule.generator A
  let r := c.rule.rounds (rule_causal c hR) (rule_fresh c) A
  obtain ⟨N,hN⟩ := sets_eventually_valid (R := c.explore) hR hin hsub
  let B := Nat.nth (safe c.explore) N
  have clock (t : ℕ) (ht : B ≤ t) : N ≤ Nat.count (safe c.explore) t := by
    have := Nat.count_monotone (safe c.explore) ht
    simpa only [B,Nat.count_nth_of_infinite hR] using this
  let early := (c.run A B).pool
  have pools (t : ℕ) (ht : B ≤ t) : ∀ x ∈ (c.run A t).pool, x ∈ early ∨ x ∈ c.family z := by
    induction t, ht using Nat.le_induction with
    | base => exact fun _ hx => Or.inl hx
    | succ t ht ih =>
      intro x hx
      change x ∈ c.nextPool A t _ _ at hx
      unfold Config.nextPool at hx
      split at hx
      · rcases Finset.mem_union.mp hx with ho|hp
        · exact ih x ho
        · exact Or.inr (hN _ (clock t ht) ((newPod_spec c hi A t _ _).2 x hp).1)
      · exact ih x hx
  have finite := early.finite_toSet.preimage r.injective.injOn
  obtain ⟨M,hM⟩ := finite.bddAbove
  refine ⟨max B (M+1),fun t ht hsafe => ?_⟩
  have mem := output_safe_mem c hi size_pos A t hsafe (c.run A t).pool (c.run A t).words
  have word : r.word t = c.output A t (c.run A t).pool (c.run A t).words := by
    change c.output A t _ (g.stage t) = _
    rw [stage_run c hR]
  have hm : r.word t ∈ (c.run A (t+1)).pool := word ▸ mem
  rcases pools (t+1) (by omega) _ hm with h|h
  · have := hM (show t ∈ r.word ⁻¹' (early : Set ℕ) from h)
    omega
  · exact h

end GenLimit.InfinitelyManyHallucinations.Pods
