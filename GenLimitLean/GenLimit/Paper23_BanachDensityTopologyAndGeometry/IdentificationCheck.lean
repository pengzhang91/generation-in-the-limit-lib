import GenLimit.Bridges.Paper00ToPaper01
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.AdversarialPrefixes
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.Topology
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FixedShapeDensity
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.ChainGeneration

/-! Corollary 5.7 uses the word “identifies”. Under the usual exact
identification interpretation, its finite-rank hypothesis is insufficient.
The same co-singleton class from P00/P01 works even on injective texts. -/
namespace GenLimit.KleinbergWei.Banach.IdentificationCheck
open Set GoldKMSeparation TowerTopology Adversary

private theorem first_derivative {K : Point coSingletonClass}
    (mem : K ∈ TowerTopology.cbDerivative coSingletonClass 1) : K.val = univ := by
  obtain ⟨i,hi⟩ := K.property
  cases i with
  | zero => exact hi.symm
  | succ n =>
    obtain ⟨L,_,ne,_,sub⟩ := mem.2 ∅ (by simp)
    obtain ⟨j,hj⟩ := L.property
    rw [←hi,←hj] at sub
    cases j with
    | zero =>
      exact (sub (show n ∈ coSingletonLanguage 0 from trivial) (by rfl)).elim
    | succ m =>
      have eq : n = m := by
        by_contra neq
        exact sub (show n ∈ coSingletonLanguage (m+1) from neq) rfl
      subst m
      exact (ne (Subtype.ext (hj.symm.trans hi))).elim

theorem rank_two : FiniteRankAtMost coSingletonClass 2 := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro K mem
  obtain ⟨L,old,ne,_⟩ := mem.2 ∅ (by simp)
  exact ne (Subtype.ext ((first_derivative old).trans (first_derivative mem.1).symm))

/-- A finite-rank countable class of infinite languages defeating every
exact language learner, even when each word is presented exactly once. -/
theorem finite_rank_not_identifiable :
    ∃ C : LanguageFamily, (∀ z, (C z).Infinite) ∧ FiniteRankAtMost (range C) 2 ∧
      ¬ ∃ M : List ℕ → Language, ∀ z s, Presents s (C z) → Function.Injective s →
        ∃ T, ∀ t ≥ T, M (textPrefix s t) = C z := by
  refine ⟨coSingletonLanguage,coSingletonLanguage_infinite,rank_two,?_⟩
  rintro ⟨M,valid⟩
  obtain ⟨p,_,legal,locked⟩ := lock _ (coSingletonLanguage_infinite 0)
    (fun h => M h = coSingletonLanguage 0) (valid 0) [] (by simp [Legal])
  obtain ⟨n,_,new⟩ := (infinite_univ : (univ : Set ℕ).Infinite).exists_notMem_finset p.toFinset
  have small : Legal (coSingletonLanguage (n+1)) p :=
    ⟨legal.1,fun x hx eq => new (List.mem_toFinset.mpr (eq ▸ hx))⟩
  obtain ⟨q,ext,legalq,fixed⟩ := lock _ (coSingletonLanguage_infinite (n+1))
    (fun h => M h = coSingletonLanguage (n+1)) (valid (n+1)) p small
  have big := locked q ext ⟨legalq.1,fun _ _ => trivial⟩
  have eq := big.symm.trans (fixed q (List.prefix_refl _) legalq)
  have inside : n ∈ coSingletonLanguage 0 := trivial
  exact (eq ▸ inside : n ∈ coSingletonLanguage (n+1)) rfl

/-- The source's fixed-shape generation and exact identification clauses
can be separated on the very same class. The generator works on positive
real dilations of every positive-width shape in every positive dimension.
A learner reporting even unrestricted sets cannot identify all targets. -/
theorem fixed_shape_separation (d : ℕ) :
    ∃ (C : LanguageFamily) (e : ℕ → Lattice (d+1)), Function.Injective e ∧
      (∀ z, (C z).Infinite) ∧ FiniteRankAtMost (range C) 2 ∧
      (∃ A : List (Lattice (d+1)) → Lattice (d+1), ∀ z s, range s = e '' C z →
        cubeValid A s (e '' C z) ∧ ∀ R : FixedShape.Box (d+1), (∀ i, R.1 i < R.2 i) →
          ENNReal.ofReal (1/2) ≤ FixedShape.density R (range (cubePlay A s)) (e '' C z)) ∧
      ¬ ∃ M : List (Lattice (d+1)) → Set (Lattice (d+1)),
        ∀ z s, range s = e '' C z → Function.Injective s →
          ∃ T, ∀ t ≥ T, M (textPrefix s t) = e '' C z := by
  classical
  obtain ⟨C,inf,rank,impossible⟩ := finite_rank_not_identifiable
  let e (n : ℕ) : Lattice (d+1) := fun _ => (n:ℤ)
  have inj : Function.Injective e := by
    intro n m same
    have eq : (n:ℤ) = (m:ℤ) := congrFun same 0
    exact_mod_cast eq
  have mono : Monotone e := fun _ _ h _ => Int.ofNat_le.mpr h
  refine ⟨C,e,inj,inf,rank,?_,?_⟩
  · obtain ⟨A,gen⟩ := filtered_chain_generation e inj mono C inf rank
    refine ⟨A,fun z s full => ?_⟩
    obtain ⟨valid,lower⟩ := gen z s full
    have sq := lower (fun V => Real.log V) (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact ⟨valid,fun R wide => sq.trans (FixedShape.of_rectangular (Nat.succ_pos d) R wide _ _)⟩
  · rintro ⟨M,learn⟩
    apply impossible
    refine ⟨fun p => e ⁻¹' (M (p.map e)),fun z s pres hs => ?_⟩
    obtain ⟨T,ok⟩ := learn z (e ∘ s) (by rw [Set.range_comp,pres]) (inj.comp hs)
    refine ⟨T,fun t ht => ?_⟩
    have same : (textPrefix s t).map e = textPrefix (e ∘ s) t := by simp [textPrefix,List.map_map]
    change e ⁻¹' M ((textPrefix s t).map e) = C z
    rw [same,ok _ ht,Set.preimage_image_eq _ inj]

end GenLimit.KleinbergWei.Banach.IdentificationCheck
