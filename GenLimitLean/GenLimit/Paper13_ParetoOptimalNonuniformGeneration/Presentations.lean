import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.NoisyProcedure
import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.Representative
import GenLimit.Support.StreamPrefixText
import GenLimit.Bridges.AngluinToPaper02

/-! # Repeated presentations and the diagonal noise coordinates of Paper 13

Finite injective histories give exactly the same achievable time profiles
as full enumerations allowing repetitions. A simulation lists the distinct
observations in a fixed order. Conversely any eligible injective prefix
can be completed with a full clean text, spending no more noise. -/
namespace GenLimit.ParetoGeneration.Presentations
open Generic Support

/-- Each coordinate has a target and an occurrence budget; one common
learner sees only the history, including repetitions. -/
def NoisyProfiles (F : ℕ → Set α) (noise : ℕ → ℕ) : Set TimeVector :=
  {t | PositiveTimeVector t ∧ ∃ A : List α → α, ∀ i s,
    OccurrenceContaminatedPresentationAtMost s (F i) (noise i) → ∀ n,
      t i ≤ (Generic.sample s n).card → A (textPrefix s n) ∈ F i \ (↑(Generic.sample s n) : Set α)}

private theorem sample_eq [DecidableEq α] (s : ℕ → α) (n : ℕ) :
    Generic.sample s n = (textPrefix s n).toFinset := by
  ext x
  simp [Generic.mem_sample_iff,mem_textPrefix_iff]

private theorem negative_le (s : ℕ → α) (K : Set α) {b : ℕ}
    (hs : OccurrenceContaminatedPresentationAtMost s K b) (n : ℕ) :
    (NoisyExamples.negativePart (Generic.sample s n) K).card ≤ b := by
  classical
  obtain ⟨V,hV,hv⟩ := (violationsAtMost_iff_exists_finset s (· ∈ K) b).mp ⟨hs.1,hs.2.1⟩
  apply le_trans (Finset.card_le_card (t := V.image s) ?_) (Finset.card_image_le.trans hV)
  intro x hx
  obtain ⟨hm,hxK⟩ := Finset.mem_filter.mp hx
  obtain ⟨a,_,rfl⟩ := Generic.mem_sample_iff.mp hm
  exact Finset.mem_image.mpr ⟨a,(hv a).mpr hxK,rfl⟩

private theorem extend_history {K : Set α} {b n : ℕ} (xs : Fin n → α)
    (hx : Function.Injective xs) (hp : ∃ s, Generic.Presents s K)
    (hb : (NoisyExamples.negativePart (sequenceSample xs) K).card ≤ b) :
    ∃ s, OccurrenceContaminatedPresentationAtMost s K b ∧ textPrefix s n = List.ofFn xs ∧
      Generic.sample s n = sequenceSample xs := by
  classical
  obtain ⟨tail,ht⟩ := hp
  let l := List.ofFn xs
  let s := prependStream l tail
  have hl : l.length = n := List.length_ofFn
  have hpre : textPrefix s n = l := by
    have h := textPrefix_prependStream l tail 0
    simpa [s,hl,textPrefix] using h
  have hsam : Generic.sample s n = sequenceSample xs := by
    rw [sample_eq,hpre]
    ext x
    simp [l,mem_sequenceSample_iff]
  let B := (Finset.univ : Finset (Fin n)).filter (fun j ↦ xs j ∉ K)
  have him : B.image xs = NoisyExamples.negativePart (sequenceSample xs) K := by
    ext x
    simp [B,NoisyExamples.negativePart,mem_sequenceSample_iff]
    aesop
  have hcard : B.card ≤ b := by
    rw [← him,Finset.card_image_of_injective _ hx] at hb
    exact hb
  let V := B.image Fin.val
  have hviol : ViolationsAtMost s (· ∈ K) b := by
    apply (violationsAtMost_iff_exists_finset _ _ _).mpr
    refine ⟨V,Finset.card_image_le.trans hcard,fun j ↦ ?_⟩
    by_cases hj : j < n
    · have hjl : j < l.length := hl.symm ▸ hj
      have hsx : s j = xs ⟨j,hj⟩ := by simp [s,prependStream,hj,l]
      rw [hsx]
      constructor
      · rintro h
        obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
        exact (Finset.mem_filter.mp ha).2
      · intro h
        exact Finset.mem_image.mpr ⟨⟨j,hj⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩
    · have hok : s j ∈ K := ht ▸ (show s j ∈ Set.range tail from
          ⟨j-l.length,(prependStream_apply_of_not_lt _ _ (by simpa [hl] using hj)).symm⟩)
      simp only [hok,not_true_eq_false,iff_false]
      rintro h
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp h
      exact hj a.isLt
  refine ⟨s,⟨hviol.1,hviol.2,?_⟩,hpre,hsam⟩
  rw [show Set.range s = _ from range_prependStream l tail,ht]
  exact Set.subset_union_right

theorem noisy_profiles_eq (F : ℕ → Set α) (noise : ℕ → ℕ)
    (hp : ∀ i, ∃ s, Generic.Presents s (F i)) :
    NoisyProfiles F noise = NoisyRealizableTimeVectors F noise := by
  classical
  ext t
  constructor
  · rintro ⟨ht,A,hA⟩
    refine ⟨fun _ xs ↦ A (List.ofFn xs),?_,ht⟩
    intro i n xs hn hx hnoise
    obtain ⟨s,hs,hpre,hsam⟩ := extend_history xs hx (hp i) hnoise
    have ha := hA i s hs n (by rw [hsam]; simpa only [Generic.sequenceSample_card_of_injective xs hx] using hn)
    rw [hpre,hsam] at ha
    exact ⟨ha.1,fun j he ↦ ha.2 (mem_sequenceSample_iff.mpr ⟨j,he.symm⟩)⟩
  · rintro ⟨G,hG,ht⟩
    let A (l : List α) := G l.toFinset.card (fun j ↦ (l.toFinset.equivFin.symm j).val)
    refine ⟨ht,A,fun i s hs n hn ↦ ?_⟩
    let S := (textPrefix s n).toFinset
    have he : Generic.sample s n = S := sample_eq s n
    let xs (j : Fin S.card) : α := (S.equivFin.symm j).val
    have hinj : Function.Injective xs := Subtype.val_injective.comp S.equivFin.symm.injective
    have hsample : sequenceSample xs = S := sequenceSample_equivFin_symm S
    have hnoise : NoiseContainedAt F noise i (sequenceSample xs) := by
      change (NoisyExamples.negativePart (sequenceSample xs) (F i)).card ≤ noise i
      rw [hsample,← he]
      exact negative_le s _ hs n
    obtain ⟨hv,hf⟩ := hG i S.card xs (he ▸ hn) hinj hnoise
    refine ⟨hv,fun h ↦ ?_⟩
    have hinS : G S.card xs ∈ S := Set.mem_of_mem_of_subset h (show (↑(Generic.sample s n) : Set α) ⊆ ↑S by rw [he])
    have hmem : G S.card xs ∈ sequenceSample xs := hsample.symm ▸ hinS
    obtain ⟨j,hj⟩ := mem_sequenceSample_iff.mp hmem
    exact hf j hj.symm

/-- One diagonal contains pairs (n,0),(n-1,1),...,(0,n). -/
def triangle : ℕ → ℕ
  | 0 => 0
  | n+1 => triangle n + n + 1

def rank (noise language : ℕ) := triangle (noise+language) + language

private theorem triangle_mono : Monotone triangle := monotone_nat_of_le_succ (fun n ↦ by
  change triangle n ≤ triangle n + n + 1
  omega)

private theorem rank_injective : Function.Injective (fun p : ℕ × ℕ ↦ rank p.1 p.2) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  change triangle (a+b)+b = triangle (c+d)+d at h
  have sum_eq : a+b = c+d := by
    rcases lt_trichotomy (a+b) (c+d) with hl | he | hg
    · have hle := triangle_mono (Nat.succ_le_of_lt hl)
      rw [triangle] at hle
      omega
    · exact he
    · have hle := triangle_mono (Nat.succ_le_of_lt hg)
      rw [triangle] at hle
      omega
  rw [sum_eq] at h
  have : b = d := by omega
  have : a = c := by omega
  congr

private theorem rank_surjective : Function.Surjective (fun p : ℕ × ℕ ↦ rank p.1 p.2) := by
  intro n
  induction n with
  | zero => exact ⟨(0,0),rfl⟩
  | succ n ih =>
    obtain ⟨⟨a,b⟩,rfl⟩ := ih
    cases a with
    | zero =>
      refine ⟨(b+1,0),?_⟩
      simp [rank,triangle]
    | succ a =>
      refine ⟨(a,b+1),?_⟩
      simp only [rank]
      rw [show a+1+b = a+(b+1) by omega]
      omega

noncomputable def diagonal : ℕ × ℕ ≃ ℕ :=
  Equiv.ofBijective (fun p ↦ rank p.1 p.2) ⟨rank_injective,rank_surjective⟩

/-- The same learner works for every language and every occurrence budget
in the source's diagonal order, even on texts with repeated observations. -/
theorem theorem_6 [Infinite α] (F : ℕ → Set α) (hp : ∀ i, ∃ s, Generic.Presents s (F i))
    (f : ℕ → ℕ) (hf : IsUnboundedScheduler f) :
    let C := fun j ↦ F (diagonal.symm j).2
    let noise := fun j ↦ (diagonal.symm j).1
    noisySchedulerTimeVector C noise f hf ∈ NoisyProfiles C noise := by
  dsimp only
  rw [noisy_profiles_eq _ _ (fun j ↦ hp (diagonal.symm j).2)]
  exact theorem_6_corrected_timeVector_realizable _ _ _ _

theorem theorem_8 [Infinite α] (F : ℕ → Set α) (hp : ∀ i, ∃ s, Generic.Presents s (F i))
    (hfinite : FiniteSublevels (canonicalNoisyComplexity
      (fun j ↦ F (diagonal.symm j).2) (fun j ↦ (diagonal.symm j).1))) :
    let C := fun j ↦ F (diagonal.symm j).2
    let noise := fun j ↦ (diagonal.symm j).1
    let t := variantCanonicalTime (canonicalNoisyComplexity C noise)
    t ∈ NoisyProfiles C noise ∧ ParetoOptimal (NoisyProfiles C noise) t := by
  dsimp only
  rw [noisy_profiles_eq _ _ (fun j ↦ hp (diagonal.symm j).2)]
  exact theorem_8_corrected_deterministic_endgame _ _ hfinite

private theorem clean_iff (F : ℕ → Set α) (i : ℕ) {n : ℕ} (xs : Fin n → α) :
    NoiseContainedAt F (fun _ ↦ 0) i (sequenceSample xs) ↔ ∀ j, xs j ∈ F i := by
  classical
  change (NoisyExamples.negativePart (sequenceSample xs) (F i)).card ≤ 0 ↔ _
  rw [Nat.le_zero,Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem]
  simp only [NoisyExamples.negativePart,Finset.mem_filter,mem_sequenceSample_iff]
  constructor
  · intro h j
    by_contra hn
    exact h (xs j) ⟨⟨j,rfl⟩,hn⟩
  · rintro h _ ⟨⟨j,rfl⟩,hn⟩; exact hn (h j)

/-- In the noiseless case the repeated-text profile set is precisely the
finite injective-history profile set used in Theorems 1, 4 and 5. Thus both
realizability and comparison with all competing generators transport. -/
theorem clean_profiles_eq (F : ℕ → Set α) (hp : ∀ i, ∃ s, Generic.Presents s (F i)) :
    NoisyProfiles F (fun _ ↦ 0) = RealizableTimeVectors F := by
  rw [noisy_profiles_eq F _ hp]
  ext t
  constructor
  · rintro ⟨G,hG,ht⟩
    exact ⟨G,fun i n xs hn hx hf ↦ hG i n xs hn hx ((clean_iff F i xs).mpr hf),ht⟩
  · rintro ⟨G,hG,ht⟩
    exact ⟨G,fun i n xs hn hx he ↦ hG i n xs hn hx ((clean_iff F i xs).mp he),ht⟩

/-- The distributional finite-history profile has exactly the paper's
full-presentation meaning. Representativeness holds on every nonempty input
history, while support correctness is required on target texts. -/
theorem representative_profiles_iff [DecidableEq α] (F : ℕ → Set α) (g : ℕ → Set α)
    (ε : ℝ) (t : TimeVector) (hp : ∀ i, ∃ s, Generic.Presents s (F i)) :
    t ∈ Representative.Realizable F g ε ↔ PositiveTimeVector t ∧
      ∃ G : List α → RepresentativeGeneration.DiscreteDistribution α,
        (∀ xs, xs.toFinset.Nonempty → RepresentativeGeneration.groupSupDistance (G xs) xs.toFinset g ≤
          ENNReal.ofReal ε) ∧ ∀ i s, Generic.Presents s (F i) → ∀ n,
          t i ≤ (Generic.sample s n).card → RepresentativeGeneration.SupportedOn (G (textPrefix s n))
            (F i \ (↑(Generic.sample s n) : Set α)) := by
  constructor
  · rintro ⟨ht,G,hG⟩
    refine ⟨ht,G,fun xs hs ↦ (hG xs hs).1,fun i s hs n hn ↦ ?_⟩
    rw [sample_eq] at *
    have hpos : (textPrefix s n).toFinset.Nonempty :=
      Finset.card_pos.mp ((ht i).trans hn)
    exact (hG _ hpos).2 i hn (fun x hx ↦ hs ▸
      (show x ∈ Set.range s from by obtain ⟨j,_,hj⟩ := mem_textPrefix_iff.mp
                                            (List.mem_toFinset.mp hx); exact ⟨j,hj⟩))
  · rintro ⟨ht,G,hr,hs⟩
    refine ⟨ht,G,fun xs hne ↦ ⟨hr xs hne,fun i hn hxs ↦ ?_⟩⟩
    obtain ⟨tail,htail⟩ := hp i
    have hp' := prependStream_presents (fun x hx ↦ hxs (List.mem_toFinset.mpr hx)) htail
    have he : textPrefix (prependStream xs tail) xs.length = xs := by
      simpa [textPrefix] using textPrefix_prependStream xs tail 0
    have h := hs i _ hp' xs.length
    rw [sample_eq,he] at h
    exact h hn

end GenLimit.ParetoGeneration.Presentations
