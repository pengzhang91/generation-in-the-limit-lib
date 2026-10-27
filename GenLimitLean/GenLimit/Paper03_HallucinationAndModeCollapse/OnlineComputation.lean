import GenLimit.Paper03_HallucinationAndModeCollapse.BreadthIdentification
import GenLimit.Paper03_HallucinationAndModeCollapse.UnambiguousModel
import GenLimit.Support.ComputableLists

/-!
# Computable online identification reductions

The exact/approximate-breadth reductions reuse the statistical finite-label
identifier, now proving syntactic index stabilization on every presentation.
The unambiguous reduction implements the source's bounded eligible-index
search. Both need only finitely many family/support membership answers.
Ordinary computation requires uniform computability of those answers;
pointwise decidable MOP alone is never promoted to a uniform decider.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic GenLimit.Support

theorem observedPrefix_set (stream : Stream ℕ) (t : ℕ) :
    {x | x ∈ GenLimit.textPrefix stream t} = (↑(Generic.sample stream t) : Set ℕ) := by
  ext x
  simp [GenLimit.mem_textPrefix_iff, Generic.sample]

private theorem firstTrue_eq_of_first {α : Type*} (p : α → ℕ → Bool) (a : α)
    (n z : ℕ) (hz : z < n) (ht : p a z = true)
    (hearlier : ∀ j < z, p a j ≠ true) : (firstTrue p a n).getD 0 = z := by
  have hne : firstTrue p a n ≠ none := by
    intro hn
    have hf := (firstTrue_eq_none_iff p a n).mp hn z hz
    simp [ht] at hf
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hne
  have hle : j ≤ z := firstTrue_le_of_true hj hz ht
  have he : j = z := by
    by_contra h
    exact hearlier j (lt_of_le_of_ne hle h) (firstTrue_spec hj).2.1
  simp [hj, he]

/-- The bounded finite-label learner stabilizes to the least target name,
not merely to a sequence of extensionally correct names. -/
theorem breadthIdentifier_identifies_of_completed {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (G : StatisticalGenerator) (Q : List ℕ → ℕ → Bool)
    (hQ : ∀ xs x, Q xs x = true ↔ x ∈ (G xs).support)
    (hcomplete : ∀ i stream, Generic.Presents stream (C i) →
      ∃ T, ∀ t, T ≤ t → completedSupport (statisticalSupportView G) stream t = C i) :
    GenLimit.Angluin.SemanticallyIdentifies (breadthIdentifier O Q) C := by
  classical
  intro i stream hP
  let hex : ∃ j, C j = C i := ⟨i, rfl⟩
  let z := Nat.find hex
  have hz : C z = C i := Nat.find_spec hex
  have hleast : IsLeastTargetIndex C z := by
    intro j hj he
    exact Nat.find_min hex hj (he.trans hz)
  obtain ⟨Tc, hTc⟩ := hcomplete i stream hP
  obtain ⟨Td, hTd⟩ := eventually_leastMatching_of_target hleast
  refine ⟨z, hz, max (max Tc Td) z, ?_⟩
  intro t ht
  have hct : (G (GenLimit.textPrefix stream t)).support ∪
      {x | x ∈ GenLimit.textPrefix stream t} = C z := by
    rw [observedPrefix_set, hz]
    have hc := hTc t (by omega)
    simpa only [completedSupport, statisticalSupportView_supportAt] using hc
  apply firstTrue_eq_of_first (breadthMatches O Q) _ _ z
  · simp only [GenLimit.textPrefix_length]; omega
  · rw [breadthMatches_correct O G Q hQ, hct]
    exact fun _ _ => Iff.rfl
  · intro j hj hm
    have hmatch := (breadthMatches_correct O G Q hQ _ j).mp hm
    rw [hct, GenLimit.textPrefix_length] at hmatch
    exact hTd t (by omega) j hj hmatch

theorem breadthIdentifier_identifies_of_fresh {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (G : StatisticalGenerator) (Q : List ℕ → ℕ → Bool)
    (hQ : ∀ xs x, Q xs x = true ↔ x ∈ (G xs).support)
    (hG : FreshBreadthInLimit (statisticalSupportView G) C) :
    GenLimit.Angluin.SemanticallyIdentifies (breadthIdentifier O Q) C := by
  apply breadthIdentifier_identifies_of_completed O G Q hQ
  intro i stream hP
  obtain ⟨T, hT⟩ := hG i stream hP
  exact ⟨T, fun t ht => completedSupport_of_freshBreadth hP (hT t ht)⟩

theorem breadthIdentifier_identifies_of_repeating {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (G : StatisticalGenerator) (Q : List ℕ → ℕ → Bool)
    (hQ : ∀ xs x, Q xs x = true ↔ x ∈ (G xs).support)
    (hG : RepeatingBreadthInLimit (statisticalSupportView G) C) :
    GenLimit.Angluin.SemanticallyIdentifies (breadthIdentifier O Q) C := by
  apply breadthIdentifier_identifies_of_completed O G Q hQ
  intro i stream hP
  obtain ⟨T, hT⟩ := hG i stream hP
  exact ⟨T, fun t ht => completedSupport_of_repeatingBreadth hP (hT t ht)⟩

theorem breadthIdentifier_identifies_of_approximate {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (G : StatisticalGenerator) (Q : List ℕ → ℕ → Bool)
    (hQ : ∀ xs x, Q xs x = true ↔ x ∈ (G xs).support)
    (hstable : StatisticalStable G C)
    (hG : ApproximateBreadthInLimit (statisticalSupportView G) C) :
    GenLimit.Angluin.SemanticallyIdentifies (breadthIdentifier O Q) C :=
  breadthIdentifier_identifies_of_completed O G Q hQ
    (stable_approximate_completedSupport hstable hG)

def unambiguousMatches {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (Q : List ℕ → ℕ → Bool) (xs : List ℕ) (j : ℕ) : Bool :=
  xs.all (O.query j) && boundedAll (fun data : List ℕ × ℕ => fun x =>
    !(O.query data.2 x) || Q data.1 x || listContains data.1 x) (xs, j) xs.length

def boundedUnambiguousIdentifier {C : Generic.LanguageFamily ℕ} (O : GenLimit.MembershipOracle C)
    (Q : List ℕ → ℕ → Bool) (xs : List ℕ) : ℕ :=
  (firstTrue (unambiguousMatches O Q) xs (xs.length + 1)).getD 0

theorem unambiguousMatches_correct {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (G : StatisticalGenerator) (Q : List ℕ → ℕ → Bool)
    (hQ : ∀ xs x, Q xs x = true ↔ x ∈ (G xs).support) (xs : List ℕ) (j : ℕ) :
    unambiguousMatches O Q xs j = true ↔
      Eligible C (G xs).support xs.toFinset xs.length j := by
  simp only [unambiguousMatches, Bool.and_eq_true, List.all_eq_true, O.query_spec,
    boundedAll_eq_true_iff, Bool.or_eq_true, hQ, listContains_eq_true_iff,
    Eligible, Set.mem_union, Finset.mem_coe, List.mem_toFinset]
  constructor
  · rintro ⟨hc, hg⟩
    refine ⟨fun x hx => hc x (List.mem_toFinset.mp hx), ?_⟩
    intro x hx hm
    rcases hg x hx with (hfalse | hsupport) | hsample
    · have ht : O.query j x = true := O.query_spec.mpr hm
      simp [ht] at hfalse
    · exact Or.inl hsupport
    · exact Or.inr hsample
  · rintro ⟨hc, hg⟩
    refine ⟨fun x hx => hc (List.mem_toFinset.mpr hx), ?_⟩
    intro x hx
    by_cases hm : x ∈ C j
    · rcases hg x hx hm with hs | hx
      · exact Or.inl (Or.inr hs)
      · exact Or.inr hx
    · have hf : O.query j x = false := Bool.eq_false_of_not_eq_true (fun ht => hm (O.query_spec.mp ht))
      exact Or.inl (Or.inl (by simp [hf]))

theorem unambiguousMatches_computable {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (hO : Computable₂ O.query)
    (Q : List ℕ → ℕ → Bool) (hQ : Computable₂ Q) : Computable₂ (unambiguousMatches O Q) := by
  have hc : Computable (fun data : List ℕ × ℕ => data.1.all (O.query data.2)) :=
    ComputableLists.all (l := fun data : List ℕ × ℕ => data.1) (f := fun data x => O.query data.2 x)
      Computable.fst (hO.comp (Computable.snd.comp Computable.fst) Computable.snd).to₂
  have hp : Computable₂ (fun data : List ℕ × ℕ => fun x =>
      !(O.query data.2 x) || Q data.1 x || listContains data.1 x) :=
    (Primrec.or.to_comp.comp (Primrec.or.to_comp.comp
      (Primrec.not.to_comp.comp (hO.comp (Computable.snd.comp Computable.fst) Computable.snd))
      (hQ.comp (Computable.fst.comp Computable.fst) Computable.snd))
      (listContains_computable.comp (Computable.fst.comp Computable.fst) Computable.snd)).to₂
  exact (Primrec.and.to_comp.comp hc ((boundedAll_computable hp).comp Computable.id
    (Computable.list_length.comp Computable.fst))).to₂

theorem boundedUnambiguousIdentifier_computable {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (hO : Computable₂ O.query)
    (Q : List ℕ → ℕ → Bool) (hQ : Computable₂ Q) : Computable (boundedUnambiguousIdentifier O Q) :=
  Computable.option_getD
    ((firstTrue_computable (unambiguousMatches_computable O hO Q hQ)).comp Computable.id
      ((Primrec.succ.comp Primrec.list_length).to_comp)) (Computable.const 0)

theorem boundedUnambiguousIdentifier_identifies {C : Generic.LanguageFamily ℕ}
    (O : GenLimit.MembershipOracle C) (G : StatisticalGenerator) (Q : List ℕ → ℕ → Bool)
    (hQ : ∀ xs x, Q xs x = true ↔ x ∈ (G xs).support) (hC : HasDistinctLanguages C)
    (hstable : StatisticalStable G C)
    (hunamb : UnambiguousInLimit (statisticalSupportView G) C) :
    GenLimit.Angluin.SemanticallyIdentifies (boundedUnambiguousIdentifier O Q) C := by
  classical
  intro i stream hP
  let hex : ∃ j, C j = C i := ⟨i, rfl⟩
  let z := Nat.find hex
  have hz : C z = C i := Nat.find_spec hex
  have hleast : IsLeastTargetIndex C z := by
    intro j hj he
    exact Nat.find_min hex hj (he.trans hz)
  have hPz : Generic.Presents stream (C z) := by simpa [hz] using hP
  obtain ⟨Tz, hTz⟩ := eventually_target_eligible hPz hC hstable hunamb
  obtain ⟨Te, hTe⟩ := eventually_earlier_not_eligible hPz hleast hstable hunamb
  have he (t j : ℕ) :
      unambiguousMatches O Q (GenLimit.textPrefix stream t) j = true ↔
        Eligible C (supportAt (statisticalSupportView G) stream t) (Generic.sample stream t) t j := by
    rw [unambiguousMatches_correct O G Q hQ, GenLimit.textPrefix_length,
      ← statisticalSupportView_supportAt]
    have hs : (GenLimit.textPrefix stream t).toFinset = Generic.sample stream t := by
      ext x
      simpa using Set.ext_iff.mp (observedPrefix_set stream t) x
    rw [hs]
  refine ⟨z, hz, max (max Tz Te) z, ?_⟩
  intro t ht
  apply firstTrue_eq_of_first (unambiguousMatches O Q) _ _ z
  · simp only [GenLimit.textPrefix_length]; omega
  · exact (he t z).mpr (hTz t (by omega))
  · intro j hj hm
    exact hTe j hj t (by omega) ((he t j).mp hm)

end GenLimit.HallucinationModeCollapse
