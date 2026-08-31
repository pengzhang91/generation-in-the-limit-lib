import GenLimit.Paper15_PartialEnumeration.AlgorithmOneRun
import GenLimit.Core.OrderedDensity
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Density accounting after Algorithm 1

This file formalizes the deterministic counting endgame of Section 3 of
Kleinberg--Wei, *Language Generation from Partial Enumerations*.  It does
not claim to construct the paper's priority-list generator.  Instead,
`WarmupChargeCertificate` records exactly the two charge maps that this
dynamic construction must supply:

* a good missed input is charged injectively to the preceding output;
* outside a finite exceptional set, a bad missed input is charged
  injectively to an earlier output.

Each charge lies at most one position to the right of its input in the
fixed order on the true language.  Combining the two injective classes
gives a genuine capacity-two map.  The finite theorem below keeps the
one-position prefix shift explicit, removes it with an additive constant,
and then proves the paper's `α / 3` lower-density conclusion using the
literal ordered `liminf`.

There are two typographical errors in the displayed proof of the source's
charge lemma (Lemma 3.4 in the numbered version).

1. Its concluding map has domain `B_g`, but the lemma and the whole proof
   concern `B_b`; the domain must be `B_b`.
2. It concludes `o_{φ(t)} < ρ(w_t)` immediately after defining
   `ρ(w_t) = o_{φ(t)}`.  This is self-referential and false.  The preceding
   argument establishes the intended inequality `ρ(w_t) < w_t`.

The certificate below uses the corrected statements.  Constructing the
certificate from the full priority-list dynamics remains the exact
unformalized boundary; none of those dynamic obligations is hidden as a
theorem here.
-/

namespace GenLimit
namespace KleinbergWei
namespace PartialEnumeration

open Filter

/-- Ranks in the fixed target ordering whose strings belong to `A`. -/
def orderedRankSet (K : OrderedLanguage) (A : Language) : Set ℕ :=
  {i | K.enumeration i ∈ A}

/-- The ranks below `n` whose strings belong to `A`. -/
noncomputable def orderedRankPrefix
    (K : OrderedLanguage) (A : Language) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun i => K.enumeration i ∈ A

@[simp] theorem orderedRankPrefix_card
    (K : OrderedLanguage) (A : Language) (n : ℕ) :
    (orderedRankPrefix K A n).card = K.prefixCount A n :=
  rfl

@[simp] theorem mem_orderedRankPrefix
    (K : OrderedLanguage) (A : Language) (n i : ℕ) :
    i ∈ orderedRankPrefix K A n ↔
      i < n ∧ K.enumeration i ∈ A := by
  classical
  simp [orderedRankPrefix]

theorem orderedRankPrefix_subset_succ
    (K : OrderedLanguage) (A : Language) (n : ℕ) :
    orderedRankPrefix K A n ⊆ orderedRankPrefix K A (n + 1) := by
  classical
  intro i hi
  simp only [orderedRankPrefix, Finset.mem_filter,
    Finset.mem_range] at hi ⊢
  exact ⟨by omega, hi.2⟩

/-- Adding one target-order position changes a prefix count by at most one. -/
theorem orderedPrefixCount_succ_le_add_one
    (K : OrderedLanguage) (A : Language) (n : ℕ) :
    K.prefixCount A (n + 1) ≤ K.prefixCount A n + 1 := by
  classical
  let old := orderedRankPrefix K A n
  let new := orderedRankPrefix K A (n + 1)
  have hsub : new ⊆ insert n old := by
    intro i hi
    simp only [new, orderedRankPrefix, Finset.mem_filter,
      Finset.mem_range] at hi
    by_cases hin : i = n
    · subst i
      simp
    · have hiold : i ∈ old := by
        simp only [old, orderedRankPrefix, Finset.mem_filter,
          Finset.mem_range]
        exact ⟨by omega, hi.2⟩
      exact Finset.mem_insert_of_mem hiold
  have hcard : new.card ≤ old.card + 1 := by
    calc
      new.card ≤ (insert n old).card := Finset.card_le_card hsub
      _ ≤ old.card + 1 := Finset.card_insert_le n old
  simpa [old, new] using hcard

/-- Corrected source-facing certificate for the warm-up `α / 3` proof.

`good` and `bad` partition the adversary points that the generator never
outputs.  The exceptional set is a finite set of *target ranks*.  The
source's good and bad maps are kept separate because each one is injective;
their union therefore has capacity two, not capacity one. -/
structure WarmupChargeCertificate
    (K : OrderedLanguage)
    (enumerated output good bad : Language) where
  missed_partition : enumerated \ output = good ∪ bad
  good_bad_disjoint : Disjoint good bad
  exceptionRanks : Finset ℕ
  goodCharge : ℕ → ℕ
  badCharge : ℕ → ℕ
  goodCharge_output :
    ∀ ⦃i : ℕ⦄, i ∈ orderedRankSet K good →
      K.enumeration (goodCharge i) ∈ output
  goodCharge_le_succ :
    ∀ ⦃i : ℕ⦄, i ∈ orderedRankSet K good →
      goodCharge i ≤ i + 1
  goodCharge_injective :
    Set.InjOn goodCharge (orderedRankSet K good)
  badCharge_output :
    ∀ ⦃i : ℕ⦄, i ∈ orderedRankSet K bad →
      i ∉ exceptionRanks →
        K.enumeration (badCharge i) ∈ output
  badCharge_le_succ :
    ∀ ⦃i : ℕ⦄, i ∈ orderedRankSet K bad →
      i ∉ exceptionRanks →
        badCharge i ≤ i + 1
  badCharge_injective :
    Set.InjOn badCharge
      (orderedRankSet K bad \ (exceptionRanks : Set ℕ))

namespace WarmupChargeCertificate

/-- The corrected combined map `barρ` from the proof of Theorem 3.1. -/
noncomputable def charge
    {K : OrderedLanguage} {enumerated output good bad : Language}
    (hcert : WarmupChargeCertificate K enumerated output good bad)
    (i : ℕ) : ℕ := by
  classical
  exact
    if K.enumeration i ∈ good then hcert.goodCharge i
    else hcert.badCharge i

/-- The charge class is the second coordinate witnessing capacity two. -/
noncomputable def chargeSlot
    {K : OrderedLanguage} {enumerated output good bad : Language}
    (_hcert : WarmupChargeCertificate K enumerated output good bad)
    (i : ℕ) : Fin 2 := by
  classical
  exact if K.enumeration i ∈ good then 0 else 1

theorem missed_rank_good_or_bad
    {K : OrderedLanguage} {enumerated output good bad : Language}
    (hcert : WarmupChargeCertificate K enumerated output good bad)
    {i : ℕ}
    (hi : i ∈ orderedRankSet K (enumerated \ output)) :
    i ∈ orderedRankSet K good ∨ i ∈ orderedRankSet K bad := by
  change K.enumeration i ∈ good ∨ K.enumeration i ∈ bad
  change K.enumeration i ∈ enumerated \ output at hi
  rw [hcert.missed_partition] at hi
  exact hi

theorem charge_output
    {K : OrderedLanguage} {enumerated output good bad : Language}
    (hcert : WarmupChargeCertificate K enumerated output good bad)
    {i : ℕ}
    (hi : i ∈ orderedRankSet K (enumerated \ output))
    (hiexception : i ∉ hcert.exceptionRanks) :
    K.enumeration (hcert.charge i) ∈ output := by
  classical
  rcases hcert.missed_rank_good_or_bad hi with higood | hibad
  · have higood' : K.enumeration i ∈ good := higood
    rw [charge, if_pos higood']
    exact hcert.goodCharge_output higood
  · have hnGood : K.enumeration i ∉ good := by
      intro higood
      exact Set.disjoint_left.1 hcert.good_bad_disjoint
        higood hibad
    rw [charge, if_neg hnGood]
    exact hcert.badCharge_output hibad hiexception

theorem charge_le_succ
    {K : OrderedLanguage} {enumerated output good bad : Language}
    (hcert : WarmupChargeCertificate K enumerated output good bad)
    {i : ℕ}
    (hi : i ∈ orderedRankSet K (enumerated \ output))
    (hiexception : i ∉ hcert.exceptionRanks) :
    hcert.charge i ≤ i + 1 := by
  classical
  rcases hcert.missed_rank_good_or_bad hi with higood | hibad
  · have higood' : K.enumeration i ∈ good := higood
    rw [charge, if_pos higood']
    exact hcert.goodCharge_le_succ higood
  · have hnGood : K.enumeration i ∉ good := by
      intro higood
      exact Set.disjoint_left.1 hcert.good_bad_disjoint
        higood hibad
    rw [charge, if_neg hnGood]
    exact hcert.badCharge_le_succ hibad hiexception

/-- The union of the two corrected injective charge maps has capacity two.

Equivalently, adding the good/bad slot makes the combined charge injective.
This is the precise combinatorial assertion behind the source sentence
"each output has preimage size at most two." -/
theorem charge_capacity_two
    {K : OrderedLanguage} {enumerated output good bad : Language}
    (hcert : WarmupChargeCertificate K enumerated output good bad) :
    Set.InjOn
      (fun i => (hcert.charge i, hcert.chargeSlot i))
      (orderedRankSet K (enumerated \ output) \
        (hcert.exceptionRanks : Set ℕ)) := by
  classical
  intro i hi j hj heq
  have hiMissed : i ∈ orderedRankSet K (enumerated \ output) :=
    hi.1
  have hjMissed : j ∈ orderedRankSet K (enumerated \ output) :=
    hj.1
  rcases hcert.missed_rank_good_or_bad hiMissed with
      hiGood | hiBad
  · rcases hcert.missed_rank_good_or_bad hjMissed with
        hjGood | hjBad
    · have hiGood' : K.enumeration i ∈ good := hiGood
      have hjGood' : K.enumeration j ∈ good := hjGood
      have hfst : hcert.charge i = hcert.charge j :=
        congrArg Prod.fst heq
      rw [charge, if_pos hiGood',
        charge, if_pos hjGood'] at hfst
      exact hcert.goodCharge_injective hiGood hjGood hfst
    · have hjNotGood : K.enumeration j ∉ good := by
        intro hjGood
        exact Set.disjoint_left.1 hcert.good_bad_disjoint
          hjGood hjBad
      have hiGood' : K.enumeration i ∈ good := hiGood
      have hslot : hcert.chargeSlot i = hcert.chargeSlot j :=
        congrArg Prod.snd heq
      rw [chargeSlot, if_pos hiGood',
        chargeSlot, if_neg hjNotGood] at hslot
      norm_num at hslot
  · have hiNotGood : K.enumeration i ∉ good := by
      intro hiGood
      exact Set.disjoint_left.1 hcert.good_bad_disjoint
        hiGood hiBad
    rcases hcert.missed_rank_good_or_bad hjMissed with
        hjGood | hjBad
    · have hjGood' : K.enumeration j ∈ good := hjGood
      have hslot : hcert.chargeSlot i = hcert.chargeSlot j :=
        congrArg Prod.snd heq
      rw [chargeSlot, if_neg hiNotGood,
        chargeSlot, if_pos hjGood'] at hslot
      norm_num at hslot
    · have hjNotGood : K.enumeration j ∉ good := by
        intro hjGood
        exact Set.disjoint_left.1 hcert.good_bad_disjoint
          hjGood hjBad
      have hfst : hcert.charge i = hcert.charge j :=
        congrArg Prod.fst heq
      rw [charge, if_neg hiNotGood,
        charge, if_neg hjNotGood] at hfst
      exact hcert.badCharge_injective
        ⟨hiBad, hi.2⟩ ⟨hjBad, hj.2⟩ hfst

/-- One injective charge class in the first `n` ranks fits into the output
prefix through rank `n`. -/
theorem prefix_card_le_shifted_output
    {K : OrderedLanguage} {output source : Language}
    (ρ : ℕ → ℕ)
    (houtput :
      ∀ ⦃i : ℕ⦄, i ∈ orderedRankSet K source →
        K.enumeration (ρ i) ∈ output)
    (hle :
      ∀ ⦃i : ℕ⦄, i ∈ orderedRankSet K source →
        ρ i ≤ i + 1)
    (hinjective : Set.InjOn ρ (orderedRankSet K source))
    (n : ℕ) :
    K.prefixCount source n ≤ K.prefixCount output (n + 1) := by
  classical
  let sourcePrefix := orderedRankPrefix K source n
  let outputPrefix := orderedRankPrefix K output (n + 1)
  have hmaps : Set.MapsTo ρ sourcePrefix outputPrefix := by
    intro i hi
    have hi' :
        i ∈ orderedRankSet K source := by
      exact (mem_orderedRankPrefix K source n i).mp hi |>.2
    apply (mem_orderedRankPrefix K output (n + 1) (ρ i)).mpr
    exact ⟨by
      have hirange :=
        (mem_orderedRankPrefix K source n i).mp hi |>.1
      have hρ := hle hi'
      omega, houtput hi'⟩
  have hinj : Set.InjOn ρ sourcePrefix := by
    intro i hi j hj hij
    apply hinjective
    · exact (mem_orderedRankPrefix K source n i).mp hi |>.2
    · exact (mem_orderedRankPrefix K source n j).mp hj |>.2
    · exact hij
  have hcard :=
    Finset.card_le_card_of_injOn ρ hmaps hinj
  simpa [sourcePrefix, outputPrefix] using hcard

/-- The bad charge class obeys the same prefix estimate, with one additive
term for every exceptional rank. -/
theorem bad_prefix_card_le_shifted_output_add_exceptions
    {K : OrderedLanguage} {enumerated output good bad : Language}
    (hcert : WarmupChargeCertificate K enumerated output good bad)
    (n : ℕ) :
    K.prefixCount bad n ≤
      K.prefixCount output (n + 1) + hcert.exceptionRanks.card := by
  classical
  let badPrefix := orderedRankPrefix K bad n
  let clean := badPrefix \ hcert.exceptionRanks
  let outputPrefix := orderedRankPrefix K output (n + 1)
  have hmaps : Set.MapsTo hcert.badCharge clean outputPrefix := by
    intro i hi
    have hiParts := Finset.mem_sdiff.mp hi
    have hiBad : i ∈ orderedRankSet K bad :=
      (mem_orderedRankPrefix K bad n i).mp hiParts.1 |>.2
    apply
      (mem_orderedRankPrefix K output (n + 1)
        (hcert.badCharge i)).mpr
    refine ⟨?_, hcert.badCharge_output hiBad hiParts.2⟩
    have hirange :=
      (mem_orderedRankPrefix K bad n i).mp hiParts.1 |>.1
    have hle := hcert.badCharge_le_succ hiBad hiParts.2
    omega
  have hinj : Set.InjOn hcert.badCharge clean := by
    intro i hi j hj hij
    have hiParts := Finset.mem_sdiff.mp hi
    have hjParts := Finset.mem_sdiff.mp hj
    apply hcert.badCharge_injective
    · exact
        ⟨(mem_orderedRankPrefix K bad n i).mp hiParts.1 |>.2,
          hiParts.2⟩
    · exact
        ⟨(mem_orderedRankPrefix K bad n j).mp hjParts.1 |>.2,
          hjParts.2⟩
    · exact hij
  have hclean :
      clean.card ≤ outputPrefix.card :=
    Finset.card_le_card_of_injOn hcert.badCharge hmaps hinj
  have hcover :
      badPrefix ⊆ clean ∪ hcert.exceptionRanks := by
    intro i hi
    by_cases hie : i ∈ hcert.exceptionRanks
    · exact Finset.mem_union_right _ hie
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hi, hie⟩)
  have hbad :
      badPrefix.card ≤
        clean.card + hcert.exceptionRanks.card :=
    (Finset.card_le_card hcover).trans
      (Finset.card_union_le _ _)
  simpa [badPrefix, clean, outputPrefix] using
    hbad.trans (Nat.add_le_add_right hclean _)

/-- The corrected finite accounting behind Theorem 3.1.

The source suppresses the successor shift in `ρ(w) ≤ Succ_K(w)`.  Here it
is retained first as `prefixCount output (n+1)` and then bounded by the
length-`n` output prefix plus one. -/
theorem theorem_3_1_warmup_finite_accounting
    {K : OrderedLanguage} {enumerated output good bad : Language}
    (hcert : WarmupChargeCertificate K enumerated output good bad)
    (n : ℕ) :
    K.prefixCount enumerated n ≤
      3 * K.prefixCount output n +
        hcert.exceptionRanks.card + 2 := by
  classical
  let cPrefix := orderedRankPrefix K enumerated n
  let oPrefix := orderedRankPrefix K output n
  let gPrefix := orderedRankPrefix K good n
  let bPrefix := orderedRankPrefix K bad n
  have hcover : cPrefix ⊆ oPrefix ∪ (gPrefix ∪ bPrefix) := by
    intro i hi
    have hiC : K.enumeration i ∈ enumerated :=
      (Finset.mem_filter.mp hi).2
    by_cases hiO : K.enumeration i ∈ output
    · apply Finset.mem_union_left
      simp only [oPrefix, orderedRankPrefix,
        Finset.mem_filter]
      exact ⟨(Finset.mem_filter.mp hi).1, hiO⟩
    · have hiMissed : K.enumeration i ∈ enumerated \ output :=
        ⟨hiC, hiO⟩
      rw [hcert.missed_partition] at hiMissed
      rcases hiMissed with hiGood | hiBad
      · apply Finset.mem_union_right
        apply Finset.mem_union_left
        simp only [gPrefix, orderedRankPrefix,
          Finset.mem_filter]
        exact ⟨(Finset.mem_filter.mp hi).1, hiGood⟩
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        simp only [bPrefix, orderedRankPrefix,
          Finset.mem_filter]
        exact ⟨(Finset.mem_filter.mp hi).1, hiBad⟩
  have hc :
      cPrefix.card ≤
        oPrefix.card + gPrefix.card + bPrefix.card := by
    calc
      cPrefix.card ≤ (oPrefix ∪ (gPrefix ∪ bPrefix)).card :=
        Finset.card_le_card hcover
      _ ≤ oPrefix.card + (gPrefix ∪ bPrefix).card :=
        Finset.card_union_le _ _
      _ ≤ oPrefix.card + (gPrefix.card + bPrefix.card) :=
        Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ = oPrefix.card + gPrefix.card + bPrefix.card := by omega
  have hg :
      gPrefix.card ≤
        (orderedRankPrefix K output (n + 1)).card := by
    simpa [gPrefix] using
      prefix_card_le_shifted_output
        hcert.goodCharge hcert.goodCharge_output
        hcert.goodCharge_le_succ hcert.goodCharge_injective n
  have hb :
      bPrefix.card ≤
        (orderedRankPrefix K output (n + 1)).card +
          hcert.exceptionRanks.card := by
    simpa [bPrefix] using
      hcert.bad_prefix_card_le_shifted_output_add_exceptions n
  have hshift :
      (orderedRankPrefix K output (n + 1)).card ≤
        oPrefix.card + 1 := by
    simpa [oPrefix] using
      orderedPrefixCount_succ_le_add_one K output n
  have hfinite :
      cPrefix.card ≤
        3 * oPrefix.card + hcert.exceptionRanks.card + 2 := by
    omega
  simpa [cPrefix, oPrefix] using hfinite

/-- The fixed finite accounting error, normalized by prefix length. -/
noncomputable def warmupExceptionOverhead
    {K : OrderedLanguage} {enumerated output good bad : Language}
    (hcert : WarmupChargeCertificate K enumerated output good bad)
    (n : ℕ) : ℝ :=
  if n = 0 then 0
  else ((hcert.exceptionRanks.card + 2 : ℕ) : ℝ) / n

theorem warmupExceptionOverhead_tendsto_zero
    {K : OrderedLanguage} {enumerated output good bad : Language}
    (hcert : WarmupChargeCertificate K enumerated output good bad) :
    Tendsto hcert.warmupExceptionOverhead atTop (nhds 0) := by
  have hbase :
      Tendsto
        (fun n : ℕ =>
          ((hcert.exceptionRanks.card + 2 : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds 0) := by
    simpa using
      tendsto_const_div_atTop_nhds_zero_nat
        (((hcert.exceptionRanks.card + 2 : ℕ) : ℝ))
  apply hbase.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : n ≠ 0 := by omega
  simp [warmupExceptionOverhead, hn0]

/-- Real-valued ordered-prefix form of the finite `α / 3` accounting. -/
theorem theorem_3_1_warmup_prefix_ratio
    {K : OrderedLanguage} {enumerated output good bad : Language}
    (hcert : WarmupChargeCertificate K enumerated output good bad)
    {n : ℕ} (hn : 0 < n) :
    K.prefixRatio enumerated n ≤
      3 * K.prefixRatio output n +
        hcert.warmupExceptionOverhead n := by
  have hn0 : n ≠ 0 := by omega
  have hfinite :=
    hcert.theorem_3_1_warmup_finite_accounting n
  have hfiniteReal :
      (K.prefixCount enumerated n : ℝ) ≤
        3 * (K.prefixCount output n : ℝ) +
          (hcert.exceptionRanks.card : ℝ) + 2 := by
    exact_mod_cast hfinite
  rw [OrderedLanguage.prefixRatio, if_neg hn0,
    OrderedLanguage.prefixRatio, if_neg hn0,
    warmupExceptionOverhead, if_neg hn0]
  have hnReal : (0 : ℝ) < n := by positivity
  calc
    (K.prefixCount enumerated n : ℝ) / (n : ℝ) ≤
        (3 * (K.prefixCount output n : ℝ) +
          (hcert.exceptionRanks.card : ℝ) + 2) / (n : ℝ) :=
      div_le_div_of_nonneg_right hfiniteReal hnReal.le
    _ = 3 * ((K.prefixCount output n : ℝ) / (n : ℝ)) +
        ((hcert.exceptionRanks.card + 2 : ℕ) : ℝ) / (n : ℝ) := by
      push_cast
      ring

/-- The literal ordered-`liminf` endgame of the warm-up theorem.

No convergence of the enumerated-set density is assumed: the proof uses
only its lower density and the vanishing finite-exception overhead. -/
theorem theorem_3_1_warmup_lowerDensity
    {K : OrderedLanguage} {enumerated output good bad : Language}
    (hcert : WarmupChargeCertificate K enumerated output good bad) :
    K.lowerDensity enumerated / 3 ≤ K.lowerDensity output := by
  apply OrderedLanguage.lowerDensity_div_le_of_eventually_prefixRatio_le
    K enumerated output 3 (by norm_num)
    hcert.warmupExceptionOverhead
    hcert.warmupExceptionOverhead_tendsto_zero
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact hcert.theorem_3_1_warmup_prefix_ratio (n := n) (by omega)

/-- The paper's `α / 3` corollary, stated from an explicit lower-density
hypothesis on the partial enumeration. -/
theorem theorem_3_1_alpha_third
    {K : OrderedLanguage} {enumerated output good bad : Language}
    (hcert : WarmupChargeCertificate K enumerated output good bad)
    {α : ℝ}
    (hα : α ≤ K.lowerDensity enumerated) :
    α / 3 ≤ K.lowerDensity output := by
  exact (div_le_div_of_nonneg_right hα (by norm_num)).trans
    hcert.theorem_3_1_warmup_lowerDensity

end WarmupChargeCertificate

/-! ## Capacity-one endpoint for the pod refinement

The optimal proof replaces the two competing charge classes by growing
pods.  The dynamic pod construction is not formalized here.  The following
certificate instead isolates its intended endpoint: after finitely many
rank exceptions, every enumerated but ungenerated point has a *single*
injective charge into a not-later-than-successor output.  This is stronger
than the intermediate inequalities printed in the source, but it is a
concrete and independently checkable condition—not an assumption silently
packaged as the paper's algorithm.

If a future formalization of the pod dynamics constructs this certificate
(or a suitable asymptotic relaxation of it), the exact `α / 2` liminf
conclusion below is already available.
-/

/-- The ideal capacity-one endpoint targeted by the pod construction. -/
structure PodCapacityOneCertificate
    (K : OrderedLanguage) (enumerated output : Language) where
  exceptionRanks : Finset ℕ
  charge : ℕ → ℕ
  charge_output :
    ∀ ⦃i : ℕ⦄,
      i ∈ orderedRankSet K (enumerated \ output) →
      i ∉ exceptionRanks →
        K.enumeration (charge i) ∈ output
  charge_le_succ :
    ∀ ⦃i : ℕ⦄,
      i ∈ orderedRankSet K (enumerated \ output) →
      i ∉ exceptionRanks →
        charge i ≤ i + 1
  charge_injective :
    Set.InjOn charge
      (orderedRankSet K (enumerated \ output) \
        (exceptionRanks : Set ℕ))

namespace PodCapacityOneCertificate

/-- Nonexceptional missed points in the first `n` ranks inject into output
ranks below `n+1`. -/
theorem missed_prefix_card_le_shifted_output_add_exceptions
    {K : OrderedLanguage} {enumerated output : Language}
    (hcert : PodCapacityOneCertificate K enumerated output)
    (n : ℕ) :
    K.prefixCount (enumerated \ output) n ≤
      K.prefixCount output (n + 1) + hcert.exceptionRanks.card := by
  classical
  let missedPrefix :=
    orderedRankPrefix K (enumerated \ output) n
  let clean := missedPrefix \ hcert.exceptionRanks
  let outputPrefix := orderedRankPrefix K output (n + 1)
  have hmaps : Set.MapsTo hcert.charge clean outputPrefix := by
    intro i hi
    have hiParts := Finset.mem_sdiff.mp hi
    have hiMissed :
        i ∈ orderedRankSet K (enumerated \ output) :=
      (mem_orderedRankPrefix
        K (enumerated \ output) n i).mp hiParts.1 |>.2
    apply
      (mem_orderedRankPrefix K output (n + 1)
        (hcert.charge i)).mpr
    refine ⟨?_, hcert.charge_output hiMissed hiParts.2⟩
    have hirange :=
      (mem_orderedRankPrefix
        K (enumerated \ output) n i).mp hiParts.1 |>.1
    have hle :=
      hcert.charge_le_succ hiMissed hiParts.2
    omega
  have hinj : Set.InjOn hcert.charge clean := by
    intro i hi j hj hij
    have hiParts := Finset.mem_sdiff.mp hi
    have hjParts := Finset.mem_sdiff.mp hj
    apply hcert.charge_injective
    · exact
        ⟨(mem_orderedRankPrefix
          K (enumerated \ output) n i).mp hiParts.1 |>.2,
          hiParts.2⟩
    · exact
        ⟨(mem_orderedRankPrefix
          K (enumerated \ output) n j).mp hjParts.1 |>.2,
          hjParts.2⟩
    · exact hij
  have hclean :
      clean.card ≤ outputPrefix.card :=
    Finset.card_le_card_of_injOn hcert.charge hmaps hinj
  have hcover :
      missedPrefix ⊆ clean ∪ hcert.exceptionRanks := by
    intro i hi
    by_cases hie : i ∈ hcert.exceptionRanks
    · exact Finset.mem_union_right _ hie
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hi, hie⟩)
  have hmissed :
      missedPrefix.card ≤
        clean.card + hcert.exceptionRanks.card :=
    (Finset.card_le_card hcover).trans
      (Finset.card_union_le _ _)
  simpa [missedPrefix, clean, outputPrefix] using
    hmissed.trans (Nat.add_le_add_right hclean _)

/-- Finite accounting at the ideal capacity-one pod boundary. -/
theorem pod_capacity_one_finite_accounting
    {K : OrderedLanguage} {enumerated output : Language}
    (hcert : PodCapacityOneCertificate K enumerated output)
    (n : ℕ) :
    K.prefixCount enumerated n ≤
      2 * K.prefixCount output n +
        hcert.exceptionRanks.card + 1 := by
  classical
  let cPrefix := orderedRankPrefix K enumerated n
  let oPrefix := orderedRankPrefix K output n
  let missedPrefix :=
    orderedRankPrefix K (enumerated \ output) n
  have hcover : cPrefix ⊆ oPrefix ∪ missedPrefix := by
    intro i hi
    have hiC : K.enumeration i ∈ enumerated :=
      (mem_orderedRankPrefix K enumerated n i).mp hi |>.2
    by_cases hiO : K.enumeration i ∈ output
    · exact Finset.mem_union_left _
        ((mem_orderedRankPrefix K output n i).mpr
          ⟨(mem_orderedRankPrefix K enumerated n i).mp hi |>.1,
            hiO⟩)
    · exact Finset.mem_union_right _
        ((mem_orderedRankPrefix K (enumerated \ output) n i).mpr
          ⟨(mem_orderedRankPrefix K enumerated n i).mp hi |>.1,
            hiC, hiO⟩)
  have hc :
      cPrefix.card ≤ oPrefix.card + missedPrefix.card :=
    (Finset.card_le_card hcover).trans
      (Finset.card_union_le _ _)
  have hmissed :
      missedPrefix.card ≤
        (orderedRankPrefix K output (n + 1)).card +
          hcert.exceptionRanks.card := by
    simpa [missedPrefix] using
      hcert.missed_prefix_card_le_shifted_output_add_exceptions n
  have hshift :
      (orderedRankPrefix K output (n + 1)).card ≤
        oPrefix.card + 1 := by
    simpa [oPrefix] using
      orderedPrefixCount_succ_le_add_one K output n
  have hfinite :
      cPrefix.card ≤
        2 * oPrefix.card + hcert.exceptionRanks.card + 1 := by
    omega
  simpa [cPrefix, oPrefix] using hfinite

/-- The normalized finite-exception error at capacity one. -/
noncomputable def podCapacityOneOverhead
    {K : OrderedLanguage} {enumerated output : Language}
    (hcert : PodCapacityOneCertificate K enumerated output)
    (n : ℕ) : ℝ :=
  if n = 0 then 0
  else ((hcert.exceptionRanks.card + 1 : ℕ) : ℝ) / n

theorem podCapacityOneOverhead_tendsto_zero
    {K : OrderedLanguage} {enumerated output : Language}
    (hcert : PodCapacityOneCertificate K enumerated output) :
    Tendsto hcert.podCapacityOneOverhead atTop (nhds 0) := by
  have hbase :
      Tendsto
        (fun n : ℕ =>
          ((hcert.exceptionRanks.card + 1 : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds 0) := by
    simpa using
      tendsto_const_div_atTop_nhds_zero_nat
        (((hcert.exceptionRanks.card + 1 : ℕ) : ℝ))
  apply hbase.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : n ≠ 0 := by omega
  simp [podCapacityOneOverhead, hn0]

/-- Ordered-prefix ratio inequality at the capacity-one pod boundary. -/
theorem pod_capacity_one_prefix_ratio
    {K : OrderedLanguage} {enumerated output : Language}
    (hcert : PodCapacityOneCertificate K enumerated output)
    {n : ℕ} (hn : 0 < n) :
    K.prefixRatio enumerated n ≤
      2 * K.prefixRatio output n +
        hcert.podCapacityOneOverhead n := by
  have hn0 : n ≠ 0 := by omega
  have hfinite :=
    hcert.pod_capacity_one_finite_accounting n
  have hfiniteReal :
      (K.prefixCount enumerated n : ℝ) ≤
        2 * (K.prefixCount output n : ℝ) +
          (hcert.exceptionRanks.card : ℝ) + 1 := by
    exact_mod_cast hfinite
  rw [OrderedLanguage.prefixRatio, if_neg hn0,
    OrderedLanguage.prefixRatio, if_neg hn0,
    podCapacityOneOverhead, if_neg hn0]
  have hnReal : (0 : ℝ) < n := by positivity
  calc
    (K.prefixCount enumerated n : ℝ) / (n : ℝ) ≤
        (2 * (K.prefixCount output n : ℝ) +
          (hcert.exceptionRanks.card : ℝ) + 1) / (n : ℝ) :=
      div_le_div_of_nonneg_right hfiniteReal hnReal.le
    _ = 2 * ((K.prefixCount output n : ℝ) / (n : ℝ)) +
        ((hcert.exceptionRanks.card + 1 : ℕ) : ℝ) / (n : ℝ) := by
      push_cast
      ring

/-- Exact ordered-`liminf` consequence of an ideal capacity-one pod
certificate. -/
theorem pod_capacity_one_lowerDensity
    {K : OrderedLanguage} {enumerated output : Language}
    (hcert : PodCapacityOneCertificate K enumerated output) :
    K.lowerDensity enumerated / 2 ≤ K.lowerDensity output := by
  apply OrderedLanguage.lowerDensity_div_le_of_eventually_prefixRatio_le
    K enumerated output 2 (by norm_num)
    hcert.podCapacityOneOverhead
    hcert.podCapacityOneOverhead_tendsto_zero
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact hcert.pod_capacity_one_prefix_ratio (n := n) (by omega)

/-- `α / 2` follows once the pod dynamics supplies the ideal capacity-one
certificate. -/
theorem pod_capacity_one_alpha_half
    {K : OrderedLanguage} {enumerated output : Language}
    (hcert : PodCapacityOneCertificate K enumerated output)
    {α : ℝ}
    (hα : α ≤ K.lowerDensity enumerated) :
    α / 2 ≤ K.lowerDensity output := by
  exact (div_le_div_of_nonneg_right hα (by norm_num)).trans
    hcert.pod_capacity_one_lowerDensity

end PodCapacityOneCertificate

end PartialEnumeration
end KleinbergWei
end GenLimit
