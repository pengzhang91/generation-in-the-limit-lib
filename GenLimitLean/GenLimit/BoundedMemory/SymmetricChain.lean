import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Set.Card

/-!
# Symmetric chains in the finite Boolean lattice

Source: Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas,
*On Language Generation in the Limit with Bounded Memory*,
arXiv:2605.30324v1, Fact 4.6.

The source defines a chain as a strictly increasing sequence of subsets, but
does not spell out the adjective “symmetric.”  This module uses its standard
ranked-poset meaning: for some lower rank `low`, the chain contains exactly
one set at every rank from `low` through `n - low`.  Thus it is saturated and
its endpoint ranks sum to `n`.

The proof is constructive.  When adjoining a new ground-set element, each
old symmetric chain is split into a long chain and, unless it is a singleton,
a short chain.  Unique coverage is preserved.  Every resulting chain has
exactly one middle-rank member, so the number of chains is the central
binomial coefficient.

Lemma 4.8 uses only the weaker consequences exposed by
`symmetric_chain_decomposition_fintype`: the power set is uniquely
partitioned into exactly the central-binomial number of inclusion chains.
The endpoint symmetry and saturation are nevertheless formalized here
because they are the standard literal content of Fact 4.6.
-/

namespace GenLimit.BoundedMemory

open Finset

/-- An unordered presentation of a saturated symmetric chain in the Boolean
lattice on `range n`.  `low` is existentially quantified: the chain has
exactly one member at every rank from `low` through `n - low`. -/
def IsSymmetricChain (n : ℕ) (C : Finset (Finset ℕ)) : Prop :=
  (∀ A ∈ C, A ⊆ Finset.range n) ∧
  (∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A) ∧
  ∃ low,
    2 * low ≤ n ∧
    (∀ A ∈ C, low ≤ A.card ∧ A.card ≤ n - low) ∧
    ∀ r, low ≤ r → r ≤ n - low →
      ∃ A ∈ C, A.card = r

/-- A finite family of symmetric chains which contains every subset of
`range n` in exactly one chain. -/
structure Decomposition (n : ℕ) where
  chains : Set (Finset (Finset ℕ))
  finite_chains : chains.Finite
  chain_spec : ∀ C ∈ chains, IsSymmetricChain n C
  existsUnique_mem :
    ∀ A : Finset ℕ, A ⊆ Finset.range n →
      ∃! C : Finset (Finset ℕ), C ∈ chains ∧ A ∈ C

def RankWitness (n : ℕ) (C : Finset (Finset ℕ)) (low : ℕ) : Prop :=
  2 * low ≤ n ∧
  (∀ A ∈ C, low ≤ A.card ∧ A.card ≤ n - low) ∧
  ∀ r, low ≤ r → r ≤ n - low →
    ∃ A ∈ C, A.card = r

theorem IsSymmetricChain.exists_rankWitness
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C) :
    ∃ low, RankWitness n C low :=
  hC.2.2

noncomputable def chainLow (n : ℕ) (C : Finset (Finset ℕ)) : ℕ := by
  classical
  exact if h : ∃ low, RankWitness n C low then Classical.choose h else 0

theorem chainLow_spec
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C) :
    RankWitness n C (chainLow n C) := by
  rw [chainLow, dif_pos hC.exists_rankWitness]
  exact Classical.choose_spec hC.exists_rankWitness

theorem chainLow_twice_le
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C) :
    2 * chainLow n C ≤ n :=
  (chainLow_spec hC).1

theorem chainLow_card_bounds
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C) {A : Finset ℕ} (hA : A ∈ C) :
    chainLow n C ≤ A.card ∧ A.card ≤ n - chainLow n C :=
  (chainLow_spec hC).2.1 A hA

theorem chainLow_rank_exists
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C) {r : ℕ}
    (hlr : chainLow n C ≤ r)
    (hr : r ≤ n - chainLow n C) :
    ∃ A ∈ C, A.card = r :=
  (chainLow_spec hC).2.2 r hlr hr

noncomputable def chainTop (n : ℕ) (C : Finset (Finset ℕ)) : Finset ℕ :=
  if h : ∃ A ∈ C, A.card = n - chainLow n C then
    Classical.choose h
  else
    ∅

theorem chainTop_spec
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C) :
    chainTop n C ∈ C ∧
      (chainTop n C).card = n - chainLow n C := by
  have hlow : chainLow n C ≤ n - chainLow n C := by
    have := chainLow_twice_le hC
    omega
  have hex :=
    chainLow_rank_exists hC hlow (le_rfl : n - chainLow n C ≤ _)
  rw [chainTop, dif_pos hex]
  exact Classical.choose_spec hex

theorem chainTop_subset_range
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C) :
    chainTop n C ⊆ Finset.range n :=
  hC.1 _ (chainTop_spec hC).1

theorem eq_chainTop_of_mem_of_card_eq
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C) {A : Finset ℕ}
    (hA : A ∈ C)
    (hcard : A.card = n - chainLow n C) :
    A = chainTop n C := by
  rcases hC.2.1 A hA (chainTop n C) (chainTop_spec hC).1 with h | h
  · exact Finset.eq_of_subset_of_card_le h
      (by rw [hcard, (chainTop_spec hC).2])
  · exact (Finset.eq_of_subset_of_card_le h
      (by rw [hcard, (chainTop_spec hC).2])).symm

theorem mem_ne_top_card_lt
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C) {A : Finset ℕ}
    (hA : A ∈ C) (hne : A ≠ chainTop n C) :
    A.card < n - chainLow n C := by
  have hle := (chainLow_card_bounds hC hA).2
  exact lt_of_le_of_ne hle (fun h =>
    hne (eq_chainTop_of_mem_of_card_eq hC hA h))

theorem mem_subset_chainTop
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C) {A : Finset ℕ}
    (hA : A ∈ C) :
    A ⊆ chainTop n C := by
  rcases hC.2.1 A hA (chainTop n C) (chainTop_spec hC).1 with h | h
  · exact h
  · have hcards : (chainTop n C).card ≤ A.card :=
      Finset.card_le_card h
    have hAupper := (chainLow_card_bounds hC hA).2
    have htopcard := (chainTop_spec hC).2
    have heqcard : A.card = (chainTop n C).card := by omega
    have heq : chainTop n C = A :=
      Finset.eq_of_subset_of_card_le h (by omega)
    simpa [heq]

noncomputable def longCarrier (n : ℕ) (C : Finset (Finset ℕ)) :
    Finset (Finset ℕ) :=
  insert (insert n (chainTop n C)) C

noncomputable def shortCarrier (n : ℕ) (C : Finset (Finset ℕ)) :
    Finset (Finset ℕ) :=
  (C.erase (chainTop n C)).image (insert n)

theorem not_mem_of_subset_range
    {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    n ∉ A := by
  intro hn
  exact (Finset.mem_range.mp (hA hn)).ne rfl

theorem erase_insert_fresh
    {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    (insert n A).erase n = A := by
  rw [Finset.erase_insert (not_mem_of_subset_range hA)]

theorem insert_fresh_card
    {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    (insert n A).card = A.card + 1 := by
  rw [Finset.card_insert_of_notMem (not_mem_of_subset_range hA)]

theorem insert_subset_range_succ
    {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    insert n A ⊆ Finset.range (n + 1) := by
  intro x hx
  rw [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · simp
  · have := Finset.mem_range.mp (hA hx)
    simp only [Finset.mem_range]
    omega

theorem subset_range_succ
    {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    A ⊆ Finset.range (n + 1) :=
  hA.trans (by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega)

theorem mem_longCarrier_iff
    {n : ℕ} {C : Finset (Finset ℕ)} {A : Finset ℕ} :
    A ∈ longCarrier n C ↔
      A = insert n (chainTop n C) ∨ A ∈ C := by
  simp [longCarrier]

theorem mem_shortCarrier_iff
    {n : ℕ} {C : Finset (Finset ℕ)} {A : Finset ℕ} :
    A ∈ shortCarrier n C ↔
      ∃ B ∈ C, B ≠ chainTop n C ∧ insert n B = A := by
  classical
  simp only [shortCarrier, Finset.mem_image, Finset.mem_erase]
  aesop

theorem longCarrier_symmetric
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C) :
    IsSymmetricChain (n + 1) (longCarrier n C) := by
  let low := chainLow n C
  have hnTop : n ∉ chainTop n C :=
    not_mem_of_subset_range (chainTop_subset_range hC)
  have htopCard :
      (insert n (chainTop n C)).card =
        n + 1 - low := by
    rw [Finset.card_insert_of_notMem hnTop, (chainTop_spec hC).2]
    dsimp [low]
    have := chainLow_twice_le hC
    omega
  refine ⟨?_, ?_, ⟨low, ?_, ?_, ?_⟩⟩
  · intro A hA
    rw [mem_longCarrier_iff] at hA
    rcases hA with rfl | hA
    · exact insert_subset_range_succ (chainTop_subset_range hC)
    · exact subset_range_succ (hC.1 A hA)
  · intro A hA B hB
    rw [mem_longCarrier_iff] at hA hB
    rcases hA with rfl | hA <;> rcases hB with rfl | hB
    · exact Or.inl (Subset.rfl)
    · exact Or.inr <|
        (mem_subset_chainTop hC hB).trans (Finset.subset_insert _ _)
    · exact Or.inl <|
        (mem_subset_chainTop hC hA).trans (Finset.subset_insert _ _)
    · exact hC.2.1 A hA B hB
  · have := chainLow_twice_le hC
    dsimp [low]
    omega
  · intro A hA
    rw [mem_longCarrier_iff] at hA
    rcases hA with rfl | hA
    · constructor
      · dsimp [low] at htopCard ⊢
        have := chainLow_twice_le hC
        omega
      · exact le_of_eq htopCard
    · have hbounds := chainLow_card_bounds hC hA
      dsimp [low] at hbounds ⊢
      constructor <;> omega
  · intro r hlr hr
    by_cases hrOld : r ≤ n - low
    · obtain ⟨A, hAC, hcard⟩ :=
        chainLow_rank_exists hC (by simpa [low] using hlr) (by
          simpa [low] using hrOld)
      exact ⟨A, (mem_longCarrier_iff).2 (Or.inr hAC), hcard⟩
    · have hre : r = n + 1 - low := by omega
      exact
        ⟨insert n (chainTop n C),
          (mem_longCarrier_iff).2 (Or.inl rfl),
          htopCard.trans hre.symm⟩

theorem insert_fresh_injective_on
    {n : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ Finset.range n) (hB : B ⊆ Finset.range n)
    (h : insert n A = insert n B) :
    A = B := by
  have := congrArg (fun X : Finset ℕ => X.erase n) h
  simpa [erase_insert_fresh hA, erase_insert_fresh hB] using this

theorem shortCarrier_symmetric
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C)
    (hsplit : 2 * chainLow n C < n) :
    IsSymmetricChain (n + 1) (shortCarrier n C) := by
  let low := chainLow n C
  have hlast : n - low - 1 < n - low := by
    have := chainLow_twice_le hC
    dsimp [low] at hsplit ⊢
    omega
  refine ⟨?_, ?_, ⟨low + 1, ?_, ?_, ?_⟩⟩
  · intro A hA
    rw [mem_shortCarrier_iff] at hA
    obtain ⟨B, hBC, -, rfl⟩ := hA
    exact insert_subset_range_succ (hC.1 B hBC)
  · intro A hA B hB
    rw [mem_shortCarrier_iff] at hA hB
    obtain ⟨A₀, hA₀C, -, rfl⟩ := hA
    obtain ⟨B₀, hB₀C, -, rfl⟩ := hB
    rcases hC.2.1 A₀ hA₀C B₀ hB₀C with h | h
    · exact Or.inl (Finset.insert_subset_insert n h)
    · exact Or.inr (Finset.insert_subset_insert n h)
  · dsimp [low] at hsplit ⊢
    omega
  · intro A hA
    rw [mem_shortCarrier_iff] at hA
    obtain ⟨B, hBC, hBne, rfl⟩ := hA
    have hBsub := hC.1 B hBC
    have hcard := insert_fresh_card hBsub
    have hlB := (chainLow_card_bounds hC hBC).1
    have huB := mem_ne_top_card_lt hC hBC hBne
    dsimp [low] at hlB huB ⊢
    constructor <;> omega
  · intro r hlr hur
    have hlold : low ≤ r - 1 := by omega
    have huold : r - 1 ≤ n - low := by omega
    obtain ⟨B, hBC, hBcard⟩ :=
      chainLow_rank_exists hC (by simpa [low] using hlold) (by
        simpa [low] using huold)
    have hBsub := hC.1 B hBC
    have hBne : B ≠ chainTop n C := by
      intro heq
      subst B
      rw [(chainTop_spec hC).2] at hBcard
      dsimp [low] at hBcard hur
      omega
    refine ⟨insert n B, (mem_shortCarrier_iff).2
      ⟨B, hBC, hBne, rfl⟩, ?_⟩
    rw [insert_fresh_card hBsub, hBcard]
    omega

theorem erase_mem_of_mem_long
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C)
    {A : Finset ℕ} (hA : A ∈ longCarrier n C) :
    A.erase n ∈ C := by
  rw [mem_longCarrier_iff] at hA
  rcases hA with rfl | hA
  · simpa [erase_insert_fresh (chainTop_subset_range hC)] using
      (chainTop_spec hC).1
  · rw [Finset.erase_eq_of_notMem
      (not_mem_of_subset_range (hC.1 A hA))]
    exact hA

theorem erase_mem_of_mem_short
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C)
    {A : Finset ℕ} (hA : A ∈ shortCarrier n C) :
    A.erase n ∈ C := by
  rw [mem_shortCarrier_iff] at hA
  obtain ⟨B, hBC, -, rfl⟩ := hA
  simpa [erase_insert_fresh (hC.1 B hBC)] using hBC

theorem mem_short_has_new
    {n : ℕ} {C : Finset (Finset ℕ)}
    {A : Finset ℕ} (hA : A ∈ shortCarrier n C) :
    n ∈ A := by
  rw [mem_shortCarrier_iff] at hA
  obtain ⟨B, -, -, rfl⟩ := hA
  exact Finset.mem_insert_self _ _

theorem long_short_disjoint
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C) :
    Disjoint (longCarrier n C) (shortCarrier n C) := by
  rw [Finset.disjoint_left]
  intro A hlong hshort
  rw [mem_longCarrier_iff] at hlong
  rw [mem_shortCarrier_iff] at hshort
  obtain ⟨B, hBC, hBne, hBA⟩ := hshort
  rcases hlong with hAnew | hAC
  · apply hBne
    apply insert_fresh_injective_on
      (hC.1 B hBC) (chainTop_subset_range hC)
    exact hBA.trans hAnew
  · have hnA : n ∉ A :=
      not_mem_of_subset_range (hC.1 A hAC)
    apply hnA
    rw [← hBA]
    exact Finset.mem_insert_self _ _

theorem erase_subset_range
    {n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.range (n + 1)) :
    A.erase n ⊆ Finset.range n := by
  intro x hx
  have hxA := Finset.mem_of_mem_erase hx
  have hxn := Finset.ne_of_mem_erase hx
  have hlt : x < n + 1 := Finset.mem_range.mp (hA hxA)
  exact Finset.mem_range.mpr (by omega)

theorem insert_erase_new
    {n : ℕ} {A : Finset ℕ} (hnA : n ∈ A) :
    insert n (A.erase n) = A :=
  Finset.insert_erase hnA

noncomputable def nextChains
    {n : ℕ} (D : Decomposition n) :
    Set (Finset (Finset ℕ)) :=
  (longCarrier n '' D.chains) ∪
  (shortCarrier n ''
    {C | C ∈ D.chains ∧ 2 * chainLow n C < n})

theorem nextChains_finite
    {n : ℕ} (D : Decomposition n) :
    (nextChains D).Finite := by
  apply Set.Finite.union
  · exact D.finite_chains.image _
  · exact (D.finite_chains.sep _).image _

theorem nextChains_chain_spec
    {n : ℕ} (D : Decomposition n)
    {C' : Finset (Finset ℕ)} (hC' : C' ∈ nextChains D) :
    IsSymmetricChain (n + 1) C' := by
  rcases hC' with ⟨C, hCD, rfl⟩ | ⟨C, ⟨hCD, hsplit⟩, rfl⟩
  · exact longCarrier_symmetric (D.chain_spec C hCD)
  · exact shortCarrier_symmetric (D.chain_spec C hCD) hsplit

theorem origin_eq_of_common_member
    {n : ℕ} (D : Decomposition n)
    {C₁ C₂ : Finset (Finset ℕ)}
    (hC₁ : C₁ ∈ D.chains) (hC₂ : C₂ ∈ D.chains)
    {A : Finset ℕ}
    (hA₁ :
      A ∈ longCarrier n C₁ ∨ A ∈ shortCarrier n C₁)
    (hA₂ :
      A ∈ longCarrier n C₂ ∨ A ∈ shortCarrier n C₂) :
    C₁ = C₂ := by
  have hs₁ := D.chain_spec C₁ hC₁
  have hs₂ := D.chain_spec C₂ hC₂
  have he₁ : A.erase n ∈ C₁ := hA₁.elim
    (erase_mem_of_mem_long hs₁) (erase_mem_of_mem_short hs₁)
  have he₂ : A.erase n ∈ C₂ := hA₂.elim
    (erase_mem_of_mem_long hs₂) (erase_mem_of_mem_short hs₂)
  have hsub : A.erase n ⊆ Finset.range n := hs₁.1 _ he₁
  exact (D.existsUnique_mem (A.erase n) hsub).unique
    ⟨hC₁, he₁⟩ ⟨hC₂, he₂⟩

theorem nextCarrier_eq_long_or_short
    {n : ℕ} (D : Decomposition n)
    {C : Finset (Finset ℕ)} (hCD : C ∈ D.chains)
    {A : Finset ℕ} {C' : Finset (Finset ℕ)}
    (hAC : A ∈ longCarrier n C ∨ A ∈ shortCarrier n C)
    (hC'next : C' ∈ nextChains D) (hAC' : A ∈ C') :
    C' = longCarrier n C ∨ C' = shortCarrier n C := by
  rcases hC'next with ⟨D₀, hD₀, rfl⟩ |
      ⟨D₀, ⟨hD₀, -⟩, rfl⟩
  · have heq := origin_eq_of_common_member D hCD hD₀ hAC
      (Or.inl hAC')
    subst D₀
    exact Or.inl rfl
  · have heq := origin_eq_of_common_member D hCD hD₀ hAC
      (Or.inr hAC')
    subst D₀
    exact Or.inr rfl

noncomputable def nextDecomposition
    {n : ℕ} (D : Decomposition n) :
    Decomposition (n + 1) where
  chains := nextChains D
  finite_chains := nextChains_finite D
  chain_spec := fun _ h => nextChains_chain_spec D h
  existsUnique_mem := by
    intro A hArange
    let A₀ := A.erase n
    have hA₀range : A₀ ⊆ Finset.range n :=
      erase_subset_range hArange
    obtain ⟨C, hC, hCunique⟩ :=
      D.existsUnique_mem A₀ hA₀range
    have hCD : C ∈ D.chains := hC.1
    have hA₀C : A₀ ∈ C := hC.2
    have hCsym := D.chain_spec C hCD
    by_cases hnA : n ∈ A
    · by_cases htop : A₀ = chainTop n C
      · have hAlong : A ∈ longCarrier n C := by
          rw [mem_longCarrier_iff]
          left
          rw [← htop]
          exact (insert_erase_new hnA).symm
        refine
          ⟨longCarrier n C,
            ⟨Or.inl ⟨C, hCD, rfl⟩, hAlong⟩, ?_⟩
        intro C' hC'
        rcases nextCarrier_eq_long_or_short D hCD
            (Or.inl hAlong) hC'.1 hC'.2 with h | h
        · exact h
        · exfalso
          subst C'
          exact (Finset.disjoint_left.mp
            (long_short_disjoint hCsym)) hAlong hC'.2
      · have hsplit : 2 * chainLow n C < n := by
          have hl := (chainLow_card_bounds hCsym hA₀C).1
          have hu := mem_ne_top_card_lt hCsym hA₀C htop
          omega
        have hAshort : A ∈ shortCarrier n C := by
          rw [mem_shortCarrier_iff]
          exact
            ⟨A₀, hA₀C, htop,
              insert_erase_new hnA⟩
        refine
          ⟨shortCarrier n C,
            ⟨Or.inr ⟨C, ⟨hCD, hsplit⟩, rfl⟩, hAshort⟩, ?_⟩
        intro C' hC'
        rcases nextCarrier_eq_long_or_short D hCD
            (Or.inr hAshort) hC'.1 hC'.2 with h | h
        · exfalso
          subst C'
          exact (Finset.disjoint_left.mp
            (long_short_disjoint hCsym)) hC'.2 hAshort
        · exact h
    · have hAerase : A₀ = A := by
        dsimp [A₀]
        exact Finset.erase_eq_of_notMem hnA
      have hAlong : A ∈ longCarrier n C := by
        rw [mem_longCarrier_iff]
        exact Or.inr (hAerase ▸ hA₀C)
      refine
        ⟨longCarrier n C,
          ⟨Or.inl ⟨C, hCD, rfl⟩, hAlong⟩, ?_⟩
      intro C' hC'
      rcases nextCarrier_eq_long_or_short D hCD
          (Or.inl hAlong) hC'.1 hC'.2 with h | h
      · exact h
      · exfalso
        subst C'
        exact hnA (mem_short_has_new hC'.2)

def zeroDecomposition : Decomposition 0 where
  chains := {({∅} : Finset (Finset ℕ))}
  finite_chains := Set.finite_singleton _
  chain_spec := by
    intro C hC
    simp only [Set.mem_singleton_iff] at hC
    subst C
    refine ⟨?_, ?_, ⟨0, by simp, ?_, ?_⟩⟩
    · simp
    · simp
    · simp
    · intro r hr₀ hr₁
      have : r = 0 := by omega
      subst r
      exact ⟨∅, by simp, by simp⟩
  existsUnique_mem := by
    intro A hA
    have hAempty : A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have := Finset.mem_range.mp (hA hx)
      omega
    subst A
    refine ⟨{∅}, by simp, ?_⟩
    intro C hC
    simpa using hC.1

noncomputable def rangeDecomposition : ∀ n : ℕ, Decomposition n
  | 0 => zeroDecomposition
  | n + 1 => nextDecomposition (rangeDecomposition n)

theorem chainLow_le_half
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C) :
    chainLow n C ≤ n / 2 := by
  have := chainLow_twice_le hC
  omega

theorem half_le_chainHigh
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C) :
    n / 2 ≤ n - chainLow n C := by
  have := chainLow_twice_le hC
  omega

noncomputable def chainMiddle
    (n : ℕ) (C : Finset (Finset ℕ)) : Finset ℕ :=
  if h : ∃ A ∈ C, A.card = n / 2 then
    Classical.choose h
  else
    ∅

theorem chainMiddle_spec
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C) :
    chainMiddle n C ∈ C ∧ (chainMiddle n C).card = n / 2 := by
  have hex := chainLow_rank_exists hC
    (chainLow_le_half hC) (half_le_chainHigh hC)
  rw [chainMiddle, dif_pos hex]
  exact Classical.choose_spec hex

theorem eq_of_mem_chain_of_card_eq
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C)
    {A B : Finset ℕ} (hAC : A ∈ C) (hBC : B ∈ C)
    (hcard : A.card = B.card) :
    A = B := by
  rcases hC.2.1 A hAC B hBC with h | h
  · exact Finset.eq_of_subset_of_card_le h (by omega)
  · exact (Finset.eq_of_subset_of_card_le h (by omega)).symm

theorem chainMiddle_unique
    {n : ℕ} {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain n C)
    {A : Finset ℕ} (hAC : A ∈ C) (hcard : A.card = n / 2) :
    chainMiddle n C = A := by
  exact eq_of_mem_chain_of_card_eq hC
    (chainMiddle_spec hC).1 hAC
    ((chainMiddle_spec hC).2.trans hcard.symm)

/-- Every symmetric-chain decomposition has exactly the central binomial
number of chains: each chain contains one and only one middle-rank set. -/
theorem decomposition_ncard
    {n : ℕ} (D : Decomposition n) :
    D.chains.ncard = Nat.choose n (n / 2) := by
  let middleLayer : Set (Finset ℕ) :=
    ((Finset.range n).powersetCard (n / 2) : Finset (Finset ℕ))
  have hcongr :
      D.chains.ncard = middleLayer.ncard := by
    apply Set.ncard_congr
      (fun C _ => chainMiddle n C)
    · intro C hCD
      have hC := D.chain_spec C hCD
      change chainMiddle n C ∈
        (Finset.range n).powersetCard (n / 2)
      rw [Finset.mem_powersetCard]
      exact
        ⟨hC.1 _ (chainMiddle_spec hC).1,
          (chainMiddle_spec hC).2⟩
    · intro C₁ C₂ hC₁ hC₂ heq
      have hs₁ := D.chain_spec C₁ hC₁
      have hs₂ := D.chain_spec C₂ hC₂
      have hm₁ := (chainMiddle_spec hs₁).1
      have hm₂ := (chainMiddle_spec hs₂).1
      exact
        (D.existsUnique_mem (chainMiddle n C₁)
          (hs₁.1 _ hm₁)).unique
          ⟨hC₁, hm₁⟩
          ⟨hC₂, heq ▸ hm₂⟩
    · intro A hAmid
      change A ∈ (Finset.range n).powersetCard (n / 2) at hAmid
      rw [Finset.mem_powersetCard] at hAmid
      obtain ⟨C, hC, -⟩ := D.existsUnique_mem A hAmid.1
      refine ⟨C, hC.1, ?_⟩
      exact chainMiddle_unique (D.chain_spec C hC.1)
        hC.2 hAmid.2
  calc
    D.chains.ncard = middleLayer.ncard := hcongr
    _ = ((Finset.range n).powersetCard (n / 2)).card := by
      exact Set.ncard_coe_finset _
    _ = Nat.choose n (n / 2) := by
      rw [Finset.card_powersetCard, Finset.card_range]

/-- Exact source Fact 4.6 on the canonical `n`-element ground set. -/
theorem symmetric_chain_decomposition_range (n : ℕ) :
    ∃ D : Decomposition n,
      D.chains.ncard = Nat.choose n (n / 2) :=
  ⟨rangeDecomposition n, decomposition_ncard (rangeDecomposition n)⟩

/-! ## Relabeling to the finite signature type used in Lemma 4.8 -/

/-- Symmetric saturated chain in the Boolean lattice of a finite type. -/
def IsFintypeSymmetricChain
    (α : Type*) [Fintype α] (C : Finset (Finset α)) : Prop :=
  (∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A) ∧
  ∃ low,
    2 * low ≤ Fintype.card α ∧
    (∀ A ∈ C,
      low ≤ A.card ∧ A.card ≤ Fintype.card α - low) ∧
    ∀ r, low ≤ r → r ≤ Fintype.card α - low →
      ∃ A ∈ C, A.card = r

/-- Exact finite-type form of a Boolean-lattice symmetric-chain
decomposition. -/
structure FintypeDecomposition (α : Type*) [Fintype α] where
  chains : Set (Finset (Finset α))
  finite_chains : chains.Finite
  chain_spec : ∀ C ∈ chains, IsFintypeSymmetricChain α C
  existsUnique_mem :
    ∀ A : Finset α,
      ∃! C : Finset (Finset α), C ∈ chains ∧ A ∈ C

noncomputable def codeEmbedding
    (α : Type*) [Fintype α] : α ↪ ℕ :=
  (Fintype.equivFin α).toEmbedding.trans Fin.valEmbedding

theorem codeEmbedding_univ
    (α : Type*) [Fintype α] :
    (Finset.univ.map (codeEmbedding α)) =
      Finset.range (Fintype.card α) := by
  classical
  ext x
  constructor
  · intro hx
    rw [Finset.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    exact Finset.mem_range.mpr
      ((Fintype.equivFin α a).isLt)
  · intro hx
    let i : Fin (Fintype.card α) :=
      ⟨x, Finset.mem_range.mp hx⟩
    let a : α := (Fintype.equivFin α).symm i
    rw [Finset.mem_map]
    refine ⟨a, Finset.mem_univ _, ?_⟩
    change ((Fintype.equivFin α) a).val = x
    simp [a, i]

noncomputable def decodeFinset
    (α : Type*) [Fintype α] (B : Finset ℕ) : Finset α :=
  B.preimage (codeEmbedding α) (codeEmbedding α).injective.injOn

@[simp] theorem mem_decodeFinset_iff
    {α : Type*} [Fintype α] {B : Finset ℕ} {a : α} :
    a ∈ decodeFinset α B ↔ codeEmbedding α a ∈ B :=
  Finset.mem_preimage

theorem decode_map_code
    {α : Type*} [Fintype α] (A : Finset α) :
    decodeFinset α (A.map (codeEmbedding α)) = A := by
  exact Finset.preimage_map _ _

theorem map_decode_of_subset
    {α : Type*} [Fintype α] {B : Finset ℕ}
    (hB : B ⊆ Finset.range (Fintype.card α)) :
    (decodeFinset α B).map (codeEmbedding α) = B := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact (mem_decodeFinset_iff.mp ha)
  · intro x hx
    have hxrange : x ∈
        Finset.univ.map (codeEmbedding α) := by
      rw [codeEmbedding_univ]
      exact hB hx
    rw [Finset.mem_map] at hxrange
    obtain ⟨a, -, ha⟩ := hxrange
    rw [Finset.mem_map]
    exact
      ⟨a, mem_decodeFinset_iff.mpr (by simpa [ha] using hx), ha⟩

theorem decode_card_of_subset
    {α : Type*} [Fintype α] {B : Finset ℕ}
    (hB : B ⊆ Finset.range (Fintype.card α)) :
    (decodeFinset α B).card = B.card := by
  rw [← Finset.card_map (codeEmbedding α),
    map_decode_of_subset hB]

theorem decode_subset_decode
    {α : Type*} [Fintype α] {A B : Finset ℕ}
    (hA : A ⊆ Finset.range (Fintype.card α))
    (hB : B ⊆ Finset.range (Fintype.card α))
    (hAB : A ⊆ B) :
    decodeFinset α A ⊆ decodeFinset α B := by
  intro x hx
  rw [mem_decodeFinset_iff] at hx ⊢
  exact hAB hx

theorem decode_injective_on_range
    {α : Type*} [Fintype α] {A B : Finset ℕ}
    (hA : A ⊆ Finset.range (Fintype.card α))
    (hB : B ⊆ Finset.range (Fintype.card α))
    (h : decodeFinset α A = decodeFinset α B) :
    A = B := by
  rw [← map_decode_of_subset hA, ← map_decode_of_subset hB, h]

noncomputable def decodeCarrier
    (α : Type*) [Fintype α] (C : Finset (Finset ℕ)) :
    Finset (Finset α) := by
  classical
  exact C.image (decodeFinset α)

theorem mem_decodeCarrier_iff
    {α : Type*} [Fintype α]
    {C : Finset (Finset ℕ)} {A : Finset α} :
    A ∈ decodeCarrier α C ↔
      ∃ B ∈ C, decodeFinset α B = A := by
  classical
  simp [decodeCarrier]

theorem decodeCarrier_injective_on_decomposition
    {α : Type*} [Fintype α]
    {D : Decomposition (Fintype.card α)}
    {C₁ C₂ : Finset (Finset ℕ)}
    (hC₁ : C₁ ∈ D.chains) (hC₂ : C₂ ∈ D.chains)
    (h : decodeCarrier α C₁ = decodeCarrier α C₂) :
    C₁ = C₂ := by
  apply Finset.Subset.antisymm
  · intro B hBC₁
    have hs₁ := D.chain_spec C₁ hC₁
    have hdec :
        decodeFinset α B ∈ decodeCarrier α C₁ :=
      (mem_decodeCarrier_iff).2 ⟨B, hBC₁, rfl⟩
    rw [h, mem_decodeCarrier_iff] at hdec
    obtain ⟨B₂, hB₂C₂, hB₂⟩ := hdec
    have hs₂ := D.chain_spec C₂ hC₂
    have heq := decode_injective_on_range
      (hs₁.1 B hBC₁) (hs₂.1 B₂ hB₂C₂) hB₂.symm
    simpa [heq] using hB₂C₂
  · intro B hBC₂
    have hs₁ := D.chain_spec C₁ hC₁
    have hs₂ := D.chain_spec C₂ hC₂
    have hdec :
        decodeFinset α B ∈ decodeCarrier α C₂ :=
      (mem_decodeCarrier_iff).2 ⟨B, hBC₂, rfl⟩
    rw [← h, mem_decodeCarrier_iff] at hdec
    obtain ⟨B₁, hB₁C₁, hB₁⟩ := hdec
    have heq := decode_injective_on_range
      (hs₂.1 B hBC₂) (hs₁.1 B₁ hB₁C₁) hB₁.symm
    simpa [heq] using hB₁C₁

noncomputable def decodeChains
    (α : Type*) [Fintype α]
    (D : Decomposition (Fintype.card α)) :
    Set (Finset (Finset α)) :=
  decodeCarrier α '' D.chains

theorem decodeChains_finite
    (α : Type*) [Fintype α]
    (D : Decomposition (Fintype.card α)) :
    (decodeChains α D).Finite :=
  D.finite_chains.image _

theorem decodeChains_ncard
    (α : Type*) [Fintype α]
    (D : Decomposition (Fintype.card α)) :
    (decodeChains α D).ncard = D.chains.ncard := by
  apply Set.ncard_image_of_injOn
  intro C₁ hC₁ C₂ hC₂ h
  exact decodeCarrier_injective_on_decomposition hC₁ hC₂ h

theorem decodeCarrier_symmetric
    {α : Type*} [Fintype α]
    {C : Finset (Finset ℕ)}
    (hC : IsSymmetricChain (Fintype.card α) C) :
    IsFintypeSymmetricChain α (decodeCarrier α C) := by
  refine ⟨?_, ?_⟩
  · intro A hA B hB
    rw [mem_decodeCarrier_iff] at hA hB
    obtain ⟨A₀, hA₀C, rfl⟩ := hA
    obtain ⟨B₀, hB₀C, rfl⟩ := hB
    rcases hC.2.1 A₀ hA₀C B₀ hB₀C with h | h
    · exact Or.inl <| decode_subset_decode
        (hC.1 A₀ hA₀C) (hC.1 B₀ hB₀C) h
    · exact Or.inr <| decode_subset_decode
        (hC.1 B₀ hB₀C) (hC.1 A₀ hA₀C) h
  · obtain ⟨low, hlow, hbounds, hranks⟩ := hC.2.2
    refine ⟨low, hlow, ?_, ?_⟩
    · intro A hA
      rw [mem_decodeCarrier_iff] at hA
      obtain ⟨A₀, hA₀C, rfl⟩ := hA
      rw [decode_card_of_subset (hC.1 A₀ hA₀C)]
      exact hbounds A₀ hA₀C
    · intro r hlr hur
      obtain ⟨A₀, hA₀C, hcard⟩ := hranks r hlr hur
      refine
        ⟨decodeFinset α A₀,
          (mem_decodeCarrier_iff).2 ⟨A₀, hA₀C, rfl⟩, ?_⟩
      rw [decode_card_of_subset (hC.1 A₀ hA₀C)]
      exact hcard

theorem map_code_subset_range
    {α : Type*} [Fintype α] (A : Finset α) :
    A.map (codeEmbedding α) ⊆ Finset.range (Fintype.card α) := by
  classical
  intro x hx
  rw [Finset.mem_map] at hx
  obtain ⟨a, -, rfl⟩ := hx
  exact Finset.mem_range.mpr (Fintype.equivFin α a).isLt

noncomputable def fintypeDecomposition
    (α : Type*) [Fintype α] :
    FintypeDecomposition α where
  chains := decodeChains α
    (rangeDecomposition (Fintype.card α))
  finite_chains := decodeChains_finite α _
  chain_spec := by
    intro C hC
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    exact decodeCarrier_symmetric
      ((rangeDecomposition (Fintype.card α)).chain_spec C₀ hC₀)
  existsUnique_mem := by
    intro A
    let D := rangeDecomposition (Fintype.card α)
    let A₀ := A.map (codeEmbedding α)
    have hA₀range : A₀ ⊆
        Finset.range (Fintype.card α) :=
      map_code_subset_range A
    obtain ⟨C₀, hC₀, hC₀unique⟩ :=
      D.existsUnique_mem A₀ hA₀range
    have hC₀D : C₀ ∈ D.chains := hC₀.1
    have hA₀C : A₀ ∈ C₀ := hC₀.2
    have hAdecoded : A ∈ decodeCarrier α C₀ := by
      rw [mem_decodeCarrier_iff]
      exact ⟨A₀, hA₀C, decode_map_code A⟩
    refine
      ⟨decodeCarrier α C₀,
        ⟨⟨C₀, hC₀D, rfl⟩, hAdecoded⟩, ?_⟩
    intro C hC
    obtain ⟨C₁, hC₁D, rfl⟩ := hC.1
    rw [mem_decodeCarrier_iff] at hC
    obtain ⟨B, hBC₁, hBdecode⟩ := hC.2
    have hBvalid :=
      D.chain_spec C₁ hC₁D |>.1 B hBC₁
    have hBcode :
        B = A₀ := by
      calc
        B = (decodeFinset α B).map (codeEmbedding α) :=
          (map_decode_of_subset hBvalid).symm
        _ = A.map (codeEmbedding α) :=
          congrArg (fun S => S.map (codeEmbedding α)) hBdecode
        _ = A₀ := rfl
    have hCeq : C₁ = C₀ :=
      hC₀unique C₁ ⟨hC₁D, hBcode ▸ hBC₁⟩
    exact congrArg (decodeCarrier α) hCeq

theorem fintypeDecomposition_ncard
    (α : Type*) [Fintype α] :
    (fintypeDecomposition α).chains.ncard =
      Nat.choose (Fintype.card α) (Fintype.card α / 2) := by
  change
    (decodeChains α
      (rangeDecomposition (Fintype.card α))).ncard =
        Nat.choose (Fintype.card α) (Fintype.card α / 2)
  rw [decodeChains_ncard]
  exact decomposition_ncard _

/-- Literal finite-type form used by the relative-signature argument in
source Lemma 4.8. -/
theorem symmetric_chain_decomposition_fintype
    (α : Type*) [Fintype α] :
    ∃ D : FintypeDecomposition α,
      D.chains.ncard =
        Nat.choose (Fintype.card α) (Fintype.card α / 2) :=
  ⟨fintypeDecomposition α, fintypeDecomposition_ncard α⟩

end GenLimit.BoundedMemory
