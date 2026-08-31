import GenLimit.Core.GenericGeneration
import Mathlib.Data.Set.Countable

/-!
# Presentations of countable languages

Paper-independent constructions for exact positive presentations.  The
prefix-completion operation is useful when a source definition quantifies
over exact presentations while a library definition quantifies over arbitrary
positive streams.
-/

namespace GenLimit.Support

/-- An exact positive presentation with no repeated examples.  This neutral
predicate is shared by papers whose source convention requires injective
presentations. -/
def InjectivePresentation
    (stream : GenLimit.Generic.Stream α) (L : Set α) : Prop :=
  Function.Injective stream ∧ GenLimit.Generic.Presents stream L

theorem InjectivePresentation.streamIn
    {stream : GenLimit.Generic.Stream α} {L : Set α}
    (h : InjectivePresentation stream L) :
    GenLimit.Generic.StreamIn stream L :=
  GenLimit.Generic.streamIn_of_presents h.2

/-- A fixed exact positive presentation of a nonempty language over a
countable example space. -/
noncomputable def exactPresentation [Countable α]
    (L : Set α) (hL : L.Nonempty) : GenLimit.Generic.Stream α := by
  classical
  have hcount : L.Countable := Set.countable_univ.mono (Set.subset_univ L)
  let enumerate : ℕ → L := Classical.choose (hcount.exists_surjective hL)
  exact fun n ↦ enumerate n

theorem exactPresentation_presents [Countable α]
    (L : Set α) (hL : L.Nonempty) :
    GenLimit.Generic.Presents (exactPresentation L hL) L := by
  classical
  have hcount : L.Countable := Set.countable_univ.mono (Set.subset_univ L)
  let henumerate := Classical.choose_spec (hcount.exists_surjective hL)
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    exact (Classical.choose (hcount.exists_surjective hL) n).property
  · intro x hx
    obtain ⟨n, hn⟩ := henumerate ⟨x, hx⟩
    exact ⟨n, congrArg Subtype.val hn⟩

/-- Complete a finite positive history to an exact presentation of `L`.
The proof that the history lies in `L` is intentionally an argument of the
construction, so callers cannot manufacture an invalid completion. -/
noncomputable def prefixThenPresentation [Countable α]
    {t : ℕ} (xs : Fin t → α) (L : Set α)
    (_hxs : ∀ i, xs i ∈ L) (hL : L.Nonempty) :
    GenLimit.Generic.Stream α :=
  fun n ↦ if hn : n < t then xs ⟨n, hn⟩
    else exactPresentation L hL (n - t)

theorem prefixThenPresentation_apply_of_lt [Countable α]
    {t : ℕ} (xs : Fin t → α) (L : Set α)
    (hxs : ∀ i, xs i ∈ L) (hL : L.Nonempty)
    {n : ℕ} (hn : n < t) :
    prefixThenPresentation xs L hxs hL n = xs ⟨n, hn⟩ := by
  simp [prefixThenPresentation, hn]

theorem prefixThenPresentation_agrees [Countable α]
    {t : ℕ} (xs : Fin t → α) (L : Set α)
    (hxs : ∀ i, xs i ∈ L) (hL : L.Nonempty)
    {n : ℕ} (hn : n < t) :
    prefixThenPresentation xs L hxs hL n = xs ⟨n, hn⟩ := by
  exact prefixThenPresentation_apply_of_lt xs L hxs hL hn

theorem prefixThenPresentation_presents [Countable α]
    {t : ℕ} (xs : Fin t → α) (L : Set α)
    (hxs : ∀ i, xs i ∈ L) (hL : L.Nonempty) :
    GenLimit.Generic.Presents (prefixThenPresentation xs L hxs hL) L := by
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    by_cases hn : n < t
    · simpa [prefixThenPresentation, hn] using hxs ⟨n, hn⟩
    · have hmem : exactPresentation L hL (n - t) ∈ L := by
        exact GenLimit.Generic.streamIn_of_presents
          (exactPresentation_presents L hL) ⟨n - t, rfl⟩
      simpa [prefixThenPresentation, hn] using hmem
  · intro x hx
    rw [← exactPresentation_presents L hL] at hx
    obtain ⟨k, hk⟩ := hx
    refine ⟨t + k, ?_⟩
    simp [prefixThenPresentation, hk]

/-- Every finite subset of an exactly presented language is contained in all
sufficiently late samples. This is the eventual form of the generic Core
progress theorem. -/
theorem finite_eventually_subset_sample
    {stream : GenLimit.Generic.Stream α} {L : GenLimit.Generic.Language α}
    (hP : GenLimit.Generic.Presents stream L)
    (F : Finset α) (hF : (↑F : Set α) ⊆ L) :
    ∃ T, ∀ t, T ≤ t → F ⊆ GenLimit.Generic.sample stream t := by
  obtain ⟨T, hT⟩ :=
    GenLimit.Generic.finset_eventually_subset_sample hP F hF
  refine ⟨T, ?_⟩
  intro t hTt u hu
  exact GenLimit.Generic.sample_mono hTt (hT hu)

end GenLimit.Support
