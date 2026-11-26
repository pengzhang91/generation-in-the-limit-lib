import GenLimit.Support.ClassIntersection
import GenLimit.Core.ClassGeneration
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-! # Finite-sample generation and finite intersections

Definition 2.2 gives the generator the set of observed words. Proposition
2.3 identifies finite intersections as the obstructions at a fixed sample
size. The alphabet of the paper gives a nonempty universe of words. -/
namespace GenLimit.ComplexityBarriers
open Generic Support
open scoped Classical
noncomputable section

def MGeneratable (H : LanguageClass α) (m : ℕ) : Prop :=
  ∃ G : Finset α → α, ∀ L ∈ H, ∀ X : Finset α, (X : Set α) ⊆ L →
    m ≤ X.card → G X ∈ L \ (X : Set α)

theorem intersection_obstruction {H S : LanguageClass α} (hS : S ⊆ H) (hNE : S.Nonempty)
    (hfin : (classIntersection S).Finite) {m : ℕ} (hm : m ≤ (classIntersection S).ncard) :
    ¬ MGeneratable H m := by
  rintro ⟨G,hG⟩
  let X := hfin.toFinset
  have he : (X : Set α) = classIntersection S := hfin.coe_toFinset
  have hc : m ≤ X.card := by simpa [X,Set.ncard_eq_toFinset_card _ hfin] using hm
  have good (L) (hL : L ∈ S) : G X ∈ L \ (X : Set α) :=
    hG L (hS hL) X (he ▸ classIntersection_subset_of_mem hL) hc
  have hin : G X ∈ classIntersection S := fun L hL ↦ (good L hL).1
  obtain ⟨L,hL⟩ := hNE
  exact (good L hL).2 (he ▸ hin)

theorem mGeneratable_of_small_intersections [Nonempty α] {H : LanguageClass α} {m : ℕ}
    (h : ∀ S ⊆ H, S.Nonempty → (classIntersection S).Finite → (classIntersection S).ncard < m) :
    MGeneratable H m := by
  let G := fun X : Finset α ↦ if hx : (commonCore H X \ (X : Set α)).Nonempty then hx.choose else Classical.arbitrary α
  refine ⟨G,fun L hL X hX hm ↦ ?_⟩
  have hl : L ∈ versionSpace H X := ⟨hL,hX⟩
  have hf : (commonCore H X).Infinite := by
    intro hf
    have hh := h (versionSpace H X) (fun _ hi ↦ hi.1) ⟨L,hl⟩ hf
    have hc := Set.ncard_le_ncard (sample_subset_commonCore (H := H) (S := X)) hf
    rw [Set.ncard_coe_finset] at hc
    change (commonCore H X).ncard < m at hh
    omega
  have hx := (hf.diff X.finite_toSet).nonempty
  have hg : G X ∈ commonCore H X \ (X : Set α) := by simpa [G,hx] using hx.choose_spec
  exact ⟨hg.1 L hl,hg.2⟩

/-- Proposition 2.3 with Core's version space and common core. -/
theorem not_mGeneratable_iff [Nonempty α] (H : LanguageClass α) (m : ℕ) :
    ¬ MGeneratable H m ↔ ∃ S ⊆ H, S.Nonempty ∧ (classIntersection S).Finite ∧ m ≤ (classIntersection S).ncard := by
  constructor
  · intro hn
    by_contra! h
    exact hn (mGeneratable_of_small_intersections h)
  · rintro ⟨S,hS,hNE,hfin,hm⟩
    exact intersection_obstruction hS hNE hfin hm

theorem pair_obstruction {L K : Set α} {m : ℕ} (hf : (L ∩ K).Finite) (hm : m ≤ (L ∩ K).ncard) :
    ¬ MGeneratable {L,K} m := by
  have he : classIntersection ({L,K} : LanguageClass α) = L ∩ K := by
    ext x; simp [classIntersection]
  apply intersection_obstruction (S := {L,K}) (Set.Subset.refl _) (Set.insert_nonempty ..) (he ▸ hf) (he ▸ hm)

/-- All words of length strictly below n. -/
def shortWords (α : Type*) [Fintype α] : ℕ → Finset (List α)
  | 0 => ∅
  | n+1 => insert [] ((Finset.univ.product (shortWords α n)).image fun aw ↦ aw.1 :: aw.2)

@[simp] theorem mem_shortWords [Fintype α] (w : List α) (n : ℕ) :
    w ∈ shortWords α n ↔ w.length < n := by
  induction n generalizing w with
  | zero => simp [shortWords]
  | succ n ih => cases w <;> simp [shortWords,ih]

theorem shortWords_card_lt [Fintype α] (ha : 2 ≤ Fintype.card α) (n : ℕ) :
    (shortWords α n).card < (Fintype.card α)^n := by
  induction n with
  | zero => simp [shortWords]
  | succ n ih =>
    have hin := Finset.card_insert_le [] ((Finset.univ.product (shortWords α n)).image fun aw ↦ aw.1 :: aw.2)
    have him := Finset.card_image_le (s := Finset.univ.product (shortWords α n)) (f := fun aw ↦ aw.1 :: aw.2)
    have hprod : (Finset.univ.product (shortWords α n) : Finset (α × List α)).card = Fintype.card α * (shortWords α n).card := by apply Finset.card_product (s := Finset.univ) (t := shortWords α n)
    rw [hprod] at him
    rw [shortWords,pow_succ]
    have hm := Nat.mul_le_mul_left (Fintype.card α) (Nat.succ_le_of_lt ih)
    nlinarith

theorem ncard_lt_of_length_lt [Fintype α] (ha : 2 ≤ Fintype.card α) {L : Set (List α)} {n : ℕ}
    (h : ∀ w ∈ L, w.length < n) : L.ncard < (Fintype.card α)^n := by
  have hsub : L ⊆ (shortWords α n : Set (List α)) := fun w hw ↦ (mem_shortWords w n).mpr (h w hw)
  have hc := Set.ncard_le_ncard hsub (shortWords α n).finite_toSet
  rw [Set.ncard_coe_finset] at hc
  exact hc.trans_lt (shortWords_card_lt ha n)

end
end GenLimit.ComplexityBarriers
