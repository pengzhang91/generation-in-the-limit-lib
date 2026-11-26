import GenLimit.Paper25_PrivateGenerationAndIdentification.MarginalPacking
import GenLimit.Paper25_PrivateGenerationAndIdentification.ClosureGeneration
import GenLimit.Paper12_NoiseLossAndFeedback.InfiniteOmissions
import Mathlib.Logic.Denumerable

/-! Hard families on h independent bit coordinates, with d common words.
Every finite intersection is exactly the common set. An optional extra
universal language allows odd as well as even collection sizes. -/
namespace GenLimit.PrivateLimit.Packing

open Set
open scoped Classical
noncomputable section

def encoding (h : ℕ) : Cube h × ℕ ≃ ℕ := @Denumerable.eqv _ (Classical.choice (nonempty_denumerable _))

def word {h : ℕ} (d : ℕ) (z : Cube h) (n : ℕ) := d+encoding h (z,n)
def decode (h d x : ℕ) : Cube h := ((encoding h).symm (x-d)).1

@[simp] theorem decode_word {h : ℕ} (d : ℕ) (z : Cube h) (n : ℕ) : decode h d (word d z n) = z := by
  simp [decode,word]

theorem word_injective {h : ℕ} (d : ℕ) (z : Cube h) : Function.Injective (word d z) := by
  intro a b eq
  exact congrArg Prod.snd ((encoding h).injective (Nat.add_left_cancel eq))

def language {h : ℕ} (d : ℕ) (i : Fin h × Bool) : Set ℕ := {x | x < d ∨ decode h d x i.1 = i.2}

@[simp] theorem word_mem {h d : ℕ} (z : Cube h) (n : ℕ) (i : Fin h × Bool) :
    word d z n ∈ language d i ↔ z i.1 = i.2 := by
  change word d z n < d ∨ _ ↔ _
  simp [word,Nat.not_lt_of_ge (Nat.le_add_right d _),decode]

theorem language_injective {h : ℕ} (d : ℕ) : Function.Injective (language (h := h) d) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ eq
  have test (z : Cube h) : z i = b ↔ z j = c := by
    simpa only [word_mem] using (show (word d z 0 ∈ language d (i,b)) ↔
      (word d z 0 ∈ language d (j,c)) by rw [eq])
  have sameBit := (test (fun _ => b)).mp rfl
  have sameIndex : i = j := by
    by_contra ne
    let z := Function.update (fun _ : Fin h => !c) i b
    have impossible := (test z).mp (Function.update_self ..)
    simp [z,Function.update_of_ne (Ne.symm ne)] at impossible
  exact Prod.ext sameIndex sameBit

theorem proper_language {h d : ℕ} (i : Fin h × Bool) : language d i ≠ univ := by
  intro all
  let z : Cube h := fun _ => !i.2
  have mem : word d z 0 ∈ language d i := all.symm ▸ mem_univ _
  simpa [z] using (word_mem z 0 i).mp mem

def family (h d : ℕ) (odd : Bool) : Set (Set ℕ) :=
  if odd then insert univ (range (language (h := h) d)) else range (language (h := h) d)

theorem language_mem (h d : ℕ) (odd : Bool) (i : Fin h × Bool) : language d i ∈ family h d odd := by
  cases odd <;> simp [family]

theorem family_finite (h d : ℕ) (odd : Bool) : (family h d odd).Finite := by
  cases odd <;> simp [family,finite_range]

theorem family_size (h d : ℕ) (odd : Bool) : (family h d odd).ncard = 2*h + (if odd then 1 else 0) := by
  have proper : univ ∉ range (language (h := h) d) := by rintro ⟨i,h⟩; exact proper_language i h
  cases odd <;> simp [family,ncard_insert_of_notMem proper,ncard_range_of_injective (language_injective d),
    Nat.card_eq_fintype_card,Nat.mul_comm]

theorem infinite_language {h : ℕ} (d : ℕ) (i : Fin h × Bool) : (language d i).Infinite := by
  let z : Cube h := fun _ => i.2
  apply (infinite_range_of_injective (word_injective d z)).mono
  rintro _ ⟨n,rfl⟩; exact (word_mem z n i).mpr rfl

theorem family_infinite (h d : ℕ) (odd : Bool) {L : Set ℕ} (mem : L ∈ family h d odd) : L.Infinite := by
  cases odd <;> simp only [family,Bool.false_eq_true,if_false,if_true,mem_insert_iff] at mem
  · obtain ⟨i,rfl⟩ := mem; exact infinite_language d i
  · obtain rfl | ⟨i,rfl⟩ := mem
    · exact infinite_univ
    · exact infinite_language d i

private theorem common {h d : ℕ} {odd : Bool} {V : Set (Set ℕ)} (sub : V ⊆ family h d odd) :
    Iio d ⊆ ⋂₀ V := by
  intro x hx L hL
  have mem := sub hL
  cases odd <;> simp only [family,Bool.false_eq_true,if_false,if_true,mem_insert_iff] at mem
  · obtain ⟨i,rfl⟩ := mem; exact Or.inl hx
  · obtain rfl | ⟨i,rfl⟩ := mem
    · trivial
    · exact Or.inl hx

private theorem column_inside {h d : ℕ} {odd : Bool} {V : Set (Set ℕ)} (sub : V ⊆ family h d odd)
    {x : ℕ} (hx : x ∈ ⋂₀ V) (large : d ≤ x) : range (word d (decode h d x)) ⊆ ⋂₀ V := by
  rintro _ ⟨n,rfl⟩ L hL
  have mem := sub hL
  have included := hx L hL
  have one (i : Fin h × Bool) (eq : language d i = L) : word d (decode h d x) n ∈ L := by
    subst L
    exact (word_mem _ _ _).mpr (included.resolve_left large.not_gt)
  cases odd <;> simp only [family,Bool.false_eq_true,if_false,if_true,mem_insert_iff] at mem
  · exact mem.elim one
  · exact mem.elim (fun e => e.symm ▸ mem_univ _) (fun r => r.elim one)

theorem family_bound (h d : ℕ) (odd : Bool) : SubcollectionClosureBound (family h d odd) d := by
  intro V sub fin
  have small : ⋂₀ V ⊆ Iio d := by
    intro x hx
    by_contra! large
    exact ((infinite_range_of_injective (word_injective d (decode h d x))).mono
      (column_inside sub hx (by simpa using large))) fin
  simpa [←Finset.coe_range] using ncard_le_ncard small (finite_Iio d)

theorem full_intersection {h : ℕ} (pos : 0 < h) (d : ℕ) (odd : Bool) : ⋂₀ family h d odd = Iio d := by
  apply subset_antisymm _ (common Subset.rfl)
  intro x hx
  by_contra! large
  let i : Fin h := ⟨0,pos⟩
  let b := decode h d x i
  have mem := hx _ (language_mem h d odd (i,!b))
  have impossible : b = !b := mem.resolve_left (by simpa using large)
  exact (Bool.not_eq_self b).mp impossible.symm

/-- A fixed column supplies a legal injective partial text for every
target sharing one of its bit values. Every column starts with the same
d words in the same order. -/
def columnText {h : ℕ} (d : ℕ) (z : Cube h) (n : ℕ) := if n < d then n else word d z (n-d)

theorem column_injective {h : ℕ} (d : ℕ) (z : Cube h) : Function.Injective (columnText d z) := by
  intro a b eq
  by_cases ha : a < d <;> by_cases hb : b < d <;> simp [columnText,ha,hb] at eq
  · exact eq
  · unfold word at eq; omega
  · unfold word at eq; omega
  · have := word_injective d z eq; omega

theorem column_legal {h d : ℕ} (z : Cube h) (i : Fin h) : range (columnText d z) ⊆ language d (i,z i) := by
  rintro _ ⟨n,rfl⟩
  by_cases hn : n < d
  · rw [columnText,if_pos hn]; exact Or.inl hn
  · rw [columnText,if_neg hn]; exact (word_mem ..).mpr rfl

end
end GenLimit.PrivateLimit.Packing
