import GenLimit.Paper16_ComplexityBarriers.BlockCounters
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Lex

/-! # A binary family with double-exponential generation threshold

A token consists of a fixed-width binary address followed by one free bit.
Its last bit has no effect on a counter and different choices give distinct
words in the intersection. -/
namespace GenLimit.ComplexityBarriers.Blocks
open List
open scoped Classical
noncomputable section

abbrev Address (ℓ : ℕ) := List.Vector Bool ℓ

instance addressOrder (ℓ : ℕ) : LinearOrder (Address ℓ) :=
  LinearOrder.lift' (fun a ↦ a.val) Subtype.val_injective

abbrev Token (ℓ : ℕ) := Address ℓ × Bool

def bits (t : Token ℓ) : List Bool := t.1.val ++ [t.2]

def encode (ts : List (Token ℓ)) : List Bool := ts.flatMap bits

@[simp] theorem bits_length (t : Token ℓ) : (bits t).length = ℓ+1 := by simp [bits,t.1.property]

@[simp] theorem encode_length (ts : List (Token ℓ)) : (encode ts).length = (ℓ+1)*ts.length := by
  induction ts with
  | nil => simp [encode]
  | cons t ts ih =>
    change (bits t ++ encode ts).length = _
    simp only [List.length_append,bits_length,ih,List.length_cons,Nat.mul_succ]; omega

theorem encode_injective (ℓ : ℕ) : Function.Injective (encode (ℓ := ℓ)) := by
  intro u
  induction u with
  | nil =>
    intro v he
    have hh := congrArg List.length he
    simp only [encode_length,List.length_nil,Nat.mul_zero,eq_comm (a := 0),Nat.mul_eq_zero] at hh
    exact (List.length_eq_zero_iff.mp (hh.resolve_left (Nat.succ_ne_zero _))).symm
  | cons a u ih =>
    intro v he
    cases v with
    | nil => have hh := congrArg List.length he; simp at hh
    | cons b v =>
      obtain ⟨hh,hr⟩ := List.append_inj he ((bits_length a).trans (bits_length b).symm)
      obtain ⟨h₁,h₂⟩ := List.append_inj hh (a.1.property.trans b.1.property.symm)
      have h : a=b := Prod.ext (Subtype.ext h₁) (List.cons.inj h₂).1
      exact congrArg₂ List.cons h (ih hr)

def binaryLanguage (n : ℕ) (d : Address ℓ) : Set (List Bool) :=
  {w | ∃ ts : List (Token ℓ), encode ts = w ∧ Good n d (ts.map Prod.fst)}

@[simp] theorem mem_encoded (n : ℕ) (d : Address ℓ) (ts : List (Token ℓ)) :
    encode ts ∈ binaryLanguage n d ↔ Good n d (ts.map Prod.fst) := by
  exact ⟨fun ⟨v,hv,h⟩ ↦ encode_injective ℓ hv ▸ h,fun h ↦ ⟨ts,rfl,h⟩⟩

def family (ℓ n : ℕ) : Finset (Set (List Bool)) := Finset.univ.image (binaryLanguage (ℓ := ℓ) n)

private theorem language_injective (n ℓ : ℕ) : Function.Injective (binaryLanguage (ℓ := ℓ) n) := by
  intro d e he
  by_contra hn
  let ts := List.replicate (n+1) (d,false)
  have hmap : ts.map Prod.fst = List.replicate (n+1) d := by simp [ts]
  have hgood : encode ts ∈ binaryLanguage n e := by
    apply (mem_encoded ..).mpr
    exact ⟨0,run_absent n e _ (by simp [hmap,Ne.symm hn])⟩
  rw [←he,mem_encoded,hmap] at hgood
  obtain ⟨k,hk⟩ := hgood
  simp [run_replicate_self] at hk

@[simp] theorem family_card (ℓ n : ℕ) : (family ℓ n).card = 2^ℓ := by
  rw [family,Finset.card_image_of_injective _ (language_injective ..)]
  simp [Address]

theorem family_infinite {ℓ : ℕ} (hl : 0 < ℓ) (n : ℕ) (d : Address ℓ) : (binaryLanguage n d).Infinite := by
  have hc : 1 < Fintype.card (Address ℓ) := by
    simp only [Address,card_vector,Fintype.card_bool]; exact Nat.one_lt_two_pow hl.ne'
  letI : Nontrivial (Address ℓ) := Fintype.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨e,he⟩ := exists_ne d
  let f := fun k : ℕ ↦ encode (List.replicate k (e,false))
  have hi : Function.Injective f := by
    intro i j h
    simpa using congrArg List.length (encode_injective ℓ h)
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨k,rfl⟩
  apply (mem_encoded ..).mpr
  exact ⟨0,run_absent n d _ (by simp [Ne.symm he])⟩

private theorem mem_inter (n ℓ : ℕ) (w : List Bool) :
    w ∈ Support.classIntersection (family ℓ n : Set (Set (List Bool))) ↔ ∀ d : Address ℓ, w ∈ binaryLanguage n d := by
  constructor
  · intro h d
    exact h _ (Finset.mem_image_of_mem _ (Finset.mem_univ d))
  · intro h L hL
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hL
    exact h d

private theorem finite_common (n ℓ : ℕ) : (Support.classIntersection (family ℓ n : Set (Set (List Bool)))).Finite := by
  let d : Address ℓ := ⟨List.replicate ℓ false,by simp⟩
  apply (shortWords Bool ((ℓ+1)*(n+1)^(Fintype.card (Address ℓ)))).finite_toSet.subset
  intro w hw
  have hall := (mem_inter ..).mp hw
  obtain ⟨ts,rfl,_⟩ := hall d
  have hl := common_length n (ts.map Prod.fst) (fun e ↦ (mem_encoded ..).mp (hall e))
  apply (mem_shortWords ..).mpr
  rw [encode_length]
  apply Nat.mul_lt_mul_of_pos_left _ (Nat.succ_pos ℓ)
  simpa using hl

theorem binary_obstruction (ℓ n : ℕ) : ¬ MGeneratable (family ℓ n : Set (Set (List Bool))) (2^(n^(family ℓ n).card)) := by
  letI : Nonempty (Address ℓ) := ⟨⟨List.replicate ℓ false,by simp⟩⟩
  obtain ⟨w,hsize,hgood⟩ := exists_long_common (D := Address ℓ) n
  let tokens := fun b : Fin w.length → Bool ↦ List.ofFn (fun i ↦ (w.get i,b i))
  let f := fun b ↦ encode (tokens b)
  have ht (b) : (tokens b).map Prod.fst = w := by simp [tokens,List.map_ofFn,Function.comp_def]
  have hi : Function.Injective f := by
    intro b c he
    have hh := congrArg (List.map Prod.snd) (encode_injective ℓ he)
    exact List.ofFn_injective (by simpa [tokens,List.map_ofFn,Function.comp_def] using hh)
  have hf := finite_common n ℓ
  have hsub : Set.range f ⊆ Support.classIntersection (family ℓ n : Set (Set (List Bool))) := by
    rintro _ ⟨b,rfl⟩
    apply (mem_inter ..).mpr
    intro d
    exact (mem_encoded ..).mpr (ht b ▸ hgood d)
  have hc := Set.ncard_le_ncard hsub hf
  rw [Set.ncard_range_of_injective hi,Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hc
  apply intersection_obstruction (Set.Subset.refl _) _ hf
  · apply (Nat.pow_le_pow_right (by decide : 0 < 2) _).trans hc
    simpa [Address] using hsize
  · exact Finset.coe_nonempty.mpr (by rw [←Finset.card_pos,family_card]; positivity)

end
end GenLimit.ComplexityBarriers.Blocks
