import GenLimit.Paper16_ComplexityBarriers.TapeGrammar
import GenLimit.Paper16_ComplexityBarriers.EffectiveBounds

/-! # No computable generation threshold for two infinite CFGs

Use P11's universal binary Turing machine on a recursive fixed point. Any
proposed algorithm gives a computable upper bound on its answer for the
two input grammars. The fixed point makes the machine print more set bits
than that bound. Every bit in the final tape contributes to the length
of the joint accepting trace, giving a finite intersection too large for
the proposed threshold. -/
namespace GenLimit.ComplexityBarriers.CFG
open List
open GenLimit.LearningAlgorithmsLimit
open NativeTape (BinaryMachine universalValue binary_realization chunks logical flat_length
  logical_length_pow logical_length_le chunks_spec)
open Nat.Partrec (Code)
open scoped Classical
noncomputable section

private theorem recursive_value : Partrec universalValue := by
  have hp : Primrec₂ (fun a b : ℕ ↦ a^b) := Primrec₂.unpaired.mpr (Primrec.nat_iff.mpr Nat.Primrec.pow)
  exact (Code.eval_part.comp (Computable.ofNat _) (Computable.const 0)).map
    ((hp.to_comp.comp (Computable.const 2) Computable.snd).to₂)

private theorem output_mass (k : ℕ) : k ≤ (chunks (2^k)).flatten.count true := by
  have h (bs : List (List Bool)) (hp : ∀ b ∈ bs, b.head? = some true) : bs.length ≤ bs.flatten.count true := by
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      have hh := hp b List.mem_cons_self
      have ht := ih (fun z hz ↦ hp z (List.mem_cons_of_mem _ hz))
      cases b with
      | nil => contradiction
      | cons a v =>
        have he : a=true := Option.some.inj hh
        subst a
        simp only [List.length_cons,List.flatten_cons,List.count_append,List.count_cons_self]
        omega
  have hm := h (chunks (2^k)) (fun b hb ↦ (chunks_spec hb).2)
  apply (logical_length_pow k).trans
  simpa [chunks] using hm

theorem no_computable_bound : ¬ ∃ A : BoundProcedure, Partrec A ∧ OnInfinite A := by
  rintro ⟨A,hA,hon⟩
  obtain ⟨U,hU⟩ := binary_realization universalValue recursive_value
  let J := TapeCheck.joint (TapeCheck.control U)
  let L := stackRules (leftStep J)
  let R := stackRules (rightStep J)
  obtain ⟨f,hf,hbound⟩ := effective_majorant A hA hon L R
  let cap := max (Fintype.card (TapeCheck.Left (TapeCheck.States U))) (Fintype.card (TapeCheck.Right (TapeCheck.States U))) + 2
  let width := Fintype.card NativeTape.Cell + 1
  let budget := fun c : Code ↦ f (inputBound cap width (Encodable.encode c))
  have hcomp : Computable budget := hf.comp ((inputBound_comp cap width).comp Computable.encode)
  obtain ⟨c,hc⟩ := MassDiagonal.constant_fixed_point budget hcomp 0
  let k := budget c+1
  have hk : k ∈ c.eval 0 := by rw [hc]; exact Part.mem_some _
  have hv : 2^k ∈ universalValue (Encodable.encode c) := by
    unfold universalValue
    rw [Denumerable.ofNat_encode]
    exact (Part.mem_map_iff _).mpr ⟨k,hk,rfl⟩
  obtain ⟨q,hq⟩ := hU _ _ hv
  let w := (chunks (Encodable.encode c)).flatten
  let l := TapeCheck.left (TapeCheck.start U) (TapeCheck.input w)
  let r := TapeCheck.right (Q := TapeCheck.States U) (TapeCheck.input w)
  obtain ⟨tr,htr,hmass⟩ := TapeCheck.run_of_eval U w (chunks (2^k)).flatten q hq
  have hlarge := (output_mass k).trans hmass
  have hw : w.length ≤ width*(Encodable.encode c+1) := by
    rw [show w.length = width*(logical (Encodable.encode c)).length from flat_length _]
    exact Nat.mul_le_mul_left _ (logical_length_le _)
  obtain ⟨hl,hr⟩ := TapeCheck.input_lengths (TapeCheck.start U) w
  have numb {X : Type} [Fintype X] (x : X) : nt x ≤ Fintype.card X + 2 := by
    exact Nat.add_le_add_right (Nat.le_of_lt ((Fintype.equivFin X x).isLt)) 2
  have hcode : Encodable.encode (l.map nt,r.map nt) ≤ inputBound cap width (Encodable.encode c) := by
    apply le_inputBound
    · intro z hz
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp hz
      exact (numb v).trans (Nat.add_le_add_right (le_max_left ..) 2)
    · intro z hz
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp hz
      exact (numb v).trans (Nat.add_le_add_right (le_max_right ..) 2)
    · rw [List.length_map]; exact hl.trans (Nat.add_le_add_right hw 2)
    · rw [List.length_map]; exact hr.trans (Nat.add_le_add_right hw 2)
  obtain ⟨m,hm,hgen⟩ := hbound _ _ _ hcode
  apply sample_obstruction htr m _ hgen
  change m ≤ budget c at hm
  dsimp [k] at hlarge
  omega

end
end GenLimit.ComplexityBarriers.CFG
