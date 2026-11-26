import GenLimit.Paper16_ComplexityBarriers.Threshold

/-! # The paper's finite-set threshold and the library's distinct-history threshold -/
namespace GenLimit.ComplexityBarriers
open Generic
open scoped Classical
noncomputable section

theorem mGeneratable_iff_uniform_at {H : LanguageClass α} (hH : UUS H) (m : ℕ) :
    MGeneratable H m ↔ ∃ G : Generator α, IsUniformGeneratorAt G H m := by
  constructor
  · rintro ⟨G,hG⟩
    let op : Generator α := fun _ xs ↦ G (sequenceSample xs)
    refine ⟨op,fun L hL stream hst t ht s hts ↦ ?_⟩
    have hsub : (sample stream s : Set α) ⊆ L := by
      intro x hx
      obtain ⟨i,_,rfl⟩ := mem_sample_iff.mp hx
      exact hst ⟨i,rfl⟩
    have good := hG L hL _ hsub (ht ▸ Finset.card_le_card (sample_mono hts))
    have he : output op stream s = G (sample stream s) := congrArg G (sequenceSample_prefix stream s)
    unfold CorrectAt
    rw [he]
    exact good
  · rintro ⟨G,hG⟩
    refine ⟨fun X ↦ G X.toList.length X.toList.get,fun L hL X hX hm ↦ ?_⟩
    obtain ⟨a,ha⟩ := (hH L hL).nonempty
    let stream := historyThenFallback X.toList a
    have hs : sample stream X.toList.length = X := by
      unfold stream
      rw [sample_historyThenFallback_length]
      simp
    have hin : StreamIn stream L := streamIn_historyThenFallback (fun x hx ↦ hX (Finset.mem_toList.mp hx)) ha
    have hm' : m ≤ (sample stream X.toList.length).card := by rw [hs]; exact hm
    obtain ⟨t,ht,he⟩ := exists_sample_card_eq_of_le hm'
    have good := hG L hL stream hin t he X.toList.length ht
    have ho : output G stream X.toList.length = G X.toList.length X.toList.get := by
      unfold output
      congr 1
      funext i
      exact dif_pos i.isLt
    simpa only [CorrectAt,hs,ho] using good

end
end GenLimit.ComplexityBarriers
