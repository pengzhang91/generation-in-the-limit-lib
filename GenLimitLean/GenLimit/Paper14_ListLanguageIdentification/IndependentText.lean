import GenLimit.Paper14_ListLanguageIdentification.FairExtraction

namespace GenLimit.ListIdentification.InfiniteDraws
open MeasureTheory Filter Set
open scoped Topology ENNReal
open PrefixSimulation

def text (x : ℕ → α) := rows x 0
def reservoir (x : ℕ → α) := rows x 1
noncomputable def bits (code : α → ℕ) (x : ℕ → α) (j : ℕ) :=
  orientation code (pairs (rows x j))
noncomputable def split (code : α → ℕ) (x : ℕ → α) :=
  (text x, bits code (reservoir x))
noncomputable def observations (code : α → ℕ) (x : ℕ → α) (j : ℕ) :=
  ((split code x).1 j,(split code x).2 j)

theorem split_law [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (code : α → ℕ) (hc : Function.Injective code) (μ : Measure α) [IsProbabilityMeasure μ]
    {a b : α} (hab : a ≠ b) (ha : 0 < μ {a}) (hb : 0 < μ {b}) :
    MeasurePreserving (split code) (iid μ) ((iid μ).prod Probabilistic.fair) := by
  have one := (orientation_law code hc μ hab ha hb).comp (pairs_law μ)
  have hb' : MeasurePreserving (bits code) (iid μ) Probabilistic.fair :=
    (iid_map one).comp (rows_iid μ)
  have splitRaw : MeasurePreserving (fun s : ℕ → α ↦ (text s,reservoir s))
      (iid μ) ((iid μ).prod (iid μ)) := (two_law (iid μ)).comp (rows_iid μ)
  have hp : MeasurePreserving (Prod.map id (bits code)) ((iid μ).prod (iid μ))
      ((iid μ).prod Probabilistic.fair) := by
    refine ⟨measurable_id.prodMap hb'.measurable, ?_⟩
    rw [← Measure.map_prod_map _ _ measurable_id hb'.measurable,Measure.map_id,hb'.map_eq]
  exact hp.comp splitRaw

theorem ae_presents [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (q : PMF α) : ∀ᵐ s ∂iid q.toMeasure, Generic.Presents s q.support := by
  have atom (a : α) : q.toMeasure {a} = q a := q.toMeasure_apply_singleton a (measurableSet_singleton a)
  have each (a : α) : ∀ᵐ s ∂iid q.toMeasure, (∃ j : ℕ, s j = a) ↔ a ∈ q.support := by
    by_cases ha : a ∈ q.support
    · have hp : 0 < q.toMeasure {a} := (atom a).symm ▸ (pos_iff_ne_zero.mpr ha)
      filter_upwards [ae_some q.toMeasure (H := {a}) (measurableSet_singleton a) hp] with s hs
      exact iff_of_true hs ha
    · have hn : ∀ᵐ v ∂q.toMeasure, v ≠ a := by
        rw [ae_iff]
        simpa only [Classical.not_not,Set.setOf_eq_eq_singleton,atom] using not_ne_iff.mp ha
      have hcoord (j : ℕ) := (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ q.toMeasure) j
        ).quasiMeasurePreserving.ae (p := fun v ↦ v ≠ a) hn
      filter_upwards [ae_all_iff.mpr hcoord] with s hs
      exact iff_of_false (fun ⟨j,hj⟩ ↦ hs j hj) ha
  filter_upwards [ae_all_iff.mpr each] with s hs
  exact Set.ext hs

private theorem local_comp {f : (ℕ → α) → ℕ → β} {g : (ℕ → β) → ℕ → γ}
    {s : ℕ → α} (hf : LocalAt f s) (hg : LocalAt g (f s)) :
    LocalAt (g ∘ f) s := by
  intro j
  obtain ⟨m,hm⟩ := hg j
  obtain ⟨n,hn⟩ := local_prefix hf m
  exact ⟨n,fun t ht ↦ hm (f t) (hn t ht)⟩

private theorem local_reindex (f : ℕ → ℕ) (x : ℕ → α) : LocalAt (fun s j ↦ s (f j)) x :=
  fun j ↦ ⟨f j + 1, fun t h ↦ h _ (Nat.lt_succ_self _)⟩

private theorem local_pairs (s : ℕ → α) : LocalAt pairs s := by
  intro j
  refine ⟨max (Nat.pair j 0) (Nat.pair j 1) + 1,fun t ht ↦ ?_⟩
  exact Prod.ext (ht _ (Nat.lt_succ_of_le (le_max_left ..))) (ht _ (Nat.lt_succ_of_le (le_max_right ..)))

private theorem local_orientation (code : α → ℕ) (w : ℕ → α × α) (hw : ∃ j, different w j) :
    LocalAt (fun v _ ↦ orientation code v) w := by
  intro _
  let m := first (different w)
  refine ⟨m+1,fun t ht ↦ ?_⟩
  have he : first (different t) = m := first_congr hw (fun i hi ↦ by
    unfold different
    rw [ht i (Nat.lt_succ_of_le hi)])
  simp only [orientation,he,ht m (Nat.lt_succ_self _),m]

theorem ae_local [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (code : α → ℕ) (μ : Measure α) [IsProbabilityMeasure μ]
    {a b : α} (hab : a ≠ b) (ha : 0 < μ {a}) (hb : 0 < μ {b}) :
    ∀ᵐ s ∂iid μ, LocalAt (observations code) s := by
  have rowLaw (i : ℕ) : MeasurePreserving (fun x : ℕ → α ↦ rows x i) (iid μ) (iid μ) :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ iid μ) i).comp (rows_iid μ)
  have one (j : ℕ) := ((pairs_law μ).comp ((rowLaw j).comp (rowLaw 1))).quasiMeasurePreserving.ae
    (p := fun w ↦ ∃ l, different w l) (ae_different μ hab ha hb)
  filter_upwards [ae_all_iff.mpr one] with s hs
  intro j
  have hbits := (local_comp (local_reindex (Nat.pair 1) s)
    (local_comp (local_reindex (Nat.pair j) (reservoir s))
      (local_comp (local_pairs (rows (reservoir s) j)) (local_orientation code _ (hs j))))) 0
  obtain ⟨n,hn⟩ := hbits
  refine ⟨max n (Nat.pair 0 j + 1),fun t ht ↦ ?_⟩
  exact Prod.ext (ht _ ((Nat.lt_succ_self _).trans_le (le_max_right ..)))
    (hn t (fun i hi ↦ ht i (hi.trans_le (le_max_left ..))))

end GenLimit.ListIdentification.InfiniteDraws
