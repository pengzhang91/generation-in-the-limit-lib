import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FilteredDensity
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.PeriodicGaps
import Mathlib.Data.Finset.Preimage

/-! The exact growth restriction for the rectangular obstruction in
Corollary 5.4. A unit-thickness tube along a lattice ray has geometric
volume V and contains V+1 consecutive ray points. -/
namespace GenLimit.KleinbergWei.Banach.FilteredObstruction
open Set Finset Real
open scoped Classical ENNReal
noncomputable section

/-- The full lattice can meet arbitrarily large ratio thresholds. -/
def feasible (f : ℕ → ℝ) : Prop := ∀ n : ℕ, ∃ V : ℕ, 2 ≤ V ∧ n ≤ V ∧ 0 < f V ∧
  (n:ℝ) ≤ V/(f V*log V)

private def axis (d : ℕ) (n : ℕ) : Lattice (d+1) := Fin.cons (n:ℤ) (fun _ => 0)
private def high (d b V : ℕ) : Lattice (d+1) := Fin.cons ((b+V:ℕ):ℤ) (fun _ => 1)

private theorem axis_inj (d : ℕ) : Function.Injective (axis d) := by
  intro i j eq; simpa [axis] using congrFun eq 0

private theorem tube {d b V : ℕ} (hv : 0 < V) :
    (∀ j, axis d b j < high d b V j) ∧ geometricVolume (axis d b) (high d b V) = V := by
  constructor
  · intro j; cases j using Fin.cases <;> simp [axis,high,hv]
  · simp [geometricVolume,Fin.prod_univ_succ,axis,high]

private theorem tube_mem {d b V i : ℕ} :
    (axis d b ≤ axis d i ∧ axis d i ≤ high d b V) ↔ b ≤ i ∧ i ≤ b+V := by
  constructor
  · rintro ⟨l,u⟩
    have h := u 0
    simp [axis,high] at h
    exact ⟨by simpa [axis] using l 0,by omega⟩
  · rintro ⟨l,u⟩; constructor <;> intro j <;> cases j using Fin.cases <;> simp [axis,high] <;> omega

private theorem count_tube (d b V) (S : Set ℕ) :
    (Rectangles.box (axis d '' S) (axis d b) (high d b V)).card = windowCount S b (V+1) := by
  symm
  apply Finset.card_bij (fun i _ => axis d i)
  · intro i mem
    obtain ⟨bounds,inS⟩ := Finset.mem_filter.mp mem
    obtain ⟨l,u⟩ := Finset.mem_Ico.mp bounds
    exact Rectangles.mem_box.mpr ⟨tube_mem.mpr ⟨l,by omega⟩,i,inS,rfl⟩
  · exact fun i _ j _ h => axis_inj d h
  · intro x mem
    obtain ⟨bounds,i,inS,rfl⟩ := Rectangles.mem_box.mp mem
    obtain ⟨l,u⟩ := tube_mem.mp bounds
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨l,by omega⟩,inS⟩,rfl⟩

/-- Density zero in any target already requires the volume growth condition. -/
theorem necessary {d} {f : ℕ → ℝ} {P O : Set (Lattice d)}
    (zero : filteredRectangularDensity f O P = 0) : feasible f := by
  intro n
  obtain ⟨M,large,volume⟩ := large_volume_of_admissible (d := d) f n
  let k := max M (n*2^d)
  have test : Nonempty {r // admissibleBox f P k r} := by
    by_contra! none
    letI := none
    have h := le_iSup (fun t => ⨅ r : {r // admissibleBox f P t r},
      ((Rectangles.box (O ∩ P) r.val.1 r.val.2).card:ℝ≥0∞)/(Rectangles.box P r.val.1 r.val.2).card) k
    change _ ≤ filteredRectangularDensity f O P at h
    rw [iInf_of_empty,zero] at h
    exact ENNReal.top_ne_zero (le_antisymm h bot_le)
  obtain ⟨⟨⟨l,u⟩,w,v,hf,ratio⟩⟩ := test
  let V := geometricVolume l u
  have mk : (M:ℝ) ≤ k := by exact_mod_cast le_max_left M (n*2^d)
  have big := volume P (l,u) ⟨w,v,hf,mk.trans ratio⟩
  refine ⟨V,v,big,hf,?_⟩
  have pos : 0 < f V*log V := mul_pos hf (Real.log_pos (by exact_mod_cast (show 1 < V from v)))
  have nk : (n:ℝ)*2^d ≤ k := by exact_mod_cast le_max_right M (n*2^d)
  have hits := (le_div_iff₀ pos).mp (nk.trans ratio)
  have cap : ((Rectangles.box P l u).card:ℝ) ≤ (2:ℝ)^d*V := by exact_mod_cast card_le_geometricVolume P w
  apply (le_div_iff₀ pos).2
  apply le_of_mul_le_mul_left (a := (2:ℝ)^d) _ (by positivity)
  linarith only [hits.trans cap]

/-- Transport the interval obstruction along an arbitrary injective coding.
One presentation has an output-free code interval of every sufficiently
large length. The family depends only on the coding. -/
theorem coded_holes {d} (e : ℕ → Lattice d) (inj : Function.Injective e) :
    ∃ C : Set (Set (Lattice d)), C.Countable ∧ (∀ L ∈ C, L.Infinite) ∧ e '' univ ∈ C ∧
      ∀ A : List (Lattice d) → Finset (Lattice d),
        (∀ L ∈ C, ∀ s : ℕ → Lattice d, range s = L → Function.Injective s →
          ∃ T, ∀ t ≥ T, ∀ x ∈ A (textPrefix s t), x ∈ L ∧ x ∉ textPrefix s t) →
        ∃ s : ℕ → Lattice d, range s = e '' univ ∧ Function.Injective s ∧ ∃ T, ∀ k ≥ T,
          ∃ b, 0 < b ∧ windowCount (e ⁻¹' {x | ∃ t, x ∈ A (textPrefix s (t+1))}) b k = 0 := by
  let C := Set.image e '' Adversary.periodicFamily
  have member {S} (hs : S ∈ Adversary.periodicFamily) : e '' S ∈ C := ⟨S,hs,rfl⟩
  refine ⟨C,Adversary.periodic_countable.image _,?_,member Adversary.univ_member,?_⟩
  · rintro L ⟨_,⟨⟨p,k,j⟩,rfl⟩,rfl⟩
    exact (Adversary.level_infinite p (Nat.succ_pos k) j).image inj.injOn
  intro A valid
  let B (p : List ℕ) := (A (p.map e)).preimage e inj.injOn
  have map_prefix (s : ℕ → ℕ) (t) : (textPrefix s t).map e = textPrefix (e ∘ s) t := by
    simp [textPrefix,List.map_map]
  have good : Adversary.ValidOn B Adversary.periodicFamily := by
    intro S hs s full hs'
    obtain ⟨T,ok⟩ := valid _ (member hs) _ (by rw [Set.range_comp,full]) (inj.comp hs')
    refine ⟨T,fun t ht x hx => ?_⟩
    have h := Finset.mem_preimage.mp hx
    rw [map_prefix] at h
    obtain ⟨⟨y,hy,eq⟩,fresh⟩ := ok t ht _ h
    exact ⟨inj eq ▸ hy,fun mem => fresh (map_prefix s t ▸ List.mem_map_of_mem mem)⟩
  obtain ⟨s,hs,full,T,holes⟩ := Adversary.periodic_holes B good
  refine ⟨e ∘ s,by rw [Set.range_comp,full],inj.comp hs,T,?_⟩
  have same : e ⁻¹' {x | ∃ t, x ∈ A (textPrefix (e ∘ s) (t+1))} =
      {x | ∃ t, x ∈ B (textPrefix s (t+1))} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_setOf_eq,B,Finset.mem_preimage,map_prefix]
  simpa only [same] using holes

/-- For every feasible filter, one fixed countable family forces filtered density
zero for every eventually valid machine, even with finite output batches. -/
theorem sufficient (d : ℕ) {f : ℕ → ℝ} (hf : feasible f) :
    ∃ C : Set (Set (Lattice (d+1))), C.Countable ∧ (∀ L ∈ C, L.Infinite) ∧
      ∃ K ∈ C, ∀ A : List (Lattice (d+1)) → Finset (Lattice (d+1)),
        (∀ L ∈ C, ∀ s : ℕ → Lattice (d+1), range s = L → Function.Injective s →
          ∃ T, ∀ t ≥ T, ∀ x ∈ A (textPrefix s t), x ∈ L ∧ x ∉ textPrefix s t) →
        ∃ s : ℕ → Lattice (d+1), range s = K ∧ Function.Injective s ∧
          filteredRectangularDensity f {x | ∃ t, x ∈ A (textPrefix s (t+1))} K = 0 := by
  let e := axis d
  obtain ⟨C,count,inf,member,holesFor⟩ := coded_holes e (axis_inj d)
  refine ⟨C,count,inf,e '' univ,member,fun A valid => ?_⟩
  obtain ⟨s,full,inj,T,holes⟩ := holesFor A valid
  let O := {x | ∃ t, x ∈ A (textPrefix s (t+1))}
  let Y := e ⁻¹' O
  have eq : O ∩ (e '' univ) = e '' Y := by
    simpa only [Set.inter_univ,Y] using (Set.image_preimage_inter e univ O).symm
  refine ⟨s,full,inj,le_antisymm ?_ bot_le⟩
  apply iSup_le; intro n
  obtain ⟨V,two,large,pos,ratio⟩ := hf (max n T)
  obtain ⟨b,_,gap⟩ := holes (V+1) (by omega)
  obtain ⟨widths,vol⟩ := tube (d := d) (b := b) (show 0 < V by omega)
  have target : (Rectangles.box (e '' univ) (axis d b) (high d b V)).card=V+1 := by
    simpa [e, windowCount] using count_tube d b V univ
  have den : 0 < f V*log V := mul_pos pos (Real.log_pos (by exact_mod_cast (show 1 < V from two)))
  have test : admissibleBox f (e '' univ) n (axis d b,high d b V) := by
    refine ⟨widths,by simpa only [vol] using two,by simpa only [vol] using pos,?_⟩
    dsimp only; rw [vol,target]
    have nn : (n:ℝ) ≤ max n T := by exact_mod_cast le_max_left n T
    exact (nn.trans ratio).trans (div_le_div_of_nonneg_right (by norm_cast; omega) den.le)
  apply (iInf_le _ ⟨_,test⟩).trans
  change ((Rectangles.box (O ∩ (e '' univ)) (axis d b) (high d b V)).card:ℝ≥0∞)/_ ≤ 0
  rw [eq,count_tube,gap]; simp

end
end GenLimit.KleinbergWei.Banach.FilteredObstruction
