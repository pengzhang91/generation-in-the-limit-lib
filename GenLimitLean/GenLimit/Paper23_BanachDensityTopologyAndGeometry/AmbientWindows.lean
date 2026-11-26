import GenLimit.Paper23_BanachDensityTopologyAndGeometry.PeriodicGaps
import Mathlib.Data.Finset.Preimage

/-! The ambient-coordinate interpretation of P23 Theorem 4.1.
Place consecutive ranks of the periodic hard family far enough apart that
each nonempty block of ranks pulls back from an admissible ambient window.
The target-count denominator still counts each rank exactly once. The
construction allows an arbitrary finite output batch at each time. -/
namespace GenLimit.KleinbergWei.Banach.Adversary
open Set
open scoped Classical ENNReal
noncomputable section

/-- Relative window density using ambient locations and ambient lengths
for the start constraint, and the number of target words for the
ratio and the growth threshold. -/
def ambientRelativeWindowDensity (f : ℕ → WithTop ℕ) (O K : Set ℕ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨅ r : {r : ℕ × ℕ // 0 < r.1 ∧ (r.1 : WithTop ℕ) ≤ f r.2 ∧ n ≤ windowCount K r.1 r.2},
    (windowCount (O ∩ K) r.val.1 r.val.2 : ℝ≥0∞) / windowCount K r.val.1 r.val.2

private def embedAt (gap : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | i+1 => embedAt gap i + gap (embedAt gap i) + 1

private theorem stretch_exists (f : ℕ → WithTop ℕ) (mono : Monotone f)
    (unbounded : ∀ n : ℕ, ∃ k, (n : WithTop ℕ) ≤ f k) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ (∀ b, 0 < e b) ∧
      ∀ b k, 0 < k → (e b : WithTop ℕ) ≤ f (e (b+k)-e b) := by
  let gap (n : ℕ) := (unbounded n).choose
  let e := embedAt gap
  have step (b) : e (b+1)=e b+gap (e b)+1 := rfl
  have inc : StrictMono e := strictMono_nat_of_lt_succ fun b => by rw [step]; omega
  refine ⟨e,inc,fun b => (show 0 < e 0 from Nat.zero_lt_one).trans_le (inc.monotone (Nat.zero_le b)),?_⟩
  intro b k hk
  apply (unbounded (e b)).choose_spec.trans
  apply mono
  have lt : e (b+1) ≤ e (b+k) := inc.monotone (by omega)
  rw [step] at lt
  change gap (e b) ≤ _; omega

private theorem rank_window {e : ℕ → ℕ} (inc : StrictMono e) (S : Set ℕ) (b k : ℕ) :
    windowCount (e '' S) (e b) (e (b+k)-e b) = windowCount S b k := by
  have le : e b ≤ e (b+k) := inc.monotone (by omega)
  unfold windowCount
  rw [Nat.add_sub_of_le le]
  symm
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx; obtain ⟨h,mem⟩ := Finset.mem_filter.mp hx
    obtain ⟨l,u⟩ := Finset.mem_Ico.mp h
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨inc.monotone l,inc u⟩,x,mem,rfl⟩
  · exact fun _ _ _ _ eq => inc.injective eq
  · intro y hy
    obtain ⟨h,⟨x,inS,rfl⟩⟩ := Finset.mem_filter.mp hy
    obtain ⟨l,u⟩ := Finset.mem_Ico.mp h
    exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨inc.le_iff_le.mp l,inc.lt_iff_lt.mp u⟩,inS⟩,rfl⟩

private theorem prefix_map (e s : ℕ → ℕ) (t) :
    (textPrefix s t).map e = textPrefix (e ∘ s) t := by simp [textPrefix,List.map_map]

/-- For every unbounded start allowance a fixed countable family forces
zero when the window length and start are measured in ambient coordinates.
The target language is the range of one increasing embedding. -/
theorem ambient_obstruction (f : ℕ → WithTop ℕ) (mono : Monotone f)
    (unbounded : ∀ n : ℕ, ∃ k, (n : WithTop ℕ) ≤ f k) :
    ∃ C : Set (Set ℕ), C.Countable ∧ (∀ L ∈ C, L.Infinite) ∧
      ∃ K ∈ C, ∀ A : List ℕ → Finset ℕ, ValidOn A C →
        ∃ s : ℕ → ℕ, range s=K ∧ Function.Injective s ∧
          ambientRelativeWindowDensity f {x | ∃ t, x ∈ A (textPrefix s (t+1))} K = 0 := by
  obtain ⟨e,inc,pos,allowed⟩ := stretch_exists f mono unbounded
  let C := Set.image e '' periodicFamily
  have image_mem {K} (h : K ∈ periodicFamily) : e '' K ∈ C := ⟨K,h,rfl⟩
  refine ⟨C,periodic_countable.image _,?_,e '' univ,image_mem univ_member,?_⟩
  · rintro _ ⟨_,⟨⟨p,k,j⟩,rfl⟩,rfl⟩
    exact (level_infinite p (Nat.succ_pos k) j).image inc.injective.injOn
  intro A valid
  let B (p : List ℕ) := (A (p.map e)).preimage e inc.injective.injOn
  have good : ValidOn B periodicFamily := by
    intro K hK s full inj
    have cover : range (e ∘ s)=e '' K := by rw [Set.range_comp,full]
    obtain ⟨T,ok⟩ := valid _ (image_mem hK) _ cover (inc.injective.comp inj)
    refine ⟨T,?_⟩
    intro t ht x hx
    have out := Finset.mem_preimage.mp hx
    rw [prefix_map] at out
    obtain ⟨mem,fresh⟩ := ok _ ht _ out
    obtain ⟨v,hv,same⟩ := mem
    refine ⟨inc.injective same ▸ hv,fun h => fresh ?_⟩
    rw [←prefix_map]; exact List.mem_map_of_mem h
  obtain ⟨s,inj,all,T,holes⟩ := periodic_holes B good
  refine ⟨e ∘ s,by rw [Set.range_comp,all],inc.injective.comp inj,le_antisymm ?_ bot_le⟩
  apply iSup_le; intro n
  let k := max (n+1) T
  obtain ⟨b,_,empty⟩ := holes k (le_max_right ..)
  let w := e (b+k)-e b
  have full : windowCount (e '' univ) (e b) w = k := by
    rw [rank_window inc]; simp [windowCount]
  let R : {r : ℕ × ℕ // 0 < r.1 ∧ (r.1 : WithTop ℕ) ≤ f r.2 ∧ n ≤ windowCount (e '' univ) r.1 r.2} :=
    ⟨(e b,w),pos b,allowed b k (Nat.succ_pos n |>.trans_le (le_max_left ..)),full ▸ (Nat.le_succ _).trans (le_max_left ..)⟩
  let O := {x | ∃ t, x ∈ A (textPrefix (e ∘ s) (t+1))}
  let Y := {x | ∃ t, x ∈ B (textPrefix s (t+1))}
  have same : O ∩ (e '' univ) = e '' Y := by
    ext x
    constructor
    · rintro ⟨⟨t,hit⟩,z,_,rfl⟩
      exact ⟨z,⟨t,Finset.mem_preimage.mpr (by rwa [prefix_map])⟩,rfl⟩
    · rintro ⟨z,⟨t,hit⟩,rfl⟩
      exact ⟨⟨t,by rw [←prefix_map]; exact Finset.mem_preimage.mp hit⟩,z,trivial,rfl⟩
  have zero : windowCount (O ∩ (e '' univ)) (e b) w = 0 := by
    rw [same,rank_window inc]; exact empty
  exact (iInf_le _ R).trans (by change (windowCount (O ∩ (e '' univ)) (e b) w : ℝ≥0∞) / _ ≤ 0; rw [zero]; simp)

end
end GenLimit.KleinbergWei.Banach.Adversary
