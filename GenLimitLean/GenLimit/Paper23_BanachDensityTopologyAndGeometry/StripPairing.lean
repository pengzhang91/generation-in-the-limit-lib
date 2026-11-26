import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RectanglePairingCheck

/-! The failure of source equation (28) grows linearly on nondegenerate
planar rectangles. Put copies of the four columns on rows ten units apart
and reverse all signs on alternate rows. Every rectangular trace has
discrepancy at most one. In each row the two interior words have unique
opposite-color neighbors outside the test rectangle. -/
namespace GenLimit.KleinbergWei.Banach.FilteredPairing.Strip
open Finset
open scoped Classical
abbrev Word := ℕ × Fin 4

private def parity (n : ℕ) : ℤ := (n%2 : ℕ)
private def rowSign (n : ℕ) := parity (n+1)-parity n
def sign (v : Word) := rowSign v.1 * color v.2
def distance (x y : Word) : ℤ :=
  max |(10:ℤ)*x.1-10*y.1| |pos x.2-pos y.2|

private def rows (n : ℕ) (l u : ℤ) :=
  (Finset.range n).filter fun r : ℕ => l ≤ (10:ℤ)*r ∧ (10:ℤ)*r ≤ u
private def cols (l u : ℤ) := Finset.univ.filter fun c => l ≤ pos c ∧ pos c ≤ u
def rectangle (n : ℕ) (xl xu yl yu : ℤ) : Finset Word := rows n yl yu ×ˢ cols xl xu

private theorem row_discrepancy (n : ℕ) (l u : ℤ) :
    |∑ r ∈ rows n l u, rowSign r| ≤ 1 := by
  let S := rows n l u
  rcases S.eq_empty_or_nonempty with empty | ne
  · change |∑ r ∈ S, rowSign r| ≤ 1; simp [empty]
  let a := S.min' ne
  let b := S.max' ne
  have amin : a ∈ S := Finset.min'_mem _ _
  have bmax : b ∈ S := Finset.max'_mem _ _
  have gap : a ≤ b+1 := (Finset.min'_le _ _ bmax).trans (Nat.le_succ _)
  have interval : S = Finset.Ico a (b+1) := by
    ext r
    constructor
    · intro h
      exact Finset.mem_Ico.mpr ⟨Finset.min'_le _ _ h,Nat.lt_succ_of_le (Finset.le_max' _ _ h)⟩
    · intro h
      obtain ⟨left,right⟩ := Finset.mem_Ico.mp h
      obtain ⟨_,lo,_⟩ := Finset.mem_filter.mp amin
      obtain ⟨small,_,hi⟩ := Finset.mem_filter.mp bmax
      have bn := Finset.mem_range.mp small
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega,by omega⟩
  change |∑ r ∈ S, rowSign r| ≤ 1
  rw [interval,Finset.sum_Ico_eq_sub _ gap]
  simp only [rowSign,Finset.sum_range_sub]
  unfold parity; rw [abs_le]; omega

theorem every_rectangle_balanced (n : ℕ) (xl xu yl yu : ℤ) :
    |∑ v ∈ rectangle n xl xu yl yu, sign v| ≤ 1 := by
  have hc : |∑ c ∈ cols xl xu, color c| ≤ 1 := coloring_balanced xl xu
  have hr := row_discrepancy n yl yu
  change |∑ v ∈ rows n yl yu ×ˢ cols xl xu, rowSign v.1*color v.2| ≤ 1
  rw [Finset.sum_product,←Finset.sum_mul_sum,abs_mul]
  simpa using mul_le_mul hr hc (abs_nonneg _) (by norm_num : (0:ℤ) ≤ 1)

private def inCol (b : Bool) : Fin 4 := if b then 2 else 1
private def outCol (b : Bool) : Fin 4 := if b then 3 else 0
def input (a : ℕ × Bool) : Word := (a.1,inCol a.2)
def reply (a : ℕ × Bool) : Word := (a.1,outCol a.2)

/-- Each input has a unique closest other word, at distance one, and its
color is opposite. The conclusion persists after any subset of other
words is removed. -/
theorem unique_reply (a : ℕ × Bool) :
    sign (reply a) = -sign (input a) ∧ distance (input a) (reply a) = 1 ∧
      ∀ v, v ≠ input a → v ≠ reply a → 1 < distance (input a) v := by
  obtain ⟨r,b⟩ := a
  have opp : ∀ b : Bool, color (outCol b) = -color (inCol b) := by decide
  have unit : ∀ b : Bool, |pos (inCol b)-pos (outCol b)| = 1 := by decide
  have other : ∀ b : Bool, ∀ c : Fin 4, c ≠ inCol b → c ≠ outCol b → 1 < |pos (inCol b)-pos c| := by decide
  refine ⟨by simp [input,reply,sign,opp],by simp [distance,input,reply,unit],?_⟩
  rintro ⟨s,c⟩ nI nR
  by_cases same : r=s
  · subst s
    apply (other b c (fun eq => nI (Prod.ext rfl eq)) (fun eq => nR (Prod.ext rfl eq))).trans_le
    exact le_max_right ..
  · have far : 1 < |(10:ℤ)*r-10*s| := by rw [lt_abs]; omega
    exact far.trans_le (le_max_left ..)

/-- Distinct rounds have distinct inputs and replies, and no input is a
reply. Thus the forced response remains available in any round order. -/
theorem distinct_rounds :
    Function.Injective input ∧ Function.Injective reply ∧
    ∀ a b, input a ≠ reply b := by
  have injI : Function.Injective inCol := by decide
  have injO : Function.Injective outCol := by decide
  have sep : ∀ i j : Bool, inCol i ≠ outCol j := by decide
  exact ⟨fun a b h => Prod.ext (congrArg (fun v : Word => v.1) h) (injI (congrArg Prod.snd h)),
    fun a b h => Prod.ext (congrArg (fun v : Word => v.1) h) (injO (congrArg Prod.snd h)),
    fun a b h => sep a.2 b.2 (congrArg Prod.snd h)⟩

/-- In n rows the test box has geometric volume 30n and contains exactly
2n adversarial inputs. All 2n forced replies are outside it. -/
theorem growing_window (n : ℕ) :
    let turns : Finset (ℕ × Bool) := Finset.range n ×ˢ Finset.univ
    let R := rectangle n 2 5 0 (10*n)
    R = turns.image input ∧ R.card = 2*n ∧ Disjoint R (turns.image reply) ∧
      |∑ v ∈ R, sign v| = 0 := by
  let turns : Finset (ℕ × Bool) := Finset.range n ×ˢ Finset.univ
  have rr : rows n 0 (10*n) = Finset.range n := by
    ext r; simp only [rows,Finset.mem_filter,Finset.mem_range]
    constructor
    · exact And.left
    · intro lt; exact ⟨lt,by positivity,by omega⟩
  have cc : cols 2 5 = {1,2} := by decide
  have rangeI : ∀ c : Fin 4, c ∈ ({1,2} : Finset _) ↔ ∃ b, inCol b = c := by decide
  have img : rectangle n 2 5 0 (10*n) = turns.image input := by
    ext v
    simp only [rectangle,rr,cc,Finset.mem_product,Finset.mem_image]
    constructor
    · rintro ⟨h,c⟩
      obtain ⟨b,eq⟩ := (rangeI _).mp c
      exact ⟨(v.1,b),Finset.mem_product.mpr ⟨h,Finset.mem_univ _⟩,Prod.ext rfl eq⟩
    · rintro ⟨⟨r,b⟩,mem,rfl⟩
      exact ⟨(Finset.mem_product.mp mem).1,(rangeI _).mpr ⟨b,rfl⟩⟩
  refine ⟨img,by rw [rectangle,rr,cc]; simp [mul_comm],?_,?_⟩
  · rw [img]
    apply Finset.disjoint_left.mpr
    rintro v hI hO
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨b,_,eq⟩ := Finset.mem_image.mp hO
    exact distinct_rounds.2.2 a b eq.symm
  · change |∑ v ∈ rows n 0 (10*n) ×ˢ cols 2 5, rowSign v.1 * color v.2| = 0
    rw [Finset.sum_product,←Finset.sum_mul_sum,show ∑ c ∈ cols 2 5, color c = 0 by decide]
    simp

end GenLimit.KleinbergWei.Banach.FilteredPairing.Strip
