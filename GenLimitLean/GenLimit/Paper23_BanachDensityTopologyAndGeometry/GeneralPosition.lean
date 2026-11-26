import GenLimit.Paper23_BanachDensityTopologyAndGeometry.MonochromaticRectangles

/-! Break coordinate ties in a finite point set while preserving every
rectangular trace. In base w, encode (x,y) by (x+wy,y+wx). The two quotients
recover y and x, and either new coordinate determines
the full point. -/
namespace GenLimit.KleinbergWei.Banach.Stages
open Set
noncomputable section

def GeneralPosition (S : Finset Point) :=
  InjOn Prod.fst (S : Set Point) ∧ InjOn Prod.snd (S : Set Point)

private def spread (w : ℕ) (p : Point) : Point := (p.1 + w*p.2, p.2 + w*p.1)

theorem finite_rectangle_distinct (k : ℕ) (hk : 0 < k) :
    ∃ S : Finset Point, GeneralPosition S ∧ ∀ c, Monochromatic S k c := by
  obtain ⟨P,property⟩ := finite_rectangle k hk
  let w := max (P.sup Prod.fst) (P.sup Prod.snd)+1
  have small {p : Point} (hp : p ∈ P) : p.1 < w ∧ p.2 < w :=
    ⟨Nat.lt_succ_of_le ((Finset.le_sup hp).trans (le_max_left ..)),
     Nat.lt_succ_of_le ((Finset.le_sup hp).trans (le_max_right ..))⟩
  have pos : 0 < w := Nat.succ_pos _
  have quot {a b : ℕ} (ha : a < w) : (a+w*b)/w=b := by simp [Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt ha]
  have remn {a b : ℕ} (ha : a < w) : (a+w*b)%w=a := by simp [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ha]
  have uniqueX {p q : Point} (hp : p ∈ P) (hq : q ∈ P)
      (eq : (spread w p).1=(spread w q).1) : p=q := by
    obtain ⟨pu,_⟩ := small hp; obtain ⟨qu,_⟩ := small hq
    change p.1+w*p.2=q.1+w*q.2 at eq
    exact Prod.ext (by simpa only [remn pu,remn qu] using congrArg (·%w) eq)
      (by simpa only [quot pu,quot qu] using congrArg (·/w) eq)
  have uniqueY {p q : Point} (hp : p ∈ P) (hq : q ∈ P)
      (eq : (spread w p).2=(spread w q).2) : p=q := by
    obtain ⟨_,pu⟩ := small hp; obtain ⟨_,qu⟩ := small hq
    change p.2+w*p.1=q.2+w*q.1 at eq
    exact Prod.ext (by simpa only [quot pu,quot qu] using congrArg (·/w) eq)
      (by simpa only [remn pu,remn qu] using congrArg (·%w) eq)
  refine ⟨P.image (spread w),⟨?_,?_⟩,?_⟩
  · intro x hx y hy e
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
    rw [uniqueX hp hq e]
  · intro x hx y hy e
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
    rw [uniqueY hp hq e]
  · intro color
    obtain ⟨lo,hi,c,size,mono⟩ := property (color ∘ spread w)
    let l : Point := (w*lo.2,w*lo.1)
    let u : Point := (w*(hi.2+1)-1,w*(hi.1+1)-1)
    have test {a b L U : ℕ} (ha : a < w) :
        (w*L ≤ a+w*b ∧ a+w*b ≤ w*(U+1)-1) ↔ L ≤ b ∧ b ≤ U := by
      have edge (t : ℕ) : 0 < w*(t+1) := Nat.mul_pos pos (Nat.succ_pos _)
      have divide := quot (b:=b) ha
      constructor
      · rintro ⟨low,high⟩
        have le := (Nat.le_div_iff_mul_le pos).mpr (by simpa [Nat.mul_comm] using low : L*w ≤ a+w*b)
        have lt := (Nat.div_lt_iff_lt_mul pos).mpr (by rw [Nat.mul_comm (U+1) w]; have := edge U; omega : a+w*b < (U+1)*w)
        omega
      · rintro ⟨low,high⟩
        have lower := (Nat.le_div_iff_mul_le pos).mp (divide.symm ▸ low)
        have upper := (Nat.div_lt_iff_lt_mul pos).mp (show (a+w*b)/w < U+1 by omega)
        rw [Nat.mul_comm L w] at lower
        rw [Nat.mul_comm (U+1) w] at upper
        omega
    have bounds {p : Point} (hp : p ∈ P) :
        (l ≤ spread w p ∧ spread w p ≤ u) ↔ lo ≤ p ∧ p ≤ hi := by
      obtain ⟨x,y⟩ := small hp
      change ((_ ≤ _ ∧ _ ≤ _) ∧ (_ ≤ _ ∧ _ ≤ _)) ↔ (_ ≤ _ ∧ _ ≤ _) ∧ (_ ≤ _ ∧ _ ≤ _)
      dsimp [l,u,spread]
      constructor
      · rintro ⟨⟨a,b⟩,c',d⟩
        obtain ⟨l₁,u₁⟩ := (test x).mp ⟨a,c'⟩
        obtain ⟨l₂,u₂⟩ := (test y).mp ⟨b,d⟩
        exact ⟨⟨l₂,l₁⟩,u₂,u₁⟩
      · rintro ⟨⟨a,b⟩,c',d⟩
        obtain ⟨l₁,u₁⟩ := (test x).mpr ⟨b,d⟩
        obtain ⟨l₂,u₂⟩ := (test y).mpr ⟨a,c'⟩
        exact ⟨⟨l₁,l₂⟩,u₁,u₂⟩
    have iso : trace (P.image (spread w)) l u = (trace P lo hi).image (spread w) := by
      ext x
      simp only [mem_trace,Finset.mem_image]
      constructor
      · rintro ⟨⟨p,hp,rfl⟩,bd⟩; exact ⟨p,⟨hp,(bounds hp).mp bd⟩,rfl⟩
      · rintro ⟨p,⟨hp,bd⟩,rfl⟩; exact ⟨⟨p,hp,rfl⟩,(bounds hp).mpr bd⟩
    refine ⟨l,u,c,?_,?_⟩
    · rw [iso,Finset.card_image_of_injOn]; exact size
      intro p hp q hq eq
      exact uniqueX (mem_trace.mp hp).1 (mem_trace.mp hq).1 (congrArg Prod.fst eq)
    · intro x hx; rw [iso] at hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx; exact mono v hv

end
end GenLimit.KleinbergWei.Banach.Stages
