import GenLimit.Core.OrderedDensity
import Mathlib.Tactic

/-!
# The fixed-pod-size limit in Theorem 3.5

The final paragraph of Kleinberg--Wei's proof of Theorem 3.5 first fixes a
pod-size threshold `s` and derives the lower-density bound

`α / (2 + 4 / s)`.

It then lets the actual pod sizes grow.  The analytic passage is valid only
when every fixed-`s` estimate applies to the *same* output run (with a finite
initial exception allowed to depend on `s`).  This file records that
quantifier explicitly and proves the limiting step.  It does not assume the
stronger capacity-one certificate from `DensityAccounting.lean`, and it does
not claim that the source's dynamic pod construction already supplies the
fixed-`s` estimates.
-/

namespace GenLimit
namespace KleinbergWei
namespace PartialEnumeration

open Filter
open scoped Topology

/-- Correct finite arithmetic for the four prefix classes in the pod proof.

Here `insideMissed` and `insideOutput` count the two parts of `C` already in
pods, while `good` and `bad` count the two classes outside all pods.  Each
inside class is bounded by the output count, and `s` copies of either outside
class are charged into the output plus `insideMissed` and an error.  The
source's displayed algebra contains an extra division by `s`; the inequality
below is the dimensionally consistent conclusion. -/
theorem fixedPod_finite_counting
    (s enumerated output insideMissed insideOutput good bad error : ℕ)
    (hcover : enumerated ≤ insideMissed + insideOutput + good + bad)
    (hInsideMissed : insideMissed ≤ output)
    (hInsideOutput : insideOutput ≤ output)
    (hGood : s * good ≤ output + insideMissed + error)
    (hBad : s * bad ≤ output + insideMissed + error) :
    s * enumerated ≤ (2 * s + 4) * output + 2 * error := by
  have hscaled := Nat.mul_le_mul_left s hcover
  have hscaledInsideMissed := Nat.mul_le_mul_left s hInsideMissed
  have hscaledInsideOutput := Nat.mul_le_mul_left s hInsideOutput
  have hclasses :
      s * insideMissed + s * insideOutput + s * good + s * bad ≤
        s * output + s * output +
          (output + insideMissed + error) +
          (output + insideMissed + error) := by
    omega
  have hreplace :
      s * output + s * output +
          (output + insideMissed + error) +
          (output + insideMissed + error) ≤
        (2 * s + 4) * output + 2 * error := by
    nlinarith
  calc
    s * enumerated ≤ s *
        (insideMissed + insideOutput + good + bad) := hscaled
    _ = s * insideMissed + s * insideOutput + s * good + s * bad := by ring
    _ ≤ s * output + s * output +
          (output + insideMissed + error) +
          (output + insideMissed + error) := hclasses
    _ ≤ (2 * s + 4) * output + 2 * error := hreplace

/-- The numerical pod bound tends to the advertised factor `α / 2` as the
fixed pod-size threshold tends to infinity. -/
theorem tendsto_fixedPodBound (α : ℝ) :
    Tendsto
      (fun s : ℕ => α / (2 + 4 / (s : ℝ)))
      atTop (𝓝 (α / 2)) := by
  have hsmall :
      Tendsto (fun s : ℕ => (4 : ℝ) / (s : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hdenominator :
      Tendsto (fun s : ℕ => (2 : ℝ) + 4 / (s : ℝ))
        atTop (𝓝 2) := by
    simpa using tendsto_const_nhds.add hsmall
  simpa using tendsto_const_nhds.div hdenominator (by norm_num : (2 : ℝ) ≠ 0)

/-- The exact limiting implication used at the end of Theorem 3.5.

The crucial point is that `d` is fixed outside the quantifier over `s`.
Thus a single growing-pod run satisfying every eventual fixed-threshold
estimate has density at least `α / 2`. -/
theorem theorem_3_5_fixedPodBounds_imply_alpha_half
    {α d : ℝ}
    (hfixed : ∀ s : ℕ, 2 ≤ s → α / (2 + 4 / (s : ℝ)) ≤ d) :
    α / 2 ≤ d := by
  apply le_of_tendsto (tendsto_fixedPodBound α)
  filter_upwards [eventually_ge_atTop 2] with s hs
  exact hfixed s hs

/-- Ordered-density specialization of the fixed-pod-size limit. -/
theorem theorem_3_5_lowerDensity_of_fixedPodBounds
    (K : OrderedLanguage) (output : Language) (α : ℝ)
    (hfixed : ∀ s : ℕ, 2 ≤ s →
      α / (2 + 4 / (s : ℝ)) ≤ K.lowerDensity output) :
    α / 2 ≤ K.lowerDensity output :=
  theorem_3_5_fixedPodBounds_imply_alpha_half hfixed

/-! ## A source-shaped asymptotic certificate

The source's intermediate counting proof does not produce the ideal
capacity-one injection used in `PodCapacityOneCertificate`.  Instead, for
each fixed threshold `s`, it aims to prove a prefix inequality with
multiplicative loss `2 + 4 / s` and a finite initial error.  The following
structures encode exactly that weaker route while keeping the order of
quantifiers visible.
-/

/-- The fixed-`s` counting conclusion expected from a growing-pod run. -/
structure FixedPodRatioCertificate
    (K : OrderedLanguage) (enumerated output : Language) (s : ℕ) where
  podSize : 2 ≤ s
  overhead : ℕ → ℝ
  overhead_tendsto_zero : Tendsto overhead atTop (𝓝 0)
  prefix_bound : ∀ᶠ n : ℕ in atTop,
    K.prefixRatio enumerated n ≤
      (2 + 4 / (s : ℝ)) * K.prefixRatio output n + overhead n

namespace FixedPodRatioCertificate

/-- A fixed pod threshold gives the paper's intermediate density factor. -/
theorem lowerDensity
    {K : OrderedLanguage} {enumerated output : Language} {s : ℕ}
    (hcert : FixedPodRatioCertificate K enumerated output s) :
    K.lowerDensity enumerated / (2 + 4 / (s : ℝ)) ≤
      K.lowerDensity output := by
  have hs : (0 : ℝ) < s := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hcert.podSize)
  apply OrderedLanguage.lowerDensity_div_le_of_eventually_prefixRatio_le
    K enumerated output (2 + 4 / (s : ℝ)) (by positivity)
    hcert.overhead hcert.overhead_tendsto_zero hcert.prefix_bound

/-- Fixed-`s` specialization from a lower-density hypothesis on the partial
enumeration. -/
theorem alpha_bound
    {K : OrderedLanguage} {enumerated output : Language} {s : ℕ}
    (hcert : FixedPodRatioCertificate K enumerated output s)
    {α : ℝ} (hα : α ≤ K.lowerDensity enumerated) :
    α / (2 + 4 / (s : ℝ)) ≤ K.lowerDensity output := by
  have hs : (0 : ℝ) < s := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hcert.podSize)
  exact (div_le_div_of_nonneg_right hα (by positivity)).trans
    hcert.lowerDensity

end FixedPodRatioCertificate

/-- The quantifier-correct certificate for one growing-pod output run:
every fixed threshold `s` has its own vanishing initial-error bound, but the
languages and hence the output density remain the same. -/
structure GrowingPodRatioCertificate
    (K : OrderedLanguage) (enumerated output : Language) where
  fixed : ∀ s : ℕ, 2 ≤ s →
    FixedPodRatioCertificate K enumerated output s

namespace GrowingPodRatioCertificate

/-- The source-shaped numerical endgame of Theorem 3.5.  Once the actual
dynamic run supplies all fixed-threshold prefix estimates, the exact
`α / 2` lower-density endpoint follows without an idealized capacity-one
injection. -/
theorem alpha_half
    {K : OrderedLanguage} {enumerated output : Language}
    (hcert : GrowingPodRatioCertificate K enumerated output)
    {α : ℝ} (hα : α ≤ K.lowerDensity enumerated) :
    α / 2 ≤ K.lowerDensity output := by
  apply theorem_3_5_lowerDensity_of_fixedPodBounds K output α
  intro s hs
  exact (hcert.fixed s hs).alpha_bound hα

end GrowingPodRatioCertificate

end PartialEnumeration
end KleinbergWei
end GenLimit
