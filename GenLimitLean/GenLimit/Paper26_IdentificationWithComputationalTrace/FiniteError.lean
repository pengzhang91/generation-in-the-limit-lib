import GenLimit.Paper26_IdentificationWithComputationalTrace.ControlBound
import GenLimit.Paper26_IdentificationWithComputationalTrace.ControlTrim

namespace GenLimit.ComputationalTrace.Control
variable {μ O A : Type}

abbrev Code (k : ℕ) (O A : Type) :=
  let σ := Option (Fin k)
  σ × (σ → Bool) × (σ → O → Option (σ × A))

def decode {k : ℕ} (c : Code k O A) : Machine (Option (Fin k)) O A :=
  ⟨c.1,c.2.1,c.2.2⟩

def allows (D : Device μ O A) (time : Sample μ → ℕ) (cutoff : ℕ) {k} (c : Code k O A) (e : Sample μ) : Bool :=
  decide (e.1.length < cutoff) ||
    acceptsWithin D (decode c) (time e) ((decode c).initial,D.load e.1)

def poolSize [Fintype O] (_ : Device μ O A) (s C : ℕ) :=
  (s + 1) * (Fintype.card O + 1)^C

/-- A pruned and relabeled copy simulates every long positive instance within
the observable time budget. Every word it accepts belongs to the target. -/
theorem code_in_ball (D : Device μ O A) [Fintype O] (M : Machine ℕ O A)
    (S : Finset ℕ) (R cutoff : ℕ) (time : Sample μ → ℕ) (s : ℕ → Sample μ)
    (runs : ∀ n, cutoff ≤ (s n).1.length → ∃ ds, Finish D M (M.initial,D.load (s n).1) ds ∧
      ds.length ≤ time (s n) ∧ ∀ e ∈ (M.initial,D.load (s n).1) :: ds,
        e.1 ∈ ball M (Finset.univ : Finset O).toList (M.initial :: S.toList) R) :
    ∃ c : Code (poolSize D S.card R) O A,
      (∀ n, allows D time cutoff c (s n) = true) ∧ language D (decode c) ⊆ language D M := by
  let qs := ball M (Finset.univ : Finset O).toList (M.initial :: S.toList) R
  let N := trim M qs
  let P (k : ℕ) := ∃ c : Code k O A,
    (∀ n, allows D time cutoff c (s n) = true) ∧ language D (decode c) ⊆ language D M
  have hlen : qs.length = poolSize D S.card R := by simp [qs,ball_length,poolSize]
  apply Eq.mp (congrArg P hlen)
  refine ⟨⟨N.initial,N.final,N.table⟩, ?_, ?_⟩
  · intro n
    change (decide ((s n).1.length < cutoff) || acceptsWithin D N _ _) = true
    by_cases h : (s n).1.length < cutoff
    · simp [h]
    · simp only [h,decide_false,Bool.false_or]
      obtain ⟨ds,hf,hh,covered⟩ := runs n (Nat.le_of_not_gt h)
      have hr := hf.trim D M qs covered
      apply (acceptsWithin_iff D N _ _).mpr
      exact ⟨_,hr,by simpa using hh⟩
  · rintro w ⟨ds,hf⟩
    have hh := (acceptsWithin_iff D N ds.length _).mpr ⟨ds,hf,le_rfl⟩
    exact accepted_within D M (trim_sound D M qs _ _ _ hh)

structure Guess (O A : Type) where
  cutoff : ℕ
  short : Finset (List Bool)
  size : ℕ
  codes : Finset (Code size O A)

/-- Run every surviving table for the same finite time. Dovetailing these
total tests over time semidecides the language represented by the output. -/
def Guess.test (H : Guess O A) (D : Device μ O A) (w : List Bool) (time : ℕ) : Bool :=
  if w.length < H.cutoff then decide (w ∈ H.short)
  else decide (∀ c : H.codes, acceptsWithin D (decode c.val) time ((decode c.val).initial,D.load w) = true)

def Guess.language (H : Guess O A) (D : Device μ O A) : Set (List Bool) :=
  {w | ∃ n, H.test D w n = true}

private def shortExample (cutoff : ℕ) (e : Sample μ) :=
  if e.1.length < cutoff then [e.1] else []

private def seenExample (e : Sample μ) := e.2.map Prod.fst

variable [Fintype O] [DecidableEq O] [Fintype A]

private def fromSize (D : Device μ O A) (time : Sample μ → ℕ) (cutoff k : ℕ) (short : Finset (List Bool))
    (xs : List (Sample μ)) : Guess O A :=
  ⟨cutoff,short,k,versionSpace Finset.univ (@allows _ _ _ D time cutoff k) xs⟩

def scopedLearner (D : Device μ O A) (time : Sample μ → ℕ) (scope : Finset ℕ → ℕ × ℕ)
    (xs : List (Sample μ)) : Guess O A :=
  let b := scope (observed seenExample xs)
  fromSize D time b.1 b.2 (observed (shortExample b.1) xs) xs

theorem identifies_in_scope (D : Device μ O A) (time : Sample μ → ℕ) (scope : Finset ℕ → ℕ × ℕ)
    (M : Machine ℕ O A) (s : ℕ → Sample μ) {budget} (hs : Presentation D M budget s)
    (complete : ∀ S : Finset ℕ, (∀ n e, e ∈ (s n).2 → e.1 ∈ S) →
      ∃ c : Code (scope S).2 O A, (∀ n, allows D time (scope S).1 c (s n) = true) ∧
        language D (decode c) ⊆ language D M) :
    ∃ H : Guess O A, H.language D = language D M ∧
      ∃ T, ∀ t ≥ T, scopedLearner D time scope (textPrefix s t) = H := by
  obtain ⟨Q,_,_,hQ⟩ := hs.finiteStates
  have seenBound (n : ℕ) : (seenExample (s n)).toFinset ⊆ Q := by
    intro q hq
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    exact hQ n e he
  obtain ⟨S,hS,T₀,h₀⟩ := finite_observations_stabilize _ _ seenBound
  let cutoff := (scope S).1
  have shortBound (n : ℕ) : (shortExample cutoff (s n)).toFinset ⊆ (wordsUpTo cutoff).toFinset := by
    by_cases hl : (s n).1.length < cutoff <;>
      simp [shortExample,hl,mem_wordsUpTo, Nat.le_of_lt] at *

  obtain ⟨U,hU,T₁,h₁⟩ := finite_observations_stabilize _ _ shortBound
  have hseen t (ht : t ≥ T₀) := (observed_prefix seenExample s t).trans (h₀ t ht)
  have hshort t (ht : t ≥ T₁) := (observed_prefix (shortExample cutoff) s t).trans (h₁ t ht)
  let k := (scope S).2
  obtain ⟨c,hc,sub⟩ := complete S (fun n e he => (hS _).mpr
    ⟨n,List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,he,rfl⟩)⟩)
  classical
  obtain ⟨V,hV,T₂,h₂⟩ := versionSpace_stabilizes Finset.univ (@allows _ _ _ D time cutoff k) s
  let H : Guess O A := ⟨cutoff,U,k,V⟩
  refine ⟨H, ?_, max (max T₀ T₁) T₂, fun t ht => ?_⟩
  · ext w
    have cover : w ∈ language D M ↔ ∃ n, (s n).1 = w := by rw [← hs.covers]; rfl
    by_cases hl : w.length < cutoff
    · have hmem : w ∈ U ↔ ∃ n, (s n).1 = w := by
        rw [hU]
        constructor
        · rintro ⟨n,hn⟩
          by_cases h : (s n).1.length < cutoff <;> simp_all [shortExample]
        · rintro ⟨n,rfl⟩
          exact ⟨n,by simp [shortExample,hl]⟩
      simpa [Guess.language,Guess.test,H,hl] using hmem.trans cover.symm
    · change (∃ time, H.test D w time = true) ↔ _
      simp only [Guess.test,H,hl,if_false,decide_eq_true_eq,Subtype.forall]
      constructor
      · rintro ⟨n,hh⟩
        exact sub (accepted_within D (decode c) (hh c ((hV c).mpr ⟨Finset.mem_univ _,hc⟩)))
      · intro hw
        obtain ⟨n,rfl⟩ := cover.mp hw
        refine ⟨time (s n),fun a ha => ?_⟩
        simpa [allows,hl] using ((hV a).mp ha).2 n
  · unfold scopedLearner
    rw [hseen t (by omega)]
    change fromSize D time cutoff k (observed (shortExample cutoff) (textPrefix s t)) _ = H
    rw [hshort t (by omega)]
    exact congrArg (Guess.mk cutoff U k) (h₂ t (by omega))

def learner (D : Device μ O A) (C cutoff : ℕ) : List (Sample μ) → Guess O A :=
  scopedLearner D (fun e => e.2.length + C) (fun S => (cutoff,poolSize D S.card C))

theorem identifies_finite_error (D : Device μ O A) (C cutoff : ℕ) (M : Machine ℕ O A)
    (s : ℕ → Sample μ) (hs : Presentation D M (FiniteBound C cutoff) s) :
    ∃ H : Guess O A, H.language D = language D M ∧
      ∃ T, ∀ t ≥ T, learner D C cutoff (textPrefix s t) = H :=
  by
    apply identifies_in_scope D _ _ M s hs
    intro S ho
    apply code_in_ball D M S C cutoff
    intro n hn
    obtain ⟨ds,hf,he⟩ := hs.traces n
    obtain ⟨j,hj,ed⟩ := he hn
    have hh := ed.length_bounds.1
    simp only [List.length_cons] at hh
    exact ⟨ds,hf,by omega,cover_finite_error D M hf ⟨j,hj,ed⟩ (ho n)⟩

end GenLimit.ComputationalTrace.Control
