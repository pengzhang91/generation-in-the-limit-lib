import GenLimit.Paper11_LearningAlgorithmsInTheLimit.PolicyTrajectories

/-! # Theorem 16 on completed single-tape observations
The finite history converter schedules every nonempty scanned prefix of
every observed trajectory. It never requests an observation from the future.
Running a rational learner twice recovers both the action and the halt
decision. The finite product replays every trajectory on its original tape. -/
namespace GenLimit.LearningAlgorithmsLimit.Policy
open Rational
variable {σ X Y : Type*} [Encodable σ]

structure Observation (σ X Y : Type*) where
  input : X
  value : Y
  events : List (Event σ)

private def pick (blank : σ) (label : Label σ) (es : List (Event σ)) (k : ℕ) : List σ × Action σ :=
  let qs := queries label es
  (qs[k % qs.length]?).getD ([blank],(blank,.stay))

private theorem pick_mem (blank : σ) (label : Label σ) {es : List (Event σ)} (he : es ≠ []) (k : ℕ) :
    pick blank label es k ∈ queries label es := by
  have hp : 0 < (queries label es).length := by
    rw [queries_length]; exact List.length_pos_iff.mpr he
  dsimp only [pick]
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hp)]
  exact List.getElem_mem ..

private theorem pick_covers {label : Label σ} {es : List (Event σ)} {z}
    (hz : z ∈ queries label es) (blank : σ) : ∃ k, pick blank label es k = z := by
  obtain ⟨k,hk,hh⟩ := List.getElem_of_mem hz
  exact ⟨k,by simpa [pick,Nat.mod_eq_of_lt hk,List.getElem?_eq_getElem hk] using hh⟩

private def asLabel (p : List σ × Action σ) : LabeledObservation (List σ) (Action σ) :=
  ⟨p.1,some p.2⟩

/-- Causal enumeration of queried words and observed rational outputs. -/
def convert (blank : σ) (label : Label σ) (xs : List (Observation σ X Y)) :
    List (LabeledObservation (List σ) (Action σ)) :=
  (List.range xs.length).map (fun n ↦ asLabel (pick blank label
    (((xs[n.unpair.1]?).map Observation.events).getD []) n.unpair.2))

private theorem convert_prefix (blank : σ) (label : Label σ) (s : ℕ → Observation σ X Y) (n : ℕ) :
    convert blank label (textPrefix s n) = textPrefix (fun k ↦ asLabel
      (pick blank label (s k.unpair.1).events k.unpair.2)) n := by
  unfold convert
  rw [textPrefix_length]
  apply List.map_congr_left
  intro k hk
  have hlt := (Nat.unpair_left_le k).trans_lt (List.mem_range.mp hk)
  simp [textPrefix,List.getElem?_map,List.getElem?_range hlt]

private theorem learn_labels [Fintype σ] (R : IOAlgorithm σ (Action σ)) (hr : Solves R)
    (P : TuringProgram σ) (blank : σ) (s : ℕ → Observation σ X Y)
    (hex : ∀ n, ∃ t out, Execution P blank 1 t (s n).events out) (label : Label σ) :
    ∃ T : Table (Action σ),
      (∀ n, CorrectAt T T.start T.fallback label (s n).events) ∧
      ∃ N, ∀ n ≥ N, R (convert blank label (textPrefix s n)) = T := by
  let target := policyTable P blank label
  let z (k : ℕ) := pick blank label (s k.unpair.1).events k.unpair.2
  have hz (k : ℕ) : z k ∈ queries label (s k.unpair.1).events := by
    obtain ⟨_,_,h⟩ := hex k.unpair.1
    exact pick_mem _ _ (fun he ↦ Nat.one_ne_zero (h.halt_iff.mpr he)) _
  have ht (n : ℕ) : CorrectAt target target.start target.fallback label (s n).events := by
    obtain ⟨_,_,h⟩ := hex n
    exact policy_correct h (by simp [states]) _ _
  have heq (k : ℕ) : target.output (z k).1 = (z k).2 := ht k.unpair.1 _ _ (hz k)
  obtain ⟨T,hT,N,hN⟩ := hr target (fun k ↦ (z k).1) (fun k ↦ query_nonempty (hz k))
  refine ⟨T,?_,N,?_⟩
  · intro n w v hw
    obtain ⟨k,hk⟩ := pick_covers hw blank
    have hz' : z (Nat.pair n k) = (w,v) := by simpa [z] using hk
    have h := (hT _ ⟨Nat.pair n k,rfl⟩).trans (heq (Nat.pair n k))
    simpa [hz',Table.output] using h
  · intro n hn
    rw [convert_prefix]
    have hh : (fun k ↦ asLabel (z k)) = labeledStream
        (fun w ↦ some (target.output w)) (fun k ↦ (z k).1) := by
      funext k
      simp [asLabel,labeledStream,heq]
    simpa only [← hh] using hN n hn

/-- A single learner on the full observed triples. Its two rational calls
receive only scanned-word/label pairs of the types specified by the paper. -/
def reducedLearner [Fintype σ] (R : IOAlgorithm σ (Action σ)) (blank : σ) :
    GenLimit.Learner (Observation σ X Y) (TuringProgram σ) := fun history ↦
  product (R (convert blank (fun a _ ↦ a) history))
    (R (convert blank (fun _ done ↦ marker blank done) history)) blank

/-- Theorem 16: any rational-function learner yields one policy-trajectory
learner for every teacher, restricted source and ordering of the source. -/
theorem theorem_16 [Fintype σ] (R : IOAlgorithm σ (Action σ)) (hr : Solves R)
    (io : TuringIO σ X Y) (P : TuringProgram σ) (target : X → Y) (I : Set X)
    (s : ℕ → Observation σ X Y) (hI : Set.range (fun n ↦ (s n).input) = I)
    (hs : ∀ n, (s n).value = target (s n).input ∧ ∃ out,
      Execution P io.blank 1 (io.initTape (s n).input) (s n).events out ∧
      io.readOutput out = some (s n).value) :
    LearnsByCriterion (reducedLearner R io.blank) s (fun Q ↦ TuringComputesOn io Q target I) := by
  have hex (n : ℕ) : ∃ t out, Execution P io.blank 1 t (s n).events out := by
    obtain ⟨out,h,_⟩ := (hs n).2
    exact ⟨_,out,h⟩
  obtain ⟨U,hu,Nu,hNu⟩ := learn_labels R hr P io.blank s hex (fun a _ ↦ a)
  obtain ⟨V,hv,Nv,hNv⟩ := learn_labels R hr P io.blank s hex (fun _ done ↦ marker io.blank done)
  refine ⟨product U V io.blank,?_,max Nu Nv,fun n hn ↦ ?_⟩
  · rw [← hI]
    rintro _ ⟨n,rfl⟩
    obtain ⟨out,h,ho⟩ := (hs n).2
    have hrp := replay h U V U.start V.start (by simp [Table.states]) (by simp [Table.states])
      _ _ (hu n) (hv n)
    simp [pack] at hrp
    exact ⟨(s n).events.length,by simp [TuringProgram.runWithin,hrp.run,ho,(hs n).1]⟩
  · exact congrArg₂ (fun A B ↦ product A B io.blank)
      (hNu n ((le_max_left _ _).trans hn)) (hNv n ((le_max_right _ _).trans hn))

end GenLimit.LearningAlgorithmsLimit.Policy
