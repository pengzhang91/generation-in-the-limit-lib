import GenLimit.Paper11_LearningAlgorithmsInTheLimit.MergeReplay
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.RationalReduction

namespace GenLimit.LearningAlgorithmsLimit.MSM.Learning
open Policy ObservedTree Replay

variable {σ : Type} [Fintype σ] [Encodable σ] [DecidableEq σ]

def samples (h : List (Observation σ X Y)) : Samples σ (Action σ) :=
  (h.map Observation.events).toFinset

noncomputable def learner (en : Event σ → ℕ × ℕ) (blank : σ) (h : List (Observation σ X Y)) :
    TuringProgram σ := guess en blank (content (samples h))

def Valid (io : TuringIO σ X Y) (P : TuringProgram σ) (f : X → Y) (I : Set X)
    (o : Observation σ X Y) := o.input ∈ I ∧ o.value = f o.input ∧ ∃ out,
    Execution P io.blank 1 (io.initTape o.input) o.events out ∧ io.readOutput out = some o.value

def HasCore (h : List (Observation σ X Y)) (core : Finset X) :=
  ∀ x ∈ core, ∃ o ∈ h, o.input = x

def LearnsWithSamples (en : Event σ → ℕ × ℕ) (io : TuringIO σ X Y)
    (P : TuringProgram σ) (f : X → Y) (I : Set X) (budget : ℕ) : Prop :=
  (∀ h : List (Observation σ X Y), (∀ o ∈ h, Valid io P f I o) →
    IsMSMOutput en io.blank (samples h) (learner en io.blank h)) ∧
  ∃ core : Finset X, (core : Set X) ⊆ I ∧ core.card ≤ budget ∧
    ∃ Q : TuringProgram σ, TuringComputesOn io Q f I ∧
      (∀ h : List (Observation σ X Y), (∀ o ∈ h, Valid io P f I o) → HasCore h core →
        learner en io.blank h = Q) ∧
      ∀ s : ℕ → Observation σ X Y, Covers (fun n ↦ (s n).input) I →
        (∀ n, Valid io P f I (s n)) →
        GenLimit.StabilizesTo (fun t ↦ learner en io.blank (GenLimit.textPrefix s t)) Q

theorem execution_unique {P : TuringProgram σ} {blank q t es out ds out'}
    (h : Execution P blank q t es out) (g : Execution P blank q t ds out') :
    es = ds ∧ out = out' := by
  induction h generalizing ds out' with
  | halt => cases g with | halt => exact ⟨rfl,rfl⟩ | step hn _ => exact (hn rfl).elim
  | step hn ht ih =>
    cases g with
    | halt => exact (hn rfl).elim
    | step _ gt =>
      obtain ⟨rfl,rfl⟩ := ih gt
      exact ⟨rfl,rfl⟩

/-- The learner depends exclusively on its recorded PTOs. One input per
used transition suffices, even when some inputs in the source never appear
in the characteristic set. -/
theorem learns_from_records (en : Event σ → ℕ × ℕ) (io : TuringIO σ X Y)
    (P : TuringProgram σ) (f : X → Y) (I : Set X) (alphabet : Finset (Event σ))
    (records : ∀ x ∈ I, ∃ es out, Execution P io.blank 1 (io.initTape x) es out ∧
      io.readOutput out = some (f x) ∧ Path en 1 es 0 ∧
      ∀ e ∈ es, P.instruction (en e).1 e.1 = ((en e).2,e.2) ∧ e ∈ alphabet) :
    LearnsWithSamples en io P f I alphabet.card := by
  classical
  let tr (x : X) := if hx : x ∈ I then (records x hx).choose else []
  have spec (x : X) (hx : x ∈ I) : ∃ out, Execution P io.blank 1 (io.initTape x) (tr x) out ∧
      io.readOutput out = some (f x) ∧ Path en 1 (tr x) 0 ∧
      ∀ e ∈ tr x, P.instruction (en e).1 e.1 = ((en e).2,e.2) ∧ e ∈ alphabet := by
    simpa [tr,hx] using (records x hx).choose_spec
  have obs {o : Observation σ X Y} (ho : Valid io P f I o) : o.events = tr o.input := by
    obtain ⟨out,he,_⟩ := ho.2.2
    obtain ⟨out',he',_⟩ := spec _ ho.1
    exact (execution_unique he he').1
  let C := alphabet.filter (fun e ↦ ∃ x ∈ I, e ∈ tr x)
  have memC {x} (hx : x ∈ I) {e} (he : e ∈ tr x) : e ∈ C := by
    obtain ⟨_,_,_,_,hg⟩ := spec _ hx
    exact Finset.mem_filter.mpr ⟨(hg e he).2,x,hx,he⟩
  have ok : ∀ e ∈ C, P.instruction (en e).1 e.1 = ((en e).2,e.2) := by
    intro e he
    obtain ⟨x,hx,hm⟩ := (Finset.mem_filter.mp he).2
    obtain ⟨_,_,_,_,hg⟩ := spec x hx
    exact (hg _ hm).1
  have ofHist {h : List (Observation σ X Y)} {es} (he : es ∈ samples h) :
      ∃ o ∈ h, o.events = es := List.mem_map.mp (List.mem_toFinset.mp he)
  have subsetC {h : List (Observation σ X Y)} (hv : ∀ o ∈ h, Valid io P f I o) : content (samples h) ⊆ C := by
    intro e he
    obtain ⟨es,hes,hm⟩ := Finset.mem_biUnion.mp he
    obtain ⟨o,ho,rfl⟩ := ofHist hes
    exact memC (hv o ho).1 ((obs (hv o ho)) ▸ List.mem_toFinset.mp hm)
  constructor
  · intro h hv
    apply guess_isMSM io.blank _ P.instruction (fun e he ↦ ok e (subsetC hv he))
    intro es hes
    obtain ⟨o,ho,rfl⟩ := ofHist hes
    obtain ⟨_,_,_,hp,_⟩ := spec _ (hv o ho).1
    exact ⟨0,obs (hv o ho) ▸ hp⟩
  let witness (e : ↥C) := ((Finset.mem_filter.mp e.property).2).choose
  have hw (e : ↥C) : witness e ∈ I ∧ e.val ∈ tr (witness e) := ((Finset.mem_filter.mp e.property).2).choose_spec
  let core := Finset.univ.image witness
  have sub : (core : Set X) ⊆ I := by
    intro x hx
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hx
    exact (hw e).1
  have count : core.card ≤ C.card := by simpa [core] using (Finset.card_image_le (f := witness) (s := Finset.univ))
  let Q := guess en io.blank C
  have stable {h : List (Observation σ X Y)} (hv : ∀ o ∈ h, Valid io P f I o) (hall : HasCore h core) :
      learner en io.blank h = Q := by
    apply congrArg (guess en io.blank)
    apply Finset.Subset.antisymm (subsetC hv)
    intro e he
    let v : ↥C := ⟨e,he⟩
    obtain ⟨o,ho,hx⟩ := hall (witness v) (Finset.mem_image_of_mem _ (Finset.mem_univ v))
    apply Finset.mem_biUnion.mpr
    refine ⟨o.events,List.mem_toFinset.mpr (List.mem_map.mpr ⟨o,ho,rfl⟩),List.mem_toFinset.mpr ?_⟩
    rw [obs (hv o ho),hx]
    exact (hw v).2
  refine ⟨core,sub,count.trans (Finset.card_le_card (Finset.filter_subset ..)),Q,?_,fun h hv hh ↦ stable hv hh,?_⟩
  · intro x hx
    obtain ⟨out,he,hr,hp,_⟩ := spec x hx
    have run := replay ok he hp (fun _ hm ↦ memC hx hm)
    exact ⟨(tr x).length,by simp [Q,TuringProgram.runWithin,run.run,hr]⟩
  · intro s hc hv
    obtain ⟨N,hN⟩ := finite_sample_cover_eventually_seen _ _ hc core sub
    refine ⟨N,fun n hn ↦ stable (fun o ho ↦ ?_) (fun x hx ↦ ?_)⟩
    · obtain ⟨t,_,rfl⟩ := GenLimit.mem_textPrefix_iff.mp ho
      exact hv t
    · obtain ⟨t,ht,he⟩ := hN x hx
      exact ⟨s t,GenLimit.mem_textPrefix_iff.mpr ⟨t,ht.trans_le hn,rfl⟩,he⟩

end GenLimit.LearningAlgorithmsLimit.MSM.Learning
