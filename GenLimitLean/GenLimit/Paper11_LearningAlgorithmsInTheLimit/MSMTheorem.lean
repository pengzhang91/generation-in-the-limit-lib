import GenLimit.Paper11_LearningAlgorithmsInTheLimit.MSMLearning

/-! # Theorem 21: learning a recursive function by maximum-similarity merging

The tagged teacher uses a finite extension of the original tape alphabet.
Its complete computations project to the original tapes. A uniform
finite-history learner returns a terminal MSM quotient, stabilizes as an
actual finite-table program on every ordering of the source, and has a
characteristic sample whose size is linear in the teacher's state count
for each fixed original tape alphabet. -/
namespace GenLimit.LearningAlgorithmsLimit.TaggedTape
open Policy MSM.Learning

variable {σ : Type} [Fintype σ] [Encodable σ] [DecidableEq σ]

private def native {n : ℕ} : Symbol σ n → Option σ
  | .inl a => some a
  | .inr _ => none

private def readTape {n : ℕ} (t : TuringTape (Symbol σ n)) : Option (TuringTape σ) := do
  let l ← t.left.mapM native
  let a ← native t.scanned
  let r ← t.right.mapM native
  return ⟨l,a,r⟩

private theorem native_list (l : List σ) (n : ℕ) :
    (l.map (Sum.inl : σ → Symbol σ n)).mapM native = some l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.mapM_cons,native,ih]

def liftIO (n : ℕ) (io : TuringIO σ X Y) : TuringIO (Symbol σ n) X Y where
  blank := .inl io.blank
  initTape x := tape n (io.initTape x)
  readOutput t := (readTape t).bind io.readOutput

private theorem read_lift (n : ℕ) (io : TuringIO σ X Y) (t : TuringTape σ) :
    (liftIO n io).readOutput (tape n t) = io.readOutput t := by
  cases t with
  | mk l a r =>
    change (readTape _).bind io.readOutput = _
    simp only [readTape,tape,native_list,native]
    rfl

private theorem recorded (io : TuringIO σ X Y) (P : TuringProgram σ) (target : X → Y)
    {x : X} {n} (h : P.runWithin n io x = some (target x)) :
    ∃ ds out, Execution (machine P io.blank) (.inl io.blank) 1 (tape _ (io.initTape x)) ds out ∧
      (liftIO _ io).readOutput out = some (target x) ∧ Path 1 ds 0 ∧
      ∀ e ∈ ds, (machine P io.blank).instruction (endpoints e).1 e.1 = ((endpoints e).2,e.2) ∧
        e ∈ allowed P := by
  simp only [TuringProgram.runWithin] at h
  split at h
  · rename_i halt
    obtain ⟨es,he⟩ := execution_of_run P io.blank n 1 (io.initTape x) halt
    obtain ⟨ds,hd,hp,_,hg⟩ := simulate he (Finset.mem_insert_self ..)
    exact ⟨ds,_,hd,(read_lift ..).trans h,hp,hg⟩
  · contradiction

theorem teacher_and_samples (io : TuringIO σ X Y) (P : TuringProgram σ) (f : X → Y)
    (I : Set X) (hf : TuringComputesOn io P f I) :
    let io' := liftIO (bound P) io
    let T := machine P io.blank
    TuringComputesOn io' T f I ∧
      LearnsWithSamples endpoints io' T f I (2 * (states T).card * Fintype.card σ) := by
  dsimp only
  have records (x : X) (hx : x ∈ I) := recorded io P f (hf x hx).choose_spec
  constructor
  · intro x hx
    obtain ⟨ds,out,he,ho,_⟩ := records x hx
    exact ⟨ds.length,by
      unfold TuringProgram.runWithin
      let final := (machine P io.blank).runConfiguration (.inl io.blank) ds.length ⟨1,tape _ (io.initTape x)⟩
      change (if final.state = 0 then (liftIO (bound P) io).readOutput final.tape else none) = _
      have heq : final = ⟨0,out⟩ := he.run
      rw [heq]
      exact ho⟩
  · obtain ⟨ha,core,hs,hcard,hq⟩ := learns_from_records endpoints (liftIO (bound P) io)
      (machine P io.blank) f I (allowed P) records
    exact ⟨ha,core,hs,hcard.trans ((allowed_card P).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (original_states_le P io.blank)))),hq⟩

/-- One tagged teacher computes the target on the whole domain and works for
every restriction. The learner's tie rule uses only visible marker labels. -/
theorem theorem_21 (io : TuringIO σ X Y) (f : X → Y)
    (hf : ∃ P, TuringComputesOn io P f Set.univ) :
    ∃ (n : ℕ) (T : TuringProgram (Symbol σ n)), TuringComputesOn (liftIO n io) T f Set.univ ∧
      ∀ I : Set X, LearnsWithSamples endpoints (liftIO n io) T f I
        (2 * (states T).card * Fintype.card σ) := by
  obtain ⟨P,hP⟩ := hf
  exact ⟨bound P,machine P io.blank,(teacher_and_samples io P f _ hP).1,
    fun I ↦ (teacher_and_samples io P f I (fun x _ ↦ hP x (Set.mem_univ _))).2⟩

end GenLimit.LearningAlgorithmsLimit.TaggedTape
