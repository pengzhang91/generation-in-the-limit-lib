import GenLimit.Paper03_HallucinationAndModeCollapse.BreadthModel
import GenLimit.Paper03_HallucinationAndModeCollapse.OracleGeneration
import GenLimit.Support.OracleSearchMinimality

/-!
# Proposition 6.5: a certified full-support sampler

Draw a full-support geometric natural-number seed and search upward from it
for the first unseen member of the named language. Infinite languages make
this deterministic membership-query search terminate for every finite seed.
Every unseen member `x` is returned when the seed is `x`, so the pushforward
PMF has exactly the required support. Empty training samples give the literal
Proposition 6.5 conclusion. This is an alternative to the printed rejection
sampler; no real-valued probability oracle is used by the program.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit GenLimit.Support GenLimit.DiscreteIID

def samplerIndex (input : List ℕ) : ℕ := (input[0]?).getD 0
def samplerSeed (input : List ℕ) : ℕ := (input[1]?).getD 0
def samplerSample (input : List ℕ) : List ℕ := input.tail.tail

theorem samplerIndex_primrec : Primrec samplerIndex :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)

theorem samplerSeed_primrec : Primrec samplerSeed :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id (Primrec.const 1)) (Primrec.const 0)

theorem samplerSample_primrec : Primrec samplerSample := Primrec.list_tail.comp Primrec.list_tail

def samplerQueries (input : List ℕ × ℕ) : List ℕ :=
  [Nat.pair (samplerIndex input.1) (samplerSeed input.1 + input.2)]

theorem samplerQueries_primrec : Primrec samplerQueries :=
  Primrec.list_cons.comp
    (Primrec₂.natPair.comp (samplerIndex_primrec.comp Primrec.fst)
      (Primrec.nat_add.comp (samplerSeed_primrec.comp Primrec.fst) Primrec.snd))
    (Primrec.const [])

def samplerPost (data : (List ℕ × ℕ) × List ℕ) : Option ℕ :=
  let y := samplerSeed data.1.1 + data.1.2
  if y ∉ samplerSample data.1.1 ∧ (data.2[0]?).getD 0 = 1 then some y else none

theorem samplerPost_computable : Computable samplerPost := by
  let D := (List ℕ × ℕ) × List ℕ
  have hy : Primrec (fun data : D => samplerSeed data.1.1 + data.1.2) :=
    Primrec.nat_add.comp (samplerSeed_primrec.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  have hm : PrimrecPred (fun data : D => samplerSeed data.1.1 + data.1.2 ∈ samplerSample data.1.1) :=
    (Primrec.nat_lt.comp
      (Primrec.list_idxOf.comp hy (samplerSample_primrec.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.list_length.comp (samplerSample_primrec.comp (Primrec.fst.comp Primrec.fst)))).of_eq
      (fun _ => List.idxOf_lt_length_iff)
  have ha : PrimrecPred (fun data : D => (data.2[0]?).getD 0 = 1) :=
    Primrec.eq.comp
      (Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd (Primrec.const 0))
        (Primrec.const 0)) (Primrec.const 1)
  exact (Primrec.ite (hm.not.and ha) (Primrec.option_some.comp hy) (Primrec.const none)).to_comp

def samplerProgram : OracleSearchProgram where
  queries := samplerQueries
  queries_primrec := samplerQueries_primrec
  output := samplerPost
  output_computable := samplerPost_computable

open scoped Classical in
theorem samplerProgram_stage (O : OracleFamily) (input : List ℕ) (q : ℕ) :
    samplerProgram.stage (generationOracle O) input q =
      if samplerSeed input + q ∉ samplerSample input ∧
          samplerSeed input + q ∈ O.language (samplerIndex input)
      then some (samplerSeed input + q) else none := by
  simp only [OracleSearchProgram.stage, samplerProgram, samplerQueries, List.map_cons,
    List.map_nil, samplerPost, List.getElem?_cons_zero, Option.getD_some]
  simp [generationOracle, O.query_spec, Nat.unpair_pair]

theorem samplerProgram_terminates (O : OracleFamily) :
    samplerProgram.Terminates (generationOracle O) := by
  intro input
  have hinf := (O.infinite' (samplerIndex input)).diff (samplerSample input).toFinset.finite_toSet
  obtain ⟨y, hy, hseed⟩ := hinf.exists_gt (samplerSeed input)
  refine ⟨y - samplerSeed input, y, ?_⟩
  rw [samplerProgram_stage]
  have he : samplerSeed input + (y - samplerSeed input) = y := Nat.add_sub_of_le hseed.le
  rw [he, if_pos ⟨by simpa using hy.2, hy.1⟩]

def seededFreshSample (O : OracleFamily) (xs : List ℕ) (j seed : ℕ) : ℕ :=
  samplerProgram.run (generationOracle O) (samplerProgram_terminates O) (j :: seed :: xs)

theorem seededFreshSample_spec (O : OracleFamily) (xs : List ℕ) (j seed : ℕ) :
    seededFreshSample O xs j seed ∈ O.language j ∧ seededFreshSample O xs j seed ∉ xs := by
  obtain ⟨q, hq⟩ := samplerProgram.run_stage (generationOracle O) (samplerProgram_terminates O)
    (j :: seed :: xs)
  rw [samplerProgram_stage] at hq
  simp only [samplerSeed, samplerIndex, samplerSample, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some, List.tail_cons] at hq
  split at hq
  · rename_i h
    have he : seededFreshSample O xs j seed = seed + q := (Option.some.inj hq).symm
    rw [he]
    exact ⟨h.2, h.1⟩
  · simp at hq

theorem seededFreshSample_self (O : OracleFamily) (xs : List ℕ) (j x : ℕ)
    (hx : x ∈ O.language j) (hfresh : x ∉ xs) : seededFreshSample O xs j x = x := by
  apply samplerProgram.run_eq_of_stage_zero
  rw [samplerProgram_stage]
  simp [samplerSeed, samplerIndex, samplerSample, hx, hfresh]

noncomputable def exactFreshSampler (O : OracleFamily) (xs : List ℕ) (j : ℕ) : PMF ℕ :=
  positiveGeometric.map (seededFreshSample O xs j)

theorem exactFreshSampler_support (O : OracleFamily) (xs : List ℕ) (j : ℕ) :
    (exactFreshSampler O xs j).support = O.language j \ {x | x ∈ xs} := by
  ext x
  simp only [exactFreshSampler, PMF.support_map, Set.mem_image, Set.mem_diff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨seed, _, rfl⟩
    exact seededFreshSample_spec O xs j seed
  · rintro ⟨hx, hfresh⟩
    exact ⟨x, positiveGeometric_support x, seededFreshSample_self O xs j x hx hfresh⟩

theorem exactFreshSampler_query_spec (O : OracleFamily) (xs : List ℕ) (j x : ℕ) :
    (O.query j x && !(listContains xs x)) = true ↔ x ∈ (exactFreshSampler O xs j).support := by
  rw [exactFreshSampler_support]
  simp [O.query_spec, listContains]

theorem seededFreshSample_computable (O : OracleFamily) (hO : Computable₂ O.query) :
    Computable (fun z : (List ℕ × ℕ) × ℕ => seededFreshSample O z.1.1 z.1.2 z.2) := by
  have ho : Computable (generationOracle O) :=
    (Computable.cond (hO.comp (Primrec.fst.comp Primrec.unpair).to_comp
      (Primrec.snd.comp Primrec.unpair).to_comp) (Computable.const 1) (Computable.const 0)).of_eq
      (fun code => by dsimp [generationOracle]; cases O.query code.unpair.1 code.unpair.2 <;> simp)
  have hi : Computable (fun z : (List ℕ × ℕ) × ℕ => z.1.2 :: z.2 :: z.1.1) :=
    Computable.list_cons.comp (Computable.snd.comp Computable.fst)
      (Computable.list_cons.comp Computable.snd (Computable.fst.comp Computable.fst))
  exact (samplerProgram.run_computable ho (samplerProgram_terminates O)).comp hi

/-- Proposition 6.5 in the infinite-language generation regime: zero training input has support
exactly the named language; its numerical-seed sampler is computable whenever
membership is computable. -/
theorem proposition_6_5 (O : OracleFamily) :
    (∀ j, (exactFreshSampler O [] j).support = O.language j) ∧
      (Computable₂ O.query →
        Computable (fun z : (List ℕ × ℕ) × ℕ => seededFreshSample O z.1.1 z.1.2 z.2)) ∧
      (∀ xs j x, (O.query j x && !(listContains xs x)) = true ↔
        x ∈ (exactFreshSampler O xs j).support) :=
  ⟨by intro j; simpa using exactFreshSampler_support O [] j,
    seededFreshSample_computable O, exactFreshSampler_query_spec O⟩

end GenLimit.HallucinationModeCollapse
