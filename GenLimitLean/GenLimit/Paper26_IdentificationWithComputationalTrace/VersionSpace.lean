import GenLimit.Support.BinaryWords
import GenLimit.Paper26_IdentificationWithComputationalTrace.Edits

namespace GenLimit.ComputationalTrace

def wordsUpTo (b : ℕ) : List (List Bool) :=
  (List.range (b + 1)).flatMap Support.binaryWords

theorem mem_wordsUpTo (x : List Bool) (b : ℕ) : x ∈ wordsUpTo b ↔ x.length ≤ b := by
  simp [wordsUpTo, Support.mem_binaryWords, Nat.lt_succ_iff]

def locateState (qs : List ℕ) (q : ℕ) : Option (Fin qs.length) :=
  if h : q ∈ qs then some ⟨qs.idxOf q, List.idxOf_lt_length_iff.mpr h⟩ else none

variable {H E β : Type*}

def observed [DecidableEq β] (get : E → List β) (xs : List E) : Finset β :=
  (xs.flatMap get).toFinset

theorem observed_prefix [DecidableEq β] (get : E → List β) (s : ℕ → E) (t : ℕ) :
    observed get (textPrefix s t) = (Finset.range t).biUnion (fun n => (get (s n)).toFinset) := by
  ext a
  simp only [observed, List.mem_toFinset,List.mem_flatMap,mem_textPrefix_iff,
    Finset.mem_biUnion,Finset.mem_range]
  constructor
  · rintro ⟨_,⟨n,hn,rfl⟩,ha⟩
    exact ⟨n,hn,ha⟩
  · rintro ⟨n,hn,ha⟩
    exact ⟨s n,⟨n,hn,rfl⟩,ha⟩

def versionSpace (pool : Finset H) (allows : H → E → Bool) (xs : List E) : Finset H :=
  pool.filter (fun h => xs.all (allows h))

theorem versionSpace_stabilizes [DecidableEq H] (pool : Finset H) (allows : H → E → Bool)
    (s : ℕ → E) :
    ∃ V : Finset H, (∀ h, h ∈ V ↔ h ∈ pool ∧ ∀ n, allows h (s n) = true) ∧
      ∃ T, ∀ t ≥ T, versionSpace pool allows (textPrefix s t) = V := by
  let bad := fun n => pool.filter (fun h => !(allows h (s n)))
  obtain ⟨U, hm, T, ht⟩ := finite_observations_stabilize bad pool
    (fun _ => Finset.filter_subset _ _)
  refine ⟨pool \ U, ?_, T, fun t hT => ?_⟩
  · intro h
    by_cases hh : h ∈ pool <;> simp [hh,hm,bad]
  · ext h
    rw [← ht t hT]
    simp only [versionSpace, Finset.mem_filter,List.all_eq_true,mem_textPrefix_iff,
      Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range, bad, Bool.not_eq_true']
    constructor
    · rintro ⟨hp,hp'⟩
      refine ⟨hp, ?_⟩
      rintro ⟨n,hn,_,hf⟩
      have hh := hp' (s n) ⟨n,hn,rfl⟩
      simp_all
    · rintro ⟨hp,hn⟩
      refine ⟨hp, ?_⟩
      rintro _ ⟨n,hn',rfl⟩
      cases h : allows _ (s n) with
      | true => rfl
      | false => exact False.elim (hn ⟨n,hn',hp,h⟩)

end GenLimit.ComputationalTrace
