import GenLimit.Support.RandomBitMachine.Basic

/-!
# Every-tape termination gives a uniform finite bound for each input

Halting by a fixed time is open in Cantor space because execution depends on
only a finite tape prefix. These open sets cover the compact space of Boolean
tapes. A finite subcover and absorption of halted states give the uniform
bound. This is the compactness/Konig step needed by P03 Lemma 6.3.
-/

namespace GenLimit.Support.RandomBitMachine.Machine

open Set

theorem halting_open (M : Machine) (input n : ℕ) :
    IsOpen {tape : ℕ → Bool | ∃ output, M.run input tape n = .inr output} := by
  apply isOpen_iff_mem_nhds.mpr
  intro tape htape
  apply Filter.mem_of_superset ((PiNat.isOpen_cylinder (fun _ => Bool) tape n).mem_nhds
    (PiNat.self_mem_cylinder tape n))
  intro other hother
  obtain ⟨output, houtput⟩ := htape
  refine ⟨output, ?_⟩
  rw [M.run_prefix input other tape n (fun k hk => PiNat.mem_cylinder_iff.mp hother k hk)]
  exact houtput

theorem uniform_halting_bound (M : Machine) (hM : M.AlwaysHalts) (input : ℕ) :
    ∃ N, ∀ tape : ℕ → Bool, ∃ output, M.run input tape N = .inr output := by
  let U := fun n => {tape : ℕ → Bool | ∃ output, M.run input tape n = .inr output}
  have hcover : (Set.univ : Set (ℕ → Bool)) ⊆ ⋃ n, U n := by
    intro tape _
    obtain ⟨n, output, houtput⟩ := hM input tape
    exact Set.mem_iUnion.mpr ⟨n, output, houtput⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U (M.halting_open input) hcover
  refine ⟨T.sup id, ?_⟩
  intro tape
  obtain ⟨n, hn, output, houtput⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ tape))
  exact ⟨output, M.run_halted_mono input tape (Finset.le_sup (f := id) hn) houtput⟩

end GenLimit.Support.RandomBitMachine.Machine
