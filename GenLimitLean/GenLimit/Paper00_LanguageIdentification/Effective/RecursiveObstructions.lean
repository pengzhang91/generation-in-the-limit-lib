import GenLimit.Paper00_LanguageIdentification.Effective.MindChanges
import GenLimit.Paper00_LanguageIdentification.Text.Superfinite

/-! # Recursive counterpresentations (Appendix I.5 and I.8) -/

namespace GenLimit.Gold.Effective

open Nat.Partrec (Code)
open GenLimit.Support

private def tailStream (h : List ℕ) (x n : ℕ) := (h[n]?).getD x

private theorem tail_comp (h : List ℕ) (x : ℕ) : Computable (tailStream h x) :=
  Computable.option_getD (Computable.list_getElem?.comp (Computable.const h) Computable.id)
    (Computable.const x)

private theorem tail_prefix (h : List ℕ) (x n : ℕ) :
    textPrefix (tailStream h x) (h.length + n) = h ++ List.replicate n x := by
  induction n with
  | zero =>
    apply List.ext_getElem
    · simp
    · intro i _ hi
      simp at hi
      simp [textPrefix, tailStream, hi]
  | succ n ih =>
    rw [Nat.add_succ, textPrefix_succ, ih, List.replicate_succ', List.append_assoc]
    simp [tailStream]

private theorem tail_range (h : List ℕ) (x : ℕ) :
    Set.range (tailStream h x) = insert x (↑h.toFinset : Language) := by
  ext y
  constructor
  · rintro ⟨n,rfl⟩
    by_cases hn : n < h.length
    · exact Or.inr (by simp [tailStream, hn])
    · simp [tailStream, List.getElem?_eq_none (Nat.le_of_not_lt hn)]
  · rintro (rfl | hm)
    · exact ⟨h.length, by simp [tailStream]⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hm)
      exact ⟨i, by simpa [tailStream, i.isLt] using hi⟩

private theorem generator_unique {c : Code} {A B : Language}
    (ha : Generator c A) (hb : Generator c B) : A = B :=
  Set.ext fun x => (ha x).trans (hb x).symm

/-- I.8 with an infinite witness possessing a recursive presentation. -/
theorem no_generator_recursive_text {C : Set Language} (finite : Text.finiteLanguages ⊆ C)
    {L : Language} (hl : L ∈ C) (hinf : L.Infinite)
    {v : ℕ → ℕ} (hv : Computable v) (hp : Presents v L) :
    ¬ Identifiable Generator recursiveText C := by
  rintro ⟨M, hc, learns⟩
  have changes (h : List ℕ) : ∃ a t, M (h ++ List.replicate t (v a)) ≠ M h := by
    by_contra! fixed
    have same (a : ℕ) : Generator (M h) (insert (v a) (↑h.toFinset : Language)) := by
      obtain ⟨c, hn, T, ht⟩ := learns _ (finite (Finset.finite_toSet h.toFinset |>.insert (v a)))
        (tailStream h (v a)) ⟨tail_comp .., tail_range ..⟩
      have hh := ht (h.length + T) (Nat.le_add_left ..)
      rw [tail_prefix, fixed] at hh
      exact hh.symm ▸ hn
    have cover : L ⊆ insert (v 0) (↑h.toFinset : Language) := by
      rintro x hx
      obtain ⟨a,rfl⟩ := hp.symm ▸ hx
      rw [← generator_unique (same a) (same 0)]
      exact Set.mem_insert ..
    exact hinf ((Finset.finite_toSet h.toFinset |>.insert (v 0)).subset cover)
  obtain ⟨s, cs, rng, hbad⟩ := mind_change_stream M hc v hv changes
  obtain ⟨_, _, T, stable⟩ := learns L hl s ⟨cs, rng.trans hp⟩
  obtain ⟨u,hu,w,hw,ne⟩ := hbad T
  exact ne ((stable u hu).trans (stable w hw).symm)

private def parity (n : ℕ) := n % 2

private theorem parity_comp : Computable parity :=
  (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)).to_comp

private theorem bit_set (s : ℕ → ℕ) (bits : ∀ n, s n < 2) : bit {n | s n = 1} = s := by
  funext n
  have h := bits n
  by_cases hi : s n = 1
  · simp [bit, hi]
  · simp [bit, hi]
    omega

/-- I.5. Even the methodical informant cannot yield an effective generator
identifier for the class of all recursive languages. -/
theorem no_generator_recursive_methodical :
    ¬ Identifiable Generator methodical recursiveLanguages := by
  rintro ⟨M, hc, learns⟩
  let P (h : List ℕ) := M (h.map parity)
  have hP : Computable P := hc.comp (ComputableLists.map Computable.id (parity_comp.comp Computable.snd).to₂)
  have changes (h : List ℕ) : ∃ a t, P (h ++ List.replicate t (parity a)) ≠ P h := by
    by_contra! fixed
    let hist := h.map parity
    let A (z : ℕ) := {n | tailStream hist z n = 1}
    have valid (z : ℕ) (hz : z < 2) : bit (A z) = tailStream hist z := by
      apply bit_set
      intro n
      by_cases hlen : n < hist.length
      · have mem : hist[n] ∈ h.map parity := List.getElem_mem hlen
        obtain ⟨x, _, hx⟩ := List.mem_map.mp mem
        simpa [tailStream, hlen, ← hx, parity] using Nat.mod_lt x (by decide : 0 < 2)
      · simpa [tailStream, List.getElem?_eq_none (Nat.le_of_not_lt hlen)] using hz
    have name (z : ℕ) (hz : z < 2) : Generator (P h) (A z) := by
      have hrec : A z ∈ recursiveLanguages := by
        change Computable (bit (A z))
        rw [valid z hz]
        exact tail_comp ..
      obtain ⟨c, hn, T, ht⟩ := learns (A z) hrec (tailStream hist z) (valid z hz).symm
      have hh := ht (hist.length + T) (Nat.le_add_left ..)
      rw [tail_prefix] at hh
      have e := fixed z T
      have hz' : parity z = z := Nat.mod_eq_of_lt hz
      simp [P, hz', List.map_replicate] at e
      change Generator (M (h.map parity)) (A z)
      rwa [e.symm.trans hh]
    have eq := Set.ext_iff.mp (generator_unique (name 0 (by decide)) (name 1 (by decide))) hist.length
    simp [A, tailStream] at eq
  obtain ⟨s, cs, rng, hbad⟩ := mind_change_stream P hP parity parity_comp changes
  have bounds (n : ℕ) : s n < 2 := by
    obtain ⟨x,h⟩ := rng ▸ Set.mem_range_self n
    rw [← h]
    exact Nat.mod_lt _ (by decide)
  let L := {n | s n = 1}
  have hbit : bit L = s := bit_set s bounds
  have hr : L ∈ recursiveLanguages := by
    change Computable (bit L)
    rwa [hbit]
  obtain ⟨c, _, T, stable⟩ := learns L hr s hbit.symm
  have hnorm (t : ℕ) : P (textPrefix s t) = M (textPrefix s t) := by
    apply congrArg M
    apply Eq.trans _ (List.map_id _)
    apply List.map_congr_left
    intro x hx
    obtain ⟨u,_,rfl⟩ := mem_textPrefix_iff.mp hx
    exact Nat.mod_eq_of_lt (bounds u)
  obtain ⟨u, hu, w, hw, ne⟩ := hbad T
  exact ne ((hnorm u).trans ((stable u hu).trans ((stable w hw).symm.trans (hnorm w).symm)))

end GenLimit.Gold.Effective
