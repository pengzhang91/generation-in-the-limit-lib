import GenLimit.Paper00_LanguageIdentification.Effective.FunctionLearning

/-! # Primitive recursive clock for detecting a negative tester answer

Stage `pair k b` revisits the learner's guess on the first `k` symbols.
The available fuel is the stage itself, hence every fixed prefix is revisited
with arbitrarily much fuel. Both evaluations are bounded.
-/

namespace GenLimit.Gold.Effective.RejectionClock

open Nat.Partrec (Code)

private def prefixOf (h : List ℕ) (k : ℕ) := textPrefix (fun i => h[i]?.getD 0) k

private theorem prefix_prim : Primrec₂ prefixOf :=
  (Primrec.list_map (Primrec.list_range.comp Primrec.snd)
    (Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.fst)
      Primrec.snd) (Primrec.const 0)).to₂).to₂

private theorem prefix_eq (s : ℕ → ℕ) {k n : ℕ} (hk : k ≤ n) :
    prefixOf (textPrefix s n) k = textPrefix s k := by
  apply List.map_congr_left
  intro i hi
  have hn := (List.mem_range.mp hi).trans_le hk
  simp [textPrefix, hn]

def rejects (m : Code) (n : ℕ) (h : List ℕ) (x : ℕ) :=
  let guess := Code.evaln n m (Encodable.encode (prefixOf h n.unpair.1))
  guess.isSome && (Code.evaln n (Denumerable.ofNat Code (guess.getD 0)) x == some 0)

theorem rejects_prim (m : Code) {A : Type*} [Primcodable A]
    {n : A → ℕ} {h : A → List ℕ} {x : A → ℕ} (hn : Primrec n) (hh : Primrec h) (hx : Primrec x) :
    Primrec fun a => rejects m (n a) (h a) (x a) := by
  have g := Code.primrec_evaln.comp ((hn.pair (Primrec.const m)).pair
    (Primrec.encode.comp (prefix_prim.comp hh (Primrec.fst.comp (Primrec.unpair.comp hn)))))
  apply (Primrec.and.comp (Primrec.option_isSome.comp g) (Primrec.beq.comp
    (Code.primrec_evaln.comp ((hn.pair ((Primrec.ofNat Code).comp (Primrec.option_getD.comp g (Primrec.const 0)))).pair hx))
    (Primrec.const (some 0)))).of_eq
  intro a
  apply Bool.eq_iff_iff.mpr
  simp [rejects]

def Implements (m : Code) (M : List ℕ → Code) : Prop :=
  ∀ h, m.eval (Encodable.encode h) = Part.some (Encodable.encode (M h))

theorem code_for {M : List ℕ → Code} (hc : Computable M) : ∃ m, Implements m M := by
  obtain ⟨m, hm⟩ := Code.exists_code.mp hc
  refine ⟨m, fun h => ?_⟩
  rw [hm]
  simp

theorem sound {m : Code} {M : List ℕ → Code} (impl : Implements m M)
    {s : ℕ → ℕ} {n x : ℕ} (h : rejects m n (textPrefix s n) x = true) :
    0 ∈ (M (textPrefix s n.unpair.1)).eval x := by
  unfold rejects at h
  rw [prefix_eq s (Nat.unpair_left_le n)] at h
  cases hg : Code.evaln n m (Encodable.encode (textPrefix s n.unpair.1)) with
  | none => simp [hg] at h
  | some e =>
    have eq := Code.evaln_sound hg
    rw [impl _] at eq
    obtain rfl : e = Encodable.encode (M (textPrefix s n.unpair.1)) := Part.mem_some_iff.mp eq
    apply Code.evaln_sound
    simpa [hg] using h

theorem complete {m : Code} {M : List ℕ → Code} (impl : Implements m M)
    (s : ℕ → ℕ) {k x : ℕ} (h : 0 ∈ (M (textPrefix s k)).eval x) (T : ℕ) :
    ∃ n ≥ T, n.unpair.1 = k ∧ rejects m n (textPrefix s n) x = true := by
  let e := M (textPrefix s k)
  have hg : Encodable.encode e ∈ m.eval (Encodable.encode (textPrefix s k)) := by
    rw [impl _]
    exact Part.mem_some _
  obtain ⟨b, hb⟩ := Code.evaln_complete.mp hg
  obtain ⟨c, hc⟩ := Code.evaln_complete.mp h
  let n := Nat.pair k (max T (max b c))
  have hn : max T (max b c) ≤ n := Nat.right_le_pair ..
  have hk : n.unpair.1 = k := by simp [n]
  refine ⟨n, (le_max_left ..).trans hn, hk, ?_⟩
  have h1 := Code.evaln_mono (le_trans (le_trans (le_max_left b c) (le_max_right T _)) hn) hb
  have h2 := Code.evaln_mono (le_trans (le_trans (le_max_right b c) (le_max_right T _)) hn) hc
  change Code.evaln n _ _ = some (Encodable.encode e) at h1
  change Code.evaln n e x = some 0 at h2
  unfold rejects
  rw [hk, prefix_eq (n := n) (k := k) s (Nat.left_le_pair ..), h1]
  simp [h2]

end GenLimit.Gold.Effective.RejectionClock
