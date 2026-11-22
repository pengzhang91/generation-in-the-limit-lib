import GenLimit.Paper00_LanguageIdentification.Abstract.Enumeration

/-! # Gold's learning-time Theorem 10.1 (printed pp. 461–462)

Learning by a deadline means that a single correct name is used at every
subsequent time. Comparing all positive deadlines includes a learner whose
learning time on a given presentation is infinite.
-/

namespace GenLimit.Gold.Abstract

def CorrectFrom (naming : Naming N O) (M : Learner I N) (s : ℕ → I)
    (o : O) (t : ℕ) : Prop :=
  ∃ n, naming.denotes n = o ∧ ∀ u ≥ t, M (textPrefix s u) = n

def NoSlower (naming : Naming N O) (allowed : Allowable I O)
    (M G : Learner I N) : Prop :=
  ∀ o s, s ∈ allowed o → ∀ t > 0, CorrectFrom naming G s o t → CorrectFrom naming M s o t

private theorem shorter_prefix {s z : ℕ → I} {t u : ℕ}
    (htu : t ≤ u) (h : textPrefix s u = textPrefix z u) : textPrefix s t = textPrefix z t := by
  have takePrefix (s : ℕ → I) : (textPrefix s u).take t = textPrefix s t := by
    simp [textPrefix, ← List.map_take, List.take_range, Nat.min_eq_left htu]
  simpa only [takePrefix] using congrArg (List.take t) h

/-- From each valid prefix one can continue on the object currently guessed
by enumeration, on a presentation where that very guess stays fixed. -/
private theorem compatible_continuation (allowed : Allowable I O) (e : ℕ → O)
    (onto : Function.Surjective e) {o s} (hs : s ∈ allowed o) (t : ℕ) :
    let i := firstCompatibleIndex allowed e (textPrefix s t)
    ∃ z ∈ allowed (e i), textPrefix z t = textPrefix s t ∧
      ∀ u ≥ t, firstCompatibleIndex allowed e (textPrefix z u) = i := by
  classical
  obtain ⟨j, rfl⟩ := onto o
  have hex : ∃ k, Compatible allowed (textPrefix s t) (e k) :=
    ⟨j, compatible_textPrefix hs t⟩
  simp only [firstCompatibleIndex, dif_pos hex]
  obtain ⟨z, hz, hp⟩ := Nat.find_spec hex
  simp only [textPrefix_length] at hp
  refine ⟨z, hz, hp, fun u hu => ?_⟩
  have hnew : ∃ k, Compatible allowed (textPrefix z u) (e k) :=
    ⟨Nat.find hex, compatible_textPrefix hz u⟩
  rw [dif_pos hnew]
  apply Nat.le_antisymm (Nat.find_min' hnew (compatible_textPrefix hz u))
  obtain ⟨w, hw, hwz⟩ := Nat.find_spec hnew
  simp only [textPrefix_length] at hwz
  apply Nat.find_min' hex
  exact ⟨w, hw, by simpa only [textPrefix_length] using (shorter_prefix hu hwz).trans hp⟩

/-- Every learner that matches every successful deadline of identification
by enumeration also has each of its own successful deadlines matched by
enumeration. This is the paper's Pareto assertion, including its remark
dispensing with collapsing uncertainty. -/
theorem enumeration_learning_time (naming : Naming N O) (allowed : Allowable I O)
    (e : ℕ → O) (onto : Function.Surjective e) (M : Learner I N) :
    let G := identificationByEnumeration naming allowed e
    NoSlower naming allowed M G → NoSlower naming allowed G M := by
  intro G dom o s hs t ht hM
  obtain ⟨n, hn, stable⟩ := hM
  refine ⟨naming.nameOf o, naming.denotes_nameOf o, fun u hu => ?_⟩
  let i := firstCompatibleIndex allowed e (textPrefix s u)
  obtain ⟨z, hz, hp, hzstable⟩ := compatible_continuation allowed e onto hs u
  have byU : CorrectFrom naming G z (e i) u :=
    ⟨naming.nameOf (e i), naming.denotes_nameOf _, fun v hv =>
      congrArg (fun j => naming.nameOf (e j)) (hzstable v hv)⟩
  obtain ⟨m, hm, stable'⟩ := dom _ _ hz u (lt_of_lt_of_le ht hu) byU
  have hnm : m = n := (stable' u le_rfl).symm.trans ((congrArg M hp).trans (stable u hu))
  have hobj : e i = o := hm.symm.trans ((congrArg naming.denotes hnm).trans hn)
  exact congrArg naming.nameOf hobj

end GenLimit.Gold.Abstract
