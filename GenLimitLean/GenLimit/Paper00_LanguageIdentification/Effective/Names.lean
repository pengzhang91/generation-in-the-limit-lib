import GenLimit.Paper00_LanguageIdentification.Text.Model
import Mathlib.Computability.PartrecCode

/-! # Effective identification and Gold's index translations

Words are represented by natural numbers. Names are partial recursive
program indices in mathlib's acceptable numbering. A tester has to halt on
every word with its membership bit. Following the number-theoretic convention
of §11, a range generator may be partial, so the empty language has a name.
-/

namespace GenLimit.Gold.Effective

open Nat.Partrec (Code)

abbrev Presentations (I O : Type*) := O → Set (ℕ → I)
abbrev Denotation (N O : Type*) := N → O → Prop

abbrev Method (I : Type*) := Presentations I Language
abbrev NameRelation (N : Type*) := Denotation N Language

def Learns {I N O : Type*} (M : List I → N) (names : Denotation N O)
    (method : Presentations I O) (C : Set O) : Prop :=
  ∀ L ∈ C, ∀ s ∈ method L, ∃ n, names n L ∧
    ∃ T, ∀ t ≥ T, M (textPrefix s t) = n

def Identifiable {I N O : Type*} [Primcodable I] [Primcodable N]
    (names : Denotation N O) (method : Presentations I O) (C : Set O) : Prop :=
  ∃ M, Computable M ∧ Learns M names method C

def Tester (e : Code) (L : Language) : Prop :=
  ∀ x, (x ∈ L → e.eval x = Part.some 1) ∧ (x ∉ L → e.eval x = Part.some 0)

def Generator (e : Code) (L : Language) : Prop :=
  ∀ x, x ∈ L ↔ ∃ u, x ∈ e.eval u

def DomainGenerator (e : Code) (L : Language) : Prop :=
  ∀ x, x ∈ L ↔ (e.eval x).Dom

def AntiDomainGenerator (e : Code) (L : Language) : Prop := DomainGenerator e Lᶜ

/-- Uniformly specialize a partial recursive procedure in its first argument. -/
theorem compile {A : Type*} [Primcodable A] {f : A → ℕ →. ℕ} (hf : Partrec₂ f) :
    ∃ k : A → Code, Computable k ∧ ∀ a x, (k a).eval x = f a x := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  refine ⟨fun a => c.curry (Encodable.encode a),
    Code.primrec₂_curry.to_comp.comp (Computable.const c) Computable.encode, ?_⟩
  intro a x
  rw [Code.eval_curry, hc]
  change ((Part.ofOption (Encodable.decode (α := A × ℕ) (Encodable.encode (a, x)))).bind
    fun z => (f z.1 z.2).map Encodable.encode) = _
  simp
  exact Part.ext fun x => by simp [Part.mem_map_iff]

/-- A limiting translation is defined on the valid source names. Its one
total recursive approximation must stabilize syntactically on each such name. -/
def LimitTranslation {A B O : Type*} [Primcodable A] [Primcodable B]
    (src : Denotation A O) (dst : Denotation B O) (C : Set O) : Prop :=
  ∃ g : A → ℕ → B, Computable₂ g ∧ ∀ L ∈ C, ∀ a, src a L →
    ∃ b, dst b L ∧ ∃ T, ∀ t ≥ T, g a t = b

/-- §11, Theorem 10.1 (printed pp. 463–464). -/
theorem identification_of_limitTranslation {I A B O : Type*}
    [Primcodable I] [Primcodable A] [Primcodable B] {method : Presentations I O}
    {src : Denotation A O} {dst : Denotation B O} {C : Set O}
    (h : Identifiable src method C) (tr : LimitTranslation src dst C) :
    Identifiable dst method C := by
  obtain ⟨M, hM, learns⟩ := h
  obtain ⟨g, hg, translates⟩ := tr
  refine ⟨fun h => g (M h) h.length, hg.comp hM Computable.list_length, ?_⟩
  intro L hL s hs
  obtain ⟨a, ha, S, hS⟩ := learns L hL s hs
  obtain ⟨b, hb, T, hT⟩ := translates L hL a ha
  refine ⟨b, hb, max S T, fun t ht => ?_⟩
  simp only [hS t (le_trans (le_max_left ..) ht), textPrefix_length]
  exact hT t (le_trans (le_max_right ..) ht)

private def outputAccepted (e : Code) (u : ℕ) : Option ℕ :=
  bif Code.evaln u.unpair.2 e u.unpair.1 == some 1 then some u.unpair.1 else none

private theorem outputAccepted_comp : Computable₂ outputAccepted := by
  have hx := Computable.fst.comp (Computable.unpair.comp (Computable.snd (α := Code) (β := ℕ)))
  have ht := Computable.snd.comp (Computable.unpair.comp (Computable.snd (α := Code) (β := ℕ)))
  have run := Code.primrec_evaln.to_comp.comp ((ht.pair Computable.fst).pair hx)
  exact (((Primrec.beq.to_comp.comp run (Computable.const (some 1))).cond
    (Computable.option_some.comp hx) (Computable.const none)).to₂).of_eq fun ⟨e,u⟩ => by
      unfold outputAccepted
      simp [Bool.cond_eq_ite]

/-- A computable map of tester indices to indices with the same range. -/
theorem tester_to_generator :
    ∃ k : Code → Code, Computable k ∧ ∀ e L, Tester e L → Generator (k e) L := by
  obtain ⟨k, hk, spec⟩ := compile (f := fun e u => Part.ofOption (outputAccepted e u))
    outputAccepted_comp.ofOption
  refine ⟨k, hk, fun e L tester x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨t, ht⟩ := Code.evaln_complete.mp ((tester x).1 hx ▸ Part.mem_some 1)
    refine ⟨Nat.pair x t, ?_⟩
    rw [spec]
    have hh : Code.evaln t e x = some 1 := ht
    simp [outputAccepted, hh]
  · rintro ⟨u, hu⟩
    rw [spec] at hu
    change x ∈ Part.ofOption (bif Code.evaln u.unpair.2 e u.unpair.1 == some 1
      then some u.unpair.1 else none) at hu
    by_cases h : Code.evaln u.unpair.2 e u.unpair.1 = some 1
    · simp [h] at hu
      have he : 1 ∈ e.eval u.unpair.1 := Code.evaln_sound h
      have hx : x = u.unpair.1 := by simpa [eq_comm] using hu
      subst x
      by_contra hn
      rw [(tester _).2 hn] at he
      simp at he
    · have hfalse : (Code.evaln u.unpair.2 e u.unpair.1 == some 1) = false :=
        beq_eq_false_iff_ne.mpr h
      simp [hfalse] at hu

/-- The direction ruled out by the literal Corollary 10.1 on p. 464 actually
has a constant-in-time effective approximation for every class. -/
theorem tester_to_generator_limit (C : Set Language) :
    LimitTranslation Tester Generator C := by
  obtain ⟨k, hk, hs⟩ := tester_to_generator
  exact ⟨fun e _ => k e, (hk.comp Computable.fst).to₂,
    fun L _ e he => ⟨k e, hs e L he, 0, fun _ _ => rfl⟩⟩

/-- Appendix Theorem I.1 for every presentation method. -/
theorem generator_identification_of_tester {I : Type*} [Primcodable I]
    {m : Method I} {C : Set Language} (h : Identifiable Tester m C) :
    Identifiable Generator m C :=
  identification_of_limitTranslation h (tester_to_generator_limit C)

/-- Appendix Corollary I.2. -/
theorem not_tester_identification_of_not_generator {I : Type*} [Primcodable I]
    {m : Method I} {C : Set Language} (h : ¬ Identifiable Generator m C) :
    ¬ Identifiable Tester m C := fun ht => h (generator_identification_of_tester ht)

end GenLimit.Gold.Effective
