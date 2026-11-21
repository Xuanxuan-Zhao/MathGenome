import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.PrimaryIdealsExample
import MathGenome.Internal.AlgebraCore.P103.Ch05.PrimaryDecomposition
import MathGenome.Internal.AlgebraCore.P103.Ch05.PrimaryLocalizationUniqueness
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-! Corollary 5.6. Specialize the module results via the primary and radical
bridges. In the two-variable example, membership is checked on every monomial;
maximality of the common radical then proves primaryness of both embedded factors. -/
namespace P103.Ch05.PrimaryIdealsExample
universe u
open P103.Specs.Ch05.PrimaryIdealsExample
open P103.Specs.Ch05.PrimarySubmodules
open P103.Specs.Ch05.AssociatedPrimesInterface

variable {R : Type u} [CommRing R]

theorem primary_iff_mathlib (Q : Ideal R) : PrimaryIdeal Q ↔ Q.IsPrimary := by
  rw [Ideal.isPrimary_iff]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun {a b} hab => ?_⟩
    by_cases ha : a ∈ Q
    · exact Or.inl ha
    · exact Or.inr (h b a (mul_comm a b ▸ hab) ha)
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun a b hab hb => (h (mul_comm a b ▸ hab)).resolve_left hb⟩

theorem primaryBridge : primaryBridgeType.{u} := by
  intro R _ Q
  exact (primary_iff_mathlib Q).trans (IrreduciblePrimary.primary_iff_mathlib R R Q).symm

theorem radicalBridge : radicalBridgeType.{u} := by
  intro R _ Q
  rw [PrimaryDecomposition.radical_eq_colon, Submodule.colon_univ]

theorem radical_eq (Q : Ideal R) : radicalValue R R Q = Q.radical := radicalBridge R Q

theorem decomposition_iff (I : Ideal R) (s : Finset (Ideal R)) :
    IsIdealDecomposition I s ↔ P103.Specs.Ch05.PrimaryDecomposition.IsDecomposition I s := by
  constructor
  · intro h
    exact ⟨h.nonempty, fun Q hQ => (primaryBridge R Q).mp (h.primary Q hQ),
      h.intersection, by simpa only [radical_eq] using h.distinct, h.irredundant⟩
  · intro h
    exact ⟨h.nonempty, fun Q hQ => (primaryBridge R Q).mpr (h.primary Q hQ),
      h.intersection, by simpa only [radical_eq] using h.distinct, h.irredundant⟩

theorem existsDecomposition : existsDecompositionType.{u} := by
  intro R _ _ I hI
  obtain ⟨s, hs⟩ := PrimaryDecomposition.exists_decomposition R R I hI
  exact ⟨s, (decomposition_iff I s).mpr hs⟩

theorem associatedRadicals : associatedRadicalsType.{u} := by
  intro R _ _ I s hs
  simpa only [radical_eq] using
    PrimaryDecomposition.associatedPrimes_eq_radicals R R I s ((decomposition_iff I s).mp hs)

theorem minimalComponent : minimalComponentType.{u} := by
  intro R _ _ I s hs p hp
  simpa only [radical_eq] using
    PrimaryLocalizationUniqueness.minimalComponent R R I s ((decomposition_iff I s).mp hs) p hp

theorem minimalComponentUnique : minimalComponentUniqueType.{u} := by
  intro R _ _ I s t hs ht p hp Q hQ P hP hradQ hradP
  exact ((minimalComponent R I s hs p hp).2 Q hQ hradQ).trans
    ((minimalComponent R I t ht p hp).2 P hP hradP).symm

theorem pair_decomposition (I P Q : Ideal R) (hp : PrimaryIdeal P) (hq : PrimaryIdeal Q)
    (heq : I = P ⊓ Q) (hrad : P.radical ≠ Q.radical) (hPI : P ≠ I) (hQI : Q ≠ I) :
    IsIdealDecomposition I {P, Q} := by
  classical
  have hPQ : P ≠ Q := fun h => hrad (congrArg Ideal.radical h)
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · intro T hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl
    · exact hp
    · exact hq
  · rw [← Finset.inf_eq_iInf]
    simpa using heq.symm
  · intro A hA B hB hAB
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact (hAB rfl).elim
    · exact hrad
    · exact Ne.symm hrad
    · exact (hAB rfl).elim
  · intro T hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    have heraseP : ({P, Q} : Finset (Ideal R)).erase P = {Q} := by simp [hPQ]
    have heraseQ : ({P, Q} : Finset (Ideal R)).erase Q = {P} := by
      rw [Finset.erase_insert_of_ne hPQ, Finset.erase_singleton]
      simp
    rcases hT with hT | hT
    · rw [hT, heraseP, ← Finset.inf_eq_iInf]
      simpa using hQI
    · rw [hT, heraseQ, ← Finset.inf_eq_iInf]
      simpa using hPI

section Example
open MvPolynomial
variable (k : Type u) [Field k]

private noncomputable def exponent (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

private theorem exponent_le (a b : ℕ) (d : Fin 2 →₀ ℕ) :
    exponent a b ≤ d ↔ a ≤ d 0 ∧ b ≤ d 1 := by
  simp [exponent, Finsupp.le_def, Fin.forall_fin_two]

private theorem monomial_exponent (a b : ℕ) :
    monomial (exponent a b) (1 : k) = X 0 ^ a * X 1 ^ b := by
  rw [exponent, monomial_add_single, ← X_pow_eq_monomial]

theorem mem_I (f : Plane k) : f ∈ exampleI k ↔
    ∀ d ∈ f.support, 2 ≤ d 0 ∨ (1 ≤ d 0 ∧ 1 ≤ d 1) := by
  have heq : exampleI k = Ideal.span ((fun d => monomial d (1 : k)) ''
      {exponent 2 0, exponent 1 1}) := by
    simp [exampleI, monomial_exponent]
  rw [heq, mem_ideal_span_monomial_image]
  simp [exponent_le]

theorem mem_P (f : Plane k) : f ∈ exampleP k ↔
    ∀ d ∈ f.support, 1 ≤ d 0 := by
  have heq : exampleP k = Ideal.span ((fun d => monomial d (1 : k)) ''
      {exponent 1 0}) := by
    simp [exampleP, monomial_exponent]
  rw [heq, mem_ideal_span_monomial_image]
  simp [exponent_le]

theorem mem_Q (f : Plane k) : f ∈ exampleQ k ↔
    ∀ d ∈ f.support, 2 ≤ d 0 ∨ 1 ≤ d 1 := by
  have heq : exampleQ k = Ideal.span ((fun d => monomial d (1 : k)) ''
      {exponent 2 0, exponent 0 1}) := by
    simp [exampleQ, monomial_exponent]
  rw [heq, mem_ideal_span_monomial_image]
  simp [exponent_le]

theorem mem_Q' (f : Plane k) : f ∈ exampleQ' k ↔
    ∀ d ∈ f.support, 2 ≤ d 0 ∨ (1 ≤ d 0 ∧ 1 ≤ d 1) ∨ 2 ≤ d 1 := by
  have heq : exampleQ' k = Ideal.span ((fun d => monomial d (1 : k)) ''
      {exponent 2 0, exponent 1 1, exponent 0 2}) := by
    simp [exampleQ', Set.image_insert_eq, Set.image_singleton, monomial_exponent]
  rw [heq, mem_ideal_span_monomial_image]
  simp [exponent_le]

theorem mem_M (f : Plane k) : f ∈ exampleM k ↔
    ∀ d ∈ f.support, 1 ≤ d 0 ∨ 1 ≤ d 1 := by
  have heq : exampleM k = Ideal.span ((fun d => monomial d (1 : k)) ''
      {exponent 1 0, exponent 0 1}) := by
    simp [exampleM, monomial_exponent]
  rw [heq, mem_ideal_span_monomial_image]
  simp [exponent_le]

theorem exampleIntersections : exampleIntersectionsType.{u} := by
  intro k _
  constructor <;> ext f
  · rw [Ideal.mem_inf, mem_I, mem_P, mem_Q]
    constructor
    · intro h
      constructor <;> intro d hd <;> have hh := h d hd <;> omega
    · rintro ⟨hp, hq⟩ d hd
      have := hp d hd
      have := hq d hd
      omega
  · rw [Ideal.mem_inf, mem_I, mem_P, mem_Q']
    constructor
    · intro h
      constructor <;> intro d hd <;> have hh := h d hd <;> omega
    · rintro ⟨hp, hq⟩ d hd
      have := hp d hd
      have := hq d hd
      omega

theorem P_prime : (exampleP k).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime MvPolynomial.X_prime

theorem M_eq_ker : exampleM k = RingHom.ker (constantCoeff : Plane k →+* k) := by
  ext f
  rw [mem_M, RingHom.mem_ker, constantCoeff_eq]
  constructor
  · intro h
    by_contra hne
    have hh := h 0 (mem_support_iff.mpr hne)
    simp at hh
  · intro h d hd
    by_contra hh
    have heq : d = 0 := by
      ext i
      fin_cases i <;> simp_all
    subst d
    exact (mem_support_iff.mp hd) h

theorem M_maximal : (exampleM k).IsMaximal := by
  rw [M_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨C a, constantCoeff_C _ a⟩)

theorem Q_radical : (exampleQ k).radical = exampleM k := by
  apply le_antisymm
  · apply (M_maximal k).isPrime.radical_le_iff.mpr
    intro f hf
    rw [mem_M]
    intro d hd
    have := (mem_Q k f).mp hf d hd
    omega
  · rw [exampleM, Ideal.span_le]
    intro f hf
    rcases hf with rfl | rfl
    · exact ⟨2, Ideal.subset_span (by simp)⟩
    · exact Ideal.le_radical (Ideal.subset_span (by simp))

theorem Q'_radical : (exampleQ' k).radical = exampleM k := by
  apply le_antisymm
  · apply (M_maximal k).isPrime.radical_le_iff.mpr
    intro f hf
    rw [mem_M]
    intro d hd
    have := (mem_Q' k f).mp hf d hd
    omega
  · rw [exampleM, Ideal.span_le]
    intro f hf
    rcases hf with rfl | rfl
    · exact ⟨2, Ideal.subset_span (by simp)⟩
    · exact ⟨2, Ideal.subset_span (by simp)⟩

theorem Q_primary : PrimaryIdeal (exampleQ k) := by
  apply (primary_iff_mathlib _).mpr
  apply Ideal.isPrimary_of_isMaximal_radical
  rw [Q_radical]
  exact M_maximal k

theorem Q'_primary : PrimaryIdeal (exampleQ' k) := by
  apply (primary_iff_mathlib _).mpr
  apply Ideal.isPrimary_of_isMaximal_radical
  rw [Q'_radical]
  exact M_maximal k

theorem X_mem_P : X 0 ∈ exampleP k := Ideal.subset_span (by simp)
theorem X_not_mem_I : X 0 ∉ exampleI k := by simp [mem_I, support_X]
theorem X_not_mem_Q : X 0 ∉ exampleQ k := by simp [mem_Q, support_X]
theorem X_not_mem_Q' : X 0 ∉ exampleQ' k := by simp [mem_Q', support_X]
theorem Y_not_mem_P : X 1 ∉ exampleP k := by simp [mem_P, support_X]
theorem Y_mem_Q : X 1 ∈ exampleQ k := Ideal.subset_span (by simp)
theorem Y_not_mem_Q' : X 1 ∉ exampleQ' k := by simp [mem_Q', support_X]
theorem Y_not_mem_I : X 1 ∉ exampleI k := by simp [mem_I, support_X]
theorem Y_sq_mem_Q' : X 1 ^ 2 ∈ exampleQ' k := Ideal.subset_span (by simp)
theorem Y_sq_not_mem_I : X 1 ^ 2 ∉ exampleI k := by simp [mem_I, support_X_pow]

theorem P_lt_M : exampleP k < exampleM k := by
  apply lt_of_le_of_ne
  · intro f hf
    rw [mem_M]
    intro d hd
    exact Or.inl ((mem_P k f).mp hf d hd)
  · intro heq
    exact Y_not_mem_P k (heq ▸ (Ideal.subset_span (by simp) : X 1 ∈ exampleM k))

theorem Q_ne_Q' : exampleQ k ≠ exampleQ' k := by
  intro heq
  exact Y_not_mem_Q' k (heq ▸ Y_mem_Q k)

theorem exampleComponents : exampleComponentsType.{u} := by
  intro k _
  exact ⟨Q_ne_Q' k, P_prime k, M_maximal k, Q_primary k, Q'_primary k,
    (P_prime k).radical, Q_radical k, Q'_radical k⟩

theorem exampleDecompositions : exampleDecompositionsType.{u} := by
  intro k _
  have hp : PrimaryIdeal (exampleP k) :=
    (primary_iff_mathlib _).mpr (P_prime k).isPrimary
  have hPI : exampleP k ≠ exampleI k := fun h => X_not_mem_I k (h ▸ X_mem_P k)
  constructor
  · apply pair_decomposition _ _ _ hp (Q_primary k) (exampleIntersections k).1
    · rw [(P_prime k).radical, Q_radical]
      exact ne_of_lt (P_lt_M k)
    · exact hPI
    · intro h
      exact Y_not_mem_I k (h ▸ Y_mem_Q k)
  · apply pair_decomposition _ _ _ hp (Q'_primary k) (exampleIntersections k).2
    · rw [(P_prime k).radical, Q'_radical]
      exact ne_of_lt (P_lt_M k)
    · exact hPI
    · intro h
      exact Y_sq_not_mem_I k (h ▸ Y_sq_mem_Q' k)

theorem exampleAssociated : exampleAssociatedType.{u} := by
  intro k _
  classical
  have hass : associatedPrimesValue (Plane k) (Plane k ⧸ exampleI k) =
      {exampleP k, exampleM k} := by
    simpa only [Finset.coe_pair, Set.image_pair, (P_prime k).radical, Q_radical] using
      associatedRadicals (Plane k) (exampleI k) {exampleP k, exampleQ k}
        (exampleDecompositions k).1
  have hp : exampleP k ∈ associatedPrimesValue (Plane k) (Plane k ⧸ exampleI k) := by
    rw [hass]
    exact Set.mem_insert _ _
  have hm : exampleM k ∈ associatedPrimesValue (Plane k) (Plane k ⧸ exampleI k) := by
    rw [hass]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  refine ⟨hass, ⟨hp, ?_⟩, hm, ?_, P_lt_M k⟩
  · intro p hmem _
    rw [hass] at hmem
    rcases hmem with rfl | rfl
    · exact le_rfl
    · exact (P_lt_M k).le
  · intro hmin
    exact (ne_of_lt (P_lt_M k)) (hmin.eq_of_le hp (P_lt_M k).le)

end Example
end P103.Ch05.PrimaryIdealsExample
