import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.FractionFieldIrreducibility
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Separable

/-! Gauss's lemma and characteristic-zero differentiation for ℂ[z][w]. -/

namespace D12Complex.Ch21.FractionFieldIrreducibility

open Polynomial

/-- An irreducible bivariate complex polynomial of positive w-degree is
primitive over ℂ[z], stays irreducible over ℂ(z), and is coprime to its
nonzero partial derivative, whose w-degree is exactly one less. -/
theorem gauss_bridge : Specs.D12Complex.Ch21.FractionFieldIrreducibility.gaussBridge := by
  intro P d hP hdeg hd
  have hpos : P.natDegree ≠ 0 := by omega
  have hprim : P.IsPrimitive := hP.isPrimitive hpos
  have hcommon : ∀ q : Polynomial ℂ, (∀ j : ℕ, q ∣ P.coeff j) →
      IsUnit q ∧ q.natDegree = 0 := by
    intro q hq
    have hu : IsUnit q := hprim q ((C_dvd_iff_dvd_coeff q P).mpr hq)
    exact ⟨hu, natDegree_eq_zero_of_isUnit hu⟩
  refine ⟨hcommon, hprim, ?_⟩
  let Q := P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))
  have hQ : Irreducible Q :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp hP
  have hQdeg : Q.natDegree = d := by
    change (P.map _).natDegree = d
    rw [natDegree_map_eq_of_injective (IsFractionRing.injective _ _), hdeg]
  have hQpos : Q.natDegree ≠ 0 := by omega
  refine ⟨hQ, hQdeg, derivative_ne_zero.mpr hpos, ?_, ?_,
    derivative_map P _, derivative_ne_zero.mpr hQpos, ?_, ?_, ?_⟩
  · rw [natDegree_derivative, hdeg]
  · rw [degree_derivative hpos, hdeg]
  · rw [natDegree_derivative, hQdeg]
  · rw [degree_derivative hQpos, hQdeg]
  · rw [← derivative_map]
    exact hQ.separable

end D12Complex.Ch21.FractionFieldIrreducibility
