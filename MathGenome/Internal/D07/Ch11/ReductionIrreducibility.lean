import MathGenome.Internal.Specs.D07.Ch11.ReductionIrreducibility
import MathGenome.Internal.D07.Ch11.CoefficientMap
import MathGenome.Internal.D07.Ch11.DegreeArithmetic
import MathGenome.Internal.D07.Ch11.GaussFractionIrreducible
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Positivity

/-!
Reduction of formal coefficients. In the primitive case a factor whose image
is a unit must have degree zero, because its leading coefficient survives.
It is a primitive constant and hence a unit. Survival for the two factors
follows from survival of their leading-coefficient product.
-/

universe u v w

namespace D07.Ch11.ReductionIrreducibility

open Polynomial
open Specs.D07.Ch11.ReductionIrreducibility

theorem monicReduction : MonicReduction.{u, v} := by
  intro R S _ _ _ _ φ f hf hi
  exact hf.irreducible_of_irreducible_map φ f hi

theorem integerReduction : IntegerReduction := by
  intro p _ f hf hi
  have h := monicReduction ℤ (ZMod p) (Int.castRingHom (ZMod p)) f hf hi
  exact ⟨h, (GaussFractionIrreducible.monicIrreducibleIff ℤ ℚ f hf).mp h⟩

theorem factorDegreesPreserved : FactorDegreesPreserved.{u, v} := by
  intro R S _ _ _ _ φ f g h he hlc
  have hp : φ g.leadingCoeff * φ h.leadingCoeff ≠ 0 := by
    simpa only [he, Polynomial.leadingCoeff_mul, map_mul] using hlc
  have hg := left_ne_zero_of_mul hp
  have hh := right_ne_zero_of_mul hp
  have hgn := natDegree_map_of_leadingCoeff_ne_zero φ hg
  have hhn := natDegree_map_of_leadingCoeff_ne_zero φ hh
  exact ⟨hg, hh, degree_map_eq_of_leadingCoeff_ne_zero φ hg,
    degree_map_eq_of_leadingCoeff_ne_zero φ hh, hgn, hhn,
    fun h => hgn ▸ h, fun h => hhn ▸ h⟩

private lemma primitive_unit_of_constant {R : Type*} [CommRing R]
    {f : R[X]} (hf : f.IsPrimitive) (hd : f.natDegree = 0) : IsUnit f := by
  have he := eq_C_of_natDegree_eq_zero hd
  rw [he]
  exact isUnit_C.mpr (hf _ (he ▸ dvd_rfl))

theorem primitiveReduction : PrimitiveReduction.{u, v} := by
  intro R S _ _ _ _ φ f hf hlc hi
  refine ⟨fun h => hi.not_isUnit (h.map (mapRingHom φ)), ?_⟩
  intro g h he
  obtain ⟨_, _, _, _, hgn, hhn, _, _⟩ :=
    factorDegreesPreserved R S φ f g h he hlc
  have hgi : g.IsPrimitive := isPrimitive_of_dvd hf ⟨h, he⟩
  have hhi : h.IsPrimitive := isPrimitive_of_dvd hf ⟨g, he.trans (mul_comm g h)⟩
  have hm : f.map φ = g.map φ * h.map φ := by rw [he, Polynomial.map_mul]
  exact (hi.isUnit_or_isUnit hm).imp
    (fun hu => primitive_unit_of_constant hgi (hgn ▸ natDegree_eq_zero_of_isUnit hu))
    (fun hu => primitive_unit_of_constant hhi (hhn ▸ natDegree_eq_zero_of_isUnit hu))

theorem primitiveReductionFraction : PrimitiveReductionFraction.{u, v, w} := by
  intro R S _ _ _ _ _ K _ _ _ φ f hf hlc hi
  have h := primitiveReduction R S φ f hf hlc hi
  exact ⟨h, (GaussFractionIrreducible.primitiveIrreducibleIff R K f hf).mp h⟩

theorem nonprimitiveCounterexample : NonprimitiveCounterexample := by
  obtain ⟨hnp, he, htwo, hlin, hred, _⟩ :=
    GaussFractionIrreducible.nonprimitiveCounterexample
  let f : ℤ[X] := C 2 * X + C 2
  let φ : ℤ →+* ZMod 3 := Int.castRingHom (ZMod 3)
  have hm : f.map φ = C (2 : ZMod 3) * X + C 2 := by
    simp [f, φ, C_ofNat]
  have hd : (f.map φ).degree = 1 := by
    rw [hm]
    exact degree_linear (by decide)
  have hlc : f.leadingCoeff = 2 := leadingCoeff_linear (by decide)
  change ¬f.IsPrimitive ∧ ¬f.Monic ∧ _
  refine ⟨hnp, ?_, he, htwo, hlin, hred, hm, hd, ?_,
    irreducible_of_degree_eq_one hd⟩
  · intro h
    have : (2 : ℤ) = 1 := hlc.symm.trans h
    norm_num at this
  · rw [hlc]
    decide

theorem degreeDropCounterexample : DegreeDropCounterexample := by
  let f : ℤ[X] := C 3 * X ^ 2 + C 4 * X + 1
  let φ : ℤ →+* ZMod 3 := Int.castRingHom (ZMod 3)
  have hf : f.IsPrimitive := by
    intro r hr
    rw [C_dvd_iff_dvd_coeff] at hr
    exact isUnit_iff_dvd_one.mpr (by simpa [f] using hr 0)
  have he : f = (C 3 * X + 1) * (X + 1) := by
    dsimp [f]
    simp only [C_ofNat]
    ring
  have hnu₁ : ¬IsUnit (C (3 : ℤ) * X + 1) := by
    apply not_isUnit_of_natDegree_pos
    change 0 < (C (3 : ℤ) * X + C 1).natDegree
    rw [natDegree_linear (by decide)]
    decide
  have hnu₂ : ¬IsUnit (X + 1 : ℤ[X]) := by
    apply not_isUnit_of_natDegree_pos
    simp
  have hm : f.map φ = (X + 1 : (ZMod 3)[X]) := by
    have h3 : φ 3 = 0 := by decide
    have h4 : φ 4 = 1 := by decide
    simp only [f, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, Polynomial.map_one, h3, h4,
      map_zero, map_one, zero_mul, zero_add, one_mul]
  have hd : (f.map φ).degree = 1 := by
    rw [hm]
    simpa using (degree_X_add_C (1 : ZMod 3))
  change f.IsPrimitive ∧ _
  refine ⟨hf, he, hnu₁, hnu₂, ?_, ?_, hm, hd, ?_, irreducible_of_degree_eq_one hd⟩
  · intro hi
    exact (hi.isUnit_or_isUnit he).elim hnu₁ hnu₂
  · exact degree_quadratic (by decide)
  · have hlc : f.leadingCoeff = 3 := leadingCoeff_quadratic (by decide)
    rw [hlc]
    decide

theorem converseCounterexample : ConverseCounterexample := by
  let f : ℤ[X] := X ^ 2 + 1
  have hf : f.Monic := monic_X_pow_add_C (1 : ℤ) (by decide : 2 ≠ 0)
  have hq : Irreducible (f.map (algebraMap ℤ ℚ)) := by
    have hm : f.map (algebraMap ℤ ℚ) = (X ^ 2 + 1 : ℚ[X]) := by simp [f]
    rw [hm]
    apply irreducible_of_degree_le_three_of_not_isRoot
    · norm_num
    · intro x hx
      have hz : x ^ 2 + 1 = 0 := by simpa [IsRoot, eval_add, eval_pow] using hx
      have : 0 < x ^ 2 + 1 := by positivity
      exact (ne_of_gt this) hz
  have hz : f.map (Int.castRingHom (ZMod 2)) = (X + 1 : (ZMod 2)[X]) ^ 2 := by
    simp only [f, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one]
    have htwo : (2 : (ZMod 2)[X]) = 0 := by
      change C (2 : ZMod 2) = 0
      rw [show (2 : ZMod 2) = 0 by decide, map_zero]
    linear_combination -htwo * X
  have hnu : ¬IsUnit (X + 1 : (ZMod 2)[X]) := by
    apply not_isUnit_of_natDegree_pos
    simp
  change f.Monic ∧ f.IsPrimitive ∧ _
  refine ⟨hf, hf.isPrimitive,
    (GaussFractionIrreducible.monicIrreducibleIff ℤ ℚ f hf).mpr hq,
    hq, hz, hnu, ?_⟩
  intro hi
  exact (hi.isUnit_or_isUnit (hz.trans (pow_two _))).elim hnu hnu

end D07.Ch11.ReductionIrreducibility
