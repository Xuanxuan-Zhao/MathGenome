import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.FiniteExceptionalSet
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.FractionFieldIrreducibility
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch06.AlgebraicClosure
import Mathlib.Algebra.Group.Nat.Even

/-! The polynomial resultant and the finite exceptional set of D12.21.02.
Nonvanishing follows by the accepted Gauss bridge over ℂ(z). Specialization
of its Sylvester determinant and the nonzero leading coefficient give
separable fibers of the original degree. The project's algebraic-closure
theorem supplies all roots, without assuming a complex FTA instance.
-/

noncomputable section
open Polynomial

namespace D12Complex.Ch21.FiniteExceptionalSet

def fiber (P : Polynomial (Polynomial ℂ)) (z : ℂ) : Polynomial ℂ :=
  P.map (Polynomial.evalRingHom z)

def resultantPolynomial (P : Polynomial (Polynomial ℂ)) : Polynomial ℂ :=
  P.resultant P.derivative

def exceptionalSet (P : Polynomial (Polynomial ℂ)) : Set ℂ :=
  {z | (P.leadingCoeff * resultantPolynomial P).eval z = 0}

theorem resultant_sylvester :
    Specs.D12Complex.Ch21.FiniteExceptionalSet.resultant_sylvester_type := by
  intro P d hdeg hd
  change P.resultant P.derivative = _
  have hder : P.derivative.natDegree = d - 1 := by
    rw [natDegree_derivative, hdeg]
  change P.resultant P.derivative P.natDegree P.derivative.natDegree = _
  rw [hdeg, hder, resultant_comm, (Nat.even_mul_pred_self d).neg_one_pow, one_mul]
  rfl

theorem resultant_specialize :
    Specs.D12Complex.Ch21.FiniteExceptionalSet.resultant_specialize_type := by
  intro P d hdeg hd z
  change (P.resultant P.derivative).eval z = _
  have hder : P.derivative.natDegree = d - 1 := by
    rw [natDegree_derivative, hdeg]
  change (Polynomial.evalRingHom z) (P.resultant P.derivative) = _
  rw [← resultant_map_map]
  simp only [hdeg, hder]
  change (P.map (Polynomial.evalRingHom z)).resultant
    (P.derivative.map (Polynomial.evalRingHom z)) d (d - 1) =
    (P.map (Polynomial.evalRingHom z)).resultant
      (P.map (Polynomial.evalRingHom z)).derivative d (d - 1)
  rw [derivative_map]

theorem resultant_degree_one :
    Specs.D12Complex.Ch21.FiniteExceptionalSet.resultant_degree_one_type := by
  intro P hdeg
  change P.resultant P.derivative = _
  have hder : P.derivative.natDegree = 0 := by rw [natDegree_derivative, hdeg]
  change P.resultant P.derivative P.natDegree P.derivative.natDegree = _
  rw [hdeg, hder, resultant_zero_right_deg, pow_one, coeff_derivative]
  simp [leadingCoeff, hdeg]

theorem resultant_nonzero :
    Specs.D12Complex.Ch21.FiniteExceptionalSet.resultant_nonzero_type := by
  intro P d hP hdeg hd
  change P.resultant P.derivative ≠ 0
  obtain ⟨_, _, hQ⟩ := FractionFieldIrreducibility.gauss_bridge P d hP hdeg hd
  dsimp only at hQ
  have hcop := hQ.2.2.2.2.2.2.2.2.2
  have hres := resultant_ne_zero _ _ hcop
  rw [resultant_map_map,
    natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ)),
    natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ))]
    at hres
  intro hz
  apply hres
  change (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (P.resultant P.derivative) = 0
  rw [hz, map_zero]

theorem finite_exceptional_set :
    Specs.D12Complex.Ch21.FiniteExceptionalSet.finite_exceptional_set_type := by
  intro P d hP hdeg hd
  classical
  have hDelta : resultantPolynomial P ≠ 0 := resultant_nonzero P d hP hdeg hd
  have hproduct : P.leadingCoeff * resultantPolynomial P ≠ 0 :=
    mul_ne_zero (leadingCoeff_ne_zero.mpr hP.ne_zero) hDelta
  refine ⟨hDelta, ?_, ?_⟩
  · exact Polynomial.finite_setOfPred_isRoot hproduct
  · intro z hz
    have hproductz : (P.leadingCoeff * resultantPolynomial P).eval z ≠ 0 := hz
    rw [eval_mul] at hproductz
    obtain ⟨hLead, hDeltaz⟩ := mul_ne_zero_iff.mp hproductz
    have hfdeg : (fiber P z).natDegree = d := by
      change (P.map (Polynomial.evalRingHom z)).natDegree = d
      exact (natDegree_map_of_leadingCoeff_ne_zero (Polynomial.evalRingHom z) hLead).trans hdeg
    have hfzero : fiber P z ≠ 0 := by
      intro hzero
      simp [hzero] at hfdeg
      omega
    have hfder : (fiber P z).derivative.natDegree = d - 1 := by
      rw [natDegree_derivative, hfdeg]
    have hres : (fiber P z).resultant (fiber P z).derivative ≠ 0 := by
      have hspec : (resultantPolynomial P).eval z =
          (fiber P z).resultant (fiber P z).derivative d (d - 1) :=
        resultant_specialize P d hdeg hd z
      change (fiber P z).resultant (fiber P z).derivative
        (fiber P z).natDegree (fiber P z).derivative.natDegree ≠ 0
      rw [hfdeg, hfder, ← hspec]
      exact hDeltaz
    have hsep : (fiber P z).Separable := by
      by_contra hcop
      exact hres (resultant_eq_zero_iff.mpr ⟨Or.inl hfzero, hcop⟩)
    have hnodup := nodup_roots hsep
    have hsplit := D12Complex.AlgebraicClosure.polynomial_splits (fiber P z)
    refine ⟨hfdeg, hnodup, ?_, ?_, ?_⟩
    · change (fiber P z).roots.toFinset.card = d
      rw [Multiset.toFinset_card_of_nodup hnodup,
        ← hsplit.natDegree_eq_card_roots, hfdeg]
    · intro w
      exact Multiset.mem_toFinset.trans (mem_roots hfzero)
    · intro w hw
      change (fiber P z).eval w = 0 at hw
      change (fiber P z).rootMultiplicity w = 1 ∧ (fiber P z).derivative.eval w ≠ 0
      have hpos := (rootMultiplicity_pos hfzero).mpr hw
      have hle := rootMultiplicity_le_one_of_separable hsep w
      refine ⟨by omega, ?_⟩
      intro hderzero
      obtain ⟨A, B, hAB⟩ := hsep
      have hval := congrArg (Polynomial.eval w) hAB
      simp [hw, hderzero] at hval

end D12Complex.Ch21.FiniteExceptionalSet
