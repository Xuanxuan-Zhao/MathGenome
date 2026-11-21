import MathGenome.Internal.Specs.D05.Foundations.FormalPolynomials

/-! Formal coefficient polynomials and the finite free coordinate module.
All statements apply to zero variables and to the zero ring. Only the leading
term statement uses a field and nonzero polynomials. -/

noncomputable section

namespace D05.Foundations.FormalPolynomials

open D05.Foundations

/-- Change the monomial indices from finite-support exponents to tuples. -/
def coefficientRingEquiv : D05.Specs.FormalPolynomials.coefficientRingEquivType := D05.Specs.FormalPolynomials.coefficientRingEquivValue

/-- Forget only the convolution-ring wrapper, retaining finite support. -/
def coefficientEquiv : D05.Specs.FormalPolynomials.coefficientEquivType := D05.Specs.FormalPolynomials.coefficientEquivValue

theorem coefficientBridge : D05.Specs.FormalPolynomials.coefficientBridge := by
  intro R _ m p α
  simp [D05.Specs.FormalPolynomials.coefficientEquivValue, D05.Specs.FormalPolynomials.coefficientRingEquivValue]

theorem inverseCoefficientBridge : D05.Specs.FormalPolynomials.inverseCoefficientBridge := by
  intro R _ m a s
  have h := coefficientBridge R m ((D05.Specs.FormalPolynomials.coefficientEquivValue R m).symm a)
    (exponentEquiv m s)
  simpa using h.symm

theorem coefficientExt : D05.Specs.FormalPolynomials.coefficientExt := by
  intro R _ m p q
  constructor
  · intro h
    subst q
    intro α
    rfl
  · intro h
    exact (D05.Specs.FormalPolynomials.coefficientEquivValue R m).injective (Finsupp.ext h)

theorem splittingMembership : D05.Specs.FormalPolynomials.splittingMembership := by
  intro m γ α β
  simp only [exponentSplittings, Finset.mem_map_equiv, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_apply, Finset.mem_antidiagonal]
  change ((exponentEquiv m).symm α + (exponentEquiv m).symm β =
    (exponentEquiv m).symm γ) ↔ α + β = γ
  rw [← (exponentEquiv m).symm.map_add]
  exact (exponentEquiv m).symm.injective.eq_iff

theorem familyOperations : D05.Specs.FormalPolynomials.familyOperations := by
  intro R _ m a b γ
  refine ⟨rfl, rfl, ?_, ?_⟩
  · classical
    change Finsupp.single 0 (1 : R) γ = _
    simp only [Finsupp.single_apply, eq_comm]
  · exact AddMonoidAlgebra.coeff_mul_antidiag a b γ (exponentSplittings γ)
      (fun {_} => splittingMembership m γ _ _)

theorem coefficientOperations : D05.Specs.FormalPolynomials.coefficientOperations := by
  intro R _ m p q α
  have h : (exponentEquiv m).symm α = 0 ↔ α = 0 := by
    rw [← (exponentEquiv m).symm.map_zero, (exponentEquiv m).symm.injective.eq_iff]
  have hc (a : FormalPolynomial R m) :
      D05.Specs.FormalPolynomials.coefficientEquivValue R m a α =
        a.coeff ((exponentEquiv m).symm α) := coefficientBridge R m a α
  simp only [hc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · classical
    have h' : 0 = (exponentEquiv m).symm α ↔ α = 0 := eq_comm.trans h
    simp only [MvPolynomial.coeff_one, h']

theorem coefficientConvolution : D05.Specs.FormalPolynomials.coefficientConvolution := by
  intro R _ m p q γ
  change (D05.Specs.FormalPolynomials.coefficientRingEquivValue R m (p * q)).coeff γ = _
  rw [map_mul]
  exact (familyOperations R m (D05.Specs.FormalPolynomials.coefficientRingEquivValue R m p)
    (D05.Specs.FormalPolynomials.coefficientRingEquivValue R m q) γ).2.2.2

theorem coefficientRingLaws : D05.Specs.FormalPolynomials.coefficientRingLaws := by
  intro R _ m a b c
  exact ⟨add_assoc a b c, add_comm a b, zero_add a, add_zero a,
    neg_add_cancel a, mul_assoc a b c, mul_comm a b, one_mul a, mul_one a,
    mul_add a b c, add_mul a b c⟩

def zeroVariableEquiv : D05.Specs.FormalPolynomials.zeroVariableEquivType := D05.Specs.FormalPolynomials.zeroVariableEquivValue

theorem zeroVariableCoefficients : D05.Specs.FormalPolynomials.zeroVariableCoefficients := by
  intro R _ p
  have h : (exponentEquiv 0).symm 0 = 0 := map_zero _
  rw [coefficientBridge, h]
  exact ⟨rfl, (MvPolynomial.eq_C_of_isEmpty p)⟩

def singleVariableEquiv : D05.Specs.FormalPolynomials.singleVariableEquivType := D05.Specs.FormalPolynomials.singleVariableEquivValue

theorem singleVariableCoefficients : D05.Specs.FormalPolynomials.singleVariableCoefficients := by
  intro R _ p n
  rw [coefficientBridge]
  have h : (exponentEquiv 1).symm (fun _ => n) = Finsupp.single default n := by
    apply Finsupp.ext
    intro i
    change n = Finsupp.single default n i
    simp [Subsingleton.elim i default]
  rw [h]
  exact MvPolynomial.coeff_uniqueAlgEquiv R p n

def univariateCoefficientEquiv : D05.Specs.FormalPolynomials.univariateCoefficientEquivType :=
  D05.Specs.FormalPolynomials.univariateCoefficientEquivValue

theorem univariateCoefficientBridge : D05.Specs.FormalPolynomials.univariateCoefficientBridge := by
  intro R _ p n
  exact Polynomial.toFinsupp_apply p n

theorem leadingTerms : D05.Specs.FormalPolynomials.leadingTerms := by
  intro K _ p q hp hq
  refine ⟨mul_ne_zero hp hq, Polynomial.leadingCoeff_mul p q, ?_,
    Polynomial.natDegree_mul hp hq, Polynomial.degree_mul⟩
  rw [← Polynomial.natDegree_mul hp hq, Polynomial.coeff_natDegree,
    Polynomial.leadingCoeff_mul]

def coordinateBasis : D05.Specs.FormalPolynomials.coordinateBasisType := D05.Specs.FormalPolynomials.coordinateBasisValue

theorem coordinateOperations : D05.Specs.FormalPolynomials.coordinateOperations := by
  intro R _ n v w r i
  exact ⟨rfl, rfl, rfl, Pi.basisFun_apply R (Fin n) i⟩

theorem coordinateExpansion : D05.Specs.FormalPolynomials.coordinateExpansion := by
  intro R _ n v
  simpa only [D05.Specs.FormalPolynomials.coordinateBasisValue, Pi.basisFun_repr] using
    (Pi.basisFun R (Fin n)).sum_repr v |>.symm

end D05.Foundations.FormalPolynomials
