import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Universal
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Polynomial

/-! Polynomial differentials, KD-07. -/
namespace AdvCommAlg.Differentials

universe u v
noncomputable section

/-- The basis indexed by the variables, valid even for an empty index type. -/
def polynomialBasis : Specs.AdvCommAlg.Differentials.polynomialBasisType.{u,v} :=
  fun A ι _ => KaehlerDifferential.mvPolynomialBasis A ι

theorem polynomial_basis_apply : Specs.AdvCommAlg.Differentials.polynomialBasisApply := by
  intro A ι _ i
  exact KaehlerDifferential.mvPolynomialBasis_apply A ι i

theorem polynomial_free : Specs.AdvCommAlg.Differentials.polynomialFree := by
  intro A ι _
  exact Module.Free.of_basis (polynomialBasis A ι)

theorem polynomial_coordinates : Specs.AdvCommAlg.Differentials.polynomialCoordinates := by
  intro A ι _ f i
  exact KaehlerDifferential.mvPolynomialBasis_repr_apply A ι f i

theorem polynomial_partials_outside_vars :
    Specs.AdvCommAlg.Differentials.polynomialPartialsOutsideVars := by
  intro A ι _ f i hi
  exact MvPolynomial.pderiv_eq_zero_of_notMem_vars hi

theorem polynomial_differential_expansion :
    Specs.AdvCommAlg.Differentials.polynomialDifferentialExpansion := by
  intro A ι _ f
  classical
  let b := KaehlerDifferential.mvPolynomialBasis A ι
  let df := KaehlerDifferential.D A (MvPolynomial ι A) f
  have hs : (b.repr df).support ⊆ f.vars := by
    intro i hi
    by_contra hn
    have hz := MvPolynomial.pderiv_eq_zero_of_notMem_vars hn
    exact (Finsupp.mem_support_iff.mp hi)
      ((KaehlerDifferential.mvPolynomialBasis_repr_apply A ι f i).trans hz)
  calc
    df = ∑ i ∈ (b.repr df).support, b.repr df i • b i := by
      simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
        (b.linearCombination_repr df).symm
    _ = ∑ i ∈ f.vars, b.repr df i • b i := by
      apply Finset.sum_subset hs
      intro i _ hi
      rw [Finsupp.notMem_support_iff.mp hi, zero_smul]
    _ = _ := by
      simp only [b, df, KaehlerDifferential.mvPolynomialBasis_repr_apply,
        KaehlerDifferential.mvPolynomialBasis_apply]

theorem univariate_differential : Specs.AdvCommAlg.Differentials.univariateDifferential := by
  intro A _ f
  exact KaehlerDifferential.polynomial_D_apply A f

theorem empty_polynomial_differentials :
    Specs.AdvCommAlg.Differentials.emptyPolynomialDifferentials := by
  intro A ι _ _
  exact (KaehlerDifferential.mvPolynomialBasis A ι).repr.injective.subsingleton

end
end AdvCommAlg.Differentials
