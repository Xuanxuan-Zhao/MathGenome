import MathGenome.Internal.Specs.D05.M15.HilbertSeries.Weighted
import MathGenome.Internal.D05.M15.HilbertSeries
import MathGenome.Internal.D05.M15.TensorBasis
import MathGenome.Internal.D05.M06.SumDimension

/-!
K05.15.hilbert_series, paper.tex:3210. The prerequisite Hilbert-series module
already proves the weighted monomial counts and formal identities. Reuse those
proofs for the same canonical objects. We additionally record finiteness of
tensor powers using their actual product basis, and finiteness and the dimension
of each graded tensor product using the finite direct-sum dimension theorem.
-/

noncomputable section
namespace D05.M15.HilbertSeries.Weighted
open Specs.D05.M15.HilbertSeries
open scoped TensorProduct DirectSum

theorem tensor_dimension : Specs.D05.M15.HilbertSeries.Weighted.tensor_dimension := by
  intro K V _ _ _ _ p
  classical
  exact ⟨(Basis.piTensorProduct (fun _ : Fin p => Module.finBasis K V)).finiteDimensional_of_finite,
    D05.M15.HilbertSeries.tensor_dimension p⟩

theorem tensor_series : Specs.D05.M15.HilbertSeries.Weighted.tensor_series :=
  D05.M15.HilbertSeries.tensor_series

theorem tensor_inverse : Specs.D05.M15.HilbertSeries.Weighted.tensor_inverse :=
  D05.M15.HilbertSeries.tensor_inverse

theorem tensor_grade_dimension :
    Specs.D05.M15.HilbertSeries.Weighted.tensor_grade_dimension := by
  intro K _ U W _ _ _ _ _ _ k
  classical
  let M := fun ab : {ab : ℕ × ℕ // ab ∈ Finset.antidiagonal k} =>
    U ab.val.1 ⊗[K] W ab.val.2
  letI : ∀ ab, FiniteDimensional K (M ab) := fun _ =>
    (D05.M15.TensorBasis.finite_dimension).1
  refine ⟨D05.M06.SumDimension.external_finiteDimensional (K := K) (M := M), ?_⟩
  change Module.finrank K (⨁ ab, M ab) = _
  rw [D05.M06.SumDimension.external_dimension (K := K) (M := M)]
  simp only [M, Module.finrank_tensorProduct]
  exact Finset.sum_coe_sort (Finset.antidiagonal k)
    (fun ab => Module.finrank K (U ab.1) * Module.finrank K (W ab.2))

theorem tensor_product_series :
    Specs.D05.M15.HilbertSeries.Weighted.tensor_product_series :=
  D05.M15.HilbertSeries.tensor_product_series

theorem weighted_exponents_finite :
    Specs.D05.M15.HilbertSeries.Weighted.weighted_exponents_finite := by
  intro I _ d hd k
  exact D05.M15.HilbertSeries.weighted_tuples_finite d hd k

theorem weighted_symmetric_part_monomials :
    Specs.D05.M15.HilbertSeries.Weighted.weighted_symmetric_part_monomials :=
  D05.M15.HilbertSeries.weighted_symmetric_part_monomials

theorem positive_weight_finiteness :
    Specs.D05.M15.HilbertSeries.Weighted.positive_weight_finiteness :=
  D05.M15.HilbertSeries.positive_weight_finiteness

theorem weighted_exterior_series :
    Specs.D05.M15.HilbertSeries.Weighted.weighted_exterior_series :=
  D05.M15.HilbertSeries.weighted_exterior_series

theorem weighted_symmetric_series :
    Specs.D05.M15.HilbertSeries.Weighted.weighted_symmetric_series :=
  D05.M15.HilbertSeries.weighted_symmetric_series

theorem weighted_geometric_inverse :
    Specs.D05.M15.HilbertSeries.Weighted.weighted_geometric_inverse :=
  D05.M15.HilbertSeries.weighted_geometric_inverse

theorem weighted_symmetric_inverse :
    Specs.D05.M15.HilbertSeries.Weighted.weighted_symmetric_inverse :=
  D05.M15.HilbertSeries.weighted_symmetric_inverse

end D05.M15.HilbertSeries.Weighted
