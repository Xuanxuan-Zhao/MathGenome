import MathGenome.Internal.Specs.D05.M15.Charcoefficients
import MathGenome.Internal.D05.M04.Trace
import MathGenome.Internal.D05.M08.Charpoly
import MathGenome.Internal.D05.M15.WedgeSign
import MathGenome.Internal.D05.M15.DeterminantLine.MinorCoefficients
import MathGenome.Internal.D05.M15.Charcoefficients.PrincipalExpansion

noncomputable section
namespace D05.M15.Charcoefficients
open scoped BigOperators
open Specs.D05.M15

/-- Simultaneously ordering the rows and columns does not change a principal minor. -/
theorem ordered_principal_minor {K : Type*} [Field K] {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (I : Set.powersetCard (Fin n) p) :
    Matrix.det (A.submatrix (I.val.orderEmbOfFin I.prop) (I.val.orderEmbOfFin I.prop)) =
      Matrix.det (A.submatrix (Subtype.val : I.val → Fin n) (Subtype.val : I.val → Fin n)) := by
  classical
  exact Matrix.det_submatrix_equiv_self (I.val.orderIsoOfFin I.prop).toEquiv
    (A.submatrix (Subtype.val : I.val → Fin n) (Subtype.val : I.val → Fin n))

theorem trace_principal_minors : Charcoefficients.trace_principal_minors := by
  intro K V _ _ _ _ n b T p
  classical
  rw [LinearMap.trace_eq_matrix_trace K (b.exteriorPower p)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  apply Finset.sum_congr rfl
  intro I _
  rw [exteriorPower.basis_apply]
  change (b.exteriorPower p).repr
    (WedgeSign.powerMap_value p T (ExteriorBasis.increasingWedge b p I)) I = _
  rw [DeterminantLine.MinorCoefficients.based_minor_coefficients,
    D05.M05.DetDefinition.matrix_det_bridge, ordered_principal_minor]

/-- Partition all subsets by their size, keeping the empty subset. -/
theorem sum_subsets_by_card {α M : Type*} [Fintype α] [AddCommMonoid M]
    (f : Finset α → M) :
    ∑ I : Finset α, f I =
      ∑ p ∈ Finset.range (Fintype.card α + 1),
        ∑ I : Set.powersetCard α p, f I.val := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card)
    (s := (Finset.univ : Finset (Finset α)))
    (t := Finset.range (Fintype.card α + 1))
    (fun I _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ I))) f]
  apply Finset.sum_congr rfl
  intro p _
  exact Finset.sum_subtype _ (by simp [Set.powersetCard]) f

theorem based_polynomial_expansion : Charcoefficients.based_polynomial_expansion := by
  intro K V _ _ _ _ n b T
  classical
  rw [D05.M08.Charpoly.determinant_formula b T]
  have hs : Matrix.scalar (Fin n) (Polynomial.X : Polynomial K) =
      (Polynomial.X : Polynomial K) • (1 : Matrix (Fin n) (Fin n) (Polynomial K)) := by
    simp only [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [hs, PrincipalExpansion.polynomial_expansion, sum_subsets_by_card]
  simp only [Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Set.powersetCard.card_eq]
  rw [← Finset.mul_sum, trace_principal_minors b T p, map_mul, map_sum]
  simp only [map_pow, map_neg, map_one]
  ring

theorem polynomial_expansion : Charcoefficients.polynomial_expansion := by
  intro K V _ _ _ _ T
  exact based_polynomial_expansion (Module.finBasis K V) T

theorem scalar_expansion : Charcoefficients.scalar_expansion := by
  intro K V _ _ _ _ n b T t
  classical
  rw [PrincipalExpansion.scalar_expansion, sum_subsets_by_card]
  simp only [Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Set.powersetCard.card_eq]
  rw [← Finset.mul_sum, trace_principal_minors b T p]
  ring

theorem degree_zero_trace : Charcoefficients.degree_zero_trace := by
  intro K V _ _ _ _ T
  have hmap : WedgeSign.powerMap_value 0 T = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply (exteriorPower.zeroEquiv K V).injective
    exact D05.M15.WedgeSign.power_map_zero T x
  rw [hmap]
  simp

theorem zero_dimensional : Charcoefficients.zero_dimensional := by
  exact D05.M08.Charpoly.zero_dimensional

theorem charpoly_comp_comm : Charcoefficients.charpoly_comp_comm := by
  intro K V _ _ _ _ A B
  classical
  rw [polynomial_expansion, polynomial_expansion]
  apply Finset.sum_congr rfl
  intro p _
  rw [D05.M15.WedgeSign.power_map_comp, D05.M15.WedgeSign.power_map_comp,
    LinearMap.trace_comp_comm']

end D05.M15.Charcoefficients
