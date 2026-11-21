import MathGenome.Internal.Specs.D05.M05.Vandermonde
import MathGenome.Internal.D05.M05.DetDefinition
import MathGenome.Internal.D05.M05.DetInvertible
import Mathlib.LinearAlgebra.Vandermonde

/-! K05.05.vandermonde: the determinant formula and evaluation isomorphism.
The standard determinant formula has the same row/exponent orientation as
the paper. The shared determinant bridge transfers it to the paper's Leibniz
definition. The coordinate formula then factors evaluation through the
coefficient isomorphism and an invertible Vandermonde matrix.
-/

noncomputable section

namespace D05.M05.Vandermonde

open scoped BigOperators

def evaluationMap : Specs.D05.M05.Vandermonde.evaluationMap_type :=
  Specs.D05.M05.Vandermonde.evaluationMap_value

theorem degree_bound : Specs.D05.M05.Vandermonde.degree_bound := by
  intro R _ n p
  exact ⟨Polynomial.mem_degreeLT, (Polynomial.degreeLT R n).zero_mem⟩

theorem empty_domain : Specs.D05.M05.Vandermonde.empty_domain := by
  intro R _ p
  have hp := Polynomial.mem_degreeLT.mp p.property
  apply Polynomial.ext
  intro m
  simpa only [Polynomial.coeff_zero] using
    (Polynomial.degree_lt_iff_coeff_zero (p : Polynomial R) 0).mp hp m (Nat.zero_le m)

theorem determinant_formula : Specs.D05.M05.Vandermonde.determinant_formula := by
  intro R _ n b
  rw [DetDefinition.matrix_det_bridge]
  exact Matrix.det_vandermonde b

theorem small_determinants : Specs.D05.M05.Vandermonde.small_determinants := by
  intro R _
  constructor <;> intro b <;> rw [determinant_formula] <;> simp

theorem evaluation_matrix : Specs.D05.M05.Vandermonde.evaluation_matrix := by
  intro R _ n b
  ext i j
  simp [Specs.D05.M04.MatrixOfMap.matrixOfMap_value, LinearMap.toMatrix_apply,
    D05.Specs.FormalPolynomials.coordinateBasisValue,
    Specs.D05.M05.Vandermonde.evaluationMap_value]

theorem evaluation_coordinates : Specs.D05.M05.Vandermonde.evaluation_coordinates := by
  intro R _ n b p
  funext i
  change (p : Polynomial R).eval (b i) =
    ∑ j : Fin n, b i ^ (j : ℕ) * ((Polynomial.degreeLTEquiv R n) p) j
  simpa only [mul_comm] using Polynomial.eval_eq_sum_degreeLTEquiv p.property (b i)

theorem determinant_nonzero_iff : Specs.D05.M05.Vandermonde.determinant_nonzero_iff := by
  intro K _ n b
  rw [DetDefinition.matrix_det_bridge]
  exact Matrix.det_vandermonde_ne_zero_iff

theorem evaluation_bijective : Specs.D05.M05.Vandermonde.evaluation_bijective := by
  intro K _ n b hb
  let A : Matrix (Fin n) (Fin n) K := Matrix.of fun (i j : Fin n) => b i ^ (j : ℕ)
  have hA : Function.Bijective
      (Specs.D05.M04.MatrixOfMap.coordinateLinearMap_value A) :=
    (DetInvertible.bijective_iff_isUnit_det A).mpr
      (isUnit_iff_ne_zero.mpr ((determinant_nonzero_iff b).mpr hb))
  have hcomp : Specs.D05.M05.Vandermonde.evaluationMap_value b =
      (Specs.D05.M04.MatrixOfMap.coordinateLinearMap_value A).comp
        (Polynomial.degreeLTEquiv K n).toLinearMap := by
    apply LinearMap.ext
    exact evaluation_coordinates b
  rw [hcomp]
  exact hA.comp (Polynomial.degreeLTEquiv K n).bijective

theorem evaluation_isomorphism : Specs.D05.M05.Vandermonde.evaluation_isomorphism := by
  intro K _ n b hb
  let e := LinearEquiv.ofBijective
    (Specs.D05.M05.Vandermonde.evaluationMap_value b) (evaluation_bijective b hb)
  refine ⟨e, fun _ _ => rfl, ?_⟩
  intro e' he'
  apply LinearEquiv.ext
  intro p
  funext i
  exact he' p i

theorem unique_interpolant : Specs.D05.M05.Vandermonde.unique_interpolant := by
  intro K _ n b hb y
  obtain ⟨e, he, _⟩ := evaluation_isomorphism b hb
  refine ⟨(e.symm y : Polynomial K),
    ⟨Polynomial.mem_degreeLT.mp (e.symm y).property, ?_⟩, ?_⟩
  · intro i
    rw [← he, e.apply_symm_apply]
  · intro p hp
    let q : Polynomial.degreeLT K n := ⟨p, Polynomial.mem_degreeLT.mpr hp.1⟩
    have hq : e q = y := by
      funext i
      exact (he q i).trans (hp.2 i)
    exact congrArg (fun r : Polynomial.degreeLT K n => (r : Polynomial K))
      (e.injective (hq.trans (e.apply_symm_apply y).symm))

end D05.M05.Vandermonde
