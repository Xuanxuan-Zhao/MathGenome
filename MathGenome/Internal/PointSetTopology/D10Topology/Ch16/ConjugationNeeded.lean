import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.ConjugationNeeded
import MathGenome.Internal.PointSetTopology.D10Topology.Ch16.SupNormAlgebras
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Polynomial

noncomputable section
open scoped ComplexConjugate
open Polynomial Set Metric
namespace D10Topology.Ch16.ConjugationNeeded

abbrev coordinate := Specs.D10Topology.Ch16.ConjugationNeeded.coordinate
abbrev conjugateCoordinate := Specs.D10Topology.Ch16.ConjugationNeeded.conjugateCoordinate
abbrev polynomialRestriction := Specs.D10Topology.Ch16.ConjugationNeeded.polynomialRestriction
abbrev polynomialAlgebra := Specs.D10Topology.Ch16.ConjugationNeeded.polynomialAlgebra

theorem restriction_apply : Specs.D10Topology.Ch16.ConjugationNeeded.restriction_apply := by
  intro p z
  exact Polynomial.aeval_continuousMap_apply p coordinate z

theorem conjugate_apply : Specs.D10Topology.Ch16.ConjugationNeeded.conjugate_apply := by
  intro z
  rfl

theorem mem_polynomialAlgebra_iff :
    Specs.D10Topology.Ch16.ConjugationNeeded.mem_polynomialAlgebra_iff := by
  intro f
  rfl

theorem contains_constants : Specs.D10Topology.Ch16.ConjugationNeeded.contains_constants := by
  intro c
  exact polynomialAlgebra.algebraMap_mem c

theorem separates_points : Specs.D10Topology.Ch16.ConjugationNeeded.separates_points := by
  intro x y hxy
  refine ⟨coordinate, ?_, ?_⟩
  · exact ⟨Polynomial.X, Polynomial.aeval_X coordinate⟩
  · exact fun h => hxy (Circle.ext h)

/-- Multiplication by z transforms the boundary error into a polynomial whose
value at the origin has modulus one. -/
private lemma boundary_error (p : ℂ[X]) (z : Circle) :
    ‖(z : ℂ) * p.eval (z : ℂ) - 1‖ =
      ‖(conjugateCoordinate - polynomialRestriction p) z‖ := by
  have hc : (z : ℂ) * conj (z : ℂ) = 1 := by
    rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
  have he : (z : ℂ) * p.eval (z : ℂ) - 1 =
      (z : ℂ) * (p.eval (z : ℂ) - conj (z : ℂ)) := by rw [mul_sub, hc]
  rw [he, norm_mul, Circle.norm_coe, one_mul]
  change _ = ‖conj (z : ℂ) - polynomialRestriction p z‖
  rw [restriction_apply, norm_sub_rev]

theorem conjugate_distance_ge_one :
    Specs.D10Topology.Ch16.ConjugationNeeded.conjugate_distance_ge_one := by
  intro p
  let q : ℂ → ℂ := fun z => z * p.eval z - 1
  have hd : Differentiable ℂ q :=
    (differentiable_id.mul p.differentiable).sub_const 1
  have hbound : ∀ z ∈ frontier (ball (0 : ℂ) 1),
      ‖q z‖ ≤ ‖conjugateCoordinate - polynomialRestriction p‖ := by
    intro z hz
    have hz' : z ∈ sphere (0 : ℂ) 1 := by
      rwa [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hz
    let w : Circle := ⟨z, hz'⟩
    exact (boundary_error p w).le.trans
      ((conjugateCoordinate - polynomialRestriction p).norm_coe_le_norm w)
  have hm := Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_ball (x := (0 : ℂ)) (r := 1)) hd.diffContOnCl hbound
    (subset_closure (mem_ball_self (by norm_num : (0 : ℝ) < 1)))
  simpa [q, Specs.D10Topology.Ch16.SupNormAlgebras.supNorm] using hm

theorem conjugate_not_uniformly_approximable :
    Specs.D10Topology.Ch16.ConjugationNeeded.conjugate_not_uniformly_approximable := by
  intro h
  obtain ⟨p, hp⟩ := h 1 zero_lt_one
  have hnorm : supNorm (conjugateCoordinate - polynomialRestriction p) < 1 := by
    apply (supNorm_lt_iff _ 1 zero_lt_one).2
    intro z
    change ‖conjugateCoordinate z - polynomialRestriction p z‖ < 1
    rw [conjugate_apply, restriction_apply]
    exact hp z
  exact (not_lt_of_ge (conjugate_distance_ge_one p)) hnorm

theorem conjugate_not_mem_uniformClosure :
    Specs.D10Topology.Ch16.ConjugationNeeded.conjugate_not_mem_uniformClosure := by
  intro h
  obtain ⟨g, hg, herr⟩ := (mem_uniformClosure_iff _ _).1 h 1 zero_lt_one
  obtain ⟨p, rfl⟩ := mem_polynomialAlgebra_iff g |>.1 hg
  exact (not_lt_of_ge (conjugate_distance_ge_one p)) herr

theorem not_uniformly_dense : Specs.D10Topology.Ch16.ConjugationNeeded.not_uniformly_dense := by
  intro h
  apply conjugate_not_mem_uniformClosure
  rw [h]
  exact Set.mem_univ _

end D10Topology.Ch16.ConjugationNeeded
