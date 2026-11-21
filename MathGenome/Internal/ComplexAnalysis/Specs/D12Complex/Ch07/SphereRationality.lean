import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.LocalQuotientsArithmetic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Rationality part of paper.tex:1818–1836, d12:07-06. Both source charts
are retained in the conclusion, so all finite cancellations and the actual
value at source infinity are fixed by the punctured rational germs. -/
noncomputable section
namespace Specs.D12Complex.Ch07.SphereRationality
open _root_.D12Complex
open Specs.D12Complex.Ch07.LocalQuotientsArithmetic.Objects

def finite_poles_type : Prop :=
  ∀ (F : RiemannSphere → RiemannSphere), ScalarMeromorphicOnSphere Set.univ F →
    Set.Finite {p | F p = sphereInfty}

def rationality_type : Prop :=
  ∀ (F : RiemannSphere → RiemannSphere), ScalarMeromorphicOnSphere Set.univ F →
    ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
      (∀ z : ℂ, F (sphereFinite z) = fill (fun z => P.eval z / Q.eval z) z) ∧
      F sphereInfty = fill (fun w => P.eval w⁻¹ / Q.eval w⁻¹) 0

end Specs.D12Complex.Ch07.SphereRationality
