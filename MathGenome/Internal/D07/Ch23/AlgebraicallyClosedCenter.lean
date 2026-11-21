import MathGenome.Internal.Specs.D07.Ch23.AlgebraicallyClosedCenter
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
K07.23.algebraically_closed_center. A central scalar map permits polynomial
evaluation in a noncommutative division ring. A singleton-generated
subalgebra is commutative even though the ambient ring need not be.
Algebraicity over a field is equivalent to integrality, so its powers span
a finite-dimensional subalgebra. A finite-dimensional domain over a field
is a division ring, hence this commutative subalgebra is a field.

For the second assertion, the library's minimal-polynomial argument applies
to any `Ring` with `IsDomain`, including noncommutative division rings:
over an algebraically closed field each irreducible minimal polynomial
is linear, making every element a scalar.
-/

universe u v

namespace D07.Ch23.AlgebraicallyClosedCenter

open Specs.D07.Ch23.AlgebraicallyClosedCenter

theorem simpleAdjoinFiniteField : SimpleAdjoinFiniteField.{u, v} := by
  intro K D _ _ _ x hx
  have hfinite : Module.Finite K (Algebra.adjoin K {x}) :=
    Algebra.finite_adjoin_simple_of_isIntegral hx.isIntegral
  let := hfinite
  let := fieldOfFiniteDimensional K (Algebra.adjoin K {x})
  exact ⟨Field.toIsField _, hfinite, (algebraMap K (Algebra.adjoin K {x})).injective⟩

theorem scalarMapBijective : ScalarMapBijective.{u, v} := by
  intro K D _ _ _ _ h
  let : Algebra.IsIntegral K D := ⟨fun x => (h x).isIntegral⟩
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

end D07.Ch23.AlgebraicallyClosedCenter
