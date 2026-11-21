import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.SeparableIntegralClosureFinite
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
The separable stage of Theorem 6.8 (paper.tex 1121–1125).
The library's integral-basis construction clears denominators in algebraic
equations. Its trace-dual construction uses nondegeneracy of the trace form
for finite separable extensions, in arbitrary characteristic. Restricting
scalars makes the dual basis a D-basis of its D-span. Integral trace
coefficients place the closure in this lattice; Noetherianness gives finiteness.
-/

namespace P103.Ch06.SeparableIntegralClosureFinite

open P103.Specs.Ch06.SeparableIntegralClosureFinite

theorem integral_basis : integral_basisType := by
  intro D _ _ _ _ E _ _ _ F _ _ _ _ _ _
  exact FiniteDimensional.exists_is_basis_integral D E F

theorem trace_duality : trace_dualityType := by
  intro D _ _ _ _ E _ _ _ F _ _ _ _ _ _ ι _ _ b i j
  exact b.trace_mul_traceDual i j

theorem trace_expansion : trace_expansionType := by
  intro D _ _ _ _ E _ _ _ F _ _ _ _ _ _ ι _ _ b z
  simpa only [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply] using
    (b.traceDual.sum_repr z).symm

theorem trace_coefficients : trace_coefficientsType := by
  intro D _ _ _ _ E _ _ _ F _ _ _ _ _ _ ι _ _ b hb z hz i
  exact IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_trace (hz.mul (hb i)))

theorem trace_lattice : trace_latticeType := by
  intro D _ _ _ _ E _ _ _ F _ _ _ _ _ _ ι _ _ b hb
  refine ⟨integralClosure_le_span_dualBasis b hb, ?_, ?_⟩
  · exact Module.Free.of_basis (b.traceDual.restrictScalars D)
  · exact Module.Finite.span_of_finite D (Set.finite_range b.traceDual)

theorem finite_integralClosure : finite_integralClosureType := by
  intro D _ _ _ _ E _ _ _ F _ _ _ _ _ _
  exact IsIntegralClosure.finite D E F (integralClosure D F)

end P103.Ch06.SeparableIntegralClosureFinite
