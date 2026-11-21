import MathGenome.Internal.Specs.D07.Ch13.TraceNormFrobeniusTraceNormFormulas
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
K07.13.trace_norm, formula and multiplication-matrix part.

The library trace/norm are defined using the linear endomorphism of left
multiplication. The first theorem proves the explicit coordinate bridge for
every finite basis. The finite-field formulas then use the library's proved
sum/product over automorphisms and the bijection between these automorphisms
and the first [L:K] powers of relative Frobenius. Finiteness of L is derived
from the hypotheses, and no Galois or separability hypothesis is added.

The norm power formula uses |L| = |K|^[L:K]. Its underlying library theorem
even holds at zero; we retain the source's nonzero premise in the interface.
-/

universe u v

namespace D07.Ch13.TraceNormFrobeniusTraceNormFormulas

open Specs.D07.Ch13.TraceNormFrobeniusTraceNormFormulas

theorem multiplicationMatrixConnection : MultiplicationMatrixConnection.{u, v} := by
  intro K L _ _ _ n b x
  exact ⟨Algebra.leftMulMatrix_eq_repr_mul b x,
    Algebra.leftMulMatrix_mulVec_repr b x,
    Algebra.trace_eq_matrix_trace b x, Algebra.norm_eq_matrix_det b x⟩

theorem frobeniusTraceFormula : FrobeniusTraceFormula.{u, v} := by
  intro K L _ _ _ _ _ q n hq hn x
  let : Finite L := Module.finite_of_finite K
  simpa only [hq, hn] using FiniteField.algebraMap_trace_eq_sum_pow K L x

theorem frobeniusNormProductFormula : FrobeniusNormProductFormula.{u, v} := by
  intro K L _ _ _ _ _ q n hq hn x
  let : Finite L := Module.finite_of_finite K
  simpa only [hq, hn] using FiniteField.algebraMap_norm_eq_prod_pow K L x

theorem frobeniusNormPowerFormula : FrobeniusNormPowerFormula.{u, v} := by
  intro K L _ _ _ _ _ q n hq hn x _hx
  let : Finite L := Module.finite_of_finite K
  have hcard : Nat.card L = q ^ n := by
    simpa only [hq, hn] using Module.natCard_eq_pow_finrank (K := K) (V := L)
  simpa only [hcard, hq] using
    (FiniteField.algebraMap_norm_eq_pow (K := K) (K' := L) (x := x))

end D07.Ch13.TraceNormFrobeniusTraceNormFormulas
