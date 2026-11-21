import MathGenome.Internal.Specs.D07.Ch13.TraceNorm
import MathGenome.Internal.D07.Ch13.TraceNormFrobeniusTraceNormFormulas

/-!
Trace and norm for finite fields, K07.13.trace_norm.

The upstream multiplication-matrix bridge and Frobenius formulas concern
the actual multiplication trace and determinant norm, with the specified
base embedding. They are reused without choosing another field copy.

A finite-dimensional extension of a finite field is itself finite, hence
separable. The nondegenerate trace pairing for separable finite extensions
gives a nonzero trace map and therefore surjectivity onto K. This argument
does not divide by [L:K], and includes characteristic dividing the degree.

For norm, the library's finite-field theorem applies directly to the induced
homomorphism on units. Its proof uses the norm power formula and cyclicity
of the unit group to bound the kernel and establish surjectivity.
-/

universe u v

namespace D07.Ch13.TraceNorm

open Specs.D07.Ch13.TraceNorm

theorem multiplicationMatrixConnection : MultiplicationMatrixConnection.{u, v} :=
  TraceNormFrobeniusTraceNormFormulas.multiplicationMatrixConnection

theorem frobeniusTraceFormula : FrobeniusTraceFormula.{u, v} :=
  TraceNormFrobeniusTraceNormFormulas.frobeniusTraceFormula

theorem frobeniusNormProductFormula : FrobeniusNormProductFormula.{u, v} :=
  TraceNormFrobeniusTraceNormFormulas.frobeniusNormProductFormula

theorem frobeniusNormPowerFormula : FrobeniusNormPowerFormula.{u, v} :=
  TraceNormFrobeniusTraceNormFormulas.frobeniusNormPowerFormula

theorem trace_linear : TraceLinear.{u, v} := by
  intro K L _ _ _ _ _
  exact ⟨(Algebra.trace K L).map_add, fun c x => (Algebra.trace K L).map_smul c x⟩

theorem trace_surjective : TraceSurjective.{u, v} := by
  intro K L _ _ _ _ _
  let : Finite L := Module.finite_of_finite K
  exact Algebra.trace_surjective K L

theorem norm_units_surjective : NormUnitsSurjective.{u, v} := by
  intro K L _ _ _ _ _
  let : Finite L := Module.finite_of_finite K
  exact FiniteField.unitsMap_norm_surjective K L

theorem norm_zero : NormZero.{u, v} := by
  intro K L _ _ _ _ _
  exact Algebra.norm_zero

end D07.Ch13.TraceNorm
