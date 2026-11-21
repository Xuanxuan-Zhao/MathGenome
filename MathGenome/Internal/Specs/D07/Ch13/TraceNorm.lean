import MathGenome.Internal.Specs.D07.Ch13.TraceNormFrobeniusTraceNormFormulas

/-!
Independent statements for K07.13.trace_norm (paper.tex:4065–4084).

The canonical `Algebra.trace` and `Algebra.norm` are respectively the trace
and determinant of the K-linear multiplication operator. The first statement
records their coordinate interpretation in every finite basis. The following
three statements retain the previously specified Frobenius formulas.

All new assertions quantify over an arbitrary specified finite extension of
a finite field, so apply in particular to the embedded fields in the fixed
algebraic closure. Neither separability nor nonvanishing of the degree in K
is assumed. The cardinality q need not be prime. Finite degree is imposed
explicitly; the natural-number finrank and cardinalities are genuine here.
The units map in the norm assertion is induced by this same determinant norm.
-/

universe u v

namespace Specs.D07.Ch13.TraceNorm

def MultiplicationMatrixConnection : Prop :=
  TraceNormFrobeniusTraceNormFormulas.MultiplicationMatrixConnection.{u, v}

def FrobeniusTraceFormula : Prop :=
  TraceNormFrobeniusTraceNormFormulas.FrobeniusTraceFormula.{u, v}

def FrobeniusNormProductFormula : Prop :=
  TraceNormFrobeniusTraceNormFormulas.FrobeniusNormProductFormula.{u, v}

def FrobeniusNormPowerFormula : Prop :=
  TraceNormFrobeniusTraceNormFormulas.FrobeniusNormPowerFormula.{u, v}

/-- Additivity and K-homogeneity of the multiplication trace. -/
def TraceLinear : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [FiniteDimensional K L],
    (∀ x y : L, Algebra.trace K L (x + y) =
      Algebra.trace K L x + Algebra.trace K L y) ∧
    (∀ (c : K) (x : L), Algebra.trace K L (c • x) = c * Algebra.trace K L x)

/-- The trace is onto even when the characteristic divides [L:K]. -/
def TraceSurjective : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [FiniteDimensional K L],
    Function.Surjective (Algebra.trace K L)

/-- Surjectivity on the multiplicative groups, not just on field elements. -/
def NormUnitsSurjective : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [FiniteDimensional K L],
    Function.Surjective (Units.map (Algebra.norm K (S := L)))

/-- The value at zero mentioned in the source proof. -/
def NormZero : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [Finite K] [FiniteDimensional K L], Algebra.norm K (0 : L) = 0

end Specs.D07.Ch13.TraceNorm
