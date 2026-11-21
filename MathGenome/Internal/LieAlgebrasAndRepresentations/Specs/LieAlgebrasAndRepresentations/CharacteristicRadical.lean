import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableRadical
import Mathlib.Algebra.Lie.TraceForm
import Mathlib.Algebra.Lie.Derivation.Basic

/-! The radical portion of LA-B08, equations (2.6) and the following two
paragraphs. The chapter assumes finite dimension; the field is any field of
characteristic zero. Scalar extensions are arbitrary field extensions. -/
universe u v w
namespace Specs.LieAlgebrasAndRepresentations.CharacteristicRadical

open scoped TensorProduct

def radical_eq_killingCompl_derived_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    SolvableRadical.radical_value k L =
      (LieAlgebra.derivedSeries k L 1).killingCompl k L

def radical_baseChange_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (K : Type w) [Field K] [Algebra k K],
    SolvableRadical.radical_value K (K ⊗[k] L) =
      (SolvableRadical.radical_value k L).baseChange K

def derivation_mem_radical_type : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (D : LieDerivation k L L) (x : L),
    x ∈ SolvableRadical.radical_value k L →
      D x ∈ SolvableRadical.radical_value k L

end Specs.LieAlgebrasAndRepresentations.CharacteristicRadical
