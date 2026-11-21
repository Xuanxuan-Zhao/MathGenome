import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.KillingCriterion
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Complex.Module

/-! Independent specification of LA-U04, source lines 909–912.
The chapter convention (lines 600–603) assumes finite dimension and
characteristic zero. Semisimplicity is the vanishing of the solvable
radical, as in LA-B05, rather than an extra nondegeneracy hypothesis.
The tensor product carries the canonical scalar-extended Lie bracket.
There is no nonzero-dimension assumption. -/

universe u v w t
namespace Specs.LieAlgebrasAndRepresentations.SemisimpleBaseChange

open scoped TensorProduct
open TraceCriterion (killingForm_value)
open SolvableRadical (IsSemisimple_value)

def killingForm_baseChange_type : Prop :=
  ∀ (k : Type u) (K : Type v) (L : Type w)
    [Field k] [Field K] [Algebra k K]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L],
    killingForm_value K (K ⊗[k] L) = (killingForm_value k L).baseChange K

def killingForm_baseChange_matrix_type : Prop :=
  ∀ (k : Type u) (K : Type v) (L : Type w)
    [Field k] [Field K] [Algebra k K]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    {ι : Type t} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k L),
    LinearMap.BilinForm.toMatrix (b.baseChange K) (killingForm_value K (K ⊗[k] L)) =
      (LinearMap.BilinForm.toMatrix b (killingForm_value k L)).map (algebraMap k K)

def semisimple_baseChange_type : Prop :=
  ∀ (k : Type u) (K : Type v) (L : Type w)
    [Field k] [Field K] [Algebra k K]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L] [CharZero k],
    IsSemisimple_value k L → IsSemisimple_value K (K ⊗[k] L)

def semisimple_complexification_type : Prop :=
  ∀ (L : Type w) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L],
    IsSemisimple_value ℝ L → IsSemisimple_value ℂ (ℂ ⊗[ℝ] L)

end Specs.LieAlgebrasAndRepresentations.SemisimpleBaseChange
