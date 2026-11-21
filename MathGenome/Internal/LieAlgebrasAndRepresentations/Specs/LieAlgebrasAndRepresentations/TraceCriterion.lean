import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DerivedLowerSeries
import Mathlib.Algebra.Lie.TraceForm

/-! LA-B04: source lines 784–861, with the finite-dimensional convention
at the start of Chapter 2. Both criteria hold over the original characteristic-zero
field, without an algebraic-closure or nonzero-dimension hypothesis. -/

universe u v
namespace Specs.LieAlgebrasAndRepresentations.TraceCriterion

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The matrix trace criterion, with the derived algebra taken intrinsically
in `A` and mapped into `End k V` by the subalgebra inclusion. -/
def trace_criterion_type : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A : LieSubalgebra k (Module.End k V)),
    LieAlgebra.IsSolvable A ↔
      ∀ x : A, x ∈ LieAlgebra.derivedSeries k A 1 →
        ∀ y : A, LinearMap.trace k V ((x : Module.End k V) * (y : Module.End k V)) = 0

/-- The Killing form is the trace of the product of adjoint operators. -/
noncomputable def killingForm_value (k : Type u) (G : Type v)
    [Field k] [LieRing G] [LieAlgebra k G] : LinearMap.BilinForm k G :=
  _root_.killingForm k G

def killingForm_type :=
  ∀ (k : Type u) (G : Type v) [Field k] [LieRing G] [LieAlgebra k G],
    LinearMap.BilinForm k G

def killingForm_apply_type : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [LieRing G] [LieAlgebra k G]
    (x y : G), killingForm_value k G x y =
      LinearMap.trace k G (LieAlgebra.ad k G x * LieAlgebra.ad k G y)

def killing_criterion_type : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {G : Type v} [LieRing G] [LieAlgebra k G] [FiniteDimensional k G],
    LieAlgebra.IsSolvable G ↔
      ∀ x : G, x ∈ LieAlgebra.derivedSeries k G 1 →
        ∀ y : G, killingForm_value k G x y = 0

end Specs.LieAlgebrasAndRepresentations.TraceCriterion
