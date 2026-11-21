import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.AbstractJordan
import Mathlib.Algebra.DirectSum.Module

/-! LA-C07, notes/005/lie-algebras-and-representations.tex, lines 1472–1555.
The section convention at 1184–1190 makes the algebra and module finite
 dimensional. The field is arbitrary of characteristic zero; algebraic closure
is imposed only for the simultaneous weight decomposition. -/

universe u v w
open scoped Classical
namespace LieAlgebrasAndRepresentations.RepresentationJordan

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual simultaneous eigenspace for a linear functional on a subalgebra. -/
def weightSpace {k : Type u} [Field k]
    {g : Type v} [LieRing g] [LieAlgebra k g]
    {V : Type w} [AddCommGroup V] [Module k V]
    (ρ : g →ₗ⁅k⁆ Module.End k V) (H : LieSubalgebra k g) (χ : H →ₗ[k] k) :
    Submodule k V :=
  ⨅ h : H, Module.End.eigenspace (ρ h.val) (χ h)

end LieAlgebrasAndRepresentations.RepresentationJordan

namespace Specs.LieAlgebrasAndRepresentations.RepresentationJordan
open _root_.LieAlgebrasAndRepresentations
open _root_.LieAlgebrasAndRepresentations.RepresentationJordan
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The represented abstract parts are the unique ordinary linear Jordan parts. -/
def preserves_jordan_type : Prop :=
  ∀ (k : Type u) (g : Type v) (V : Type w)
    [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V],
    SolvableRadical.IsSemisimple_value k g →
    ∀ (ρ : g →ₗ⁅k⁆ Module.End k V) (x s n : g),
      IsAbstractJordanDecomposition (k := k) x s n →
      IsJordanDecomposition (ρ x) (ρ s) (ρ n)

/-- An explicit version of both equalities in (3.10), without chosen part functions. -/
def jordan_parts_eq_type : Prop :=
  ∀ (k : Type u) (g : Type v) (V : Type w)
    [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V],
    SolvableRadical.IsSemisimple_value k g →
    ∀ (ρ : g →ₗ⁅k⁆ Module.End k V) (x s n : g)
      (S N : Module.End k V),
      IsAbstractJordanDecomposition (k := k) x s n →
      IsJordanDecomposition (ρ x) S N → ρ s = S ∧ ρ n = N

/-- The restriction to any abelian subalgebra of adjoint-semisimple elements. -/
def toral_acts_semisimply_type : Prop :=
  ∀ (k : Type u) (g : Type v) (V : Type w)
    [Field k] [CharZero k] [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V],
    SolvableRadical.IsSemisimple_value k g →
    ∀ (ρ : g →ₗ⁅k⁆ Module.End k V) (H : LieSubalgebra k g),
      (∀ a b : H, ⁅a, b⁆ = 0) →
      (∀ a : H, IsAbsolutelySemisimple (LieAlgebra.ad k g a.val)) →
      ∀ a : H, IsAbsolutelySemisimple (ρ a.val)

/-- Over an algebraically closed field, the canonical sum of simultaneous
weight spaces is an isomorphism. Weights are actual linear functionals on H.
Zero representations and the zero subalgebra are included. -/
def toral_weight_decomposition_type : Prop :=
  ∀ (k : Type u) (g : Type v) (V : Type w)
    [Field k] [CharZero k] [IsAlgClosed k]
    [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V],
    SolvableRadical.IsSemisimple_value k g →
    ∀ (ρ : g →ₗ⁅k⁆ Module.End k V) (H : LieSubalgebra k g),
      (∀ a b : H, ⁅a, b⁆ = 0) →
      (∀ a : H, IsAbsolutelySemisimple (LieAlgebra.ad k g a.val)) →
      DirectSum.IsInternal (fun χ : H →ₗ[k] k => weightSpace ρ H χ)

end Specs.LieAlgebrasAndRepresentations.RepresentationJordan
