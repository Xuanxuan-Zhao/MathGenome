import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
Independent statements for K07.23.algebraically_closed_center,
paper.tex:7425–7448. `Algebra K D` specifies the central scalar map;
it does not impose commutativity on the division ring D. Algebraicity
is elementwise and does not assume finite dimension of D.

The subring K[x] is the canonical singleton-generated subalgebra, with
its inherited operations and scalar action. `IsField` asserts the field
property for those operations, and `Module.Finite` asserts finite degree,
not finite cardinality. Equality with the embedded base field is expressed
by bijectivity of the specified scalar map between the two types.
-/

universe u v

namespace Specs.D07.Ch23.AlgebraicallyClosedCenter

/-- An algebraic element generates a finite field extension inside D. -/
def SimpleAdjoinFiniteField : Prop :=
  ∀ (K : Type u) (D : Type v) [Field K] [DivisionRing D] [Algebra K D]
    (x : D), IsAlgebraic K x →
    IsField (Algebra.adjoin K {x}) ∧
    Module.Finite K (Algebra.adjoin K {x}) ∧
    Function.Injective (algebraMap K (Algebra.adjoin K {x}))

/-- A division ring algebraic over an algebraically closed central field
consists exactly of the scalars, with the specified embedding. -/
def ScalarMapBijective : Prop :=
  ∀ (K : Type u) (D : Type v) [Field K] [DivisionRing D] [Algebra K D]
    [IsAlgClosed K], (∀ x : D, IsAlgebraic K x) →
    Function.Bijective (algebraMap K D)

end Specs.D07.Ch23.AlgebraicallyClosedCenter
