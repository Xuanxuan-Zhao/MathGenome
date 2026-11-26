import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups

universe u v

namespace LinearAlgebraicGroups.Specs.DiscreteDiagonals

open Arithmetic Arithmetic.AdelicGroups
open LinearAlgebraicGroups.Specs.IntegralModels (MatrixRealization RationalPoints)

/-- The constant field consists of the elements algebraic over the given finite base field. -/
def functionFieldConstants : Prop :=
  ∀ {F : Type v} {K : Type u} [Field F] [Field K] [Finite F] [Algebra F K]
    (_t : SeparatingParameter F K) (x : K),
    (∀ w : FunctionPlace K, x ∈ w.1) ↔ IsAlgebraic F x

/-- The additive diagonal in the full scalar adele ring. -/
def scalarDiagonalImage {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K) :
    Set D.AdeleRing :=
  {a | ∃ x : K, ∀ w : D.Place, D.coordinate w a = D.embedding w x}

/-- The rational diagonal with every place retained. -/
def groupDiagonalImage {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) :
    Set (Adeles D i ∅) :=
  {a | ∃ g : RationalPoints G, ∀ w : Outside D ∅, a w = localPoint D i w.1 g}

def scalarClosedDiscrete : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K),
    IsClosed (scalarDiagonalImage D) ∧ IsDiscrete (scalarDiagonalImage D)

def groupClosedDiscrete : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G),
    IsClosed (groupDiagonalImage D i) ∧ IsDiscrete (groupDiagonalImage D i)

end LinearAlgebraicGroups.Specs.DiscreteDiagonals
