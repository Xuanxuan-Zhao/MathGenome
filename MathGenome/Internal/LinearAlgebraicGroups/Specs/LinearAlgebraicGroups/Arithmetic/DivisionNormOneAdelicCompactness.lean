import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels

universe u v

namespace LinearAlgebraicGroups.Specs.DivisionNormOneAdelicCompactness

open Arithmetic (GlobalFieldData)
open Arithmetic.AdelicGroups (Adeles)
open Arithmetic.ArithmeticLatticeProjection (diagonalSubgroup)
open IntegralModels (MatrixRealization)
open OuterTypeAModels (RepresentsNormOne)
open _root_.Specs.RM03.CSA (isCentralSimple)

/-- The full adelic quotient of the original reduced-norm-one group of a central
division algebra by its rational diagonal is compact in every closed matrix
realization, over a number field or a global function field. -/
def CompactQuotient : Prop :=
  ∀ {K A : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    [DivisionRing A] [Algebra K A] (hA : isCentralSimple K A),
    ∀ {I : Type u} [Fintype I] (b : Module.Basis I K A) (G : AffineAlgebraicGroup K),
      RepresentsNormOne hA b G →
      ∀ i : MatrixRealization G, CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i)

end LinearAlgebraicGroups.Specs.DivisionNormOneAdelicCompactness
