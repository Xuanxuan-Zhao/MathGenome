import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianCompactRealConnectedness

open LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (LocalPoints)
open IntegralModels (MatrixRealization)
open NontrialitarianSpinModels
  (EquivariantSpinTrivialization DescendedQuadraticPair SpinModel IsOrthogonal)
open Topology

/-- The full group of points at a compact real factor is connected in the
topology of the given closed matrix realization. -/
def CompactRealConnectedness : Prop :=
  ∀ {k L I : Type u} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]
    [IsGalois k L] [Fintype I] [DecidableEq I] [Nonempty I]
    (hK : NumberField k) (G : AffineAlgebraicGroup k),
    AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G →
    4 ≤ Fintype.card I →
    ∀ (C : EquivariantSpinTrivialization (K := L) (I := I) G)
      (Q : DescendedQuadraticPair C.action), SpinModel G Q →
    IsOrthogonal
      (SymplecticInvolutionModels.DivisionForms.toDivisionInvolution Q.involution) →
    ∀ (D : GlobalFieldData.{u, u} k), D = .number hK →
    ∀ (i : MatrixRealization G) (w : D.InfinitePlace)
      (R : D.Completion (.inr w) ≃+* ℝ), IsHomeomorph R →
    CompactSpace (LocalPoints D i (.inr w)) → ConnectedSpace (LocalPoints D i (.inr w))

end LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianCompactRealConnectedness
