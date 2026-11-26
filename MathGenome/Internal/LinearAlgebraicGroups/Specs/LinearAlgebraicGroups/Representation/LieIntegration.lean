import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SplitLieIntegration
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FullyFaithfulDifferentiation
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FrobeniusDifferential

universe u

namespace LinearAlgebraicGroups.Specs.LieIntegration

open GeometricRadicals (IsSemisimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open SplitLieIntegration (Integrates)

/-- Every finite-dimensional Lie module of a geometrically simply connected
semisimple group in characteristic zero comes from a rational representation
of that group over its ground field. -/
def EssentialSurjectivity : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (G : AffineAlgebraicGroup k),
    IsSemisimple G → GeometricallySimplyConnected G →
      ∀ s : IdentityLieStructure G.val,
        letI := s.lieRing
        letI := s.lieAlgebra
        ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
          [LieRingModule (Lie k G.val) V] [LieModule k (Lie k G.val) V],
          Integrates G V

/-- Differentiation, its essential image for split simple modules,
and the relative Frobenius example. -/
def Statement : Prop :=
  FullyFaithfulDifferentiationOfPresentation.{u} ∧
  EssentialSurjectivity.{u} ∧
  SplitLieIntegration.SplitIntegration.{u} ∧
  FrobeniusDifferential.RelativeFrobeniusDifferential.{u} ∧
  FrobeniusDifferential.SplitSL2Example.{u}

end LinearAlgebraicGroups.Specs.LieIntegration
