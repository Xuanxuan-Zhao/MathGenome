import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.MatrixHilbert90
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.SmoothTorsors

namespace LinearAlgebraicGroups.Specs.Hilbert90AndTorsors

open LinearAlgebraicGroups.Descent.MatrixHilbert90.Specification

universe u

/-- Result F04. The pointed first cohomology sets for the general and special
linear groups are singletons over the base field and at finite Galois
levels. For a smooth affine algebraic group, the cocycle of a point over the
separable closure classifies its right fppf torsors. A right torsor is trivial
if and only if it has a rational point. -/
def Statement : Prop :=
  ContinuousGLH1.{u} ∧ ContinuousSLH1.{u} ∧
    FiniteGLH1.{u} ∧ FiniteSLH1.{u} ∧
    SmoothTorsors.Classification.{u} ∧ Fppf.RationalPointCriterion.{u}

end LinearAlgebraicGroups.Specs.Hilbert90AndTorsors
