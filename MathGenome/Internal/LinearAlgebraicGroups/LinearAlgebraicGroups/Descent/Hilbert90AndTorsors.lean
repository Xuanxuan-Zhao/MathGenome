import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.Hilbert90AndTorsors
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.MatrixHilbert90
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.SmoothTorsors

namespace LinearAlgebraicGroups.Descent

universe u

/-- Matrix Hilbert 90 and the classification of smooth affine group torsors. -/
theorem hilbert90AndTorsors : Specs.Hilbert90AndTorsors.Statement.{u} :=
  ⟨MatrixHilbert90.continuousGLH1, MatrixHilbert90.continuousSLH1,
    MatrixHilbert90.finiteGLH1, MatrixHilbert90.finiteSLH1,
    SmoothTorsors.classification, Fppf.rationalPointCriterion⟩

end LinearAlgebraicGroups.Descent
