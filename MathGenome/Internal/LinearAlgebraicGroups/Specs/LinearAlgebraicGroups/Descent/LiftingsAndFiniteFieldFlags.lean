import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.ExactLifting
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.FiniteFieldFlags

namespace LinearAlgebraicGroups.Specs.LiftingsAndFiniteFieldFlags

open ExactLifting (GaloisExactness FiniteFieldLifting NonsquareCounterexample)
open FiniteFieldFlags (RationalBorelExists GeometricallyMaximalTorusExists ReductiveQuasiSplit)

/-- Rational lifting and its obstruction for smooth homogeneous quotients,
including the odd-order nonsquare example, and the finite-field existence of
rational Borels and geometrically maximal tori and quasi-splitness. -/
def RationalLiftingsAndFiniteFieldFlags.{u} : Prop :=
  GaloisExactness.{u} ∧
    FiniteFieldLifting.{u} ∧
    NonsquareCounterexample.{u} ∧
    RationalBorelExists.{u} ∧
    GeometricallyMaximalTorusExists.{u} ∧
    ReductiveQuasiSplit.{u}

end LinearAlgebraicGroups.Specs.LiftingsAndFiniteFieldFlags
