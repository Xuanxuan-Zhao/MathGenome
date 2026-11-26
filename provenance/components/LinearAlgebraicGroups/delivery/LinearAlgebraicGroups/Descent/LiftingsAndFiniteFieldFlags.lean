import Specs.LinearAlgebraicGroups.Descent.LiftingsAndFiniteFieldFlags
import LinearAlgebraicGroups.Descent.ExactLifting

import LinearAlgebraicGroups.Descent.FiniteFieldFlags
namespace LinearAlgebraicGroups.Descent.LiftingsAndFiniteFieldFlags

open Specs.FiniteFieldFlags (GeometricallyMaximalTorusExists RationalBorelExists ReductiveQuasiSplit)
open Specs.LiftingsAndFiniteFieldFlags (RationalLiftingsAndFiniteFieldFlags)

/-- Assemble the lifting results with the three finite-field flag premises. -/
theorem rationalLiftingsAndFiniteFieldFlags_conditional.{u}
    (maximalTorus : GeometricallyMaximalTorusExists.{u})
    (borel : RationalBorelExists.{u})
    (quasiSplit : ReductiveQuasiSplit.{u}) :
    RationalLiftingsAndFiniteFieldFlags.{u} :=
  ⟨ExactLifting.galoisExactness, ExactLifting.finiteFieldLifting,
    ExactLifting.nonsquareCounterexample, borel, maximalTorus, quasiSplit⟩

end LinearAlgebraicGroups.Descent.LiftingsAndFiniteFieldFlags

universe v8_closure_bfbe11f65b8e113a_u0
theorem _root_.«LinearAlgebraicGroups».«Descent».«LiftingsAndFiniteFieldFlags».«rationalLiftingsAndFiniteFieldFlags» : _root_.«LinearAlgebraicGroups».«Specs».«LiftingsAndFiniteFieldFlags».«RationalLiftingsAndFiniteFieldFlags».{v8_closure_bfbe11f65b8e113a_u0} :=
  @_root_.«LinearAlgebraicGroups».«Descent».«LiftingsAndFiniteFieldFlags».«rationalLiftingsAndFiniteFieldFlags_conditional».{v8_closure_bfbe11f65b8e113a_u0} (@_root_.«LinearAlgebraicGroups».«Descent».«FiniteFieldFlags».«geometricallyMaximalTorusExists».{v8_closure_bfbe11f65b8e113a_u0}) (@_root_.«LinearAlgebraicGroups».«Descent».«FiniteFieldFlags».«rationalBorelExists».{v8_closure_bfbe11f65b8e113a_u0}) (@_root_.«LinearAlgebraicGroups».«Descent».«FiniteFieldFlags».«reductiveQuasiSplit».{v8_closure_bfbe11f65b8e113a_u0})
