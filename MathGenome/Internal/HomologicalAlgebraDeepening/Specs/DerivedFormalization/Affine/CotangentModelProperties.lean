import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.KahlerDifferentials
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.SemifreeAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.KProjective

open CategoryTheory

universe u v

namespace Specs.DerivedFormalization.Affine.CotangentModelProperties

open _root_.DerivedFormalization.Affine
open _root_.DerivedFormalization.Affine.Kahler (DifferentialModel)
open Tensor (ModuleTensor regular)
open Specs.DerivedFormalization.DG.KProjective (isKProjective)

set_option linter.checkUnivs false in
def CotangentModelType :=
  ∀ {k : Type u} [Field k] [CharZero k], ModuleTensor.{u,v} k →
    ∀ {A P B : NonpositiveCDGA.{u,v} k} {f : A ⟶ P},
    (P ⟶ B) → DifferentialModel (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra) → B.Module

/-- The scalar extension of relative differentials along the augmentation. -/
abbrev cotangentModel {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k)
    {A P B : NonpositiveCDGA.{u,v} k} {f : A ⟶ P} (p : P ⟶ B)
    (O : DifferentialModel (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra)) : B.Module :=
  (T.baseChange (p : P.toCommDGAlgebra ⟶ B.toCommDGAlgebra)).obj O.module

/-- For every semifree surjective resolution over the given base, its
cotangent model is K-projective and K-flat in the original module category. -/
def ModelProperties : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (T : ModuleTensor.{u,v} k)
    {A P B : NonpositiveCDGA.{u,v} k} (b : A ⟶ B) (f : A ⟶ P) (p : P ⟶ B)
    (O : DifferentialModel (f : A.toCommDGAlgebra ⟶ P.toCommDGAlgebra)),
    f ≫ p = b →
    Semifree.IsSemifree A f →
    NonpositiveCDGA.DegreewiseSurjective p →
    NonpositiveCDGA.IsQuasiIso p →
    T.Formulas (p : P.toCommDGAlgebra ⟶ B.toCommDGAlgebra) (regular B.toCommDGAlgebra) →
    (∀ N : B.Module, T.Formulas (𝟙 B.toCommDGAlgebra) N) →
    isKProjective (cotangentModel T p O) ∧ T.KFlat (cotangentModel T p O)

end Specs.DerivedFormalization.Affine.CotangentModelProperties
