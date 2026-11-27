import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.OrdinaryComplex

open CategoryTheory

universe u v t

namespace Specs.DerivedFormalization.Affine.OrdinaryStalkComparison

open _root_.DerivedFormalization
open _root_.DerivedFormalization.Affine
open CotangentComplex (liftCDGA)
open Cochains (compValue)
open DG.HomComplex (gradedHom HomotopyEquation)

noncomputable section

/-- The coefficient enlargement used for the cotangent model, applied to
the given ordinary algebra in degree zero. -/
abbrev transported (k : Type u) [Field k] [CharZero k]
    (R : Type v) [CommRing R] [Algebra k R] : NonpositiveCDGA.{u,max v t} k :=
  liftCDGA.{u,v,t} (NonpositiveCDGA.ordinary (CommAlgCat.of k R))

variable {k : Type u} [Field k] [CharZero k]
variable {R : Type v} [CommRing R] [Algebra k R]

/-- Restriction on the original ring's cochain complexes at the common bound. -/
abbrev restrictComplex (k : Type u) [Field k]
    (R : Type v) [CommRing R] [Algebra k R] :
    compValue.{max v t} R ⥤ ModuleCochain.{u,max v t} k :=
  (ModuleCat.restrictScalars.{max v t} (algebraMap k R)).mapHomologicalComplex (.up ℤ)

local instance transportedCommRing :
    CommRing (transported.{u,v,t} k R).toCommDGAlgebra.DegreeZero :=
  CommDGAlgebra.instCommRingDegreeZero _

local instance transportedAlgebra :
    Algebra k (transported.{u,v,t} k R).toCommDGAlgebra.DegreeZero :=
  CommDGAlgebra.instAlgebraDegreeZero _

set_option autoImplicit false in
/-- The strict comparison and its action on the original scalars, maps and
underlying complexes. Its tests use all objects at the common bound. -/
structure Comparison (k : Type u) [Field k] [CharZero k]
    (R : Type v) [CommRing R] [Algebra k R] where
  scalar : R ≃ₐ[k] (transported.{u,v,t} k R).toCommDGAlgebra.DegreeZero
  scalar_apply (r : R) : scalar r = ULift.up r
  strict : compValue.{max v t} R ≌ (transported.{u,v,t} k R).Module
  additive {X Y : compValue.{max v t} R} (f g : X ⟶ Y) :
    (strict.functor.map (f + g)).app () =
      (strict.functor.map f).app () + (strict.functor.map g).app ()
  terms : restrictComplex.{u,v,t} k R ≅ strict.functor ⋙ RightDGModuleModel.eval ()
  action (X : compValue.{max v t} R) (i : ℤ) (r : R) (x : X.X i) :
    Tensor.act (strict.functor.obj X) i 0 i (add_zero i) ((terms.hom.app X).f i x) (scalar r) =
      (terms.hom.app X).f i (r • x)
  homotopy {X Y : compValue.{max v t} R} (f g : X ⟶ Y) :
    Nonempty (Homotopy f g) ↔
      ∃ z : gradedHom (strict.functor.obj X) (strict.functor.obj Y) (-1),
        HomotopyEquation (strict.functor.map f) (strict.functor.map g) z
  quasiIso {X Y : compValue.{max v t} R} (f : X ⟶ Y) :
    QuasiIso f ↔ DG.Module.quasiIsomorphism (strict.functor.map f)
  projective (X : compValue.{max v t} R) :
    CochainModels.isKProjectiveValue X ↔ DG.KProjective.isKProjective (strict.functor.obj X)

def ComparisonExists : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (R : Type v) [CommRing R] [Algebra k R],
    Nonempty (Comparison.{u,v,t} k R)

end

end Specs.DerivedFormalization.Affine.OrdinaryStalkComparison
