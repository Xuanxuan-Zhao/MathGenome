import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.TorBalance
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.Horseshoe
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! HA-R14, source lines 2181–2203, with conventions at 117–135,
967–977 and 1767–1775. Right modules are modules over the opposite ring;
the target is abelian groups, represented as integer modules. The classical
Tor objects and maps below are the original noncommutative balanced tensor
quotients of P103. No replacement definition of Tor is introduced here.

The full comparison requires one coherent family on *every* ordinary
projective resolution. Its right-module naturality includes independence
of resolutions (take the base map to be the identity). Coefficient naturality
uses the actual derived transformation of HA-R07. Degree zero is identified
by H⁰ of the HA-R07 counit on the stalk and by the ordinary augmentation.
The connecting condition is the positive classical lift-and-differentiate
formula for each horseshoe, with indices n+1,n corresponding to cochain
degrees −(n+1),−n.
-/
noncomputable section
set_option linter.checkUnivs false
set_option linter.unusedVariables false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.TorBalance
universe u v w x y

namespace Specs.AdvancedHomologicalAlgebra.DerivedTorComparison

section FixedRing
variable (R : Type u) [Ring R]

/-- Sizes include free resolutions, without restricting the size of R or A. -/
abbrev RightModules := ModuleCat.{max u v} Rᵐᵒᵖ
abbrev Groups := ModuleCat.{max u v w} ℤ
abbrev Coefficients := ModuleCat.{w} R

def tensor (M : Coefficients.{u,w} R) : RightModules.{u,v} R ⥤ Groups.{u,v,w} :=
  tensorFunctor M

instance tensor_additive (M : Coefficients.{u,w} R) :
    (tensor.{u,v,w} R M).Additive :=
  inferInstanceAs (tensorFunctor M).Additive

variable [HasDerivedCategory.{x} (RightModules.{u,v} R)]
    [HasDerivedCategory.{y} (Groups.{u,v,w})]
    [(minus (RightModules.{u,v} R)).IsTriangulated]
    [(minus (Groups.{u,v,w})).IsTriangulated]

/-- Total left derived data for tensoring with each coefficient module. -/
abbrev DerivedFamily := ∀ M : Coefficients.{u,w} R,
  ExactLeftData.{_, _, _, _, x, y} (tensor.{u,v,w} R M)

/-- H⁰ of the actual HA-R07 counit on the stalk, followed by the standard
identification of the degree-zero homology of the tensor stalk. -/
def counitOnTensorStalk (M : Coefficients.{u,w} R)
    (D : ExactLeftData.{_, _, _, _, x, y} (tensor.{u,v,w} R M))
    (A : RightModules.{u,v} R) :
    (leftValue (tensor.{u,v,w} R M) D 0).obj A ⟶ (tensor.{u,v,w} R M).obj A := by
  let C := RightModules.{u,v} R
  let B := Groups.{u,v,w}
  let F := tensor.{u,v,w} R M
  let K := (CochainComplex.singleFunctor C 0).obj A
  let S := minusStalkValue A
  let FK := (F.mapHomologicalComplex (.up ℤ)).obj K
  let quotient := HomotopyCategory.quotient B (.up ℤ)
  let sourceStalk : (minusSingle C).obj A ≅ (QMinus C).obj S :=
    DerivedCategory.Minus.ι.preimageIso ((DerivedCategory.singleFunctorIsoCompQh C 0).app A)
  let tensorModel : ((minusUValue F).obj S).obj ≅ (DerivedCategory.Qh (C := B)).obj
      (quotient.obj FK) :=
    DerivedCategory.Qh.mapIso
      ((F.mapHomotopyCategory (.up ℤ)).mapIso
        ((HomotopyCategory.singleFunctorPostcompQuotientIso C 0).app A) ≪≫
        (F.mapHomotopyCategoryFactors (.up ℤ)).app K)
  let tensorStalk : ((minusUValue F).obj S).obj ≅
      (DerivedCategory.singleFunctor B 0).obj (F.obj A) :=
    tensorModel ≪≫ (DerivedCategory.quotientCompQhIso B).symm.app FK ≪≫
      DerivedCategory.Q.mapIso ((F.mapCochainComplexSingleFunctor 0).app A)
  exact (DerivedCategory.homologyFunctor B 0).map
    (DerivedCategory.Minus.ι.map (D.functor.map sourceStalk.hom ≫ D.counit.app S) ≫
      tensorStalk.hom) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app (F.obj A)

/-- A partial milestone: computation on every ordinary projective resolution.
Naturality, normalization and boundary compatibility are additionally required
by `FullStatement`, not assumed as inputs to this proposition. -/
def ValuesStatement : Prop :=
  ∀ (M : Coefficients.{u,w} R) (D : ExactLeftData.{_, _, _, _, x, y} (tensor.{u,v,w} R M))
    (A : RightModules.{u,v} R) (P : LeftResolution Rᵐᵒᵖ A), P.IsProjective →
    ∀ n : ℕ, Nonempty ((leftValue (tensor.{u,v,w} R M) D n).obj A ≅
      ModuleCat.of ℤ (TorWith P M n))

/-- One choice of comparison works in both variables, in every degree and
on every ordinary resolution. Each field is a conclusion to be proved. -/
structure Comparison (T : CanonicalTheory.{u,max u v,w} R)
    (D : DerivedFamily.{u,v,w,x,y} R) where
  iso : ∀ (M : Coefficients.{u,w} R) (A : RightModules.{u,v} R)
    (P : ProjectiveChoice Rᵐᵒᵖ A) (n : ℕ),
    (leftValue (tensor.{u,v,w} R M) (D M) n).obj A ≅
      ModuleCat.of ℤ (TorWith P.val M n)
  right_naturality : ∀ (M : Coefficients.{u,w} R) (n : ℕ)
    {A B : RightModules.{u,v} R} (P : ProjectiveChoice Rᵐᵒᵖ A)
    (Q : ProjectiveChoice Rᵐᵒᵖ B) (f : A ⟶ B),
    (leftValue (tensor.{u,v,w} R M) (D M) n).map f ≫ (iso M B Q n).hom =
      (iso M A P n).hom ≫ ModuleCat.ofHom ((T.torMaps n).map P Q f (𝟙 M))
  coefficient_naturality : ∀ {M N : Coefficients.{u,w} R} (g : M ⟶ N)
    (α : (D M).functor ⟶ (D N).functor),
    whiskerLeft (QMinus (RightModules.{u,v} R)) α ≫ (D N).counit =
      (D M).counit ≫ minusUMapValue (tensor.{u,v,w} R M) (tensor.{u,v,w} R N)
        (AdvancedHomologicalAlgebra.TorBalance.tensorCoefficientMap g.hom) →
    ∀ (A : RightModules.{u,v} R) (P : ProjectiveChoice Rᵐᵒᵖ A) (n : ℕ),
      (DerivedCategory.homologyFunctor (Groups.{u,v,w}) (-(n : ℤ))).map
        (DerivedCategory.Minus.ι.map (α.app ((minusSingle (RightModules.{u,v} R)).obj A))) ≫
          (iso N A P n).hom =
        (iso M A P n).hom ≫ ModuleCat.ofHom ((T.torMaps n).map P P (𝟙 A) g)
  zero : ∀ M : Coefficients.{u,w} R,
    leftValue (tensor.{u,v,w} R M) (D M) 0 ≅ tensor.{u,v,w} R M
  zero_counit : ∀ (M : Coefficients.{u,w} R) (A : RightModules.{u,v} R),
    (zero M).hom.app A = counitOnTensorStalk R M (D M) A
  zero_formula : ∀ (M : Coefficients.{u,w} R) (A : RightModules.{u,v} R)
    (P : ProjectiveChoice Rᵐᵒᵖ A) (z : cycles (tensorComplex P.val.complex M) 0),
    (zero M).hom.app A ((iso M A P 0).inv (homologyClass _ 0 z)) =
      tensorMap P.val.ε LinearMap.id z.val
  balance : ∀ (M : Coefficients.{u,w} R) (A : RightModules.{u,v} R)
    (P : ProjectiveChoice Rᵐᵒᵖ A) (Q : LeftResolution R M), Q.IsProjective →
    ∃ (a : Augmentations P.val Q) (hL : QuasiIsomorphism a.left)
      (hR : QuasiIsomorphism a.right), ∀ n : ℕ,
      ∃ e : (leftValue (tensor.{u,v,w} R M) (D M) n).obj A ≃ₗ[ℤ]
        Homology (leftOrdinaryTensorComplex A Q.complex) n,
        ∀ z, e z = balanceEquiv a hL hR n ((iso M A P n).hom z)
  connecting : ∀ (M : Coefficients.{u,w} R) (S : ShortComplex (RightModules.{u,v} R))
    (hS : S.ShortExact) (P : ProjectiveChoice Rᵐᵒᵖ S.X₁)
    (Q : ProjectiveChoice Rᵐᵒᵖ S.X₃),
    Nonempty (P103.Specs.Ch10.Horseshoe.ProjectiveData S.f.hom S.g.hom P.val Q.val) ∧
    ∀ (H : P103.Specs.Ch10.Horseshoe.ProjectiveData S.f.hom S.g.hom P.val Q.val)
      (n : ℕ),
    P103.Specs.Ch10.HomologySequence.Connecting
      (tensorFirstMap H.inclusion M) (tensorFirstMap H.projection M) (n + 1) n
      ((iso M S.X₁ P n).hom.hom.comp
        ((leftBoundary (tensor.{u,v,w} R M) (D M) hS n).hom.comp
          (iso M S.X₃ Q (n + 1)).inv.hom))

/-- The full HA-R14 obligation. For each choice of the established derived
functor data and classical theory, the comparison uses that data's counit. -/
def FullStatement : Prop :=
  ∀ (T : CanonicalTheory.{u,max u v,w} R) (D : DerivedFamily.{u,v,w,x,y} R),
    Nonempty (Comparison R T D)

end FixedRing

/-- Full quantification for the verified object-computation milestone. -/
def ValuesType : Prop :=
  ∀ (R : Type u) [Ring R]
    [HasDerivedCategory.{x} (RightModules.{u,v} R)]
    [HasDerivedCategory.{y} (Groups.{u,v,w})]
    (hA : (minus (RightModules.{u,v} R)).IsTriangulated)
    (hB : (minus (Groups.{u,v,w})).IsTriangulated),
    letI := hA; letI := hB
    ValuesStatement.{u,v,w,x,y} R

/-- Full quantification for the eventual HA-R14 assembly. -/
def FullType : Prop :=
  ∀ (R : Type u) [Ring R]
    [HasDerivedCategory.{x} (RightModules.{u,v} R)]
    [HasDerivedCategory.{y} (Groups.{u,v,w})]
    (hA : (minus (RightModules.{u,v} R)).IsTriangulated)
    (hB : (minus (Groups.{u,v,w})).IsTriangulated),
    letI := hA; letI := hB
    FullStatement.{u,v,w,x,y} R

end Specs.AdvancedHomologicalAlgebra.DerivedTorComparison
