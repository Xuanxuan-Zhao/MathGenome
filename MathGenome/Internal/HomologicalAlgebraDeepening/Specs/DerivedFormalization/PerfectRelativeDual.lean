import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedCoinduction
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedScalarExtension
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.PerfectComplex

/-! The tensor-evaluation comparison for a perfect algebra. -/

namespace Specs.DerivedFormalization.PerfectRelativeDual

open CategoryTheory MonoidalCategory
open Cochains (compValue derivedValue qValue stalkValue)
open CochainModels (isKInjectiveValue)
open CochainTensor (tensor map pure isKFlat)
open CochainTensorTransport (AdequateModel representedUnit)
open CoinductionComplex (coinduceValue evaluationValue restrictedRegular)
open DerivedCoinduction (Coinduction comparison)
open DerivedRestriction (restrictScalarsComplexValue)
open ScalarExtensionTransport (ModelStability extension extendPure cochainAdjunction)
open DerivedScalarExtension (Extension)
open PerfectComplex (isPerfectValue)

universe u w v

set_option linter.checkUnivs false

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
variable {A' B' : Type (max u w v)} [CommRing A'] [CommRing B']
variable (e : A ≃+* A') (d : B ≃+* B')

/-- The regular B-module in degree zero after restriction to A. -/
abbrev algebraStalk : compValue.{max u w v} A := (stalkValue A).obj (restrictedRegular.{max u v} f)

/-- The relative dual, with the B-action of derived coinduction. -/
abbrev relativeDual (G : Coinduction.{max u v} f) : derivedValue.{max u w v} B :=
  G.functor.obj ((qValue.{max u w v} A).obj (representedUnit e))

def RelativeDualType :=
  ∀ {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    {A' : Type (max u w v)} [CommRing A'] (_ : A ≃+* A'),
    Coinduction.{max u v} f → derivedValue.{max u w v} B

/-- The functor sending Y to the derived B-tensor of the relative dual and L_f(Y). -/
abbrev source {MB : AdequateModel d} (T : DerivedTensor.Model MB) (L : Extension d f)
    (G : Coinduction.{max u v} f) : derivedValue.{max u w v} A ⥤ derivedValue.{max u w v} B :=
  ((Functor.const (derivedValue.{max u w v} A)).obj (relativeDual f e G)).prod' L.derived ⋙
    T.toDescent.tensorFunctor

/-- The cochain adjunction underlying the U14 coinduction model. -/
def coinductionAdjunction :
    restrictScalarsComplexValue.{max u w v} f ⊣ coinduceValue.{max u v} f :=
  let adj := ModuleCat.restrictCoextendScalarsAdj.{max u v, u, w} f
  letI := adj.right_adjoint_additive
  cochainAdjunction adj

/-- Tensor evaluation on the coinduced B-complexes. The transpose uses
balanced tensor cancellation followed by evaluation at one. -/
def chainEvaluation (S : ModelStability d f) (I P : compValue.{max u w v} A) :
    tensor ((coinduceValue.{max u v} f).obj I) ((extension d f).obj P) ⟶
      (coinduceValue.{max u v} f).obj (tensor I P) :=
  (coinductionAdjunction.{u,w,v} f).homEquiv _ _
    ((S.cancel ((coinduceValue.{max u v} f).obj I) P).hom ≫ map (evaluationValue.{max u v} f I) (𝟙 P))

/-- On homogeneous generators, tensor evaluation sends φ ⊗ (s ⊗ p) to b ↦ φ(sb) ⊗ p. -/
def ChainEvaluationFormula : Prop :=
  ∀ {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    {B' : Type (max u w v)} [CommRing B'] (d : B ≃+* B')
    (S : ModelStability d f) (I P : compValue.{max u w v} A)
    {i j n : ℤ} (h : i + j = n) (z : ((coinduceValue.{max u v} f).obj I).X i) (s b : B) (p : P.X j),
    ModuleCat.CoextendScalars.equiv f ((tensor I P).X n)
        ((chainEvaluation.{u,w,v} f d S I P).f n
          (pure ((coinduceValue.{max u v} f).obj I) ((extension d f).obj P) h z
            (extendPure d f P j s p))) b =
      pure I P h (ModuleCat.CoextendScalars.equiv f (I.X i) z (s * b)) p

/-- The B-linear comparison used in the derived category, after a
K-injective replacement of the target of tensor evaluation. -/
abbrev chainComparison (S : ModelStability d f) (I P J : compValue.{max u w v} A) (j : tensor I P ⟶ J) :
    tensor ((coinduceValue.{max u v} f).obj I) ((extension d f).obj P) ⟶ (coinduceValue.{max u v} f).obj J :=
  chainEvaluation.{u,w,v} f d S I P ≫ (coinduceValue.{max u v} f).map j

/-- With a perfect regular module, the chain comparison is a quasi-isomorphism
after restriction to A. -/
def ChainComparisonQuasiIso : Prop :=
  ∀ {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    {A' B' : Type (max u w v)} [CommRing A'] [CommRing B']
    (e : A ≃+* A') (d : B ≃+* B') (S : ModelStability d f),
    isPerfectValue ((qValue.{max u w v} A).obj (algebraStalk.{u,w,v} f)) →
    ∀ (I P J : compValue.{max u w v} A) (a : representedUnit e ⟶ I) (j : tensor I P ⟶ J),
      QuasiIso a → isKInjectiveValue I → isKFlat P → QuasiIso j → isKInjectiveValue J →
      QuasiIso ((restrictScalarsComplexValue.{max u w v} f).map (chainComparison.{u,w,v} f d S I P J j))

/-- Identify the source at the image of a K-flat model of Y. -/
def sourceModel {MB : AdequateModel d} (T : DerivedTensor.Model MB) (L : Extension d f)
    (G : Coinduction.{max u v} f) {I : compValue.{max u w v} A} (a : representedUnit e ⟶ I)
    [QuasiIso a] (hI : isKInjectiveValue I) (P : compValue.{max u w v} A) (hP : isKFlat P) :
    (source f e d T L G).obj ((qValue.{max u w v} A).obj P) ≅
      (qValue.{max u w v} B).obj (tensor ((coinduceValue.{max u v} f).obj I) ((extension d f).obj P)) :=
  letI := T.toDescent.monoidal
  letI := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u w v} A) a).2
    (inferInstance : QuasiIso a)
  tensorIso (G.modelIso f I (asIso ((qValue.{max u w v} A).map a)) hI) (L.toLift.model P hP) ≪≫
    T.compare ((coinduceValue.{max u v} f).obj I) ((extension d f).obj P) (Or.inr (L.preservesFlat P hP))

/-- The map from P to the replacement of I ⊗ P, induced by A[0] → I
and the inverse of the left unit isomorphism. -/
def targetAugmentation (MA : AdequateModel e) {I : compValue.{max u w v} A} (a : representedUnit e ⟶ I)
    {P J : compValue.{max u w v} A} (j : tensor I P ⟶ J) : P ⟶ J :=
  letI := MA.chainMonoidal
  let unitor := MA.tensorModel (representedUnit e) P ≪≫
    tensorIso MA.unitModel (Iso.refl P) ≪≫ λ_ P
  unitor.inv ≫ map a (𝟙 P) ≫ j

/-- The relative duality isomorphism is natural on all of D(A).
Its components are the localized tensor-evaluation maps on the
K-flat and K-injective presentations. -/
def RelativeDuality : Prop :=
  ∀ {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    {A' B' : Type (max u w v)} [CommRing A'] [CommRing B']
    {e : A ≃+* A'} {d : B ≃+* B'} (MA : AdequateModel e) {MB : AdequateModel d}
    (T : DerivedTensor.Model MB) (L : Extension d f) (G : Coinduction.{max u v} f)
    (S : ModelStability d f),
    isPerfectValue ((qValue.{max u w v} A).obj (algebraStalk.{u,w,v} f)) →
    ∃ η : source f e d T L G ⟶ G.functor, IsIso η ∧
      ∀ (I P J : compValue.{max u w v} A) (a : representedUnit e ⟶ I) [QuasiIso a]
        (hI : isKInjectiveValue I) (hP : isKFlat P) (j : tensor I P ⟶ J) [QuasiIso j]
        (_ : isKInjectiveValue J),
        QuasiIso (targetAugmentation.{u,w,v} e MA a j) ∧
        η.app ((qValue.{max u w v} A).obj P) ≫
            G.functor.map ((qValue.{max u w v} A).map (targetAugmentation.{u,w,v} e MA a j)) =
          (sourceModel f e d T L G a hI P hP).hom ≫
            (qValue.{max u w v} B).map (chainComparison.{u,w,v} f d S I P J j) ≫
            comparison.{max u v} f G.adjunction J


open CochainCoefficientLift (lift liftD liftDFactors)

/-- The same comparison on an original complex of independently sized modules.
The two augmentations are taken on the same-ring coefficient lift of that
complex. -/
def RelativeDualityOnOriginal : Prop :=
  ∀ {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
    {A' B' : Type (max u w v)} [CommRing A'] [CommRing B']
    {e : A ≃+* A'} {d : B ≃+* B'} (MA : AdequateModel e) {MB : AdequateModel d}
    (T : DerivedTensor.Model MB) (L : Extension d f) (G : Coinduction.{max u v} f)
    (S : ModelStability d f),
    let qA := qValue.{max u w v} A
    let qB := qValue.{max u w v} B
    let F := source f e d T L G
    isPerfectValue (qA.obj (algebraStalk.{u,w,v} f)) →
    ∃ η : F ⟶ G.functor, IsIso η ∧
      ∀ (X : compValue.{v} A) (I : compValue.{max u w v} A)
        (a : representedUnit e ⟶ I) [QuasiIso a] (hI : isKInjectiveValue I),
        let X' := (lift.{max u w, v} A).obj X
        let Y := (liftD.{max u w, v} A).obj ((qValue.{v} A).obj X)
        ∃ (P J : compValue.{max u w v} A) (p : P ⟶ X') (i : X' ⟶ J)
          (j : tensor I P ⟶ J) (_ : QuasiIso p) (_ : QuasiIso i)
          (hP : isKFlat P) (hJ : isKInjectiveValue J),
          QuasiIso j ∧
          qA.map (targetAugmentation.{u,w,v} e MA a j) = qA.map (p ≫ i) ∧
          letI := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u w v} A) p).2
            (inferInstance : QuasiIso p)
          letI := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u w v} A) i).2
            (inferInstance : QuasiIso i)
          let α := (liftDFactors.{max u w, v} A).app X ≪≫ (asIso (qA.map p)).symm
          let β := (liftDFactors.{max u w, v} A).app X ≪≫ asIso (qA.map i)
          η.app Y ≫ (G.modelIso f J β hJ).hom =
            F.map α.hom ≫ (sourceModel f e d T L G a hI P hP).hom ≫
              qB.map (chainComparison.{u,w,v} f d S I P J j)

end

end Specs.DerivedFormalization.PerfectRelativeDual
