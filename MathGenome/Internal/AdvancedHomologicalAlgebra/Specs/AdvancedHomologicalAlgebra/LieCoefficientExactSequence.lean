import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ChevalleyEilenbergExt
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtExactSequences
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Ulift

/-! HA-A06/A07 and the coefficient sequence used in LA-C04.
All coefficients are left U-modules. Their k-action is restriction of scalars.
The models below carry the actual displayed all-degree CE formula and the
specified evaluation isomorphism, not an abstract replacement complex.
Existence of these models is a separate obligation. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch10.HomologySequence P103.Specs.Ch11.ExtTorDefinitions
namespace AdvancedHomologicalAlgebra.CE.Coefficients
open scoped TensorProduct
universe u v w
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

instance coefficientModule (M : ModuleCat.{w} (U k g)) : Module k M :=
  Module.restrictScalars k (U k g) M
instance coefficientTower (M : ModuleCat.{w} (U k g)) : IsScalarTower k (U k g) M :=
  IsScalarTower.restrictScalars k (U k g) M

variable (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)
/-- A CE model with its explicit differential and prescribed evaluation. -/
structure Model (M : ModuleCat.{w} (U k g)) where
  δ : ∀ n, (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M)
  square : ∀ n, (δ (n+1)).comp (δ n) = 0
  evaluation : homComplex (Ext.chain k g d hc) M ≅ Ext.cochain k g M δ square
  eval : ∀ n (F : V k g n →ₗ[U k g] M) z,
    (evaluation.hom.f n).hom F z = F ((1 : U k g) ⊗ₜ[k] z)
  formula : ∀ n f x, δ n f (wedge k g (n+1) x) =
    cochainActionSum k g M n f x + cochainBracketSum k g M n f x

namespace Model
variable {k g d hc}
variable {M N P : ModuleCat.{w} (U k g)}
abbrev complex (C : Model k g d hc M) := Ext.cochain k g M C.δ C.square
/-- Coefficient maps are specified through evaluation; the implementation
must also prove their pointwise postcomposition formula. -/
def map (C : Model k g d hc M) (D : Model k g d hc N) (h : M ⟶ N) :
    C.complex ⟶ D.complex :=
  C.evaluation.inv ≫ homPostMap (Ext.chain k g d hc) h.hom ≫ D.evaluation.hom

/-- HA-A07's comparison, induced on the actual quotient by inverse evaluation. -/
def comparison (C : Model k g d hc M) (n : ℕ) :
    Homology C.complex n ≃ₗ[ℤ] Homology (homComplex (Ext.chain k g d hc) M) n :=
  ((quotientHomology (ComplexShape.up ℕ) n).mapIso C.evaluation.symm).toLinearEquiv
end Model
end AdvancedHomologicalAlgebra.CE.Coefficients

namespace Specs.AdvancedHomologicalAlgebra.CE.Coefficients
open _root_.AdvancedHomologicalAlgebra.CE
open _root_.AdvancedHomologicalAlgebra.CE.Coefficients
open P103.Specs.Ch11.ExtExactSequences P103.Specs.Ch11.ExtBalance
universe u v w
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
variable (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)

def modelsExpected : Prop :=
  HasBoundaryFormula k g d → ∀ M : ModuleCat.{w} (U k g), Nonempty (Model k g d hc M)

/-- No resolution or differential certificate is assumed: the source
construction actually supplies the boundary, its exactness and every model. -/
def constructionExpected : Prop :=
  Module.Free k g → ∃ (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d),
    HasBoundaryFormula k g d ∧ Ext.AugmentedExact k g d ∧
      ∀ M : ModuleCat.{w} (U k g), Nonempty (Model k g d hc M)

def mapExpected : Prop :=
  ∀ (M N : ModuleCat.{w} (U k g)) (C : Model k g d hc M) (D : Model k g d hc N)
    (h : M ⟶ N) n f, ((C.map D h).f n).hom f = (h.hom.restrictScalars k).comp f

/-- Exactness uses freeness of the exterior powers, with unrestricted rank. -/
def degreewiseExpected : Prop :=
  Module.Free k g → ∀ (M N P : ModuleCat.{w} (U k g))
    (C : Model k g d hc M) (D : Model k g d hc N) (E : Model k g d hc P)
    (i : M ⟶ N) (p : N ⟶ P),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    DegreewiseExact (C.map D i) (D.map E p)

/-- The full sequence, including 0 → H⁰ and the positive lift/differentiate
boundary formula on every pair of lifted alternating cochains. -/
def sequenceExpected : Prop :=
  Module.Free k g → ∀ (M N P : ModuleCat.{w} (U k g))
    (C : Model k g d hc M) (D : Model k g d hc N) (E : Model k g d hc P)
    (i : M ⟶ N) (p : N ⟶ P),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    ∃ δ : ∀ n, Homology E.complex n →ₗ[ℤ] Homology C.complex (n+1),
      Function.Injective (homologyMap (C.map D i) 0) ∧
      ∀ n, Connecting (C.map D i) (D.map E p) n (n+1) (δ n) ∧
        SequenceExact (C.map D i) (D.map E p) n (n+1) (δ n)

/-- Every chosen lift of an alternating cocycle computes the boundary by
the printed CE differential, with a positive sign. -/
def liftedExpected : Prop :=
  Module.Free k g → ∀ (M N P : ModuleCat.{w} (U k g))
    (C : Model k g d hc M) (D : Model k g d hc N) (E : Model k g d hc P)
    (i : M ⟶ N) (p : N ⟶ P),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    ∀ n (δ : Homology E.complex n →ₗ[ℤ] Homology C.complex (n+1)),
    Connecting (C.map D i) (D.map E p) n (n+1) δ →
    ∀ (z : cycles E.complex n) (b : W k g n →ₗ[k] N),
    (p.hom.restrictScalars k).comp b = z.val →
    ∃ a : cycles C.complex (n+1),
      (∀ x, i.hom (a.val (wedge k g (n+1) x)) =
        cochainActionSum k g N n b x + cochainBracketSum k g N n b x) ∧
      δ (homologyClass _ n z) = homologyClass _ (n+1) a

/-- All five squares, including the boundary square, for every commuting
map of short exact coefficient sequences. -/
def naturalityExpected : Prop :=
  Module.Free k g → ∀ (M N P M' N' P' : ModuleCat.{w} (U k g))
    (C : Model k g d hc M) (D : Model k g d hc N) (E : Model k g d hc P)
    (C' : Model k g d hc M') (D' : Model k g d hc N') (E' : Model k g d hc P')
    (i : M ⟶ N) (p : N ⟶ P) (i' : M' ⟶ N') (p' : N' ⟶ P')
    (a : M ⟶ M') (b : N ⟶ N') (c : P ⟶ P'),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    Function.Injective i'.hom → Function.Exact i'.hom p'.hom → Function.Surjective p'.hom →
    i ≫ b = a ≫ i' → p ≫ c = b ≫ p' → ∀ n
    (δ : Homology E.complex n →ₗ[ℤ] Homology C.complex (n+1))
    (ε : Homology E'.complex n →ₗ[ℤ] Homology C'.complex (n+1)),
    Connecting (C.map D i) (D.map E p) n (n+1) δ →
    Connecting (C'.map D' i') (D'.map E' p') n (n+1) ε →
    (homologyMap (D.map D' b) n).comp (homologyMap (C.map D i) n) =
      (homologyMap (C'.map D' i') n).comp (homologyMap (C.map C' a) n) ∧
    (homologyMap (E.map E' c) n).comp (homologyMap (D.map E p) n) =
      (homologyMap (D'.map E' p') n).comp (homologyMap (D.map D' b) n) ∧
    (homologyMap (C.map C' a) (n+1)).comp δ = ε.comp (homologyMap (E.map E' c) n) ∧
    (homologyMap (D.map D' b) (n+1)).comp (homologyMap (C.map D i) (n+1)) =
      (homologyMap (C'.map D' i') (n+1)).comp (homologyMap (C.map C' a) (n+1)) ∧
    (homologyMap (E.map E' c) (n+1)).comp (homologyMap (D.map E p) (n+1)) =
      (homologyMap (D'.map E' p') (n+1)).comp (homologyMap (D.map D' b) (n+1))

/-- Comparison of both ordinary arrows and the connector with the ordinary
Ext coefficient sequence. `he` is actual augmented exactness, supplied by
HA-A07, and does not assume a conclusion about coefficient cohomology. -/
def extExpected : Prop :=
  Module.Free k g → ∀ (he : Ext.AugmentedExact k g d)
    (M N P : ModuleCat.{w} (U k g))
    (C : Model k g d hc M) (D : Model k g d hc N) (E : Model k g d hc P)
    (i : M ⟶ N) (p : N ⟶ P),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    ∀ n (δ : Homology E.complex n →ₗ[ℤ] Homology C.complex (n+1))
      (ε : Homology (homComplex (Ext.chain k g d hc) P) n →ₗ[ℤ]
        Homology (homComplex (Ext.chain k g d hc) M) (n+1)),
    Connecting (C.map D i) (D.map E p) n (n+1) δ →
    SecondConnecting (A := @ModuleCat.of (U k g) _ k _ (Ext.trivialModule k g)) (Ext.resolution k g d hc he) i p n ε →
    (D.comparison n).toLinearMap.comp (homologyMap (C.map D i) n) =
      (homologyMap (homPostMap (Ext.chain k g d hc) i.hom) n).comp (C.comparison n).toLinearMap ∧
    (E.comparison n).toLinearMap.comp (homologyMap (D.map E p) n) =
      (homologyMap (homPostMap (Ext.chain k g d hc) p.hom) n).comp (D.comparison n).toLinearMap ∧
    (C.comparison (n+1)).toLinearMap.comp δ = ε.comp (E.comparison n).toLinearMap

/-- The same boundary agrees with the injective-resolution computation of
right-derived Hom under the canonical, augmentation-prescribed balance maps. -/
def derivedExpected : Prop :=
  Module.Free k g → ∀ (he : Ext.AugmentedExact k g d)
    (M N P : ModuleCat.{w} (U k g))
    (C : Model k g d hc M) (D : Model k g d hc N) (E : Model k g d hc P)
    (i : M ⟶ N) (p : N ⟶ P),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    letI := Ext.trivialModule k g
    ∀ (L : InjectiveResolution (U k g) M) (T : InjectiveResolution (U k g) P)
      (H : P103.Specs.Ch10.Horseshoe.InjectiveData i.hom p.hom L T) n
      (δ : Homology E.complex n →ₗ[ℤ] Homology C.complex (n+1))
      (ε : Homology (injectiveHom (ModuleCat.of (U k g) k) T.complex) n →ₗ[ℤ]
        Homology (injectiveHom (ModuleCat.of (U k g) k) L.complex) (n+1)),
    Connecting (C.map D i) (D.map E p) n (n+1) δ →
    Connecting (injectiveHomMap (LinearMap.id : k →ₗ[U k g] k) H.inclusion)
      (injectiveHomMap (LinearMap.id : k →ₗ[U k g] k) H.projection) n (n+1) ε →
    ∀ (eT : Homology (injectiveHom (ModuleCat.of (U k g) k) T.complex) n ≃ₗ[ℤ]
          ExtWith (Ext.resolution k g d hc he) P n)
      (eL : Homology (injectiveHom (ModuleCat.of (U k g) k) L.complex) (n+1) ≃ₗ[ℤ]
          ExtWith (Ext.resolution k g d hc he) M (n+1)),
    BalancedComparison (A := ModuleCat.of (U k g) k) (B := P) (Ext.resolution k g d hc he) T n eT →
    BalancedComparison (A := ModuleCat.of (U k g) k) (B := M) (Ext.resolution k g d hc he) L (n+1) eL →
    (C.comparison (n+1)).symm.toLinearMap.comp (eL.toLinearMap.comp ε) =
      δ.comp ((E.comparison n).symm.toLinearMap.comp eT.toLinearMap)

def modelsType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d), modelsExpected.{u,v,w} k g d hc

def constructionType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g], constructionExpected.{u,v,w} k g

def mapType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d), mapExpected.{u,v,w} k g d hc

def degreewiseType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d), degreewiseExpected.{u,v,w} k g d hc

def sequenceType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d), sequenceExpected.{u,v,w} k g d hc

def liftedType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d), liftedExpected.{u,v,w} k g d hc

def naturalityType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d), naturalityExpected.{u,v,w} k g d hc

def extType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d), extExpected.{u,v,w} k g d hc

def derivedType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d), derivedExpected.{u,v,w} k g d hc

end Specs.AdvancedHomologicalAlgebra.CE.Coefficients

open Specs.AdvancedHomologicalAlgebra.UniversalDeltaFunctors
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open P103.Specs.Ch11.ExtExactSequences P103.Specs.Ch11.ExtBalance
namespace AdvancedHomologicalAlgebra.CE.Coefficients.Derived
universe r a s h h'
variable (R : Type r) [Ring R] (X : ModuleCat.{a} R)
  (P : LeftResolution R X) (hP : P.IsProjective)

structure OrdinaryData where
  maps : ∀ n, ExtMaps.{r,a,max r a s} R n
  boundary : ∀ {S : ShortComplex (ModuleCat.{max r a s} R)}, S.ShortExact → ∀ n,
    ExtWith P S.X₃ n →ₗ[ℤ] ExtWith P S.X₁ (n+1)
  connecting : ∀ {S : ShortComplex (ModuleCat.{max r a s} R)} (hS : S.ShortExact) n,
    SecondConnecting (A := X) P S.f S.g n (boundary hS n)
  exactness : ∀ {S : ShortComplex (ModuleCat.{max r a s} R)} (hS : S.ShortExact) n,
    SecondExact (A := X) P S.f S.g n (boundary hS n)

variable {R X P hP}

def OrdinaryData.system (D : OrdinaryData.{r,a,s} R X P) (hP : P.IsProjective) : CohomologicalSystem (ModuleCat.{max r a s} R) (ModuleCat.{max r a s} ℤ) where
  value n := (D.maps n).coefficients ⟨P, hP⟩
  δ hS n := ModuleCat.ofHom (D.boundary hS n)

open CategoryTheory.Functor

/-- The degree-zero map induced by the actual right-derived unit on stalks. -/
def degreeZeroUnit {A : Type*} {B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{h} A] [HasDerivedCategory.{h'} B]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] : F ⟶ rightValue F 0 := by
  let stalk : A ⥤ CochainComplex.Plus A :=
    (CochainComplex.plus A).lift (CochainComplex.singleFunctor A 0)
      (fun _ => ⟨0, inferInstance⟩)
  let e : F ⋙ DerivedCategory.Plus.singleFunctor B 0 ≅
      stalk ⋙ F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q := by
    apply ((FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).whiskeringRight A).preimageIso
    change F ⋙ DerivedCategory.singleFunctor B 0 ≅
      CochainComplex.singleFunctor A 0 ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
    exact isoWhiskerLeft F (DerivedCategory.singleFunctorIsoCompQ B 0) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).symm _ ≪≫
      Functor.associator _ _ _
  exact (isoWhiskerLeft F (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0)).inv ≫
    whiskerRight (e.hom ≫ whiskerLeft stalk F.rightDerivedFunctorPlusUnit)
      (DerivedCategory.Plus.homologyFunctor B 0)

end AdvancedHomologicalAlgebra.CE.Coefficients.Derived

namespace Specs.AdvancedHomologicalAlgebra.CE.Coefficients.Derived
open _root_.AdvancedHomologicalAlgebra.CE.Coefficients.Derived
universe r a s h h'

def dataExistsType : Prop :=
  ∀ (R : Type r) [Ring R] (X : ModuleCat.{a} R) (P : LeftResolution R X),
    P.IsProjective → Nonempty (OrdinaryData.{r,a,s} R X P)

/-- Ordinary Ext and the actual right-derived Hom are isomorphic as
cohomological delta-functors. The zero component is fixed on [f ε].
Consequently this comparison includes the derived-triangle boundary. -/
def rightDerivedType : Prop :=
  ∀ (R : Type r) [Ring R] (X : ModuleCat.{a} R) (P : LeftResolution R X)
    (hP : P.IsProjective)
    [HasDerivedCategory.{h} (ModuleCat.{max r a s} R)]
    [HasDerivedCategory.{h'} (ModuleCat.{max r a s} ℤ)]
    (D : OrdinaryData.{r,a,s} R X P),
    let F := (covariantHom (R := R) X : ModuleCat.{max r a s} R ⥤ ModuleCat.{max r a s} ℤ)
    ∃ φ : CohomologicalMorphism (D.system hP) (rightSystem F),
      (∀ n, IsIso (φ.component n)) ∧
      ∀ (M : ModuleCat.{max r a s} R) (f : X →ₗ[R] M),
        ((φ.component 0).app M).hom (homClass P M f) = ((degreeZeroUnit F).app M).hom f

end Specs.AdvancedHomologicalAlgebra.CE.Coefficients.Derived

namespace Specs.AdvancedHomologicalAlgebra.CE.Coefficients
open _root_.AdvancedHomologicalAlgebra.CE
open _root_.AdvancedHomologicalAlgebra.CE.Coefficients
universe u v w h h'

/-- The complete comparison square with HA-R09's actual right-derived-Hom
boundary (defined by applying RF to the HA-D04 stalk triangle). This is
assembled with HA-A07 inverse evaluation, not an arbitrary CE group isomorphism.
Ordinary-system existence and canonical degree-zero comparison are separately
specified above. The coefficient universe may always be enlarged to contain k
and g; the earlier sequence targets also cover small coefficients directly. -/
def rightDerivedSequenceType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    [Module.Free k g] (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)
    (he : Ext.AugmentedExact k g d),
    letI := Ext.trivialModule k g
    ∀ [HasDerivedCategory.{h} (ModuleCat.{max u v w} (U k g))]
      [HasDerivedCategory.{h'} (ModuleCat.{max u v w} ℤ)],
    ∃ (hP : (Ext.resolution k g d hc he).IsProjective)
      (O : _root_.AdvancedHomologicalAlgebra.CE.Coefficients.Derived.OrdinaryData.{max u v,u,w} (U k g) (ModuleCat.of (U k g) k)
        (Ext.resolution k g d hc he))
      (φ : CohomologicalMorphism (O.system hP)
        (rightSystem (P103.Specs.Ch11.ExtBalance.covariantHom (R := U k g) k :
          ModuleCat.{max u v w} (U k g) ⥤ ModuleCat.{max u v w} ℤ))),
      (∀ n, IsIso (φ.component n)) ∧
      (∀ (M : ModuleCat.{max u v w} (U k g)) (f : k →ₗ[U k g] M),
        ((φ.component 0).app M).hom (homClass (Ext.resolution k g d hc he) M f) =
          ((_root_.AdvancedHomologicalAlgebra.CE.Coefficients.Derived.degreeZeroUnit
            (P103.Specs.Ch11.ExtBalance.covariantHom (R := U k g) k :
              ModuleCat.{max u v w} (U k g) ⥤ ModuleCat.{max u v w} ℤ)).app M).hom f) ∧
      ∀ (S : ShortComplex (ModuleCat.{max u v w} (U k g))) (hS : S.ShortExact)
        (C : Model k g d hc S.X₁) (D : Model k g d hc S.X₂) (E : Model k g d hc S.X₃)
        n (δ : Homology E.complex n →ₗ[ℤ] Homology C.complex (n+1)),
        Connecting (C.map D S.f) (D.map E S.g) n (n+1) δ →
        ((φ.component (n+1)).app S.X₁).hom.comp ((C.comparison (n+1)).toLinearMap.comp δ) =
          (rightBoundary (P103.Specs.Ch11.ExtBalance.covariantHom (R := U k g) k :
            ModuleCat.{max u v w} (U k g) ⥤ ModuleCat.{max u v w} ℤ) hS n).hom.comp
              (((φ.component n).app S.X₃).hom.comp (E.comparison n).toLinearMap)

end Specs.AdvancedHomologicalAlgebra.CE.Coefficients

namespace AdvancedHomologicalAlgebra.CE.Coefficients
universe u v w
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
variable (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)

/-- Change only the coefficient carrier, over the original enveloping algebra. -/
abbrev liftCoefficients : ModuleCat.{w} (U k g) ⥤ ModuleCat.{max u v w} (U k g) :=
  ModuleCat.uliftFunctor.{max u v, w} (U k g)

/-- Cohomology comparison obtained from postcomposition with the canonical
carrier equivalence. The naturality equations retain the original maps. -/
structure LiftedCohomology where
  ext : ∀ (M : ModuleCat.{w} (U k g)) n,
    Homology (homComplex (Ext.chain k g d hc) M) n ≃ₗ[ℤ]
      Homology (homComplex (Ext.chain k g d hc) ((liftCoefficients.{u,v,w} k g).obj M)) n
  ext_induced : ∀ (M : ModuleCat.{w} (U k g)),
    Ext.InducesCohomologyMap
      (K := homComplex (Ext.chain k g d hc) M)
      (L := homComplex (Ext.chain k g d hc) ((liftCoefficients.{u,v,w} k g).obj M))
      (fun _ => (P103.HomTensorExactness.post
        (ULift.moduleEquiv (R := U k g) (M := M)).symm.toLinearMap).toIntLinearMap)
      (fun n => (ext M n).toLinearMap)
  ext_natural : ∀ {M N : ModuleCat.{w} (U k g)} (f : M ⟶ N) n,
    (ext N n).toLinearMap.comp (homologyMap (homPostMap (Ext.chain k g d hc) f.hom) n) =
      (homologyMap (homPostMap (Ext.chain k g d hc)
        ((liftCoefficients.{u,v,w} k g).map f).hom) n).comp (ext M n).toLinearMap
  ce_induced : ∀ (M : ModuleCat.{w} (U k g)) (C : Model k g d hc M)
    (D : Model k g d hc ((liftCoefficients.{u,v,w} k g).obj M)),
    Ext.InducesCohomologyMap (K := C.complex) (L := D.complex)
      (fun _ => (P103.HomTensorExactness.post
        ((ULift.moduleEquiv (R := U k g) (M := M)).symm.toLinearMap.restrictScalars k)).toIntLinearMap)
      (fun n => ((C.comparison n).trans ((ext M n).trans (D.comparison n).symm)).toLinearMap)

end AdvancedHomologicalAlgebra.CE.Coefficients

namespace Specs.AdvancedHomologicalAlgebra.CE.Coefficients
open _root_.AdvancedHomologicalAlgebra.CE
open _root_.AdvancedHomologicalAlgebra.CE.Coefficients
open P103.Specs.Ch11.ExtExactSequences P103.Specs.Ch11.ExtBalance
universe u v w h h'

/-- The actual connector of the lifted short exact sequence, compared to
the original CE and ordinary Ext connectors on their original quotients. -/
def liftedRightDerivedSequenceType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    [Module.Free k g] (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)
    (he : Ext.AugmentedExact k g d),
    letI := Ext.trivialModule k g
    let P := Ext.resolution k g d hc he
    ∀ [HasDerivedCategory.{h} (ModuleCat.{max u v w} (U k g))]
      [HasDerivedCategory.{h'} (ModuleCat.{max u v w} ℤ)],
    let F := (covariantHom (R := U k g) k :
      ModuleCat.{max u v w} (U k g) ⥤ ModuleCat.{max u v w} ℤ)
    ∃ (L : LiftedCohomology.{u,v,w} k g d hc) (hP : P.IsProjective)
      (O : _root_.AdvancedHomologicalAlgebra.CE.Coefficients.Derived.OrdinaryData.{max u v,u,w}
        (U k g) (ModuleCat.of (U k g) k) P)
      (φ : CohomologicalMorphism (O.system hP) (rightSystem F)),
      (∀ n, IsIso (φ.component n)) ∧
      (∀ (M : ModuleCat.{max u v w} (U k g)) (f : k →ₗ[U k g] M),
        ((φ.component 0).app M).hom (homClass P M f) =
          ((_root_.AdvancedHomologicalAlgebra.CE.Coefficients.Derived.degreeZeroUnit F).app M).hom f) ∧
      ∀ (S : ShortComplex (ModuleCat.{w} (U k g))) (hS : S.ShortExact)
        (C : Model k g d hc S.X₁) (D : Model k g d hc S.X₂) (E : Model k g d hc S.X₃)
        n (δ : Homology E.complex n →ₗ[ℤ] Homology C.complex (n+1))
        (ε : ExtWith P S.X₃ n →ₗ[ℤ] ExtWith P S.X₁ (n+1)),
        Connecting (C.map D S.f) (D.map E S.g) n (n+1) δ →
        SecondConnecting (A := ModuleCat.of (U k g) k) P S.f S.g n ε →
        let hS' := hS.map_of_exact (liftCoefficients.{u,v,w} k g)
        (L.ext S.X₁ (n+1)).toLinearMap.comp ε =
          (O.boundary hS' n).comp (L.ext S.X₃ n).toLinearMap ∧
        ((φ.component (n+1)).app ((liftCoefficients.{u,v,w} k g).obj S.X₁)).hom.comp
            ((L.ext S.X₁ (n+1)).toLinearMap.comp ((C.comparison (n+1)).toLinearMap.comp δ)) =
          (rightBoundary F hS' n).hom.comp
            (((φ.component n).app ((liftCoefficients.{u,v,w} k g).obj S.X₃)).hom.comp
              ((L.ext S.X₃ n).toLinearMap.comp (E.comparison n).toLinearMap))

end Specs.AdvancedHomologicalAlgebra.CE.Coefficients

namespace AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous

open _root_.AdvancedHomologicalAlgebra.CE
universe u v a b c a' b' c' s t q
variable {A : CochainComplex (ModuleCat.{s} ℤ) ℕ}
  {B : CochainComplex (ModuleCat.{t} ℤ) ℕ} {C : CochainComplex (ModuleCat.{q} ℤ) ℕ}

/-- A map on the original quotient, with every image of a class fixed by
the specified cochain map. -/
structure QuotientMap (A : CochainComplex (ModuleCat.{s} ℤ) ℕ)
    (B : CochainComplex (ModuleCat.{t} ℤ) ℕ) (f : ∀ n, A.X n →ₗ[ℤ] B.X n) where
  hom : ∀ n, Homology A n →ₗ[ℤ] Homology B n
  induced : Ext.InducesCohomologyMap f hom

/-- The long exact sequence on three original cochain complexes whose terms
need not have the same universe. The boundary uses the positive differential. -/
structure Sequence (i : ∀ n, A.X n →ₗ[ℤ] B.X n) (p : ∀ n, B.X n →ₗ[ℤ] C.X n) where
  inclusion : QuotientMap A B i
  projection : QuotientMap B C p
  degreewise : ∀ n, Function.Injective (i n) ∧ Function.Exact (i n) (p n) ∧
    Function.Surjective (p n)
  boundary : ∀ n, Homology C n →ₗ[ℤ] Homology A (n+1)
  initial : Function.Injective (inclusion.hom 0)
  exactness : ∀ n, Function.Exact (inclusion.hom n) (projection.hom n) ∧
    Function.Exact (projection.hom n) (boundary n) ∧
    Function.Exact (boundary n) (inclusion.hom (n+1))
  lift_boundary : ∀ n (z : cycles C n) (y : B.X n), p n y = z.val →
    ∃ x : cycles A (n+1), i (n+1) x.val = (B.d n (n+1)).hom y ∧
      boundary n (homologyClass C n z) = homologyClass A (n+1) x

/-- The three squares in every degree, including the one crossing the
connecting map. -/
def Sequence.Commutes {A' : CochainComplex (ModuleCat.{a'} ℤ) ℕ}
    {B' : CochainComplex (ModuleCat.{b'} ℤ) ℕ} {C' : CochainComplex (ModuleCat.{c'} ℤ) ℕ}
    {i : ∀ n, A.X n →ₗ[ℤ] B.X n} {p : ∀ n, B.X n →ₗ[ℤ] C.X n}
    {i' : ∀ n, A'.X n →ₗ[ℤ] B'.X n} {p' : ∀ n, B'.X n →ₗ[ℤ] C'.X n}
    (S : Sequence i p) (T : Sequence i' p')
    (α : ∀ n, Homology A n →ₗ[ℤ] Homology A' n)
    (β : ∀ n, Homology B n →ₗ[ℤ] Homology B' n)
    (γ : ∀ n, Homology C n →ₗ[ℤ] Homology C' n) : Prop :=
  ∀ n, (β n).comp (S.inclusion.hom n) = (T.inclusion.hom n).comp (α n) ∧
    (γ n).comp (S.projection.hom n) = (T.projection.hom n).comp (β n) ∧
    (α (n+1)).comp (S.boundary n) = (T.boundary n).comp (γ n)

variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
  {d : BoundaryFamily k g} {hc : IsAugmentedComplex k g d}
  {M : ModuleCat.{a} (U k g)} {N : ModuleCat.{b} (U k g)} {P : ModuleCat.{c} (U k g)}

/-- Original exterior cochains, with their maps given by restricted postcomposition. -/
abbrev cePost (CM : Model k g d hc M) (CN : Model k g d hc N) (h : M →ₗ[U k g] N) :
    ∀ n, CM.complex.X n →ₗ[ℤ] CN.complex.X n :=
  fun _ => (P103.HomTensorExactness.post (h.restrictScalars k)).toIntLinearMap

/-- Original projective-Hom cochains, with their maps given by U-linear postcomposition. -/
abbrev extPost (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)
    (h : M →ₗ[U k g] N) :
    ∀ n, (homComplex (Ext.chain k g d hc) M).X n →ₗ[ℤ]
      (homComplex (Ext.chain k g d hc) N).X n :=
  fun _ => (P103.HomTensorExactness.post h).toIntLinearMap

/-- The two actual long exact sequences, compared by inverse evaluation. -/
structure CoefficientSequence (CM : Model k g d hc M) (CN : Model k g d hc N)
    (CP : Model k g d hc P) (i : M →ₗ[U k g] N) (p : N →ₗ[U k g] P) where
  ce : Sequence (cePost CM CN i) (cePost CN CP p)
  ext : Sequence (extPost d hc i) (extPost d hc p)
  comparison : ce.Commutes ext
    (fun n => (CM.comparison n).toLinearMap)
    (fun n => (CN.comparison n).toLinearMap)
    (fun n => (CP.comparison n).toLinearMap)

universe l

/-- The canonical lift of one original module into a common category. -/
abbrev lift (M : ModuleCat.{a} (U k g)) : ModuleCat.{max a l} (U k g) :=
  ModuleCat.of (U k g) (ULift.{l} M)

abbrev liftEquiv (M : ModuleCat.{a} (U k g)) : M ≃ₗ[U k g] (lift.{u,v,a,l} M) :=
  (ULift.moduleEquiv (R := U k g) (M := M)).symm

/-- The original map between independently sized modules, conjugated by
the two carrier equivalences into the common module category. -/
def liftMap (h : M →ₗ[U k g] N) :
    lift.{u,v,a,max a b l} M ⟶ lift.{u,v,b,max a b l} N :=
  ModuleCat.ofHom ((liftEquiv.{u,v,b,max a b l} N).toLinearMap.comp
    (h.comp (liftEquiv.{u,v,a,max a b l} M).symm.toLinearMap))

/-- This short complex uses the given maps on the given carrier lifts. -/
def liftSequence (i : M →ₗ[U k g] N) (p : N →ₗ[U k g] P)
    (hp : Function.Exact i p) :
    ShortComplex (ModuleCat.{max u v a b c} (U k g)) :=
  ShortComplex.mk (liftMap.{u,v,a,b,max u v c} i) (liftMap.{u,v,b,c,max u v a} p) (by
    apply ModuleCat.hom_ext
    ext x
    change p (i x.down) = 0
    exact DFunLike.congr_fun hp.linearMap_comp_eq_zero x.down)

end AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous

namespace Specs.AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous

open _root_.AdvancedHomologicalAlgebra.CE
open _root_.AdvancedHomologicalAlgebra.CE.Coefficients
open _root_.AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous
open P103.Specs.Ch11.ExtExactSequences P103.Specs.Ch11.ExtBalance
universe u v a b c a' b' c' h h'

/-- The exterior and ordinary Ext long exact sequences on every original
coefficient sequence, with no common original carrier universe. -/
def sequenceType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g] [Module.Free k g]
    (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)
    (M : ModuleCat.{a} (U k g)) (N : ModuleCat.{b} (U k g)) (P : ModuleCat.{c} (U k g))
    (CM : Model k g d hc M) (CN : Model k g d hc N) (CP : Model k g d hc P)
    (i : M →ₗ[U k g] N) (p : N →ₗ[U k g] P),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    Nonempty (CoefficientSequence CM CN CP i p)

/-- Both long exact sequences are natural under the given maps of original
short exact sequences, with six independent coefficient universes. -/
def naturalityType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
    (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)
    (M : ModuleCat.{a} (U k g)) (N : ModuleCat.{b} (U k g)) (P : ModuleCat.{c} (U k g))
    (M' : ModuleCat.{a'} (U k g)) (N' : ModuleCat.{b'} (U k g)) (P' : ModuleCat.{c'} (U k g))
    (CM : Model k g d hc M) (CN : Model k g d hc N) (CP : Model k g d hc P)
    (CM' : Model k g d hc M') (CN' : Model k g d hc N') (CP' : Model k g d hc P')
    (i : M →ₗ[U k g] N) (p : N →ₗ[U k g] P) (i' : M' →ₗ[U k g] N') (p' : N' →ₗ[U k g] P')
    (α : M →ₗ[U k g] M') (β : N →ₗ[U k g] N') (γ : P →ₗ[U k g] P'),
    β.comp i = i'.comp α → γ.comp p = p'.comp β →
    ∀ (S : CoefficientSequence CM CN CP i p) (T : CoefficientSequence CM' CN' CP' i' p'),
      ∃ (aCE : QuotientMap _ _ (cePost CM CM' α)) (bCE : QuotientMap _ _ (cePost CN CN' β))
        (cCE : QuotientMap _ _ (cePost CP CP' γ)) (aExt : QuotientMap _ _ (extPost d hc α))
        (bExt : QuotientMap _ _ (extPost d hc β)) (cExt : QuotientMap _ _ (extPost d hc γ)),
        S.ce.Commutes T.ce aCE.hom bCE.hom cCE.hom ∧
        S.ext.Commutes T.ext aExt.hom bExt.hom cExt.hom

/-- Compare the original quotient boundary with the actual derived triangle
of its exact, termwise carrier lift, via the normalized derived unit. -/
def rightDerivedType : Prop :=
  ∀ (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g] [Module.Free k g]
    (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)
    (he : Ext.AugmentedExact k g d),
    letI := Ext.trivialModule k g
    let Q := Ext.resolution k g d hc he
    ∀ [HasDerivedCategory.{h} (ModuleCat.{max u v a b c} (U k g))]
      [HasDerivedCategory.{h'} (ModuleCat.{max u v a b c} ℤ)],
    let F := (covariantHom (R := U k g) k :
      ModuleCat.{max u v a b c} (U k g) ⥤ ModuleCat.{max u v a b c} ℤ)
    ∃ (hQ : Q.IsProjective)
      (O : _root_.AdvancedHomologicalAlgebra.CE.Coefficients.Derived.OrdinaryData.{max u v,u,max a b c} (U k g) (ModuleCat.of (U k g) k) Q)
      (φ : CohomologicalMorphism (O.system hQ) (rightSystem F)),
      (∀ n, IsIso (φ.component n)) ∧
      (∀ (B : ModuleCat.{max u v a b c} (U k g)) (f : k →ₗ[U k g] B),
        ((φ.component 0).app B).hom (homClass Q B f) =
          ((_root_.AdvancedHomologicalAlgebra.CE.Coefficients.Derived.degreeZeroUnit F).app B).hom f) ∧
      ∀ (M : ModuleCat.{a} (U k g)) (N : ModuleCat.{b} (U k g)) (P : ModuleCat.{c} (U k g))
        (CM : Model k g d hc M) (CN : Model k g d hc N) (CP : Model k g d hc P)
        (i : M →ₗ[U k g] N) (p : N →ₗ[U k g] P),
        Function.Injective i → ∀ hp : Function.Exact i p, Function.Surjective p →
        ∀ T : CoefficientSequence CM CN CP i p,
        let S := liftSequence i p hp
        ∃ (hS : S.ShortExact)
          (LM : Model k g d hc S.X₁) (LN : Model k g d hc S.X₂) (LP : Model k g d hc S.X₃)
          (L : CoefficientSequence LM LN LP S.f.hom S.g.hom)
          (eM : ∀ n, ExtWith Q M n ≃ₗ[ℤ] ExtWith Q S.X₁ n)
          (eN : ∀ n, ExtWith Q N n ≃ₗ[ℤ] ExtWith Q S.X₂ n)
          (eP : ∀ n, ExtWith Q P n ≃ₗ[ℤ] ExtWith Q S.X₃ n),
          let fM := (liftEquiv.{u,v,a,max u v a b c} M).toLinearMap
          let fN := (liftEquiv.{u,v,b,max u v a b c} N).toLinearMap
          let fP := (liftEquiv.{u,v,c,max u v a b c} P).toLinearMap
          let fME := fun n => (eM n).toLinearMap
          let fNE := fun n => (eN n).toLinearMap
          let fPE := fun n => (eP n).toLinearMap
          let fMC := fun n => ((CM.comparison n).trans ((eM n).trans (LM.comparison n).symm)).toLinearMap
          let fNC := fun n => ((CN.comparison n).trans ((eN n).trans (LN.comparison n).symm)).toLinearMap
          let fPC := fun n => ((CP.comparison n).trans ((eP n).trans (LP.comparison n).symm)).toLinearMap
          Ext.InducesCohomologyMap (extPost d hc fM) fME ∧
          Ext.InducesCohomologyMap (extPost d hc fN) fNE ∧
          Ext.InducesCohomologyMap (extPost d hc fP) fPE ∧
          Ext.InducesCohomologyMap (cePost CM LM fM) fMC ∧
          Ext.InducesCohomologyMap (cePost CN LN fN) fNC ∧
          Ext.InducesCohomologyMap (cePost CP LP fP) fPC ∧
          T.ext.Commutes L.ext fME fNE fPE ∧
          T.ce.Commutes L.ce fMC fNC fPC ∧
          ∀ n, L.ext.boundary n = O.boundary hS n ∧
            ((φ.component (n+1)).app S.X₁).hom.comp
                  ((fME (n+1)).comp ((CM.comparison (n+1)).toLinearMap.comp (T.ce.boundary n))) =
              (rightBoundary F hS n).hom.comp
                  (((φ.component n).app S.X₃).hom.comp ((fPE n).comp (CP.comparison n).toLinearMap))

end Specs.AdvancedHomologicalAlgebra.CE.Coefficients.Heterogeneous
