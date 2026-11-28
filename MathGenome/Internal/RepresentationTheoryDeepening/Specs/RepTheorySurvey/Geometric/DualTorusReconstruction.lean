import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusSatake
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

noncomputable section

open CategoryTheory CategoryTheory.Functor LinearAlgebraicGroups
open scoped MonoidalCategory TensorProduct ChangeOfRings

namespace RepTheorySurvey.Geometric.DualTorusReconstructionSpecs

open Analytic TorusPerverseSpecs TorusOrderedConvolutionSpecs TorusFusionSpecs
  TorusSymmetricConvolutionSpecs TorusSatakeSpecs

abbrev Test := TestAlgebra ℚ

abbrev extend (A : Test) := ModuleCat.extendScalars (algebraMap ℚ A)

variable {r : ℕ} {D : OrderedGeometry r} {g : StageGeometry r} {c : ContinuousJets r}
  {P : OrderedProduct D g c} {U : OrderedConstraints P} {σ : SwapsConvolution P}
  {S : SymmetricConvolution U σ}

/-- The monoidal functor of degree-zero global sections, extended to the test algebra. -/
abbrev fiber (E : SatakeEquivalence S) (A : Test) :
    letI := S.monoidal
    LaxMonoidalFunctor (Heart r g c) (ModuleCat A) :=
  letI := S.monoidal
  letI := S.symmetric
  letI := E.globalBraided
  ⟨globalSections r g c ⋙ extend A, inferInstance⟩

abbrev FiberAut (E : SatakeEquivalence S) (A : Test) :=
  letI := S.monoidal
  Aut (fiber E A)

abbrev fiberApp (E : SatakeEquivalence S) {A : Test} (η : FiberAut E A) (V : Heart r g c) :
    (extend A).obj ((globalSections r g c).obj V) ⟶
      (extend A).obj ((globalSections r g c).obj V) :=
  letI := S.monoidal
  η.asIso.hom.hom.app V

/-- The canonical comparison from extension to B to successive extensions to A and B. -/
def scalarComparison {A B : Test} (f : A ⟶ B) :
    extend B ≅ extend A ⋙ ModuleCat.extendScalars f.hom.toRingHom :=
  eqToIso (congrArg ModuleCat.extendScalars
    (show algebraMap ℚ B = f.hom.toRingHom.comp (algebraMap ℚ A) by
      ext q
      exact (f.hom.commutes q).symm)) ≪≫
    ModuleCat.extendScalarsComp (algebraMap ℚ A) f.hom.toRingHom

/-- The character groups with postcomposition by the map on units. -/
def characterFunctor (r : ℕ) : Test ⥤ GrpCat where
  obj A := GrpCat.of (Characters r →* Aˣ)
  map f := GrpCat.ofHom
    { toFun := fun u ↦ (Units.map f.hom.toMonoidHom).comp u
      map_one' := by ext a; simp
      map_mul' := by intro u v; ext a; simp }
  map_id := by intro A; apply GrpCat.ext; intro u; ext a; rfl
  map_comp := by intro A B C f h; apply GrpCat.ext; intro u; ext a; rfl

/-- The automorphism groups and their canonical scalar extension maps. -/
structure FiberScalarExtension (E : SatakeEquivalence S) where
  map {A B : Test} (f : A ⟶ B) : FiberAut E A →* FiberAut E B
  map_id (A : Test) (η : FiberAut E A) : map (𝟙 A) η = η
  map_comp {A B C : Test} (f : A ⟶ B) (h : B ⟶ C) (η : FiberAut E A) :
    map (f ≫ h) η = map h (map f η)
  comparison {A B : Test} (f : A ⟶ B) (η : FiberAut E A) (V : Heart r g c) :
    fiberApp E (map f η) V ≫ (scalarComparison f).hom.app ((globalSections r g c).obj V) =
      (scalarComparison f).hom.app ((globalSections r g c).obj V) ≫
        (ModuleCat.extendScalars f.hom.toRingHom).map (fiberApp E η V)

def FiberScalarExtension.functor {E : SatakeEquivalence S} (M : FiberScalarExtension E) :
    Test ⥤ GrpCat.{1} where
  obj A := GrpCat.of (FiberAut E A)
  map f := GrpCat.ofHom (M.map f)
  map_id A := GrpCat.ext (M.map_id A)
  map_comp f h := GrpCat.ext (M.map_comp f h)

abbrev pointsFunctor (r : ℕ) := (groupPointsFunctor ℚ).obj (dualTorus r)

/-- Under the Satake fibre comparison, the inverse reconstruction map acts on every
extended weight space by the given character. The comparison to the points of the
dual torus uses the spectrum of the algebra map evaluated on the character basis. -/
def Reconstruction (E : SatakeEquivalence S) : Prop :=
  ∃ (M : FiberScalarExtension E)
    (scale : ∀ A : Test, (Characters r →* Aˣ) ≃* FiberAut E A)
    (points : characterFunctor r ≅ pointsFunctor r),
    (∀ {A B : Test} (f : A ⟶ B) (u : Characters r →* Aˣ),
      M.map f (scale A u) = scale B ((characterFunctor r).map f u)) ∧
    (∀ (A : Test) (u : Characters r →* Aˣ) (V : Heart r g c)
      (a : Labels r) (x : weightAt (E.equivalence.functor.obj V) a) (b : A),
      let v := E.fiberIso.inv.app V (weightInclusion (E.equivalence.functor.obj V) a x)
      (fiberApp E (scale A u) V)
          (b ⊗ₜ[ℚ,algebraMap ℚ A] v) =
        (↑(u (Multiplicative.ofAdd a)) * b : A) ⊗ₜ[ℚ,algebraMap ℚ A] v) ∧
    (∀ (A : Test) (u : Characters r →* Aˣ),
      let ev : coordinateAlgebra r →ₐ[ℚ] A :=
        MonoidAlgebra.lift ℚ A (Characters r) ((Units.coeHom A).comp u)
      (∀ a : Labels r, ev (MonoidAlgebra.of ℚ (Characters r) (Multiplicative.ofAdd a)) =
        ↑(u (Multiplicative.ofAdd a))) ∧
      (points.hom.app A u : Points (dualTorus r).X A).left =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom ev.toRingHom))

/-- Reconstruction at every rank on the geometric heart and convolution of split-torus Satake. -/
def DualTorusReconstruction : Prop :=
  ∀ r : ℕ, ∃ (D : OrderedGeometry r) (g : StageGeometry r) (c : ContinuousJets r)
    (P : OrderedProduct D g c) (U : OrderedConstraints P) (σ : SwapsConvolution P)
    (S : SymmetricConvolution U σ),
    FlipsConvolutionSummands P σ ∧ LocalGeometry D ∧
    (∀ (A B : Set (Labels r)), A.Finite → B.Finite →
      ∃ (N : ℕ) (G : SectionGeometry N A B) (H : SectionGeometry N B A)
        (J : SectionExchange G H) (E : CoefficientExchange D J),
        ClearsPoles N A B ∧ SpecializesToConvolution σ E) ∧
    ∃ E : SatakeEquivalence S, Reconstruction E

end RepTheorySurvey.Geometric.DualTorusReconstructionSpecs
