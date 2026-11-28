import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusSymmetricConvolution
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.TorusWeights

noncomputable section

open CategoryTheory CategoryTheory.Functor
open scoped Classical DirectSum TensorProduct MonoidalCategory BraidedCategory

namespace RepTheorySurvey.Geometric.TorusSatakeSpecs

open Analytic TorusPerverseSpecs TorusOrderedConvolutionSpecs TorusFusionSpecs
  TorusSymmetricConvolutionSpecs
open RepTheorySurvey.Invariants.Specs.TorusWeights
open LinearAlgebraicGroups (specGroup)
open LinearAlgebraicGroups.WeightDecomposition (weightSpace tensorCoactionMap)

abbrev Characters (r : ℕ) := Multiplicative (Labels r)

/-- The coordinate Hopf algebra of the dual torus is the group algebra of
the additive coweight lattice, written multiplicatively. -/
abbrev coordinateAlgebra (r : ℕ) := coordinates ℚ (Characters r)

abbrev dualTorus (r : ℕ) := specGroup (coordinateAlgebra r)

/-- Finite-dimensional algebraic representations of this affine group scheme
in the right-comodule model over its coordinate Hopf algebra. -/
abbrev Representations (r : ℕ) := FiniteComodule ℚ (Characters r)

abbrev underlying (r : ℕ) : Representations r ⥤ Coeff.{0} :=
  forgetComodule

def weightAt {r : ℕ} (X : Representations r) (a : Labels r) : Coeff.{0} :=
  ModuleCat.of ℚ (weightSpace X.coaction (Multiplicative.ofAdd a))

def weightInclusion {r : ℕ} (X : Representations r) (a : Labels r) :
    weightAt X a ⟶ (underlying r).obj X :=
  ModuleCat.ofHom (weightSpace X.coaction (Multiplicative.ofAdd a)).subtype

/-- The representation tensor product is the ordinary vector-space tensor
product with coaction induced by multiplication in the coordinate algebra.
The unit has the trivial coaction. The braided forgetful functor identifies
the constraints with the ordinary linear associator, unitors and flip. -/
structure RepresentationTensor (r : ℕ) where
  monoidal : MonoidalCategory (Representations r)
  symmetric : @SymmetricCategory (Representations r) _ monoidal
  forgetBraided :
    letI := monoidal
    letI := symmetric
    (underlying r).Braided
  tensorCoaction :
    letI := monoidal
    letI := symmetric
    letI := forgetBraided
    ∀ (X Y : Representations r),
      ((X ⊗ Y).coaction.coaction).comp (LaxMonoidal.μ (underlying r) X Y).hom =
        ((LaxMonoidal.μ (underlying r) X Y).hom.rTensor (coordinateAlgebra r)).comp
          (tensorCoactionMap X.coaction Y.coaction)
  unitCoaction :
    letI := monoidal
    letI := symmetric
    letI := forgetBraided
    ∀ x : (𝟙_ Coeff.{0}),
      (𝟙_ (Representations r)).coaction.coaction ((LaxMonoidal.ε (underlying r)).hom x) =
        (LaxMonoidal.ε (underlying r)).hom x ⊗ₜ[ℚ] MonoidAlgebra.of ℚ (Characters r) 1

/-- Global sections of the degree-zero cohomology sheaf. -/
def globalSections (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    Heart r g c ⥤ Coeff.{0} :=
  forgetPerverse r g c ⋙ cohomology (torusSpace r) 0 ⋙ sectionsOn ⊤

instance coeffDerivedCategory : HasDerivedCategory.{1} Coeff.{0} :=
  HasDerivedCategory.standard _

/-- Hypercohomology as the right-derived functor of sections on the whole space. -/
def derivedGlobalSections (r : ℕ) :
    BoundedBelow (torusSpace r) ⥤ DerivedCategory.Plus Coeff.{0} :=
  (sectionsOn (⊤ : TopologicalSpace.Opens (torusSpace r))).rightDerivedFunctorPlus

def globalGerm {r : ℕ} {g : StageGeometry r} {c : ContinuousJets r}
    (V : Heart r g c) (a : Labels r) :
    (globalSections r g c).obj V ⟶ OrderedProduct.Stalk V a :=
  ((cohomology (torusSpace r) 0).obj ((forgetPerverse r g c).obj V)).presheaf.germ
    ⊤ (monomialPoint r a) (by simp)

abbrev StalkSum {r : ℕ} {g : StageGeometry r} {c : ContinuousJets r} (V : Heart r g c) :
    Coeff.{0} :=
  ModuleCat.of ℚ (⨁ a : Labels r, OrderedProduct.Stalk V a)

/-- The global section from one stalk, under the direct-sum comparison. -/
def stalkSection {r : ℕ} {g : StageGeometry r} {c : ContinuousJets r}
    {V : Heart r g c} (s : StalkSum V ≅ (globalSections r g c).obj V) (a : Labels r) :
    OrderedProduct.Stalk V a ⟶ (globalSections r g c).obj V :=
  ModuleCat.ofHom (DirectSum.lof ℚ (Labels r) (fun b ↦ (OrderedProduct.Stalk V b : Type)) a) ≫ s.hom

variable {r : ℕ} {g : StageGeometry r} {c : ContinuousJets r} {D : OrderedGeometry r}
  {P : OrderedProduct D g c} {U : OrderedConstraints P} {σ : SwapsConvolution P}

/-- A symmetric monoidal equivalence on the given geometric convolution heart,
with its stalk and hypercohomology comparisons. -/
structure SatakeEquivalence (S : SymmetricConvolution U σ) where
  representationTensor : RepresentationTensor r
  equivalence : Heart r g c ≌ Representations r
  braided :
    letI := S.monoidal
    letI := S.symmetric
    letI := representationTensor.monoidal
    letI := representationTensor.symmetric
    equivalence.functor.Braided
  stalkWeight : ∀ (V : Heart r g c) (a : Labels r),
    OrderedProduct.Stalk V a ≅ weightAt (equivalence.functor.obj V) a
  stalkWeight_naturality : ∀ {V W : Heart r g c} (f : V ⟶ W) (a : Labels r),
    ((stalkFamily r g c).map f).app (Discrete.mk a) ≫
        (stalkWeight W a).hom ≫ weightInclusion (equivalence.functor.obj W) a =
      (stalkWeight V a).hom ≫ weightInclusion (equivalence.functor.obj V) a ≫
        (underlying r).map (equivalence.functor.map f)
  boundedBelow : Heart r g c ⥤ BoundedBelow (torusSpace r)
  boundedBelowComparison : boundedBelow ⋙ DerivedCategory.Plus.ι ≅ forgetPerverse r g c
  derivedComparison :
    boundedBelow ⋙ derivedGlobalSections r ≅
      globalSections r g c ⋙ DerivedCategory.Plus.singleFunctor Coeff.{0} 0
  sumIso : ∀ V : Heart r g c, StalkSum V ≅ (globalSections r g c).obj V
  sumIso_germ : ∀ (V : Heart r g c) (a : Labels r),
    (sumIso V).inv ≫ ModuleCat.ofHom
      (DirectSum.component ℚ (Labels r) (fun b : Labels r ↦ (OrderedProduct.Stalk V b : Type)) a) = globalGerm V a
  globalBraided :
    letI := S.monoidal
    letI := S.symmetric
    (globalSections r g c).Braided
  fiberIso : globalSections r g c ≅ equivalence.functor ⋙ underlying r
  fiberIso_weight : ∀ (V : Heart r g c) (a : Labels r),
    stalkSection (sumIso V) a ≫ fiberIso.hom.app V =
      (stalkWeight V a).hom ≫ weightInclusion (equivalence.functor.obj V) a
  fiberIso_monoidal :
    letI := S.monoidal
    letI := S.symmetric
    letI := representationTensor.monoidal
    letI := representationTensor.symmetric
    letI := braided
    letI := representationTensor.forgetBraided
    letI := globalBraided
    NatTrans.IsMonoidal fiberIso.hom
  globalUnit :
    letI := S.monoidal
    letI := S.symmetric
    letI := globalBraided
    let e : U.unit = 𝟙_ (Heart r g c) :=
      (congrArg (fun M : MonoidalCategoryStruct (Heart r g c) ↦ M.tensorUnit) S.ordered).symm
    let scalar : (𝟙_ Coeff.{0}) ⟶ OrderedProduct.Stalk U.unit 0 :=
      eqToHom (by simp [pointUnit]) ≫ U.unitStalk.inv.app (Discrete.mk 0)
    scalar ≫ stalkSection (sumIso U.unit) 0 ≫ (globalSections r g c).map (eqToHom e) =
      LaxMonoidal.ε (globalSections r g c)
  globalTensor :
    letI := S.monoidal
    letI := S.symmetric
    letI := globalBraided
    ∀ (V W : Heart r g c) (a b : Labels r),
      let e : V ⊗ W = P.convolution.obj (V, W) :=
        congrArg (fun M : MonoidalCategoryStruct (Heart r g c) ↦ M.tensorObj V W) S.ordered
      (stalkSection (sumIso V) a ⊗ₘ stalkSection (sumIso W) b) ≫
          LaxMonoidal.μ (globalSections r g c) V W ≫
          (globalSections r g c).map (eqToHom e) =
        P.includeSummand V W a b ≫ stalkSection (sumIso (P.convolution.obj (V, W))) (a + b)

/-- Geometric Satake for every complex split torus, including rank zero. The
geometric commutor comes from the specialization of the two-point exchange. -/
def TorusSatake : Prop :=
  ∀ r : ℕ,
    Nonempty (dualTorus r ≅
      (LinearAlgebraicGroups.Specs.StandardGroups.multiplicativePowerGroup ℚ (Fin r)).val) ∧
    ∃ (D : OrderedGeometry r) (g : StageGeometry r) (c : ContinuousJets r)
      (P : OrderedProduct D g c) (U : OrderedConstraints P) (σ : SwapsConvolution P)
      (S : SymmetricConvolution U σ),
      FlipsConvolutionSummands P σ ∧ LocalGeometry D ∧
      (∀ (A B : Set (Labels r)), A.Finite → B.Finite →
        ∃ (N : ℕ) (G : SectionGeometry N A B) (H : SectionGeometry N B A)
          (J : SectionExchange G H) (E : CoefficientExchange D J),
          ClearsPoles N A B ∧ SpecializesToConvolution σ E) ∧
      Nonempty (SatakeEquivalence S)

end RepTheorySurvey.Geometric.TorusSatakeSpecs
