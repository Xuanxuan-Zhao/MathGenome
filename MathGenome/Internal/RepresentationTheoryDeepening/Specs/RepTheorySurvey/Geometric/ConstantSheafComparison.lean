import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedLocalSheaves
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SmallCochainComparison
import Mathlib.Algebra.Homology.HomologySequence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open P202Specs.CohomologyPairs P202Specs.RelativeSingularChains

universe u

namespace RepTheorySurvey.Geometric.Analytic.ConstantSheafCohomology

open SingularCochains

/-- The ordinary singular pair consisting of an open and an open subspace of it.
The closed support is the complement of the subspace in the open. Every closed
subset of the larger open arises this way, since its complement is open in the
ambient space. -/
def openPair {X : TopCat.{u}} {V U : Opens X} (_ : V ⟶ U) : Pair.{u} :=
  ⟨TopCat.of U, Subtype.val ⁻¹' (V : Set X)⟩

/-- Identify the second space of the singular pair with the given smaller open. -/
def subspaceIso {X : TopCat.{u}} {V U : Opens X} (i : V ⟶ U) :
    TopCat.of V ≅ (openPair i).sub where
  hom := TopCat.ofHom ⟨fun x => ⟨⟨x.val, i.le x.property⟩, x.property⟩,
    (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
  inv := TopCat.ofHom ⟨fun x => ⟨x.val.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; rfl

/-- The inclusion of one open pair into another, given the two open inclusions. -/
def openPairInclusion {X : TopCat.{u}} {V U V' U' : Opens X}
    (i : V ⟶ U) (i' : V' ⟶ U') (j : U ⟶ U') (k : V ⟶ V') :
    openPair i ⟶ openPair i' :=
  ⟨(Opens.toTopCat X).map j, fun _ hx => k.le hx⟩

/-- The actual kernel sequence for restriction of sections of a complex of sheaves. -/
abbrev sectionSequence {X : TopCat.{u}} (K : CochainComplex (Sheaves X) ℤ)
    {V U : Opens X} (i : V ⟶ U) : ShortComplex (CochainComplex Coeff.{u} ℤ) :=
  ShortComplex.kernelSequence ((LocalSheaf.openSectionComplexes K).map i.op)

set_option maxHeartbeats 300000 in
/-- Restriction of the section sequences, acting on supported sections by the induced
map of kernels. -/
def sectionSequenceRestriction {X : TopCat.{u}} (K : CochainComplex (Sheaves X) ℤ)
    {V U V' U' : Opens X} (i : V ⟶ U) (i' : V' ⟶ U')
    (j : U ⟶ U') (k : V ⟶ V') : sectionSequence K i' ⟶ sectionSequence K i := by
  let F := LocalSheaf.openSectionComplexes K
  have h : F.map i'.op ≫ F.map k.op = F.map j.op ≫ F.map i.op := by
    rw [← F.map_comp, ← F.map_comp]
    congr 1
  exact ShortComplex.Hom.mk (kernel.map _ _ (F.map j.op) (F.map k.op) h)
    (F.map j.op) (F.map k.op) (by simp) h.symm

/-- The constant rational sheaf as a bounded-below cochain complex in degree zero. -/
abbrev rationalComplex (X : TopCat.{u}) : CochainComplex.Plus (Sheaves X) :=
  ⟨(CochainComplex.singleFunctor (Sheaves X) 0).obj (rational X), 0, inferInstance⟩

namespace Expected

/-- The comparison stated on the complexes computing cohomology in all integer
degrees. The augmentation identifies the sheaf complex with the constant sheaf.
The right-derived units identify its ordinary and supported section complexes
with the corresponding derived sections. The maps of the actual short exact
sequences identify absolute, relative, and connecting cohomology maps. -/
def Comparison : Prop :=
  ∀ (X : TopCat.{u}) [SecondCountableTopology X] [LocallyCompactSpace X] [T2Space X],
    HasContractibleOpenBasis X →
    ∃ hn : (sheafComplex X).IsStrictlyGE 0,
      let K : CochainComplex.Plus (Sheaves X) := ⟨sheafComplex X, 0, hn⟩
      let a : rationalComplex X ⟶ K := ObjectProperty.homMk (augmentation X)
      IsIso (DerivedCategory.Plus.Q.map a) ∧
      (∀ U : Opens X, QuasiIso (sectionMap U) ∧
        IsIso ((sectionsOn U).rightDerivedFunctorPlusUnit.app K)) ∧
      (∀ {V U : Opens X} (i : V ⟶ U),
        (ordinaryCochainFunctor ℚ Values.{u}).map ((Opens.toTopCat X).map i).op ≫ sectionMap V =
          sectionMap U ≫ SmallCochains.sectionsRestriction i) ∧
      (∀ {Z : Set X} (hZ : IsClosed Z) (U : Opens X),
        let i : U ⊓ complementOpen Z hZ ⟶ U := homOfLE inf_le_left
        let T := LocalSheaf.supportedSectionsOn hZ U
        IsIso (T.rightDerivedFunctorPlusUnit.app K) ∧
          ∃ e : (T.mapCochainComplexPlus.obj K).obj ≅ (sectionSequence K.obj i).X₁,
            e.hom ≫ (sectionSequence K.obj i).f =
              ((LocalSheaf.supportedSectionsInclusion hZ U).mapCochainComplexPlus.app K).hom) ∧
      ∃ (hSing : ∀ {V U : Opens X} (i : V ⟶ U),
          (cochainSequence ℚ Values.{u} (openPair i)).ShortExact)
        (hSh : ∀ {V U : Opens X} (i : V ⟶ U), (sectionSequence K.obj i).ShortExact)
        (φ : ∀ {V U : Opens X} (i : V ⟶ U),
          cochainSequence ℚ Values.{u} (openPair i) ⟶ sectionSequence K.obj i),
        (∀ {V U : Opens X} (i : V ⟶ U),
          (φ i).τ₂ = sectionMap U ∧
          (φ i).τ₃ = (ordinaryCochainFunctor ℚ Values.{u}).map (subspaceIso i).hom.op ≫
            sectionMap V ∧
          QuasiIso (φ i).τ₁ ∧ QuasiIso (φ i).τ₂ ∧ QuasiIso (φ i).τ₃ ∧
          ∀ q : ℤ,
            (hSing i).δ q (q + 1) rfl ≫ HomologicalComplex.homologyMap (φ i).τ₁ (q + 1) =
              HomologicalComplex.homologyMap (φ i).τ₃ q ≫ (hSh i).δ q (q + 1) rfl) ∧
        (∀ {V U V' U' : Opens X} (i : V ⟶ U) (i' : V' ⟶ U')
            (j : U ⟶ U') (k : V ⟶ V'),
          cochainSequenceMap ℚ Values.{u} (openPairInclusion i i' j k) ≫ φ i =
            φ i' ≫ sectionSequenceRestriction K.obj i i' j k)

end Expected
end RepTheorySurvey.Geometric.Analytic.ConstantSheafCohomology
