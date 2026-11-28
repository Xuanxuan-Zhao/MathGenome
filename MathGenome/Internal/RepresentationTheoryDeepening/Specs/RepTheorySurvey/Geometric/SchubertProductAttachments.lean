import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SchubertProjectionBaseChange
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedPullbackPasting

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Pretriangulated TopologicalSpace Topology

namespace RepTheorySurvey.Geometric.SchubertProductAttachmentsSpecs

open Analytic Analytic.IntersectionComplex
open Analytic.DerivedPullbackPasting.Expected (squareValue)
open LatticeModelSpecs SchubertIntersectionConstructibilitySpecs

def productMap (T : TopCat.{0}) {U X : TopCat.{0}} (j : U ⟶ X) :
    TopCat.of (T × U) ⟶ TopCat.of (T × X) :=
  TopCat.ofHom ⟨fun p => (p.1, j p.2), continuous_fst.prodMk
    (j.hom.continuous.comp continuous_snd)⟩

def productProjection (T X : TopCat.{0}) : TopCat.of (T × X) ⟶ X :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

theorem productMap_open (T : TopCat.{0}) {U X : TopCat.{0}} {j : U ⟶ X}
    (hj : IsOpenEmbedding j) : IsOpenEmbedding (productMap T j) :=
  IsOpenEmbedding.id.prodMap hj

theorem projectionSquare (T : TopCat.{0}) {U X : TopCat.{0}} (j : U ⟶ X) :
    productMap T j ≫ productProjection T X = productProjection T U ≫ j :=
  TopCat.ext (fun _ => rfl)

namespace Expected

/-- Smooth projection with its dimension shift preserves an actual Schubert IC
attachment and the identification of its restriction to the preceding stage. -/
def ShiftedProductAttachment : Prop :=
  ∀ (T : TopCat.{0}) (e : ℕ),
    (∃ V : Opens (Fin e → ℂ), Nonempty (T ≃ₜ V)) →
    ∀ (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N) (k : ℕ)
      {U X : TopCat.{0}} (j : U ⟶ X) (hj : IsOpenEmbedding j)
      (f : X ⟶ SchubertSpace ab N hN) (Q : Stratification U) (P : Stratification X)
      {d : ℕ} (D : DimensionFiltration U d),
      IsNormalizedOrbitIC ab N hN (j ≫ f) k Q D →
      RealizesOrbitStage f (k + 1) P →
      let s := orbitDimension ab (k + 1)
      let F := complex D
      ∀ (_ : AttachmentStratification j s Q P),
        IsConstructibleOnBoundary j ((derivedDirectImage j).obj F) →
        let jT := productMap T j
        let pX := productProjection T X
        let pU := productProjection T U
        let n : ℤ := e
        ∀ (QT : Stratification (TopCat.of (T × U)))
          (PT : Stratification (TopCat.of (T × X)))
          (_ : AttachmentStratification jT (s + e) QT PT)
          (G : BoundedBelow (TopCat.of (T × U))),
          IsMiddlePerverse QT G.obj →
          ∀ (g : ((derivedInverseImage pU).obj F.obj)⟦n⟧ ≅ G.obj)
            (a : boundedBelowInverseImage jT ⊣ derivedDirectImage jT)
            (b : boundedBelowInverseImage j ⊣ derivedDirectImage j),
            let E := (attachment j hj s).obj F
            let ET := (attachment jT (productMap_open T hj) (s + e)).obj G
            let r : (boundedBelowInverseImage j).obj E ⟶ F :=
              (boundedBelowInverseImage j).map ((attachmentInclusion j hj s).app F) ≫
                b.counit.app F
            let rT : (boundedBelowInverseImage jT).obj ET ⟶ G :=
              (boundedBelowInverseImage jT).map
                ((attachmentInclusion jT (productMap_open T hj) (s + e)).app G) ≫
                a.counit.app G
            IsMiddlePerverse PT ET.obj ∧
              IsStrictExtension (productMap_open T hj) (s + e) ET ∧ IsIso rT ∧
              ∃ c : ((derivedInverseImage pX).obj E.obj)⟦n⟧ ≅ ET.obj,
                (derivedInverseImage jT).map c.hom ≫ rT.hom =
                  ((inverseImage jT).mapDerivedCategory.commShiftIso n).hom.app
                    ((derivedInverseImage pX).obj E.obj) ≫
                  (shiftFunctor (Derived (TopCat.of (T × U))) n).map
                    ((squareValue (projectionSquare T j)).hom.app E.obj ≫
                      (derivedInverseImage pU).map r.hom) ≫ g.hom

end Expected
end RepTheorySurvey.Geometric.SchubertProductAttachmentsSpecs
