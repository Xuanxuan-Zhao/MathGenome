import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.RelativeWeylScheme
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.SimpleParabolicProduct

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Relative.RelativeBruhat

open GeometricRadicals (IsReductive)
open MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open RelativeWeylScheme (QuotientData rationalProjection)
open SchemeDerivedGroup (IsSubgroupOf)
open SimpleParabolicProduct (doubleCoset)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- The multiplication morphism whose fppf image is the indicated double orbit. -/
def doubleOrbitMap (P : ClosedSubgroup G.val) (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
    P.group.X ⊗ P.group.X ⟶ G.val.X :=
  (fst _ _ ≫ P.inclusion.hom.hom) * (toUnit _ ≫ n) * (snd _ _ ≫ P.inclusion.hom.hom)

/-- A locally closed representative of the fppf image of the double-orbit map.
The fppf projection ensures that its points admit local factorizations. -/
structure DoubleOrbit (P : ClosedSubgroup G.val) (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) where
  scheme : SchemeOver k
  inclusion : scheme ⟶ G.val.X
  immersion : IsImmersion inclusion.left
  projection : P.group.X ⊗ P.group.X ⟶ scheme
  factors : projection ≫ inclusion = doubleOrbitMap P n
  flat : Flat projection.left
  surjective : Surjective projection.left
  finitePresentation : LocallyOfFinitePresentation projection.left

/-- Relative Bruhat decomposition over an arbitrary field. The finite constant
scheme quotient and the quotient of rational points give the same labels. The
rational double cosets cover the rational points, and their fppf double-orbit
schemes are locally closed and pairwise disjoint. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (S P : ClosedSubgroup G.val), IsMaximalSplitTorus S →
      IsMinimalParabolic G P → IsSubgroupOf S P →
      ∃ D : QuotientData S,
        let W := D.splitImage.labels
        let Z := MonoidHom.range (IsMonHom.monoidHom D.inclusion.hom.hom (𝟙_ (SchemeOver k)))
        ∃ (_ : Z.Normal) (e : (𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X) ⧸ Z ≃* W),
          (∀ n, rationalProjection D n =
            D.splitImage.constantGroup.sectionPoint (e (QuotientGroup.mk n))) ∧
          (∀ w : W, ∃ n, rationalProjection D n = D.splitImage.constantGroup.sectionPoint w) ∧
          ∀ n : W → (𝟙_ (SchemeOver k) ⟶ D.normalizer.group.X),
            (∀ w, rationalProjection D (n w) = D.splitImage.constantGroup.sectionPoint w) →
            let g := fun w ↦ n w ≫ D.normalizer.inclusion.hom.hom
            let C := fun w ↦ doubleCoset P (𝟙_ (SchemeOver k)) (g w)
            (⋃ w, C w) = Set.univ ∧ Pairwise (fun w v ↦ Disjoint (C w) (C v)) ∧
            ∃ O : ∀ w, DoubleOrbit P (g w),
              Pairwise (fun w v ↦ Disjoint (Set.range (O w).inclusion.left)
                (Set.range (O v).inclusion.left))

end

end LinearAlgebraicGroups.Specs.Relative.RelativeBruhat
