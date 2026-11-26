import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.FlagCovarianceLinearization

open CharacterDescent (Character)
open AdjointRepresentation (GroupPoints)
open EquivariantAffineModules FlagCohomology
open FlagLineBundle (OppositeBorelPair BorelProjection)
open QuotientEmbedding (Presentation)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}

abbrev torusAction {Q : SchemeOver k} (a : ModObj G.val.X Q) : ModObj P.torus.group.X Q :=
  letI := a
  Mod.scalarRestriction P.torus.inclusion.hom.hom Q

/-- The scalar coordinate obtained by adjunction from inclusion into regular
functions on the quotient torsor, evaluated on a specified lift. -/
def flagLineCoordinate
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q) {Z : SchemeOver k} (g : Z ⟶ G.val.X) :
    Pull (g ≫ Q.projection) (flagLineSheaf Q p χ h) ⟶ structureModule Z.left :=
  let D := flagLineData Q p χ h
  let e := ((Scheme.Modules.pullbackPushforwardAdjunction Q.projection.left).homEquiv
    D.sheaf (structureModule G.val.X.left)).symm D.inclusion
  (pullComp D.sheaf g Q.projection).inv ≫ (Scheme.Modules.pullback g.left).map e ≫
    ((Scheme.Modules.pullbackPushforwardAdjunction g.left).homEquiv
      (structureModule G.val.X.left) (structureModule Z.left)).symm (pullbackRegular g.left)

/-- Transport in the associated line preserves the coordinate when the
torsor lift is translated by the same torus point. -/
def PreservesFlagLineCoordinate
    (Q : Presentation P.negative) (a : ModObj G.val.X Q.scheme)
    (p : BorelProjection P) (χ : Character P.torus.group) (h : FlagKernelPair Q)
    (ℓ : Linearization (torusAction (P := P) a) (flagLineSheaf Q p χ h)) : Prop :=
  ∀ (Z : SchemeOver k) (t : Z ⟶ P.torus.group.X) (g : Z ⟶ G.val.X),
    let aT := torusAction (P := P) a
    let F := flagLineSheaf Q p χ h
    let g' := lift (t ≫ P.torus.inclusion.hom.hom) g ≫ μ[G.val.X]
    ∃ w : actOn aT t (g ≫ Q.projection) = g' ≫ Q.projection,
      (transport aT ℓ.iso t (g ≫ Q.projection)).hom ≫
        (pullCongr F w).hom ≫ flagLineCoordinate Q p χ h g' =
        flagLineCoordinate Q p χ h g

/-- On every scalar extension, inverse point translation and inverse fiber
transport determine a coefficient map on the extended flag. Its derived
action in the extended cohomology basis is the existing point action. -/
def AgreesWithFlagCohomologyAction
    (Q : Presentation P.negative) (a : ModObj G.val.X Q.scheme)
    (p : BorelProjection P) (χ : Character P.torus.group) (h : FlagKernelPair Q)
    (ℓ : Linearization (torusAction (P := P) a) (flagLineSheaf Q p χ h)) : Prop :=
  ∀ (R : TestAlgebra k) (t : GroupPoints P.torus.group R)
    (E : (flagLineData Q p χ h).ScalarExtension R),
    let g : GroupPoints G.val R := t ≫ P.torus.inclusion.hom.hom
    let Y := (extendScheme R).obj Q.scheme
    let D := (flagLineData Q p χ h).extend R
    let F := flagLineSheaf Q p χ h
    let Yk := (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k R)))).obj Y
    let x : Yk ⟶ Q.scheme :=
      Over.homMk (extensionProjection R Q.scheme) (extensionProjection_over R Q.scheme)
    let y : Yk ⟶ (testSpec k).obj (op R) := Over.homMk Y.hom
    let fR : Y ⟶ Y := Over.homMk (pointTranslation a.smul R g⁻¹) (by
      have q := pointTranslation_over a.smul R g⁻¹
      rw [show Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 _ from Spec.map_id _,
        Category.comp_id] at q
      exact q)
    let f : Yk ⟶ Yk :=
      (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k R)))).map fR
    let aT := torusAction (P := P) a
    let e : Pull x F ≅ D.sheaf :=
      @asIso _ _ _ _ _ E.sheafIso
    ∃ w : f ≫ x = actOn aT (y ≫ t⁻¹) x,
      let c : Pull f D.sheaf ⟶ D.sheaf :=
        (Scheme.Modules.pullback f.left).map e.inv ≫ (pullComp F f x).hom ≫
          (pullCongr F w).hom ≫ (transport aT ℓ.iso (y ≫ t⁻¹) x).inv ≫ e.hom
      let α := ((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv
        D.sheaf D.sheaf) c
      ∀ (n : ℕ),
        ∃ m : (cohomology Y n).obj D.sheaf ⟶ (cohomology Y n).obj D.sheaf,
          IsCohomologyMap (RingHom.id R) f.left (pointTranslation_over a.smul R g⁻¹) α n
            (m ≫ (ModuleCat.restrictScalarsId'App (RingHom.id R) rfl _).inv) ∧
          ∀ (b : CohomologyBasis (p := p) (χ := χ) h n)
            (ρ : RootWeightAction.Representation G.val (CohomologyIndex (p := p) (χ := χ) h n)),
            IsFlagCohomologyAction h a n b ρ →
            ∀ v, extendedCoordinates R b ((E.iso n).inv (m v)) =
              RootWeightAction.act ρ R g (extendedCoordinates R b ((E.iso n).inv v))

/-- The inverse-character covariance sheaf on the actual flag has the
associated torus linearization, in every characteristic and for every
torus character. -/
def FlagCovarianceLinearizationStatement : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (a : ModObj G.val.X Q.scheme)
    (p : BorelProjection P) (χ : Character P.torus.group) (h : FlagKernelPair Q),
    μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    ∃ ℓ : Linearization (torusAction (P := P) a) (flagLineSheaf Q p χ h),
      PreservesFlagLineCoordinate Q a p χ h ℓ ∧ AgreesWithFlagCohomologyAction Q a p χ h ℓ

end

end LinearAlgebraicGroups.Specs.FlagCovarianceLinearization
