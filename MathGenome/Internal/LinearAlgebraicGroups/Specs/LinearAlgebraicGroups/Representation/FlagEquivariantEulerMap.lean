import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.DatumAndWeyl

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.FlagEquivariantEulerMap

open AbstractPairing (Datum)
open AdjointRepresentation (GroupPoints)
open CharacterPairing (characterValue)
open CharacterDescent (Character)
open DatumAndWeyl (Identification)
open EquivariantAffineModules
open FlagCohomology (cohomology IsCohomologyMap structureModule)
open FlagLineBundle (OppositeBorelPair BorelProjection AssociatedBundle affineLine linePoint)
open QuotientEmbedding (Presentation)

noncomputable section

variable {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}

/-- The derived map induced by pullback followed by a morphism of
coefficients. -/
def InducesOnCohomology (f : Y ⟶ X) {F : X.left.Modules} {H : Y.left.Modules}
    (c : Pull f F ⟶ H) (n : ℕ) (m : (cohomology X n).obj F ⟶ (cohomology Y n).obj H) :
    Prop :=
  IsCohomologyMap (RingHom.id k) f.left (by
    rw [show Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _ from Spec.map_id _,
      Category.comp_id]
    exact Over.w f)
    ((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv F H c) n
    (m ≫ (ModuleCat.restrictScalarsId'App (RingHom.id k) rfl _).inv)

/-- The projection with covariant transport and the action give maps into the
same cohomology group on the product with the acting group scheme. -/
structure CohomologyPullbacks {a : ModObj T.X X} (F : EquivariantCoherent a) (n : ℕ) where
  viaProjection : (cohomology X n).obj F.sheaf ⟶
    (cohomology (T.X ⊗ X) n).obj (Pull a.smul F.sheaf)
  viaAction : (cohomology X n).obj F.sheaf ⟶
    (cohomology (T.X ⊗ X) n).obj (Pull a.smul F.sheaf)
  projection_induced : InducesOnCohomology (snd T.X X) F.lin.iso.hom n viaProjection
  action_induced : InducesOnCohomology a.smul (𝟙 _) n viaAction

/-- A weight is tested over the universal element of the torus. -/
def cohomologyWeightSpace {a : ModObj T.X X} {F : EquivariantCoherent a} {n : ℕ}
    (m : CohomologyPullbacks F n) (χ : Character T) :
    Submodule k ((cohomology X n).obj F.sheaf) :=
  LinearMap.ker (m.viaProjection.hom -
    ((cohomology (T.X ⊗ X) n).map (multiply _
      ((fst T.X X).left.appTop (characterFunction χ)))).hom.comp m.viaAction.hom)

def IsCohomologyCharacter {a : ModObj T.X X} (F : EquivariantCoherent a)
    (n : ℕ) (c : CharacterRing T) : Prop :=
  Module.Finite k ((cohomology X n).obj F.sheaf) ∧
    ∃ m : CohomologyPullbacks F n,
      ∀ χ, c.coeff χ = (Module.finrank k (cohomologyWeightSpace m χ) : ℤ)

def IsEulerCharacter {a : ModObj T.X X} (F : EquivariantCoherent a)
    (c : CharacterRing T) : Prop :=
  ∃ (N : ℕ) (ch : ℕ → CharacterRing T),
    (∀ n, IsCohomologyCharacter F n (ch n)) ∧
    (∀ n ≥ N, IsZero ((cohomology X n).obj F.sheaf)) ∧
    c = ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n • ch n

/-- The trivial action on the terminal scheme over the field. -/
abbrev terminalAction (T : GroupScheme k) := ModObj.trivialAction T.X (𝟙_ (SchemeOver k))

/-- The ordinary fiber of the given linearized sheaf has the specified
character. -/
def IsFiberCharacter {a : ModObj T.X X} (x : 𝟙_ (SchemeOver k) ⟶ X)
    (F : EquivariantCoherent a) (c : CharacterRing T) : Prop :=
  ∃ (H : EquivariantCoherent (terminalAction T)) (e : Pull x F.sheaf ≅ H.sheaf),
    IsEquivariantPullback x F H e ∧ IsCohomologyCharacter H 0 c

/-- A point class is represented by the equivariant direct image of the
structure sheaf with its trivial linearization. -/
def IsPointClass {a : ModObj T.X X} (x : 𝟙_ (SchemeOver k) ⟶ X)
    (F : EquivariantCoherent a) : Prop :=
  ∃ (H : EquivariantCoherent (terminalAction T))
    (_ : H.sheaf ≅ structureModule (𝟙_ (SchemeOver k) : SchemeOver k).left)
    (e : F.sheaf ≅ (Scheme.Modules.pushforward x.left).obj H.sheaf),
      H.lin.iso.hom = (pullCongr H.sheaf (rfl : snd T.X _ = (terminalAction T).smul)).hom ∧
      IsEquivariantPushforward x H F e

abbrev torusAction {G : AffineAlgebraicGroup k} (S : ClosedSubgroup G.val)
    (a : ModObj G.val.X X) : ModObj S.group.X X :=
  letI := a
  Mod.scalarRestriction S.inclusion.hom.hom X

/-- Existence of the character-ring linear Euler map on the actual flag,
with the normalization on equivariant direct images from rational fixed
closed sections. -/
def FlagEulerMap : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G)
    (Q : Presentation P.negative) (a : ModObj G.val.X Q.scheme),
    μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    let t := torusAction P.torus a
    ∃ euler : GZero t →ₗ[CharacterRing P.torus.group] CharacterRing P.torus.group,
      (∀ F, IsEulerCharacter F (euler (classOf F))) ∧
      (∀ (x : 𝟙_ (SchemeOver k) ⟶ Q.scheme) (F : EquivariantCoherent t),
        IsClosedImmersion x.left → IsEquivariantMap t (terminalAction P.torus.group) x →
        IsPointClass x F → euler (classOf F) = 1)

/-- A chosen rational representative maps to the Weyl section given by the
identification of the normalizer quotient. -/
abbrev RepresentsWeylElement {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    [IsCommMonObj P.torus.group.X] {D : Datum P.torus}
    (J : Identification D) (w : D.rootDatum.weylGroup)
    (n : 𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X) : Prop :=
  n ≫ J.quotient.hom.hom = J.image.constantGroup.sectionPoint (J.labelEquiv w)

/-- A pullback of the covariance sheaf to a lift in the flag torsor has
a scalar coordinate given by the inclusion into functions on the torsor. -/
def flagLineCoordinate {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagCohomology.FlagKernelPair Q) {Z : SchemeOver k} (g : Z ⟶ G.val.X) :
    Pull (g ≫ Q.projection) (FlagCohomology.flagLineSheaf Q p χ h) ⟶ structureModule Z.left :=
  let D := FlagCohomology.flagLineData Q p χ h
  let e := ((Scheme.Modules.pullbackPushforwardAdjunction Q.projection.left).homEquiv
    D.sheaf (structureModule G.val.X.left)).symm D.inclusion
  (pullComp D.sheaf g Q.projection).inv ≫ (Scheme.Modules.pullback g.left).map e ≫
    ((Scheme.Modules.pullbackPushforwardAdjunction g.left).homEquiv
      (structureModule G.val.X.left) (structureModule Z.left)).symm
      (FlagCohomology.pullbackRegular g.left)

/-- In torsor coordinates the associated left action transports the scalar
unchanged while translating the lifted point by the torus element. -/
def IsFlagLineBundleTransport {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (a : ModObj G.val.X Q.scheme)
    (p : BorelProjection P) (χ : Character P.torus.group) (h : FlagCohomology.FlagKernelPair Q)
    (ℓ : Linearization (torusAction P.torus a) (FlagCohomology.flagLineSheaf Q p χ h)) : Prop :=
  ∀ (Z : SchemeOver k) (t : Z ⟶ P.torus.group.X) (g : Z ⟶ G.val.X),
    let aT := torusAction P.torus a
    let F := FlagCohomology.flagLineSheaf Q p χ h
    let g' := lift (t ≫ P.torus.inclusion.hom.hom) g ≫ μ[G.val.X]
    ∃ w : actOn aT t (g ≫ Q.projection) = g' ≫ Q.projection,
      (transport aT ℓ.iso t (g ≫ Q.projection)).hom ≫
        (pullCongr F w).hom ≫ flagLineCoordinate Q p χ h g' =
        flagLineCoordinate Q p χ h g

/-- The torus linearization on the covariance sheaf has the prescribed Weyl
fiber character and gives the same cohomology characters as the actual
left-translation action on the associated line bundle. -/
def FlagLineBundleCharacters : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (a : ModObj G.val.X Q.scheme)
    (p : BorelProjection P) (χ : Character P.torus.group) (h : FlagCohomology.FlagKernelPair Q),
    μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    let t := torusAction P.torus a
    let F := FlagCohomology.flagLineSheaf Q p χ h
    ∃ (hF : F.IsFinitePresentation) (ℓ : Linearization t F),
      let L : EquivariantCoherent t := ⟨F, hF, ℓ⟩
      IsFlagLineBundleTransport Q a p χ h ℓ ∧
      (∀ (i : ℕ) (b : FlagCohomology.CohomologyBasis (p := p) (χ := χ) h i)
            (ρ : RootWeightAction.Representation G.val
              (FlagCohomology.CohomologyIndex (p := p) (χ := χ) h i)),
        FlagCohomology.IsFlagCohomologyAction h a i b ρ →
          IsCohomologyCharacter L i (FormalCharacters.formalCharacter P.torus ρ)) ∧
        (∀ [IsCommMonObj P.torus.group.X] {D : Datum P.torus} (J : Identification D)
            (w : D.rootDatum.weylGroup) (n : 𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X),
          RepresentsWeylElement J w n →
          IsFiberCharacter (n ≫ J.normalizer.inclusion.hom.hom ≫ Q.projection) L
            (eChar ((J.labelEquiv w).val χ)))


/-- In the coordinate given by the chosen representative, torus transport
on the actual associated bundle is scalar multiplication by the Weyl
translate, on points over every test algebra. -/
def WeylFiberTransport : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    [IsCommMonObj P.torus.group.X] {D : Datum P.torus}
    (J : Identification D) (w : D.rootDatum.weylGroup)
    (n : 𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X), RepresentsWeylElement J w n →
    ∀ {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
      {p : BorelProjection P} {χ : Character P.torus.group}
      (L : AssociatedBundle Q a p χ),
      let g₀ := n ≫ J.normalizer.inclusion.hom.hom
      IsPullback (prod.fst : (𝟙_ (SchemeOver k) : SchemeOver k) ⨯ affineLine k ⟶ _)
        (prod.map g₀ (𝟙 (affineLine k)) ≫ L.trivialization) (g₀ ≫ Q.projection) L.projection ∧
      ∀ (R : TestAlgebra k) (t : Points P.torus.group.X R) (z : R),
        let g := toUnit ((testSpec k).obj (.op R)) ≫ n ≫ J.normalizer.inclusion.hom.hom
        lift (t ≫ P.torus.inclusion.hom.hom)
            (prod.lift g (linePoint R z) ≫ L.trivialization) ≫ L.action.smul =
          prod.lift g (linePoint R (characterValue ((J.labelEquiv w).val χ) R t * z)) ≫
            L.trivialization

end

end LinearAlgebraicGroups.Specs.FlagEquivariantEulerMap
