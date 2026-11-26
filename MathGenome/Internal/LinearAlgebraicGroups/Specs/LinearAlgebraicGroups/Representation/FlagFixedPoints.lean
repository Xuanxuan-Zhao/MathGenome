import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.EquivariantCoherentRestriction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagDerivedRestriction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagEquivariantEulerMap
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagLocalizationGeometry
import Mathlib.Algebra.Module.LocalizedModule.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.FlagFixedPoints

open AbstractPairing (Datum Root)
open CharacterDescent (Character)
open DatumAndWeyl (Identification)
open EquivariantAffineModules
open FlagEquivariantEulerMap (IsEulerCharacter IsFiberCharacter IsPointClass)
open FlagLineBundle (OppositeBorelPair BorelProjection)
open FlagLocalizationGeometry (PositiveRoot cotangentWeight torusAction)
open QuotientEmbedding (Presentation)

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k : Type u} [Field k]
variable {T : GroupScheme k} {X : SchemeOver k}

abbrev RestrictionSequence := EquivariantCoherentRestriction.RestrictionSequence.{u}
abbrev pointAction := @FlagEquivariantEulerMap.terminalAction

/-- Localization by all the root factors in the integral character ring. -/
def rootFactors {G : AffineAlgebraicGroup k} (S : ClosedSubgroup G.val) :
    Submonoid (CharacterRing S.group) :=
  Submonoid.closure (Set.range fun α : Root S => 1 - eChar α.val)

abbrev LocalCharacterRing {G : AffineAlgebraicGroup k} (S : ClosedSubgroup G.val) :=
  Localization (rootFactors S)

abbrev LocalGZero {G : AffineAlgebraicGroup k} (S : ClosedSubgroup G.val)
    (a : ModObj S.group.X X) := LocalizedModule (rootFactors S) (GZero a)

def localClass {G : AffineAlgebraicGroup k} {S : ClosedSubgroup G.val}
    {a : ModObj S.group.X X} (F : EquivariantCoherent a) : LocalGZero S a :=
  LocalizedModule.mkLinearMap (rootFactors S) _ (classOf F)

instance localGZeroModule {G : AffineAlgebraicGroup k} (S : ClosedSubgroup G.val)
    (a : ModObj S.group.X X) : Module (LocalCharacterRing S) (LocalGZero S a) :=
  LocalizedModule.moduleOfIsLocalization

abbrev localScalar {G : AffineAlgebraicGroup k} (S : ClosedSubgroup G.val) :=
  algebraMap (CharacterRing S.group) (LocalCharacterRing S)

/-- A homogeneous unit annihilates equivariant coherent classes by its
character factor. This is applied to the first nonzero coordinate of a cell. -/
def CoordinateStratumVanishing : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {X : SchemeOver k}
    (a : ModObj T.X X) (f : Γ(X.left, ⊤)) (χ : Character T),
    IsUnit f → HasFunctionWeight a f χ →
    ∀ c : GZero a, (1 - eChar χ) • c = 0

/-- An invariant affine neighborhood of a fixed rational point. -/
structure FixedPointChart {a : ModObj T.X X} (x : 𝟙_ (SchemeOver k) ⟶ X) where
  scheme : SchemeOver k
  action : ModObj T.X scheme
  inclusion : scheme ⟶ X
  point : 𝟙_ (SchemeOver k) ⟶ scheme
  affine : IsAffine scheme.left
  openImmersion : IsOpenImmersion inclusion.left
  equivariant : IsEquivariantMap a action inclusion
  over : point ≫ inclusion = x

/-- The derived character on an invariant affine polynomial chart at the fixed
point. Both alternating Tor and every bounded equivariant locally free
resolution of the restricted sheaf compute this character. -/
def IsDerivedFiberCharacter {a : ModObj T.X X} (x : 𝟙_ (SchemeOver k) ⟶ X)
    (F : EquivariantCoherent a) (c : CharacterRing T) : Prop :=
  ∃ (n : ℕ) (U : FlagDerivedRestriction.PolynomialChart a n), U.point = toUnit _ ≫ x ∧
    ∃ H, FlagDerivedRestriction.RestrictsTo U F H ∧
      (∃ ch, FlagDerivedRestriction.IsTorCharacter U H ch ∧
        c = ∑ q ∈ Finset.range (n + 1), (-1 : ℤ)^q • ch q) ∧
      Nonempty (FlagDerivedRestriction.LocallyFreeResolution H) ∧
      ∀ C : FlagDerivedRestriction.LocallyFreeResolution H, ∃ ch : ℕ → CharacterRing T,
        (∀ q, FlagDerivedRestriction.IsFiberCharacter (FlagDerivedRestriction.origin k n)
          (C.term q) (ch q)) ∧
        c = ∑ q ∈ Finset.range C.length, (-1 : ℤ)^q • ch q

/-- A cotangent weight basis at a rational fixed point, specified by
homogeneous lifts in its maximal ideal on an invariant affine chart. -/
def HasCotangentWeights {a : ModObj T.X X} {I : Type u}
    (x : 𝟙_ (SchemeOver k) ⟶ X) (ν : I → Character T) : Prop :=
  ∃ V : FixedPointChart (a := a) x,
    let A := Γ(V.scheme.left, ⊤)
    let m := RingHom.ker V.point.left.appTop.hom
    letI : Algebra k A := (FlagCohomology.groundRingHom V.scheme).toAlgebra
    ∃ (f : I → m) (basis : Module.Basis I k m.Cotangent),
      ∀ i, m.toCotangent (f i) = basis i ∧ HasFunctionWeight V.action (f i).val (ν i)

def cotangentProduct {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    [IsCommMonObj P.torus.group.X] {D : Datum P.torus}
    (J : DatumAndWeyl.Identification D) (w : D.rootDatum.weylGroup)
    [Fintype (PositiveRoot P)] : CharacterRing P.torus.group :=
  ∏ α : PositiveRoot P, (1 - eChar (cotangentWeight J w α))

/-- The fixed-point localization, derived restrictions and Euler formula on
the actual flag quotient of the specified opposite Borel. -/
def FlagLocalization : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G)
    (Q : Presentation P.negative) (a : ModObj G.val.X Q.scheme),
    μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    ∃ hT : IsCommMonObj P.torus.group.X, letI := hT
    ∃ (D : Datum P.torus) (J : DatumAndWeyl.Identification D)
      (_ : Fintype D.rootDatum.weylGroup) (_ : Fintype (PositiveRoot P)),
      (∀ w, ∃ n, BruhatOrbitParametrization.IsRepresentative J w n) ∧
      ∀ (n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X)),
        (∀ w, BruhatOrbitParametrization.IsRepresentative J w (n w)) →
        let x := fun w => n w ≫ J.normalizer.inclusion.hom.hom ≫ Q.projection
        let t := torusAction P.torus a
        let R := LocalCharacterRing P.torus
        let M := LocalGZero P.torus t
        let δ := fun w => localScalar P.torus (cotangentProduct J w)
        (∀ (K : Type u) [Field K] [Algebra k K]
            (y : Over.mk (fieldSpecMap k K) ⟶ Q.scheme),
          BruhatOrbitParametrization.FixedOver (T := P.torus) a y ↔
            ∃! w, y = toUnit _ ≫ x w) ∧
        (∀ w, HasCotangentWeights (a := t) (x w) (cotangentWeight J w)) ∧
        (∃ (V : SchemeOver k) (b : ModObj P.torus.group.X V) (j : V ⟶ Q.scheme),
          IsOpenImmersion j.left ∧ IsEquivariantMap t b j ∧
          Set.range j.left = (⋃ w, Set.range (x w).left)ᶜ ∧
          Subsingleton (LocalGZero P.torus b)) ∧
        ∃ (F : D.rootDatum.weylGroup → EquivariantCoherent t)
          (basis : Module.Basis D.rootDatum.weylGroup R M)
          (res : D.rootDatum.weylGroup → M →ₗ[R] R) (euler : M →ₗ[R] R),
          (∀ w, IsPointClass (x w) (F w) ∧ basis w = localClass (F w) ∧
            IsUnit (δ w) ∧ euler (basis w) = 1) ∧
          (∀ w v, res w (basis v) = if w = v then δ w else 0) ∧
          (∀ w H, ∃ c, IsDerivedFiberCharacter (x w) H c ∧
            res w (localClass H) = localScalar P.torus c) ∧
          (∀ H, ∃ c, IsEulerCharacter H c ∧ euler (localClass H) = localScalar P.torus c) ∧
          (∀ H : EquivariantCoherent t, H.sheaf.IsLocallyFree →
            ∃ f : D.rootDatum.weylGroup → CharacterRing P.torus.group,
              (∀ w, IsFiberCharacter (x w) H (f w)) ∧
              euler (localClass H) = ∑ w, localScalar P.torus (f w) * Ring.inverse (δ w)) ∧
          (∀ (p : BorelProjection P) (χ : Character P.torus.group)
            (h : FlagCohomology.FlagKernelPair Q)
            (ρ : ∀ i, RootWeightAction.Representation G.val
              (FlagCohomology.CohomologyIndex (p := p) (χ := χ) h i))
            (b : ∀ i, FlagCohomology.CohomologyBasis (p := p) (χ := χ) h i),
            (∀ i, FlagCohomology.IsFlagCohomologyAction h a i (b i) (ρ i)) →
            ∀ N, (∀ i ≥ N, IsZero (FlagCohomology.flagCohomology Q p χ h i)) →
              localScalar P.torus (FlagCohomology.equivariantEulerCharacteristic h ρ N) =
                ∑ w, localScalar P.torus (eChar ((J.labelEquiv w).val χ)) * Ring.inverse (δ w))

end

end LinearAlgebraicGroups.Specs.FlagFixedPoints
