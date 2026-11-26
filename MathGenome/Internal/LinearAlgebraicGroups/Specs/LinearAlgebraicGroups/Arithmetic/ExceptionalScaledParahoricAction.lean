import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBuilding
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AdjointCocharacters

namespace LinearAlgebraicGroups.Specs.ExceptionalScaledParahoricAction

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Pointwise TensorProduct WithZero
open Pinning (BasedRootDatum)
open IntegralSemisimpleModel
open ExceptionalAffineRootSystems (ApartmentRoots)
open ExceptionalAffineBruhat
open ExceptionalAffineBuilding
open ExceptionalIwahoriCongruence
open ExceptionalLocalRootCoordinates (normalizedValuation residueMap)
open ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom)
open ExceptionalMarkedRootDescent (MarkedFibre markedWeylWord)
open AdjointRepresentation (GroupPoints)
open GeometricRadicals (IsReductive IsSplitTorus IsMaximalTorus)
open GeometricBorelConjugacy (IsKBorel)

universe u

set_option maxHeartbeats 700000

noncomputable section

/-- The scaled cocharacter evaluated in the original integral marking. -/
def markedCocharacter {E : BasedRootDatum.{u}} (M : IntegralMarking E)
    (R : IntegralAlgebra.{u}) (y : E.Y) (s : Rˣ) : IntegralPoints M.group R :=
  torusPoint E R (cocharacter E y R s) ≫ M.torus.hom.hom

/-- Integral coefficient changes and their compatibilities with the two scalar maps. -/
structure Coefficients (F K L : Type u) [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [ValuativeRel F] [ValuativeRel L] [ValuativeExtension F L] (ξ : Lˣ) where
  fieldAction : Gal(K/F) →* Gal(L/F)
  restrict (σ : Gal(K/F)) (z : K) :
    fieldAction σ (algebraMap K L z) = algebraMap K L (σ z)
  fixes_root (σ : Gal(K/F)) : fieldAction σ (ξ : L) = ξ
  integerAction : Gal(K/F) →* (localIntegers L ≃+* localIntegers L)
  integer_eq (σ : Gal(K/F)) (z : localIntegers L) :
    (integerAction σ z : L) = fieldAction σ (z : L)
  residueAction : letI := (residueMap F L).toAlgebra
    Gal(K/F) ≃* Gal(residue L / residue F)
  residue_eq (σ : Gal(K/F)) (z : localIntegers L) :
    letI := (residueMap F L).toAlgebra
    (residueHom (localIntegers L)).hom (integerAction σ z) =
      residueAction σ ((residueHom (localIntegers L)).hom z)

/-- Act on the model's points by a coefficient change followed by an integral
group automorphism. -/
def coefficientPoint {G : IntegralGroup.{u}} {R : Type u} [CommRing R]
    (f : R ≃+* R) (δ : Aut G) : IntegralPoints G (integralRing R) →*
      IntegralPoints G (integralRing R) :=
  (integralPointHom δ.asIso.hom (integralRing R)).comp
    (changeRingHom G (integralRingMap f.toRingHom))

section Local

variable {F K L : Type u} [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
  [ValuativeRel F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

local notation "P(" t ")" => parahoric Y.ad (cotype t)

/-- The prescribed reduction in the marked integral adjoint model.
The rational point comparison is part of the reduction data. -/
structure FaceReduction (B : SplitBuildingLevel Y)
    (t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p')) (x : ℚ ⊗[ℤ] E.Y)
    (d : ℕ) (y : E.Y) (ξ : Lˣ) where
  integral : P(t) →* IntegralPoints M'.group (localIntegers L)
  scale (g : P(t)) :
    let s := markedCocharacter M'.toIntegralMarking (integralRing L) y ξ
    changeRingHom M'.group (localIntegersInclusion L) (integral g) =
      s * scalarPoints M' (algebraMap K L) (g : FieldPoints M' K) * s⁻¹
  muGroup : GroupScheme (residue L)
  unitPoints : (groupPointsFunctor (residue L)).obj muGroup ≅
    DiagonalizableGroups.rootsOfUnityPoints (residue L) d
  μImage : muGroup ⟶ (fibre (residue L)).obj M'.group
  μImage_cocharacter (R : TestAlgebra (residue L)) (r : GroupPoints muGroup R) :
    let s : rootsOfUnity d R := unitPoints.hom.app R r
    forgetFibrePoint M'.group R (r ≫ μImage.hom.hom) =
      markedCocharacter M'.toIntegralMarking (integralRing R) y s.val
  centralizer : ClosedSubgroup ((fibre (residue L)).obj M'.group)
  centralizes : RepresentsSubgroup centralizer (fun _ g => Centralizes μImage g)
  centralizer_smooth : Smooth centralizer.group.X.hom
  identityComponent : ClosedSubgroup centralizer.group
  component_open : IsOpenImmersion identityComponent.inclusion.hom.hom.left
  component_eq : Set.range identityComponent.inclusion.hom.hom.left =
    connectedComponent (η[centralizer.group.X].left (IsLocalRing.closedPoint (residue L)))
  group_is_affine : IsAffine identityComponent.group.X.left
  group_lft : LocallyOfFiniteType identityComponent.group.X.hom
  group_qc : QuasiCompact identityComponent.group.X.hom
  reductive : IsReductive ⟨identityComponent.group, group_is_affine, group_lft, group_qc⟩
  torus : ClosedSubgroup identityComponent.group
  torusComparison : (fibre (residue L)).obj (splitTorus E) ≅ torus.group
  torus_marked :
    torusComparison.hom ≫ torus.inclusion ≫ identityComponent.inclusion ≫ centralizer.inclusion =
      (fibre (residue L)).map M'.torus
  torus_split : IsSplitTorus torus.group
  torus_maximal : ∃ h : IsClosedImmersion
      ((groupBaseChange (residue L) (AlgebraicClosure (residue L))).map torus.inclusion).hom.hom.left,
    IsMaximalTorus (GeometricRadicals.baseChangedSubgroup (AlgebraicClosure (residue L)) torus h)
  ambientMarking : MarkedFibre M' (residue L)
  root_characters :
    CharacterPairing.absoluteRoots torus =
      (fun a : E.I => Pinning.transportCharacter (ambientMarking.torusIso.symm ≪≫ torusComparison)
        (ambientMarking.realization.datumIso.val.indexEquiv a).val) ''
        {a | ∃ j : ℤ, (ApartmentRoots.split E.datum ℚ).root a x = j}
  roots (a : E.I) :
    (∃ r : (fibre (residue L)).obj M'.line.group ⟶ identityComponent.group,
      r ≫ identityComponent.inclusion ≫ centralizer.inclusion =
        (fibre (residue L)).map (M'.root a)) ↔ ∃ j : ℤ, (ApartmentRoots.split E.datum ℚ).root a x = j
  borel : ClosedSubgroup identityComponent.group
  borel_is_borel : IsKBorel borel
  borel_torus : SchemeDerivedGroup.IsSubgroupOf torus borel
  borel_roots (a : E.I) :
    (∃ r : (fibre (residue L)).obj M'.line.group ⟶ borel.group,
      r ≫ borel.inclusion ≫ identityComponent.inclusion ≫ centralizer.inclusion =
        (fibre (residue L)).map (M'.root a)) ↔
      ∃ j : ℤ, (ApartmentRoots.split E.datum ℚ).root a x = j ∧ (ApartmentRoots.split E.datum ℚ).positive p' (a, -j)
  reduction : P(t) →* GroupPoints identityComponent.group (CommAlgCat.of (residue L) (residue L))
  reduction_eq (g : P(t)) :
    forgetFibrePoint M'.group (CommAlgCat.of (residue L) (residue L))
      (reduction g ≫ identityComponent.inclusion.hom.hom ≫ centralizer.inclusion.hom.hom) =
        changeRingHom M'.group (residueHom (localIntegers L)) (integral g)

/-- The pinned integral operators, checked against the actual coefficient action.
The root datum map specifies the transport of the marked torus and roots. -/
structure PinnedOperators (ρ : Gal(K/F) →* MulAut (FieldPoints M' K))
    (h : Gal(K/F) → (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y)) where
  diagram : Gal(K/F) → E.datum.Equiv E.datum
  pinned : Gal(K/F) →* Aut M'.group
  h_eq (σ : Gal(K/F)) :
    h σ = (ExceptionalAffineRootSystems.diagramCocharacters (diagram σ)).toAffineEquiv
  torus_formula (σ : Gal(K/F)) (R : IntegralAlgebra.{u}) (v : TorusValues E R) :
    (torusPoint E R v ≫ M'.torus.hom.hom) ≫ (pinned σ).asIso.hom.hom.hom =
      torusPoint E R
        (v.comp (diagram σ).weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative) ≫
          M'.torus.hom.hom
  root_formula (σ : Gal(K/F)) (i : E.I) :
    ∃ ε : Integers.{u}ˣ, ∀ (R : IntegralAlgebra.{u}) (z : R),
      (M'.line.point R z ≫ (M'.root i).hom.hom) ≫ (pinned σ).asIso.hom.hom.hom =
        M'.line.point R (algebraMap Integers.{u} R (ε : Integers.{u}) * z) ≫
          (M'.root ((diagram σ).indexEquiv i)).hom.hom
  generic_eq (σ : Gal(K/F)) (g : FieldPoints M' K) :
    coefficientPoint σ.toRingEquiv (pinned σ) g = ρ σ g

/-- Use the actual lift at the type class of the cocycle value. -/
abbrev typeLift (a : Gal(K/F) → FieldPoints M' K) (σ : Gal(K/F)) : Y.ad.N :=
  Y.typeQuotient.lift (typeChange Y.typeQuotient (a σ))

/-- The integral lift of the scaled length-zero factor, quantified over the
actual factorization and the character valuation cancellation. -/
def IntegralNormalizerCorrection : Prop :=
  ∀ {F K L : Type u} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (Y : SplitLevel K c p p' e)
    (ρ : Gal(K/F) →* MulAut (FieldPoints M' K))
    (h : Gal(K/F) → (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y))
    (δ : PinnedOperators ρ h) (a : Gal(K/F) → FieldPoints M' K)
    (σ : Gal(K/F)) (y : E.Y) (ξ : Lˣ),
    let N := Y.ad.localIwahori.normalizer
    let n := typeLift (Y := Y) a σ
    let w := (N.label n).val.coweightEquiv.symm
    ∀ (v : TorusValues E (integralRing K)),
      (N.torusPart n : FieldPoints M' K) =
        torusPoint E (integralRing K) v ≫ M'.torus.hom.hom →
      (∀ χ : E.X,
        let f := E.datum.toLinearMap χ
        normalizedValuation L
          ((ξ : L) ^ (f y - f (w ((δ.diagram σ).coweightEquiv.symm y))) *
            algebraMap K L (v (Multiplicative.ofAdd χ) : K)) = 1) →
      let s := markedCocharacter M'.toIntegralMarking (integralRing L) y ξ
      ∃ q : TorusValues E (localIntegers L),
        let q₀ : IntegralPoints M'.group (localIntegers L) :=
          (torusPoint E (localIntegers L) q ≫ M'.torus.hom.hom) *
            markedWeylWord M'.toIntegralMarking (localIntegers L) (N.word (N.label n))
        changeRingHom M'.group (localIntegersInclusion L) q₀ =
          s * scalarPoints M' (algebraMap K L) (n : FieldPoints M' K) *
            (integralPointHom (δ.pinned σ).asIso.hom (integralRing L) s)⁻¹

/-- The data from the fixed face, the pinning and the scaling extension. -/
structure ScaledInput [ValuativeExtension F L] [ValuativeExtension K L]
    {B : SplitBuildingLevel Y} {t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p')}
    {x : ℚ ⊗[ℤ] E.Y} {d : ℕ} {y : E.Y} {ξ : Lˣ}
    (R : FaceReduction B t x d y ξ) where
  coefficients : Coefficients F K L ξ
  ρ : Gal(K/F) →* MulAut (FieldPoints M' K)
  h : Gal(K/F) → (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y)
  δ : PinnedOperators ρ h
  coefficient_comparison : ∀ σ, AutomorphismComparison Y.ad (ρ σ) (h σ)
  onBuilding : CoefficientAction B.ad ρ h
  equivariant (σ : Gal(K/F)) (g : FieldPoints M' K) (z : B.ad.realization.Point) :
    onBuilding.action σ (B.adjoint.action g z) =
      B.adjoint.action (ρ σ g) (onBuilding.action σ z)
  a : Gal(K/F) → FieldPoints M' K
  cocycle (σ τ : Gal(K/F)) : a (σ * τ) = a σ * ρ σ (a τ)
  barycenter : IsBarycenter (cotype t) t
  point_eq : rationalPoint B.ad.realization.coordinates x =
    simplexPoint B.ad.realization.coordinates B.ad.realization.vertex t
  fixed (σ : Gal(K/F)) : B.adjoint.action (a σ)
    (onBuilding.action σ (B.ad.realization.place 1 t)) = B.ad.realization.place 1 t
  d_pos : 0 < d
  scale_eq : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y
  b : Gal(K/F) → P(t)
  factor (σ : Gal(K/F)) :
    a σ = (b σ : FieldPoints M' K) * (typeLift (Y := Y) a σ : FieldPoints M' K)
  affine_fixed (σ : Gal(K/F)) :
    Y.ad.affine (typeLift (Y := Y) a σ) (h σ x) = x
  torusValues : Gal(K/F) → TorusValues E (integralRing K)
  torusValues_eq (σ : Gal(K/F)) :
    let N := Y.ad.localIwahori.normalizer
    let n := typeLift (Y := Y) a σ
    (N.torusPart n : FieldPoints M' K) =
      torusPoint E (integralRing K) (torusValues σ) ≫ M'.torus.hom.hom
  valuation_cancel (σ : Gal(K/F)) (χ : E.X) :
    let N := Y.ad.localIwahori.normalizer
    let n := typeLift (Y := Y) a σ
    let w := (N.label n).val.coweightEquiv.symm
    let f := E.datum.toLinearMap χ
    normalizedValuation L
      ((ξ : L) ^ (f y - f (w ((δ.diagram σ).coweightEquiv.symm y))) *
        algebraMap K L (torusValues σ (Multiplicative.ofAdd χ) : K)) = 1
  cocharacter_eq (σ : Gal(K/F)) (S : IntegralAlgebra.{u}) (r : Sˣ) (hr : r ^ d = 1) :
    let N := Y.ad.localIwahori.normalizer
    let n := typeLift (Y := Y) a σ
    let w := (N.label n).val.coweightEquiv.symm
    cocharacter E (w ((δ.diagram σ).coweightEquiv.symm y)) S r = cocharacter E y S r

/-- The Galois action on the scaled model, given by the actual integral
parahoric lift, the corrected normalizer lift and the pinned operators. -/
structure ScaledIntegralAction [ValuativeExtension F L] [ValuativeExtension K L]
    {B : SplitBuildingLevel Y} {t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p')}
    {x : ℚ ⊗[ℤ] E.Y} {d : ℕ} {y : E.Y} {ξ : Lˣ}
    {R : FaceReduction B t x d y ξ} (S : ScaledInput (F := F) R) where
  normalizer : Gal(K/F) → IntegralPoints M'.group (localIntegers L)
  normalizer_eq (σ : Gal(K/F)) :
    let s := markedCocharacter M'.toIntegralMarking (integralRing L) y ξ
    changeRingHom M'.group (localIntegersInclusion L) (normalizer σ) =
      s * scalarPoints M' (algebraMap K L)
          (typeLift (Y := Y) S.a σ : FieldPoints M' K) *
        (integralPointHom (S.δ.pinned σ).asIso.hom (integralRing L) s)⁻¹
  cocycle (σ τ : Gal(K/F)) :
    R.integral (S.b (σ * τ)) * normalizer (σ * τ) =
      (R.integral (S.b σ) * normalizer σ) *
        coefficientPoint (S.coefficients.integerAction σ) (S.δ.pinned σ)
          (R.integral (S.b τ) * normalizer τ)
  fixed_cocharacter (σ : Gal(K/F)) (T : IntegralAlgebra.{u})
      (f : localIntegers L ⟶ T) (r : Tˣ) (hr : r ^ d = 1) :
    let q := changeRingHom M'.group f (normalizer σ)
    let z := markedCocharacter M'.toIntegralMarking T y r
    q * integralPointHom (S.δ.pinned σ).asIso.hom T z * q⁻¹ = z
  invariant (σ : Gal(K/F)) (g : P(t)) :
    S.a σ * S.ρ σ (g : FieldPoints M' K) * (S.a σ)⁻¹ ∈ P(t)
  equivariant (σ : Gal(K/F)) (g : P(t)) :
    let p := R.integral (S.b σ) * normalizer σ
    R.integral ⟨_, invariant σ g⟩ =
      p * coefficientPoint (S.coefficients.integerAction σ) (S.δ.pinned σ) (R.integral g) * p⁻¹

namespace ScaledIntegralAction

variable [ValuativeExtension F L] [ValuativeExtension K L]
    {B : SplitBuildingLevel Y} {t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p')}
    {x : ℚ ⊗[ℤ] E.Y} {d : ℕ} {y : E.Y} {ξ : Lˣ}
    {R : FaceReduction B t x d y ξ} {S : ScaledInput (F := F) R}

/-- The ambient reduction of the operator's correcting point. -/
def correctingResidue (J : ScaledIntegralAction S) (σ : Gal(K/F)) :
    IntegralPoints M'.group (integralRing (residue L)) :=
  changeRingHom M'.group (residueHom (localIntegers L))
    (R.integral (S.b σ) * J.normalizer σ)

end ScaledIntegralAction

abbrev FaceReduction.group {B : SplitBuildingLevel Y} {t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p')}
    {x : ℚ ⊗[ℤ] E.Y} {d : ℕ} {y : E.Y} {ξ : Lˣ}
    (R : FaceReduction B t x d y ξ) : AffineAlgebraicGroup (residue L) :=
  ⟨R.identityComponent.group, R.group_is_affine, R.group_lft, R.group_qc⟩

open _root_.LinearAlgebraicGroups.Descent (HopfDescentDatum)
open AdjointCocharacters (coordinateHopf coordinateHopfIso)

/-- The test algebra in which the transported point takes its values. -/
def transportAlgebra {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (galois : Gal(k'/k)) (T : TestAlgebra k') : TestAlgebra k' :=
  @CommAlgCat.of k' _ T T.commRing
    (((algebraMap k' T).comp (galois⁻¹).toRingHom).toAlgebra)

/-- Restrict a field-algebra point along the inverse coordinate action. -/
def transportPoint {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {H : AffineAlgebraicGroup k'} (J : HopfDescentDatum k (coordinateHopf H))
    (galois : Gal(k'/k)) {T : TestAlgebra k'} (f : CommAlgCat.of k' (coordinateHopf H) ⟶ T) :
    CommAlgCat.of k' (coordinateHopf H) ⟶ transportAlgebra galois T := by
  refine ConcreteCategory.ofHom (C := CommAlgCat k')
    (X := CommAlgCat.of k' (coordinateHopf H)) (Y := transportAlgebra galois T)
    { toFun := fun z => f.hom (J.action.act galois⁻¹ z)
      map_zero' := by simp only [map_zero]; rfl
      map_one' := by simp only [J.map_one, map_one]; rfl
      map_add' x y := by simp only [map_add]; rfl
      map_mul' x y := by simp only [J.map_mul, map_mul]; rfl
      commutes' := fun z => by
        change f.hom (J.action.act galois⁻¹ (algebraMap k' (coordinateHopf H) z)) =
          algebraMap k' T (galois⁻¹ z)
        rw [Algebra.algebraMap_eq_smul_one, J.action.map_smul, J.map_one,
          Algebra.smul_def, mul_one]
        exact f.hom.commutes (galois⁻¹ z) }

/-- Points of the connected reductive residue group in its chosen Hopf presentation. -/
def coordinatePoint {k : Type u} [Field k] (H : AffineAlgebraicGroup k) (T : TestAlgebra k)
    (f : CommAlgCat.of k (coordinateHopf H) ⟶ T) : GroupPoints H.val T :=
  (testSpec k).map f.op ≫ (coordinateHopfIso H).hom.hom.hom

/-- Scheme descent keeps the given residue group and tracks the conjugate of
its Borel on every test algebra. -/
structure ScaledResidueAction [ValuativeExtension F L] [ValuativeExtension K L]
    {B : SplitBuildingLevel Y} {t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p')}
    {x : ℚ ⊗[ℤ] E.Y} {d : ℕ} {y : E.Y} {ξ : Lˣ}
    {R : FaceReduction B t x d y ξ} {S : ScaledInput (F := F) R}
    (J : ScaledIntegralAction S) where
  hopf : letI := (residueMap F L).toAlgebra
    HopfDescentDatum (residue F) (coordinateHopf R.group)
  ambient (σ : Gal(K/F)) (T : TestAlgebra (residue L))
      (f : CommAlgCat.of (residue L) (coordinateHopf R.group) ⟶ T) :
    letI := (residueMap F L).toAlgebra
    let galois := S.coefficients.residueAction σ
    let T' := transportAlgebra galois T
    let g := coordinatePoint R.group T f
    let g' := coordinatePoint R.group T' (transportPoint hopf galois f)
    let q := changeRingHom M'.group (integralRingMap (algebraMap (residue L) T'))
      (J.correctingResidue σ)
    let z := forgetFibrePoint M'.group T
      (g ≫ R.identityComponent.inclusion.hom.hom ≫ R.centralizer.inclusion.hom.hom)
    let z' : IntegralPoints M'.group (integralRing T') :=
      integralPointHom (S.δ.pinned σ).asIso.hom (integralRing T) z
    forgetFibrePoint M'.group T'
      (g' ≫ R.identityComponent.inclusion.hom.hom ≫ R.centralizer.inclusion.hom.hom) =
        q * z' * q⁻¹
  borel (σ : Gal(K/F)) (T : TestAlgebra (residue L))
      (f : CommAlgCat.of (residue L) (coordinateHopf R.group) ⟶ T) :
    letI := (residueMap F L).toAlgebra
    let galois := S.coefficients.residueAction σ
    let T' := transportAlgebra galois T
    let f₀ : CommAlgCat.of (residue L) (residue L) ⟶ T' :=
      ConcreteCategory.ofHom (C := CommAlgCat (residue L))
        (X := CommAlgCat.of (residue L) (residue L)) (Y := T')
        { toRingHom := algebraMap (residue L) T'
          commutes' := fun _ => rfl }
    let u : GroupPoints R.identityComponent.group T' :=
      mapPoints f₀ (R.reduction (S.b σ))
    (∃ g : GroupPoints R.borel.group T,
      g ≫ R.borel.inclusion.hom.hom = coordinatePoint R.group T f) ↔
    ∃ g' : GroupPoints R.borel.group T',
      let v : GroupPoints R.identityComponent.group T' := g' ≫ R.borel.inclusion.hom.hom
      u * v * u⁻¹ =
        coordinatePoint R.group T' (transportPoint hopf galois f)
  rational (σ : Gal(K/F)) (g : P(t)) :
    letI := (residueMap F L).toAlgebra
    let galois := S.coefficients.residueAction σ
    let T := CommAlgCat.of (residue L) (residue L)
    let T' := transportAlgebra galois T
    let f := fun q : CommAlgCat.of (residue L) (coordinateHopf R.group) ⟶ T =>
      coordinatePoint R.group T q
    ∀ q, f q = R.reduction g →
      let m : T' ⟶ T := ConcreteCategory.ofHom (C := CommAlgCat (residue L))
        (X := T') (Y := T) { galois.toRingHom with
          commutes' := fun r => galois.apply_symm_apply r }
      mapPoints m (coordinatePoint R.group T' (transportPoint hopf galois q)) =
      R.reduction ⟨_, J.invariant σ g⟩

/-- The scaled semilinear descent at the prescribed standard face. -/
def ScaledParahoricDescent : Prop :=
  ∀ {F K L : Type u} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
    [ValuativeRel F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [ValuativeExtension F L]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    {Y : SplitLevel K c p p' e} {B : SplitBuildingLevel Y}
    {t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p')}
    {x : ℚ ⊗[ℤ] E.Y} {d : ℕ} {y : E.Y} {ξ : Lˣ}
    (R : FaceReduction B t x d y ξ) (S : ScaledInput (F := F) R),
    ∃ J : ScaledIntegralAction S, Nonempty (ScaledResidueAction J)

end Local

end
end LinearAlgebraicGroups.Specs.ExceptionalScaledParahoricAction
