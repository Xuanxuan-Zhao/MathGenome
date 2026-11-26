import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.Ring.Aut

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj ValuativeRel WithZero

universe u

namespace LinearAlgebraicGroups.Specs.SplitIwahoriUnramifiedTorsor

noncomputable section

abbrev localIntegers (K : Type u) [Field K] [ValuativeRel K] := 𝒪[K]

abbrev residue (K : Type u) [Field K] [ValuativeRel K] := 𝓀[K]

abbrev normalizedValuation (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : K) : ℤᵐ⁰ :=
  IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (ValuativeRel.valuation K x)

def IsUnramifiedLocalExtension (F K : Type u) [Field F] [Field K] [Algebra F K]
    [ValuativeRel F] [ValuativeRel K] [TopologicalSpace F] [TopologicalSpace K]
    [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K] : Prop :=
  ∀ x : F, normalizedValuation K (algebraMap F K x) = normalizedValuation F x

section Coefficients

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [ValuativeRel F] [ValuativeRel K] [ValuativeExtension F K]

theorem localIntegerMap_mem_iff (x : F) :
    ValuativeRel.valuation K (algebraMap F K x) ≤ 1 ↔ ValuativeRel.valuation F x ≤ 1 := by
  rw [← (ValuativeRel.valuation K).vle_one_iff, ← (ValuativeRel.valuation F).vle_one_iff,
    ← (algebraMap F K).map_one, ValuativeExtension.vle_iff_vle]

/-- Restriction of the given field inclusion to the valuation rings. -/
def localIntegerMap : localIntegers F →+* localIntegers K where
  toFun x := ⟨algebraMap F K (x : F), (localIntegerMap_mem_iff _).mpr x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' x y := Subtype.ext (map_add (algebraMap F K) (x : F) (y : F))
  map_mul' x y := Subtype.ext (map_mul (algebraMap F K) (x : F) (y : F))

end Coefficients

abbrev integerScheme (K : Type u) [Field K] [ValuativeRel K] : Scheme.{u} :=
  Spec (CommRingCat.of (localIntegers K))

abbrev residuePoint (K : Type u) [Field K] [ValuativeRel K] :
    Spec (CommRingCat.of (residue K)) ⟶ integerScheme K :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue (localIntegers K)))

section Schemes

abbrev Sections {S : Scheme.{u}} (X : Over S) := Over.mk (𝟙 S) ⟶ X

abbrev schemeMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :=
  Spec.map (CommRingCat.ofHom f)

variable {Γ : Type*} [Group Γ] {S : Type u} [CommRing S]
variable (t : Γ →* RingAut S)

abbrev scalar (σ : Γ) := schemeMap (t σ).toRingHom

/-- The group-scheme operators lie over the inverse coefficient automorphisms. -/
structure SemilinearGroupAction (G : Grp (Over (Spec (CommRingCat.of S)))) where
  operator (σ : Γ) : G ≅ (Over.pullback (scalar t σ⁻¹)).mapGrp.obj G
  one :
    (operator 1).hom.hom.hom.left ≫ pullback.fst G.X.hom (scalar t (1 : Γ)⁻¹) = 𝟙 _
  mul (σ τ : Γ) :
    (operator (σ * τ)).hom.hom.hom.left ≫ pullback.fst G.X.hom (scalar t (σ * τ)⁻¹) =
      ((operator τ).hom.hom.hom.left ≫ pullback.fst G.X.hom (scalar t τ⁻¹)) ≫
        ((operator σ).hom.hom.hom.left ≫ pullback.fst G.X.hom (scalar t σ⁻¹))

namespace SemilinearGroupAction

variable {t} {G : Grp (Over (Spec (CommRingCat.of S)))}
variable (a : SemilinearGroupAction t G)

def onScheme (σ : Γ) : G.X.left ⟶ G.X.left :=
  (a.operator σ).hom.hom.hom.left ≫ pullback.fst G.X.hom (scalar t σ⁻¹)

theorem scalar_cancel (t : Γ →* RingAut S) (σ : Γ) : scalar t σ ≫ scalar t σ⁻¹ = 𝟙 _ := by
  rw [← Spec.map_comp]
  apply Spec.map_eq_id.mpr
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change t σ (t σ⁻¹ (x : S)) = x
  rw [← RingAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem onScheme_over (σ : Γ) :
    a.onScheme σ ≫ G.X.hom = G.X.hom ≫ scalar t σ⁻¹ := by
  let p : G.X.left ⟶ pullback G.X.hom (scalar t σ⁻¹) :=
    (a.operator σ).hom.hom.hom.left
  have hp : p ≫ pullback.snd G.X.hom (scalar t σ⁻¹) = G.X.hom :=
    Over.w (a.operator σ).hom.hom.hom
  change (p ≫ pullback.fst _ _) ≫ G.X.hom = _
  rw [Category.assoc, pullback.condition, ← Category.assoc, hp]

def onSection (σ : Γ) (x : Sections G.X) : Sections G.X :=
  Over.homMk (scalar t σ ≫ x.left ≫ a.onScheme σ) (by
    rw [Category.assoc, Category.assoc, a.onScheme_over, Over.w_assoc]
    simpa using scalar_cancel t σ)

def leftTranslation (d : Sections G.X) : G.X ⟶ G.X :=
  (toUnit G.X ≫ d) * 𝟙 G.X

/-- Left translation gives a descent datum on the right regular torsor. -/
def translatingMap (d : Γ → Sections G.X) (σ : Γ) : G.X.left ⟶ G.X.left :=
  a.onScheme σ ≫ (leftTranslation (d σ)).left

end SemilinearGroupAction

/-- A projection is effective when its canonical map to the scalar extension
of the descended scheme is an isomorphism. -/
structure DescentProjection {U V : Scheme.{u}} (f : U ⟶ V)
    (X : Over U) (Y : Over V) where
  projection : (Over.map f).obj X ⟶ Y
  effective : IsIso (((Over.mapPullbackAdj f).homEquiv X Y) projection)

end Schemes

section Targets

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [ValuativeRel F] [ValuativeRel K] [ValuativeExtension F K]

abbrev coefficientMap : integerScheme K ⟶ integerScheme F :=
  schemeMap (localIntegerMap (F := F) (K := K))

/-- The unramified extension of local rings is a finite étale cover, and the
field automorphisms restrict to the actual valuation rings. -/
def UnramifiedValuationRingCover : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [ValuativeRel K] [ValuativeExtension F K] [TopologicalSpace F]
    [TopologicalSpace K] [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K],
    IsUnramifiedLocalExtension F K →
    IsFinite (coefficientMap (F := F) (K := K)) ∧
    Etale (coefficientMap (F := F) (K := K)) ∧
    Surjective (coefficientMap (F := F) (K := K)) ∧
    ∃ t : Gal(K/F) →* RingAut (localIntegers K),
      ∀ (σ : Gal(K/F)) (x : localIntegers K), (t σ x : K) = σ (x : K)

/-- A section pulled back along the given coefficient inclusion. -/
def extendSection {U V : Scheme.{u}} (f : U ⟶ V) {P : Over V}
    (q : Sections P) : Sections ((Over.pullback f).obj P) :=
  Over.homMk (pullback.lift (f ≫ q.left) (𝟙 U) (by
    rw [Category.assoc, Over.w]
    change f ≫ 𝟙 V = 𝟙 U ≫ f
    rw [Category.comp_id, Category.id_comp])) (by exact pullback.lift_snd _ _ _)

variable (t : Gal(K/F) →* RingAut (localIntegers K))
variable {D : Grp (Over (integerScheme K))} (a : SemilinearGroupAction t D)
variable (d : Gal(K/F) → Sections D.X)

local notation "b" => coefficientMap (F := F) (K := K)
local notation "B" => Over.pullback b

/-- The descended group and right translating torsor over the base valuation
ring, with their equivariant identifications and an integral section. -/
structure TranslatingTorsorDescent where
  group : Grp (Over (integerScheme F))
  groupAffine : IsAffine group.X.left
  groupSmooth : Smooth group.X.hom
  specialConnected : ConnectedSpace (((Over.pullback (residuePoint F)).obj group.X).left)
  torsor : Over (integerScheme F)
  torsorAffine : IsAffine torsor.left
  torsorSmooth : Smooth torsor.hom
  torsorSurjective : Surjective torsor.hom
  rightAction : torsor ⊗ group.X ⟶ torsor
  actOne {T : Over (integerScheme F)} (x : T ⟶ torsor) :
    lift x (1 : T ⟶ group.X) ≫ rightAction = x
  actMul {T : Over (integerScheme F)} (x : T ⟶ torsor) (g h : T ⟶ group.X) :
    lift x (g * h) ≫ rightAction = lift (lift x g ≫ rightAction) h ≫ rightAction
  torsorIso : IsIso (lift (fst torsor group.X) rightAction)
  groupComparison : D ≅ (B).mapGrp.obj group
  torsorComparison : D.X ≅ (B).obj torsor
  groupEquivariant (σ : Gal(K/F)) :
    a.onScheme σ ≫ groupComparison.hom.hom.hom.left ≫ pullback.fst group.X.hom b =
      groupComparison.hom.hom.hom.left ≫ pullback.fst group.X.hom b
  torsorEquivariant (σ : Gal(K/F)) :
    a.translatingMap d σ ≫ torsorComparison.hom.left ≫ pullback.fst torsor.hom b =
      torsorComparison.hom.left ≫ pullback.fst torsor.hom b
  actionComparison {T : Over (integerScheme K)} (x g : T ⟶ D.X) :
    (x * g) ≫ torsorComparison.hom =
      lift (x ≫ torsorComparison.hom) (g ≫ groupComparison.hom.hom.hom) ≫
        (prodComparisonIso B torsor group.X).inv ≫ (B).map rightAction
  integralSection : Sections torsor
  fixed (σ : Gal(K/F)) :
    let x := extendSection b integralSection ≫ torsorComparison.inv
    d σ * a.onSection σ x = x
  neutralization (σ : Gal(K/F)) :
    let x := extendSection b integralSection ≫ torsorComparison.inv
    x⁻¹ * d σ * a.onSection σ x = 1

/-- A cocycle for any of the indicated semilinear scheme actions descends
to a smooth affine torsor with an integral correction. -/
def UnramifiedTranslatingTorsor : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [ValuativeRel K] [ValuativeExtension F K] [TopologicalSpace F]
    [TopologicalSpace K] [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField K],
    IsUnramifiedLocalExtension F K →
    ∀ (t : Gal(K/F) →* RingAut (localIntegers K)),
      (∀ (σ : Gal(K/F)) (x : localIntegers K), (t σ x : K) = σ (x : K)) →
      ∀ (D : Grp (Over (integerScheme K))) (_ : IsAffine D.X.left)
        (_ : Smooth D.X.hom) (_ : GeometricallyConnected D.X.hom)
        (a : SemilinearGroupAction t D) (d : Gal(K/F) → Sections D.X),
        (∀ σ τ, d (σ * τ) = d σ * a.onSection σ (d τ)) →
        Nonempty (TranslatingTorsorDescent t a d)

end Targets

end

end LinearAlgebraicGroups.Specs.SplitIwahoriUnramifiedTorsor
