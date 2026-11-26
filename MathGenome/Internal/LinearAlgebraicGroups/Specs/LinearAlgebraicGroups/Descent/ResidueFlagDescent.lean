import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AffineGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AdjointCocharacters
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.FiniteFieldFlags
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.QuotientEmbedding

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open LinearAlgebraicGroups.Descent
open scoped TensorProduct CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Specs.ResidueFlagDescent

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

abbrev RationalPoint (X : SchemeOver K) := 𝟙_ (SchemeOver K) ⟶ X

/-- The map on the field spectrum induced by a coefficient automorphism. -/
abbrev scalarMap (σ : Gal(K/k)) : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom σ.toRingHom)

theorem scalarMap_comp_inverse (σ : Gal(K/k)) :
    scalarMap σ ≫ scalarMap σ⁻¹ = 𝟙 _ := by
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (σ⁻¹ : Gal(K/k)).toRingHom ≫
      CommRingCat.ofHom σ.toRingHom = 𝟙 _ := by
    ext x
    exact σ.apply_symm_apply x
  rw [h, Spec.map_id]

theorem scalarMap_over (σ : Gal(K/k)) :
    scalarMap σ ≫ fieldSpecMap k K = fieldSpecMap k K := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact σ.commutes x

/-- Inverse pullback on the Hopf algebra gives the action on the affine spectrum. -/
def coordinateOperator {A : HopfAlgebraCategory K} (D : HopfDescentDatum k A)
    (σ : Gal(K/k)) : A →+* A where
  toFun := D.action.act σ⁻¹
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := D.map_one _
  map_mul' := D.map_mul _

/-- The underlying semilinear morphism acts over the inverse field-spectrum map. -/
def schemeOperator (H : AffineAlgebraicGroup K)
    (D : HopfDescentDatum k (AdjointCocharacters.coordinateHopf H)) (σ : Gal(K/k)) :
    H.val.X.left ⟶ H.val.X.left :=
  let e := AdjointCocharacters.coordinateHopfIso H
  e.inv.hom.hom.left ≫ Spec.map (CommRingCat.ofHom (coordinateOperator D σ)) ≫
    e.hom.hom.hom.left

theorem schemeOperator_over (H : AffineAlgebraicGroup K)
    (D : HopfDescentDatum k (AdjointCocharacters.coordinateHopf H)) (σ : Gal(K/k)) :
    schemeOperator H D σ ≫ H.val.X.hom = H.val.X.hom ≫ scalarMap σ⁻¹ := by
  have h : (algebraMap K (AdjointCocharacters.coordinateHopf H)).comp
        (σ⁻¹ : Gal(K/k)).toRingHom =
      (coordinateOperator D σ).comp (algebraMap K (AdjointCocharacters.coordinateHopf H)) := by
    ext x
    change algebraMap K _ (σ⁻¹ x) = D.action.act σ⁻¹ (algebraMap K _ x)
    simp only [Algebra.algebraMap_eq_smul_one, D.action.map_smul, D.map_one]
  let A := AdjointCocharacters.coordinateHopf H
  have hs : Spec.map (CommRingCat.ofHom (coordinateOperator D σ)) ≫
      (specGroup A).X.hom = (specGroup A).X.hom ≫ scalarMap σ⁻¹ := by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K A)) ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : K →+* A ↦ Spec.map (CommRingCat.ofHom f)) h.symm
  let e := AdjointCocharacters.coordinateHopfIso H
  change (e.inv.hom.hom.left ≫ Spec.map (CommRingCat.ofHom (coordinateOperator D σ)) ≫
      e.hom.hom.hom.left) ≫ H.val.X.hom = _
  rw [Category.assoc, Category.assoc, Over.w e.hom.hom.hom]
  change e.inv.hom.hom.left ≫
    (Spec.map (CommRingCat.ofHom (coordinateOperator D σ)) ≫ (specGroup A).X.hom) = _
  rw [hs, ← Category.assoc, Over.w e.inv.hom.hom]

/-- A semilinear morphism acts on a rational point by changing coefficients in
the source as well as applying the underlying morphism of schemes. -/
def semilinearPoint {X : SchemeOver K} (σ : Gal(K/k)) (a : X.left ⟶ X.left)
    (ha : a ≫ X.hom = X.hom ≫ scalarMap σ⁻¹) (p : RationalPoint X) :
    RationalPoint X :=
  Over.homMk (scalarMap σ ≫ p.left ≫ a) (by
    rw [Category.assoc, Category.assoc, ha, ← Category.assoc p.left, Over.w]
    change scalarMap σ ≫ 𝟙 _ ≫ scalarMap σ⁻¹ = 𝟙 _
    rw [Category.id_comp, scalarMap_comp_inverse])

def groupPointOperator (H : AffineAlgebraicGroup K)
    (D : HopfDescentDatum k (AdjointCocharacters.coordinateHopf H)) (σ : Gal(K/k)) :
    RationalPoint H.val.X → RationalPoint H.val.X :=
  semilinearPoint σ (schemeOperator H D σ) (schemeOperator_over H D σ)

/-- The canonical semilinear map on an extended scheme comes from the identity
on the original scheme and the inverse automorphism on the field spectrum. -/
def coefficientMap (σ : Gal(K/k)) (X : SchemeOver k) :
    ((baseChange k K).obj X).left ⟶ ((baseChange k K).obj X).left :=
  let l := pullback.fst X.hom (fieldSpecMap k K)
  let r := pullback.snd X.hom (fieldSpecMap k K)
  pullback.lift l (r ≫ scalarMap σ⁻¹) (by
    rw [Category.assoc, scalarMap_over, pullback.condition])

def coefficientPoint (σ : Gal(K/k)) (X : SchemeOver k) :
    RationalPoint ((baseChange k K).obj X) → RationalPoint ((baseChange k K).obj X) :=
  semilinearPoint σ (coefficientMap σ X) (pullback.lift_snd _ _ _)

def rightTranslate {G : GroupScheme K} {S : SchemeOver K} (g : S ⟶ G.X)
    (c : RationalPoint G.X) : S ⟶ G.X := g * (toUnit S ≫ c)

/-- The datum moves the subgroup scheme to the indicated conjugate. The
isomorphism is on underlying schemes because its scalar map is semilinear. -/
def MovesBorel {H : AffineAlgebraicGroup K}
    (D : HopfDescentDatum k (AdjointCocharacters.coordinateHopf H)) (B : ClosedSubgroup H.val)
    (σ : Gal(K/k)) (c : RationalPoint H.val.X) : Prop :=
  ∃ i : B.group.X.left ≅ B.group.X.left,
    let s := toUnit B.group.X ≫ c
    i.hom ≫ (s * B.inclusion.hom.hom * s⁻¹).left =
      B.inclusion.hom.hom.left ≫ schemeOperator H D σ

/-- Effective descent of a finite-field reductive residue group and its flags. -/
def FiniteFieldFlagDescent : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Fintype k] [Fintype K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (H : AffineAlgebraicGroup K) (B : ClosedSubgroup H.val)
    (Q : QuotientEmbedding.Presentation B),
    GeometricRadicals.IsReductive H → GeometricBorelConjugacy.IsKBorel B →
    ∀ (D : HopfDescentDatum k (AdjointCocharacters.coordinateHopf H))
      (u : Gal(K/k) → RationalPoint H.val.X),
    (∀ σ, MovesBorel D B σ (u σ)) →
    ∃ (H₀ : AffineAlgebraicGroup k) (B₀ : ClosedSubgroup H₀.val)
      (Q₀ : QuotientEmbedding.Presentation B₀)
      (e : (groupBaseChange k K).obj H₀.val ≅ H.val)
      (j : (baseChange k K).obj Q₀.scheme ≅ Q.scheme)
      (c : RationalPoint H.val.X),
      GeometricRadicals.IsReductive H₀ ∧ GeometricBorelConjugacy.IsKBorel B₀ ∧
      (∀ σ (g : RationalPoint ((groupBaseChange k K).obj H₀.val).X),
        coefficientPoint σ H₀.val.X g ≫ e.hom.hom.hom =
          groupPointOperator H D σ (g ≫ e.hom.hom.hom)) ∧
      (∀ (S : SchemeOver K) (g : S ⟶ ((groupBaseChange k K).obj H₀.val).X),
        g ≫ (baseChange k K).map Q₀.projection ≫ j.hom =
          rightTranslate (g ≫ e.hom.hom.hom) c ≫ Q.projection) ∧
      (∀ σ (g : RationalPoint H.val.X),
        coefficientPoint σ Q₀.scheme (g ≫ Q.projection ≫ j.inv) ≫ j.hom =
          rightTranslate (groupPointOperator H D σ g) (u σ) ≫ Q.projection) ∧
      Nonempty (RationalPoint Q₀.scheme)

end

end LinearAlgebraicGroups.Specs.ResidueFlagDescent
