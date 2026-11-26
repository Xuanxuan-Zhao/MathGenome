import Specs.LinearAlgebraicGroups.Arithmetic.WeakApproximationTorusParameters
import LinearAlgebraicGroups.Affine.SmoothnessCriteria
import LinearAlgebraicGroups.Arithmetic.DominantTorusProducts
import LinearAlgebraicGroups.Arithmetic.TorusNormCovers
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj nonZeroDivisors

universe u

namespace LinearAlgebraicGroups.Arithmetic.WeakApproximationTorusParameters

noncomputable section

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.DominantTorusProducts (orderedSubgroupProduct)
open LinearAlgebraicGroups.Specs.GeometricRadicals (IsTorus)

private theorem exists_eval_ne_zero {k : Type u} [Field k] [Infinite k] {σ : Type u}
    {p : MvPolynomial σ k} (hp : p ≠ 0) :
    ∃ x : σ → k, MvPolynomial.aeval x p ≠ 0 := by
  by_contra! h
  apply hp
  apply MvPolynomial.funext
  intro x
  exact (h x).trans (map_zero _).symm

private def rationalPoint {k : Type u} [Field k] {σ : Type u}
    {p : MvPolynomial σ k} (x : σ → k) (hx : MvPolynomial.aeval x p ≠ 0) :
    Points (PrincipalOpen p) (CommAlgCat.of k k) :=
  (testSpec k).map (CommAlgCat.ofHom
    (IsLocalization.Away.liftAlgHom p
      (f := MvPolynomial.aeval x) (isUnit_iff_ne_zero.mpr hx))).op

/-- Over a characteristic-zero domain an injective map to another domain of
finite presentation is smooth after inverting a nonzero element of the target. -/
private theorem exists_smooth_localization (A B : Type u) [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [CharZero A] [Algebra A B]
    [Algebra.FinitePresentation A B] (hinj : Function.Injective (algebraMap A B)) :
    ∃ q : B, q ≠ 0 ∧ Algebra.Smooth A (Localization.Away q) := by
  let p : Ideal A := ⊥
  let r : Ideal B := ⊥
  have : p.IsPrime := Ideal.isPrime_bot
  have : r.IsPrime := Ideal.isPrime_bot
  have : r.LiesOver p := ⟨by
    ext a
    change (a = 0) ↔ algebraMap A B a = 0
    rw [← map_zero (algebraMap A B), hinj.eq_iff]⟩
  let := Localization.AtPrime.algebraOfLiesOver p r
  have : IsFractionRing A (Localization.AtPrime p) := by
    change IsLocalization A⁰ (Localization.AtPrime p)
    rw [← Ideal.primeCompl_bot]
    infer_instance
  have : IsFractionRing B (Localization.AtPrime r) := by
    change IsLocalization B⁰ (Localization.AtPrime r)
    rw [← Ideal.primeCompl_bot]
    infer_instance
  let : Field (Localization.AtPrime p) := IsFractionRing.toField A
  let : Field (Localization.AtPrime r) := IsFractionRing.toField B
  have : CharZero (Localization.AtPrime p) :=
    IsFractionRing.charZero_of_isFractionRing A
  have : Algebra.FormallySmooth A (Localization.AtPrime p) :=
    Algebra.FormallySmooth.of_isLocalization p.primeCompl
  have : Algebra.EssFiniteType A (Localization.AtPrime r) := inferInstance
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime r) :=
    Algebra.EssFiniteType.of_comp A _ _
  have : Algebra.FormallySmooth (Localization.AtPrime p) (Localization.AtPrime r) :=
    Algebra.FormallySmooth.of_perfectField
  have : Algebra.IsSmoothAt A r :=
    Algebra.FormallySmooth.comp A (Localization.AtPrime p) (Localization.AtPrime r)
  obtain ⟨q, hq, hs⟩ := Algebra.IsSmoothAt.exists_notMem_smooth A r
  exact ⟨q, hq, hs⟩

private def rationalBaseIso (k : Type u) [Field k] :
    (testSpec k).obj (op (CommAlgCat.of k k)) ≅ 𝟙_ (SchemeOver k) :=
  (show (𝟙_ (SchemeOver k)) ≅ (testSpec k).obj (op (CommAlgCat.of k k)) from
    Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
      change (𝟙 (Spec (CommRingCat.of k))) ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _
      rw [Category.id_comp]
      exact Spec.map_id (CommRingCat.of k))).symm

private def rightMultiply {k : Type u} [Field k] {G : Specs.GroupScheme k}
    (b : Points G.X (CommAlgCat.of k k)) : G.X ⟶ G.X :=
  (𝟙 G.X : G.X ⟶ G.X) * (toUnit G.X ≫ (rationalBaseIso k).inv ≫ b)

private theorem comp_rightMultiply {k : Type u} [Field k] {G : Specs.GroupScheme k}
    {X : SchemeOver k} (x : X ⟶ G.X) (b : Points G.X (CommAlgCat.of k k)) :
    x ≫ rightMultiply b = x * (toUnit X ≫ (rationalBaseIso k).inv ≫ b) := by
  simp only [rightMultiply, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]

private def rightTranslation {k : Type u} [Field k] {G : Specs.GroupScheme k}
    (b : Points G.X (CommAlgCat.of k k)) : G.X ≅ G.X where
  hom := rightMultiply b
  inv := rightMultiply b⁻¹
  hom_inv_id := by
    rw [comp_rightMultiply, rightMultiply, mul_assoc]
    simp only [← Category.assoc, ← MonObj.comp_mul, mul_inv_cancel, MonObj.comp_one, mul_one]
  inv_hom_id := by
    rw [comp_rightMultiply, rightMultiply, mul_assoc]
    simp only [← Category.assoc, ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, mul_one]

private theorem comp_rightTranslation {k : Type u} [Field k] {G : Specs.GroupScheme k}
    (x b : Points G.X (CommAlgCat.of k k)) :
    x ≫ (rightTranslation b).hom = x * b := by
  change x ≫ rightMultiply b = x * b
  rw [comp_rightMultiply]
  have h : toUnit ((testSpec k).obj (op (CommAlgCat.of k k))) = (rationalBaseIso k).hom :=
    toUnit_unique _ _
  rw [h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

private theorem pointed_of_smooth {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {σ : Type u} {p : MvPolynomial σ k} (f : PrincipalOpen p ⟶ G.val.X)
    (a : Points (PrincipalOpen p) (CommAlgCat.of k k)) (hf : Smooth f.left) :
    ∃ g : PrincipalOpen p ⟶ G.val.X,
      a ≫ g = (1 : Points G.val.X (CommAlgCat.of k k)) ∧ Smooth g.left := by
  let e := rightTranslation (G := G.val) ((a ≫ f)⁻¹)
  refine ⟨f ≫ e.hom, ?_, ?_⟩
  · rw [← Category.assoc, comp_rightTranslation, mul_inv_cancel]
  · change Smooth (f.left ≫ e.hom.left)
    have : Smooth f.left := hf
    have : IsIso e.hom.left :=
      (Over.forget (Spec (CommRingCat.of k))).map_isIso e.hom
    infer_instance

/-- A dominant affine parametrization gives a pointed smooth one in characteristic zero.
The injective algebra map is the coordinate-ring form of dominance. -/
theorem pointed_of_dominant_coordinates {k : Type u} [Field k] [CharZero k]
    (G : AffineAlgebraicGroup k)
    {A : Type u} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (e : (testSpec k).obj (op (CommAlgCat.of k A)) ≅ G.val.X)
    (n : ℕ) {p : MvPolynomial (ULift.{u} (Fin n)) k} (hp : p ≠ 0)
    (φ : A →ₐ[k] Localization.Away p) (hinj : Function.Injective φ) :
    ∃ (q : MvPolynomial (ULift.{u} (Fin n)) k)
      (a : Points (PrincipalOpen q) (CommAlgCat.of k k))
      (f : PrincipalOpen q ⟶ G.val.X),
      a ≫ f = (1 : Points G.val.X (CommAlgCat.of k k)) ∧ Smooth f.left := by
  let P := MvPolynomial (ULift.{u} (Fin n)) k
  let B := Localization.Away p
  have : IsDomain B := Localization.Away.isDomain hp
  have : IsDomain A := hinj.isDomain φ
  have : CharZero A := charZero_of_injective_algebraMap (algebraMap k A).injective
  let : Algebra A B := φ.toRingHom.toAlgebra
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType k A B
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  obtain ⟨z, hz, hs⟩ := exists_smooth_localization A B hinj
  let r := (IsLocalization.Away.sec p z).1
  have hassoc : Associated (algebraMap P B r) z := IsLocalization.Away.associated_sec_fst p z
  have hr : r ≠ 0 := by
    intro hr
    have h := hassoc.symm
    rw [hr, map_zero] at h
    exact hz ((associated_zero_iff_eq_zero z).mp h)
  let L := Localization.Away z
  have : IsLocalization.Away (p * r) L :=
    IsLocalization.Away.mul_of_associated p r z hassoc
  let j := IsLocalization.algEquiv (Submonoid.powers (p * r)) L (Localization.Away (p * r))
  let ψ : A →ₐ[k] Localization.Away (p * r) :=
    (j.restrictScalars k).toAlgHom.comp ((Algebra.algHom k B L).comp φ)
  have hψ : ψ.toRingHom.Smooth := by
    have h₁ : (algebraMap A L).Smooth := RingHom.smooth_algebraMap.mpr hs
    have h₂ : j.toRingEquiv.toRingHom.Smooth := RingHom.Smooth.of_bijective j.bijective
    have h₃ : ψ.toRingHom = j.toRingEquiv.toRingHom.comp (algebraMap A L) := by
      ext x
      change j (algebraMap B L (φ x)) = j (algebraMap A L x)
      rw [IsScalarTower.algebraMap_apply A B L]
      rfl
    rw [h₃]
    exact h₁.comp h₂
  let f : PrincipalOpen (p * r) ⟶ G.val.X := (testSpec k).map (CommAlgCat.ofHom ψ).op ≫ e.hom
  have hf : Smooth f.left := by
    change Smooth (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ e.hom.left)
    have hmap : Smooth (Spec.map (CommRingCat.ofHom ψ.toRingHom)) :=
      (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr hψ
    have : IsIso e.hom.left :=
      (Over.forget (Spec (CommRingCat.of k))).map_isIso e.hom
    have : IsOpenImmersion e.hom.left := inferInstance
    have he : Smooth e.hom.left := inferInstance
    exact MorphismProperty.comp_mem @Smooth _ _ hmap he
  have : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
  obtain ⟨x, hx⟩ := exists_eval_ne_zero (mul_ne_zero hp hr)
  let a := rationalPoint x hx
  obtain ⟨f', hpoint, hsmooth⟩ := pointed_of_smooth f a hf
  exact ⟨p * r, a, f', hpoint, hsmooth⟩

open private isReduced_of_smooth_over_field
  from LinearAlgebraicGroups.Affine.SmoothnessCriteria

/-- A dominant map from a polynomial principal open to a smooth affine group
can be made smooth and translated to take a rational parameter to the identity. -/
theorem pointed_of_dominant_morphism {k : Type u} [Field k] [CharZero k]
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom)
    (n : ℕ) {p : MvPolynomial (ULift.{u} (Fin n)) k} (hp : p ≠ 0)
    (f : PrincipalOpen p ⟶ G.val.X) (hf : IsDominant f.left) :
    ∃ (q : MvPolynomial (ULift.{u} (Fin n)) k)
      (a : Points (PrincipalOpen q) (CommAlgCat.of k k))
      (g : PrincipalOpen q ⟶ G.val.X),
      a ≫ g = (1 : Points G.val.X (CommAlgCat.of k k)) ∧ Smooth g.left := by
  obtain ⟨D, ⟨e⟩⟩ := (AlgebraicGeometry.essImage_algSpec (R := CommRingCat.of k)).mpr G.2.1
  let A := D.unop
  change (testSpec k).obj (op A) ≅ G.val.X at e
  have he : IsIso e.hom.left := (Over.forget (Spec (CommRingCat.of k))).map_isIso e.hom
  have hfinite : LocallyOfFiniteType ((testSpec k).obj (op A)).hom := by
    rw [← Over.w e.hom]
    have h₁ : LocallyOfFiniteType e.hom.left := inferInstance
    exact MorphismProperty.comp_mem @LocallyOfFiniteType _ _ h₁ G.2.2.1
  have : Algebra.FiniteType k A := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) at hfinite
    exact RingHom.finiteType_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hfinite)
  let F := AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of k)
  let j := F.preimage (f ≫ e.inv)
  have hj : (testSpec k).map j = f ≫ e.inv := F.map_preimage _
  let φ : A →ₐ[k] Localization.Away p := j.unop.hom
  have hd : DenseRange (PrimeSpectrum.comap φ.toRingHom) := by
    have h₁ : IsIso e.inv.left :=
      (Over.forget (Spec (CommRingCat.of k))).map_isIso e.inv
    have h₂ : IsDominant e.inv.left := inferInstance
    have h₃ : IsDominant ((testSpec k).map j).left := by
      rw [hj, Over.comp_left]
      exact ⟨h₂.denseRange.comp hf.denseRange e.inv.left.continuous⟩
    exact h₃.denseRange
  have hG : IsReduced G.val.X.left := isReduced_of_smooth_over_field G.val.X.hom
  have heopen : IsOpenImmersion e.hom.left := inferInstance
  have hA : _root_.IsReduced A :=
    (affine_isReduced_iff (CommRingCat.of A)).mp
      (@isReduced_of_isOpenImmersion _ _ e.hom.left heopen hG)
  have hker := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ.toRingHom).mp hd
  rw [nilradical_eq_bot_iff.mpr hA, le_bot_iff] at hker
  exact pointed_of_dominant_coordinates G e n hp φ
    ((RingHom.injective_iff_ker_eq_bot _).mpr hker)

/-- The trivial group has the constant parametrization from affine space of dimension zero. -/
theorem pointed_of_trivial {k : Type u} [Field k] [CharZero k]
    (G : AffineAlgebraicGroup k) (h : G.val ≅ Grp.trivial (SchemeOver k)) :
    ∃ (n : ℕ) (p : MvPolynomial (ULift.{u} (Fin n)) k)
      (a : Points (PrincipalOpen p) (CommAlgCat.of k k))
      (f : PrincipalOpen p ⟶ G.val.X),
      a ≫ f = (1 : Points G.val.X (CommAlgCat.of k k)) ∧ Smooth f.left := by
  let e := rationalBaseIso k ≪≫ (Grp.forget (SchemeOver k)).mapIso h.symm
  let p : MvPolynomial (ULift.{u} (Fin 0)) k := 1
  have hp : p ≠ 0 := one_ne_zero
  have : IsDomain (Localization.Away p) := Localization.Away.isDomain hp
  let φ : k →ₐ[k] Localization.Away p := Algebra.ofId k _
  obtain ⟨q, a, f, hf, hs⟩ := pointed_of_dominant_coordinates G e 0 hp φ
    (algebraMap k (Localization.Away p)).injective
  exact ⟨0, q, a, f, hf, hs⟩

section Products

open scoped BigOperators

variable {k : Type u} [Field k] {m : ℕ} {σ : Fin m → Type u}
variable (p : ∀ i, MvPolynomial (σ i) k)

private def includeVariables (i : Fin m) :
    MvPolynomial (σ i) k →ₐ[k] MvPolynomial (Σ j, σ j) k :=
  MvPolynomial.rename (Sigma.mk i)

/-- On the direct product of affine spaces the product open is cut out by
the product of the pulled-back polynomials. -/
def productPolynomial : MvPolynomial (Σ i, σ i) k :=
  ∏ i, includeVariables i (p i)

private theorem factor_isUnit (i : Fin m) :
    IsUnit (algebraMap _ (Localization.Away (productPolynomial p)) (includeVariables i (p i))) :=
  IsLocalization.Away.isUnit_of_dvd (productPolynomial p)
    (Finset.dvd_prod_of_mem (fun j => includeVariables j (p j)) (Finset.mem_univ i))

private def factorCoordinates (i : Fin m) :
    Localization.Away (p i) →ₐ[k] Localization.Away (productPolynomial p) :=
  IsLocalization.Away.liftAlgHom (p i)
    (f := (Algebra.algHom k _ _).comp (includeVariables i)) (factor_isUnit p i)

private theorem factorCoordinates_algebraMap (i : Fin m) (s : MvPolynomial (σ i) k) :
    factorCoordinates p i (algebraMap _ _ s) =
      algebraMap _ _ (includeVariables i s) :=
  IsLocalization.Away.lift_eq (p i) (factor_isUnit p i) s

private def evalProduct {A : Type u} [CommRing A] [Algebra k A]
    (f : ∀ i, Localization.Away (p i) →ₐ[k] A) : MvPolynomial (Σ i, σ i) k →ₐ[k] A :=
  MvPolynomial.aeval (fun j : Σ i, σ i =>
    f j.1 (algebraMap (MvPolynomial (σ j.1) k) (Localization.Away (p j.1)) (MvPolynomial.X j.2)))

private theorem evalProduct_include {A : Type u} [CommRing A] [Algebra k A]
    (f : ∀ i, Localization.Away (p i) →ₐ[k] A) (i : Fin m)
    (s : MvPolynomial (σ i) k) :
    evalProduct p f (includeVariables i s) = f i (algebraMap _ _ s) := by
  have he : (evalProduct p f).comp (includeVariables i) =
      (f i).comp (Algebra.algHom k _ _) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [evalProduct, includeVariables]
    rfl
  exact DFunLike.congr_fun he s

private theorem evalProduct_isUnit {A : Type u} [CommRing A] [Algebra k A]
    (f : ∀ i, Localization.Away (p i) →ₐ[k] A) :
    IsUnit (evalProduct p f (productPolynomial p)) := by
  rw [productPolynomial, map_prod]
  refine IsUnit.prod_univ_iff.mpr (fun i ↦ ?_)
  rw [evalProduct_include]
  exact (IsLocalization.Away.algebraMap_isUnit (p i)).map (f i)

private def liftProduct {A : Type u} [CommRing A] [Algebra k A]
    (f : ∀ i, Localization.Away (p i) →ₐ[k] A) :
    Localization.Away (productPolynomial p) →ₐ[k] A :=
  IsLocalization.Away.liftAlgHom (productPolynomial p) (f := evalProduct p f)
    (evalProduct_isUnit p f)

private theorem liftProduct_comp {A : Type u} [CommRing A] [Algebra k A]
    (f : ∀ i, Localization.Away (p i) →ₐ[k] A) (i : Fin m) :
    (liftProduct p f).comp (factorCoordinates p i) = f i := by
  apply IsLocalization.algHom_ext (.powers (p i))
  apply AlgHom.ext
  intro s
  change liftProduct p f (factorCoordinates p i (algebraMap _ _ s)) = f i (algebraMap _ _ s)
  rw [factorCoordinates_algebraMap]
  exact (IsLocalization.Away.lift_eq (productPolynomial p) (evalProduct_isUnit p f) _).trans
    (evalProduct_include p f i s)

private theorem product_algHom_ext {A : Type u} [CommRing A] [Algebra k A]
    {f g : Localization.Away (productPolynomial p) →ₐ[k] A}
    (h : ∀ i, f.comp (factorCoordinates p i) = g.comp (factorCoordinates p i)) : f = g := by
  apply IsLocalization.algHom_ext (.powers (productPolynomial p))
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  have hh := DFunLike.congr_fun (h i)
    (algebraMap (MvPolynomial (σ i) k) (Localization.Away (p i)) (MvPolynomial.X j))
  change f (algebraMap _ _ (MvPolynomial.X (Sigma.mk i j))) =
    g (algebraMap _ _ (MvPolynomial.X (Sigma.mk i j)))
  simpa only [AlgHom.comp_apply, factorCoordinates_algebraMap, includeVariables,
    MvPolynomial.rename_X] using hh

private def factorCofan :
    Cofan (fun i => CommAlgCat.of k (Localization.Away (p i))) :=
  Cofan.mk (CommAlgCat.of k (Localization.Away (productPolynomial p)))
    (fun i => CommAlgCat.ofHom (factorCoordinates p i))

private def factorCofanIsColimit : IsColimit (factorCofan p) :=
  Cofan.IsColimit.mk _
    (fun c => CommAlgCat.ofHom (liftProduct p (fun i => (c.inj i).hom)))
    (fun c i => CommAlgCat.hom_ext (liftProduct_comp p (fun i => (c.inj i).hom) i))
    (fun c _f h => CommAlgCat.hom_ext (product_algHom_ext p fun i =>
      (congrArg CommAlgCat.Hom.hom (h i)).trans
        (liftProduct_comp p (fun j => (c.inj j).hom) i).symm))

/-- Finite products in the slice of polynomial principal opens are again
polynomial principal opens. This includes the empty product. -/
def principalOpenProductIso :
    PrincipalOpen (productPolynomial p) ≅ ∏ᶜ fun i => PrincipalOpen (p i) := by
  letI : PreservesLimitsOfSize.{0, 0} (testSpec k) :=
    AlgebraicGeometry.preservesLimitsOfSize_algSpec
  exact (isLimitFanMkObjOfIsLimit (testSpec k) _
    (fun i => (CommAlgCat.ofHom (factorCoordinates p i)).op)
    (Cofan.IsColimit.op (factorCofanIsColimit p))).conePointUniqueUpToIso
      (productIsProduct _)

theorem productPolynomial_ne_zero (hp : ∀ i, p i ≠ 0) : productPolynomial p ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (MvPolynomial.rename_injective _ (fun _ _ h => Sigma.mk.inj_iff.mp h |>.2.eq))
    |>.ne (hp i)

end Products

/-- Rename a finite family of variables to the standard affine-space indexing. -/
def principalOpenReindex {k : Type u} [Field k] {σ τ : Type u}
    (e : σ ≃ τ) (p : MvPolynomial σ k) :
    PrincipalOpen (MvPolynomial.rename e p) ≅ PrincipalOpen p := by
  let r := MvPolynomial.renameEquiv k e
  let j := IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers p) (T := Submonoid.powers (MvPolynomial.rename e p))
    (Localization.Away p) (Localization.Away (MvPolynomial.rename e p)) r (by
      rw [Submonoid.map_powers]
      rfl)
  exact (testSpec k).mapIso (CommAlgCat.isoMk j).op

/-- Surjectivity on points over every algebraically closed extension implies
surjectivity on the underlying schemes. -/
private theorem surjective_of_algebraicallyClosedPoints {k : Type u} [Field k]
    {X Y : SchemeOver k} (f : X ⟶ Y)
    (hf : ∀ (E : Type u) [Field E] [Algebra k E] [IsAlgClosed E],
      Function.Surjective (fun p : Points X (CommAlgCat.of k E) => p ≫ f)) :
    Surjective f.left := by
  constructor
  intro y
  let R := Y.left.residueField y
  let a := Spec.fullyFaithful.preimage (Y.left.fromSpecResidueField y ≫ Y.hom)
  let : Algebra k R := a.unop.hom.toAlgebra
  let yR : Points Y (CommAlgCat.of k R) :=
    Over.homMk (Y.left.fromSpecResidueField y) (Spec.fullyFaithful.map_preimage _).symm
  let E := AlgebraicClosure R
  let : Algebra k E := ((algebraMap R E).comp (algebraMap k R)).toAlgebra
  let b : R →ₐ[k] E :=
    { toRingHom := algebraMap R E
      commutes' := fun _ => rfl }
  obtain ⟨x, hx⟩ := hf E (mapPoints (CommAlgCat.ofHom b) yR)
  let z : ((testSpec k).obj (op (CommAlgCat.of k E))).left := IsLocalRing.closedPoint E
  refine ⟨x.left z, ?_⟩
  change (x ≫ f).left z = y
  exact (congrArg (fun w : Points Y (CommAlgCat.of k E) => w.left z) hx).trans
    (Y.left.fromSpecResidueField_apply y _)

private theorem piMap_surjective_of_algebraicallyClosedPoints
    {k : Type u} [Field k] {m : ℕ} {X Y : Fin m → SchemeOver k} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i (E : Type u) [Field E] [Algebra k E] [IsAlgClosed E],
      Function.Surjective (fun p : Points (X i) (CommAlgCat.of k E) => p ≫ f i)) :
    Surjective (Limits.Pi.map f).left := by
  apply surjective_of_algebraicallyClosedPoints (Limits.Pi.map f)
  intro E _ _ _ y
  choose x hx using fun i => hf i E (y ≫ Pi.π Y i)
  refine ⟨Pi.lift x, ?_⟩
  apply Limits.Pi.hom_ext
  intro i
  rw [Category.assoc, Limits.Pi.map_π, ← Category.assoc, Limits.Pi.lift_comp_π]
  exact hx i

/-- Replace a finite product of principal opens by one principal open in affine space. -/
private theorem principalOpen_of_product {k : Type u} [Field k] {m : ℕ} (n : Fin m → ℕ)
    (p : ∀ i, MvPolynomial (ULift.{u} (Fin (n i))) k) (hp : ∀ i, p i ≠ 0) :
    ∃ (d : ℕ) (q : MvPolynomial (ULift.{u} (Fin d)) k), q ≠ 0 ∧
      Nonempty (PrincipalOpen q ≅ ∏ᶜ fun i => PrincipalOpen (p i)) := by
  classical
  let σ (i : Fin m) := ULift.{u} (Fin (n i))
  let d := Fintype.card (Σ i, σ i)
  let e : (Σ i, σ i) ≃ ULift.{u} (Fin d) :=
    (Fintype.equivFin _).trans Equiv.ulift.symm
  refine ⟨d, MvPolynomial.rename e (productPolynomial p), ?_,
    ⟨principalOpenReindex e (productPolynomial p) ≪≫ principalOpenProductIso p⟩⟩
  intro h
  apply productPolynomial_ne_zero p hp
  exact (MvPolynomial.rename_injective e e.injective) (h.trans (map_zero _).symm)

/-- A principal affine cover of a torus, surjective on geometric points. -/
private theorem torusCover {k : Type u} [Field k] [CharZero k]
    (T : AffineAlgebraicGroup k) (hT : IsTorus T.val) :
    ∃ (n : ℕ) (p : MvPolynomial (ULift.{u} (Fin n)) k)
      (_ : p ≠ 0) (f : PrincipalOpen p ⟶ T.val.X),
      ∀ (E : Type u) [Field E] [Algebra k E] [IsAlgClosed E],
        Function.Surjective (fun x : Points (PrincipalOpen p) (CommAlgCat.of k E) => x ≫ f) := by
  obtain ⟨m, n, p, hp, f, hf⟩ := TorusNormCovers.torusCoversByProducts T hT
  obtain ⟨d, q, hq, ⟨e⟩⟩ := principalOpen_of_product n p hp
  refine ⟨d, q, hq, e.hom ≫ f, ?_⟩
  intro E _ _ _ y
  obtain ⟨x, hx⟩ := hf E y
  exact ⟨x ≫ e.inv, by simpa [Category.assoc] using hx⟩

/-- The torus norm covers and ordered multiplication give a dominant map
from a principal open. Shrink to its smooth locus and translate to the identity. -/
theorem smoothPointedParametrization :
    Specs.WeakApproximationTorusParameters.SmoothPointedParametrization.{u} := by
  classical
  intro k _ _ G hG
  obtain ⟨m, T, hT, hdom⟩ := DominantTorusProducts.dominantTorusProducts G hG
  choose n p hp f hf using fun i =>
    torusCover (Specs.Unipotent.closedSubgroupAlgebraicGroup (T i)) (hT i)
  let φ := Limits.Pi.map f
  have hs : Surjective φ.left := piMap_surjective_of_algebraicallyClosedPoints f hf
  obtain ⟨d, q, hq, ⟨j⟩⟩ := principalOpen_of_product n p hp
  let g : PrincipalOpen q ⟶ G.val.X := j.hom ≫ φ ≫ orderedSubgroupProduct T
  have hg : IsDominant g.left := by
    have h₁ : IsIso j.hom.left :=
      (Over.forget (Spec (CommRingCat.of k))).map_isIso j.hom
    have h₂ : IsDominant j.hom.left := inferInstance
    have h₃ : IsDominant φ.left := inferInstance
    change IsDominant (j.hom.left ≫ φ.left ≫ (orderedSubgroupProduct T).left)
    exact ⟨(hdom.denseRange.comp h₃.denseRange (orderedSubgroupProduct T).left.continuous).comp
      h₂.denseRange (φ.left ≫ (orderedSubgroupProduct T).left).continuous⟩
  exact ⟨d, pointed_of_dominant_morphism G hG.1 d hq g hg⟩

end

end LinearAlgebraicGroups.Arithmetic.WeakApproximationTorusParameters
