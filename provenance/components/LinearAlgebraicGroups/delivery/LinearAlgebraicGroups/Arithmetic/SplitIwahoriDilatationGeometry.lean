import Specs.LinearAlgebraicGroups.Arithmetic.SplitIwahoriDilatationGeometry
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TensorProduct.Quotient

namespace LinearAlgebraicGroups.Arithmetic.SplitIwahoriDilatationGeometry

open Specs.SplitIwahoriDilatationGeometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

section AffineDilatation

variable {R A T : Type*} [CommRing R] [CommRing A] [CommRing T]
  [Algebra R A] [Algebra R T]

/-- The coordinate ring with the centre divisor inverted. -/
abbrev InvertedUniformizer (A : Type*) [CommRing A] [Algebra R A] (π : R) :=
  Localization.Away (algebraMap R A π)

/-- The coordinate algebra of the affine dilatation along a closed subscheme
with ideal `J` containing the centre divisor. -/
def dilatationAlgebra (π : R) (J : Ideal A) : Subalgebra R (InvertedUniformizer A π) :=
  Algebra.adjoin R (Set.range (algebraMap A (InvertedUniformizer A π)) ∪
    (fun a : A => algebraMap A (InvertedUniformizer A π) a *
      IsLocalization.Away.invSelf (S := InvertedUniformizer A π) (algebraMap R A π)) '' (J : Set A))

/-- The morphism to the original affine scheme, expressed on algebras. -/
def toDilatationAlgebra (π : R) (J : Ideal A) : A →ₐ[R] dilatationAlgebra π J :=
  (IsScalarTower.toAlgHom R A (InvertedUniformizer A π)).codRestrict _
    (fun a => Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩))

private def dividedElement (π : R) (J : Ideal A) (a : J) : dilatationAlgebra π J :=
  ⟨algebraMap A (InvertedUniformizer A π) a.val *
    IsLocalization.Away.invSelf (S := InvertedUniformizer A π) (algebraMap R A π),
    Algebra.subset_adjoin (Or.inr ⟨a.val, a.property, rfl⟩)⟩

private theorem mul_dividedElement (π : R) (J : Ideal A) (a : J) :
    toDilatationAlgebra π J (algebraMap R A π) * dividedElement π J a =
      toDilatationAlgebra π J a.val := by
  apply Subtype.ext
  change algebraMap A (InvertedUniformizer A π) (algebraMap R A π) *
    (algebraMap A (InvertedUniformizer A π) a.val *
      IsLocalization.Away.invSelf (S := InvertedUniformizer A π) (algebraMap R A π)) = _
  rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]
  rfl

private theorem injective_inverted (π : R) (hπ : algebraMap R T π ∈ nonZeroDivisors T) :
    Function.Injective (algebraMap T (InvertedUniformizer T π)) :=
  IsLocalization.injective _ (Submonoid.powers_le.mpr hπ)

private def mapInverted (π : R) (f : A →ₐ[R] T) :
    InvertedUniformizer A π →ₐ[R] InvertedUniformizer T π := by
  letI : IsLocalization.Away (f (algebraMap R A π)) (InvertedUniformizer T π) := by
    rw [f.commutes]
    infer_instance
  exact IsLocalization.Away.mapₐ _ _ f (algebraMap R A π)

private theorem mapInverted_algebraMap (π : R) (f : A →ₐ[R] T) (a : A) :
    mapInverted π f (algebraMap A (InvertedUniformizer A π) a) = algebraMap T (InvertedUniformizer T π) (f a) := by
  let h : IsLocalization.Away (f (algebraMap R A π)) (InvertedUniformizer T π) := by
    rw [f.commutes]
    infer_instance
  have hp : Submonoid.powers (algebraMap R A π) ≤
      (Submonoid.powers (f (algebraMap R A π))).comap f.toRingHom := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, (map_pow f _ _).symm⟩
  exact IsLocalization.map_eq (Q := InvertedUniformizer T π) hp a

private theorem mapInverted_mem_range (π : R) (J : Ideal A) (f : A →ₐ[R] T)
    (h : ∀ a ∈ J, algebraMap R T π ∣ f a) (z : dilatationAlgebra π J) :
    mapInverted π f z.val ∈ (IsScalarTower.toAlgHom R T (InvertedUniformizer T π)).range := by
  let S := (IsScalarTower.toAlgHom R T (InvertedUniformizer T π)).range
  have hs : dilatationAlgebra π J ≤ S.comap (mapInverted π f) := by
    apply Algebra.adjoin_le
    rintro _ (⟨a, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact ⟨f a, mapInverted_algebraMap π f a |>.symm⟩
    · obtain ⟨b, hb⟩ := h a ha
      refine ⟨b, ?_⟩
      have hu := IsLocalization.Away.mul_invSelf (S := InvertedUniformizer A π) (algebraMap R A π)
      have hu' := congrArg (mapInverted π f) hu
      simp only [map_mul, map_one, mapInverted_algebraMap, f.commutes] at hu'
      change algebraMap T (InvertedUniformizer T π) b = _
      rw [map_mul]
      change _ = mapInverted π f (algebraMap A (InvertedUniformizer A π) a) *
        mapInverted π f (IsLocalization.Away.invSelf (S := InvertedUniformizer A π) (algebraMap R A π))
      rw [mapInverted_algebraMap π f a, hb, map_mul, mul_right_comm, hu', one_mul]
  exact hs z.property

/-- The affine universal property on a test algebra on which multiplication
by the centre divisor is injective. -/
theorem dilatationAlgebra_universal (π : R) (J : Ideal A) (f : A →ₐ[R] T)
    (hπ : algebraMap R T π ∈ nonZeroDivisors T) :
    (∀ a ∈ J, algebraMap R T π ∣ f a) ↔
      ∃! g : dilatationAlgebra π J →ₐ[R] T, g.comp (toDilatationAlgebra π J) = f := by
  constructor
  · intro h
    let ι := IsScalarTower.toAlgHom R T (InvertedUniformizer T π)
    let e : T ≃ₐ[R] ι.range := AlgEquiv.ofInjective ι (injective_inverted π hπ)
    let g : dilatationAlgebra π J →ₐ[R] T := e.symm.toAlgHom.comp
      (((mapInverted π f).comp (dilatationAlgebra π J).val).codRestrict _
        (mapInverted_mem_range π J f h))
    have hg : g.comp (toDilatationAlgebra π J) = f := by
      ext a
      apply e.injective
      change e (g (toDilatationAlgebra π J a)) = e (f a)
      simp only [g, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
      apply Subtype.ext
      exact mapInverted_algebraMap π f a
    refine ⟨g, hg, fun k hk => ?_⟩
    have hd (a : J) (l : dilatationAlgebra π J →ₐ[R] T)
        (hl : l.comp (toDilatationAlgebra π J) = f) :
        algebraMap R T π * l (dividedElement π J a) = f a.val := by
      have he := congrArg l (mul_dividedElement π J a)
      have hl' (x : A) : l (toDilatationAlgebra π J x) = f x := DFunLike.congr_fun hl x
      simpa only [map_mul, hl', f.commutes] using he
    have hc (a : J) : k (dividedElement π J a) = g (dividedElement π J a) := by
      have hh := (hd a k hk).trans (hd a g hg).symm
      apply sub_eq_zero.mp
      apply mem_nonZeroDivisors_iff_left.mp hπ
      simp [mul_sub, hh]
    apply AlgHom.ext
    intro z
    refine Algebra.adjoin_induction
      (p := fun x hx => k ⟨x, hx⟩ = g ⟨x, hx⟩) ?_ ?_ ?_ ?_ z.property
    · rintro _ (⟨a, rfl⟩ | ⟨a, ha, rfl⟩)
      · exact (DFunLike.congr_fun hk a).trans (DFunLike.congr_fun hg a).symm
      · exact hc ⟨a, ha⟩
    · intro r
      exact (k.commutes r).trans (g.commutes r).symm
    · intro x y hx hy ihx ihy
      change k (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
    · intro x y hx hy ihx ihy
      change k (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]
  · rintro ⟨g, hg, _⟩ a ha
    refine ⟨g (dividedElement π J ⟨a, ha⟩), ?_⟩
    have he := congrArg g (mul_dividedElement π J ⟨a, ha⟩)
    have hg' (x : A) : g (toDilatationAlgebra π J x) = f x := DFunLike.congr_fun hg x
    simpa only [map_mul, hg', f.commutes] using he.symm

/-- After inverting the uniformizer, the dilatation algebra has the same
localization as the original coordinate ring. -/
theorem dilatationAlgebra_isLocalization (π : R) (J : Ideal A) :
    IsLocalization.Away (algebraMap R (dilatationAlgebra π J) π) (InvertedUniformizer A π) := by
  let δ := algebraMap R (dilatationAlgebra π J) π
  let B := InvertedUniformizer A π
  have hδ : algebraMap (dilatationAlgebra π J) B δ = algebraMap A B (algebraMap R A π) := by
    exact IsScalarTower.algebraMap_apply R A B π
  change IsLocalization (Submonoid.powers δ) B
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [map_pow, hδ]
    exact (IsLocalization.map_units B
      (⟨algebraMap R A π, Submonoid.mem_powers _⟩ :
        Submonoid.powers (algebraMap R A π))).pow n
  · intro z
    obtain ⟨⟨a, q⟩, h⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R A π)) z
    obtain ⟨n, hn⟩ := q.property
    change (algebraMap R A π) ^ n = (q : A) at hn
    refine ⟨⟨toDilatationAlgebra π J a, δ ^ n, ⟨n, rfl⟩⟩, ?_⟩
    change z * algebraMap (dilatationAlgebra π J) B (δ ^ n) = algebraMap A B a
    rw [map_pow, hδ, ← map_pow, hn]
    exact h
  · intro x y hxy
    exact ⟨1, by simpa using Subtype.ext hxy⟩

/-- The localization comparison on the generic coordinate algebras. -/
def dilatationAlgebraAwayEquiv (π : R) (J : Ideal A) :
    Localization.Away (algebraMap R (dilatationAlgebra π J) π) ≃ₐ[dilatationAlgebra π J]
      InvertedUniformizer A π :=
  letI := dilatationAlgebra_isLocalization π J
  IsLocalization.algEquiv (Submonoid.powers (algebraMap R (dilatationAlgebra π J) π)) _ _

/-- Multiplication by the centre divisor is injective on the dilatation
algebra, since the divisor is a unit in the ambient localization. -/
theorem dilatationAlgebra_regular (π : R) (J : Ideal A) :
    algebraMap R (dilatationAlgebra π J) π ∈ nonZeroDivisors (dilatationAlgebra π J) := by
  rw [mem_nonZeroDivisors_iff_left]
  intro x hx
  apply Subtype.ext
  have h := congrArg Subtype.val hx
  change algebraMap R (InvertedUniformizer A π) π * x.val = 0 at h
  rw [IsScalarTower.algebraMap_apply R A (InvertedUniformizer A π)] at h
  have hπ := IsLocalization.map_units (InvertedUniformizer A π)
    (⟨algebraMap R A π, Submonoid.mem_powers _⟩ : Submonoid.powers (algebraMap R A π))
  exact (hπ.mul_left_cancel (h.trans (mul_zero _).symm))

/-- An affine flat test algebra factors through the dilatation precisely when
reduction of the original morphism kills the centre ideal. -/
theorem dilatationAlgebra_factors [IsDomain R] [Module.Flat R T] (π : R) (hπ : π ≠ 0)
    (J : Ideal A) (f : A →ₐ[R] T) :
    (∀ a ∈ J, Ideal.Quotient.mk (Ideal.span {algebraMap R T π}) (f a) = 0) ↔
      ∃! g : dilatationAlgebra π J →ₐ[R] T, g.comp (toDilatationAlgebra π J) = f := by
  have hregular : algebraMap R T π ∈ nonZeroDivisors T := by
    rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    have hi := isRegular_iff_ne_zero.mpr hπ |>.isSMulRegular (M := T)
    apply hi
    simpa only [Algebra.smul_def, mul_zero] using hx
  simpa only [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using
    dilatationAlgebra_universal π J f hregular

/-- The affine dilatation over a discrete valuation ring is flat over the
valuation ring. -/
theorem dilatationAlgebra_flat [IsDomain R] [IsDiscreteValuationRing R] (π : R)
    (hπ : Irreducible π) (J : Ideal A) : Module.Flat R (dilatationAlgebra π J) := by
  have h : Module.IsTorsionFree R (dilatationAlgebra π J) := by
    constructor
    intro r hr x y hxy
    have hr₀ := isRegular_iff_ne_zero.mp hr
    obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr₀ hπ
    have hπunit := IsLocalization.map_units (InvertedUniformizer A π)
      (⟨algebraMap R A π, Submonoid.mem_powers _⟩ : Submonoid.powers (algebraMap R A π))
    have hu : IsUnit (algebraMap R (InvertedUniformizer A π) ((v : R) * π ^ n)) := by
      rw [map_mul, map_pow, IsScalarTower.algebraMap_apply R A (InvertedUniformizer A π) π]
      exact ((v.isUnit).map (algebraMap R (InvertedUniformizer A π))).mul (hπunit.pow n)
    apply Subtype.ext
    apply hu.mul_left_cancel
    simpa only [Algebra.smul_def, Subalgebra.coe_mul, Subalgebra.coe_algebraMap] using
      congrArg Subtype.val hxy
  infer_instance

end AffineDilatation

section SchemeDilatation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite


variable {R A T : Type u} [CommRing R] [CommRing A] [CommRing T]
  [Algebra R A] [Algebra R T]

private abbrev specQuotient {T : Type u} [CommRing T] (I : Ideal T) :
    Spec (CommRingCat.of (T ⧸ I)) ⟶ Spec (CommRingCat.of T) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

private def quotientPullbackIso (I : Ideal R) :
    Spec (CommRingCat.of (T ⧸ I.map (algebraMap R T))) ≅
      pullback (algebraScheme R T).hom (specQuotient I) :=
  Scheme.Spec.mapIso
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot T I).symm.toRingEquiv.toCommRingCatIso.op ≪≫
      (pullbackSpecIso R T (R ⧸ I)).symm

@[reassoc]
private theorem quotientPullbackIso_fst (I : Ideal R) :
    (quotientPullbackIso (T := T) I).hom ≫
      pullback.fst (algebraScheme R T).hom (specQuotient I) =
        specQuotient (I.map (algebraMap R T)) := by
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot T I
  change (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      (pullbackSpecIso R T (R ⧸ I)).inv) ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R T))) (specQuotient I) = _
  rw [Category.assoc, pullbackSpecIso_inv_fst', ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun t => e.symm.commutes t)

private theorem quotient_factors_iff (J : Ideal A) (I : Ideal T) (f : A →ₐ[R] T) :
    (∃ b : Spec (CommRingCat.of (T ⧸ I)) ⟶ Spec (CommRingCat.of (A ⧸ J)),
      b ≫ specQuotient J = specQuotient I ≫ (algebraSchemeMap f).left) ↔
    ∀ a ∈ J, Ideal.Quotient.mk I (f a) = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨q, rfl⟩ := Spec.map_surjective b
    have h : CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ q =
        CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      apply Spec.map_injective
      change Spec.map q ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
            Spec.map (CommRingCat.ofHom f.toRingHom) at hb
      simpa only [Spec.map_comp] using hb
    intro a ha
    have h' := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) a
    simpa [Ideal.Quotient.eq_zero_iff_mem.mpr ha] using h'.symm
  · intro h
    let q := Ideal.Quotient.liftₐ J ((Ideal.Quotient.mkₐ R I).comp f) h
    refine ⟨Spec.map (CommRingCat.ofHom q.toRingHom), ?_⟩
    change Spec.map (CommRingCat.ofHom q.toRingHom) ≫ specQuotient J =
      specQuotient I ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1


private theorem affineSpecMap_existsUnique_iff {B : Type u} [CommRing B] [Algebra R B]
    (a : A →ₐ[R] B) (f : A →ₐ[R] T) :
    (∃! q : algebraScheme R T ⟶ algebraScheme R B,
      q ≫ algebraSchemeMap a = algebraSchemeMap f) ↔
    ∃! q : B →ₐ[R] T, q.comp a = f := by
  let F := algSpec (CommRingCat.of R)
  let ff := algSpec.fullyFaithful (R := CommRingCat.of R)
  let E : (B →ₐ[R] T) ≃ (algebraScheme R T ⟶ algebraScheme R B) :=
    ((show (B →ₐ[R] T) ≃ (CommAlgCat.of R B ⟶ CommAlgCat.of R T) from
      ⟨CommAlgCat.ofHom, CommAlgCat.Hom.hom, fun _ => rfl, CommAlgCat.ofHom_hom⟩).trans
      Quiver.Hom.opEquiv).trans ff.homEquiv
  have he (q : B →ₐ[R] T) :
      E q ≫ algebraSchemeMap a = algebraSchemeMap f ↔ q.comp a = f := by
    change F.map (CommAlgCat.ofHom q).op ≫ F.map (CommAlgCat.ofHom a).op =
      F.map (CommAlgCat.ofHom f).op ↔ _
    rw [← Functor.map_comp]
    change F.map (CommAlgCat.ofHom (q.comp a)).op = F.map (CommAlgCat.ofHom f).op ↔ _
    constructor
    · intro h
      exact congrArg (fun s => s.unop.hom) (ff.map_injective h)
    · rintro rfl
      rfl
  constructor
  · rintro ⟨q, hq, hu⟩
    refine ⟨E.symm q, (he _).mp ?_, fun b hb => ?_⟩
    · rw [Equiv.apply_symm_apply]
      exact hq
    · apply E.injective
      rw [Equiv.apply_symm_apply]
      exact hu _ ((he _).mpr hb)
  · rintro ⟨q, hq, hu⟩
    refine ⟨E q, (he _).mpr hq, fun b hb => ?_⟩
    have h := he (E.symm b)
    rw [Equiv.apply_symm_apply] at h
    rw [← E.apply_symm_apply b, hu _ (h.mp hb)]

/-- The dilatation represents the special-fibre factorization condition
on affine flat test schemes. -/
theorem dilatation_affine_universal [IsDomain R] [Module.Flat R T] (π : R) (hπ : π ≠ 0)
    (J : Ideal A) (f : A →ₐ[R] T) :
    (∃ b : pullback (algebraScheme R T).hom (specQuotient (Ideal.span {π})) ⟶
        Spec (CommRingCat.of (A ⧸ J)),
      b ≫ specQuotient J = pullback.fst _ _ ≫ (algebraSchemeMap f).left) ↔
    ∃! q : algebraScheme R T ⟶ algebraScheme R (dilatationAlgebra π J),
        q ≫ algebraSchemeMap (toDilatationAlgebra π J) = algebraSchemeMap f := by
  let I : Ideal R := Ideal.span {π}
  let e := quotientPullbackIso (T := T) I
  have h : I.map (algebraMap R T) = Ideal.span {algebraMap R T π} := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [affineSpecMap_existsUnique_iff, ← dilatationAlgebra_factors π hπ]
  rw [← h, ← quotient_factors_iff]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨e.hom ≫ b, ?_⟩
    have hf := quotientPullbackIso_fst (T := T) I
    exact (Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) hb).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (algebraSchemeMap f).left) hf)))
  · rintro ⟨b, hb⟩
    refine ⟨e.inv ≫ b, ?_⟩
    have hf := quotientPullbackIso_fst (T := T) I
    have hf' : e.inv ≫ specQuotient (I.map (algebraMap R T)) =
        pullback.fst (algebraScheme R T).hom (specQuotient I) :=
      (congrArg (e.inv ≫ ·) hf.symm).trans (e.inv_hom_id_assoc _)
    exact (Category.assoc _ _ _).trans ((congrArg (e.inv ≫ ·) hb).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (algebraSchemeMap f).left) hf')))

private def FactorsOnBaseChange {S B : Scheme.{u}} (d : B ⟶ S)
    {G X : Over S} {Z : Scheme.{u}} (c : Z ⟶ G.left) (f : X ⟶ G) : Prop :=
  ∃ b : ((Over.pullback d).obj X).left ⟶ Z,
    b ≫ c = pullback.fst X.hom d ≫ f.left

@[reassoc]
private theorem pullback_left_natural {S B : Scheme.{u}} (d : B ⟶ S)
    {X Y : Over S} (m : X ⟶ Y) :
    ((Over.pullback d).map m).left ≫ pullback.fst Y.hom d = pullback.fst X.hom d ≫ m.left := by
  change pullback.lift (pullback.fst X.hom d ≫ m.left) (pullback.snd X.hom d) _ ≫
    pullback.fst Y.hom d = _
  exact pullback.lift_fst _ _ _

private theorem FactorsOnBaseChange.comp {S B : Scheme.{u}} {d : B ⟶ S}
    {G X W : Over S} {Z : Scheme.{u}} {c : Z ⟶ G.left} {f : X ⟶ G}
    (h : FactorsOnBaseChange d c f) (m : W ⟶ X) : FactorsOnBaseChange d c (m ≫ f) := by
  obtain ⟨b, hb⟩ := h
  refine ⟨((Over.pullback d).map m).left ≫ b, ?_⟩
  rw [Category.assoc, hb, pullback_left_natural_assoc, Over.comp_left]

private theorem schemeFlat_of_spec [Module.Flat R T] : Flat (algebraScheme R T).hom := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap R T)))
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

private theorem dilatation_isAffine_universal [IsDomain R] (π : R) (hπ : π ≠ 0)
    (J : Ideal A) {X : Over (Spec (CommRingCat.of R))}
    (hX : IsAffine X.left) (hflat : Flat X.hom) (f : X ⟶ algebraScheme R A) :
    FactorsOnBaseChange (specQuotient (Ideal.span {π})) (specQuotient J) f ↔
      ∃! q : X ⟶ algebraScheme R (dilatationAlgebra π J),
          q ≫ algebraSchemeMap (toDilatationAlgebra π J) = f := by
  let d := specQuotient (Ideal.span {π})
  let c := specQuotient J
  let F := algSpec (CommRingCat.of R)
  obtain ⟨T, ⟨e⟩⟩ := (essImage_algSpec (G := X)).mpr hX
  have hf : Flat (algebraScheme R T.unop).hom := by
    have he : (algebraScheme R T.unop).hom = e.hom.left ≫ X.hom := (Over.w e.hom).symm
    rw [he]
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    infer_instance
  have : Module.Flat R T.unop :=
    RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hf)
  let ff := algSpec.fullyFaithful (R := CommRingCat.of R)
  let g := ff.preimage (e.hom ≫ f)
  let a : A →ₐ[R] T.unop := g.unop.hom
  have ha : algebraSchemeMap a = e.hom ≫ f := by
    change F.map (CommAlgCat.ofHom g.unop.hom).op = _
    rw [CommAlgCat.ofHom_hom]
    exact ff.map_preimage (e.hom ≫ f)
  have hc : FactorsOnBaseChange d c (e.hom ≫ f) ↔ FactorsOnBaseChange d c f := by
    constructor
    · intro h
      simpa using h.comp e.inv
    · exact fun h => h.comp e.hom
  have heq := dilatation_affine_universal π hπ J a
  change FactorsOnBaseChange d c (algebraSchemeMap a) ↔ _ at heq
  rw [ha] at heq
  rw [← hc, heq]
  apply (Iso.homCongr e (Iso.refl _)).existsUnique_congr
  intro q
  change q ≫ algebraSchemeMap (toDilatationAlgebra π J) = e.hom ≫ f ↔
    (e.inv ≫ q ≫ 𝟙 _) ≫ algebraSchemeMap (toDilatationAlgebra π J) = f
  simp only [Category.comp_id, Category.assoc]
  constructor
  · intro h
    rw [h, e.inv_hom_id_assoc]
  · intro h
    rw [← h, e.hom_inv_id_assoc]

private theorem dilatation_factors_special [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (J : Ideal A) :
    FactorsOnBaseChange (specQuotient (Ideal.span {π})) (specQuotient J)
      (algebraSchemeMap (toDilatationAlgebra π J)) := by
  have : Module.Flat R (dilatationAlgebra π J) := dilatationAlgebra_flat π hπ J
  have hd (a : A) (ha : a ∈ J) :
      Ideal.Quotient.mk (Ideal.span {algebraMap R (dilatationAlgebra π J) π})
        (toDilatationAlgebra π J a) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    refine ⟨dividedElement π J ⟨a, ha⟩, ?_⟩
    rw [← (toDilatationAlgebra π J).commutes, mul_dividedElement]
  have h₁ := (dilatationAlgebra_factors π hπ.ne_zero J (toDilatationAlgebra π J)).mp hd
  have h₂ := (affineSpecMap_existsUnique_iff (toDilatationAlgebra π J)
    (toDilatationAlgebra π J)).mpr h₁
  exact (dilatation_affine_universal π hπ.ne_zero J (toDilatationAlgebra π J)).mpr h₂

private theorem dilatation_hom_ext [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π)
    (J : Ideal A) {X : Over (Spec (CommRingCat.of R))} (hflat : Flat X.hom)
    {g h : X ⟶ algebraScheme R (dilatationAlgebra π J)}
    (heq : g ≫ algebraSchemeMap (toDilatationAlgebra π J) =
      h ≫ algebraSchemeMap (toDilatationAlgebra π J)) : g = h := by
  let 𝒰 := X.left.affineCover
  apply Over.OverMorphism.ext
  apply 𝒰.hom_ext
  intro i
  let xi : Over (Spec (CommRingCat.of R)) := Over.mk (𝒰.f i ≫ X.hom)
  let ui : xi ⟶ X := Over.homMk (𝒰.f i)
  have ha : IsAffine xi.left := by
    change IsAffine (X.left.affineCover.X i)
    dsimp [Scheme.affineCover]
    infer_instance
  have hf : Flat xi.hom := by
    change Flat (𝒰.f i ≫ X.hom)
    have : IsOpenImmersion (𝒰.f i) := inferInstance
    infer_instance
  let c := algebraSchemeMap (toDilatationAlgebra π J)
  have hl : (ui ≫ g) ≫ c = ui ≫ (h ≫ c) := by
    rw [Category.assoc, heq]
  have hr : (ui ≫ h) ≫ c = ui ≫ (h ≫ c) := Category.assoc _ _ _
  have hh := (dilatation_factors_special π hπ J).comp (ui ≫ h)
  have hex := (dilatation_isAffine_universal π hπ.ne_zero J ha hf (ui ≫ (h ≫ c))).mp
    (by simpa only [c, Category.assoc] using hh)
  exact congrArg Over.Hom.left (hex.unique hl hr)

/-- The affine dilatation has the same factorization property on every
flat test scheme over the discrete valuation ring. -/
theorem dilatation_scheme_universal [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (J : Ideal A) {X : Over (Spec (CommRingCat.of R))}
    (hflat : Flat X.hom) (f : X ⟶ algebraScheme R A) :
    FactorsOnBaseChange (specQuotient (Ideal.span {π})) (specQuotient J) f ↔
      ∃! q : X ⟶ algebraScheme R (dilatationAlgebra π J),
          q ≫ algebraSchemeMap (toDilatationAlgebra π J) = f := by
  let d := algebraScheme R (dilatationAlgebra π J)
  let c := algebraSchemeMap (toDilatationAlgebra π J)
  constructor
  · intro h
    let 𝒰 := X.left.affineCover
    let xi (i : 𝒰.I₀) : Over (Spec (CommRingCat.of R)) := Over.mk (𝒰.f i ≫ X.hom)
    let ui (i : 𝒰.I₀) : xi i ⟶ X := Over.homMk (𝒰.f i)
    have ha (i : 𝒰.I₀) : IsAffine (xi i).left := by
      change IsAffine (X.left.affineCover.X i)
      dsimp [Scheme.affineCover]
      infer_instance
    have hf (i : 𝒰.I₀) : Flat (xi i).hom := by
      change Flat (𝒰.f i ≫ X.hom)
      have : IsOpenImmersion (𝒰.f i) := inferInstance
      infer_instance
    have hl (i : 𝒰.I₀) : ∃ q : xi i ⟶ d, q ≫ c = ui i ≫ f :=
      ((dilatation_isAffine_universal π hπ.ne_zero J (ha i) (hf i) (ui i ≫ f)).mp
        (h.comp (ui i))).exists
    choose q hq using hl
    have hcompat (i j : 𝒰.I₀) :
        pullback.fst (𝒰.f i) (𝒰.f j) ≫ (q i).left =
          pullback.snd (𝒰.f i) (𝒰.f j) ≫ (q j).left := by
      let p₁ := pullback.fst (𝒰.f i) (𝒰.f j)
      let p₂ := pullback.snd (𝒰.f i) (𝒰.f j)
      let z : Over (Spec (CommRingCat.of R)) := Over.mk (p₁ ≫ (xi i).hom)
      let zi : z ⟶ xi i := Over.homMk p₁
      let zj : z ⟶ xi j := Over.homMk p₂ (by
        change p₂ ≫ 𝒰.f j ≫ X.hom = p₁ ≫ 𝒰.f i ≫ X.hom
        exact (pullback.condition_assoc _).symm)
      have hflat' : Flat z.hom := by
        have hp : IsOpenImmersion (𝒰.f j) := inferInstance
        have : Flat (xi i).hom := hf i
        change Flat (p₁ ≫ (xi i).hom)
        infer_instance
      have hcomp : zi ≫ ui i = zj ≫ ui j := Over.OverMorphism.ext pullback.condition
      have he : (zi ≫ q i) ≫ c = (zj ≫ q j) ≫ c := by
        rw [Category.assoc, Category.assoc, hq, hq, ← Category.assoc zi, ← Category.assoc zj, hcomp]
      exact congrArg Over.Hom.left (dilatation_hom_ext π hπ J hflat' he)
    let q' := 𝒰.glueMorphisms (fun i => (q i).left) hcompat
    let q₀ : X ⟶ d := Over.homMk q' (by
      apply 𝒰.hom_ext
      intro i
      rw [← Category.assoc, 𝒰.ι_glueMorphisms]
      exact Over.w (q i))
    have h₀ : q₀ ≫ c = f := by
      apply Over.OverMorphism.ext
      apply 𝒰.hom_ext
      intro i
      change 𝒰.f i ≫ q' ≫ c.left = 𝒰.f i ≫ f.left
      rw [← Category.assoc, 𝒰.ι_glueMorphisms]
      exact congrArg Over.Hom.left (hq i)
    exact ⟨q₀, h₀, fun g hg => dilatation_hom_ext π hπ J hflat (hg.trans h₀.symm)⟩
  · rintro ⟨q, hq, _⟩
    exact hq ▸ (dilatation_factors_special π hπ J).comp q

end SchemeDilatation

section GroupDilatation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj


variable {S S₀ : Scheme.{u}} (j : S₀ ⟶ S)
  {G : Grp (Over S)} {H : Grp (Over S₀)}
  (b : H ⟶ ((Over.pullback j).mapGrp).obj G)

private theorem factorsThroughSpecialSubgroup_one {T : Over S} :
    FactorsThroughSpecialSubgroup j b (1 : T ⟶ G.X) := by
  let n : (T ⟶ G.X) →*
      ((Over.pullback j).obj T ⟶ (((Over.pullback j).mapGrp).obj G).X) :=
    (Over.pullback j).homMonoidHom (X := T) (M := G.X)
  refine ⟨1, ?_⟩
  exact ((IsMonHom.monoidHom b.hom.hom _).map_one).trans
    n.map_one.symm

private theorem factorsThroughSpecialSubgroup_mul {T : Over S} {x y : T ⟶ G.X}
    (hx : FactorsThroughSpecialSubgroup j b x) (hy : FactorsThroughSpecialSubgroup j b y) :
    FactorsThroughSpecialSubgroup j b (x * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨c, hc⟩ := hy
  let m := IsMonHom.monoidHom b.hom.hom ((Over.pullback j).obj T)
  let n : (T ⟶ G.X) →*
      ((Over.pullback j).obj T ⟶ (((Over.pullback j).mapGrp).obj G).X) :=
    (Over.pullback j).homMonoidHom (X := T) (M := G.X)
  change m a = n x at ha
  change m c = n y at hc
  refine ⟨a * c, ?_⟩
  change m (a * c) = n (x * y)
  rw [map_mul, map_mul, ha, hc]

private theorem factorsThroughSpecialSubgroup_inv {T : Over S} {x : T ⟶ G.X}
    (hx : FactorsThroughSpecialSubgroup j b x) : FactorsThroughSpecialSubgroup j b x⁻¹ := by
  obtain ⟨a, ha⟩ := hx
  let m := IsMonHom.monoidHom b.hom.hom ((Over.pullback j).obj T)
  let n : (T ⟶ G.X) →*
      ((Over.pullback j).obj T ⟶ (((Over.pullback j).mapGrp).obj G).X) :=
    (Over.pullback j).homMonoidHom (X := T) (M := G.X)
  change m a = n x at ha
  refine ⟨a⁻¹, ?_⟩
  change m a⁻¹ = n x⁻¹
  rw [map_inv, map_inv, ha]

private theorem factorsThroughSpecialSubgroup_comp {T X : Over S}
    {x : X ⟶ G.X} (hx : FactorsThroughSpecialSubgroup j b x) (a : T ⟶ X) :
    FactorsThroughSpecialSubgroup j b (a ≫ x) := by
  obtain ⟨z, hz⟩ := hx
  let F := Over.pullback j
  refine ⟨F.map a ≫ z, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (F.map a ≫ ·) hz).trans (F.map_comp a x).symm)

private theorem flat_over_tensor {X Y : Over S} [Flat X.hom] [Flat Y.hom] :
    Flat (X ⊗ Y).hom := by
  change Flat (pullback.fst X.hom Y.hom ≫ X.hom)
  infer_instance

/-- A flat scheme representing the special-subgroup condition acquires a
group law. The structure map to the integral group is a group homomorphism. -/
theorem groupStructure_of_dilatation {D : Over S} (hD : Flat D.hom) (p : D ⟶ G.X)
    (hp : FactorsThroughSpecialSubgroup j b p)
    (universal : ∀ {T : Over S}, Flat T.hom → ∀ f : T ⟶ G.X,
      FactorsThroughSpecialSubgroup j b f ↔ ∃! q : T ⟶ D, q ≫ p = f) :
    ∃ h : GrpObj D, @IsMonHom _ _ _ _ _ h.toMonObj G.grp.toMonObj p := by
  have hflat₀ : Flat (𝟙_ (Over S)).hom := by
    change Flat (𝟙 S)
    infer_instance
  have hflat₂ : Flat (D ⊗ D).hom := flat_over_tensor
  have hflat₃ : Flat ((D ⊗ D) ⊗ D).hom := flat_over_tensor
  let opOne := (universal hflat₀ 1).mp (factorsThroughSpecialSubgroup_one j b)
  let one := opOne.exists.choose
  have hone : one ≫ p = 1 := opOne.exists.choose_spec
  let opMul := (universal hflat₂ ((fst D D ≫ p) * (snd D D ≫ p))).mp
    (factorsThroughSpecialSubgroup_mul j b
      (factorsThroughSpecialSubgroup_comp j b hp _) (factorsThroughSpecialSubgroup_comp j b hp _))
  let mul := opMul.exists.choose
  have hmul : mul ≫ p = (fst D D ≫ p) * (snd D D ≫ p) := opMul.exists.choose_spec
  let opInv := (universal hD p⁻¹).mp (factorsThroughSpecialSubgroup_inv j b hp)
  let inv := opInv.exists.choose
  have hinv : inv ≫ p = p⁻¹ := opInv.exists.choose_spec
  have hext {T : Over S} (hT : Flat T.hom) {a c : T ⟶ D} (he : a ≫ p = c ≫ p) : a = c := by
    have h := factorsThroughSpecialSubgroup_comp j b hp c
    have hu := (universal hT _).mp h
    exact hu.unique he rfl
  have hm {T : Over S} (q : T ⟶ D ⊗ D) :
      q ≫ mul ≫ p = (q ≫ fst D D ≫ p) * (q ≫ snd D D ≫ p) := by
    rw [hmul, MonObj.comp_mul]
  let mon : MonObj D :=
    { one := one
      mul := mul
      one_mul := by
        apply hext (flat_over_tensor (X := 𝟙_ (Over S)) (Y := D))
        rw [Category.assoc, hm, whiskerRight_fst_assoc, whiskerRight_snd_assoc,
          hone, MonObj.comp_one, one_mul, leftUnitor_hom]
      mul_one := by
        apply hext (flat_over_tensor (X := D) (Y := 𝟙_ (Over S)))
        rw [Category.assoc, hm, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc,
          hone, MonObj.comp_one, mul_one, rightUnitor_hom]
      mul_assoc := by
        apply hext hflat₃
        simp only [Category.assoc, hm, MonObj.comp_mul, whiskerRight_fst_assoc, whiskerRight_snd_assoc,
          whiskerLeft_fst_assoc, whiskerLeft_snd_assoc,
          associator_hom_fst_assoc, associator_hom_snd_fst_assoc,
          associator_hom_snd_snd_assoc, mul_assoc] }
  let grp : GrpObj D :=
    { toMonObj := mon
      inv := inv
      left_inv := by
        apply hext hD
        change (lift inv (𝟙 D) ≫ mul) ≫ p = (toUnit D ≫ one) ≫ p
        rw [Category.assoc, Category.assoc, hm, lift_fst_assoc, lift_snd_assoc,
          Category.id_comp, hinv, inv_mul_cancel, hone, MonObj.comp_one]
      right_inv := by
        apply hext hD
        change (lift (𝟙 D) inv ≫ mul) ≫ p = (toUnit D ≫ one) ≫ p
        rw [Category.assoc, Category.assoc, hm, lift_fst_assoc, lift_snd_assoc,
          Category.id_comp, hinv, mul_inv_cancel, hone, MonObj.comp_one] }
  refine ⟨grp, ⟨?_, ?_⟩⟩
  · exact hone.trans (Category.id_comp _).symm
  · exact hmul.trans (by rw [Hom.mul_def, lift_fst_comp_snd_comp])

end GroupDilatation

section ClosedCentre

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj


private theorem factorsThroughSpecialSubgroup_iff {S S₀ : Scheme.{u}}
    (j : S₀ ⟶ S) [Mono j] {G : Grp (Over S)} {B : Grp (Over S₀)}
    (b : B ⟶ (Over.pullback j).mapGrp.obj G) {X : Over S} (f : X ⟶ G.X) :
    FactorsThroughSpecialSubgroup j b f ↔
      FactorsOnBaseChange j (b.hom.hom.left ≫ pullback.fst G.X.hom j) f := by
  let q := (Over.pullback j).map f
  let p₁ := pullback.fst G.X.hom j
  let p₂ := pullback.snd G.X.hom j
  have hq : q.left ≫ p₁ = pullback.fst X.hom j ≫ f.left :=
    pullback_left_natural j f
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a.left, ?_⟩
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun v : (Over.pullback j).obj X ⟶ (Over.pullback j).obj G.X =>
        v.left ≫ p₁) ha).trans hq)
  · rintro ⟨a, ha⟩
    have h₁ : (a ≫ b.hom.hom.left) ≫ p₁ = q.left ≫ p₁ :=
      (Category.assoc _ _ _).trans (ha.trans hq.symm)
    have h₂ : (a ≫ b.hom.hom.left) ≫ p₂ = q.left ≫ p₂ := by
      apply (cancel_mono j).mp
      have hc : p₁ ≫ G.X.hom = p₂ ≫ j := pullback.condition
      calc
        _ = (a ≫ b.hom.hom.left) ≫ (p₂ ≫ j) := Category.assoc _ _ _
        _ = ((a ≫ b.hom.hom.left) ≫ p₁) ≫ G.X.hom :=
          (congrArg ((a ≫ b.hom.hom.left) ≫ ·) hc.symm).trans (Category.assoc _ _ _).symm
        _ = (q.left ≫ p₁) ≫ G.X.hom := congrArg (· ≫ G.X.hom) h₁
        _ = _ := (Category.assoc _ _ _).trans
          ((congrArg (q.left ≫ ·) hc).trans (Category.assoc _ _ _).symm)
    let a' : (Over.pullback j).obj X ⟶ B.X := Over.homMk a (by
      change a ≫ B.X.hom = ((Over.pullback j).obj X).hom
      rw [← Over.w b.hom.hom, ← Category.assoc]
      exact h₂.trans (Over.w q))
    exact ⟨a', Over.OverMorphism.ext (pullback.hom_ext h₁ h₂)⟩

private theorem factorsOnBaseChange_iff_of_iso {S S₀ : Scheme.{u}} (j : S₀ ⟶ S)
    {G H X : Over S} {Z W : Scheme.{u}} (e : H ≅ G) (i : Z ≅ W)
    {c : Z ⟶ G.left} {d : W ⟶ H.left}
    (he : c ≫ e.inv.left = i.hom ≫ d) (f : X ⟶ G) :
    FactorsOnBaseChange j c f ↔ FactorsOnBaseChange j d (f ≫ e.inv) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a ≫ i.hom, ?_⟩
    simp only [Category.assoc, ← he, ← Category.assoc a, ha, Over.comp_left]
  · rintro ⟨a, ha⟩
    refine ⟨a ≫ i.inv, ?_⟩
    apply (cancel_mono e.inv.left).mp
    calc
      ((a ≫ i.inv) ≫ c) ≫ e.inv.left = a ≫ d := by
        simp only [Category.assoc, he, i.inv_hom_id_assoc]
      _ = (pullback.fst X.hom j ≫ f.left) ≫ e.inv.left :=
        ha.trans (Category.assoc _ _ _).symm

/-- The dilatation of a flat-test affine group model along a closed subgroup
of its special fibre is an affine flat group scheme with the same universal
factorization property. -/
theorem existsGroupDilatation {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (π : R) (hπ : Irreducible π)
    (G : Grp (Over (Spec (CommRingCat.of R)))) (hG : IsAffine G.X.left)
    (B : Grp (Over (Spec (CommRingCat.of (R ⧸ Ideal.span {π})))))
    (b : B ⟶ (Over.pullback (specQuotient (Ideal.span {π}))).mapGrp.obj G)
    (hb : IsClosedImmersion b.hom.hom.left) :
    ∃ (D : Grp (Over (Spec (CommRingCat.of R)))) (p : D ⟶ G),
      IsAffine D.X.left ∧ Flat D.X.hom ∧ RepresentsDilatation (closedPoint π) b p.hom.hom := by
  let j := specQuotient (Ideal.span {π})
  have : IsClosedImmersion j :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of R) (Ideal.span {π})
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (G := G.X)).mpr hG
  let c := b.hom.hom.left ≫ pullback.fst G.X.hom j
  have hclosed : IsClosedImmersion (c ≫ e.inv.left) := by
    let stable : MorphismProperty.IsStableUnderBaseChange
        (@IsClosedImmersion : MorphismProperty Scheme.{u}) :=
      IsClosedImmersion.isStableUnderBaseChange
    have hj : IsClosedImmersion (pullback.fst G.X.hom j) :=
      stable.of_isPullback (IsPullback.of_hasPullback G.X.hom j).flip ‹IsClosedImmersion j›
    have hi : IsIso e.inv.left :=
      inferInstanceAs (IsIso ((Over.forget _).map e.inv))
    have hc : IsClosedImmersion c :=
      @IsClosedImmersion.comp _ _ _ b.hom.hom.left (pullback.fst G.X.hom j) hb hj
    exact @IsClosedImmersion.comp _ _ _ c e.inv.left hc (inferInstance : IsClosedImmersion e.inv.left)
  obtain ⟨J, i, hi⟩ := (IsClosedImmersion.Spec_iff (R := CommRingCat.of A.unop)).mp hclosed
  let D := algebraScheme R (dilatationAlgebra π J)
  let d := algebraSchemeMap (toDilatationAlgebra π J)
  let p : D ⟶ G.X := d ≫ e.hom
  have hD : Flat D.hom := by
    let := dilatationAlgebra_flat π hπ J
    exact schemeFlat_of_spec
  have he : p ≫ e.inv = d :=
    (Category.assoc _ _ _).trans
      ((congrArg (d ≫ ·) e.hom_inv_id).trans (Category.comp_id d))
  have universal {X : Over (Spec (CommRingCat.of R))} (hX : Flat X.hom) (f : X ⟶ G.X) :
      FactorsThroughSpecialSubgroup j b f ↔ ∃! q : X ⟶ D, q ≫ p = f := by
    rw [factorsThroughSpecialSubgroup_iff, factorsOnBaseChange_iff_of_iso j e i hi,
      dilatation_scheme_universal π hπ J hX]
    apply existsUnique_congr
    intro q
    constructor
    · intro h
      calc
        q ≫ p = (q ≫ d) ≫ e.hom := (Category.assoc _ _ _).symm
        _ = (f ≫ e.inv) ≫ e.hom := congrArg (· ≫ e.hom) h
        _ = f := (Category.assoc _ _ _).trans
          ((congrArg (f ≫ ·) e.inv_hom_id).trans (Category.comp_id f))
    · intro h
      exact (congrArg (q ≫ ·) he.symm).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ e.inv) h))
  have hp : FactorsThroughSpecialSubgroup j b p := by
    rw [factorsThroughSpecialSubgroup_iff, factorsOnBaseChange_iff_of_iso j e i hi]
    rw [he]
    exact dilatation_factors_special π hπ J
  obtain ⟨g, hg⟩ := groupStructure_of_dilatation j b hD p hp universal
  let : GrpObj D := g
  let : IsMonHom p := hg
  have ha : IsAffine D.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of
    (dilatationAlgebra π J))))
  exact ⟨Grp.mk D, Grp.ofHom p, ha, hD, hp, fun {X} => universal (X := X)⟩

end ClosedCentre

section GenericFibre

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


private theorem factorsThroughSpecialSubgroup_of_disjoint {S S₀ V : Scheme.{u}}
    {j : S₀ ⟶ S} {g : V ⟶ S} (h : Disjoint (Set.range g) (Set.range j))
    {G : Grp (Over S)} {B : Grp (Over S₀)}
    (b : B ⟶ (Over.pullback j).mapGrp.obj G) (X : Over V)
    (f : (Over.map g).obj X ⟶ G.X) :
    FactorsThroughSpecialSubgroup j b f := by
  have hz : Disjoint (Set.range ((Over.map g).obj X).hom) (Set.range j) := by
    apply h.mono_left
    rintro _ ⟨x, rfl⟩
    exact ⟨X.hom x, rfl⟩
  let Y := (Over.pullback j).obj ((Over.map g).obj X)
  let : IsEmpty Y.left := Scheme.isEmpty_pullback_iff.mpr hz
  let z : Y ⟶ B.X := Over.homMk (isInitialOfIsEmpty.to B.X.left)
    (isInitialOfIsEmpty.hom_ext _ _)
  exact ⟨z, Over.OverMorphism.ext (isInitialOfIsEmpty.hom_ext _ _)⟩

/-- On a flat base change disjoint from the special divisor a dilatation
agrees with the original group. -/
theorem groupDilatation_iso_of_disjoint {S S₀ V : Scheme.{u}}
    {j : S₀ ⟶ S} {g : V ⟶ S} (h : Disjoint (Set.range g) (Set.range j)) [Flat g]
    {G D : Grp (Over S)} [Flat G.X.hom] [Flat D.X.hom]
    {B : Grp (Over S₀)} (b : B ⟶ (Over.pullback j).mapGrp.obj G) (p : D ⟶ G)
    (universal : ∀ {X : Over S}, Flat X.hom → ∀ f : X ⟶ G.X,
      FactorsThroughSpecialSubgroup j b f ↔ ∃! q : X ⟶ D.X, q ≫ p.hom.hom = f) :
    IsIso ((Over.pullback g).mapGrp.map p) := by
  let M := Over.map g
  let F := Over.pullback g
  let A := Over.mapPullbackAdj g
  let G' := F.obj G.X
  let D' := F.obj D.X
  have flatG : Flat (M.obj G').hom := by
    change Flat (pullback.snd G.X.hom g ≫ g)
    infer_instance
  have flatD : Flat (M.obj D').hom := by
    change Flat (pullback.snd D.X.hom g ≫ g)
    infer_instance
  have hf := factorsThroughSpecialSubgroup_of_disjoint h b G' (A.counit.app G.X)
  obtain ⟨v, hv, _⟩ := (universal flatG (A.counit.app G.X)).mp hf
  let inv : G' ⟶ D' := (A.homEquiv G' D.X) v
  let p' : D' ⟶ G' := F.map p.hom.hom
  have hid (X : Over S) : (A.homEquiv (F.obj X) X).symm (𝟙 (F.obj X)) = A.counit.app X :=
    (Adjunction.homEquiv_counit A (F.obj X) X (𝟙 (F.obj X))).trans
      ((congrArg (· ≫ A.counit.app X) (M.map_id (F.obj X))).trans (Category.id_comp _))
  have hR : inv ≫ p' = 𝟙 G' := by
    apply (A.homEquiv G' G.X).symm.injective
    change (A.homEquiv G' G.X).symm (inv ≫ F.map p.hom.hom) = _
    rw [A.homEquiv_naturality_right_symm]
    exact (congrArg (· ≫ p.hom.hom) (Equiv.symm_apply_apply _ v)).trans
      (hv.trans (hid G.X).symm)
  have hL : p' ≫ inv = 𝟙 D' := by
    apply (A.homEquiv D' D.X).symm.injective
    let f := A.counit.app D.X ≫ p.hom.hom
    have hu := (universal flatD f).mp (factorsThroughSpecialSubgroup_of_disjoint h b D' f)
    apply hu.unique
    · rw [A.homEquiv_naturality_left_symm, Category.assoc]
      change (M.map p' ≫ ((A.homEquiv G' D.X).symm inv ≫ p.hom.hom)) = f
      rw [show (A.homEquiv G' D.X).symm inv = v from Equiv.symm_apply_apply _ _, hv]
      exact A.counit.naturality p.hom.hom
    · exact congrArg (· ≫ p.hom.hom) (hid D.X)
  let : IsIso p' := ⟨⟨inv, hL, hR⟩⟩
  let q := F.mapGrp.map p
  let : IsIso q.hom.hom := inferInstanceAs (IsIso p')
  let e := Grp.mkIso (G := F.mapGrp.obj D) (H := F.mapGrp.obj G)
    (asIso q.hom.hom)
    (IsMonHom.one_hom q.hom.hom) (IsMonHom.mul_hom q.hom.hom)
  have he : e.hom = q := Grp.hom_ext _ _ rfl
  change IsIso q
  rw [← he]
  infer_instance

private theorem fractionRing_isLocalizationAway {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π) : IsLocalization.Away π K := by
  apply (IsLocalization.iff_of_le_of_exists_dvd (S := K)
    (Submonoid.powers π) (nonZeroDivisors R) ?_ ?_).mpr
  · infer_instance
  · rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hπ.ne_zero)
  · intro r hr
    obtain ⟨n, u, hu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (mem_nonZeroDivisors_iff_ne_zero.mp hr) hπ
    refine ⟨π ^ n, ⟨n, rfl⟩, ↑u⁻¹, ?_⟩
    calc
      π ^ n = (↑u * ↑u⁻¹) * π ^ n := by simp
      _ = r * ↑u⁻¹ := by rw [hu]; ac_rfl

end GenericFibre



section Chart

open MvPolynomial

variable {R C T ι : Type u} [CommRing R] [CommRing C] [CommRing T]
  [Algebra R C] [Algebra R T]

private theorem scaleAlg_universal [IsDomain R] [Module.Flat R T]
    (π : R) (hπ : π ≠ 0) (f : MvPolynomial ι C →ₐ[R] T) :
    (∀ i, algebraMap R T π ∣ f (X i)) ↔
      ∃! g : MvPolynomial ι C →ₐ[R] T, g.comp (scaleCoordinates R C ι π) = f := by
  have regular : IsSMulRegular T π :=
    (isRegular_iff_ne_zero.mpr hπ).isSMulRegular
  have scaleC (c : C) : scaleCoordinates R C ι π (MvPolynomial.C c) = MvPolynomial.C c :=
    aeval_C _ _
  have scaleX (i : ι) : scaleCoordinates R C ι π (X i : MvPolynomial ι C) =
      algebraMap R (MvPolynomial ι C) π * X i := aeval_X _ _
  constructor
  · intro h
    choose x hx using h
    let c : C →+* T := f.toRingHom.comp MvPolynomial.C
    let g : MvPolynomial ι C →ₐ[R] T :=
      { toRingHom := eval₂Hom c x
        commutes' := fun r => by
          change eval₂Hom c x (MvPolynomial.C (algebraMap R C r)) = _
          rw [eval₂Hom_C]
          exact f.commutes r }
    have hg : g.comp (scaleCoordinates R C ι π) = f := by
      apply AlgHom.toRingHom_injective
      apply MvPolynomial.ringHom_ext'
      · ext r
        change g (scaleCoordinates R C ι π (MvPolynomial.C r)) = f (MvPolynomial.C r)
        rw [scaleC]
        exact eval₂Hom_C _ _ _
      · intro i
        change g (scaleCoordinates R C ι π (X i)) = f (X i)
        rw [scaleX, map_mul, g.commutes]
        rw [show g (X i) = x i from eval₂Hom_X' c x i]
        exact (hx i).symm
    refine ⟨g, hg, fun g' hg' => ?_⟩
    apply AlgHom.toRingHom_injective
    apply MvPolynomial.ringHom_ext'
    · ext c
      have e (k : MvPolynomial ι C →ₐ[R] T) (hk : k.comp (scaleCoordinates R C ι π) = f) :
          k (MvPolynomial.C c) = f (MvPolynomial.C c) := by
        simpa only [AlgHom.comp_apply, scaleC] using DFunLike.congr_fun hk (MvPolynomial.C c)
      exact (e g' hg').trans (e g hg).symm
    · intro i
      have he := (DFunLike.congr_fun hg' (X i)).trans (DFunLike.congr_fun hg (X i)).symm
      simp only [AlgHom.comp_apply, scaleX, map_mul, AlgHom.commutes] at he
      change g' (X i) = g (X i)
      apply regular
      simpa only [Algebra.smul_def] using he
  · rintro ⟨g, hg, -⟩ i
    refine ⟨g (X i), ?_⟩
    rw [← DFunLike.congr_fun hg (X i), AlgHom.comp_apply, scaleX, map_mul, g.commutes]

private abbrev chartCentre (π : R) :
    ((Over.pullback (closedPoint π)).obj (algebraScheme R C)).left ⟶ (chart R C ι).left :=
  pullback.fst (algebraScheme R C).hom (closedPoint π) ≫ (zeroSection R C ι).left

set_option backward.isDefEq.respectTransparency false in
private theorem factors_chart_affine_iff (π : R) (f : MvPolynomial ι C →ₐ[R] T) :
    FactorsOnBaseChange (closedPoint π) (chartCentre (C := C) (ι := ι) π)
      (algebraSchemeMap f) ↔ ∀ i, algebraMap R T π ∣ f (X i) := by
  let I : Ideal R := Ideal.span {π}
  let IC := I.map (algebraMap R C)
  let IT := I.map (algebraMap R T)
  let eC := quotientPullbackIso (T := C) I
  let eT := quotientPullbackIso (T := T) I
  let qC := Ideal.Quotient.mk IC
  let qT := Ideal.Quotient.mk IT
  let ev : MvPolynomial ι C →+* C := eval₂Hom (RingHom.id C) (fun _ => 0)
  have hdiv (t : T) : qT t = 0 ↔ algebraMap R T π ∣ t := by
    change Ideal.Quotient.mk IT t = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, show IT = Ideal.span {algebraMap R T π} by
      simp [IT, I, Ideal.map_span], Ideal.mem_span_singleton]
  have hc : eC.hom ≫ chartCentre (C := C) (ι := ι) π =
      Spec.map (CommRingCat.ofHom (qC.comp ev)) := by
    change eC.hom ≫ pullback.fst (algebraScheme R C).hom (closedPoint π) ≫
      Spec.map (CommRingCat.ofHom ev) = _
    rw [quotientPullbackIso_fst_assoc]
    exact (Spec.map_comp _ _).symm
  have ht : eT.hom ≫ pullback.fst (algebraScheme R T).hom (closedPoint π) ≫
      (algebraSchemeMap f).left = Spec.map (CommRingCat.ofHom (qT.comp f.toRingHom)) := by
    rw [quotientPullbackIso_fst_assoc]
    exact (Spec.map_comp _ _).symm
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨g, hg⟩ := Spec.map_surjective (eT.hom ≫ b ≫ eC.inv)
    have h : Spec.map g ≫ Spec.map (CommRingCat.ofHom (qC.comp ev)) =
        Spec.map (CommRingCat.ofHom (qT.comp f.toRingHom)) := by
      rw [hg, ← hc]
      simp only [Category.assoc, eC.inv_hom_id_assoc, hb, ht]
    rw [← Spec.map_comp] at h
    have h' := Spec.map_injective h
    intro i
    apply (hdiv _).mp
    have hi := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h') (X i)
    simpa [ev] using hi.symm
  · intro h
    let g : C ⧸ IC →+* T ⧸ IT :=
      Ideal.Quotient.lift IC ((qT.comp f.toRingHom).comp MvPolynomial.C) (by
        have hle : IC ≤ RingHom.ker ((qT.comp f.toRingHom).comp MvPolynomial.C) := by
          rw [show IC = Ideal.span {algebraMap R C π} by simp [IC, I, Ideal.map_span]]
          apply Ideal.span_le.mpr
          intro c hc
          rw [Set.mem_singleton_iff] at hc
          subst c
          change qT (f (algebraMap R (MvPolynomial ι C) π)) = 0
          rw [f.commutes]
          exact (hdiv _).mpr dvd_rfl
        exact fun c hc => hle hc)
    have hg : (g.comp qC).comp ev = qT.comp f.toRingHom := by
      apply MvPolynomial.ringHom_ext'
      · ext c
        simp only [RingHom.comp_apply, ev, eval₂Hom_C, RingHom.id_apply]
        exact Ideal.Quotient.lift_mk _ _ _
      · intro i
        simpa [ev] using ((hdiv _).mpr (h i)).symm
    refine ⟨eT.inv ≫ Spec.map (CommRingCat.ofHom g) ≫ eC.hom, ?_⟩
    rw [Category.assoc, Category.assoc, hc]
    have he : (CommRingCat.ofHom (qC.comp ev)) ≫ CommRingCat.ofHom g =
        CommRingCat.ofHom (qT.comp f.toRingHom) := CommRingCat.hom_ext hg
    have hspec : Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom (qC.comp ev)) =
        Spec.map (CommRingCat.ofHom (qT.comp f.toRingHom)) :=
      (Spec.map_comp _ _).symm.trans (congrArg Spec.map he)
    rw [hspec, ← ht, eT.inv_hom_id_assoc]

private theorem factors_chart_iff [IsDomain R] (π : R) (hπ : π ≠ 0)
    {Y : Over (base R)} (hY : IsAffine Y.left) (hf : Flat Y.hom)
    (f : Y ⟶ chart R C ι) :
    FactorsOnBaseChange (closedPoint π) (chartCentre (C := C) (ι := ι) π) f ↔
      ∃! q : Y ⟶ chart R C ι, q ≫ scale R C ι π = f := by
  let j := closedPoint π
  let c := chartCentre (C := C) (ι := ι) π
  let F := algSpec (CommRingCat.of R)
  let ff := algSpec.fullyFaithful (R := CommRingCat.of R)
  obtain ⟨T, ⟨e⟩⟩ := (essImage_algSpec (G := Y)).mpr hY
  have hf' : Flat (algebraScheme R T.unop).hom := by
    rw [show (algebraScheme R T.unop).hom = e.hom.left ≫ Y.hom from (Over.w e.hom).symm]
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    infer_instance
  have : Module.Flat R T.unop := RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hf')
  let a : MvPolynomial ι C →ₐ[R] T.unop := (ff.preimage (e.hom ≫ f)).unop.hom
  have ha : algebraSchemeMap a = e.hom ≫ f := by
    change F.map (CommAlgCat.ofHom (ff.preimage (e.hom ≫ f)).unop.hom).op = _
    rw [CommAlgCat.ofHom_hom]
    exact ff.map_preimage (e.hom ≫ f)
  have hc : FactorsOnBaseChange j c (e.hom ≫ f) ↔ FactorsOnBaseChange j c f :=
    ⟨fun h => by simpa using h.comp e.inv, fun h => h.comp e.hom⟩
  rw [← hc, ← ha, factors_chart_affine_iff, scaleAlg_universal π hπ,
    ← affineSpecMap_existsUnique_iff, ha]
  apply (Iso.homCongr e (Iso.refl _)).existsUnique_congr
  intro q
  change q ≫ scale R C ι π = e.hom ≫ f ↔
    (e.inv ≫ q ≫ 𝟙 _) ≫ scale R C ι π = f
  simp only [Category.comp_id, Category.assoc]
  constructor
  · intro h
    rw [h, e.inv_hom_id_assoc]
  · intro h
    rw [← h, e.hom_inv_id_assoc]

end Chart

section Comparison

private theorem dilatation_hom_cancel {S S₀ : Scheme.{u}} {j : S₀ ⟶ S}
    {G : Grp (Over S)} {B : Grp (Over S₀)} {b : B ⟶ (Over.pullback j).mapGrp.obj G}
    {D T : Over S} {p : D ⟶ G.X} (hp : RepresentsDilatation j b p) (hT : Flat T.hom)
    {f g : T ⟶ D} (h : f ≫ p = g ≫ p) : f = g :=
  ((hp.2 hT (g ≫ p)).mp (factorsThroughSpecialSubgroup_comp j b hp.1 g)).unique h rfl

set_option backward.isDefEq.respectTransparency false in
private theorem centreChart_comp
    {R C ι : Type u} [CommRing R] [CommRing C] [Algebra R C] (π : R)
    {G : Grp (Over (base R))} {B : Grp (Over (base (R ⧸ Ideal.span {π})))}
    {b : B ⟶ (Over.pullback (closedPoint π)).mapGrp.obj G}
    {v : chart R C ι ⟶ G.X}
    (e : B.X ≅ (Over.pullback (closedPoint π)).obj (algebraScheme R C))
    (he : e.hom ≫ (Over.pullback (closedPoint π)).map (zeroSection R C ι ≫ v) = b.hom.hom) :
    b.hom.hom.left ≫ pullback.fst G.X.hom (closedPoint π) =
      e.hom.left ≫ chartCentre (C := C) (ι := ι) π ≫ v.left := by
  rw [← he]
  change (e.hom.left ≫ ((Over.pullback (closedPoint π)).map (zeroSection R C ι ≫ v)).left) ≫
    pullback.fst G.X.hom (closedPoint π) = _
  rw [Category.assoc, pullback_left_natural, Over.comp_left]
  simp only [chartCentre, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem centreChart_factors_iff
    {R C ι : Type u} [CommRing R] [CommRing C] [Algebra R C] (π : R)
    {G : Grp (Over (base R))} {B : Grp (Over (base (R ⧸ Ideal.span {π})))}
    {b : B ⟶ (Over.pullback (closedPoint π)).mapGrp.obj G}
    {v : chart R C ι ⟶ G.X} (hv : IsCentreChart π b v)
    {Y : Over (base R)} (f : Y ⟶ chart R C ι) :
    FactorsThroughSpecialSubgroup (closedPoint π) b (f ≫ v) ↔
      FactorsOnBaseChange (closedPoint π) (chartCentre (C := C) (ι := ι) π) f := by
  let j := closedPoint π
  have : IsClosedImmersion j := IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of R) (Ideal.span {π})
  have : IsOpenImmersion v.left := hv.1
  obtain ⟨e, he⟩ := hv.2
  have he' := centreChart_comp π e he
  rw [factorsThroughSpecialSubgroup_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a ≫ e.hom.left, (cancel_mono v.left).mp ?_⟩
    change ((a ≫ e.hom.left) ≫ chartCentre π) ≫ v.left =
      (pullback.fst Y.hom j ≫ f.left) ≫ v.left
    rw [Category.assoc, Category.assoc a, ← he', ← Category.assoc]
    exact ha
  · rintro ⟨a, ha⟩
    refine ⟨a ≫ e.inv.left, ?_⟩
    have hei : e.inv.left ≫ e.hom.left = 𝟙 _ :=
      congrArg Over.Hom.left e.inv_hom_id
    have he'' : e.inv.left ≫ (b.hom.hom.left ≫ pullback.fst G.X.hom j) =
        chartCentre (C := C) (ι := ι) π ≫ v.left := by
      rw [he', ← Category.assoc, hei, Category.id_comp]
    change (a ≫ e.inv.left) ≫ (b.hom.hom.left ≫ pullback.fst G.X.hom j) =
      pullback.fst Y.hom j ≫ (f.left ≫ v.left)
    rw [Category.assoc, he'', ← Category.assoc a, ha, Category.assoc]

private theorem chartProjection_comp {R C ι : Type u} [CommRing R] [CommRing C] [Algebra R C] :
    chartProjection R C ι ≫ (algebraScheme R C).hom = (chart R C ι).hom :=
  (Spec.map_comp _ _).symm

private def chartIsoAffineSpace {R C ι : Type u} [CommRing R] [CommRing C] [Algebra R C] :
    (chart R C ι).left ≅ AffineSpace ι (algebraScheme R C).left :=
  (AffineSpace.SpecIso ι (CommRingCat.of C)).symm

private theorem chartProjection_eq {R C ι : Type u} [CommRing R] [CommRing C] [Algebra R C] :
    chartProjection R C ι =
      chartIsoAffineSpace.hom ≫ (AffineSpace ι (algebraScheme R C).left ↘ (algebraScheme R C).left) :=
  (AffineSpace.SpecIso_inv_over (n := ι) (CommRingCat.of C)).symm

theorem chartIsAffineSpaceProduct : ChartIsAffineSpaceProduct.{u} := by
  intro R C ι _ _ _
  let Z := (algebraScheme R C).left
  let z := (algebraScheme R C).hom
  let e := chartIsoAffineSpace (R := R) (C := C) (ι := ι)
  refine ⟨chartProjection_comp, e.hom ≫ AffineSpace.map ι z, ?_⟩
  apply (AffineSpace.isPullback_map (n := ι) z).flip.of_iso' e
    (Iso.refl Z) (Iso.refl (AffineSpace ι (base R))) (Iso.refl (base R))
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (chartProjection_eq (R := R) (C := C) (ι := ι)).symm
  · simp only [Iso.refl_hom, Category.comp_id]
  · change 𝟙 Z ≫ z = z ≫ 𝟙 (base R)
    simp
  · simp

private theorem chart_flat {R C ι : Type u} [CommRing R] [CommRing C] [Algebra R C]
    [Flat (algebraScheme R C).hom] : Flat (chart R C ι).hom := by
  have : Flat (chartProjection R C ι) := by
    apply Flat.SpecMap_iff.mpr
    change (algebraMap C (MvPolynomial ι C)).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  rw [← chartProjection_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem scaledChartComparison : ScaledChartComparison.{u} := by
  intro R C ι _ _ _ _ _ π hπ G hG B b v hv D p hD hDflat hZflat hd
  let j := closedPoint π
  let U := chart R C ι
  let s := scale R C ι π
  have : IsOpenImmersion v.left := hv.1
  have hU : IsAffine U.left := inferInstanceAs (IsAffine (base (MvPolynomial ι C)))
  have hUflat : Flat U.hom := chart_flat
  have hfactor : FactorsThroughSpecialSubgroup j b (s ≫ v) :=
    (centreChart_factors_iff π hv s).mpr
      ((factors_chart_affine_iff π (scaleCoordinates R C ι π)).mpr fun i =>
        ⟨MvPolynomial.X i, MvPolynomial.aeval_X _ _⟩)
  obtain ⟨w, hw, -⟩ := (hd.2 hUflat (s ≫ v)).mp hfactor
  have hcomm : w.left ≫ p.left = s.left ≫ v.left :=
    congrArg Over.Hom.left hw
  let l := pullback.lift w.left s.left hcomm
  let fst := pullback.fst p.left v.left
  let snd := pullback.snd p.left v.left
  let W := Over.mk (fst ≫ D.hom)
  let a : W ⟶ D := Over.homMk fst rfl
  let c : W ⟶ U := Over.homMk snd (by
    change snd ≫ U.hom = fst ≫ D.hom
    rw [← Over.w v, ← Over.w p, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ G.X.hom) pullback.condition.symm)
  have hac : a ≫ p = c ≫ v := Over.OverMorphism.ext pullback.condition
  have hW : IsAffine W.left := inferInstanceAs (IsAffine (pullback p.left v.left))
  have hWflat : Flat W.hom := inferInstanceAs (Flat (fst ≫ D.hom))
  have hc : FactorsThroughSpecialSubgroup j b (c ≫ v) :=
    hac ▸ factorsThroughSpecialSubgroup_comp j b hd.1 a
  let hcl := (factors_chart_iff π hπ.ne_zero hW hWflat c).mp
    ((centreChart_factors_iff π hv c).mp hc)
  obtain ⟨r, hr, _⟩ := hcl
  have hra : r ≫ w = a := by
    apply dilatation_hom_cancel hd hWflat
    rw [Category.assoc, hw, ← Category.assoc, hr, hac]
  have hright : r.left ≫ l = 𝟙 W.left := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      exact congrArg Over.Hom.left hra
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      exact congrArg Over.Hom.left hr
  let k : U ⟶ W := Over.homMk l (by
    change l ≫ fst ≫ D.hom = U.hom
    rw [pullback.lift_fst_assoc]
    exact Over.w w)
  have hleft : l ≫ r.left = 𝟙 U.left := by
    have hks : k ≫ c = s := Over.OverMorphism.ext (pullback.lift_snd _ _ _)
    have h := (factors_chart_iff π hπ.ne_zero hU hUflat s).mp
      ((centreChart_factors_iff π hv s).mp hfactor)
    exact congrArg Over.Hom.left (h.unique (by rw [Category.assoc, hr, hks]) (Category.id_comp _))
  let e : U.left ≅ W.left := ⟨l, r.left, hleft, hright⟩
  have hsquare : IsPullback w.left s.left p.left v.left :=
    IsPullback.of_iso_pullback ⟨hcomm⟩ e (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hopen : IsOpenImmersion w.left := MorphismProperty.of_isPullback hsquare.flip hv.1
  refine ⟨w, hopen, hsquare, ?_⟩
  have hrange := Scheme.image_preimage_eq_of_isPullback hsquare.flip Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at hrange
  change Set.range w.left = p.left ⁻¹' Set.range v.left at hrange
  rw [hrange]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hd.1
  obtain ⟨eB, heB⟩ := hv.2
  refine ⟨(eB.hom.left ≫ chartCentre (C := C) (ι := ι) π) (y.left x), ?_⟩
  have heq := centreChart_comp π eB heB
  have hh := congrArg Over.Hom.left hy
  change y.left ≫ b.hom.hom.left = ((Over.pullback j).map p).left at hh
  have hhy :
      y.left ≫ b.hom.hom.left ≫ pullback.fst G.X.hom j =
        pullback.fst D.hom j ≫ p.left := by
    rw [← Category.assoc, hh, pullback_left_natural]
  have ht := (congrArg (y.left ≫ ·) heq).symm.trans hhy
  change (y.left ≫ eB.hom.left ≫ chartCentre (C := C) (ι := ι) π ≫ v.left) x =
    (pullback.fst D.hom j ≫ p.left) x
  exact congrArg (fun f : ((Over.pullback j).obj D).left ⟶ G.X.left => f x) ht


end Comparison


section Uniqueness

open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

theorem schemeDilatationUnique : SchemeDilatationUnique.{u} := by
  intro S S₀ j G B b D E p q hD hE hp hq
  obtain ⟨f, hf, hf_unique⟩ := (hq.2 hD p).mp hp.1
  obtain ⟨g, hg, _⟩ := (hp.2 hE q).mp hq.1
  have hfg : f ≫ g = 𝟙 D := by
    apply dilatation_hom_cancel hp hD
    rw [Category.assoc, hg, hf, Category.id_comp]
  have hgf : g ≫ f = 𝟙 E := by
    apply dilatation_hom_cancel hq hE
    rw [Category.assoc, hf, hg, Category.id_comp]
  exact ⟨⟨f, g, hfg, hgf⟩, hf, fun e he => Iso.ext (hf_unique _ he)⟩

theorem groupDilatationUnique : GroupDilatationUnique.{u} := by
  intro S S₀ j G B b D E p q hD hE hp hq
  obtain ⟨e, he, _⟩ :=
    schemeDilatationUnique S S₀ j G B b D.X E.X p.hom.hom q.hom.hom hD hE hp hq
  have hOne : η[D.X] ≫ e.hom = η[E.X] := by
    apply dilatation_hom_cancel hq (show Flat (𝟙_ (Over S)).hom by
      change Flat (𝟙 S)
      infer_instance)
    rw [Category.assoc, he, IsMonHom.one_hom p.hom.hom, IsMonHom.one_hom q.hom.hom]
  have hMul : μ[D.X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[E.X] := by
    apply dilatation_hom_cancel hq
      (flat_over_tensor (X := D.X) (Y := D.X))
    simp only [Category.assoc, he, IsMonHom.mul_hom]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, he]
  let i := Grp.mkIso e hOne hMul
  refine ⟨i, Grp.hom_ext _ _ he, fun k hk => ?_⟩
  apply Iso.ext
  apply Grp.hom_ext
  apply dilatation_hom_cancel hq hD
  exact (congrArg (fun f : D ⟶ G => f.hom.hom) hk).trans he.symm

theorem genericHomExt : GenericHomExt.{u} := by
  intro R K _ _ _ _ _ _ X Y hX hY f g h
  let j := genericPoint R K
  have : IsDominant j := by
    rw [isDominant_iff]
    change DenseRange (PrimeSpectrum.comap (algebraMap R K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot (algebraMap R K)).mp (IsFractionRing.injective R K)]
    exact bot_le
  have : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  have : QuasiCompact j :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R K))))
  let k := pullback.fst X.hom j
  have hk : k ≫ f.left = k ≫ g.left := by
    change pullback.fst X.hom j ≫ f.left = pullback.fst X.hom j ≫ g.left
    rw [← pullback_left_natural j f, ← pullback_left_natural j g]
    exact congrArg (fun t => t.left ≫ pullback.fst Y.hom j) h
  apply Over.OverMorphism.ext
  apply ext_of_isAffine
  have : Mono k.appTop :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr (k.app_injective ⊤)
  apply (cancel_mono k.appTop).mp
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hk]

theorem representsOfGenericIso : RepresentsOfGenericIso.{u} := by
  intro R K _ _ _ _ _ _ π G B b D p ha hD hi h
  refine ⟨(h hD p).mpr ⟨𝟙 D, Category.id_comp _, fun f hf => ?_⟩, h⟩
  apply genericHomExt R K D D hD ha
  let F := Over.pullback (genericPoint R K)
  apply (cancel_mono (F.map p)).mp
  rw [← F.map_comp, ← F.map_comp, hf, Category.id_comp]

end Uniqueness


section Geometry

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

private theorem genericPoint_isOpenImmersion (π : R) (hπ : Irreducible π) :
    IsOpenImmersion (genericPoint R K) := by
  let := fractionRing_isLocalizationAway (K := K) π hπ
  let e := IsLocalization.algEquiv (Submonoid.powers π) (Localization.Away π) K
  let i := Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  let m := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away π)))
  have h : i.hom ≫ m = genericPoint R K := by
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away π))) = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext e.commutes
  rw [← h]
  exact IsOpenImmersion.comp i.hom m

private theorem genericPoint_range (π : R) (hπ : Irreducible π) :
    Set.range (genericPoint R K) = (PrimeSpectrum.zeroLocus {π})ᶜ := by
  let := fractionRing_isLocalizationAway (K := K) π hπ
  change Set.range (PrimeSpectrum.comap (algebraMap R K)) = _
  rw [PrimeSpectrum.localization_away_comap_range K π, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]

omit [IsDomain R] [IsDiscreteValuationRing R] in
private theorem closedPoint_range (π : R) :
    Set.range (closedPoint π) = PrimeSpectrum.zeroLocus {π} := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {π}))) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]

omit [IsDomain R] [IsDiscreteValuationRing R] in
private theorem chart_smooth {C ι : Type u} [CommRing C] [Algebra R C] [Finite ι]
    [Smooth (algebraScheme R C).hom] : Smooth (chart R C ι).hom := by
  rw [← chartProjection_comp, chartProjection_eq]
  infer_instance

omit [IsDomain R] [IsDiscreteValuationRing R] in
private theorem chart_geometricallyConnected {C ι : Type u} [CommRing C] [Algebra R C] [Finite ι]
    [Smooth (algebraScheme R C).hom] [GeometricallyConnected (algebraScheme R C).hom] :
    GeometricallyConnected (chart R C ι).hom := by
  let Z := (algebraScheme R C).left
  let a : AffineSpace ι Z ⟶ Z := AffineSpace ι Z ↘ Z
  let e := chartIsoAffineSpace (R := R) (C := C) (ι := ι)
  let z := (algebraScheme R C).hom
  have : GeometricallyIrreducible a := inferInstanceAs (GeometricallyIrreducible (AffineSpace ι Z ↘ Z))
  have : GeometricallyConnected a := by
    refine ⟨fun L _ y Y f g h => ?_⟩
    have : IrreducibleSpace Y := GeometricallyIrreducible.geometrically_irreducibleSpace y f g h
    infer_instance
  have : UniversallyOpen a := by
    have : Smooth a := inferInstanceAs (Smooth (AffineSpace ι Z ↘ Z))
    infer_instance
  have ha := GeometricallyConnected.comp a z
  have eq : (chart R C ι).hom = e.hom ≫ a ≫ z := by
    rw [← Category.assoc, ← chartProjection_eq, chartProjection_comp]
  rw [eq, GeometricallyConnected.eq_geometrically]
  exact (MorphismProperty.cancel_left_of_respectsIso _ e.hom (a ≫ z)).mpr
    ha.geometrically_connectedSpace

set_option backward.isDefEq.respectTransparency false in
private theorem specialChart_isIso {S S₀ : Scheme.{u}} (j : S₀ ⟶ S) {U D : Over S}
    (w : U ⟶ D) [IsOpenImmersion w.left]
    (hs : Set.range (pullback.fst D.hom j) ⊆ Set.range w.left) :
    IsIso ((Over.pullback j).map w).left := by
  let k := ((Over.pullback j).map w).left
  have ho : IsPullback (k ≫ pullback.snd D.hom j) (pullback.fst U.hom j)
      j (w.left ≫ D.hom) := by
    rw [show k ≫ pullback.snd D.hom j = pullback.snd U.hom j from
      Over.w ((Over.pullback j).map w), Over.w w]
    exact (IsPullback.of_hasPullback U.hom j).flip
  have h := ho.of_right (pullback_left_natural j w) (IsPullback.of_hasPullback D.hom j).flip
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨MorphismProperty.of_isPullback h.flip inferInstance, ⟨?_⟩⟩
  have hr := Scheme.image_preimage_eq_of_isPullback h.flip Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at hr
  intro x
  have hx : x ∈ Set.range k := hr.symm ▸
    (show pullback.fst D.hom j x ∈ Set.range w.left from hs ⟨x, rfl⟩)
  exact hx

private theorem geometricallyConnected_of_two_fibres (π : R) (hπ : Irreducible π)
    {X : Scheme.{u}} (f : X ⟶ base R)
    (hs : GeometricallyConnected (pullback.snd f (closedPoint π)))
    (hg : GeometricallyConnected (pullback.snd f (genericPoint R K))) :
    GeometricallyConnected f := by
  let := fractionRing_isLocalizationAway (K := K) π hπ
  refine ⟨(geometrically_iff_of_isClosedUnderIsomorphisms).mpr fun L _ y => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  have transfer {T : Scheme.{u}} (t : T ⟶ base R) (q : base L ⟶ T)
      (h : q ≫ t = Spec.map φ) (hc : GeometricallyConnected (pullback.snd f t)) :
      ConnectedSpace ↥(pullback f (Spec.map φ)) := by
    rw [← h, ← (pullbackLeftPullbackSndIso f t q).hom.homeomorph.connectedSpace_iff]
    exact pullback_of_geometrically hc.geometrically_connectedSpace L q
  by_cases hzero : φ π = 0
  · let ψ := Ideal.Quotient.lift (Ideal.span {π}) φ.hom (fun x hx => by
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
      simp [hzero])
    apply transfer (closedPoint π) (Spec.map (CommRingCat.ofHom ψ)) _ hs
    change Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {π}))) = Spec.map φ
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change ψ (Ideal.Quotient.mk (Ideal.span {π}) x) = φ x
    rfl
  · have hunit : IsUnit (φ.hom π) := isUnit_iff_ne_zero.mpr hzero
    let ψ := IsLocalization.Away.lift (S := K) π (g := φ.hom) hunit
    apply transfer (genericPoint R K) (Spec.map (CommRingCat.ofHom ψ)) _ hg
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext fun x => IsLocalization.Away.lift_eq (S := K) π hunit x

private theorem connected_of_iso_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [IsIso f] (h : GeometricallyConnected g) : GeometricallyConnected (f ≫ g) := by
  rw [GeometricallyConnected.eq_geometrically]
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr h.geometrically_connectedSpace

set_option backward.isDefEq.respectTransparency false in
private theorem dilatation_geometry {C ι : Type u} [CommRing C] [Algebra R C] [Finite ι]
    (π : R) (hπ : Irreducible π) {G D : Grp (Over (base R))}
    (p : D ⟶ G) [Smooth G.X.hom] [GeometricallyConnected G.X.hom]
    [Smooth (algebraScheme R C).hom] [GeometricallyConnected (algebraScheme R C).hom]
    (v : chart R C ι ⟶ G.X) (hc : IsScaledChart π v p.hom.hom)
    (hi : IsIso ((Over.pullback (genericPoint R K)).mapGrp.map p)) :
    Smooth D.X.hom ∧ GeometricallyConnected D.X.hom := by
  let j := closedPoint π
  let g := genericPoint R K
  let F := Over.pullback g
  let q := F.map p.hom.hom
  let dg := pullback.fst D.X.hom g
  obtain ⟨w, hwo, _, hws⟩ := hc
  have : IsOpenImmersion g := genericPoint_isOpenImmersion π hπ
  have : IsOpenImmersion dg := MorphismProperty.pullback_fst _ _ ‹IsOpenImmersion g›
  have : IsIso q := inferInstanceAs (IsIso ((Grp.forget _).map (F.mapGrp.map p)))
  have : IsIso q.left := inferInstanceAs (IsIso ((Over.forget _).map q))
  have hq : q.left ≫ pullback.snd G.X.hom g = pullback.snd D.X.hom g := Over.w q
  have hsg : Smooth (pullback.snd D.X.hom g) := by
    rw [← hq]
    infer_instance
  have hsw : Smooth (w.left ≫ D.X.hom) := by
    rw [Over.w w]
    exact chart_smooth
  have hsmooth : Smooth D.X.hom := by
    let cover : D.X.left.OpenCover :=
      Scheme.Cover.mkOfCovers Bool
        (fun i => if i then (chart R C ι).left else (F.obj D.X).left)
        (fun i => by cases i; exact dg; exact w.left)
        (fun x => by
          by_cases hx : D.X.hom x ∈ Set.range j
          · have hm : x ∈ Set.range (pullback.fst D.X.hom j) := by
              rwa [Scheme.Pullback.range_fst]
            have h := hws hm
            obtain ⟨y, hy⟩ := h
            exact ⟨true, y, hy⟩
          · have hy : D.X.hom x ∈ Set.range g := by
              rw [genericPoint_range π hπ, ← closedPoint_range π]
              exact hx
            have hm : x ∈ Set.range dg := by rwa [Scheme.Pullback.range_fst]
            obtain ⟨y, hy⟩ := hm
            exact ⟨false, y, hy⟩)
        (fun i => by cases i; exact ‹IsOpenImmersion dg›; exact hwo)
    refine IsZariskiLocalAtSource.of_openCover cover fun i => ?_
    cases i
    · change Smooth (dg ≫ D.X.hom)
      rw [pullback.condition]
      infer_instance
    · exact hsw
  refine ⟨hsmooth, geometricallyConnected_of_two_fibres (K := K) π hπ D.X.hom ?_ ?_⟩
  · let w' := (Over.pullback j).map w
    have hiw : IsIso w'.left := specialChart_isIso j w hws
    have hw : w'.left ≫ pullback.snd D.X.hom j = pullback.snd (chart R C ι).hom j := Over.w w'
    have : GeometricallyConnected (chart R C ι).hom := chart_geometricallyConnected
    have he : inv w'.left ≫ pullback.snd (chart R C ι).hom j = pullback.snd D.X.hom j := by
      rw [← hw, IsIso.inv_hom_id_assoc]
    rw [← he]
    exact connected_of_iso_comp _ _ inferInstance
  · rw [← hq]
    exact connected_of_iso_comp q.left _ inferInstance

theorem smoothDilatationExists : SmoothDilatationExists.{u} := by
  intro R K C ι _ _ _ _ _ _ _ _ _ π hπ G hG hGs hGc B b hb hZs hZc v hv
  obtain ⟨D, p, hD, hDf, hd⟩ := existsGroupDilatation π hπ G hG B b hb
  let j := closedPoint π
  let g := genericPoint R K
  have : IsOpenImmersion g := genericPoint_isOpenImmersion π hπ
  have hsep : Disjoint (Set.range g) (Set.range j) := by
    rw [genericPoint_range π hπ, closedPoint_range π]
    exact disjoint_compl_left
  have hi := groupDilatation_iso_of_disjoint hsep b p (fun {X} => hd.2 (T := X))
  have hc := scaledChartComparison R C ι π hπ G hG B b v hv D.X p.hom.hom hD hDf
    (inferInstance : Flat (algebraScheme R C).hom) hd
  obtain ⟨hs, hg⟩ := dilatation_geometry π hπ p v hc hi
  exact ⟨D, p, hD, hs, hg, hi, hd, hc⟩

end Geometry

end
end LinearAlgebraicGroups.Arithmetic.SplitIwahoriDilatationGeometry
