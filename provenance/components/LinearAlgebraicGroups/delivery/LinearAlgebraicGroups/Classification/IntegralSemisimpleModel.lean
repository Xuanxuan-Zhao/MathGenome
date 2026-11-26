import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import LinearAlgebraicGroups.Affine.Components
import LinearAlgebraicGroups.Reductive.CocharacterOpenCell
import Batteries.Tactic.OpenPrivate
import LinearAlgebraicGroups.Multiplicative.CharacterDescent
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.HopfAlgebra.Quotient
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Group.Pi.Units
import Specs.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import Specs.LinearAlgebraicGroups.Classification.IntegralLattices
import LinearAlgebraicGroups.Flag.MatrixOpenCell
import LinearAlgebraicGroups.Classification.IntegralRankOneExtension
import LinearAlgebraicGroups.Classification.IntegralRootCellOrders
import LinearAlgebraicGroups.Classification.IntegralFibreReductivity
import LinearAlgebraicGroups.Classification.IntegralFibreDatum

open AlgebraicGeometry CategoryTheory Opposite CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct Matrix CategoryTheory.MonObj CategoryTheory.MonoidalCategory

namespace LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

noncomputable section

universe u

open LinearAlgebraicGroups.Specs (Lie)
open Specs.IntegralRootCellOrders (IsOrderedRootChart)

/-- Integer algebra homomorphism with the integer algebra structures already
in use on the source and target. -/
private def overIntegers {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℤ A] [Algebra ℤ B] (f : A →+* B) : A →ₐ[ℤ] B where
  toRingHom := f
  commutes' z := RingHom.congr_fun (Subsingleton.elim
    (f.comp (algebraMap ℤ A)) (algebraMap ℤ B)) z

/-- The image algebra of a map into a rational algebra is flat over the integers.
For restriction of functions to the generic fibre, this is the coordinate
algebra of the schematic closure. -/
theorem flat_range {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℤ A] [Algebra ℚ B] (f : A →ₐ[ℤ] B) : Module.Flat ℤ f.range := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  have : Module.IsTorsionFree ℤ B :=
    Module.IsTorsionFree.trans ℚ
  exact f.range.toSubmodule.instIsTorsionFree

/-- A schematic closure in an affine scheme of finite type over the integers
is itself of finite presentation. -/
theorem finitePresentation_range {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℤ A] [Algebra ℤ B] [Algebra.FiniteType ℤ A]
    (f : A →ₐ[ℤ] B) : Algebra.FinitePresentation ℤ f.range :=
  Algebra.FinitePresentation.of_finiteType.mp
    (Algebra.FiniteType.of_surjective f.rangeRestrict f.rangeRestrict_surjective)

/-- The equation ideal of an affine schematic closure localizes to the
equation ideal of its restriction to the principal open. -/
theorem ker_awayMap {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (r : A) :
    RingHom.ker (IsLocalization.Away.map (Localization.Away r)
      (Localization.Away (f r)) f r) =
      (RingHom.ker f).map (algebraMap A (Localization.Away r)) := by
  exact IsLocalization.ker_map _ f (Submonoid.map_powers f r)

/-- An injective algebra map is localization away from a single element when
a surjective map from a principal localization supplies all the fractions. -/
private theorem isLocalization_of_surjective_lift {A B C : Type*}
    [CommRing A] [CommRing B] [CommRing C] [Algebra B C]
    (q : A →+* B) (a : A) (j : Localization.Away a →+* C)
    (hj : Function.Surjective j)
    (hcomp : ∀ b, j (algebraMap A (Localization.Away a) b) = algebraMap B C (q b))
    (hinj : Function.Injective (algebraMap B C)) :
    IsLocalization.Away (q a) C := by
  change IsLocalization (Submonoid.powers (q a)) C
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨m, hm⟩ := y.property
    have ha : IsUnit (algebraMap B C (q a)) := by
      rw [← hcomp]
      exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a).map j
    change IsUnit (algebraMap B C (y.val : B))
    rw [← hm, map_pow]
    exact ha.pow m
  · intro z
    obtain ⟨v, rfl⟩ := hj z
    obtain ⟨m, b, hb⟩ := IsLocalization.Away.surj a v
    refine ⟨⟨q b, ⟨(q a) ^ m, ⟨m, rfl⟩⟩⟩, ?_⟩
    change j v * algebraMap B C (q a ^ m) = algebraMap B C (q b)
    rw [map_pow]
    simpa only [map_mul, map_pow, hcomp] using congrArg j hb
  · intro x y hxy
    have he : x = y := hinj hxy
    exact ⟨1, by rw [he]⟩

/-- If a map to an affine chart becomes surjective after inverting a
single function, the chart is the corresponding principal open of its
schematic image. -/
theorem isLocalization_range_of_away_surjective {k A B : Type*}
    [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (a : A) (g : Localization.Away a →+* B)
    (hg : Function.Surjective g) (hcomp : ∀ b, g (algebraMap A (Localization.Away a) b) = f b) :
    IsLocalization.Away (f.rangeRestrict a) B :=
  isLocalization_of_surjective_lift f.rangeRestrict.toRingHom a g hg hcomp Subtype.val_injective

/-- Restriction of the closure coordinates to an integral chart whose equations
are those of the generic image. -/
def chartRestriction {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (f : A →ₐ[k] B) (g : A →ₐ[k] C) (h : RingHom.ker f = RingHom.ker g) :
    (A ⧸ RingHom.ker f) →ₐ[k] C :=
  Ideal.Quotient.liftₐ (RingHom.ker f) g fun _ ha => RingHom.mem_ker.mp (h ▸ ha)

@[simp] theorem chartRestriction_mk {k A B C : Type*}
    [CommRing k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (f : A →ₐ[k] B) (g : A →ₐ[k] C)
    (h : RingHom.ker f = RingHom.ker g) (a : A) :
    chartRestriction f g h (Ideal.Quotient.mk (RingHom.ker f) a) = g a :=
  rfl

/-- A matrix chart with the same equation ideal and a surjective localized
coordinate map is the principal open of the closure. -/
theorem isLocalization_chartRestriction {k A B C : Type*}
    [CommRing k] [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (f : A →ₐ[k] B) (g : A →ₐ[k] C)
    (h : RingHom.ker f = RingHom.ker g) (a : A) (j : Localization.Away a →+* C)
    (hj : Function.Surjective j)
    (hcomp : ∀ b, j (algebraMap A (Localization.Away a) b) = g b) :
    letI : Algebra (A ⧸ RingHom.ker f) C := (chartRestriction f g h).toRingHom.toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk (RingHom.ker f) a) C := by
  let : Algebra (A ⧸ RingHom.ker f) C := (chartRestriction f g h).toRingHom.toAlgebra
  refine isLocalization_of_surjective_lift (Ideal.Quotient.mk (RingHom.ker f)) a j hj hcomp ?_
  intro x y hxy
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  apply Ideal.Quotient.eq.mpr
  rw [h, RingHom.mem_ker, map_sub, sub_eq_zero]
  exact hxy

section HopfClosure

variable {R K A B : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing A] [CommRing B] [Algebra R B]

/-- Tensoring a map to a fraction-field algebra, with the target tensor
product taken over the fraction field. -/
def genericTensorMap [Algebra R A] [Algebra K B] [IsScalarTower R K B] (f : A →ₐ[R] B) :
    A ⊗[R] A →ₗ[R] B ⊗[K] B :=
  (((IsLocalization.moduleTensorEquiv (nonZeroDivisors R) K B B).symm :
    B ⊗[R] B ≃ₗ[K] B ⊗[K] B).toLinearMap.restrictScalars R) ∘ₗ
      TensorProduct.map f.toLinearMap f.toLinearMap

/-- The closure of a generic subgroup over a Bézout domain has a Hopf
equation ideal. The hypotheses express the compatibility of the given map
with comultiplication, counit and inverse on the generic fibre. -/
theorem isHopfIdeal_ker_of_generic [IsBezout R] [HopfAlgebra R A] [HopfAlgebra K B]
    [IsScalarTower R K B] (f : A →ₐ[R] B)
    (hcomul : ∀ a, genericTensorMap (K := K) f (Coalgebra.comul a) =
      Coalgebra.comul (R := K) (f a))
    (hcounit : ∀ a, algebraMap R K (Coalgebra.counit (R := R) a) = Coalgebra.counit (R := K) (f a))
    (hinverse : ∀ a, f (HopfAlgebra.antipode R a) = HopfAlgebra.antipode K (f a)) :
    (RingHom.ker f).IsHopfIdeal R := by
  let I := RingHom.ker f
  let i := Ideal.kerLiftAlg f
  let π := Ideal.Quotient.mkₐ R I
  have hi : Function.Injective i := Ideal.kerLiftAlg_injective f
  have hK : Module.IsTorsionFree R K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (IsFractionRing.injective R K)
  have hB : Module.IsTorsionFree R B := Module.IsTorsionFree.trans K
  have hQ : Module.IsTorsionFree R (A ⧸ I) :=
    hi.moduleIsTorsionFree i (map_smul i)
  have hflatB : Module.Flat R B := by
    rwa [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  have hflatQ : Module.Flat R (A ⧸ I) := by
    rwa [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  have hinj : Function.Injective (genericTensorMap (K := K) i) :=
    (IsLocalization.moduleTensorEquiv (nonZeroDivisors R) K B B).symm.injective.comp
      (TensorProduct.map_injective_of_flat_flat i.toLinearMap i.toLinearMap hi hi)
  have hcomp : i.toLinearMap ∘ₗ π.toLinearMap = f.toLinearMap := by
    ext a
    exact Ideal.kerLiftAlg_mk f a
  have hcoideal : (I.restrictScalars R).IsCoideal := by
    constructor
    · intro a ha
      change f a = 0 at ha
      apply IsFractionRing.injective R K
      rw [map_zero, hcounit, ha, map_zero]
    · intro a ha
      change f a = 0 at ha
      change TensorProduct.map π.toLinearMap π.toLinearMap (Coalgebra.comul a) = 0
      apply hinj
      rw [map_zero]
      have hm : (genericTensorMap (K := K) i).comp (TensorProduct.map
          π.toLinearMap π.toLinearMap) = genericTensorMap (K := K) f := by
        simp only [genericTensorMap, LinearMap.comp_assoc, ← TensorProduct.map_comp, hcomp]
      change ((genericTensorMap (K := K) i).comp (TensorProduct.map
          π.toLinearMap π.toLinearMap)) (Coalgebra.comul a) = 0
      rw [hm, hcomul, ha, map_zero]
  constructor
  intro a ha
  change f a = 0 at ha
  change f (HopfAlgebra.antipode R a) = 0
  rw [hinverse, ha, map_zero]

end HopfClosure

section AffineRestriction

variable {A : Type u} [CommRing A]

/-- Adjoin the fraction `e / x` in the localization at `x`. When `e` lifts
an idempotent modulo `x`, this ring removes the part of the special fibre
where that idempotent is one. -/
def componentRestriction (x e : A) : Subalgebra A (Localization.Away x) :=
  Algebra.adjoin A (Set.singleton (IsLocalization.mk' (Localization.Away x) e
    (⟨x, Submonoid.mem_powers _⟩ : Submonoid.powers x)))

private theorem denominators_of_adjoin_single {B : Type u} [CommRing B]
    [Algebra A B] (q : B) (r s : A)
    (hgen : Algebra.adjoin A {q} = ⊤)
    (hq : algebraMap A B r * q = algebraMap A B s) :
    ∀ b : B, ∃ a n, algebraMap A B a = algebraMap A B r ^ n * b := by
  intro b
  have hb : b ∈ Algebra.adjoin A {q} := by simp [hgen]
  refine Algebra.adjoin_induction (s := {q}) (p := fun b _ ↦
    ∃ a n, algebraMap A B a = algebraMap A B r ^ n * b) ?_ ?_ ?_ ?_ hb
  · intro b hb
    obtain rfl := Set.mem_singleton_iff.mp hb
    exact ⟨s, 1, by simpa using hq.symm⟩
  · intro a
    exact ⟨a, 0, by simp⟩
  · intro b c _ _ hb hc
    obtain ⟨a, n, ha⟩ := hb
    obtain ⟨d, m, hd⟩ := hc
    refine ⟨r ^ m * a + r ^ n * d, n + m, ?_⟩
    simp only [map_add, map_mul, map_pow, ha, hd, pow_add]
    ring
  · intro b c _ _ hb hc
    obtain ⟨a, n, ha⟩ := hb
    obtain ⟨d, m, hd⟩ := hc
    exact ⟨a * d, n + m, by simp only [map_mul, ha, hd, pow_add]; ring⟩

private theorem componentRestriction_generator (x e : A) :
    ∃ q : componentRestriction x e,
      Algebra.adjoin A {q} = ⊤ ∧ algebraMap A (componentRestriction x e) x * q =
        algebraMap A (componentRestriction x e) e := by
  let z := IsLocalization.mk' (Localization.Away x) e (⟨x, Submonoid.mem_powers _⟩ : Submonoid.powers x)
  let B := componentRestriction x e
  let q : B := ⟨z, Algebra.subset_adjoin (Set.mem_singleton z)⟩
  refine ⟨q, ?_, ?_⟩
  · apply (Subalgebra.map_injective (f := B.val) Subtype.val_injective)
    rw [AlgHom.map_adjoin, Set.image_singleton, Algebra.map_top, Subalgebra.range_val]
    rfl
  · apply Subtype.ext
    change algebraMap A (Localization.Away x) x * z = algebraMap A (Localization.Away x) e
    rw [mul_comm]
    exact IsLocalization.mk'_spec _ _ _

private theorem componentRestriction_regular (x e : A)
    (hx : x ∈ nonZeroDivisors A) :
    Function.Injective (algebraMap A (componentRestriction x e)) := by
  intro a b h
  apply IsLocalization.injective (Localization.Away x) (Submonoid.powers_le.mpr hx)
  exact congrArg Subtype.val h

private theorem localization_open_of_denominators {B : Type u} [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) (r : A)
    (hr : ∀ b : B, ∃ a n, f a = f r ^ n * b) :
    let i := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (f r))))
    let j := Spec.map (CommRingCat.ofHom f)
    IsOpenImmersion (i ≫ j) ∧ Set.range (i ≫ j) =
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum A)) := by
  dsimp only
  let g := IsLocalization.Away.map (Localization.Away r)
    (Localization.Away (f r)) f r
  have hg : Function.Bijective g := ⟨
    (IsLocalization.Away.map_injective_iff _ _ _).mpr fun a ha ↦
      ⟨0, by simp [hf (ha.trans f.map_zero.symm)]⟩,
    (IsLocalization.Away.map_surjective_iff _ _ _ _).mpr hr⟩
  let i := CommRingCat.ofHom (algebraMap A (Localization.Away r))
  let e := (RingEquiv.ofBijective g hg).toCommRingCatIso
  have hcomp : CommRingCat.ofHom f ≫
      CommRingCat.ofHom (algebraMap B (Localization.Away (f r))) = i ≫ e.hom := by
    apply CommRingCat.hom_ext
    ext a
    change algebraMap B (Localization.Away (f r)) (f a) = g (algebraMap A _ a)
    exact (IsLocalization.map_eq _ a).symm
  rw [← Spec.map_comp, hcomp, Spec.map_comp]
  refine ⟨inferInstance, ?_⟩
  change (Spec.map e.hom ≫ Spec.map i).opensRange.1 = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  have hrange := Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of A) r
  exact congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum A) => (U : Set (PrimeSpectrum A))) hrange

set_option maxHeartbeats 500000 in
/-- The spectrum of the fraction algebra is the open obtained by retaining
the zero locus of the idempotent in the special fibre, together with all of
the locus where `x` is invertible. -/
theorem componentRestriction_open (x e t : A) (hx : x ∈ nonZeroDivisors A)
    (he : (1 - e) * e = x * t) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap A (componentRestriction x e)))
    IsOpenImmersion f ∧ Set.range f =
      (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) ∪ PrimeSpectrum.basicOpen (1 - e) := by
  dsimp only
  let B := componentRestriction x e
  let f : A →+* B := algebraMap A B
  let morph := Spec.map (CommRingCat.ofHom f)
  obtain ⟨q, hgen, hq⟩ := componentRestriction_generator x e
  have hf : Function.Injective f := componentRestriction_regular x e hx
  have hyq : f (1 - e) * q = f t := by
    apply Subtype.ext
    change algebraMap A (Localization.Away x) (1 - e) * (q : Localization.Away x) =
      algebraMap A (Localization.Away x) t
    apply (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away x) x).mul_right_inj.mp
    calc
      _ = algebraMap A (Localization.Away x) (1 - e) * (algebraMap A (Localization.Away x) x *
          (q : Localization.Away x)) := by ring
      _ = algebraMap A (Localization.Away x) (1 - e) * algebraMap A (Localization.Away x) e :=
        congrArg (_ * ·) (congrArg Subtype.val hq)
      _ = _ := by rw [← map_mul, he, map_mul]
  have hden (r : A) (h : r = x ∨ r = 1 - e) : ∀ b : B, ∃ a n, f a = f r ^ n * b := by
    rcases h with h | h
    · subst r
      exact denominators_of_adjoin_single q x e hgen hq
    · subst r
      exact denominators_of_adjoin_single q (1 - e) t hgen hyq
  have hcover (P : PrimeSpectrum B) : f x ∉ P.asIdeal ∨ f (1 - e) ∉ P.asIdeal := by
    by_contra! h
    have heP : f e ∈ P.asIdeal := by rw [← hq]; exact P.asIdeal.mul_mem_right q h.1
    have hone : (1 : B) ∈ P.asIdeal := by
      convert P.asIdeal.add_mem h.2 heP using 1
      rw [← map_add, sub_add_cancel, map_one]
    exact P.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)
  have hinj : Function.Injective morph := by
    intro P Q hPQ
    change PrimeSpectrum.comap f P = PrimeSpectrum.comap f Q at hPQ
    apply PrimeSpectrum.ext
    ext b
    have hcon (a : A) : f a ∈ P.asIdeal ↔ f a ∈ Q.asIdeal := by
      change a ∈ (PrimeSpectrum.comap f P).asIdeal ↔ a ∈ (PrimeSpectrum.comap f Q).asIdeal
      rw [hPQ]
    have hex : ∃ r : A, (r = x ∨ r = 1 - e) ∧ f r ∉ P.asIdeal :=
      (hcover P).elim (fun h ↦ ⟨x, Or.inl rfl, h⟩) (fun h ↦ ⟨1 - e, Or.inr rfl, h⟩)
    obtain ⟨r, hr, hrP⟩ := hex
    have hrQ : f r ∉ Q.asIdeal := fun h ↦ hrP ((hcon r).mpr h)
    obtain ⟨a, n, ha⟩ := hden r hr b
    have hmem (T : PrimeSpectrum B) (hrT : f r ∉ T.asIdeal) :
        f a ∈ T.asIdeal ↔ b ∈ T.asIdeal := by
      have hpow : f r ^ n ∉ T.asIdeal := fun h ↦ hrT (T.2.mem_of_pow_mem n h)
      rw [ha, T.2.mul_mem_iff_mem_or_mem]
      simp [hpow]
    exact (hmem P hrP).symm.trans ((hcon a).trans (hmem Q hrQ))
  have hl (r : A) (hr : r = x ∨ r = 1 - e) :=
    localization_open_of_denominators f hf r (hden r hr)
  change IsOpenImmersion morph ∧ _
  constructor
  · apply IsOpenImmersion.of_forall_source_exists morph hinj
    intro P
    have H (r : A) (hr : r = x ∨ r = 1 - e) (hrP : f r ∉ P.asIdeal) :
        ∃ (U : Scheme.{u}) (i : U ⟶ Spec (CommRingCat.of B)) (_ : IsOpenImmersion i),
          P ∈ i.opensRange ∧ IsOpenImmersion (i ≫ morph) := by
      let i : Spec (CommRingCat.of (Localization.Away (f r))) ⟶ Spec (CommRingCat.of B) :=
        Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (f r))))
      let hi : IsOpenImmersion i := Scheme.isOpenImmersion_SpecMap_localizationAway
        (R := CommRingCat.of B) (f r)
      have hv : P ∈ i.opensRange := by
        rw [show i.opensRange = PrimeSpectrum.basicOpen (f r) from
          Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of B) (f r)]
        exact hrP
      have hio : IsOpenImmersion (i ≫ morph) := (hl r hr).1
      exact ⟨_, i, hi, hv, hio⟩
    exact (hcover P).elim (H x (Or.inl rfl)) (H (1 - e) (Or.inr rfl))
  · apply Set.Subset.antisymm
    · rintro _ ⟨P, rfl⟩
      exact hcover P
    · intro a ha
      have H (r : A) (hr : r = x ∨ r = 1 - e) (ha : a ∈ PrimeSpectrum.basicOpen r) :
          a ∈ Set.range morph := by
        have ha' : a ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum A)) := ha
        rw [← (hl r hr).2] at ha'
        obtain ⟨b, hb⟩ := ha'
        exact ⟨_, hb⟩
      exact ha.elim (H x (Or.inl rfl)) (H (1 - e) (Or.inr rfl))

/-- Retaining an arbitrary clopen part of a principal fibre of an affine
scheme gives an affine open, provided the defining parameter is regular. -/
theorem exists_affine_open_of_clopen_fibre (x : A) (hx : x ∈ nonZeroDivisors A)
    (S : Set (PrimeSpectrum (A ⧸ Ideal.span ({x} : Set A)))) (hS : IsClopen S) :
    ∃ (e : A),
      let f := Spec.map (CommRingCat.ofHom (algebraMap A (componentRestriction x e)))
      IsOpenImmersion f ∧
        Set.range f = (PrimeSpectrum.basicOpen x : Set (PrimeSpectrum A)) ∪
          PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {x})) '' S := by
  let I : Ideal A := Ideal.span {x}
  let π : A →+* A ⧸ I := Ideal.Quotient.mk I
  obtain ⟨ē, hē, hS_eq⟩ := PrimeSpectrum.isClopen_iff_zeroLocus.mp hS
  obtain ⟨e, he⟩ := Ideal.Quotient.mk_surjective (I := I) ē
  have hprod : (1 - e) * e ∈ I := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change π ((1 - e) * e) = 0
    rw [map_mul, map_sub, map_one, he, sub_mul, one_mul, hē.eq, sub_self]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hprod
  obtain ⟨hopen, hrange⟩ := componentRestriction_open x e t hx ht
  refine ⟨e, hopen, hrange.trans ?_⟩
  have hr : Set.range (PrimeSpectrum.comap π) = PrimeSpectrum.zeroLocus (I : Set A) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker]
  have hmem (P : PrimeSpectrum (A ⧸ I)) :
      P ∈ S ↔ PrimeSpectrum.comap π P ∈ PrimeSpectrum.basicOpen (1 - e) := by
    have hi : ē ∈ P.asIdeal ↔ 1 - ē ∉ P.asIdeal := by
      constructor
      · intro h h'
        exact P.2.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using P.asIdeal.add_mem h' h))
      · intro h
        exact (P.2.mem_or_mem (show (1 - ē) * ē ∈ P.asIdeal by
          rw [sub_mul, one_mul, hē.eq, sub_self]
          exact P.asIdeal.zero_mem)).resolve_left h
    change P ∈ S ↔ π (1 - e) ∉ P.asIdeal
    rw [hS_eq, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, map_sub, map_one, he]
    exact hi
  ext P
  by_cases hP : x ∈ P.asIdeal
  · have hPr : P ∈ Set.range (PrimeSpectrum.comap π) := by
      rw [hr, PrimeSpectrum.mem_zeroLocus]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hP)
    obtain ⟨Q, rfl⟩ := hPr
    have hn : PrimeSpectrum.comap π Q ∉ PrimeSpectrum.basicOpen x := fun h ↦ h hP
    simp only [Set.mem_union, SetLike.mem_coe, hn, false_or]
    constructor
    · exact fun h ↦ ⟨Q, (hmem Q).mpr h, rfl⟩
    · rintro ⟨Q', hQ', hEq⟩
      exact hEq ▸ (hmem Q').mp hQ'
  · simp [hP]

end AffineRestriction

/-- A closed subset missing the generic fibre lies over the zero locus of a
nonzero base scalar. The localization is at the images of nonzero scalars. -/
theorem exists_nonzero_base_scalar_mem_ideal {R A L : Type*}
    [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] [CommRing L] [Algebra A L]
    [IsLocalization ((nonZeroDivisors R).map (algebraMap R A)) L]
    (I : Ideal A) (hI : I.map (algebraMap A L) = ⊤) :
    ∃ r : R, r ≠ 0 ∧ algebraMap R A r ∈ I := by
  have h1 : algebraMap A L 1 ∈ I.map (algebraMap A L) := by simp [hI]
  obtain ⟨a, ha, hm⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((nonZeroDivisors R).map (algebraMap R A)) L I 1).mp h1
  obtain ⟨r, hr, rfl⟩ := Submonoid.mem_map.mp ha
  exact ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, by simpa only [mul_one] using hm⟩


section MatrixCell

open Specs.MatrixOpenCell
open Specs.IntegralLattices (ClosedRootImage Index Negative Positive TorusCoordinatesGenerate
  orderedMatrix)
open Specs.Pinning (BasedRootDatum)

/-- Coordinate algebra of the split torus times the affine space of all root
parameters. Both the base and the character lattice retain their integral structure. -/
abbrev IntegralCellCoordinates (D : BasedRootDatum.{u}) :=
  MvPolynomial D.I (AddMonoidAlgebra ℤ D.X)

private def parameterSubstitution {D : BasedRootDatum.{u}} {σ : Type u} (label : σ → D.I) :
    MvPolynomial σ ℤ →+* IntegralCellCoordinates D :=
  MvPolynomial.eval₂Hom (Int.castRingHom (IntegralCellCoordinates D)) (MvPolynomial.X ∘ label)

private def diagonalCharacter {D : BasedRootDatum.{u}} (w : D.X) :
    (IntegralCellCoordinates D)ˣ where
  val := MvPolynomial.C (AddMonoidAlgebra.single w 1)
  inv := MvPolynomial.C (AddMonoidAlgebra.single (-w) 1)
  val_inv := by rw [← map_mul]; simp [AddMonoidAlgebra.single_mul_single, ← AddMonoidAlgebra.one_def]
  inv_val := by rw [← map_mul]; simp [AddMonoidAlgebra.single_mul_single, ← AddMonoidAlgebra.one_def]

def cellFactors {D : BasedRootDatum.{u}} {n : ℕ}
    (negative : List (Negative D)) (positive : List (Positive D))
    (w : Index.{u} n → D.X) (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hneg : IsOrderedRootChart false (orderedMatrix negative (fun a => p a.val)))
    (hpos : IsOrderedRootChart true (orderedMatrix positive (fun a => p a.val))) :
    Factors (IntegralCellCoordinates D) n where
  lower := ((parameterSubstitution Subtype.val).mapMatrix
    (orderedMatrix negative (fun a => p a.val))).submatrix ULift.up ULift.up
  diagonal i := diagonalCharacter (w (ULift.up i))
  upper := ((parameterSubstitution Subtype.val).mapMatrix
    (orderedMatrix positive (fun a => p a.val))).submatrix ULift.up ULift.up
  lower_zero i j hij := by
    change parameterSubstitution Subtype.val
      (orderedMatrix negative (fun a => p a.val) (ULift.up i) (ULift.up j)) = 0
    rw [hneg.1 _ _ (show ¬ (ULift.up j : Index.{u} n) < ULift.up i from not_lt_of_gt hij)]
    have hne : (ULift.up i : Index.{u} n) ≠ ULift.up j := fun h ↦ hij.ne (congrArg ULift.down h)
    rw [Matrix.one_apply_ne hne, map_zero]
  lower_one i := by
    change parameterSubstitution Subtype.val
      (orderedMatrix negative (fun a => p a.val) (ULift.up i) (ULift.up i)) = 1
    rw [hneg.1 _ _ (show ¬ (ULift.up i : Index.{u} n) < ULift.up i from lt_irrefl _)]
    rw [Matrix.one_apply_eq, map_one]
  upper_zero i j hij := by
    change parameterSubstitution Subtype.val
      (orderedMatrix positive (fun a => p a.val) (ULift.up i) (ULift.up j)) = 0
    rw [hpos.1 _ _ (show ¬ (ULift.up i : Index.{u} n) < ULift.up j from not_lt_of_gt hij)]
    have hne : (ULift.up i : Index.{u} n) ≠ ULift.up j := fun h ↦ hij.ne (congrArg ULift.down h.symm)
    rw [Matrix.one_apply_ne hne, map_zero]
  upper_one i := by
    change parameterSubstitution Subtype.val
      (orderedMatrix positive (fun a => p a.val) (ULift.up i) (ULift.up i)) = 1
    rw [hpos.1 _ _ (show ¬ (ULift.up i : Index.{u} n) < ULift.up i from lt_irrefl _)]
    rw [Matrix.one_apply_eq, map_one]

/-- The matrix of the marked cell determines its coordinate algebra. -/
private theorem integralCell_surjective {D : BasedRootDatum.{u}} {n : ℕ}
    (negative : List (Negative D)) (positive : List (Positive D))
    (w : Index.{u} n → D.X) (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hw : TorusCoordinatesGenerate w)
    (hneg : IsOrderedRootChart false (orderedMatrix negative (fun a => p a.val)))
    (hpos : IsOrderedRootChart true (orderedMatrix positive (fun a => p a.val))) :
    ∃ φ : CellCoordinates Specs.IntegralSemisimpleModel.Integers.{u} n →+* IntegralCellCoordinates D,
      Function.Surjective φ ∧
      φ.mapMatrix (cellMatrix _ n) = (cellFactors negative positive w p hneg hpos).product := by
  exact IntegralRootCellOrders.integralCell_surjective negative positive w p hw hneg hpos

end MatrixCell

section ChangeBasis

variable {K M ι₁ κ : Type*} [CommRing K] [AddCommGroup M] [Module K M]
  [Fintype ι₁] [Fintype κ] [DecidableEq ι₁] [DecidableEq κ]
  (b : Module.Basis ι₁ K M) (c : Module.Basis κ K M)
  {R : Type*} [CommRing R] [Algebra K R]

omit [Fintype κ] [DecidableEq ι₁] in
private theorem basisMatrices_mul :
    (c.toMatrix b).map (algebraMap K R) * (b.toMatrix c).map (algebraMap K R) = 1 := by
  rw [← Matrix.map_mul, c.toMatrix_mul_toMatrix_flip, Matrix.map_one _ (map_zero _) (map_one _)]

/-- Express a matrix over a scalar extension in the basis induced by `b`. -/
def changeBasisMatrix : Matrix κ κ R →+* Matrix ι₁ ι₁ R where
  toFun m := (b.toMatrix c).map (algebraMap K R) * m * (c.toMatrix b).map (algebraMap K R)
  map_zero' := by simp
  map_add' m n := by simp [Matrix.mul_add, Matrix.add_mul]
  map_one' := by simpa only [Matrix.mul_one] using basisMatrices_mul (R := R) c b
  map_mul' m n := by
    let L := (b.toMatrix c).map (algebraMap K R)
    let B := (c.toMatrix b).map (algebraMap K R)
    change L * (m * n) * B = L * m * B * (L * n * B)
    have h : B * L = 1 := basisMatrices_mul b c
    calc
      _ = L * (m * ((B * L) * (n * B))) := by
        rw [h, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem changeBasisMatrix_eq_of_intertwines {m : Matrix κ κ R} {n : Matrix ι₁ ι₁ R}
    (h : m * (c.toMatrix b).map (algebraMap K R) = (c.toMatrix b).map (algebraMap K R) * n) :
    changeBasisMatrix b c m = n := by
  change (b.toMatrix c).map (algebraMap K R) * m * (c.toMatrix b).map (algebraMap K R) = n
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, basisMatrices_mul c b, Matrix.one_mul]

theorem changeBasisMatrix_natural {S : Type*} [CommRing S] [Algebra K S]
    (g : R →ₐ[K] S) (m : Matrix κ κ R) :
    g.toRingHom.mapMatrix (changeBasisMatrix b c m) =
      changeBasisMatrix b c (g.toRingHom.mapMatrix m) := by
  change (((b.toMatrix c).map (algebraMap K R) * m * (c.toMatrix b).map (algebraMap K R)).map g) = _
  simp only [Matrix.map_mul]
  have hl : ((b.toMatrix c).map (algebraMap K R)).map g = (b.toMatrix c).map (algebraMap K S) := by
    ext i j
    exact g.commutes _
  have hr : ((c.toMatrix b).map (algebraMap K R)).map g = (c.toMatrix b).map (algebraMap K S) := by
    ext i j
    exact g.commutes _
  rw [hl, hr]
  rfl

end ChangeBasis

section Block

variable {J : Type*} {κ : J → Type*} [Fintype J] [DecidableEq J]
  [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
variable {R S : Type*} [CommRing R] [CommRing S]

omit [∀ j, DecidableEq (κ j)] in
private theorem blockDiagonal_mul_column (m : ∀ j, Matrix (κ j) (κ j) R)
    {ι₁ : Type*} (b : Matrix (Sigma κ) ι₁ R) (k : Sigma κ) (i : ι₁) :
    (Matrix.blockDiagonal' m * b) k i = (m k.1 *ᵥ fun l => b ⟨k.1, l⟩ i) k.2 := by
  rcases k with ⟨j, k⟩
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _) (fun l _ hlj => by
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hlj)])]
  simp only [Matrix.blockDiagonal'_apply_eq]

variable {K : Type*} [CommRing K]

private def productBasis : Module.Basis (Sigma κ) K ((j : J) → κ j → K) :=
  Pi.basis (fun j => Pi.basisFun K (κ j))

omit [DecidableEq J] [∀ j, DecidableEq (κ j)] in
@[simp] private theorem productBasis_toMatrix {ι₁ : Type*}
    (b : Module.Basis ι₁ K ((j : J) → κ j → K)) (k : Sigma κ) (i : ι₁) :
    (productBasis.toMatrix b) k i = b i k.1 k.2 := by
  simp [productBasis, Module.Basis.toMatrix_apply, Pi.basis_repr]

end Block

open Specs.IntegralLattices (Index RationalHighestWeight dividedPower exponentialPolynomial)
open Specs.RationalRealization (RationalField Realization)
open Specs.CharacterPairing (characterValue)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Pinning (BasedRootDatum)

section RationalRepresentation

variable {D : BasedRootDatum.{u}} {A : Specs.RootGroups.AdditiveLine RationalField.{u}}
  {Q : Realization D A}
  [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {z : Specs.IntegralRootRelations.RootCoordinates Q}
  {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
  [DecidableEq D.base.support]
  {ω : D.base.support → D.X}
  (V : ∀ i, RationalHighestWeight z e h (ω i)) {n : ℕ}
  (b : Module.Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))

private abbrev weightBasis :=
  productBasis (κ := fun i : D.base.support => Index.{u} (V i).dimension) (K := RationalField.{u})

/-- The sum of the fundamental representations, expressed in the given basis. -/
def rationalMatrixAction :
    (groupPointsFunctor RationalField).obj Q.pinned.pair.G.val ⟶
      Specs.StandardGroups.generalLinearPoints RationalField (Index.{u} n) where
  app R := by
    letI := Q.pinned.pair.G.val.grp
    let F := (groupPointsFunctor RationalField).obj Q.pinned.pair.G.val
    let block := (changeBasisMatrix (R := R) b (weightBasis V)).comp
      (Matrix.blockDiagonal'RingHom (fun i => Index.{u} (V i).dimension) R)
    let components : F.obj R →* (∀ i, Matrix.GeneralLinearGroup (Index.{u} (V i).dimension) R) :=
      MonoidHom.pi fun i => (V i).action.app R |>.hom
    exact GrpCat.ofHom ((Units.map block.toMonoidHom).comp
      (MulEquiv.piUnits.symm.toMonoidHom.comp components))
  naturality {R S} f := by
    classical
    apply GrpCat.ext
    intro g
    apply Units.ext
    let M (i : D.base.support) : Matrix (Index.{u} (V i).dimension) _ R :=
      ((V i).action.app R g : Matrix.GeneralLinearGroup _ R).val
    let g' := ((groupPointsFunctor RationalField).obj Q.pinned.pair.G.val).map f g
    change changeBasisMatrix b (weightBasis V)
        (Matrix.blockDiagonal' fun i => ((V i).action.app S g' : Matrix.GeneralLinearGroup _ S).val) =
      f.hom.toRingHom.mapMatrix (changeBasisMatrix b (weightBasis V) (Matrix.blockDiagonal' M))
    rw [changeBasisMatrix_natural]
    congr 1
    change _ = (Matrix.blockDiagonal' M).map f.hom
    rw [Matrix.blockDiagonal'_map _ _ (map_zero f.hom)]
    congr 1
    funext i
    have hi := congrArg (fun g' => g' g) ((V i).action.naturality f)
    exact congrArg (fun g : Matrix.GeneralLinearGroup (Index.{u} (V i).dimension) S => g.val) hi

private theorem rationalMatrixAction_value (R : TestAlgebra RationalField.{u})
    (g : GroupPoints Q.pinned.pair.G.val R) :
    ((rationalMatrixAction V b).app R g : Matrix.GeneralLinearGroup _ R).val =
      changeBasisMatrix b (weightBasis V)
        (Matrix.blockDiagonal' fun i => ((V i).action.app R g : Matrix.GeneralLinearGroup _ R).val) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- In the basis of weight vectors, the marked torus acts by the specified diagonal entries. -/
theorem rationalMatrixAction_torus (w : Index.{u} n → D.X)
    (hw : ∀ j i, b j i ∈ (V i).weightSpace (w j))
    (R : TestAlgebra RationalField.{u}) (t : GroupPoints Q.pinned.pair.T.group R) :
    ((rationalMatrixAction V b).app R (t ≫ Q.pinned.pair.T.inclusion.hom.hom) :
      Matrix.GeneralLinearGroup _ R).val =
      Matrix.diagonal (fun j => characterValue (Additive.toMul (Q.datumIso.val.weightEquiv (w j))) R t) := by
  classical
  rw [rationalMatrixAction_value]
  simp_rw [RationalHighestWeight.torus_action]
  rw [Matrix.blockDiagonal'_diagonal]
  apply changeBasisMatrix_eq_of_intertwines
  ext ⟨i, l⟩ j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  change characterValue (Additive.toMul (Q.datumIso.val.weightEquiv ((V i).weight l))) R t *
    algebraMap RationalField R ((weightBasis V).toMatrix b ⟨i, l⟩ j) =
    algebraMap RationalField R ((weightBasis V).toMatrix b ⟨i, l⟩ j) *
      characterValue (Additive.toMul (Q.datumIso.val.weightEquiv (w j))) R t
  rw [productBasis_toMatrix]
  by_cases hl : (V i).weight l = w j
  · rw [hl, mul_comm]
  · have hz : b j i l = 0 := hw j i l hl
    rw [hz, map_zero, mul_zero, zero_mul]

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq D.base.support] in
private theorem coeff_exponential_entry (a : D.I) (m : ℕ)
    (i : D.base.support) (s t : Index.{u} (V i).dimension) :
    (exponentialPolynomial ((V i).rootOperator a) (V i).nilpotenceBound s t).coeff m =
      dividedPower ((V i).rootOperator a) m s t := by
  let E := (V i).rootOperator a
  have hn : E ^ (V i).nilpotenceBound = 0 := (V i).nilpotent a
  have hcoeff (q : ℕ) :
      ((((Polynomial.X : Polynomial RationalField.{u}) ^ q) •
        (Polynomial.C : RationalField.{u} →+* Polynomial RationalField.{u}).mapMatrix
          (dividedPower E q) : Matrix (Index ((V i).dimension)) _ (Polynomial RationalField)) s t
        ).coeff m = if m = q then dividedPower E q s t else 0 := by
    change (Polynomial.X ^ q * Polynomial.C (dividedPower E q s t)).coeff m = _
    rw [(Polynomial.commute_X_pow (Polynomial.C (dividedPower E q s t)) q).eq,
      Polynomial.coeff_C_mul_X_pow]
  change (exponentialPolynomial E _ s t).coeff m = dividedPower E m s t
  unfold exponentialPolynomial
  simp only [Matrix.sum_apply, Polynomial.finsetSum_coeff, hcoeff]
  by_cases hm : m < (V i).nilpotenceBound
  · rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr hm) (fun j _ h => ite_eq_right (Ne.symm h))]
    simp
  · have hp : E ^ m = 0 := by
      rw [← Nat.add_sub_of_le (le_of_not_gt hm), pow_add, hn, zero_mul]
    rw [show dividedPower E m s t = 0 by simp [dividedPower, hp]]
    apply Finset.sum_eq_zero
    intro j hj
    have hne : m ≠ j := fun h => hm (h.symm ▸ Finset.mem_range.mp hj)
    exact ite_eq_right hne

private theorem exponential_intertwines (a : D.I)
    (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hp : ∀ (m : ℕ) (j : Index.{u} n) (i : D.base.support),
      ∑ l : Index.{u} n, ((p l j).coeff m : RationalField.{u}) • b l i =
        (dividedPower ((V i).rootOperator a) m).mulVec (b j i)) :
    (Matrix.blockDiagonal' fun i =>
        exponentialPolynomial ((V i).rootOperator a) (V i).nilpotenceBound) *
        ((weightBasis V).toMatrix b).map Polynomial.C =
      (((weightBasis V).toMatrix b).map Polynomial.C) *
        p.map (Polynomial.map (Int.castRingHom RationalField.{u})) := by
  classical
  apply Matrix.ext
  rintro ⟨i, k⟩ j
  apply Polynomial.ext
  intro m
  rw [blockDiagonal_mul_column]
  have hc := congrFun (hp m j i) k
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hc
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
    productBasis_toMatrix, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_mul_C, Polynomial.coeff_map, coeff_exponential_entry]
  simpa only [Int.coe_castRingHom, mul_comm] using hc.symm

/-- The lattice polynomials give the actual root action on every rational test algebra. -/
theorem rationalMatrixAction_root (a : D.I)
    (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hp : ∀ (m : ℕ) (j : Index.{u} n) (i : D.base.support),
      ∑ l : Index.{u} n, ((p l j).coeff m : RationalField.{u}) • b l i =
        (dividedPower ((V i).rootOperator a) m).mulVec (b j i))
    (R : TestAlgebra RationalField.{u}) (x : R) :
    ((rationalMatrixAction V b).app R (Specs.IntegralRootRelations.root Q z a R x) :
      Matrix.GeneralLinearGroup _ R).val =
      (Polynomial.eval₂RingHom (Int.castRingHom R) x).mapMatrix p := by
  classical
  rw [rationalMatrixAction_value]
  simp_rw [RationalHighestWeight.root_action]
  apply changeBasisMatrix_eq_of_intertwines
  let f := Polynomial.eval₂RingHom (algebraMap RationalField.{u} R) x
  have heval := congrArg (fun M : Matrix _ _ (Polynomial RationalField.{u}) => M.map f)
    (exponential_intertwines V b a p hp)
  simp only [Matrix.map_mul, Matrix.blockDiagonal'_map _ _ (map_zero f)] at heval
  have hc : (((weightBasis V).toMatrix b).map Polynomial.C).map f =
      ((weightBasis V).toMatrix b).map (algebraMap RationalField.{u} R) := by
    ext i j
    exact Polynomial.eval₂_C _ _
  have hmap : (p.map (Polynomial.map (Int.castRingHom RationalField.{u}))).map f =
      (Polynomial.eval₂RingHom (Int.castRingHom R) x).mapMatrix p := by
    ext i j
    change ((p i j).map (Int.castRingHom RationalField.{u})).eval₂
      (algebraMap RationalField.{u} R) x = (p i j).eval₂ (Int.castRingHom R) x
    rw [Polynomial.eval₂_map, show (algebraMap RationalField.{u} R).comp (Int.castRingHom _) =
      Int.castRingHom R from Subsingleton.elim _ _]
  rwa [hc, hmap] at heval

end RationalRepresentation

section LinearGroup

open Specs.MatrixOpenCell (genericMatrix MatrixGroupCoordinates)

variable (k : Type u) [CommRing k] (n : ℕ)

private abbrev universalGLMatrix : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n))
    (MatrixGroupCoordinates k n) :=
  (algebraMap _ (MatrixGroupCoordinates k n)).mapMatrix (genericMatrix k n)

private theorem universalGLMatrix_det_unit : IsUnit (universalGLMatrix k n).det := by
  rw [← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit _

variable {k n}

private def evalMatrix {B : Type u} [CommRing B] [Algebra k B]
    (M : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) B) :
      MvPolynomial ((ULift.{u} (Fin n)) × (ULift.{u} (Fin n))) k →ₐ[k] B :=
  MvPolynomial.aeval fun ij => M ij.1 ij.2

private theorem evalMatrix_universal {B : Type u} [CommRing B] [Algebra k B]
    (M : Matrix (ULift.{u} (Fin n)) (ULift.{u} (Fin n)) B) :
    (evalMatrix M).mapMatrix (genericMatrix k n) = M := by
  ext i j
  exact MvPolynomial.aeval_X _ _

private theorem evalMatrix_det_unit {B : Type u} [CommRing B] [Algebra k B]
    (M : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) B) :
    IsUnit (evalMatrix M.val (genericMatrix k n).det) := by
  rw [AlgHom.map_det, evalMatrix_universal]
  exact (Matrix.GeneralLinearGroup.det M).isUnit

private def evalGL {B : Type u} [CommRing B] [Algebra k B]
    (M : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) B) :
    MatrixGroupCoordinates k n →ₐ[k] B :=
  IsLocalization.Away.liftAlgHom (genericMatrix k n).det (evalMatrix_det_unit M)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem evalGL_universal {B : Type u} [CommRing B] [Algebra k B]
    (M : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) B) :
    (evalGL M).mapMatrix (universalGLMatrix k n) = M.val := by
  ext i j
  change evalGL M (algebraMap _ (MatrixGroupCoordinates k n) (genericMatrix k n i j)) = _
  rw [evalGL, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact MvPolynomial.aeval_X _ _

private theorem glAlgHom_ext {B : Type u} [CommRing B] [Algebra k B]
    {f g : MatrixGroupCoordinates k n →ₐ[k] B}
    (h : f.mapMatrix (universalGLMatrix k n) = g.mapMatrix (universalGLMatrix k n)) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (genericMatrix k n).det)
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  exact congrFun (congrFun h i) j

/-- Evaluation at the universal determinant-localized matrix. -/
def matrixCoordinatesEquiv {B : Type u} [CommRing B] [Algebra k B] :
    (MatrixGroupCoordinates k n →ₐ[k] B) ≃ Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) B where
  toFun f := Matrix.GeneralLinearGroup.mk'' (f.mapMatrix (universalGLMatrix k n)) (by
    rw [← AlgHom.map_det]
    exact (universalGLMatrix_det_unit k n).map f)
  invFun := evalGL
  left_inv f := glAlgHom_ext (evalGL_universal _)
  right_inv M := Units.ext (evalGL_universal M)

private theorem matrixCoordinatesEquiv_val {B : Type u} [CommRing B] [Algebra k B]
    (f : MatrixGroupCoordinates k n →ₐ[k] B) :
    (matrixCoordinatesEquiv f).val = f.mapMatrix (universalGLMatrix k n) := rfl

variable (k n)

private def relativeMatrixPoints : CommAlgCat.{u} k ⥤ GrpCat.{u} where
  obj B := GrpCat.of (Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) B)
  map f := GrpCat.ofHom (Matrix.GeneralLinearGroup.map f.hom.toRingHom)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private abbrev matrixAlgebraObject := op (CommAlgCat.of k (MatrixGroupCoordinates k n))

set_option backward.isDefEq.respectTransparency false in
private def relativeMatrixRepresentation :
    ((unopUnop (CommAlgCat.{u} k) ⋙ relativeMatrixPoints k n) ⋙ forget _).RepresentableBy
      (matrixAlgebraObject k n) where
  homEquiv {X} :=
    { toFun f := matrixCoordinatesEquiv f.unop.hom
      invFun M := (CommAlgCat.ofHom (matrixCoordinatesEquiv.symm M)).op
      left_inv f := Quiver.Hom.unop_inj (CommAlgCat.hom_ext (matrixCoordinatesEquiv.symm_apply_apply _))
      right_inv M := matrixCoordinatesEquiv.apply_symm_apply _ }
  homEquiv_comp f g := by
    apply Units.ext
    rfl

@[instance_reducible]
private def matrixGroupObject :
    GrpObj (matrixAlgebraObject k n) :=
  GrpObj.ofRepresentableBy _ (unopUnop (CommAlgCat.{u} k) ⋙ relativeMatrixPoints k n)
    (relativeMatrixRepresentation k n)

/-- The Hopf algebra of the full matrix group over an arbitrary commutative ring. -/
@[instance_reducible] def matrixCoordinateHopfAlgebra :
    HopfAlgebra k (MatrixGroupCoordinates k n) :=
  @instHopfAlgebraCarrierUnopCommAlgCatOfGrpObjOpposite k _ (matrixAlgebraObject k n)
    (matrixGroupObject k n)

attribute [local instance] matrixCoordinateHopfAlgebra

private theorem matrix_comul :
    (Bialgebra.comulAlgHom k (MatrixGroupCoordinates k n)).mapMatrix (universalGLMatrix k n) =
      (Algebra.TensorProduct.includeLeft :
        MatrixGroupCoordinates k n →ₐ[k] (MatrixGroupCoordinates k n) ⊗[k] (MatrixGroupCoordinates k n)
        ).mapMatrix (universalGLMatrix k n) *
      (Algebra.TensorProduct.includeRight :
        MatrixGroupCoordinates k n →ₐ[k] (MatrixGroupCoordinates k n) ⊗[k] (MatrixGroupCoordinates k n)
        ).mapMatrix (universalGLMatrix k n) := by
  let X := matrixAlgebraObject k n
  let P := relativeMatrixRepresentation k n
  let : GrpObj X := matrixGroupObject k n
  have h : P.homEquiv (μ[X]) = P.homEquiv (fst X X) * P.homEquiv (snd X X) := by
    change P.homEquiv (P.homEquiv.symm _) = _
    exact Equiv.apply_symm_apply _ _
  exact congrArg Units.val h

private theorem matrix_counit :
    (Bialgebra.counitAlgHom k (MatrixGroupCoordinates k n)).mapMatrix (universalGLMatrix k n) = 1 := by
  let X := matrixAlgebraObject k n
  let P := relativeMatrixRepresentation k n
  let : GrpObj X := matrixGroupObject k n
  have h : P.homEquiv (η[X]) = 1 := by
    change P.homEquiv (P.homEquiv.symm 1) = 1
    exact Equiv.apply_symm_apply _ _
  exact congrArg Units.val h

private theorem matrix_antipode :
    (HopfAlgebra.antipodeAlgHom k (MatrixGroupCoordinates k n)).mapMatrix (universalGLMatrix k n) =
      ((matrixCoordinatesEquiv (AlgHom.id k (MatrixGroupCoordinates k n)))⁻¹ :
        Matrix.GeneralLinearGroup _ (MatrixGroupCoordinates k n)).val := by
  let X := matrixAlgebraObject k n
  let P := relativeMatrixRepresentation k n
  let : GrpObj X := matrixGroupObject k n
  have h : P.homEquiv (ι[X]) = (P.homEquiv (𝟙 X))⁻¹ := by
    change P.homEquiv (P.homEquiv.symm _) = _
    exact Equiv.apply_symm_apply _ _
  exact congrArg Units.val h

end LinearGroup

open Specs.MatrixOpenCell (MatrixGroupCoordinates)

section MatrixClosure

open WithConv
open Algebra.TensorProduct (includeLeft includeRight)

variable {R K : Type u} [CommRing R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  (B : CommHopfAlgCat.{u} K) [Algebra R B] [IsScalarTower R K B]
  {n : ℕ}
  (ρ : convolutionPoints B ⟶ Specs.StandardGroups.generalLinearPoints K (ULift.{u} (Fin n)))

private abbrev matrixAtUniversalPoint : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) B :=
  ρ.app (CommAlgCat.of K B) (toConv (AlgHom.id K B))

/-- The coordinate ring homomorphism determined by a matrix representation of
a generic affine group. -/
def rationalMatrixCoordinates : MatrixGroupCoordinates R n →ₐ[R] B :=
  evalGL (matrixAtUniversalPoint B ρ)

private theorem representation_evaluation {A : Type u} [CommRing A] [Algebra K A]
    (a : B →ₐ[K] A) :
    ρ.app (CommAlgCat.of K A) (toConv a) =
      Matrix.GeneralLinearGroup.map a.toRingHom (matrixAtUniversalPoint B ρ) := by
  let f : CommAlgCat.of K B ⟶ CommAlgCat.of K A := CommAlgCat.ofHom a
  have h := ρ.naturality_apply f (toConv (AlgHom.id K B))
  change ρ.app (CommAlgCat.of K A) (toConv (a.comp (AlgHom.id K B))) = _
    at h
  rw [AlgHom.comp_id] at h
  exact h

private def genericTensorAlgHom {A : Type u} [CommRing A] [Algebra R A]
    (f : A →ₐ[R] B) : A ⊗[R] A →ₐ[R] B ⊗[K] B :=
  ((IsLocalization.algebraTensorEquiv (nonZeroDivisors R) K B B).symm.toAlgHom.restrictScalars R).comp
    (Algebra.TensorProduct.map f f)

private theorem genericTensorAlgHom_tmul {A : Type u} [CommRing A] [Algebra R A]
    (f : A →ₐ[R] B) (x y : A) :
    genericTensorAlgHom B f (x ⊗ₜ[R] y) = f x ⊗ₜ[K] f y := by
  simp only [genericTensorAlgHom, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom]
  rfl

private theorem genericTensorAlgHom_toLinearMap {A : Type u} [CommRing A] [Algebra R A]
    (f : A →ₐ[R] B) : (genericTensorAlgHom B f).toLinearMap = genericTensorMap (K := K) f := by
  apply TensorProduct.ext'
  intro x y
  exact genericTensorAlgHom_tmul B f x y

attribute [local instance] matrixCoordinateHopfAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem rationalMatrixCoordinates_comul :
    (genericTensorAlgHom B (rationalMatrixCoordinates (R := R) B ρ)).comp
        (Bialgebra.comulAlgHom R (MatrixGroupCoordinates R n)) =
      ((Bialgebra.comulAlgHom K B).restrictScalars R).comp (rationalMatrixCoordinates B ρ) := by
  let f := rationalMatrixCoordinates (R := R) B ρ
  let U := universalGLMatrix R n
  let T := B ⊗[K] B
  let X := matrixAtUniversalPoint B ρ
  let δ := genericTensorAlgHom B f
  let l : B →ₐ[K] T := includeLeft
  let r : B →ₐ[K] T := includeRight
  let C : TestAlgebra K := CommAlgCat.of K T
  have hδ : toConv (Bialgebra.comulAlgHom K B) =
      (toConv l : (convolutionPoints B).obj C) * toConv r := by
    apply ofConv_injective
    ext x
    rw [AlgHom.convMul_apply]
    have hv : Algebra.TensorProduct.lift l r (fun _ _ => Commute.all _ _) =
        AlgHom.id K T := by
      exact Algebra.TensorProduct.lift_includeLeft_includeRight
    rw [hv]
    rfl
  have hmul := (ρ.app C).hom.map_mul (toConv l) (toConv r)
  rw [← hδ] at hmul
  change ρ.app C (toConv (Bialgebra.comulAlgHom K B)) =
    ρ.app C (toConv l) * ρ.app C (toConv r) at hmul
  rw [representation_evaluation B ρ, representation_evaluation B ρ,
    representation_evaluation B ρ] at hmul
  have hentries := congrArg (fun M : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) T => M.val) hmul
  have hl : δ.comp (includeLeft (R := R) (A := MatrixGroupCoordinates R n)) =
      (l.restrictScalars R).comp f := by
    apply AlgHom.ext
    intro x
    change genericTensorAlgHom B f (x ⊗ₜ[R] 1) = f x ⊗ₜ[K] 1
    rw [genericTensorAlgHom_tmul, map_one]
  have hr : δ.comp (includeRight (R := R) (A := MatrixGroupCoordinates R n)) =
      (r.restrictScalars R).comp f := by
    apply AlgHom.ext
    intro x
    change genericTensorAlgHom B f (1 ⊗ₜ[R] x) = 1 ⊗ₜ[K] f x
    rw [genericTensorAlgHom_tmul, map_one]
  apply glAlgHom_ext
  change (δ.comp (Bialgebra.comulAlgHom R (MatrixGroupCoordinates R n))).mapMatrix U =
    (((Bialgebra.comulAlgHom K B).restrictScalars R).comp f).mapMatrix U
  change δ.mapMatrix ((Bialgebra.comulAlgHom R (MatrixGroupCoordinates R n)).mapMatrix U) =
    (Bialgebra.comulAlgHom K B).mapMatrix (f.mapMatrix U)
  rw [matrix_comul, map_mul]
  change (δ.comp (includeLeft (R := R) (A := MatrixGroupCoordinates R n))).mapMatrix U *
    (δ.comp (includeRight (R := R) (A := MatrixGroupCoordinates R n))).mapMatrix U = _
  rw [hl, hr]
  change l.mapMatrix (f.mapMatrix U) * r.mapMatrix (f.mapMatrix U) =
    (Bialgebra.comulAlgHom K B).mapMatrix (f.mapMatrix U)
  have hU : f.mapMatrix U = X.val := evalGL_universal X
  rw [hU]
  exact hentries.symm

set_option backward.isDefEq.respectTransparency false in
omit [IsFractionRing R K] in
private theorem rationalMatrixCoordinates_counit :
    ((Algebra.ofId R K).comp (Bialgebra.counitAlgHom R (MatrixGroupCoordinates R n))) =
      ((Bialgebra.counitAlgHom K B).restrictScalars R).comp (rationalMatrixCoordinates B ρ) := by
  let C : TestAlgebra K := CommAlgCat.of K K
  have hone : toConv (Bialgebra.counitAlgHom K B) = (1 : (convolutionPoints B).obj C) := by
    rfl
  have h := (ρ.app C).hom.map_one
  change ρ.app C 1 = 1 at h
  rw [← hone, representation_evaluation B ρ] at h
  have hpoint := congrArg Units.val h
  apply glAlgHom_ext
  simp only [← AlgHom.mapMatrix_comp, AlgHom.comp_apply, matrix_counit, map_one]
  have hU : (rationalMatrixCoordinates (R := R) B ρ).mapMatrix (universalGLMatrix R n) =
      (matrixAtUniversalPoint B ρ).val := evalGL_universal _
  rw [hU]
  exact hpoint.symm

set_option backward.isDefEq.respectTransparency false in
omit [IsFractionRing R K] in
private theorem rationalMatrixCoordinates_antipode :
    (rationalMatrixCoordinates (R := R) B ρ).comp
        (HopfAlgebra.antipodeAlgHom R (MatrixGroupCoordinates R n)) =
      ((HopfAlgebra.antipodeAlgHom K B).restrictScalars R).comp (rationalMatrixCoordinates B ρ) := by
  let C : TestAlgebra K := CommAlgCat.of K B
  have hinv : toConv (HopfAlgebra.antipodeAlgHom K B) =
      ((toConv (AlgHom.id K B))⁻¹ : (convolutionPoints B).obj C) := by
    change _ = toConv ((AlgHom.id K B).comp (HopfAlgebra.antipodeAlgHom K B))
    rw [AlgHom.id_comp]
  have h := (ρ.app C).hom.map_inv (toConv (AlgHom.id K B))
  change ρ.app C _ = (matrixAtUniversalPoint B ρ)⁻¹ at h
  rw [← hinv, representation_evaluation B ρ] at h
  have hpoint := congrArg Units.val h
  apply glAlgHom_ext
  simp only [← AlgHom.mapMatrix_comp, AlgHom.comp_apply, matrix_antipode]
  have hU : (rationalMatrixCoordinates (R := R) B ρ).mapMatrix (universalGLMatrix R n) =
      (matrixAtUniversalPoint B ρ).val := evalGL_universal _
  rw [hU]
  change ((Matrix.GeneralLinearGroup.map _ (_⁻¹))).val = _
  rw [map_inv]
  have hU : (Matrix.GeneralLinearGroup.map (rationalMatrixCoordinates (R := R) B ρ).toRingHom
      (matrixCoordinatesEquiv (AlgHom.id R (MatrixGroupCoordinates R n)))) =
        matrixAtUniversalPoint B ρ := Units.ext (evalGL_universal _)
  rw [hU]
  exact hpoint.symm

/-- The generic matrix representation defines a Hopf ideal in the integral matrix
coordinates. -/
theorem matrixClosure_isHopfIdeal [IsDomain R] [IsBezout R] :
    (RingHom.ker (rationalMatrixCoordinates (R := R) B ρ)).IsHopfIdeal R := by
  apply isHopfIdeal_ker_of_generic (K := K)
  · intro x
    rw [← genericTensorAlgHom_toLinearMap B]
    exact DFunLike.congr_fun (rationalMatrixCoordinates_comul B ρ) x
  · exact DFunLike.congr_fun (rationalMatrixCoordinates_counit B ρ)
  · exact DFunLike.congr_fun (rationalMatrixCoordinates_antipode B ρ)


/-- The integral equations of the generic representation inside the full
matrix group, regarded as a quotient algebra. -/
abbrev MatrixClosureCoordinates :=
  MatrixGroupCoordinates R n ⧸ RingHom.ker (rationalMatrixCoordinates (R := R) B ρ)

/-- Affine group given by the flat schematic closure of the generic matrix image. -/
def matrixClosure [IsDomain R] [IsBezout R] :
    Grp (Over (Spec (CommRingCat.of R))) :=
  letI := matrixClosure_isHopfIdeal (R := R) B ρ
  (hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R
    (MatrixClosureCoordinates (R := R) B ρ)))

/-- The closure coordinate algebra is flat and finitely presented over the base. -/
theorem matrixClosure_coordinates [IsDomain R] [IsBezout R] [IsNoetherianRing R] :
    Module.Flat R (MatrixClosureCoordinates (R := R) B ρ) ∧
      Algebra.FinitePresentation R (MatrixClosureCoordinates (R := R) B ρ) := by
  let f := rationalMatrixCoordinates (R := R) B ρ
  let I := RingHom.ker f
  let E := MatrixGroupCoordinates R n
  have hK : Module.IsTorsionFree R K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (IsFractionRing.injective R K)
  have hB : Module.IsTorsionFree R B := Module.IsTorsionFree.trans K
  have hQ : Module.IsTorsionFree R (E ⧸ I) :=
    (Ideal.kerLiftAlg_injective f).moduleIsTorsionFree (Ideal.kerLiftAlg f) (map_smul _)
  have hflat : Module.Flat R (E ⧸ I) := by
    rwa [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  let P := MvPolynomial ((ULift.{u} (Fin n)) × (ULift.{u} (Fin n))) R
  let : Algebra.FinitePresentation P E :=
    IsLocalization.Away.finitePresentation (Specs.MatrixOpenCell.genericMatrix R n).det
  let : Algebra.FiniteType R E :=
    Algebra.FiniteType.trans (R := R) (S := P) (A := E) inferInstance inferInstance
  let : Algebra.FiniteType R (E ⧸ I) := inferInstance
  exact ⟨hflat, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

end MatrixClosure

set_option backward.isDefEq.respectTransparency false in
private theorem smooth_of_smooth_point_over_algClosed
    {k : Type u} [Field k] [IsAlgClosed k] {H : Scheme.{u}}
    (f : H ⟶ Spec (CommRingCat.of k)) [LocallyOfFinitePresentation f]
    [GrpObj (Over.mk f)] (hn : (f.smoothLocus : Set H).Nonempty) :
    Smooth f := by
  let : JacobsonSpace H := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints hn f.smoothLocus.2.isLocallyClosed
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro h
  obtain ⟨x, hx, hxclosed⟩ :=
    nonempty_inter_closedPoints h f.smoothLocus.2.isClosed_compl.isLocallyClosed
  let X : 𝟙_ _ ⟶ Over.mk f :=
    Over.homMk (pointOfClosedPoint f x hxclosed) (pointOfClosedPoint_comp f x hxclosed)
  let Y : 𝟙_ _ ⟶ Over.mk f :=
    Over.homMk (pointOfClosedPoint f y hyclosed) (pointOfClosedPoint_comp f y hyclosed)
  let t := GrpObj.mulRight (X⁻¹ * Y)
  have ht : X ≫ t.hom = Y := by
    change X ≫ _ ≫ _ = Y
    simp only [comp_lift_assoc, Category.comp_id]
    have hunit : X ≫ toUnit (Over.mk f) = 𝟙 _ := toUnit_unique _ _
    rw [← Category.assoc, hunit, Category.id_comp]
    change X * (X⁻¹ * Y) = Y
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hpoint : t.hom.left x = y := by
    have hpt := congrArg (fun p : 𝟙_ _ ⟶ Over.mk f => p.left (IsLocalRing.closedPoint k)) ht
    change t.hom.left (pointOfClosedPoint f x hxclosed (IsLocalRing.closedPoint k)) =
      pointOfClosedPoint f y hyclosed (IsLocalRing.closedPoint k) at hpt
    rw [pointOfClosedPoint_apply, pointOfClosedPoint_apply] at hpt
    exact hpt
  apply hx
  have hpre : t.hom.left ⁻¹ᵁ f.smoothLocus = f.smoothLocus := by
    rw! [Scheme.Hom.preimage_smoothLocus_eq, show t.hom.left ≫ f = f from Over.w t.hom]
    rfl
  rw [← hpre]
  change t.hom.left x ∈ (f.smoothLocus : Set H)
  rwa [hpoint]

open CategoryTheory.Limits in
private theorem smooth_open_section_baseChange {H S U T : Scheme.{u}} (f : H ⟶ S)
    (i : U ⟶ H) [IsOpenImmersion i] [Smooth (i ≫ f)] (s : S ⟶ U) (hs : s ≫ i ≫ f = 𝟙 S)
    (g : T ⟶ S) :
    ∃ (V : Scheme.{u}) (j : V ⟶ pullback f g) (t : T ⟶ V),
      IsOpenImmersion j ∧ Smooth (j ≫ pullback.snd f g) ∧ t ≫ j ≫ pullback.snd f g = 𝟙 T := by
  let j := (pullbackRightPullbackFstIso f g i).inv ≫ pullback.snd i (pullback.fst f g)
  have hj : j ≫ pullback.snd f g = pullback.snd (i ≫ f) g :=
    pullbackRightPullbackFstIso_inv_snd_snd f g i
  let t := pullback.lift (g ≫ s) (𝟙 T) (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])
  refine ⟨_, j, t, ?_, ?_, ?_⟩
  · dsimp [j]
    infer_instance
  · rw [hj]
    infer_instance
  · rw [hj]
    exact pullback.lift_snd _ _ _

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
private theorem smooth_of_smooth_open_with_section_over_field
    {k : Type u} [Field k] {H U : Scheme.{u}}
    (f : H ⟶ Spec (CommRingCat.of k)) [LocallyOfFinitePresentation f] [GrpObj (Over.mk f)]
    (i : U ⟶ H) [IsOpenImmersion i] [Smooth (i ≫ f)] (s : Spec (CommRingCat.of k) ⟶ U)
    (hs : s ≫ i ≫ f = 𝟙 _) :
    Smooth f := by
  let K := AlgebraicClosure k
  let g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  apply MorphismProperty.of_pullback_snd_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := g)
  · exact ⟨⟨by dsimp [g]; infer_instance, by dsimp [g]; infer_instance⟩,
      by dsimp [g]; infer_instance⟩
  · let : GrpObj (Over.mk (pullback.snd f g)) := Over.grpObjMkPullbackSnd
    obtain ⟨V, j, t, hj, hjs, _⟩ := smooth_open_section_baseChange f i s hs g
    apply smooth_of_smooth_point_over_algClosed
    refine ⟨j (t (IsLocalRing.closedPoint K)), ?_⟩
    change t (IsLocalRing.closedPoint K) ∈ (j ⁻¹ᵁ (pullback.snd f g).smoothLocus)
    rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top]
    exact Set.mem_univ _

open CategoryTheory.Limits in
/-- A flat group scheme, locally of finite presentation, is smooth if it has a
smooth open subscheme with a section over the base. -/
theorem smooth_of_smooth_open_with_section {H S U : Scheme.{u}}
    (f : H ⟶ S) [LocallyOfFinitePresentation f] [Flat f] [GrpObj (Over.mk f)]
    (i : U ⟶ H) [IsOpenImmersion i] [Smooth (i ≫ f)] (s : S ⟶ U)
    (hs : s ≫ i ≫ f = 𝟙 _) :
    Smooth f := by
  apply Smooth.of_smooth_fiberToSpecResidueField
  intro p
  let g := S.fromSpecResidueField p
  change Smooth (pullback.snd f g)
  let grp : GrpObj (Over.mk (pullback.snd f g)) := Over.grpObjMkPullbackSnd
  let fp : LocallyOfFinitePresentation (pullback.snd f g) :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd f (S.fromSpecResidueField p)))
  obtain ⟨_, j, t, hj, hjs, ht⟩ := smooth_open_section_baseChange f i s hs g
  exact @smooth_of_smooth_open_with_section_over_field (S.residueField p) _ _ _
    (pullback.snd f g) fp grp j hj hjs t ht


/-- A free character lattice gives a formally smooth group algebra. The
values on a basis lift as units across every square-zero ideal. -/
theorem formallySmooth_characterAlgebra (k : Type*) [CommRing k]
    (X : Type*) [AddCommGroup X] [Module.Free ℤ X] :
    Algebra.FormallySmooth k (AddMonoidAlgebra k X) := by
  classical
  rw [Algebra.FormallySmooth.iff_comp_surjective]
  intro B _ _ I hI f
  let π := Units.map (Ideal.Quotient.mk I).toMonoidHom
  have hnil : IsNilpotent I := ⟨2, hI⟩
  have hπ : Function.Surjective π := by
    intro v
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective v.val
    have hu : IsUnit a := hnil.isUnit_quotient_mk_iff.mp (ha.symm ▸ v.isUnit)
    exact ⟨hu.unit, Units.ext (by change Ideal.Quotient.mk I _ = _; rw [hu.unit_spec, ha])⟩
  let b := Module.Free.chooseBasis ℤ X
  let v : Multiplicative X →* (B ⧸ I)ˣ :=
    (f.toMonoidHom.comp (AddMonoidAlgebra.of k X)).toHomUnits
  choose lift hlift using fun i => hπ (v (Multiplicative.ofAdd (b i)))
  let g : X →ₗ[ℤ] Additive Bˣ := b.constr ℤ (fun i => Additive.ofMul (lift i))
  let gUnits : Multiplicative X →* Bˣ := g.toAddMonoidHom.toMultiplicativeLeft
  have he : π.toAdditive.toIntLinearMap.comp g = v.toAdditiveRight.toIntLinearMap := by
    apply b.ext
    intro i
    change π ((b.constr ℤ (fun j => Additive.ofMul (lift j)) (b i)).toMul) = _
    rw [Module.Basis.constr_basis]
    exact hlift i
  refine ⟨AddMonoidAlgebra.lift k B X ((Units.coeHom B).comp gUnits), ?_⟩
  apply AddMonoidAlgebra.algHom_ext
  · intro x
    have hx := DFunLike.congr_fun he x
    have hval := congrArg (fun z : Additive (B ⧸ I)ˣ => (z.toMul : B ⧸ I)) hx
    change Ideal.Quotient.mk I (↑(gUnits (Multiplicative.ofAdd x)) : B) = f (AddMonoidAlgebra.single x 1) at hval
    change Ideal.Quotient.mk I
      ((AddMonoidAlgebra.lift k B X ((Units.coeHom B).comp gUnits)) (AddMonoidAlgebra.single x 1)) = _
    rw [AddMonoidAlgebra.lift_single, one_smul]
    exact hval
  · exact Subsingleton.elim _ _

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Integers integerAlgebra)

private theorem integralCell_smooth_over_int (D : BasedRootDatum.{u}) :
    Algebra.Smooth ℤ (IntegralCellCoordinates D) := by
  let A := AddMonoidAlgebra ℤ D.X
  let : Module.Finite ℤ D.X := D.finiteX
  let : Module.Free ℤ D.X := D.freeX
  let : AddGroup.FG D.X := Module.Finite.iff_addGroup_fg.mp D.finiteX
  let : Finite D.I := D.finiteRoots
  let : Algebra.FormallySmooth ℤ A := formallySmooth_characterAlgebra ℤ D.X
  let : Algebra.FiniteType ℤ A := AddMonoidAlgebra.finiteType_of_fg ℤ D.X
  let : Algebra.FinitePresentation ℤ A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Smooth ℤ A := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth A (MvPolynomial D.I A) := ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.comp ℤ A (MvPolynomial D.I A)

/-- The coordinate ring of the product of the two affine root-coordinate
spaces and the marked split torus is smooth over the lifted integers. -/
theorem integralCell_smooth (D : BasedRootDatum.{u}) :
    letI : Algebra Integers.{u} (IntegralCellCoordinates D) := integerAlgebra _
    Algebra.Smooth Integers.{u} (IntegralCellCoordinates D) := by
  let e : Integers.{u} ≃+* ℤ := ULift.ringEquiv
  let : Algebra Integers.{u} (IntegralCellCoordinates D) := integerAlgebra _
  have h₁ : e.toRingHom.Smooth := RingHom.Smooth.of_bijective e.bijective
  have h₂ : (algebraMap ℤ (IntegralCellCoordinates D)).Smooth :=
    RingHom.smooth_algebraMap.mpr (integralCell_smooth_over_int D)
  apply RingHom.smooth_algebraMap.mp
  exact (h₁.comp h₂ : ((algebraMap ℤ (IntegralCellCoordinates D)).comp e.toRingHom).Smooth)

section MatrixChartComparison

open Specs.MatrixOpenCell (CellCoordinates glMatrix cellMatrix)

variable {R K : Type u} [CommRing R] [Field K]
  (B : CommHopfAlgCat.{u} K) [Algebra R B] {n : ℕ}
  (ρ : convolutionPoints B ⟶ Specs.StandardGroups.generalLinearPoints K (ULift.{u} (Fin n)))

/-- A dense restriction of the generic representation and an injective
scalar extension of the integral cell give the same equations once they
agree on the universal matrix entries. -/
theorem matrixClosure_ker_eq_of_dense_chart [IsReduced B]
    {C T : Type u} [CommRing C] [Algebra R C] [CommRing T] [Algebra R T]
    (φ : CellCoordinates R n →ₐ[R] C)
    (j : B →ₐ[R] T) (i : C →ₐ[R] T)
    (hj : DenseRange (PrimeSpectrum.comap j.toRingHom)) (hi : Function.Injective i)
    (hmat : ∀ a b : Fin n, j ((rationalMatrixCoordinates (R := R) B ρ) (glMatrix R n a b)) =
      i (φ (cellMatrix R n a b))) :
    RingHom.ker (rationalMatrixCoordinates (R := R) B ρ) =
      RingHom.ker (φ.comp (IsScalarTower.toAlgHom R (MatrixGroupCoordinates R n) (CellCoordinates R n))) := by
  let f := rationalMatrixCoordinates (R := R) B ρ
  let g := φ.comp (IsScalarTower.toAlgHom R (MatrixGroupCoordinates R n) (CellCoordinates R n))
  have hker : RingHom.ker j.toRingHom ≤ nilradical B :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mp hj
  have hj' : Function.Injective j := by
    apply (RingHom.injective_iff_ker_eq_bot _).mpr
    have hred : nilradical B = ⊥ := nilradical_eq_zero B
    rw [hred] at hker
    exact le_antisymm hker bot_le
  have hcomp : j.comp f = i.comp g := by
    apply glAlgHom_ext
    apply Matrix.ext
    rintro ⟨a⟩ ⟨b⟩
    exact hmat a b
  have hcomp' := congrArg AlgHom.toRingHom hcomp
  change RingHom.ker f.toRingHom = RingHom.ker g.toRingHom
  rw [← RingHom.ker_comp_of_injective f.toRingHom hj', ← RingHom.ker_comp_of_injective g.toRingHom hi]
  exact congrArg RingHom.ker hcomp'

end MatrixChartComparison

section ClosureGeometry

open Specs.MatrixOpenCell (CellCoordinates minorProduct)

variable {R K : Type u} [CommRing R] [IsDomain R] [IsBezout R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  (B : CommHopfAlgCat.{u} K) [Algebra R B] [IsScalarTower R K B] {n : ℕ}
  (ρ : convolutionPoints B ⟶ Specs.StandardGroups.generalLinearPoints K (ULift.{u} (Fin n)))

set_option backward.isDefEq.respectTransparency false in
/-- A surjective restriction of the localized matrix coordinates, with the
same equations as the generic image, exhibits the chart as an open of the
flat closure. -/
theorem matrixClosure_chart {C : Type u} [CommRing C] [Algebra R C]
    (φ : CellCoordinates R n →ₐ[R] C) (hφ : Function.Surjective φ)
    (hker : RingHom.ker (rationalMatrixCoordinates (R := R) B ρ) =
      RingHom.ker (φ.comp (IsScalarTower.toAlgHom R (MatrixGroupCoordinates R n) (CellCoordinates R n)))) :
    ∃ i : Spec (CommRingCat.of C) ⟶ (matrixClosure (R := R) B ρ).X.left,
      IsOpenImmersion i ∧ i ≫ (matrixClosure (R := R) B ρ).X.hom =
        Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
  let E := MatrixGroupCoordinates R n
  let f := rationalMatrixCoordinates (R := R) B ρ
  let g := φ.comp (IsScalarTower.toAlgHom R E (CellCoordinates R n))
  let I := RingHom.ker f
  let j := chartRestriction f g hker
  let : Algebra (E ⧸ I) C := j.toRingHom.toAlgebra
  have hloc : IsLocalization.Away (Ideal.Quotient.mk I (minorProduct R n)) C :=
    isLocalization_chartRestriction f g hker (minorProduct R n) φ.toRingHom hφ (fun _ => rfl)
  refine ⟨Spec.map (CommRingCat.ofHom j.toRingHom), ?_, ?_⟩
  · exact IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk I (minorProduct R n))
  · change Spec.map (CommRingCat.ofHom j.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (E ⧸ I))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext r
    exact j.commutes r

set_option backward.isDefEq.respectTransparency false in
/-- When the principal chart is smooth and has a section, all fibres
of the flat matrix closure are smooth by translation. -/
theorem matrixClosure_smooth_of_chart [IsNoetherianRing R]
    {C : Type u} [CommRing C] [Algebra R C] [Algebra.Smooth R C]
    (φ : CellCoordinates R n →ₐ[R] C) (hφ : Function.Surjective φ)
    (hker : RingHom.ker (rationalMatrixCoordinates (R := R) B ρ) =
      RingHom.ker (φ.comp (IsScalarTower.toAlgHom R (MatrixGroupCoordinates R n) (CellCoordinates R n))))
    (s : C →ₐ[R] R) :
    Smooth (matrixClosure (R := R) B ρ).X.hom := by
  let H := matrixClosure (R := R) B ρ
  let A := MatrixClosureCoordinates (R := R) B ρ
  let f := H.X.hom
  have hf : f = Spec.map (CommRingCat.ofHom (algebraMap R A)) := rfl
  have hcoords := matrixClosure_coordinates (R := R) B ρ
  have hflat : Flat f := by
    rw [hf, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr hcoords.1
  have hfp : LocallyOfFinitePresentation f := by
    rw [hf, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.finitePresentation_algebraMap.mpr hcoords.2
  let : GrpObj (Over.mk f) := H.grp
  obtain ⟨i, hi, hcomp⟩ := matrixClosure_chart (R := R) B ρ φ hφ hker
  have his : Smooth (i ≫ f) := by
    rw [hcomp, HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  let s' := Spec.map (CommRingCat.ofHom s.toRingHom)
  have hs : s' ≫ i ≫ f = 𝟙 _ := by
    rw [hcomp, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    exact s.commutes r
  exact smooth_of_smooth_open_with_section f i s' hs

end ClosureGeometry

section OverIntegers

open Specs.IntegralSemisimpleModel (Integers IntegralGroup integerAlgebra)
open Specs.RationalRealization (RationalField)
open Specs.IntegralLattices (Index)

attribute [local instance] integerAlgebra

private theorem integers_isPrincipalIdealRing : IsPrincipalIdealRing Integers.{u} :=
  IsPrincipalIdealRing.of_surjective ULift.ringEquiv.symm.toRingHom ULift.ringEquiv.symm.surjective

private theorem integers_isFractionRing : IsFractionRing Integers.{u} RationalField.{u} := by
  let e : ℚ ≃ₐ[ℤ] RationalField.{u} :=
    { ULift.ringEquiv.symm with
      commutes' := fun r => map_intCast ULift.ringEquiv.symm r }
  let : IsFractionRing ℤ RationalField.{u} := IsFractionRing.of_algEquiv e
  exact IsFractionRing.of_ringEquiv_left (ULift.ringEquiv : Integers ≃+* ℤ) fun _ => rfl

private theorem integers_scalarTower (B : Type u) [CommRing B] [Algebra RationalField.{u} B] :
    @IsScalarTower Integers.{u} RationalField.{u} B
      (integerAlgebra RationalField.{u}).toSMul
      (inferInstance : Algebra RationalField.{u} B).toSMul (integerAlgebra B).toSMul :=
  IsScalarTower.of_algebraMap_eq fun (x : Integers.{u}) =>
    (map_intCast (algebraMap RationalField.{u} B) x.down).symm

/-- The closure of a rational matrix representation over the lifted integers. -/
def integralMatrixClosure (B : CommHopfAlgCat.{u} RationalField.{u}) {n : ℕ}
    (ρ : convolutionPoints B ⟶ Specs.StandardGroups.generalLinearPoints RationalField (Index.{u} n)) :
    IntegralGroup.{u} := by
  let : IsDomain Integers.{u} :=
    (ULift.ringEquiv : Integers.{u} ≃+* ℤ).toMulEquiv.isDomain ℤ
  let : IsPrincipalIdealRing Integers.{u} := integers_isPrincipalIdealRing
  let : IsFractionRing Integers.{u} RationalField.{u} := integers_isFractionRing
  letI : Algebra Integers.{u} RationalField.{u} := integerAlgebra _
  letI : Algebra Integers.{u} B := integerAlgebra _
  letI := integers_scalarTower B
  exact matrixClosure (R := Integers.{u}) B ρ

end OverIntegers

section Height

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (Realization)
open Specs.CharacterPairing (pairing)
open Specs.CharacterDescent (Cocharacter)
open Specs.BorelsAndChambers (IsRegular positiveRoots)
open Specs.IntegralLattices (Positive Negative)

variable {k : Type u} [Field k] {D : BasedRootDatum.{u}}
  {A : Specs.RootGroups.AdditiveLine k} (F : Realization D A)

/-- The integral height functional of the ordered weight basis, read as a
cocharacter of the marked torus through the perfect pairing. -/
def heightCocharacter (height : D.X →ₗ[ℤ] ℤ) : Cocharacter F.pinned.pair.T.group :=
  Additive.toMul (F.datumIso.val.coweightEquiv.symm
    (D.datum.toLinearMap.flip.toPerfPair.symm height))

set_option backward.isDefEq.respectTransparency false in
theorem heightCocharacter_pairing (height : D.X →ₗ[ℤ] ℤ) (a : D.I) :
    pairing F.pinned.pair.T.group (F.datumIso.val.indexEquiv a).val
      (heightCocharacter F height) = height (D.datum.root a) := by
  let : IsCommMonObj F.pinned.pair.T.group.X := F.attached.comm
  rw [← F.attached.datum.pairing_eq, ← F.attached.datum.root_eq]
  let y := D.datum.toLinearMap.flip.toPerfPair.symm height
  change F.attached.toBased.datum.root' (F.datumIso.val.indexEquiv a)
    (F.datumIso.val.coweightEquiv.symm y) = _
  rw [F.datumIso.val.root'_coweightEquiv]
  exact DFunLike.congr_fun (D.datum.toLinearMap.flip.toPerfPair.apply_symm_apply height)
    (D.datum.root a)

/-- Positive and negative root signs for the weight-basis height are the
signs in the actual marked root system. -/
theorem heightCocharacter_regular (height : D.X →ₗ[ℤ] ℤ)
    (hp : ∀ a : Positive D, 0 < height (D.datum.root a))
    (hn : ∀ a : Negative D, height (D.datum.root a) < 0) :
    IsRegular F.pinned.pair.T (heightCocharacter F height) ∧
      F.datumIso.val.indexEquiv '' {a | D.base.IsPos a} =
        positiveRoots F.pinned.pair.T (heightCocharacter F height) := by
  constructor
  · intro α
    obtain ⟨a, rfl⟩ := F.datumIso.val.indexEquiv.surjective α
    rw [heightCocharacter_pairing]
    by_cases ha : D.base.IsPos a
    · exact (hp ⟨a, ha⟩).ne'
    · exact (hn ⟨a, ha⟩).ne
  · ext α
    obtain ⟨a, rfl⟩ := F.datumIso.val.indexEquiv.surjective α
    have hsign : D.base.IsPos a ↔ F.datumIso.val.indexEquiv a ∈
        positiveRoots F.pinned.pair.T (heightCocharacter F height) := by
      change D.base.IsPos a ↔ 0 < pairing _ (F.datumIso.val.indexEquiv a).val _
      rw [heightCocharacter_pairing]
      exact ⟨fun ha => hp ⟨a, ha⟩, fun h => by
        by_contra ha
        exact (hn ⟨a, ha⟩).not_gt h⟩
    constructor
    · rintro ⟨b, hb, hab⟩
      have heq := F.datumIso.val.indexEquiv.injective hab
      exact hsign.mp (heq ▸ hb)
    · exact fun ha => ⟨a, hsign.mpr ha, rfl⟩

open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap IntegerCharacters)
open LinearAlgebraicGroups.CocharacterDynamics (oppositeCocharacter)

section OppositeCocharacter

variable {k : Type u} [Field k]

private abbrev multiplicativeGroup := specGroup (groupAlgebra k IntegerCharacters.{u})

private theorem multiplicativeLine_inverse :
    (specGroupMap (groupAlgebraMap k (invMonoidHom (α := IntegerCharacters.{u})))).hom.hom =
      GrpObj.inv (X := (multiplicativeGroup (k := k)).X) := by
  let C := MonoidAlgebra k IntegerCharacters.{u}
  have h : (MonoidAlgebra.mapDomainBialgHom k (invMonoidHom (α := IntegerCharacters.{u}))).toAlgHom =
      HopfAlgebra.antipodeAlgHom k C := by
    apply MonoidAlgebra.algHom_ext
    · intro m
      change (MonoidAlgebra.mapDomainBialgHom k (invMonoidHom (α := IntegerCharacters.{u})))
        (MonoidAlgebra.single m 1) = HopfAlgebra.antipode k (MonoidAlgebra.single m 1 : C)
      rw [MonoidAlgebra.mapDomainBialgHom_single, MonoidAlgebra.antipode_single, HopfAlgebra.antipode_one]
      rfl
    · exact Subsingleton.elim _ _
  exact congrArg (fun f : C →ₐ[k] C =>
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op) h

private theorem oppositeCocharacter_eq_inv {T : Specs.GroupScheme k} [IsCommMonObj T.X]
    (c : Cocharacter T) : oppositeCocharacter c = c⁻¹ := by
  apply Grp.hom_ext
  change (specGroupMap (groupAlgebraMap k (invMonoidHom (α := IntegerCharacters.{u})))).hom.hom ≫
    c.hom.hom = c.hom.hom ≫ GrpObj.inv (X := T.X)
  rw [multiplicativeLine_inverse]
  exact GrpObj.inv_hom c.hom.hom

end OppositeCocharacter

set_option backward.isDefEq.respectTransparency false in
theorem heightCocharacter_pairing_opposite (height : D.X →ₗ[ℤ] ℤ) (a : D.I) :
    pairing F.pinned.pair.T.group (F.datumIso.val.indexEquiv a).val
      (oppositeCocharacter (heightCocharacter F height)) = -height (D.datum.root a) := by
  let : IsCommMonObj F.pinned.pair.T.group.X := F.attached.comm
  have h₁ := heightCocharacter_pairing F height a
  rw [oppositeCocharacter_eq_inv, ← F.attached.datum.pairing_eq]
  rw [← F.attached.datum.pairing_eq] at h₁
  change F.attached.datum.rootDatum.toLinearMap (Additive.ofMul (F.datumIso.val.indexEquiv a).val)
    (-Additive.ofMul (heightCocharacter F height)) = _
  rw [map_neg, h₁]

/-- The negative list corresponding to the integral height is the
positive list for the opposite cocharacter. -/
theorem heightCocharacter_negativeRoots (height : D.X →ₗ[ℤ] ℤ)
    (hp : ∀ a : Positive D, 0 < height (D.datum.root a))
    (hn : ∀ a : Negative D, height (D.datum.root a) < 0) :
    F.datumIso.val.indexEquiv '' {a | ¬ D.base.IsPos a} =
      positiveRoots F.pinned.pair.T (oppositeCocharacter (heightCocharacter F height)) := by
  ext α
  obtain ⟨a, rfl⟩ := F.datumIso.val.indexEquiv.surjective α
  have hs : ¬ D.base.IsPos a ↔ F.datumIso.val.indexEquiv a ∈
      positiveRoots F.pinned.pair.T (oppositeCocharacter (heightCocharacter F height)) := by
    change (¬ D.base.IsPos a) ↔ 0 < pairing _ (F.datumIso.val.indexEquiv a).val _
    rw [heightCocharacter_pairing_opposite, neg_pos]
    exact ⟨fun ha => hn ⟨a, ha⟩, fun h ha => (hp ⟨a, ha⟩).not_gt h⟩
  constructor
  · rintro ⟨b, hb, hab⟩
    exact hs.mp (F.datumIso.val.indexEquiv.injective hab ▸ hb)
  · exact fun ha => ⟨a, hs.mpr ha, rfl⟩

open Specs.OrderedRootProducts (Enumerates RegularRootCell rootCellMap)

private theorem enumerates_map_equiv {I J : Type u} (e : I ≃ J) {l : List I} {S : Set I}
    (h : Enumerates l S) : Enumerates (l.map e) (e '' S) := by
  refine ⟨h.1.map e.injective, ?_⟩
  intro j
  simp only [List.mem_map, Set.mem_image, h.2]

/-- The field root-cell theorem applies to the two signed enumerations in
the marking of the given realization. -/
theorem markedRootCell_isOpenImmersion (cellTheorem : RegularRootCell.{u})
    (height : D.X →ₗ[ℤ] ℤ)
    (hp : ∀ a : Positive D, 0 < height (D.datum.root a))
    (hn : ∀ a : Negative D, height (D.datum.root a) < 0)
    (negative positive : List D.I)
    (hnl : Enumerates negative {a | ¬ D.base.IsPos a})
    (hpl : Enumerates positive {a | D.base.IsPos a}) :
    IsOpenImmersion (rootCellMap F.pinned.pair.T F.pinned.roots
      (negative.map F.datumIso.val.indexEquiv) (positive.map F.datumIso.val.indexEquiv)).left := by
  have hpos := heightCocharacter_regular F height hp hn
  have hn' := enumerates_map_equiv F.datumIso.val.indexEquiv hnl
  have hp' := enumerates_map_equiv F.datumIso.val.indexEquiv hpl
  rw [heightCocharacter_negativeRoots F height hp hn] at hn'
  rw [hpos.2] at hp'
  exact cellTheorem F.pinned.pair.G F.pinned.pair.reductive F.pinned.pair.T F.pinned.pair.split
    F.pinned.pair.maximal (heightCocharacter F height) hpos.1 F.pinned.roots _ _ hn' hp'

end Height

section IntegralRootMatrices

open Specs.IntegralLattices (Index)
open Specs.RationalRealization (RationalField)

variable {n : ℕ}

private theorem rationalField_intCast_injective :
    Function.Injective (Int.castRingHom RationalField.{u}) := fun _ _ h =>
  Int.cast_injective (α := ℚ) (congrArg ULift.down h)

/-- Evaluate a matrix of integer polynomials on a scalar in any commutative ring. -/
def integralPolynomialMatrix {R : Type*} [CommRing R]
    (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ)) (x : R) :
    Matrix (Index.{u} n) (Index.{u} n) R :=
  (Polynomial.eval₂RingHom (Int.castRingHom R) x).mapMatrix p

private theorem integralPolynomialMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ)) (x : R) :
    g.mapMatrix (integralPolynomialMatrix p x) = integralPolynomialMatrix p (g x) := by
  apply Matrix.ext
  intro i j
  change g ((p i j).eval₂ (Int.castRingHom R) x) =
    (p i j).eval₂ (Int.castRingHom S) (g x)
  rw [Polynomial.hom_eval₂, show g.comp (Int.castRingHom R) = Int.castRingHom S from
    Subsingleton.elim _ _]

/-- The additive matrix law for an integer polynomial root coordinate
descends from the universal rational polynomial algebra. -/
theorem integralPolynomialMatrix_add_of_generic
    (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (h : ∀ (R : TestAlgebra RationalField.{u}) (x y : R),
      integralPolynomialMatrix p (x + y) =
        integralPolynomialMatrix p x * integralPolynomialMatrix p y)
    (R : Type u) [CommRing R] (x y : R) :
    integralPolynomialMatrix p (x + y) =
      integralPolynomialMatrix p x * integralPolynomialMatrix p y := by
  let A := MvPolynomial Bool ℤ
  let B := MvPolynomial Bool RationalField.{u}
  let f : A →+* B := MvPolynomial.map (Int.castRingHom RationalField.{u})
  let X : A := MvPolynomial.X false
  let Y : A := MvPolynomial.X true
  have hf : Function.Injective f := MvPolynomial.map_injective _ rationalField_intCast_injective
  have key : integralPolynomialMatrix p (X + Y) =
      integralPolynomialMatrix p X * integralPolynomialMatrix p Y := by
    have he : f.mapMatrix (integralPolynomialMatrix p (X + Y)) =
        f.mapMatrix (integralPolynomialMatrix p X * integralPolynomialMatrix p Y) := by
      rw [map_mul, integralPolynomialMatrix_map, integralPolynomialMatrix_map,
        integralPolynomialMatrix_map, map_add]
      exact h (CommAlgCat.of RationalField.{u} B) (f X) (f Y)
    exact Matrix.ext fun i j => hf (congrFun (congrFun he i) j)
  let g : A →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R)
    (fun t : Bool => if t then y else x)
  have hX : g X = x := MvPolynomial.eval₂Hom_X' _ _ false
  have hY : g Y = y := MvPolynomial.eval₂Hom_X' _ _ true
  have he := congrArg g.mapMatrix key
  rwa [map_mul, integralPolynomialMatrix_map, integralPolynomialMatrix_map,
    integralPolynomialMatrix_map, map_add, hX, hY] at he

/-- The zero parameter of an integral root polynomial gives identity
whenever it gives identity over the rationals. -/
theorem integralPolynomialMatrix_zero_of_generic
    (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (h : integralPolynomialMatrix p (0 : RationalField.{u}) = 1)
    (R : Type*) [CommRing R] :
    integralPolynomialMatrix p (0 : R) = 1 := by
  have hZ : integralPolynomialMatrix p (0 : ℤ) = 1 := by
    have hQ : (Int.castRingHom RationalField.{u}).mapMatrix
          (integralPolynomialMatrix p (0 : ℤ)) =
        (Int.castRingHom RationalField.{u}).mapMatrix 1 := by
      rw [integralPolynomialMatrix_map, map_zero, map_one, h]
    exact Matrix.ext fun i j => rationalField_intCast_injective (congrFun (congrFun hQ i) j)
  have he := congrArg (Int.castRingHom R).mapMatrix hZ
  rwa [integralPolynomialMatrix_map, map_zero, map_one] at he

end IntegralRootMatrices

section AffineCoordinates
variable {k : Type u} [CommRing k]

private abbrev affineObject (A : Type u) [CommRing A] [Algebra k A] :
    Over (Spec (CommRingCat.of k)) :=
  (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A))

private abbrev affineMap {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) : affineObject (k := k) B ⟶ affineObject (k := k) A :=
  (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op

private def affineHomEquiv (A B : Type u) [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] :
    (A →ₐ[k] B) ≃ (affineObject (k := k) B ⟶ affineObject (k := k) A) where
  toFun := affineMap
  invFun f := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage f).unop.hom
  left_inv f := by
    change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom f).op)).unop.hom = f
    rw [Functor.FullyFaithful.preimage_map]
    rfl
  right_inv f := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage f

private theorem iso_of_affine_point_bijective {A : Type u} [CommRing A] [Algebra k A]
    {Y : Over (Spec (CommRingCat.of k))} (hY : IsAffine Y.left)
    (f : affineObject (k := k) A ⟶ Y)
    (h : ∀ (B : CommAlgCat.{u} k), Function.Bijective
      (fun p : affineObject (k := k) B ⟶ affineObject (k := k) A => p ≫ f)) :
    IsIso f := by
  obtain ⟨B, ⟨e⟩⟩ := essImage_algSpec.mpr hY
  obtain ⟨g, hg⟩ := (h B.unop).2 e.hom
  exact ⟨⟨e.inv ≫ g,
    (h (CommAlgCat.of k A)).1 (by simp [Category.assoc, hg]),
    by simp [Category.assoc, hg]⟩⟩

private theorem affine_tensor {X Y : Over (Spec (CommRingCat.of k))}
    (hX : IsAffine X.left) (hY : IsAffine Y.left) : IsAffine (X ⊗ Y).left := by
  rw [Over.tensorObj_left]
  exact inferInstance

private def polynomialPointEquiv (B : CommAlgCat.{u} k) :
    B ≃ (affineObject (k := k) B ⟶ affineObject (k := k) (Polynomial k)) :=
  (Polynomial.aevalEquiv (R := k) (A := B)).trans (affineHomEquiv (Polynomial k) B)

private theorem polynomialPointEquiv_apply (B : CommAlgCat.{u} k) (b : B) :
    polynomialPointEquiv B b = affineMap (Polynomial.aeval b : Polynomial k →ₐ[k] B) := rfl

private theorem affineMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] (f : A →ₐ[k] B) (g : B →ₐ[k] C) :
    affineMap g ≫ affineMap f = affineMap (f := g.comp f) := by
  rw [← Functor.map_comp]
  rfl

private theorem polynomialPoint_naturality {A B : CommAlgCat.{u} k} (f : A →ₐ[k] B) (a : A) :
    affineMap f ≫ polynomialPointEquiv A a = polynomialPointEquiv B (f a) := by
  rw [polynomialPointEquiv_apply, polynomialPointEquiv_apply, affineMap_comp]
  congr 1
  apply Polynomial.algHom_ext
  simp

end AffineCoordinates

section OrderedFactors
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {I : Type u}
  (X : I → C)

private abbrev orderedFactors : List I → C
  | [] => 𝟙_ C
  | i :: l => X i ⊗ orderedFactors l

variable {X}

private def orderedFactorPoint {Z : C} (p : ∀ i, Z ⟶ X i) :
    (l : List I) → Z ⟶ orderedFactors X l
  | [] => toUnit _
  | i :: l => lift (p i) (orderedFactorPoint p l)

private theorem comp_orderedFactorPoint {Z W : C} (f : W ⟶ Z) (p : ∀ i, Z ⟶ X i)
    (l : List I) :
    f ≫ orderedFactorPoint p l = orderedFactorPoint (fun i => f ≫ p i) l := by
  induction l with
  | nil => exact toUnit_unique _ _
  | cons i l ih =>
    apply CartesianMonoidalCategory.hom_ext
    · simp [orderedFactorPoint]
    · simp [orderedFactorPoint, ih]

private theorem orderedFactorPoint_eq {Z : C} (p q : ∀ i, Z ⟶ X i) (l : List I) :
    orderedFactorPoint p l = orderedFactorPoint q l ↔ ∀ i ∈ l, p i = q i := by
  induction l with
  | nil => simp [orderedFactorPoint]
  | cons i l ih =>
    constructor
    · intro h j hj
      rcases List.mem_cons.mp hj with hji | hj
      · subst j
        simpa [orderedFactorPoint] using congrArg (fun f => f ≫ fst (X i) (orderedFactors X l)) h
      · apply ih.mp _ j hj
        simpa [orderedFactorPoint] using congrArg (fun f => f ≫ snd (X i) (orderedFactors X l)) h
    · intro h
      apply CartesianMonoidalCategory.hom_ext
      · simpa [orderedFactorPoint] using h i List.mem_cons_self
      · simpa [orderedFactorPoint] using ih.mpr fun j hj => h j (List.mem_cons_of_mem i hj)

private theorem exists_orderedFactorPoint {Z : C} (P : Type*) [Nonempty P]
    (e : ∀ i, P → (Z ⟶ X i)) (he : ∀ i, Function.Surjective (e i)) (l : List I)
    (hl : l.Nodup) (p : Z ⟶ orderedFactors X l) :
    ∃ v : I → P, orderedFactorPoint (fun i => e i (v i)) l = p := by
  classical
  induction l with
  | nil => exact ⟨fun _ => Classical.choice inferInstance, toUnit_unique _ _⟩
  | cons i l ih =>
    obtain ⟨v, hv⟩ := ih (List.nodup_cons.mp hl).2 (p ≫ snd _ _)
    obtain ⟨a, ha⟩ := he i (p ≫ fst _ _)
    refine ⟨Function.update v i a, CartesianMonoidalCategory.hom_ext _ _ ?_ ?_⟩
    · change lift (e i (Function.update v i a i)) _ ≫ fst _ _ = _
      simpa only [lift_fst, Function.update_self] using ha
    · change lift (e i (Function.update v i a i)) _ ≫ snd _ _ = _
      rw [lift_snd, ← hv]
      apply (orderedFactorPoint_eq _ _ l).mpr
      intro j hj
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hj (List.nodup_cons.mp hl).1)]

end OrderedFactors

section EvaluateProducts

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]
  {U T V G W : C} [GrpObj G]

private theorem lift_mul_factors (x : W ⟶ U) (y : W ⟶ V) (a : U ⟶ G) (b : V ⟶ G) :
    lift x y ≫ ((fst U V ≫ a) * (snd U V ≫ b)) = (x ≫ a) * (y ≫ b) := by
  simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]

private theorem lift_mul_three_factors (x : W ⟶ U) (t : W ⟶ T) (y : W ⟶ V)
    (a : U ⟶ G) (c : T ⟶ G) (b : V ⟶ G) :
    lift x (lift t y) ≫ ((fst U (T ⊗ V) ≫ a) *
      (snd U (T ⊗ V) ≫ ((fst T V ≫ c) * (snd T V ≫ b)))) =
    (x ≫ a) * (t ≫ c) * (y ≫ b) := by
  rw [lift_mul_factors, lift_mul_factors, mul_assoc]

end EvaluateProducts

section CellCoordinates
variable {k : Type u} [CommRing k] {I M : Type u} [CommRing M] [Algebra k M]
  {X : I → Over (Spec (CommRingCat.of k))} {Y : Over (Spec (CommRingCat.of k))}
  (rootIso : ∀ i, affineObject (k := k) (Polynomial k) ≅ X i)
  (torusIso : affineObject (k := k) M ≅ Y)

private abbrev splitCellOver (l r : List I) :=
  orderedFactors X l ⊗ (Y ⊗ orderedFactors X r)

private def splitCellPoint (l r : List I) (B : CommAlgCat.{u} k)
    (t : M →ₐ[k] B) (v : I → B) : affineObject (k := k) B ⟶ splitCellOver (X := X) (Y := Y) l r :=
  let root i := polynomialPointEquiv B (v i) ≫ (rootIso i).hom
  lift (orderedFactorPoint root l) (lift (affineMap t ≫ torusIso.hom) (orderedFactorPoint root r))

private theorem comp_splitCellPoint (l r : List I) {B C : CommAlgCat.{u} k}
    (f : B →ₐ[k] C) (t : M →ₐ[k] B) (v : I → B) :
    affineMap f ≫ splitCellPoint rootIso torusIso l r B t v =
      splitCellPoint rootIso torusIso l r C (f.comp t) (f ∘ v) := by
  rw [splitCellPoint, splitCellPoint, comp_lift, comp_lift, comp_orderedFactorPoint,
    comp_orderedFactorPoint]
  simp [← Category.assoc, affineMap_comp, polynomialPoint_naturality]

private theorem splitCellPoint_bijective (l r : List I)
    (hl : l.Nodup) (hr : r.Nodup) (hcover : ∀ i, i ∈ l ∨ i ∈ r)
    (hdisj : ∀ i, i ∈ l → i ∉ r) (B : CommAlgCat.{u} k) :
    Function.Bijective (fun q : (M →ₐ[k] B) × (I → B) =>
      splitCellPoint rootIso torusIso l r B q.1 q.2) := by
  classical
  let e (i : I) : B ≃ (affineObject (k := k) B ⟶ X i) :=
    (polynomialPointEquiv B).trans ((Iso.refl _).homCongr (rootIso i))
  let eT : (M →ₐ[k] B) ≃ (affineObject (k := k) B ⟶ Y) :=
    (affineHomEquiv M B).trans ((Iso.refl _).homCongr torusIso)
  change Function.Bijective (fun q : (M →ₐ[k] B) × (I → B) =>
    lift (orderedFactorPoint (fun i => e i (q.2 i)) l)
      (lift (eT q.1) (orderedFactorPoint (fun i => e i (q.2 i)) r)))
  constructor
  · rintro ⟨s, u⟩ ⟨t, v⟩ h
    have hleft := congrArg (fun f : _ ⟶ splitCellOver (X := X) (Y := Y) l r => f ≫ fst _ _) h
    have hright := congrArg (fun f : _ ⟶ splitCellOver (X := X) (Y := Y) l r => f ≫ snd _ _) h
    simp only [lift_fst, lift_snd] at hleft hright
    have htor := congrArg (fun f : _ ⟶ Y ⊗ orderedFactors X r => f ≫ fst _ _) hright
    have hpos := congrArg (fun f : _ ⟶ Y ⊗ orderedFactors X r => f ≫ snd _ _) hright
    simp only [lift_fst, lift_snd] at htor hpos
    refine Prod.ext (eT.injective htor) (funext fun i => (e i).injective ?_)
    exact (hcover i).elim ((orderedFactorPoint_eq _ _ l).mp hleft i)
      ((orderedFactorPoint_eq _ _ r).mp hpos i)
  · intro p
    obtain ⟨v₁, hv₁⟩ := exists_orderedFactorPoint B (fun i => e i) (fun i => (e i).surjective)
      l hl (p ≫ fst _ _)
    obtain ⟨v₂, hv₂⟩ := exists_orderedFactorPoint B (fun i => e i) (fun i => (e i).surjective)
      r hr (p ≫ snd _ _ ≫ snd _ _)
    obtain ⟨t, ht⟩ := eT.surjective (p ≫ snd _ _ ≫ fst _ _)
    refine ⟨⟨t, fun i => if i ∈ l then v₁ i else v₂ i⟩, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, ← hv₁]
      apply (orderedFactorPoint_eq _ _ l).mpr
      intro i hi
      simp only [ite_eq_left hi]
    · rw [lift_snd]
      apply CartesianMonoidalCategory.hom_ext
      · simpa only [lift_fst, Category.assoc] using ht
      · rw [lift_snd, Category.assoc, ← hv₂]
        apply (orderedFactorPoint_eq _ _ r).mpr
        intro i hi
        have hi' : i ∉ l := fun h => hdisj i h hi
        simp only [ite_eq_right hi']

private theorem orderedFactors_affine {X : I → Over (Spec (CommRingCat.of k))}
    (hX : ∀ i, IsAffine (X i).left) (l : List I) : IsAffine (orderedFactors X l).left := by
  induction l with
  | nil => exact inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  | cons i l ih => exact affine_tensor (hX i) ih

private def splitCellCoordinateMap (l r : List I) :
    affineObject (k := k) (MvPolynomial I M) ⟶ splitCellOver (X := X) (Y := Y) l r :=
  splitCellPoint rootIso torusIso l r (CommAlgCat.of k (MvPolynomial I M))
    (IsScalarTower.toAlgHom k M (MvPolynomial I M)) MvPolynomial.X

set_option maxHeartbeats 800000 in
private theorem splitCellCoordinateMap_isIso (l r : List I)
    (hl : l.Nodup) (hr : r.Nodup) (hcover : ∀ i, i ∈ l ∨ i ∈ r)
    (hdisj : ∀ i, i ∈ l → i ∉ r) :
    IsIso (splitCellCoordinateMap rootIso torusIso l r) := by
  have affine_iso {A : Type u} [CommRing A] [Algebra k A]
      {Z : Over (Spec (CommRingCat.of k))} (e : affineObject (k := k) A ≅ Z) :
      IsAffine Z.left := essImage_algSpec.mp ⟨op (CommAlgCat.of k A), ⟨e⟩⟩
  apply iso_of_affine_point_bijective (affine_tensor
    (orderedFactors_affine (fun i => affine_iso (rootIso i)) l)
    (affine_tensor (affine_iso torusIso) (orderedFactors_affine (fun i => affine_iso (rootIso i)) r)))
  intro B
  let split (f : MvPolynomial I M →ₐ[k] B) : (M →ₐ[k] B) × (I → B) :=
    (f.comp (IsScalarTower.toAlgHom k M (MvPolynomial I M)), fun i => f (MvPolynomial.X i))
  have hs : Function.Bijective split := by
    constructor
    · intro f g h
      apply AlgHom.toRingHom_injective
      apply MvPolynomial.ringHom_ext
      · exact DFunLike.congr_fun (congrArg Prod.fst h)
      · exact congrFun (congrArg Prod.snd h)
    · rintro ⟨t, v⟩
      refine ⟨MvPolynomial.aevalTower t v, Prod.ext ?_ ?_⟩
      · ext x
        exact MvPolynomial.aevalTower_C t v x
      · exact funext (MvPolynomial.aevalTower_X t v)
  let a := affineHomEquiv (k := k) (MvPolynomial I M) B
  let c := splitCellCoordinateMap rootIso torusIso l r
  have heq : (fun g => g ≫ c) ∘ a =
      (fun p : (M →ₐ[k] B) × (I → B) => splitCellPoint rootIso torusIso l r B p.1 p.2) ∘ split := by
    funext f
    change affineMap f ≫
      splitCellPoint rootIso torusIso l r (CommAlgCat.of k (MvPolynomial I M))
        (IsScalarTower.toAlgHom k M (MvPolynomial I M)) MvPolynomial.X =
      splitCellPoint rootIso torusIso l r B
        (f.comp (IsScalarTower.toAlgHom k M (MvPolynomial I M))) (f ∘ MvPolynomial.X)
    exact comp_splitCellPoint rootIso torusIso l r (B := CommAlgCat.of k (MvPolynomial I M))
      (C := B) f (IsScalarTower.toAlgHom k M (MvPolynomial I M)) MvPolynomial.X
  have hb : Function.Bijective ((fun g => g ≫ c) ∘ a) := by
    rw [heq]
    exact (splitCellPoint_bijective rootIso torusIso l r hl hr hcover hdisj B).comp hs
  exact (Function.Bijective.of_comp_iff (fun g => g ≫ c) a.bijective).mp hb
end CellCoordinates

section IntegralCellEvaluation

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Integers integerAlgebra)
open Specs.IntegralLattices (Index Positive Negative orderedMatrix ClosedRootImage)
open Specs.MatrixOpenCell (Factors)

attribute [local instance] integerAlgebra

private def overLiftedIntegers {A B : Type u} [CommRing A] [CommRing B]
    [Algebra Integers.{u} A] [Algebra Integers.{u} B] (f : A →+* B) : A →ₐ[Integers.{u}] B where
  toRingHom := f
  commutes' := by
    intro x
    let g := (algebraMap Integers.{u} A).comp (ULift.ringEquiv.symm : ℤ ≃+* Integers.{u}).toRingHom
    let h := (algebraMap Integers.{u} B).comp (ULift.ringEquiv.symm : ℤ ≃+* Integers.{u}).toRingHom
    exact RingHom.congr_fun (Subsingleton.elim (f.comp g) h) x.down

variable (D : BasedRootDatum.{u}) (k : Type u) [CommRing k]

private abbrev CellPolynomialAlgebra := MvPolynomial D.I (MonoidAlgebra k (Multiplicative D.X))

private def cellScalars : IntegralCellCoordinates D →ₐ[Integers.{u}] CellPolynomialAlgebra D k :=
  overLiftedIntegers <| MvPolynomial.map
    ((AddMonoidAlgebra.toMultiplicativeAlgEquiv k k D.X).toRingHom.comp
      (AddMonoidAlgebra.mapRingHom D.X (Int.castRingHom k)))

private theorem cellScalars_injective (h : Function.Injective (Int.castRingHom k)) :
    Function.Injective (cellScalars D k) :=
  MvPolynomial.map_injective _ ((AddMonoidAlgebra.toMultiplicativeAlgEquiv k k D.X).injective.comp
    (AddMonoidAlgebra.map_injective _ h))

private theorem cellScalars_X (i : D.I) :
    cellScalars D k (MvPolynomial.X i) = MvPolynomial.X i :=
  MvPolynomial.map_X _ _

private theorem cellScalars_monomial (x : D.X) :
    cellScalars D k (MvPolynomial.C (AddMonoidAlgebra.single x 1)) =
      MvPolynomial.C (MonoidAlgebra.single (Multiplicative.ofAdd x) 1) := by
  change (MvPolynomial.map _) (MvPolynomial.C _) = _
  rw [MvPolynomial.map_C, RingHom.comp_apply, AddMonoidAlgebra.mapRingHom_single, map_one]
  exact congrArg MvPolynomial.C (AddMonoidAlgebra.toMultiplicativeAlgEquiv_single (R := k) x (1 : k))

private theorem orderedMatrix_evaluation {n : ℕ} {σ : Type u} {B : Type*} [CommRing B]
    (l : List σ) (p : σ → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (f : MvPolynomial σ ℤ →+* B) :
    f.mapMatrix (orderedMatrix l p) =
      (l.map (fun a => integralPolynomialMatrix (p a) (f (MvPolynomial.X a)))).prod := by
  unfold orderedMatrix
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  apply Matrix.ext
  intro i j
  change f ((p a i j).eval₂ (algebraMap ℤ (MvPolynomial σ ℤ)) (MvPolynomial.X a)) =
    (p a i j).eval₂ (Int.castRingHom B) (f (MvPolynomial.X a))
  rw [Polynomial.hom_eval₂, show f.comp (algebraMap ℤ _) = Int.castRingHom B from
    Subsingleton.elim _ _]

private theorem cellScalars_factors {n : ℕ}
    (negative : List (Negative D)) (positive : List (Positive D))
    (w : Index.{u} n → D.X) (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hneg : IsOrderedRootChart false (orderedMatrix negative (fun a => p a.val)))
    (hpos : IsOrderedRootChart true (orderedMatrix positive (fun a => p a.val))) :
    let T := CellPolynomialAlgebra D k
    let l := (negative.map (fun a => integralPolynomialMatrix (p a.val) (MvPolynomial.X a.val))).prod
    let r := (positive.map (fun a => integralPolynomialMatrix (p a.val) (MvPolynomial.X a.val))).prod
    let t : Matrix (Index.{u} n) (Index.{u} n) T :=
      Matrix.diagonal (fun j => MvPolynomial.C (MonoidAlgebra.single (Multiplicative.ofAdd (w j)) 1))
    (cellScalars D k).toRingHom.mapMatrix (cellFactors negative positive w p hneg hpos).product =
      (Matrix.reindexRingEquiv T Equiv.ulift) (l * t * r) := by
  dsimp only
  let s := (cellScalars D k).toRingHom
  let reindex := Matrix.reindexRingEquiv (CellPolynomialAlgebra D k) (Equiv.ulift : Index.{u} n ≃ Fin n)
  rw [map_mul, map_mul, Specs.MatrixOpenCell.Factors.product, map_mul, map_mul]
  congr 1
  · congr 1
    · simp only [cellFactors]
      have h := orderedMatrix_evaluation negative (fun a => p a.val)
        (s.comp (parameterSubstitution Subtype.val))
      have hx (a : Negative D) :
          (s.comp (parameterSubstitution Subtype.val)) (MvPolynomial.X a) = MvPolynomial.X a.val := by
        simp only [RingHom.comp_apply, parameterSubstitution, MvPolynomial.eval₂Hom_X',
          Function.comp_apply]
        exact cellScalars_X D k a.val
      simp only [hx] at h
      exact congrArg reindex h
    · change (Matrix.diagonal fun i : Fin n =>
        MvPolynomial.C (AddMonoidAlgebra.single (w (ULift.up i)) 1)).map s =
        (Matrix.diagonal fun j => MvPolynomial.C (MonoidAlgebra.single (Multiplicative.ofAdd (w j)) 1)
         ).submatrix Equiv.ulift.symm Equiv.ulift.symm
      rw [Matrix.diagonal_map (map_zero s)]
      rw [Matrix.submatrix_diagonal_equiv]
      congr 1
      funext i
      exact cellScalars_monomial D k _
  · simp only [cellFactors]
    have h := orderedMatrix_evaluation positive (fun a => p a.val)
      (s.comp (parameterSubstitution Subtype.val))
    have hx (a : Positive D) :
        (s.comp (parameterSubstitution Subtype.val)) (MvPolynomial.X a) = MvPolynomial.X a.val := by
      simp only [RingHom.comp_apply, parameterSubstitution, MvPolynomial.eval₂Hom_X',
        Function.comp_apply]
      exact cellScalars_X D k a.val
    simp only [hx] at h
    exact congrArg reindex h

end IntegralCellEvaluation

section MarkedCell

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (Realization RationalField)
open Specs.IntegralLattices (Negative Positive)
open Specs.IntegralRootRelations (RootCoordinates)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.OrderedRootProducts (Enumerates rootProduct rootCellMap product)
open Specs.DiagonalizableGroups (groupAlgebra)
open Specs.AbstractPairing (Root)

variable {D : BasedRootDatum.{u}} {A : Specs.RootGroups.AdditiveLine RationalField.{u}}
  (F : Realization D A)

private abbrev markedRootLabels : D.I ≃ Root F.pinned.pair.T := F.datumIso.val.indexEquiv

private abbrev markedRootFactors (a : D.I) :=
  (F.pinned.roots (markedRootLabels F a)).val.group.X

private def markedFactorsReindex : (l : List D.I) →
    orderedFactors (markedRootFactors F) l ≅
      product (fun a : Root F.pinned.pair.T => (F.pinned.roots a).val.group.X)
        (l.map (markedRootLabels F))
  | [] => Iso.refl _
  | a :: l => MonoidalCategory.tensorIso (Iso.refl (markedRootFactors F a)) (markedFactorsReindex l)

private def markedRootFactorIso (z : RootCoordinates F) (a : D.I) :
    affineObject (k := RationalField.{u}) (Polynomial RationalField.{u}) ≅ markedRootFactors F a :=
  (Grp.forget _).mapIso (z a).val

private abbrev MarkedCellCoordinates (D : BasedRootDatum.{u}) :=
  CellPolynomialAlgebra D RationalField.{u}

set_option backward.isDefEq.respectTransparency false in
private theorem markedRootProduct_evaluation {R : TestAlgebra RationalField.{u}} (z : RootCoordinates F)
    (v : D.I → R) (l : List D.I) :
    orderedFactorPoint (fun a => polynomialPointEquiv R (v a) ≫ (markedRootFactorIso F z a).hom) l ≫
      (markedFactorsReindex F l).hom ≫
      rootProduct F.pinned.roots (l.map (markedRootLabels F)) =
    (l.map (fun a => Specs.IntegralRootRelations.root F z a R (v a))).prod := by
  induction l with
  | nil =>
    change toUnit (affineObject (k := RationalField.{u}) R) ≫ 𝟙 _ ≫
        (1 : 𝟙_ (SchemeOver RationalField.{u}) ⟶ F.pinned.pair.G.val.X) = 1
    rw [Category.id_comp, MonObj.comp_one]
  | cons a l ih =>
    let e := markedRootLabels F
    let i : markedRootFactors F a ⟶ F.pinned.pair.G.val.X :=
      (F.pinned.roots (e a)).val.inclusion.hom.hom
    let p (j : D.I) := polynomialPointEquiv R (v j) ≫ (markedRootFactorIso F z j).hom
    let Q := product (fun j : Root F.pinned.pair.T => (F.pinned.roots j).val.group.X) (l.map e)
    change lift (p a) (orderedFactorPoint p l) ≫
        (𝟙 (markedRootFactors F a) ⊗ₘ (markedFactorsReindex F l).hom) ≫
        ((fst (markedRootFactors F a) Q ≫ i) *
          (snd (markedRootFactors F a) Q ≫ rootProduct F.pinned.roots (l.map e))) = _
    rw [lift_map_assoc, Category.comp_id]
    have h := lift_mul_factors (p a) (orderedFactorPoint p l ≫ (markedFactorsReindex F l).hom)
      i (rootProduct F.pinned.roots (l.map e))
    rw [h]
    have htail : (orderedFactorPoint p l ≫ (markedFactorsReindex F l).hom) ≫
        rootProduct F.pinned.roots (l.map e) =
        (l.map (fun j => Specs.IntegralRootRelations.root F z j R (v j))).prod :=
      (Category.assoc _ _ _).trans ih
    have hhead : p a ≫ i = Specs.IntegralRootRelations.root F z a R (v a) := rfl
    exact congrArg₂ (fun x y : affineObject (k := RationalField.{u}) R ⟶ F.pinned.pair.G.val.X =>
      x * y) hhead htail

private def markedCellPoint (z : RootCoordinates F)
    (τ : specGroup (groupAlgebra RationalField.{u} (Multiplicative D.X)) ≅ F.pinned.pair.T.group)
    (l r : List D.I) :
    GroupPoints F.pinned.pair.G.val (CommAlgCat.of RationalField.{u} (MarkedCellCoordinates D)) :=
  let R := CommAlgCat.of RationalField.{u} (MarkedCellCoordinates D)
  let root (a : D.I) : GroupPoints F.pinned.pair.G.val R :=
    Specs.IntegralRootRelations.root F z a R (MvPolynomial.X a)
  let t := IsScalarTower.toAlgHom RationalField.{u}
    (MonoidAlgebra RationalField.{u} (Multiplicative D.X)) R
  let torus : GroupPoints F.pinned.pair.G.val R :=
    affineMap t ≫ τ.hom.hom.hom ≫ F.pinned.pair.T.inclusion.hom.hom
  (l.map root).prod * torus * (r.map root).prod

set_option maxHeartbeats 1100000 in
set_option backward.isDefEq.respectTransparency false in
private theorem exists_markedRootCell (cellTheorem : Specs.OrderedRootProducts.RegularRootCell.{u})
    (z : RootCoordinates F)
    (τ : specGroup (groupAlgebra RationalField.{u} (Multiplicative D.X)) ≅ F.pinned.pair.T.group)
    (height : D.X →ₗ[ℤ] ℤ) (hp : ∀ a : Positive D, 0 < height (D.datum.root a))
    (hn : ∀ a : Negative D, height (D.datum.root a) < 0)
    (negative positive : List D.I)
    (hnl : Enumerates negative {a | ¬ D.base.IsPos a})
    (hpl : Enumerates positive {a | D.base.IsPos a}) :
    ∃ q : affineObject (k := RationalField.{u}) (MarkedCellCoordinates D) ⟶
          F.pinned.pair.G.val.X,
      IsOpenImmersion q.left ∧ q = markedCellPoint F z τ negative positive := by
  classical
  let e := markedRootLabels F
  let isoNeg := markedFactorsReindex F negative
  let isoPos := markedFactorsReindex F positive
  let j := MonoidalCategory.tensorIso isoNeg
    (MonoidalCategory.tensorIso (Iso.refl F.pinned.pair.T.group.X) isoPos)
  let c := splitCellCoordinateMap (markedRootFactorIso F z) ((Grp.forget _).mapIso τ)
    negative positive
  have hcover (a : D.I) : a ∈ negative ∨ a ∈ positive := by
    by_cases ha : D.base.IsPos a
    · exact Or.inr ((hpl.2 a).mpr ha)
    · exact Or.inl ((hnl.2 a).mpr ha)
  have hdisj (a : D.I) (ha : a ∈ negative) : a ∉ positive :=
    fun hb => (hnl.2 a).mp ha ((hpl.2 a).mp hb)
  have hc : IsIso c := splitCellCoordinateMap_isIso _ _ _ _ hnl.1 hpl.1 hcover hdisj
  let q := rootCellMap F.pinned.pair.T F.pinned.roots (negative.map e) (positive.map e)
  have hq : IsOpenImmersion q.left :=
    markedRootCell_isOpenImmersion F cellTheorem
      height hp hn negative positive hnl hpl
  have hcLeft : IsIso c.left := (Over.forget _).map_isIso c
  have hjLeft : IsIso j.hom.left := (Over.forget _).map_isIso j.hom
  refine ⟨c ≫ j.hom ≫ q, ?_, ?_⟩
  · change IsOpenImmersion (c.left ≫ j.hom.left ≫ q.left)
    infer_instance
  · let R := CommAlgCat.of RationalField.{u} (MarkedCellCoordinates D)
    let t := IsScalarTower.toAlgHom RationalField.{u} (MonoidAlgebra RationalField.{u} (Multiplicative D.X)) R
    let root (a : D.I) := polynomialPointEquiv R (MvPolynomial.X a) ≫ (markedRootFactorIso F z a).hom
    change lift (orderedFactorPoint root negative)
      (lift (affineMap t ≫ τ.hom.hom.hom) (orderedFactorPoint root positive)) ≫
      (isoNeg.hom ⊗ₘ (𝟙 F.pinned.pair.T.group.X ⊗ₘ isoPos.hom)) ≫
      rootCellMap F.pinned.pair.T F.pinned.roots (negative.map e) (positive.map e) = _
    rw [lift_map_assoc, lift_map, Category.comp_id]
    have h := lift_mul_three_factors (orderedFactorPoint root negative ≫ isoNeg.hom)
      (affineMap t ≫ τ.hom.hom.hom) (orderedFactorPoint root positive ≫ isoPos.hom)
      (rootProduct F.pinned.roots (negative.map e)) F.pinned.pair.T.inclusion.hom.hom
      (rootProduct F.pinned.roots (positive.map e))
    change _ ≫ ((fst _ _ ≫ rootProduct F.pinned.roots (negative.map e)) *
      (snd _ _ ≫ ((fst _ _ ≫ F.pinned.pair.T.inclusion.hom.hom) *
        (snd _ _ ≫ rootProduct F.pinned.roots (positive.map e))))) = _
    rw [h]
    have hneg := (Category.assoc (orderedFactorPoint root negative) isoNeg.hom
      (rootProduct F.pinned.roots (negative.map e))).trans
      (markedRootProduct_evaluation (R := R) F z MvPolynomial.X negative)
    have hpos := (Category.assoc (orderedFactorPoint root positive) isoPos.hom
      (rootProduct F.pinned.roots (positive.map e))).trans
      (markedRootProduct_evaluation (R := R) F z MvPolynomial.X positive)
    have ht := Category.assoc (affineMap t) τ.hom.hom.hom F.pinned.pair.T.inclusion.hom.hom
    let mul (x y : affineObject (k := RationalField.{u}) R ⟶ F.pinned.pair.G.val.X) := x * y
    exact congrArg₂ mul (congrArg₂ mul hneg ht) hpos

end MarkedCell

section MarkedTorus

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (Realization)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue)
open Specs.CharacterDescent (Character StandardLattice)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap IntegerCharacters integerGenerator)

variable {k : Type u} [Field k] {D : BasedRootDatum.{u}} {A : Specs.RootGroups.AdditiveLine k}
  (F : Realization D A)

/-- The label equivalence on the full marked character lattice. -/
private def markedCharacters : Multiplicative D.X ≃* Character F.pinned.pair.T.group where
  toFun a := Additive.toMul (F.datumIso.val.weightEquiv a.toAdd)
  invFun a := Multiplicative.ofAdd (F.datumIso.val.weightEquiv.symm (Additive.ofMul a))
  left_inv a := F.datumIso.val.weightEquiv.symm_apply_apply a.toAdd
  right_inv a := F.datumIso.val.weightEquiv.apply_symm_apply (Additive.ofMul a)
  map_mul' a b := F.datumIso.val.weightEquiv.map_add a.toAdd b.toAdd

set_option backward.isDefEq.respectTransparency false in
private theorem characterValue_iso {S T : Specs.GroupScheme k} (i : S ≅ T)
    (χ : Character S) (R : TestAlgebra k) (t : GroupPoints S R) :
    characterValue (i.inv ≫ χ) R (t ≫ i.hom.hom.hom) = characterValue χ R t := by
  have h : i.hom.hom.hom ≫ i.inv.hom.hom = 𝟙 S.X :=
    (Grp.forget _).congr_map i.hom_inv_id
  have hc : (t ≫ i.hom.hom.hom) ≫ (i.inv ≫ χ).hom.hom = t ≫ χ.hom.hom := by
    change (t ≫ i.hom.hom.hom) ≫ i.inv.hom.hom ≫ χ.hom.hom = _
    calc
      _ = t ≫ i.hom.hom.hom ≫ i.inv.hom.hom ≫ χ.hom.hom :=
        Category.assoc t i.hom.hom.hom _
      _ = t ≫ (i.hom.hom.hom ≫ i.inv.hom.hom) ≫ χ.hom.hom :=
        congrArg (t ≫ ·) (Category.assoc i.hom.hom.hom i.inv.hom.hom χ.hom.hom).symm
      _ = _ := congrArg (t ≫ ·)
        ((congrArg (· ≫ χ.hom.hom) h).trans (Category.id_comp χ.hom.hom))
  unfold characterValue
  rw [hc]

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
/-- Identify the split torus of a realization using its full lattice marking.
Every marked character evaluates as the corresponding group-algebra monomial. -/
private theorem exists_markedTorusIso :
    ∃ τ : specGroup (groupAlgebra k (Multiplicative D.X)) ≅ F.pinned.pair.T.group,
      ∀ (R : TestAlgebra k) (t : MonoidAlgebra k (Multiplicative D.X) →ₐ[k] R) (x : D.X),
        characterValue (Additive.toMul (F.datumIso.val.weightEquiv x)) R
          (affineMap t ≫ τ.hom.hom.hom) = t (MonoidAlgebra.single (Multiplicative.ofAdd x) 1) := by
  obtain ⟨r, ⟨tSplit⟩⟩ := F.pinned.pair.split
  obtain ⟨std⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) r
  let i := std ≪≫ tSplit.symm
  let iChar : Character (specGroup (groupAlgebra k (StandardLattice.{u} r))) ≃*
      Character F.pinned.pair.T.group :=
    { toEquiv := i.homCongr (Iso.refl _)
      map_mul' x y := by
        apply Grp.hom_ext
        exact MonObj.comp_mul _ _ _ }
  obtain ⟨χ, _, hχ, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing
    (k := k) r
  let e : Multiplicative D.X ≃* StandardLattice.{u} r :=
    (markedCharacters F).trans ((χ.trans (iChar)).symm)
  let q := MonoidAlgebra.domCongrBialgEquiv k k e.symm
  let j : specGroup (groupAlgebra k (Multiplicative D.X)) ≅
      specGroup (groupAlgebra k (StandardLattice.{u} r)) :=
    (hopfSpec (CommRingCat.of k)).mapIso (CommHopfAlgCat.isoMk q).op
  refine ⟨j ≪≫ i, ?_⟩
  intro R t x
  let m := e (Multiplicative.ofAdd x)
  have hm : iChar (χ m) = markedCharacters F (Multiplicative.ofAdd x) :=
    (χ.trans (iChar)).apply_symm_apply (markedCharacters F (Multiplicative.ofAdd x))
  have ht : affineMap t ≫ (j ≪≫ i).hom.hom.hom =
      affineMap (t.comp q.toAlgEquiv.toAlgHom) ≫ i.hom.hom.hom := by
    change affineMap t ≫ j.hom.hom.hom ≫ i.hom.hom.hom = _
    rw [← Category.assoc]
    change (affineMap t ≫ affineMap q.toAlgEquiv.toAlgHom) ≫ i.hom.hom.hom = _
    rw [affineMap_comp]
  change characterValue (markedCharacters F (Multiplicative.ofAdd x)) R _ = _
  rw [ht, ← hm]
  change characterValue (i.inv ≫ χ m) R
    (affineMap (t.comp q.toAlgEquiv.toAlgHom) ≫ i.hom.hom.hom) = _
  rw [characterValue_iso, hχ]
  let g := MonoidAlgebra.mapDomainBialgHom k
    ((zpowersHom _ m).comp MulEquiv.ulift.toMonoidHom)
  let a := t.comp q.toAlgEquiv.toAlgHom
  have hcomp : affineMap a ≫ (specGroupMap (CommHopfAlgCat.ofHom g)).hom.hom =
      affineMap (a.comp g.toAlgHom) := affineMap_comp _ _
  unfold characterValue
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    (affineMap a ≫ (specGroupMap (CommHopfAlgCat.ofHom g)).hom.hom)).unop.hom _ = _
  rw [hcomp]
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (a.comp g.toAlgHom)).op)).unop.hom _ = _
  rw [Functor.FullyFaithful.preimage_map]
  change t (q.toAlgEquiv (g (MonoidAlgebra.single integerGenerator 1))) = _
  rw [MonoidAlgebra.mapDomainBialgHom_single]
  change t (MonoidAlgebra.domCongr k k e.symm (MonoidAlgebra.single (m ^ (1 : ℤ)) 1)) = _
  rw [zpow_one, MonoidAlgebra.domCongr_single, e.symm_apply_apply]

end MarkedTorus

section AffineGroupCoordinates

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open Specs.GeometricRadicals (IsReductive)
open Specs.AdjointRepresentation (GroupPoints)
open private group_geometricallyIrreducible from LinearAlgebraicGroups.Reductive.CocharacterOpenCell
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria

variable {k : Type u} [Field k] (B : CommHopfAlgCat.{u} k)
  {G : GroupScheme k} (e : specGroup B ≅ G)

private def restrictGroupCoordinates {C : Type u} [CommRing C] [Algebra k C]
    (q : affineObject (k := k) C ⟶ G.X) : B →ₐ[k] C :=
  (affineHomEquiv B C).symm (q ≫ e.inv.hom.hom)

set_option backward.isDefEq.respectTransparency false in
private theorem restrictGroupCoordinates_point {C : Type u} [CommRing C] [Algebra k C]
    (q : affineObject (k := k) C ⟶ G.X) :
    affineMap (restrictGroupCoordinates B e q) ≫ e.hom.hom.hom = q := by
  have h := (affineHomEquiv (k := k) B C).apply_symm_apply (q ≫ e.inv.hom.hom)
  change affineMap (restrictGroupCoordinates B e q) = q ≫ e.inv.hom.hom at h
  have hInvHom : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 G.X :=
    (Grp.forget _).congr_map e.inv_hom_id
  rw [h, Category.assoc, hInvHom, Category.comp_id]

private def representationOnHopfPoints {n : ℕ}
    (ρ : (groupPointsFunctor k).obj G ⟶
      Specs.StandardGroups.generalLinearPoints k (ULift.{u} (Fin n))) :
    convolutionPoints B ⟶ Specs.StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)) :=
  (hopfSpecPointIso B).hom ≫ (groupPointsFunctor k).map e.hom ≫ ρ

private theorem representationOnHopfPoints_apply {n : ℕ}
    (ρ : (groupPointsFunctor k).obj G ⟶
      Specs.StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
    (R : TestAlgebra k) (f : B →ₐ[k] R) :
    (representationOnHopfPoints B e ρ).app R (WithConv.toConv f) =
      ρ.app R (affineMap f ≫ e.hom.hom.hom) := rfl

set_option maxHeartbeats 850000 in
set_option backward.isDefEq.respectTransparency false in
private theorem restrictGroupCoordinates_dense {P : AffineAlgebraicGroup k} (hP : IsReductive P)
    (e : specGroup B ≅ P.val) {C : Type u} [CommRing C] [Algebra k C] [Nontrivial C]
    (q : affineObject (k := k) C ⟶ P.val.X) (hq : IsOpenImmersion q.left) :
    _root_.IsReduced B ∧ DenseRange (PrimeSpectrum.comap (restrictGroupCoordinates B e q).toRingHom) := by
  let f := (Grp.forget _).mapIso e
  have hcon : GeometricallyConnected P.val.X.hom := hP.2.1
  have hconn : ConnectedSpace P.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton P.val.X.hom
  have hgeom := group_geometricallyIrreducible P
  have hirr : IrreducibleSpace P.val.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton P.val.X.hom
  have hsm : Smooth P.val.X.hom := hP.1
  have hr : AlgebraicGeometry.IsReduced P.val.X.left :=
    isReduced_of_smooth_over_field P.val.X.hom
  have hfi : IsIso f.hom.left := (Over.forget _).map_isIso f.hom
  have hgi : IsIso f.inv.left := (Over.forget _).map_isIso f.inv
  have hr' : AlgebraicGeometry.IsReduced ((Grp.forget (SchemeOver k)).obj P.val).left := hr
  have hrB : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of B)) :=
    isReduced_of_isOpenImmersion f.hom.left
  refine ⟨(affine_isReduced_iff (CommRingCat.of B)).mp hrB, ?_⟩
  let j := restrictGroupCoordinates B e q
  have hj : (affineMap j).left = q.left ≫ f.inv.left := by
    change ((affineMap j).left) = (q ≫ f.inv).left
    exact congrArg (fun h => h.left) ((affineHomEquiv (k := k) B C).apply_symm_apply (q ≫ f.inv))
  have hCA : Nonempty (affineObject (k := k) C).left := inferInstanceAs (Nonempty (PrimeSpectrum C))
  have ho : IsOpenImmersion (affineMap j).left := by
    rw [hj]
    infer_instance
  have hiP : IrreducibleSpace ((Grp.forget (SchemeOver k)).obj P.val).left := hirr
  have hiB : IrreducibleSpace (affineObject (k := k) B).left :=
    f.inv.left.homeomorph.surjective.irreducibleSpace f.inv.left.continuous
  exact (affineMap j).left.isOpenMap.denseRange_of_isPreirreducibleSpace

end AffineGroupCoordinates

section CellIdentity

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralSemisimpleModel (Integers integerAlgebra)
open Specs.IntegralRootRelations (RootCoordinates)
open Specs.IntegralLattices (Index Positive Negative RationalHighestWeight dividedPower
  ClosedRootImage orderedMatrix)
open Specs.MatrixOpenCell (Factors)

private def cellIdentity (D : BasedRootDatum.{u}) :
    letI : Algebra Integers.{u} (IntegralCellCoordinates D) := integerAlgebra _
    IntegralCellCoordinates D →ₐ[Integers.{u}] Integers.{u} := by
  let : Algebra Integers.{u} (IntegralCellCoordinates D) := integerAlgebra _
  exact overLiftedIntegers <| MvPolynomial.eval₂Hom
    ((Int.castRingHom Integers.{u}).comp
      (Bialgebra.counitAlgHom ℤ (AddMonoidAlgebra ℤ D.X)).toRingHom) (fun _ => 0)

variable {D : BasedRootDatum.{u}} {A : Specs.RootGroups.AdditiveLine RationalField.{u}}
  {Q : Realization D A} {z : RootCoordinates Q}
  [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
  {ω : Module.Basis D.base.support ℤ D.X} {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
private theorem integralRootMatrix_zero
    (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
    (b : Module.Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
    (a : D.I) (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hcoeff : ∀ (j : Index.{u} n) (i : D.base.support),
      ∑ l : Index.{u} n, ((p l j).coeff 0 : RationalField.{u}) • b l i =
        (dividedPower ((V i).rootOperator a) 0).mulVec (b j i)) :
    integralPolynomialMatrix p (0 : Integers.{u}) = 1 := by
  classical
  apply integralPolynomialMatrix_zero_of_generic p
  apply Matrix.ext
  intro i j
  have hb : (∑ l : Index.{u} n, ((p l j).coeff 0 : RationalField.{u}) • b l) = b j := by
    funext t
    simpa only [Finset.sum_apply, Pi.smul_apply, dividedPower, Nat.factorial_zero,
      Nat.cast_one, inv_one, pow_zero, one_smul, Matrix.one_mulVec] using hcoeff j t
  have he := congrArg (b.coord i) hb
  simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at he
  change (p i j).eval₂ (Int.castRingHom RationalField.{u}) 0 = _
  rw [Polynomial.eval₂_at_zero]
  simpa only [Int.coe_castRingHom, Matrix.one_apply, eq_comm] using he

private theorem cellIdentity_X (D : BasedRootDatum.{u}) (a : D.I) :
    cellIdentity D (MvPolynomial.X a) = 0 := by
  exact MvPolynomial.eval₂Hom_X' _ _ _

private theorem cellIdentity_monomial (D : BasedRootDatum.{u}) (x : D.X) :
    cellIdentity D (MvPolynomial.C (AddMonoidAlgebra.single x 1)) = (1 : Integers.{u}) := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C _) = _
  rw [MvPolynomial.eval₂Hom_C]
  change ((Int.castRingHom Integers.{u}) (Coalgebra.counit (R := ℤ)
    (AddMonoidAlgebra.single x (1 : ℤ)))) = _
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem cellIdentity_factors {n : ℕ} {D : BasedRootDatum.{u}}
    (negative : List (Negative D)) (positive : List (Positive D))
    (w : Index.{u} n → D.X) (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hneg : IsOrderedRootChart false (orderedMatrix negative (fun a => p a.val)))
    (hpos : IsOrderedRootChart true (orderedMatrix positive (fun a => p a.val)))
    (hp0 : ∀ a, integralPolynomialMatrix (p a) (0 : Integers.{u}) = 1) :
    letI : Algebra Integers.{u} (IntegralCellCoordinates D) := integerAlgebra _
    (cellIdentity D).toRingHom.mapMatrix (cellFactors negative positive w p hneg hpos).product =
      (1 : Matrix (Fin n) (Fin n) Integers.{u}) := by
  let : Algebra Integers.{u} (IntegralCellCoordinates D) := integerAlgebra _
  let f := (cellIdentity D).toRingHom
  let F := cellFactors negative positive w p hneg hpos
  let reindex := Matrix.reindexRingEquiv Integers.{u} (Equiv.ulift : Index.{u} n ≃ Fin n)
  have evalOrder {σ : Type u} (l : List σ) (a : σ → D.I) :
      reindex ((f.comp (parameterSubstitution a)).mapMatrix (orderedMatrix l (p ∘ a))) = 1 := by
    have hx (b : σ) : (f.comp (parameterSubstitution a)) (MvPolynomial.X b) = 0 := by
      simp only [RingHom.comp_apply, parameterSubstitution, MvPolynomial.eval₂Hom_X',
        Function.comp_apply]
      exact cellIdentity_X D (a b)
    rw [orderedMatrix_evaluation]
    simp only [hx, Function.comp_apply, hp0, List.prod_map_one, map_one]
  have hl : f.mapMatrix F.lower = 1 :=
    evalOrder negative Subtype.val
  have hu : f.mapMatrix F.upper = 1 :=
    evalOrder positive Subtype.val
  have hd : f.mapMatrix (Matrix.diagonal fun j => (F.diagonal j : IntegralCellCoordinates D)) = 1 := by
    change (Matrix.diagonal (fun j : Fin n => MvPolynomial.C
      (AddMonoidAlgebra.single (w (ULift.up j)) 1))).map f = _
    rw [Matrix.diagonal_map (map_zero f), ← Matrix.diagonal_one]
    congr 1
    funext j
    exact cellIdentity_monomial D (w (ULift.up j))
  change f.mapMatrix F.product = _
  rw [Factors.product, map_mul, map_mul, hl, hd, hu, mul_one, mul_one]

end CellIdentity

section PointedClosureChart

open Specs.MatrixOpenCell (CellCoordinates minorProduct)

attribute [local instance] matrixCoordinateHopfAlgebra

variable {R K : Type u} [CommRing R] [IsDomain R] [IsBezout R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  (B : CommHopfAlgCat.{u} K) [Algebra R B] [IsScalarTower R K B] {n : ℕ}
  (ρ : convolutionPoints B ⟶ Specs.StandardGroups.generalLinearPoints K (ULift.{u} (Fin n)))

set_option maxHeartbeats 850000 in
set_option backward.isDefEq.respectTransparency false in
/-- The principal chart contains the identity when evaluation of its
matrix entries at the given section gives the identity matrix. -/
theorem matrixClosure_pointedChart {C : Type u} [CommRing C] [Algebra R C]
    (φ : CellCoordinates R n →ₐ[R] C) (hφ : Function.Surjective φ)
    (hker : RingHom.ker (rationalMatrixCoordinates (R := R) B ρ) =
      RingHom.ker (φ.comp (IsScalarTower.toAlgHom R (MatrixGroupCoordinates R n) (CellCoordinates R n))))
    (s : C →ₐ[R] R)
    (hId : (s.comp (φ.comp (IsScalarTower.toAlgHom R (MatrixGroupCoordinates R n)
      (CellCoordinates R n)))).mapMatrix (universalGLMatrix R n) = 1) :
    ∃ i : Spec (CommRingCat.of C) ⟶ (matrixClosure (R := R) B ρ).X.left,
      IsOpenImmersion i ∧
        i ≫ (matrixClosure (R := R) B ρ).X.hom =
          Spec.map (CommRingCat.ofHom (algebraMap R C)) ∧
        Spec.map (CommRingCat.ofHom s.toRingHom) ≫ i = η[(matrixClosure (R := R) B ρ).X].left := by
  let E := MatrixGroupCoordinates R n
  let f := rationalMatrixCoordinates (R := R) B ρ
  let g := φ.comp (IsScalarTower.toAlgHom R E (CellCoordinates R n))
  let I := RingHom.ker f
  let H := E ⧸ I
  let : I.IsHopfIdeal R := matrixClosure_isHopfIdeal (R := R) B ρ
  let j := chartRestriction f g hker
  let : Algebra H C := j.toRingHom.toAlgebra
  let i := Spec.map (CommRingCat.ofHom j.toRingHom)
  have hloc : IsLocalization.Away (Ideal.Quotient.mk I (minorProduct R n)) C :=
    isLocalization_chartRestriction f g hker (minorProduct R n) φ.toRingHom hφ (fun _ => rfl)
  refine ⟨i, IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk I (minorProduct R n)), ?_, ?_⟩
  · change i ≫ Spec.map (CommRingCat.ofHom (algebraMap R H)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext r
    exact j.commutes r
  · have hε : s.comp g = Bialgebra.counitAlgHom R E :=
      glAlgHom_ext (hId.trans (matrix_counit R n).symm)
    have hco : s.comp j = Bialgebra.counitAlgHom R H := by
      apply AlgHom.ext
      intro a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact DFunLike.congr_fun hε b
    have hh : η[(matrixClosure (R := R) B ρ).X].left =
        Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom R H).toRingHom) := rfl
    rw [hh, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f : H →ₐ[R] R => Spec.map (CommRingCat.ofHom f.toRingHom)) hco

end PointedClosureChart

section ClosureComparison

open WithConv
open _root_.LinearAlgebraicGroups.Specs (IdentityLieStructure)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralSemisimpleModel (Integers integerAlgebra)
open Specs.IntegralRootRelations (RootCoordinates)
open Specs.IntegralLattices (Index Positive Negative RationalHighestWeight dividedPower
  TorusCoordinatesGenerate ClosedRootImage orderedMatrix)
open Specs.OrderedRootProducts (Enumerates RegularRootCell)
open Specs.CharacterPairing (characterValue)
open Specs.DiagonalizableGroups (groupAlgebra)
open Specs.MatrixOpenCell (CellCoordinates glMatrix cellMatrix Factors)

private theorem enumerates_subtype_values {I : Type u} {S : Set I} {l : List S}
    (h : Enumerates l Set.univ) : Enumerates (l.map Subtype.val) S := by
  refine ⟨h.1.map Subtype.val_injective, ?_⟩
  intro i
  constructor
  · rintro hi
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hi
    exact hj ▸ j.property
  · intro hi
    exact List.mem_map.mpr ⟨⟨i, hi⟩, (h.2 _).mpr (Set.mem_univ _), rfl⟩

variable {D : BasedRootDatum.{u}} {A : Specs.RootGroups.AdditiveLine RationalField.{u}}
  {Q : Realization D A} {z : RootCoordinates Q}
  [DecidableEq D.base.support]
  [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
  {ω : Module.Basis D.base.support ℤ D.X}
  {n : ℕ}
  (V : ∀ i : D.base.support, RationalHighestWeight z e h (ω i))
  (b : Module.Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))

set_option maxHeartbeats 1250000 in
set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- Restrict the generic matrix representation to the marked rational big cell.
The integral matrix chart and the generic representation then have the same
equations in the full matrix coordinates. -/
private theorem matrixClosure_matches_integralCell
    (cellTheorem : RegularRootCell.{u})
    (negative : List (Negative D)) (positive : List (Positive D))
    (hnl : Enumerates negative Set.univ) (hpl : Enumerates positive Set.univ)
    (w : Index.{u} n → D.X)
    (weight : ∀ j i, b j i ∈ (V i).weightSpace (w j))
    (height : D.X →ₗ[ℤ] ℤ) (hp : ∀ a : Positive D, 0 < height (D.datum.root a))
    (hn : ∀ a : Negative D, height (D.datum.root a) < 0)
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hcoeff : ∀ (a : D.I) (m : ℕ) (j : Index.{u} n) (i : D.base.support),
      ∑ l : Index.{u} n, ((p a l j).coeff m : RationalField.{u}) • b l i =
        (dividedPower ((V i).rootOperator a) m).mulVec (b j i))
    (hw : TorusCoordinatesGenerate w)
    (hneg : IsOrderedRootChart false (orderedMatrix negative (fun a => p a.val)))
    (hpos : IsOrderedRootChart true (orderedMatrix positive (fun a => p a.val)))
    (B : CommHopfAlgCat.{u} RationalField.{u}) (ε : specGroup B ≅ Q.pinned.pair.G.val)
    (τ : specGroup (groupAlgebra RationalField.{u} (Multiplicative D.X)) ≅ Q.pinned.pair.T.group)
    (hτ : ∀ (R : TestAlgebra RationalField.{u})
        (t : MonoidAlgebra RationalField.{u} (Multiplicative D.X) →ₐ[RationalField.{u}] R) (x : D.X),
        characterValue (Additive.toMul (Q.datumIso.val.weightEquiv x)) R
          (affineMap t ≫ τ.hom.hom.hom) = t (MonoidAlgebra.single (Multiplicative.ofAdd x) 1)) :
    letI : Algebra Integers.{u} B := integerAlgebra B
    letI : Algebra Integers.{u} (IntegralCellCoordinates D) := integerAlgebra _
    let ρ := representationOnHopfPoints B ε (rationalMatrixAction V b)
    ∃ φ : CellCoordinates Integers.{u} n →ₐ[Integers.{u}] IntegralCellCoordinates D,
      Function.Surjective φ ∧
      (RingHom.ker (rationalMatrixCoordinates (R := Integers.{u}) B ρ) =
      RingHom.ker (φ.comp (IsScalarTower.toAlgHom Integers.{u}
        (MatrixGroupCoordinates Integers.{u} n) (CellCoordinates Integers.{u} n)))) ∧
      ((cellIdentity D).comp (φ.comp (IsScalarTower.toAlgHom Integers.{u}
        (MatrixGroupCoordinates Integers.{u} n) (CellCoordinates Integers.{u} n)))).mapMatrix
        (universalGLMatrix Integers.{u} n) = 1 ∧
      φ.toRingHom.mapMatrix (cellMatrix Integers.{u} n) =
        (cellFactors negative positive w p hneg hpos).product := by
  classical
  let T := MarkedCellCoordinates D
  let C := IntegralCellCoordinates D
  let R := CommAlgCat.of RationalField.{u} T
  letI : Algebra Integers.{u} RationalField.{u} := integerAlgebra _
  letI : Algebra Integers.{u} B := integerAlgebra B
  letI : Algebra Integers.{u} C := integerAlgebra _
  letI : Algebra Integers.{u} T := integerAlgebra _
  letI := integers_scalarTower B
  letI := integers_scalarTower T
  let ρ₀ := rationalMatrixAction V b
  let ρ := representationOnHopfPoints B ε ρ₀
  let l := negative.map Subtype.val
  let r := positive.map Subtype.val
  obtain ⟨q, hqOpen, hq⟩ := exists_markedRootCell Q cellTheorem z τ height hp hn l r
    (enumerates_subtype_values hnl) (enumerates_subtype_values hpl)
  let t := IsScalarTower.toAlgHom RationalField.{u}
    (MonoidAlgebra RationalField.{u} (Multiplicative D.X)) T
  let j := restrictGroupCoordinates B ε q
  obtain ⟨hreduced, hdense⟩ := restrictGroupCoordinates_dense B Q.pinned.pair.reductive ε q hqOpen
  obtain ⟨φ₀, hφ, hφmatrix⟩ := integralCell_surjective negative positive w p hw hneg hpos
  let φ : CellCoordinates Integers.{u} n →ₐ[Integers.{u}] C := overLiftedIntegers φ₀
  refine ⟨φ, hφ, ?_, ?_, hφmatrix⟩
  · apply matrixClosure_ker_eq_of_dense_chart B ρ φ (j.restrictScalars Integers.{u})
      (cellScalars D RationalField.{u}) hdense (cellScalars_injective D RationalField.{u} rationalField_intCast_injective)
    have hmatrix := congrArg Units.val (representation_evaluation B ρ j)
    rw [representationOnHopfPoints_apply, restrictGroupCoordinates_point] at hmatrix
    have hgeneric : (rationalMatrixCoordinates (R := Integers.{u}) B ρ).mapMatrix
        (universalGLMatrix Integers.{u} n) = (matrixAtUniversalPoint B ρ).val :=
      evalGL_universal _
    let ρval := (Units.coeHom (Matrix (Index.{u} n) (Index.{u} n) R)).comp (ρ₀.app R).hom
    have hroot (a : D.I) :
        ρval (Specs.IntegralRootRelations.root Q z a R (MvPolynomial.X a)) =
        integralPolynomialMatrix (p a) (MvPolynomial.X a : R) :=
      rationalMatrixAction_root V b a (p a) (hcoeff a) R _
    let tPoint : Specs.AdjointRepresentation.GroupPoints Q.pinned.pair.G.val R :=
      affineMap t ≫ τ.hom.hom.hom ≫ Q.pinned.pair.T.inclusion.hom.hom
    have htorus : ρval tPoint =
        Matrix.diagonal (fun j => MvPolynomial.C (MonoidAlgebra.single (Multiplicative.ofAdd (w j)) 1)) := by
      change ((ρ₀.app R (affineMap t ≫ τ.hom.hom.hom ≫ Q.pinned.pair.T.inclusion.hom.hom)) :
        Matrix.GeneralLinearGroup (Index.{u} n) R).val = _
      rw [← Category.assoc, rationalMatrixAction_torus V b w weight]
      congr 1
      funext a
      exact hτ R t (w a)
    have hprod (s : List D.I) :
        ρval (s.map (fun a => Specs.IntegralRootRelations.root Q z a R (MvPolynomial.X a))).prod =
          (s.map (fun a => integralPolynomialMatrix (p a) (MvPolynomial.X a : R))).prod := by
      rw [map_list_prod, List.map_map]
      congr 1
      apply List.map_congr_left
      exact fun a _ => hroot a
    have heval : ρval q =
        (l.map (fun a => integralPolynomialMatrix (p a) (MvPolynomial.X a : R))).prod *
          Matrix.diagonal (fun j => MvPolynomial.C (MonoidAlgebra.single (Multiplicative.ofAdd (w j)) 1)) *
        (r.map (fun a => integralPolynomialMatrix (p a) (MvPolynomial.X a : R))).prod := by
      rw [hq]
      change ρval
        ((l.map (fun a => Specs.IntegralRootRelations.root Q z a R (MvPolynomial.X a))).prod *
          tPoint *
          (r.map (fun a => Specs.IntegralRootRelations.root Q z a R (MvPolynomial.X a))).prod) = _
      rw [map_mul, map_mul, htorus, hprod, hprod]
    have hφscalars := congrArg ((cellScalars D RationalField.{u}).toRingHom.mapMatrix) hφmatrix
    rw [cellScalars_factors D RationalField.{u}] at hφscalars
    let reindex := Matrix.reindexRingEquiv T (Equiv.ulift : Index.{u} n ≃ Fin n)
    intro a c
    change j ((rationalMatrixCoordinates (R := Integers.{u}) B ρ) (glMatrix Integers.{u} n a c)) =
      cellScalars D RationalField.{u} (φ₀ (cellMatrix Integers.{u} n a c))
    calc
      _ = reindex (ρval q) a c := by
        have hg := congrArg (fun M : Matrix (Index.{u} n) (Index.{u} n) B =>
          j (M (ULift.up a) (ULift.up c))) hgeneric
        have hm := congrArg (fun M : Matrix (Index.{u} n) (Index.{u} n) R =>
          M (ULift.up a) (ULift.up c)) hmatrix
        exact hg.trans hm.symm
      _ = _ := by
        have hv := congrArg (fun M : Matrix (Index.{u} n) (Index.{u} n) R => reindex M a c) heval
        have hc := congrArg (fun M : Matrix (Fin n) (Fin n) T => M a c) hφscalars
        simp only [l, r, List.map_map] at hv
        exact hv.trans hc.symm
  · have hzero (a : D.I) : integralPolynomialMatrix (p a) (0 : Integers.{u}) = 1 :=
      integralRootMatrix_zero V b a (p a) (hcoeff a 0)
    have hId := (congrArg (cellIdentity D).toRingHom.mapMatrix hφmatrix).trans
      (cellIdentity_factors negative positive w p hneg hpos hzero)
    apply Matrix.ext
    rintro ⟨i⟩ ⟨j⟩
    let a := (cellIdentity D) (φ₀ (cellMatrix Integers.{u} n i j))
    change a = (1 : Matrix (Index.{u} n) (Index.{u} n) Integers.{u}) (ULift.up i) (ULift.up j)
    have ha : a = (1 : Matrix (Fin n) (Fin n) Integers.{u}) i j :=
      congrFun (congrFun hId i) j
    simpa only [Matrix.one_apply, ULift.up_inj] using ha

end ClosureComparison

section SmoothIntegralClosure

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField)
open Specs.IntegralSemisimpleModel (Integers IntegralGroup integerAlgebra)
open Specs.IntegralLattices (Index Positive Negative)
open Specs.OrderedRootProducts (Enumerates RegularRootCell)
open Specs.MatrixOpenCell (CellCoordinates)


set_option maxHeartbeats 900000 in
set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
private theorem integralMatrixClosure_smoothChart (D : BasedRootDatum.{u})
    (B : CommHopfAlgCat.{u} RationalField.{u}) {n : ℕ}
    (ρ : convolutionPoints B ⟶ Specs.StandardGroups.generalLinearPoints RationalField (Index.{u} n)) :
    letI : Algebra Integers.{u} B := integerAlgebra B
    letI : Algebra Integers.{u} (IntegralCellCoordinates D) := integerAlgebra _
    ∀ (φ : CellCoordinates Integers.{u} n →ₐ[Integers.{u}] IntegralCellCoordinates D),
    Function.Surjective φ →
    RingHom.ker (rationalMatrixCoordinates (R := Integers.{u}) B ρ) =
      RingHom.ker (φ.comp (IsScalarTower.toAlgHom Integers.{u}
        (MatrixGroupCoordinates Integers.{u} n) (CellCoordinates Integers.{u} n))) →
    ((cellIdentity D).comp (φ.comp (IsScalarTower.toAlgHom Integers.{u}
      (MatrixGroupCoordinates Integers.{u} n) (CellCoordinates Integers.{u} n)))).mapMatrix
      (universalGLMatrix Integers.{u} n) = 1 →
    let G := integralMatrixClosure B ρ
    IsAffine G.X.left ∧ LocallyOfFinitePresentation G.X.hom ∧ QuasiCompact G.X.hom ∧
      Smooth G.X.hom ∧
      ∃ i : Spec (CommRingCat.of (IntegralCellCoordinates D)) ⟶ G.X.left,
        IsOpenImmersion i ∧ i ≫ G.X.hom =
          Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} (IntegralCellCoordinates D))) ∧
        Spec.map (CommRingCat.ofHom (cellIdentity D).toRingHom) ≫ i = η[G.X].left := by
  let : IsDomain Integers.{u} :=
    (ULift.ringEquiv : Integers.{u} ≃+* ℤ).toMulEquiv.isDomain ℤ
  let : IsPrincipalIdealRing Integers.{u} := integers_isPrincipalIdealRing
  letI : Algebra Integers.{u} RationalField.{u} := integerAlgebra _
  letI : Algebra Integers.{u} B := integerAlgebra _
  letI : IsFractionRing Integers.{u} RationalField.{u} := integers_isFractionRing
  letI := integers_scalarTower B
  letI : Algebra Integers.{u} (IntegralCellCoordinates D) := integerAlgebra _
  let hs : Algebra.Smooth Integers.{u} (IntegralCellCoordinates D) := integralCell_smooth D
  intro φ hφ heq hId
  dsimp only
  let G := integralMatrixClosure B ρ
  let H := MatrixClosureCoordinates (R := Integers.{u}) B ρ
  have hcoords := matrixClosure_coordinates (R := Integers.{u}) B ρ
  have hlfp : LocallyOfFinitePresentation G.X.hom := by
    change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} H)))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.finitePresentation_algebraMap.mpr hcoords.2
  have ha : IsAffine G.X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of H)))
  have hqc : QuasiCompact G.X.hom := inferInstanceAs
    (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} H))))
  have hsmooth : Smooth G.X.hom :=
    matrixClosure_smooth_of_chart (R := Integers.{u}) B ρ φ hφ heq (cellIdentity D)
  exact ⟨ha, hlfp, hqc, hsmooth, matrixClosure_pointedChart (R := Integers.{u}) B ρ φ hφ heq (cellIdentity D) hId⟩

end SmoothIntegralClosure

section IntegralAdditiveLine

open Specs.IntegralSemisimpleModel (AdditiveLine IntegralAlgebra Integers integralSpec
  additiveScheme additivePoint)

private def additiveTestPoints (k : Type u) [CommRing k] : CommAlgCat.{u} k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (Multiplicative R)
  map f := GrpCat.ofHom f.hom.toRingHom.toAddMonoidHom.toMultiplicative
  map_id _ := by apply GrpCat.ext; intro r; rfl
  map_comp _ _ := by apply GrpCat.ext; intro r; rfl

private abbrev polynomialObject (k : Type u) [CommRing k] :=
  op (CommAlgCat.of k (Polynomial k))

private def polynomialPointRepresentation (k : Type u) [CommRing k] :
    ((unopUnop (CommAlgCat.{u} k) ⋙ additiveTestPoints k) ⋙ forget _).RepresentableBy
      (polynomialObject k) where
  homEquiv {X} :=
    { toFun f := Multiplicative.ofAdd (f.unop.hom Polynomial.X)
      invFun r := by
        let t : Multiplicative X.unop := r
        exact (CommAlgCat.ofHom (Polynomial.aeval t.toAdd : Polynomial k →ₐ[k] X.unop)).op
      left_inv f := by
        apply Quiver.Hom.unop_inj
        apply CommAlgCat.hom_ext
        apply Polynomial.algHom_ext
        exact Polynomial.aeval_X _
      right_inv r := by
        let t : Multiplicative X.unop := r
        exact congrArg Multiplicative.ofAdd (Polynomial.aeval_X (R := k) t.toAdd) }
  homEquiv_comp f g := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The relative additive group with its polynomial coordinate over the integers. -/
def integralAdditiveLine : AdditiveLine.{u} := by
  let k := Integers.{u}
  let X := polynomialObject k
  let F := unopUnop (CommAlgCat.{u} k) ⋙ additiveTestPoints k
  let P := polynomialPointRepresentation k
  letI : GrpObj X := GrpObj.ofRepresentableBy X F P
  let G : Grp (CommAlgCat.{u} k)ᵒᵖ := ⟨X⟩
  let e := yonedaGrpObjIsoOfRepresentableBy X F P
  let S := algSpec (CommRingCat.of k)
  letI : S.Braided := AlgebraicGeometry.braidedAlgSpec
  refine ⟨(S.mapGrp.obj G).grp, ?_⟩
  intro R a b
  let p (c : R) : op R ⟶ X := (CommAlgCat.ofHom (Polynomial.aeval c)).op
  have hp (c : R) : P.homEquiv (p c) = Multiplicative.ofAdd c := Polynomial.aeval_X c
  have h : p a * p b = p (a + b) := by
    apply P.homEquiv.injective
    have hm := (e.hom.app (op (op R))).hom.map_mul (p a) (p b)
    change P.homEquiv (p a * p b) = P.homEquiv (p a) * P.homEquiv (p b) at hm
    rw [hm, hp, hp, hp]
    rfl
  exact (S.map_mul (p a) (p b)).symm.trans (congrArg S.map h)

end IntegralAdditiveLine

section AffineComponentRestriction

private theorem isClopen_of_discrete_fibres {X S : Type*} [TopologicalSpace X]
    [TopologicalSpace S] [DiscreteTopology S] (f : X → S) (hf : Continuous f) (U : Set X)
    (h : ∀ s : S, IsClopen ((Subtype.val : (f ⁻¹' {s}) → X) ⁻¹' U)) : IsClopen U := by
  have hOpen (V : Set X) (hV : ∀ s : S, IsOpen ((Subtype.val : (f ⁻¹' {s}) → X) ⁻¹' V)) :
      IsOpen V := by
    refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
    let s := f x
    let T : Set X := f ⁻¹' {s}
    let p : T → X := Subtype.val
    refine ⟨p '' (p ⁻¹' V), Set.image_preimage_subset _ _, ?_, ?_⟩
    · exact ((isOpen_discrete {s}).preimage hf).isOpenMap_subtype_val _ (hV s)
    · exact ⟨⟨x, rfl⟩, hx, rfl⟩
  refine ⟨?_, hOpen U fun s => (h s).2⟩
  exact isOpen_compl_iff.mp (hOpen Uᶜ fun s => (h s).1.isOpen_compl : IsOpen Uᶜ)

variable {A : Type u} [CommRing A]

private abbrev intScalar (n : ℤ) : A := algebraMap ℤ A n

/-- The change of base of the ring modulo an integer to the affine ring
modulo the same integer. -/
def integerFibreMap (n : ℤ) :
    (ℤ ⧸ Ideal.span {n}) →+* (A ⧸ Ideal.span {intScalar (A := A) n}) := by
  let I : Ideal ℤ := Ideal.span {n}
  let J : Ideal A := Ideal.span {intScalar (A := A) n}
  let f : ℤ →+* A ⧸ J := (Ideal.Quotient.mk J).comp (algebraMap ℤ A)
  have h : I ≤ RingHom.ker f := by
    refine Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
    change Ideal.Quotient.mk J (intScalar (A := A) n) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  exact Ideal.Quotient.lift I f h

set_option linter.style.haveILetI false in
/-- An open containing the complement of a principal integer fibre and
retaining clopen parts of the closed fibres has an affine presentation. -/
theorem exists_affine_open_over_integer_fibres (n : ℤ) (hn : n ≠ 0)
    (hx : intScalar (A := A) n ∈ nonZeroDivisors A) (U : Set (PrimeSpectrum A))
    (hU : (PrimeSpectrum.basicOpen (intScalar (A := A) n) : Set _) ⊆ U)
    (h : let f := PrimeSpectrum.comap (integerFibreMap (A := A) n)
      let π := PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {intScalar (A := A) n}))
      ∀ s : PrimeSpectrum (ℤ ⧸ Ideal.span {n}),
        IsClopen ((Subtype.val : (f ⁻¹' {s}) → _) ⁻¹' (π ⁻¹' U))) :
    ∃ e : A,
      let i := Spec.map (CommRingCat.ofHom (algebraMap A (componentRestriction (intScalar n) e)))
      IsOpenImmersion i ∧ Set.range i = U := by
  let x : A := intScalar n
  let I : Ideal A := Ideal.span {x}
  let π := PrimeSpectrum.comap (Ideal.Quotient.mk I)
  let f := PrimeSpectrum.comap (integerFibreMap (A := A) n)
  letI : NeZero n := ⟨hn⟩
  letI : IsArtinianRing (ℤ ⧸ Ideal.span {n}) := isArtinian_of_finite
  letI : DiscreteTopology (PrimeSpectrum (ℤ ⧸ Ideal.span {n})) := inferInstance
  have hc : IsClopen (π ⁻¹' U) := isClopen_of_discrete_fibres f
    (PrimeSpectrum.continuous_comap _) _ h
  obtain ⟨e, ho, hr⟩ := exists_affine_open_of_clopen_fibre x hx (π ⁻¹' U) hc
  refine ⟨e, ho, hr.trans ?_⟩
  apply Set.Subset.antisymm
  · exact Set.union_subset hU (Set.image_preimage_subset _ _)
  · intro P hP
    by_cases hxP : x ∈ P.asIdeal
    · have hP' : P ∈ Set.range π := by
        change P ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I))
        rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
          PrimeSpectrum.mem_zeroLocus]
        exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxP)
      obtain ⟨Q, rfl⟩ := hP'
      exact Or.inr ⟨Q, hP, rfl⟩
    · exact Or.inl hxP

end AffineComponentRestriction

section GenericFibre

open CategoryTheory.Limits

private theorem connected_spectrum_of_injective {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) [ConnectedSpace (PrimeSpectrum B)] :
    ConnectedSpace (PrimeSpectrum A) := by
  have hd : DenseRange (PrimeSpectrum.comap f) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mpr
      ((RingHom.injective_iff_ker_eq_bot f).mp hf ▸ bot_le)
  let : PreconnectedSpace (PrimeSpectrum A) := hd.preconnectedSpace (PrimeSpectrum.continuous_comap f)
  exact ⟨(inferInstance : Nonempty (PrimeSpectrum B)).map (PrimeSpectrum.comap f)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem geometricallyConnected_spec_of_injective
    {k A B : Type u} [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (hf : Function.Injective f)
    (hB : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k B)))) :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun X : Scheme.{u} => ConnectedSpace X)).mpr
  intro K _ _
  let kToK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let kToA := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let kToB := Spec.map (CommRingCat.ofHom (algebraMap k B))
  let eB := pullbackSymmetry kToB kToK ≪≫ pullbackSpecIso k K B
  let eA := pullbackSymmetry kToA kToK ≪≫ pullbackSpecIso k K A
  have hcB : ConnectedSpace (pullback kToB kToK : Scheme) :=
    hB.geometrically_connectedSpace kToK (pullback.fst _ _) (pullback.snd _ _)
      (IsPullback.of_hasPullback kToB kToK)
  have hB' : ConnectedSpace (PrimeSpectrum (K ⊗[k] B)) :=
    eB.hom.homeomorph.connectedSpace_iff.mp hcB
  let F := Algebra.TensorProduct.map (AlgHom.id k K) f
  have hF : Function.Injective F := Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap hf
  have hA' := connected_spectrum_of_injective F.toRingHom hF
  exact eA.hom.homeomorph.connectedSpace_iff.mpr hA'

section FractionField
variable {R K A B : Type u} [CommRing R] [Field K]
  [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra R K]
  [Algebra K B] [IsScalarTower R K B] [IsFractionRing R K]

set_option backward.isDefEq.respectTransparency false in
private theorem fractionField_extension_injective (f : A →ₐ[R] B) (hf : Function.Injective f) :
    Function.Injective (AlgHom.liftEquiv R K A B f) := by
  let fK := AlgHom.liftEquiv R K A B f
  let : Algebra A (K ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization ((nonZeroDivisors R).map (algebraMap R A)) (K ⊗[R] A) :=
    IsLocalization.tensorRight (S := A) K (nonZeroDivisors R)
  have h (a : A) : fK (algebraMap A (K ⊗[R] A) a) = f a := by
    change AlgHom.liftEquiv R K A B f ((1 : K) ⊗ₜ[R] a) = f a
    rw [AlgHom.liftEquiv_tmul, one_smul]
  apply (IsLocalization.injective_iff_map_algebraMap_eq ((nonZeroDivisors R).map (algebraMap R A))
    fK.toRingHom).mpr
  intro a b
  constructor
  · exact fun e => congrArg fK e
  · intro e
    change fK (algebraMap A (K ⊗[R] A) a) = fK (algebraMap A (K ⊗[R] A) b) at e
    exact congrArg (algebraMap A (K ⊗[R] A)) (hf ((h a).symm.trans (e.trans (h b))))

end FractionField

set_option backward.isDefEq.respectTransparency false in
/-- The generic fibre of the matrix closure inherits geometric connectedness
from the affine rational group through the injective coordinate restriction. -/
theorem matrixClosure_genericCoordinates_connected
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (B : CommHopfAlgCat.{u} K) [Algebra R B] [IsScalarTower R K B] {n : ℕ}
    (ρ : convolutionPoints B ⟶ Specs.StandardGroups.generalLinearPoints K (ULift.{u} (Fin n)))
    (hB : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap K B)))) :
    let C := MatrixClosureCoordinates (R := R) B ρ
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (R := K) (S := K ⊗[R] C)
      (algebraMap K (K ⊗[R] C)))) := by
  let f := rationalMatrixCoordinates (R := R) B ρ
  let j := Ideal.kerLiftAlg f
  let jK := AlgHom.liftEquiv R K (MatrixClosureCoordinates (R := R) B ρ) B j
  have hjK : Function.Injective jK := fractionField_extension_injective j (Ideal.kerLiftAlg_injective f)
  exact geometricallyConnected_spec_of_injective jK hjK hB

end GenericFibre

section OpenCellProduct

open CategoryTheory.Limits
open private tensorHom_property from LinearAlgebraicGroups.Affine.Components

variable {S : Scheme.{u}} (H : Grp (Over S))

private def multiplicationShear : H.X ⊗ H.X ≅ H.X ⊗ H.X := by
  let a := fst H.X H.X
  let b := snd H.X H.X
  refine ⟨lift a (a * b), lift a (a⁻¹ * b), ?_, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext
    · simp [a]
    · simp only [Category.assoc, lift_snd, lift_fst, Category.id_comp,
        MonObj.comp_mul, GrpObj.comp_inv, a, b, inv_mul_cancel_left]
  · apply CartesianMonoidalCategory.hom_ext
    · simp [a]
    · simp only [Category.assoc, lift_snd, lift_fst, Category.id_comp,
        MonObj.comp_mul, a, b, mul_inv_cancel_left]

/-- Relative group multiplication is smooth when the structural morphism
is smooth. Translation identifies it with a product projection. -/
theorem groupMultiplication_smooth [Smooth H.X.hom] : Smooth (μ[H.X]).left := by
  let e := multiplicationShear H
  have hs : Smooth (snd H.X H.X).left := by
    rw [Over.snd_left]
    infer_instance
  have he : e.hom ≫ snd H.X H.X = μ[H.X] := by
    change lift (fst H.X H.X) (fst H.X H.X * snd H.X H.X) ≫ snd H.X H.X = _
    rw [lift_snd, Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hh : e.hom.left ≫ (snd H.X H.X).left = (μ[H.X]).left :=
    congrArg Over.Hom.left he
  rw [← hh]
  have hi : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  infer_instance

/-- The image of the product of two copies of an open chart in a smooth
relative group is open. -/
theorem isOpenMap_multiply_openChart [Smooth H.X.hom] {W : Over S}
    (i : W ⟶ H.X) [IsOpenImmersion i.left] :
    IsOpenMap ((i ⊗ₘ i) ≫ μ[H.X]).left := by
  have hi := tensorHom_property i i (P := @IsOpenImmersion) inferInstance inferInstance
  have hm := groupMultiplication_smooth H
  exact (μ[H.X]).left.isOpenMap.comp (i ⊗ₘ i).left.isOpenMap

end OpenCellProduct

section ProductOfOpenCell

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open private group_geometricallyIrreducible from LinearAlgebraicGroups.Reductive.CocharacterOpenCell

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false in
private theorem rationalPoint_lifts_open {U X : SchemeOver k} (i : U ⟶ X)
    [IsOpenImmersion i.left] (p : 𝟙_ (SchemeOver k) ⟶ X)
    (hp : p.left (IsLocalRing.closedPoint k) ∈ Set.range i.left) :
    ∃ q : 𝟙_ (SchemeOver k) ⟶ U, q ≫ i = p := by
  let : Subsingleton (𝟙_ (SchemeOver k)).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have h : Set.range p.left ⊆ Set.range i.left := by
    rintro _ ⟨r, rfl⟩
    rw [Subsingleton.elim r (IsLocalRing.closedPoint k)]
    exact hp
  let g := IsOpenImmersion.lift i.left p.left h
  have hg : g ≫ i.left = p.left := IsOpenImmersion.lift_fac _ _ h
  refine ⟨Over.homMk g ?_, Over.OverMorphism.ext hg⟩
  rw [← Over.w i, ← Category.assoc, hg]
  exact Over.w p

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Products of two points of a nonempty open chart in a smooth connected
group over an algebraically closed field cover the group. -/
theorem multiply_openChart_surjective [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    [Smooth G.val.X.hom] [ConnectedSpace G.val.X.left]
    {U : SchemeOver k} [Nonempty U.left] (i : U ⟶ G.val.X) [IsOpenImmersion i.left] :
    Surjective ((i ⊗ₘ i) ≫ μ[G.val.X]).left := by
  let X := G.val.X
  have hX := G.property.2.1
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  let : GeometricallyIrreducible X.hom := group_geometricallyIrreducible G
  let : IrreducibleSpace X.left := GeometricallyIrreducible.irreducibleSpace_of_subsingleton X.hom
  let m : U ⊗ U ⟶ X := (i ⊗ₘ i) ≫ μ[X]
  have hm : IsOpen (Set.range m.left) := (isOpenMap_multiply_openChart G.val i).isOpen_range
  have allClosed (x : X.left) (hclosed : IsClosed ({x} : Set X.left)) :
      x ∈ Set.range m.left := by
    let x₀ : 𝟙_ (SchemeOver k) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom x hclosed) (pointOfClosedPoint_comp X.hom x hclosed)
    let t := GrpObj.mulRight x₀
    let j := i ≫ ι[X] ≫ t.hom
    have hinv : IsIso (ι[X]).left := (Over.forget _).map_isIso ι[X]
    have ht : IsIso t.hom.left := (Over.forget _).map_isIso t.hom
    have hj : IsOpenImmersion j.left := by
      change IsOpenImmersion (i.left ≫ (ι[X]).left ≫ t.hom.left)
      infer_instance
    have hiOpen : IsOpen (Set.range i.left) := i.left.isOpenMap.isOpen_range
    have hjOpen : IsOpen (Set.range j.left) := j.left.isOpenMap.isOpen_range
    have hne : (Set.range j.left ∩ Set.range i.left).Nonempty :=
      (hiOpen.dense (Set.range_nonempty i.left)).inter_open_nonempty _ hjOpen (Set.range_nonempty j.left)
    obtain ⟨y, hy, hyClosed⟩ := nonempty_inter_closedPoints hne (hjOpen.inter hiOpen).isLocallyClosed
    let y₀ : 𝟙_ (SchemeOver k) ⟶ X :=
      Over.homMk (pointOfClosedPoint X.hom y hyClosed) (pointOfClosedPoint_comp X.hom y hyClosed)
    have hy₀ : y₀.left (IsLocalRing.closedPoint k) = y :=
      pointOfClosedPoint_apply _ _ _ _
    obtain ⟨a, ha⟩ := rationalPoint_lifts_open j y₀ (hy₀.symm ▸ hy.1)
    obtain ⟨b, hb⟩ := rationalPoint_lifts_open i y₀ (hy₀.symm ▸ hy.2)
    have htEval (g : 𝟙_ (SchemeOver k) ⟶ X) : g ≫ t.hom = g * x₀ := by
      change g ≫ lift (𝟙 X) (toUnit X ≫ x₀) ≫ μ[X] = _
      rw [comp_lift_assoc, Category.comp_id, ← Category.assoc g (toUnit X) x₀,
        toUnit_unique (g ≫ toUnit X) (𝟙 _), Category.id_comp]
      rfl
    have hab : y₀ = (a ≫ i)⁻¹ * x₀ := by
      calc
        _ = a ≫ j := ha.symm
        _ = ((a ≫ i) ≫ ι[X]) ≫ t.hom := by simp only [j, Category.assoc]
        _ = _ := htEval _
    let p := lift a b
    have hx : p ≫ m = x₀ := by
      change lift a b ≫ (i ⊗ₘ i) ≫ μ[X] = x₀
      rw [lift_map_assoc]
      change (a ≫ i) * (b ≫ i) = x₀
      rw [hb, hab, mul_inv_cancel_left]
    refine ⟨p.left (IsLocalRing.closedPoint k), ?_⟩
    have hx' := congrArg (fun f : 𝟙_ (SchemeOver k) ⟶ X => f.left (IsLocalRing.closedPoint k)) hx
    exact hx'.trans (pointOfClosedPoint_apply _ _ _ _)
  constructor
  intro x
  by_contra hx
  obtain ⟨y, hy, hClosed⟩ := nonempty_inter_closedPoints
    (show (Set.range m.left)ᶜ.Nonempty from ⟨x, hx⟩) hm.isClosed_compl.isLocallyClosed
  exact hy (allClosed y hClosed)

end ProductOfOpenCell

section FibreIdentityComponent

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
/-- A connected open chart containing the identity has a twofold product
whose image is the identity component of the group over an algebraically
closed field. -/
theorem multiply_openChart_identityComponent {k : Type u} [Field k] [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    {U : SchemeOver k} [ConnectedSpace U.left] (i : U ⟶ G.val.X) [IsOpenImmersion i.left]
    (s : 𝟙_ (SchemeOver k) ⟶ U) (hs : s ≫ i = η[G.val.X]) :
    Set.range ((i ⊗ₘ i) ≫ μ[G.val.X]).left =
      connectedComponent (η[G.val.X].left (IsLocalRing.closedPoint k)) := by
  obtain ⟨Q, H, q, j, h⟩ := LinearAlgebraicGroups.identityComponentAndQuotient k G
  let : Subsingleton (𝟙_ (SchemeOver k)).left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let j₀ := j.hom.hom
  have hjO : IsOpenImmersion j₀.left := h.1.openImmersion
  have hjC : IsClosedImmersion j₀.left := h.1.closedImmersion
  have hcomp : Set.range j₀.left = connectedComponent (η[G.val.X].left (IsLocalRing.closedPoint k)) :=
    h.1.identityComponent.trans (congrArg (fun x => connectedComponent (η[G.val.X].left x))
      (Subsingleton.elim _ _))
  have hcon : _root_.IsConnected (Set.range i.left) := by
    rw [← Set.image_univ]
    exact isConnected_univ.image _ i.left.continuous.continuousOn
  have hmem : η[G.val.X].left (IsLocalRing.closedPoint k) ∈ Set.range i.left :=
    ⟨s.left (IsLocalRing.closedPoint k),
      congrArg (fun f : 𝟙_ (SchemeOver k) ⟶ G.val.X => f.left (IsLocalRing.closedPoint k)) hs⟩
  have hsub : Set.range i.left ⊆ Set.range j₀.left :=
    hcomp.symm ▸ hcon.subset_connectedComponent hmem
  let l := IsOpenImmersion.lift j₀.left i.left hsub
  have hl : l ≫ j₀.left = i.left := IsOpenImmersion.lift_fac _ _ hsub
  let i₀ : U ⟶ H.X := Over.homMk l (by rw [← Over.w j₀, ← Category.assoc, hl]; exact Over.w i)
  have hi₀ : IsOpenImmersion i₀.left := by
    change IsOpenImmersion l
    have hlO : IsOpenImmersion (l ≫ j₀.left) := hl.symm ▸ inferInstanceAs (IsOpenImmersion i.left)
    exact IsOpenImmersion.of_comp l j₀.left
  have hcmp : i₀ ≫ j₀ = i := Over.OverMorphism.ext hl
  have hA : IsAffine G.val.X.left := G.property.1
  have hT : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  have hQ : QuasiCompact G.val.X.hom := G.property.2.2
  have hH : IsAffine H.X.left := isAffine_of_isAffineHom j₀.left
  have hHT : LocallyOfFiniteType H.X.hom := by rw [← Over.w j₀]; infer_instance
  have hHQ : QuasiCompact H.X.hom := by rw [← Over.w j₀]; infer_instance
  have hHS : Smooth H.X.hom := by rw [← Over.w j₀]; infer_instance
  have hHC : GeometricallyConnected H.X.hom := h.1.geometricallyConnected
  have hconn : ConnectedSpace H.X.left := GeometricallyConnected.connectedSpace_of_subsingleton H.X.hom
  let HH : AffineAlgebraicGroup k := ⟨H, hH, hHT, hHQ⟩
  let m : U ⊗ U ⟶ H.X := (i₀ ⊗ₘ i₀) ≫ μ[H.X]
  have hm : Surjective m.left := multiply_openChart_surjective HH i₀
  have hmf : m ≫ j₀ = (i ⊗ₘ i) ≫ μ[G.val.X] := by
    change ((i₀ ⊗ₘ i₀) ≫ μ[H.X]) ≫ j₀ = _
    rw [Category.assoc, IsMonHom.mul_hom j₀, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, hcmp]
  rw [← hmf, ← hcomp]
  change Set.range (j₀.left ∘ m.left) = Set.range j₀.left
  rw [Set.range_comp, Set.range_eq_univ.mpr hm.surj, Set.image_univ]

end FibreIdentityComponent

section GeometricCell

open CategoryTheory.Limits
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Integers integerAlgebra)

/-- Extending the integral chart coordinates over the integers changes only
the base of the polynomial ring and of the group algebra. -/
def integralCellBaseChange (D : BasedRootDatum.{u}) (k : Type u) [CommRing k] :
    (k ⊗[ℤ] IntegralCellCoordinates D) ≃ₐ[k] CellPolynomialAlgebra D k :=
  MvPolynomial.rTensorAlgEquiv.trans <| MvPolynomial.mapAlgEquiv D.I
    ((AddMonoidAlgebra.scalarTensorEquiv ℤ k).trans
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv k k D.X))

private theorem cellPolynomialAlgebra_isDomain (D : BasedRootDatum.{u})
    (k : Type u) [CommRing k] [IsDomain k] :
    IsDomain (CellPolynomialAlgebra D k) := by
  let : Module.Free ℤ D.X := D.freeX
  let b := Module.Free.chooseBasis ℤ D.X
  let : UniqueSums D.X := b.repr.toAddEquiv.uniqueSums_iff.mpr inferInstance
  exact inferInstanceAs (IsDomain (MvPolynomial D.I (MonoidAlgebra k (Multiplicative D.X))))

/-- The coordinate ring after a coefficient extension to a field is a domain. -/
theorem integralCellBaseChange_isDomain (D : BasedRootDatum.{u}) (k : Type u) [Field k] :
    IsDomain (k ⊗[ℤ] IntegralCellCoordinates D) := by
  let : IsDomain (CellPolynomialAlgebra D k) := cellPolynomialAlgebra_isDomain D k
  exact (integralCellBaseChange D k).toRingEquiv.toMulEquiv.isDomain (CellPolynomialAlgebra D k)

end GeometricCell

section FiniteSupport

open CategoryTheory.Limits

private theorem affine_open_contains_principal_of_generic {R A K : Type u}
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing A] [Algebra R A] (U : Set (PrimeSpectrum A)) (hU : IsOpen U)
    (hgeneric : Set.range (pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⊆ U) :
    ∃ r : R, r ≠ 0 ∧ (PrimeSpectrum.basicOpen (algebraMap R A r) : Set _) ⊆ U := by
  let : Algebra A (K ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let I := PrimeSpectrum.vanishingIdeal Uᶜ
  have hI : PrimeSpectrum.zeroLocus (I : Set A) = Uᶜ :=
    (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure Uᶜ).trans hU.isClosed_compl.closure_eq
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let e := pullbackSymmetry f g ≪≫ pullbackSpecIso R K A
  have he : e.inv ≫ pullback.fst f g =
      Spec.map (CommRingCat.ofHom (algebraMap A (K ⊗[R] A))) := by
    simp [e, f, g]
    rfl
  have hg : ∀ z : PrimeSpectrum (K ⊗[R] A),
      PrimeSpectrum.comap (algebraMap A (K ⊗[R] A)) z ∈ U := by
    intro z
    apply hgeneric
    exact ⟨e.inv z, congrArg (fun m : Spec (CommRingCat.of (K ⊗[R] A)) ⟶ _ => m z) he⟩
  have htop : I.map (algebraMap A (K ⊗[R] A)) = ⊤ := by
    rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top]
    have heq : I.map (algebraMap A (K ⊗[R] A)) =
        Ideal.span ((algebraMap A (K ⊗[R] A)) '' (I : Set A)) :=
      calc
        _ = (Ideal.span (I : Set A)).map (algebraMap A (K ⊗[R] A)) :=
          congrArg (fun J : Ideal A => J.map (algebraMap A (K ⊗[R] A))) (Ideal.span_eq I).symm
        _ = _ := Ideal.map_span _ _
    rw [heq, PrimeSpectrum.zeroLocus_span, ← PrimeSpectrum.preimage_comap_zeroLocus, hI]
    exact Set.eq_empty_iff_forall_notMem.mpr fun z hz => hz (hg z)
  let : IsLocalization ((nonZeroDivisors R).map (algebraMap R A)) (K ⊗[R] A) :=
    IsLocalization.tensorRight (S := A) K (nonZeroDivisors R)
  obtain ⟨r, hr, hm⟩ := exists_nonzero_base_scalar_mem_ideal (R := R) (L := K ⊗[R] A) I htop
  refine ⟨r, hr, ?_⟩
  intro z hz
  by_contra hz'
  exact hz ((PrimeSpectrum.mem_vanishingIdeal _ _).mp hm z hz')

end FiniteSupport

section IntegerBaseChange

private theorem ringHom_eq_of_equiv_int {R A : Type*} [CommRing R] [CommRing A]
    (e : R ≃+* ℤ) (g : R →+* A) : g = (Int.castRingHom A).comp e.toRingHom := by
  apply RingHom.ext
  intro z
  have h := RingHom.congr_fun (Subsingleton.elim
    (g.comp e.symm.toRingHom) (Int.castRingHom A)) (e z)
  change g (e.symm (e z)) = (Int.castRingHom A) (e z) at h
  rwa [e.symm_apply_apply] at h

private def integerTensorEquiv {R : Type u} [CommRing R] (e : R ≃+* ℤ)
    (k A : Type u) [CommRing k] [CommRing A] [Algebra R k] [Algebra R A] :
    k ⊗[R] A ≃ₐ[k] k ⊗[ℤ] A := by
  have h {B : Type u} [CommRing B] [Algebra R B] (r : R) (b : B) : r • b = e r • b := by
    rw [Algebra.smul_def r, Algebra.smul_def (e r),
      ringHom_eq_of_equiv_int e (algebraMap R B)]
    rfl
  let : TensorProduct.CompatibleSMul ℤ R k A := ⟨fun r a b => by
    rw [h r a, h r b, TensorProduct.smul_tmul]⟩
  exact Algebra.TensorProduct.equivOfCompatibleSMul ℤ R k k A

private theorem algebraMap_nonZeroDivisor_of_torsionFree
    {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] [Module.IsTorsionFree R A]
    (r : R) (hr : r ≠ 0) : algebraMap R A r ∈ nonZeroDivisors A := by
  refine mem_nonZeroDivisors_iff_left.mpr fun a ha => ?_
  exact (smul_eq_zero.mp ((Algebra.smul_def r a).trans ha)).resolve_left hr

end IntegerBaseChange
section AffineIntegerOpen

open CategoryTheory.Limits

variable {A : Type u} [CommRing A]

set_option backward.isDefEq.respectTransparency false in
private theorem quotientFibres_clopen {R : Type u} [CommRing R] [Algebra R A]
    (e : R ≃+* ℤ) (n : ℤ) (U : Set (PrimeSpectrum A))
    (hU : ∀ s : PrimeSpectrum R, IsClopen
      ((Subtype.val : (PrimeSpectrum.comap (algebraMap R A) ⁻¹' {s}) → _) ⁻¹' U)) :
    let f := PrimeSpectrum.comap (integerFibreMap (A := A) n)
    let π := PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {intScalar (A := A) n}))
    ∀ s : PrimeSpectrum (ℤ ⧸ Ideal.span {n}),
      IsClopen ((Subtype.val : (f ⁻¹' {s}) → _) ⁻¹' (π ⁻¹' U)) := by
  dsimp only
  let I : Ideal ℤ := Ideal.span {n}
  let J : Ideal A := Ideal.span {intScalar (A := A) n}
  let α := integerFibreMap (A := A) n
  let β := (Ideal.Quotient.mk I).comp e.toRingHom
  let π := PrimeSpectrum.comap (Ideal.Quotient.mk J)
  have hcomp : (Ideal.Quotient.mk J).comp (algebraMap R A) = α.comp β := by
    apply RingHom.ext
    intro r
    change Ideal.Quotient.mk J (algebraMap R A r) = α (Ideal.Quotient.mk I (e r))
    rw [show algebraMap R A r = algebraMap ℤ A (e r) from
      RingHom.congr_fun (ringHom_eq_of_equiv_int e (algebraMap R A)) r]
    exact (Ideal.Quotient.lift_mk I ((Ideal.Quotient.mk J).comp (algebraMap ℤ A)) _).symm
  intro s
  let t := PrimeSpectrum.comap β s
  let f := PrimeSpectrum.comap (algebraMap R A)
  let j : (PrimeSpectrum.comap α ⁻¹' {s}) → (f ⁻¹' {t}) := fun y =>
    ⟨π y, by
      change PrimeSpectrum.comap (algebraMap R A) (π y) = t
      rw [← PrimeSpectrum.comap_comp_apply, hcomp, PrimeSpectrum.comap_comp_apply]
      exact congrArg (PrimeSpectrum.comap β) y.property⟩
  have hc : Continuous j :=
    ((PrimeSpectrum.continuous_comap _).comp continuous_subtype_val).subtype_mk _
  exact (hU t).preimage hc

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 750000 in
/-- A fibrewise clopen open of a flat affine integer scheme is affine if it
contains the generic fibre. -/
theorem exists_affine_open_on_integer_base
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (e : R ≃+* ℤ) {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] (U : Set X) (hU : IsOpen U)
    (hgeneric : Set.range (pullback.fst f (Spec.map
      (CommRingCat.ofHom (algebraMap R K)))) ⊆ U)
    (hfibre : ∀ x : Spec (CommRingCat.of R),
      IsClopen ((Subtype.val : (f ⁻¹' {x}) → _) ⁻¹' U)) :
    ∃ (Y : Scheme.{u}) (i : Y ⟶ X), IsAffine Y ∧ IsOpenImmersion i ∧ Set.range i = U := by
  let A := Γ(X, ⊤)
  let E := X.isoSpec
  let φ := Spec.preimage (E.inv ≫ f)
  let : Algebra R A := φ.hom.toAlgebra
  let f₀ := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have h₀ : f₀ = E.inv ≫ f := Spec.map_preimage _
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let U₀ := E.inv ⁻¹' U
  have ho₀ : IsOpen U₀ := hU.preimage E.inv.continuous
  have hflat : Flat f₀ := h₀ ▸ (inferInstance : Flat (E.inv ≫ f))
  have hfA : Module.Flat R A := RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hflat)
  have hgen₀ : Set.range (pullback.fst f₀ g) ⊆ U₀ := by
    let p : pullback f₀ g ⟶ pullback f g :=
      pullback.lift (pullback.fst f₀ g ≫ E.inv) (pullback.snd f₀ g)
        (by rw [Category.assoc, ← h₀, pullback.condition])
    rintro _ ⟨x, rfl⟩
    apply hgeneric
    refine ⟨p x, ?_⟩
    have hp : p ≫ pullback.fst f g = pullback.fst f₀ g ≫ E.inv := pullback.lift_fst _ _ _
    exact congrArg (fun a : pullback f₀ g ⟶ X => a x) hp
  obtain ⟨r, hr, hBasic⟩ := affine_open_contains_principal_of_generic U₀ ho₀ hgen₀
  let n := e r
  have hn : n ≠ 0 := fun h => hr (e.injective (h.trans e.map_zero.symm))
  have hcast : algebraMap R A r = intScalar (A := A) n :=
    RingHom.congr_fun (ringHom_eq_of_equiv_int e (algebraMap R A)) r
  rw [hcast] at hBasic
  have hx : intScalar (A := A) n ∈ nonZeroDivisors A :=
    hcast ▸ algebraMap_nonZeroDivisor_of_torsionFree r hr
  have hfibre₀ (x : PrimeSpectrum R) : IsClopen
      ((Subtype.val : (PrimeSpectrum.comap (algebraMap R A) ⁻¹' {x}) → _) ⁻¹' U₀) := by
    let g : PrimeSpectrum A → X := E.inv
    let j : (PrimeSpectrum.comap (algebraMap R A) ⁻¹' {x}) → (f ⁻¹' {x}) := fun y =>
      ⟨g y.val, (congrArg (fun a : Spec A ⟶ Spec (CommRingCat.of R) => a y.val) h₀).symm.trans
        y.property⟩
    have hg : Continuous g := E.inv.continuous
    have hc : Continuous j := (hg.comp continuous_subtype_val).subtype_mk _
    exact (hfibre x).preimage hc
  obtain ⟨a, hi, hrange⟩ := exists_affine_open_over_integer_fibres n hn hx U₀ hBasic
    (quotientFibres_clopen e n U₀ hfibre₀)
  let i := Spec.map (CommRingCat.ofHom (algebraMap A (componentRestriction (intScalar n) a)))
  refine ⟨_, i ≫ E.inv, inferInstance, ?_, ?_⟩
  · have : IsOpenImmersion i := hi
    infer_instance
  · change Set.range (E.inv ∘ i) = U
    rw [Set.range_comp, show Set.range i = U₀ from hrange]
    exact E.inv.surjective.image_preimage U

end AffineIntegerOpen

section RelativeIdentityComponent

open CategoryTheory.Limits
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)

set_option backward.isDefEq.respectTransparency false in
private theorem overPullback_map_isPullback {S T : Scheme.{u}} (f : T ⟶ S)
    {X Y : Over S} (g : X ⟶ Y) :
    IsPullback ((Over.pullback f).map g).left (pullback.fst X.hom f)
      (pullback.fst Y.hom f) g.left := by
  apply IsPullback.of_right (h₁₂ := pullback.snd Y.hom f) (h₂₂ := Y.hom) (v₁₃ := f)
  · simp only [Over.pullback_map_left, pullback.lift_snd, Over.w g]
    exact (IsPullback.of_hasPullback X.hom f).flip
  · simp only [Over.pullback_map_left, pullback.lift_fst]
  · exact (IsPullback.of_hasPullback Y.hom f).flip

private theorem range_comp_of_surjective {A B C : Scheme.{u}} (a : A ⟶ B)
    (b : B ⟶ C) [Surjective a] :
    Set.range (a ≫ b) = Set.range b := by
  change Set.range (b ∘ a) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr a.surjective, Set.image_univ]

private theorem overPullback_map_range {S T : Scheme.{u}} (f : T ⟶ S)
    {X Y : Over S} (g : X ⟶ Y) :
    Set.range ((Over.pullback f).map g).left =
      (pullback.fst Y.hom f) ⁻¹' Set.range g.left := by
  let h := overPullback_map_isPullback f g
  rw [← h.isoPullback_hom_fst, range_comp_of_surjective, Scheme.Pullback.range_fst]

set_option backward.isDefEq.respectTransparency false in
private theorem overPullback_multiply_chart {S T : Scheme.{u}} (f : T ⟶ S)
    (G : Grp (Over S)) {W : Over S} (i : W ⟶ G.X) :
    let F := Over.pullback f
    let G' := F.mapGrp.obj G
    let i' := F.map i
    (i' ⊗ₘ i') ≫ μ[G'.X] = Functor.LaxMonoidal.μ F W W ≫ F.map ((i ⊗ₘ i) ≫ μ[G.X]) := by
  dsimp only
  change _ ≫ Functor.LaxMonoidal.μ (Over.pullback f) _ _ ≫ (Over.pullback f).map μ[G.X] = _
  rw [Functor.map_comp, Functor.LaxMonoidal.μ_natural_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem overPullback_multiply_chart_range {S T : Scheme.{u}} (f : T ⟶ S)
    (G : Grp (Over S)) {W : Over S} (i : W ⟶ G.X) :
    let F := Over.pullback f
    let G' := F.mapGrp.obj G
    let i' := F.map i
    Set.range ((i' ⊗ₘ i') ≫ μ[G'.X]).left =
      (pullback.fst G.X.hom f) ⁻¹' Set.range ((i ⊗ₘ i) ≫ μ[G.X]).left := by
  dsimp only
  rw [overPullback_multiply_chart f G i, Over.comp_left]
  have : IsIso (Functor.LaxMonoidal.μ (Over.pullback f) W W).left := (Over.forget _).map_isIso _
  rw [range_comp_of_surjective]
  exact overPullback_map_range f ((i ⊗ₘ i) ≫ μ[G.X])

private theorem overPullback_chart_section {S T : Scheme.{u}} (f : T ⟶ S)
    (G : Grp (Over S)) {W : Over S} (i : W ⟶ G.X) (s : 𝟙_ (Over S) ⟶ W)
    (hs : s ≫ i = η[G.X]) :
    (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map s) ≫ (Over.pullback f).map i =
      η[((Over.pullback f).mapGrp.obj G).X] := by
  rw [Category.assoc, ← Functor.map_comp, hs]
  rfl

private theorem range_subset_of_fibres {S : Scheme.{u}} {X Y : Over S}
    (g : X ⟶ Y) (U : Set Y.left)
    (h : ∀ s : S, Set.range ((Over.pullback (S.fromSpecResidueField s)).map g).left ⊆
      (Y.hom.fiberι s) ⁻¹' U) : Set.range g.left ⊆ U := by
  rintro _ ⟨x, rfl⟩
  let s := X.hom x
  let f := S.fromSpecResidueField s
  let y : ((Over.pullback f).obj X).left := X.hom.asFiber x
  have hx : pullback.fst X.hom f y = x := X.hom.fiberι_asFiber x
  have H := congrArg (fun a : ((Over.pullback f).obj X).left ⟶ Y.left => a y)
    (overPullback_map_isPullback f g).w
  change pullback.fst Y.hom f (((Over.pullback f).map g).left y) =
    g.left (pullback.fst X.hom f y) at H
  rw [hx] at H
  have hmem := h s (Set.mem_range_self y : ((Over.pullback f).map g).left y ∈
    Set.range ((Over.pullback f).map g).left)
  change pullback.fst Y.hom f (((Over.pullback f).map g).left y) ∈ U at hmem
  exact H ▸ hmem

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
private theorem exists_fieldIdentityComponent
    {k : Type u} [Field k] (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom]
    {W : SchemeOver k} [GeometricallyConnected W.hom]
    (i : W ⟶ G.val.X) [IsOpenImmersion i.left] (s : 𝟙_ (SchemeOver k) ⟶ W)
    (hs : s ≫ i = η[G.val.X]) :
    ∃ (Q H : Specs.GroupScheme k) (q : G.val ⟶ Q) (j : H ⟶ G.val),
      Specs.ComponentQuotient Q H q j ∧
      Set.range j.hom.hom.left = Set.range ((i ⊗ₘ i) ≫ μ[G.val.X]).left := by
  obtain ⟨Q, H, q, j, h, _, _, hbase⟩ := LinearAlgebraicGroups.identityComponentAndQuotient k G
  refine ⟨Q, H, q, j, h, ?_⟩
  let K := AlgebraicClosure k
  let f := fieldSpecMap k K
  let F := baseChange k K
  let G' := (groupBaseChange k K).obj G.val
  let i' := F.map i
  let j' := (groupBaseChange k K).map j
  let s' := Functor.LaxMonoidal.ε F ≫ F.map s
  let _ : IsAffine G.val.X.left := G.property.1
  let _ : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  let _ : QuasiCompact G.val.X.hom := G.property.2.2
  have hAffMap : IsAffineHom G.val.X.hom := isAffineHom_of_isAffine G.val.X.hom
  have hAP : IsAffineHom (pullback.snd G.val.X.hom f) :=
    MorphismProperty.pullback_snd G.val.X.hom f hAffMap
  have hA : IsAffine G'.X.left := isAffine_of_isAffineHom (pullback.snd G.val.X.hom f)
  have hT : LocallyOfFiniteType G'.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.val.X.hom f))
  have hQ : QuasiCompact G'.X.hom := inferInstanceAs (QuasiCompact (pullback.snd G.val.X.hom f))
  let _ : Smooth G'.X.hom := inferInstanceAs (Smooth (pullback.snd G.val.X.hom f))
  have hC : GeometricallyConnected (F.obj W).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd W.hom f))
  let _ : ConnectedSpace (F.obj W).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (F.obj W).hom
  let _ : IsOpenImmersion i'.left :=
    MorphismProperty.of_isPullback (overPullback_map_isPullback f i).flip inferInstance
  let Gₖ : AffineAlgebraicGroup K := ⟨G', hA, hT, hQ⟩
  have hm := multiply_openChart_identityComponent Gₖ i' s' (overPullback_chart_section f G.val i s hs)
  have hj' := (hbase K).identityComponent
  let : Subsingleton (𝟙_ (SchemeOver K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hsame : Set.range j'.hom.hom.left = Set.range ((i' ⊗ₘ i') ≫ μ[G'.X]).left := by
    rw [hj', hm]
    exact congrArg (fun x => connectedComponent (η[G'.X].left x)) (Subsingleton.elim _ _)
  have hsurj : Surjective f := ⟨Function.surjective_to_subsingleton f⟩
  apply (pullback.fst G.val.X.hom f).surjective.preimage_injective
  rw [← overPullback_map_range f j.hom.hom, ← overPullback_multiply_chart_range f G.val i]
  exact hsame

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 650000 in
private theorem exists_identityComponent_of_chart_baseChange
    {S : Scheme.{u}} (G : Grp (Over S))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [QuasiCompact G.X.hom]
    {W : Over S} [GeometricallyConnected W.hom] (i : W ⟶ G.X) [IsOpenImmersion i.left]
    (s : 𝟙_ (Over S) ⟶ W) (hs : s ≫ i = η[G.X]) {k : Type u} [Field k]
    (f : Spec (CommRingCat.of k) ⟶ S) :
    let F := Over.pullback f
    let G' := F.mapGrp.obj G
    ∃ (Q H : Specs.GroupScheme k) (q : G' ⟶ Q) (j : H ⟶ G'),
      Specs.ComponentQuotient Q H q j ∧
      Set.range j.hom.hom.left =
        (pullback.fst G.X.hom f) ⁻¹' Set.range ((i ⊗ₘ i) ≫ μ[G.X]).left := by
  dsimp only
  let F := Over.pullback f
  let G' := F.mapGrp.obj G
  let i' := F.map i
  let s' := Functor.LaxMonoidal.ε F ≫ F.map s
  have hAP : IsAffineHom (pullback.snd G.X.hom f) :=
    MorphismProperty.pullback_snd G.X.hom f inferInstance
  have hS : Smooth G'.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom f))
  have hT : LocallyOfFiniteType G'.X.hom := inferInstance
  have hQ : QuasiCompact G'.X.hom := inferInstanceAs (QuasiCompact (pullback.snd G.X.hom f))
  have hC : GeometricallyConnected (F.obj W).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd W.hom f))
  have hi' : IsOpenImmersion i'.left :=
    MorphismProperty.of_isPullback (overPullback_map_isPullback f i).flip inferInstance
  let Gₖ : AffineAlgebraicGroup k :=
    ⟨G', isAffine_of_isAffineHom (pullback.snd G.X.hom f), hT, hQ⟩
  obtain ⟨Q, H, q, j, h, hEq⟩ := exists_fieldIdentityComponent Gₖ i' s'
    (overPullback_chart_section f G i s hs)
  exact ⟨Q, H, q, j, h, hEq.trans (overPullback_multiply_chart_range f G i)⟩

private def liftOpenOver {S : Scheme.{u}} {X V Z : Over S} (i : V ⟶ X) (f : Z ⟶ X)
    [IsOpenImmersion i.left] (h : Set.range f.left ⊆ Set.range i.left) : Z ⟶ V :=
  Over.homMk (IsOpenImmersion.lift i.left f.left h) (by
    rw [← Over.w i, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])

@[reassoc]
private theorem liftOpenOver_fac {S : Scheme.{u}} {X V Z : Over S} (i : V ⟶ X) (f : Z ⟶ X)
    [IsOpenImmersion i.left] (h : Set.range f.left ⊆ Set.range i.left) :
    liftOpenOver i f h ≫ i = f :=
  Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ h)

section GroupRestriction

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {X V : C} [GrpObj X]
  (j : V ⟶ X) [Mono j]
  (e : 𝟙_ C ⟶ V) (m : V ⊗ V ⟶ V) (v : V ⟶ V)
  (he : e ≫ j = η[X]) (hm : m ≫ j = (j ⊗ₘ j) ≫ μ[X]) (hv : v ≫ j = j ≫ ι[X])

omit [Mono j] in
include hm in
private theorem comp_restricted_mul {U : C} (a : U ⟶ V ⊗ V) :
    a ≫ m ≫ j = (a ≫ fst V V ≫ j) * (a ≫ snd V V ≫ j) := by
  simp only [hm, MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst,
    tensorHom_snd]

include he hm hv in
@[instance_reducible]
private def groupOfRestrictedOperations : GrpObj V where
  one := e
  mul := m
  inv := v
  one_mul := by
    apply (cancel_mono j).mp
    rw [Category.assoc, comp_restricted_mul j m hm]
    simp [he, leftUnitor_hom, MonObj.one_eq_one X]
  mul_one := by
    apply (cancel_mono j).mp
    rw [Category.assoc, comp_restricted_mul j m hm]
    simp [he, rightUnitor_hom, MonObj.one_eq_one X]
  mul_assoc := by
    apply (cancel_mono j).mp
    simp only [Category.assoc, comp_restricted_mul j m hm, whiskerRight_fst_assoc, whiskerRight_snd_assoc,
      whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, MonObj.comp_mul, associator_hom_fst_assoc,
      associator_hom_snd_fst_assoc, associator_hom_snd_snd_assoc, mul_assoc]
  left_inv := by
    apply (cancel_mono j).mp
    rw [Category.assoc, Category.assoc, comp_restricted_mul j m hm]
    simp only [lift_fst_assoc, lift_snd_assoc, hv, Category.id_comp, he]
    change j⁻¹ * j = 1
    exact inv_mul_cancel j
  right_inv := by
    apply (cancel_mono j).mp
    rw [Category.assoc, Category.assoc, comp_restricted_mul j m hm]
    simp only [lift_fst_assoc, lift_snd_assoc, hv, Category.id_comp, he]
    change j * j⁻¹ = 1
    exact mul_inv_cancel j

end GroupRestriction

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private theorem exists_openSubgroup_of_chart_range
    {S : Scheme.{u}} (G : Grp (Over S))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [QuasiCompact G.X.hom]
    {W V : Over S} [GeometricallyConnected W.hom] (i : W ⟶ G.X) [IsOpenImmersion i.left]
    (s : 𝟙_ (Over S) ⟶ W) (hs : s ≫ i = η[G.X])
    (j : V ⟶ G.X) [IsOpenImmersion j.left]
    (hj : Set.range j.left = Set.range ((i ⊗ₘ i) ≫ μ[G.X]).left) :
    ∃ g : GrpObj V, ∃ j' : ({ X := V, grp := g } : Grp (Over S)) ⟶ G,
      j'.hom.hom = j ∧ GeometricallyConnected V.hom := by
  have hfield (k : Type u) [Field k] (f : Spec (CommRingCat.of k) ⟶ S) :
      let F := Over.pullback f
      ∃ (H : Specs.GroupScheme k) (l : H ⟶ F.mapGrp.obj G),
        IsOpenImmersion l.hom.hom.left ∧ GeometricallyConnected H.X.hom ∧
        Set.range (F.map j).left = Set.range l.hom.hom.left := by
    obtain ⟨Q, H, q, l, hq, heq⟩ :=
      exists_identityComponent_of_chart_baseChange G i s hs f
    refine ⟨H, l, hq.openImmersion, hq.geometricallyConnected, ?_⟩
    exact (overPullback_map_range f j).trans (by rw [hj, heq])
  have hsection : lift s s ≫ ((i ⊗ₘ i) ≫ μ[G.X]) = η[G.X] := by
    rw [lift_map_assoc]
    change (s ≫ i) * (s ≫ i) = η[G.X]
    rw [hs]
    exact one_mul (1 : 𝟙_ (Over S) ⟶ G.X)
  have he : Set.range (η[G.X]).left ⊆ Set.range j.left := by
    rw [hj, ← hsection, Over.comp_left]
    rintro _ ⟨z, rfl⟩
    exact ⟨_, rfl⟩
  have hlifts (x : S) :
      let F := Over.pullback (S.fromSpecResidueField x)
      ∃ (H : Specs.GroupScheme (S.residueField x)) (l : H ⟶ F.mapGrp.obj G)
        (p : F.obj V ⟶ H.X),
        p ≫ l.hom.hom = F.map j ∧ Set.range l.hom.hom.left = Set.range (F.map j).left := by
    obtain ⟨H, l, hO, _, hrange⟩ := hfield (S.residueField x) (S.fromSpecResidueField x)
    let p := liftOpenOver l.hom.hom ((Over.pullback (S.fromSpecResidueField x)).map j) hrange.le
    exact ⟨H, l, p, liftOpenOver_fac _ _ _, hrange.symm⟩
  have hm : Set.range ((j ⊗ₘ j) ≫ μ[G.X]).left ⊆ Set.range j.left := by
    apply range_subset_of_fibres
    intro x
    let f := S.fromSpecResidueField x
    let F := Over.pullback f
    let G' := F.mapGrp.obj G
    have hrange : Set.range (F.map j).left =
        (G.X.hom.fiberι x) ⁻¹' Set.range j.left := overPullback_map_range f j
    obtain ⟨H, l, p, hp, hl⟩ := hlifts x
    have hop : ((F.map j ⊗ₘ F.map j) ≫ μ[G'.X]) = ((p ⊗ₘ p) ≫ μ[H.X]) ≫ l.hom.hom := by
      rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
        MonoidalCategory.tensorHom_comp_tensorHom, hp]
    have h : Set.range ((F.map j ⊗ₘ F.map j) ≫ μ[G'.X]).left ⊆ Set.range (F.map j).left := by
      rw [hop, ← hl, Over.comp_left]
      rintro _ ⟨z, rfl⟩
      exact ⟨_, rfl⟩
    rw [overPullback_multiply_chart f G j, Over.comp_left] at h
    have : IsIso (Functor.LaxMonoidal.μ F V V).left := (Over.forget _).map_isIso _
    rw [range_comp_of_surjective] at h
    exact h.trans hrange.le
  have hv : Set.range (j ≫ ι[G.X]).left ⊆ Set.range j.left := by
    apply range_subset_of_fibres
    intro x
    let f := S.fromSpecResidueField x
    let F := Over.pullback f
    let G' := F.mapGrp.obj G
    have hrange : Set.range (F.map j).left =
        (G.X.hom.fiberι x) ⁻¹' Set.range j.left := overPullback_map_range f j
    obtain ⟨H, l, p, hp, hl⟩ := hlifts x
    have hop : F.map (j ≫ ι[G.X]) = (p ≫ ι[H.X]) ≫ l.hom.hom := by
      rw [F.map_comp, Category.assoc, GrpObj.inv_hom, ← Category.assoc, hp]
      rfl
    change Set.range (F.map (j ≫ ι[G.X])).left ⊆ _
    rw [hop, ← hrange, ← hl, Over.comp_left]
    rintro _ ⟨z, rfl⟩
    exact ⟨_, rfl⟩
  have hgc : GeometricallyConnected V.hom := by
    constructor
    apply (geometrically_iff_of_isClosedUnderIsomorphisms
      (P := fun X : Scheme.{u} => ConnectedSpace X)).mpr
    intro k _ f
    let F := Over.pullback f
    obtain ⟨H, l, hO, hC, hrange⟩ := hfield k f
    have : IsOpenImmersion (F.map j).left :=
      MorphismProperty.of_isPullback (overPullback_map_isPullback f j).flip inferInstance
    let e := IsOpenImmersion.isoOfRangeEq (F.map j).left l.hom.hom.left hrange
    exact e.hom.homeomorph.connectedSpace_iff.mpr
      (GeometricallyConnected.connectedSpace_of_subsingleton H.X.hom)
  let e := liftOpenOver j (η[G.X]) he
  let m := liftOpenOver j ((j ⊗ₘ j) ≫ μ[G.X]) hm
  let v := liftOpenOver j (j ≫ ι[G.X]) hv
  let : Mono j := Over.mono_of_mono_left j
  let g : GrpObj V := groupOfRestrictedOperations j e m v
    (liftOpenOver_fac _ _ _) (liftOpenOver_fac _ _ _) (liftOpenOver_fac _ _ _)
  let : GrpObj V := g
  let : IsMonHom j := ⟨liftOpenOver_fac _ _ _, liftOpenOver_fac _ _ _⟩
  exact ⟨g, Grp.ofHom j, rfl, hgc⟩

end RelativeIdentityComponent

section GeometricallyConnectedIntegralChart

open CategoryTheory.Limits
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Integers integerAlgebra)

set_option backward.isDefEq.respectTransparency false in
private theorem geometricallyConnected_spec_over_integer_base {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] (e : R ≃+* ℤ)
    (h : ∀ (k : Type u) [Field k], IsDomain (k ⊗[ℤ] A)) :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun X : Scheme.{u} => ConnectedSpace X)).mpr
  intro k _ _
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R k))
  let E := pullbackSymmetry f g ≪≫ pullbackSpecIso R k A
  let : IsDomain (k ⊗[ℤ] A) := h k
  let : IsDomain (k ⊗[R] A) := (integerTensorEquiv e k A).toRingEquiv.toMulEquiv.isDomain _
  exact E.hom.homeomorph.connectedSpace_iff.mpr
    (inferInstanceAs (ConnectedSpace (PrimeSpectrum (k ⊗[R] A))))

/-- The integral polynomial chart has geometrically connected fibres. -/
theorem integralCell_geometricallyConnected (D : BasedRootDatum.{u}) :
    letI : Algebra Integers.{u} (IntegralCellCoordinates D) := integerAlgebra _
    GeometricallyConnected (Spec.map (CommRingCat.ofHom
      (algebraMap Integers.{u} (IntegralCellCoordinates D)))) := by
  let : Algebra Integers.{u} (IntegralCellCoordinates D) := integerAlgebra _
  exact geometricallyConnected_spec_over_integer_base ULift.ringEquiv (integralCellBaseChange_isDomain D)

end GeometricallyConnectedIntegralChart

section AffineIdentityComponent

open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- The twofold product of a pointed geometrically connected open chart
in a smooth affine group over the integers is an affine open subgroup
with geometrically connected fibres if the generic fibre is connected. -/
theorem exists_affineIdentityComponent_of_openChart {R K : Type u}
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (e : R ≃+* ℤ) (G : Grp (Over (Spec (CommRingCat.of R))))
    [IsAffine G.X.left] [Smooth G.X.hom] [QuasiCompact G.X.hom]
    (hGeneric : ConnectedSpace ↑(pullback G.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    {W : Over (Spec (CommRingCat.of R))} [GeometricallyConnected W.hom]
    (i : W ⟶ G.X) [IsOpenImmersion i.left]
    (s : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ W) (hs : s ≫ i = η[G.X]) :
    ∃ (H : Grp (Over (Spec (CommRingCat.of R)))) (j : H ⟶ G) (i₀ : W ⟶ H.X),
      IsAffine H.X.left ∧ Smooth H.X.hom ∧ QuasiCompact H.X.hom ∧
        GeometricallyConnected H.X.hom ∧ IsOpenImmersion j.hom.hom.left ∧
        Set.range j.hom.hom.left = Set.range ((i ⊗ₘ i) ≫ μ[G.X]).left ∧
        IsOpenImmersion i₀.left ∧ i₀ ≫ j.hom.hom = i ∧ s ≫ i₀ = η[H.X] := by
  let S := Spec (CommRingCat.of R)
  let f := G.X.hom
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let U := Set.range ((i ⊗ₘ i) ≫ μ[G.X]).left
  have ho : IsOpen U := (isOpenMap_multiply_openChart G i).isOpen_range
  have hA : IsAffineHom G.X.hom := isAffineHom_of_isAffine _
  have hoc (x : S) : IsClopen ((Subtype.val : (f ⁻¹' {x}) → _) ⁻¹' U) := by
    obtain ⟨Q, H, q, j, h, hj⟩ :=
      exists_identityComponent_of_chart_baseChange G i s hs (S.fromSpecResidueField x)
    have hI : IsOpenImmersion j.hom.hom.left := h.openImmersion
    have hC : IsClosedImmersion j.hom.hom.left := h.closedImmersion
    have hc : IsClopen (Set.range j.hom.hom.left) :=
      ⟨j.hom.hom.left.isClosedEmbedding.isClosed_range, j.hom.hom.left.isOpenMap.isOpen_range⟩
    rw [hj] at hc
    let E := f.fiberHomeo x
    convert hc.preimage E.symm.continuous using 1
    ext y
    change y.val ∈ U ↔ f.fiberι x (E.symm y) ∈ U
    rw [f.fiberι_fiberHomeo_symm]
  have hgen : Set.range (pullback.fst f g) ⊆ U := by
    obtain ⟨Q, H, q, j, h, hj⟩ := exists_identityComponent_of_chart_baseChange G i s hs g
    let : ConnectedSpace ((Over.pullback g).mapGrp.obj G).X.left := hGeneric
    have h' : (pullback.fst f g) ⁻¹' U = Set.univ := by
      rw [← hj, h.identityComponent]
      exact Set.eq_univ_of_forall fun _ =>
        isConnected_univ.subset_connectedComponent (Set.mem_univ _) (Set.mem_univ _)
    rintro _ ⟨x, rfl⟩
    exact (h'.symm ▸ Set.mem_univ x : x ∈ (pullback.fst f g) ⁻¹' U)
  obtain ⟨Y, j, hY, hjO, hjR⟩ := exists_affine_open_on_integer_base e f U ho hgen hoc
  let V : Over S := Over.mk (j ≫ f)
  let j₀ : V ⟶ G.X := Over.homMk j rfl
  have hj₀O : IsOpenImmersion j₀.left := hjO
  obtain ⟨grp, j₁, hj₁, hconn⟩ := exists_openSubgroup_of_chart_range G i s hs j₀ hjR
  let H : Grp (Over S) := { X := V, grp := grp }
  have hSmooth : Smooth H.X.hom := inferInstanceAs (Smooth (j ≫ f))
  have hQ : QuasiCompact H.X.hom := by
    have : IsAffine H.X.left := hY
    have : IsAffineHom H.X.hom := isAffineHom_of_isAffine _
    infer_instance
  have hi : Set.range i.left ⊆ U := by
    let l : W ⟶ W ⊗ W := lift (𝟙 W) (toUnit W ≫ s)
    have hl : l ≫ ((i ⊗ₘ i) ≫ μ[G.X]) = i := by
      dsimp only [l]
      rw [lift_map_assoc, Category.id_comp, Category.assoc, hs]
      exact mul_one i
    rintro _ ⟨x, rfl⟩
    exact ⟨l.left x, congrArg (fun a : W ⟶ G.X => a.left x) hl⟩
  let l : W ⟶ V := liftOpenOver j₀ i (hjR.symm ▸ hi)
  have hl : l ≫ j₀ = i := liftOpenOver_fac _ _ _
  have hlO : IsOpenImmersion l.left := by
    have hEq : l.left ≫ j₀.left = i.left := congrArg Over.Hom.left hl
    have hcomp : IsOpenImmersion (l.left ≫ j₀.left) := hEq.symm ▸ inferInstanceAs (IsOpenImmersion i.left)
    exact IsOpenImmersion.of_comp l.left j₀.left
  have hpoint : s ≫ l = η[H.X] := by
    have : Mono j₀ := Over.mono_of_mono_left _
    apply (cancel_mono j₀).mp
    rw [Category.assoc, hl, hs, ← hj₁, IsMonHom.one_hom]
  exact ⟨H, j₁, l, hY, hSmooth, hQ, hconn, hj₁.symm ▸ hj₀O,
    hj₁.symm ▸ hjR, hlO, hj₁.symm ▸ hl, hpoint⟩

end AffineIdentityComponent

section ConnectedGroupFactor

open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
/-- A morphism from a group with geometrically connected fibres takes
values in the open identity subgroup. This applies in particular to the
marked split torus and to each additive root group. -/
theorem exists_factor_through_identityComponent {S : Scheme.{u}}
    {G H : Grp (Over S)} [IsAffineHom G.X.hom] [Smooth G.X.hom] [QuasiCompact G.X.hom]
    {W : Over S} [GeometricallyConnected W.hom] (i : W ⟶ G.X) [IsOpenImmersion i.left]
    (s : 𝟙_ (Over S) ⟶ W) (hs : s ≫ i = η[G.X])
    (j : H ⟶ G) [IsOpenImmersion j.hom.hom.left]
    (hj : Set.range j.hom.hom.left = Set.range ((i ⊗ₘ i) ≫ μ[G.X]).left)
    {P : Grp (Over S)} [GeometricallyConnected P.X.hom] (p : P ⟶ G) :
    ∃ t : P ⟶ H, t ≫ j = p := by
  have h : Set.range p.hom.hom.left ⊆ Set.range j.hom.hom.left := by
    apply range_subset_of_fibres
    intro x
    let f := S.fromSpecResidueField x
    let F := Over.pullback f
    let P' := F.mapGrp.obj P
    let G' := F.mapGrp.obj G
    let p' := F.mapGrp.map p
    have hP : GeometricallyConnected P'.X.hom :=
      inferInstanceAs (GeometricallyConnected (pullback.snd P.X.hom f))
    have hPc : ConnectedSpace P'.X.left :=
      GeometricallyConnected.connectedSpace_of_subsingleton P'.X.hom
    obtain ⟨Q, H₀, q, j₀, hq, heq⟩ := exists_identityComponent_of_chart_baseChange G i s hs f
    let k : Type u := S.residueField x
    let e := Classical.choice (inferInstance : Nonempty (Spec (CommRingCat.of k)))
    have hRange : _root_.IsConnected (Set.range p'.hom.hom.left) := by
      rw [← Set.image_univ]
      exact isConnected_univ.image _ p'.hom.hom.left.continuous.continuousOn
    have hpoint : η[G'.X].left e ∈ Set.range p'.hom.hom.left := by
      refine ⟨η[P'.X].left e, ?_⟩
      exact congrArg (fun a : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G'.X => a.left e)
        (IsMonHom.one_hom (f := p'.hom.hom))
    have hsub : Set.range p'.hom.hom.left ⊆ Set.range j₀.hom.hom.left := by
      rw [hq.identityComponent]
      exact hRange.subset_connectedComponent hpoint
    change Set.range p'.hom.hom.left ⊆ (pullback.fst G.X.hom f) ⁻¹' Set.range j.hom.hom.left
    rw [hj, ← heq]
    exact hsub
  let t := liftOpenOver j.hom.hom p.hom.hom h
  have ht : t ≫ j.hom.hom = p.hom.hom := liftOpenOver_fac _ _ _
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : IsMonHom t := by
    constructor
    · apply (cancel_mono j.hom.hom).mp
      rw [Category.assoc, ht, IsMonHom.one_hom, IsMonHom.one_hom]
    · apply (cancel_mono j.hom.hom).mp
      rw [Category.assoc, ht, IsMonHom.mul_hom (f := p.hom.hom),
        Category.assoc, IsMonHom.mul_hom (f := j.hom.hom), ← Category.assoc,
        MonoidalCategory.tensorHom_comp_tensorHom, ht]
  exact ⟨Grp.homMk t, Grp.hom_ext _ _ ht⟩

end ConnectedGroupFactor

section MatrixClosureIdentityComponent

open CategoryTheory.Limits
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField)
open Specs.IntegralSemisimpleModel (Integers IntegralGroup integerAlgebra)
open Specs.IntegralLattices (Index)
open Specs.OrderedRootProducts (RegularRootCell)

set_option backward.isDefEq.respectTransparency false in
private theorem matrixClosure_genericFibre_connected {R K : Type u}
    [CommRing R] [IsDomain R] [IsBezout R] [Field K] [Algebra R K] [IsFractionRing R K]
    (B : CommHopfAlgCat.{u} K) [Algebra R B] [IsScalarTower R K B] {n : ℕ}
    (ρ : convolutionPoints B ⟶ Specs.StandardGroups.generalLinearPoints K (Index.{u} n))
    (hB : ConnectedSpace (PrimeSpectrum B)) :
    ConnectedSpace ↑(pullback (matrixClosure (R := R) B ρ).X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
  let C := MatrixClosureCoordinates (R := R) B ρ
  let j := Ideal.kerLiftAlg (rationalMatrixCoordinates (R := R) B ρ)
  let jK := AlgHom.liftEquiv R K C B j
  have hjK : Function.Injective jK := fractionField_extension_injective j (Ideal.kerLiftAlg_injective _)
  have hc := connected_spectrum_of_injective (A := K ⊗[R] C) (B := B) jK.toRingHom hjK
  let f := Spec.map (CommRingCat.ofHom (algebraMap R C))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let E := pullbackSymmetry f g ≪≫ pullbackSpecIso R K C
  exact E.hom.homeomorph.connectedSpace_iff.mpr hc

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
private theorem integralMatrixClosure_genericFibre_connected
    (B : CommHopfAlgCat.{u} RationalField.{u}) {n : ℕ}
    (ρ : convolutionPoints B ⟶ Specs.StandardGroups.generalLinearPoints RationalField (Index.{u} n))
    (hB : ConnectedSpace (PrimeSpectrum B)) :
    letI : Algebra Integers.{u} RationalField.{u} := integerAlgebra _
    ConnectedSpace ↑(pullback (integralMatrixClosure B ρ).X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} RationalField.{u})))) := by
  let : IsDomain Integers.{u} :=
    (ULift.ringEquiv : Integers.{u} ≃+* ℤ).toMulEquiv.isDomain ℤ
  let : IsPrincipalIdealRing Integers.{u} := integers_isPrincipalIdealRing
  letI : Algebra Integers.{u} RationalField.{u} := integerAlgebra _
  letI : Algebra Integers.{u} B := integerAlgebra _
  letI : IsFractionRing Integers.{u} RationalField.{u} := integers_isFractionRing
  letI := integers_scalarTower B
  exact matrixClosure_genericFibre_connected B ρ hB

end MatrixClosureIdentityComponent

section IntegralRootCoordinate

open Specs.IntegralLattices (Index ClosedRootImage orderedMatrix triangularEntries)

set_option backward.isDefEq.respectTransparency false in
/-- A parameter of an ordered closed root product can be recovered from the
matrix of that root alone by setting every other parameter to zero. -/
theorem integralRootParameter_from_orderedProduct {n : ℕ} {I : Type u} [DecidableEq I]
    (l : List I) (hn : l.Nodup) (a : I) (ha : a ∈ l) (upper : Bool)
    (p : I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hImage : ClosedRootImage upper (orderedMatrix l p))
    (k : Type u) [CommRing k]
    (hzero : ∀ b, integralPolynomialMatrix (p b) (0 : Polynomial k) = 1) :
    ∃ q : MvPolynomial (triangularEntries n upper) ℤ,
      MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial k))
        (fun ij => integralPolynomialMatrix (p a) Polynomial.X ij.val.1 ij.val.2) q =
        Polynomial.X := by
  let v (b : I) : Polynomial k := if b = a then Polynomial.X else 0
  let f := MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial k)) v
  have hf (b : I) : f (MvPolynomial.X b) = v b := MvPolynomial.eval₂Hom_X' _ _ b
  let P := orderedMatrix l p
  have hP : f.mapMatrix P = integralPolynomialMatrix (p a) (Polynomial.X : Polynomial k) := by
    rw [orderedMatrix_evaluation l p f]
    simp only [hf]
    rw [List.prod_map_eq_pow_single a, List.Nodup.count_of_mem hn ha, pow_one]
    · simp [v]
    · intro b hb _
      simpa only [v, ite_eq_right hb] using hzero b
  obtain ⟨q, hq⟩ := hImage.2.1 a
  refine ⟨q, ?_⟩
  have hh := congrArg f hq
  rw [MvPolynomial.aeval_def, MvPolynomial.hom_eval₂] at hh
  have hc : f.comp (algebraMap ℤ (MvPolynomial I ℤ)) = Int.castRingHom (Polynomial k) :=
    Subsingleton.elim _ _
  have he (ij : triangularEntries n upper) :
      f (P ij.val.1 ij.val.2) = integralPolynomialMatrix (p a) (Polynomial.X : Polynomial k)
        ij.val.1 ij.val.2 := congrFun (congrFun hP ij.val.1) ij.val.2
  change q.eval₂ (f.comp (algebraMap ℤ (MvPolynomial I ℤ)))
    (fun ij => f (P ij.val.1 ij.val.2)) = f (MvPolynomial.X a) at hh
  rw [hc, hf, show v a = Polynomial.X by simp [v]] at hh
  simpa only [he, MvPolynomial.coe_eval₂Hom] using hh

/-- An additive integer matrix polynomial with identity constant term
takes values in the general linear group. -/
def integralRootMatrixUnit {n : ℕ} {R : Type*} [CommRing R]
    (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hzero : integralPolynomialMatrix p (0 : R) = 1)
    (hadd : ∀ x y : R, integralPolynomialMatrix p (x + y) =
      integralPolynomialMatrix p x * integralPolynomialMatrix p y) (x : R) :
    Matrix.GeneralLinearGroup (Index.{u} n) R :=
  ⟨integralPolynomialMatrix p x, integralPolynomialMatrix p (-x),
    (hadd x (-x)).symm.trans (by rwa [add_neg_cancel]),
    (hadd (-x) x).symm.trans (by rwa [neg_add_cancel])⟩

set_option backward.isDefEq.respectTransparency false in
/-- Recovery of the root parameter implies a closed immersion from the
standard affine line into the full matrix group. -/
theorem integralRootCoordinate_isClosedImmersion {n : ℕ} {k : Type u} [CommRing k]
    (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ)) (upper : Bool)
    (hzero : integralPolynomialMatrix p (0 : Polynomial k) = 1)
    (hadd : ∀ x y : Polynomial k, integralPolynomialMatrix p (x + y) =
      integralPolynomialMatrix p x * integralPolynomialMatrix p y)
    (hParameter : ∃ q : MvPolynomial (triangularEntries n upper) ℤ,
      MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial k))
        (fun ij => integralPolynomialMatrix p Polynomial.X ij.val.1 ij.val.2) q =
        Polynomial.X) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (evalGL (k := k) (integralRootMatrixUnit p hzero hadd Polynomial.X)).toRingHom)) := by
  let M := integralRootMatrixUnit p hzero hadd (Polynomial.X : Polynomial k)
  let f := evalGL (k := k) M
  obtain ⟨q, hq⟩ := hParameter
  let g := MvPolynomial.eval₂Hom (Int.castRingHom (MatrixGroupCoordinates k n))
    (fun ij : triangularEntries n upper => universalGLMatrix k n ij.val.1 ij.val.2)
  have hmat := evalGL_universal (k := k) M
  have hf : f (g q) = Polynomial.X := by
    change f.toRingHom (g q) = _
    rw [MvPolynomial.map_eval₂Hom]
    have hconstant : f.toRingHom.comp (Int.castRingHom (MatrixGroupCoordinates k n)) =
        Int.castRingHom (Polynomial k) := Subsingleton.elim _ _
    rw [hconstant]
    have hentry (ij : triangularEntries n upper) :
        f.toRingHom (universalGLMatrix k n ij.val.1 ij.val.2) =
          integralPolynomialMatrix p (Polynomial.X : Polynomial k) ij.val.1 ij.val.2 :=
      congrFun (congrFun hmat ij.val.1) ij.val.2
    simpa only [hentry] using hq
  apply IsClosedImmersion.spec_of_surjective
  intro b
  let a : Polynomial k →ₐ[k] MatrixGroupCoordinates k n := Polynomial.aeval (g q)
  have hfa : f.comp a = AlgHom.id k (Polynomial k) := by
    apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, AlgHom.id_apply]
    exact (congrArg f (Polynomial.aeval_X _)).trans hf
  exact ⟨a b, DFunLike.congr_fun hfa b⟩

end IntegralRootCoordinate

section IntegralClosurePoints

open WithConv
open Specs.IntegralLattices (Index)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
/-- An integral matrix whose scalar extension is a point of the generic
representation factors through the schematic closure, when the coefficient
extension is injective. The factor is surjective on coordinate rings if the
original matrix coordinates are surjective. -/
theorem matrixClosure_factor_of_generic_point {R K : Type u} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (B : CommHopfAlgCat.{u} K) [Algebra R B] [IsScalarTower R K B] {n : ℕ}
    (ρ : convolutionPoints B ⟶ Specs.StandardGroups.generalLinearPoints K (Index.{u} n))
    {A Aₖ : Type u} [CommRing A] [CommRing Aₖ] [Algebra R A] [Algebra R Aₖ]
    [Algebra K Aₖ] [IsScalarTower R K Aₖ]
    (j : A →ₐ[R] Aₖ) (hj : Function.Injective j)
    (f : MatrixGroupCoordinates R n →ₐ[R] A) (x : B →ₐ[K] Aₖ)
    (hx : (j.comp f).mapMatrix (universalGLMatrix R n) =
      (ρ.app (CommAlgCat.of K Aₖ) (toConv x) : Matrix.GeneralLinearGroup (Index.{u} n) Aₖ).val) :
    ∃ g : MatrixClosureCoordinates (R := R) B ρ →ₐ[R] A,
      (∀ q, g (Ideal.Quotient.mk (RingHom.ker (rationalMatrixCoordinates (R := R) B ρ)) q) = f q) ∧
      (Function.Surjective f → Function.Surjective g) := by
  let r := rationalMatrixCoordinates (R := R) B ρ
  have hx' : ((x.restrictScalars R).comp r).mapMatrix (universalGLMatrix R n) =
      (ρ.app (CommAlgCat.of K Aₖ) (toConv x) : Matrix.GeneralLinearGroup (Index.{u} n) Aₖ).val := by
    rw [representation_evaluation B ρ x]
    change x.toRingHom.mapMatrix (r.mapMatrix (universalGLMatrix R n)) =
      x.toRingHom.mapMatrix (matrixAtUniversalPoint B ρ).val
    dsimp only [r]
    rw [rationalMatrixCoordinates, evalGL_universal]
  have hcomp : j.comp f = (x.restrictScalars R).comp r :=
    glAlgHom_ext (hx.trans hx'.symm)
  have hker (q : MatrixGroupCoordinates R n) (hq : q ∈ RingHom.ker r) : f q = 0 := by
    apply hj
    have hh : j (f q) = x (r q) := DFunLike.congr_fun hcomp q
    simp only [RingHom.mem_ker.mp hq, map_zero] at hh ⊢
    exact hh
  let g : MatrixClosureCoordinates (R := R) B ρ →ₐ[R] A :=
    Ideal.Quotient.liftₐ (RingHom.ker r) f hker
  refine ⟨g, fun _ => rfl, ?_⟩
  intro hf a
  obtain ⟨q, rfl⟩ := hf a
  exact ⟨Ideal.Quotient.mk (RingHom.ker r) q, rfl⟩

end IntegralClosurePoints

section AffineTestPoints

variable {k : Type u} [CommRing k]

private theorem affinePoint_ext {X Y : Over (Spec (CommRingCat.of k))}
    (hX : IsAffine X.left) {f g : X ⟶ Y}
    (h : ∀ (R : CommAlgCat.{u} k) (p : affineObject (k := k) R ⟶ X), p ≫ f = p ≫ g) :
    f = g := by
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr hX
  exact (cancel_epi e.hom).mp (h A.unop e.hom)

set_option backward.isDefEq.respectTransparency false in
private theorem isMonHom_of_affine_points {G H : Grp (Over (Spec (CommRingCat.of k)))}
    (hG : IsAffine G.X.left) (f : G.X ⟶ H.X)
    (hOne : ∀ (R : CommAlgCat.{u} k),
      (1 : affineObject (k := k) R ⟶ G.X) ≫ f = 1)
    (hMul : ∀ (R : CommAlgCat.{u} k) (x y : affineObject (k := k) R ⟶ G.X),
      (x * y) ≫ f = (x ≫ f) * (y ≫ f)) :
    IsMonHom f := by
  constructor
  · apply affinePoint_ext (X := 𝟙_ (Over (Spec (CommRingCat.of k)))) (by
      change IsAffine (Spec (CommRingCat.of k))
      infer_instance)
    intro R p
    rw [show p = toUnit _ from toUnit_unique _ _]
    rw [← Category.assoc]
    exact hOne R
  · have : IsAffine G.X.left := hG
    apply affinePoint_ext (X := G.X ⊗ G.X) (by rw [Over.tensorObj_left]; infer_instance)
    intro R p
    let x := p ≫ fst G.X G.X
    let y := p ≫ snd G.X G.X
    have hl : lift (x ≫ f) (y ≫ f) = p ≫ (f ⊗ₘ f) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [x, y]
    calc
      p ≫ μ[G.X] ≫ f = (x * y) ≫ f := by
        rw [← Category.assoc, MonObj.mul_eq_mul, MonObj.comp_mul]
      _ = (x ≫ f) * (y ≫ f) := hMul R x y
      _ = p ≫ (f ⊗ₘ f) ≫ μ[H.X] := by simp only [Hom.mul_def, hl, Category.assoc]

end AffineTestPoints

section RelativeMatrixGroup

open WithConv Algebra.TensorProduct
open Specs.MatrixOpenCell (MatrixGroupCoordinates)

variable {k : Type u} [CommRing k] {n : ℕ}

attribute [local instance] matrixCoordinateHopfAlgebra

private abbrev relativeGL (k : Type u) [CommRing k] (n : ℕ) :
    Grp (Over (Spec (CommRingCat.of k))) :=
  (hopfSpec (CommRingCat.of k)).obj (op (CommHopfAlgCat.of k (MatrixGroupCoordinates k n)))

private def matrixConvolutionEquiv {B : Type u} [CommRing B] [Algebra k B] :
    WithConv (MatrixGroupCoordinates k n →ₐ[k] B) ≃*
      Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) B where
  toEquiv := (WithConv.equiv _).trans matrixCoordinatesEquiv
  map_mul' f g := by
    apply Units.ext
    change ((f * g).ofConv).mapMatrix (universalGLMatrix k n) =
      f.ofConv.mapMatrix (universalGLMatrix k n) * g.ofConv.mapMatrix (universalGLMatrix k n)
    rw [AlgHom.convMul_def]
    change ((lmul' k).comp (Algebra.TensorProduct.map f.ofConv g.ofConv)).mapMatrix
        ((Bialgebra.comulAlgHom k (MatrixGroupCoordinates k n)).mapMatrix
          (universalGLMatrix k n)) = _
    rw [← productMap_eq_comp_map, matrix_comul, map_mul]
    change ((productMap f.ofConv g.ofConv).comp includeLeft).mapMatrix (universalGLMatrix k n) *
      ((productMap f.ofConv g.ofConv).comp includeRight).mapMatrix (universalGLMatrix k n) = _
    rw [productMap_left, productMap_right]

private def relativeGLPointEquiv (B : Type u) [CommRing B] [Algebra k B] :
    (affineObject (k := k) B ⟶ (relativeGL k n).X) ≃*
      Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) B :=
  (Spec.mapMulEquiv (R := k) (S := MatrixGroupCoordinates k n) (T := B)).symm.trans
    matrixConvolutionEquiv

private theorem relativeGLPointEquiv_affineMap {B : Type u} [CommRing B] [Algebra k B]
    (f : MatrixGroupCoordinates k n →ₐ[k] B) :
    (relativeGLPointEquiv B (affineMap f)).val = f.mapMatrix (universalGLMatrix k n) := by
  change (matrixConvolutionEquiv
    ((Spec.mapMulEquiv (R := k) (S := MatrixGroupCoordinates k n) (T := B)).symm
      ((Spec.mapMulEquiv (R := k) (S := MatrixGroupCoordinates k n) (T := B)) (toConv f)))).val = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end RelativeMatrixGroup

section GroupAlgebraEvaluation

variable {k M : Type*} [CommRing k] [CommGroup M]

private def monomialUnits : M →* (MonoidAlgebra k M)ˣ :=
  (MonoidAlgebra.of k M).toHomUnits

private def torusEvaluation {B : Type*} [CommRing B] [Algebra k B] (t : M →* Bˣ) :
    MonoidAlgebra k M →ₐ[k] B :=
  MonoidAlgebra.lift k B M ((Units.coeHom B).comp t)

@[simp]
private theorem torusEvaluation_single {B : Type*} [CommRing B] [Algebra k B]
    (t : M →* Bˣ) (m : M) :
    torusEvaluation (k := k) t (MonoidAlgebra.single m 1) = t m := by
  simp [torusEvaluation, MonoidAlgebra.lift_single]

end GroupAlgebraEvaluation

section MatrixTorus

open WithConv
open Specs.MatrixOpenCell (MatrixGroupCoordinates)

variable {k : Type u} [CommRing k] {M : Type u} [CommGroup M] {n : ℕ}

private abbrev affineTorus (k : Type u) [CommRing k] (M : Type u) [CommGroup M] :
    Grp (Over (Spec (CommRingCat.of k))) :=
  (hopfSpec (CommRingCat.of k)).obj (op (CommHopfAlgCat.of k (MonoidAlgebra k M)))

private def torusConvolutionEquiv (B : Type u) [CommRing B] [Algebra k B] :
    (M →* Bˣ) ≃* WithConv (MonoidAlgebra k M →ₐ[k] B) where
  toFun t := toConv (torusEvaluation t)
  invFun f := (f.ofConv.toMonoidHom.comp (MonoidAlgebra.of k M)).toHomUnits
  left_inv t := by
    ext m : 1
    apply Units.ext
    exact torusEvaluation_single t m
  right_inv f := by
    apply WithConv.ofConv_injective
    apply MonoidAlgebra.algHom_ext
    · intro m
      exact torusEvaluation_single _ m
    · exact Subsingleton.elim _ _
  map_mul' t s := by
    apply WithConv.ofConv_injective
    apply MonoidAlgebra.algHom_ext
    · intro m
      change torusEvaluation (k := k) (t * s) (MonoidAlgebra.single m 1) =
        (toConv (torusEvaluation (k := k) t) * toConv (torusEvaluation (k := k) s))
          (MonoidAlgebra.single m 1)
      rw [AlgHom.convMul_apply, (MonoidAlgebra.isGroupLikeElem_single_one m).comul_eq_tmul_self]
      simp [Algebra.TensorProduct.lift_tmul, MonoidHom.mul_apply]
    · exact Subsingleton.elim _ _

private def affineTorusPointEquiv (B : Type u) [CommRing B] [Algebra k B] :
    (M →* Bˣ) ≃* (affineObject (k := k) B ⟶ (affineTorus k M).X) :=
  (torusConvolutionEquiv (k := k) (M := M) B).trans
    (Spec.mapMulEquiv (R := k) (S := MonoidAlgebra k M) (T := B))

private theorem affineTorusPointEquiv_apply {B : Type u} [CommRing B] [Algebra k B]
    (t : M →* Bˣ) :
    affineTorusPointEquiv B t = affineMap (torusEvaluation (k := k) t) := rfl

private def diagonalMatrixUnit {B : Type u} [CommRing B] (v : ULift.{u} (Fin n) → Bˣ) :
    Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) B :=
  ⟨Matrix.diagonal (fun i => (v i : B)), Matrix.diagonal (fun i => ((v i)⁻¹ : Bˣ).val),
    by rw [Matrix.diagonal_mul_diagonal]; simp,
    by rw [Matrix.diagonal_mul_diagonal]; simp⟩

private def diagonalMatrixCoordinates (w : ULift.{u} (Fin n) → M) :
    MatrixGroupCoordinates k n →ₐ[k] MonoidAlgebra k M :=
  evalGL (diagonalMatrixUnit (monomialUnits (k := k) ∘ w))

private theorem diagonalMatrixCoordinates_spec (w : ULift.{u} (Fin n) → M) :
    (diagonalMatrixCoordinates (k := k) w).mapMatrix (universalGLMatrix k n) =
      Matrix.diagonal (fun i => MonoidAlgebra.single (w i) 1) :=
  evalGL_universal _

set_option backward.isDefEq.respectTransparency false in
private theorem diagonalMatrixPoint_formula (w : ULift.{u} (Fin n) → M)
    {B : Type u} [CommRing B] [Algebra k B] (t : M →* Bˣ) :
    (relativeGLPointEquiv B (affineTorusPointEquiv B t ≫
      affineMap (diagonalMatrixCoordinates (k := k) w))).val =
      Matrix.diagonal (fun i => (t (w i) : B)) := by
  rw [affineTorusPointEquiv_apply, affineMap_comp, relativeGLPointEquiv_affineMap]
  change (torusEvaluation (k := k) t).mapMatrix ((diagonalMatrixCoordinates w).mapMatrix
    (universalGLMatrix k n)) = _
  rw [diagonalMatrixCoordinates_spec]
  ext i j
  by_cases h : i = j <;> simp [h]

set_option backward.isDefEq.respectTransparency false in
private theorem diagonalMatrixMap_isMonHom (w : ULift.{u} (Fin n) → M) :
    IsMonHom (M := (affineTorus k M).X) (N := (relativeGL k n).X)
      (affineMap (diagonalMatrixCoordinates (k := k) w)) := by
  let f : (affineTorus k M).X ⟶ (relativeGL k n).X :=
    affineMap (diagonalMatrixCoordinates (k := k) w)
  have ha : IsAffine (affineTorus k M).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k M))))
  apply isMonHom_of_affine_points (G := affineTorus k M) (H := relativeGL k n) ha f
  · intro R
    apply (relativeGLPointEquiv R).injective
    apply Units.ext
    have he : affineTorusPointEquiv (k := k) (M := M) R (1 : M →* Rˣ) = 1 :=
      map_one (affineTorusPointEquiv (k := k) (M := M) R)
    rw [← he, diagonalMatrixPoint_formula, map_one]
    simp
  · intro R p q
    obtain ⟨t, rfl⟩ := (affineTorusPointEquiv (k := k) (M := M) R).surjective p
    obtain ⟨s, rfl⟩ := (affineTorusPointEquiv (k := k) (M := M) R).surjective q
    apply (relativeGLPointEquiv R).injective
    apply Units.ext
    rw [← map_mul, map_mul (relativeGLPointEquiv R)]
    change (relativeGLPointEquiv R (affineTorusPointEquiv (k := k) (M := M) R (t * s) ≫ f)).val =
      (relativeGLPointEquiv R (affineTorusPointEquiv (k := k) (M := M) R t ≫ f)).val *
        (relativeGLPointEquiv R (affineTorusPointEquiv (k := k) (M := M) R s ≫ f)).val
    dsimp only [f]
    rw [diagonalMatrixPoint_formula, diagonalMatrixPoint_formula, diagonalMatrixPoint_formula,
      Matrix.diagonal_mul_diagonal]
    rfl

end MatrixTorus

section MatrixTorusCoordinates

open Specs.MatrixOpenCell (MatrixGroupCoordinates)
variable {k : Type u} [CommRing k] {M : Type u} [CommGroup M] {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
private theorem diagonalMatrixCoordinates_inverse (w : ULift.{u} (Fin n) → M) :
    (diagonalMatrixCoordinates (k := k) w).toRingHom.mapMatrix
      ((matrixCoordinatesEquiv (AlgHom.id k (MatrixGroupCoordinates k n)))⁻¹).val =
      Matrix.diagonal (fun i => MonoidAlgebra.single ((w i)⁻¹) 1) := by
  let f := diagonalMatrixCoordinates (k := k) w
  let U := matrixCoordinatesEquiv (AlgHom.id k (MatrixGroupCoordinates k n))
  change (Matrix.GeneralLinearGroup.map f.toRingHom U⁻¹).val = _
  rw [map_inv]
  have hU : Matrix.GeneralLinearGroup.map f.toRingHom U =
      diagonalMatrixUnit (monomialUnits (k := k) ∘ w) := by
    apply Units.ext
    exact diagonalMatrixCoordinates_spec w
  rw [hU]
  apply congrArg Matrix.diagonal
  funext i
  change ((monomialUnits (k := k) (w i))⁻¹ : (MonoidAlgebra k M)ˣ).val = _
  rw [← map_inv]
  rfl

private theorem diagonalMatrixCoordinates_range (w : ULift.{u} (Fin n) → M) (i : ULift.{u} (Fin n)) :
    MonoidAlgebra.single (w i) 1 ∈ (diagonalMatrixCoordinates (k := k) w).range ∧
      MonoidAlgebra.single ((w i)⁻¹) 1 ∈ (diagonalMatrixCoordinates (k := k) w).range := by
  exact ⟨⟨universalGLMatrix k n i i,
    (congrFun (congrFun (diagonalMatrixCoordinates_spec (k := k) w) i) i).trans
      (Matrix.diagonal_apply_eq _ _)⟩,
    ⟨((matrixCoordinatesEquiv (AlgHom.id k (MatrixGroupCoordinates k n)))⁻¹).val i i,
      (congrFun (congrFun (diagonalMatrixCoordinates_inverse (k := k) w) i) i).trans
        (Matrix.diagonal_apply_eq _ _)⟩⟩

end MatrixTorusCoordinates

section ClosedMatrixGroup

open Specs.MatrixOpenCell (MatrixGroupCoordinates)
open Specs.IntegralLattices (Index)
open WithConv

attribute [local instance] matrixCoordinateHopfAlgebra

variable {R K : Type u} [CommRing R] [IsDomain R] [IsBezout R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  (B : CommHopfAlgCat.{u} K) [Algebra R B] [IsScalarTower R K B] {n : ℕ}
  (ρ : convolutionPoints B ⟶ Specs.StandardGroups.generalLinearPoints K (Index.{u} n))

/-- The schematic closure sits in the original matrix group via its Hopf quotient. -/
private def matrixClosureEmbedding :
    matrixClosure (R := R) B ρ ⟶ relativeGL R n :=
  let I := RingHom.ker (rationalMatrixCoordinates (R := R) B ρ)
  letI : I.IsHopfIdeal R := matrixClosure_isHopfIdeal (R := R) B ρ
  (hopfSpec (CommRingCat.of R)).map (CommHopfAlgCat.ofHom
    (Bialgebra.Quotient.mkBialgHom (R := R) I)).op

set_option backward.isDefEq.respectTransparency false in
private theorem matrixClosureEmbedding_hom :
    (matrixClosureEmbedding (R := R) B ρ).hom.hom =
      affineMap (Ideal.Quotient.mkₐ R (RingHom.ker (rationalMatrixCoordinates (R := R) B ρ))) :=
  rfl

private theorem matrixClosureEmbedding_isClosedImmersion :
    IsClosedImmersion (matrixClosureEmbedding (R := R) B ρ).hom.hom.left := by
  let I := RingHom.ker (rationalMatrixCoordinates (R := R) B ρ)
  rw [matrixClosureEmbedding_hom]
  change IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  exact IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.mk_surjective (I := I))

set_option backward.isDefEq.respectTransparency false in
private theorem matrixClosure_hasGroupLift {P : Grp (Over (Spec (CommRingCat.of R)))}
    {A : Type u} [CommRing A] [Algebra R A] (a : P.X ⟶ affineObject (k := R) A)
    (f : MatrixGroupCoordinates R n →ₐ[R] A)
    (hf : IsMonHom (a ≫ affineMap f : P.X ⟶ (relativeGL R n).X))
    (g : MatrixClosureCoordinates (R := R) B ρ →ₐ[R] A)
    (hg : ∀ q, g (Ideal.Quotient.mk (RingHom.ker (rationalMatrixCoordinates (R := R) B ρ)) q) = f q) :
    ∃ x : P ⟶ matrixClosure (R := R) B ρ,
      x.hom.hom ≫ (matrixClosureEmbedding (R := R) B ρ).hom.hom = a ≫ affineMap f := by
  let G := matrixClosure (R := R) B ρ
  let i := (matrixClosureEmbedding (R := R) B ρ).hom.hom
  let u : P.X ⟶ G.X := a ≫ affineMap g
  have hi : IsClosedImmersion i.left := matrixClosureEmbedding_isClosedImmersion B ρ
  have hiMono : Mono i := Over.mono_of_mono_left i
  have hiMon : IsMonHom i := inferInstanceAs (IsMonHom (matrixClosureEmbedding (R := R) B ρ).hom.hom)
  let q := Ideal.Quotient.mkₐ R (RingHom.ker (rationalMatrixCoordinates (R := R) B ρ))
  have hfg : g.comp q = f := AlgHom.ext hg
  let p : P.X ⟶ (relativeGL R n).X := a ≫ affineMap f
  have hp : IsMonHom p := hf
  have hcomp : u ≫ i = p := by
    dsimp only [u, i, p]
    rw [matrixClosureEmbedding_hom, Category.assoc, affineMap_comp, hfg]
  have hMon : IsMonHom u := by
    constructor
    · apply (cancel_mono i).mp
      rw [Category.assoc, hcomp, IsMonHom.one_hom, IsMonHom.one_hom]
    · apply (cancel_mono i).mp
      rw [Category.assoc, hcomp, IsMonHom.mul_hom (f := p),
        Category.assoc, IsMonHom.mul_hom (f := i), ← Category.assoc,
        MonoidalCategory.tensorHom_comp_tensorHom, hcomp]
  exact ⟨Grp.homMk u, hcomp⟩

end ClosedMatrixGroup

section PolynomialMatrixGroup

open Specs.IntegralLattices (Index)
open Specs.MatrixOpenCell (MatrixGroupCoordinates)
open Specs.IntegralSemisimpleModel (Integers IntegralAlgebra IntegralPoints additivePoint AdditiveLine)

variable {n : ℕ}
variable (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
  (zeroValue : ∀ (R : Type u) [CommRing R], integralPolynomialMatrix p (0 : R) = 1)
  (addLaw : ∀ (R : Type u) [CommRing R] (x y : R), integralPolynomialMatrix p (x + y) =
    integralPolynomialMatrix p x * integralPolynomialMatrix p y)

private def polynomialMatrixCoordinates :
    MatrixGroupCoordinates Integers.{u} n →ₐ[Integers.{u}] Polynomial Integers.{u} :=
  evalGL (integralRootMatrixUnit p (zeroValue _) (addLaw _) Polynomial.X)

set_option backward.isDefEq.respectTransparency false in
private theorem polynomialMatrixPoint_formula (L : AdditiveLine.{u}) (R : IntegralAlgebra.{u})
    (r : R) :
    let f : L.group.X ⟶ (relativeGL Integers.{u} n).X :=
      affineMap (polynomialMatrixCoordinates p zeroValue addLaw)
    (relativeGLPointEquiv R (additivePoint R r ≫ f)).val = integralPolynomialMatrix p r := by
  dsimp only
  change (relativeGLPointEquiv R (affineMap (Polynomial.aeval r) ≫
    affineMap (polynomialMatrixCoordinates p zeroValue addLaw))).val = _
  rw [affineMap_comp, relativeGLPointEquiv_affineMap]
  change (Polynomial.aeval r).toRingHom.mapMatrix
    ((polynomialMatrixCoordinates p zeroValue addLaw).mapMatrix (universalGLMatrix Integers.{u} n)) = _
  rw [polynomialMatrixCoordinates, evalGL_universal]
  change (Polynomial.aeval r).toRingHom.mapMatrix
      (integralPolynomialMatrix p (Polynomial.X : Polynomial Integers.{u})) = _
  rw [integralPolynomialMatrix_map, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X]

set_option backward.isDefEq.respectTransparency false in
private theorem additivePoint_zero (L : AdditiveLine.{u}) (R : IntegralAlgebra.{u}) :
    letI := L.operations
    additivePoint R 0 = (1 : IntegralPoints L.group R) := by
  let := L.operations
  have h := L.add R 0 0
  rw [zero_add] at h
  exact mul_left_cancel (h.trans (mul_one _).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem polynomialMatrixMap_isMonHom (L : AdditiveLine.{u}) :
    letI := L.operations
    IsMonHom (M := L.group.X) (N := (relativeGL Integers.{u} n).X)
      (affineMap (polynomialMatrixCoordinates p zeroValue addLaw)) := by
  dsimp only
  let := L.operations
  let f : L.group.X ⟶ (relativeGL Integers.{u} n).X :=
    affineMap (polynomialMatrixCoordinates p zeroValue addLaw)
  have ha : IsAffine L.group.X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial Integers.{u}))))
  apply isMonHom_of_affine_points (G := L.group) (H := relativeGL Integers.{u} n) ha f
  · intro R
    apply (relativeGLPointEquiv R).injective
    apply Units.ext
    rw [← additivePoint_zero L R, polynomialMatrixPoint_formula p zeroValue addLaw L, zeroValue]
    exact congrArg Units.val ((relativeGLPointEquiv R).map_one).symm
  · intro R x y
    obtain ⟨r, rfl⟩ := (polynomialPointEquiv R).surjective x
    obtain ⟨s, rfl⟩ := (polynomialPointEquiv R).surjective y
    have hx (c : R) : polynomialPointEquiv R c = additivePoint R c := rfl
    simp only [hx]
    have hm : (additivePoint R r : IntegralPoints L.group R) * additivePoint R s =
        additivePoint R (r + s) := L.add R r s
    rw [hm]
    apply (relativeGLPointEquiv R).injective
    apply Units.ext
    rw [map_mul (relativeGLPointEquiv R)]
    change (relativeGLPointEquiv R (additivePoint R (r + s) ≫ f)).val =
      (relativeGLPointEquiv R (additivePoint R r ≫ f)).val *
        (relativeGLPointEquiv R (additivePoint R s ≫ f)).val
    rw [polynomialMatrixPoint_formula p zeroValue addLaw L R (r + s),
      polynomialMatrixPoint_formula p zeroValue addLaw L R r,
      polynomialMatrixPoint_formula p zeroValue addLaw L R s]
    exact addLaw R r s

end PolynomialMatrixGroup

section IntegralMarkedCoordinates

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField)
open Specs.IntegralSemisimpleModel (Integers IntegralGroup IntegralAlgebra IntegralPoints
  integerAlgebra TorusValues splitTorus torusPoint AdditiveLine additivePoint)
open Specs.IntegralLattices (Index TorusCoordinatesGenerate triangularEntries)
open Specs.MatrixOpenCell (MatrixGroupCoordinates)
open WithConv

variable (B : CommHopfAlgCat.{u} RationalField.{u}) {n : ℕ}
  (ρ : convolutionPoints B ⟶ Specs.StandardGroups.generalLinearPoints RationalField (Index.{u} n))

private def integralMatrixClosureEmbedding :
    integralMatrixClosure B ρ ⟶ relativeGL Integers.{u} n := by
  let : IsDomain Integers.{u} :=
    (ULift.ringEquiv : Integers.{u} ≃+* ℤ).toMulEquiv.isDomain ℤ
  let : IsPrincipalIdealRing Integers.{u} := integers_isPrincipalIdealRing
  let : Algebra Integers.{u} RationalField.{u} := integerAlgebra _
  let : Algebra Integers.{u} B := integerAlgebra _
  let : IsFractionRing Integers.{u} RationalField.{u} := integers_isFractionRing
  let := integers_scalarTower B
  exact matrixClosureEmbedding (R := Integers.{u}) B ρ

private theorem integralMatrixClosureEmbedding_isClosedImmersion :
    IsClosedImmersion (integralMatrixClosureEmbedding B ρ).hom.hom.left := by
  let : IsDomain Integers.{u} :=
    (ULift.ringEquiv : Integers.{u} ≃+* ℤ).toMulEquiv.isDomain ℤ
  let : IsPrincipalIdealRing Integers.{u} := integers_isPrincipalIdealRing
  let : Algebra Integers.{u} RationalField.{u} := integerAlgebra _
  let : Algebra Integers.{u} B := integerAlgebra _
  let : IsFractionRing Integers.{u} RationalField.{u} := integers_isFractionRing
  let := integers_scalarTower B
  exact matrixClosureEmbedding_isClosedImmersion (R := Integers.{u}) B ρ

set_option backward.isDefEq.respectTransparency false in
private theorem exists_integralGroupMap_of_generic_matrix
    {P : IntegralGroup.{u}}
    {C Cₖ : Type u} [CommRing C] [CommRing Cₖ] [Algebra Integers.{u} C] [Algebra RationalField.{u} Cₖ]
    (a : P.X ⟶ affineObject (k := Integers.{u}) C) (f : MatrixGroupCoordinates Integers.{u} n →ₐ[Integers.{u}] C)
    (hf : IsMonHom (M := P.X) (N := (relativeGL Integers.{u} n).X) (a ≫ affineMap f))
    (j : C →+* Cₖ) (hj : Function.Injective j) (x : B →ₐ[RationalField.{u}] Cₖ)
    (hx : j.mapMatrix (f.mapMatrix (universalGLMatrix Integers.{u} n)) =
      (ρ.app (CommAlgCat.of RationalField.{u} Cₖ) (toConv x) :
        Matrix.GeneralLinearGroup (Index.{u} n) Cₖ).val) :
    ∃ p : P ⟶ integralMatrixClosure B ρ,
      p.hom.hom ≫ (integralMatrixClosureEmbedding B ρ).hom.hom = a ≫ affineMap f := by
  let : IsDomain Integers.{u} :=
    (ULift.ringEquiv : Integers.{u} ≃+* ℤ).toMulEquiv.isDomain ℤ
  let : IsPrincipalIdealRing Integers.{u} := integers_isPrincipalIdealRing
  let : Algebra Integers.{u} RationalField.{u} := integerAlgebra _
  let : Algebra Integers.{u} B := integerAlgebra _
  let : Algebra Integers.{u} Cₖ := integerAlgebra _
  let : IsFractionRing Integers.{u} RationalField.{u} := integers_isFractionRing
  let := integers_scalarTower B
  let := integers_scalarTower Cₖ
  let j₀ : C →ₐ[Integers.{u}] Cₖ := overLiftedIntegers j
  obtain ⟨g, hg, _⟩ := matrixClosure_factor_of_generic_point B ρ j₀ hj f x hx
  exact matrixClosure_hasGroupLift B ρ a f hf g hg

set_option backward.isDefEq.respectTransparency false in
/-- An integral polynomial root coordinate of the generic representation
is represented by a closed immersion of the additive group into the closure. -/
theorem exists_integralRoot_in_matrixClosure
    (L : AdditiveLine.{u}) (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (zeroValue : ∀ (R : Type u) [CommRing R], integralPolynomialMatrix p (0 : R) = 1)
    (addLaw : ∀ (R : Type u) [CommRing R] (x y : R), integralPolynomialMatrix p (x + y) =
      integralPolynomialMatrix p x * integralPolynomialMatrix p y)
    (upper : Bool)
    (recover : ∃ q : MvPolynomial (triangularEntries n upper) ℤ,
      MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial Integers.{u}))
        (fun ij => integralPolynomialMatrix p Polynomial.X ij.val.1 ij.val.2) q = Polynomial.X)
    (x : B →ₐ[RationalField.{u}] Polynomial RationalField.{u})
    (hx : (ρ.app (CommAlgCat.of RationalField.{u} (Polynomial RationalField.{u})) (toConv x) :
      Matrix.GeneralLinearGroup (Index.{u} n) (Polynomial RationalField.{u})).val =
        integralPolynomialMatrix p Polynomial.X) :
    ∃ root : L.group ⟶ integralMatrixClosure B ρ,
      IsClosedImmersion root.hom.hom.left ∧
      ∀ (R : IntegralAlgebra.{u}) (z : R),
        (relativeGLPointEquiv R (additivePoint R z ≫ root.hom.hom ≫
          (integralMatrixClosureEmbedding B ρ).hom.hom)).val = integralPolynomialMatrix p z := by
  let f := polynomialMatrixCoordinates p zeroValue addLaw
  let K := RationalField.{u}
  let : Algebra Integers.{u} K := integerAlgebra K
  let j := Polynomial.mapRingHom (algebraMap Integers.{u} K)
  let : IsFractionRing Integers.{u} K := integers_isFractionRing
  have hj : Function.Injective j := Polynomial.map_injective _ (IsFractionRing.injective Integers.{u} K)
  have hmatrix : j.mapMatrix (f.mapMatrix (universalGLMatrix Integers.{u} n)) =
      (ρ.app (CommAlgCat.of K (Polynomial K)) (toConv x) :
        Matrix.GeneralLinearGroup (Index.{u} n) (Polynomial K)).val := by
    rw [hx]
    dsimp only [f]
    rw [polynomialMatrixCoordinates, evalGL_universal]
    change j.mapMatrix (integralPolynomialMatrix p (Polynomial.X : Polynomial Integers.{u})) = _
    rw [integralPolynomialMatrix_map]
    change integralPolynomialMatrix p ((Polynomial.X : Polynomial Integers.{u}).map
      (algebraMap Integers.{u} K)) = _
    rw [Polynomial.map_X]
  let := L.operations
  have hom : IsMonHom (M := L.group.X) (N := (relativeGL Integers.{u} n).X) (𝟙 L.group.X ≫ affineMap f) := by
    rw [Category.id_comp]
    exact polynomialMatrixMap_isMonHom p zeroValue addLaw L
  obtain ⟨root, hroot⟩ := exists_integralGroupMap_of_generic_matrix B ρ (𝟙 L.group.X) f hom j hj x hmatrix
  rw [Category.id_comp] at hroot
  have hi : IsClosedImmersion (integralMatrixClosureEmbedding B ρ).hom.hom.left :=
    integralMatrixClosureEmbedding_isClosedImmersion B ρ
  refine ⟨root, ?_, fun R z => ?_⟩
  · have hc : IsClosedImmersion (root.hom.hom.left ≫ (integralMatrixClosureEmbedding B ρ).hom.hom.left) := by
      rw [← Over.comp_left, hroot]
      exact integralRootCoordinate_isClosedImmersion p upper (zeroValue _) (addLaw _) recover
    exact IsClosedImmersion.of_comp_isClosedImmersion root.hom.hom.left
      (integralMatrixClosureEmbedding B ρ).hom.hom.left
  · rw [hroot]
    exact polynomialMatrixPoint_formula p zeroValue addLaw L R z

end IntegralMarkedCoordinates

section IntegralTorusCoordinates

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField)
open Specs.IntegralLattices (Index TorusCoordinatesGenerate)
open Specs.IntegralSemisimpleModel (Integers IntegralAlgebra TorusValues torusPoint splitTorus)
open WithConv

set_option backward.isDefEq.respectTransparency false in
private theorem integralDiagonalMatrixCoordinates_surjective {D : BasedRootDatum.{u}} {n : ℕ}
    (w : Index.{u} n → D.X) (hw : TorusCoordinatesGenerate w) :
    Function.Surjective (diagonalMatrixCoordinates (k := Integers.{u}) (Multiplicative.ofAdd ∘ w)) := by
  let f := diagonalMatrixCoordinates (k := Integers.{u}) (Multiplicative.ofAdd ∘ w)
  let S := (overIntegers f.toRingHom).range
  let l := AddMonoidAlgebra.mapRingHom D.X (Int.castRingHom Integers.{u})
  let e := AddMonoidAlgebra.toMultiplicativeAlgEquiv Integers.{u} Integers.{u} D.X
  let c := overIntegers (e.toRingHom.comp l)
  have hc : Function.Surjective c := e.surjective.comp
    (AddMonoidAlgebra.map_surjective (Int.castRingHom Integers.{u}).toAddMonoidHom
      (fun r => ⟨r.down, rfl⟩))
  have hs (x : D.X) : c (AddMonoidAlgebra.single x 1) =
      MonoidAlgebra.single (Multiplicative.ofAdd x) 1 := by
    change e (l _) = _
    rw [AddMonoidAlgebra.mapRingHom_single, map_one]
    exact AddMonoidAlgebra.toMultiplicativeAlgEquiv_single (R := Integers.{u}) x 1
  have htop : S.comap c = ⊤ := by
    apply top_unique
    rw [← hw]
    apply Algebra.adjoin_le
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · change c (AddMonoidAlgebra.single (w i) 1) ∈ S
      rw [hs]
      exact (diagonalMatrixCoordinates_range (k := Integers.{u}) (Multiplicative.ofAdd ∘ w) i).1
    · change c (AddMonoidAlgebra.single (-w i) 1) ∈ S
      rw [hs]
      exact (diagonalMatrixCoordinates_range (k := Integers.{u}) (Multiplicative.ofAdd ∘ w) i).2
  intro x
  obtain ⟨y, rfl⟩ := hc x
  have hy : y ∈ S.comap c := htop ▸ Algebra.mem_top
  exact hy

set_option backward.isDefEq.respectTransparency false in
/-- A diagonal representation with the marked characters as weights embeds
the split torus into the integral closure when the weights generate its coordinates. -/
theorem exists_integralTorus_in_matrixClosure {D : BasedRootDatum.{u}} (B : CommHopfAlgCat.{u} RationalField.{u})
    {n : ℕ} (ρ : convolutionPoints B ⟶ Specs.StandardGroups.generalLinearPoints RationalField (Index.{u} n))
    (w : Index.{u} n → D.X) (hw : TorusCoordinatesGenerate w)
    (x : B →ₐ[RationalField.{u}] MonoidAlgebra RationalField.{u} (Multiplicative D.X))
    (hx : (ρ.app (CommAlgCat.of RationalField.{u}
      (MonoidAlgebra RationalField.{u} (Multiplicative D.X))) (toConv x) :
        Matrix.GeneralLinearGroup (Index.{u} n) _).val =
      Matrix.diagonal (fun i => MonoidAlgebra.single (Multiplicative.ofAdd (w i)) 1)) :
    ∃ torus : splitTorus D ⟶ integralMatrixClosure B ρ,
      IsClosedImmersion torus.hom.hom.left ∧
      ∀ (R : IntegralAlgebra.{u}) (t : TorusValues D R),
        (relativeGLPointEquiv R (torusPoint D R t ≫ torus.hom.hom ≫
          (integralMatrixClosureEmbedding B ρ).hom.hom)).val =
          Matrix.diagonal (fun i => (t (Multiplicative.ofAdd (w i)) : R)) := by
  let W := Multiplicative.ofAdd ∘ w
  let f := diagonalMatrixCoordinates (k := Integers.{u}) W
  let K := RationalField.{u}
  let M := Multiplicative D.X
  let : Algebra Integers.{u} K := Specs.IntegralSemisimpleModel.integerAlgebra K
  let : IsFractionRing Integers.{u} K := integers_isFractionRing
  let j := MonoidAlgebra.mapRingHom M (algebraMap Integers.{u} K)
  have hj : Function.Injective j :=
    MonoidAlgebra.map_injective _ (IsFractionRing.injective Integers.{u} K)
  have hmatrix : j.mapMatrix (f.mapMatrix (universalGLMatrix Integers.{u} n)) =
      (ρ.app (CommAlgCat.of K (MonoidAlgebra K M)) (toConv x) :
        Matrix.GeneralLinearGroup (Index.{u} n) (MonoidAlgebra K M)).val := by
    rw [hx]
    dsimp only [f]
    rw [diagonalMatrixCoordinates_spec]
    ext i l
    by_cases h : i = l
    · subst l
      simp [j, W, MonoidAlgebra.mapRingHom_single]
    · simp [h]
  have hom : IsMonHom (M := (splitTorus D).X) (N := (relativeGL Integers.{u} n).X)
      (𝟙 (splitTorus D).X ≫ affineMap f) := by
    rw [Category.id_comp]
    exact diagonalMatrixMap_isMonHom W
  obtain ⟨torus, htorus⟩ := exists_integralGroupMap_of_generic_matrix B ρ (𝟙 (splitTorus D).X)
    f hom j hj x hmatrix
  rw [Category.id_comp] at htorus
  have hi : IsClosedImmersion (integralMatrixClosureEmbedding B ρ).hom.hom.left :=
    integralMatrixClosureEmbedding_isClosedImmersion B ρ
  refine ⟨torus, ?_, fun R t => ?_⟩
  · have hc : IsClosedImmersion (torus.hom.hom.left ≫ (integralMatrixClosureEmbedding B ρ).hom.hom.left) := by
      rw [← Over.comp_left, htorus]
      exact IsClosedImmersion.spec_of_surjective _ (integralDiagonalMatrixCoordinates_surjective w hw)
    exact IsClosedImmersion.of_comp_isClosedImmersion torus.hom.hom.left
      (integralMatrixClosureEmbedding B ρ).hom.hom.left
  · rw [htorus]
    exact diagonalMatrixPoint_formula (k := Integers.{u}) W t

end IntegralTorusCoordinates

section ConnectedMarkings

open CategoryTheory.Limits
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Integers AdditiveLine splitTorus)

set_option backward.isDefEq.respectTransparency false in
private theorem geometricallyConnected_spec_of_tensor_domain {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    (h : ∀ (K : Type u) [Field K] [Algebra R K], IsDomain (K ⊗[R] A)) :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun X : Scheme.{u} => ConnectedSpace X)).mpr
  intro K _ _
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let E := pullbackSymmetry f g ≪≫ pullbackSpecIso R K A
  let : IsDomain (K ⊗[R] A) := h K
  exact E.hom.homeomorph.connectedSpace_iff.mpr
    (inferInstanceAs (ConnectedSpace (PrimeSpectrum (K ⊗[R] A))))

private theorem integralAdditiveLine_geometricallyConnected (L : AdditiveLine.{u}) :
    GeometricallyConnected L.group.X.hom := by
  change GeometricallyConnected
    (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} (Polynomial Integers.{u}))))
  apply geometricallyConnected_spec_of_tensor_domain
  intro K _ _
  let e₀ := MvPolynomial.uniqueAlgEquiv Integers.{u} (PUnit : Type u)
  let e := (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e₀.symm).toRingEquiv.trans
    (MvPolynomial.scalarRTensorAlgEquiv (R := Integers.{u}) (N := K) (σ := (PUnit : Type u))).toRingEquiv
  exact e.toMulEquiv.isDomain _

private theorem integralSplitTorus_geometricallyConnected (D : BasedRootDatum.{u}) :
    GeometricallyConnected (splitTorus D).X.hom := by
  let M := Multiplicative D.X
  change GeometricallyConnected
    (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} (MonoidAlgebra Integers.{u} M))))
  apply geometricallyConnected_spec_of_tensor_domain
  intro K _ _
  let : Module.Free ℤ D.X := D.freeX
  let b := Module.Free.chooseBasis ℤ D.X
  let : UniqueSums D.X := b.repr.toAddEquiv.uniqueSums_iff.mpr inferInstance
  exact (MonoidAlgebra.scalarTensorEquiv Integers.{u} K (M := M)).toRingEquiv.toMulEquiv.isDomain
    (MonoidAlgebra K M)

set_option backward.isDefEq.respectTransparency false in
private theorem exists_closedMap_in_identityComponent {S : Scheme.{u}}
    {G H : Grp (Over S)} [IsAffineHom G.X.hom] [Smooth G.X.hom] [QuasiCompact G.X.hom]
    {W : Over S} [GeometricallyConnected W.hom] (i : W ⟶ G.X) [IsOpenImmersion i.left]
    (s : 𝟙_ (Over S) ⟶ W) (hs : s ≫ i = η[G.X])
    (j : H ⟶ G) [IsOpenImmersion j.hom.hom.left]
    (hj : Set.range j.hom.hom.left = Set.range ((i ⊗ₘ i) ≫ μ[G.X]).left)
    {P : Grp (Over S)} [GeometricallyConnected P.X.hom] (p : P ⟶ G)
    (hp : IsClosedImmersion p.hom.hom.left) :
    ∃ t : P ⟶ H, t ≫ j = p ∧ IsClosedImmersion t.hom.hom.left := by
  obtain ⟨t, ht⟩ := exists_factor_through_identityComponent i s hs j hj p
  have hc : t.hom.hom.left ≫ j.hom.hom.left = p.hom.hom.left :=
    congrArg (fun f : P ⟶ G => f.hom.hom.left) ht
  have : IsClosedImmersion (t.hom.hom.left ≫ j.hom.hom.left) := hc.symm ▸ hp
  exact ⟨t, ht, IsClosedImmersion.of_comp t.hom.hom.left j.hom.hom.left⟩

end ConnectedMarkings

section RationalRootLaw

open _root_.LinearAlgebraicGroups.Specs (GroupScheme)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.RootGroups (AdditiveLine rootPoint)
open WithConv

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false in
private theorem rootPoint_additive {A : AdditiveLine k} {G : GroupScheme k}
    (q : A.group ⟶ G) (R : TestAlgebra k) (a b : R) :
    rootPoint q R (a + b) = rootPoint q R a * rootPoint q R b := by
  let := A.operations.hopf
  let f (c : R) : WithConv (Polynomial k →ₐ[k] R) := toConv (Polynomial.aeval c)
  have hf : f (a + b) = f a * f b := by
    apply WithConv.ofConv_injective
    apply Polynomial.algHom_ext
    change Polynomial.aeval (a + b) Polynomial.X = (f a * f b) Polynomial.X
    rw [Polynomial.aeval_X, AlgHom.convMul_apply,
      show Coalgebra.comul (R := k) (Polynomial.X : Polynomial k) =
        Polynomial.X ⊗ₜ[k] 1 + 1 ⊗ₜ[k] Polynomial.X from A.comultiplication]
    simp [f, Algebra.TensorProduct.lift_tmul]
  let e := Spec.mapMulEquiv (R := k) (S := Polynomial k) (T := R)
  let v (c : R) : GroupPoints A.group R := e (f c)
  have hv : v (a + b) = v a * v b := (congrArg e hf).trans (map_mul e _ _)
  change v (a + b) ≫ q.hom.hom = _
  rw [hv, MonObj.mul_comp]
  rfl

end RationalRootLaw

section IntegralTorusConjugation

open Specs.IntegralLattices (Index)
open Specs.RationalRealization (RationalField)

variable {M : Type u} [CommGroup M] {n : ℕ}

private def torusWeightMatrix {R : Type u} [CommRing R]
    (w : Index.{u} n → M) (t : M →* Rˣ) : Matrix (Index.{u} n) (Index.{u} n) R :=
  Matrix.diagonal (fun i => (t (w i) : R))

private theorem torusWeightMatrix_map {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (w : Index.{u} n → M) (t : M →* Rˣ) :
    f.mapMatrix (torusWeightMatrix w t) = torusWeightMatrix w ((Units.map f.toMonoidHom).comp t) := by
  ext i j
  by_cases h : i = j <;> simp [torusWeightMatrix, h]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The diagonal conjugation identity over all rational test rings descends
to the integral matrix polynomials and then to arbitrary test rings. -/
theorem integralPolynomialMatrix_torusLaw_of_generic
    (w : Index.{u} n → M) (χ : M) (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (h : ∀ (R : TestAlgebra RationalField.{u}) (t : M →* Rˣ) (x : R),
      torusWeightMatrix w t * integralPolynomialMatrix p x =
        integralPolynomialMatrix p ((t χ : R) * x) * torusWeightMatrix w t)
    (R : Type u) [CommRing R] (t : M →* Rˣ) (x : R) :
    torusWeightMatrix w t * integralPolynomialMatrix p x =
      integralPolynomialMatrix p ((t χ : R) * x) * torusWeightMatrix w t := by
  let A := Polynomial (MonoidAlgebra ℤ M)
  let B := Polynomial (MonoidAlgebra RationalField.{u} M)
  let v : M →* Aˣ := (Units.map Polynomial.C.toMonoidHom).comp (monomialUnits (k := ℤ))
  let z : A := Polynomial.X
  let f : A →+* B := Polynomial.mapRingHom (MonoidAlgebra.mapRingHom M (Int.castRingHom RationalField.{u}))
  have hf : Function.Injective f := Polynomial.map_injective _
    (MonoidAlgebra.map_injective _ rationalField_intCast_injective)
  have hu : torusWeightMatrix w v * integralPolynomialMatrix p z =
      integralPolynomialMatrix p ((v χ : A) * z) * torusWeightMatrix w v := by
    have he := h (CommAlgCat.of RationalField.{u} B) ((Units.map f.toMonoidHom).comp v) (f z)
    have he' : f.mapMatrix (torusWeightMatrix w v * integralPolynomialMatrix p z) =
        f.mapMatrix (integralPolynomialMatrix p ((v χ : A) * z) * torusWeightMatrix w v) := by
      rw [map_mul, map_mul, torusWeightMatrix_map (R := A) (S := B) f w v,
        integralPolynomialMatrix_map (R := A) (S := B) f p z, integralPolynomialMatrix_map (R := A) (S := B) f p ((v χ : A) * z),
        map_mul]
      exact he
    exact Matrix.ext fun i j => hf (congrFun (congrFun he' i) j)
  let fR : A →+* R := Polynomial.eval₂RingHom (torusEvaluation (k := ℤ) t).toRingHom x
  have hv : (Units.map fR.toMonoidHom).comp v = t := by
    ext m : 1
    apply Units.ext
    change (MonoidAlgebra.single m 1 |> Polynomial.C |> fR) = (t m : R)
    exact (Polynomial.eval₂_C _ _).trans (torusEvaluation_single t m)
  have hz : fR z = x := Polynomial.eval₂_X _ _
  have he := congrArg fR.mapMatrix hu
  rw [map_mul, map_mul, torusWeightMatrix_map (R := A) (S := R) fR w v,
    integralPolynomialMatrix_map (R := A) (S := R) fR p z, integralPolynomialMatrix_map (R := A) (S := R) fR p ((v χ : A) * z),
    map_mul, hv, hz] at he
  have hχ := congrArg (fun t' : M →* Rˣ => (t' χ : R)) hv
  change fR (v χ : A) = (t χ : R) at hχ
  rwa [hχ] at he

end IntegralTorusConjugation

section LatticeMarkings

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates)
open Specs.IntegralLattices
  (Index Positive Negative RationalHighestWeight dividedPower ClosedRootImage orderedMatrix
    triangularEntries TorusCoordinatesGenerate)
open Specs.IntegralSemisimpleModel
  (Integers IntegralAlgebra splitTorus torusPoint TorusValues additivePoint)
open Specs.OrderedRootProducts (Enumerates)
open Specs.CharacterPairing (characterValue)
open Specs.DiagonalizableGroups (groupAlgebra)
open _root_.LinearAlgebraicGroups.Specs (Lie)
open WithConv

variable {D : BasedRootDatum.{u}} {A : Specs.RootGroups.AdditiveLine RationalField.{u}}
  {Q : Realization D A}
  [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {z : RootCoordinates Q}
  {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
  [DecidableEq D.base.support] {ω : D.base.support → D.X}
  (V : ∀ i, RationalHighestWeight z e h (ω i)) {n : ℕ}
  (b : Module.Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))

set_option backward.isDefEq.respectTransparency false in
private theorem latticeRootMatrix_laws (a : D.I)
    (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hp : ∀ (m : ℕ) (j : Index.{u} n) (i : D.base.support),
      ∑ l : Index.{u} n, ((p l j).coeff m : RationalField.{u}) • b l i =
        (dividedPower ((V i).rootOperator a) m).mulVec (b j i)) :
    (∀ (R : Type u) [CommRing R], integralPolynomialMatrix p (0 : R) = 1) ∧
      ∀ (R : Type u) [CommRing R] (x y : R), integralPolynomialMatrix p (x + y) =
        integralPolynomialMatrix p x * integralPolynomialMatrix p y := by
  let ρ := rationalMatrixAction V b
  let q := (z a).val.hom ≫ (Q.pinned.roots (Q.datumIso.val.indexEquiv a)).val.inclusion
  have hx (R : TestAlgebra RationalField.{u}) (x : R) :
      ((ρ.app R (Specs.RootGroups.rootPoint q R x)) :
        Matrix.GeneralLinearGroup (Index.{u} n) R).val = integralPolynomialMatrix p x :=
    rationalMatrixAction_root V b a p hp R x
  let R₀ := CommAlgCat.of RationalField.{u} RationalField.{u}
  have h₀ : Specs.RootGroups.rootPoint q R₀ 0 = 1 := by
    have he := (rootPoint_additive q R₀ 0 0).symm
    rw [zero_add] at he
    exact mul_left_cancel (he.trans (mul_one _).symm)
  constructor
  · apply integralPolynomialMatrix_zero_of_generic p
    rw [← hx R₀, h₀, map_one]
    rfl
  · apply integralPolynomialMatrix_add_of_generic p
    intro R x y
    rw [← hx R (x + y), ← hx R x, ← hx R y, rootPoint_additive, map_mul]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 950000 in
/-- The characters and root polynomials of the chosen fundamental
lattices yield closed integral markings in the same matrix closure. -/
private theorem exists_integralMarkings_of_lattices
    (negative : List (Negative D)) (positive : List (Positive D))
    (hnl : Enumerates negative Set.univ) (hpl : Enumerates positive Set.univ)
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hcoeff : ∀ (a : D.I) (m : ℕ) (j : Index.{u} n) (i : D.base.support),
      ∑ l : Index.{u} n, ((p a l j).coeff m : RationalField.{u}) • b l i =
        (dividedPower ((V i).rootOperator a) m).mulVec (b j i))
    (hneg : ClosedRootImage false (orderedMatrix negative (fun a => p a.val)))
    (hpos : ClosedRootImage true (orderedMatrix positive (fun a => p a.val)))
    (w : Index.{u} n → D.X)
    (weight : ∀ j i, b j i ∈ (V i).weightSpace (w j))
    (hw : TorusCoordinatesGenerate w)
    (B : CommHopfAlgCat.{u} RationalField.{u}) (ε : specGroup B ≅ Q.pinned.pair.G.val)
    (τ : specGroup (groupAlgebra RationalField.{u} (Multiplicative D.X)) ≅ Q.pinned.pair.T.group)
    (hτ : ∀ (R : TestAlgebra RationalField.{u})
        (t : MonoidAlgebra RationalField.{u} (Multiplicative D.X) →ₐ[RationalField.{u}] R) (x : D.X),
        characterValue (Additive.toMul (Q.datumIso.val.weightEquiv x)) R
          (affineMap t ≫ τ.hom.hom.hom) = t (MonoidAlgebra.single (Multiplicative.ofAdd x) 1)) :
    let ρ := representationOnHopfPoints B ε (rationalMatrixAction V b)
    let G := integralMatrixClosure B ρ
    let i := (integralMatrixClosureEmbedding B ρ).hom.hom
    ∃ (torus : splitTorus D ⟶ G) (root : D.I → (integralAdditiveLine.group ⟶ G)),
      IsClosedImmersion torus.hom.hom.left ∧
      (∀ a, IsClosedImmersion (root a).hom.hom.left) ∧
      (∀ (R : IntegralAlgebra.{u}) (t : TorusValues D R),
        (relativeGLPointEquiv R (torusPoint D R t ≫ torus.hom.hom ≫ i)).val =
          Matrix.diagonal (fun j => (t (Multiplicative.ofAdd (w j)) : R))) ∧
      ∀ (a : D.I) (R : IntegralAlgebra.{u}) (x : R),
        (relativeGLPointEquiv R (additivePoint R x ≫ (root a).hom.hom ≫ i)).val =
          integralPolynomialMatrix (p a) x := by
  classical
  let ρ₀ := rationalMatrixAction V b
  let ρ := representationOnHopfPoints B ε ρ₀
  let R := CommAlgCat.of RationalField.{u} (MonoidAlgebra RationalField.{u} (Multiplicative D.X))
  let t := AlgHom.id RationalField.{u} R
  let q := (affineMap t ≫ τ.hom.hom.hom) ≫ Q.pinned.pair.T.inclusion.hom.hom
  let cq := restrictGroupCoordinates B ε q
  have hq : (ρ.app R (toConv cq) : Matrix.GeneralLinearGroup (Index.{u} n) R).val =
      Matrix.diagonal (fun i => MonoidAlgebra.single (Multiplicative.ofAdd (w i)) 1) := by
    change ((representationOnHopfPoints B ε ρ₀).app R (toConv cq) :
      Matrix.GeneralLinearGroup (Index.{u} n) R).val = _
    rw [representationOnHopfPoints_apply, restrictGroupCoordinates_point]
    change ((ρ₀.app R q) : Matrix.GeneralLinearGroup (Index.{u} n) R).val = _
    dsimp only [q, ρ₀]
    rw [rationalMatrixAction_torus V b w weight]
    exact congrArg Matrix.diagonal (funext fun j => hτ R t (w j))
  obtain ⟨torus, htorus, ht⟩ := exists_integralTorus_in_matrixClosure B ρ w hw cq hq
  have hz (a : D.I) (S : Type u) [CommRing S] : integralPolynomialMatrix (p a) (0 : S) = 1 :=
    (latticeRootMatrix_laws V b a (p a) (hcoeff a)).1 S
  have ha (a : D.I) (S : Type u) [CommRing S] (x y : S) :
      integralPolynomialMatrix (p a) (x + y) =
        integralPolynomialMatrix (p a) x * integralPolynomialMatrix (p a) y :=
    (latticeRootMatrix_laws V b a (p a) (hcoeff a)).2 S x y
  have hroot (a : D.I) :
      ∃ root : integralAdditiveLine.group ⟶ integralMatrixClosure B ρ,
        IsClosedImmersion root.hom.hom.left ∧ ∀ (S : IntegralAlgebra.{u}) (x : S),
          (relativeGLPointEquiv S (additivePoint S x ≫ root.hom.hom ≫
            (integralMatrixClosureEmbedding B ρ).hom.hom)).val =
          integralPolynomialMatrix (p a) x := by
    obtain ⟨upper, hrec⟩ : ∃ upper : Bool, ∃ q : MvPolynomial (triangularEntries n upper) ℤ,
        MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial Integers.{u}))
          (fun ij => integralPolynomialMatrix (p a) Polynomial.X ij.val.1 ij.val.2) q =
          Polynomial.X := by
      by_cases h : D.base.IsPos a
      · let α : Positive D := ⟨a, h⟩
        have hm : α ∈ positive := (hpl.2 α).mpr (Set.mem_univ α)
        exact ⟨true, integralRootParameter_from_orderedProduct positive hpl.1 α hm true
          (fun i => p i.val) hpos Integers.{u} (fun i => hz i.val _)⟩
      · let α : Negative D := ⟨a, h⟩
        have hm : α ∈ negative := (hnl.2 α).mpr (Set.mem_univ α)
        exact ⟨false, integralRootParameter_from_orderedProduct negative hnl.1 α hm false
          (fun i => p i.val) hneg Integers.{u} (fun i => hz i.val _)⟩
    let S := CommAlgCat.of RationalField.{u} (Polynomial RationalField.{u})
    let q := Specs.IntegralRootRelations.root Q z a S Polynomial.X
    let c := restrictGroupCoordinates B ε q
    apply exists_integralRoot_in_matrixClosure B ρ integralAdditiveLine (p a) (hz a) (ha a) upper hrec c
    change ((representationOnHopfPoints B ε ρ₀).app S (toConv c) :
      Matrix.GeneralLinearGroup (Index.{u} n) S).val = _
    rw [representationOnHopfPoints_apply, restrictGroupCoordinates_point]
    exact rationalMatrixAction_root V b a (p a) (hcoeff a) S Polynomial.X
  choose root hclosed hmat using hroot
  exact ⟨torus, root, htorus, hclosed, ht, hmat⟩

end LatticeMarkings

section LatticeConjugation

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralRootRelations (RootCoordinates)
open Specs.IntegralLattices (Index RationalHighestWeight dividedPower)
open Specs.CharacterPairing (characterValue)
open Specs.DiagonalizableGroups (groupAlgebra)
open Specs.AdjointRepresentation (GroupPoints)
open _root_.LinearAlgebraicGroups.Specs (Lie)

variable {D : BasedRootDatum.{u}} {A : Specs.RootGroups.AdditiveLine RationalField.{u}}
  {Q : Realization D A}
  [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
  [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
  {z : RootCoordinates Q}
  {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
  [DecidableEq D.base.support] {ω : D.base.support → D.X}
  (V : ∀ i, RationalHighestWeight z e h (ω i)) {n : ℕ}
  (b : Module.Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
private theorem latticeRootMatrix_torusLaw
    (w : Index.{u} n → D.X) (weight : ∀ j i, b j i ∈ (V i).weightSpace (w j))
    (a : D.I) (p : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hp : ∀ (m : ℕ) (j : Index.{u} n) (i : D.base.support),
      ∑ l : Index.{u} n, ((p l j).coeff m : RationalField.{u}) • b l i =
        (dividedPower ((V i).rootOperator a) m).mulVec (b j i))
    (τ : specGroup (groupAlgebra RationalField.{u} (Multiplicative D.X)) ≅ Q.pinned.pair.T.group)
    (hτ : ∀ (R : TestAlgebra RationalField.{u})
        (t : MonoidAlgebra RationalField.{u} (Multiplicative D.X) →ₐ[RationalField.{u}] R) (x : D.X),
        characterValue (Additive.toMul (Q.datumIso.val.weightEquiv x)) R
          (affineMap t ≫ τ.hom.hom.hom) = t (MonoidAlgebra.single (Multiplicative.ofAdd x) 1))
    (R : Type u) [CommRing R] (t : Multiplicative D.X →* Rˣ) (x : R) :
    torusWeightMatrix (Multiplicative.ofAdd ∘ w) t * integralPolynomialMatrix p x =
      integralPolynomialMatrix p ((t (Multiplicative.ofAdd (D.datum.root a)) : R) * x) *
        torusWeightMatrix (Multiplicative.ofAdd ∘ w) t := by
  apply integralPolynomialMatrix_torusLaw_of_generic
  intro S t' x'
  let t₁ := torusEvaluation (k := RationalField.{u}) t'
  let t₀ : GroupPoints Q.pinned.pair.T.group S := affineMap t₁ ≫ τ.hom.hom.hom
  let g : GroupPoints Q.pinned.pair.G.val S := t₀ ≫ Q.pinned.pair.T.inclusion.hom.hom
  let q := (z a).val.hom ≫ (Q.pinned.roots (Q.datumIso.val.indexEquiv a)).val.inclusion
  let α := (Q.datumIso.val.indexEquiv a).val
  let := Q.attached.comm
  have hRoot : Additive.toMul (Q.datumIso.val.weightEquiv (D.datum.root a)) = α := by
    change Additive.toMul (Q.datumIso.val.toHom.weightMap (D.datum.root a)) = _
    rw [RootPairing.Hom.root_weightMap_apply]
    exact congrArg Additive.toMul (Q.attached.datum.root_eq _)
  have hχ (χ : D.X) : characterValue (Additive.toMul (Q.datumIso.val.weightEquiv χ)) S t₀ =
      (t' (Multiplicative.ofAdd χ) : S) :=
    (hτ S t₁ χ).trans (torusEvaluation_single t' _)
  have hα : characterValue α S t₀ = (t' (Multiplicative.ofAdd (D.datum.root a)) : S) :=
    hRoot ▸ hχ (D.datum.root a)
  have hconj := (z a).property S t₀ x'
  change g * Specs.RootGroups.rootPoint q S x' * g⁻¹ =
    Specs.RootGroups.rootPoint q S (characterValue α S t₀ * x') at hconj
  have hmul : g * Specs.RootGroups.rootPoint q S x' =
      Specs.RootGroups.rootPoint q S ((t' (Multiplicative.ofAdd (D.datum.root a)) : S) * x') * g := by
    rw [← hα]
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using congrArg (· * g) hconj
  let ρ := (rationalMatrixAction V b).app S
  have hmat (y : S) : (ρ (Specs.RootGroups.rootPoint q S y) :
      Matrix.GeneralLinearGroup (Index.{u} n) S).val = integralPolynomialMatrix p y :=
    rationalMatrixAction_root V b a p hp S y
  have hd : (ρ g : Matrix.GeneralLinearGroup (Index.{u} n) S).val =
      torusWeightMatrix (Multiplicative.ofAdd ∘ w) t' := by
    change ((rationalMatrixAction V b).app S (t₀ ≫ Q.pinned.pair.T.inclusion.hom.hom) :
      Matrix.GeneralLinearGroup (Index.{u} n) S).val = _
    rw [rationalMatrixAction_torus V b w weight]
    exact congrArg Matrix.diagonal (funext fun i => hχ (w i))
  have hm := congrArg (fun z => (ρ z : Matrix.GeneralLinearGroup (Index.{u} n) S).val) hmul
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, hd, hmat, hmat] at hm
  exact hm

end LatticeConjugation

section MarkedScalarAction

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralLattices (Index)
open Specs.IntegralSemisimpleModel (Integers IntegralGroup IntegralAlgebra IntegralPoints
  splitTorus torusPoint TorusValues AdditiveLine additivePoint)

set_option backward.isDefEq.respectTransparency false in
private theorem markedRootConjugation_of_matrix_law {D : BasedRootDatum.{u}} {n : ℕ}
    {G : IntegralGroup.{u}} (i : G ⟶ relativeGL Integers.{u} n) [Mono i.hom.hom]
    (L : AdditiveLine.{u}) (torus : splitTorus D ⟶ G) (root : D.I → (L.group ⟶ G))
    (w : Index.{u} n → D.X) (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (ht : ∀ (R : IntegralAlgebra.{u}) (t : TorusValues D R),
      (relativeGLPointEquiv R (torusPoint D R t ≫ torus.hom.hom ≫ i.hom.hom)).val =
        torusWeightMatrix (Multiplicative.ofAdd ∘ w) t)
    (hr : ∀ (a : D.I) (R : IntegralAlgebra.{u}) (z : R),
      (relativeGLPointEquiv R (additivePoint R z ≫ (root a).hom.hom ≫ i.hom.hom)).val =
        integralPolynomialMatrix (p a) z)
    (hm : ∀ (a : D.I) (R : IntegralAlgebra.{u}) (t : TorusValues D R) (z : R),
      torusWeightMatrix (Multiplicative.ofAdd ∘ w) t * integralPolynomialMatrix (p a) z =
        integralPolynomialMatrix (p a) ((t (Multiplicative.ofAdd (D.datum.root a)) : R) * z) *
          torusWeightMatrix (Multiplicative.ofAdd ∘ w) t) :
    ∀ (R : IntegralAlgebra.{u}) (t : TorusValues D R) (a : D.I) (z : R),
      let g := torusPoint D R t ≫ torus.hom.hom
      g * (L.point R z ≫ (root a).hom.hom) * g⁻¹ =
        L.point R ((t (Multiplicative.ofAdd (D.datum.root a)) : R) * z) ≫ (root a).hom.hom := by
  intro R t a z
  let g : IntegralPoints G R := torusPoint D R t ≫ torus.hom.hom
  let x (v : R) : IntegralPoints G R := additivePoint R v ≫ (root a).hom.hom
  let z' := (t (Multiplicative.ofAdd (D.datum.root a)) : R) * z
  have h : g * x z = x z' * g := by
    apply (cancel_mono i.hom.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp]
    apply (relativeGLPointEquiv R).injective
    apply Units.ext
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
    dsimp only [g, x]
    simp only [Category.assoc, ht R t, hr a R z, hr a R z']
    exact hm a R t z
  change g * x z * g⁻¹ = x z'
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

end MarkedScalarAction

section MarkedOpenCell

open Specs.IntegralSemisimpleModel (Integers IntegralGroup IntegralAlgebra IntegralPoints IntegralScheme
  AdditiveLine splitTorus TorusValues torusPoint additivePoint cellMap rootProduct product)
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralLattices (Index)
open Specs.OrderedRootProducts (Enumerates)

private abbrev IntegralMarkedCellCoordinates (D : BasedRootDatum.{u}) :=
  MvPolynomial D.I (MonoidAlgebra Integers.{u} (Multiplicative D.X))

private def integralRootFactorsIso (L : AdditiveLine.{u}) {I : Type u} :
    (l : List I) → orderedFactors (fun _ : I => L.group.X) l ≅ product (fun _ : I => L.group.X) l
  | [] => Iso.refl _
  | _ :: l => MonoidalCategory.tensorIso (Iso.refl _) (integralRootFactorsIso L l)

set_option backward.isDefEq.respectTransparency false in
private theorem integralRootProduct_evaluation {D : BasedRootDatum.{u}} {G : IntegralGroup.{u}}
    (L : AdditiveLine.{u}) (root : D.I → (L.group ⟶ G))
    {R : IntegralAlgebra.{u}} (v : D.I → R) (l : List D.I) :
    orderedFactorPoint (fun a => additivePoint R (v a)) l ≫
      (integralRootFactorsIso L l).hom ≫ rootProduct L root l =
      (l.map (fun a => additivePoint R (v a) ≫ (root a).hom.hom)).prod := by
  induction l with
  | nil =>
    change toUnit _ ≫ 𝟙 _ ≫ (1 : 𝟙_ IntegralScheme.{u} ⟶ G.X) = 1
    rw [Category.id_comp, MonObj.comp_one]
  | cons a l ih =>
    let T := product (fun _ : D.I => L.group.X) l
    change lift (additivePoint R (v a)) (orderedFactorPoint (fun b => additivePoint R (v b)) l) ≫
      (𝟙 _ ⊗ₘ (integralRootFactorsIso L l).hom) ≫
      ((fst L.group.X T ≫ (root a).hom.hom) * (snd L.group.X T ≫ rootProduct L root l)) =
      (additivePoint R (v a) ≫ (root a).hom.hom) *
        (l.map (fun a => additivePoint R (v a) ≫ (root a).hom.hom)).prod
    rw [lift_map_assoc, Category.comp_id, lift_mul_factors, Category.assoc, ih]

private def integralCellParameters (D : BasedRootDatum.{u}) :
    TorusValues D (CommAlgCat.of Integers.{u} (IntegralMarkedCellCoordinates D)) :=
  (Units.map (MvPolynomial.C :
    MonoidAlgebra Integers.{u} (Multiplicative D.X) →+* IntegralMarkedCellCoordinates D).toMonoidHom).comp
    monomialUnits

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem integralCellParameters_point (D : BasedRootDatum.{u}) :
    torusPoint D (CommAlgCat.of Integers.{u} (IntegralMarkedCellCoordinates D)) (integralCellParameters D) =
      affineMap (IsScalarTower.toAlgHom Integers.{u}
        (MonoidAlgebra Integers.{u} (Multiplicative D.X)) (IntegralMarkedCellCoordinates D)) := by
  let R := CommAlgCat.of Integers.{u} (IntegralMarkedCellCoordinates D)
  let t := torusEvaluation (k := Integers.{u}) (B := R) (integralCellParameters D)
  let c := IsScalarTower.toAlgHom Integers.{u}
    (MonoidAlgebra Integers.{u} (Multiplicative D.X)) (IntegralMarkedCellCoordinates D)
  have h : t = c := by
    apply MonoidAlgebra.algHom_ext
    · intro a
      dsimp only [t]
      rw [torusEvaluation_single]
      rfl
    · exact Subsingleton.elim _ _
  apply Over.OverMorphism.ext
  have he := congrArg (fun q : MonoidAlgebra Integers.{u} (Multiplicative D.X) →ₐ[Integers.{u}]
      IntegralMarkedCellCoordinates D => Spec.map (CommRingCat.ofHom
        (R := MonoidAlgebra Integers.{u} (Multiplicative D.X)) (S := IntegralMarkedCellCoordinates D)
        q.toRingHom)) h
  exact he

private def integralCellCoordinateMap {D : BasedRootDatum.{u}} (L : AdditiveLine.{u})
    (negative positive : List D.I) :
    affineObject (k := Integers.{u}) (IntegralMarkedCellCoordinates D) ⟶
      product (fun _ : D.I => L.group.X) negative ⊗
        ((splitTorus D).X ⊗ product (fun _ : D.I => L.group.X) positive) :=
  splitCellCoordinateMap (k := Integers.{u}) (X := fun _ : D.I => L.group.X)
    (Y := (splitTorus D).X) (M := MonoidAlgebra Integers.{u} (Multiplicative D.X))
    (fun _ => Iso.refl _) (Iso.refl _) negative positive ≫
      ((integralRootFactorsIso L negative).hom ⊗ₘ
        (𝟙 (splitTorus D).X ⊗ₘ (integralRootFactorsIso L positive).hom))

set_option backward.isDefEq.respectTransparency false in
private theorem integralCellCoordinateMap_isIso {D : BasedRootDatum.{u}} (L : AdditiveLine.{u})
    (negative positive : List D.I)
    (hneg : Enumerates negative {a | ¬ D.base.IsPos a})
    (hpos : Enumerates positive {a | D.base.IsPos a}) :
    IsIso (integralCellCoordinateMap L negative positive) := by
  classical
  have hi : IsIso (splitCellCoordinateMap (k := Integers.{u}) (X := fun _ : D.I => L.group.X)
      (Y := (splitTorus D).X) (M := MonoidAlgebra Integers.{u} (Multiplicative D.X))
      (fun _ => Iso.refl _) (Iso.refl _) negative positive) := by
    apply splitCellCoordinateMap_isIso _ _ _ _ hneg.1 hpos.1
    · intro a
      by_cases ha : D.base.IsPos a
      · exact Or.inr ((hpos.2 a).mpr ha)
      · exact Or.inl ((hneg.2 a).mpr ha)
    · intro a hm hn
      exact (hneg.2 a).mp hm ((hpos.2 a).mp hn)
  unfold integralCellCoordinateMap
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem integralCellMap_point {D : BasedRootDatum.{u}} {G : IntegralGroup.{u}}
    (L : AdditiveLine.{u}) (torus : splitTorus D ⟶ G) (root : D.I → (L.group ⟶ G))
    (negative positive : List D.I) :
    let R := CommAlgCat.of Integers.{u} (IntegralMarkedCellCoordinates D)
    let V (l : List D.I) : IntegralPoints G R :=
      (l.map (fun a => additivePoint R (MvPolynomial.X a) ≫ (root a).hom.hom)).prod
    integralCellCoordinateMap L negative positive ≫ cellMap L torus root negative positive =
      V negative * (torusPoint D R (integralCellParameters D) ≫ torus.hom.hom) * V positive := by
  let R := CommAlgCat.of Integers.{u} (IntegralMarkedCellCoordinates D)
  let v (a : D.I) := additivePoint R (MvPolynomial.X a)
  let t := torusPoint D R (integralCellParameters D)
  have hc : integralCellCoordinateMap L negative positive =
      lift (orderedFactorPoint v negative ≫ (integralRootFactorsIso L negative).hom)
        (lift t (orderedFactorPoint v positive ≫ (integralRootFactorsIso L positive).hom)) := by
    dsimp only [t]
    rw [integralCellParameters_point D]
    unfold integralCellCoordinateMap splitCellCoordinateMap splitCellPoint
    simp only [Iso.refl_hom, Category.comp_id, lift_map]
    rfl
  dsimp only
  rw [hc, cellMap, lift_mul_three_factors, Category.assoc, Category.assoc,
    integralRootProduct_evaluation, integralRootProduct_evaluation]

set_option backward.isDefEq.respectTransparency false in
/-- Matrix entries identify a marked open multiplication cell with an affine
chart of the same group. The two ordered lists fix the matrix product. -/
private theorem integralCellMap_isOpen_of_matrix_formula {D : BasedRootDatum.{u}} {n : ℕ}
    {G : IntegralGroup.{u}} (i : G ⟶ relativeGL Integers.{u} n) [Mono i.hom.hom]
    (L : AdditiveLine.{u}) (torus : splitTorus D ⟶ G) (root : D.I → (L.group ⟶ G))
    (w : Index.{u} n → D.X) (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (ht : ∀ (R : IntegralAlgebra.{u}) (t : TorusValues D R),
      (relativeGLPointEquiv R (torusPoint D R t ≫ torus.hom.hom ≫ i.hom.hom)).val =
        Matrix.diagonal (fun j => (t (Multiplicative.ofAdd (w j)) : R)))
    (hr : ∀ (a : D.I) (R : IntegralAlgebra.{u}) (z : R),
      (relativeGLPointEquiv R (additivePoint R z ≫ (root a).hom.hom ≫ i.hom.hom)).val =
        integralPolynomialMatrix (p a) z)
    (negative positive : List D.I)
    (hneg : Enumerates negative {a | ¬ D.base.IsPos a})
    (hpos : Enumerates positive {a | D.base.IsPos a})
    (j : affineObject (k := Integers.{u}) (IntegralMarkedCellCoordinates D) ⟶ G.X)
    (hj : IsOpenImmersion j.left)
    (hm : (relativeGLPointEquiv (IntegralMarkedCellCoordinates D) (j ≫ i.hom.hom)).val =
      (negative.map (fun a => integralPolynomialMatrix (p a) (MvPolynomial.X a :
        IntegralMarkedCellCoordinates D))).prod *
      Matrix.diagonal (fun k => MvPolynomial.C (MonoidAlgebra.single (Multiplicative.ofAdd (w k)) 1)) *
      (positive.map (fun a => integralPolynomialMatrix (p a) (MvPolynomial.X a :
        IntegralMarkedCellCoordinates D))).prod) :
    IsOpenImmersion (cellMap L torus root negative positive).left := by
  let R := CommAlgCat.of Integers.{u} (IntegralMarkedCellCoordinates D)
  let c := integralCellCoordinateMap L negative positive
  have he : c ≫ cellMap L torus root negative positive = j := by
    apply (cancel_mono i.hom.hom).mp
    apply (relativeGLPointEquiv R).injective
    apply Units.ext
    let ρ : IntegralPoints G R →* Matrix (Index.{u} n) (Index.{u} n) R :=
      { toFun g := (relativeGLPointEquiv R (g ≫ i.hom.hom)).val
        map_one' := by rw [MonObj.one_comp, map_one]; rfl
        map_mul' a b := by rw [MonObj.mul_comp, map_mul]; rfl }
    change ρ (c ≫ cellMap L torus root negative positive) = ρ j
    change ρ j = _ at hm
    rw [integralCellMap_point, hm, map_mul, map_mul]
    have hT : ρ (torusPoint D R (integralCellParameters D) ≫ torus.hom.hom) =
        Matrix.diagonal (fun k => MvPolynomial.C (MonoidAlgebra.single (Multiplicative.ofAdd (w k)) 1)) := by
      change (relativeGLPointEquiv R
        ((torusPoint D R (integralCellParameters D) ≫ torus.hom.hom) ≫ i.hom.hom)).val = _
      rw [Category.assoc]
      exact ht R (integralCellParameters D)
    have hList (l : List D.I) :
        ρ (l.map (fun a => additivePoint R (MvPolynomial.X a) ≫ (root a).hom.hom)).prod =
        (l.map (fun a => integralPolynomialMatrix (p a) (MvPolynomial.X a :
          IntegralMarkedCellCoordinates D))).prod := by
      rw [map_list_prod, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      change (relativeGLPointEquiv R
        ((additivePoint R (MvPolynomial.X a) ≫ (root a).hom.hom) ≫ i.hom.hom)).val = _
      rw [Category.assoc]
      exact hr a R (MvPolynomial.X a)
    rw [hT, hList, hList]
  let hIso : IsIso c := integralCellCoordinateMap_isIso L negative positive hneg hpos
  have hcell : cellMap L torus root negative positive = (asIso c).inv ≫ j := by
    rw [← he]
    change cellMap L torus root negative positive =
      (asIso c).inv ≫ (asIso c).hom ≫ cellMap L torus root negative positive
    rw [Iso.inv_hom_id_assoc]
  rw [hcell, Over.comp_left]
  have : IsIso (asIso c).inv.left := (Over.forget _).map_isIso (asIso c).inv
  infer_instance

end MarkedOpenCell

section IntegralChartFormula

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField)
open Specs.IntegralSemisimpleModel (Integers integerAlgebra)
open Specs.IntegralLattices (Index Positive Negative ClosedRootImage orderedMatrix)
open Specs.MatrixOpenCell (MatrixGroupCoordinates CellCoordinates cellMatrix minorProduct)

set_option backward.isDefEq.respectTransparency false in
private theorem integralCellScalars_bijective (D : BasedRootDatum.{u}) :
    Function.Bijective (cellScalars D Integers.{u}) := by
  have h : Function.Bijective (Int.castRingHom Integers.{u}) := by
    exact (ULift.ringEquiv.symm : ℤ ≃+* Integers.{u}).bijective
  refine ⟨cellScalars_injective D Integers.{u} h.1, ?_⟩
  apply MvPolynomial.map_surjective
  exact (AddMonoidAlgebra.toMultiplicativeAlgEquiv Integers.{u} Integers.{u} D.X).surjective.comp
    (AddMonoidAlgebra.map_surjective (Int.castRingHom Integers.{u}).toAddMonoidHom h.2)

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
private theorem matrixClosure_openChart_with_matrix_formula
    (D : BasedRootDatum.{u}) (B : CommHopfAlgCat.{u} RationalField.{u}) {n : ℕ}
    (ρ : convolutionPoints B ⟶ Specs.StandardGroups.generalLinearPoints RationalField (Index.{u} n))
    (negative : List (Negative D)) (positive : List (Positive D))
    (w : Index.{u} n → D.X) (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hneg : IsOrderedRootChart false (orderedMatrix negative (fun a => p a.val)))
    (hpos : IsOrderedRootChart true (orderedMatrix positive (fun a => p a.val))) :
    letI : Algebra Integers.{u} B := integerAlgebra B
    letI : Algebra Integers.{u} (IntegralCellCoordinates D) := integerAlgebra _
    ∀ (φ : CellCoordinates Integers.{u} n →ₐ[Integers.{u}] IntegralCellCoordinates D),
      Function.Surjective φ →
      RingHom.ker (rationalMatrixCoordinates (R := Integers.{u}) B ρ) =
        RingHom.ker (φ.comp (IsScalarTower.toAlgHom Integers.{u}
          (MatrixGroupCoordinates Integers.{u} n) (CellCoordinates Integers.{u} n))) →
      φ.toRingHom.mapMatrix (cellMatrix Integers.{u} n) =
        (cellFactors negative positive w p hneg hpos).product →
      ∃ q : affineObject (k := Integers.{u}) (IntegralMarkedCellCoordinates D) ⟶ (integralMatrixClosure B ρ).X,
        IsOpenImmersion q.left ∧
        (relativeGLPointEquiv (IntegralMarkedCellCoordinates D)
          (q ≫ (integralMatrixClosureEmbedding B ρ).hom.hom)).val =
          (negative.map (fun a => integralPolynomialMatrix (p a.val) (MvPolynomial.X a.val :
            IntegralMarkedCellCoordinates D))).prod *
          Matrix.diagonal (fun j => MvPolynomial.C (MonoidAlgebra.single (Multiplicative.ofAdd (w j)) 1)) *
          (positive.map (fun a => integralPolynomialMatrix (p a.val) (MvPolynomial.X a.val :
            IntegralMarkedCellCoordinates D))).prod := by
  let : IsDomain Integers.{u} :=
    (ULift.ringEquiv : Integers.{u} ≃+* ℤ).toMulEquiv.isDomain ℤ
  let : IsPrincipalIdealRing Integers.{u} := integers_isPrincipalIdealRing
  letI : Algebra Integers.{u} RationalField.{u} := integerAlgebra _
  letI : Algebra Integers.{u} B := integerAlgebra _
  letI : IsFractionRing Integers.{u} RationalField.{u} := integers_isFractionRing
  letI := integers_scalarTower B
  letI : Algebra Integers.{u} (IntegralCellCoordinates D) := integerAlgebra _
  intro φ hφ hker hmatrix
  let Z := Integers.{u}
  let E := MatrixGroupCoordinates Z n
  let A := IntegralCellCoordinates D
  let C := IntegralMarkedCellCoordinates D
  let f := rationalMatrixCoordinates (R := Z) B ρ
  let g := φ.comp (IsScalarTower.toAlgHom Z E (CellCoordinates Z n))
  let I := RingHom.ker f
  let r := chartRestriction f g hker
  let r₀ : affineObject (k := Z) A ⟶ (integralMatrixClosure B ρ).X := affineMap r
  let κ₀ : A →+* C := MvPolynomial.map
    ((AddMonoidAlgebra.toMultiplicativeAlgEquiv Z Z D.X).toRingHom.comp
      (AddMonoidAlgebra.mapRingHom D.X (Int.castRingHom Z)))
  let κ : A →ₐ[Z] C :=
    { toRingHom := κ₀
      commutes' x := by
        let e : Z ≃+* ℤ := ULift.ringEquiv
        have h₁ := ringHom_eq_of_equiv_int (R := Z) (A := C) e (κ₀.comp (algebraMap Z A))
        have h₂ := ringHom_eq_of_equiv_int (R := Z) (A := C) e (algebraMap Z C)
        exact RingHom.congr_fun (h₁.trans h₂.symm) x }
  let v : affineObject (k := Z) C ⟶ affineObject (k := Z) A := affineMap (k := Z) (B := C) κ
  let q := v ≫ r₀
  have hκ : Function.Bijective κ := integralCellScalars_bijective D
  have hO : IsOpenImmersion r₀.left := by
    let : Algebra (E ⧸ I) A := r.toRingHom.toAlgebra
    have : IsLocalization.Away (Ideal.Quotient.mk I (minorProduct Z n)) A :=
      isLocalization_chartRestriction f g hker (minorProduct Z n) φ.toRingHom hφ (fun _ => rfl)
    exact IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk I (minorProduct Z n))
  have hISO : IsIso v.left := by
    let i := RingEquiv.toCommRingCatIso (R := A) (S := C) (AlgEquiv.ofBijective κ hκ).toRingEquiv
    exact Scheme.Spec.map_isIso i.hom.op
  refine ⟨q, ?_, ?_⟩
  · change IsOpenImmersion (v.left ≫ r₀.left)
    infer_instance
  · let i := (integralMatrixClosureEmbedding B ρ).hom.hom
    have hir : r₀ ≫ i = affineMap g := by
      change affineMap r ≫ (matrixClosureEmbedding (R := Z) B ρ).hom.hom = _
      rw [matrixClosureEmbedding_hom, affineMap_comp]
      have eq : r.comp (Ideal.Quotient.mkₐ Z I) = g := AlgHom.ext fun _ => rfl
      exact congrArg (fun h : E →ₐ[Z] A => affineMap h) eq
    change (relativeGLPointEquiv C ((v ≫ r₀) ≫ i)).val = _
    dsimp only [v]
    rw [Category.assoc, hir, affineMap_comp, relativeGLPointEquiv_affineMap]
    let e := Matrix.reindexRingEquiv C (Equiv.ulift : Index.{u} n ≃ Fin n)
    apply e.injective
    have he := (congrArg κ₀.mapMatrix hmatrix).trans
      (cellScalars_factors D Z negative positive w p hneg hpos)
    exact he

end IntegralChartFormula

section IntegralCellFunctoriality

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (IntegralGroup AdditiveLine splitTorus cellMap rootProduct product)

set_option backward.isDefEq.respectTransparency false in
private theorem integralRootProduct_map {D : BasedRootDatum.{u}} {H G : IntegralGroup.{u}}
    (j : H ⟶ G) (L : AdditiveLine.{u}) (root : D.I → (L.group ⟶ H)) (l : List D.I) :
    rootProduct L (fun a => root a ≫ j) l = rootProduct L root l ≫ j.hom.hom := by
  induction l with
  | nil => exact (MonObj.one_comp j.hom.hom).symm
  | cons a l ih =>
    dsimp only [rootProduct]
    rw [MonObj.mul_comp, ih, Category.assoc, Category.assoc]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem integralCellMap_map {D : BasedRootDatum.{u}} {H G : IntegralGroup.{u}}
    (j : H ⟶ G) (L : AdditiveLine.{u}) (torus : splitTorus D ⟶ H)
    (root : D.I → (L.group ⟶ H)) (l r : List D.I) :
    cellMap L (torus ≫ j) (fun a => root a ≫ j) l r =
      cellMap L torus root l r ≫ j.hom.hom := by
  dsimp only [cellMap]
  simp only [MonObj.mul_comp, Category.assoc, integralRootProduct_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem integralCellMap_open_of_openSubgroup {D : BasedRootDatum.{u}} {H G : IntegralGroup.{u}}
    (j : H ⟶ G) [IsOpenImmersion j.hom.hom.left]
    (L : AdditiveLine.{u}) (torus : splitTorus D ⟶ H)
    (root : D.I → (L.group ⟶ H)) (l r : List D.I)
    (h : IsOpenImmersion (cellMap L (torus ≫ j) (fun a => root a ≫ j) l r).left) :
    IsOpenImmersion (cellMap L torus root l r).left := by
  rw [integralCellMap_map, Over.comp_left] at h
  exact IsOpenImmersion.of_comp (cellMap L torus root l r).left j.hom.hom.left

end IntegralCellFunctoriality

section IntegralFibrePoints

open CategoryTheory.Limits
open Specs.IntegralSemisimpleModel
  (Integers IntegralGroup IntegralPoints integralSpec integerAlgebra fibre forgetFibrePoint)
open Specs.AdjointRepresentation (GroupPoints)

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension to a field is represented on its test algebras by the
same points of the integral model, with the given structure map to the field. -/
theorem forgetFibrePoint_bijective {k : Type u} [Field k] (G : IntegralGroup.{u})
    (R : TestAlgebra k) : Function.Bijective (forgetFibrePoint G R) := by
  let a := Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} k))
  let X := (testSpec k).obj (op R)
  let Y := integralSpec.obj (op (CommAlgCat.of Integers.{u} R))
  let Z := ((fibre k).obj G).X
  have hbase : X.hom ≫ a = Y.hom := by
    change Spec.map (CommRingCat.ofHom (algebraMap k R)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} k)) =
        Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} R))
    rw [← Spec.map_comp]
    congr 2
    ext x
    exact map_intCast (algebraMap k R) x.down
  constructor
  · intro x y he
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congrArg (fun p : IntegralPoints G (CommAlgCat.of Integers.{u} R) => p.left) he
    · exact (Over.w x).trans (Over.w y).symm
  · intro x
    have h : x.left ≫ G.X.hom = X.hom ≫ a := (Over.w x).trans hbase.symm
    let y : X ⟶ Z := Over.homMk (pullback.lift x.left X.hom h) (pullback.lift_snd _ _ _)
    refine ⟨y, ?_⟩
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _

end IntegralFibrePoints

section IntegralRankOne

open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField Realization)
open Specs.IntegralLattices (Index RationalHighestWeight dividedPower)
open Specs.IntegralRootRelations (RootCoordinates OppositeRootRelations)
open Specs.IntegralSemisimpleModel
open Specs.CharacterPairing (characterValue pairing)
open Specs.DiagonalizableGroups (groupAlgebra)
open Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open private markedPairing from LinearAlgebraicGroups.Classification.IntegralRootRelations

private def cocharacterMatrix {n : ℕ} {R : Type u} [CommRing R]
    (weight : Index.{u} n → ℤ) (s : Rˣ) : Matrix (Index.{u} n) (Index.{u} n) R :=
  Matrix.diagonal (fun j => (↑(s ^ weight j) : R))

private theorem cocharacterMatrix_map {n : ℕ} {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (weight : Index.{u} n → ℤ) (s : Rˣ) :
    f.mapMatrix (cocharacterMatrix weight s) =
      cocharacterMatrix weight (Units.map f.toMonoidHom s) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp only [cocharacterMatrix, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_eq]
    exact congrArg Units.val (map_zpow (Units.map f.toMonoidHom) s (weight i))
  · simp [cocharacterMatrix, h]

/-- The root relation on the rational pivot chart descends by evaluating it
on the integral polynomial algebra with the same pivot inverted. -/
private theorem oppositeMatrixRelation_of_generic {n : ℕ}
    (p q : Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ)) (weight : Index.{u} n → ℤ)
    (generic : ∀ (S : TestAlgebra RationalField.{u}) (x y : S) (s : Sˣ), (s : S) = 1 + x * y →
      integralPolynomialMatrix p x * integralPolynomialMatrix q y =
        integralPolynomialMatrix q (y * (↑s⁻¹ : S)) * cocharacterMatrix weight s *
          integralPolynomialMatrix p (x * (↑s⁻¹ : S))) :
    ∀ (R : Type u) [CommRing R] (x y : R) (s : Rˣ), (s : R) = 1 + x * y →
      integralPolynomialMatrix p x * integralPolynomialMatrix q y =
        integralPolynomialMatrix q (y * (↑s⁻¹ : R)) * cocharacterMatrix weight s *
          integralPolynomialMatrix p (x * (↑s⁻¹ : R)) := by
  let A := MvPolynomial (ULift.{u} Bool) ℤ
  let B := MvPolynomial (ULift.{u} Bool) RationalField.{u}
  let X : A := MvPolynomial.X ⟨false⟩
  let Y : A := MvPolynomial.X ⟨true⟩
  let a := 1 + X * Y
  let f : A →+* B := MvPolynomial.map (Int.castRingHom RationalField.{u})
  let A' := Localization.Away a
  let B' := Localization.Away (f a)
  let j : A' →+* B' := Localization.awayMap f a
  have hj : Function.Injective j := by
    apply Localization.awayMap_injective_iff.mpr
    intro v hv
    have hf : Function.Injective f := MvPolynomial.map_injective _ rationalField_intCast_injective
    rw [show v = 0 from hf (hv.trans (map_zero f).symm)]
    exact ⟨0, mul_zero _⟩
  let x₀ : A' := algebraMap A A' X
  let y₀ : A' := algebraMap A A' Y
  let s₀ : A'ˣ := (IsLocalization.Away.algebraMap_isUnit (S := A') a).unit
  have hs₀ : (s₀ : A') = 1 + x₀ * y₀ := by
    change algebraMap A A' a = _
    simp only [a, x₀, y₀, map_add, map_mul, map_one]
  have transport {S : Type u} [CommRing S] (g : A' →+* S) :
      g.mapMatrix (integralPolynomialMatrix p x₀ * integralPolynomialMatrix q y₀) =
        integralPolynomialMatrix p (g x₀) * integralPolynomialMatrix q (g y₀) ∧
      g.mapMatrix (integralPolynomialMatrix q (y₀ * (↑s₀⁻¹ : A')) * cocharacterMatrix weight s₀ *
          integralPolynomialMatrix p (x₀ * (↑s₀⁻¹ : A'))) =
        integralPolynomialMatrix q (g y₀ * (↑(Units.map g.toMonoidHom s₀)⁻¹ : S)) *
          cocharacterMatrix weight (Units.map g.toMonoidHom s₀) *
            integralPolynomialMatrix p (g x₀ * (↑(Units.map g.toMonoidHom s₀)⁻¹ : S)) := by
    constructor
    · rw [map_mul, integralPolynomialMatrix_map, integralPolynomialMatrix_map]
    · simp only [map_mul, integralPolynomialMatrix_map, cocharacterMatrix_map]
      rfl
  have hA : integralPolynomialMatrix p x₀ * integralPolynomialMatrix q y₀ =
      integralPolynomialMatrix q (y₀ * (↑s₀⁻¹ : A')) * cocharacterMatrix weight s₀ *
        integralPolynomialMatrix p (x₀ * (↑s₀⁻¹ : A')) := by
    apply Matrix.ext
    intro i k
    apply hj
    have he : ((Units.map j.toMonoidHom s₀ : B'ˣ) : B') = 1 + j x₀ * j y₀ := by
      change j (s₀ : A') = _
      rw [hs₀, map_add, map_one, map_mul]
    have h := generic (CommAlgCat.of RationalField.{u} B') (j x₀) (j y₀)
      (Units.map j.toMonoidHom s₀) he
    rw [← (transport j).1, ← (transport j).2] at h
    exact congrArg (fun m : Matrix (Index.{u} n) (Index.{u} n) B' => m i k) h
  intro R _ x y s hs
  let e : A →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R)
    (fun i => if i.down then y else x)
  have hX : e X = x :=
    MvPolynomial.eval₂Hom_X' _ (fun i : ULift.{u} Bool => if i.down then y else x) ⟨false⟩
  have hY : e Y = y :=
    MvPolynomial.eval₂Hom_X' _ (fun i : ULift.{u} Bool => if i.down then y else x) ⟨true⟩
  have ha : e a = (s : R) := by
    rw [show a = 1 + X * Y from rfl, map_add, map_one, map_mul, hX, hY, hs]
  let hu : IsUnit (e a) := ha ▸ s.isUnit
  let g : A' →+* R := IsLocalization.Away.lift a hu
  have hx : g x₀ = x := (IsLocalization.Away.lift_eq a hu X).trans hX
  have hy : g y₀ = y := (IsLocalization.Away.lift_eq a hu Y).trans hY
  have hh : Units.map g.toMonoidHom s₀ = s := by
    apply Units.ext
    change g (algebraMap A A' a) = (s : R)
    exact (IsLocalization.Away.lift_eq a hu a).trans ha
  have h := congrArg g.mapMatrix hA
  rw [(transport g).1, (transport g).2, hx, hy, hh] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
private theorem latticeRootMatrix_opposite
    {D : BasedRootDatum.{u}} {A : Specs.RootGroups.AdditiveLine RationalField.{u}}
    {Q : Realization D A}
    [LieRing (Lie RationalField.{u} Q.pinned.pair.G.val)]
    [LieAlgebra RationalField.{u} (Lie RationalField.{u} Q.pinned.pair.G.val)]
    {z : RootCoordinates Q} (hop : OppositeRootRelations Q z)
    {e h : D.I → Lie RationalField.{u} Q.pinned.pair.G.val}
    [DecidableEq D.base.support] {ω : D.base.support → D.X}
    (V : ∀ i, RationalHighestWeight z e h (ω i)) {n : ℕ}
    (b : Module.Basis (Index.{u} n) RationalField.{u} ((i : D.base.support) → (V i).space))
    (w : Index.{u} n → D.X) (hw : ∀ j i, b j i ∈ (V i).weightSpace (w j))
    (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (hp : ∀ (a : D.I) (m : ℕ) (j : Index.{u} n) (i : D.base.support),
      ∑ l : Index.{u} n, ((p a l j).coeff m : RationalField.{u}) • b l i =
        (dividedPower ((V i).rootOperator a) m).mulVec (b j i))
    (a : D.I) :
    let a' := D.datum.reflectionPerm a a
    ∀ (R : Type u) [CommRing R] (x y : R) (s : Rˣ), (s : R) = 1 + x * y →
      integralPolynomialMatrix (p a) x * integralPolynomialMatrix (p a') y =
        integralPolynomialMatrix (p a') (y * (↑s⁻¹ : R)) *
          cocharacterMatrix (fun i => D.datum.toLinearMap (w i) (D.datum.coroot a)) s *
          integralPolynomialMatrix (p a) (x * (↑s⁻¹ : R)) := by
  let a' := D.datum.reflectionPerm a a
  apply oppositeMatrixRelation_of_generic
  intro R x y s hs
  have ha : D.datum.root a' = -D.datum.root a := by
    change D.datum.root (D.datum.reflectionPerm a a) = _
    rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_self]
  let ρ := (rationalMatrixAction V b).app R
  have hroot (c : D.I) (r : R) :
      (ρ (Specs.IntegralRootRelations.root Q z c R r) :
        Matrix.GeneralLinearGroup (Index.{u} n) R).val = integralPolynomialMatrix (p c) r :=
    rationalMatrixAction_root V b c (p c) (hp c) R r
  let c : Specs.CharacterDescent.Cocharacter Q.pinned.pair.T.group :=
    Additive.toMul (Q.datumIso.val.coweightEquiv.symm (D.datum.coroot a))
  have ht : (ρ (Specs.IntegralRootRelations.torus Q (D.datum.coroot a) R s) :
      Matrix.GeneralLinearGroup (Index.{u} n) R).val =
      cocharacterMatrix (fun i => D.datum.toLinearMap (w i) (D.datum.coroot a)) s := by
    change (ρ (cocharacterPoint c R s ≫ Q.pinned.pair.T.inclusion.hom.hom) :
      Matrix.GeneralLinearGroup (Index.{u} n) R).val = _
    rw [rationalMatrixAction_torus V b w hw]
    congr 1
    funext i
    let χ : Specs.CharacterDescent.Character Q.pinned.pair.T.group :=
      Additive.toMul (Q.datumIso.val.weightEquiv (w i))
    change characterValue χ R (cocharacterPoint c R s) =
      (↑(s ^ D.datum.toLinearMap (w i) (D.datum.coroot a)) : R)
    exact ((LinearAlgebraicGroups.RootData.CharacterPairing.characterPairingComposition _ χ c).2 R s).trans
      (congrArg (fun m : ℤ => (↑(s ^ m) : R)) (markedPairing Q (w i) (D.datum.coroot a)))
  let f : GroupPoints Q.pinned.pair.G.val R →* Matrix (Index.{u} n) (Index.{u} n) R :=
    (Units.coeHom _).comp ρ.hom
  have hR (i : D.I) (r : R) : f (Specs.IntegralRootRelations.root Q z i R r) =
      integralPolynomialMatrix (p i) r := hroot i r
  have hT : f (Specs.IntegralRootRelations.torus Q (D.datum.coroot a) R s) =
      cocharacterMatrix (fun i => D.datum.toLinearMap (w i) (D.datum.coroot a)) s := ht
  simpa only [map_mul, hR, hT] using congrArg f (hop a a' ha R x y s hs)

set_option backward.isDefEq.respectTransparency false in
private theorem torusPoint_natural {D : BasedRootDatum.{u}} {R S : IntegralAlgebra.{u}}
    (f : R ⟶ S) (t : TorusValues D R) :
    integralSpec.map f.op ≫ torusPoint D R t =
      torusPoint D S ((Units.map f.hom.toMonoidHom).comp t) := by
  change affineMap f.hom ≫ affineMap (torusEvaluation t) = affineMap (torusEvaluation _)
  rw [affineMap_comp]
  congr 1
  apply MonoidAlgebra.algHom_ext
  · intro m
    rw [AlgHom.comp_apply, torusEvaluation_single, torusEvaluation_single]
    rfl
  · exact Subsingleton.elim _ _

private theorem cocharacter_natural {D : BasedRootDatum.{u}} (v : D.Y)
    {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (s : Rˣ) :
    (Units.map f.hom.toMonoidHom).comp (cocharacter D v R s) =
      cocharacter D v S (Units.map f.hom.toMonoidHom s) := by
  apply MonoidHom.ext
  intro m
  exact map_zpow (Units.map f.hom.toMonoidHom) s (D.datum.toLinearMap m.toAdd v)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem exists_integralRankOne {D : BasedRootDatum.{u}} {n : ℕ}
    {G : IntegralGroup.{u}} (affine : IsAffine G.X.left)
    (i : G ⟶ relativeGL Integers.{u} n) [Mono i.hom.hom]
    (L : AdditiveLine.{u}) (torus : splitTorus D ⟶ G) (root : D.I → (L.group ⟶ G))
    (w : Index.{u} n → D.X) (p : D.I → Matrix (Index.{u} n) (Index.{u} n) (Polynomial ℤ))
    (ht : ∀ (R : IntegralAlgebra.{u}) (t : TorusValues D R),
      (relativeGLPointEquiv R (torusPoint D R t ≫ torus.hom.hom ≫ i.hom.hom)).val =
        torusWeightMatrix (Multiplicative.ofAdd ∘ w) t)
    (hr : ∀ (a : D.I) (R : IntegralAlgebra.{u}) (z : R),
      (relativeGLPointEquiv R (additivePoint R z ≫ (root a).hom.hom ≫ i.hom.hom)).val =
        integralPolynomialMatrix (p a) z)
    (hconj : ∀ (R : IntegralAlgebra.{u}) (t : TorusValues D R) (a : D.I) (z : R),
      let g := torusPoint D R t ≫ torus.hom.hom
      g * (L.point R z ≫ (root a).hom.hom) * g⁻¹ =
        L.point R ((t (Multiplicative.ofAdd (D.datum.root a)) : R) * z) ≫ (root a).hom.hom)
    (a : D.I)
    (hop : let a' := D.datum.reflectionPerm a a
      ∀ (R : Type u) [CommRing R] (x y : R) (s : Rˣ), (s : R) = 1 + x * y →
        integralPolynomialMatrix (p a) x * integralPolynomialMatrix (p a') y =
          integralPolynomialMatrix (p a') (y * (↑s⁻¹ : R)) *
            cocharacterMatrix (fun j => D.datum.toLinearMap (w j) (D.datum.coroot a)) s *
            integralPolynomialMatrix (p a) (x * (↑s⁻¹ : R))) :
    ∃ F : rankOnePoints.{u} ⟶ integralPointFunctor G,
      (∀ (R : IntegralAlgebra.{u}) (x : R),
        F.app R (Specs.IntegralRootRelations.upper x) = L.point R x ≫ (root a).hom.hom) ∧
      (∀ (R : IntegralAlgebra.{u}) (y : R),
        F.app R (Specs.IntegralRootRelations.lower y) =
          L.point R y ≫ (root (D.datum.reflectionPerm a a)).hom.hom) ∧
      (∀ (R : IntegralAlgebra.{u}) (s : Rˣ),
        F.app R (Specs.IntegralRootRelations.diagonal s) =
          torusPoint D R (cocharacter D (D.datum.coroot a) R s) ≫ torus.hom.hom) := by
  let a' := D.datum.reflectionPerm a a
  let v := D.datum.coroot a
  letI : GrpObj L.group.X := L.operations
  let x (i : D.I) (R : IntegralAlgebra.{u}) : Multiplicative R →* IntegralPoints G R :=
    MonoidHom.mk'
      (fun z => L.point R z.toAdd ≫ (root i).hom.hom)
      (fun y z => by
        letI : IsMonHom (root i).hom.hom := (root i).hom.isMonHom_hom
        rw [← MonObj.mul_comp]
        exact congrArg (· ≫ (root i).hom.hom) (L.add R y.toAdd z.toAdd).symm)
  let t (R : IntegralAlgebra.{u}) : Rˣ →* IntegralPoints G R :=
    MonoidHom.mk' (fun s => torusPoint D R (cocharacter D v R s) ≫ torus.hom.hom)
      (fun s t => by
        rw [← MonObj.mul_comp]
        change affineTorusPointEquiv R (cocharacter D v R (s * t)) ≫ torus.hom.hom =
          (affineTorusPointEquiv R (cocharacter D v R s) *
            affineTorusPointEquiv R (cocharacter D v R t)) ≫ torus.hom.hom
        rw [← map_mul]
        congr 2
        apply MonoidHom.ext
        intro m
        exact mul_zpow s t (D.datum.toLinearMap m.toAdd v))
  have hx {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (c : D.I) (z : R) :
      (integralPointFunctor G).map f (x c R (.ofAdd z)) = x c S (.ofAdd (f.hom z)) := by
    change affineMap f.hom ≫ polynomialPointEquiv R z ≫ (root c).hom.hom =
      polynomialPointEquiv S (f.hom z) ≫ (root c).hom.hom
    rw [← Category.assoc, polynomialPoint_naturality]
  have htv {R S : IntegralAlgebra.{u}} (f : R ⟶ S) (s : Rˣ) :
      (integralPointFunctor G).map f (t R s) = t S (Units.map f.hom.toMonoidHom s) := by
    change integralSpec.map f.op ≫ torusPoint D R (cocharacter D v R s) ≫ torus.hom.hom =
      torusPoint D S _ ≫ torus.hom.hom
    rw [← Category.assoc, torusPoint_natural, cocharacter_natural]
  have ha : D.datum.root a' = -D.datum.root a := by
    change D.datum.root (D.datum.reflectionPerm a a) = _
    rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_self]
  have hv : D.datum.toLinearMap (D.datum.root a) v = 2 := D.datum.root_coroot_two a
  have hv' : D.datum.toLinearMap (D.datum.root a') v = -(2 : ℤ) := by
    rw [ha, map_neg, LinearMap.neg_apply, hv]
  have hc (R : IntegralAlgebra.{u}) (s : Rˣ) (b : D.I) (r : R) :
      t R s * x b R (.ofAdd r) * (t R s)⁻¹ =
        x b R (.ofAdd ((↑(s ^ D.datum.toLinearMap (D.datum.root b) v) : R) * r)) :=
    hconj R (cocharacter D v R s) b r
  have hop' (R : IntegralAlgebra.{u}) (r u : R) (s : Rˣ) (hs : (s : R) = 1 + r * u) :
      x a R (.ofAdd r) * x a' R (.ofAdd u) =
        x a' R (.ofAdd (u * (↑s⁻¹ : R))) * t R s * x a R (.ofAdd (r * (↑s⁻¹ : R))) := by
    let F : IntegralPoints G R →* Matrix (Index.{u} n) (Index.{u} n) R :=
      { toFun := fun g => (relativeGLPointEquiv R (g ≫ i.hom.hom)).val
        map_one' := by rw [MonObj.one_comp, map_one]; rfl
        map_mul' g h := by rw [MonObj.mul_comp, map_mul]; rfl }
    have hF : Function.Injective F := fun g h he =>
      (cancel_mono i.hom.hom).mp ((relativeGLPointEquiv R).injective (Units.ext he))
    have hX (b : D.I) (z : R) : F (x b R (.ofAdd z)) = integralPolynomialMatrix (p b) z := by
      change (relativeGLPointEquiv R ((additivePoint R z ≫ (root b).hom.hom) ≫ i.hom.hom)).val = _
      rw [Category.assoc]
      exact hr b R z
    have hT : F (t R s) = cocharacterMatrix (fun j => D.datum.toLinearMap (w j) v) s := by
      change (relativeGLPointEquiv R
        ((torusPoint D R (cocharacter D v R s) ≫ torus.hom.hom) ≫ i.hom.hom)).val = _
      rw [Category.assoc, ht]
      rfl
    apply hF
    simp only [map_mul, hX, hT]
    exact hop R r u s hs
  let data : Specs.IntegralRankOneExtension.RootHomomorphisms G :=
    { positive := x a
      negative := x a'
      coroot := t
      map_positive := fun f z => hx f a z
      map_negative := fun f z => hx f a' z
      map_coroot := htv
      positive_conjugation := fun R s z => by
        change t R s * x a R (.ofAdd z) * (t R s)⁻¹ =
          x a R (.ofAdd ((s : R) ^ 2 * z))
        simpa only [hv, zpow_ofNat, Units.val_pow_eq_pow_val] using hc R s a z
      negative_conjugation := fun R s z => by
        change t R s * x a' R (.ofAdd z) * (t R s)⁻¹ =
          x a' R (.ofAdd ((↑s⁻¹ : R) ^ 2 * z))
        simpa only [hv', zpow_neg, zpow_ofNat, ← inv_pow, Units.val_pow_eq_pow_val] using hc R s a' z
      opposite := hop' }
  exact IntegralRankOneExtension.rankOneExtension G affine data

end IntegralRankOne

section FieldBaseChange

open CategoryTheory.Limits
open _root_.LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (diagonalTorus)
open Specs.IntegralSemisimpleModel
open Specs.AdjointRepresentation (GroupPoints)
open Specs.RootGroups (rootPoint)
open _root_.LinearAlgebraicGroups.RootData.RootGroups (additivePoints)
open private additivePoints_add additivePoints_natural rootPoint_eq
  from LinearAlgebraicGroups.RootData.RootGroups
open private groupIsoOfPointIso from LinearAlgebraicGroups.Affine.IdentityTangent

attribute [local instance] integerAlgebra

private abbrev fibreBaseMap (k : Type u) [Field k] :=
  Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} k))

private abbrev fibreScheme (k : Type u) [Field k] := Over.pullback (fibreBaseMap k)

private def restrictToIntegers (k : Type u) [Field k] : TestAlgebra k ⥤ IntegralAlgebra.{u} where
  obj R := CommAlgCat.of Integers.{u} R
  map f := CommAlgCat.ofHom
    { toRingHom := f.hom.toRingHom
      commutes' x := map_intCast f.hom.toRingHom x.down }
  map_id _ := rfl
  map_comp _ _ := rfl

private def projectFibrePoint {k : Type u} [Field k] (X : IntegralScheme.{u}) (R : TestAlgebra k)
    (p : Points ((fibreScheme k).obj X) R) :
    integralSpec.obj (op ((restrictToIntegers k).obj R)) ⟶ X :=
  Over.homMk (p.left ≫ pullback.fst X.hom (fibreBaseMap k)) (by
    change (p.left ≫ pullback.fst X.hom (fibreBaseMap k)) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} R))
    erw [Category.assoc, pullback.condition, ← Category.assoc]
    have hp : p.left ≫ ((fibreScheme k).obj X).hom = ((testSpec k).obj (op R)).hom := Over.w p
    erw [hp]
    change Spec.map (CommRingCat.ofHom (algebraMap k R)) ≫ fibreBaseMap k =
      Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} R))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext n
    exact map_intCast (algebraMap k R) n.down)

set_option backward.isDefEq.respectTransparency false in
private theorem projectFibrePoint_comp {k : Type u} [Field k] {X Y : IntegralScheme.{u}}
    (f : X ⟶ Y) (R : TestAlgebra k) (p : Points ((fibreScheme k).obj X) R) :
    projectFibrePoint Y R (p ≫ (fibreScheme k).map f) = projectFibrePoint X R p ≫ f := by
  apply Over.OverMorphism.ext
  change (p.left ≫ ((fibreScheme k).map f).left) ≫ pullback.fst Y.hom (fibreBaseMap k) =
    (p.left ≫ pullback.fst X.hom (fibreBaseMap k)) ≫ f.left
  simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]

private theorem forgetFibrePoint_comp {k : Type u} [Field k] {G H : IntegralGroup.{u}} (f : G ⟶ H)
    (R : TestAlgebra k) (p : GroupPoints ((fibre k).obj G) R) :
    forgetFibrePoint H R (p ≫ ((fibre k).map f).hom.hom) = forgetFibrePoint G R p ≫ f.hom.hom :=
  projectFibrePoint_comp f.hom.hom R p

set_option backward.isDefEq.respectTransparency false in
private theorem forgetFibrePoint_mul {k : Type u} [Field k] (G : IntegralGroup.{u}) (R : TestAlgebra k)
    (p q : GroupPoints ((fibre k).obj G) R) :
    forgetFibrePoint G R (p * q) = forgetFibrePoint G R p * forgetFibrePoint G R q := by
  let F := fibreScheme k
  let m := Functor.LaxMonoidal.μ F G.X G.X
  let a : Points (F.obj (G.X ⊗ G.X)) R := lift p q ≫ m
  have ha : projectFibrePoint (G.X ⊗ G.X) R a =
      lift (forgetFibrePoint G R p) (forgetFibrePoint G R q) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [← projectFibrePoint_comp, lift_fst]
      change projectFibrePoint G.X R (a ≫ F.map (fst _ _)) = projectFibrePoint G.X R p
      rw [show a ≫ F.map (fst G.X G.X) = p by
        dsimp only [a, m]
        rw [Category.assoc, Functor.Monoidal.μ_fst]
        exact lift_fst (show Points (F.obj G.X) R from p) (show Points (F.obj G.X) R from q)]
    · rw [← projectFibrePoint_comp, lift_snd]
      change projectFibrePoint G.X R (a ≫ F.map (snd _ _)) = projectFibrePoint G.X R q
      rw [show a ≫ F.map (snd G.X G.X) = q by
        dsimp only [a, m]
        rw [Category.assoc, Functor.Monoidal.μ_snd]
        exact lift_snd (show Points (F.obj G.X) R from p) (show Points (F.obj G.X) R from q)]
  change projectFibrePoint G.X R (lift p q ≫ (m ≫ F.map μ[G.X])) =
    lift (forgetFibrePoint G R p) (forgetFibrePoint G R q) ≫ μ[G.X]
  rw [← Category.assoc]
  change projectFibrePoint G.X R (a ≫ F.map μ[G.X]) = _
  rw [projectFibrePoint_comp, ha]

private def fibrePointsEquiv {k : Type u} [Field k] (G : IntegralGroup.{u}) (R : TestAlgebra k) :
    GroupPoints ((fibre k).obj G) R ≃* IntegralPoints G ((restrictToIntegers k).obj R) where
  toEquiv := Equiv.ofBijective _ (forgetFibrePoint_bijective G R)
  map_mul' := forgetFibrePoint_mul G R

private def fibrePointIso {k : Type u} [Field k] (G : IntegralGroup.{u}) :
    (groupPointsFunctor k).obj ((fibre k).obj G) ≅ restrictToIntegers k ⋙ integralPointFunctor G :=
  NatIso.ofComponents (fun R => (fibrePointsEquiv G R).toGrpIso) (by
    intro R S f
    apply GrpCat.ext
    intro p
    apply Over.OverMorphism.ext
    exact Category.assoc _ _ _)

private theorem fibre_isAffine {k : Type u} [Field k] (G : IntegralGroup.{u}) [IsAffine G.X.left] :
    IsAffine ((fibre k).obj G).X.left := by
  change IsAffine (pullback G.X.hom (fibreBaseMap k))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem exists_additiveFibreIso {k : Type u} [Field k] (L : AdditiveLine.{u})
    (A : Specs.RootGroups.AdditiveLine k) :
    ∃ e : A.group ≅ (fibre k).obj L.group,
      ∀ (R : TestAlgebra k) (x : R),
        forgetFibrePoint L.group R (rootPoint e.hom R x) = L.point ((restrictToIntegers k).obj R) x := by
  letI : GrpObj L.group.X := L.operations
  let e (R : TestAlgebra k) :
      GroupPoints A.group R ≃* IntegralPoints L.group ((restrictToIntegers k).obj R) :=
    { toEquiv := (additivePoints A R).symm.trans (polynomialPointEquiv ((restrictToIntegers k).obj R))
      map_mul' := by
        intro x y
        obtain ⟨x, rfl⟩ := (additivePoints A R).surjective x
        obtain ⟨y, rfl⟩ := (additivePoints A R).surjective y
        rw [← additivePoints_add]
        let P := polynomialPointEquiv ((restrictToIntegers k).obj R)
        let E := additivePoints A R
        change P (E.symm (E (x + y))) = P (E.symm (E x)) * P (E.symm (E y))
        simp only [Equiv.symm_apply_apply]
        exact (L.add ((restrictToIntegers k).obj R) x y).symm }
  let d : (groupPointsFunctor k).obj A.group ≅ restrictToIntegers k ⋙ integralPointFunctor L.group :=
    NatIso.ofComponents (fun R => (e R).toGrpIso) (by
      intro R S f
      apply GrpCat.ext
      intro p
      obtain ⟨x, rfl⟩ := (additivePoints A R).surjective p
      change e S (mapPoints f (additivePoints A R x)) =
        affineMap ((restrictToIntegers k).map f).hom ≫ e R (additivePoints A R x)
      rw [additivePoints_natural]
      simp only [e, MulEquiv.coe_mk, Equiv.trans_apply, Equiv.symm_apply_apply]
      exact (polynomialPoint_naturality ((restrictToIntegers k).map f).hom x).symm)
  have : IsAffine A.group.X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial k))))
  have : IsAffine L.group.X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (Polynomial Integers.{u}))))
  have : IsAffine ((fibre k).obj L.group).X.left := fibre_isAffine L.group
  let P := d ≪≫ (fibrePointIso L.group).symm
  let j := groupIsoOfPointIso P
  have hj : (groupPointsFunctor k).map j.hom = P.hom :=
    (groupHomEquiv A.group ((fibre k).obj L.group) ‹IsAffine A.group.X.left›).apply_symm_apply _
  refine ⟨j, fun R x => ?_⟩
  have h := DFunLike.congr_fun (congrArg (fun t => (t.app R).hom) hj) (additivePoints A R x)
  change additivePoints A R x ≫ j.hom.hom.hom =
    (fibrePointsEquiv L.group R).symm (e R (additivePoints A R x)) at h
  rw [rootPoint_eq, h]
  change (fibrePointsEquiv L.group R) ((fibrePointsEquiv L.group R).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  exact congrArg (polynomialPointEquiv ((restrictToIntegers k).obj R))
    ((additivePoints A R).symm_apply_apply x)

private theorem affineTorusPoint_natural {k M : Type u} [CommRing k] [CommGroup M]
    {R S : CommAlgCat.{u} k} (f : R ⟶ S) (t : M →* Rˣ) :
    affineMap f.hom ≫ affineTorusPointEquiv R t =
      affineTorusPointEquiv S ((Units.map f.hom.toMonoidHom).comp t) := by
  change affineMap f.hom ≫ affineMap (torusEvaluation t) = affineMap (torusEvaluation _)
  rw [affineMap_comp]
  congr 1
  apply MonoidAlgebra.algHom_ext
  · intro m
    rw [AlgHom.comp_apply, torusEvaluation_single, torusEvaluation_single]
    rfl
  · exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
private theorem exists_torusFibreIso {k : Type u} [Field k] (D : BasedRootDatum.{u}) :
    ∃ t : (diagonalTorus k D).val ≅ (fibre k).obj (splitTorus D),
      ∀ (R : TestAlgebra k) (v : TorusValues D ((restrictToIntegers k).obj R)),
        forgetFibrePoint (splitTorus D) R
          (Specs.IntegralFibreReductivity.torusPoint D R v ≫ t.hom.hom.hom) =
          torusPoint D ((restrictToIntegers k).obj R) v := by
  let e (R : TestAlgebra k) :
      GroupPoints (diagonalTorus k D).val R ≃* IntegralPoints (splitTorus D) ((restrictToIntegers k).obj R) :=
    (affineTorusPointEquiv (k := k) R).symm.trans
      (affineTorusPointEquiv (k := Integers.{u}) ((restrictToIntegers k).obj R))
  have hEval (R : TestAlgebra k) (v : Multiplicative D.X →* Rˣ) :
      e R (affineTorusPointEquiv (k := k) R v) =
        affineTorusPointEquiv (k := Integers.{u}) ((restrictToIntegers k).obj R) v :=
    congrArg (affineTorusPointEquiv (k := Integers.{u}) ((restrictToIntegers k).obj R))
      ((affineTorusPointEquiv (k := k) R).symm_apply_apply v)
  let d : (groupPointsFunctor k).obj (diagonalTorus k D).val ≅
      restrictToIntegers k ⋙ integralPointFunctor (splitTorus D) :=
    NatIso.ofComponents (fun R => (e R).toGrpIso) (by
      intro R S f
      apply GrpCat.ext
      intro p
      obtain ⟨x, rfl⟩ := (affineTorusPointEquiv (k := k) R).surjective p
      change e S (affineMap f.hom ≫ affineTorusPointEquiv R x) =
        affineMap ((restrictToIntegers k).map f).hom ≫ e R (affineTorusPointEquiv R x)
      rw [affineTorusPoint_natural, hEval, hEval, affineTorusPoint_natural]
      rfl)
  have : IsAffine (diagonalTorus k D).val.X.left := (diagonalTorus k D).property.1
  have : IsAffine (splitTorus D).X.left := inferInstanceAs
    (IsAffine (Spec (CommRingCat.of (MonoidAlgebra Integers.{u} (Multiplicative D.X)))))
  have : IsAffine ((fibre k).obj (splitTorus D)).X.left := fibre_isAffine _
  let P := d ≪≫ (fibrePointIso (splitTorus D)).symm
  let j := groupIsoOfPointIso P
  have hj : (groupPointsFunctor k).map j.hom = P.hom :=
    (groupHomEquiv (diagonalTorus k D).val ((fibre k).obj (splitTorus D))
      ‹IsAffine (diagonalTorus k D).val.X.left›).apply_symm_apply _
  refine ⟨j, fun R v => ?_⟩
  have h := DFunLike.congr_fun (congrArg (fun t => (t.app R).hom) hj)
    (Specs.IntegralFibreReductivity.torusPoint D R v)
  change Specs.IntegralFibreReductivity.torusPoint D R v ≫ j.hom.hom.hom =
    (fibrePointsEquiv (splitTorus D) R).symm (e R (affineTorusPointEquiv R v)) at h
  rw [h]
  change (fibrePointsEquiv (splitTorus D) R) ((fibrePointsEquiv (splitTorus D) R).symm _) = _
  rw [MulEquiv.apply_symm_apply, hEval]
  rfl

end FieldBaseChange

section MarkedFieldFibres

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup)
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (diagonalTorus)
open Specs.IntegralSemisimpleModel
open Specs.OrderedRootProducts (Enumerates)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.RootGroups (rootPoint HasScalarAction)
open Specs.CharacterPairing (characterValue)
open Specs.IntegralRootRelations (upper lower diagonal)
open Specs.DiagonalizableGroups (IntegerCharacters)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitCoordinates)
open _root_.LinearAlgebraicGroups.RootData.RootGroups (additivePoints)
open private rootPoint_eq from LinearAlgebraicGroups.RootData.RootGroups

attribute [local instance] integerAlgebra

variable {k : Type u} [Field k] {D : BasedRootDatum.{u}} {G : IntegralGroup.{u}}
  {L : AdditiveLine.{u}} {A : Specs.RootGroups.AdditiveLine k}

private abbrev fieldRoot (a : A.group ≅ (fibre k).obj L.group)
    (root : D.I → (L.group ⟶ G)) (i : D.I) :=
  a.hom ≫ (fibre k).map (root i)

private abbrev fieldTorus (b : (diagonalTorus k D).val ≅ (fibre k).obj (splitTorus D))
    (torus : splitTorus D ⟶ G) :=
  b.hom ≫ (fibre k).map torus

private def productImageIso {C E : Type*} [Category C] [Category E]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory E] (F : C ⥤ E) [F.Monoidal]
    {X Y : C} {U V : E} (a : U ≅ F.obj X) (b : V ≅ F.obj Y) : U ⊗ V ≅ F.obj (X ⊗ Y) :=
  (a ⊗ᵢ b) ≪≫ Functor.Monoidal.μIso F X Y

@[reassoc]
private theorem productImageIso_fst {C E : Type*} [Category C] [Category E]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory E] (F : C ⥤ E) [F.Monoidal]
    {X Y : C} {U V : E} (a : U ≅ F.obj X) (b : V ≅ F.obj Y) :
    (productImageIso F a b).hom ≫ F.map (fst X Y) = fst U V ≫ a.hom := by
  simp only [productImageIso, Iso.trans_hom, tensorIso_hom, Functor.Monoidal.μIso_hom,
    Category.assoc, Functor.Monoidal.μ_fst, tensorHom_fst]

@[reassoc]
private theorem productImageIso_snd {C E : Type*} [Category C] [Category E]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory E] (F : C ⥤ E) [F.Monoidal]
    {X Y : C} {U V : E} (a : U ≅ F.obj X) (b : V ≅ F.obj Y) :
    (productImageIso F a b).hom ≫ F.map (snd X Y) = snd U V ≫ b.hom := by
  simp only [productImageIso, Iso.trans_hom, tensorIso_hom, Functor.Monoidal.μIso_hom,
    Category.assoc, Functor.Monoidal.μ_snd, tensorHom_snd]

private def fibreObjectIso {J : GroupScheme k} {K : IntegralGroup.{u}}
    (i : J ≅ (fibre k).obj K) : J.X ≅ (fibreScheme k).obj K.X :=
  (Grp.forget _).mapIso i

private def fibreRootFactorsIso (a : A.group ≅ (fibre k).obj L.group) :
    (l : List D.I) → Specs.OrderedRootProducts.product (fun _ : D.I => A.group.X) l ≅
      (fibreScheme k).obj (product (fun _ : D.I => L.group.X) l)
  | [] => Functor.Monoidal.εIso (fibreScheme k)
  | _ :: l => productImageIso (fibreScheme k) (fibreObjectIso a) (fibreRootFactorsIso a l)

set_option backward.isDefEq.respectTransparency false in
private theorem fibreRootProduct (a : A.group ≅ (fibre k).obj L.group)
    (root : D.I → (L.group ⟶ G)) (l : List D.I) :
    (fibreRootFactorsIso a l).hom ≫ (fibreScheme k).map (rootProduct L root l) =
      Specs.IntegralFibreReductivity.rootProduct A (fieldRoot a root) l := by
  let F := fibreScheme k
  letI : GrpObj (F.obj G.X) := ((fibre k).obj G).grp
  have hmul {X : IntegralScheme.{u}} (f g : X ⟶ G.X) :
      F.map (f * g) = (F.map f * F.map g : F.obj X ⟶ F.obj G.X) := F.map_mul f g
  induction l with
  | nil =>
    have h₁ : rootProduct L root [] = η[G.X] := by
      change toUnit (𝟙_ IntegralScheme.{u}) ≫ η[G.X] = η[G.X]
      rw [show toUnit (𝟙_ IntegralScheme.{u}) = 𝟙 _ from Subsingleton.elim _ _, Category.id_comp]
    rw [h₁]
    change η[((fibre k).obj G).X] =
      toUnit (𝟙_ (SchemeOver k)) ≫ η[((fibre k).obj G).X]
    rw [show toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ from Subsingleton.elim _ _, Category.id_comp]
  | cons i l ih =>
    let U := product (fun _ : D.I => L.group.X) l
    let W := Specs.OrderedRootProducts.product (fun _ : D.I => A.group.X) l
    let a' : A.group.X ≅ F.obj L.group.X := fibreObjectIso a
    let e : W ≅ F.obj U := fibreRootFactorsIso a l
    change (productImageIso F a' e).hom ≫ F.map
      ((fst L.group.X U ≫ (root i).hom.hom) * (snd L.group.X U ≫ rootProduct L root l)) =
      (fst A.group.X W ≫ (fieldRoot a root i).hom.hom) *
        (snd A.group.X W ≫ Specs.IntegralFibreReductivity.rootProduct A (fieldRoot a root) l)
    simp only [hmul, Functor.map_comp, MonObj.comp_mul,
      productImageIso_fst_assoc, productImageIso_snd_assoc]
    exact congrArg₂ (· * ·) rfl (congrArg (snd A.group.X W ≫ ·) ih)

set_option backward.isDefEq.respectTransparency false in
private theorem fibreCellMap_open (a : A.group ≅ (fibre k).obj L.group)
    (b : (diagonalTorus k D).val ≅ (fibre k).obj (splitTorus D))
    (root : D.I → (L.group ⟶ G)) (torus : splitTorus D ⟶ G)
    (l r : List D.I) (h : IsOpenImmersion (cellMap L torus root l r).left) :
    IsOpenImmersion (Specs.IntegralFibreReductivity.cellMap A (fieldTorus b torus)
      (fieldRoot a root) l r).left := by
  let F := fibreScheme k
  letI : GrpObj (F.obj G.X) := ((fibre k).obj G).grp
  let e := productImageIso F (fibreRootFactorsIso a l)
    (productImageIso F (fibreObjectIso b) (fibreRootFactorsIso a r))
  have hmul {X : IntegralScheme.{u}} (f g : X ⟶ G.X) :
      F.map (f * g) = (F.map f * F.map g : F.obj X ⟶ F.obj G.X) := F.map_mul f g
  have he : e.hom ≫ F.map (cellMap L torus root l r) =
      Specs.IntegralFibreReductivity.cellMap A (fieldTorus b torus) (fieldRoot a root) l r := by
    dsimp only [cellMap, Specs.IntegralFibreReductivity.cellMap, e]
    simp only [hmul, Functor.map_comp, MonObj.comp_mul,
      productImageIso_fst_assoc, productImageIso_snd_assoc]
    rw [fibreRootProduct, fibreRootProduct]
    rfl
  rw [← he, Over.comp_left]
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have : IsOpenImmersion (F.map (cellMap L torus root l r)).left :=
    MorphismProperty.of_isPullback
      (overPullback_map_isPullback (fibreBaseMap k) (cellMap L torus root l r)).flip h
  infer_instance

private def rankOneFibre (M : IntegralMarking D) (i : D.I) :
    Specs.IntegralFibreReductivity.rankOnePoints k ⟶ (groupPointsFunctor k).obj ((fibre k).obj M.group) :=
  let e : Specs.IntegralFibreReductivity.rankOnePoints k ⟶ restrictToIntegers k ⋙ rankOnePoints.{u} :=
    { app := fun _ => 𝟙 _
      naturality := fun _ _ _ => by
        apply GrpCat.ext
        intro x
        rfl }
  e ≫ Functor.whiskerLeft (restrictToIntegers k) (M.rankOne i) ≫ (fibrePointIso M.group).inv

private theorem rankOneFibre_apply (M : IntegralMarking D) (i : D.I) (R : TestAlgebra k)
    (x : Matrix.SpecialLinearGroup (Fin 2) R) :
    forgetFibrePoint M.group R ((rankOneFibre M i).app R x) =
      (M.rankOne i).app ((restrictToIntegers k).obj R) x :=
  (fibrePointsEquiv M.group R).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
private theorem markedCocharacter_point (D : BasedRootDatum.{u}) (y : D.Y)
    (R : TestAlgebra k) (s : Rˣ) :
    cocharacterPoint (Specs.IntegralFibreDatum.markedCocharacter D y) R s =
      Specs.IntegralFibreReductivity.torusPoint D R
        (Specs.IntegralFibreReductivity.cocharacter D y R s) := by
  let m : Multiplicative D.X →* IntegerCharacters.{u} :=
    { toFun := fun x => ⟨Multiplicative.ofAdd (D.datum.toLinearMap x.toAdd y)⟩
      map_one' := by
        change ULift.up (Multiplicative.ofAdd (D.datum.toLinearMap 0 y)) = _
        simp
        rfl
      map_mul' := by
        intro x z
        change ULift.up (Multiplicative.ofAdd (D.datum.toLinearMap (x.toAdd + z.toAdd) y)) =
          ULift.up (Multiplicative.ofAdd
            (D.datum.toLinearMap x.toAdd y + D.datum.toLinearMap z.toAdd y))
        simp }
  let g := (MonoidAlgebra.mapDomainBialgHom k m).toAlgHom
  change affineMap (unitCoordinates R s) ≫ affineMap g = affineMap (torusEvaluation _)
  rw [affineMap_comp]
  congr 1
  apply MonoidAlgebra.algHom_ext
  · intro x
    rw [AlgHom.comp_apply, torusEvaluation_single]
    change unitCoordinates R s (MonoidAlgebra.mapDomainBialgHom k m
      (MonoidAlgebra.single x 1)) = _
    rw [MonoidAlgebra.mapDomainBialgHom_single, unitCoordinates, MonoidAlgebra.lift_single]
    simp only [MonoidHom.comp_apply, one_smul]
    rfl
  · exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1100000 in
private theorem fieldRealization_of_integralMarking (D : BasedRootDatum.{u})
    (hss : RootData.rationalRootAnnihilator D.datum = ⊥)
    (hspan : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) (M : IntegralMarking D)
    (l r : List D.I) (hl : Enumerates l {j | ¬ D.base.IsPos j}) (hr : Enumerates r {j | D.base.IsPos j}) :
    ∃ (A : Specs.RootGroups.AdditiveLine k) (F : Specs.RationalRealization.Realization D A)
      (e : (fibre k).obj M.group ≅ F.pinned.pair.G.val)
      (t : (fibre k).obj (splitTorus D) ≅ F.pinned.pair.T.group)
      (z : ∀ a : D.I, Specs.Pinning.RootCoordinate A F.pinned.pair.T
        (F.pinned.roots (F.datumIso.val.indexEquiv a)).val (F.datumIso.val.indexEquiv a).val),
      ((fibre k).map M.torus) ≫ e.hom = t.hom ≫ F.pinned.pair.T.inclusion ∧
      (∀ a : D.base.support, z a.val = F.pinned.pin (F.simpleRoot a)) ∧
      (∀ (R : TestAlgebra k) (s : GroupPoints ((fibre k).obj (splitTorus D)) R)
          (v : TorusValues D (CommAlgCat.of Integers.{u} R)),
        forgetFibrePoint (splitTorus D) R s = torusPoint D (CommAlgCat.of Integers.{u} R) v →
        ∀ x : D.X, characterValue (Additive.toMul (F.datumIso.val.weightEquiv x)) R
          (s ≫ t.hom.hom.hom) = (v (Multiplicative.ofAdd x) : R)) ∧
      ∀ (a : D.I) (R : TestAlgebra k) (x : R),
        forgetFibrePoint M.group R
          (rootPoint ((z a).val.hom ≫ (F.pinned.roots (F.datumIso.val.indexEquiv a)).val.inclusion ≫ e.inv)
            R x) =
          M.line.point (CommAlgCat.of Integers.{u} R) x ≫ (M.root a).hom.hom := by
  let F := fibreScheme k
  let H := (fibre k).obj M.group
  have : IsAffine M.group.X.left := M.affine
  have : Smooth M.group.X.hom := M.smooth
  have : GeometricallyConnected M.group.X.hom := M.connected
  have : QuasiCompact M.group.X.hom := M.quasiCompact
  have hH : Smooth H.X.hom := inferInstanceAs (Smooth (pullback.snd M.group.X.hom (fibreBaseMap k)))
  have hC : GeometricallyConnected H.X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd M.group.X.hom (fibreBaseMap k)))
  let H₀ : AffineAlgebraicGroup k :=
    ⟨H, fibre_isAffine M.group, inferInstance, inferInstanceAs
      (QuasiCompact (pullback.snd M.group.X.hom (fibreBaseMap k)))⟩
  obtain ⟨ops, hd, he, hi, _⟩ := _root_.LinearAlgebraicGroups.StandardGroups.additiveGroupSpecification k
  let A : Specs.RootGroups.AdditiveLine k := ⟨ops, hd, he, hi⟩
  obtain ⟨a, ha⟩ := exists_additiveFibreIso M.line A
  obtain ⟨b, hb⟩ := exists_torusFibreIso (k := k) D
  let t := fieldTorus b M.torus
  let x := fieldRoot a M.root
  have ht : IsClosedImmersion t.hom.hom.left := by
    have : IsClosedImmersion (F.map M.torus.hom.hom).left :=
      MorphismProperty.of_isPullback
        (overPullback_map_isPullback (fibreBaseMap k) M.torus.hom.hom).flip M.torusClosed
    have : IsIso b.hom.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso b.hom
    change IsClosedImmersion (b.hom.hom.hom.left ≫ (F.map M.torus.hom.hom).left)
    infer_instance
  have hx (i : D.I) : IsClosedImmersion (x i).hom.hom.left := by
    have : IsClosedImmersion (F.map (M.root i).hom.hom).left :=
      MorphismProperty.of_isPullback
        (overPullback_map_isPullback (fibreBaseMap k) (M.root i).hom.hom).flip (M.rootClosed i)
    have : IsIso a.hom.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso a.hom
    change IsClosedImmersion (a.hom.hom.hom.left ≫ (F.map (M.root i).hom.hom).left)
    infer_instance
  have hcell := fibreCellMap_open a b M.root M.torus l r (M.openCell l r hl hr)
  have htp (R : TestAlgebra k) (v : TorusValues D ((restrictToIntegers k).obj R)) :
      forgetFibrePoint M.group R (Specs.IntegralFibreReductivity.torusPoint D R v ≫ t.hom.hom) =
        torusPoint D ((restrictToIntegers k).obj R) v ≫ M.torus.hom.hom := by
    change forgetFibrePoint M.group R (Specs.IntegralFibreReductivity.torusPoint D R v ≫
      (b.hom.hom.hom ≫ ((fibre k).map M.torus).hom.hom)) = _
    rw [← Category.assoc, forgetFibrePoint_comp, hb]
  have hxp (i : D.I) (R : TestAlgebra k) (z : R) :
      forgetFibrePoint M.group R (rootPoint (x i) R z) =
        M.line.point ((restrictToIntegers k).obj R) z ≫ (M.root i).hom.hom := by
    rw [rootPoint_eq]
    change forgetFibrePoint M.group R (additivePoints A R z ≫
      (a.hom.hom.hom ≫ ((fibre k).map (M.root i)).hom.hom)) = _
    rw [← Category.assoc, forgetFibrePoint_comp, ← rootPoint_eq, ha]
  have hConj (R : TestAlgebra k) (v : Specs.IntegralFibreReductivity.TorusValues D R)
      (i : D.I) (z : R) :
      let g : GroupPoints H R := Specs.IntegralFibreReductivity.torusPoint D R v ≫ t.hom.hom
      g * rootPoint (x i) R z * g⁻¹ =
        rootPoint (x i) R ((v (Multiplicative.ofAdd (D.datum.root i)) : R) * z) := by
    apply (fibrePointsEquiv M.group R).injective
    rw [map_mul, map_mul, map_inv]
    change forgetFibrePoint M.group R (_ ≫ t.hom.hom) * forgetFibrePoint M.group R (rootPoint (x i) R z) *
      (forgetFibrePoint M.group R (_ ≫ t.hom.hom))⁻¹ = forgetFibrePoint M.group R (rootPoint (x i) R _)
    rw [htp, hxp, hxp]
    exact M.conjugation ((restrictToIntegers k).obj R) v i z
  let rank := rankOneFibre (k := k) M
  have hu (i : D.I) (R : TestAlgebra k) (z : R) :
      (rank i).app R (upper z) = rootPoint (x i) R z := by
    apply (forgetFibrePoint_bijective M.group R).injective
    rw [rankOneFibre_apply, hxp]
    exact M.rankOneUpper i ((restrictToIntegers k).obj R) z
  have hd (i : D.I) (R : TestAlgebra k) (z : R) :
      (rank i).app R (lower z) = rootPoint (x (D.datum.reflectionPerm i i)) R z := by
    apply (forgetFibrePoint_bijective M.group R).injective
    rw [rankOneFibre_apply, hxp]
    exact M.rankOneLower i ((restrictToIntegers k).obj R) z
  have hc (i : D.I) (R : TestAlgebra k) (s : Rˣ) :
      (rank i).app R (diagonal s) =
        Specs.IntegralFibreReductivity.torusPoint D R
          (Specs.IntegralFibreReductivity.cocharacter D (D.datum.coroot i) R s) ≫ t.hom.hom := by
    apply (forgetFibrePoint_bijective M.group R).injective
    rw [rankOneFibre_apply, htp]
    exact M.rankOneDiagonal i ((restrictToIntegers k).obj R) s
  let N : Specs.IntegralFibreReductivity.Marking D H :=
    ⟨A, t, ht, x, hx, hConj, l, r, hl, hr, hcell, rank, hu, hd, hc⟩
  obtain ⟨hreductive, hmax⟩ :=
    _root_.LinearAlgebraicGroups.IntegralFibreReductivity.fibreReductivity k D hss hspan H₀ hH hC N
  have hchar (w : D.X) (R : TestAlgebra k) (v : Specs.IntegralFibreReductivity.TorusValues D R) :
      characterValue (Specs.IntegralFibreDatum.markedCharacter D w) R
        (Specs.IntegralFibreReductivity.torusPoint D R v) = (v (Multiplicative.ofAdd w) : R) := by
    exact (IntegralFibreDatum.markedCharacter_value (D := D) w R (torusEvaluation v)).trans
      (torusEvaluation_single v _)
  have hscalar (i : D.I) :
      HasScalarAction (⟨(diagonalTorus k D).val, t, ht⟩ : Specs.ClosedSubgroup H)
        (Specs.IntegralFibreDatum.markedCharacter D (D.datum.root i)) (x i) := by
    intro R s z
    obtain ⟨v, rfl⟩ := (affineTorusPointEquiv (k := k) R).surjective s
    change _ = rootPoint (x i) R (characterValue (Specs.IntegralFibreDatum.markedCharacter D
      (D.datum.root i)) R (Specs.IntegralFibreReductivity.torusPoint D R v) * z)
    rw [hchar]
    exact hConj R v i z
  have hProduct (order : List D.I) :
      Specs.IntegralFibreDatum.rootProduct (A := A) x order =
        Specs.IntegralFibreReductivity.rootProduct A x order := by
    induction order with
    | nil => rfl
    | cons j order ih =>
      simp only [Specs.IntegralFibreDatum.rootProduct, Specs.IntegralFibreReductivity.rootProduct, ih]
  have hMap : Specs.IntegralFibreDatum.cellMap (A := A) t x l r =
      Specs.IntegralFibreReductivity.cellMap A t x l r := by
    simp only [Specs.IntegralFibreDatum.cellMap, Specs.IntegralFibreReductivity.cellMap, hProduct]
  have hcell' : IsOpenImmersion (Specs.IntegralFibreDatum.cellMap (A := A) t x l r).left :=
    hMap.symm ▸ hcell
  let P : Specs.IntegralFibreDatum.Marking D H₀ A :=
    ⟨t, ht, hmax, x, hx, hscalar, ⟨l, r, hl, hr, hcell'⟩, rank, hu, hd, fun i R s => by
      rw [markedCocharacter_point]
      exact hc i R s⟩
  obtain ⟨J⟩ := IntegralFibreDatum.integralFibreDatum D H₀ hreductive A P
  let J₀ := J.realization
  let z := fun i => J.coordinates (J.datumIso.val.indexEquiv i)
  refine ⟨A, J₀, Iso.refl _, b.symm, z, ?_, ?_, ?_, ?_⟩
  · change (fibre k).map M.torus ≫ 𝟙 _ = b.inv ≫ (b.hom ≫ (fibre k).map M.torus)
    rw [Category.comp_id, Iso.inv_hom_id_assoc]
  · intro i
    rfl
  · intro R s v hsv w
    have hs : s = Specs.IntegralFibreReductivity.torusPoint D R v ≫ b.hom.hom.hom :=
      (forgetFibrePoint_bijective (splitTorus D) R).injective (hsv.trans (hb R v).symm)
    have hid : b.hom.hom.hom ≫ b.inv.hom.hom = 𝟙 _ :=
      congrArg (fun f : (diagonalTorus k D).val ⟶ (diagonalTorus k D).val => f.hom.hom) b.hom_inv_id
    let χ : Specs.CharacterDescent.Character (diagonalTorus k D).val :=
      Additive.toMul (J.datumIso.val.weightEquiv w)
    have hp : s ≫ b.inv.hom.hom = Specs.IntegralFibreReductivity.torusPoint D R v := by
      rw [hs, Category.assoc, hid, Category.comp_id]
    change characterValue χ R (s ≫ b.inv.hom.hom) = _
    calc
      _ = characterValue (Specs.IntegralFibreDatum.markedCharacter D w) R
          (Specs.IntegralFibreReductivity.torusPoint D R v) :=
        congrArg₂ (fun c q => characterValue c R q) (J.character w) hp
      _ = _ := hchar w R v
  · intro i R y
    change forgetFibrePoint M.group R
      (rootPoint ((z i).val.hom ≫ (J.roots (J.datumIso.val.indexEquiv i)).val.inclusion ≫ 𝟙 H) R y) = _
    rw [Category.comp_id, show (z i).val.hom ≫ (J.roots (J.datumIso.val.indexEquiv i)).val.inclusion =
      x i from J.rootCoordinate i]
    exact hxp i R y

end MarkedFieldFibres

section IntegralConstruction

open CategoryTheory.Limits
open Specs.Pinning (BasedRootDatum)
open Specs.RationalRealization (RationalField)
open Specs.IntegralLattices (Index Negative Positive)
open Specs.IntegralSemisimpleModel
open Specs.OrderedRootProducts (Enumerates)

private theorem enumerates_subtype {I : Type u} {S : Set I} (l : List I) (h : Enumerates l S) :
    ∃ l' : List S, l'.map Subtype.val = l ∧ Enumerates l' Set.univ := by
  let l' := l.attach.map (fun i => (⟨i.val, (h.2 i.val).mp i.property⟩ : S))
  have hv : l'.map Subtype.val = l := by
    rw [List.map_map]
    exact List.attach_map_subtype_val l
  refine ⟨l', hv, List.Nodup.of_map Subtype.val (hv.symm ▸ h.1), ?_⟩
  intro i
  constructor
  · exact fun _ => Set.mem_univ _
  · intro _
    obtain ⟨j, hj, hj'⟩ := List.mem_map.mp (show i.val ∈ l'.map Subtype.val by
      rw [hv]
      exact (h.2 i.val).mpr i.property)
    exact (Subtype.ext hj' : j = i) ▸ hj

set_option maxHeartbeats 1900000 in
set_option backward.isDefEq.respectTransparency false in
private theorem integralMarking_exists (D : BasedRootDatum.{u})
    (hss : RootData.rationalRootAnnihilator D.datum = ⊥)
    (hspan : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) :
    Nonempty (IntegralMarking D) := by
  classical
  let : Fintype D.I := @Fintype.ofFinite _ D.finiteRoots
  let negative : List (Negative D) := Finset.univ.toList
  let positive : List (Positive D) := Finset.univ.toList
  have hn : Enumerates negative Set.univ := ⟨Finset.nodup_toList _, by simp [negative]⟩
  have hp : Enumerates positive Set.univ := ⟨Finset.nodup_toList _, by simp [positive]⟩
  obtain ⟨A, Q, z, s, h⟩ := IntegralLattices.integralLattices D hss hspan
  let : LieRing (Lie RationalField Q.pinned.pair.G.val) := s.lieRing
  let : LieAlgebra RationalField (Lie RationalField Q.pinned.pair.G.val) := s.lieAlgebra
  obtain ⟨_, _, _, _, hop, _, _, _, _, h⟩ := h
  obtain ⟨V, n, b, w, height, p, _, _, hb, hsort, hpHeight, hnHeight, hw, hcoeff, htest, hneg, hpos⟩ :=
    h negative positive hn hp
  obtain ⟨τ, hτ⟩ := exists_markedTorusIso Q
  obtain ⟨B₀, ⟨ε⟩⟩ := essImage_hopfSpec.mpr Q.pinned.pair.G.property.1
  let B := B₀.unop
  let ρ := representationOnHopfPoints B ε (rationalMatrixAction V b)
  let G := integralMatrixClosure B ρ
  let cell : Specs.OrderedRootProducts.RegularRootCell.{u} :=
    _root_.LinearAlgebraicGroups.RootData.OrderedRootProducts.regularRootCell
  have hneg₀ : IsOrderedRootChart false (Specs.IntegralLattices.orderedMatrix negative (fun a => p a.val)) :=
    ⟨hneg.1, hneg.2.1⟩
  have hpos₀ : IsOrderedRootChart true (Specs.IntegralLattices.orderedMatrix positive (fun a => p a.val)) :=
    ⟨hpos.1, hpos.2.1⟩
  obtain ⟨φ, hφ, hker, hId, _⟩ := matrixClosure_matches_integralCell V b cell negative positive hn hp
    w hb height hpHeight hnHeight p hcoeff hw hneg₀ hpos₀ B ε τ hτ
  obtain ⟨hG, _, hQ, hS, q, hq, hbase, hsection⟩ :=
    integralMatrixClosure_smoothChart D B ρ φ hφ hker hId
  let : IsAffine G.X.left := hG
  let : IsAffineHom G.X.hom := isAffineHom_of_isAffine _
  let : QuasiCompact G.X.hom := hQ
  let : Smooth G.X.hom := hS
  let : Algebra Integers.{u} RationalField.{u} := integerAlgebra _
  let : IsDomain Integers.{u} :=
    (ULift.ringEquiv : Integers.{u} ≃+* ℤ).toMulEquiv.isDomain ℤ
  let : IsFractionRing Integers.{u} RationalField.{u} := integers_isFractionRing
  let : Algebra Integers.{u} (IntegralCellCoordinates D) := integerAlgebra _
  let W := affineObject (k := Integers.{u}) (IntegralCellCoordinates D)
  let i₀ : W ⟶ G.X := Over.homMk q hbase
  let : IsOpenImmersion i₀.left := hq
  let : GeometricallyConnected W.hom := integralCell_geometricallyConnected D
  let s₀ : 𝟙_ IntegralScheme.{u} ⟶ W :=
    Over.homMk (Spec.map (CommRingCat.ofHom (cellIdentity D).toRingHom)) (by
      change Spec.map (CommRingCat.ofHom (cellIdentity D).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} (IntegralCellCoordinates D))) =
          𝟙 (Spec (CommRingCat.of Integers.{u}))
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      apply CommRingCat.hom_ext
      exact RingHom.ext (cellIdentity D).commutes)
  have hs₀ : s₀ ≫ i₀ = η[G.X] := Over.OverMorphism.ext hsection
  have hconn : GeometricallyConnected Q.pinned.pair.G.val.X.hom := Q.pinned.pair.reductive.2.1
  have hspace : ConnectedSpace Q.pinned.pair.G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton Q.pinned.pair.G.val.X.hom
  have : IsIso ε.hom.hom.hom.left := (Grp.forget _ ⋙ Over.forget _).map_isIso ε.hom
  have hB : ConnectedSpace (PrimeSpectrum B) :=
    ε.hom.hom.hom.left.homeomorph.connectedSpace_iff.mpr hspace
  have hgeneric := integralMatrixClosure_genericFibre_connected B ρ hB
  obtain ⟨H, j, _, hHA, hHS, hHQ, hHC, hj, hjRange, _, _, _⟩ :=
    exists_affineIdentityComponent_of_openChart ULift.ringEquiv G hgeneric i₀ s₀ hs₀
  let : Smooth H.X.hom := hHS
  let : IsOpenImmersion j.hom.hom.left := hj
  obtain ⟨T, X, hT, hX, hTmatrix, hXmatrix⟩ := exists_integralMarkings_of_lattices V b
    negative positive hn hp p hcoeff hneg hpos w hb hw B ε τ hτ
  let L := integralAdditiveLine.{u}
  let : GeometricallyConnected (splitTorus D).X.hom := integralSplitTorus_geometricallyConnected D
  let : GeometricallyConnected L.group.X.hom := integralAdditiveLine_geometricallyConnected L
  obtain ⟨t, htj, ht⟩ := exists_closedMap_in_identityComponent i₀ s₀ hs₀ j hjRange T hT
  have hRoot (a : D.I) := exists_closedMap_in_identityComponent i₀ s₀ hs₀ j hjRange (X a) (hX a)
  choose x hxj hx using hRoot
  let I := integralMatrixClosureEmbedding B ρ
  let J := j ≫ I
  have : IsClosedImmersion I.hom.hom.left := integralMatrixClosureEmbedding_isClosedImmersion B ρ
  have : Mono I.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : Mono J.hom.hom := inferInstanceAs (Mono (j.hom.hom ≫ I.hom.hom))
  have htMat (R : IntegralAlgebra.{u}) (v : TorusValues D R) :
      (relativeGLPointEquiv R (torusPoint D R v ≫ t.hom.hom ≫ J.hom.hom)).val =
        torusWeightMatrix (Multiplicative.ofAdd ∘ w) v := by
    change (relativeGLPointEquiv R
      (torusPoint D R v ≫ t.hom.hom ≫ j.hom.hom ≫ I.hom.hom)).val = _
    rw [← Category.assoc t.hom.hom, show t.hom.hom ≫ j.hom.hom = T.hom.hom from
      congrArg (fun f : splitTorus D ⟶ G => f.hom.hom) htj]
    exact hTmatrix R v
  have hxMat (a : D.I) (R : IntegralAlgebra.{u}) (v : R) :
      (relativeGLPointEquiv R (additivePoint R v ≫ (x a).hom.hom ≫ J.hom.hom)).val =
        integralPolynomialMatrix (p a) v := by
    change (relativeGLPointEquiv R
      (additivePoint R v ≫ (x a).hom.hom ≫ j.hom.hom ≫ I.hom.hom)).val = _
    rw [← Category.assoc (x a).hom.hom, show (x a).hom.hom ≫ j.hom.hom = (X a).hom.hom from
      congrArg (fun f : L.group ⟶ G => f.hom.hom) (hxj a)]
    exact hXmatrix a R v
  have hscale : Specs.IntegralRootCellOrders.ScalarAction w p := fun a R _ v y =>
    latticeRootMatrix_torusLaw V b w hb a (p a) (hcoeff a) τ hτ R v y
  have hconj := markedRootConjugation_of_matrix_law J L t x w p htMat hxMat
    (fun a R v y => hscale a R v y)
  have hp0 (a : D.I) (i j : Index.{u} n) : (p a i j).coeff 0 = (1 : Matrix _ _ ℤ) i j := by
    have hh := (latticeRootMatrix_laws V b a (p a) (hcoeff a)).1 Integers.{u}
    have h := congrArg (fun P : Matrix (Index.{u} n) (Index.{u} n) Integers.{u} => (P i j).down) hh
    change ((p a i j).eval₂ (Int.castRingHom Integers.{u}) 0).down = _ at h
    rw [Polynomial.eval₂_at_zero] at h
    change (p a i j).coeff 0 = ((1 : Matrix _ _ Integers.{u}) i j).down at h
    by_cases hij : i = j <;> simpa [Matrix.one_apply, hij] using h
  have hcharts (l : List (Negative D)) (r : List (Positive D))
      (hl : Enumerates l Set.univ) (hr : Enumerates r Set.univ) :
      IsOpenImmersion (cellMap L T X (l.map Subtype.val) (r.map Subtype.val)).left := by
    obtain ⟨hleft, hright⟩ := IntegralRootCellOrders.orderedRootCells w height p hsort hpHeight hnHeight
      hp0 hscale htest l r hl hr
    obtain ⟨ψ, hψ, hker', _, hψmat⟩ := matrixClosure_matches_integralCell V b cell l r hl hr
      w hb height hpHeight hnHeight p hcoeff hw hleft hright B ε τ hτ
    obtain ⟨q, hq, hqmat⟩ := matrixClosure_openChart_with_matrix_formula D B ρ l r w p
      hleft hright ψ hψ hker' hψmat
    apply integralCellMap_isOpen_of_matrix_formula I L T X w p hTmatrix hXmatrix
      _ _ (enumerates_subtype_values hl) (enumerates_subtype_values hr) q hq
    rw [List.map_map, List.map_map]
    exact hqmat
  have hopen : ∀ l r : List D.I, Enumerates l {a | ¬ D.base.IsPos a} →
      Enumerates r {a | D.base.IsPos a} → IsOpenImmersion (cellMap L t x l r).left := by
    intro l r hl hr
    obtain ⟨l', rfl, hl'⟩ := enumerates_subtype l hl
    obtain ⟨r', rfl, hr'⟩ := enumerates_subtype r hr
    apply integralCellMap_open_of_openSubgroup j
    rw [htj, show (fun a => x a ≫ j) = X from funext hxj]
    exact hcharts l' r' hl' hr'
  have hrank (a : D.I) := exists_integralRankOne hHA J L t x w p htMat hxMat hconj a
    (latticeRootMatrix_opposite hop V b w hb p hcoeff a)
  choose rank hUpper hLower hDiag using hrank
  exact ⟨⟨H, hHA, inferInstance, hHQ, hHS, hHC, L, t, ht, x, hx, hconj, hopen,
    rank, hUpper, hLower, hDiag⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The simply connected semisimple datum, with its fixed character lattice and
pinning, is realized by a smooth affine integral group. -/
theorem integralSemisimpleModel : Statement.{u} := by
  intro D hss hspan
  classical
  let : Fintype D.I := @Fintype.ofFinite _ D.finiteRoots
  let negative : List (Negative D) := Finset.univ.toList
  let positive : List (Positive D) := Finset.univ.toList
  have hnegative : Enumerates negative Set.univ := ⟨Finset.nodup_toList _, by simp [negative]⟩
  have hpositive : Enumerates positive Set.univ := ⟨Finset.nodup_toList _, by simp [positive]⟩
  obtain ⟨M⟩ := integralMarking_exists D hss hspan
  refine ⟨_root_.LinearAlgebraicGroups.IntegralFibreReductivity.primitiveCoroots D hspan, ⟨⟨M, ?_⟩⟩⟩
  intro k _
  exact fieldRealization_of_integralMarking D hss hspan M (negative.map Subtype.val)
    (positive.map Subtype.val) (enumerates_subtype_values hnegative) (enumerates_subtype_values hpositive)

end IntegralConstruction

end

end LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
