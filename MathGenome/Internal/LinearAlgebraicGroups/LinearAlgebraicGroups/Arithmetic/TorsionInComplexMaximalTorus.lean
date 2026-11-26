import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TorsionInComplexMaximalTorus
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelPositivity
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterDynamics
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriExist
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

namespace LinearAlgebraicGroups.TorsionInComplexMaximalTorus

set_option linter.style.haveILetI false

section Solvable

variable {K A : Type*} [Field K] [CharZero K] [Group A]

private theorem conjugate_into_additive_kernel (N : Subgroup A)
    (q : N →* Multiplicative K) (hq : Function.Surjective q)
    (t g : A) (c : K)
    (stable : ∀ x : N, t * x.val * t⁻¹ ∈ N)
    (scale : ∀ x : N, (q ⟨t * x.val * t⁻¹, stable x⟩).toAdd = c * (q x).toAdd)
    (m : ℕ) (hm : m ≠ 0) (hg : g ^ m = 1) (ht : t ^ m = 1)
    (hu : g * t⁻¹ ∈ N) :
    ∃ x : N, ∃ y : q.ker, x.val⁻¹ * g * x.val * t⁻¹ = y.val.val := by
  let u : N := ⟨g * t⁻¹, hu⟩
  let σ (x : N) : N := ⟨t * x.val * t⁻¹, stable x⟩
  have hx : ∃ x : N, (1 - c) * (q x).toAdd = (q u).toAdd := by
    by_cases hc : c = 1
    · let v : ℕ → N := Nat.rec 1 (fun _ x => u * σ x)
      have hv (n : ℕ) : (v n).val = g ^ n * (t ^ n)⁻¹ := by
        induction n with
        | zero => simp [v]
        | succ n ih =>
          change (g * t⁻¹) * (t * (v n).val * t⁻¹) = g ^ (n + 1) * (t ^ (n + 1))⁻¹
          rw [ih, pow_succ' g, pow_succ' t]
          group
      have hqv (n : ℕ) : (q (v n)).toAdd = (n : K) * (q u).toAdd := by
        induction n with
        | zero => simp [v]
        | succ n ih =>
          change (q (u * σ (v n))).toAdd = _
          rw [map_mul q, toAdd_mul, show (q (σ (v n))).toAdd = _ from scale (v n),
            hc, one_mul, ih, Nat.cast_succ, add_mul, one_mul, add_comm]
      have hv₀ : v m = 1 := by
        apply Subtype.ext
        rw [hv, hg, ht, inv_one, mul_one]
        rfl
      have hzero : (m : K) * (q u).toAdd = 0 := by
        rw [← hqv, hv₀, map_one, toAdd_one]
      have hu₀ := (mul_eq_zero.mp hzero).resolve_left (Nat.cast_ne_zero.mpr hm)
      exact ⟨1, by simp [hc, hu₀]⟩
    · obtain ⟨x, hx⟩ := hq (Multiplicative.ofAdd ((q u).toAdd / (1 - c)))
      refine ⟨x, ?_⟩
      rw [hx, toAdd_ofAdd, mul_comm]
      exact div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm hc))
  obtain ⟨x, hx⟩ := hx
  refine ⟨x, ⟨x⁻¹ * u * σ x, ?_⟩, ?_⟩
  · change q (x⁻¹ * u * σ x) = 1
    apply Multiplicative.toAdd.injective
    rw [map_mul q, map_mul q, map_inv q, toAdd_mul, toAdd_mul,
      toAdd_inv, toAdd_one,
      show (q (σ x)).toAdd = _ from scale x, ← hx]
    ring
  · change x.val⁻¹ * g * x.val * t⁻¹ = x.val⁻¹ * (g * t⁻¹) * (t * x.val * t⁻¹)
    group

/-- A finite-order element with the same image as a finite-order lift is
conjugate to that lift if the kernel has a stable filtration with additive
factors on which the lift acts by scalars. -/
theorem conjugate_of_additive_series (N : ℕ → Subgroup A) (n : ℕ)
    (t g : A) (m : ℕ) (hm : m ≠ 0) (hg : g ^ m = 1) (ht : t ^ m = 1)
    (hbottom : N n = ⊥) (hu : g * t⁻¹ ∈ N 0)
    (stable : ∀ i < n, ∀ x : N i, t * x.val * t⁻¹ ∈ N i)
    (factors : ∀ i (hi : i < n), ∃ (q : N i →* Multiplicative K) (c : K),
      Function.Surjective q ∧
      (∀ x : N i, (q ⟨t * x.val * t⁻¹, stable i hi x⟩).toAdd = c * (q x).toAdd) ∧
      (∀ y : q.ker, y.val.val ∈ N (i + 1))) :
    ∃ a : A, a⁻¹ * g * a = t := by
  have stage (i : ℕ) (hi : i ≤ n) : ∃ a : A, a⁻¹ * g * a * t⁻¹ ∈ N i := by
    induction i with
    | zero => exact ⟨1, by simpa using hu⟩
    | succ i ih =>
      obtain ⟨a, ha⟩ := ih (Nat.le_of_succ_le hi)
      have hi' : i < n := hi
      obtain ⟨q, c, hq, scale, kernel⟩ := factors i hi'
      have hpow : (a⁻¹ * g * a) ^ m = 1 := by
        have h := conj_pow (i := m) (a := a⁻¹) (b := g)
        simpa [hg] using h
      obtain ⟨x, y, hy⟩ := conjugate_into_additive_kernel (N i) q hq t
        (a⁻¹ * g * a) c (stable i hi') scale m hm hpow ht ha
      refine ⟨a * x.val, ?_⟩
      have he : (a * x.val)⁻¹ * g * (a * x.val) * t⁻¹ = y.val.val := by
        rw [← hy]
        group
      rw [he]
      exact kernel y
  obtain ⟨a, ha⟩ := stage n le_rfl
  rw [hbottom, Subgroup.mem_bot] at ha
  exact ⟨a, mul_inv_eq_one.mp ha⟩

end Solvable

section Incidence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup GroupScheme)
open Specs.QuotientEmbedding (Presentation)

universe u

variable {k : Type u} [Field k] {G : GroupScheme k} {B : ClosedSubgroup G}

open private quotientAct quotientAct_comp quotientAct_projection rationalLift
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private exists_rational_point from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit
open private projection_eq_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding

/-- The incidence scheme of elements and flags fixed by those elements. -/
noncomputable def fixedFlagIncidence (Q : Presentation B) : SchemeOver k :=
  equalizer (quotientAct Q (prod.fst : G.X ⨯ Q.scheme ⟶ G.X) (prod.snd : G.X ⨯ Q.scheme ⟶ Q.scheme)) (prod.snd : G.X ⨯ Q.scheme ⟶ Q.scheme)

/-- The projection from the fixed-flag incidence scheme to the acting group. -/
noncomputable def fixedFlagProjection (Q : Presentation B) : fixedFlagIncidence Q ⟶ G.X :=
  equalizer.ι _ _ ≫ (prod.fst : G.X ⨯ Q.scheme ⟶ G.X)

theorem fixedFlagProjection_proper (Q : Presentation B) [IsProper Q.scheme.hom] :
    IsProper (fixedFlagProjection Q).left := by
  let act := quotientAct Q (prod.fst : G.X ⨯ Q.scheme ⟶ G.X) (prod.snd : G.X ⨯ Q.scheme ⟶ Q.scheme)
  let j := equalizer.ι act (prod.snd : G.X ⨯ Q.scheme ⟶ Q.scheme)
  let p := (prod.fst : G.X ⨯ Q.scheme ⟶ G.X)
  haveI : IsClosedImmersion j.left := by
    dsimp only [j]
    infer_instance
  haveI : IsProper p.left := by
    change IsProper (prod.fst : G.X ⨯ Q.scheme ⟶ G.X).left
    exact MorphismProperty.of_isPullback (P := @IsProper)
      (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd G.X Q.scheme)).flip inferInstance
  change IsProper (j.left ≫ p.left)
  infer_instance

/-- The group elements fixing a flag form the image of a proper morphism. -/
theorem isClosed_range_fixedFlagProjection (Q : Presentation B) [IsProper Q.scheme.hom] :
    IsClosed (Set.range (fixedFlagProjection Q).left) := by
  letI := fixedFlagProjection_proper Q
  simpa only [Set.image_univ] using (fixedFlagProjection Q).left.isClosedMap Set.univ isClosed_univ

/-- Any scheme-valued conjugate of an element of the subgroup has a fixed
flag, namely the coset of the conjugating element. -/
theorem conjugate_factors_through_fixedFlagProjection (Q : Presentation B)
    {Y : SchemeOver k} (a : Y ⟶ G.X) (b : Y ⟶ B.group.X) :
    ∃ z : Y ⟶ fixedFlagIncidence Q,
      z ≫ fixedFlagProjection Q = a * (b ≫ B.inclusion.hom.hom) * a⁻¹ := by
  let t := a * (b ≫ B.inclusion.hom.hom) * a⁻¹
  let f := prod.lift t (a ≫ Q.projection)
  have hf : quotientAct Q t (a ≫ Q.projection) = a ≫ Q.projection := by
    rw [quotientAct_projection, eq_comm, projection_eq_iff]
    have h : a⁻¹ * (t * a) = b ≫ B.inclusion.hom.hom := by
      dsimp only [t]
      group
    exact ⟨b, h.symm⟩
  let v : G.X ⨯ Q.scheme ⟶ G.X := prod.fst
  let w : G.X ⨯ Q.scheme ⟶ Q.scheme := prod.snd
  let act := quotientAct Q v w
  have he : f ≫ act = f ≫ w := by
    dsimp only [act, v, w]
    rw [quotientAct_comp]
    simp only [f, prod.lift_fst, prod.lift_snd]
    exact hf
  refine ⟨equalizer.lift f he, ?_⟩
  change equalizer.lift f he ≫ equalizer.ι act w ≫ v = t
  rw [← Category.assoc, equalizer.lift_ι]
  exact prod.lift_fst _ _

/-- Over an algebraically closed field, a rational point in the image of the
incidence projection is conjugate to a rational point of the subgroup. -/
theorem conjugate_of_mem_fixedFlagProjection [IsAlgClosed k] (Q : Presentation B)
    [IsProper Q.scheme.hom] (t : 𝟙_ (SchemeOver k) ⟶ G.X)
    (ht : t.left (IsLocalRing.closedPoint k) ∈ Set.range (fixedFlagProjection Q).left) :
    ∃ (a : 𝟙_ (SchemeOver k) ⟶ G.X) (b : 𝟙_ (SchemeOver k) ⟶ B.group.X),
      a⁻¹ * t * a = b ≫ B.inclusion.hom.hom := by
  let p := fixedFlagProjection Q
  haveI : IsProper p.left := fixedFlagProjection_proper Q
  let F := pullback p t
  let q := pullback.snd p t
  have hpb := (IsPullback.of_hasPullback p t).map (Over.forget _)
  haveI : LocallyOfFiniteType q.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb
      (show LocallyOfFiniteType p.left from inferInstance)
  haveI : LocallyOfFiniteType F.hom := by
    rw [← Over.w q]
    change LocallyOfFiniteType (q.left ≫ 𝟙 _)
    infer_instance
  obtain ⟨z, hz⟩ := ht
  obtain ⟨w, _, _⟩ := Scheme.exists_preimage_of_isPullback hpb z
    (IsLocalRing.closedPoint k) hz
  letI : Nonempty F.left := ⟨w⟩
  obtain ⟨x⟩ := exists_rational_point F
  have hq : x ≫ q = 𝟙 _ := toUnit_unique _ _
  let y := x ≫ pullback.fst p t
  have hy : y ≫ p = t := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hq, Category.id_comp]
  let v : G.X ⨯ Q.scheme ⟶ G.X := prod.fst
  let w : G.X ⨯ Q.scheme ⟶ Q.scheme := prod.snd
  let act := quotientAct Q v w
  let j : fixedFlagIncidence Q ⟶ G.X ⨯ Q.scheme := equalizer.ι act w
  let flag := (y ≫ j) ≫ w
  have hfix : quotientAct Q t flag = flag := by
    have he : j ≫ act = j ≫ w := equalizer.condition act w
    have hp : (y ≫ j) ≫ v = t :=
      (Category.assoc y j v).trans hy
    unfold flag
    rw [← hp, ← quotientAct_comp]
    exact (Category.assoc y j act).trans
      ((congrArg (y ≫ ·) he).trans (Category.assoc y j w).symm)
  haveI := Q.finitePresentation
  obtain ⟨a, ha⟩ := rationalLift Q.projection Q.surjective inferInstance flag
  rw [← ha, quotientAct_projection, eq_comm, projection_eq_iff] at hfix
  obtain ⟨b, hb⟩ := hfix
  change b ≫ B.inclusion.hom.hom = a⁻¹ * (t * a) at hb
  exact ⟨a, b, by simpa only [mul_assoc] using hb.symm⟩

end Incidence

section Density

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj LaurentPolynomial

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme)
open Specs.EquivariantUnipotentSeries (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open CocharacterDynamics

open private affinePointEquiv affinePointEquiv_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent
open private evalLaurent evalLaurent_constants evalLaurent_parameter polynomialConstants
  polynomialConstants_zero polynomialConstants_laurent
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private algMapPoints algMapPoints_comp pointMap pointMap_natural multiply_isOpenImmersion
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterOpenCell
open private affine_tensor from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure

variable {k : Type u} [Field k] {G : GroupScheme k}

/-- A polynomial substitution fixing the variable is injective when its
coefficient map is injective after evaluation at zero. -/
private theorem polynomialSubstitution_injective {A R : Type*} [CommRing A]
    [CommRing R] (a : A →+* Polynomial R)
    (ha : Function.Injective ((Polynomial.evalRingHom 0).comp a)) :
    Function.Injective (Polynomial.eval₂RingHom a Polynomial.X) := by
  let F := Polynomial.eval₂RingHom a Polynomial.X
  have h0 (p : Polynomial A) :
      (F p).coeff 0 = ((Polynomial.evalRingHom 0).comp a) (p.coeff 0) := by
    rw [Polynomial.coeff_zero_eq_eval_zero (F p)]
    change Polynomial.evalRingHom (0 : R) (F p) = _
    have h : (Polynomial.evalRingHom 0).comp F =
        Polynomial.eval₂RingHom ((Polynomial.evalRingHom 0).comp a) 0 := by
      apply Polynomial.ringHom_ext
      · intro x
        simp [F]
      · simp [F]
    rw [← RingHom.comp_apply, h]
    exact Polynomial.eval₂_at_zero _
  apply (injective_iff_map_eq_zero F).2
  intro p
  induction p using Polynomial.recOnHorner with
  | M0 => simp
  | MC p c hp hc _ =>
    intro h
    have hz := h0 (p + Polynomial.C c)
    rw [h, Polynomial.coeff_zero, Polynomial.coeff_add, hp, Polynomial.coeff_C_zero,
      zero_add] at hz
    let ev := (Polynomial.evalRingHom (0 : R)).comp a
    exact (hc (ha (hz.symm.trans (map_zero ev).symm))).elim
  | MX p hp ih =>
    intro h
    rw [map_mul, show F Polynomial.X = Polynomial.X from Polynomial.eval₂_X _ _] at h
    have hp₀ : F p = 0 :=
      Polynomial.mul_X_pow_eq_zero (n := 1) (by simpa only [pow_one] using h)
    rw [ih hp₀, zero_mul]

/-- The same injectivity holds on the punctured line. -/
private theorem laurentSubstitution_injective {A R : TestAlgebra k}
    (a : A ⟶ polynomialAlgebra R)
    (ha : Function.Injective ((a ≫ polynomialEvaluate R 0).hom)) :
    Function.Injective
      (evalLaurent (a ≫ polynomialToLaurent R) (laurentParameter R)).hom := by
  let j := evalLaurent (a ≫ polynomialToLaurent R) (laurentParameter R)
  let F := Polynomial.eval₂RingHom a.hom.toRingHom Polynomial.X
  have hF : Function.Injective F := polynomialSubstitution_injective _ ha
  have hp : j.hom.toRingHom.comp Polynomial.toLaurent =
      Polynomial.toLaurent.comp F := by
    apply Polynomial.ringHom_ext
    · intro x
      change LaurentPolynomial.eval₂ (a ≫ polynomialToLaurent R).hom.toRingHom
        (laurentParameter R) (Polynomial.toLaurent (Polynomial.C x)) =
          Polynomial.toLaurent ((Polynomial.C x).eval₂ a.hom.toRingHom Polynomial.X)
      rw [Polynomial.toLaurent_C, LaurentPolynomial.eval₂_C, Polynomial.eval₂_C]
      rfl
    · change LaurentPolynomial.eval₂ (a ≫ polynomialToLaurent R).hom.toRingHom
        (laurentParameter R) (Polynomial.toLaurent Polynomial.X) =
          Polynomial.toLaurent (Polynomial.X.eval₂ a.hom.toRingHom Polynomial.X)
      rw [Polynomial.toLaurent_X, LaurentPolynomial.eval₂_T, zpow_one, Polynomial.eval₂_X,
        Polynomial.toLaurent_X]
      rfl
  apply (injective_iff_map_eq_zero j.hom).2
  intro q hq
  obtain ⟨n, p, h⟩ := LaurentPolynomial.exists_T_pow q
  have hzero : j.hom (Polynomial.toLaurent p) = 0 := by
    rw [h, map_mul, hq, zero_mul]
  change (j.hom.toRingHom.comp Polynomial.toLaurent) p = 0 at hzero
  rw [hp, RingHom.comp_apply, Polynomial.toLaurent_eq_zero] at hzero
  have hp₀ : p = 0 := hF (hzero.trans (map_zero F).symm)
  rw [hp₀, map_zero] at h
  exact (LaurentPolynomial.isUnit_T (n : ℤ)).mul_left_inj.mp (h.symm.trans (zero_mul _).symm)

private theorem denseRange_affinePoint_iff {A R : TestAlgebra k} [IsReduced A]
    {Y : SchemeOver k} (e : (testSpec k).obj (op A) ≅ Y) (a : A →ₐ[k] R) :
    DenseRange (affinePointEquiv e R a).left ↔ Function.Injective a := by
  let e' := (Over.forget _).mapIso e
  change DenseRange ((Spec.map (CommRingCat.ofHom a.toRingHom)) ≫ e'.hom) ↔ _
  change DenseRange (e'.hom ∘ PrimeSpectrum.comap a.toRingHom) ↔ _
  change Dense (Set.range (e'.schemeIsoToHomeo ∘ PrimeSpectrum.comap a.toRingHom)) ↔ _
  rw [Set.range_comp, e'.schemeIsoToHomeo.isDenseEmbedding.dense_image]
  change DenseRange (PrimeSpectrum.comap a.toRingHom) ↔ _
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, nilradical_eq_zero]
  change RingHom.ker a.toRingHom ≤ ⊥ ↔ Function.Injective a.toRingHom
  rw [le_bot_iff, RingHom.injective_iff_ker_eq_bot]

private theorem affineCoordinates_map {A R S : TestAlgebra k}
    {Y : SchemeOver k} (e : (testSpec k).obj (op A) ≅ Y) (a : R ⟶ S) (x : Points Y R) :
    (affinePointEquiv e S).symm (mapPoints a x) =
      a.hom.comp ((affinePointEquiv e R).symm x) := by
  apply (affinePointEquiv e S).injective
  rw [Equiv.apply_symm_apply, affinePointEquiv_natural, Equiv.apply_symm_apply]

private noncomputable abbrev pointParameter (c : Cocharacter G) (R : TestAlgebra k) :
    GroupPoints G (laurentAlgebra R) :=
  cocharacterPoint c _ (laurentParameter R)

private theorem evalLaurent_pointParameter {A S : TestAlgebra k} (c : Cocharacter G)
    (a : A ⟶ S) (s : Sˣ) :
    algMapPoints G (evalLaurent a s) (pointParameter c A) = cocharacterPoint c S s := by
  exact (mapPoints_cocharacterPoint (evalLaurent a s) c _).trans
    (congrArg (cocharacterPoint c S) (evalLaurent_parameter a s))

/-- Translating the punctured family on the right by the cocharacter
gives a dense image when the polynomial family is dense at zero. -/
private theorem denseRange_translate_polynomialFamily
    (hAff : IsAffine G.X.left) (hInt : IsIntegral G.X.left)
    (c : Cocharacter G) {R : TestAlgebra k} (f : GroupPoints G (polynomialAlgebra R))
    (h : DenseRange (mapPoints (polynomialEvaluate R 0) f).left) :
    DenseRange (algMapPoints G (polynomialToLaurent R) f * pointParameter c R).left := by
  obtain ⟨Aop, ⟨e₀⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hAff
  let A := Aop.unop
  let e : (testSpec k).obj (op A) ≅ G.X := e₀
  let e' : Spec (CommRingCat.of A) ≅ G.X.left := (Over.forget _).mapIso e
  haveI : IsIntegral G.X.left := hInt
  haveI : IsDomain A := (affine_isIntegral_iff (CommRingCat.of A)).mp
    (IsIntegral.of_isIso e'.inv)
  let φ : A ⟶ polynomialAlgebra R := CommAlgCat.ofHom ((affinePointEquiv e _).symm f)
  have hφ : Function.Injective (φ ≫ polynomialEvaluate R 0).hom := by
    have hi := (denseRange_affinePoint_iff e
      ((affinePointEquiv e _).symm (mapPoints (polynomialEvaluate R 0) f))).mp
      (by rwa [Equiv.apply_symm_apply])
    rw [affineCoordinates_map] at hi
    exact hi
  let ψ := evalLaurent (φ ≫ polynomialToLaurent R) (laurentParameter R)
  have hψ : Function.Injective ψ.hom := laurentSubstitution_injective φ hφ
  let x : GroupPoints G (laurentAlgebra A) := mapPoints (laurentConstants A) e.hom
  let xPlus := x * pointParameter c A
  let xMinus := x * (pointParameter c A)⁻¹
  let b : A ⟶ laurentAlgebra A := CommAlgCat.ofHom ((affinePointEquiv e _).symm xMinus)
  let ρ := evalLaurent b (laurentParameter A)
  have he : algMapPoints G ρ x = xMinus := by
    change mapPoints ρ (mapPoints (laurentConstants A) e.hom) = xMinus
    rw [← mapPoints_comp, evalLaurent_constants]
    exact (affinePointEquiv e _).apply_symm_apply xMinus
  have hρ : mapPoints ρ xPlus = x := by
    change algMapPoints G ρ (x * pointParameter c A) = x
    rw [map_mul, he, evalLaurent_pointParameter]
    simp [xMinus, mul_assoc]
  have hxcoords : (affinePointEquiv e _).symm x = (laurentConstants A).hom := by
    change (affinePointEquiv e _).symm
      (affinePointEquiv e _ (laurentConstants A).hom) = _
    exact Equiv.symm_apply_apply _ _
  have hd : Function.Injective ((affinePointEquiv e _).symm xPlus) := by
    have eq := congrArg (affinePointEquiv e _).symm hρ
    rw [affineCoordinates_map, hxcoords] at eq
    intro a₁ a₂ hEq
    have hC : (LaurentPolynomial.C a₁ : LaurentPolynomial A) = LaurentPolynomial.C a₂ := by
      change (laurentConstants A).hom a₁ = (laurentConstants A).hom a₂
      rw [← eq]
      exact congrArg ρ.hom hEq
    simpa using congrArg (fun z : LaurentPolynomial A => z.coeff 0) hC
  have hψx : algMapPoints G ψ x = algMapPoints G (polynomialToLaurent R) f := by
    change mapPoints ψ (mapPoints (laurentConstants A) e.hom) = _
    rw [← mapPoints_comp, evalLaurent_constants, mapPoints_comp]
    have hfx : mapPoints φ e.hom = f := (affinePointEquiv e _).apply_symm_apply f
    rw [hfx]
    rfl
  have hψPlus : mapPoints ψ xPlus =
      algMapPoints G (polynomialToLaurent R) f * pointParameter c R := by
    change algMapPoints G ψ (x * pointParameter c A) = _
    rw [map_mul, hψx, evalLaurent_pointParameter]
  rw [← hψPlus, ← (affinePointEquiv e _).apply_symm_apply (mapPoints ψ xPlus)]
  apply (denseRange_affinePoint_iff e _).2
  rw [affineCoordinates_map]
  exact hψ.comp hd

open Specs.QuotientEmbedding (Presentation)
open Specs.SchemeDerivedGroup (IsSubgroupOf)

/-- Opposite contraction specializes the translated conjugation family to
big-cell multiplication. Properness then gives a flag over every point. -/
private theorem fixedFlagProjection_range_of_bigCell
    (H : AffineAlgebraicGroup k) [Smooth H.val.X.hom] [IsIntegral H.val.X.left]
    (T : ClosedSubgroup H.val) (c : Cocharacter T.group)
    (D : LimitDecomposition (c ≫ T.inclusion))
    (E : LimitDecomposition (oppositeCocharacter (c ≫ T.inclusion)))
    (hTB : IsSubgroupOf T D.parabolic) (Q : Presentation D.parabolic)
    [IsProper Q.scheme.hom] :
    Set.range (fixedFlagProjection Q).left = Set.univ := by
  obtain ⟨j, hj⟩ := hTB
  let q : Cocharacter D.parabolic.group := oppositeCocharacter c ≫ j
  let d := oppositeCocharacter (c ≫ T.inclusion)
  have hq : q ≫ D.parabolic.inclusion = d := by
    simp only [q, d, oppositeCocharacter, Category.assoc, hj]
  let X := E.contracting.group.X ⊗ D.parabolic.group.X
  let m : X ⟶ H.val.X := multiplyFactors E.contracting.inclusion D.parabolic.inclusion
  haveI : IsOpenImmersion m.left := multiply_isOpenImmersion H (c ≫ T.inclusion) D E
  haveI : Nonempty X.left :=
    ⟨(lift (1 : 𝟙_ (SchemeOver k) ⟶ E.contracting.group.X)
      (1 : 𝟙_ (SchemeOver k) ⟶ D.parabolic.group.X)).left (IsLocalRing.closedPoint k)⟩
  have hDense : DenseRange m.left :=
    m.left.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _
  letI : IsAffine E.contracting.group.X.left :=
    (affineAlgebraicSubgroup E.contracting H.property.1 H.property.2.1 H.property.2.2).property.1
  letI : IsAffine D.parabolic.group.X.left :=
    (affineAlgebraicSubgroup D.parabolic H.property.1 H.property.2.1 H.property.2.2).property.1
  obtain ⟨Rop, ⟨e₀⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr
    (affine_tensor (A := E.contracting.group.X) (B := D.parabolic.group.X))
  let R := Rop.unop
  let e : (testSpec k).obj (op R) ≅ X := e₀
  let u : GroupPoints E.contracting.group R := e.hom ≫ fst _ _
  let b : GroupPoints D.parabolic.group R := e.hom ≫ snd _ _
  let a : GroupPoints H.val R := pointMap E.contracting.inclusion R u
  let y : GroupPoints H.val R := pointMap D.parabolic.inclusion R b
  have hay : a * y = e.hom ≫ m := by
    change (e.hom ≫ fst _ _ ≫ E.contracting.inclusion.hom.hom) *
      (e.hom ≫ snd _ _ ≫ D.parabolic.inclusion.hom.hom) = _
    simp only [m, multiplyFactors, MonObj.comp_mul]
  have hDense₀ : DenseRange (a * y).left := by
    have h := hDense.comp ((Over.forget _).mapIso e).schemeIsoToHomeo.surjective.denseRange
      m.left.continuous
    rwa [hay]
  have hlim : HasLimit d a⁻¹ 1 := (E.contracting_points R _).2
    ⟨u⁻¹, map_inv (pointMap E.contracting.inclusion R).hom u⟩
  obtain ⟨l, hl, hl₀⟩ := hlim
  let f := algMapPoints H.val (polynomialConstants R) (a * y) * l
  have hf₀ : mapPoints (polynomialEvaluate R 0) f = a * y := by
    change algMapPoints H.val (polynomialEvaluate R 0)
      (algMapPoints H.val (polynomialConstants R) (a * y) * l) = a * y
    rw [map_mul, show algMapPoints H.val (polynomialEvaluate R 0) l = 1 from hl₀, mul_one]
    change mapPoints (polynomialEvaluate R 0) (mapPoints (polynomialConstants R) (a * y)) = _
    rw [← mapPoints_comp, polynomialConstants_zero]
    simp [mapPoints]
  have hF := denseRange_translate_polynomialFamily H.property.1 (by infer_instance) d f
    (by rw [hf₀]; exact hDense₀)
  let A := algMapPoints H.val (laurentConstants R) a
  let Y := algMapPoints H.val (laurentConstants R) y
  let L := pointParameter d R
  let b' := algMapPoints D.parabolic.group (laurentConstants R) b * pointParameter q R
  have hb' : pointMap D.parabolic.inclusion (laurentAlgebra R) b' = Y * L := by
    change (pointMap D.parabolic.inclusion _).hom
      (algMapPoints D.parabolic.group (laurentConstants R) b * pointParameter q R) = _
    rw [map_mul, ← pointMap_natural]
    congr 1
    change (unitPoint (laurentAlgebra R) (laurentParameter R) ≫ q.hom.hom) ≫
      D.parabolic.inclusion.hom.hom =
      unitPoint (laurentAlgebra R) (laurentParameter R) ≫ d.hom.hom
    rw [Category.assoc, ← show (q ≫ D.parabolic.inclusion).hom.hom =
      q.hom.hom ≫ D.parabolic.inclusion.hom.hom from rfl, hq]
  have hfL : algMapPoints H.val (polynomialToLaurent R) f * L = A * (Y * L) * A⁻¹ := by
    change algMapPoints H.val (polynomialToLaurent R)
      (algMapPoints H.val (polynomialConstants R) (a * y) * l) * L = _
    rw [map_mul, ← algMapPoints_comp, polynomialConstants_laurent, map_mul,
      show algMapPoints H.val (polynomialToLaurent R) l = orbit d a⁻¹ from hl]
    change (A * Y) * (L * algMapPoints H.val (laurentConstants R) a⁻¹ * L⁻¹) * L = _
    rw [map_inv]
    change (A * Y) * (L * A⁻¹ * L⁻¹) * L = A * (Y * L) * A⁻¹
    group
  obtain ⟨z, hz⟩ := conjugate_factors_through_fixedFlagProjection Q A b'
  have hz' : z ≫ fixedFlagProjection Q = algMapPoints H.val (polynomialToLaurent R) f * L := by
    rw [hfL, ← hb']
    exact hz
  have hSubset : Set.range (algMapPoints H.val (polynomialToLaurent R) f * L).left ⊆
      Set.range (fixedFlagProjection Q).left := by
    rintro _ ⟨x, rfl⟩
    exact ⟨z.left x, by rw [← hz', Over.comp_left, Scheme.Hom.comp_apply]⟩
  have hd := dense_iff_closure_eq.mp (hF.mono hSubset)
  rwa [(isClosed_range_fixedFlagProjection Q).closure_eq] at hd

end Density

section SplitExtension

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme IsNormalSubgroup subgroupConjugation)
open Specs.EquivariantUnipotentSeries (GroupPoints onPoints IsSplitTorus)
open Specs.Unipotent (IsUnipotent IsFppfGroupQuotient closedSubgroupAlgebraicGroup ClosedSeries)

open private rationalLift from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private Unipotent.onPoints_comp Unipotent.onPoints_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private Unipotent.closedSeries_inclusion_closed
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

variable {k : Type u} [Field k] [IsAlgClosed k]

local notation "R₀" => CommAlgCat.of k k

private noncomputable def rationalPointSource (k : Type u) [Field k] :
    (testSpec k).obj (op (CommAlgCat.of k k)) ≅ 𝟙_ (SchemeOver k) :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
    change (𝟙 _) ≫ (𝟙 _) = Spec.map (𝟙 (CommRingCat.of k))
    rw [Spec.map_id, Category.comp_id])

private theorem onRationalPoints_surjective {G H : GroupScheme k} (f : G ⟶ H)
    (hf : Surjective f.hom.hom.left) (hft : LocallyOfFiniteType f.hom.hom.left) :
    Function.Surjective (onPoints f R₀) := by
  let e := rationalPointSource k
  intro y
  change Points H.X R₀ at y
  obtain ⟨x, hx⟩ := rationalLift f.hom.hom hf hft (e.inv ≫ y)
  refine ⟨e.hom ≫ x, ?_⟩
  change (e.hom ≫ x) ≫ f.hom.hom = y
  rw [Category.assoc, hx, Iso.hom_inv_id_assoc]

omit [IsAlgClosed k] in
private theorem normal_onPoints {G H : GroupScheme k} (i : H ⟶ G) (hi : IsNormalSubgroup i)
    (R : TestAlgebra k) (t : GroupPoints G R) (y : GroupPoints H R) :
    ∃ z : GroupPoints H R, onPoints i R z = t * onPoints i R y * t⁻¹ := by
  obtain ⟨c, hc⟩ := hi
  refine ⟨lift t y ≫ c, ?_⟩
  change Points G.X R at t
  change Points H.X R at y
  change (lift t y ≫ c) ≫ i.hom.hom = t * (y ≫ i.hom.hom) * t⁻¹
  rw [Category.assoc, hc]
  simp only [subgroupConjugation, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
    lift_fst, lift_snd]

omit [IsAlgClosed k] in
private theorem point_eq_one_of_trivial {H : GroupScheme k}
    (e : H ≅ Grp.trivial (SchemeOver k)) (g : GroupPoints H R₀) : g = 1 := by
  have h : onPoints e.hom R₀ g = 1 := toUnit_unique _ _
  have he := congrArg (onPoints e.inv R₀) h
  rw [map_one, ← Unipotent.onPoints_comp, e.hom_inv_id] at he
  exact he

variable [CharZero k]

/-- In a split torus extension with smooth connected unipotent kernel, a
finite-order rational point is conjugate to its image under the section. -/
theorem torsion_conjugate_to_section {G T : AffineAlgebraicGroup k}
    (U : ClosedSubgroup G.val) (p : G.val ⟶ T.val) (hp : IsFppfGroupQuotient U p)
    (j : T.val ⟶ G.val) (hj : j ≫ p = 𝟙 _)
    (hT : IsSplitTorus T.val)
    (hs : Smooth U.group.X.hom) (hc : ConnectedSpace U.group.X.left)
    (hu : IsUnipotent (closedSubgroupAlgebraicGroup U))
    (g : GroupPoints G.val R₀) (hg : IsOfFinOrder g) :
    ∃ a : GroupPoints G.val R₀,
      a⁻¹ * g * a = onPoints j R₀ (onPoints p R₀ g) := by
  classical
  obtain ⟨m, hm, hg⟩ := hg.exists_pow_eq_one
  obtain ⟨n, S, _, _, normal, factors⟩ :=
    EquivariantUnipotentSeries.stableSeriesForTorusExtension G T U p hp hT hs hc hu
  let i (d : ℕ) := S.inclusion d ≫ U.inclusion
  let f (d : ℕ) := onPoints (i d) R₀
  let N (d : ℕ) := (f d).range
  have finj (d : ℕ) : Function.Injective (f d) := by
    apply Unipotent.onPoints_injective
    haveI := Unipotent.closedSeries_inclusion_closed S d
    haveI := U.isClosedImmersion
    exact IsClosedImmersion.comp (S.inclusion d).hom.hom.left U.inclusion.hom.hom.left
  let e (d : ℕ) : GroupPoints (S.term d).val R₀ ≃* N d := MonoidHom.ofInjective (finj d)
  let t := onPoints j R₀ (onPoints p R₀ g)
  have ht : t ^ m = 1 := by
    change (onPoints j R₀ (onPoints p R₀ g)) ^ m = 1
    simp only [← map_pow, hg, map_one]
  have hbottom : N n = ⊥ := by
    apply le_antisymm _ bot_le
    rintro x ⟨v, rfl⟩
    rw [point_eq_one_of_trivial S.bottom v, map_one]
    exact (⊥ : Subgroup _).one_mem
  have htop : g * t⁻¹ ∈ N 0 := by
    have hpt : onPoints p R₀ t = onPoints p R₀ g := by
      change onPoints p R₀ (onPoints j R₀ _) = _
      rw [← Unipotent.onPoints_comp, hj]
      rfl
    have hkg : onPoints p R₀ (g * t⁻¹) = 1 := by
      rw [map_mul, map_inv, hpt, mul_inv_cancel]
    obtain ⟨v, hv⟩ := (schemeKernel_sections hp.1
      (show Points G.val.X R₀ from g * t⁻¹)).mpr hkg
    refine ⟨onPoints S.top.inv R₀ v, ?_⟩
    change onPoints (S.top.hom ≫ U.inclusion) R₀ (onPoints S.top.inv R₀ v) = _
    have he := Unipotent.onPoints_comp S.top.inv (S.top.hom ≫ U.inclusion) R₀ v
    rw [S.top.inv_hom_id_assoc] at he
    exact he.symm.trans hv
  have stable (d : ℕ) (hd : d < n) (x : N d) : t * x.val * t⁻¹ ∈ N d := by
    obtain ⟨z, hz⟩ := normal_onPoints (i d) (normal d hd.le) R₀ t ((e d).symm x)
    refine ⟨z, ?_⟩
    exact hz.trans (congrArg (fun a => t * a * t⁻¹)
      (MonoidHom.apply_ofInjective_symm (finj d) x))
  apply conjugate_of_additive_series (K := k) N n t g m (Nat.ne_of_gt hm)
    hg ht hbottom htop stable
  intro d hd
  obtain ⟨Q, q, eq, M, em, χ, hq, action⟩ := factors d hd
  let q₀ : N d →* Multiplicative k :=
    (eq.hom.app R₀).hom.comp ((onPoints q R₀).comp (e d).symm.toMonoidHom)
  let c : k := (show kˣ from em.hom.app R₀ (onPoints χ R₀ (onPoints p R₀ t))).val
  refine ⟨q₀, c, ?_, ?_, ?_⟩
  · haveI := hq.2.2.2.1
    exact (ConcreteCategory.bijective_of_isIso (eq.hom.app R₀)).2.comp
      ((onRationalPoints_surjective q hq.2.2.1 inferInstance).comp (e d).symm.surjective)
  · intro x
    let z : N d := ⟨t * x.val * t⁻¹, stable d hd x⟩
    have hz : f d ((e d).symm z) = t * f d ((e d).symm x) * t⁻¹ := by
      rw [show f d ((e d).symm z) = z.val from MonoidHom.apply_ofInjective_symm (finj d) z,
        show f d ((e d).symm x) = x.val from MonoidHom.apply_ofInjective_symm (finj d) x]
    exact action R₀ t ((e d).symm x) ((e d).symm z) hz
  · intro y
    let v := (e d).symm y.val
    have hy : (eq.hom.app R₀).hom (onPoints q R₀ v) = 1 := y.property
    have hv : onPoints q R₀ v = 1 := by
      apply (ConcreteCategory.bijective_of_isIso (eq.hom.app R₀)).1
      simpa only [map_one] using hy
    obtain ⟨z, hz⟩ := (schemeKernel_sections hq.1 (show Points _ R₀ from v)).mpr hv
    refine ⟨z, ?_⟩
    change onPoints (S.inclusion (d + 1) ≫ U.inclusion) R₀ z = y.val.val
    have he := Unipotent.onPoints_comp (S.step d) (i d) R₀ z
    rw [← Category.assoc] at he
    change f (d + 1) z = f d (z ≫ (S.step d).hom.hom) at he
    change z ≫ (S.step d).hom.hom = v at hz
    rw [hz] at he
    exact he.trans (MonoidHom.apply_ofInjective_symm (finj d) y.val)

open Specs.SchemeDerivedGroup (IsSolvable)

open private split_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting

/-- A finite-order point of a smooth connected solvable group is conjugate
into a split maximal torus of that group. -/
theorem torsion_conjugate_into_solvable_maximal_torus (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) (hsolv : IsSolvable G.val)
    (g : GroupPoints G.val R₀) (hg : IsOfFinOrder g) :
    ∃ (S : ClosedSubgroup G.val) (a : GroupPoints G.val R₀) (s : GroupPoints S.group R₀),
      Specs.GeometricTorusSplitting.IsMaximalTorus S ∧ IsSplitTorus S.group ∧
      a⁻¹ * g * a = onPoints S.inclusion R₀ s := by
  obtain ⟨U, T, p, hU, hp, hT, ⟨S, hS⟩, hmax⟩ :=
    GeometricTorusSplitting.splitting G hs hc hsolv
  haveI : IsIso (S.inclusion ≫ p) := ((hmax S).1).mp hS
  let e := asIso (S.inclusion ≫ p)
  let j := e.inv ≫ S.inclusion
  have hj : j ≫ p = 𝟙 T.val := by
    change (e.inv ≫ S.inclusion) ≫ p = _
    rw [Category.assoc]
    exact e.inv_hom_id
  obtain ⟨a, ha⟩ := torsion_conjugate_to_section U p hp j hj hT hU.1 hU.2.1 hU.2.2.2.1 g hg
  refine ⟨S, a, onPoints e.inv R₀ (onPoints p R₀ g), hS,
    split_of_torus (D := closedSubgroupAlgebraicGroup S) hS.1, ?_⟩
  exact ha.trans (Unipotent.onPoints_comp e.inv S.inclusion R₀ _)

open Specs.GeometricRadicals (IsReductive IsMaximalTorus)
open Specs.GeometricBorelConjugacy (IsBorel subgroupOfSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)

open private innerMap innerIso comp_innerMap borel_transport
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private transportSubgroup maximal_of_square solvable_maximal_torus_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

private noncomputable def rationalPointEquiv (G : GroupScheme k) :
    GroupPoints G R₀ ≃* (𝟙_ (SchemeOver k) ⟶ G.X) where
  toFun r := (rationalPointSource k).inv ≫ r
  invFun r := (rationalPointSource k).hom ≫ r
  left_inv r := Iso.hom_inv_id_assoc _ (show Points G.X R₀ from r)
  right_inv r := Iso.inv_hom_id_assoc _ r
  map_mul' r s := MonObj.comp_mul _ (show Points G.X R₀ from r) (show Points G.X R₀ from s)

/-- A finite-order point conjugate into a Borel lies in a split maximal
torus of a Borel in the given group. -/
theorem torsion_in_maximal_torus_of_conjugate_into_borel
    (H : AffineAlgebraicGroup k) (hH : IsReductive H)
    (B : ClosedSubgroup H.val) (hB : IsBorel B)
    (t : 𝟙_ (SchemeOver k) ⟶ H.val.X) (ht : IsOfFinOrder t)
    (g : 𝟙_ (SchemeOver k) ⟶ H.val.X) (b : 𝟙_ (SchemeOver k) ⟶ B.group.X)
    (hb : g⁻¹ * t * g = b ≫ B.inclusion.hom.hom) :
    ∃ (B' T : ClosedSubgroup H.val) (s : 𝟙_ (SchemeOver k) ⟶ T.group.X),
      IsBorel B' ∧ IsMaximalTorus T ∧ IsSplitTorus T.group ∧ IsSubgroupOf T B' ∧
      s ≫ T.inclusion.hom.hom = t := by
  let D := closedSubgroupAlgebraicGroup B
  let b₀ := (rationalPointEquiv B.group).symm b
  haveI : GeometricallyConnected H.val.X.hom := hH.2.1
  have hconn : ConnectedSpace H.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := H.val.X.hom)
  obtain ⟨m, hm, htm⟩ := ht.exists_pow_eq_one
  have hbm : b ^ m = 1 := by
    have he := B.isClosedImmersion
    letI : Mono B.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono B.inclusion.hom.hom).mp
    let f : (𝟙_ (SchemeOver k) ⟶ B.group.X) →* (𝟙_ (SchemeOver k) ⟶ H.val.X) :=
      ((yonedaGrp.map B.inclusion).app (op (𝟙_ (SchemeOver k)))).hom
    change f (b ^ m) = f 1
    rw [map_pow, map_one, show f b = g⁻¹ * t * g from hb.symm]
    simpa only [inv_inv, htm, mul_one, inv_mul_cancel] using
      (conj_pow (i := m) (a := g⁻¹) (b := t))
  have hb₀ : IsOfFinOrder b₀ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, by
      change ((rationalPointEquiv B.group).symm b) ^ m = 1
      rw [← map_pow, hbm, map_one]⟩
  obtain ⟨S, a₀, s₀, hS, hsplit, ha₀⟩ :=
    torsion_conjugate_into_solvable_maximal_torus D hB.1.1 hB.1.2.1 hB.1.2.2 b₀ hb₀
  let a := rationalPointEquiv B.group a₀
  let s := rationalPointEquiv S.group s₀
  let sb : S.group.X ⟶ B.group.X := S.inclusion.hom.hom
  let bi : B.group.X ⟶ H.val.X := B.inclusion.hom.hom
  have ha : a⁻¹ * b * a = s ≫ sb := by
    have h := congrArg (rationalPointEquiv B.group) ha₀
    simp only [map_mul, map_inv, b₀, MulEquiv.apply_symm_apply] at h
    exact h.trans (Category.assoc (rationalPointSource k).inv (show Points S.group.X R₀ from s₀) sb).symm
  let r := g * (a ≫ bi)
  let e := innerIso r
  let T₀ := subgroupOfSubgroup B S
  let T := transportSubgroup e T₀
  let B' := transportSubgroup e B
  have hmax₀ : IsMaximalTorus T₀ :=
    (MaximalToriConjugate.borelMaximalTorusIff H hH.1 hconn B hB S).mp
      ((solvable_maximal_torus_iff D S).mp hS)
  have hmax : IsMaximalTorus T := maximal_of_square e T₀ T (Iso.refl _) (Category.id_comp _) hmax₀
  have hB' : IsBorel B' := borel_transport hB e
  refine ⟨B', T, s, hB', hmax, hsplit, ⟨S.inclusion, ?_⟩, ?_⟩
  · change S.inclusion ≫ B.inclusion ≫ e.hom = (S.inclusion ≫ B.inclusion) ≫ e.hom
    exact (Category.assoc _ _ _).symm
  · change s ≫ sb ≫ bi ≫ (innerMap r).hom.hom = t
    rw [← Category.assoc s, ← Category.assoc (s ≫ sb), comp_innerMap,
      show toUnit (𝟙_ (SchemeOver k)) ≫ r = r from Category.id_comp _, ← ha,
      MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, ← show g⁻¹ * t * g = b ≫ bi from hb]
    dsimp only [r]
    group

end SplitExtension

section ComplexPlacement

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

open Specs.EquivariantUnipotentSeries (GroupPoints)
open Specs.GeometricRadicals (IsReductive)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open CocharacterDynamics (existsLimitDecomposition oppositeCocharacter)

open private isTorus_iff_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private split_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private exists_regular_cocharacter from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private geometricMaximal_of_maximal isKBorel_iff_of_isAlgClosed
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer

/-- Every finite-order point of a connected complex reductive group lies
in a maximal torus of a Borel subgroup of that group. -/
theorem torsionInComplexMaximalTorus : Specs.TorsionInComplexMaximalTorus.Statement := by
  intro H hH t ht
  letI : Smooth H.val.X.hom := hH.1
  letI : GeometricallyConnected H.val.X.hom := hH.2.1
  letI : ConnectedSpace H.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton H.val.X.hom
  letI : IsIntegral H.val.X.left := WordDomainGeometry.smoothConnectedGroupIntegral H hH.1 inferInstance
  obtain ⟨T, hT, hMax⟩ := MaximalToriExist.geometricallyMaximalTorusExists H hH.1 inferInstance
  let A := Specs.Unipotent.closedSubgroupAlgebraicGroup T
  have hSplit := split_of_torus (D := A) ((isTorus_iff_coordinates A).mp hT)
  obtain ⟨c, hc⟩ := exists_regular_cocharacter H T hSplit
  obtain ⟨D⟩ := existsLimitDecomposition H (c ≫ T.inclusion)
  obtain ⟨E⟩ := existsLimitDecomposition H (oppositeCocharacter (c ≫ T.inclusion))
  obtain ⟨_, hKB, hTB, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel H hH T hSplit hMax c hc D
  have hB := (isKBorel_iff_of_isAlgClosed H D.parabolic).mp hKB
  obtain ⟨Q⟩ := (HomogeneousQuotient.homogeneousQuotient ℂ H D.parabolic).1
  have hContains : Specs.BorelProper.ContainsGeometricBorel D.parabolic := by
    obtain ⟨he, hBe⟩ := hKB
    exact ⟨he, _, hBe, ⟨𝟙 _, Category.id_comp _⟩⟩
  letI : IsProper Q.scheme.hom :=
    (BorelProper.quotientProperIff H hH.1 inferInstance D.parabolic hB.1.1 Q).mpr hContains
  have hRange := fixedFlagProjection_range_of_bigCell H T c D E hTB Q
  let t₀ := rationalPointEquiv H.val t
  have ht₀ : IsOfFinOrder t₀ := by
    obtain ⟨n, hn, hpow⟩ := ht.exists_pow_eq_one
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
    change (rationalPointEquiv H.val t) ^ n = 1
    rw [← map_pow, hpow, map_one]
  obtain ⟨g, b, hb⟩ := conjugate_of_mem_fixedFlagProjection Q t₀ (by rw [hRange]; trivial)
  obtain ⟨B', T', s, hB', hMax', hSplit', hTB', hs⟩ :=
    torsion_in_maximal_torus_of_conjugate_into_borel H hH D.parabolic hB t₀ ht₀ g b hb
  let P : Specs.Pinning.SplitBorelPair ℂ :=
    ⟨H, hH, T', hSplit', geometricMaximal_of_maximal H T' hMax', B',
      (isKBorel_iff_of_isAlgClosed H B').mpr hB', hTB'⟩
  refine ⟨P, rfl, (rationalPointEquiv T'.group).symm s, ?_⟩
  change ((rationalPointSource ℂ).hom ≫ s) ≫ T'.inclusion.hom.hom = t
  rw [Category.assoc, hs]
  exact (rationalPointEquiv H.val).symm_apply_apply t

end ComplexPlacement

end LinearAlgebraicGroups.TorsionInComplexMaximalTorus
