import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.TwoDegreeExampleDualizingCalculation
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularCoverDualizingModel
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open IsLocalRing (maximalIdeal ResidueField residue)
open ModuleCat (restrictScalars)
open Specs.CommutativeAlgebraNotes.TwoDegreeExampleDualizingCalculation

namespace CommutativeAlgebraNotes.TwoDegreeExampleDualizingCalculation

universe u w

set_option linter.style.haveILetI false

private theorem quotient_surjective (k : Type u) [Field k] :
    Function.Surjective (quotientMap k) :=
  Ideal.Quotient.mk_surjective

private theorem quotient_precomplete {A : Type u} [CommRing A] (I J : Ideal A)
    [IsPrecomplete J A] : IsPrecomplete J (A ⧸ I) := by
  let f := (Ideal.Quotient.mkₐ A I).toLinearMap
  apply (AdicCompletion.of_surjective_iff (I := J) (M := A ⧸ I)).mp
  intro z
  obtain ⟨v, rfl⟩ := AdicCompletion.map_surjective J (f := f)
    (Ideal.Quotient.mkₐ_surjective A I) z
  obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective (I := J) (M := A) v
  exact ⟨f a, (AdicCompletion.map_of J f a).symm⟩

theorem completeRegularCover : CompleteRegularCover.{u} := by
  intro k _
  obtain ⟨_, hS, hSc, _, hd, _, _, eS, heS⟩ := CompleteRegularPowerSeries.overField k 2
  letI := hS
  let q := quotientMap k
  have hq : Function.Surjective q := quotient_surjective k
  letI : Nontrivial (ExampleRing k) := (constantTerm k).domain_nontrivial
  letI : IsLocalRing (ExampleRing k) := IsLocalRing.of_surjective' q hq
  letI : IsLocalHom q := IsLocalHom.of_surjective q hq
  have hR : IsNoetherianRing (ExampleRing k) := inferInstance
  have hpre : IsPrecomplete (maximalIdeal (Series k)) (ExampleRing k) :=
    quotient_precomplete (definingIdeal k) (maximalIdeal (Series k))
  have hRc : IsAdicComplete (maximalIdeal (ExampleRing k)) (ExampleRing k) := by
    have hm := IsLocalRing.map_maximalIdeal_of_surjective q hq
    have hp := (IsPrecomplete.map_algebraMap_iff
      (S := ExampleRing k) (I := maximalIdeal (Series k)) (M := ExampleRing k)).mpr hpre
    change IsPrecomplete ((maximalIdeal (Series k)).map q) (ExampleRing k) at hp
    rw [hm] at hp
    exact { toIsHausdorff := inferInstance, toIsPrecomplete := hp }
  let e := RingEquiv.ofBijective (ResidueField.map q) (localQuotient_residue_bijective q hq)
  refine ⟨hS, inferInstance, hSc, hd, hR, hRc, inferInstance, hq, e.symm.trans eS, ?_⟩
  intro r
  obtain ⟨s, rfl⟩ := hq r
  change eS (e.symm (residue (ExampleRing k) (q s))) = MvPowerSeries.constantCoeff s
  rw [← ResidueField.map_residue q, show (ResidueField.map q) (residue (Series k) s) =
    e (residue (Series k) s) from rfl, e.symm_apply_apply, heS]

section Resolution

variable (k : Type u) [Field k]

local notation "S" => Series k
local notation "Qring" => ExampleRing k
local notation "I" => definingIdeal k

private theorem x_ne_zero : x k ≠ 0 := by
  intro h
  have hc := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h
  simp [x, MvPowerSeries.coeff_index_single_self_X] at hc

/-- Multiplication by the second variable is injective modulo the first. -/
private theorem dvd_of_dvd_y_mul (a : S) (h : x k ∣ y k * a) : x k ∣ a := by
  rw [x, MvPowerSeries.X_dvd_iff] at h ⊢
  intro m hm
  have hz := h (Finsupp.single (1 : Fin 2) 1 + m) (by
    simp [Finsupp.add_apply, hm])
  simpa only [y, MvPowerSeries.X_def, MvPowerSeries.coeff_add_monomial_mul, one_mul] using hz

private def column : S →ₗ[S] S × S where
  toFun c := (-y k * c, x k * c)
  map_add' _ _ := by ext <;> simp [mul_add]
  map_smul' _ _ := by ext <;> simp [mul_left_comm]

private def row : S × S →ₗ[S] S where
  toFun p := p.1 * x k ^ 2 + p.2 * (x k * y k)
  map_add' _ _ := by simp; ring
  map_smul' _ _ := by simp; ring

private def rowToIdeal : S × S →ₗ[S] I :=
  (row k).codRestrict I (fun p => Ideal.mem_span_pair.mpr ⟨p.1, p.2, rfl⟩)

private theorem rowToIdeal_surjective : Function.Surjective (rowToIdeal k) := by
  intro z
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp z.property
  exact ⟨(a, b), Subtype.ext hab⟩

private theorem column_injective : Function.Injective (column k) := fun _ _ h =>
  mul_left_cancel₀ (x_ne_zero k) (congrArg Prod.snd h)

private theorem resolution_exact : Function.Exact (column k) (rowToIdeal k) := by
  rintro ⟨a, b⟩
  constructor
  · intro h
    have hab : x k * (x k * a + y k * b) = 0 := by
      convert congrArg Subtype.val h using 1
      change _ = a * x k ^ 2 + b * (x k * y k)
      ring
    have hlin := (mul_eq_zero.mp hab).resolve_left (x_ne_zero k)
    obtain ⟨c, rfl⟩ := dvd_of_dvd_y_mul k b (by
      refine ⟨-a, ?_⟩
      rw [mul_neg]
      exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hlin))
    refine ⟨c, Prod.ext (mul_left_cancel₀ (x_ne_zero k) ?_) rfl⟩
    change x k * (-y k * c) = x k * a
    linear_combination (norm := ring_nf) -hlin
  · rintro ⟨c, h⟩
    change (-(y k) * c, x k * c) = (a,b) at h
    cases h
    apply Subtype.ext
    change (-y k * c) * x k ^ 2 + (x k * c) * (x k * y k) = 0
    ring

private def quotientLinear : S →ₗ[S] Qring := (Ideal.Quotient.mkₐ S I).toLinearMap

private theorem quotient_exact : Function.Exact (definingIdeal k).subtype (quotientLinear k) := by
  intro z
  change quotientMap k z = 0 ↔ z ∈ Set.range (definingIdeal k).subtype
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun hz => ⟨⟨z, hz⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.property⟩

private abbrev presentationKernel : ShortComplex (ModuleCat.{u} S) :=
  ModuleCat.shortComplexOfCompEqZero (column k) (rowToIdeal k)
    (resolution_exact k).linearMap_comp_eq_zero

private theorem presentationKernel_shortExact : (presentationKernel k).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (resolution_exact k) (column_injective k)
    (rowToIdeal_surjective k)

private abbrev presentationQuotient : ShortComplex (ModuleCat.{u} S) :=
  ModuleCat.shortComplexOfCompEqZero (definingIdeal k).subtype (quotientLinear k)
    (quotient_exact k).linearMap_comp_eq_zero

private theorem presentationQuotient_shortExact : (presentationQuotient k).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (quotient_exact k) (definingIdeal k).injective_subtype
    (quotient_surjective k)

end Resolution

section ConnectingMaps

variable {A : Type u} [CommRing A] {T : ShortComplex (ModuleCat.{u} A)}
  (hT : T.ShortExact) (Y : ModuleCat.{u} A)

private theorem ext_eq_zero_of_projective {P : ModuleCat.{u} A} [Projective P]
    {n : ℕ} (hn : n ≠ 0) (e : Ext.{u} P Y n) : e = 0 := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n => exact Ext.eq_zero_of_projective e

private def connecting (n : ℕ) : Ext.{u} T.X₁ Y n →ₗ[A] Ext.{u} T.X₃ Y (1 + n) :=
  hT.extClass.precompOfLinear A Y rfl

private theorem connecting_surjective [Projective T.X₂] (n : ℕ) :
    Function.Surjective (connecting hT Y n) := by
  intro e
  exact Ext.contravariant_sequence_exact₃ hT Y e
    (ext_eq_zero_of_projective Y (by omega) _) rfl

private theorem connecting_injective [Projective T.X₂] {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (connecting hT Y n) := by
  apply (injective_iff_map_eq_zero (connecting hT Y n)).mpr
  intro e he
  obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₁ hT Y e rfl he
  rw [ext_eq_zero_of_projective Y hn a, Ext.comp_zero] at ha
  exact ha.symm

private def homBoundary : (T.X₁ ⟶ Y) →ₗ[A] Ext.{u} T.X₃ Y 1 :=
  (connecting hT Y 0).comp (Ext.linearEquiv₀ (R := A)).symm.toLinearMap

private theorem homBoundary_surjective [Projective T.X₂] :
    Function.Surjective (homBoundary hT Y) :=
  (connecting_surjective hT Y 0).comp (Ext.linearEquiv₀ (R := A)).symm.surjective

private theorem homBoundary_eq_zero_iff (f : T.X₁ ⟶ Y) :
    homBoundary hT Y f = 0 ↔ ∃ g : T.X₂ ⟶ Y, T.f ≫ g = f := by
  change hT.extClass.comp (Ext.mk₀ f) (rfl : 1 + 0 = 1) = 0 ↔ _
  constructor
  · intro hf
    obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₁ hT Y (Ext.mk₀ f) rfl hf
    obtain ⟨g, rfl⟩ := Ext.linearEquiv₀ (R := A) |>.symm.surjective a
    refine ⟨g, (Ext.linearEquiv₀ (R := A)).symm.injective ?_⟩
    simpa only [Ext.linearEquiv₀_symm_apply, Ext.mk₀_comp_mk₀] using ha
  · rintro ⟨g, rfl⟩
    rw [← Ext.mk₀_comp_mk₀]
    exact hT.extClass_comp_assoc (Ext.mk₀ g)

end ConnectingMaps

section DualMaps

variable (k : Type u) [Field k]

local notation "S" => Series k
local notation "I" => definingIdeal k
local notation "B" => ModuleCat.of S S

private def xSquare : I := ⟨x k ^ 2, Ideal.subset_span (by simp)⟩
private def xy : I := ⟨x k * y k, Ideal.subset_span (by simp)⟩

private theorem exists_divideX (z : I) : ∃ a : S, x k * a = z.val := by
  obtain ⟨a, b, hz⟩ := Ideal.mem_span_pair.mp z.property
  refine ⟨a * x k + b * y k, ?_⟩
  rw [← hz]
  ring

private def divideX : I →ₗ[S] S where
  toFun z := (exists_divideX k z).choose
  map_add' a b := by
    apply mul_left_cancel₀ (x_ne_zero k)
    rw [mul_add, (exists_divideX k (a+b)).choose_spec,
      (exists_divideX k a).choose_spec, (exists_divideX k b).choose_spec]
    rfl
  map_smul' r z := by
    apply mul_left_cancel₀ (x_ne_zero k)
    change x k * (exists_divideX k (r • z)).choose =
      x k * (r * (exists_divideX k z).choose)
    rw [(exists_divideX k (r • z)).choose_spec, mul_left_comm,
      (exists_divideX k z).choose_spec]
    rfl

private theorem mul_divideX (z : I) : x k * divideX k z = z.val :=
  (exists_divideX k z).choose_spec

private theorem divideX_xSquare : divideX k (xSquare k) = x k :=
  mul_left_cancel₀ (x_ne_zero k) (by rw [mul_divideX]; exact pow_two _)

private theorem divideX_xy : divideX k (xy k) = y k :=
  mul_left_cancel₀ (x_ne_zero k) (by rw [mul_divideX]; rfl)

private theorem homIdeal_ext {f g : ModuleCat.of S I ⟶ B}
    (hx : f (xSquare k) = g (xSquare k)) (hy : f (xy k) = g (xy k)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨a,b,hz⟩ := Ideal.mem_span_pair.mp z.property
  have h : a • xSquare k + b • xy k = z := Subtype.ext hz
  simp only [← h, map_add, map_smul]
  change a • f _ + b • f _ = a • g _ + b • g _
  rw [hx, hy]

private def idealHomFromScalar : S →ₗ[S] (ModuleCat.of S I ⟶ B) :=
  LinearMap.toSpanSingleton S _ (ModuleCat.ofHom (divideX k))

private theorem idealHom_xSquare (c : S) : idealHomFromScalar k c (xSquare k) = c * x k := by
  change c * divideX k (xSquare k) = c * x k
  rw [divideX_xSquare]

private theorem idealHom_xy (c : S) : idealHomFromScalar k c (xy k) = c * y k := by
  change c * divideX k (xy k) = c * y k
  rw [divideX_xy]

private theorem idealHomFromScalar_surjective : Function.Surjective (idealHomFromScalar k) := by
  intro f
  have h : y k • xSquare k = x k • xy k := by
    apply Subtype.ext
    change y k * x k ^ 2 = x k * (x k * y k)
    ring
  have hf := congrArg (fun z => f.hom z) h
  simp only [map_smul] at hf
  change y k * f (xSquare k) = x k * f (xy k) at hf
  obtain ⟨c, hc⟩ := dvd_of_dvd_y_mul k (f (xSquare k)) ⟨_, hf⟩
  refine ⟨c, homIdeal_ext k ?_ ?_⟩
  · rw [idealHom_xSquare, hc, mul_comm]
  · rw [idealHom_xy]
    apply mul_left_cancel₀ (x_ne_zero k)
    rw [← hf, hc]
    ring

private def ringHomFromScalar : S ≃ₗ[S] (B ⟶ B) :=
  (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf S S S)).symm

private theorem ringHomFromScalar_apply (c a : S) : ringHomFromScalar k c a = a * c := rfl

end DualMaps

section ExtCalculation

variable (k : Type u) [Field k]

local notation "S" => Series k
local notation "Qring" => ExampleRing k
local notation "I" => definingIdeal k
local notation "B" => ModuleCat.of S S
local notation "P" => ModuleCat.of S (S × S)
local notation "C" => ModuleCat.of S Qring

private instance : Projective B := inferInstance
private instance : Projective P := inferInstance

private def extOneMap : S →ₗ[S] Ext.{u} C B 1 :=
  (homBoundary (presentationQuotient_shortExact k) B).comp (idealHomFromScalar k)

private theorem extOneMap_surjective : Function.Surjective (extOneMap k) :=
  (homBoundary_surjective (presentationQuotient_shortExact k) B).comp
    (idealHomFromScalar_surjective k)

private theorem ker_extOneMap : LinearMap.ker (extOneMap k) = Ideal.span {x k} := by
  ext c
  change (homBoundary (presentationQuotient_shortExact k) B) (idealHomFromScalar k c) = 0 ↔ _
  rw [homBoundary_eq_zero_iff, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨a, rfl⟩ := (ringHomFromScalar k).surjective g
    have h := congrArg (fun f => f (xSquare k)) hg
    change ringHomFromScalar k a (x k ^ 2) = idealHomFromScalar k c (xSquare k) at h
    rw [ringHomFromScalar_apply, idealHom_xSquare] at h
    refine ⟨a, mul_right_cancel₀ (x_ne_zero k) ?_⟩
    rw [← h]
    ring
  · rintro ⟨a, rfl⟩
    refine ⟨ringHomFromScalar k a, ModuleCat.hom_ext (LinearMap.ext fun z => ?_)⟩
    change ringHomFromScalar k a z.val = (x k * a) * divideX k z
    rw [ringHomFromScalar_apply, ← mul_divideX k z]
    ring

private def extIdealOneMap : S →ₗ[S] Ext.{u} (ModuleCat.of S I) B 1 :=
  (homBoundary (presentationKernel_shortExact k) B).comp (ringHomFromScalar k).toLinearMap

private theorem extIdealOneMap_surjective : Function.Surjective (extIdealOneMap k) :=
  (homBoundary_surjective (presentationKernel_shortExact k) B).comp
    (ringHomFromScalar k).surjective

private theorem ker_extIdealOneMap :
    LinearMap.ker (extIdealOneMap k) = Ideal.span {x k, y k} := by
  ext c
  change (homBoundary (presentationKernel_shortExact k) B) (ringHomFromScalar k c) = 0 ↔ _
  rw [homBoundary_eq_zero_iff, Ideal.mem_span_pair]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g (0, 1), -g (1, 0), ?_⟩
    have h := congrArg (fun f : B ⟶ B => f 1) hg
    change g (-y k * 1, x k * 1) = ringHomFromScalar k c 1 at h
    rw [ringHomFromScalar_apply, mul_one, mul_one, one_mul] at h
    have hp : (-y k, x k) = (-y k) • ((1, 0) : S × S) + x k • ((0, 1) : S × S) := by
      ext <;> simp
    rw [← h, hp]
    change _ = g.hom ((-y k) • ((1, 0) : S × S) + x k • ((0, 1) : S × S))
    rw [map_add, map_smul, map_smul]
    change g (0, 1) * x k + -g (1, 0) * y k = (-y k) * g (1, 0) + x k * g (0, 1)
    ring
  · rintro ⟨a,b,rfl⟩
    let g : S × S →ₗ[S] S := (-b) • LinearMap.fst S S S + a • LinearMap.snd S S S
    refine ⟨ModuleCat.ofHom g, ModuleCat.hom_ext (LinearMap.ext fun z => ?_)⟩
    change g (-y k * z, x k * z) = ringHomFromScalar k (a * x k + b * y k) z
    rw [ringHomFromScalar_apply]
    change (-b) * (-y k * z) + a * (x k * z) = _
    ring

private def extTwoShift : Ext.{u} (ModuleCat.of S I) B 1 ≃ₗ[S] Ext.{u} C B 2 :=
  LinearEquiv.ofBijective (connecting (presentationQuotient_shortExact k) B 1)
    ⟨connecting_injective (presentationQuotient_shortExact k) B one_ne_zero,
      connecting_surjective (presentationQuotient_shortExact k) B 1⟩

private def xQuotientLinear : S →ₗ[S] (restrictScalars (quotientMap k)).obj (xQuotientModule k) where
  toFun := Ideal.Quotient.mk (Ideal.span {x k})
  map_add' := map_add (Ideal.Quotient.mk _)
  map_smul' := map_mul (Ideal.Quotient.mk _)

private def coefficientLinear : S →ₗ[S] (restrictScalars (quotientMap k)).obj (coefficientModule k) where
  toFun := MvPowerSeries.constantCoeff
  map_add' := map_add MvPowerSeries.constantCoeff
  map_smul' := map_mul MvPowerSeries.constantCoeff

private theorem ker_coefficientLinear :
    LinearMap.ker (coefficientLinear k) = Ideal.span {x k, y k} := by
  obtain ⟨_, _, _, hm, _, _, _, e, he⟩ := CompleteRegularPowerSeries.overField k 2
  have hxy : Set.range (MvPowerSeries.X : Fin 2 → S) = {x k, y k} := by
    ext z
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp [x,y]
    · intro h
      rcases Set.mem_insert_iff.mp h with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, (Set.mem_singleton_iff.mp h).symm⟩
  change maximalIdeal S = Ideal.span _ at hm
  rw [hxy] at hm
  rw [← hm]
  ext z
  change MvPowerSeries.constantCoeff z = 0 ↔ z ∈ maximalIdeal S
  rw [← he, ← map_zero e]
  exact e.injective.eq_iff.trans Ideal.Quotient.eq_zero_iff_mem

private def extOneEquiv :
    Ext.{u} C B 1 ≃ₗ[S] (restrictScalars (quotientMap k)).obj (xQuotientModule k) := by
  have hker : LinearMap.ker (extOneMap k) = LinearMap.ker (xQuotientLinear k) := by
    rw [ker_extOneMap]
    ext z
    exact Ideal.Quotient.eq_zero_iff_mem.symm
  exact (LinearMap.quotKerEquivOfSurjective _ (extOneMap_surjective k)).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans
      (LinearMap.quotKerEquivOfSurjective _ Ideal.Quotient.mk_surjective))

private def extTwoEquiv :
    Ext.{u} C B 2 ≃ₗ[S] (restrictScalars (quotientMap k)).obj (coefficientModule k) := by
  have hker := (ker_extIdealOneMap k).trans (ker_coefficientLinear k).symm
  have hsurj : Function.Surjective (coefficientLinear k) := by
    intro a
    change k at a
    refine ⟨MvPowerSeries.C a, ?_⟩
    change MvPowerSeries.constantCoeff (MvPowerSeries.C a : S) = a
    exact MvPowerSeries.constantCoeff_C a
  exact (extTwoShift k).symm.trans
    ((LinearMap.quotKerEquivOfSurjective _ (extIdealOneMap_surjective k)).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective _ hsurj)))

private theorem extZero_subsingleton : Subsingleton (Ext.{u} C B 0) := by
  have hzero (f : C ⟶ B) : f = 0 := by
    have h : x k ^ 2 • (1 : Qring) = 0 := by
      change quotientMap k (x k ^ 2) * 1 = 0
      rw [mul_one]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (xSquare k).property
    have hf : x k ^ 2 * f (1 : Qring) = 0 := by
      exact (f.hom.map_smul (x k ^ 2) 1).symm.trans (by rw [h, map_zero])
    have h1 : f (1 : Qring) = 0 := (mul_eq_zero.mp hf).resolve_left (pow_ne_zero _ (x_ne_zero k))
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    obtain ⟨s, rfl⟩ := quotient_surjective k r
    have hs : quotientMap k s = s • (1 : Qring) := (mul_one _).symm
    rw [hs]
    change f.hom (s • (1 : Qring)) = (0 : S)
    rw [map_smul]
    change s * f (1 : Qring) = 0
    rw [h1, mul_zero]
  letI : Subsingleton (C ⟶ B) := subsingleton_of_forall_eq 0 hzero
  exact (Ext.linearEquiv₀ (R := S)).injective.subsingleton

private theorem extHigh_subsingleton (n : ℕ) (hn : 2 < n) : Subsingleton (Ext.{u} C B n) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = 1 + (1 + (j + 1)) := ⟨n - 3, by omega⟩
  refine subsingleton_of_forall_eq 0 fun e => ?_
  obtain ⟨a, rfl⟩ :=
    connecting_surjective (presentationQuotient_shortExact k) B (1 + (j + 1)) e
  obtain ⟨b, rfl⟩ := connecting_surjective (presentationKernel_shortExact k) B (j + 1) a
  have hb : b = 0 := Ext.eq_zero_of_projective b
  simp only [hb, map_zero]

end ExtCalculation

section DualizingModel

open Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel (ShiftedRingResolution dualizingComplex stalk)
open CommutativeAlgebraNotes.RegularCoverDualizingModel (regularHomComplexIso shiftedHomEquiv)
open private shiftedStalkHomEquivExt shiftedStalkHom_subsingleton upgradeRestriction from
  MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularCoverDualizingModel
open DerivedCategory

variable (k : Type u) [Field k]

local notation "S" => Series k
local notation "R₀" => ExampleRing k
local notation "B" => ModuleCat.of S S
local notation "C" => ModuleCat.of S R₀

private def quotientRestrictionIso :
    (restrictScalars (quotientMap k)).obj (ModuleCat.of R₀ R₀) ≅ C :=
  (show (restrictScalars (quotientMap k)).obj (ModuleCat.of R₀ R₀) ≃ₗ[S] C from
    { AddEquiv.refl R₀ with map_smul' := fun _ _ => rfl }).toModuleIso

private def cohomologyShiftedHom [HasDerivedCategory.{w} (ModuleCat.{u} S)]
    (J : ShiftedRingResolution S 2) (q j : ℤ) (h : 2 + q = j) :
    (restrictScalars (quotientMap k)).obj ((dualizingComplex (quotientMap k) J.complex).homology q)
      ≃ₗ[S] (Q.obj (stalk S 0 C) ⟶ Q.obj ((stalk S 0 B)⟦j⟧)) :=
  ((restrictScalars (quotientMap k)).mapIso
    ((HomologicalComplex.homologyFunctor (ModuleCat R₀) (.up ℤ) q).mapIso
      (regularHomComplexIso (dualizingComplex (quotientMap k) J.complex)))).toLinearEquiv.trans
    (shiftedHomEquiv (quotientMap k) (ModuleCat.of R₀ R₀) (quotientRestrictionIso k) J q j h)

private def cohomologyExt [HasDerivedCategory.{w} (ModuleCat.{u} S)]
    (J : ShiftedRingResolution S 2) (q : ℤ) (j : ℕ) (h : 2 + q = (j : ℤ)) :
    (restrictScalars (quotientMap k)).obj ((dualizingComplex (quotientMap k) J.complex).homology q)
      ≃ₗ[S] Ext.{u} C B j :=
  (cohomologyShiftedHom k J q j h).trans (shiftedStalkHomEquivExt C B j)

/-- The cohomology of the normalized dualizing model, with scalars over the quotient ring. -/
theorem dualizingCohomology : DualizingCohomology.{u} := by
  intro k _ J
  letI := HasDerivedCategory.standard (ModuleCat.{u} (Series k))
  have hq := quotient_surjective k
  refine ⟨⟨?_⟩, ⟨?_⟩, ?_⟩
  · exact (upgradeRestriction (quotientMap k) hq
      ((cohomologyExt k J (-1) 1 (by decide)).trans (extOneEquiv k))).toModuleIso
  · exact (upgradeRestriction (quotientMap k) hq
      ((cohomologyExt k J 0 2 (by decide)).trans (extTwoEquiv k))).toModuleIso
  · intro q h₁ h₂
    apply ModuleCat.isZero_iff_subsingleton.mpr
    by_cases hq' : 0 ≤ 2 + q
    · let j := (2 + q).toNat
      have hj : (j : ℤ) = 2 + q := Int.toNat_of_nonneg hq'
      have hE : Subsingleton (Ext.{u} (ModuleCat.of (Series k) (ExampleRing k))
          (ModuleCat.of (Series k) (Series k)) j) := by
        by_cases hj₀ : j = 0
        · rw [hj₀]
          exact extZero_subsingleton k
        · exact extHigh_subsingleton k j (by omega)
      exact (cohomologyExt k J q j hj.symm).injective.subsingleton
    · haveI := shiftedStalkHom_subsingleton
        (ModuleCat.of (Series k) (ExampleRing k)) (ModuleCat.of (Series k) (Series k))
        (2 + q) (by omega)
      exact (cohomologyShiftedHom k J q (2 + q) rfl).injective.subsingleton

end DualizingModel
end CommutativeAlgebraNotes.TwoDegreeExampleDualizingCalculation
