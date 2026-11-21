import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.CuspSerreExample
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.DimensionOneDVR
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace AdvCommAlg.Normality.Cusp
open Polynomial
universe u
variable (k : Type u) [Field k]

/-- Every polynomial in the cusp algebra has zero linear coefficient. -/
theorem coeff_one_eq_zero (p : algebra k) : (p : k[X]).coeff 1 = 0 := by
  obtain ⟨p, hp⟩ := p
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    rcases hp with rfl | hp
    · simp
    · rcases hp with rfl
      simp
  | algebraMap a => simp
  | add p q hp hq ihp ihq => simp [ihp, ihq]
  | mul p q hp hq ihp ihq => simp [Polynomial.mul_coeff_one, ihp, ihq]

/-- Multiplication by a denominator with nonzero constant term cannot hide `X`. -/
theorem denominator_obstruction (p q : algebra k)
    (hq : (q : k[X]).coeff 0 ≠ 0) : (p : k[X]) ≠ X * (q : k[X]) := by
  intro h
  have hh := congrArg (fun p : k[X] => p.coeff 1) h
  apply hq
  simpa [coeff_one_eq_zero, Polynomial.mul_coeff_one] using hh.symm

theorem X_not_mem : (X : k[X]) ∉ algebra k := by
  intro h
  have := coeff_one_eq_zero k ⟨X, h⟩
  simp at this

theorem square_ne_zero : square k ≠ 0 := by
  intro h
  have hh := congrArg (fun p : algebra k => (p : k[X])) h
  simp [square] at hh

theorem cube_sq_eq_square_cube : cube k ^ 2 = square k ^ 3 := by
  apply Subtype.ext
  change (X ^ 3 : k[X]) ^ 2 = (X ^ 2) ^ 3
  ring

theorem X_integral : IsIntegral (algebra k) (X : k[X]) := by
  apply IsIntegral.of_pow (n := 2) (by decide)
  exact isIntegral_algebraMap (x := square k)

instance algebra_noetherian : IsNoetherianRing (algebra k) := by
  apply isNoetherianRing_of_fg
  exact Subalgebra.fg_def.mpr ⟨{X ^ 2, X ^ 3}, Set.toFinite _, rfl⟩

instance polynomial_finiteType : Algebra.FiniteType (algebra k) k[X] :=
  Algebra.FiniteType.of_restrictScalars_finiteType k (algebra k) k[X]

instance polynomial_integral : Algebra.IsIntegral (algebra k) k[X] := by
  apply integralClosure_eq_top_iff.mp
  apply top_unique
  have h : Algebra.adjoin k {(X : k[X])} ≤
      (integralClosure (algebra k) k[X]).restrictScalars k := by
    apply Algebra.adjoin_le
    intro x hx
    rcases hx with rfl
    exact X_integral k
  intro p _
  apply h
  simp

instance polynomial_finite : Module.Finite (algebra k) k[X] :=
  Algebra.IsIntegral.finite

theorem parameter_sq : parameter k ^ 2 =
    algebraMap (algebra k) (FractionRing (algebra k)) (square k) := by
  have h : algebraMap (algebra k) (FractionRing (algebra k)) (square k) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (square_ne_zero k)
  rw [parameter, div_pow, div_eq_iff (pow_ne_zero 2 h), ← map_pow, ← map_pow]
  rw [cube_sq_eq_square_cube]
  simp only [map_pow]
  ring

theorem parameter_integral : IsIntegral (algebra k) (parameter k) := by
  apply IsIntegral.of_pow (n := 2) (by decide)
  rw [parameter_sq]
  exact isIntegral_algebraMap

@[simp] theorem localToFraction_algebraMap (a : algebra k) :
    localToFraction k (algebraMap (algebra k) (Local k) a) =
      algebraMap (algebra k) (FractionRing (algebra k)) a :=
  (IsScalarTower.algebraMap_apply (algebra k) (Local k) (FractionRing (algebra k)) a).symm

/-- The parameter is absent even after localization at the origin. -/
theorem parameter_not_in_local_image : parameter k ∉ Set.range (localToFraction k) := by
  rintro ⟨z, hz⟩
  obtain ⟨⟨p, q⟩, he⟩ := IsLocalization.surj (origin k).primeCompl z
  have h := congrArg (localToFraction k) he
  simp only [map_mul, localToFraction_algebraMap, hz, parameter] at h
  have hs : algebraMap (algebra k) (FractionRing (algebra k)) (square k) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (square_ne_zero k)
  have heq : cube k * (q : algebra k) = p * square k := by
    apply IsFractionRing.injective (algebra k) (FractionRing (algebra k))
    simp only [map_mul]
    apply (div_eq_iff hs).mp
    simpa only [div_mul_eq_mul_div] using h
  have hpq : (p : k[X]) = X * (q.val : k[X]) := by
    have heq' := congrArg (fun a : algebra k => (a : k[X])) heq
    change X ^ 3 * (q.val : k[X]) = (p : k[X]) * X ^ 2 at heq'
    apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero (R := k)))
    calc
      X ^ 2 * (p : k[X]) = (p : k[X]) * X ^ 2 := mul_comm _ _
      _ = X ^ 3 * (q.val : k[X]) := heq'.symm
      _ = X ^ 2 * (X * (q.val : k[X])) := by ring
  exact denominator_obstruction k p q.val (by
    intro hc
    exact q.property hc) hpq

theorem sub_residue_mem_span (p : algebra k) :
    p - algebraMap k (algebra k) (residue k p) ∈
      Ideal.span {square k, cube k} := by
  obtain ⟨p, hp⟩ := p
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    rcases hp with rfl | hp
    · simpa [residue, square, Polynomial.constantCoeff] using
        (Ideal.subset_span (Set.mem_insert (square k) {cube k}))
    · rcases hp with rfl
      simpa [residue, cube, Polynomial.constantCoeff] using
        (Ideal.subset_span (Set.mem_insert_of_mem (square k) (Set.mem_singleton (cube k))))
  | algebraMap a =>
    convert (Ideal.span {square k, cube k}).zero_mem using 1
    apply Subtype.ext
    simp [residue, Polynomial.constantCoeff]
  | add p q hp hq ihp ihq =>
    convert (Ideal.span {square k, cube k}).add_mem ihp ihq using 1
    apply Subtype.ext
    simp [residue, Polynomial.constantCoeff]
    ring
  | mul p q hp hq ihp ihq =>
    have hh := (Ideal.span {square k, cube k}).add_mem
      ((Ideal.span {square k, cube k}).mul_mem_left (⟨p, hp⟩ : algebra k) ihq)
      ((Ideal.span {square k, cube k}).mul_mem_left
        (algebraMap k (algebra k) (residue k ⟨q, hq⟩)) ihp)
    convert hh using 1
    apply Subtype.ext
    simp [residue, Polynomial.constantCoeff]
    ring

/-- The kernel defining the origin is exactly the displayed two-generator ideal. -/
theorem origin_eq_span : origin k = Ideal.span {square k, cube k} := by
  apply le_antisymm
  · intro p hp
    have hr : residue k p = 0 := hp
    simpa [hr] using sub_residue_mem_span k p
  · apply Ideal.span_le.mpr
    intro p hp
    rcases hp with rfl | hp
    · change (X ^ 2 : k[X]).coeff 0 = 0
      simp
    · rcases hp with rfl
      change (X ^ 3 : k[X]).coeff 0 = 0
      simp

theorem parameter_integral_over_local : IsIntegral (Local k) (parameter k) :=
  (parameter_integral k).tower_top

theorem local_not_integrallyClosed : ¬ IsIntegrallyClosed (Local k) := by
  intro h
  let := h
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp (parameter_integral_over_local k)
  exact parameter_not_in_local_image k ⟨a, ha⟩

instance algebra_dimLE_one : Ring.KrullDimLE 1 (algebra k) := by
  apply Ring.krullDimLE_one_iff_of_noZeroDivisors.mpr
  intro p hp hprime
  let := hprime
  obtain ⟨q, _, hq, hqp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    p (⊥ : Ideal k[X]) (by simp [← RingHom.ker_eq_comap_bot])
  have hqne : q ≠ ⊥ := by
    intro h
    apply hp
    rw [← hqp, h]
    simp [← RingHom.ker_eq_comap_bot]
  let := hq
  have hmax : q.IsMaximal :=
    Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance q hqne hq
  let := hmax
  exact hqp ▸ Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := algebra k) q

theorem origin_ne_bot : origin k ≠ ⊥ := by
  intro h
  have hs : square k ∈ origin k := by
    change (X ^ 2 : k[X]).coeff 0 = 0
    simp
  rw [h] at hs
  exact square_ne_zero k hs

theorem local_dimension : ringKrullDim (Local k) = 1 := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (origin k) (Local k)]
  apply le_antisymm
  · exact (Ideal.height_le_ringKrullDim_of_isPrime (I := origin k)).trans (Ring.krullDimLE_iff.mp inferInstance)
  · have h : (1 : ℕ∞) ≤ (origin k).height :=
      Order.one_le_iff_ne_zero.mpr
        ((Ideal.height_eq_zero_iff_eq_bot).not.mpr (origin_ne_bot k))
    exact_mod_cast h

instance local_noetherian : IsNoetherianRing (Local k) := inferInstance

@[simp] theorem fractionEmbedding_algebraMap (a : algebra k) :
    fractionEmbedding k (algebraMap (algebra k) (FractionRing (algebra k)) a) =
      algebraMap k[X] (FractionRing k[X]) (a : k[X]) :=
  IsFractionRing.lift_algebraMap _ a

/-- The fraction `t³/t²` is the original polynomial parameter, not a new element. -/
theorem fractionEmbedding_parameter : fractionEmbedding k (parameter k) =
    algebraMap k[X] (FractionRing k[X]) X := by
  have hx : algebraMap k[X] (FractionRing k[X]) X ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr X_ne_zero
  simp only [parameter, map_div₀, fractionEmbedding_algebraMap, square, cube,
    map_pow]
  field_simp

/-- The same obstruction inside the original ambient rational function field. -/
theorem polynomial_parameter_not_in_local_image :
    algebraMap k[X] (FractionRing k[X]) X ∉
      Set.range ((fractionEmbedding k).comp (localToFraction k)) := by
  rintro ⟨a, ha⟩
  apply parameter_not_in_local_image k
  refine ⟨a, (fractionEmbedding k).injective ?_⟩
  rw [fractionEmbedding_parameter]
  exact ha

/-- A Noetherian domain of dimension at most one satisfies every Serre depth condition. -/
theorem serreCondition_of_domain_dim_le_one (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (hd : ringKrullDim R ≤ 1) (n : ℕ) :
    CohenMacaulay.RingSerreCondition R n := by
  intro p hp
  let S := Localization.AtPrime p.asIdeal
  let M := LocalizedModule.AtPrime p.asIdeal R
  have hdim : Module.supportDim S M ≤ (1 : WithBot ℕ∞) := by
    apply (Module.supportDim_le_ringKrullDim S M).trans
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal S]
    exact Ideal.height_le_ringKrullDim_of_isPrime.trans hd
  by_cases hz : IsLocalRing.depth (ModuleCat.of S M) = 0
  · have hass := (CohenMacaulay.localized_depth_eq_zero_iff_associated R R p hp).mp hz
    have hbot : p.asIdeal = ⊥ := by
      apply le_antisymm _ bot_le
      intro a ha
      have hzero : a ∈ (nonZeroDivisors R : Set R)ᶜ := by
        rw [← biUnion_associatedPrimes_eq_compl_nonZeroDivisors R]
        exact Set.mem_iUnion₂_of_mem hass ha
      simpa [mem_nonZeroDivisors_iff_ne_zero] using hzero
    have hdim0 : Module.supportDim S M ≤ 0 := by
      apply (Module.supportDim_le_ringKrullDim S M).trans
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal S, hbot, Ideal.height_bot]
      exact le_rfl
    exact (min_le_right _ _).trans (hdim0.trans (by simp))
  · have hdepth : (1 : WithBot ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of S M) := by
      exact_mod_cast Order.one_le_iff_ne_zero.mpr hz
    exact (min_le_right _ _).trans (hdim.trans hdepth)

theorem local_serre_two : CohenMacaulay.RingSerreCondition (Local k) 2 :=
  serreCondition_of_domain_dim_le_one (Local k) (local_dimension k).le 2

/-- In dimension one, the closed point in `(R₁)` tests the local ring itself. -/
theorem not_regularInCodimension_one_of_not_integrallyClosed
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 1) (hnormal : ¬ IsIntegrallyClosed R) :
    ¬ RegularInCodimension R 1 := by
  intro h
  have : IsRegularLocalRing
      (Localization.AtPrime (IsLocalRing.maximalIdeal R)) := by
    apply h (IsLocalRing.closedPoint R)
    apply WithBot.coe_le_coe.mp
    change ((IsLocalRing.maximalIdeal R).height : WithBot ℕ∞) ≤ (1 : WithBot ℕ∞)
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdim]
  let e : R ≃ₐ[R] Localization.AtPrime (IsLocalRing.maximalIdeal R) :=
    IsLocalization.atUnits R (IsLocalRing.maximalIdeal R).primeCompl
      (fun x => by simpa using! fun a => a)
  have : IsRegularLocalRing R := IsRegularLocalRing.of_ringEquiv e.toRingEquiv.symm
  exact hnormal ((dimension_one_dvr_equivalences R hdim).1.mpr inferInstance)

theorem local_not_regularInCodimension_one : ¬ RegularInCodimension (Local k) 1 :=
  not_regularInCodimension_one_of_not_integrallyClosed (Local k)
    (local_dimension k) (local_not_integrallyClosed k)

theorem algebra_dimension : ringKrullDim (algebra k) = 1 := by
  apply le_antisymm (Ring.krullDimLE_iff.mp inferInstance)
  calc
    1 = ringKrullDim (Local k) := (local_dimension k).symm
    _ = (origin k).height :=
      IsLocalization.AtPrime.ringKrullDim_eq_height (origin k) (Local k)
    _ ≤ ringKrullDim (algebra k) := Ideal.height_le_ringKrullDim_of_isPrime

theorem polynomial_dimension : ringKrullDim k[X] = 1 :=
  IsPrincipalIdealRing.ringKrullDim_eq_one k[X] (Polynomial.not_isField k)

/-- The cusp separates the two Serre conditions over every field. -/
theorem cuspExample : Specs.cuspExampleType.{u} := by
  intro k _
  exact ⟨origin_eq_span k, inferInstance, inferInstance, inferInstance,
    inferInstance, X_integral k, fractionEmbedding_parameter k,
    parameter_integral k, parameter_integral_over_local k,
    parameter_not_in_local_image k, polynomial_parameter_not_in_local_image k,
    inferInstance, inferInstance,
    algebra_dimension k, polynomial_dimension k, local_dimension k,
    inferInstance, local_serre_two k, local_not_regularInCodimension_one k⟩

end AdvCommAlg.Normality.Cusp
