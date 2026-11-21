import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.Mobius
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereHolomorphic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Batteries.Tactic.OpenPrivate

open scoped Topology
open Filter
noncomputable section
namespace D12Complex.MobiusDefinitions
abbrev Regular := D12Complex.Mobius.Regular
abbrev spherePair := D12Complex.Mobius.spherePair
abbrev mobiusMap := D12Complex.Mobius.mobiusMap
abbrev inverseCoefficients := D12Complex.Mobius.inverseCoefficients
abbrev SphereBiholomorphicPair := D12Complex.Mobius.SphereBiholomorphicPair
end D12Complex.MobiusDefinitions

namespace D12Complex.Mobius

open private coordinate_open coordinate_continuousAt from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereHolomorphic

theorem mobiusMap_finite (M : Coefficients) (z : ℂ)
    (hz : M 1 0 * z + M 1 1 ≠ 0) :
    mobiusMap M (sphereFinite z) =
      sphereFinite ((M 0 0 * z + M 0 1) / (M 1 0 * z + M 1 1)) := by
  simp [mobiusMap, sphereFinite, spherePair, hz]

theorem mobiusMap_pole (M : Coefficients) (_hM : Regular M) (hc : M 1 0 ≠ 0) :
    mobiusMap M (sphereFinite (-M 1 1 / M 1 0)) = sphereInfty := by
  have h : M 1 0 * (-M 1 1 / M 1 0) + M 1 1 = 0 := by field_simp; ring
  simp [mobiusMap, sphereFinite, spherePair, h]

theorem mobiusMap_infty (M : Coefficients) :
    (M 1 0 ≠ 0 → mobiusMap M sphereInfty = sphereFinite (M 0 0 / M 1 0)) ∧
    (M 1 0 = 0 → mobiusMap M sphereInfty = sphereInfty) := by
  constructor <;> intro h <;> simp [mobiusMap, sphereInfty, spherePair, h]

theorem spherePair_scale (x y k : ℂ) (hk : k ≠ 0) :
    spherePair (k * x) (k * y) = spherePair x y := by
  by_cases hy : y = 0
  · simp [spherePair, hy]
  · simp [spherePair, hy, hk, mul_div_mul_left]

theorem spherePair_self (z : ℂ) : spherePair z 1 = sphereFinite z := by
  simp [spherePair]

theorem mobiusMap_one : mobiusMap 1 = id := by
  funext p
  induction p using OnePoint.rec with
  | infty => simp [mobiusMap, spherePair, sphereInfty]
  | coe z => simp [mobiusMap, spherePair, sphereFinite]

theorem regular_mul (M N : Coefficients) (hM : Regular M) (hN : Regular N) :
    Regular (M * N) := by
  exact (Matrix.det_mul M N).trans_ne (mul_ne_zero hM hN)

theorem regular_inverseCoefficients (M : Coefficients) (hM : Regular M) :
    Regular (inverseCoefficients M) := by
  change (inverseCoefficients M).det ≠ 0
  simpa [inverseCoefficients, Matrix.det_fin_two, Regular, mul_comm] using hM

/-- Invertibility excludes the zero column in every homogeneous coordinate. -/
theorem image_pair_nonzero (M : Coefficients) (hM : Regular M)
    (x y : ℂ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    M 0 0 * x + M 0 1 * y ≠ 0 ∨ M 1 0 * x + M 1 1 * y ≠ 0 := by
  by_contra h
  push Not at h
  have hx : M.det * x = 0 := by
    rw [Matrix.det_fin_two]
    linear_combination M 1 1 * h.1 - M 0 1 * h.2
  have hy : M.det * y = 0 := by
    rw [Matrix.det_fin_two]
    linear_combination -M 1 0 * h.1 + M 0 0 * h.2
  exact hxy.elim (fun hn => hn ((mul_eq_zero.mp hx).resolve_left hM))
    (fun hn => hn ((mul_eq_zero.mp hy).resolve_left hM))

/-- The homogeneous action formula, independent of the chosen nonzero representative. -/
theorem mobiusMap_pair (M : Coefficients) (x y : ℂ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    mobiusMap M (spherePair x y) =
      spherePair (M 0 0 * x + M 0 1 * y) (M 1 0 * x + M 1 1 * y) := by
  by_cases hy : y = 0
  · subst y
    have hx := hxy.resolve_right (not_ne_iff.mpr rfl)
    rw [show spherePair x 0 = sphereInfty by simp [spherePair]]
    change spherePair (M 0 0) (M 1 0) = _
    simpa only [mul_zero, zero_mul, add_zero, mul_comm] using (spherePair_scale (M 0 0) (M 1 0) x hx).symm
  · rw [spherePair, ite_eq_right (by exact hy)]
    change spherePair (M 0 0 * (x / y) + M 0 1) (M 1 0 * (x / y) + M 1 1) = _
    have hn : M 0 0 * (x / y) + M 0 1 = y⁻¹ * (M 0 0 * x + M 0 1 * y) := by
      field_simp
    have hd : M 1 0 * (x / y) + M 1 1 = y⁻¹ * (M 1 0 * x + M 1 1 * y) := by
      field_simp
    rw [hn, hd, spherePair_scale _ _ _ (inv_ne_zero hy)]

theorem mobiusMap_mul (M N : Coefficients) (_hM : Regular M) (hN : Regular N) :
    mobiusMap (M * N) = mobiusMap M ∘ mobiusMap N := by
  funext p
  induction p using OnePoint.rec with
  | infty =>
    change spherePair _ _ = mobiusMap M (spherePair _ _)
    have hcol : N 0 0 ≠ 0 ∨ N 1 0 ≠ 0 := by
      simpa using image_pair_nonzero N hN 1 0 (Or.inl one_ne_zero)
    rw [mobiusMap_pair M _ _ hcol]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
  | coe z =>
    change spherePair _ _ = mobiusMap M (spherePair _ _)
    have hcol : N 0 0 * z + N 0 1 ≠ 0 ∨ N 1 0 * z + N 1 1 ≠ 0 := by
      simpa using image_pair_nonzero N hN z 1 (Or.inr one_ne_zero)
    rw [mobiusMap_pair M _ _ hcol]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    congr 1 <;> ring

theorem mobiusMap_smul (M : Coefficients) (k : ℂ) (hk : k ≠ 0) :
    mobiusMap (k • M) = mobiusMap M := by
  funext p
  induction p using OnePoint.rec with
  | infty => exact spherePair_scale _ _ k hk
  | coe z =>
    change spherePair (k * M 0 0 * z + k * M 0 1)
      (k * M 1 0 * z + k * M 1 1) = _
    rw [show k * M 0 0 * z + k * M 0 1 = k * (M 0 0 * z + M 0 1) by ring,
      show k * M 1 0 * z + k * M 1 1 = k * (M 1 0 * z + M 1 1) by ring]
    exact spherePair_scale _ _ k hk

theorem inverseCoefficients_mul (M : Coefficients) :
    inverseCoefficients M * M = M.det • (1 : Coefficients) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverseCoefficients, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem mul_inverseCoefficients (M : Coefficients) :
    M * inverseCoefficients M = M.det • (1 : Coefficients) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverseCoefficients, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem mobiusMap_inverse (M : Coefficients) (hM : Regular M) :
    Function.LeftInverse (mobiusMap (inverseCoefficients M)) (mobiusMap M) ∧
    Function.RightInverse (mobiusMap (inverseCoefficients M)) (mobiusMap M) := by
  have hI := regular_inverseCoefficients M hM
  have hl : mobiusMap (inverseCoefficients M) ∘ mobiusMap M = id := by
    rw [← mobiusMap_mul _ _ hI hM, inverseCoefficients_mul,
      mobiusMap_smul _ _ hM, mobiusMap_one]
  have hr : mobiusMap M ∘ mobiusMap (inverseCoefficients M) = id := by
    rw [← mobiusMap_mul _ _ hM hI, mul_inverseCoefficients,
      mobiusMap_smul _ _ hM, mobiusMap_one]
  exact ⟨fun p => congrFun hl p, fun p => congrFun hr p⟩

theorem spherePair_eq_infty_iff (x y : ℂ) : spherePair x y = sphereInfty ↔ y = 0 := by
  by_cases hy : y = 0 <;> simp [spherePair, hy, sphereFinite, sphereInfty]

/-- An invertible matrix inducing the identity is a nonzero scalar matrix. -/
theorem scalar_of_mobiusMap_eq_id (M : Coefficients) (hM : Regular M)
    (h : mobiusMap M = id) : ∃ k : ℂ, k ≠ 0 ∧ M = k • (1 : Coefficients) := by
  have hc : M 1 0 = 0 := by
    apply (spherePair_eq_infty_iff _ _).mp
    exact congrFun h sphereInfty
  have hd : M 1 1 ≠ 0 := by
    intro hd
    apply hM
    simp [Matrix.det_fin_two, hc, hd]
  have hb : M 0 1 = 0 := by
    have h0 := congrFun h (sphereFinite 0)
    have he : sphereFinite (M 0 1 / M 1 1) = sphereFinite 0 := by
      simpa [mobiusMap, spherePair, sphereFinite, hc, hd] using h0
    exact (div_eq_zero_iff.mp (sphereFinite_injective he)).resolve_right hd
  have ha : M 0 0 = M 1 1 := by
    have h1 := congrFun h (sphereFinite 1)
    have he : sphereFinite (M 0 0 / M 1 1) = sphereFinite 1 := by
      simpa [mobiusMap, spherePair, sphereFinite, hc, hb, hd] using h1
    exact (div_eq_one_iff_eq hd).mp (sphereFinite_injective he)
  refine ⟨M 1 1, hd, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc, hb, ha]

theorem mobiusMap_eq_iff (M N : Coefficients) (hM : Regular M) (hN : Regular N) :
    mobiusMap M = mobiusMap N ↔ ∃ k : ℂ, k ≠ 0 ∧ M = k • N := by
  constructor
  · intro he
    have hI := regular_inverseCoefficients N hN
    have hK := regular_mul (inverseCoefficients N) M hI hM
    have hmap : mobiusMap (inverseCoefficients N * M) = id := by
      rw [mobiusMap_mul _ _ hI hM, he]
      funext p
      exact (mobiusMap_inverse N hN).1 p
    obtain ⟨k, hk, hke⟩ := scalar_of_mobiusMap_eq_id _ hK hmap
    have hmul : N.det • M = k • N := by
      calc
        N.det • M = (N * inverseCoefficients N) * M := by
          rw [mul_inverseCoefficients, smul_mul_assoc, one_mul]
        _ = N * (inverseCoefficients N * M) := mul_assoc _ _ _
        _ = k • N := by rw [hke, mul_smul_comm, mul_one]
    refine ⟨N.det⁻¹ * k, mul_ne_zero (inv_ne_zero hN) hk, ?_⟩
    have hscaled := congrArg (fun A : Coefficients => N.det⁻¹ • A) hmul
    simpa [smul_smul, show N.det ≠ 0 from hN] using hscaled
  · rintro ⟨k, hk, rfl⟩
    exact mobiusMap_smul N k hk


/-- A quotient of holomorphic germs is holomorphic where its denominator is nonzero. -/
theorem holomorphicGermAt_div {u v : ℂ → ℂ} {a : ℂ}
    (hu : HolomorphicGermAt u a) (hv : HolomorphicGermAt v a) (ha : v a ≠ 0) :
    HolomorphicGermAt (fun z => u z / v z) a := by
  have hne := hv.differentiableAt.continuousAt.eventually_ne ha
  rw [holomorphicGermAt_iff_eventually] at hu hv ⊢
  filter_upwards [hu, hv, hne] with z hz h'z hnz
  exact hz.div h'z hnz

/-- On the infinity target chart [x:y] has coordinate y/x, including y=0. -/
theorem spherePair_eq_infinityParametrization (x y : ℂ) (hx : x ≠ 0) :
    spherePair x y = infinityParametrization (y / x) := by
  by_cases hy : y = 0
  · simp [spherePair, hy, infinityParametrization]
  · simp [spherePair, hy, hx, infinityParametrization, inv_div]

/-- Local homogeneous holomorphic expressions supply continuity as well as
holomorphy, even at a zero of the denominator. -/
theorem planeSphereHolomorphicAt_pair {u v : ℂ → ℂ} {a : ℂ}
    (hu : HolomorphicGermAt u a) (hv : HolomorphicGermAt v a)
    (ha : u a ≠ 0 ∨ v a ≠ 0) :
    PlaneSphereHolomorphicAt (fun z => spherePair (u z) (v z)) a := by
  by_cases hva : v a = 0
  · have hua : u a ≠ 0 := ha.resolve_right (not_ne_iff.mpr hva)
    have hq := holomorphicGermAt_div hv hu hua
    have hne := hu.differentiableAt.continuousAt.eventually_ne hua
    have he : (fun z => spherePair (u z) (v z)) =ᶠ[𝓝 a]
        (fun z => infinityParametrization (v z / u z)) := by
      filter_upwards [hne] with z hz
      exact spherePair_eq_infinityParametrization _ _ hz
    have hcont : ContinuousAt (fun z => spherePair (u z) (v z)) a :=
      (continuous_infinityParametrization.continuousAt.comp
        hq.differentiableAt.continuousAt).congr_of_eventuallyEq he
    refine ⟨hcont, .reciprocal, ?_, ?_⟩
    · change spherePair (u a) (v a) ≠ sphereFinite 0
      simp [spherePair, hva, sphereInfty, sphereFinite]
    · apply hq.congr
      filter_upwards [he] with z hz
      change v z / u z = infinityCoordinate (spherePair (u z) (v z))
      rw [hz]
      exact (infinityChart.right_inv (Set.mem_univ _)).symm
  · have hq := holomorphicGermAt_div hu hv hva
    have hne := hv.differentiableAt.continuousAt.eventually_ne hva
    have he : (fun z => spherePair (u z) (v z)) =ᶠ[𝓝 a]
        (fun z => sphereFinite (u z / v z)) := by
      filter_upwards [hne] with z hz
      simp [spherePair, hz]
    have hcont : ContinuousAt (fun z => spherePair (u z) (v z)) a :=
      (continuous_sphereFinite.continuousAt.comp
        hq.differentiableAt.continuousAt).congr_of_eventuallyEq he
    refine ⟨hcont, .finite, ?_, ?_⟩
    · change spherePair (u a) (v a) ≠ sphereInfty
      simp [spherePair_eq_infty_iff, hva]
    · apply hq.congr
      filter_upwards [he] with z hz
      change u z / v z = finiteCoordinate (spherePair (u z) (v z))
      rw [hz, finiteCoordinate_sphereFinite]

/-- Transfer a plane-source expression back through either genuine source chart. -/
theorem sphereHolomorphicAt_of_pullback (F : RiemannSphere → RiemannSphere)
    (p : RiemannSphere) (c : SphereCoordinate)
    (hc : p ∈ (sphereCoordinate c).source)
    (h : PlaneSphereHolomorphicAt (fun z => F ((sphereCoordinate c).symm z))
      (sphereCoordinate c p)) : SphereHolomorphicAt F p := by
  have he := (sphereCoordinate c).left_inv hc
  have hcc := coordinate_continuousAt c p hc
  have hcont : ContinuousAt F p := by
    have hh := h.1.comp hcc
    apply hh.congr_of_eventuallyEq
    filter_upwards [(coordinate_open c).mem_nhds hc] with q hq
    exact congrArg F ((sphereCoordinate c).left_inv hq).symm
  rcases h.2 with ⟨d, hd, hg⟩
  exact ⟨hcont, c, d, hc, by simpa only [he] using hd, hg⟩

/-- The pullback in the infinity source coordinate is [a+bw:c+dw]. -/
theorem mobiusMap_infinityParametrization (M : Coefficients) (w : ℂ) :
    mobiusMap M (infinityParametrization w) =
      spherePair (M 0 0 + M 0 1 * w) (M 1 0 + M 1 1 * w) := by
  have he : infinityParametrization w = spherePair 1 w := by
    by_cases hw : w = 0 <;> simp [spherePair, infinityParametrization, hw, one_div]
  rw [he, mobiusMap_pair M 1 w (Or.inl one_ne_zero)]
  simp

/-- All four source/target chart combinations, including the pole and infinity,
are covered by local quotients of affine holomorphic functions. -/
theorem mobiusMap_holomorphic (M : Coefficients) (hM : Regular M) :
    SphereHolomorphicOn Set.univ (mobiusMap M) := by
  refine ⟨isOpen_univ, fun p _ => ?_⟩
  induction p using OnePoint.rec with
  | infty =>
    apply sphereHolomorphicAt_of_pullback _ sphereInfty .reciprocal
      (OnePoint.infty_ne_coe 0)
    have hn : M 0 0 ≠ 0 ∨ M 1 0 ≠ 0 := by
      simpa using image_pair_nonzero M hM 1 0 (Or.inl one_ne_zero)
    have hu : HolomorphicGermAt (fun w : ℂ => M 0 0 + M 0 1 * w) 0 :=
      ⟨Set.univ, Set.mem_univ _, isOpen_univ, fun _ _ =>
        (differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id)⟩
    have hv : HolomorphicGermAt (fun w : ℂ => M 1 0 + M 1 1 * w) 0 :=
      ⟨Set.univ, Set.mem_univ _, isOpen_univ, fun _ _ =>
        (differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id)⟩
    have hp := planeSphereHolomorphicAt_pair hu hv (by simpa using hn)
    change PlaneSphereHolomorphicAt (fun w => mobiusMap M (infinityParametrization w)) 0
    simpa only [mobiusMap_infinityParametrization] using hp
  | coe z =>
    apply sphereHolomorphicAt_of_pullback _ (sphereFinite z) .finite
      (OnePoint.coe_ne_infty z)
    have hn : M 0 0 * z + M 0 1 ≠ 0 ∨ M 1 0 * z + M 1 1 ≠ 0 := by
      simpa using image_pair_nonzero M hM z 1 (Or.inr one_ne_zero)
    have hu : HolomorphicGermAt (fun w : ℂ => M 0 0 * w + M 0 1) z :=
      ⟨Set.univ, Set.mem_univ _, isOpen_univ, fun _ _ =>
        ((differentiableAt_const _).mul differentiableAt_id).add (differentiableAt_const _)⟩
    have hv : HolomorphicGermAt (fun w : ℂ => M 1 0 * w + M 1 1) z :=
      ⟨Set.univ, Set.mem_univ _, isOpen_univ, fun _ _ =>
        ((differentiableAt_const _).mul differentiableAt_id).add (differentiableAt_const _)⟩
    exact planeSphereHolomorphicAt_pair hu hv hn

theorem mobiusMap_biholomorphic (M : Coefficients) (hM : Regular M) :
    SphereBiholomorphicPair (mobiusMap M) (mobiusMap (inverseCoefficients M)) :=
  ⟨mobiusMap_holomorphic M hM,
    mobiusMap_holomorphic _ (regular_inverseCoefficients M hM), mobiusMap_inverse M hM⟩

theorem mobiusMap_bijective (M : Coefficients) (hM : Regular M) :
    Function.Bijective (mobiusMap M) :=
  ⟨(mobiusMap_inverse M hM).1.injective, (mobiusMap_inverse M hM).2.surjective⟩

/-- The permutation group of the sphere represented by these matrices. -/
theorem mobiusMap_group :
    ∃ G : Subgroup (Equiv.Perm RiemannSphere), ∀ e : Equiv.Perm RiemannSphere,
      e ∈ G ↔ ∃ M : Coefficients, Regular M ∧ ∀ p, e p = mobiusMap M p := by
  let G : Subgroup (Equiv.Perm RiemannSphere) := {
    carrier := {e | ∃ M : Coefficients, Regular M ∧ ∀ p, e p = mobiusMap M p}
    one_mem' := by
      refine ⟨1, ?_, ?_⟩
      · simp [Regular]
      · intro p
        exact (congrFun mobiusMap_one p).symm
    mul_mem' := by
      rintro e f ⟨M, hM, he⟩ ⟨N, hN, hf⟩
      refine ⟨M * N, regular_mul M N hM hN, ?_⟩
      intro p
      change e (f p) = mobiusMap (M * N) p
      rw [he, hf]
      exact (congrFun (mobiusMap_mul M N hM hN) p).symm
    inv_mem' := by
      rintro e ⟨M, hM, he⟩
      refine ⟨inverseCoefficients M, regular_inverseCoefficients M hM, ?_⟩
      intro p
      change e.symm p = mobiusMap (inverseCoefficients M) p
      apply e.injective
      rw [e.apply_symm_apply, he]
      exact ((mobiusMap_inverse M hM).2 p).symm }
  exact ⟨G, fun _ => Iff.rfl⟩

end D12Complex.Mobius
