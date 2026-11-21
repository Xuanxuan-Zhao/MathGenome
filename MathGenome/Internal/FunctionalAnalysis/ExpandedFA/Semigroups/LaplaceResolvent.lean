import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.LaplaceResolvent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.SemigroupGrowthAndGenerator
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
Laplace resolvents for the exact-domain generator of a real or complex C₀
semigroup, paper.tex 14449–14457. All integration is vector-valued. The proof
uses weighted orbit integration by parts and graph closedness. The recurrence
for the moments then proves all powers without a multivariable integral.
-/

noncomputable section
open MeasureTheory Filter Set Topology

namespace ExpandedFA.Semigroups.LaplaceResolvent
open LaplaceResolventSpec

variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem norm_scalar_exp (z : 𝕜) : ‖NormedSpace.exp z‖ = Real.exp (RCLike.re z) := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · let e := RCLike.realRingEquiv h
    have he : e (NormedSpace.exp z) = NormedSpace.exp (e z) :=
      NormedSpace.map_exp e (RCLike.realLinearIsometryEquiv h).continuous z
    rw [← (RCLike.realLinearIsometryEquiv h).norm_map]
    change ‖e (NormedSpace.exp z)‖ = _
    rw [he, ← Real.exp_eq_exp_ℝ]
    exact Real.norm_eq_abs _ |>.trans (abs_of_pos (Real.exp_pos _))
  · let e := RCLike.complexRingEquiv h
    have he : e (NormedSpace.exp z) = NormedSpace.exp (e z) :=
      NormedSpace.map_exp e (RCLike.complexLinearIsometryEquiv h).continuous z
    rw [← (RCLike.complexLinearIsometryEquiv h).norm_map]
    change ‖e (NormedSpace.exp z)‖ = _
    rw [he, ← Complex.exp_eq_exp_ℂ, Complex.norm_exp]
    simp [e, RCLike.complexRingEquiv]

theorem norm_kernel (ζ : 𝕜) (t : ℝ) :
    ‖kernel ζ t‖ = Real.exp (-RCLike.re ζ * t) := by
  rw [kernel, norm_scalar_exp]
  congr 1
  simp only [RCLike.smul_re]
  ring

@[simp] theorem kernel_zero (ζ : 𝕜) : kernel ζ 0 = 1 := by
  simp [kernel]

theorem hasDerivAt_kernel (ζ : 𝕜) (t : ℝ) :
    HasDerivAt (kernel ζ) (-ζ * kernel ζ t) t := by
  unfold kernel
  simpa only [smul_neg, neg_smul] using
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-ζ) t)

theorem continuous_kernel (ζ : 𝕜) : Continuous (kernel ζ) :=
  NormedSpace.exp_continuous.comp (continuous_id.neg.smul continuous_const)

local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
local instance : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X

theorem continuous_orbit (T : C0Semigroup 𝕜 X) (ζ : 𝕜) (x : X) :
    Continuous (orbit T ζ x) :=
  (continuous_kernel ζ).smul
    (T.continuous_real_orbit x)

theorem norm_orbit_le (T : C0Semigroup 𝕜 X) {M ω : ℝ}
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (ζ : 𝕜)
    (x : X) {t : ℝ} (ht : 0 ≤ t) :
    ‖orbit T ζ x t‖ ≤ (M * ‖x‖) * Real.exp (-(RCLike.re ζ - ω) * t) := by
  rw [orbit, norm_smul, norm_kernel]
  calc
    _ ≤ Real.exp (-RCLike.re ζ * t) *
        ((M * Real.exp (ω * t)) * ‖x‖) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact (T.operators t.toNNReal).le_opNorm x |>.trans
        (mul_le_mul_of_nonneg_right (by simpa [Real.coe_toNNReal _ ht] using hT.2 t.toNNReal)
          (norm_nonneg x))
    _ = _ := by rw [show -(RCLike.re ζ - ω) * t = -RCLike.re ζ * t + ω * t by ring,
      Real.exp_add]; ring

/-- The scalar majorant is integrable for every natural moment. -/
theorem scalar_moment_integrable (n : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-a * t)) (Ioi 0) := by
  simpa only [Real.rpow_natCast, Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n : ℝ))
      (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)) zero_lt_one ha)

theorem scalar_moment_integral (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, t ^ n * Real.exp (-a * t)) =
      (n.factorial : ℝ) / a ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := ((n + 1 : ℕ) : ℝ)) (r := a) (by positivity) ha
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Real.rpow_natCast,
    ← neg_mul] at h
  rw [h, Real.Gamma_nat_eq_factorial, ← Nat.cast_add_one, Real.rpow_natCast]
  ring

theorem norm_weighted_orbit_le (T : C0Semigroup 𝕜 X) {M ω : ℝ}
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (ζ : 𝕜)
    (n : ℕ) (x : X) {t : ℝ} (ht : 0 ≤ t) :
    ‖t ^ n • orbit T ζ x t‖ ≤
      (M * ‖x‖) * (t ^ n * Real.exp (-(RCLike.re ζ - ω) * t)) := by
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg ht n)]
  exact (mul_le_mul_of_nonneg_left (norm_orbit_le T hT ζ x ht) (pow_nonneg ht n)).trans_eq
    (by ring)

theorem weighted_integrability : LaplaceResolventSpec.Integrability (𝕜 := 𝕜) (X := X) := by
  intro T M ω ζ hT hζ n x
  refine ((scalar_moment_integrable n (sub_pos.mpr hζ)).const_mul (M * ‖x‖)).mono'
    (((continuous_id.pow n).smul (continuous_orbit T ζ x)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_weighted_orbit_le T hT ζ n x ht.le

theorem weighted_integral_bound (T : C0Semigroup 𝕜 X) {M ω : ℝ}
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (ζ : 𝕜)
    (hζ : ω < RCLike.re ζ) (n : ℕ) (x : X) :
    ‖∫ t : ℝ in Ioi 0, t ^ n • orbit T ζ x t‖ ≤
      (M * ‖x‖) * ((n.factorial : ℝ) / (RCLike.re ζ - ω) ^ (n + 1)) := by
  have hb := norm_integral_le_of_norm_le
    ((scalar_moment_integrable n (sub_pos.mpr hζ)).const_mul (M * ‖x‖))
    (f := fun t : ℝ => t ^ n • orbit T ζ x t) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_weighted_orbit_le T hT ζ n x ht.le)
  simpa only [integral_const_mul, scalar_moment_integral n (sub_pos.mpr hζ)] using hb

theorem moment_bound : LaplaceResolventSpec.MomentBound (𝕜 := 𝕜) (X := X) := by
  intro T M ω ζ hT hζ n x
  rw [moment, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (n.factorial : ℝ)⁻¹)]
  calc
    _ ≤ (n.factorial : ℝ)⁻¹ *
        ((M * ‖x‖) * ((n.factorial : ℝ) / (RCLike.re ζ - ω) ^ (n + 1))) :=
      mul_le_mul_of_nonneg_left (weighted_integral_bound T hT ζ hζ n x) (by positivity)
    _ = _ := by
      have hn : (n.factorial : ℝ) ≠ 0 := by positivity
      field_simp

theorem weighted_orbit_tendsto_zero (T : C0Semigroup 𝕜 X) {M ω : ℝ}
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (ζ : 𝕜)
    (hζ : ω < RCLike.re ζ) (n : ℕ) (x : X) :
    Tendsto (fun t : ℝ => t ^ n • orbit T ζ x t) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun t : ℝ =>
    (M * ‖x‖) * (t ^ n * Real.exp (-(RCLike.re ζ - ω) * t)))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact norm_weighted_orbit_le T hT ζ n x ht
  · simpa only [mul_zero, Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ)
        (RCLike.re ζ - ω) (sub_pos.mpr hζ)).const_mul (M * ‖x‖)

/-- Integration preserves a closed linear subspace, even for an infinite measure.
The quotient map reduces this to integration of the zero function. -/
theorem integral_mem_closed_submodule {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (S : Submodule ℝ E)
    (hS : IsClosed (S : Set E)) {f : ℝ → E} {μ : Measure ℝ}
    (hf : Integrable f μ) (hm : ∀ᵐ t ∂μ, f t ∈ S) : (∫ t, f t ∂μ) ∈ S := by
  let : IsClosed (S : Set E) := hS
  apply (Submodule.Quotient.mk_eq_zero S).mp
  change S.mkQL (∫ t, f t ∂μ) = 0
  rw [← S.mkQL.integral_comp_comm hf]
  apply integral_eq_zero_of_ae
  filter_upwards [hm] with t ht
  exact (Submodule.Quotient.mk_eq_zero S).mpr ht

/-- The unnormalized Laplace moments as bounded scalar-linear operators. -/
def integralOperator (T : C0Semigroup 𝕜 X) (M ω : ℝ) (ζ : 𝕜)
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (hζ : ω < RCLike.re ζ)
    (n : ℕ) : X →L[𝕜] X := by
  let L : X →ₗ[𝕜] X :=
    { toFun := fun x => ∫ t : ℝ in Ioi 0, t ^ n • orbit T ζ x t
      map_add' := by
        intro x y
        simp only [orbit, map_add, smul_add]
        exact integral_add (weighted_integrability T M ω ζ hT hζ n x)
          (weighted_integrability T M ω ζ hT hζ n y)
      map_smul' := by
        intro c x
        simp only [orbit, map_smul, RingHom.id_apply, smul_comm _ c]
        exact integral_smul c _ }
  apply L.mkContinuousOfExistsBound
  refine ⟨M * ((n.factorial : ℝ) / (RCLike.re ζ - ω) ^ (n + 1)), fun x => ?_⟩
  exact (weighted_integral_bound T hT ζ hζ n x).trans_eq (by ring)

@[simp] theorem integralOperator_apply (T : C0Semigroup 𝕜 X) (M ω : ℝ) (ζ : 𝕜)
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (hζ : ω < RCLike.re ζ)
    (n : ℕ) (x : X) :
    integralOperator T M ω ζ hT hζ n x = ∫ t : ℝ in Ioi 0, t ^ n • orbit T ζ x t := rfl

theorem hasDerivAt_orbit (T : C0Semigroup 𝕜 X) (ζ : 𝕜)
    (x : (generator T).domain) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (orbit T ζ x)
      (orbit T ζ (generator T x) t - ζ • orbit T ζ x t) t := by
  have hd := (hasDerivAt_kernel ζ t).smul
    ((T.hasDerivWithinAt_orbit x t ht.le).hasDerivAt (Ici_mem_nhds ht))
  convert hd using 1
  · rfl
  · simp only [orbit, mul_smul, neg_smul, sub_eq_add_neg]

theorem integralOperator_graph (T : C0Semigroup 𝕜 X) (M ω : ℝ) (ζ : 𝕜)
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (hζ : ω < RCLike.re ζ)
    (n : ℕ) (x : (generator T).domain) :
    (integralOperator T M ω ζ hT hζ n x,
      integralOperator T M ω ζ hT hζ n (generator T x)) ∈ (generator T).graph := by
  let S : Submodule ℝ (X × X) := (generator T).graph.restrictScalars ℝ
  have hf := (weighted_integrability T M ω ζ hT hζ n x).prodMk
    (weighted_integrability T M ω ζ hT hζ n (generator T x))
  have hmem : ∀ t : ℝ, (t ^ n • orbit T ζ x t,
      t ^ n • orbit T ζ (generator T x) t) ∈ S := by
    intro t
    have hg : (T.operators t.toNNReal x,
        T.operators t.toNNReal (generator T x)) ∈ (generator T).graph := by
      exact (mem_generator_graph_iff T _ _).mpr
        (T.hasGeneratorLimit_map t.toNNReal (generator_has_limit T x))
    have hk := (generator T).graph.smul_mem (kernel ζ t) hg
    have hk' : (orbit T ζ x t, orbit T ζ (generator T x) t) ∈ S := hk
    exact S.smul_mem (t ^ n) hk'
  have hi := integral_mem_closed_submodule S (T.generator_graph_closed) hf
    (Eventually.of_forall hmem)
  change (_, _) ∈ S
  simpa only [integral_pair (weighted_integrability T M ω ζ hT hζ n x)
    (weighted_integrability T M ω ζ hT hζ n (generator T x)), integralOperator_apply] using hi

theorem laplace_difference (T : C0Semigroup 𝕜 X) (M ω : ℝ) (ζ : 𝕜)
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (hζ : ω < RCLike.re ζ)
    (x : (generator T).domain) :
    ζ • integralOperator T M ω ζ hT hζ 0 x -
      integralOperator T M ω ζ hT hζ 0 (generator T x) = x := by
  have hf (y : X) : IntegrableOn (orbit T ζ y) (Ioi 0) := by
    simpa only [pow_zero, one_smul] using weighted_integrability T M ω ζ hT hζ 0 y
  have hl : Tendsto (orbit T ζ (x : X)) atTop (𝓝 0) := by
    simpa only [pow_zero, one_smul] using weighted_orbit_tendsto_zero T hT ζ hζ 0 x
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto
    (continuous_orbit T ζ (x : X)).continuousAt.continuousWithinAt
    (fun t ht => hasDerivAt_orbit T ζ x ht)
    ((hf (generator T x)).sub ((hf x).smul ζ)) hl
  have hisub : (∫ t : ℝ in Ioi 0,
      orbit T ζ (generator T x) t - ζ • orbit T ζ (x : X) t) =
      (∫ t : ℝ in Ioi 0, orbit T ζ (generator T x) t) -
        ζ • (∫ t : ℝ in Ioi 0, orbit T ζ (x : X) t) := by
    erw [integral_sub (hf (generator T x)) ((hf x).smul ζ), integral_smul]
  rw [hisub] at hi
  have hzero : orbit T ζ (x : X) 0 = x := by
    simp only [orbit, kernel_zero, Real.toNNReal_zero, T.zero_apply, one_smul]
  rw [hzero, zero_sub] at hi
  simpa only [integralOperator_apply, pow_zero, one_smul, neg_sub, neg_neg] using congrArg Neg.neg hi

/-- Closedness and density extend the resolvent graph identity from D(A) to X. -/
theorem laplace_graph (T : C0Semigroup 𝕜 X) (M ω : ℝ) (ζ : 𝕜)
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (hζ : ω < RCLike.re ζ)
    (x : X) :
    (integralOperator T M ω ζ hT hζ 0 x,
      ζ • integralOperator T M ω ζ hT hζ 0 x - x) ∈ (generator T).graph := by
  let L := integralOperator T M ω ζ hT hζ 0
  let C : Set X := {y | (L y, ζ • L y - y) ∈ (generator T).graph}
  have hc : IsClosed C := T.generator_graph_closed.preimage
    (L.continuous.prodMk ((L.continuous.const_smul ζ).sub continuous_id))
  have hd : Dense ((generator T).domain : Set X) := T.generator_domain_dense
  have hs : ((generator T).domain : Set X) ⊆ C := by
    intro y hy
    have hi := laplace_difference T M ω ζ hT hζ ⟨y, hy⟩
    have heq : L (generator T ⟨y, hy⟩) = ζ • L y - y := by
      change ζ • L y - L (generator T ⟨y, hy⟩) = y at hi
      apply eq_sub_iff_add_eq.mpr
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp hi).symm
    have hg := integralOperator_graph T M ω ζ hT hζ 0 ⟨y, hy⟩
    change (L y, L (generator T ⟨y, hy⟩)) ∈ (generator T).graph at hg
    change (L y, ζ • L y - y) ∈ (generator T).graph
    simpa only [heq] using hg
  have hall := closure_minimal hs hc
  rw [hd.closure_eq] at hall
  exact hall (mem_univ x)

/-- The Laplace transform is a bounded, everywhere defined two-sided inverse,
with values in the full right-derivative domain. -/
def inverse (T : C0Semigroup 𝕜 X) (M ω : ℝ) (ζ : 𝕜)
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (hζ : ω < RCLike.re ζ) :
    Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) ζ where
  inverse := integralOperator T M ω ζ hT hζ 0
  mem_domain x := ((Unbounded.mem_graph_iff (generator T) _).mp
    (laplace_graph T M ω ζ hT hζ x)).choose
  right_inverse x := by
    have hg := ((Unbounded.mem_graph_iff (generator T) _).mp
      (laplace_graph T M ω ζ hT hζ x)).choose_spec
    dsimp only at hg
    erw [hg]
    abel
  left_inverse x := by
    rw [map_sub, map_smul]
    exact laplace_difference T M ω ζ hT hζ x

theorem laplace_inverse : LaplaceResolventSpec.LaplaceInverse (𝕜 := 𝕜) (X := X) := by
  intro T M ω ζ hT hζ
  refine ⟨inverse T M ω ζ hT hζ, fun x => ?_⟩
  simp only [inverse, integralOperator_apply, pow_zero, one_smul]

/-- Differentiating a weighted orbit produces the successive-moment recurrence. -/
theorem hasDerivAt_weighted_orbit (T : C0Semigroup 𝕜 X) (ζ : 𝕜)
    (n : ℕ) (x : (generator T).domain) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => s ^ (n + 1) • orbit T ζ x s)
      (((n + 1 : ℕ) : ℝ) • (t ^ n • orbit T ζ x t) +
        t ^ (n + 1) • orbit T ζ (generator T x) t -
        ζ • (t ^ (n + 1) • orbit T ζ x t)) t := by
  have hd := ((hasDerivAt_id t).pow (n + 1)).smul (hasDerivAt_orbit T ζ x ht)
  convert hd using 1
  · rfl
  · simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, mul_one, mul_smul, smul_sub,
      smul_comm (t ^ (n + 1)) ζ]
    abel

theorem weighted_laplace_difference (T : C0Semigroup 𝕜 X) (M ω : ℝ) (ζ : 𝕜)
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (hζ : ω < RCLike.re ζ)
    (n : ℕ) (x : (generator T).domain) :
    ζ • integralOperator T M ω ζ hT hζ (n + 1) x -
      integralOperator T M ω ζ hT hζ (n + 1) (generator T x) =
        ((n + 1 : ℕ) : ℝ) • integralOperator T M ω ζ hT hζ n x := by
  have hf := weighted_integrability T M ω ζ hT hζ
  have h₁ := (hf n x).smul ((n + 1 : ℕ) : ℝ)
  have h₂ := hf (n + 1) (generator T x)
  have h₃ := (hf (n + 1) x).smul ζ
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto
    (((continuous_id.pow (n + 1)).smul (continuous_orbit T ζ (x : X))).continuousAt.continuousWithinAt)
    (fun t ht => hasDerivAt_weighted_orbit T ζ n x ht)
    ((h₁.add h₂).sub h₃) (weighted_orbit_tendsto_zero T hT ζ hζ (n + 1) x)
  erw [integral_sub (h₁.add h₂) h₃, integral_add h₁ h₂,
    integral_smul (𝕜 := ℝ) ((n + 1 : ℕ) : ℝ), integral_smul ζ] at hi
  simp only [Pi.smul_apply', Pi.pow_apply, id_eq, zero_pow (Nat.succ_ne_zero n), zero_smul, sub_self] at hi
  change ((n + 1 : ℕ) : ℝ) • integralOperator T M ω ζ hT hζ n x +
    integralOperator T M ω ζ hT hζ (n + 1) (generator T x) -
    ζ • integralOperator T M ω ζ hT hζ (n + 1) x = 0 at hi
  apply sub_eq_iff_eq_add.mpr
  exact (sub_eq_zero.mp hi).symm

theorem integralOperator_recurrence (T : C0Semigroup 𝕜 X) (M ω : ℝ) (ζ : 𝕜)
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (hζ : ω < RCLike.re ζ)
    (R : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) ζ)
    (n : ℕ) (x : X) :
    integralOperator T M ω ζ hT hζ (n + 1) x =
      ((n + 1 : ℕ) : ℝ) • R.inverse (integralOperator T M ω ζ hT hζ n x) := by
  let L := integralOperator T M ω ζ hT hζ
  let C : Set X := {y | L (n + 1) y = ((n + 1 : ℕ) : ℝ) • R.inverse (L n y)}
  have hc : IsClosed C := isClosed_eq (L (n + 1)).continuous
    ((R.inverse.continuous.comp (L n).continuous).const_smul ((n + 1 : ℕ) : ℝ))
  have hd : Dense ((generator T).domain : Set X) := T.generator_domain_dense
  have hs : ((generator T).domain : Set X) ⊆ C := by
    intro y hy
    obtain ⟨hz, hAz⟩ := (Unbounded.mem_graph_iff (generator T) _).mp
      (integralOperator_graph T M ω ζ hT hζ (n + 1) ⟨y, hy⟩)
    have hr := R.left_inverse ⟨L (n + 1) y, hz⟩
    erw [hAz, weighted_laplace_difference T M ω ζ hT hζ n ⟨y, hy⟩,
      ContinuousLinearMap.map_smul_of_tower] at hr
    exact hr.symm
  have hall := closure_minimal hs hc
  rw [hd.closure_eq] at hall
  exact hall (mem_univ x)

theorem moment_recurrence (T : C0Semigroup 𝕜 X) (M ω : ℝ) (ζ : 𝕜)
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (hζ : ω < RCLike.re ζ)
    (R : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) ζ)
    (n : ℕ) (x : X) : moment T ζ (n + 1) x = R.inverse (moment T ζ n x) := by
  change ((n + 1).factorial : ℝ)⁻¹ • integralOperator T M ω ζ hT hζ (n + 1) x =
    R.inverse ((n.factorial : ℝ)⁻¹ • integralOperator T M ω ζ hT hζ n x)
  rw [integralOperator_recurrence T M ω ζ hT hζ R n x,
    ContinuousLinearMap.map_smul_of_tower, smul_smul]
  congr 1
  simp only [Nat.factorial_succ, Nat.cast_mul]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Every bounded two-sided resolvent has all the stated moment formulas. -/
theorem resolvent_power_formula (T : C0Semigroup 𝕜 X) (M ω : ℝ) (ζ : 𝕜)
    (hT : C0SemigroupSpec.exponentialBoundValue T M ω) (hζ : ω < RCLike.re ζ)
    (R : Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) ζ)
    (n : ℕ) (x : X) : (R.inverse ^ (n + 1)) x = moment T ζ n x := by
  induction n with
  | zero =>
    have hu := Unbounded.resolvent_inverse_unique ζ (C0SemigroupSpec.generatorValue T)
      R (inverse T M ω ζ hT hζ)
    rw [pow_one, hu]
    simp only [inverse, integralOperator_apply, moment, pow_zero, one_smul,
      Nat.factorial_zero, Nat.cast_one, inv_one]
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, moment_recurrence T M ω ζ hT hζ R n x]

theorem resolvent_powers : LaplaceResolventSpec.ResolventPowers (𝕜 := 𝕜) (X := X) := by
  intro T M ω ζ hT hζ R n
  refine ⟨resolvent_power_formula T M ω ζ hT hζ R n, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (le_trans zero_le_one hT.1)
    (pow_nonneg (sub_pos.mpr hζ).le _))
  intro x
  rw [resolvent_power_formula T M ω ζ hT hζ R n x]
  exact moment_bound T M ω ζ hT hζ n x

theorem canonical_resolvent : LaplaceResolventSpec.CanonicalResolvent (𝕜 := 𝕜) (X := X) := by
  intro T M ω ζ hT hζ
  have h : Nonempty (Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue T) ζ) :=
    ⟨inverse T M ω ζ hT hζ⟩
  refine ⟨h, ?_, ?_⟩
  · intro x
    have hu := Unbounded.resolvent_inverse_unique ζ (C0SemigroupSpec.generatorValue T)
      h.some (inverse T M ω ζ hT hζ)
    simp only [Unbounded.OperatorDomainsSpec.resolventValue, dite_eq_left h, hu,
      inverse, integralOperator_apply, pow_zero, one_smul]
  · simpa only [Unbounded.OperatorDomainsSpec.resolventValue, dite_eq_left h] using
      resolvent_powers T M ω ζ hT hζ h.some

end ExpandedFA.Semigroups.LaplaceResolvent
