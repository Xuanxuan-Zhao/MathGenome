import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.DirichletModel
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.SlabPoincare
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped InnerProductSpace NNReal
set_option maxHeartbeats 600000

namespace VariationalNotes.Sobolev.Dirichlet

variable {d : ℕ} (Ω : Opens (Domain d))

private theorem two_exponent : Exponent.two.ennreal = 2 := by
  norm_num [Exponent.two, Exponent.ennreal]

/-- The genuine L² gradient, with only the exponent's spelling changed. -/
def gradientL2 : H1 Ω 1 →L[ℝ] Lp (Gradient 1 d) 2 (domainMeasure Ω) :=
  (lpExponentEquiv (domainMeasure Ω) two_exponent).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (gradient Ω 1 Exponent.two)

/-- The scalar value of the single-coordinate target. -/
def valueL2 : H1 Ω 1 →L[ℝ] Source Ω :=
  (lpExponentEquiv (domainMeasure Ω) two_exponent).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((coordinateLp Ω Exponent.two (0 : Fin 1)).comp (value Ω 1 Exponent.two))

theorem gradientL2_coe (u : H1 Ω 1) :
    (gradientL2 Ω u : Domain d → Gradient 1 d) = gradient Ω 1 Exponent.two u :=
  lpExponentEquiv_coe (domainMeasure Ω) two_exponent _

theorem gradientL2_norm (u : H1 Ω 1) :
    ‖gradientL2 Ω u‖ = ‖gradient Ω 1 Exponent.two u‖ :=
  (lpExponentEquiv (domainMeasure Ω) two_exponent).norm_map _

theorem valueL2_ae (u : H1 Ω 1) :
    (valueL2 Ω u : Domain d → ℝ) =ᵐ[domainMeasure Ω]
      fun x => value Ω 1 Exponent.two u x 0 := by
  change (lpExponentEquiv (domainMeasure Ω) two_exponent
    (coordinateLp Ω Exponent.two (0 : Fin 1) (value Ω 1 Exponent.two u)) : Domain d → ℝ) =ᵐ[_] _
  rw [lpExponentEquiv_coe]
  exact coordinateLp_ae Ω Exponent.two 0 _

theorem valueL2_norm_le (u : H1 Ω 1) :
    ‖valueL2 Ω u‖ ≤ ‖value Ω 1 Exponent.two u‖ := by
  change ‖lpExponentEquiv (domainMeasure Ω) two_exponent
    (coordinateLp Ω Exponent.two (0 : Fin 1) (value Ω 1 Exponent.two u))‖ ≤ _
  rw [(lpExponentEquiv (domainMeasure Ω) two_exponent).norm_map]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coordinateLp_ae Ω Exponent.two (0 : Fin 1)
    (value Ω 1 Exponent.two u)] with x hx
  rw [hx]
  exact PiLp.norm_apply_le _ _

theorem gradient_pairing (u v : H1 Ω 1) :
    ⟪gradientL2 Ω u, gradientL2 Ω v⟫_ℝ =
      ∫ x, frobenius (gradient Ω 1 Exponent.two u x)
        (gradient Ω 1 Exponent.two v x) ∂domainMeasure Ω := by
  rw [L2.inner_def, gradientL2_coe, gradientL2_coe]
  rfl

theorem source_pairing (b : Source Ω) (u : H1 Ω 1) :
    ⟪b, valueL2 Ω u⟫_ℝ =
      ∫ x, b x * value Ω 1 Exponent.two u x 0 ∂domainMeasure Ω := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [valueL2_ae Ω u] with x hx
  simp [hx, mul_comm]

/-- Both terms of the real energy are integrable for every H¹ class and
every L² source; the real-valued energy uses ordinary finite integrals. -/
theorem energy_integrable (b : Source Ω) (u : H1 Ω 1) :
    Integrable (fun x => ‖gradient Ω 1 Exponent.two u x‖ ^ 2) (domainMeasure Ω) ∧
      Integrable (fun x => b x * value Ω 1 Exponent.two u x 0) (domainMeasure Ω) := by
  constructor
  · have h := L2.integrable_inner (𝕜 := ℝ) (gradientL2 Ω u) (gradientL2 Ω u)
    simpa only [gradientL2_coe, real_inner_self_eq_norm_sq] using h
  · apply (L2.integrable_inner (𝕜 := ℝ) b (valueL2 Ω u)).congr
    filter_upwards [valueL2_ae Ω u] with x hx
    simp [hx, mul_comm]

theorem energy_eq (b : Source Ω) (u : H1 Ω 1) :
    energy Ω b u = ‖gradientL2 Ω u‖ ^ 2 / 2 - ⟪b, valueL2 Ω u⟫_ℝ := by
  rw [source_pairing]
  have h : (∫ x, ‖gradient Ω 1 Exponent.two u x‖ ^ 2 ∂domainMeasure Ω) =
      ‖gradientL2 Ω u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, gradientL2_coe]
    simp only [real_inner_self_eq_norm_sq]
  simp only [energy, h]
  ring

theorem stationary_iff (b : Source Ω) (u : H1 Ω 1) :
    Stationary Ω b u ↔ ∀ φ : H1Zero Ω 1,
      ⟪gradientL2 Ω u, gradientL2 Ω φ.val⟫_ℝ = ⟪b, valueL2 Ω φ.val⟫_ℝ := by
  simp only [Stationary, gradient_pairing, source_pairing]

/-- Riesz representation on a closed linear range. Only the range needs a
normed structure; the functional bound is stated in terms of its image. -/
theorem exists_gradient_representative {E F : Type*} [AddCommGroup E]
    [Module ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (D : E →ₗ[ℝ] F) (hinj : Function.Injective D)
    (hc : IsClosed (D.range : Set F)) (L : E →ₗ[ℝ] ℝ) (C : ℝ)
    (hL : ∀ v, ‖L v‖ ≤ C * ‖D v‖) :
    ∃ v : E, ∀ w : E, ⟪D v, D w⟫_ℝ = L w := by
  have : CompleteSpace D.range := hc.completeSpace_coe
  let e := LinearEquiv.ofInjective D hinj
  have he (z : D.range) : D (e.symm z) = (z : F) :=
    congrArg Subtype.val (e.apply_symm_apply z)
  let ℓ : D.range →L[ℝ] ℝ :=
    (L.comp e.symm.toLinearMap).mkContinuous C (fun z => by
      change ‖L (e.symm z)‖ ≤ C * ‖z‖
      simpa only [he, Submodule.norm_coe] using hL (e.symm z))
  let z : D.range := (InnerProductSpace.toDual ℝ D.range).symm ℓ
  refine ⟨e.symm z, fun w => ?_⟩
  have hz := InnerProductSpace.toDual_symm_apply (x := e w) (y := ℓ)
  change ⟪(z : F), (e w : F)⟫_ℝ = ℓ (e w) at hz
  have hwe : (e w : F) = D w := rfl
  have hℓ : ℓ (e w) = L w := by
    change L (e.symm (e w)) = L w
    rw [e.symm_apply_apply]
  rw [← he z, hwe, hℓ] at hz
  exact hz

/-- The exact quadratic expansion, with no differentiability assumption. -/
theorem energy_add (b : Source Ω) (u v : H1 Ω 1) :
    energy Ω b (u + v) - energy Ω b u =
      ⟪gradientL2 Ω u, gradientL2 Ω v⟫_ℝ - ⟪b, valueL2 Ω v⟫_ℝ +
        ‖gradientL2 Ω v‖ ^ 2 / 2 := by
  simp only [energy_eq, map_add, norm_add_sq_real, inner_add_right]
  ring

theorem energy_difference : Expected.EnergyDifference := by
  intro d Ω b u hu φ
  rw [energy_add, (stationary_iff Ω b u).mp hu φ, sub_self, zero_add,
    gradientL2_norm]

theorem stationary_minimizer (u₀ u : H1 Ω 1) (b : Source Ω)
    (hu : u - u₀ ∈ zeroSubmodule Ω 1 Exponent.two) (hs : Stationary Ω b u) :
    Minimizer Ω u₀ b u := by
  refine ⟨hu, fun v hv => ?_⟩
  have hφ : v - u ∈ zeroSubmodule Ω 1 Exponent.two := by
    have h := (zeroSubmodule Ω 1 Exponent.two).sub_mem hv hu
    convert h using 1; abel
  let φ : H1Zero Ω 1 := ⟨v - u, hφ⟩
  have he := energy_difference Ω b u hs φ
  have heq : u + φ.val = v := by dsimp [φ]; abel
  rw [heq] at he
  nlinarith [sq_nonneg ‖gradient Ω 1 Exponent.two φ.val‖]


def zeroGradientL2 : H1Zero Ω 1 →L[ℝ] Lp (Gradient 1 d) 2 (domainMeasure Ω) :=
  (gradientL2 Ω).comp (zeroSubmodule Ω 1 Exponent.two).subtypeL

def zeroValueL2 : H1Zero Ω 1 →L[ℝ] Source Ω :=
  (valueL2 Ω).comp (zeroSubmodule Ω 1 Exponent.two).subtypeL

def loadL2 (u₀ : H1 Ω 1) (b : Source Ω) : H1Zero Ω 1 →L[ℝ] ℝ :=
  ((innerSL ℝ b).comp (zeroValueL2 Ω)) -
    ((innerSL ℝ (gradientL2 Ω u₀)).comp (zeroGradientL2 Ω))

theorem zeroGradientL2_lower (j : Fin d) {a c : ℝ} (hac : a < c)
    (hΩ : InCoordinateStrip Ω j a c) :
    AntilipschitzWith ⟨c-a+1, by linarith⟩ (zeroGradientL2 Ω) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro v w
  rw [dist_eq_norm, dist_eq_norm, ← (zeroGradientL2 Ω).map_sub]
  change ‖v-w‖ ≤ (c-a+1) * ‖gradientL2 Ω (v-w).val‖
  rw [gradientL2_norm]
  exact (slab_norm_equivalence Ω Exponent.two j a c hac hΩ (v-w)).2

theorem zeroGradientL2_closed (j : Fin d) {a c : ℝ} (hac : a < c)
    (hΩ : InCoordinateStrip Ω j a c) :
    IsClosed ((zeroGradientL2 Ω).toLinearMap.range : Set (Lp (Gradient 1 d) 2 (domainMeasure Ω))) := by
  have : CompleteSpace (H1Zero Ω 1) :=
    (smoothSubmodule Ω 1 Exponent.two).isClosed_topologicalClosure.completeSpace_coe
  exact (zeroGradientL2_lower Ω j hac hΩ).isClosed_range (zeroGradientL2 Ω).uniformContinuous

theorem zeroValueL2_bound (j : Fin d) {a c : ℝ} (hac : a < c)
    (hΩ : InCoordinateStrip Ω j a c) (v : H1Zero Ω 1) :
    ‖zeroValueL2 Ω v‖ ≤ (c-a) * ‖zeroGradientL2 Ω v‖ := by
  change ‖valueL2 Ω v.val‖ ≤ (c-a) * ‖gradientL2 Ω v.val‖
  rw [gradientL2_norm]
  exact (valueL2_norm_le Ω v.val).trans (slab_gradient_control Ω Exponent.two j a c hac hΩ v)

theorem loadL2_bound (j : Fin d) {a c : ℝ} (hac : a < c)
    (hΩ : InCoordinateStrip Ω j a c) (u₀ : H1 Ω 1) (b : Source Ω) (v : H1Zero Ω 1) :
    ‖loadL2 Ω u₀ b v‖ ≤ (‖b‖*(c-a)+‖gradientL2 Ω u₀‖) * ‖zeroGradientL2 Ω v‖ := by
  change ‖⟪b, zeroValueL2 Ω v⟫_ℝ - ⟪gradientL2 Ω u₀, zeroGradientL2 Ω v⟫_ℝ‖ ≤ _
  calc
    _ ≤ ‖⟪b, zeroValueL2 Ω v⟫_ℝ‖ + ‖⟪gradientL2 Ω u₀, zeroGradientL2 Ω v⟫_ℝ‖ := norm_sub_le _ _
    _ ≤ ‖b‖ * ‖zeroValueL2 Ω v‖ + ‖gradientL2 Ω u₀‖ * ‖zeroGradientL2 Ω v‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (zeroValueL2_bound Ω j hac hΩ v) (norm_nonneg b)]

theorem exists_zeroGradientL2_representative (j : Fin d) {a c : ℝ} (hac : a < c)
    (hΩ : InCoordinateStrip Ω j a c) (u₀ : H1 Ω 1) (b : Source Ω) :
    ∃ v : H1Zero Ω 1, ∀ φ : H1Zero Ω 1,
      ⟪zeroGradientL2 Ω v, zeroGradientL2 Ω φ⟫_ℝ = loadL2 Ω u₀ b φ := by
  exact exists_gradient_representative (zeroGradientL2 Ω).toLinearMap
    (zeroGradientL2_lower Ω j hac hΩ).injective (zeroGradientL2_closed Ω j hac hΩ)
    (loadL2 Ω u₀ b).toLinearMap (‖b‖*(c-a)+‖gradientL2 Ω u₀‖)
    (loadL2_bound Ω j hac hΩ u₀ b)

/-- The algebraic step for adding nonhomogeneous data to a represented load. -/
theorem inner_map_add_eq {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
    (D : E →ₗ[ℝ] F) (u v w : E) (r : ℝ)
    (h : ⟪D v, D w⟫_ℝ = r - ⟪D u, D w⟫_ℝ) :
    ⟪D (u+v), D w⟫_ℝ = r := by
  rw [map_add, inner_add_left]
  exact (add_comm _ _).trans (eq_sub_iff_add_eq.mp h)

theorem submodule_translate_mem {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S : Submodule ℝ E) (u : E) (v : S) : u+v.val-u ∈ S := by
  simpa only [add_sub_cancel_left] using v.property

theorem perturbation_mem_affine {m : ℕ} (p : Exponent)
    (u₀ : W1p Ω m p) (v : W1pZero Ω m p) :
    u₀ + v.val - u₀ ∈ zeroSubmodule Ω m p :=
  submodule_translate_mem (zeroSubmodule Ω m p) u₀ v

theorem stationary_of_representative (u₀ : H1 Ω 1) (b : Source Ω) (v : H1Zero Ω 1)
    (hv : ∀ φ : H1Zero Ω 1,
      ⟪zeroGradientL2 Ω v, zeroGradientL2 Ω φ⟫_ℝ = loadL2 Ω u₀ b φ) :
    Stationary Ω b (u₀ + v.val) := by
  apply (stationary_iff Ω b (u₀ + v.val)).mpr
  intro φ
  have h := hv φ
  change ⟪gradientL2 Ω v.val, gradientL2 Ω φ.val⟫_ℝ =
    ⟪b, valueL2 Ω φ.val⟫_ℝ - ⟪gradientL2 Ω u₀, gradientL2 Ω φ.val⟫_ℝ at h
  exact inner_map_add_eq (gradientL2 Ω).toLinearMap u₀ v.val φ.val
    ⟪b, valueL2 Ω φ.val⟫_ℝ h

theorem exists_stationary_in_strip (j : Fin d) {a c : ℝ} (hac : a < c)
    (hΩ : InCoordinateStrip Ω j a c) (u₀ : H1 Ω 1) (b : Source Ω) :
    ∃ u, u - u₀ ∈ zeroSubmodule Ω 1 Exponent.two ∧ Stationary Ω b u := by
  obtain ⟨v, hv⟩ := exists_zeroGradientL2_representative Ω j hac hΩ u₀ b
  exact ⟨u₀ + v.val, perturbation_mem_affine Ω Exponent.two u₀ v,
    stationary_of_representative Ω u₀ b v hv⟩

theorem bounded_domain_in_strip (hd : 0 < d)
    (hΩ : Bornology.IsBounded (Ω : Set (Domain d))) :
    ∃ (j : Fin d) (a c : ℝ), a < c ∧ InCoordinateStrip Ω j a c := by
  obtain ⟨R, hR, hball⟩ := hΩ.subset_ball_lt 0 (0 : Domain d)
  let j : Fin d := ⟨0, hd⟩
  refine ⟨j, -R, R, by linarith, fun x hx => ?_⟩
  have hn : ‖x‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hball hx
  exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using
    (PiLp.norm_apply_le x j).trans_lt hn)

/-- Poincaré turns equality of energies with a stationary competitor into
equality of the Sobolev classes, including nonhomogeneous boundary data. -/
theorem minimizer_eq_stationary_in_strip (j : Fin d) {a c : ℝ} (hac : a < c)
    (hΩ : InCoordinateStrip Ω j a c) (u₀ : H1 Ω 1) (b : Source Ω)
    (u v : H1 Ω 1) (hu : u - u₀ ∈ zeroSubmodule Ω 1 Exponent.two)
    (hs : Stationary Ω b u) (hv : Minimizer Ω u₀ b v) : v = u := by
  have hφ : v - u ∈ zeroSubmodule Ω 1 Exponent.two := by
    have h := (zeroSubmodule Ω 1 Exponent.two).sub_mem hv.1 hu
    convert h using 1; abel
  let φ : H1Zero Ω 1 := ⟨v-u, hφ⟩
  have he := energy_difference Ω b u hs φ
  have heq : u + φ.val = v := by dsimp [φ]; abel
  rw [heq] at he
  have hmin := hv.2 u hu
  have hn : ‖gradient Ω 1 Exponent.two φ.val‖ = 0 := by
    nlinarith [sq_nonneg ‖gradient Ω 1 Exponent.two φ.val‖,
      norm_nonneg (gradient Ω 1 Exponent.two φ.val)]
  have hz := zero_of_gradient_eq_zero Ω Exponent.two j hac hΩ φ (norm_eq_zero.mp hn)
  have hz' : v-u = 0 := congrArg Subtype.val hz
  exact sub_eq_zero.mp hz'

theorem existence_unique : Expected.ExistenceUnique := by
  intro d Ω hd hΩ u₀ b
  obtain ⟨j, a, c, hac, hstrip⟩ := bounded_domain_in_strip Ω hd hΩ
  obtain ⟨u, hu, hs⟩ := exists_stationary_in_strip Ω j hac hstrip u₀ b
  refine ⟨u, stationary_minimizer Ω u₀ u b hu hs, ?_⟩
  intro v hv
  exact minimizer_eq_stationary_in_strip Ω j hac hstrip u₀ b u v hu hs hv

theorem characterization : Expected.Characterization := by
  intro d Ω hd hΩ u₀ b u hu
  refine ⟨?_, stationary_minimizer Ω u₀ u b hu⟩
  intro hmin
  obtain ⟨j, a, c, hac, hstrip⟩ := bounded_domain_in_strip Ω hd hΩ
  obtain ⟨v, hv, hs⟩ := exists_stationary_in_strip Ω j hac hstrip u₀ b
  have he := minimizer_eq_stationary_in_strip Ω j hac hstrip u₀ b v u hv hs hmin
  simpa only [he] using hs

theorem weak_dirichlet_principle : Expected.WeakDirichletPrinciple := by
  intro d Ω hd hΩ u₀
  refine ⟨existence_unique Ω hd hΩ u₀ 0, fun u hu => ?_⟩
  simpa only [Stationary, ← source_pairing, inner_zero_left] using
    characterization Ω hd hΩ u₀ 0 u hu

end VariationalNotes.Sobolev.Dirichlet
