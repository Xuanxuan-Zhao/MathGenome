import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Ergodic.ContinuousMeanErgodic
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Ergodic.DiscreteMeanErgodic
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerIntegral
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
Continuous-time part of the mean ergodic theorem (paper.tex:12556–12574).
The averages are defined vectorwise, then shown to be scalar-linear contractions.
Their values on y - T(s)y are differences of endpoint integrals and have norm
at most 2s‖y‖/t. The subspace on which the averages vanish is closed by
uniform contractivity. Its orthogonal complement consists of common fixed
vectors, so every vector splits into a fixed vector and a vanishing vector.
The discrete clause is reused from the accepted discrete mean ergodic theorem.
-/
noncomputable section
open Filter MeasureTheory
open scoped NNReal Topology InnerProductSpace
namespace ExpandedFA.Ergodic.ContinuousMeanErgodic
open Spec
universe u v

theorem discrete_strong_convergence : Spec.DiscreteStrongConvergence.{u,v} :=
  DiscreteMeanErgodic.strong_convergence

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma orbit_continuous (S : ContractionSemigroup 𝕜 H) (x : H) :
    Continuous (orbit S x) := (S.continuous x).comp continuous_real_toNNReal

omit [CompleteSpace H] in
lemma orbit_norm_le (S : ContractionSemigroup 𝕜 H) (x : H) (s : ℝ) :
    ‖orbit S x s‖ ≤ ‖x‖ := by
  simpa only [orbit, one_mul] using (S.op (Real.toNNReal s)).le_of_opNorm_le (S.norm_le _) x

theorem orbit_integrable : Spec.OrbitIntegrable.{u,v} := by
  intro 𝕜 H _ _ _ _ S x a b
  exact (orbit_continuous S x).intervalIntegrable a b

theorem average_contraction : Spec.AverageContraction.{u,v} := by
  intro 𝕜 H _ _ _ _ S t x
  let : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ 𝕜 H
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := (t:ℝ)) (fun s _ => orbit_norm_le S x s)
  rw [sub_zero, abs_of_nonneg t.coe_nonneg] at h
  dsimp [average]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg t.coe_nonneg]
  by_cases ht : t = 0
  · simp [ht]
  · have ht' : (t:ℝ) ≠ 0 := by exact_mod_cast ht
    calc
      (t:ℝ)⁻¹ * ‖∫ s in (0:ℝ)..(t:ℝ), orbit S x s‖ ≤
          (t:ℝ)⁻¹ * (‖x‖ * (t:ℝ)) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr t.coe_nonneg)
      _ = ‖x‖ := by field_simp

local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ 𝕜 H
local instance : IsScalarTower ℝ 𝕜 H := IsScalarTower.restrictScalars ℝ 𝕜 H

omit [CompleteSpace H] in
lemma orbit_add (S : ContractionSemigroup 𝕜 H) (x y : H) (s : ℝ) :
    orbit S (x + y) s = orbit S x s + orbit S y s := by simp [orbit]

omit [CompleteSpace H] in
lemma orbit_sub (S : ContractionSemigroup 𝕜 H) (x y : H) (s : ℝ) :
    orbit S (x - y) s = orbit S x s - orbit S y s := by simp [orbit]

lemma average_add (S : ContractionSemigroup 𝕜 H) (t : ℝ≥0) (x y : H) :
    average S t (x + y) = average S t x + average S t y := by
  simp only [average, orbit_add]
  rw [intervalIntegral.integral_add (orbit_integrable 𝕜 H S x 0 t)
    (orbit_integrable 𝕜 H S y 0 t), smul_add]

lemma average_smul (S : ContractionSemigroup 𝕜 H) (t : ℝ≥0) (c : 𝕜) (x : H) :
    average S t (c • x) = c • average S t x := by
  simp only [average, orbit, map_smul]
  rw [intervalIntegral.integral_smul, smul_comm]

/-- The vectorwise integral defines a bounded scalar-linear operator. -/
def averageCLM (S : ContractionSemigroup 𝕜 H) (t : ℝ≥0) : H →L[𝕜] H :=
  LinearMap.mkContinuous
    { toFun := average S t
      map_add' := average_add S t
      map_smul' := average_smul S t }
    1 (fun x => by simpa using average_contraction 𝕜 H S t x)

@[simp] lemma averageCLM_apply (S : ContractionSemigroup 𝕜 H) (t : ℝ≥0) (x : H) :
    averageCLM S t x = average S t x := rfl

lemma averageCLM_norm_le (S : ContractionSemigroup 𝕜 H) (t : ℝ≥0) :
    ‖averageCLM S t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by simpa using average_contraction 𝕜 H S t x)

theorem average_operator : Spec.AverageOperator.{u,v} := by
  intro 𝕜 H _ _ _ _ S t
  exact ⟨averageCLM S t, averageCLM_norm_le S t, fun _ => rfl⟩

omit [CompleteSpace H] in
lemma mem_fixedSpace (S : ContractionSemigroup 𝕜 H) (x : H) :
    x ∈ fixedSpace S ↔ ∀ s, S.op s x = x := by
  simp only [fixedSpace, ClosedSubmodule.mem_iInf]
  change (∀ s, x - S.op s x = 0) ↔ _
  simp only [sub_eq_zero]
  exact forall_congr' (fun s => eq_comm)

theorem fixed_space_identification : Spec.FixedSpaceIdentification.{u,v} := by
  intro 𝕜 H _ _ _ S x
  exact mem_fixedSpace S x

lemma average_fixed (S : ContractionSemigroup 𝕜 H) {x : H}
    (hx : x ∈ fixedSpace S) {t : ℝ≥0} (ht : t ≠ 0) : average S t x = x := by
  have hx' := (mem_fixedSpace S x).mp hx
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  simp only [average, orbit, hx', intervalIntegral.integral_const, sub_zero,
    smul_smul, inv_mul_cancel₀ ht', one_smul]

omit [CompleteSpace H] in
lemma orbit_shift (S : ContractionSemigroup 𝕜 H) (s : ℝ≥0) (y : H)
    {u : ℝ} (hu : 0 ≤ u) : orbit S (S.op s y) u = orbit S y (u + s) := by
  simp only [orbit, Real.toNNReal_add hu s.coe_nonneg, Real.toNNReal_coe,
    S.add, ContinuousLinearMap.comp_apply]

lemma average_coboundary (S : ContractionSemigroup 𝕜 H) (t s : ℝ≥0) (y : H) :
    average S t (y - S.op s y) = (t:ℝ)⁻¹ •
      ((∫ u in (0:ℝ)..(s:ℝ), orbit S y u) -
        ∫ u in (t:ℝ)..((t:ℝ) + s), orbit S y u) := by
  have hshift : (∫ u in (0:ℝ)..(t:ℝ), orbit S (S.op s y) u) =
      ∫ u in (s:ℝ)..((t:ℝ) + s), orbit S y u := by
    calc
      _ = ∫ u in (0:ℝ)..(t:ℝ), orbit S y (u + s) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le t.coe_nonneg] at hu
        exact orbit_shift S s y hu.1
      _ = _ := by rw [intervalIntegral.integral_comp_add_right, zero_add]
  have h₁ := intervalIntegral.integral_add_adjacent_intervals
    (orbit_integrable 𝕜 H S y 0 t) (orbit_integrable 𝕜 H S y t ((t:ℝ)+s))
  have h₂ := intervalIntegral.integral_add_adjacent_intervals
    (orbit_integrable 𝕜 H S y 0 s) (orbit_integrable 𝕜 H S y s ((t:ℝ)+s))
  simp only [average, orbit_sub]
  rw [intervalIntegral.integral_sub (orbit_integrable 𝕜 H S y 0 t)
    (orbit_integrable 𝕜 H S (S.op s y) 0 t)]
  change (t:ℝ)⁻¹ • ((∫ u in (0:ℝ)..(t:ℝ), orbit S y u) -
    ∫ u in (0:ℝ)..(t:ℝ), orbit S (S.op s y) u) = _
  rw [hshift]
  congr 1
  have h := h₁.trans h₂.symm
  exact sub_eq_sub_iff_add_eq_add.mpr h

/-- Endpoint cancellation gives decay of every semigroup coboundary. -/
lemma norm_average_coboundary_le (S : ContractionSemigroup 𝕜 H)
    (t s : ℝ≥0) (y : H) :
    ‖average S t (y - S.op s y)‖ ≤ (t:ℝ)⁻¹ * (2 * (s:ℝ) * ‖y‖) := by
  rw [average_coboundary, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg t.coe_nonneg]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr t.coe_nonneg)
  have h₁ := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := (s:ℝ)) (fun u _ => orbit_norm_le S y u)
  have h₂ := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (t:ℝ)) (b := (t:ℝ)+s) (fun u _ => orbit_norm_le S y u)
  rw [sub_zero, abs_of_nonneg s.coe_nonneg] at h₁
  rw [add_sub_cancel_left, abs_of_nonneg s.coe_nonneg] at h₂
  calc
    _ ≤ ‖∫ u in (0:ℝ)..(s:ℝ), orbit S y u‖ +
        ‖∫ u in (t:ℝ)..((t:ℝ)+s), orbit S y u‖ := norm_sub_le _ _
    _ ≤ ‖y‖ * (s:ℝ) + ‖y‖ * (s:ℝ) := add_le_add h₁ h₂
    _ = _ := by ring

lemma tendsto_average_coboundary (S : ContractionSemigroup 𝕜 H) (s : ℝ≥0) (y : H) :
    Tendsto (fun t : ℝ≥0 => average S t (y - S.op s y)) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ≥0 => (t:ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hi : Tendsto (fun t : ℝ≥0 => (t:ℝ)⁻¹ * (2 * (s:ℝ) * ‖y‖))
      atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp ht).mul_const (2 * (s:ℝ) * ‖y‖)
  exact squeeze_zero_norm (fun t => norm_average_coboundary_le S t s y) hi

/-- The vectors whose averages tend to zero form a linear subspace. -/
def vanishingSubmodule (S : ContractionSemigroup 𝕜 H) : Submodule 𝕜 H where
  carrier := {x | Tendsto (fun t : ℝ≥0 => averageCLM S t x) atTop (𝓝 0)}
  zero_mem' := by
    change Tendsto (fun t : ℝ≥0 => averageCLM S t 0) atTop (𝓝 0)
    simpa only [map_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => (0 : H)) atTop (𝓝 0))
  add_mem' := by
    intro x y hx hy
    simpa only [Set.mem_ofPred_eq, map_add, zero_add] using hx.add hy
  smul_mem' := by
    intro c x hx
    simpa only [Set.mem_ofPred_eq, map_smul, smul_zero] using hx.const_smul c

lemma vanishingSubmodule_isClosed (S : ContractionSemigroup 𝕜 H) :
    IsClosed (vanishingSubmodule S : Set H) := by
  have hLip : ∀ t : ℝ≥0, LipschitzWith 1 (averageCLM S t) := by
    intro t
    apply (averageCLM S t).lipschitzWith.weaken
    exact_mod_cast averageCLM_norm_le S t
  have heq : Equicontinuous (fun t : ℝ≥0 => (averageCLM S t : H → H)) :=
    (LipschitzWith.uniformEquicontinuous _ 1 hLip).equicontinuous
  exact heq.isClosed_setOfPred_tendsto continuous_const

/-- Uniform contractivity extends decay to the closure of the coboundary span. -/
def vanishingSpace (S : ContractionSemigroup 𝕜 H) : ClosedSubmodule 𝕜 H :=
  ⟨vanishingSubmodule S, vanishingSubmodule_isClosed S⟩

lemma coboundary_mem_vanishingSpace (S : ContractionSemigroup 𝕜 H) (s : ℝ≥0) (y : H) :
    y - S.op s y ∈ vanishingSpace S := tendsto_average_coboundary S s y

lemma orthogonal_vanishingSpace_le_fixedSpace (S : ContractionSemigroup 𝕜 H) :
    (vanishingSpace S).toSubmodule.orthogonal ≤ (fixedSpace S).toSubmodule := by
  intro x hx
  apply (mem_fixedSpace S x).mpr
  intro s
  have hi := (Submodule.mem_orthogonal (vanishingSpace S).toSubmodule x).mp hx
    (x - S.op s x) (coboundary_mem_vanishingSpace S s x)
  rw [inner_sub_left, sub_eq_zero] at hi
  apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := 𝕜)
  · simpa only [one_mul] using (S.op s).le_of_opNorm_le (S.norm_le s) x
  · rw [← hi]
    simp

lemma orthogonal_fixedSpace_le_vanishingSpace (S : ContractionSemigroup 𝕜 H) :
    (fixedSpace S).toSubmodule.orthogonal ≤ (vanishingSpace S).toSubmodule := by
  have h := Submodule.orthogonal_le (orthogonal_vanishingSpace_le_fixedSpace S)
  simpa only [Submodule.orthogonal_orthogonal] using h

/-- The continuous mean ergodic theorem, with the original common fixed space. -/
theorem strong_convergence : Spec.StrongConvergence.{u,v} := by
  intro 𝕜 H _ _ _ _ S x
  let F := (fixedSpace S).toSubmodule
  have hz : Tendsto (fun t : ℝ≥0 => average S t (x - F.starProjection x))
      atTop (𝓝 0) :=
    orthogonal_fixedSpace_le_vanishingSpace S
      (Submodule.sub_starProjection_mem_orthogonal (K := F) x)
  have hp : Tendsto (fun t : ℝ≥0 => average S t (F.starProjection x))
      atTop (𝓝 (F.starProjection x)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    exact (average_fixed S (F.starProjection_apply_mem x) (ne_of_gt ht)).symm
  have h := hz.add hp
  simpa only [zero_add, ← average_add, sub_add_cancel] using h

end ExpandedFA.Ergodic.ContinuousMeanErgodic
