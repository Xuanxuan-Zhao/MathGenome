import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Flux.ObstacleDistribution
import MathGenome.Internal.VariationalMethods.VariationalNotes.Flux.ObstacleMinimizer
import MathGenome.Internal.VariationalMethods.VariationalNotes.Flux.WeakDivergence
import Mathlib.Topology.Order.Compact

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory TopologicalSpace Set Filter
open scoped InnerProductSpace
namespace VariationalNotes.Flux
open Sobolev

variable {d : ℕ} (Ω : Opens (Domain d))

/-- The actual scalar value of the Sobolev class of a smooth test. -/
theorem scalarValue_test_ae (φ : P102.U4.TestSpace ℝ Ω) (v : H1Zero Ω 1)
    (hv : WeakDivergenceSpec.IsTestClass Ω Exponent.two φ v) :
    (scalarValue Ω v : Domain d → ℝ) =ᵐ[domainMeasure Ω] φ := by
  change (coordinateLp Ω Exponent.two 0 (value Ω 1 Exponent.two v.val) :
    Domain d → ℝ) =ᵐ[domainMeasure Ω] φ
  rw [hv]
  exact P102.U4.testToDomainLp_ae Ω Exponent.two.ennreal φ

/-- Only homogeneity of the Dirichlet pairing is needed for signed variations. -/
theorem dirichletPairing_smul_right (u v : H1Zero Ω 1) (c : ℝ) :
    dirichletPairing Ω u (c • v) = c * dirichletPairing Ω u v := by
  unfold dirichletPairing
  have h : gradient Ω 1 Exponent.two (c • v).val =
      c • gradient Ω 1 Exponent.two v.val := by
    change gradient Ω 1 Exponent.two (c • v.val) = _
    exact map_smul _ _ _
  rw [h]
  calc
    (∫ x, Sobolev.frobenius (gradient Ω 1 Exponent.two u.val x)
        ((c • gradient Ω 1 Exponent.two v.val) x) ∂domainMeasure Ω) =
      ∫ x, c * Sobolev.frobenius (gradient Ω 1 Exponent.two u.val x)
        (gradient Ω 1 Exponent.two v.val x) ∂domainMeasure Ω := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c (gradient Ω 1 Exponent.two v.val)] with x hx
      simp only [hx, Pi.smul_apply, Sobolev.frobenius, real_inner_smul_right]
    _ = _ := integral_const_mul _ _

theorem obstacleResidual_smul (ℓ : H1Zero Ω 1 →L[ℝ] ℝ)
    (u v : H1Zero Ω 1) (c : ℝ) :
    obstacleResidual Ω ℓ u (c • v) = c * obstacleResidual Ω ℓ u v := by
  simp only [obstacleResidual, dirichletPairing_smul_right, map_smul,
    smul_eq_mul, mul_sub]

/-- Nonnegative smooth perturbations preserve the obstacle inequality a.e. -/
theorem obstacle_add_test_nonnegative (ψ : Domain d → ℝ) (u : H1Zero Ω 1)
    (hu : u ∈ obstacleSet Ω ψ) (φ : P102.U4.TestSpace ℝ Ω) (v : H1Zero Ω 1)
    (hv : WeakDivergenceSpec.IsTestClass Ω Exponent.two φ v)
    (hφ : ∀ x, 0 ≤ φ x) : u + v ∈ obstacleSet Ω ψ := by
  change ∀ᵐ x ∂domainMeasure Ω, ψ x ≤ scalarValue Ω (u+v) x
  rw [map_add]
  filter_upwards [hu, scalarValue_test_ae Ω φ v hv,
    Lp.coeFn_add (scalarValue Ω u) (scalarValue Ω v)] with x hx hvx hadd
  rw [hadd, Pi.add_apply, hvx]
  exact hx.trans (le_add_of_nonneg_right (hφ x))

theorem obstacle_nonnegative_of_vi (ℓ : H1Zero Ω 1 →L[ℝ] ℝ)
    (ψ : Domain d → ℝ) (u : H1Zero Ω 1) (hu : u ∈ obstacleSet Ω ψ)
    (hvi : ∀ w ∈ obstacleSet Ω ψ, ℓ (w-u) ≤ dirichletPairing Ω u (w-u)) :
    obstacleNonnegative Ω ℓ u := by
  intro φ v hv hφ
  have h := hvi (u+v) (obstacle_add_test_nonnegative Ω ψ u hu φ v hv hφ)
  simpa only [add_sub_cancel_left, obstacleResidual, sub_nonneg] using h

/-- A compactly supported test inside the noncontact region admits uniform
perturbations of both signs. This also covers the identically zero test. -/
theorem test_small_perturbation (U Ψ : Domain d → ℝ)
    (hU : ContinuousOn U Ω) (hΨ : ContinuousOn Ψ Ω)
    (φ : P102.U4.TestSpace ℝ Ω)
    (hs : tsupport (φ : Domain d → ℝ) ⊆ obstacleInactiveSet Ω U Ψ) :
    ∃ t : ℝ, 0 < t ∧ ∀ c : ℝ, |c| ≤ t → ∀ x ∈ Ω,
      Ψ x ≤ U x → Ψ x ≤ U x + c * φ x := by
  by_cases hne : (tsupport (φ : Domain d → ℝ)).Nonempty
  · have hcont : ContinuousOn (fun x => U x - Ψ x) (tsupport (φ : Domain d → ℝ)) :=
      (hU.sub hΨ).mono (fun x hx => (hs hx).1)
    obtain ⟨x₀, hx₀, hmin⟩ := φ.hasCompactSupport.exists_isMinOn hne hcont
    let δ := U x₀ - Ψ x₀
    have hδ : 0 < δ := sub_pos.mpr (hs hx₀).2
    obtain ⟨M, hM⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
    have hM₀ : 0 ≤ M := (norm_nonneg (φ x₀)).trans (hM x₀)
    let t := δ / (M+1)
    have ht : 0 < t := div_pos hδ (by linarith)
    have htM : t * M ≤ δ := by
      have he : t * (M+1) = δ := by
        dsimp [t]
        exact div_mul_cancel₀ _ (by linarith)
      nlinarith
    refine ⟨t, ht, ?_⟩
    intro c hc x hx hxle
    by_cases hxs : x ∈ tsupport (φ : Domain d → ℝ)
    · have hgap : δ ≤ U x - Ψ x := hmin hxs
      have habs : |c * φ x| ≤ δ := by
        rw [abs_mul]
        exact (mul_le_mul hc (by simpa only [Real.norm_eq_abs] using hM x)
          (abs_nonneg _) ht.le).trans htM
      have hlo := (abs_le.mp habs).1
      linarith
    · rw [image_eq_zero_of_notMem_tsupport hxs, mul_zero, add_zero]
      exact hxle
  · refine ⟨1, zero_lt_one, ?_⟩
    intro c hc x hx hxle
    have hxs : x ∉ tsupport (φ : Domain d → ℝ) := fun h => hne ⟨x,h⟩
    rw [image_eq_zero_of_notMem_tsupport hxs, mul_zero, add_zero]
    exact hxle

/-- Continuous representatives are used only on Ω. The feasibility calculation
uses a.e. equalities throughout and imposes no pointwise constraint on null sets. -/
theorem obstacle_small_test_variations (ψ : Domain d → ℝ) (u : H1Zero Ω 1)
    (hu : u ∈ obstacleSet Ω ψ) (U Ψ : Domain d → ℝ)
    (hU : ContinuousOn U Ω) (hΨ : ContinuousOn Ψ Ω)
    (huU : (scalarValue Ω u : Domain d → ℝ) =ᵐ[domainMeasure Ω] U)
    (hψΨ : ψ =ᵐ[domainMeasure Ω] Ψ)
    (φ : P102.U4.TestSpace ℝ Ω) (v : H1Zero Ω 1)
    (hv : WeakDivergenceSpec.IsTestClass Ω Exponent.two φ v)
    (hs : tsupport (φ : Domain d → ℝ) ⊆ obstacleInactiveSet Ω U Ψ) :
    ∃ t : ℝ, 0 < t ∧ ∀ c : ℝ, |c| ≤ t → u + c • v ∈ obstacleSet Ω ψ := by
  obtain ⟨t, ht, hpert⟩ := test_small_perturbation Ω U Ψ hU hΨ φ hs
  refine ⟨t, ht, ?_⟩
  intro c hc
  change ∀ᵐ x ∂domainMeasure Ω, ψ x ≤ scalarValue Ω (u+c•v) x
  rw [map_add, map_smul]
  filter_upwards [hu, huU, hψΨ, scalarValue_test_ae Ω φ v hv,
    ae_restrict_mem Ω.isOpen.measurableSet,
    Lp.coeFn_add (scalarValue Ω u) (c • scalarValue Ω v),
    Lp.coeFn_smul c (scalarValue Ω v)] with x hux hUx hΨx hvx hx hadd hsmul
  rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hUx, hvx, hΨx]
  exact hpert c hc x hx (by rwa [← hΨx, ← hUx])

theorem obstacle_inactiveSet_open (U Ψ : Domain d → ℝ)
    (hU : ContinuousOn U Ω) (hΨ : ContinuousOn Ψ Ω) :
    IsOpen (obstacleInactiveSet Ω U Ψ) := by
  have h := (hU.sub hΨ).isOpen_inter_preimage Ω.isOpen (isOpen_Ioi (a := (0 : ℝ)))
  convert h using 1
  ext x
  simp only [obstacleInactiveSet, Set.mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioi,
    Pi.sub_apply, sub_pos]
  rfl

theorem obstacle_inactive_of_vi (ℓ : H1Zero Ω 1 →L[ℝ] ℝ)
    (ψ : Domain d → ℝ) (u : H1Zero Ω 1) (hu : u ∈ obstacleSet Ω ψ)
    (hvi : ∀ w ∈ obstacleSet Ω ψ, ℓ (w-u) ≤ dirichletPairing Ω u (w-u)) :
    obstacleInactiveEquation Ω ℓ ψ u := by
  intro U Ψ hU hΨ huU hψΨ
  refine ⟨obstacle_inactiveSet_open Ω U Ψ hU hΨ, ?_⟩
  intro φ v hv hs
  obtain ⟨t, ht, hpert⟩ := obstacle_small_test_variations Ω ψ u hu U Ψ hU hΨ huU hψΨ φ v hv hs
  have hp := hvi (u + t • v) (hpert t (by rw [abs_of_pos ht]))
  have hn := hvi (u + (-t) • v) (hpert (-t) (by rw [abs_neg, abs_of_pos ht]))
  have hpos : 0 ≤ t * obstacleResidual Ω ℓ u v := by
    rw [← obstacleResidual_smul]
    simpa only [add_sub_cancel_left, obstacleResidual, sub_nonneg] using hp
  have hneg : 0 ≤ (-t) * obstacleResidual Ω ℓ u v := by
    rw [← obstacleResidual_smul]
    simpa only [add_sub_cancel_left, obstacleResidual, sub_nonneg] using hn
  nlinarith

/-- The full theorem retains the upstream minimizer and its exact variational
characterization, and adds both distributional conclusions. -/
theorem obstacle_full : ObstacleDistributionExpected.FullTheorem := by
  intro n Ω hΩ ℓ ψ hψ hne
  refine ⟨obstacle_unique_minimizer Ω hΩ ℓ ψ hψ hne, ?_, ?_⟩
  · exact fun u hu => obstacle_minimization_iff Ω hΩ ℓ ψ hψ u hu
  · intro u hu hmin
    have hvi := (obstacle_minimization_iff Ω hΩ ℓ ψ hψ u hu).mp hmin
    exact ⟨obstacle_nonnegative_of_vi Ω ℓ ψ u hu hvi,
      obstacle_inactive_of_vi Ω ℓ ψ u hu hvi⟩

end VariationalNotes.Flux
