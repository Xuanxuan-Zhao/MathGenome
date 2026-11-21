import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Evolution.DenseConvergence
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Evolution.OrbitError
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Evolution.SemigroupBound

open Filter Topology

noncomputable section

namespace NumAnalysis206.Evolution

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X]

/-- Every individual mesh error is at most the mesh maximum. -/
theorem norm_mesh_error_le (C : ℝ → X →L[𝕜] X)
    (T : StronglyContinuousSemigroup 𝕜 X) (T₀ h : ℝ) (x : X)
    {n : ℕ} (hn : n ∈ meshIndices T₀ h) :
    ‖(C h ^ n) x - T ((n : ℝ) * h) x‖ ≤ meshError C T T₀ h x :=
  Finset.le_sup (f := fun n : ℕ => ‖(C h ^ n) x - T ((n : ℝ) * h) x‖₊) hn

/-- The maximum over mesh times inherits the uniform operator bounds. -/
theorem meshErrorExtensionEstimate :
    Specs.NumAnalysis206.Evolution.meshErrorExtensionEstimate := by
  intro 𝕜 _ X _ _ _ C T T₀ h₀ M K _hT₀ _hh₀ hM hK hstable hT x y h hh hhh₀
  have hbound : 0 ≤ meshError C T T₀ h y + (M + K) * ‖x - y‖ :=
    add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (add_nonneg hM hK) (norm_nonneg _))
  change (meshIndices T₀ h).sup
    (fun n => ‖(C h ^ n) x - T ((n : ℝ) * h) x‖₊) ≤
    (⟨meshError C T T₀ h y + (M + K) * ‖x - y‖, hbound⟩ : NNReal)
  apply Finset.sup_le
  intro n hn
  have hnT := (mem_meshIndices_iff hh n).mp hn
  have ht : (n : ℝ) * h ∈ Set.Icc 0 T₀ :=
    ⟨mul_nonneg (Nat.cast_nonneg _) hh.le, hnT⟩
  have hsplit :
      (C h ^ n) x - T ((n : ℝ) * h) x =
        ((C h ^ n) y - T ((n : ℝ) * h) y) +
        ((C h ^ n) (x - y) - T ((n : ℝ) * h) (x - y)) := by
    simp only [map_sub]
    abel
  change ‖(C h ^ n) x - T ((n : ℝ) * h) x‖ ≤ _
  calc
    ‖(C h ^ n) x - T ((n : ℝ) * h) x‖ ≤
        ‖(C h ^ n) y - T ((n : ℝ) * h) y‖ +
        ‖(C h ^ n) (x - y) - T ((n : ℝ) * h) (x - y)‖ := by
      rw [hsplit]
      exact norm_add_le _ _
    _ ≤ meshError C T T₀ h y +
        (‖(C h ^ n) (x - y)‖ + ‖T ((n : ℝ) * h) (x - y)‖) :=
      add_le_add (norm_mesh_error_le C T T₀ h y hn) (norm_sub_le _ _)
    _ ≤ meshError C T T₀ h y +
        (M * ‖x - y‖ + K * ‖x - y‖) := by
      apply add_le_add le_rfl
      apply add_le_add
      · exact ((C h ^ n).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hstable h hh hhh₀ n hnT) (norm_nonneg _))
      · exact ((T ((n : ℝ) * h)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hT _ ht) (norm_nonneg _))
    _ = meshError C T T₀ h y + (M + K) * ‖x - y‖ := by rw [add_mul]

/-- Stability first gives convergence on the dense class. The comparison
vector used below depends on x and ε, and is fixed throughout the step limit. -/
theorem stabilityAndDenseOrbitConvergence :
    Specs.NumAnalysis206.Evolution.stabilityAndDenseOrbitConvergence := by
  intro 𝕜 _ X _ _ _ C T T₀ h₀ M hT₀ hh₀ hstable
  have hquant := stabilityOrbitErrorBound C T T₀ h₀ M hT₀ hh₀ hstable
  refine ⟨hquant, ?_⟩
  intro D hD hcons
  have hM : 0 ≤ M := (norm_nonneg (C h₀ ^ 0)).trans
    (hstable h₀ hh₀ le_rfl 0 (by simpa using hT₀.le))
  obtain ⟨K, hK, hT⟩ := semigroupCompactBound T T₀ hT₀
  have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ h ≤ h₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ h in 𝓝[>] (0 : ℝ), h ≤ h₀ from
        nhdsWithin_le_nhds (Iic_mem_nhds hh₀))] with h hh hle
    exact ⟨hh, hle⟩
  have hdenseConv (y : X) (hy : y ∈ D) :
      Tendsto (fun h => meshError C T T₀ h y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hupper : Tendsto (fun h => M * T₀ * orbitDefect C T T₀ h y)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [mul_zero] using
        (show Tendsto (fun h => orbitDefect C T T₀ h y) _ _ from hcons y hy).const_mul
          (M * T₀)
    apply squeeze_zero' (Eventually.of_forall (fun h => NNReal.coe_nonneg _)) _ hupper
    filter_upwards [hsmall] with h hh
    exact hquant y h hh.1 hh.2
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hApos : 0 < M + K + 1 := by linarith
  obtain ⟨y, hy, hxy⟩ := hD.exists_dist_lt x (div_pos (half_pos hε) hApos)
  rw [dist_eq_norm] at hxy
  have happrox : (M + K) * ‖x - y‖ < ε / 2 := by
    have := (lt_div_iff₀ hApos).mp hxy
    nlinarith [norm_nonneg (x - y)]
  have hySmall := (Metric.tendsto_nhds.mp (hdenseConv y hy)) (ε / 2) (half_pos hε)
  filter_upwards [hsmall, hySmall] with h hh hyh
  have hext := meshErrorExtensionEstimate C T T₀ h₀ M K hT₀ hh₀ hM hK
    hstable hT x y h hh.1 hh.2
  have hEy : 0 ≤ meshError C T T₀ h y := NNReal.coe_nonneg _
  have hEx : 0 ≤ meshError C T T₀ h x := NNReal.coe_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hEy] at hyh
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hEx]
  linarith

/-- W19 applied directly to the canonical finite-horizon stability predicate. -/
theorem denseOrbitConvergence : Specs.NumAnalysis206.Evolution.denseOrbitConvergence := by
  intro 𝕜 _ X _ _ _ C T T₀ hT₀ hstable D hD hcons
  obtain ⟨h₀, hh₀, M, _hM, hbound⟩ := hstable
  exact (stabilityAndDenseOrbitConvergence C T T₀ h₀ M hT₀ hh₀ hbound).2 D hD hcons

end NumAnalysis206.Evolution
