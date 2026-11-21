import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Evolution.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

open Filter Topology

namespace NumAnalysis206.Evolution

universe u v

/-- Public value-checked presentation of finite-horizon small-step stability.
The canonical interfaces and all other finite-horizon definitions live in Specs. -/
def smallStepStability : Specs.NumAnalysis206.Evolution.smallStepStabilityType :=
  @SmallStepStable

/-- The floor cutoff loses no mesh points, for every positive step. -/
theorem mem_meshIndices_iff {T₀ h : ℝ} (hh : 0 < h) (n : ℕ) :
    n ∈ meshIndices T₀ h ↔ (n : ℝ) * h ≤ T₀ := by
  simp only [meshIndices, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun hn => hn.2, fun hn =>
    ⟨Nat.lt_succ_iff.mpr (Nat.le_floor ((le_div_iff₀ hh).mpr hn)), hn⟩⟩

/-- The orbit maximum ranges over precisely the completed steps. -/
theorem mem_orbitIndices_iff {T₀ h : ℝ} (hh : 0 < h) (j : ℕ) :
    j ∈ orbitIndices T₀ h ↔ ((j : ℝ) + 1) * h ≤ T₀ := by
  simp only [orbitIndices, Finset.mem_filter, mem_meshIndices_iff hh]
  constructor
  · exact And.right
  · intro hj
    exact ⟨by nlinarith, hj⟩

variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X]

theorem generator_hasValue (T : StronglyContinuousSemigroup 𝕜 X)
    (x : generatorDomain T) : HasGeneratorValue T x (generator T x) :=
  Classical.choose_spec x.property

theorem generatorValue_unique {T : StronglyContinuousSemigroup 𝕜 X}
    {x A B : X} (hA : HasGeneratorValue T x A) (hB : HasGeneratorValue T x B) : A = B :=
  tendsto_nhds_unique hA hB

/-- Subtracting the exact difference quotient leaves the vector local defect. -/
theorem differenceQuotient_sub (C : ℝ → X →L[𝕜] X)
    (T : StronglyContinuousSemigroup 𝕜 X) (h : ℝ) (x : X) :
    differenceQuotient C h x - differenceQuotient T.toFun h x =
      (h⁻¹ : 𝕜) • ((C h - T h) x) := by
  simp only [differenceQuotient, sub_apply,
    one_apply_eq_self, ← smul_sub]
  congr 1
  abel

/-- On positive steps, taking the norm gives exactly the source's scalar defect. -/
theorem norm_differenceQuotient_sub (C : ℝ → X →L[𝕜] X)
    (T : StronglyContinuousSemigroup 𝕜 X) (x : X) {h : ℝ} (hh : 0 < h) :
    ‖differenceQuotient C h x - differenceQuotient T.toFun h x‖ =
      localDefect C T h x := by
  rw [differenceQuotient_sub, norm_smul, norm_inv, RCLike.norm_ofReal,
    abs_of_pos hh]
  rfl

/-- The generator formulation of pointwise consistency is equivalent to the
one-step defect formulation on the generator domain. -/
theorem generatorConsistencyEquivalence :
    Specs.NumAnalysis206.Evolution.generatorConsistencyEquivalence := by
  intro 𝕜 _ X _ _ _ C T x
  have hT := generator_hasValue T x
  have heq : (fun h => ‖differenceQuotient C h x - differenceQuotient T.toFun h x‖)
      =ᶠ[𝓝[>] (0 : ℝ)] (fun h => localDefect C T h x) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact norm_differenceQuotient_sub C T x hh
  change PointwiseConsistent C T x ↔ _
  constructor
  · intro hC
    have hnorm : Tendsto (fun h => ‖differenceQuotient C h x -
        differenceQuotient T.toFun h x‖) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      (show Tendsto (fun h => localDefect C T h x) _ _ from hC).congr' heq.symm
    have hdiff := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
    have hsum := hdiff.add hT
    simpa only [sub_add_cancel, zero_add] using hsum
  · intro hC
    have hdiff := hC.sub hT
    have hnorm := tendsto_zero_iff_norm_tendsto_zero.mp
      (by simpa only [sub_self] using hdiff)
    exact hnorm.congr' heq

end NumAnalysis206.Evolution
