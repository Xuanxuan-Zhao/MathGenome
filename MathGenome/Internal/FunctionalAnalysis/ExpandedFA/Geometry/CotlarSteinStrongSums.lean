import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.CotlarSteinStrongSums
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Geometry.CotlarSteinFinite
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07DenseConvergence

/-!
For each finite subset, restrict to its subtype and apply the accepted finite
Cotlar–Stein estimate. Nonnegativity bounds each restricted row by its full
convergent sum. To handle arbitrary index sets we extend the dense-convergence
argument to a general filter: uniform operator bounds give a Cauchy image
filter at every vector, completeness supplies limits, and uniqueness of limits
preserves linearity. The norm bound passes to the pointwise limit.
-/

noncomputable section
open Filter
open scoped Topology
namespace ExpandedFA.Geometry.CotlarSteinStrongSums

universe u v w

/-- Filter version of dense convergence. The domain need not be complete. -/
theorem dense_convergence_along_filter
    {𝕜 E F β : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (U : β → E →L[𝕜] F) (l : Filter β) [NeBot l]
    (D : Set E) (M : ℝ) (hM : 0 ≤ M) (hD : Dense D)
    (hbound : ∀ b, ‖U b‖ ≤ M)
    (hconv : ∀ d ∈ D, ∃ y, Tendsto (fun b => U b d) l (𝓝 y)) :
    ∃ S : E →L[𝕜] F, ‖S‖ ≤ M ∧
      ∀ x, Tendsto (fun b => U b x) l (𝓝 (S x)) := by
  have hc (x : E) : Cauchy (map (fun b => U b x) l) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    have hden : 0 < 4 * (M + 1) := by positivity
    obtain ⟨d, hd, hxd⟩ := hD.exists_dist_lt x (div_pos hε hden)
    have hsmall : 2 * M * dist x d < ε / 2 := by
      have h := (lt_div_iff₀ hden).mp hxd
      nlinarith [dist_nonneg (x := x) (y := d)]
    obtain ⟨y, hy⟩ := hconv d hd
    have he : ∀ᶠ b in l, dist (U b d) y < ε / 4 :=
      (Metric.tendsto_nhds.mp hy) (ε / 4) (by positivity)
    refine ⟨(fun b => U b x) '' {b | dist (U b d) y < ε / 4}, ?_, ?_⟩
    · change {b | U b x ∈ (fun b => U b x) '' {b | dist (U b d) y < ε / 4}} ∈ l
      filter_upwards [he] with b hb
      exact ⟨b, hb, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have hmid : dist (U a d) (U b d) < ε / 2 := by
        have ht := dist_triangle (U a d) y (U b d)
        rw [dist_comm y (U b d)] at ht
        change dist (U a d) y < ε / 4 at ha
        change dist (U b d) y < ε / 4 at hb
        linarith
      calc
        dist (U a x) (U b x) ≤
            dist (U a x) (U a d) + dist (U a d) (U b d) +
              dist (U b d) (U b x) := dist_triangle4 _ _ _ _
        _ ≤ M * dist x d + dist (U a d) (U b d) + M * dist x d := by
          gcongr
          · exact P1.C07DenseConvergence.operator_dist_le_of_norm_le _ (hbound a) x d
          · simpa only [dist_comm d x] using
              P1.C07DenseConvergence.operator_dist_le_of_norm_le _ (hbound b) d x
        _ < ε := by linarith
  choose f hf using fun x => cauchy_map_iff_exists_tendsto.mp (hc x)
  let L : E →ₗ[𝕜] F :=
    { toFun := f
      map_add' := fun x y => tendsto_nhds_unique
        (by simpa only [map_add] using hf (x + y)) ((hf x).add (hf y))
      map_smul' := fun a x => tendsto_nhds_unique
        (by simpa only [map_smul] using hf (a • x)) ((hf x).const_smul a) }
  have hb (x : E) : ‖L x‖ ≤ M * ‖x‖ :=
    le_of_tendsto (hf x).norm (Eventually.of_forall fun b =>
      (U b).le_of_opNorm_le (hbound b) x)
  let S : E →L[𝕜] F := L.mkContinuous M hb
  exact ⟨S, S.opNorm_le_bound hM hb, hf⟩

/-- Infinite row bounds imply the estimate for every finite partial sum. -/
theorem cotlar_stein_partial_sum_estimate : Spec.PartialSumEstimate.{u, v, w} := by
  intro 𝕜 H ι _ _ _ _ T A B hA hB ha hb s
  classical
  have h := CotlarSteinFinite.cotlar_stein_row_estimate 𝕜 H s
    (fun i => T i) A B hA hB
    (fun i => ?_) (fun i => ?_)
  · rwa [Finset.sum_coe_sort s T] at h
  · rw [Finset.sum_coe_sort s (fun j : ι => Real.sqrt ‖(T (i : ι)).adjoint.comp (T j)‖)]
    exact ((ha i).1.sum_le_tsum s (fun _ _ => Real.sqrt_nonneg _)).trans (ha i).2
  · rw [Finset.sum_coe_sort s (fun j : ι => Real.sqrt ‖(T (i : ι)).comp (T j).adjoint‖)]
    exact ((hb i).1.sum_le_tsum s (fun _ _ => Real.sqrt_nonneg _)).trans (hb i).2

/-- The same dense-convergence implication for any nontrivial filter of
finite partial sums, including a prescribed ordering. -/
theorem cotlar_stein_strong_sum_along_filter : Spec.StrongSumAlongFilter.{u, v, w} := by
  intro 𝕜 H ι _ _ _ _ T A B hA hB ha hb D l _ hD hconv
  exact dense_convergence_along_filter (fun s : Finset ι => ∑ i ∈ s, T i)
    l D (Real.sqrt (A * B)) (Real.sqrt_nonneg _) hD
    (cotlar_stein_partial_sum_estimate 𝕜 H ι T A B hA hB ha hb) hconv

/-- Strong sum of the entire family as the net of finite partial sums. -/
theorem cotlar_stein_strong_sum : Spec.StrongSum.{u, v, w} := by
  intro 𝕜 H ι _ _ _ _ T A B hA hB ha hb D hD hconv
  exact cotlar_stein_strong_sum_along_filter 𝕜 H ι T A B hA hB ha hb D atTop hD hconv

end ExpandedFA.Geometry.CotlarSteinStrongSums
