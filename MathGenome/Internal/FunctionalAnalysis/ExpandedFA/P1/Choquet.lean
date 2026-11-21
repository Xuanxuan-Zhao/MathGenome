import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.Choquet
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24KreinMilman
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.Barycenters
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.ChoquetMetrizable

/-! The two Choquet representation statements, `fa2:p1:choquet`.
Krein–Milman and the compact-set barycenter theorem prove the first clause.
The accepted metrizable theorem proves the second on the original compact
subspace. Real moment identities imply scalar-linear moment identities by
applying the real and imaginary parts of each continuous scalar-linear test.
-/

noncomputable section

namespace ExpandedFA.P1.Choquet

open Set MeasureTheory
open scoped Topology

universe u v

private theorem scalar_moments_of_real
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [TopologicalSpace E] (S : Set E) [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    (b : E) (hb : ∀ ℓ : E →L[ℝ] ℝ,
      ℓ b = ∫ x : S, ℓ (x : E) ∂μ) :
    ∀ ℓ : E →L[𝕜] 𝕜, Integrable (fun x : S => ℓ (x : E)) μ ∧
      ℓ b = ∫ x : S, ℓ (x : E) ∂μ := by
  intro ℓ
  have hi : Integrable (fun x : S => ℓ (x : E)) μ :=
    (ℓ.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨hi, ?_⟩
  apply RCLike.ext
  · rw [← integral_re hi]
    exact hb (RCLike.reCLM.comp (ℓ.restrictScalars ℝ))
  · rw [← integral_im hi]
    exact hb (RCLike.imCLM.comp (ℓ.restrictScalars ℝ))

/-- Every point is represented on the closure of the extreme points, over
both scalar fields and without any metrizability assumption. -/
theorem closure_extreme_representation : Spec.ClosureExtremeRepresentation.{u,v} := by
  intro 𝕜 E _ _ _ _ _ _ _ _ _ _ K hne hK hconv b hb
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let S := closure (C24FacesSpec.extremePoints K)
  have hSK : S ⊆ K := closure_minimal (fun _ hx => hx.1) hK.isClosed
  have hS : IsCompact S := hK.of_isClosed_subset isClosed_closure hSK
  have hkm : K = closure (convexHull ℝ (C24FacesSpec.extremePoints K)) :=
    real_krein_milman K hne hK hconv
  have hhull : closure (convexHull ℝ S) = K := by
    apply Subset.antisymm
    · exact closure_minimal (convexHull_min hSK hconv) hK.isClosed
    · rw [hkm]
      exact closure_mono (convexHull_mono subset_closure)
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨μ, hprob, hreg, hmom⟩ := Barycenters.representing_probability ℝ E
    (fun x y hxy => C24.real_locally_convex_points_separated x y hxy)
    S hS (hhull.symm ▸ hK) b (hhull.symm ▸ hb)
  let : IsProbabilityMeasure μ := hprob
  exact ⟨μ, hprob, hreg, scalar_moments_of_real S μ b (fun ℓ => (hmom ℓ).2)⟩

/-- Metrizability of the compact subset suffices for mass one on the extreme
set itself; no closedness of that set is assumed. -/
theorem extreme_supported_representation : Spec.ExtremeSupportedRepresentation.{u,v} := by
  intro 𝕜 E _ _ _ _ _ _ _ _ _ _ K hne hK hconv _ b hb
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  refine ⟨ChoquetMetrizable.extreme_set_borel E K hK hconv, ?_⟩
  obtain ⟨μ, hprob, hreg, hmom, hmass⟩ :=
    ChoquetMetrizable.extreme_supported_representation E K hne hK hconv b hb
  let : IsProbabilityMeasure μ := hprob
  exact ⟨μ, hprob, hreg, scalar_moments_of_real K μ b (fun ℓ => (hmom ℓ).2), hmass⟩

end ExpandedFA.P1.Choquet
