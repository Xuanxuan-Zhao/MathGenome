import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12DualPair

/-!
Compactness in the original normed target, relative weak compactness, and
complete continuity. These definitions apply over both ℝ and ℂ, retain the
zero-space cases, and in particular apply to the Banach spaces in the source.
-/

namespace ExpandedFA.Compactness

universe u v w
open Filter
open scoped Topology
noncomputable section

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- The closed unit ball has compact image closure inside F itself.
Neither boundedness of T nor completeness of F is presupposed. -/
def IsCompactLinearMap (T : E →ₗ[𝕜] F) : Prop :=
  IsCompact (closure (T '' Metric.closedBall (0 : E) 1))

/-- The unit-ball image has compact closure for σ(F,F'), where F' is the
original norm-continuous scalar-linear dual. -/
def IsWeaklyCompactOperator (T : E →L[𝕜] F) : Prop :=
  @IsCompact F (P1.dualPairTopology 𝕜 F (F →L[𝕜] 𝕜) (topDualPairing 𝕜 F))
    (@closure F (P1.dualPairTopology 𝕜 F (F →L[𝕜] 𝕜) (topDualPairing 𝕜 F))
      (T '' Metric.closedBall (0 : E) 1))

/-- A bounded map preserves weakly convergent sequences as norm convergent
sequences, with their corresponding limits. -/
def IsCompletelyContinuous (T : E →L[𝕜] F) : Prop :=
  ∀ (s : ℕ → E) (x : E),
    (∀ f : E →L[𝕜] 𝕜, Tendsto (fun n => f (s n)) atTop (𝓝 (f x))) →
    Tendsto (fun n => T (s n)) atTop (𝓝 (T x))

/-- The neighborhood-of-zero definition agrees with the source definition,
also for algebraic linear maps and incomplete normed spaces. -/
theorem compact_iff_isCompactOperator : DefinitionsSpec.CompactIffNative := by
  intro 𝕜 _ E F _ _ _ _ T
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall T zero_lt_one).symm

/-- Compactness on the unit ball is equivalent to relative compactness of
the image of every norm-bounded set, including the empty set. -/
theorem compact_iff_bounded_images : DefinitionsSpec.CompactIffBoundedImages := by
  intro 𝕜 _ E F _ _ _ _ T
  constructor
  · intro h S hS
    exact ((compact_iff_isCompactOperator T).mp h).isCompact_closure_image_of_bounded hS
  · intro h
    exact h (Metric.closedBall 0 1) Metric.isBounded_closedBall

/-- Compatibility of weak compactness with Mathlib's native weak space. -/
theorem weaklyCompact_iff_weakSpace : DefinitionsSpec.WeaklyCompactIffWeakSpace := by
  intro 𝕜 _ E F _ _ _ _ T
  change @IsCompact (WeakSpace 𝕜 F) (TopologicalSpace.induced id
    (instTopologicalSpaceWeakSpace 𝕜 F))
    (@closure (WeakSpace 𝕜 F)
      (TopologicalSpace.induced id (instTopologicalSpaceWeakSpace 𝕜 F)) _) ↔ _
  rw [induced_id]
  rfl

/-- Weak convergence is exactly convergence against the original dual.
The initial-topology argument needs no sequential compactness theorem. -/
theorem weak_convergence_iff_tests : DefinitionsSpec.WeakConvergenceTests := by
  intro 𝕜 _ E _ _ s x
  change Tendsto s atTop (@nhds E
    (P1.C12DualPairSpec.DualPairTopologyValue
      𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) x) ↔ _
  rw [P1.dualPairTopology_evaluation 𝕜 E, nhds_iInf]
  simp only [tendsto_iInf, nhds_induced, tendsto_comap_iff, Function.comp_def]

/-- Complete continuity is the weak-to-norm property for sequences, with
norm limit T x. The weak topology is the shared evaluation topology. -/
theorem completelyContinuous_iff_weak_convergence :
    DefinitionsSpec.CompletelyContinuousIffWeakConvergence := by
  intro 𝕜 _ E F _ _ _ _ T
  constructor
  · intro h s x hs
    exact h s x ((weak_convergence_iff_tests s x).mp hs)
  · intro h s x hs
    exact h s x ((weak_convergence_iff_tests s x).mpr hs)

end
end ExpandedFA.Compactness
