import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C07WeakBoundedness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05BidualIsometry
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04DualComplete

/-!
Weak boundedness detects norm boundedness without completeness of E.
Apply uniform boundedness to evaluation maps indexed by A, on the Banach
space E′. The canonical bidual isometry then gives the norm bound in E.
-/

namespace ExpandedFA.P1.C07WeakBoundedness

universe u v

theorem weak_boundedness : Spec.WeakBoundedness.{u, v} := by
  intro 𝕜 E _ _ _ A
  constructor
  · intro hA f
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hA
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨‖f‖ * C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (f.le_opNorm x).trans
      (mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg f))
  · intro hA
    let : CompleteSpace (E →L[𝕜] 𝕜) := C04DualComplete.dual_completeSpace 𝕜 E
    let T : A → (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
      fun x => C04CanonicalMap.canonicalEvaluation 𝕜 E x
    have hpoint : ∀ f : E →L[𝕜] 𝕜, ∃ C : ℝ, ∀ x : A, ‖T x f‖ ≤ C := by
      intro f
      obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (hA f)
      exact ⟨C, fun x => hC (f x) ⟨x, x.property, rfl⟩⟩
    obtain ⟨C, _, hC⟩ :=
      C07UniformBoundedness.uniform_boundedness 𝕜 (E →L[𝕜] 𝕜) 𝕜 A T hpoint
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨C, fun x hx => ?_⟩
    have h := hC ⟨x, hx⟩
    change ‖C04CanonicalMap.canonicalEvaluation 𝕜 E x‖ ≤ C at h
    exact (C05BidualIsometry.canonicalEvaluation_norm 𝕜 E x) ▸ h

end ExpandedFA.P1.C07WeakBoundedness
