import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01FiniteDimension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01Norm
import Mathlib.Analysis.RCLike.Lemmas

/-! Finite-dimensional norm equivalence and its topological consequences.

For arbitrary norm functions we put the target seminorm on a separate copy of
`E`, then use continuity of linear maps from finite-dimensional normed spaces.
Doing this in both directions gives positive comparison constants. Mathlib's
finite-dimensional completeness and properness theorems give the remaining
claims, with no nonzero-dimension or ambient-completeness hypothesis.
-/

noncomputable section
namespace ExpandedFA.P1.C01FiniteDimension

/-- Any seminorm on a finite-dimensional normed space has a global norm bound.
The separate type `ULift E` carries this seminorm, so no topology compatibility
is assumed between the given norm and the seminorm to be bounded. -/
private theorem seminorm_bound (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (q : Seminorm 𝕜 E) : ∃ C > (0 : ℝ), ∀ x, q x ≤ C * ‖x‖ := by
  let u : ULift.{0} E →ₗ[𝕜] E :=
    { toFun := ULift.down
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let q' := q.comp u
  let g : SeminormedAddCommGroup (ULift.{0} E) := C01Norm.seminormedGroup q'
  let : TopologicalSpace (ULift.{0} E) := g.toUniformSpace.toTopologicalSpace
  let : NormedSpace 𝕜 (ULift.{0} E) :=
    { (inferInstance : Module 𝕜 (ULift.{0} E)) with
      norm_smul_le := fun a x => (map_smul_eq_mul q' a x).le }
  let v : E →ₗ[𝕜] ULift.{0} E :=
    { toFun := ULift.up
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨C, hC, h⟩ := v.toContinuousLinearMap.bound
  exact ⟨C, hC, h⟩

theorem finite_dimensional_norm_equivalence : Spec.NormEquivalence := by
  intro 𝕜 E _ _ _ _ p q hp hq
  let P := C01Norm.seminormOfAxioms 𝕜 E p hp.1
  let Q := C01Norm.seminormOfAxioms 𝕜 E q hq.1
  have bound (r s : Seminorm 𝕜 E) (hr : ∀ x, r x = 0 → x = 0) :
      ∃ C > (0 : ℝ), ∀ x, s x ≤ C * r x := by
    let : NormedAddCommGroup E := C01Norm.normedGroup r hr
    let : NormedSpace 𝕜 E :=
      { (inferInstance : Module 𝕜 E) with
        norm_smul_le := fun a x => (map_smul_eq_mul r a x).le }
    exact seminorm_bound 𝕜 E s
  obtain ⟨C, hC, hupper⟩ := bound P Q (fun x hx => (hp.2 x).mp hx)
  obtain ⟨D, hD, hlower⟩ := bound Q P (fun x hx => (hq.2 x).mp hx)
  refine ⟨D⁻¹, inv_pos.mpr hD, C, hC, fun x => ⟨?_, hupper x⟩⟩
  exact (inv_mul_le_iff₀ hD).mpr (hlower x)

theorem finite_dimensional_complete : Spec.Completeness := by
  intro 𝕜 E _ _ _ _
  exact FiniteDimensional.complete 𝕜 E

theorem finite_dimensional_closed_bounded_compact :
    Spec.ClosedBoundedCompact := by
  intro 𝕜 E _ _ _ _ s
  let := FiniteDimensional.proper_rclike 𝕜 E
  exact Metric.isCompact_iff_isClosed_bounded

theorem finite_dimensional_locally_compact : Spec.LocalCompactness := by
  intro 𝕜 E _ _ _ _
  let := FiniteDimensional.proper_rclike 𝕜 E
  infer_instance

theorem finite_dimensional_subspace_closed : Spec.SubspaceClosed := by
  intro 𝕜 E _ _ _ M _
  exact M.closed_of_finiteDimensional

end ExpandedFA.P1.C01FiniteDimension
