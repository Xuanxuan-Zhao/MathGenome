import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Conventions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04Dual

/-!
Native Hilbert conventions, including bounded forms on two different spaces.
No new Hilbert or dual structure is introduced. See the independent Specs for
source locations and the exact existence and boundary-case obligations.
-/

noncomputable section
open scoped InnerProductSpace ComplexConjugate

namespace ExpandedFA.Hilbert.Conventions
universe u v w

/-- The shared scalar-linear continuous dual H′. -/
abbrev ContinuousDual : Spec.ContinuousDualType.{u, v} :=
  fun 𝕜 H _ _ _ => ExpandedFA.P1.C04Dual.ContinuousDual 𝕜 H

/-- Continuous conjugate-linear functionals, with the native operator norm. -/
abbrev ContinuousAntidual : Spec.ContinuousAntidualType.{u, v} :=
  fun 𝕜 H _ _ _ => H →L⋆[𝕜] 𝕜

/-- Bounded forms, conjugate linear in the test slot, linear in the unknown slot. -/
abbrev BoundedSesquilinearForm : Spec.BoundedSesquilinearFormType.{u, v, w} :=
  fun 𝕜 H K _ _ _ _ _ => H →L⋆[𝕜] K →L[𝕜] 𝕜

/-- An admissible nonnegative bound for a form. -/
def FormBound : Spec.FormBoundType.{u, v, w} :=
  fun _ _ _ _ _ _ _ _ a C => 0 ≤ C ∧ ∀ x y, ‖a x y‖ ≤ C * ‖x‖ * ‖y‖

/-- Real-part coercivity with its specified positive constant. -/
def FormCoercive : Spec.FormCoerciveType.{u, v} :=
  fun _ _ _ _ _ a α => 0 < α ∧ ∀ x, α * ‖x‖ ^ 2 ≤ RCLike.re (a x x)

/-- Hermitian symmetry, imposed separately from boundedness and coercivity. -/
def FormHermitian : Spec.FormHermitianType.{u, v} :=
  fun _ _ _ _ _ a => ∀ x y, a x y = conj (a y x)

/-- The original conjugate-first inner product as a bounded form. -/
abbrev innerForm : Spec.InnerFormType.{u, v} := fun 𝕜 _ _ _ _ => innerSL 𝕜

/-- Orthogonal complement of an arbitrary set, including the empty set. -/
def orthogonalComplement : Spec.OrthogonalComplementType.{u, v} :=
  fun 𝕜 _ _ _ _ A => (Submodule.span 𝕜 A).orthogonal

/-- Ambient-valued orthogonal projection, using Mathlib's existence class. -/
abbrev orthogonalProjection : Spec.OrthogonalProjectionType.{u, v} :=
  fun _ _ _ _ _ M _ => M.starProjection

/-- Native real restriction of scalars with inner product Re ⟪x,y⟫.
Use locally as an instance; H keeps its original normed additive group. -/
abbrev realification : Spec.RealificationType.{u, v} :=
  fun 𝕜 H _ _ _ => InnerProductSpace.rclikeToReal 𝕜 H

/-- Real convexity on the original underlying space. -/
def RealConvex : Spec.RealConvexType.{u, v} :=
  fun 𝕜 H _ _ _ C => letI := realification 𝕜 H; Convex ℝ C

theorem inner_convention : Spec.InnerConvention.{u, v} := by
  intro 𝕜 H _ _ _ c x y
  exact ⟨inner_smul_left x y c, inner_smul_right x y c, inner_conj_symm x y⟩

theorem antidual_identification : Spec.AntidualIdentification.{u, v} := by
  intro 𝕜 H _ _ _ f
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨F.continuous, F.map_add, fun c x => F.map_smulₛₗ c x⟩
  · rintro ⟨hc, ha, hs⟩
    exact ⟨{ toFun := f, map_add' := ha, map_smul' := hs, cont := hc }, rfl⟩

theorem antidual_norm_supremum : Spec.AntidualNormSupremum.{u, v} := by
  intro 𝕜 H _ _ _ F
  simpa only [Metric.closedBall, dist_zero_right] using F.sSup_unitClosedBall_eq_norm.symm

theorem bounded_form_identification : Spec.BoundedFormIdentification.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ a
  constructor
  · rintro ⟨A, hA⟩
    have heq : a = fun x y => A x y := by
      funext x y
      exact (hA x y).symm
    subst a
    refine ⟨?_, ?_, ?_, ?_, ‖A‖, norm_nonneg A, A.le_opNorm₂⟩
    · intro x z y
      exact congrArg (fun f : K →L[𝕜] 𝕜 => f y) (A.map_add x z)
    · intro c x y
      exact congrArg (fun f : K →L[𝕜] 𝕜 => f y) (A.map_smulₛₗ c x)
    · intro x y z
      exact (A x).map_add y z
    · intro c x y
      exact (A x).map_smul c y
  · rintro ⟨ha, hs, hb, ht, C, _, hC⟩
    let A : H →ₗ⋆[𝕜] K →ₗ[𝕜] 𝕜 := LinearMap.mk₂'ₛₗ _ _ a ha hs hb ht
    exact ⟨A.mkContinuous₂ C hC, fun _ _ => rfl⟩

theorem form_norm_least_bound : Spec.FormNormLeastBound.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ a
  exact ⟨⟨norm_nonneg a, a.le_opNorm₂⟩, fun _ hC => a.opNorm_le_bound₂ hC.1 hC.2⟩

theorem form_norm_infimum : Spec.FormNormInfimum.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ a
  exact (form_norm_least_bound 𝕜 H K a).csInf_eq.symm

theorem form_norm_zero_slots : Spec.FormNormZeroSlots.{u, v, w} := by
  intro 𝕜 H K _ _ _ _ _ a h
  rcases h with h | h
  · let := h
    exact a.opNorm_subsingleton
  · let := h
    have ha : a = 0 := by
      ext x y
      have hy : y = 0 := Subsingleton.elim _ _
      simp [hy]
    rw [ha]
    exact ContinuousLinearMap.opNorm_zero

theorem real_conventions : Spec.RealConventions.{v} := by
  intro H _ _ a α
  refine ⟨Iff.rfl, ?_⟩
  simp only [Spec.FormHermitianValue, conj_trivial]

theorem innerForm_apply : Spec.InnerFormEvaluation.{u, v} := by
  intro 𝕜 H _ _ _ x y
  rfl

theorem mem_orthogonalComplement : Spec.OrthogonalMembership.{u, v} := by
  intro 𝕜 H _ _ _ A y
  change y ∈ (Submodule.span 𝕜 A).orthogonal ↔ _
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h x hx
    exact h x (Submodule.subset_span hx)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => exact inner_zero_left y
    | add x z _ _ hx hz => rw [inner_add_left, hx, hz, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]

theorem orthogonalComplement_isClosed : Spec.OrthogonalClosed.{u, v} := by
  intro 𝕜 H _ _ _ A
  exact (Submodule.span 𝕜 A).isClosed_orthogonal

theorem orthogonalComplement_submodule : Spec.OrthogonalSubmodule.{u, v} := by
  intro 𝕜 H _ _ _ M
  change (Submodule.span 𝕜 (M : Set H)).orthogonal = M.orthogonal
  rw [Submodule.span_eq]

theorem closed_projection_exists : Spec.ClosedProjectionExists.{u, v} := by
  intro 𝕜 H _ _ _ _ M hM
  let : CompleteSpace M := hM.completeSpace_coe
  infer_instance

theorem orthogonalProjection_characterization : Spec.ProjectionCharacterization.{u, v} := by
  intro 𝕜 H _ _ _ M _ x
  exact ⟨M.starProjection_apply_mem x, M.sub_starProjection_mem_orthogonal x⟩

theorem realification_geometry : Spec.RealificationGeometry.{u, v} := by
  intro 𝕜 H _ _ _
  exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, rfl, rfl, fun _ _ => rfl⟩

end ExpandedFA.Hilbert.Conventions
