import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.FiniteDomainOperators
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01FiniteDimension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03OperatorNorm
import Mathlib.Tactic.Ring

/-! Finite-dimensional operator coordinates and uniform norm comparisons.
The constants below depend on the spaces, norms and bases, never on the map.
No unit sphere is assumed nonempty, so all arguments include dimension zero.
-/

noncomputable section
namespace ExpandedFA.P1.FiniteDomainOperators

theorem finite_domain_linear_maps_bounded : Spec.Boundedness := by
  intro 𝕜 E F _ _ _ _ _ _ T
  exact ⟨T.continuous_of_finiteDimensional, T.toContinuousLinearMap.bound⟩

theorem finite_matrix_coordinates : Spec.MatrixCoordinates := by
  intro 𝕜 E F _ _ _ _ _ n m b c T
  refine ⟨T.toMatrix_apply b c, T.toMatrix_mulVec_repr b c, ?_, ?_⟩
  · intro a
    have h := T.toMatrix_mulVec_repr b c (b.equivFun.symm a)
    have ha : (b.repr (b.equivFun.symm a) : Fin n → 𝕜) = a :=
      b.equivFun.apply_symm_apply a
    rw [ha] at h
    rw [← b.equivFun_symm_apply a, ← c.equivFun_symm_apply]
    simpa only [← Module.Basis.equivFun_apply, LinearEquiv.symm_apply_apply] using
      congrArg c.equivFun.symm h.symm
  · intro a
    apply (WithLp.linearEquiv 2 𝕜 (Fin m → 𝕜)).injective
    change c.equivFun (T (b.equivFun.symm (WithLp.ofLp a))) =
      (LinearMap.toMatrix b c T).mulVec (WithLp.ofLp a)
    have h := T.toMatrix_mulVec_repr b c (b.equivFun.symm (WithLp.ofLp a))
    simpa only [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using h.symm

theorem operator_norm_for_native : Spec.NativeNormFormula := by
  intro 𝕜 E F _ _ _ _ _ _ T
  exact T.toContinuousLinearMap.norm_def.symm

theorem operator_norm_for_isLeastBound : Spec.NormForIsLeastBound := by
  intro 𝕜 E F _ _ _ _ _ _ p q hp hq T
  let P := C01Norm.seminormOfAxioms 𝕜 E p hp.1
  let Q := C01Norm.seminormOfAxioms 𝕜 F q hq.1
  let : NormedAddCommGroup E := C01Norm.normedGroup P (fun x hx => (hp.2 x).mp hx)
  let : NormedSpace 𝕜 E :=
    { (inferInstance : Module 𝕜 E) with
      norm_smul_le := fun a x => (map_smul_eq_mul P a x).le }
  let : NormedAddCommGroup F := C01Norm.normedGroup Q (fun x hx => (hq.2 x).mp hx)
  let : NormedSpace 𝕜 F :=
    { (inferInstance : Module 𝕜 F) with
      norm_smul_le := fun a x => (map_smul_eq_mul Q a x).le }
  have hn : operatorNormFor p q T = ‖T.toContinuousLinearMap‖ :=
    T.toContinuousLinearMap.norm_def.symm
  rw [hn]
  exact ⟨⟨norm_nonneg _, T.toContinuousLinearMap.le_opNorm⟩,
    fun C hC => T.toContinuousLinearMap.opNorm_le_bound hC.1 hC.2⟩

/-- Substitution of two vector norm comparisons into the least-bound formula.
Only the domain is required finite-dimensional for this directed comparison. -/
theorem operator_norm_for_le_of_bounds {𝕜 E F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F]
    {p p' : E → ℝ} {q q' : F → ℝ}
    (hp : C01Norm.NormAxioms 𝕜 p) (hp' : C01Norm.NormAxioms 𝕜 p')
    (hq : C01Norm.NormAxioms 𝕜 q) (hq' : C01Norm.NormAxioms 𝕜 q')
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdom : ∀ x, p x ≤ A * p' x) (hcod : ∀ y, q' y ≤ B * q y)
    (T : E →ₗ[𝕜] F) :
    operatorNormFor p' q' T ≤ (B * A) * operatorNormFor p q T := by
  have hN := operator_norm_for_isLeastBound 𝕜 E F p q hp hq T
  apply (operator_norm_for_isLeastBound 𝕜 E F p' q' hp' hq' T).2
  refine ⟨mul_nonneg (mul_nonneg hB hA) hN.1.1, fun x => ?_⟩
  calc
    q' (T x) ≤ B * q (T x) := hcod _
    _ ≤ B * (operatorNormFor p q T * p x) := mul_le_mul_of_nonneg_left (hN.1.2 x) hB
    _ ≤ B * (operatorNormFor p q T * (A * p' x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hdom x) hN.1.1) hB
    _ = (B * A) * operatorNormFor p q T * p' x := by ring

theorem finite_operator_norm_change : Spec.NormChangeComparison := by
  intro 𝕜 E F _ _ _ _ _ _ _ p₁ p₂ q₁ q₂ hp₁ hp₂ hq₁ hq₂
  obtain ⟨_, _, A, hA, hdom⟩ :=
    C01FiniteDimension.finite_dimensional_norm_equivalence 𝕜 E p₂ p₁ hp₂ hp₁
  obtain ⟨_, _, B, hB, hcod⟩ :=
    C01FiniteDimension.finite_dimensional_norm_equivalence 𝕜 F q₁ q₂ hq₁ hq₂
  obtain ⟨_, _, D, hD, hdom'⟩ :=
    C01FiniteDimension.finite_dimensional_norm_equivalence 𝕜 E p₁ p₂ hp₁ hp₂
  obtain ⟨_, _, G, hG, hcod'⟩ :=
    C01FiniteDimension.finite_dimensional_norm_equivalence 𝕜 F q₂ q₁ hq₂ hq₁
  refine ⟨(G * D)⁻¹, inv_pos.mpr (mul_pos hG hD), B * A, mul_pos hB hA,
    fun T => ⟨?_, ?_⟩⟩
  · apply (inv_mul_le_iff₀ (mul_pos hG hD)).mpr
    exact operator_norm_for_le_of_bounds hp₂ hp₁ hq₂ hq₁ hD.le hG.le
      (fun x => (hdom' x).2) (fun y => (hcod' y).2) T
  · exact operator_norm_for_le_of_bounds hp₁ hp₂ hq₁ hq₂ hA.le hB.le
      (fun x => (hdom x).2) (fun y => (hcod y).2) T

/-- Pulling back a genuine norm along a linear equivalence gives exactly the
manuscript norm axioms, without imposing a topology on the domain. -/
theorem norm_axioms_of_linearEquiv {𝕜 E G : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (e : E ≃ₗ[𝕜] G) : C01Norm.NormAxioms 𝕜 (fun x => ‖e x‖) := by
  refine ⟨⟨fun x => norm_nonneg _, ?_, ?_⟩, ?_⟩
  · intro a x
    change ‖e (a • x)‖ = ‖a‖ * ‖e x‖
    rw [map_smul, norm_smul]
  · intro x y
    change ‖e (x + y)‖ ≤ ‖e x‖ + ‖e y‖
    rw [map_add]
    exact norm_add_le _ _
  · intro x
    rw [norm_eq_zero, ← e.map_zero]
    exact e.injective.eq_iff

/-- Coordinate transport of the operator norm uses every vector, via the
surjectivity of the domain coordinate equivalence. -/
theorem operator_norm_for_coordinates {𝕜 E F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
    {n m : ℕ} (b : Module.Basis (Fin n) 𝕜 E) (d : Module.Basis (Fin m) 𝕜 F)
    (T : E →ₗ[𝕜] F) :
    operatorNormFor (fun x => ‖euclideanCoordinates b x‖)
      (fun y => ‖euclideanCoordinates d y‖) T =
      ‖(operatorInCoordinates b d T).toContinuousLinearMap‖ := by
  rw [ContinuousLinearMap.norm_def]
  unfold operatorNormFor
  congr 1
  ext C
  constructor
  · rintro ⟨hC, h⟩
    refine ⟨hC, fun a => ?_⟩
    simpa [operatorInCoordinates] using h ((euclideanCoordinates b).symm a)
  · rintro ⟨hC, h⟩
    refine ⟨hC, fun x => ?_⟩
    simpa [operatorInCoordinates] using h (euclideanCoordinates b x)

theorem finite_coordinate_norm_comparison :
    Spec.CoordinateNormComparison := by
  intro 𝕜 E F _ _ _ _ _ n m b d
  let := b.finiteDimensional_of_finite
  let := d.finiteDimensional_of_finite
  obtain ⟨c, hc, C, hC, h⟩ := finite_operator_norm_change 𝕜 E F
    norm (fun x => ‖euclideanCoordinates b x‖)
    norm (fun y => ‖euclideanCoordinates d y‖)
    (C01Norm.canonical_norm_axioms 𝕜 E) (norm_axioms_of_linearEquiv _)
    (C01Norm.canonical_norm_axioms 𝕜 F) (norm_axioms_of_linearEquiv _)
  refine ⟨c, hc, C, hC, fun T => ?_⟩
  simpa only [operator_norm_for_native 𝕜 E F T, operator_norm_for_coordinates] using h T

theorem finite_basis_change_comparison : Spec.BasisChangeComparison := by
  intro 𝕜 E F _ _ _ _ _ n₁ n₂ m₁ m₂ b₁ b₂ d₁ d₂
  let := b₁.finiteDimensional_of_finite
  let := d₁.finiteDimensional_of_finite
  obtain ⟨c, hc, C, hC, h⟩ := finite_operator_norm_change 𝕜 E F
    (fun x => ‖euclideanCoordinates b₁ x‖) (fun x => ‖euclideanCoordinates b₂ x‖)
    (fun y => ‖euclideanCoordinates d₁ y‖) (fun y => ‖euclideanCoordinates d₂ y‖)
    (norm_axioms_of_linearEquiv _) (norm_axioms_of_linearEquiv _)
    (norm_axioms_of_linearEquiv _) (norm_axioms_of_linearEquiv _)
  refine ⟨c, hc, C, hC, fun T => ?_⟩
  simpa only [operator_norm_for_coordinates] using h T

end ExpandedFA.P1.FiniteDomainOperators
