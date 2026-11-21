import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06Bipolar
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06Polars
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06StrongSeparation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03OperatorNorm
import Mathlib.Tactic.FieldSimp

/-! Elementary polar identities from `fa2:p1:c06:bipolar`. The closed hull is the
shared finite-sum hull followed by norm closure; the proof also handles ∅. -/

namespace ExpandedFA.P1.C06Bipolar
open C06Polars

universe u v w
open scoped BigOperators Pointwise ComplexConjugate

theorem polar_antitone : Spec.PolarAntitone := by
  intro 𝕜 E _ _ _ A C h f hf a ha
  exact hf a (h ha)

theorem prepolar_antitone : Spec.PrepolarAntitone := by
  intro 𝕜 E _ _ _ B D h x hx f hf
  exact hx f (h hf)

theorem polar_iUnion : Spec.PolarUnion := by
  intro 𝕜 E _ _ _ I A
  ext f
  change (∀ a ∈ ⋃ i, A i, ‖f a‖ ≤ 1) ↔ _
  simp only [Set.mem_iUnion, Set.mem_iInter, C06Polars.Spec.PolarValue,
    Set.mem_ofPred_eq]
  constructor
  · intro h i a ha
    exact h a ⟨i, ha⟩
  · rintro h a ⟨i, ha⟩
    exact h i a ha

theorem prepolar_iUnion : Spec.PrepolarUnion := by
  intro 𝕜 E _ _ _ I B
  ext x
  change (∀ f ∈ ⋃ i, B i, ‖f x‖ ≤ 1) ↔ _
  simp only [Set.mem_iUnion, Set.mem_iInter, C06Polars.Spec.PrepolarValue,
    Set.mem_ofPred_eq]
  constructor
  · intro h i f hf
    exact h f ⟨i, hf⟩
  · rintro h f ⟨i, hf⟩
    exact h i f hf

/-- A modulus bound passes to the zero-inclusive finite-sum hull. -/
theorem norm_apply_le_one_on_absolutelyConvexHull
    (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f : E →L[𝕜] 𝕜) (A : Set E) (h : ∀ a ∈ A, ‖f a‖ ≤ 1) :
    ∀ x ∈ absolutelyConvexHull 𝕜 E A, ‖f x‖ ≤ 1 := by
  rintro x ⟨n, c, y, hy, hc, rfl⟩
  calc
    ‖f (∑ i, c i • y i)‖ = ‖∑ i, c i * f (y i)‖ := by simp
    _ ≤ ∑ i, ‖c i * f (y i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖c i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (h _ (hy i))
    _ ≤ 1 := hc

/-- Continuity passes the same bound to the norm closure. -/
theorem norm_apply_le_one_on_closedAbsolutelyConvexHull
    (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f : E →L[𝕜] 𝕜) (A : Set E) (h : ∀ a ∈ A, ‖f a‖ ≤ 1) :
    ∀ x ∈ closedAbsolutelyConvexHull 𝕜 E A, ‖f x‖ ≤ 1 := by
  exact closure_minimal (norm_apply_le_one_on_absolutelyConvexHull 𝕜 E f A h)
    (isClosed_le f.continuous.norm continuous_const)

theorem polar_closedAbsolutelyConvexHull : Spec.PolarClosedHull := by
  intro 𝕜 E _ _ _ A
  apply Set.Subset.antisymm
  · apply polar_antitone 𝕜 E
    intro x hx
    exact subset_closure (subset_absolutelyConvexHull 𝕜 E A hx)
  · intro f hf
    exact norm_apply_le_one_on_closedAbsolutelyConvexHull 𝕜 E f A hf

theorem prepolar_closedAbsolutelyConvexHull : Spec.PrepolarClosedHull := by
  intro 𝕜 E _ _ _ B
  apply Set.Subset.antisymm
  · apply prepolar_antitone 𝕜 E
    intro f hf
    exact subset_closure (subset_absolutelyConvexHull 𝕜 (E →L[𝕜] 𝕜) B hf)
  · intro x hx
    exact norm_apply_le_one_on_closedAbsolutelyConvexHull 𝕜 (E →L[𝕜] 𝕜)
      (ContinuousLinearMap.apply 𝕜 𝕜 x) B hx

/-- The scaling identity even holds for any nonzero scalar. -/
theorem polar_smul (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A : Set E) (a : 𝕜) (ha : a ≠ 0) :
    polar 𝕜 E (a • A) = a⁻¹ • polar 𝕜 E A := by
  ext f
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero ha), inv_inv]
  constructor
  · intro hf x hx
    simpa only [smul_apply, smul_eq_mul, map_smul] using
      hf (a • x) (Set.smul_mem_smul_set hx)
  · rintro hf y ⟨x, hx, rfl⟩
    simpa only [smul_apply, smul_eq_mul, map_smul] using hf x hx

theorem prepolar_smul (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (B : Set (E →L[𝕜] 𝕜)) (a : 𝕜) (ha : a ≠ 0) :
    prepolar 𝕜 E (a • B) = a⁻¹ • prepolar 𝕜 E B := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero ha), inv_inv]
  constructor
  · intro hx f hf
    simpa only [smul_apply, smul_eq_mul, map_smul] using
      hx (a • f) (Set.smul_mem_smul_set hf)
  · rintro hx g ⟨f, hf, rfl⟩
    simpa only [smul_apply, smul_eq_mul, map_smul] using hx f hf

theorem polar_smul_pos : Spec.PolarScaling := by
  intro 𝕜 E _ _ _ A r hr
  exact polar_smul 𝕜 E A (r : 𝕜) (by exact_mod_cast hr.ne')

theorem prepolar_smul_pos : Spec.PrepolarScaling := by
  intro 𝕜 E _ _ _ B r hr
  exact prepolar_smul 𝕜 E B (r : 𝕜) (by exact_mod_cast hr.ne')

theorem polar_closed_unit_ball : Spec.PolarClosedUnitBall := by
  intro 𝕜 E _ _ _
  ext f
  change (∀ x ∈ Metric.closedBall (0 : E) 1, ‖f x‖ ≤ 1) ↔ _
  simp only [Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro hf
    rw [C03OperatorNorm.operator_norm_supremum 𝕜 E 𝕜 f]
    apply csSup_le (C03OperatorNorm.operator_unit_ball_nonempty 𝕜 E 𝕜 f).2
    rintro _ ⟨x, hx, rfl⟩
    exact hf x hx
  · intro hf x hx
    exact (f.unit_le_opNorm x hx).trans hf

/-- Balance turns an upper bound on real parts into the same modulus bound. -/
theorem norm_apply_le_of_re_le_on_balanced
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {C : Set E} (hC : Balanced 𝕜 C) (f : E →L[𝕜] 𝕜) {s : ℝ}
    (hs : 0 ≤ s) (hf : ∀ c ∈ C, RCLike.re (f c) ≤ s) :
    ∀ c ∈ C, ‖f c‖ ≤ s := by
  intro c hc
  by_cases hzero : f c = 0
  · simpa [hzero] using hs
  let a : 𝕜 := (‖f c‖ : 𝕜)⁻¹ * conj (f c)
  have ha : ‖a‖ ≤ 1 := by
    simp [a, norm_mul, norm_inv, norm_ne_zero_iff.mpr hzero]
  have hb := hf (a • c) (hC.smul_mem ha hc)
  have heq : RCLike.re (f (a • c)) = ‖f c‖ := by
    rw [map_smul, smul_eq_mul]
    dsimp only [a]
    rw [mul_assoc, RCLike.conj_mul, ← RCLike.ofReal_inv, ← RCLike.ofReal_pow,
      ← RCLike.ofReal_mul, RCLike.ofReal_re]
    field_simp
  rwa [heq] at hb

/-- The double polar equals the norm closure of the zero-inclusive finite-sum hull. -/
theorem bipolar_theorem : Spec.BipolarTheorem := by
  intro 𝕜 E _ _ _ A
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  change prepolar 𝕜 E (polar 𝕜 E A) = closedAbsolutelyConvexHull 𝕜 E A
  apply Set.Subset.antisymm
  · intro x hx
    by_contra houtside
    let C := closedAbsolutelyConvexHull 𝕜 E A
    have hzero : (0 : E) ∈ C :=
      subset_closure (zero_mem_absolutelyConvexHull 𝕜 E A)
    have hconv : Convex ℝ C := (absolutelyConvexHull_isAbsolutelyConvex 𝕜 E A).1.closure
    have hbal : Balanced 𝕜 C := (absolutelyConvexHull_isAbsolutelyConvex 𝕜 E A).2.closure
    obtain ⟨h, _, hbd, hlt⟩ := C06.real_point_strong_separation C x
      ⟨0, hzero⟩ isClosed_closure hconv houtside
    let f : E →L[𝕜] 𝕜 := StrongDual.extendRCLike h
    have hre (y : E) : RCLike.re (f y) = h y :=
      StrongDual.re_extendRCLike_apply h y
    let s := sSup (h '' C)
    have hs : 0 ≤ s := by
      simpa using (le_csSup hbd (Set.mem_image_of_mem h hzero))
    have hbound : ∀ c ∈ C, ‖f c‖ ≤ s := by
      apply norm_apply_le_of_re_le_on_balanced hbal f hs
      intro c hc
      rw [hre]
      exact le_csSup hbd (Set.mem_image_of_mem h hc)
    let t : ℝ := (s + h x) / 2
    have hst : s < t := by dsimp [t, s]; linarith
    have htx : t < h x := by dsimp [t, s]; linarith
    have ht : 0 < t := hs.trans_lt hst
    let g : E →L[𝕜] 𝕜 := (t : 𝕜)⁻¹ • f
    have hg : g ∈ polar 𝕜 E A := by
      intro a ha
      change ‖(t : 𝕜)⁻¹ * f a‖ ≤ 1
      rw [norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_pos ht]
      apply (inv_mul_le_iff₀ ht).mpr
      simpa using (hbound a (subset_closure (subset_absolutelyConvexHull 𝕜 E A ha))).trans hst.le
    have hgx := hx g hg
    change ‖(t : 𝕜)⁻¹ * f x‖ ≤ 1 at hgx
    rw [norm_mul, norm_inv, RCLike.norm_ofReal, abs_of_pos ht] at hgx
    have hfx : ‖f x‖ ≤ t := by
      simpa using (inv_mul_le_iff₀ ht).mp hgx
    have := RCLike.re_le_norm (f x)
    rw [hre] at this
    exact (htx.trans_le (this.trans hfx)).false
  · intro x hx f hf
    exact norm_apply_le_one_on_closedAbsolutelyConvexHull 𝕜 E f A hf x hx

end ExpandedFA.P1.C06Bipolar
