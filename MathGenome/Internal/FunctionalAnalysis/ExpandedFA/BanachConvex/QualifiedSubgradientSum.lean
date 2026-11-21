import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.QualifiedSubgradientSum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.SubgradientBasicCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.FenchelRockafellar
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

namespace ExpandedFA.BanachConvex
open P1.ExtendedConvexFunctions Set
open scoped Pointwise
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The unconditional inclusion needs neither convexity nor properness. -/
theorem subdifferential_sum_inclusion : SumSpec.SumInclusion.{u} := by
  intro X _ _ φ ψ x f hf
  obtain ⟨g, hg, h, hh, rfl⟩ := hf
  change (φ x + ψ x ≠ ⊤) ∧ _
  refine ⟨WithTop.add_ne_top.mpr ⟨hg.1, hh.1⟩, ?_⟩
  intro y
  have h := add_le_add (hg.2 y) (hh.2 y)
  simpa only [Pi.add_apply, add_apply, WithTop.coe_add, add_add_add_comm] using h

/-- Subtract a continuous linear function from an extended convex function. -/
def subtractLinear (φ : ExtendedFunction X) (f : X →L[ℝ] ℝ) : ExtendedFunction X :=
  fun y => φ y + ((-f y : ℝ) : WithTop ℝ)

lemma subtractLinear_finite (φ : ExtendedFunction X) (f : X →L[ℝ] ℝ) (y : X) :
    subtractLinear φ f y ≠ ⊤ ↔ φ y ≠ ⊤ := by
  simp [subtractLinear]

lemma subtractLinear_value (φ : ExtendedFunction X) (f : X →L[ℝ] ℝ)
    (y : X) (s : ℝ) (hy : subtractLinear φ f y = (s : WithTop ℝ)) :
    φ y = ((s + f y : ℝ) : WithTop ℝ) := by
  have hn : φ y ≠ ⊤ := (subtractLinear_finite φ f y).mp (hy ▸ WithTop.coe_ne_top)
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hn
  simp only [subtractLinear, ← ht, ← WithTop.coe_add, WithTop.coe_inj] at hy
  rw [← ht]
  congr 1
  linarith

lemma subtractLinear_convex (φ : ExtendedFunction X) (f : X →L[ℝ] ℝ)
    (hc : P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ) :
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X (subtractLinear φ f) := by
  intro x y r s a b hx hy ha hb hab
  have h := hc x y (r + f x) (s + f y) a b
    (subtractLinear_value φ f x r hx) (subtractLinear_value φ f y s hy) ha hb hab
  have h' := add_le_add h (le_refl (((-f (a • x + b • y) : ℝ) : WithTop ℝ)))
  change subtractLinear φ f (a • x + b • y) ≤ _ at h'
  convert h' using 1
  simp only [← WithTop.coe_add, map_add, map_smul, smul_eq_mul]
  congr 1
  ring

/-- The continuity qualification supplies a decomposition of every sum
subgradient. Separation is applied to φ and ψ minus the given functional. -/
theorem subdifferential_sum_qualified : SumSpec.QualifiedSum.{u} := by
  intro X _ _ φ ψ _ _ hcφ hcψ x₀ hx₀ hy₀ hcont x
  change subdifferential X (φ + ψ) x = subdifferential X φ x + subdifferential X ψ x
  apply subset_antisymm
  · intro f hf
    have hfin : φ x ≠ ⊤ ∧ ψ x ≠ ⊤ := WithTop.add_ne_top.mp hf.1
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfin.1
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hfin.2
    obtain ⟨r₀, hr₀⟩ := WithTop.ne_top_iff_exists.mp hx₀
    obtain ⟨s₀, hs₀⟩ := WithTop.ne_top_iff_exists.mp hy₀
    have hbase : (φ + ψ) x = ((r + s : ℝ) : WithTop ℝ) := by
      simp only [Pi.add_apply, ← hr, ← hs, WithTop.coe_add]
    have hbound := (mem_subdifferential_iff_of_value (φ + ψ) x (r + s) hbase f).mp hf
    let a := r + s - f x
    have ha : ∀ (y : X) (r' s' : ℝ), φ y = (r' : WithTop ℝ) →
        subtractLinear ψ f y = (s' : WithTop ℝ) → a ≤ r' + s' := by
      intro y r' s' hy hz
      have hψ := subtractLinear_value ψ f y s' hz
      have h := hbound y (r' + (s' + f y)) (by
        simp only [Pi.add_apply, hy, hψ, WithTop.coe_add])
      rw [map_sub] at h
      dsimp [a]
      linarith
    obtain ⟨g, c, hφ, hψ⟩ := P1.FenchelRockafellar.affine_minorants_of_lower_bound
      φ (subtractLinear ψ f) hcφ (subtractLinear_convex ψ f hcψ)
      x₀ r₀ (s₀ - f x₀) hr₀.symm (by
        simp only [subtractLinear, ← hs₀, sub_eq_add_neg, WithTop.coe_add]) hcont a ha
    have hp : g x + c ≤ r := by
      have h := hφ x
      rwa [← hr, WithTop.coe_le_coe] at h
    have hq : -g x + (a - c) ≤ s - f x := by
      have h := hψ x
      simpa only [subtractLinear, ← hs, ← WithTop.coe_add, WithTop.coe_le_coe,
        sub_eq_add_neg] using h
    have heq : g x + c = r := by dsimp [a] at hq; linarith
    refine ⟨g, ?_, f - g, ?_, by abel_nf⟩
    · apply (mem_subdifferential_iff_of_value φ x r hr.symm g).mpr
      intro y t ht
      have h := hφ y
      rw [ht, WithTop.coe_le_coe] at h
      rw [map_sub]
      linarith
    · apply (mem_subdifferential_iff_of_value ψ x s hs.symm (f - g)).mpr
      intro y t ht
      have h := hψ y
      simp only [subtractLinear, ht, ← WithTop.coe_add, WithTop.coe_le_coe] at h
      simp only [sub_apply, map_sub]
      dsimp [a] at h
      linarith
  · exact subdifferential_sum_inclusion X φ ψ x

/-- The specified negative-square-root function, extended by +∞. -/
noncomputable def negativeSqrtExample : SumSpec.SqrtExampleType :=
  SumSpec.SqrtExampleValue

/-- The convex indicator of the singleton {0}. -/
noncomputable def zeroIndicatorExample : SumSpec.PointIndicatorType :=
  SumSpec.PointIndicatorValue

private lemma sqrtExample_zero : negativeSqrtExample 0 = 0 := by
  simp [negativeSqrtExample, SumSpec.SqrtExampleValue]

private lemma indicatorExample_zero : zeroIndicatorExample 0 = 0 := by
  simp [zeroIndicatorExample, SumSpec.PointIndicatorValue]

lemma negativeSqrtExample_convex :
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue ℝ negativeSqrtExample := by
  intro x y r s a b hx hy ha hb hab
  have hx0 : 0 ≤ x := by
    by_contra hn
    simp [negativeSqrtExample, SumSpec.SqrtExampleValue, hn] at hx
  have hy0 : 0 ≤ y := by
    by_contra hn
    simp [negativeSqrtExample, SumSpec.SqrtExampleValue, hn] at hy
  have hr : -Real.sqrt x = r := by
    simpa only [negativeSqrtExample, SumSpec.SqrtExampleValue, ite_eq_left hx0,
      WithTop.coe_inj] using hx
  have hs : -Real.sqrt y = s := by
    simpa only [negativeSqrtExample, SumSpec.SqrtExampleValue, ite_eq_left hy0,
      WithTop.coe_inj] using hy
  have hz : 0 ≤ a • x + b • y := by
    simpa only [smul_eq_mul] using add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0)
  simp only [negativeSqrtExample, SumSpec.SqrtExampleValue, ite_eq_left hz, WithTop.coe_le_coe]
  have h := Real.strictConcaveOn_sqrt.concaveOn.2 hx0 hy0 ha hb hab
  simp only [smul_eq_mul] at h ⊢
  rw [← hr, ← hs]
  linarith

lemma zeroIndicatorExample_convex :
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue ℝ zeroIndicatorExample := by
  intro x y r s a b hx hy ha hb hab
  have hx0 : x = 0 := by
    by_contra hn
    simp [zeroIndicatorExample, SumSpec.PointIndicatorValue, hn] at hx
  have hy0 : y = 0 := by
    by_contra hn
    simp [zeroIndicatorExample, SumSpec.PointIndicatorValue, hn] at hy
  subst x
  subst y
  have hr : r = 0 := by
    simpa only [indicatorExample_zero, ← WithTop.coe_zero, WithTop.coe_inj, eq_comm] using hx
  have hs : s = 0 := by
    simpa only [indicatorExample_zero, ← WithTop.coe_zero, WithTop.coe_inj, eq_comm] using hy
  simp [hr, hs, indicatorExample_zero]

lemma example_sum_eq_indicator : negativeSqrtExample + zeroIndicatorExample =
    zeroIndicatorExample := by
  ext t
  by_cases ht : t = 0
  · subst t
    simp [sqrtExample_zero, indicatorExample_zero]
  · simp [zeroIndicatorExample, SumSpec.PointIndicatorValue, ht]

/-- An arbitrarily small positive square contradicts every finite slope
supporting -sqrt at zero. -/
lemma negativeSqrtExample_subdifferential_zero :
    subdifferential ℝ negativeSqrtExample 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro f hf
  let t : ℝ := (|f 1| + 1)⁻¹
  have hden : 0 < |f 1| + 1 := by positivity
  have ht : 0 < t := inv_pos.mpr hden
  have hid : (|f 1| + 1) * t = 1 := mul_inv_cancel₀ (ne_of_gt hden)
  have hft : -1 < f 1 * t := by
    have h := mul_le_mul_of_nonneg_right (neg_abs_le (f 1)) ht.le
    nlinarith
  have hv : negativeSqrtExample (t ^ 2) = ((-t : ℝ) : WithTop ℝ) := by
    simp [negativeSqrtExample, SumSpec.SqrtExampleValue, sq_nonneg, Real.sqrt_sq ht.le]
  have h := (mem_subdifferential_iff_of_value negativeSqrtExample 0 0
    (by simpa using sqrtExample_zero) f).mp hf (t ^ 2) (-t) hv
  have hfy : f (t ^ 2) = t ^ 2 * f 1 := by
    simpa only [smul_eq_mul, mul_one] using f.map_smul (t ^ 2) (1 : ℝ)
  simp only [sub_zero, zero_add, hfy] at h
  nlinarith [mul_pos (show 0 < 1 + f 1 * t by linarith) ht]

lemma zeroIndicatorExample_subdifferential_zero :
    subdifferential ℝ zeroIndicatorExample 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro f
  apply (mem_subdifferential_iff_of_value zeroIndicatorExample 0 0
    (by simpa using indicatorExample_zero) f).mpr
  intro y s hy
  have hy0 : y = 0 := by
    by_contra hn
    simp [zeroIndicatorExample, SumSpec.PointIndicatorValue, hn] at hy
  subst y
  have hs : s = 0 := by
    simpa only [indicatorExample_zero, ← WithTop.coe_zero, WithTop.coe_inj, eq_comm] using hy
  simp [hs]

/-- The manuscript's strict-inclusion example uses proper convex functions. -/
theorem subdifferential_sum_strict_example : SumSpec.StrictExample := by
  change P1.ExtendedConvexFunctions.Spec.ProperValue ℝ negativeSqrtExample ∧
    P1.ExtendedConvexFunctions.Spec.ProperValue ℝ zeroIndicatorExample ∧
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue ℝ negativeSqrtExample ∧
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue ℝ zeroIndicatorExample ∧
    negativeSqrtExample + zeroIndicatorExample = zeroIndicatorExample ∧
    subdifferential ℝ negativeSqrtExample 0 = ∅ ∧
    subdifferential ℝ (negativeSqrtExample + zeroIndicatorExample) 0 = Set.univ ∧
    subdifferential ℝ negativeSqrtExample 0 + subdifferential ℝ zeroIndicatorExample 0 ⊂
      subdifferential ℝ (negativeSqrtExample + zeroIndicatorExample) 0
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, negativeSqrtExample_convex, zeroIndicatorExample_convex,
    example_sum_eq_indicator, negativeSqrtExample_subdifferential_zero, ?_, ?_⟩
  · change negativeSqrtExample 0 ≠ ⊤
    simp [sqrtExample_zero]
  · change zeroIndicatorExample 0 ≠ ⊤
    simp [indicatorExample_zero]
  · rw [example_sum_eq_indicator, zeroIndicatorExample_subdifferential_zero]
  · rw [negativeSqrtExample_subdifferential_zero, Set.empty_add,
      example_sum_eq_indicator, zeroIndicatorExample_subdifferential_zero]
    exact Set.empty_ssubset.mpr ⟨0, Set.mem_univ _⟩

end ExpandedFA.BanachConvex
