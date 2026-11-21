import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.AffineMinorants
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.ExtendedConvexFunctions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06StrongSeparation
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic.Linarith

/-! Affine minorants of proper closed convex functions, including infinite values. -/
noncomputable section
namespace ExpandedFA.P1.AffineMinorants
open Set ExpandedFA.P1.ExtendedConvexFunctions
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Split a separating functional on the real normed product into its two
coordinates. Upward closure of the epigraph forces the vertical coefficient
nonnegative; it need not be positive. -/
lemma epigraph_separator (φ : ExtendedFunction E)
    (hp : Proper E φ) (hc : ExtendedConvex E φ) (hl : LowerSemicontinuous E φ)
    (x : E) (t : ℝ) (ht : (t : WithTop ℝ) < φ x) :
    ∃ (ℓ : E →L[ℝ] ℝ) (b α : ℝ), 0 ≤ b ∧ ℓ x + b * t < α ∧
      ∀ (y : E) (s : ℝ), φ y ≤ (s : WithTop ℝ) → α ≤ ℓ y + b * s := by
  obtain ⟨x₁, r₁, hr₁⟩ := (proper_iff_finite_value E φ).mp hp
  have hne : (realEpigraph E φ).Nonempty := ⟨(x₁, r₁), hr₁.le⟩
  have hclosed := (lowerSemicontinuous_iff_closed_epigraph E φ).mp hl
  have hconv := (convex_iff_convex_epigraph E φ).mp hc
  obtain ⟨f, _, hbd, hlt⟩ := C06.real_point_strong_separation
    (realEpigraph E φ) (x, t) hne hclosed hconv (not_le_of_gt ht)
  let L : (E × ℝ) →L[ℝ] ℝ := -f
  let ℓ : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let b : ℝ := L (0, 1)
  let α : ℝ := -sSup (f '' realEpigraph E φ)
  have hsplit (y : E) (s : ℝ) : L (y, s) = ℓ y + b * s := by
    have heq : (y, s) = (y, 0) + s • (0, (1 : ℝ)) := by ext <;> simp
    rw [heq, map_add, map_smul]
    simp [ℓ, b, mul_comm]
  have hsep (y : E) (s : ℝ) (hs : φ y ≤ (s : WithTop ℝ)) : α ≤ ℓ y + b * s := by
    rw [← hsplit]
    exact neg_le_neg (le_csSup hbd ⟨(y, s), hs, rfl⟩)
  have hgap : ℓ x + b * t < α := by
    rw [← hsplit]
    exact neg_lt_neg hlt
  have hb : 0 ≤ b := by
    by_contra hn
    have hbneg : b < 0 := lt_of_not_ge hn
    let d : ℝ := ℓ x₁ + b * r₁ - α
    have hd : 0 ≤ d := by dsimp [d]; linarith [hsep x₁ r₁ hr₁.le]
    let k : ℝ := (d + 1) / (-b)
    have hk : 0 < k := div_pos (by linarith) (neg_pos.mpr hbneg)
    have hbk : b * k = -(d + 1) := by
      dsimp [k]
      field_simp [hbneg.ne]
    have hs : φ x₁ ≤ ((r₁ + k : ℝ) : WithTop ℝ) :=
      hr₁.le.trans (WithTop.coe_le_coe.mpr (by linarith))
    have hh := hsep x₁ (r₁ + k) hs
    dsimp [d] at hbk
    nlinarith
  exact ⟨ℓ, b, α, hb, hgap, hsep⟩

/-- A finite domain point rules out a vertical separator and supplies the
first affine minorant. -/
theorem exists_continuous_affine_minorant : Spec.Existence := by
  intro E _ _ φ hp hc hl
  obtain ⟨x₁, r₁, hr₁⟩ := (proper_iff_finite_value E φ).mp hp
  obtain ⟨ℓ, b, α, hb, hgap, hsep⟩ := epigraph_separator φ hp hc hl x₁ (r₁ - 1)
    (by rw [hr₁]; exact WithTop.coe_lt_coe.mpr (by linarith))
  have hbpos : 0 < b := by
    have hh := hsep x₁ r₁ hr₁.le
    nlinarith
  refine ⟨(-b⁻¹) • ℓ, α / b, ?_⟩
  intro y
  by_cases hy : φ y = ⊤
  · simp [hy]
  · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
    rw [← hs]
    apply WithTop.coe_le_coe.mpr
    have hh := hsep y s hs.ge
    change (-b⁻¹) * ℓ y + α / b ≤ s
    have heq : -b⁻¹ * ℓ y + α / b = (α - ℓ y) / b := by
      simp only [div_eq_mul_inv]; ring
    rw [heq]
    exact (div_le_iff₀ hbpos).mpr (by linarith)

/-- Perturb a possibly vertical separator by the known affine minorant.
On the epigraph the correction is nonnegative, while at the chosen point
its coefficient can be chosen small enough to preserve the strict gap. -/
theorem continuous_affine_minorant_above : Spec.StrictApproximation := by
  intro E _ _ φ hp hc hl x t ht
  obtain ⟨h₀, c₀, hm₀⟩ := exists_continuous_affine_minorant E φ hp hc hl
  obtain ⟨ℓ, b, α, hb, hgap, hsep⟩ := epigraph_separator φ hp hc hl x t ht
  obtain ⟨ε, hε, hsmall⟩ := exists_pos_mul_lt
    (show 0 < α - (ℓ x + b * t) by linarith) (t - (h₀ x + c₀))
  let B : ℝ := b + ε
  have hB : 0 < B := by dsimp [B]; linarith
  let h : E →L[ℝ] ℝ := B⁻¹ • (ε • h₀ - ℓ)
  let c : ℝ := (α + ε * c₀) / B
  have heval (y : E) : h y + c = (α + ε * c₀ - ℓ y + ε * h₀ y) / B := by
    simp only [h, c, smul_apply, sub_apply,
      smul_eq_mul, div_eq_mul_inv]
    ring
  refine ⟨h, c, ?_, ?_⟩
  · intro y
    by_cases hy : φ y = ⊤
    · simp [hy]
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
      rw [← hs]
      apply WithTop.coe_le_coe.mpr
      rw [heval]
      apply (div_le_iff₀ hB).mpr
      have hm : h₀ y + c₀ ≤ s := WithTop.coe_le_coe.mp (by simpa [hs] using hm₀ y)
      have hh := hsep y s hs.ge
      dsimp [B]
      nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hm)]
  · rw [heval]
    apply (lt_div_iff₀ hB).mpr
    dsimp [B]
    nlinarith

/-- The full supremum assertion in the extended codomain: in particular,
minorant values are unbounded above wherever `φ x = +∞`. -/
theorem continuous_affine_minorants_isLUB : Spec.PointwiseSupremum := by
  intro E _ _ φ hp hc hl x
  constructor
  · rintro r ⟨h, c, hm, rfl⟩
    exact hm x
  · intro r hr
    by_contra hn
    have hlt : r < φ x := lt_of_not_ge hn
    obtain ⟨t, hrt, htf⟩ := WithTop.lt_iff_exists_coe_btwn.mp hlt
    obtain ⟨h, c, hm, htc⟩ := continuous_affine_minorant_above E φ hp hc hl x t htf
    have hbound := hr ⟨h, c, hm, rfl⟩
    exact (not_lt_of_ge hbound) (hrt.trans (WithTop.coe_lt_coe.mpr htc))

end ExpandedFA.P1.AffineMinorants
