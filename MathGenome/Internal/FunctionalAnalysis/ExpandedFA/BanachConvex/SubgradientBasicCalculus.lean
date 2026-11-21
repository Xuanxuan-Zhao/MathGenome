import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.SubgradientBasicCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Asplund.NormSquareConjugate
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01Norm
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ExpandedFA.BanachConvex

open P1.ExtendedConvexFunctions P1.C06Conjugates
open Filter Set
open scoped Topology

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma mem_subdifferential_iff_of_value (φ : ExtendedFunction X) (x : X) (r : ℝ)
    (hx : φ x = (r : WithTop ℝ)) (f : X →L[ℝ] ℝ) :
    f ∈ subdifferential X φ x ↔
      ∀ (y : X) (s : ℝ), φ y = (s : WithTop ℝ) → r + f (y - x) ≤ s := by
  change (φ x ≠ ⊤ ∧ ∀ y, φ x + (f (y - x) : WithTop ℝ) ≤ φ y) ↔ _
  rw [hx]
  simp only [← WithTop.coe_add]
  constructor
  · rintro ⟨_, h⟩ y s hy
    simpa only [hy, WithTop.coe_le_coe] using h y
  · intro h
    refine ⟨WithTop.coe_ne_top, ?_⟩
    intro y
    by_cases hy : φ y = ⊤
    · simp [hy]
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
      simpa only [← hs, WithTop.coe_le_coe] using h y s hs.symm

lemma subdifferential_eq_iInter (φ : ExtendedFunction X) (x : X) (r : ℝ)
    (hx : φ x = (r : WithTop ℝ)) :
    subdifferential X φ x = ⋂ y : X, ⋂ s : ℝ, ⋂ (_ : φ y = (s : WithTop ℝ)),
      {f : X →L[ℝ] ℝ | r + f (y - x) ≤ s} := by
  ext f
  simp only [mem_iInter, mem_ofPred_eq, mem_subdifferential_iff_of_value φ x r hx]

theorem subdifferential_closed_convex : BasicCalculusSpec.ClosedConvex.{u} := by
  intro X _ _ φ x
  by_cases hx : φ x = ⊤
  · change IsClosed (subdifferential X φ x) ∧ Convex ℝ (subdifferential X φ x)
    have he : subdifferential X φ x = ∅ := subdifferential_at_infinity X φ x hx
    rw [he]
    exact ⟨isClosed_empty, convex_empty⟩
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx
    change IsClosed (subdifferential X φ x) ∧ Convex ℝ (subdifferential X φ x)
    rw [subdifferential_eq_iInter φ x r hr.symm]
    constructor
    · apply isClosed_iInter; intro y
      apply isClosed_iInter; intro s
      apply isClosed_iInter; intro _
      exact isClosed_le (continuous_const.add (ContinuousLinearMap.apply ℝ ℝ (y - x)).continuous)
        continuous_const
    · apply convex_iInter; intro y
      apply convex_iInter; intro s
      apply convex_iInter; intro _ f hf g hg a b ha hb hab
      change r + (a • f + b • g) (y - x) ≤ s
      simp only [add_apply, smul_apply, smul_eq_mul]
      change r + f (y - x) ≤ s at hf
      change r + g (y - x) ≤ s at hg
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hf), mul_nonneg hb (sub_nonneg.mpr hg),
        congrArg (fun t : ℝ => t * (s - r)) hab]

theorem subdifferential_monotone : BasicCalculusSpec.MonotoneGraph.{u} := by
  intro X _ _ φ x y f g hf hg
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hf.1
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hg.1
  have hxy := (mem_subdifferential_iff_of_value φ x r hr.symm f).mp hf y s hs.symm
  have hyx := (mem_subdifferential_iff_of_value φ y s hs.symm g).mp hg x r hr.symm
  simp only [map_sub, sub_apply] at hxy hyx ⊢
  linarith


/-- Attainment of the conjugate at x is exactly the supporting inequality. -/
lemma mem_subdifferential_iff_conjugate (φ : ExtendedFunction X) (x : X) (r : ℝ)
    (hx : φ x = (r : WithTop ℝ)) (f : X →L[ℝ] ℝ) :
    f ∈ subdifferential X φ x ↔
      convexConjugate X φ f = ((f x - r : ℝ) : EReal) := by
  rw [mem_subdifferential_iff_of_value φ x r hx]
  constructor
  · intro h
    apply le_antisymm
    · apply (convexConjugate_isLUB X φ f).2
      rintro _ ⟨y, rfl⟩
      by_cases hy : φ y = ⊤
      · change (f y : EReal) - extendedRealValue (φ y) ≤ _
        rw [hy]
        change (f y : EReal) - ⊤ ≤ _
        rw [EReal.sub_top]
        exact bot_le
      · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hy
        change (f y : EReal) - extendedRealValue (φ y) ≤ _
        rw [← hs]
        change (f y : EReal) - (s : EReal) ≤ _
        rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
        have hh := h y s hs.symm
        rw [map_sub] at hh
        linarith
    · have hh : (f x : EReal) - extendedRealValue (φ x) ≤ convexConjugate X φ f :=
        (convexConjugate_isLUB X φ f).1 ⟨x, rfl⟩
      simpa only [hx, show extendedRealValue (r : WithTop ℝ) = (r : EReal) from rfl,
        ← EReal.coe_sub] using hh
  · intro h y s hy
    have hh : (f y : EReal) - extendedRealValue (φ y) ≤ convexConjugate X φ f :=
      (convexConjugate_isLUB X φ f).1 ⟨y, rfl⟩
    change (f y : EReal) - extendedRealValue (φ y) ≤ convexConjugate X φ f at hh
    rw [h, hy] at hh
    change (f y : EReal) - (s : EReal) ≤ ((f x - r : ℝ) : EReal) at hh
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at hh
    rw [map_sub]
    linarith

theorem subdifferential_fenchel_iff : BasicCalculusSpec.FenchelEquality.{u} := by
  intro X _ _ φ x f
  change f ∈ subdifferential X φ x ↔
    φ x ≠ ⊤ ∧ extendedRealValue (φ x) + convexConjugate X φ f = (f x : EReal)
  constructor
  · intro hf
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hf.1
    refine ⟨hf.1, ?_⟩
    rw [(mem_subdifferential_iff_conjugate φ x r hr.symm f).mp hf, ← hr]
    change (r : EReal) + ((f x - r : ℝ) : EReal) = (f x : EReal)
    rw [← EReal.coe_add]
    congr 1
    ring
  · rintro ⟨hx, heq⟩
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hx
    apply (mem_subdifferential_iff_conjugate φ x r hr.symm f).mpr
    rw [← hr] at heq
    change (r : EReal) + convexConjugate X φ f = (f x : EReal) at heq
    calc
      convexConjugate X φ f = (r : EReal) + convexConjugate X φ f - (r : EReal) :=
        EReal.add_sub_cancel_left.symm
      _ = (f x : EReal) - (r : EReal) := by rw [heq]
      _ = ((f x - r : ℝ) : EReal) := (EReal.coe_sub _ _).symm

lemma reference_norm_equivalent : Asplund.NormSquareConjugate.EquivalentNorm (norm : X → ℝ) := by
  refine ⟨P1.C01Norm.canonical_norm_axioms ℝ X, 1, 1, zero_lt_one, zero_lt_one, ?_⟩
  intro x
  simp

lemma reference_dualNorm (f : X →L[ℝ] ℝ) :
    Asplund.NormSquareConjugate.dualNorm (norm : X → ℝ) f = ‖f‖ := by
  symm
  simpa only [Asplund.NormSquareConjugate.dualNorm, Real.norm_eq_abs]
    using P1.C04Dual.dual_norm_supremum ℝ X f

theorem halfNormSquare_subdifferential : BasicCalculusSpec.HalfNormSquare.{u} := by
  intro X _ _ x
  change subdifferential X _ x = dualityMap X x
  ext f
  rw [mem_subdifferential_iff_conjugate _ x (‖x‖ ^ 2 / 2) rfl f]
  have hconj : convexConjugate X (Asplund.NormSquareConjugate.halfNormSquare norm) f =
      ((Asplund.NormSquareConjugate.dualNorm norm f ^ 2 / 2 : ℝ) : EReal) :=
    Asplund.NormSquareConjugate.normSquare_conjugate X norm reference_norm_equivalent f
  rw [hconj, reference_dualNorm, EReal.coe_eq_coe_iff]
  change ‖f‖ ^ 2 / 2 = f x - ‖x‖ ^ 2 / 2 ↔ ‖f‖ = ‖x‖ ∧ f x = ‖x‖ ^ 2
  have hb : f x ≤ ‖f‖ * ‖x‖ := (le_abs_self _).trans (f.le_opNorm x)
  constructor
  · intro heq
    have hnorm : ‖f‖ = ‖x‖ := by nlinarith [sq_nonneg (‖f‖ - ‖x‖)]
    refine ⟨hnorm, ?_⟩
    rw [hnorm] at heq
    linarith
  · rintro ⟨hnorm, hx⟩
    rw [hnorm, hx]
    ring

/-- A formula valid at zero and at nonzero points alike. -/
lemma norm_subdifferential (x : X) :
    subdifferential X (fun y : X => (‖y‖ : WithTop ℝ)) x =
      {f : X →L[ℝ] ℝ | ‖f‖ ≤ 1 ∧ f x = ‖x‖} := by
  ext f
  rw [mem_subdifferential_iff_of_value _ x ‖x‖ rfl f]
  constructor
  · intro h
    have h0 := h 0 0 (by simp)
    have h2 := h ((2 : ℝ) • x) (2 * ‖x‖) (by simp [norm_smul])
    simp only [map_sub, map_smul, smul_eq_mul, map_zero] at h0 h2
    have hx : f x = ‖x‖ := by linarith
    have hu (y : X) : f y ≤ ‖y‖ := by
      have hh := h y ‖y‖ rfl
      rw [map_sub, hx] at hh
      linarith
    refine ⟨f.opNorm_le_bound zero_le_one (fun y => ?_), hx⟩
    rw [Real.norm_eq_abs, one_mul, abs_le]
    have hh := hu (-y)
    simp only [map_neg, norm_neg] at hh
    exact ⟨by linarith, hu y⟩
  · rintro ⟨hb, hx⟩ y s hs
    have hs' : s = ‖y‖ := (WithTop.coe_inj.mp hs).symm
    rw [hs', map_sub, hx]
    have hu := f.le_of_opNorm_le hb y
    rw [Real.norm_eq_abs, one_mul] at hu
    linarith [le_abs_self (f y)]

theorem norm_subdifferential_zero : BasicCalculusSpec.NormAtZero.{u} := by
  intro X _ _
  change subdifferential X _ 0 = _
  rw [norm_subdifferential]
  ext f
  simp [Metric.mem_closedBall, dist_zero_right]

theorem norm_subdifferential_ne_zero : BasicCalculusSpec.NormAtNonzero.{u} := by
  intro X _ _ x hx
  change subdifferential X _ x = _
  rw [norm_subdifferential]
  ext f
  constructor
  · rintro ⟨hb, hv⟩
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hh := f.le_opNorm x
    rw [Real.norm_eq_abs, hv, abs_of_nonneg (norm_nonneg x)] at hh
    exact ⟨by nlinarith, hv⟩
  · rintro ⟨hn, hv⟩
    exact ⟨hn.le, hv⟩

theorem indicator_subdifferential : BasicCalculusSpec.Indicator.{u} := by
  classical
  intro X _ _ C x
  change subdifferential X _ x = normalCone X C x
  by_cases hx : x ∈ C
  · ext f
    rw [mem_subdifferential_iff_of_value _ x 0 (by simp [hx]) f]
    change (∀ (y : X) (s : ℝ), (if y ∈ C then (0 : WithTop ℝ) else ⊤) = (s : WithTop ℝ) →
      0 + f (y - x) ≤ s) ↔ x ∈ C ∧ ∀ y ∈ C, f (y - x) ≤ 0
    constructor
    · intro h
      exact ⟨hx, fun y hy => by simpa using h y 0 (by simp [hy])⟩
    · rintro ⟨_, h⟩ y s hs
      by_cases hy : y ∈ C
      · have hs0 : s = (0 : ℝ) := by simpa [hy] using hs
        simpa [hs0] using h y hy
      · simp [hy] at hs
  · have he : subdifferential X (fun y => if y ∈ C then (0 : WithTop ℝ) else ⊤) x = ∅ :=
      subdifferential_at_infinity X _ x (by simp [hx])
    have hn : normalCone X C x = ∅ := normalCone_outside X C x hx
    rw [he, hn]


/-- Secants of a convex function lie above its derivative at the base point.
Only the function's real representative near x is differentiated. -/
lemma derivative_supports (φ : ExtendedFunction X) (u : X → ℝ) (x : X)
    (d : X →L[ℝ] ℝ) (hc : ExtendedConvex X φ)
    (hlocal : ∀ᶠ y in 𝓝 x, φ y = (u y : WithTop ℝ))
    (hd : ∀ v : X, HasDerivAt (fun t : ℝ => u (x + t • v)) (d v) 0) :
    d ∈ subdifferential X φ x := by
  have hx : φ x = (u x : WithTop ℝ) := hlocal.self_of_nhds
  apply (mem_subdifferential_iff_of_value φ x (u x) hx d).mpr
  intro y s hy
  have ht : Tendsto (fun t : ℝ => x + t • (y - x)) (𝓝[>] 0) (𝓝 x) := by
    have hcont : Continuous (fun t : ℝ => x + t • (y - x)) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hh : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ * (u (x + t • (y - x)) - u x) ≤ s - u x := by
    filter_upwards [ht.eventually hlocal, self_mem_nhdsWithin,
      ((eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds)] with t he ht0 ht1
    have hc' := hc x y (u x) s (1 - t) t hx hy (by linarith) (le_of_lt ht0) (by ring)
    have hv : (1 - t) • x + t • y = x + t • (y - x) := by module
    rw [hv, he, WithTop.coe_le_coe] at hc'
    have hb : u (x + t • (y - x)) - u x ≤ t * (s - u x) := by nlinarith only [hc']
    have hm := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (le_of_lt ht0))
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (show (0 : ℝ) < t from ht0)), one_mul] using hm
  have hlim := (hd (y - x)).tendsto_slope_zero_right
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at hlim
  have hb : d (y - x) ≤ s - u x := le_of_tendsto hlim hh
  linarith

lemma subgradient_eq_derivative (φ : ExtendedFunction X) (u : X → ℝ) (x : X)
    (d : X →L[ℝ] ℝ) (hlocal : ∀ᶠ y in 𝓝 x, φ y = (u y : WithTop ℝ))
    (hd : ∀ v : X, HasDerivAt (fun t : ℝ => u (x + t • v)) (d v) 0)
    (f : X →L[ℝ] ℝ) (hf : f ∈ subdifferential X φ x) : f = d := by
  have hx : φ x = (u x : WithTop ℝ) := hlocal.self_of_nhds
  have hs := (mem_subdifferential_iff_of_value φ x (u x) hx f).mp hf
  ext v
  have hmin : IsLocalMin (fun t : ℝ => u (x + t • v) - f (x + t • v)) 0 := by
    have ht : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
      have hcont : Continuous (fun t : ℝ => x + t • v) :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa only [zero_smul, add_zero] using (hcont.continuousAt (x := (0 : ℝ))).tendsto
    filter_upwards [ht.eventually hlocal] with t he
    have hh := hs (x + t • v) (u (x + t • v)) he
    simp only [zero_smul, add_zero, map_sub] at hh ⊢
    linarith
  have hfline : HasDerivAt (fun t : ℝ => f (x + t • v)) (f v) 0 := by
    have hlin : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    exact f.hasFDerivAt.comp_hasDerivAt 0 hlin
  have hz := hmin.hasDerivAt_eq_zero ((hd v).sub hfline)
  linarith

theorem differentiableAlongLines_subdifferential : BasicCalculusSpec.DifferentiableAlongLines.{u} := by
  intro X _ _ φ u x d hc hlocal hd
  change subdifferential X φ x = {d}
  ext f
  constructor
  · intro hf
    exact subgradient_eq_derivative φ u x d hlocal hd f hf
  · intro hf
    have hfd : f = d := hf
    rw [hfd]
    exact derivative_supports φ u x d hc hlocal hd

theorem differentiable_subdifferential : BasicCalculusSpec.Differentiable.{u} := by
  intro X _ _ φ u x d hc hlocal hd
  apply differentiableAlongLines_subdifferential X φ u x d hc hlocal
  intro v
  have hlin : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  exact hd.comp_hasDerivAt_of_eq 0 hlin (by simp)

end ExpandedFA.BanachConvex
