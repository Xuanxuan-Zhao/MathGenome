import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.LegendreNecessity
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.SecondVariation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc

noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace VariationalNotes.Classical

/-- A fixed smooth scalar test with strictly positive derivative energy. -/
private theorem exists_localization_test :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ tsupport ψ ⊆ Ioo (-1) 1 ∧
      0 < ∫ r in (-1 : ℝ)..1, (deriv ψ r) ^ 2 := by
  let β : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let ψ : ℝ → ℝ := fun r => r * β r
  have hψ : ContDiff ℝ ∞ ψ := contDiff_id.mul β.contDiff
  have hs : tsupport ψ ⊆ Ioo (-1 : ℝ) 1 := by
    apply (tsupport_mul_subset_right (f := id) (g := (β : ℝ → ℝ))).trans
    rw [β.tsupport_eq]
    intro r hr
    have hr' : |r| ≤ 1 / 2 := by simpa [Metric.mem_closedBall, Real.dist_eq, β] using hr
    have := abs_le.mp hr'
    constructor <;> linarith
  have hd : deriv ψ 0 = 1 := by
    have he : ψ =ᶠ[𝓝 (0 : ℝ)] id := by
      filter_upwards [β.eventuallyEq_one] with r hr
      simp [ψ, hr]
    exact he.deriv_eq.trans (by simp)
  refine ⟨ψ, hψ, hs, ?_⟩
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ : ℝ => (0 : ℝ)) (g := fun r => (deriv ψ r) ^ 2)
    (by norm_num : (-1 : ℝ) < 1) continuousOn_const
    ((hψ.continuous_deriv (by simp)).pow 2).continuousOn
    (fun r _ => sq_nonneg (deriv ψ r)) ⟨0, by norm_num, by simp [hd]⟩
  simpa using hi

/-- Localization of a continuous scalar quadratic differential form. No
regularity of the coefficients beyond continuity is used. -/
theorem scalar_legendre_of_nonnegative_secondVariation
    {a b : ℝ} {A B C : ℝ → ℝ}
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C)
    (hQ : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → φ a = 0 → φ b = 0 →
      0 ≤ ∫ t in a..b, A t * (φ t) ^ 2 +
        2 * B t * φ t * deriv φ t + C t * (deriv φ t) ^ 2)
    {x : ℝ} (hx : x ∈ Ioo a b) : 0 ≤ C x := by
  obtain ⟨ψ, hψ, hsψ, henergy⟩ := exists_localization_test
  let φ : ℝ → ℝ → ℝ := fun ε t => ε * ψ ((t - x) / ε)
  let F : ℝ → ℝ → ℝ := fun ε t => A t * (φ ε t) ^ 2 +
    2 * B t * φ ε t * deriv (φ ε) t + C t * (deriv (φ ε) t) ^ 2
  -- The rescaled integrand has a continuous extension to ε = 0.
  let G : ℝ → ℝ → ℝ := fun ε r => A (ε * r + x) * (ε * ψ r) ^ 2 +
    2 * B (ε * r + x) * (ε * ψ r) * deriv ψ r +
      C (ε * r + x) * (deriv ψ r) ^ 2
  have hd (ε : ℝ) (hε : ε ≠ 0) (t : ℝ) :
      deriv (φ ε) t = deriv ψ ((t - x) / ε) := by
    have h := (((hψ.differentiable (by simp) ((t - x) / ε)).hasDerivAt).comp t
      (((hasDerivAt_id t).sub_const x).div_const ε)).const_mul ε
    convert h.deriv using 1
    dsimp
    field_simp
  have hz (r : ℝ) (hr : r ∉ Ioo (-1 : ℝ) 1) :
      ψ r = 0 ∧ deriv ψ r = 0 := by
    have hn : r ∉ tsupport ψ := fun h => hr (hsψ h)
    exact ⟨image_eq_zero_of_notMem_tsupport hn,
      image_eq_zero_of_notMem_tsupport (fun h => hn (tsupport_deriv_subset h))⟩
  have hJ : Continuous (fun ε : ℝ => ∫ r in (-1 : ℝ)..1, G ε r) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    change Continuous (fun p : ℝ × ℝ => G p.1 p.2)
    have hψc := hψ.continuous
    have hψd := hψ.continuous_deriv (by simp)
    dsimp [G]
    fun_prop
  have hnonneg : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 ≤ ∫ r in (-1 : ℝ)..1, G ε r := by
    have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < min (x - a) (b - x) :=
      (eventually_lt_nhds (show (0 : ℝ) < min (x - a) (b - x) by
        exact lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2))).filter_mono nhdsWithin_le_nhds
    filter_upwards [hevent, self_mem_nhdsWithin] with ε hsmall hε
    have hε : 0 < ε := hε
    have hε0 : ε ≠ 0 := hε.ne'
    have hleft : a < x - ε := by have := (lt_min_iff.mp hsmall).1; linarith
    have hright : x + ε < b := by have := (lt_min_iff.mp hsmall).2; linarith
    have hφ : ContDiff ℝ ∞ (φ ε) := by
      dsimp [φ]
      exact contDiff_const.mul (hψ.comp ((contDiff_id.sub contDiff_const).div_const ε))
    have hφa : φ ε a = 0 := by
      dsimp [φ]
      rw [(hz _ (by
        simp only [mem_Ioo, not_and_or, not_lt]
        exact Or.inl ((div_le_iff₀ hε).mpr (by linarith)))).1, mul_zero]
    have hφb : φ ε b = 0 := by
      dsimp [φ]
      rw [(hz _ (by
        simp only [mem_Ioo, not_and_or, not_lt]
        exact Or.inr ((le_div_iff₀ hε).mpr (by linarith)))).1, mul_zero]
    have hsF : Function.support (F ε) ⊆ Ioo (x - ε) (x + ε) := by
      intro t ht
      by_contra hn
      have hr : (t - x) / ε ∉ Ioo (-1 : ℝ) 1 := by
        intro hr
        have hr1 := (lt_div_iff₀ hε).mp hr.1
        have hr2 := (div_lt_iff₀ hε).mp hr.2
        apply hn
        constructor <;> linarith
      obtain ⟨hz1, hz2⟩ := hz _ hr
      apply ht
      simp only [F, hd ε hε0]
      simp [φ, hz1, hz2]
    -- Support containment and the affine change of variables give Q(φ_ε) = ε J(ε).
    have heq : (∫ t in a..b, F ε t) = ε * ∫ r in (-1 : ℝ)..1, G ε r := by
      have h1 := intervalIntegral.integral_eq_integral_of_support_subset
        (f := F ε) (μ := volume)
        (hsF.trans (fun _ ht => ⟨hleft.trans ht.1, ht.2.le.trans hright.le⟩))
      have h2 := intervalIntegral.integral_eq_integral_of_support_subset
        (f := F ε) (μ := volume) (hsF.trans Ioo_subset_Ioc_self)
      rw [h1, ← h2]
      have hsub := intervalIntegral.smul_integral_comp_mul_add (F ε)
        (a := (-1 : ℝ)) (b := 1) ε x
      simp only [smul_eq_mul, mul_neg, mul_one] at hsub
      rw [show -ε + x = x - ε by ring, show ε + x = x + ε by ring] at hsub
      rw [← hsub]
      congr 1
      apply intervalIntegral.integral_congr
      intro r _
      have hr : (ε * r + x - x) / ε = r := by field_simp; ring
      dsimp only [F, G]
      rw [hd ε hε0]
      simp only [φ, hr]
    have hpos : 0 ≤ ε * ∫ r in (-1 : ℝ)..1, G ε r := by
      rw [← heq]
      exact hQ (φ ε) hφ hφa hφb
    exact nonneg_of_mul_nonneg_right hpos hε
  have hlim : 0 ≤ ∫ r in (-1 : ℝ)..1, G 0 r :=
    ge_of_tendsto (hJ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hnonneg
  have hvalue : (∫ r in (-1 : ℝ)..1, G 0 r) =
      C x * ∫ r in (-1 : ℝ)..1, (deriv ψ r) ^ 2 := by
    simp only [G, zero_mul, zero_add, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
    exact intervalIntegral.integral_const_mul _ _
  rw [hvalue] at hlim
  exact nonneg_of_mul_nonneg_left hlim henergy

/-- The Legendre conclusion depends only on the continuous Hessian along the
curve and nonnegativity on the full endpoint-zero C¹ variation space. -/
theorem legendre_of_nonnegative_secondVariation
    {I : Interval} {m : ℕ} (L : Lagrangian m) (u : C1Curve I m)
    (hreg : regularNearGraph L u 2)
    (hQ : ∀ η : C1Curve I m, η ∈ endpointZero I m → 0 ≤ secondVariationForm L u η)
    (t : I.Points) (ht : (t : ℝ) ∈ Ioo I.a I.b) (e : State m) :
    0 ≤ secondVariationVV L (graphPoint u t) e e := by
  obtain ⟨U, hU, hu, _, hL⟩ := hreg
  -- Clamping extends the continuous coefficients to ℝ without changing them on [a,b].
  let π : ℝ → I.Points := projIcc I.a I.b I.increasing.le
  let H := fun s : ℝ => fderiv ℝ (fderiv ℝ L.value) (graphPoint u (π s))
  have hg : Continuous (fun s : I.Points => graphPoint u s) :=
    continuous_subtype_val.prodMk (u.state.continuous.prodMk u.velocity.continuous)
  have hH : Continuous H := by
    have hL1 : ContDiffOn ℝ 1 (fderiv ℝ L.value) U :=
      hL.fderiv_of_isOpen hU (by norm_num)
    have hD := hL1.continuousOn_fderiv_of_isOpen hU (by norm_num)
    exact (hD.comp_continuous hg hu).comp continuous_projIcc
  let A : ℝ → ℝ := fun s => H s (0, e, 0) (0, e, 0)
  let B : ℝ → ℝ := fun s => H s (0, e, 0) (0, 0, e)
  let C : ℝ → ℝ := fun s => H s (0, 0, e) (0, 0, e)
  have hA : Continuous A := (hH.clm_apply continuous_const).clm_apply continuous_const
  have hB : Continuous B := (hH.clm_apply continuous_const).clm_apply continuous_const
  have hC : Continuous C := (hH.clm_apply continuous_const).clm_apply continuous_const
  have hscalar : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → φ I.a = 0 → φ I.b = 0 →
      0 ≤ ∫ s in I.a..I.b, A s * (φ s) ^ 2 +
        2 * B s * φ s * deriv φ s + C s * (deriv φ s) ^ 2 := by
    intro φ hφ ha hb
    let v : ℝ → State m := fun s => φ s • e
    have hv : ContDiff ℝ ∞ v := hφ.smul contDiff_const
    let η : C1Curve I m := interiorTestCurve v hv
    have hd (s : ℝ) : deriv v s = deriv φ s • e :=
      ((hφ.differentiable (by simp) s).hasDerivAt.smul_const e).deriv
    have hη : η ∈ endpointZero I m := by
      constructor
      · change φ I.a • e = 0
        rw [ha, zero_smul]
      · change φ I.b • e = 0
        rw [hb, zero_smul]
    have heq : secondVariationForm L u η =
        ∫ s in I.a..I.b, A s * (φ s) ^ 2 +
          2 * B s * φ s * deriv φ s + C s * (deriv φ s) ^ 2 := by
      unfold secondVariationForm
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le I.increasing.le] at hs
      have hπ : π s = (⟨s, hs⟩ : I.Points) := projIcc_of_mem _ hs
      have hz (c : ℝ) : ((0 : ℝ), c • e, (0 : State m)) = c • (0, e, 0) := by simp
      have hw (c : ℝ) : ((0 : ℝ), (0 : State m), c • e) = c • (0, 0, e) := by simp
      change secondVariationZZ L _ (stateField I m η s) (stateField I m η s) +
        2 * secondVariationZV L _ (stateField I m η s) (velocityField I m η s) +
        secondVariationVV L _ (velocityField I m η s) (velocityField I m η s) = _
      have hstate : stateField I m η s = φ s • e := by
        simp [stateField, extendState, hs, η, interiorTestCurve, C1Curve.state, v]
      have hvel : velocityField I m η s = deriv φ s • e := by
        simpa [velocityField, extendState, hs, η, interiorTestCurve, C1Curve.velocity] using hd s
      rw [hstate, hvel]
      dsimp only [secondVariationZZ, secondVariationZV, secondVariationVV, A, B, C, H]
      rw [hπ]
      simp only [stateField, velocityField, extendState, dite_eq_left hs]
      change fderiv ℝ (fderiv ℝ L.value) (graphPoint u ⟨s, hs⟩)
          (0, φ s • e, 0) (0, φ s • e, 0) +
        2 * fderiv ℝ (fderiv ℝ L.value) (graphPoint u ⟨s, hs⟩)
          (0, φ s • e, 0) (0, 0, deriv φ s • e) +
        fderiv ℝ (fderiv ℝ L.value) (graphPoint u ⟨s, hs⟩)
          (0, 0, deriv φ s • e) (0, 0, deriv φ s • e) = _
      rw [hz, hw]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    exact heq ▸ hQ η hη
  have h := scalar_legendre_of_nonnegative_secondVariation hA hB hC hscalar ht
  simpa only [C, H, π, projIcc_of_mem I.increasing.le t.property, secondVariationVV] using h

theorem classicalLegendreNecessity :
    Specs.VariationalNotes.Classical.LegendreNecessity.classicalLegendreNecessity := by
  intro I m L xₐ xᵦ u hmin hreg t ht e
  exact legendre_of_nonnegative_secondVariation L u hreg
    (fun η hη => (classicalSecondVariation I m L xₐ xᵦ u hmin hreg η hη).2) t ht e

theorem classicalLegendreTheorem :
    Specs.VariationalNotes.Classical.LegendreNecessity.classicalLegendreTheorem := by
  intro I m L xₐ xᵦ u hmin hreg
  exact ⟨classicalSecondVariation I m L xₐ xᵦ u hmin hreg,
    classicalLegendreNecessity I m L xₐ xᵦ u hmin hreg⟩

end VariationalNotes.Classical
