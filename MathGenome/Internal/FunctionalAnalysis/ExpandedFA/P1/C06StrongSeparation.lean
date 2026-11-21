import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06StrongSeparation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06OpenSeparation
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Tactic.Linarith

/-! Strong separation from closed convex sets, `fa2:p1:c06:strong-separation`.

For each radius below the distance to C, separate the open ball from C using
the accepted open-separation theorem. Applying the resulting inequality at
both u and -u bounds the operator norm and gives the prescribed r * ‖f‖ gap.
Complexification preserves both the real part and the norm of the separator.

For a locally convex space, geometric Hahn–Banach separates a point from a
closed convex set. The real supremum remains strictly below the point's value.
For compact D, C - D is closed and convex, excludes zero, and point separation
of this difference gives one positive gap for every c ∈ C and d ∈ D.
-/
namespace ExpandedFA.P1.C06
universe u
open Set Metric
open scoped Pointwise

/-- Separation at each prescribed radius below the distance to C. -/
theorem real_point_strong_separation_quantitative :
    Specs.ExpandedFA.P1.C06StrongSeparation.realQuantitativeType.{u} := by
  intro E _ _ C x₀ hC _hc hcC _hx r hr hrd
  have hd : Disjoint (ball x₀ r) C := by
    refine Set.disjoint_left.mpr ?_
    intro y hy hyC
    have hy' : dist x₀ y < r := by simpa only [mem_ball, dist_comm] using hy
    exact (hrd.trans_le (infDist_le_dist_of_mem hyC)).not_ge hy'.le
  obtain ⟨g, α, hgn, hgB, hgC⟩ := real_open_convex_separation
    (ball x₀ r) C ⟨x₀, mem_ball_self hr⟩ hC (convex_ball x₀ r) hcC hd isOpen_ball
  let f : E →L[ℝ] ℝ := -g
  have hfn : f ≠ 0 := neg_ne_zero.mpr hgn
  have hsep : ∀ c ∈ C, ∀ u : E, ‖u‖ < r → f c + f u ≤ f x₀ := by
    intro c hc u hu
    have hb : x₀ - u ∈ ball x₀ r := by
      simpa only [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg] using hu
    have h1 := hgB (x₀ - u) hb
    have h2 := hgC c hc
    dsimp [f]
    simp only [map_sub] at h1
    simp only [neg_apply]
    linarith
  have hgap : ∀ c ∈ C, r * ‖f‖ ≤ f x₀ - f c := by
    intro c hc
    have hbound : ∀ u ∈ ball (0 : E) r, ‖f u‖ ≤ f x₀ - f c := by
      intro u hu
      have hu' : ‖u‖ < r := mem_ball_zero_iff.mp hu
      have hp := hsep c hc u hu'
      have hn := hsep c hc (-u) (by simpa only [norm_neg] using hu')
      rw [map_neg] at hn
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hbound' : ∀ u ∈ closedBall (0 : E) r, ‖f u‖ ≤ f x₀ - f c := by
      have hh : closure (ball (0 : E) r) ⊆ {u | ‖f u‖ ≤ f x₀ - f c} :=
        closure_minimal hbound (isClosed_le f.continuous.norm continuous_const)
      intro u hu
      apply hh
      rwa [closure_ball _ hr.ne']
    have hop := f.opNorm_bound_of_ball_bound hr (f x₀ - f c) hbound'
    have hm := (le_div_iff₀ hr).mp hop
    nlinarith [hm]
  have hbd : BddAbove (f '' C) := by
    refine ⟨f x₀ - r * ‖f‖, ?_⟩
    rintro y ⟨c, hc, rfl⟩
    have := hgap c hc
    linarith
  have hsup : sSup (f '' C) ≤ f x₀ - r * ‖f‖ := by
    apply csSup_le (hC.image f)
    rintro y ⟨c, hc, rfl⟩
    have := hgap c hc
    linarith
  have hpos : 0 < r * ‖f‖ := mul_pos hr (norm_pos_iff.mpr hfn)
  refine ⟨f, hfn, hbd, ?_, ?_⟩ <;> linarith

/-- The real separator extends complex-linearly with identical norm and real part. -/
theorem complex_point_strong_separation_quantitative :
    Specs.ExpandedFA.P1.C06StrongSeparation.complexQuantitativeType.{u} := by
  intro E _ _ C x₀ hC hc hcC hx r hr hrd
  obtain ⟨h, hn, hbd, hlt, hgap⟩ :=
    real_point_strong_separation_quantitative C x₀ hC hc hcC hx r hr hrd
  let f : E →L[ℂ] ℂ := StrongDual.extendRCLike h
  have hre : (fun x => (f x).re) = h := by
    funext x
    exact StrongDual.re_extendRCLike_apply (𝕜 := ℂ) h x
  have hre₀ : (f x₀).re = h x₀ := congrFun hre x₀
  have hfn : f ≠ 0 := by
    intro hf
    apply hn
    ext x
    have := congrFun hre x
    simpa only [hf, zero_apply, Complex.zero_re] using this.symm
  have hnorm : ‖f‖ = ‖h‖ := StrongDual.norm_extendRCLike h
  refine ⟨f, hfn, ?_, ?_, ?_⟩
  · simpa only [hre] using hbd
  · change sSup ((fun x => (f x).re) '' C) < (fun x => (f x).re) x₀
    simpa only [hre, hre₀] using hlt
  · change r * ‖f‖ ≤ (fun x => (f x).re) x₀ - sSup ((fun x => (f x).re) '' C)
    simpa only [hre, hre₀, hnorm] using hgap

/-- Qualitative real normed-space separation, with a finite scalar supremum. -/
theorem real_point_strong_separation :
    Specs.ExpandedFA.P1.C06StrongSeparation.realNormedType.{u} := by
  intro E _ _ C x₀ hC hc hcC hx
  have hd : 0 < infDist x₀ C := (hc.notMem_iff_infDist_pos hC).mp hx
  obtain ⟨f, hn, hbd, hlt, _⟩ := real_point_strong_separation_quantitative
    C x₀ hC hc hcC hx (infDist x₀ C / 2) (by linarith) (by linarith)
  exact ⟨f, hn, hbd, hlt⟩

/-- Qualitative complex normed-space separation, using the complex linear dual. -/
theorem complex_point_strong_separation :
    Specs.ExpandedFA.P1.C06StrongSeparation.complexNormedType.{u} := by
  intro E _ _ C x₀ hC hc hcC hx
  have hd : 0 < infDist x₀ C := (hc.notMem_iff_infDist_pos hC).mp hx
  obtain ⟨f, hn, hbd, hlt, _⟩ := complex_point_strong_separation_quantitative
    C x₀ hC hc hcC hx (infDist x₀ C / 2) (by linarith) (by linarith)
  exact ⟨f, hn, hbd, hlt⟩

/-- Strong point separation in the given Hausdorff locally convex topology. -/
theorem real_locally_convex_point_strong_separation :
    Specs.ExpandedFA.P1.C06StrongSeparation.realLocallyConvexType.{u} := by
  intro E _ _ _ _ _ _ _ C x₀ hC hc hcC hx
  obtain ⟨f, α, hbelow, habove⟩ := geometric_hahn_banach_closed_point hcC hc hx
  have hfn : f ≠ 0 := by
    intro hf
    obtain ⟨c, hc⟩ := hC
    have := (hbelow c hc).trans habove
    simp only [hf, zero_apply, lt_self_iff_false] at this
  have hbd : BddAbove (f '' C) := by
    refine ⟨α, ?_⟩
    rintro y ⟨c, hc, rfl⟩
    exact (hbelow c hc).le
  refine ⟨f, hfn, hbd, lt_of_le_of_lt ?_ habove⟩
  apply csSup_le (hC.image f)
  rintro y ⟨c, hc, rfl⟩
  exact (hbelow c hc).le

/-- The locally convex complex conclusion is expressed by a real part. -/
theorem complex_locally_convex_point_strong_separation :
    Specs.ExpandedFA.P1.C06StrongSeparation.complexLocallyConvexType.{u} := by
  intro E _ _ _ _ _ _ _ C x₀ hC hc hcC hx
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  obtain ⟨h, hn, hbd, hlt⟩ :=
    real_locally_convex_point_strong_separation C x₀ hC hc hcC hx
  let f : E →L[ℂ] ℂ := StrongDual.extendRCLike h
  have hre : (fun x => (f x).re) = h := by
    funext x
    exact StrongDual.re_extendRCLike_apply (𝕜 := ℂ) h x
  have hre₀ : (f x₀).re = h x₀ := congrFun hre x₀
  have hfn : f ≠ 0 := by
    intro hf
    apply hn
    ext x
    have := congrFun hre x
    simpa only [hf, zero_apply, Complex.zero_re] using this.symm
  refine ⟨f, hfn, ?_, ?_⟩
  · simpa only [hre] using hbd
  · change sSup ((fun x => (f x).re) '' C) < (fun x => (f x).re) x₀
    simpa only [hre, hre₀] using hlt


/-- The compact-set clause in an arbitrary Hausdorff locally convex real space. -/
theorem real_locally_convex_compact_convex_separation :
    Specs.ExpandedFA.P1.C06StrongSeparation.realLocallyConvexCompactType.{u} := by
  intro E _ _ _ _ _ _ _ C D hC hcC hvC hD hkD hvD hd
  have hne : (C - D).Nonempty := by
    obtain ⟨c, hc⟩ := hC
    obtain ⟨d, hd⟩ := hD
    exact ⟨c - d, sub_mem_sub hc hd⟩
  have hclosed : IsClosed (C - D) := by
    rw [sub_eq_add_neg]
    exact hcC.add_right_of_isCompact hkD.neg
  have hzero : (0 : E) ∉ C - D := by
    intro hz
    obtain ⟨c, hc, d, hdD, heq⟩ := mem_sub.mp hz
    have hcd : c = d := sub_eq_zero.mp heq
    subst d
    exact Set.disjoint_left.mp hd hc hdD
  obtain ⟨h, hn, hb, hs⟩ := real_locally_convex_point_strong_separation
    (C - D) 0 hne hclosed (hvC.sub hvD) hzero
  rw [map_zero] at hs
  refine ⟨h, -sSup (h '' (C - D)), hn, neg_pos.mpr hs, ?_⟩
  intro c hc d hdD
  have hle : h (c - d) ≤ sSup (h '' (C - D)) :=
    le_csSup hb ⟨c - d, sub_mem_sub hc hdD, rfl⟩
  rw [map_sub] at hle
  linarith

/-- A continuous complex-linear separator with the specified nonzero real part. -/
theorem complex_locally_convex_compact_convex_separation :
    Specs.ExpandedFA.P1.C06StrongSeparation.complexLocallyConvexCompactType.{u} := by
  intro E _ _ _ _ _ _ _ C D hC hcC hvC hD hkD hvD hd
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  obtain ⟨h, δ, hn, hδ, hgap⟩ := real_locally_convex_compact_convex_separation
    C D hC hcC hvC hD hkD hvD hd
  let f : E →L[ℂ] ℂ := StrongDual.extendRCLike h
  have hre : ∀ x, h x = (f x).re := by
    intro x
    exact (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) h x).symm
  refine ⟨h, f, δ, hn, ?_, hre, hδ, hgap⟩
  intro hf
  apply hn
  ext x
  simpa only [hf, zero_apply, Complex.zero_re] using hre x

/-- Real normed spaces are locally convex; completeness is unnecessary. -/
theorem real_compact_convex_separation :
    Specs.ExpandedFA.P1.C06StrongSeparation.realNormedCompactType.{u} := by
  intro E _ _ C D hC hcC hvC hD hkD hvD hd
  exact real_locally_convex_compact_convex_separation C D hC hcC hvC hD hkD hvD hd

/-- Complex normed spaces with their underlying real convex geometry. -/
theorem complex_compact_convex_separation :
    Specs.ExpandedFA.P1.C06StrongSeparation.complexNormedCompactType.{u} := by
  intro E _ _ C D hC hcC hvC hD hkD hvD hd
  exact complex_locally_convex_compact_convex_separation C D hC hcC hvC hD hkD hvD hd

end ExpandedFA.P1.C06
