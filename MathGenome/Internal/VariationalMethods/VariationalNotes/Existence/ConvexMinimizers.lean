import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Existence.ConvexMinimizers
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.DifferentiabilityMonotonicity
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Calculus.TangentCone.Real

noncomputable section
open Set Filter Topology
universe u
namespace VariationalNotes.Existence

/-- Convexity of the feasible epigraph gives the finite-endpoint inequality. -/
lemma feasible_jensen {E : Type u} [AddCommGroup E] [Module ℝ E]
    {C : Set E} {J : E → WithTop ℝ}
    (hJ : Convex ℝ {p : E × ℝ | p.1 ∈ C ∧ J p.1 ≤ (p.2 : WithTop ℝ)})
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) {r s : ℝ}
    (hr : J x = (r : WithTop ℝ)) (hs : J y = (s : WithTop ℝ))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    J (a • x + b • y) ≤ ((a * r + b * s : ℝ) : WithTop ℝ) := by
  exact (hJ (show (x, r) ∈ _ from ⟨hx, hr.le⟩)
    (show (y, s) ∈ _ from ⟨hy, hs.le⟩) ha hb hab).2

theorem localMin_isMin : Specs.localMin_isMin.{u} := by
  intro E _ _ _ _ _ C J hC _ hJ x hx hfinite hlocal y hy
  change J x ≤ J y
  by_cases hyt : J y = ⊤
  · simp [hyt]
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hfinite)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hyt
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hzero : line 0 = x := AffineMap.lineMap_apply_zero x y
  have hmaps : MapsTo line (Icc 0 1) C := by
    simpa only [line, mapsTo_iff_image_subset, ← segment_eq_image_lineMap]
      using hC.segment_subset hx hy
  have hl : IsLocalMinOn (J ∘ line) (Icc 0 1) 0 := by
    rw [← hzero] at hlocal
    exact hlocal.comp_continuousOn hmaps AffineMap.lineMap_continuous.continuousOn
      (left_mem_Icc.mpr zero_le_one)
  rw [IsLocalMinOn, nhdsWithin_Icc_eq_nhdsGE (show (0 : ℝ) < 1 by norm_num)] at hl
  have hl' : ∀ᶠ t in 𝓝[>] (0 : ℝ), (r : WithTop ℝ) ≤ J (line t) := by
    simpa only [IsMinFilter, Function.comp_apply, hzero, ← hr] using
      hl.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)
  obtain ⟨t, hlow, ht⟩ := (hl'.and (Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  have hu := feasible_jensen hJ hx hy hr.symm hs.symm
    (show 0 ≤ 1-t by linarith [ht.2]) ht.1.le (show 1-t+t=1 by ring)
  have hline : line t = (1-t) • x + t • y :=
    AffineMap.lineMap_apply_module x y t
  rw [hline] at hlow
  have hreal := WithTop.coe_le_coe.mp (hlow.trans hu)
  rw [← hr, ← hs, WithTop.coe_le_coe]
  nlinarith [ht.1]

theorem minimizer_unique : Specs.minimizer_unique.{u} := by
  intro E _ _ C J hC hproper _ hstrict x hx y hy hxmin hymin
  by_contra hne
  obtain ⟨z, hz, hzfin⟩ := hproper
  have hxf : J x < ⊤ := (hxmin hz).trans_lt hzfin
  have hyf : J y < ⊤ := (hymin hz).trans_lt hzfin
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hxf)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hyf)
  have hrs : r = s := WithTop.coe_inj.mp
    ((hr.trans ((hxmin hy).antisymm (hymin hx))).trans hs.symm)
  have hm := hstrict x hx y hy r s hr.symm hs.symm hne
    (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
  have hmem := hC hx hy (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (1/2 : ℝ)+1/2=1 by norm_num)
  have hlow := hxmin hmem
  rw [← hr] at hlow
  have heq : (1/2 : ℝ)*r + (1/2)*s = r := by rw [← hrs]; ring
  rw [heq] at hm
  exact (lt_of_le_of_lt hlow hm).false

theorem isMin_iff_gradient_nonneg : Specs.isMin_iff_gradient_nonneg.{u} := by
  intro E _ _ _ C U J g hC hU hUconv hCU hg hd hagree x hx
  have hbridge : IsMinOn J C x ↔ IsMinOn g C x := by
    constructor <;> intro hm y hy
    · have h : J x ≤ J y := hm hy
      change g x ≤ g y
      rw [hagree x hx, hagree y hy, WithTop.coe_le_coe] at h
      exact h
    · change J x ≤ J y
      rw [hagree x hx, hagree y hy, WithTop.coe_le_coe]
      exact hm hy
  rw [hbridge]
  constructor
  · intro hm y hy
    rw [inner_gradient_left]
    apply hm.isLocalMinOn.hasFDerivWithinAt_nonneg (hd x (hCU hx)).hasFDerivAt.hasFDerivWithinAt
    exact sub_mem_posTangentConeAt_of_openSegment_subset
      ((openSegment_subset_segment ℝ x y).trans (hC.segment_subset hx hy))
  · intro hgrad y hy
    change g x ≤ g y
    have hs := (ConvexAnalysis.convexOn_iff_derivative_supports U g
      (fun z => fderiv ℝ g z) hU hUconv (fun z hz => (hd z hz).hasFDerivAt)).mp hg
      x (hCU hx) y (hCU hy)
    have hn := hgrad y hy
    rw [inner_gradient_left] at hn
    linarith

end VariationalNotes.Existence
