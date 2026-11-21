import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.LocalLipschitz
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.ScalarComparison
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

noncomputable section
open Set Metric Filter Real
open scoped Topology

namespace D13Unified

/-- The shared open-domain local hypothesis gives relative local control on
any closed time rectangle in that domain. This also explains the endpoint
restriction in the independent specification. -/
theorem ODE.LocallyLipschitzInState.on_closed_rectangle
    {F : ODE ℝ} (hF : F.LocallyLipschitzInState) {a b : ℝ} {J : Set ℝ}
    (hJ : IsOpen J) (hrect : Icc a b ×ˢ J ⊆ F.domain) :
    Specs.D13Unified.Ch05.ScalarComparison.localControl F.eval (Icc a b) J := by
  intro s hs ξ hξ
  obtain ⟨δ, ρ, L, hδ, hρ, hL, _hdom, hLip⟩ := hF s ξ (hrect ⟨hs, hξ⟩)
  obtain ⟨r, hr, hrJ⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds hξ)
  refine ⟨δ, min ρ r, L, hδ, lt_min hρ hr, hL, ?_, ?_⟩
  · exact (ball_subset_ball (min_le_right _ _)).trans hrJ
  · intro t ht x hx y hy
    exact hLip t ht.2 x ((ball_subset_ball (min_le_left _ _)) hx)
      y ((ball_subset_ball (min_le_left _ _)) hy)

/-- A positive function cannot appear from nonpositive initial data when
its derivative is strictly negative wherever the function is positive. -/
private theorem nonpos_of_deriv_neg_on_pos {w w' : ℝ → ℝ} {a b : ℝ}
    (hw : ContinuousOn w (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt w (w' t) (Ici t) t)
    (ha : w a ≤ 0)
    (hneg : ∀ t ∈ Ico a b, 0 < w t → w' t < 0) :
    ∀ t ∈ Icc a b, w t ≤ 0 := by
  intro t ht
  by_contra h
  have hpos : 0 < w t := lt_of_not_ge h
  have hbound : w t ≤ w t / 2 := by
    apply image_le_of_deriv_right_lt_deriv_boundary hw hd
      (B := fun _ => w t / 2) (B' := fun _ => 0)
    · linarith
    · intro x
      exact hasDerivAt_const x _
    · intro x hx hxeq
      apply hneg x hx
      linarith
    · exact ht
  linarith

/-- Comparison using a constant only for the pair of curves on this interval.
This is used on small intervals obtained from local state Lipschitz control. -/
private theorem comparison_of_pair_bound {u v u' v' : ℝ → ℝ} {a b L : ℝ}
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hdu : ∀ t ∈ Ico a b, HasDerivWithinAt u (u' t) (Ici t) t)
    (hdv : ∀ t ∈ Ico a b, HasDerivWithinAt v (v' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico a b, v t ≤ u t → u' t - v' t ≤ L * (u t - v t))
    (ha : u a ≤ v a) : ∀ t ∈ Icc a b, u t ≤ v t := by
  let e : ℝ → ℝ := fun t => exp (-(L + 1) * t)
  let w : ℝ → ℝ := fun t => e t * (u t - v t)
  let w' : ℝ → ℝ := fun t => e t * ((u' t - v' t) - (L + 1) * (u t - v t))
  have he (t : ℝ) : HasDerivAt e (e t * (-(L + 1))) t := by
    simpa [e] using (((hasDerivAt_id t).const_mul (-(L + 1))).exp)
  have hwd : ∀ t ∈ Ico a b, HasDerivWithinAt w (w' t) (Ici t) t := by
    intro t ht
    convert (he t).hasDerivWithinAt.mul ((hdu t ht).sub (hdv t ht)) using 1
    dsimp [w, w']
    ring
  have hec : ContinuousOn e (Icc a b) :=
    fun t _ => (he t).continuousAt.continuousWithinAt
  have hwn : ∀ t ∈ Icc a b, w t ≤ 0 := by
    apply nonpos_of_deriv_neg_on_pos
      (hec.mul (hu.sub hv)) hwd
    · dsimp [w]
      exact mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (sub_nonpos.mpr ha)
    · intro t ht hpos
      have hep : 0 < e t := exp_pos _
      have hdiff : 0 < u t - v t := (mul_pos_iff_of_pos_left hep).mp hpos
      have hb := hbound t ht (by linarith)
      have hn : (u' t - v' t) - (L + 1) * (u t - v t) < 0 := by nlinarith
      exact mul_neg_of_pos_of_neg hep hn
  intro t ht
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right (hwn t ht) (exp_pos _))

/-- Comparison under relative local state Lipschitz control. Only continuity
and the indicated one-sided derivatives of the curves are needed here. -/
private theorem comparison_of_local_control {J : Set ℝ} {a b : ℝ}
    {f : ℝ → ℝ → ℝ} {u v u' v' : ℝ → ℝ}
    (hloc : Specs.D13Unified.Ch05.ScalarComparison.localControl f (Icc a b) J)
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (huJ : MapsTo u (Icc a b) J) (_hvJ : MapsTo v (Icc a b) J)
    (hdu : ∀ t ∈ Icc a b, HasDerivWithinAt u (u' t) (Icc a b) t)
    (hdv : ∀ t ∈ Icc a b, HasDerivWithinAt v (v' t) (Icc a b) t)
    (hus : ∀ t ∈ Icc a b, u' t ≤ f t (u t))
    (hvs : ∀ t ∈ Icc a b, f t (v t) ≤ v' t)
    (ha : u a ≤ v a) : ∀ t ∈ Icc a b, u t ≤ v t := by
  have hclosed : IsClosed ({t | u t ≤ v t} ∩ Icc a b) := by
    rw [inter_comm]
    exact (hu.prodMk hv).preimage_isClosed_of_isClosed isClosed_Icc
      OrderClosedTopology.isClosed_le'
  apply hclosed.Icc_subset_of_forall_exists_gt ha
  rintro x ⟨horder, hx⟩ y hy
  change u x ≤ v x at horder
  have hxT : x ∈ Icc a b := Ico_subset_Icc_self hx
  rcases horder.lt_or_eq with hlt | heq
  · have hnear : ∀ᶠ z in 𝓝[Icc a b] x, u z < v z :=
      (hu.prodMk hv) x hxT
        (IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_snd) hlt)
    have hnear' : ∀ᶠ z in 𝓝[>] x, u z < v z :=
      nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem hx) hnear
    exact (hnear'.and (Ioc_mem_nhdsGT hy)).exists.imp
      (fun z hz => ⟨hz.1.le, hz.2⟩)
  · obtain ⟨δ, ρ, L, hδ, hρ, _hL, _hJ, hLip⟩ := hloc x hxT (u x) (huJ hxT)
    have hub : ∀ᶠ z in 𝓝[Icc a b] x, u z ∈ ball (u x) ρ :=
      hu x hxT (ball_mem_nhds _ hρ)
    have hvb : ∀ᶠ z in 𝓝[Icc a b] x, v z ∈ ball (u x) ρ := by
      rw [heq]
      exact hv x hxT (ball_mem_nhds _ hρ)
    have hnear : {z | z ∈ Icc a b ∧ z < y ∧ z ∈ ball x δ ∧
        u z ∈ ball (u x) ρ ∧ v z ∈ ball (u x) ρ} ∈ 𝓝[≥] x := by
      filter_upwards [Icc_mem_nhdsGE_of_mem hx,
        nhdsWithin_le_nhds (Iio_mem_nhds hy),
        nhdsWithin_le_nhds (ball_mem_nhds x hδ),
        nhdsWithin_le_of_mem (Icc_mem_nhdsGE_of_mem hx) hub,
        nhdsWithin_le_of_mem (Icc_mem_nhdsGE_of_mem hx) hvb]
        with z hzT hzy hzx hzu hzv
      exact ⟨hzT, hzy, hzx, hzu, hzv⟩
    obtain ⟨c, hxc, hc⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hnear
    have hsub : Icc x c ⊆ Icc a b := fun t ht => (hc ht).1
    have hlocal : ∀ t ∈ Icc x c, u t ≤ v t := by
      apply comparison_of_pair_bound (L := L) (hu.mono hsub) (hv.mono hsub)
      · intro t ht
        exact (hdu t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ⟨(hsub (Ico_subset_Icc_self ht)).1,
            ht.2.trans_le (hsub (right_mem_Icc.mpr hxc.le)).2⟩)
      · intro t ht
        exact (hdv t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ⟨(hsub (Ico_subset_Icc_self ht)).1,
            ht.2.trans_le (hsub (right_mem_Icc.mpr hxc.le)).2⟩)
      · intro t ht htu
        have htcc := Ico_subset_Icc_self ht
        have hb := hc htcc
        have hl := hLip t ⟨hb.1, hb.2.2.1⟩ (u t) hb.2.2.2.1 (v t) hb.2.2.2.2
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr htu)] at hl
        have hfuv := (le_abs_self (f t (u t) - f t (v t))).trans hl
        have h1 := hus t (hsub htcc)
        have h2 := hvs t (hsub htcc)
        linarith
      · exact heq.le
    exact ⟨c, hlocal c (right_mem_Icc.mpr hxc.le), hxc,
      (hc (right_mem_Icc.mpr hxc.le)).2.1.le⟩

/-- Scalar subsolutions lie below supersolutions on their entire common
closed interval (paper.tex, Theorem d13:05:comparison). -/
theorem scalar_comparison :
    Specs.D13Unified.Ch05.ScalarComparison.scalarComparisonExpected := by
  intro J _hopen _hinterval a b _hab f _hf hloc u v u' v' hu hv huJ hvJ
    hdu hdv hus hvs ha
  exact comparison_of_local_control hloc hu.continuousOn hv.continuousOn huJ hvJ
    hdu hdv hus hvs ha

end D13Unified
