import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.LocalValueSupport
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.PerturbationModels
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.LocalLipschitz
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.Subgradients
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

noncomputable section
open Set Topology Metric
universe u v
namespace VariationalNotes.Ch04
open VariationalNotes.ConvexAnalysis

/-- A minus-infinite fiber propagates to zero by mixing it with a nearby
finite candidate in the opposite direction. No infimum is assumed attained. -/
theorem marginal_ne_bot_of_local_upper_bound
    {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Φ : X × Y → WithTop ℝ) (hc : IsConvex Φ)
    (p r M : ℝ) (h0 : marginal Φ 0 = (p : EReal)) (hr : 0 < r)
    (hM : ∀ u : Y, ‖u‖ < r → marginal Φ u ≤ (M : EReal)) :
    ∀ u, marginal Φ u ≠ ⊥ := by
  intro u hu
  let ε := r / (2 * (‖u‖ + 1))
  have hden : 0 < 2 * (‖u‖ + 1) := by positivity
  have hε : 0 < ε := div_pos hr hden
  have heq : ε * (2 * (‖u‖ + 1)) = r := div_mul_cancel₀ _ hden.ne'
  have hn : ‖(-ε) • u‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hε]
    nlinarith [norm_nonneg u]
  obtain ⟨x, s, hx, hs⟩ := exists_candidate_lt Φ ((-ε) • u) (M + 1)
    ((hM _ hn).trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith)))
  have hd : 0 < 1 + ε := by linarith
  have hab : ε / (1 + ε) + 1 / (1 + ε) = 1 := by field_simp; ring
  have hz : (ε / (1 + ε)) • u + (1 / (1 + ε)) • ((-ε) • u) = 0 := by
    rw [smul_smul, ← add_smul]
    have hz : ε / (1 + ε) + 1 / (1 + ε) * -ε = 0 := by ring
    rw [hz, zero_smul]
  have hbot := marginal_eq_bot_of_left Φ hc u ((-ε) • u) hu x s hx
    (ε / (1 + ε)) (1 / (1 + ε)) (div_pos hε hd) (by positivity) hab
  rw [hz, h0] at hbot
  exact EReal.coe_ne_bot p hbot

/-- Separation of the epigraph gives a continuous subgradient at a locally
bounded finite point, without any global closedness hypothesis. -/
theorem exists_subgradient_of_local_upper_bound
    {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : Y → WithTop ℝ) (hc : IsConvex f)
    (p r M : ℝ) (h0 : f 0 = (p : WithTop ℝ)) (hr : 0 < r)
    (hM : ∀ u : Y, ‖u‖ < r → f u ≤ (M : WithTop ℝ)) :
    ∃ y : Y →L[ℝ] ℝ, y ∈ subdifferential f 0 := by
  let A : Set (Y × ℝ) := epigraph f
  have hAc : Convex ℝ A := hc
  have hInt : (0, M + 1) ∈ interior A := by
    have hopen : IsOpen (ball (0 : Y) r ×ˢ Ioi M) := isOpen_ball.prod isOpen_Ioi
    apply interior_mono (s := ball (0 : Y) r ×ˢ Ioi M) (t := A) ?_
      (by rw [hopen.interior_eq]; exact ⟨mem_ball_self hr, by simp⟩)
    rintro ⟨u, t⟩ ⟨hu, ht⟩
    exact (hM u (by simpa using hu)).trans (WithTop.coe_le_coe.mpr ht.le)
  have hboundary : (0, p) ∉ interior A := by
    intro h
    obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h)
    have hd : ((0 : Y), p - δ / 2) ∈ ball (0, p) δ := by
      rw [mem_ball, Prod.dist_eq]
      simp only [dist_self, Real.dist_eq]
      rw [abs_of_nonpos (by linarith : p - δ / 2 - p ≤ 0)]
      apply max_lt
      · exact hδ
      · linarith
    have hh : f 0 ≤ ((p - δ / 2 : ℝ) : WithTop ℝ) := hb hd
    rw [h0] at hh
    have := WithTop.coe_le_coe.mp hh
    linarith
  obtain ⟨F, hFne, hF⟩ := geometric_hahn_banach_of_nonempty_interior_point
    hAc hboundary ⟨_, hInt⟩
  have hstrict : F (0, M + 1) < F (0, p) := by
    have hopen := F.isOpenMap_of_ne_zero hFne (interior A) isOpen_interior
    have hsub : F '' interior A ⊆ Iic (F (0, p)) := by
      rintro _ ⟨z, hz, rfl⟩
      exact hF z (interior_subset hz)
    have h := interior_maximal hsub hopen (mem_image_of_mem F hInt)
    simpa only [interior_Iic, mem_Iio] using h
  let a : Y →L[ℝ] ℝ := F.comp (ContinuousLinearMap.inl ℝ Y ℝ)
  let c : ℝ := F (0, 1)
  have hsplit (u : Y) (t : ℝ) : F (u, t) = a u + t * c := by
    change F (u, t) = F (u, 0) + t * F (0, 1)
    rw [← smul_eq_mul, ← F.map_smul, ← F.map_add]
    congr 1
    ext <;> simp
  have hpM : p ≤ M := by
    have := hM 0 (by simpa using hr)
    rw [h0] at this
    exact WithTop.coe_le_coe.mp this
  have hcneg : c < 0 := by
    rw [hsplit, hsplit] at hstrict
    simp only [map_zero, zero_add] at hstrict
    nlinarith
  refine ⟨(-c⁻¹) • a, ?_⟩
  apply (mem_subdifferential_iff h0 _).mpr
  intro u
  induction hu : f u using WithTop.recTopCoe with
  | top => exact le_top
  | coe s =>
    have h := hF (u, s) (show (u, s) ∈ A from hu.le)
    rw [hsplit, hsplit] at h
    simp only [map_zero, zero_add] at h
    apply WithTop.coe_le_coe.mpr
    simp only [sub_zero, smul_apply, smul_eq_mul]
    have hcpos : 0 < -c := by linarith
    have hmul := (div_le_iff₀ hcpos).mpr (show a u ≤ (s - p) * -c by nlinarith)
    have heq : a u / -c = -c⁻¹ * a u := by field_simp
    rw [heq] at hmul
    linarith

/-- The original marginal is proper, locally finite and Lipschitz, and has
a continuous supporting functional at zero. -/
theorem local_value_support : Specs.local_value_support.{u,v} := by
  intro X Y _ _ _ _ Φ _ hc p r M h0 hr hM
  have hnb := marginal_ne_bot_of_local_upper_bound Φ hc p r M h0 hr hM
  have hex : ∀ u : Y, ∃ s : WithTop ℝ, toEReal s = Specs.marginal Φ u :=
    fun u => (toEReal_conventions.2.2.2.1 _).mp (hnb u)
  choose f hf using hex
  have hf0 : f 0 = (p : WithTop ℝ) :=
    WithBot.coe_injective ((hf 0).trans h0)
  have hfc : IsConvex f := by
    apply (convex_iff_twoPoint f).mpr
    intro u v r s hu hv a b ha hb hab
    have hmu : marginal Φ u = (r : EReal) :=
      (hf u).symm.trans (congrArg toEReal hu)
    have hmv : marginal Φ v = (s : EReal) :=
      (hf v).symm.trans (congrArg toEReal hv)
    have hh := marginal_convex_finite Φ hc u v r s hmu hmv a b ha hb hab
    rw [← hf (a • u + b • v)] at hh
    exact WithBot.coe_le_coe.mp hh
  have hfM : ∀ u : Y, ‖u‖ < r → f u ≤ (M : WithTop ℝ) := by
    intro u hu
    have hh := hM u hu
    rw [← hf u] at hh
    exact WithBot.coe_le_coe.mp hh
  have hfp : Proper f := ⟨0, hf0 ▸ WithTop.coe_lt_top p⟩
  obtain ⟨U, hU, K, hfin, hLip⟩ := localLipschitz_of_boundedAbove f hfp hfc 0
    ⟨M, Filter.mem_of_superset (Metric.ball_mem_nhds (0 : Y) hr)
      (fun u hu => hfM u (by simpa using hu))⟩
  have hreal (u : Y) (hu : u ∈ U) : f u = (((f u).untopD 0 : ℝ) : WithTop ℝ) := by
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt (hfin u hu))
    rw [← hs, WithTop.untopD_coe]
  have htoReal (u : Y) (hu : u ∈ U) :
      (Specs.marginal Φ u).toReal = (f u).untopD 0 := by
    rw [← hf u, hreal u hu]
    exact EReal.toReal_coe _
  refine ⟨hnb, ⟨U, hU, K, ?_, ?_⟩, ?_⟩
  · intro u hu
    rw [htoReal u hu, ← hf u]
    exact congrArg toEReal (hreal u hu)
  · intro u hu v hv
    dsimp only
    rw [htoReal u hu, htoReal v hv]
    exact hLip hu hv
  · obtain ⟨y, hy⟩ := exists_subgradient_of_local_upper_bound f hfc p r M hf0 hr hfM
    refine ⟨y, fun u => ?_⟩
    have hh := (mem_subdifferential_iff hf0 y).mp hy u
    simp only [sub_zero] at hh
    rw [← hf u]
    exact WithBot.coe_le_coe.mpr hh

end VariationalNotes.Ch04
