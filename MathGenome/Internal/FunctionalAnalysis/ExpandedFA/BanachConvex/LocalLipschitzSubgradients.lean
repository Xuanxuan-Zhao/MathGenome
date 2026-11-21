import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.LocalLipschitzSubgradients
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.SubgradientBasicCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05RealHahnBanach
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FieldSimp

/-! The local part of subgradient calculus, paper.tex:8080–8086.
Reflection and local convex boundedness give local Lipschitz continuity.
Finite right derivatives along lines form a norm-bounded sublinear function;
Hahn–Banach, initialized on the specified line, gives an attaining continuous
subgradient. Finite secants promote its local domination to global support.
No completeness or lower semicontinuity is used. -/

namespace ExpandedFA.BanachConvex

open P1.ExtendedConvexFunctions LocalSpec
open Filter Set Metric
open scoped Topology
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma realValue_eq_of_le (φ : ExtendedFunction X) {y : X} {M : ℝ}
    (hy : φ y ≤ (M : WithTop ℝ)) : φ y = (realValue φ y : WithTop ℝ) := by
  obtain ⟨s, hs, _⟩ := WithTop.le_coe_iff.mp hy
  simp [realValue, hs]

lemma realValue_convexOn (φ : ExtendedFunction X) (hc : ExtendedConvex X φ)
    {C : Set X} (hC : Convex ℝ C) (hfin : ∀ y ∈ C, φ y ≠ ⊤) :
    ConvexOn ℝ C (realValue φ) := by
  refine ⟨hC, ?_⟩
  intro y hy z hz a b ha hb hab
  have hval (w : X) (hw : w ∈ C) : φ w = (realValue φ w : WithTop ℝ) := by
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (hfin w hw)
    simp [realValue, ← hr]
  have hh := hc y z _ _ a b (hval y hy) (hval z hz) ha hb hab
  rw [hval _ (hC hy hz ha hb hab), WithTop.coe_le_coe] at hh
  exact hh

/-- Reflection gives the lower bound on the same closed ball. -/
lemma realValue_ball_bounds (φ : ExtendedFunction X) (x : X) (R M : ℝ)
    (hc : ExtendedConvex X φ) (hR : 0 ≤ R)
    (hM : ∀ y ∈ closedBall x R, φ y ≤ (M : WithTop ℝ)) :
    ∀ y ∈ closedBall x R,
      2 * realValue φ x - M ≤ realValue φ y ∧ realValue φ y ≤ M := by
  have hval (y : X) (hy : y ∈ closedBall x R) := realValue_eq_of_le φ (hM y hy)
  have hx : x ∈ closedBall x R := mem_closedBall_self hR
  have hupper (y : X) (hy : y ∈ closedBall x R) : realValue φ y ≤ M := by
    have hh := hM y hy
    rwa [hval y hy, WithTop.coe_le_coe] at hh
  intro y hy
  have hz : 2 • x - y ∈ closedBall x R := by
    rw [mem_closedBall_iff_norm] at hy ⊢
    have he : (2 • x - y) - x = -(y - x) := by module
    simpa only [he, norm_neg] using hy
  have hh := hc y (2 • x - y) _ _ (1/2) (1/2) (hval y hy) (hval _ hz)
    (by norm_num) (by norm_num) (by norm_num)
  have he : (1/2 : ℝ) • y + (1/2 : ℝ) • (2 • x - y) = x := by module
  rw [he, hval x hx, WithTop.coe_le_coe] at hh
  exact ⟨by linarith [hupper _ hz], hupper y hy⟩

theorem locally_lipschitz_of_ball_bound : LocalSpec.LocalLipschitz.{u} := by
  intro X _ _ φ x R M _ hc hR hM
  have hval (y : X) (hy : y ∈ closedBall x R) := realValue_eq_of_le φ (hM y hy)
  refine ⟨hval, ?_⟩
  have hconv : ConvexOn ℝ (ball x R) (realValue φ) :=
    realValue_convexOn φ hc (convex_ball x R) (fun y hy =>
      ne_top_of_le_ne_top WithTop.coe_ne_top (hM y (ball_subset_closedBall hy)))
  apply ((hconv.continuousOn_tfae isOpen_ball ⟨x, mem_ball_self hR⟩).out 5 1).mp
  intro y hy
  refine ⟨M, ?_⟩
  change ∀ᶠ z in 𝓝 y, realValue φ z ≤ M
  filter_upwards [isOpen_ball.mem_nhds hy] with z hz
  have hh := hM z (ball_subset_closedBall hz)
  rwa [hval z (ball_subset_closedBall hz), WithTop.coe_le_coe] at hh

/-- The pointwise upper bound for a subgradient follows without convexity. -/
lemma subgradient_ball_bound (φ : ExtendedFunction X) (x : X) (R M : ℝ)
    (hR : 0 < R) (hM : ∀ y ∈ closedBall x R, φ y ≤ (M : WithTop ℝ))
    (f : X →L[ℝ] ℝ) (hf : f ∈ subdifferential X φ x) :
    ‖f‖ ≤ (M - realValue φ x) / R := by
  have hx := realValue_eq_of_le φ (hM x (mem_closedBall_self hR.le))
  have hcenter : realValue φ x ≤ M := by
    have hh := hM x (mem_closedBall_self hR.le)
    rwa [hx, WithTop.coe_le_coe] at hh
  have hb : ∀ v : X, ‖v‖ ≤ R → f v ≤ M - realValue φ x := by
    intro v hv
    have hy : x + v ∈ closedBall x R := by
      simpa only [mem_closedBall_iff_norm, add_sub_cancel_left] using hv
    have hh := hf.2 (x + v)
    have hh' := hh.trans (hM _ hy)
    rw [hx, ← WithTop.coe_add, WithTop.coe_le_coe] at hh'
    simp only [add_sub_cancel_left] at hh'
    linarith
  apply f.opNorm_le_bound (div_nonneg (sub_nonneg.mpr hcenter) hR.le)
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hscaled : ‖(R / ‖v‖) • v‖ ≤ R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR hn)]
    exact le_of_eq (div_mul_cancel₀ R hn.ne')
  have hpos := hb ((R / ‖v‖) • v) hscaled
  have hneg := hb (-((R / ‖v‖) • v)) (by simpa only [norm_neg] using hscaled)
  simp only [map_smul, map_neg, smul_eq_mul] at hpos hneg
  have he : (R / ‖v‖) * ((M - realValue φ x) / R * ‖v‖) =
      M - realValue φ x := by field_simp
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · apply (mul_le_mul_iff_right₀ (div_pos hR hn)).mp
    rw [mul_neg, he]
    linarith [hneg]
  · apply (mul_le_mul_iff_right₀ (div_pos hR hn)).mp
    rw [he]
    exact hpos

theorem subgradient_norm_bound : LocalSpec.SubgradientNormBound.{u} := by
  intro X _ _ φ x R M _ _ hR hM f hf
  exact subgradient_ball_bound φ x R M hR hM f hf

/-- Hahn–Banach with a prescribed contact direction, including v = 0. -/
lemma exists_dominated_continuous_support (p : X → ℝ) (hp : P1.IsSublinear p)
    (K : ℝ) (hbound : ∀ w, p w ≤ K * ‖w‖) (v : X) :
    ∃ f : X →L[ℝ] ℝ, (∀ w, f w ≤ p w) ∧ f v = p v := by
  classical
  let hzero : ∀ c : ℝ, c • v = 0 → c • p v = 0 := by
    intro c hc
    rcases smul_eq_zero.mp hc with hc | hv
    · simp [hc]
    · simp [hv, hp.map_zero]
  let l : X →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' v (p v) hzero
  have hl : ∀ w : l.domain, l w ≤ p w := by
    rintro ⟨w, hw⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [LinearPMap.mkSpanSingleton'_apply]
    change c * p v ≤ p (c • v)
    by_cases hc : 0 ≤ c
    · rw [hp.2 c hc v]
    · have hc' : 0 ≤ -c := by linarith
      have he : c • v = (-c) • (-v) := by simp
      rw [he, hp.2 (-c) hc' (-v)]
      have hh := mul_le_mul_of_nonneg_left (hp.neg_le v) hc'
      nlinarith
  obtain ⟨g, hg, hgp⟩ := P1.real_hahn_banach l.domain p hp l.toFun hl
  have hgK (w : X) : ‖g w‖ ≤ K * ‖w‖ := by
    rw [Real.norm_eq_abs, abs_le]
    have hh := (hgp (-w)).trans (hbound (-w))
    simp only [map_neg, norm_neg] at hh
    exact ⟨by linarith, (hgp w).trans (hbound w)⟩
  refine ⟨g.mkContinuous K hgK, hgp, ?_⟩
  change g v = p v
  rw [← l.domain.coe_mk v (Submodule.mem_span_singleton_self v), hg]
  exact LinearPMap.mkSpanSingleton'_apply_self _ _ _ _

/-- Restriction of a convex function to a line has a finite right derivative
at any point in its open domain. -/
lemma exists_directional_limit {C : Set X} (hC : IsOpen C) (u : X → ℝ)
    (hu : ConvexOn ℝ C u) (x : X) (hx : x ∈ C) (v : X) :
    ∃ d : ℝ, Tendsto (fun t : ℝ => (u (x + t • v) - u x) / t)
      (𝓝[>] 0) (𝓝 d) := by
  let S := {t : ℝ | x + t • v ∈ C}
  have he (a b t s : ℝ) (hab : a + b = 1) :
      a • (x + t • v) + b • (x + s • v) = x + (a * t + b * s) • v := by
    calc
      _ = (a • x + b • x) + (a * t + b * s) • v := by module
      _ = _ := by rw [← add_smul, hab, one_smul]
  have hconv : ConvexOn ℝ S (fun t : ℝ => u (x + t • v)) := by
    refine ⟨?_, ?_⟩
    · intro t ht s hs a b ha hb hab
      change x + (a * t + b * s) • v ∈ C
      rw [← he a b t s hab]
      exact hu.1 ht hs ha hb hab
    · intro t ht s hs a b ha hb hab
      simpa only [smul_eq_mul, he a b t s hab] using hu.2 ht hs ha hb hab
  have hS : IsOpen S := hC.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hz : (0 : ℝ) ∈ interior S := by rw [hS.interior_eq]; simpa [S]
  have hd := hconv.hasDerivWithinAt_rightDeriv_of_mem_interior hz
  refine ⟨derivWithin (fun t : ℝ => u (x + t • v)) (Ioi 0) 0, ?_⟩
  have hh := (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi 0 by simp)).mp hd
  have heq : slope (fun t : ℝ => u (x + t • v)) 0 =
      (fun t : ℝ => (u (x + t • v) - u x) / t) := by
    funext t
    simp only [slope_def_field, sub_zero, zero_smul, add_zero]
  rwa [heq] at hh

lemma tendsto_pos_mul_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ => c * t) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [id_eq, mul_zero] using
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0)).const_mul c
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos hc ht

/-- Limits of convex secants form a sublinear function. -/
lemma directional_limits_sublinear {C : Set X} (hC : IsOpen C) (u : X → ℝ)
    (hu : ConvexOn ℝ C u) (x : X) (hx : x ∈ C) (p : X → ℝ)
    (hp : ∀ v, Tendsto (fun t : ℝ => (u (x + t • v) - u x) / t)
      (𝓝[>] 0) (𝓝 (p v))) : P1.IsSublinear p := by
  have hlocal (v : X) : ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • v ∈ C := by
    have hcont : Continuous (fun t : ℝ => x + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact ((hcont.continuousAt (x := 0)).eventually (by simpa using hC.mem_nhds hx)).filter_mono
      nhdsWithin_le_nhds
  have hzero : p 0 = 0 := by
    apply tendsto_nhds_unique (hp 0)
    simpa only [smul_zero, add_zero, sub_self, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))
  refine ⟨?_, ?_⟩
  · intro v w
    have hl := (hp (v + w)).comp (tendsto_pos_mul_zero (1/2) (by norm_num))
    have hr := (hp v).add (hp w)
    apply le_of_tendsto_of_tendsto hl hr
    filter_upwards [hlocal v, hlocal w, self_mem_nhdsWithin] with t hv hw ht
    have hh := hu.2 hv hw (show (0 : ℝ) ≤ 1/2 by norm_num)
      (show (0 : ℝ) ≤ 1/2 by norm_num) (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    have he : (1/2 : ℝ) • (x + t • v) + (1/2 : ℝ) • (x + t • w) =
        x + ((1/2 : ℝ) * t) • (v + w) := by module
    rw [he] at hh
    change (u (x + (1/2 * t) • (v + w)) - u x) / (1/2 * t) ≤
      (u (x + t • v) - u x) / t + (u (x + t • w) - u x) / t
    apply (mul_le_mul_iff_left₀ (show 0 < t from ht)).mp
    have heq : (u (x + (1/2 * t) • (v + w)) - u x) / (1/2 * t) * t =
        2 * (u (x + (1/2 * t) • (v + w)) - u x) := by
      field_simp [ne_of_gt (show 0 < t from ht)]
    rw [heq, add_mul, div_mul_cancel₀ _ ht.ne', div_mul_cancel₀ _ ht.ne']
    change u (x + (1/2 * t) • (v + w)) ≤
      (1/2 : ℝ) * u (x + t • v) + (1/2 : ℝ) * u (x + t • w) at hh
    linarith
  · intro c hc v
    rcases eq_or_lt_of_le hc with hc0 | hcpos
    · simp [← hc0, hzero]
    · have hh := ((hp v).comp (tendsto_pos_mul_zero c hcpos)).const_mul c
      apply tendsto_nhds_unique (hp (c • v))
      apply hh.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      change c * ((u (x + (c * t) • v) - u x) / (c * t)) =
        (u (x + t • (c • v)) - u x) / t
      rw [smul_smul, mul_comm t c]
      field_simp

/-- A local Lipschitz constant bounds every right directional derivative. -/
lemma directional_limits_bound {C : Set X} (hC : IsOpen C) (u : X → ℝ)
    (hLip : LocallyLipschitzOn C u) (x : X) (hx : x ∈ C) (p : X → ℝ)
    (hp : ∀ v, Tendsto (fun t : ℝ => (u (x + t • v) - u x) / t)
      (𝓝[>] 0) (𝓝 (p v))) : ∃ K : ℝ, ∀ v, p v ≤ K * ‖v‖ := by
  obtain ⟨K, s, hs, hK⟩ := hLip hx
  rw [hC.nhdsWithin_eq hx] at hs
  refine ⟨K, fun v => ?_⟩
  apply le_of_tendsto (hp v)
  have hlocal : ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • v ∈ s := by
    have hcont : Continuous (fun t : ℝ => x + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact ((hcont.continuousAt (x := 0)).eventually (by simpa using hs)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hlocal, self_mem_nhdsWithin] with t ht htpos
  have hh := hK.norm_sub_le ht (mem_of_mem_nhds hs)
  simp only [Real.norm_eq_abs, add_sub_cancel_left, norm_smul,
    abs_of_pos (show 0 < t from htpos)] at hh
  apply (div_le_iff₀ htpos).mpr
  have hb := (le_abs_self (u (x + t • v) - u x)).trans hh
  nlinarith

/-- The directional limits lie below every finite secant; each continuous
subgradient lies below these limits. This is the local-to-global convexity step. -/
lemma directional_limits_support (φ : ExtendedFunction X) (u : X → ℝ) (x : X)
    (hc : ExtendedConvex X φ) (hlocal : ∀ᶠ y in 𝓝 x, φ y = (u y : WithTop ℝ))
    (p : X → ℝ) (hp : ∀ v, Tendsto (fun t : ℝ => (u (x + t • v) - u x) / t)
      (𝓝[>] 0) (𝓝 (p v))) :
    (∀ (y : X) (s : ℝ), φ y = (s : WithTop ℝ) → p (y - x) ≤ s - u x) ∧
    (∀ f ∈ subdifferential X φ x, ∀ v : X, f v ≤ p v) := by
  have hx : φ x = (u x : WithTop ℝ) := hlocal.self_of_nhds
  have ht (v : X) : Tendsto (fun t : ℝ => x + t • v) (𝓝[>] 0) (𝓝 x) := by
    have hcont : Continuous (fun t : ℝ => x + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using
      (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  constructor
  · intro y s hy
    apply le_of_tendsto (hp (y - x))
    filter_upwards [(ht (y - x)).eventually hlocal, self_mem_nhdsWithin,
      ((eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds)]
      with t he ht0 ht1
    have hh := hc x y (u x) s (1 - t) t hx hy (by linarith) (le_of_lt ht0) (by ring)
    have hv : (1 - t) • x + t • y = x + t • (y - x) := by module
    rw [hv, he, WithTop.coe_le_coe] at hh
    apply (div_le_iff₀ ht0).mpr
    nlinarith only [hh]
  · intro f hf v
    apply le_of_tendsto_of_tendsto tendsto_const_nhds (hp v)
    filter_upwards [(ht v).eventually hlocal, self_mem_nhdsWithin] with t he ht0
    have hh := (mem_subdifferential_iff_of_value φ x (u x) hx f).mp hf _ _ he
    simp only [add_sub_cancel_left, map_smul, smul_eq_mul] at hh
    apply (le_div_iff₀ ht0).mpr
    nlinarith only [hh]

/-- On an open set where an extended convex function has a locally Lipschitz
real representative, every direction has an attaining continuous subgradient. -/
lemma directional_maximum_of_local_lipschitz (φ : ExtendedFunction X) (u : X → ℝ)
    (C : Set X) (hC : IsOpen C) (hCconv : Convex ℝ C) (hc : ExtendedConvex X φ)
    (hval : ∀ y ∈ C, φ y = (u y : WithTop ℝ))
    (hLip : LocallyLipschitzOn C u) (x : X) (hx : x ∈ C) :
    ∀ v : X, ∃ d : ℝ,
      Tendsto (fun t : ℝ => (u (x + t • v) - u x) / t) (𝓝[>] 0) (𝓝 d) ∧
      (∃ f ∈ subdifferential X φ x, f v = d) ∧
      (∀ f ∈ subdifferential X φ x, f v ≤ d) := by
  classical
  have hu : ConvexOn ℝ C u := by
    refine ⟨hCconv, ?_⟩
    intro y hy z hz a b ha hb hab
    have hh := hc y z (u y) (u z) a b (hval y hy) (hval z hz) ha hb hab
    rwa [hval _ (hCconv hy hz ha hb hab), WithTop.coe_le_coe] at hh
  choose p hp using exists_directional_limit hC u hu x hx
  have hsub := directional_limits_sublinear hC u hu x hx p hp
  obtain ⟨K, hK⟩ := directional_limits_bound hC u hLip x hx p hp
  have hlocal : ∀ᶠ y in 𝓝 x, φ y = (u y : WithTop ℝ) := by
    filter_upwards [hC.mem_nhds hx] with y hy
    exact hval y hy
  obtain ⟨hsupport, hbelow⟩ := directional_limits_support φ u x hc hlocal p hp
  intro v
  obtain ⟨f, hf, hfv⟩ := exists_dominated_continuous_support p hsub K hK v
  have hmem : f ∈ subdifferential X φ x := by
    apply (mem_subdifferential_iff_of_value φ x (u x) (hval x hx) f).mpr
    intro y s hy
    have hh := (hf (y - x)).trans (hsupport y s hy)
    linarith
  exact ⟨p v, hp v, ⟨f, hmem, hfv⟩, fun g hg => hbelow g hg v⟩

theorem subgradients_nonempty_of_ball_bound : LocalSpec.SubgradientsNonempty.{u} := by
  intro X _ _ φ x R M hproper hc hR hM y hy
  obtain ⟨hval, hLip⟩ := locally_lipschitz_of_ball_bound X φ x R M hproper hc hR hM
  obtain ⟨d, hd, ⟨f, hf, _⟩, _⟩ := directional_maximum_of_local_lipschitz
    φ (realValue φ) (ball x R) isOpen_ball (convex_ball x R) hc
    (fun z hz => hval z (ball_subset_closedBall hz)) hLip y hy (0 : X)
  exact ⟨f, hf⟩

theorem directional_derivative_maximum : LocalSpec.DirectionalMaximum.{u} := by
  intro X _ _ φ x R M hproper hc hR hM
  obtain ⟨hval, hLip⟩ := locally_lipschitz_of_ball_bound X φ x R M hproper hc hR hM
  exact directional_maximum_of_local_lipschitz φ (realValue φ) (ball x R)
    isOpen_ball (convex_ball x R) hc (fun z hz => hval z (ball_subset_closedBall hz))
    hLip x (mem_ball_self hR)

end ExpandedFA.BanachConvex
