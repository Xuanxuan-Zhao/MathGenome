import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ContinuousGraphFlux
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff
/-! The continuous-graph analytic step for the corner Stokes argument.
The vertical flux follows from Fubini and the one-dimensional compact-support
FTC. Directed curve substitution follows by composing a continuous primitive
with the original real lift and using FTC off its finite set of joins.
No region geometry, Stokes identity, or differentiable graph height is assumed.
-/
namespace P202.ContinuousGraphFlux
open P202Specs.PlanarRegionTopology P202Specs.ContinuousGraphFlux

theorem unit_coordinates {e : Plane} (he : ‖e‖ = 1) : e 0 ^ 2 + e 1 ^ 2 = 1 := by
  simpa [Fin.sum_univ_two, he] using (EuclideanSpace.real_norm_sq_eq e).symm

/-- The rotation with columns `e` and the prescribed positive quarter turn. -/
def rotation (e : Plane) (he : ‖e‖ = 1) : Plane ≃ₗᵢ[ℝ] Plane where
  toFun v := v 0 • e + v 1 • quarterTurn e
  invFun w := !₂[e 0 * w 0 + e 1 * w 1, -e 1 * w 0 + e 0 * w 1]
  map_add' v w := by simp [add_smul]; abel
  map_smul' a v := by
    ext i
    simp [quarterTurn]
    ring
  left_inv v := by
    have he' := unit_coordinates he
    ext i
    fin_cases i <;> simp [quarterTurn]
    · linear_combination v 0 * he'
    · linear_combination v 1 * he'
  right_inv v := by
    have he' := unit_coordinates he
    ext i
    fin_cases i <;> simp [quarterTurn]
    · linear_combination v 0 * he'
    · linear_combination v 1 * he'
  norm_map' v := by
    have he' := unit_coordinates he
    have h₁ := EuclideanSpace.real_norm_sq_eq (v 0 • e + v 1 • quarterTurn e)
    have h₂ := EuclideanSpace.real_norm_sq_eq v
    simp [Fin.sum_univ_two, quarterTurn] at h₁ h₂
    change ‖v 0 • e + v 1 • quarterTurn e‖ = ‖v‖
    have hsq : ‖v 0 • e + v 1 • quarterTurn e‖ ^ 2 = ‖v‖ ^ 2 := by
      calc
        _ = (v 0 ^ 2 + v 1 ^ 2) * (e 0 ^ 2 + e 1 ^ 2) := by dsimp only [quarterTurn]; rw [h₁]; ring
        _ = _ := by rw [he', mul_one, h₂]
    nlinarith [norm_nonneg (v 0 • e + v 1 • quarterTurn e), norm_nonneg v]

/-- Ordinary product coordinates, transported to the L² plane. -/
def coordinates : (ℝ × ℝ) ≃L[ℝ] Plane :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    (EuclideanSpace.equiv (Fin 2) ℝ).symm

@[simp] theorem coordinates_apply (q : ℝ × ℝ) : coordinates q = !₂[q.1, q.2] := rfl

def frameHomeomorph (p e : Plane) (he : ‖e‖ = 1) : (ℝ × ℝ) ≃ₜ Plane :=
  (coordinates.toHomeomorph.trans (rotation e he).toHomeomorph).trans
    (Homeomorph.addLeft p)

@[simp] theorem frameHomeomorph_apply (p e : Plane) (he : ‖e‖ = 1) (q : ℝ × ℝ) :
    frameHomeomorph p e he q = frame p e q := by
  simp [frameHomeomorph, rotation, frame, add_assoc]

theorem frame_measurePreserving (p e : Plane) (he : ‖e‖ = 1) :
    MeasurePreserving (frame p e) volume volume := by
  have hc : MeasurePreserving coordinates volume volume :=
    (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm
  convert (measurePreserving_add_left volume p).comp
    ((rotation e he).measurePreserving.comp hc) using 1
  ext q
  simp [rotation, frame, add_assoc]

theorem frameTransport : Expected.frameTransport := by
  intro p e he
  exact ⟨⟨rotation e he, fun _ => rfl⟩,
    ⟨frameHomeomorph p e he, funext (frameHomeomorph_apply p e he)⟩,
    frame_measurePreserving p e he⟩

theorem contDiff_frame (p e : Plane) : ContDiff ℝ ∞ (frame p e) :=
  (contDiff_const.add (contDiff_fst.smul contDiff_const)).add
    (contDiff_snd.smul contDiff_const)

theorem frameDerivative : Expected.frameDerivative := by
  intro p e f hf q
  have hF : HasFDerivAt (frame p e)
      (((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight e) +
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (quarterTurn e))) q := by
    convert (((((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := q)).smul_const e).add
      (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := q)).smul_const
        (quarterTurn e))).const_add p) using 1
    ext z
    simp [frame, add_assoc]
  rw [((hf.differentiable one_ne_zero _).hasFDerivAt.comp q hF).fderiv]
  simp

/-- Continuous graphs have singleton vertical sections, hence zero planar volume. -/
theorem graph_coordinates_null (g : ℝ → ℝ) (hg : Continuous g) :
    volume (range (fun x => (x, g x))) = 0 := by
  have hs : range (fun x => (x, g x)) = {q : ℝ × ℝ | g q.1 = q.2} := by
    ext q
    simp [Prod.ext_iff]
  have hm : MeasurableSet {q : ℝ × ℝ | g q.1 = q.2} :=
    (isClosed_eq (hg.comp continuous_fst) continuous_snd).measurableSet
  rw [hs, Measure.volume_eq_prod, Measure.prod_apply hm]
  simp

theorem graph_image (p e : Plane) (g : ℝ → ℝ) :
    graph p e g = frame p e '' range (fun x => (x, g x)) :=
  range_comp (frame p e) (fun x => (x, g x))

theorem graph_null (p e : Plane) (he : ‖e‖ = 1) (g : ℝ → ℝ) (hg : Continuous g) :
    volume (graph p e g) = 0 := by
  let H := frameHomeomorph p e he
  have hH : (H : (ℝ × ℝ) → Plane) = frame p e := funext (frameHomeomorph_apply p e he)
  rw [graph_image, ← hH, ← (frame_measurePreserving p e he).map_eq, ← hH,
    H.measurableEmbedding.map_apply, H.injective.preimage_image]
  exact graph_coordinates_null g hg

theorem epigraph_ae_eq (p e : Plane) (he : ‖e‖ = 1) (g : ℝ → ℝ) (hg : Continuous g) :
    strictEpigraph p e g =ᵐ[volume] closedEpigraph p e g := by
  have hn : ∀ᵐ z : Plane ∂volume, z ∉ graph p e g := by
    rw [ae_iff]
    simpa using graph_null p e he g hg
  filter_upwards [hn] with z hz
  change z ∉ graph p e g at hz
  apply propext
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, show g q.1 ≤ q.2 from le_of_lt hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q, show g q.1 < q.2 from lt_of_le_of_ne hq ?_, rfl⟩
    intro h
    apply hz
    exact ⟨q.1, by simp [h]⟩

theorem graphNull : Expected.graphNull := by
  intro p e he g hg
  exact ⟨graph_null p e he g hg, epigraph_ae_eq p e he g hg⟩

/-- The endpoint at positive infinity is zero by compact support. -/
theorem vertical_slice {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (x a : ℝ) :
    (∫ y in Ioi a, fderiv ℝ f (x, y) (0, 1)) = -f (x, a) := by
  have hd (y : ℝ) : deriv (fun s => f (x, s)) y = fderiv ℝ f (x, y) (0, 1) :=
    ((hf.differentiable one_ne_zero (x, y)).hasFDerivAt.comp_hasDerivAt y
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))).deriv
  have hs : HasCompactSupport (fun s => f (x, s)) := hc.comp_isClosedEmbedding
    (show Isometry (fun s : ℝ => (x, s)) from fun a b => by simp [Prod.edist_eq]).isClosedEmbedding
  have hsm : ContDiff ℝ 1 (fun s : ℝ => f (x, s)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  simpa only [hd] using HasCompactSupport.integral_Ioi_deriv_eq hsm hs a

/-- Fubini over the actual variable lower limit. No derivative of `g` occurs. -/
theorem vertical_coordinates (g : ℝ → ℝ) (hg : Continuous g)
    {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Integrable (fun x => f (x, g x)) ∧
    (∫ q in {q : ℝ × ℝ | g q.1 < q.2}, fderiv ℝ f q (0, 1)) =
      -(∫ x : ℝ, f (x, g x)) := by
  let D : ℝ × ℝ → ℝ := fun q => fderiv ℝ f q (0, 1)
  let S : Set (ℝ × ℝ) := {q | g q.1 < q.2}
  have hS : MeasurableSet S := (isOpen_lt (hg.comp continuous_fst) continuous_snd).measurableSet
  have hi : Integrable D :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (0, 1))
  have hprod : Integrable (S.indicator D) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hi.indicator hS
  have hslice (x : ℝ) : (∫ y : ℝ, S.indicator D (x, y)) = -f (x, g x) := by
    have heq : (fun y => S.indicator D (x, y)) =
        (Ioi (g x)).indicator (fun y => fderiv ℝ f (x, y) (0, 1)) := by
      funext y
      simp [S, D, Set.indicator]
    rw [heq, integral_indicator measurableSet_Ioi]
    exact vertical_slice hf hc x (g x)
  constructor
  · have hh := hprod.integral_prod_left
    simp_rw [hslice] at hh
    simpa using hh.neg
  · rw [← integral_indicator hS, Measure.volume_eq_prod, integral_prod _ hprod]
    simp_rw [hslice]
    exact integral_neg _

theorem verticalFlux : Expected.verticalFlux := by
  intro p e he g hg f hf hc
  have hi : Integrable (fun z => fderiv ℝ f z (quarterTurn e)) :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (quarterTurn e))
  let H := frameHomeomorph p e he
  have hH : (H : (ℝ × ℝ) → Plane) = frame p e := funext (frameHomeomorph_apply p e he)
  have hcf : ContDiff ℝ 1 (f ∘ frame p e) := hf.comp ((contDiff_frame p e).of_le (by simp))
  have hcs : HasCompactSupport (f ∘ frame p e) := by
    rw [← hH]
    exact hc.comp_homeomorph H
  obtain ⟨htrace, hflux⟩ := vertical_coordinates g hg hcf hcs
  have hstrict : (∫ z in strictEpigraph p e g, fderiv ℝ f z (quarterTurn e)) =
      -(∫ x : ℝ, f (frame p e (x, g x))) := by
    change (∫ z in frame p e '' {q : ℝ × ℝ | g q.1 < q.2},
      fderiv ℝ f z (quarterTurn e)) = _
    rw [(frame_measurePreserving p e he).setIntegral_image_emb
      (hH ▸ H.measurableEmbedding)]
    simpa only [frameDerivative p e f hf, Function.comp_apply] using hflux
  exact ⟨hi, htrace, hi.integrableOn, hi.integrableOn, hstrict,
    (setIntegral_congr_set (epigraph_ae_eq p e he g hg).symm).trans hstrict⟩

theorem realLift_continuous (c : RegularJordanCurve) :
    Continuous (realLift c.parametrization) :=
  c.parametrization.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))

/-- Smooth one-sided extensions bound the actual derivative on both sides,
including its totalized value at a nondifferentiable join. -/
theorem realLift_deriv_locally_bounded (c : RegularJordanCurve) (t : ℝ) :
    ∃ N ∈ 𝓝 t, Bornology.IsBounded ((deriv (realLift c.parametrization)) '' N) := by
  obtain ⟨d, l, r, hd, hl, hr, hel, her, _⟩ := c.regular_joins t
  let J := Icc (t - d / 2) (t + d / 2)
  have hJ : J ⊆ Ioo (t - d) (t + d) := by
    intro x hx
    dsimp [J] at hx
    constructor <;> linarith [hx.1, hx.2]
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hl.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).mono hJ)
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hr.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).mono hJ)
  have hel' : EqOn (deriv l) (deriv (realLift c.parametrization)) (Ioo (t - d) t) :=
    (hel.mono Ioo_subset_Icc_self).deriv isOpen_Ioo
  have her' : EqOn (deriv r) (deriv (realLift c.parametrization)) (Ioo t (t + d)) :=
    (her.mono Ioo_subset_Icc_self).deriv isOpen_Ioo
  refine ⟨Ioo (t - d / 2) (t + d / 2), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max (max L R) ‖deriv (realLift c.parametrization) t‖, ?_⟩
  rintro y ⟨s, hs, rfl⟩
  have hsJ : s ∈ J := ⟨hs.1.le, hs.2.le⟩
  rcases lt_trichotomy s t with hst | rfl | hts
  · rw [← hel' (by constructor <;> linarith [hs.1])]
    exact (hL s hsJ).trans ((le_max_left L R).trans (le_max_left _ _))
  · exact le_max_right _ _
  · rw [← her' (by constructor <;> linarith [hs.2])]
    exact (hR s hsJ).trans ((le_max_right L R).trans (le_max_left _ _))

theorem realLift_deriv_bounded (c : RegularJordanCurve) (a b : ℝ) :
    ∃ L : ℝ, ∀ t ∈ uIcc a b, ‖deriv (realLift c.parametrization) t‖ ≤ L := by
  obtain ⟨L, hL⟩ := (Bornology.isBounded_image_of_isLocallyBounded_of_isCompact
    (s := uIcc a b) isCompact_uIcc (realLift_deriv_locally_bounded c)).exists_norm_le
  exact ⟨L, fun t ht => hL _ (mem_image_of_mem _ ht)⟩

theorem curve_integrable (c : RegularJordanCurve) (e : Plane)
    {f : Plane → ℝ} (hf : Continuous f) (a b : ℝ) :
    IntervalIntegrable (fun t => f (realLift c.parametrization t) *
      inner ℝ e (deriv (realLift c.parametrization) t)) volume a b := by
  let γ := realLift c.parametrization
  have hγ : Continuous γ := realLift_continuous c
  have hcomp : Continuous (fun t => f (γ t)) := hf.comp hγ
  obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn
    (hcomp.continuousOn : ContinuousOn (fun t => f (γ t)) (uIcc a b))
  obtain ⟨L, hL⟩ := realLift_deriv_bounded c a b
  have hMpos : 0 ≤ M := (norm_nonneg _).trans (hM a (left_mem_uIcc))
  have hm : Measurable (fun t => f (γ t) * inner ℝ e (deriv γ t)) :=
    hcomp.measurable.mul ((innerSL ℝ e).continuous.measurable.comp (measurable_deriv γ))
  have hint : IntegrableOn (fun t => f (γ t) * inner ℝ e (deriv γ t)) (uIcc a b) := by
    apply (integrableOn_const (C := M * (‖e‖ * L)) (μ := volume) (s := uIcc a b)
      isCompact_uIcc.measure_ne_top).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIcc] with t ht
    rw [norm_mul]
    apply mul_le_mul (hM t ht) _ (norm_nonneg _) hMpos
    exact (norm_inner_le_norm e (deriv γ t)).trans
      (mul_le_mul_of_nonneg_left (hL t ht) (norm_nonneg e))
  exact hint.intervalIntegrable

/-- Any interval of length less than one embeds in one quotient period. -/
theorem short_interval_in_period {a b : ℝ} (hab : |b - a| < 1) :
    uIcc a b ⊆ Ico (min a b) (min a b + 1) := by
  intro t ht
  rw [uIcc] at ht
  refine ⟨ht.1, ?_⟩
  have hh : max a b - min a b < 1 := by rwa [max_sub_min_eq_abs]
  linarith [ht.2]

theorem join_times_finite (c : RegularJordanCurve) {a b : ℝ} (hab : |b - a| < 1) :
    {t ∈ uIcc a b | (t : ParameterCircle) ∈ c.joins}.Finite := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  apply Set.Finite.of_injOn (f := fun t : ℝ => (t : ParameterCircle))
    (t := (c.joins : Set ParameterCircle)) (fun t ht => ht.2) _ c.joins.finite_toSet
  intro x hx y hy hxy
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (short_interval_in_period hab hx.1) (short_interval_in_period hab hy.1)).mp hxy

theorem removeJoins_ae_eq (c : RegularJordanCurve) {a b : ℝ} (hab : |b - a| < 1)
    (h : ℝ → ℝ) : removeJoins c h =ᵐ[volume.restrict (uIoc a b)] h := by
  filter_upwards [ae_restrict_of_ae ((join_times_finite c hab).countable.ae_notMem volume),
    ae_restrict_mem measurableSet_uIoc] with t ht hI
  have hj : (t : ParameterCircle) ∉ c.joins :=
    fun hj => ht ⟨uIoc_subset_uIcc hI, hj⟩
  simp [removeJoins, hj]

theorem finiteJoinRemoval : Expected.finiteJoinRemoval := by
  intro c a b hab
  refine ⟨join_times_finite c hab, fun h => ⟨?_, ?_⟩⟩
  · exact intervalIntegrable_congr_ae (removeJoins_ae_eq c hab h)
  · exact intervalIntegral.integral_congr_ae_restrict (removeJoins_ae_eq c hab h)

theorem projection_continuous (c : RegularJordanCurve) (p e : Plane) :
    Continuous (projection c p e) :=
  continuous_const.inner ((realLift_continuous c).sub continuous_const)

theorem projection_hasDerivAt (c : RegularJordanCurve) (p e : Plane) {t : ℝ}
    (ht : (t : ParameterCircle) ∉ c.joins) :
    HasDerivAt (projection c p e)
      (inner ℝ e (deriv (realLift c.parametrization) t)) t := by
  have hd := ((c.smooth_off_joins t ht).differentiableAt (by simp)).hasDerivAt
  exact (innerSL ℝ e).hasFDerivAt.comp_hasDerivAt t (hd.sub_const p)

/-- A continuous primitive permits substitution across all the finitely many
joins at once. No inverse-graph derivative or monotonicity is needed for this
stronger form of the directed substitution identity. -/
theorem parameter_substitution (c : RegularJordanCurve) (p e : Plane)
    (g : ℝ → ℝ) (hg : Continuous g) (f : Plane → ℝ) (hf : Continuous f)
    (a b : ℝ) (hab : |b - a| < 1)
    (harc : ∀ t ∈ uIcc a b, realLift c.parametrization t =
      frame p e (projection c p e t, g (projection c p e t))) :
    (∫ t in a..b, f (realLift c.parametrization t) *
      inner ℝ e (deriv (realLift c.parametrization) t)) =
      ∫ x in projection c p e a..projection c p e b, f (frame p e (x, g x)) := by
  let u := projection c p e
  let K : ℝ → ℝ := fun x => f (frame p e (x, g x))
  let G : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..x, K y
  let D : ℝ → ℝ := fun t => f (realLift c.parametrization t) *
    inner ℝ e (deriv (realLift c.parametrization) t)
  let J : Set ℝ := {t ∈ uIcc a b | (t : ParameterCircle) ∈ c.joins}
  have hK : Continuous K :=
    hf.comp (((contDiff_frame p e).continuous).comp (continuous_id.prodMk hg))
  have hGder (x : ℝ) : HasDerivAt G (K x) x :=
    intervalIntegral.integral_hasDerivAt_right (hK.intervalIntegrable 0 x)
      (hK.stronglyMeasurableAtFilter volume (𝓝 x)) hK.continuousAt
  have hG : Continuous G := continuous_iff_continuousAt.mpr fun x => (hGder x).continuousAt
  have hEq (t : ℝ) (ht : t ∈ uIcc a b) : K (u t) = f (realLift c.parametrization t) :=
    congrArg f (harc t ht).symm
  have hint : IntervalIntegrable D volume a b := curve_integrable c e hf a b
  have hd : ∀ t ∈ Ioo (min a b) (max a b) \ J, HasDerivAt (G ∘ u) (D t) t := by
    intro t ht
    have htI : t ∈ uIcc a b := ⟨ht.1.1.le, ht.1.2.le⟩
    have htJ : (t : ParameterCircle) ∉ c.joins := fun hj => ht.2 ⟨htI, hj⟩
    simpa only [D, hEq t htI] using
      (hGder (u t)).comp t (projection_hasDerivAt c p e htJ)
  calc
    _ = G (u b) - G (u a) :=
      integral_eq_of_hasDerivAt_off_countable (G ∘ u) D
        (join_times_finite c hab).countable
        (hG.comp (projection_continuous c p e)).continuousOn hd hint
    _ = _ := intervalIntegral.integral_interval_sub_left
      (hK.intervalIntegrable 0 (u b)) (hK.intervalIntegrable 0 (u a))

theorem parameterSubstitution : Expected.parameterSubstitution := by
  intro c p e _ g hg f hf a b hab _ harc
  refine ⟨curve_integrable c e hf a b, ?_,
    parameter_substitution c p e g hg f hf a b hab harc⟩
  exact (hf.comp (((contDiff_frame p e).continuous).comp
    (continuous_id.prodMk hg))).intervalIntegrable _ _

end P202.ContinuousGraphFlux
