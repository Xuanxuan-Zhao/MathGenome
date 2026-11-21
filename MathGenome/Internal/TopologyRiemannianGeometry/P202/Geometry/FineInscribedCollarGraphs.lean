import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.FineInscribedCollarGraphs
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PlanarRegionCornerCollar
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Module

/-!
Affine transverse collars and continuous height graphs for sufficiently fine
literal inscribed polygons. The actual collar inverse projects each edge onto
its original sample interval; compactness assembles the global graph.
-/
noncomputable section
open Set Topology Filter
open scoped ContDiff
set_option maxHeartbeats 800000

namespace P202.FineInscribedCollarGraphs
open P202Specs.PlanarRegionTopology
open P202Specs.PlaneTurning
open P202Specs.FineInscribedCollarGraphs
open P202.PlanarRegionTopology

/-- The oriented quarter turn in the fixed Euclidean coordinates has exactly
one of the two possible signs. -/
lemma rotation_eq_signed_quarterTurn (o : Orientation ℝ Plane (Fin 2)) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ v : Plane,
      o.rightAngleRotation v = σ • quarterTurn v := by
  let x : Plane := !₂[1, 0]
  let y : Plane := !₂[0, 1]
  let J := o.rightAngleRotation
  let σ : ℝ := J x 1
  have hx : J x 0 = 0 := by
    have h := o.inner_rightAngleRotation_self x
    simpa [x, PiLp.inner_apply, Fin.sum_univ_two] using h
  have hy : J y 1 = 0 := by
    have h := o.inner_rightAngleRotation_self y
    simpa [y, PiLp.inner_apply, Fin.sum_univ_two] using h
  have hxy : J y 0 = -σ := by
    have h := o.inner_rightAngleRotation_swap x y
    simpa [x, y, σ, PiLp.inner_apply, Fin.sum_univ_two] using h
  have hxvec : J x = !₂[0, σ] := by
    ext i
    fin_cases i <;> simp [hx, σ]
  have hyvec : J y = !₂[-σ, 0] := by
    ext i
    fin_cases i <;> simp [hy, hxy]
  have hxscale : J x = σ • y := by
    rw [hxvec]
    ext i
    fin_cases i <;> simp [y]
  have hsq : σ * σ = 1 := by
    have h := congrArg (fun v : Plane => v 0) (o.rightAngleRotation_rightAngleRotation x)
    change J (J x) 0 = (-x) 0 at h
    rw [hxscale, map_smul, hyvec] at h
    simp [x] at h
    nlinarith
  refine ⟨σ, ?_, ?_⟩
  · rcases eq_or_eq_neg_of_sq_eq_sq σ 1 (by nlinarith [hsq]) with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro v
    have hv : v = v 0 • x + v 1 • y := by
      ext i
      fin_cases i <;> simp [x, y]
    conv_lhs => rw [hv, map_add, map_smul, map_smul, hxvec, hyvec]
    ext i
    fin_cases i <;> simp [quarterTurn] <;> ring

/-- Reversing only the fiber coordinate preserves the same symmetric source. -/
lemma negate_collar_fibers (c : RegularJordanCurve) (W : C(ParameterCircle, Plane))
    (a : ℝ) (e : OpenPartialHomeomorph (ParameterCircle × ℝ) Plane)
    (he : e.source = univ ×ˢ Ioo (-a) a)
    (hf : ∀ z, e z = c.parametrization z.1 + z.2 • W z.1) :
    ∃ g : OpenPartialHomeomorph (ParameterCircle × ℝ) Plane,
      g.source = univ ×ˢ Ioo (-a) a ∧
      ∀ z, g z = c.parametrization z.1 + z.2 • (-W z.1) := by
  let H : (ParameterCircle × ℝ) ≃ₜ (ParameterCircle × ℝ) :=
    (Homeomorph.refl ParameterCircle).prodCongr (Homeomorph.neg ℝ)
  let g := H.toOpenPartialHomeomorph.trans e
  refine ⟨g, ?_, ?_⟩
  · ext z
    simp [g, H, he]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  · intro z
    change e (z.1, -z.2) = _
    rw [hf]
    simp

/-- Construction of a bicollar for every orientation, retaining the original
parametrization and a globally affine formula. -/
theorem collarExists : Expected.collarExists := by
  intro c o
  obtain ⟨W, hWoff, hWjoin⟩ := curve_transverse_field c
  obtain ⟨a, e, ha, he, hf⟩ := curve_bicollar_of_transverse_field c W hWoff hWjoin
  obtain ⟨sign, hsign, hrot⟩ := rotation_eq_signed_quarterTurn o
  rcases hsign with rfl | rfl
  · refine ⟨⟨W, a, e, ha, he, hf, ?_⟩⟩
    intro t ht
    simpa only [hrot, one_smul] using hWoff t ht
  · obtain ⟨g, hg, hgf⟩ := negate_collar_fibers c W a e he hf
    refine ⟨⟨-W, a, g, ha, hg, ?_, ?_⟩⟩
    · simpa using hgf
    · intro t ht
      obtain ⟨hs, hp⟩ := hWoff t ht
      refine ⟨hs.neg, ?_⟩
      simpa only [ContinuousMap.neg_apply, hrot, neg_one_smul, inner_neg_neg] using hp


/-- Strict positivity persists jointly in the sample point and varying covector. -/
theorem uniform_projection_across_join {c : RegularJordanCurve} {t δ : ℝ}
    {l r : ℝ → Plane} {a : ℝ → Plane} (hδ : 0 < δ)
    (hl : ContDiffOn ℝ ∞ l (Ioo (t - δ) (t + δ)))
    (hr : ContDiffOn ℝ ∞ r (Ioo (t - δ) (t + δ)))
    (hel : EqOn l (realLift c.parametrization) (Icc (t - δ) t))
    (her : EqOn r (realLift c.parametrization) (Icc t (t + δ)))
    (ha : ContinuousAt a t)
    (hpl : 0 < inner ℝ (a t) (deriv l t))
    (hpr : 0 < inner ℝ (a t) (deriv r t)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ Icc (t - ε) (t + ε),
      StrictMonoOn (fun s => inner ℝ (a q) (realLift c.parametrization s))
        (Icc (t - ε) (t + ε)) := by
  have ht : t ∈ Ioo (t - δ) (t + δ) := ⟨by linarith, by linarith⟩
  have hcl : ContinuousAt (deriv l) t :=
    (hl.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).continuousAt
      (isOpen_Ioo.mem_nhds ht)
  have hcr : ContinuousAt (deriv r) t :=
    (hr.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).continuousAt
      (isOpen_Ioo.mem_nhds ht)
  have ha₂ : ContinuousAt (fun p : ℝ × ℝ => a p.1) (t, t) :=
    ContinuousAt.comp (g := a) ha continuousAt_fst
  have hcl₂ : ContinuousAt (fun p : ℝ × ℝ => deriv l p.2) (t, t) :=
    ContinuousAt.comp (g := deriv l) hcl continuousAt_snd
  have hcr₂ : ContinuousAt (fun p : ℝ × ℝ => deriv r p.2) (t, t) :=
    ContinuousAt.comp (g := deriv r) hcr continuousAt_snd
  have hcontl : ContinuousAt (fun p : ℝ × ℝ =>
      inner ℝ (a p.1) (deriv l p.2)) (t, t) := ha₂.inner (𝕜 := ℝ) hcl₂
  have hcontr : ContinuousAt (fun p : ℝ × ℝ =>
      inner ℝ (a p.1) (deriv r p.2)) (t, t) := ha₂.inner (𝕜 := ℝ) hcr₂
  have hposl : ∀ᶠ p : ℝ × ℝ in 𝓝 (t, t),
      0 < inner ℝ (a p.1) (deriv l p.2) :=
    hcontl.eventually (Ioi_mem_nhds hpl)
  have hposr : ∀ᶠ p : ℝ × ℝ in 𝓝 (t, t),
      0 < inner ℝ (a p.1) (deriv r p.2) :=
    hcontr.eventually (Ioi_mem_nhds hpr)
  obtain ⟨η, hη, hηball⟩ := Metric.mem_nhds_iff.mp (hposl.and hposr)
  let ε := min δ η / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; have := min_le_left δ η; linarith
  have hεη : ε < η := by dsimp [ε]; have := min_le_right δ η; linarith
  have hsmall : ∀ q ∈ Icc (t - ε) (t + ε), ∀ s ∈ Icc (t - ε) (t + ε),
      s ∈ Ioo (t - δ) (t + δ) ∧
      0 < inner ℝ (a q) (deriv l s) ∧ 0 < inner ℝ (a q) (deriv r s) := by
    intro q hq s hs
    refine ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    apply hηball (a := (q, s))
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor <;> rw [Real.dist_eq, abs_lt] <;>
      constructor <;> linarith [hq.1, hq.2, hs.1, hs.2]
  have hsubL : Icc (t - ε) t ⊆ Ioo (t - δ) (t + δ) := by
    intro s hs
    exact (hsmall t ⟨by linarith, by linarith⟩ s ⟨hs.1, by linarith [hs.2]⟩).1
  have hsubR : Icc t (t + ε) ⊆ Ioo (t - δ) (t + δ) := by
    intro s hs
    exact (hsmall t ⟨by linarith, by linarith⟩ s ⟨by linarith [hs.1], hs.2⟩).1
  refine ⟨ε, hε, ?_⟩
  intro q hq
  have hlmono : StrictMonoOn (fun s => inner ℝ (a q) (l s)) (Icc (t - ε) t) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      ((continuousOn_const.inner (hl.continuousOn.mono hsubL)))
    intro s hs
    have hs' := interior_subset hs
    have hds : DifferentiableAt ℝ l s :=
      ((hl s (hsubL hs')).contDiffAt (isOpen_Ioo.mem_nhds (hsubL hs'))).differentiableAt
        (by simp)
    rw [deriv_inner_apply ℝ (differentiableAt_const (a q)) hds]
    simpa using (hsmall q hq s ⟨hs'.1, by linarith [hs'.2]⟩).2.1
  have hrmono : StrictMonoOn (fun s => inner ℝ (a q) (r s)) (Icc t (t + ε)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      ((continuousOn_const.inner (hr.continuousOn.mono hsubR)))
    intro s hs
    have hs' := interior_subset hs
    have hds : DifferentiableAt ℝ r s :=
      ((hr s (hsubR hs')).contDiffAt (isOpen_Ioo.mem_nhds (hsubR hs'))).differentiableAt
        (by simp)
    rw [deriv_inner_apply ℝ (differentiableAt_const (a q)) hds]
    simpa using (hsmall q hq s ⟨by linarith [hs'.1], hs'.2⟩).2.2
  refine strictMonoOn_across_join hε hlmono hrmono ?_ ?_
  · exact hel.mono (by intro s hs; exact ⟨by linarith [hs.1], hs.2⟩)
  · exact her.mono (by intro s hs; exact ⟨hs.1, by linarith [hs.2]⟩)

/-- A continuous varying transversal is positive on nearby ordered secants,
with the arbitrary orientation retained in the assertion. -/
theorem uniform_secant_transversality (o : Orientation ℝ Plane (Fin 2))
    {c : RegularJordanCurve} {t δ : ℝ} {l r W : ℝ → Plane} (hδ : 0 < δ)
    (hl : ContDiffOn ℝ ∞ l (Ioo (t - δ) (t + δ)))
    (hr : ContDiffOn ℝ ∞ r (Ioo (t - δ) (t + δ)))
    (hel : EqOn l (realLift c.parametrization) (Icc (t - δ) t))
    (her : EqOn r (realLift c.parametrization) (Icc t (t + δ)))
    (hW : ContinuousAt W t)
    (hpl : 0 < inner ℝ (W t) (o.rightAngleRotation (deriv l t)))
    (hpr : 0 < inner ℝ (W t) (o.rightAngleRotation (deriv r t))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ Icc (t - ε) (t + ε),
      ∀ s ∈ Icc (t - ε) (t + ε), ∀ u ∈ Icc (t - ε) (t + ε), s < u →
        0 < inner ℝ (W q) (o.rightAngleRotation
          (realLift c.parametrization u - realLift c.parametrization s)) := by
  have ha : ContinuousAt (fun q => -o.rightAngleRotation (W q)) t :=
    (o.rightAngleRotation.continuous.continuousAt.comp hW).neg
  have heq : ∀ w v : Plane,
      inner ℝ (-o.rightAngleRotation w) v = inner ℝ w (o.rightAngleRotation v) := by
    intro w v
    rw [inner_neg_left, o.inner_rightAngleRotation_swap', neg_neg]
  obtain ⟨ε, hε, hm⟩ := uniform_projection_across_join hδ hl hr hel her ha
    (by simpa only [heq] using hpl) (by simpa only [heq] using hpr)
  refine ⟨ε, hε, ?_⟩
  intro q hq s hs u hu hsu
  have h := sub_pos.mpr (hm q hq hs hu hsu)
  rw [← inner_sub_right, heq] at h
  exact h

/-- No two distinct points of a chord can have the same actual affine fiber
when the chord is strictly transverse to the fibers it meets. -/
theorem affine_fiber_projection_injective (o : Orientation ℝ Plane (Fin 2))
    {X : Type*} {S : Set ℝ} (γ W : X → Plane) (q : ℝ → X) (r : ℝ → ℝ)
    (b E : Plane)
    (hfib : ∀ s ∈ S, b + s • E = γ (q s) + r s • W (q s))
    (htrans : ∀ s ∈ S, 0 < inner ℝ (W (q s)) (o.rightAngleRotation E)) :
    Set.InjOn q S := by
  intro s hs t ht hst
  let a := -o.rightAngleRotation (W (q s))
  have horth : inner ℝ a (W (q s)) = 0 := by
    simp [a, o.inner_rightAngleRotation_self]
  have hpos : 0 < inner ℝ a E := by
    simpa only [a, inner_neg_left, o.inner_rightAngleRotation_swap', neg_neg]
      using htrans s hs
  have h₁ := congrArg (fun x => inner ℝ a x) (hfib s hs)
  have h₂ := congrArg (fun x => inner ℝ a x) (hfib t ht)
  rw [← hst] at h₂
  simp only [inner_add_right, inner_smul_right, horth, mul_zero, add_zero] at h₁ h₂
  nlinarith


/-- A continuous varying transverse field pairs positively with all nearby secants,
including secants crossing a noncuspidal join. -/
theorem standard_uniform_secant_transversality {c : RegularJordanCurve} {t δ : ℝ}
    {l r W : ℝ → Plane} (hδ : 0 < δ)
    (hl : ContDiffOn ℝ ∞ l (Ioo (t - δ) (t + δ)))
    (hr : ContDiffOn ℝ ∞ r (Ioo (t - δ) (t + δ)))
    (hel : EqOn l (realLift c.parametrization) (Icc (t - δ) t))
    (her : EqOn r (realLift c.parametrization) (Icc t (t + δ)))
    (hW : ContinuousAt W t)
    (hpl : 0 < inner ℝ (W t) (quarterTurn (deriv l t)))
    (hpr : 0 < inner ℝ (W t) (quarterTurn (deriv r t))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ Icc (t - ε) (t + ε),
      ∀ s ∈ Icc (t - ε) (t + ε), ∀ u ∈ Icc (t - ε) (t + ε), s < u →
        0 < inner ℝ (W q) (quarterTurn
          (realLift c.parametrization u - realLift c.parametrization s)) := by
  have hQ : Continuous quarterTurn := by unfold quarterTurn; fun_prop
  have ha : ContinuousAt (fun q => -quarterTurn (W q)) t :=
    ((hQ.continuousAt).comp hW).neg
  obtain ⟨ε, hε, hm⟩ := uniform_projection_across_join hδ hl hr hel her ha
    (by simpa only [inner_neg_quarterTurn_left] using hpl)
    (by simpa only [inner_neg_quarterTurn_left] using hpr)
  refine ⟨ε, hε, ?_⟩
  intro q hq s hs u hu hsu
  have h := sub_pos.mpr (hm q hq hs hu hsu)
  rw [← inner_sub_right, inner_neg_quarterTurn_left] at h
  exact h


/-- The field supplied by the actual corner construction controls all nearby
secants at every lifted parameter, including either side of the period cut. -/
lemma standard_field_local_secants (c : RegularJordanCurve)
    (W : C(ParameterCircle, Plane))
    (hWoff : ∀ t : ℝ, (t : ParameterCircle) ∉ c.joins →
      ContDiffAt ℝ ∞ (realLift W) t ∧
        0 < inner ℝ (W (t : ParameterCircle))
          (quarterTurn (deriv (realLift c.parametrization) t)))
    (hWjoin : ∀ q ∈ c.joins, ∃ w : Plane, w ≠ 0 ∧ W =ᶠ[𝓝 q] (fun _ => w) ∧
      HasStrictJoinTransversality c q w) :
    ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ Icc (t - ε) (t + ε),
      ∀ s ∈ Icc (t - ε) (t + ε), ∀ u ∈ Icc (t - ε) (t + ε), s < u →
        0 < inner ℝ (W (q : ParameterCircle)) (quarterTurn
          (realLift c.parametrization u - realLift c.parametrization s)) := by
  intro t
  have hWreal : Continuous (realLift W) := W.continuous.comp continuous_quotient_mk'
  by_cases ht : (t : ParameterCircle) ∈ c.joins
  · obtain ⟨w, -, hconst, s, δ, l, r, hs, hδ, hl, hr, hel, her, hpl, hpr⟩ :=
      hWjoin (t : ParameterCircle) ht
    have hWs : W (s : ParameterCircle) = w := by
      rw [hs]
      exact hconst.eq_of_nhds
    obtain ⟨ε, hε, hm⟩ := standard_uniform_secant_transversality hδ hl hr hel her
      (hWreal.continuousAt (x := s))
      (by simpa only [realLift, hWs] using hpl)
      (by simpa only [realLift, hWs] using hpr)
    have hshift : ∀ x : ℝ, ((x + s - t : ℝ) : ParameterCircle) = (x : ParameterCircle) := by
      intro x
      simp only [AddCircle.coe_sub, AddCircle.coe_add, hs, add_sub_cancel_right]
    refine ⟨ε, hε, ?_⟩
    intro q hq x hx y hy hxy
    have hp := hm (q + s - t) ⟨by linarith [hq.1], by linarith [hq.2]⟩
      (x + s - t) ⟨by linarith [hx.1], by linarith [hx.2]⟩
      (y + s - t) ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith)
    simpa only [realLift, hshift] using hp
  · obtain ⟨δ, l, r, hδ, hl, hr, hel, her, -, -, -⟩ := c.regular_joins t
    have hleft : DifferentiableAt ℝ l t :=
      (hl.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)).differentiableAt
        (by simp)
    have hcurve := (c.smooth_off_joins t ht).differentiableAt (by simp)
    have hdl := deriv_eq_of_eqOn_left hδ hleft hcurve hel
    have hdr := right_extension_deriv hδ hcurve hr her
    exact standard_uniform_secant_transversality hδ hl hr hel her hWreal.continuousAt
      (by simpa only [realLift, hdl] using (hWoff t ht).2)
      (by simpa only [realLift, ← hdr] using (hWoff t ht).2)

/-- The arbitrary-orientation collar can retain all the joint secant estimates
needed to control projection of literal inscribed edges. -/
theorem collarWithLocalSecants : Expected.collarWithLocalSecants := by
  intro c o
  obtain ⟨W, hWoff, hWjoin⟩ := curve_transverse_field c
  obtain ⟨a, e, ha, he, hf⟩ := curve_bicollar_of_transverse_field c W hWoff hWjoin
  have hlocal := standard_field_local_secants c W hWoff hWjoin
  obtain ⟨sign, hsign, hrot⟩ := rotation_eq_signed_quarterTurn o
  rcases hsign with rfl | rfl
  · refine ⟨⟨W, a, e, ha, he, hf, ?_⟩, ?_⟩
    · intro t ht
      simpa only [hrot, one_smul] using hWoff t ht
    · intro t
      obtain ⟨ε, hε, hm⟩ := hlocal t
      refine ⟨ε, hε, ?_⟩
      intro q hq s hs u hu hsu
      simpa only [hrot, one_smul] using hm q hq s hs u hu hsu
  · obtain ⟨g, hg, hgf⟩ := negate_collar_fibers c W a e he hf
    refine ⟨⟨-W, a, g, ha, hg, ?_, ?_⟩, ?_⟩
    · simpa using hgf
    · intro t ht
      obtain ⟨hs, hp⟩ := hWoff t ht
      refine ⟨hs.neg, ?_⟩
      simpa only [ContinuousMap.neg_apply, hrot, neg_one_smul, inner_neg_neg] using hp
    · intro t
      obtain ⟨ε, hε, hm⟩ := hlocal t
      refine ⟨ε, hε, ?_⟩
      intro q hq s hs u hu hsu
      simpa only [ContinuousMap.neg_apply, hrot, neg_one_smul, inner_neg_neg]
        using hm q hq s hs u hu hsu

lemma uniform_inverse_control {c : RegularJordanCurve}
    {o : Orientation ℝ Plane (Fin 2)} (D : TransverseCollar c o)
    {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (q : ParameterCircle) (z : Plane),
      dist z (c.parametrization q) < ρ → z ∈ D.chart.target ∧
        dist (D.chart.symm z).1 q < η ∧ |(D.chart.symm z).2| < D.width / 4 := by
  have hzsrc (q : ParameterCircle) : (q, (0 : ℝ)) ∈ D.chart.source := by
    rw [D.source_eq]
    exact ⟨mem_univ _, by linarith [D.width_pos], D.width_pos⟩
  have hz (q : ParameterCircle) : D.chart (q, 0) = c.parametrization q := by
    simp [D.formula]
  have hzinv (q : ParameterCircle) : D.chart.symm (c.parametrization q) = (q, 0) := by
    rw [← hz q]
    exact D.chart.left_inv (hzsrc q)
  let V : Set (ParameterCircle × Plane) := {p | p.2 ∈ D.chart.target ∧
    dist (D.chart.symm p.2).1 p.1 < η ∧ |(D.chart.symm p.2).2| < D.width / 4}
  have hV : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have ht : ∀ᶠ v : ParameterCircle × Plane in 𝓝 p, v.2 ∈ D.chart.target :=
      continuous_snd.continuousAt.preimage_mem_nhds (D.chart.open_target.mem_nhds hp.1)
    have hc := (D.chart.symm.continuousAt hp.1).comp continuous_snd.continuousAt
    have hd : ContinuousAt (fun v : ParameterCircle × Plane =>
        dist (D.chart.symm v.2).1 v.1) p := hc.fst.dist continuous_fst.continuousAt
    have hh : ContinuousAt (fun v : ParameterCircle × Plane =>
        |(D.chart.symm v.2).2|) p := hc.snd.abs
    exact ht.and ((hd.eventually (gt_mem_nhds hp.2.1)).and
      (hh.eventually (gt_mem_nhds hp.2.2)))
  have hS : IsCompact (range (fun q : ParameterCircle => (q, c.parametrization q))) :=
    isCompact_range (continuous_id.prodMk c.parametrization.continuous)
  have hsub : range (fun q : ParameterCircle => (q, c.parametrization q)) ⊆ V := by
    rintro _ ⟨q, rfl⟩
    refine ⟨?_, ?_⟩
    · change c.parametrization q ∈ D.chart.target
      rw [← hz q]
      exact D.chart.map_source (hzsrc q)
    · simp only [hzinv, dist_self, abs_zero]
      exact ⟨hη, by linarith [D.width_pos]⟩
  obtain ⟨ρ, hρ, hρV⟩ := hS.exists_thickening_subset_open hV hsub
  refine ⟨ρ, hρ, ?_⟩
  intro q z hdist
  change (q, z) ∈ V
  apply hρV
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(q, c.parametrization q), mem_range_self q, ?_⟩
  simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using hdist

lemma partition_time_mem (Q : Partition) (i : Fin (Q.count + 1)) :
    Q.time i ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rw [← Q.first]
    exact Q.strictMono.monotone (Fin.zero_le i)
  · rw [← Q.last]
    exact Q.strictMono.monotone (Fin.le_last i)


lemma edgeMap_dist_vertex_le (c : RegularJordanCurve) (Q : Partition)
    (i : Fin Q.count) (t : unitInterval) :
    dist (inscribedEdgeMap c Q i t) (inscribedVertex c Q i) ≤
      dist (realLift c.parametrization (Q.time i.succ)) (inscribedVertex c Q i) := by
  rw [dist_eq_norm, inscribedEdgeMap, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg t.property.1, dist_eq_norm]
  exact mul_le_of_le_one_left (norm_nonneg _) t.property.2


lemma short_edges (c : RegularJordanCurve) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.MeshLT δ → ∀ i : Fin Q.count,
      dist (realLift c.parametrization (Q.time i.succ)) (inscribedVertex c Q i) < ε := by
  have hc : Continuous (realLift c.parametrization) :=
    c.parametrization.continuous.comp continuous_quotient_mk'
  have hu : UniformContinuousOn (realLift c.parametrization) (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn
  obtain ⟨δ, hδ, hdist⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ, hδ, ?_⟩
  intro Q hmesh i
  exact hdist _ (partition_time_mem Q i.succ) _ (partition_time_mem Q i.castSucc) (by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr (Q.strictMono (by simp)))]
    exact hmesh i)


lemma circle_close_lifts {s t η : ℝ}
    (h : dist (s : ParameterCircle) (t : ParameterCircle) ≤ η) :
    ∃ k : ℤ, dist (t + k) s ≤ η := by
  have hh : t ∈ ((↑) : ℝ → ParameterCircle) ⁻¹'
      Metric.closedBall (s : ParameterCircle) η := by
    exact (dist_comm _ _).le.trans h
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion] at hh
  obtain ⟨k, hk⟩ := mem_iUnion.mp hh
  refine ⟨-k, ?_⟩
  simpa only [Metric.mem_closedBall, zsmul_eq_mul, mul_one, Int.cast_neg,
    Real.dist_eq, sub_add_eq_sub_sub, ← sub_eq_add_neg, sub_right_comm] using hk


lemma uniform_secant_radius {c : RegularJordanCurve}
    {o : Orientation ℝ Plane (Fin 2)} {W : C(ParameterCircle, Plane)}
    (hloc : LocallyPositiveSecants c o W) :
    ∃ η : ℝ, 0 < η ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ q ∈ Icc (t - η) (t + η), ∀ s ∈ Icc (t - η) (t + η),
      ∀ u ∈ Icc (t - η) (t + η), s < u →
        0 < inner ℝ (W (q : ParameterCircle)) (o.rightAngleRotation
          (realLift c.parametrization u - realLift c.parametrization s)) := by
  choose ε hε hm using hloc
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric
    (s := Icc (0 : ℝ) 1) (c := fun t : ℝ => Ioo (t - ε t) (t + ε t))
    isCompact_Icc (fun _ => isOpen_Ioo) (by
      intro t ht
      exact mem_iUnion.mpr ⟨t, by constructor <;> linarith [hε t]⟩)
  refine ⟨δ / 2, by positivity, ?_⟩
  intro t ht
  obtain ⟨v, hv⟩ := hcover t ht
  have hsub : Icc (t - δ / 2) (t + δ / 2) ⊆ Icc (v - ε v) (v + ε v) := by
    intro x hx
    have hxball : x ∈ Metric.ball t δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    exact ⟨(hv hxball).1.le, (hv hxball).2.le⟩
  intro q hq s hs u hu hsu
  exact hm v q (hsub hq) s (hsub hs) u (hsub hu) hsu

lemma eventual_controlled_edges {c : RegularJordanCurve}
    {o : Orientation ℝ Plane (Fin 2)} (D : TransverseCollar c o)
    (hloc : LocallyPositiveSecants c o D.field) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.MeshLT δ →
      ∀ (i : Fin Q.count) (t : unitInterval),
        inscribedEdgeMap c Q i t ∈ D.chart.target ∧
        |(D.chart.symm (inscribedEdgeMap c Q i t)).2| < D.width / 4 ∧
        0 < inner ℝ (D.field ((D.chart.symm (inscribedEdgeMap c Q i t)).1))
          (o.rightAngleRotation (inscribedEdge c Q i)) := by
  obtain ⟨η, hη, hsec⟩ := uniform_secant_radius hloc
  obtain ⟨ρ, hρ, hctrl⟩ := uniform_inverse_control D hη
  obtain ⟨δ, hδ, hshort⟩ := short_edges c ρ hρ
  refine ⟨min δ η, lt_min hδ hη, ?_⟩
  intro Q hmesh i t
  have hmδ : Q.MeshLT δ := fun j => (hmesh j).trans_le (min_le_left _ _)
  have hmη : Q.MeshLT η := fun j => (hmesh j).trans_le (min_le_right _ _)
  have hdist := (edgeMap_dist_vertex_le c Q i t).trans_lt (hshort Q hmδ i)
  obtain ⟨hz, hbase, hheight⟩ := hctrl (Q.time i.castSucc : ParameterCircle)
    (inscribedEdgeMap c Q i t) hdist
  refine ⟨hz, hheight, ?_⟩
  obtain ⟨q, hq⟩ := QuotientAddGroup.mk_surjective
    ((D.chart.symm (inscribedEdgeMap c Q i t)).1)
  obtain ⟨k, hk⟩ := circle_close_lifts (s := Q.time i.castSucc) (t := q)
    (by simpa only [hq, dist_comm] using hbase.le)
  have hk' : q + k ∈ Icc (Q.time i.castSucc - η) (Q.time i.castSucc + η) := by
    rw [Real.dist_eq, abs_le] at hk
    constructor <;> linarith [hk.1, hk.2]
  have hstart : Q.time i.castSucc ∈ Icc (Q.time i.castSucc - η) (Q.time i.castSucc + η) :=
    ⟨by linarith, by linarith⟩
  have horder : Q.time i.castSucc < Q.time i.succ := Q.strictMono (by simp)
  have hend : Q.time i.succ ∈ Icc (Q.time i.castSucc - η) (Q.time i.castSucc + η) :=
    ⟨by linarith, by linarith [hmη i]⟩
  have hpos := hsec (Q.time i.castSucc) (partition_time_mem Q i.castSucc)
    (q + k) hk' (Q.time i.castSucc) hstart (Q.time i.succ) hend horder
  have hkcoe : ((q + k : ℝ) : ParameterCircle) = (q : ParameterCircle) := by
    have hperiod : Function.Periodic (fun s : ℝ => (s : ParameterCircle)) 1 := by
      intro s
      simp
    simpa using hperiod.int_mul k q
  simpa only [hkcoe, hq, inscribedEdge, inscribedVertex] using hpos

/-- At the last edge, parameter 1 is the same circle point as parameter 0. -/
lemma next_vertex (c : RegularJordanCurve) (Q : Partition) (i : Fin Q.count) :
    inscribedVertex c Q (finRotate Q.count i) =
      realLift c.parametrization (Q.time i.succ) := by
  have general : ∀ (n : ℕ) (i : Fin n),
      (finRotate n i).castSucc = i.succ ∨
      ((finRotate n i).castSucc = 0 ∧ i.succ = Fin.last n) := by
    intro n i
    cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      by_cases hi : i = Fin.last n
      · right
        subst i
        simp
      · left
        apply Fin.ext
        exact coe_finRotate_of_ne_last hi
  have hrot := general Q.count i
  rcases hrot with h | ⟨hzero, hlast⟩
  · simp only [inscribedVertex, h]
  · simp only [inscribedVertex, hzero, hlast, Q.first, Q.last, realLift]
    congr 1
    exact (AddCircle.coe_period (1 : ℝ)).symm

lemma edgeVector_eq (c : RegularJordanCurve) (Q : Partition) (i : Fin Q.count) :
    P202Specs.PolygonTurning.edgeVector (Polygon.mk (inscribedVertex c Q)) i =
      inscribedEdge c Q i := by
  exact congrArg (fun v => v - inscribedVertex c Q i) (next_vertex c Q i)


lemma edgePath_eq (c : RegularJordanCurve) (Q : Partition) (i : Fin Q.count)
    (t : ℝ) :
    (Polygon.mk (inscribedVertex c Q)).edgePath ℝ i t =
      inscribedVertex c Q i + t • inscribedEdge c Q i := by
  change AffineMap.lineMap (inscribedVertex c Q i)
    (inscribedVertex c Q (finRotate Q.count i)) t = _
  rw [next_vertex]
  simp [AffineMap.lineMap_apply_module, inscribedEdge]
  module

/-- Full actual-edge containment, height control and strict transverse sign,
without a refinement, simplicity, orientation-side, or isotopy assumption. -/
theorem fineEdgeControl : Expected.fineEdgeControl := by
  intro c o
  obtain ⟨D, hlocal⟩ := collarWithLocalSecants c o
  obtain ⟨δ, hδ, hctrl⟩ := eventual_controlled_edges D hlocal
  refine ⟨D, δ, hδ, ?_⟩
  intro Q hmesh i t ht
  have h := hctrl Q hmesh i ⟨t, ht⟩
  simpa only [edgePath_eq, edgeVector_eq, inscribedEdgeMap] using h

/-- The inverse on the original curve is the zero section, in the actual chart. -/
lemma collar_inverse_zero {c : RegularJordanCurve}
    {o : Orientation ℝ Plane (Fin 2)} (D : TransverseCollar c o)
    (q : ParameterCircle) : D.chart.symm (c.parametrization q) = (q, 0) := by
  have hs : (q, (0 : ℝ)) ∈ D.chart.source := by
    rw [D.source_eq]
    exact ⟨mem_univ _, by linarith [D.width_pos], D.width_pos⟩
  have hz : D.chart (q, 0) = c.parametrization q := by simp [D.formula]
  rw [← hz]
  exact D.chart.left_inv hs

/-- Small metric neighborhoods of a circle parameter have a unique representative
in the open chart centered there; this also controls the cyclic cut. -/
lemma centered_circle_lift {s : ℝ} {q : ParameterCircle}
    (hq : dist q (s : ParameterCircle) < (1 : ℝ) / 4) :
    let v : ℝ := AddCircle.equivIco 1 (s - 1 / 2) q
    v ∈ Ioo (s - 1 / 2) (s + 1 / 2) ∧
      q ≠ ((s - 1 / 2 : ℝ) : ParameterCircle) := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨k, hk⟩ := circle_close_lifts (s := s) (t := t) (by simpa only [dist_comm] using hq.le)
  have hkcoe : ((t + k : ℝ) : ParameterCircle) = (t : ParameterCircle) := by simp
  have hmem : t + k ∈ Ioo (s - 1 / 2) (s + 1 / 2) := by
    rw [Real.dist_eq, abs_le] at hk
    constructor <;> linarith [hk.1, hk.2]
  have hico : t + k ∈ Ico (s - 1 / 2) (s - 1 / 2 + 1) :=
    ⟨hmem.1.le, by linarith [hmem.2]⟩
  have hv : (AddCircle.equivIco 1 (s - 1 / 2) (t : ParameterCircle) : ℝ) = t + k := by
    rw [← hkcoe]
    exact AddCircle.equivIco_coe_of_mem hico
  refine ⟨by simpa only [hv] using hmem, ?_⟩
  intro heq
  have hc := (AddCircle.coe_eq_coe_iff_of_mem_Ico hico
    (show s - 1 / 2 ∈ Ico (s - 1 / 2) (s - 1 / 2 + 1) from
      ⟨le_rfl, by linarith⟩)).mp (hkcoe.trans heq)
  linarith [hmem.1]

/-- The projection of a controlled short chord, lifted in the chart at its
first sample, is strictly increasing and covers exactly the original interval. -/
lemma edge_projection_interval {c : RegularJordanCurve}
    {o : Orientation ℝ Plane (Fin 2)} (D : TransverseCollar c o)
    (Q : Partition) (i : Fin Q.count)
    (hmesh : Q.MeshLT ((1 : ℝ) / 4))
    (hctrl : ∀ t : unitInterval,
      inscribedEdgeMap c Q i t ∈ D.chart.target ∧
      0 < inner ℝ (D.field ((D.chart.symm (inscribedEdgeMap c Q i t)).1))
        (o.rightAngleRotation (inscribedEdge c Q i)))
    (hclose : ∀ t : unitInterval,
      dist (D.chart.symm (inscribedEdgeMap c Q i t)).1
        (Q.time i.castSucc : ParameterCircle) < (1 : ℝ) / 4) :
    ∃ L : ℝ → ℝ, ContinuousOn L (Icc 0 1) ∧
      (∀ t : unitInterval, (L t : ParameterCircle) =
        (D.chart.symm (inscribedEdgeMap c Q i t)).1) ∧
      InjOn L (Icc 0 1) ∧ L 0 = Q.time i.castSucc ∧ L 1 = Q.time i.succ ∧
      L '' Icc 0 1 = Icc (Q.time i.castSucc) (Q.time i.succ) := by
  let z : ℝ → Plane := fun t => inscribedVertex c Q i + t • inscribedEdge c Q i
  let b : ℝ → ParameterCircle := fun t => (D.chart.symm (z t)).1
  let L : ℝ → ℝ := fun t => AddCircle.equivIco 1 (Q.time i.castSucc - 1 / 2) (b t)
  have hz : Continuous z := by fun_prop
  have hb : ContinuousOn b (Icc 0 1) := by
    intro t ht
    have hzt : z t ∈ D.chart.target := (hctrl ⟨t, ht⟩).1
    have hinv : ContinuousAt (fun x : ℝ => D.chart.symm (z x)) t :=
      (D.chart.symm.continuousAt hzt).comp hz.continuousAt
    exact hinv.fst.continuousWithinAt
  have hL : ContinuousOn L (Icc 0 1) := by
    intro t ht
    have hcut : b t ≠ ((Q.time i.castSucc - 1 / 2 : ℝ) : ParameterCircle) :=
      (centered_circle_lift (hclose ⟨t, ht⟩)).2
    have hc : ContinuousAt (fun q : ParameterCircle =>
        (AddCircle.equivIco 1 (Q.time i.castSucc - 1 / 2) q : ℝ)) (b t) :=
      continuous_subtype_val.continuousAt.comp
        (AddCircle.continuousAt_equivIco 1 (Q.time i.castSucc - 1 / 2) hcut)
    exact hc.comp_continuousWithinAt (hb t ht)
  have hcoe (t : unitInterval) : (L t : ParameterCircle) = b t :=
    AddCircle.coe_equivIco
  have hbinj : InjOn b (Icc 0 1) := by
    apply affine_fiber_projection_injective o c.parametrization D.field b
      (fun t => (D.chart.symm (z t)).2) (inscribedVertex c Q i) (inscribedEdge c Q i)
    · intro t ht
      exact ((D.chart.right_inv (hctrl ⟨t, ht⟩).1).symm.trans
        (D.formula (D.chart.symm (z t))))
    · intro t ht
      exact (hctrl ⟨t, ht⟩).2
  have hLinj : InjOn L (Icc 0 1) := by
    intro t ht u hu heq
    apply hbinj ht hu
    exact (hcoe ⟨t, ht⟩).symm.trans
      ((congrArg (fun x : ℝ => (x : ParameterCircle)) heq).trans (hcoe ⟨u, hu⟩))
  have hb0 : b 0 = (Q.time i.castSucc : ParameterCircle) := by
    simp only [b, z, zero_smul, add_zero, inscribedVertex, realLift, collar_inverse_zero]
  have hb1 : b 1 = (Q.time i.succ : ParameterCircle) := by
    have hz1 : z 1 = realLift c.parametrization (Q.time i.succ) := by
      simp [z, inscribedEdge]
    simp only [b, hz1, realLift, collar_inverse_zero]
  have horder : Q.time i.castSucc < Q.time i.succ := Q.strictMono (by simp)
  have hL0 : L 0 = Q.time i.castSucc := by
    change (AddCircle.equivIco 1 (Q.time i.castSucc - 1 / 2) (b 0) : ℝ) = _
    rw [hb0]
    exact AddCircle.equivIco_coe_of_mem ⟨by linarith, by linarith⟩
  have hL1 : L 1 = Q.time i.succ := by
    change (AddCircle.equivIco 1 (Q.time i.castSucc - 1 / 2) (b 1) : ℝ) = _
    rw [hb1]
    exact AddCircle.equivIco_coe_of_mem ⟨by linarith, by linarith [hmesh i]⟩
  have hmono := ContinuousOn.strictMonoOn_of_injOn_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (show L 0 ≤ L 1 by rw [hL0, hL1]; exact horder.le) hL hLinj
  refine ⟨L, hL, hcoe, hLinj, hL0, hL1, ?_⟩
  simpa only [hL0, hL1] using
    hL.image_Icc_of_monotoneOn (by norm_num : (0 : ℝ) ≤ 1) hmono.monotoneOn

/-- Consecutive intervals in any finite list cover the interval between its
first and last values. Here all such intervals are positively ordered. -/
lemma finite_interval_cover {n : ℕ} (hn : 0 < n) (f : Fin (n + 1) → ℝ)
    {v : ℝ} (hv : v ∈ Icc (f 0) (f (Fin.last n))) :
    ∃ i : Fin n, v ∈ Icc (f i.castSucc) (f i.succ) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact ⟨0, by simpa using hv⟩
    · by_cases hcut : v ≤ f (Fin.last n).castSucc
      · obtain ⟨i, hi⟩ := ih (by omega) (fun j => f j.castSucc) ⟨hv.1, hcut⟩
        exact ⟨i.castSucc, by simpa using hi⟩
      · exact ⟨Fin.last n, by simpa using
          (show f (Fin.last n).castSucc ≤ v ∧ v ≤ f (Fin.last (n + 1)) from
            ⟨(lt_of_not_ge hcut).le, hv.2⟩)⟩

/-- The only ambiguity of representatives in a full closed period is its
pair of endpoints. -/
lemma circle_closed_period_collision {v w : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1)
    (heq : (v : ParameterCircle) = (w : ParameterCircle)) :
    v = w ∨ (v = 0 ∧ w = 1) ∨ (v = 1 ∧ w = 0) := by
  by_cases hv1 : v = 1
  · by_cases hw0 : w = 0
    · exact Or.inr (Or.inr ⟨hv1, hw0⟩)
    · left
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc
        (show v ∈ Ioc (0 : ℝ) (0 + 1) by subst v; norm_num)
        (show w ∈ Ioc (0 : ℝ) (0 + 1) from
          ⟨lt_of_le_of_ne hw.1 (Ne.symm hw0), by simpa using hw.2⟩)).mp heq
  · by_cases hw1 : w = 1
    · by_cases hv0 : v = 0
      · exact Or.inr (Or.inl ⟨hv0, hw1⟩)
      · left
        exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc
          (show v ∈ Ioc (0 : ℝ) (0 + 1) from
            ⟨lt_of_le_of_ne hv.1 (Ne.symm hv0), by simpa using hv.2⟩)
          (show w ∈ Ioc (0 : ℝ) (0 + 1) by subst w; norm_num)).mp heq
    · left
      exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (show v ∈ Ico (0 : ℝ) (0 + 1) from ⟨hv.1, by simpa using lt_of_le_of_ne hv.2 hv1⟩)
        (show w ∈ Ico (0 : ℝ) (0 + 1) from ⟨hw.1, by simpa using lt_of_le_of_ne hw.2 hw1⟩)).mp heq

lemma boundary_eq_inscribedTrace (c : RegularJordanCurve) (Q : Partition) :
    (Polygon.mk (inscribedVertex c Q)).boundary ℝ = inscribedTrace c Q := by
  ext z
  simp only [Polygon.boundary, Polygon.edgeSet_eq_image_edgePath, inscribedTrace,
    mem_iUnion, mem_image, mem_range]
  constructor
  · rintro ⟨i, t, ht, rfl⟩
    exact ⟨i, ⟨t, ht⟩, by rw [edgePath_eq]; rfl⟩
  · rintro ⟨i, t, rfl⟩
    exact ⟨i, t, t.property, by rw [edgePath_eq]; rfl⟩

lemma inscribedTrace_compact (c : RegularJordanCurve) (Q : Partition) :
    IsCompact (inscribedTrace c Q) := by
  apply isCompact_iUnion
  intro i
  exact isCompact_range (show Continuous (inscribedEdgeMap c Q i) by
    unfold inscribedEdgeMap; fun_prop)

/-- Once each edge projects exactly onto its sample interval, the actual base
projection of the literal compact trace is bijective. -/
lemma trace_projection_bijective {c : RegularJordanCurve}
    {o : Orientation ℝ Plane (Fin 2)} (D : TransverseCollar c o) (Q : Partition)
    (hproj : ∀ i : Fin Q.count, ∃ L : ℝ → ℝ,
      ContinuousOn L (Icc 0 1) ∧
      (∀ t : unitInterval, (L t : ParameterCircle) =
        (D.chart.symm (inscribedEdgeMap c Q i t)).1) ∧
      InjOn L (Icc 0 1) ∧ L 0 = Q.time i.castSucc ∧ L 1 = Q.time i.succ ∧
      L '' Icc 0 1 = Icc (Q.time i.castSucc) (Q.time i.succ)) :
    Function.Bijective (fun z : inscribedTrace c Q => (D.chart.symm z.val).1) := by
  classical
  choose L hcont hcoe hinj hzero hone himage using hproj
  have hmem (i : Fin Q.count) (t : unitInterval) :
      L i t ∈ Icc (Q.time i.castSucc) (Q.time i.succ) := by
    rw [← himage i]
    exact mem_image_of_mem _ t.property
  have hunit (i : Fin Q.count) (t : unitInterval) : L i t ∈ Icc (0 : ℝ) 1 :=
    ⟨(partition_time_mem Q i.castSucc).1.trans (hmem i t).1,
      (hmem i t).2.trans (partition_time_mem Q i.succ).2⟩
  have hend (i : Fin Q.count) (t : unitInterval)
      (h : L i t = Q.time i.castSucc ∨ L i t = Q.time i.succ) :
      inscribedEdgeMap c Q i t = c.parametrization (L i t : ParameterCircle) := by
    rcases h with h | h
    · have ht : (t : ℝ) = 0 := hinj i t.property (by norm_num) (h.trans (hzero i).symm)
      simp [inscribedEdgeMap, ht, hzero i, inscribedVertex, realLift]
    · have ht : (t : ℝ) = 1 := hinj i t.property (by norm_num) (h.trans (hone i).symm)
      simp [inscribedEdgeMap, ht, hone i, inscribedEdge, realLift]
  have hpair (i j : Fin Q.count) (t u : unitInterval)
      (heq : (L i t : ParameterCircle) = (L j u : ParameterCircle)) :
      inscribedEdgeMap c Q i t = inscribedEdgeMap c Q j u := by
    rcases circle_closed_period_collision (hunit i t) (hunit j u) heq with hvw | h01 | h10
    · rcases lt_trichotomy i j with hij | hij | hij
      · have horder : Q.time i.succ ≤ Q.time j.castSucc :=
          Q.strictMono.monotone (by simpa only [Fin.le_iff_val_le_val, Fin.val_succ,
            Fin.val_castSucc] using (show i.val + 1 ≤ j.val by omega))
        have hi : L i t = Q.time i.succ := by linarith [(hmem i t).2, (hmem j u).1]
        have hj : L j u = Q.time j.castSucc := by linarith [(hmem i t).2, (hmem j u).1]
        exact (hend i t (Or.inr hi)).trans ((congrArg c.parametrization heq).trans
          (hend j u (Or.inl hj)).symm)
      · subst j
        have htu : (t : ℝ) = u := hinj i t.property u.property hvw
        exact congrArg (inscribedEdgeMap c Q i) (Subtype.ext htu)
      · have horder : Q.time j.succ ≤ Q.time i.castSucc :=
          Q.strictMono.monotone (by simpa only [Fin.le_iff_val_le_val, Fin.val_succ,
            Fin.val_castSucc] using (show j.val + 1 ≤ i.val by omega))
        have hi : L i t = Q.time i.castSucc := by linarith [(hmem i t).1, (hmem j u).2]
        have hj : L j u = Q.time j.succ := by linarith [(hmem i t).1, (hmem j u).2]
        exact (hend i t (Or.inl hi)).trans ((congrArg c.parametrization heq).trans
          (hend j u (Or.inr hj)).symm)
    · have hi : L i t = Q.time i.castSucc := by
        linarith [(hmem i t).1, (partition_time_mem Q i.castSucc).1, h01.1]
      have hj : L j u = Q.time j.succ := by
        linarith [(hmem j u).2, (partition_time_mem Q j.succ).2, h01.2]
      exact (hend i t (Or.inl hi)).trans ((congrArg c.parametrization heq).trans
        (hend j u (Or.inr hj)).symm)
    · have hi : L i t = Q.time i.succ := by
        linarith [(hmem i t).2, (partition_time_mem Q i.succ).2, h10.1]
      have hj : L j u = Q.time j.castSucc := by
        linarith [(hmem j u).1, (partition_time_mem Q j.castSucc).1, h10.2]
      exact (hend i t (Or.inr hi)).trans ((congrArg c.parametrization heq).trans
        (hend j u (Or.inl hj)).symm)
  constructor
  · rintro ⟨z, hz⟩ ⟨w, hw⟩ heq
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    obtain ⟨t, rfl⟩ := hi
    obtain ⟨j, hj⟩ := mem_iUnion.mp hw
    obtain ⟨u, rfl⟩ := hj
    apply Subtype.ext
    exact hpair i j t u ((hcoe i t).trans (heq.trans (hcoe j u).symm))
  · intro q
    let v : ℝ := AddCircle.equivIco 1 0 q
    have hv : v ∈ Icc (0 : ℝ) 1 := by
      exact ⟨(AddCircle.equivIco 1 0 q).property.1,
        le_of_lt (by simpa using (AddCircle.equivIco 1 0 q).property.2)⟩
    obtain ⟨i, hi⟩ := finite_interval_cover (by have := Q.at_least_three; omega)
      Q.time (v := v) (by simpa only [Q.first, Q.last] using hv)
    rw [← himage i] at hi
    obtain ⟨t, ht, htv⟩ := hi
    refine ⟨⟨inscribedEdgeMap c Q i ⟨t, ht⟩, mem_iUnion.mpr ⟨i, mem_range_self _⟩⟩, ?_⟩
    change (D.chart.symm (inscribedEdgeMap c Q i ⟨t, ht⟩)).1 = q
    rw [← hcoe i ⟨t, ht⟩, htv]
    exact AddCircle.coe_equivIco

/-- A compact trace with bijective actual collar projection has a continuous
height graph, with exactly the prescribed range and height bound. -/
lemma graph_of_trace_projection {c : RegularJordanCurve}
    {o : Orientation ℝ Plane (Fin 2)} (D : TransverseCollar c o) (Q : Partition)
    (hctrl : ∀ z ∈ inscribedTrace c Q, z ∈ D.chart.target ∧
      |(D.chart.symm z).2| < D.width / 4)
    (hbij : Function.Bijective
      (fun z : inscribedTrace c Q => (D.chart.symm z.val).1)) :
    ∃ f : C(ParameterCircle, ℝ), (∀ q, |f q| < D.width / 4) ∧
      (Polygon.mk (inscribedVertex c Q)).boundary ℝ = range (fun q => D.chart (q, f q)) := by
  let K := inscribedTrace c Q
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (inscribedTrace_compact c Q)
  let B : K → ParameterCircle := fun z => (D.chart.symm z.val).1
  have hC : Continuous (fun z : K => D.chart.symm z.val) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (D.chart.symm.continuousAt (hctrl z.val z.property).1).comp
      continuous_subtype_val.continuousAt
  have hB : Continuous B := hC.fst
  let H : K ≃ₜ ParameterCircle :=
    (Equiv.ofBijective B hbij).toHomeomorphOfContinuousClosed hB hB.isClosedMap
  let f : C(ParameterCircle, ℝ) := ⟨fun q => (D.chart.symm (H.symm q).val).2,
    hC.snd.comp H.symm.continuous⟩
  refine ⟨f, fun q => (hctrl _ (H.symm q).property).2, ?_⟩
  rw [boundary_eq_inscribedTrace]
  ext z
  constructor
  · intro hz
    let x : K := ⟨z, hz⟩
    refine ⟨B x, ?_⟩
    have hx : H.symm (B x) = x := H.symm_apply_apply x
    change D.chart (B x, (D.chart.symm (H.symm (B x)).val).2) = z
    rw [hx]
    exact D.chart.right_inv (hctrl z hz).1
  · rintro ⟨q, rfl⟩
    have hbase : (D.chart.symm (H.symm q).val).1 = q := H.apply_symm_apply q
    have hz : D.chart (q, f q) = (H.symm q).val := by
      change D.chart (q, (D.chart.symm (H.symm q).val).2) = _
      have hp : (q, (D.chart.symm (H.symm q).val).2) = D.chart.symm (H.symm q).val :=
        Prod.ext hbase.symm rfl
      rw [hp]
      exact D.chart.right_inv (hctrl _ (H.symm q).property).1
    change D.chart (q, f q) ∈ inscribedTrace c Q
    rw [hz]
    exact (H.symm q).property

/-- Every sufficiently fine literal inscribed polygon is a graph in this
collar. Fineness, rather than preservation of any particular knots, suffices. -/
lemma eventual_polygon_graphs {c : RegularJordanCurve}
    {o : Orientation ℝ Plane (Fin 2)} (D : TransverseCollar c o)
    (hloc : LocallyPositiveSecants c o D.field) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Partition, Q.MeshLT δ → IsPolygonGraph D Q := by
  obtain ⟨δE, hδE, hE⟩ := eventual_controlled_edges D hloc
  obtain ⟨ρ, hρ, hnear⟩ := uniform_inverse_control D (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨δC, hδC, hC⟩ := short_edges c ρ hρ
  refine ⟨min δE (min δC (1 / 4)), lt_min hδE (lt_min hδC (by norm_num)), ?_⟩
  intro Q hmesh
  have hmE : Q.MeshLT δE := fun i => (hmesh i).trans_le (min_le_left _ _)
  have hmC : Q.MeshLT δC := fun i => (hmesh i).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hm4 : Q.MeshLT ((1 : ℝ) / 4) := fun i => (hmesh i).trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  have hproj (i : Fin Q.count) : ∃ L : ℝ → ℝ,
      ContinuousOn L (Icc 0 1) ∧
      (∀ t : unitInterval, (L t : ParameterCircle) =
        (D.chart.symm (inscribedEdgeMap c Q i t)).1) ∧
      InjOn L (Icc 0 1) ∧ L 0 = Q.time i.castSucc ∧ L 1 = Q.time i.succ ∧
      L '' Icc 0 1 = Icc (Q.time i.castSucc) (Q.time i.succ) := by
    apply edge_projection_interval D Q i hm4
    · intro t
      exact ⟨(hE Q hmE i t).1, (hE Q hmE i t).2.2⟩
    · intro t
      exact (hnear (Q.time i.castSucc : ParameterCircle) (inscribedEdgeMap c Q i t)
        ((edgeMap_dist_vertex_le c Q i t).trans_lt (hC Q hmC i))).2.1
  have htrace : ∀ z ∈ inscribedTrace c Q, z ∈ D.chart.target ∧
      |(D.chart.symm z).2| < D.width / 4 := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    obtain ⟨t, rfl⟩ := hi
    exact ⟨(hE Q hmE i t).1, (hE Q hmE i t).2.1⟩
  refine ⟨graph_of_trace_projection D Q htrace (trace_projection_bijective D Q hproj), ?_⟩
  intro i t ht
  simpa only [edgePath_eq, edgeVector_eq, inscribedEdgeMap] using
    (hE Q hmE i ⟨t, ht.1.le, ht.2.le⟩).2.2

/-- Full transverse-collar graph statement for all refining fine partitions,
with the literal vertices and the inverse of the very collar constructed. -/
theorem fineGraphs : Expected.fineGraphs := by
  intro c o A
  obtain ⟨D, hlocal⟩ := collarWithLocalSecants c o
  obtain ⟨δ, hδ, hgraphs⟩ := eventual_polygon_graphs D hlocal
  exact ⟨D, δ, hδ, fun Q _ hmesh => hgraphs Q hmesh⟩

end P202.FineInscribedCollarGraphs
