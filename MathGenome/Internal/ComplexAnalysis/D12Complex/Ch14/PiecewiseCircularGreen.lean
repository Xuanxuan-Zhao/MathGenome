import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.PiecewiseCircularGreen
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CircularCornerRounding
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.ComplexGreenBridge
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CircularSurgeryPartition
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.ParametrizedBoundaryDisplay
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Positivity

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology Interval
open scoped RealInnerProductSpace ContDiff
namespace D12Complex.PiecewiseCircularGreen
open D12Complex.CircularExhaustion D12Complex.CircularCornerRounding


lemma continuousOn_gradient {O : Set ℂ} (hO : IsOpen O) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ 2 u O) : ContinuousOn (gradient u) O := by
  exact (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp_continuousOn
    (hu.continuousOn_fderiv_of_isOpen hO (by norm_num))

lemma continuous_arcParam (c : ℂ) (r : ℝ) : Continuous (arcParam c r) := by
  unfold arcParam
  fun_prop

lemma flux_intervalIntegrable {U O : Set ℂ} (hO : IsOpen O) (hUO : closure U ⊆ O)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O)
    (c : ℂ) (r a b s : ℝ) (hab : a ≤ b)
    (hbound : arcParam c r '' Icc a b ⊆ frontier U) :
    IntervalIntegrable (fun t =>
      (u (arcParam c r t) * inner ℝ (gradient v (arcParam c r t))
        (s • Complex.exp ((t : ℂ) * Complex.I)) -
       v (arcParam c r t) * inner ℝ (gradient u (arcParam c r t))
        (s • Complex.exp ((t : ℂ) * Complex.I))) * r)
      MeasureTheory.volume a b := by
  have hc : ContinuousOn (arcParam c r) (Icc a b) :=
    (continuous_arcParam c r).continuousOn
  have hm : MapsTo (arcParam c r) (Icc a b) O := by
    intro t ht
    exact hUO (frontier_subset_closure (hbound (mem_image_of_mem _ ht)))
  have hcu := hu.continuousOn.comp hc hm
  have hcv := hv.continuousOn.comp hc hm
  have hgu := (continuousOn_gradient hO hu).comp hc hm
  have hgv := (continuousOn_gradient hO hv).comp hc hm
  have hn : ContinuousOn (fun t : ℝ => s • Complex.exp ((t : ℂ) * Complex.I)) (Icc a b) := by
    fun_prop
  exact ((hcu.mul (hgv.inner hn)).sub (hcv.mul (hgu.inner hn))).mul_const r |>.intervalIntegrable_of_Icc hab

lemma array_flux_intervalIntegrable {U O : Set ℂ} (hO : IsOpen O) (hUO : closure U ⊆ O)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O)
    (n : ℕ) (center : Fin n → ℂ) (radius start stop sign : Fin n → ℝ)
    (hab : ∀ i, start i ≤ stop i)
    (hcover : frontier U = ⋃ i, arcParam (center i) (radius i) '' Icc (start i) (stop i)) :
    ∀ i, IntervalIntegrable (fun t =>
      (u (arcParam (center i) (radius i) t) *
         inner ℝ (gradient v (arcParam (center i) (radius i) t))
           (sign i • Complex.exp ((t : ℂ) * Complex.I)) -
       v (arcParam (center i) (radius i) t) *
         inner ℝ (gradient u (arcParam (center i) (radius i) t))
           (sign i • Complex.exp ((t : ℂ) * Complex.I))) * radius i)
      MeasureTheory.volume (start i) (stop i) := by
  intro i
  apply flux_intervalIntegrable hO hUO u v hu hv (center i) (radius i)
    (start i) (stop i) (sign i) (hab i)
  rw [hcover]
  exact subset_iUnion_of_subset i (Subset.refl _)

lemma abs_scalar_flux_le (u v : ℂ → ℝ) (z ν : ℂ) :
    |u z * inner ℝ (gradient v z) ν - v z * inner ℝ (gradient u z) ν| ≤
      (|u z| * ‖gradient v z‖ + |v z| * ‖gradient u z‖) * ‖ν‖ := by
  calc
    _ ≤ |u z * inner ℝ (gradient v z) ν| + |v z * inner ℝ (gradient u z) ν| :=
      abs_sub _ _
    _ = |u z| * |inner ℝ (gradient v z) ν| + |v z| * |inner ℝ (gradient u z) ν| := by
      rw [abs_mul, abs_mul]
    _ ≤ |u z| * (‖gradient v z‖ * ‖ν‖) + |v z| * (‖gradient u z‖ * ‖ν‖) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _))
    _ = _ := by ring

lemma compact_scalar_flux_bound {K O : Set ℂ} (hK : IsCompact K)
    (hO : IsOpen O) (hKO : K ⊆ O) (u v : ℂ → ℝ)
    (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O) :
    ∃ M > 0, ∀ z ∈ K, ∀ ν : ℂ, ‖ν‖ ≤ 1 →
      |u z * inner ℝ (gradient v z) ν - v z * inner ℝ (gradient u z) ν| ≤ M := by
  let F : ℂ → ℝ := fun z => |u z| * ‖gradient v z‖ + |v z| * ‖gradient u z‖
  have hF : ContinuousOn F K := by
    exact ((hu.continuousOn.mono hKO).abs.mul ((continuousOn_gradient hO hv).mono hKO).norm).add
      ((hv.continuousOn.mono hKO).abs.mul ((continuousOn_gradient hO hu).mono hKO).norm)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz ν hν
  calc
    _ ≤ F z * ‖ν‖ := abs_scalar_flux_le u v z ν
    _ ≤ F z := mul_le_of_le_one_right (by dsimp [F]; positivity) hν
    _ ≤ ‖F z‖ := le_abs_self _
    _ ≤ C := hC z hz
    _ ≤ max C 1 := le_max_left _ _

lemma circle_flux_pointwise_bound {K : Set ℂ} (u v : ℂ → ℝ) {M : ℝ}
    (hM : ∀ z ∈ K, ∀ ν : ℂ, ‖ν‖ ≤ 1 →
      |u z * inner ℝ (gradient v z) ν - v z * inner ℝ (gradient u z) ν| ≤ M)
    (c : ℂ) (r s t : ℝ) (hr : 0 ≤ r) (hs : |s| ≤ 1)
    (ht : arcParam c r t ∈ K) :
    |(u (arcParam c r t) * inner ℝ (gradient v (arcParam c r t))
        (s • Complex.exp ((t : ℂ) * Complex.I)) -
       v (arcParam c r t) * inner ℝ (gradient u (arcParam c r t))
        (s • Complex.exp ((t : ℂ) * Complex.I))) * r| ≤ M * r := by
  have hn : ‖s • Complex.exp ((t : ℂ) * Complex.I)‖ ≤ 1 := by
    simpa only [norm_smul, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs] using hs
  rw [abs_mul, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_right (hM _ ht _ hn) hr

lemma circle_flux_integral_bound {K : Set ℂ} (u v : ℂ → ℝ) {M : ℝ}
    (hM : ∀ z ∈ K, ∀ ν : ℂ, ‖ν‖ ≤ 1 →
      |u z * inner ℝ (gradient v z) ν - v z * inner ℝ (gradient u z) ν| ≤ M)
    (c : ℂ) (r a b s : ℝ) (hr : 0 ≤ r) (hab : a ≤ b) (hs : |s| ≤ 1)
    (htrace : arcParam c r '' Icc a b ⊆ K) :
    |∫ t in a..b,
      (u (arcParam c r t) * inner ℝ (gradient v (arcParam c r t))
        (s • Complex.exp ((t : ℂ) * Complex.I)) -
       v (arcParam c r t) * inner ℝ (gradient u (arcParam c r t))
        (s • Complex.exp ((t : ℂ) * Complex.I))) * r| ≤ M * r * (b - a) := by
  have H := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := M * r)
    (f := fun t =>
      (u (arcParam c r t) * inner ℝ (gradient v (arcParam c r t))
        (s • Complex.exp ((t : ℂ) * Complex.I)) -
       v (arcParam c r t) * inner ℝ (gradient u (arcParam c r t))
        (s • Complex.exp ((t : ℂ) * Complex.I))) * r) ?_
  · simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using H
  · intro t ht
    have ht' : t ∈ Icc a b := Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using ht)
    exact circle_flux_pointwise_bound u v hM c r s t hr hs
      (htrace (mem_image_of_mem _ ht'))

theorem circular_flux_integrable :
    Specs.D12Complex.Ch14.PiecewiseCircularGreen.circular_flux_integrable_type := by
  intro U O hO hUO u v hu hv n center radius start stop sign hab hcover
  exact array_flux_intervalIntegrable hO hUO u v hu hv n center radius start stop sign hab hcover

lemma parametrized_flux_integral_bound {K : Set ℂ} (u v : ℂ → ℝ) {M : ℝ}
    (hM : ∀ z ∈ K, ∀ ν : ℂ, ‖ν‖ ≤ 1 →
      |u z * inner ℝ (gradient v z) ν - v z * inner ℝ (gradient u z) ν| ≤ M)
    (γ N : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (htrace : MapsTo γ (Icc a b) K)
    (hN : ∀ t ∈ Icc a b, ‖N t‖ ≤ 1)
    (hspeed : IntervalIntegrable (fun t => ‖deriv γ t‖) MeasureTheory.volume a b) :
    |∫ t in a..b,
      (u (γ t) * inner ℝ (gradient v (γ t)) (N t) -
       v (γ t) * inner ℝ (gradient u (γ t)) (N t)) * ‖deriv γ t‖| ≤
      M * ∫ t in a..b, ‖deriv γ t‖ := by
  rw [← intervalIntegral.integral_const_mul, ← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le hab ?_ (hspeed.const_mul M)
  filter_upwards [] with t ht
  have ht' : t ∈ Icc a b := Ioc_subset_Icc_self ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right (hM _ (htrace ht') _ (hN t ht')) (norm_nonneg _)


theorem compact_flux_bound :
    Specs.D12Complex.Ch14.PiecewiseCircularGreen.compact_scalar_flux_bound_type := by
  intro K O hK hO hKO u v hu hv
  exact compact_scalar_flux_bound hK hO hKO u v hu hv

theorem rounded_harmonic_green :
    Specs.D12Complex.Ch14.PiecewiseCircularGreen.rounded_harmonic_green_type := by
  intro U J hgeom O hO hUO u v hu hv hLu hLv
  obtain ⟨C, ε₀, hC, hε₀, hr⟩ := CircularCornerRounding.circular_corner_rounding U J hgeom
  refine ⟨C, ε₀, hC, hε₀, ?_⟩
  intro ε hε hεsmall
  obtain ⟨V, hV⟩ := hr ε hε hεsmall
  refine ⟨V, hV, ?_⟩
  exact ComplexGreenBridge.harmonic_second_green V O hV.2.2.1 hO
    ((closure_mono hV.2.1).trans hUO) u v hu hv
    (fun z hz => hLu z (hV.2.1 hz)) (fun z hz => hLv z (hV.2.1 hz))

/-- Scalar flux/arclength substitution, allowing zero derivative and arbitrary
interval-integrable density. The density may include an arbitrary continuous
normal field on the trace; it is simply a scalar function w here. -/
lemma scalar_arclength_substitution_monotone
    {a b : ℝ} {φ : ℝ → ℝ} {γ : ℝ → ℂ} {w : ℝ → ℝ}
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b))
    (hφd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ φ t)
    (hm : MonotoneOn φ (Icc a b))
    (hγd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ (φ t))
    (hint : IntervalIntegrable (fun s => w s * ‖deriv γ s‖) volume (φ a) (φ b)) :
    IntervalIntegrable (fun t => w (φ t) * ‖deriv (γ ∘ φ) t‖) volume a b ∧
      (∫ t in a..b, w (φ t) * ‖deriv (γ ∘ φ) t‖) =
        ∫ s in φ a..φ b, w s * ‖deriv γ s‖ := by
  have hc : ContinuousOn φ [[a, b]] := by simpa only [uIcc_of_le hab] using hφ
  have hd : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt φ (deriv φ t) t := by
    intro t ht
    exact (hφd t (by simpa only [min_eq_left hab, max_eq_right hab] using ht)).hasDerivAt
  have hn : ∀ t ∈ Ioo (min a b) (max a b), 0 ≤ deriv φ t := by
    intro t ht
    have ht' : t ∈ Ioo a b := by simpa only [min_eq_left hab, max_eq_right hab] using ht
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht'.1 ht'.2)]
    exact hm.derivWithin_nonneg
  have he : EqOn
      (fun t => (w (φ t) * ‖deriv γ (φ t)‖) * deriv φ t)
      (fun t => w (φ t) * ‖deriv (γ ∘ φ) t‖) (Ioo a b) := by
    intro t ht
    dsimp only
    rw [deriv.scomp t (hγd t ht) (hφd t ht), norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hn t (by simpa only [min_eq_left hab, max_eq_right hab] using ht))]
    ring
  have hi := (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg hc hd hn).2 hint
  refine ⟨hi.congr_uIoo (by simpa only [uIoo_of_le hab, Function.comp_apply, Pi.neg_apply] using he), ?_⟩
  calc
    _ = ∫ t in a..b, (w (φ t) * ‖deriv γ (φ t)‖) * deriv φ t :=
      intervalIntegral.integral_congr_Ioo_of_le hab (fun t ht => (he ht).symm)
    _ = _ := by
      simpa only [Function.comp_apply] using
        intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
          (g := fun s => w s * ‖deriv γ s‖) hc hd hn

lemma scalar_arclength_substitution_antitone
    {a b : ℝ} {φ : ℝ → ℝ} {γ : ℝ → ℂ} {w : ℝ → ℝ}
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b))
    (hφd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ φ t)
    (hm : AntitoneOn φ (Icc a b))
    (hγd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ (φ t))
    (hint : IntervalIntegrable (fun s => w s * ‖deriv γ s‖) volume (φ b) (φ a)) :
    IntervalIntegrable (fun t => w (φ t) * ‖deriv (γ ∘ φ) t‖) volume a b ∧
      (∫ t in a..b, w (φ t) * ‖deriv (γ ∘ φ) t‖) =
        ∫ s in φ b..φ a, w s * ‖deriv γ s‖ := by
  have hc : ContinuousOn φ [[a, b]] := by simpa only [uIcc_of_le hab] using hφ
  have hd : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt φ (deriv φ t) t := by
    intro t ht
    exact (hφd t (by simpa only [min_eq_left hab, max_eq_right hab] using ht)).hasDerivAt
  have hn : ∀ t ∈ Ioo (min a b) (max a b), deriv φ t ≤ 0 := by
    intro t ht
    have ht' : t ∈ Ioo a b := by simpa only [min_eq_left hab, max_eq_right hab] using ht
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht'.1 ht'.2)]
    exact hm.derivWithin_nonpos
  have he : EqOn
      (fun t => -((w (φ t) * ‖deriv γ (φ t)‖) * deriv φ t))
      (fun t => w (φ t) * ‖deriv (γ ∘ φ) t‖) (Ioo a b) := by
    intro t ht
    dsimp only
    rw [deriv.scomp t (hγd t ht) (hφd t ht), norm_smul, Real.norm_eq_abs,
      abs_of_nonpos (hn t (by simpa only [min_eq_left hab, max_eq_right hab] using ht))]
    ring
  have hi := (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos hc hd hn).2 hint.symm
  refine ⟨hi.neg.congr_uIoo ?_, ?_⟩
  · intro t ht
    apply he
    simpa only [uIoo_of_le hab] using ht
  ·
    calc
      _ = ∫ t in a..b, -((w (φ t) * ‖deriv γ (φ t)‖) * deriv φ t) :=
        intervalIntegral.integral_congr_Ioo_of_le hab (fun t ht => (he ht).symm)
      _ = -(∫ s in φ a..φ b, w s * ‖deriv γ s‖) := by
        rw [intervalIntegral.integral_neg]
        congr 1
        simpa only [Function.comp_apply] using
          intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
            (g := fun s => w s * ‖deriv γ s‖) hc hd hn
      _ = _ := by rw [intervalIntegral.integral_symm]; simp only [neg_neg]

/-- Equality of curve values on the closed interval suffices to compare their
actual scalar arclength integrals; derivatives are compared only in the interior. -/
lemma scalar_arclength_density_congr
    {a b : ℝ} {γ η : ℝ → ℂ} {w : ℝ → ℝ}
    (hab : a ≤ b) (heq : EqOn η γ (Icc a b)) :
    (IntervalIntegrable (fun t => w t * ‖deriv γ t‖) volume a b ↔
      IntervalIntegrable (fun t => w t * ‖deriv η t‖) volume a b) ∧
      (∫ t in a..b, w t * ‖deriv η t‖) = ∫ t in a..b, w t * ‖deriv γ t‖ := by
  have hd : EqOn (fun t => w t * ‖deriv η t‖)
      (fun t => w t * ‖deriv γ t‖) (Ioo a b) := by
    intro t ht
    have hh : η =ᶠ[𝓝 t] γ := by
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
      exact heq hs
    dsimp only
    rw [hh.deriv_eq]
  refine ⟨?_, intervalIntegral.integral_congr_Ioo_of_le hab hd⟩
  exact intervalIntegrable_congr_uIoo
    (by simpa only [uIoo_of_le hab] using hd.symm)


lemma pullback_speed_bound (g : ℂ → ℂ) (γ : ℝ → ℂ) {R : ℝ} {L : NNReal}
    (hg : ContDiffOn ℝ 1 g (ball 0 R)) (hγ : ContDiff ℝ 1 γ)
    (hLip : LipschitzOnWith L g (closedBall 0 R))
    (htrace : MapsTo γ (Icc (0 : ℝ) 1) (ball 0 R)) :
    IntervalIntegrable (fun t => ‖deriv (g ∘ γ) t‖) MeasureTheory.volume 0 1 ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (g ∘ γ) t‖ ≤ (L : ℝ) * ‖deriv γ t‖ := by
  let V := γ ⁻¹' ball 0 R
  have hV : IsOpen V := isOpen_ball.preimage hγ.continuous
  have hc : ContDiffOn ℝ 1 (g ∘ γ) V := hg.comp hγ.contDiffOn (fun _ hx => hx)
  have hIV : Icc (0 : ℝ) 1 ⊆ V := htrace
  refine ⟨((hc.continuousOn_deriv_of_isOpen hV (by norm_num)).mono hIV).norm.intervalIntegrable_of_Icc (by norm_num), ?_⟩
  intro t ht
  have hx := htrace ht
  have hgd : DifferentiableAt ℝ g (γ t) :=
    ((hg _ hx).contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt (by norm_num)
  rw [fderiv_comp_deriv t hgd (hγ.differentiable (by norm_num) t)]
  calc
    _ ≤ ‖fderiv ℝ g (γ t)‖ * ‖deriv γ t‖ := (fderiv ℝ g (γ t)).le_opNorm _
    _ ≤ (L : ℝ) * ‖deriv γ t‖ := mul_le_mul_of_nonneg_right
      (norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hx)
        (hLip.mono ball_subset_closedBall)) (norm_nonneg _)

lemma pullback_length_le (g : ℂ → ℂ) (γ : ℝ → ℂ) {R B : ℝ} {L : NNReal}
    (hg : ContDiffOn ℝ 1 g (ball 0 R)) (hγ : ContDiff ℝ 1 γ)
    (hLip : LipschitzOnWith L g (closedBall 0 R))
    (htrace : MapsTo γ (Icc (0 : ℝ) 1) (ball 0 R))
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ t‖ ≤ B) :
    IntervalIntegrable (fun t => ‖deriv (g ∘ γ) t‖) MeasureTheory.volume 0 1 ∧
    (∫ t in (0 : ℝ)..1, ‖deriv (g ∘ γ) t‖) ≤ (L : ℝ) * B := by
  obtain ⟨hi, hbound⟩ := pullback_speed_bound g γ hg hγ hLip htrace
  refine ⟨hi, ?_⟩
  have H := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hi
    (intervalIntegrable_const (c := (L : ℝ) * B)) (fun t ht =>
      (hbound t ht).trans (mul_le_mul_of_nonneg_left (hspeed t ht) L.coe_nonneg))
  simpa using H

lemma pullback_roundingArc_length (g : ℂ → ℂ) {R ε θ : ℝ} {L : NNReal}
    (hg : ContDiffOn ℝ 1 g (ball 0 R))
    (hLip : LipschitzOnWith L g (closedBall 0 R))
    (hε : 0 < ε) (hεR : ε < R) (hθ : 0 < θ) :
    IntervalIntegrable (fun t => ‖deriv (g ∘ roundingArc ε θ) t‖) MeasureTheory.volume 0 1 ∧
    (∫ t in (0 : ℝ)..1, ‖deriv (g ∘ roundingArc ε θ) t‖) ≤
      (L : ℝ) * (Real.pi / 2 + 6 * θ) * ε := by
  have ht : MapsTo (roundingArc ε θ) (Icc (0 : ℝ) 1) (ball 0 R) := by
    intro t ht
    rw [mem_ball, dist_zero_right, norm_roundingArc hε.le ht]
    exact (mul_le_of_le_one_right hε.le (radialProfile_bounds ht).2).trans_lt hεR
  simpa only [mul_assoc] using pullback_length_le g (roundingArc ε θ)
    hg ((contDiff_roundingArc ε θ).of_le (by simp)) hLip ht
    (fun t ht => norm_deriv_roundingArc_le hε hθ ht)

lemma pullback_shortRay_length (g : ℂ → ℂ) {R ε : ℝ} {L : NNReal}
    (hg : ContDiffOn ℝ 1 g (ball 0 R))
    (hLip : LipschitzOnWith L g (closedBall 0 R))
    (hε : 0 < ε) (hεR : ε < R) (ξ : ℂ) (hξ : ‖ξ‖ ≤ 1) :
    IntervalIntegrable (fun t => ‖deriv (g ∘ (fun t : ℝ => (ε * t) • ξ)) t‖)
      MeasureTheory.volume 0 1 ∧
    (∫ t in (0 : ℝ)..1, ‖deriv (g ∘ (fun t : ℝ => (ε * t) • ξ)) t‖) ≤ (L : ℝ) * ε := by
  have ht : MapsTo (fun t : ℝ => (ε * t) • ξ) (Icc (0 : ℝ) 1) (ball 0 R) := by
    intro t ht
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hε.le ht.1)]
    calc
      ε * t * ‖ξ‖ ≤ ε * t := mul_le_of_le_one_right (mul_nonneg hε.le ht.1) hξ
      _ ≤ ε := mul_le_of_le_one_right hε.le ht.2
      _ < R := hεR
  apply pullback_length_le g (fun t : ℝ => (ε * t) • ξ) hg (by fun_prop) hLip ht
  intro t ht
  have hd : HasDerivAt (fun s : ℝ => (ε * s) • ξ) (ε • ξ) t := by
    simpa using ((hasDerivAt_id t).const_mul ε).smul_const ξ
  rw [hd.deriv, norm_smul, Real.norm_eq_abs, abs_of_nonneg hε.le]
  exact mul_le_of_le_one_right hε.le hξ


lemma deleted_subinterval_sum_bound (n : ℕ) (node : ℕ → ℝ) (hm : Monotone node)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume (node 0) (node n))
    (M : ℝ) (hM : ∀ t ∈ Icc (node 0) (node n), |f t| ≤ M)
    (keep : ℕ → Prop) [DecidablePred keep] :
    (∫ t in (node 0)..(node n), f t) =
      (∑ k ∈ (Finset.range n).filter keep, ∫ t in (node k)..(node (k+1)), f t) +
      (∑ k ∈ (Finset.range n).filter (fun k => ¬ keep k),
        ∫ t in (node k)..(node (k+1)), f t) ∧
    |(∫ t in (node 0)..(node n), f t) -
      (∑ k ∈ (Finset.range n).filter keep, ∫ t in (node k)..(node (k+1)), f t)| ≤
      M * ∑ k ∈ (Finset.range n).filter (fun k => ¬ keep k), (node (k+1) - node k) := by
  have hi : ∀ k < n, IntervalIntegrable f volume (node k) (node (k+1)) := by
    intro k hk
    exact hf.mono_set (by
      rw [uIcc_of_le (hm (Nat.zero_le n)), uIcc_of_le (hm (Nat.le_succ k))]
      exact Icc_subset_Icc (hm (Nat.zero_le k)) (hm (Nat.succ_le_of_lt hk)))
  have he : (∫ t in (node 0)..(node n), f t) =
      (∑ k ∈ (Finset.range n).filter keep, ∫ t in (node k)..(node (k+1)), f t) +
      (∑ k ∈ (Finset.range n).filter (fun k => ¬ keep k),
        ∫ t in (node k)..(node (k+1)), f t) := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact (intervalIntegral.sum_integral_adjacent_intervals hi).symm
  refine ⟨he, ?_⟩
  rw [he, add_sub_cancel_left, Finset.mul_sum]
  calc
    _ ≤ ∑ k ∈ (Finset.range n).filter (fun k => ¬ keep k),
        |∫ t in (node k)..(node (k+1)), f t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k < n := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := node k) (b := node (k+1)) (C := M) (f := f) (fun t ht => ?_)
      · simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hm (Nat.le_succ k)))] using hb
      · apply hM
        have ht' : t ∈ Ioc (node k) (node (k+1)) := by
          simpa only [uIoc_of_le (hm (Nat.le_succ k))] using ht
        exact ⟨(hm (Nat.zero_le k)).trans ht'.1.le,
          ht'.2.trans (hm (Nat.succ_le_of_lt hkn))⟩

section CircleNormal
open D12Complex.ComplexGreenBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
lemma gradient_signed_circle (c : ℂ) (r s : ℝ) (z : ℂ) :
    gradient (fun w : ℂ => s * (‖w - c‖ ^ 2 - r ^ 2)) z =
      (2 * s) • (z - c) := by
  have hd := (((hasFDerivAt_id z).sub_const c).norm_sq.sub_const (r ^ 2)).const_mul s
  simp only [id_eq] at hd
  apply ext_inner_right ℝ
  intro w
  rw [inner_gradient_left, hd.fderiv]
  simp
  ring

lemma outwardNormal_signed_circle {D V : Set (Specs.D04.C01.EuclideanInterfaces.Model.E 2)}
    (hD : IsClassicalRegularDomain D) (c : ℂ) (r s t : ℝ)
    (hr : 0 < r) (hs : s = 1 ∨ s = -1)
    (p : frontier D)
    (hp : (p : Specs.D04.C01.EuclideanInterfaces.Model.E 2) = planeIsometry (D12Complex.CircularExhaustion.arcParam c r t))
    (hρ : IsDefiningFunction D V
      (fun x => s * (‖planeIsometry.symm x - c‖ ^ 2 - r ^ 2)))
    (hpV : (p : Specs.D04.C01.EuclideanInterfaces.Model.E 2) ∈ V) :
    planeIsometry.symm (outwardNormal hD p) = s • Complex.exp ((t : ℂ) * Complex.I) := by
  have hg : (fun x : Specs.D04.C01.EuclideanInterfaces.Model.E 2 => s * (‖planeIsometry.symm x - c‖ ^ 2 - r ^ 2)) ∘
      planeIsometry = (fun z : ℂ => s * (‖z - c‖ ^ 2 - r ^ 2)) := by
    funext z
    simp only [Function.comp_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [outwardNormal_defining hD p _ hρ hpV, hg, gradient_signed_circle]
  rw [hp]
  simp only [LinearIsometryEquiv.symm_apply_apply, D12Complex.CircularExhaustion.arcParam,
    add_sub_cancel_left]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  rcases hs with rfl | rfl
  · simp only [mul_one, one_smul]
    simp only [norm_smul, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs,
      abs_of_pos hr]
    norm_num
    field_simp
  · norm_num only [mul_neg, mul_one, neg_smul, one_smul]
    simp only [norm_neg, norm_smul, norm_mul, Complex.norm_real,
      Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs, abs_of_pos hr]
    norm_num
    field_simp
lemma signed_circle_frontier (c : ℂ) (r s : ℝ) (hr : 0 < r)
    (hs : s = 1 ∨ s = -1) :
    frontier {z : ℂ | s * (‖z - c‖ ^ 2 - r ^ 2) < 0} = Metric.sphere c r := by
  rcases hs with rfl | rfl
  · have he : {z : ℂ | (1 : ℝ) * (‖z - c‖ ^ 2 - r ^ 2) < 0} = Metric.ball c r := by
      ext z
      simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm]
      constructor <;> intro h <;> nlinarith [norm_nonneg (z - c)]
    rw [he, frontier_ball c (ne_of_gt hr)]
  · have he : {z : ℂ | (-1 : ℝ) * (‖z - c‖ ^ 2 - r ^ 2) < 0} =
        (Metric.closedBall c r)ᶜ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Metric.mem_closedBall,
        dist_eq_norm, not_le]
      constructor <;> intro h <;> nlinarith [norm_nonneg (z - c)]
    rw [he, frontier_compl, frontier_closedBall c (ne_of_gt hr)]

lemma signed_circle_zero_iff (c : ℂ) (r s : ℝ) (hr : 0 < r)
    (hs : s = 1 ∨ s = -1) (z : ℂ) :
    s * (‖z - c‖ ^ 2 - r ^ 2) = 0 ↔ ‖z - c‖ = r := by
  rcases hs with rfl | rfl <;> constructor <;> intro h
  · nlinarith [norm_nonneg (z - c)]
  · rw [h]; ring
  · nlinarith [norm_nonneg (z - c)]
  · rw [h]; ring

lemma frontier_iff_signed_circle_zero {D W : Set ℂ} (c : ℂ) (r s : ℝ)
    (hr : 0 < r) (hs : s = 1 ∨ s = -1) (hW : IsOpen W)
    (hside : ∀ z ∈ W, z ∈ D ↔ s * (‖z - c‖ ^ 2 - r ^ 2) < 0)
    {z : ℂ} (hz : z ∈ W) :
    z ∈ frontier D ↔ s * (‖z - c‖ ^ 2 - r ^ 2) = 0 := by
  let Q : Set ℂ := {z | s * (‖z - c‖ ^ 2 - r ^ 2) < 0}
  have he : D ∩ W = Q ∩ W := by
    ext z
    simp only [Set.mem_inter_iff]
    exact and_congr_left (fun hz => hside z hz)
  have hfe : frontier D ∩ W = frontier Q ∩ W := by
    rw [← frontier_inter_open_inter hW, he, frontier_inter_open_inter hW]
  have hfz : z ∈ frontier D ↔ z ∈ frontier Q := by
    exact ⟨fun h => ((Set.ext_iff.mp hfe z).mp ⟨h, hz⟩).1,
      fun h => ((Set.ext_iff.mp hfe z).mpr ⟨h, hz⟩).1⟩
  rw [hfz, show frontier Q = Metric.sphere c r from signed_circle_frontier c r s hr hs]
  simpa only [Metric.mem_sphere, dist_eq_norm] using
    (signed_circle_zero_iff c r s hr hs z).symm

lemma signed_circle_defining_function {D W : Set ℂ}
    (c : ℂ) (r s : ℝ) (hr : 0 < r) (hs : s = 1 ∨ s = -1)
    (hW : IsOpen W)
    (hside : ∀ z ∈ W, z ∈ D ↔ s * (‖z - c‖ ^ 2 - r ^ 2) < 0) :
    IsDefiningFunction (planeIsometry '' D) (planeIsometry '' W)
      (fun x => s * (‖planeIsometry.symm x - c‖ ^ 2 - r ^ 2)) := by
  have hmem (x : Specs.D04.C01.EuclideanInterfaces.Model.E 2) : x ∈ planeIsometry '' D ↔ planeIsometry.symm x ∈ D := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [LinearIsometryEquiv.symm_apply_apply] using hz
    · intro hx
      exact ⟨planeIsometry.symm x, hx, planeIsometry.apply_symm_apply x⟩
  have hxW (x : Specs.D04.C01.EuclideanInterfaces.Model.E 2) (hx : x ∈ planeIsometry '' W) : planeIsometry.symm x ∈ W := by
    obtain ⟨z, hz, rfl⟩ := hx
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hz
  have hreg : ContDiff ℝ 1 (fun x : Specs.D04.C01.EuclideanInterfaces.Model.E 2 => s * (‖planeIsometry.symm x - c‖ ^ 2 - r ^ 2)) :=
    contDiff_const.mul (((planeIsometry.symm.toContinuousLinearEquiv.contDiff.sub
      contDiff_const).norm_sq ℝ).sub contDiff_const)
  refine ⟨planeIsometry.toHomeomorph.isOpenMap W hW, hreg.contDiffOn, ?_, ?_, ?_⟩
  · intro x hx
    exact (hmem x).trans (hside _ (hxW x hx))
  · intro x hx
    rw [frontier_image]
    have hfr (x : Specs.D04.C01.EuclideanInterfaces.Model.E 2) : x ∈ planeIsometry '' frontier D ↔
        planeIsometry.symm x ∈ frontier D := by
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa only [LinearIsometryEquiv.symm_apply_apply] using hz
      · intro h
        exact ⟨planeIsometry.symm x, h, planeIsometry.apply_symm_apply x⟩
    exact (hfr x).trans (frontier_iff_signed_circle_zero c r s hr hs hW hside (hxW x hx))
  · intro x hx hzero hderiv
    let z := planeIsometry.symm x
    have hz : ‖z - c‖ = r := (signed_circle_zero_iff c r s hr hs z).mp hzero
    have hc := (((hasFDerivAt_id z).sub_const c).norm_sq.sub_const (r ^ 2)).const_mul s
    simp only [id_eq] at hc
    have hρdiff : DifferentiableAt ℝ
        (fun x : Specs.D04.C01.EuclideanInterfaces.Model.E 2 => s * (‖planeIsometry.symm x - c‖ ^ 2 - r ^ 2)) (planeIsometry z) := by
      exact hreg.differentiable (by norm_num) _
    have hf := hρdiff.hasFDerivAt.comp z planeIsometry.toContinuousLinearEquiv.hasFDerivAt
    have heq : (fun x : Specs.D04.C01.EuclideanInterfaces.Model.E 2 => s * (‖planeIsometry.symm x - c‖ ^ 2 - r ^ 2)) ∘
        planeIsometry = (fun z : ℂ => s * (‖z - c‖ ^ 2 - r ^ 2)) := by
      funext w
      simp only [Function.comp_apply, LinearIsometryEquiv.symm_apply_apply]
    rw [heq] at hf
    have hf0 : fderiv ℝ (fun z : ℂ => s * (‖z - c‖ ^ 2 - r ^ 2)) z = 0 := by
      rw [hf.fderiv]
      change (fderiv ℝ (fun x : Specs.D04.C01.EuclideanInterfaces.Model.E 2 => s * (‖planeIsometry.symm x - c‖ ^ 2 - r ^ 2))
        (planeIsometry z)).comp _ = 0
      have hzx : planeIsometry z = x := planeIsometry.apply_symm_apply x
      rw [hzx, hderiv, ContinuousLinearMap.zero_comp]
    have hval := congrArg (fun f : ℂ →L[ℝ] ℝ => f (z - c)) hf0
    rw [hc.fderiv] at hval
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, zero_apply] at hval
    rw [real_inner_self_eq_norm_sq, hz] at hval
    norm_num [smul_eq_mul] at hval
    rcases hs with rfl | rfl <;> norm_num at hval <;> linarith


lemma outwardNormal_signed_circle_of_local_side {D W : Set ℂ}
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (c : ℂ) (r s t : ℝ) (hr : 0 < r) (hs : s = 1 ∨ s = -1)
    (p : frontier (planeIsometry '' D))
    (hp : (p : Specs.D04.C01.EuclideanInterfaces.Model.E 2) = planeIsometry (D12Complex.CircularExhaustion.arcParam c r t))
    (hW : IsOpen W) (hpW : D12Complex.CircularExhaustion.arcParam c r t ∈ W)
    (hside : ∀ z ∈ W, z ∈ D ↔ s * (‖z - c‖ ^ 2 - r ^ 2) < 0) :
    planeIsometry.symm (outwardNormal hD p) = s • Complex.exp ((t : ℂ) * Complex.I) := by
  apply outwardNormal_signed_circle hD c r s t hr hs p hp
    (signed_circle_defining_function c r s hr hs hW hside)
  rw [hp]
  exact Set.mem_image_of_mem _ hpW

end CircleNormal

/-- The literal finite-chart surgery, with the genuine D04 density identity.
No boundary-parameter representation is included in this proper part. -/
lemma chart_surgery_harmonic_green {U O : Set ℂ} {J : Finset ℂ}
    (hgeom : RoundingGeometry U J)
    (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (θ : ℂ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hθ : ∀ p ∈ J, 0 < θ p ∧ θ p < 2 * Real.pi)
    (hside : ∀ p ∈ J, (e p).IsImage U (CircularExhaustion.sector (θ p)))
    (hc : ∀ p ∈ J, ContDiffOn ℝ 1 (e p) (e p).source ∧
      ContDiffOn ℝ 1 (e p).symm (e p).target)
    (hp : ∀ p ∈ J, p ∈ (e p).source ∧ e p p = 0)
    (hdisj : ∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (e p).source (e q).source)
    (htip : ∀ p ∈ J, sectorTip ε (θ p) ⊆ (e p).target)
    (hO : IsOpen O) (hUO : closure U ⊆ O)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O)
    (hLu : ∀ z ∈ U, coordinateLaplacian u z = 0)
    (hLv : ∀ z ∈ U, coordinateLaplacian v z = 0) :
    let V := U \ ⋃ p ∈ J, (e p).symm '' sectorTip ε (θ p)
    ∃ hV : Specs.D04.C12.ClassicalRegularDomains.Model.IsClassicalRegularDomain
        (ComplexGreenBridge.planeIsometry '' V),
      HasC1DefiningFunctions V ∧ HasRegularBoundaryParametrizations V ∧ closure V ⊆ O ∧
      Specs.D04.C12.GaussDivergenceTheorem.Model.HasDensityIntegral (d := 1)
        (ComplexGreenBridge.boundaryFlux hV u v) 0 ∧
      Specs.D04.C12.IntegrationByPartsAndGreenIdentities.Model.boundaryIntegral
        (ComplexGreenBridge.boundaryFlux hV u v) = 0 := by
  have H := finite_chart_surgery hgeom e θ hε hθ hside hc hp hdisj htip
  have hVO : closure (U \ ⋃ p ∈ J, (e p).symm '' sectorTip ε (θ p)) ⊆ O :=
    (closure_mono sdiff_subset).trans hUO
  refine ⟨H.2.2.2.1, H.2.2.1, H.2.2.2.2, hVO, ?_⟩
  exact ComplexGreenBridge.harmonic_second_green _ O H.2.2.2.1 hO hVO u v hu hv
    (fun z hz => hLu z hz.1) (fun z hz => hLv z hz.1)


lemma parametrized_flux_integrable {O : Set ℂ} (hO : IsOpen O)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O)
    (γ N : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (htrace : MapsTo γ (Icc a b) O)
    (hN : ContinuousOn N (Icc a b))
    (hspeed : IntervalIntegrable (fun t => ‖deriv γ t‖) volume a b) :
    IntervalIntegrable (fun t =>
      (u (γ t) * inner ℝ (gradient v (γ t)) (N t) -
       v (γ t) * inner ℝ (gradient u (γ t)) (N t)) * ‖deriv γ t‖) volume a b := by
  have hcu := hu.continuousOn.comp hγ htrace
  have hcv := hv.continuousOn.comp hγ htrace
  have hgu := (continuousOn_gradient hO hu).comp hγ htrace
  have hgv := (continuousOn_gradient hO hv).comp hγ htrace
  apply hspeed.continuousOn_mul
  rw [uIcc_of_le hab]
  exact (hcu.mul (hgv.inner hN)).sub (hcv.mul (hgu.inner hN))

lemma pullback_roundingArc_flux_bound {K O : Set ℂ} (hO : IsOpen O) (hKO : K ⊆ O)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z ∈ K, ∀ ν : ℂ, ‖ν‖ ≤ 1 →
      |u z * inner ℝ (gradient v z) ν - v z * inner ℝ (gradient u z) ν| ≤ M)
    (g : ℂ → ℂ) {R ε θ : ℝ} {L : NNReal}
    (hg : ContDiffOn ℝ 1 g (ball 0 R)) (hLip : LipschitzOnWith L g (closedBall 0 R))
    (hε : 0 < ε) (hεR : ε < R) (hθ : 0 < θ)
    (N : ℝ → ℂ) (hN : ContinuousOn N (Icc (0 : ℝ) 1))
    (hNnorm : ∀ t ∈ Icc (0 : ℝ) 1, ‖N t‖ ≤ 1)
    (htrace : MapsTo (g ∘ roundingArc ε θ) (Icc (0 : ℝ) 1) K) :
    IntervalIntegrable (fun t =>
      (u (g (roundingArc ε θ t)) * inner ℝ (gradient v (g (roundingArc ε θ t))) (N t) -
       v (g (roundingArc ε θ t)) * inner ℝ (gradient u (g (roundingArc ε θ t))) (N t)) *
        ‖deriv (g ∘ roundingArc ε θ) t‖) volume 0 1 ∧
    |∫ t in (0 : ℝ)..1,
      (u (g (roundingArc ε θ t)) * inner ℝ (gradient v (g (roundingArc ε θ t))) (N t) -
       v (g (roundingArc ε θ t)) * inner ℝ (gradient u (g (roundingArc ε θ t))) (N t)) *
        ‖deriv (g ∘ roundingArc ε θ) t‖| ≤
      M * (L : ℝ) * (Real.pi / 2 + 6 * θ) * ε := by
  have hpre : MapsTo (roundingArc ε θ) (Icc (0 : ℝ) 1) (ball 0 R) := by
    intro t ht
    rw [mem_ball, dist_zero_right, norm_roundingArc hε.le ht]
    exact (mul_le_of_le_one_right hε.le (radialProfile_bounds ht).2).trans_lt hεR
  have hcont : ContinuousOn (g ∘ roundingArc ε θ) (Icc (0 : ℝ) 1) :=
    hg.continuousOn.comp (contDiff_roundingArc ε θ).continuous.continuousOn hpre
  have H := pullback_roundingArc_length g hg hLip hε hεR hθ
  refine ⟨parametrized_flux_integrable hO u v hu hv _ N 0 1 (by norm_num)
    hcont (fun t ht => hKO (htrace ht)) hN H.1, ?_⟩
  calc
    _ ≤ M * ∫ t in (0 : ℝ)..1, ‖deriv (g ∘ roundingArc ε θ) t‖ :=
      parametrized_flux_integral_bound u v hbound _ N 0 1 (by norm_num) htrace hNnorm H.1
    _ ≤ M * ((L : ℝ) * (Real.pi / 2 + 6 * θ) * ε) := mul_le_mul_of_nonneg_left H.2 hM
    _ = _ := by ring

lemma tendsto_zero_of_linear_bound {F : ℝ → ℝ} {C δ : ℝ} (hδ : 0 < δ)
    (hF : ∀ ε ∈ Ioo (0 : ℝ) δ, |F ε| ≤ C * ε) :
    Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' (a := fun ε => C * ε) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with ε hε hεsmall
    simpa only [Real.norm_eq_abs] using hF ε ⟨hε, hεsmall⟩
  · simpa using (tendsto_const_nhds.mul hid :
      Tendsto (fun ε : ℝ => C * ε) (𝓝[>] (0 : ℝ)) (𝓝 (C * 0)))


/-- The first local rounding limit uses a single compact flux bound and actual
parameter speed. The normal fields may vary arbitrarily with the scale. -/
lemma pullback_roundingArc_flux_tendsto_zero {K O : Set ℂ}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O)
    (g : ℂ → ℂ) {R θ : ℝ} {L : NNReal} (hR : 0 < R) (hθ : 0 < θ)
    (hg : ContDiffOn ℝ 1 g (ball 0 R)) (hLip : LipschitzOnWith L g (closedBall 0 R))
    (N : ℝ → ℝ → ℂ)
    (hN : ∀ ε ∈ Ioo (0 : ℝ) R, ContinuousOn (N ε) (Icc (0 : ℝ) 1))
    (hNnorm : ∀ ε ∈ Ioo (0 : ℝ) R, ∀ t ∈ Icc (0 : ℝ) 1, ‖N ε t‖ ≤ 1)
    (htrace : ∀ ε ∈ Ioo (0 : ℝ) R,
      MapsTo (g ∘ roundingArc ε θ) (Icc (0 : ℝ) 1) K) :
    Tendsto (fun ε => ∫ t in (0 : ℝ)..1,
      (u (g (roundingArc ε θ t)) * inner ℝ (gradient v (g (roundingArc ε θ t))) (N ε t) -
       v (g (roundingArc ε θ t)) * inner ℝ (gradient u (g (roundingArc ε θ t))) (N ε t)) *
        ‖deriv (g ∘ roundingArc ε θ) t‖) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  obtain ⟨M, hM, hbound⟩ := compact_scalar_flux_bound hK hO hKO u v hu hv
  apply tendsto_zero_of_linear_bound (C := M * (L : ℝ) * (Real.pi / 2 + 6 * θ)) hR
  intro ε hε
  exact (pullback_roundingArc_flux_bound hO hKO u v hu hv hM.le hbound g hg hLip
    hε.1 hε.2 hθ (N ε) (hN ε hε) (hNnorm ε hε) (htrace ε hε)).2

lemma pullback_shortRay_flux_bound {K O : Set ℂ} (hO : IsOpen O) (hKO : K ⊆ O)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z ∈ K, ∀ ν : ℂ, ‖ν‖ ≤ 1 →
      |u z * inner ℝ (gradient v z) ν - v z * inner ℝ (gradient u z) ν| ≤ M)
    (g : ℂ → ℂ) {R ε : ℝ} {L : NNReal}
    (hg : ContDiffOn ℝ 1 g (ball 0 R)) (hLip : LipschitzOnWith L g (closedBall 0 R))
    (hε : 0 < ε) (hεR : ε < R) (ξ : ℂ) (hξ : ‖ξ‖ ≤ 1)
    (N : ℝ → ℂ) (hN : ContinuousOn N (Icc (0 : ℝ) 1))
    (hNnorm : ∀ t ∈ Icc (0 : ℝ) 1, ‖N t‖ ≤ 1)
    (htrace : MapsTo (g ∘ (fun t : ℝ => (ε * t) • ξ)) (Icc (0 : ℝ) 1) K) :
    IntervalIntegrable (fun t =>
      (u (g ((ε * t) • ξ)) * inner ℝ (gradient v (g ((ε * t) • ξ))) (N t) -
       v (g ((ε * t) • ξ)) * inner ℝ (gradient u (g ((ε * t) • ξ))) (N t)) *
        ‖deriv (g ∘ (fun t : ℝ => (ε * t) • ξ)) t‖) volume 0 1 ∧
    |∫ t in (0 : ℝ)..1,
      (u (g ((ε * t) • ξ)) * inner ℝ (gradient v (g ((ε * t) • ξ))) (N t) -
       v (g ((ε * t) • ξ)) * inner ℝ (gradient u (g ((ε * t) • ξ))) (N t)) *
        ‖deriv (g ∘ (fun t : ℝ => (ε * t) • ξ)) t‖| ≤ M * (L : ℝ) * ε := by
  have hpre : MapsTo (fun t : ℝ => (ε * t) • ξ) (Icc (0 : ℝ) 1) (ball 0 R) := by
    intro t ht
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hε.le ht.1)]
    exact (mul_le_of_le_one_right (mul_nonneg hε.le ht.1) hξ).trans_lt
      ((mul_le_of_le_one_right hε.le ht.2).trans_lt hεR)
  have hcont : ContinuousOn (g ∘ (fun t : ℝ => (ε * t) • ξ)) (Icc (0 : ℝ) 1) :=
    hg.continuousOn.comp (by fun_prop) hpre
  have H := pullback_shortRay_length g hg hLip hε hεR ξ hξ
  refine ⟨parametrized_flux_integrable hO u v hu hv _ N 0 1 (by norm_num)
    hcont (fun t ht => hKO (htrace ht)) hN H.1, ?_⟩
  calc
    _ ≤ M * ∫ t in (0 : ℝ)..1, ‖deriv (g ∘ (fun t : ℝ => (ε * t) • ξ)) t‖ :=
      parametrized_flux_integral_bound u v hbound _ N 0 1 (by norm_num) htrace hNnorm H.1
    _ ≤ M * ((L : ℝ) * ε) := mul_le_mul_of_nonneg_left H.2 hM
    _ = _ := by ring

lemma pullback_shortRay_flux_tendsto_zero {K O : Set ℂ}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O)
    (g : ℂ → ℂ) {R : ℝ} {L : NNReal} (hR : 0 < R)
    (hg : ContDiffOn ℝ 1 g (ball 0 R)) (hLip : LipschitzOnWith L g (closedBall 0 R))
    (ξ : ℂ) (hξ : ‖ξ‖ ≤ 1) (N : ℝ → ℝ → ℂ)
    (hN : ∀ ε ∈ Ioo (0 : ℝ) R, ContinuousOn (N ε) (Icc (0 : ℝ) 1))
    (hNnorm : ∀ ε ∈ Ioo (0 : ℝ) R, ∀ t ∈ Icc (0 : ℝ) 1, ‖N ε t‖ ≤ 1)
    (htrace : ∀ ε ∈ Ioo (0 : ℝ) R,
      MapsTo (g ∘ (fun t : ℝ => (ε * t) • ξ)) (Icc (0 : ℝ) 1) K) :
    Tendsto (fun ε => ∫ t in (0 : ℝ)..1,
      (u (g ((ε * t) • ξ)) * inner ℝ (gradient v (g ((ε * t) • ξ))) (N ε t) -
       v (g ((ε * t) • ξ)) * inner ℝ (gradient u (g ((ε * t) • ξ))) (N ε t)) *
        ‖deriv (g ∘ (fun t : ℝ => (ε * t) • ξ)) t‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  obtain ⟨M, hM, hbound⟩ := compact_scalar_flux_bound hK hO hKO u v hu hv
  apply tendsto_zero_of_linear_bound (C := M * (L : ℝ)) hR
  intro ε hε
  exact (pullback_shortRay_flux_bound hO hKO u v hu hv hM.le hbound g hg hLip
    hε.1 hε.2 ξ hξ (N ε) (hN ε hε) (hNnorm ε hε) (htrace ε hε)).2


section SurgeryAssembly
open D12Complex.ComplexGreenBridge D12Complex.ParametrizedBoundaryDisplay
open D12Complex.CircularSurgeryPartition
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.ClassicalRegularDomains.Model

lemma normalAt_signed_circle_of_local_side {V W : Set ℂ}
    (hV : IsClassicalRegularDomain (planeIsometry '' V))
    (c : ℂ) (r s t : ℝ) (hr : 0 < r) (hs : s = 1 ∨ s = -1)
    (hfront : arcParam c r t ∈ frontier V)
    (hW : IsOpen W) (htW : arcParam c r t ∈ W)
    (hside : ∀ z ∈ W, z ∈ V ↔ s * (‖z - c‖ ^ 2 - r ^ 2) < 0) :
    normalAt hV (arcParam c r t) = s • Complex.exp ((t : ℂ) * Complex.I) := by
  have hz : planeIsometry (arcParam c r t) ∈ frontier (planeIsometry '' V) := by
    rw [frontier_image]
    exact mem_image_of_mem _ hfront
  rw [normalAt_eq_actual hV _ hz]
  exact outwardNormal_signed_circle_of_local_side hV c r s t hr hs
    ⟨planeIsometry (arcParam c r t), hz⟩ rfl hW htW hside

lemma norm_normalAt_le_one {V : Set ℂ}
    (hV : IsClassicalRegularDomain (planeIsometry '' V)) (z : ℂ) :
    ‖normalAt hV z‖ ≤ 1 := by
  unfold normalAt
  split_ifs with hz
  · simpa only [LinearIsometryEquiv.norm_map] using
      (D04.ClassicalRegularDomains.outwardNormal_unit hV
        ⟨planeIsometry z, hz⟩).le
  · simp

lemma norm_deriv_arcParam (c : ℂ) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    ‖deriv (arcParam c r) t‖ = r := by
  change ‖deriv (circleMap c r) t‖ = r
  rw [(FiniteCircularArcs.circle_hasDerivAt c r t).deriv]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, Complex.norm_I, mul_one, abs_of_pos hr]

lemma literalIntegrand_circle_of_local_side {V W : Set ℂ}
    (hV : IsClassicalRegularDomain (planeIsometry '' V))
    (c : ℂ) (r s t : ℝ) (hr : 0 < r) (hs : s = 1 ∨ s = -1)
    (hfront : arcParam c r t ∈ frontier V)
    (hW : IsOpen W) (htW : arcParam c r t ∈ W)
    (hside : ∀ z ∈ W, z ∈ V ↔ s * (‖z - c‖ ^ 2 - r ^ 2) < 0)
    (u v : ℂ → ℝ) :
    literalIntegrand hV (arcParam c r) u v t =
      (u (arcParam c r t) * inner ℝ (gradient v (arcParam c r t))
        (s • Complex.exp ((t : ℂ) * Complex.I)) -
       v (arcParam c r t) * inner ℝ (gradient u (arcParam c r t))
        (s • Complex.exp ((t : ℂ) * Complex.I))) * r := by
  rw [literalIntegrand,
    normalAt_signed_circle_of_local_side hV c r s t hr hs hfront hW htW hside,
    norm_deriv_arcParam c hr]

open CircularSurgeryPartition
lemma retained_literalIntegrand_eq {U : Set ℂ} {J : Finset ℂ} {n : ℕ}
    {center : Fin n → ℂ} {radius start stop sign : Fin n → ℝ}
    {e : ℂ → OpenPartialHomeomorph ℂ ℂ} {θ : ℂ → ℝ} {C ε : ℝ}
    (P : SurgeryPartitionAt U J n center radius start stop sign e θ C ε)
    (hV : IsClassicalRegularDomain (planeIsometry '' surgeryDomain U J e θ ε))
    (hr : ∀ i, 0 < radius i) (hs : ∀ i, sign i = 1 ∨ sign i = -1)
    (i : Fin n) (j : Fin (P.subdivision i).count) (hj : (P.subdivision i).keep j = true)
    (u v : ℂ → ℝ) (t : ℝ)
    (ht : t ∈ Ioo ((P.subdivision i).node j.castSucc) ((P.subdivision i).node j.succ)) :
    literalIntegrand hV (arcParam (center i) (radius i)) u v t =
      (u (arcParam (center i) (radius i) t) *
        inner ℝ (gradient v (arcParam (center i) (radius i) t))
          (sign i • Complex.exp ((t : ℂ) * Complex.I)) -
       v (arcParam (center i) (radius i) t) *
        inner ℝ (gradient u (arcParam (center i) (radius i) t))
          (sign i • Complex.exp ((t : ℂ) * Complex.I))) * radius i := by
  obtain ⟨W, hW, htW, _, hside⟩ := P.retained_side i j t hj ht
  exact literalIntegrand_circle_of_local_side hV (center i) (radius i) (sign i) t
    (hr i) (hs i) (P.retained_closed i j hj (mem_image_of_mem _ ⟨ht.1.le, ht.2.le⟩))
    hW htW hside u v

lemma localRegularExtension_of_embedding {V : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (h : HasLocalRegularExtensions V γ a b) :
    LocalRegularExtension V γ a b := by
  classical
  intro t ht
  obtain ⟨δ, W, η, hδ, hW, htW, hη, hn, heq, hemb, himage⟩ := h t ht
  let I : Set ℝ := Ioo (t - δ) (t + δ)
  let f : I → ℂ := fun s => η s
  have hI : t ∈ I := by dsimp [I]; constructor <;> linarith
  let : Nonempty I := ⟨⟨t, hI⟩⟩
  let E := hemb.toPartialHomeomorph f
  let κ : ℂ → ℝ := fun z => E.symm z
  have hrange : Set.range f = frontier V ∩ W := by
    have hr : Set.range f = η '' I := by
      ext z
      simp [f, Set.mem_image]
    rw [hr]
    exact himage
  have htarget : E.target = frontier V ∩ W := by
    simpa only [E, Topology.IsEmbedding.toPartialHomeomorph_target] using hrange
  refine ⟨δ, W, η, κ, hδ, hW, htW, hη, hn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact heq s ⟨hs.2, hs.1⟩
  · intro s hs
    rw [← himage]
    exact mem_image_of_mem η hs
  · intro z hz
    exact (E.symm z).property
  · intro s hs
    change ((E.symm (f ⟨s, hs⟩) : I) : ℝ) = s
    rw [Topology.IsEmbedding.toPartialHomeomorph_left_inv]
  · intro z hz
    have hzE : z ∈ E.target := htarget.symm ▸ hz
    exact E.right_inv hzE
  · have hcont : ContinuousOn (fun z : ℂ => ((E.symm z : I) : ℝ)) E.target :=
      continuous_subtype_val.comp_continuousOn E.continuousOn_symm
    exact htarget ▸ hcont

lemma regularBoundaryCurves_of_partition {U : Set ℂ} {J : Finset ℂ} {n : ℕ}
    {center : Fin n → ℂ} {radius start stop sign : Fin n → ℝ}
    {e : ℂ → OpenPartialHomeomorph ℂ ℂ} {θ : ℂ → ℝ} {C ε : ℝ}
    (P : SurgeryPartitionAt U J n center radius start stop sign e θ C ε) :
    ∃ T : Fin P.m → Set ℝ,
      RegularBoundaryCurves (surgeryDomain U J e θ ε) P.m P.γ P.a P.b T := by
  choose T hT hI hγ hn using P.regular_neighborhood
  exact ⟨T, ⟨P.ordered, hT, hI, hγ, hn, P.frontier_eq, P.injective_open,
    P.disjoint_open, fun i => localRegularExtension_of_embedding (P.extensions i)⟩⟩


lemma fin_integral_adjacent (k : ℕ) (node : Fin (k+1) → ℝ)
    (hm : Monotone node) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (node 0) (node (Fin.last k))) :
    (∑ j : Fin k, ∫ t in node j.castSucc..node j.succ, f t) =
      ∫ t in node 0..node (Fin.last k), f t := by
  let a : ℕ → ℝ := fun j => node ⟨min j k, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have he (j : ℕ) (hj : j ≤ k) : a j = node ⟨j, Nat.lt_succ_of_le hj⟩ := by
    simp [a, min_eq_left hj]
  have ham : Monotone a := fun i j hij => hm (by simpa [a] using min_le_min_right k hij)
  have hi : ∀ j < k, IntervalIntegrable f volume (a j) (a (j+1)) := by
    intro j hj
    apply hf.mono_set
    rw [uIcc_of_le (hm (Fin.zero_le _)), uIcc_of_le (ham (Nat.le_succ j))]
    apply Icc_subset_Icc
    · change node 0 ≤ node _
      exact hm (Fin.zero_le _)
    · change node _ ≤ node (Fin.last k)
      exact hm (Fin.le_last _)
  have H := intervalIntegral.sum_integral_adjacent_intervals hi
  rw [← Fin.sum_univ_eq_sum_range] at H
  calc
    _ = ∑ j : Fin k, ∫ t in a j.val..a (j.val+1), f t := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [he _ (Nat.le_of_lt j.isLt), he _ (Nat.succ_le_of_lt j.isLt)]
      rfl
    _ = ∫ t in a 0..a k, f t := H
    _ = _ := by rw [he 0 (Nat.zero_le k), he k le_rfl]; rfl

lemma subdivision_flux_error {n : ℕ} {a b radius : Fin n → ℝ}
    (P : ∀ i, AngularSubdivision (a i) (b i)) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, IntervalIntegrable (f i) volume (a i) (b i))
    (M : ℝ) (hpoint : ∀ i t, t ∈ Icc (a i) (b i) → |f i t| ≤ M * radius i) :
    |(∑ i, ∫ t in a i..b i, f i t) -
      (∑ i, ∑ j : Fin (P i).count,
        if (P i).keep j then ∫ t in (P i).node j.castSucc..(P i).node j.succ, f i t else 0)| ≤
      M * (∑ i, ∑ j : Fin (P i).count,
        if (P i).keep j then 0 else radius i * ((P i).node j.succ - (P i).node j.castSucc)) := by
  classical
  have hbound (i : Fin n) (j : Fin (P i).count) :
      |∫ t in (P i).node j.castSucc..(P i).node j.succ, f i t| ≤
        M * (radius i * ((P i).node j.succ - (P i).node j.castSucc)) := by
    have hab := (P i).strict (show j.castSucc < j.succ from Fin.castSucc_lt_succ)
    have H := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (P i).node j.castSucc) (b := (P i).node j.succ)
      (C := M * radius i) (f := f i) (fun t ht => ?_)
    · simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab), mul_assoc] using H
    · apply hpoint i t
      have ht' : t ∈ Ioc ((P i).node j.castSucc) ((P i).node j.succ) := by
        simpa only [uIoc_of_le hab.le] using ht
      constructor
      · rw [← (P i).first]
        exact ((P i).strict.monotone (Fin.zero_le _)).trans ht'.1.le
      · rw [← (P i).last]
        exact ht'.2.trans ((P i).strict.monotone (Fin.le_last _))
  have heq : (∑ i, ∫ t in a i..b i, f i t) =
      (∑ i, ∑ j : Fin (P i).count,
        if (P i).keep j then ∫ t in (P i).node j.castSucc..(P i).node j.succ, f i t else 0) +
      (∑ i, ∑ j : Fin (P i).count,
        if (P i).keep j then 0 else ∫ t in (P i).node j.castSucc..(P i).node j.succ, f i t) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    have H := fin_integral_adjacent (P i).count (P i).node (P i).strict.monotone (f i)
      (by simpa only [(P i).first, (P i).last] using hf i)
    rw [(P i).first, (P i).last] at H
    rw [← H]
    apply Finset.sum_congr rfl
    intro j hj
    cases (P i).keep j <;> simp
  rw [heq, add_sub_cancel_left, Finset.mul_sum]
  calc
    _ ≤ ∑ i, |∑ j : Fin (P i).count,
        if (P i).keep j then 0 else ∫ t in (P i).node j.castSucc..(P i).node j.succ, f i t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mul_sum]
      calc
        _ ≤ ∑ j : Fin (P i).count,
            |if (P i).keep j then 0 else ∫ t in (P i).node j.castSucc..(P i).node j.succ, f i t| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j hj
          cases h : (P i).keep j
          · simpa only [h, Bool.false_eq_true, ↓reduceIte] using hbound i j
          · simp only [↓reduceIte, abs_zero, mul_zero, le_refl]


lemma inserted_curve_mem_closure {U : Set ℂ} {J : Finset ℂ} {n : ℕ}
    {center : Fin n → ℂ} {radius start stop sign : Fin n → ℝ}
    {e : ℂ → OpenPartialHomeomorph ℂ ℂ} {θ : ℂ → ℝ} {C ε : ℝ}
    (P : SurgeryPartitionAt U J n center radius start stop sign e θ C ε)
    (p : ℂ) (hp : p ∈ J) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (e p).symm (roundingArc ε (θ p) t) ∈ closure U := by
  let q := P.index.symm (Sum.inr ⟨p, hp⟩)
  have he : P.index q = Sum.inr ⟨p, hp⟩ := P.index.apply_symm_apply _
  obtain ⟨hγ, ha, hb⟩ := P.inserted_curve q ⟨p, hp⟩ he
  have hfront : (e p).symm (roundingArc ε (θ p) t) ∈
      frontier (surgeryDomain U J e θ ε) := by
    rw [P.frontier_eq]
    apply mem_iUnion.mpr
    refine ⟨q, ?_⟩
    rw [hγ, ha, hb]
    exact mem_image_of_mem _ ht
  exact closure_mono sdiff_subset (frontier_subset_closure hfront)

lemma inserted_flux_sum_bound {U : Set ℂ} {J : Finset ℂ} {n : ℕ}
    {center : Fin n → ℂ} {radius start stop sign : Fin n → ℝ}
    {e : ℂ → OpenPartialHomeomorph ℂ ℂ} {θ : ℂ → ℝ} {C ε M : ℝ}
    (P : SurgeryPartitionAt U J n center radius start stop sign e θ C ε)
    (hV : IsClassicalRegularDomain (planeIsometry '' surgeryDomain U J e θ ε))
    (u v : ℂ → ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z ∈ closure U, ∀ ν : ℂ, ‖ν‖ ≤ 1 →
      |u z * inner ℝ (gradient v z) ν - v z * inner ℝ (gradient u z) ν| ≤ M) :
    |∑ p ∈ J, ∫ t in (0 : ℝ)..1,
      literalIntegrand hV (fun s => (e p).symm (roundingArc ε (θ p) s)) u v t| ≤
      M * C * ε := by
  calc
    _ ≤ ∑ p ∈ J, |∫ t in (0 : ℝ)..1,
        literalIntegrand hV (fun s => (e p).symm (roundingArc ε (θ p) s)) u v t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ J, M * ∫ t in (0 : ℝ)..1,
        ‖deriv (fun s => (e p).symm (roundingArc ε (θ p) s)) t‖ := by
      apply Finset.sum_le_sum
      intro p hp
      apply parametrized_flux_integral_bound u v hbound
        (fun s => (e p).symm (roundingArc ε (θ p) s))
        (fun s => normalAt hV ((e p).symm (roundingArc ε (θ p) s))) 0 1
        (by norm_num)
        (fun t ht => inserted_curve_mem_closure P p hp t ht)
        (fun t _ => norm_normalAt_le_one hV _)
        (P.speed_integrable p hp)
    _ = M * (∑ p ∈ J, ∫ t in (0 : ℝ)..1,
        ‖deriv (fun s => (e p).symm (roundingArc ε (θ p) s)) t‖) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ M * (C * ε) := mul_le_mul_of_nonneg_left P.added_length hM
    _ = M * C * ε := (mul_assoc _ _ _).symm


lemma retained_literalIntegral_eq {U : Set ℂ} {J : Finset ℂ} {n : ℕ}
    {center : Fin n → ℂ} {radius start stop sign : Fin n → ℝ}
    {e : ℂ → OpenPartialHomeomorph ℂ ℂ} {θ : ℂ → ℝ} {C ε : ℝ}
    (P : SurgeryPartitionAt U J n center radius start stop sign e θ C ε)
    (hV : IsClassicalRegularDomain (planeIsometry '' surgeryDomain U J e θ ε))
    (hr : ∀ i, 0 < radius i) (hs : ∀ i, sign i = 1 ∨ sign i = -1)
    (i : Fin n) (j : Fin (P.subdivision i).count) (hj : (P.subdivision i).keep j = true)
    (u v : ℂ → ℝ) :
    (∫ t in ((P.subdivision i).node j.castSucc)..((P.subdivision i).node j.succ),
      literalIntegrand hV (arcParam (center i) (radius i)) u v t) =
    (∫ t in ((P.subdivision i).node j.castSucc)..((P.subdivision i).node j.succ),
      (u (arcParam (center i) (radius i) t) *
        inner ℝ (gradient v (arcParam (center i) (radius i) t))
          (sign i • Complex.exp ((t : ℂ) * Complex.I)) -
       v (arcParam (center i) (radius i) t) *
        inner ℝ (gradient u (arcParam (center i) (radius i) t))
          (sign i • Complex.exp ((t : ℂ) * Complex.I))) * radius i) := by
  apply intervalIntegral.integral_congr_Ioo_of_le
    ((P.subdivision i).strict (Fin.castSucc_lt_succ)).le
  intro t ht
  exact retained_literalIntegrand_eq P hV hr hs i j hj u v t ht


lemma surgeryPartition_sum
    {U : Set ℂ} {J : Finset ℂ} {n : ℕ} {center : Fin n → ℂ}
    {radius start stop sign : Fin n → ℝ}
    {e : ℂ → OpenPartialHomeomorph ℂ ℂ} {θ : ℂ → ℝ} {C ε : ℝ}
    (P : SurgeryPartitionAt U J n center radius start stop sign e θ C ε)
    (F : (ℝ → ℂ) → ℝ → ℝ → ℝ) :
    (∑ q, F (P.γ q) (P.a q) (P.b q)) =
      (∑ i, ∑ j : Fin (P.subdivision i).count,
        if (P.subdivision i).keep j then
          F (arcParam (center i) (radius i))
            ((P.subdivision i).node j.castSucc) ((P.subdivision i).node j.succ)
        else 0) +
      ∑ p ∈ J, F (fun t => (e p).symm (roundingArc ε (θ p) t)) 0 1 := by
  classical
  let : Fintype (RetainedIndex P.subdivision) :=
    inferInstanceAs (Fintype (Σ i, {j : Fin (P.subdivision i).count // (P.subdivision i).keep j = true}))
  let G : RetainedIndex P.subdivision ⊕ {p : ℂ // p ∈ J} → ℝ :=
    Sum.elim
      (fun d => F (arcParam (center d.1) (radius d.1))
        ((P.subdivision d.1).node d.2.1.castSucc) ((P.subdivision d.1).node d.2.1.succ))
      (fun p => F (fun t => (e p).symm (roundingArc ε (θ p) t)) 0 1)
  have heq : ∀ q, F (P.γ q) (P.a q) (P.b q) = G (P.index q) := by
    intro q
    rcases he : P.index q with d | p
    · obtain ⟨hγ, ha, hb⟩ := P.retained_curve q d he
      simp only [G, Sum.elim_inl, hγ, ha, hb]
    · obtain ⟨hγ, ha, hb⟩ := P.inserted_curve q p he
      simp only [G, Sum.elim_inr, hγ, ha, hb]
  rw [Fintype.sum_equiv P.index _ G heq, Fintype.sum_sum_type]
  apply congrArg₂ (fun x y : ℝ => x + y)
  · change (∑ d : (Σ i, {j : Fin (P.subdivision i).count // (P.subdivision i).keep j = true}),
        F (arcParam (center d.1) (radius d.1))
          ((P.subdivision d.1).node d.2.1.castSucc) ((P.subdivision d.1).node d.2.1.succ)) = _
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i hi
    let f : Fin (P.subdivision i).count → ℝ := fun j =>
      F (arcParam (center i) (radius i))
        ((P.subdivision i).node j.castSucc) ((P.subdivision i).node j.succ)
    change (∑ j : {j : Fin (P.subdivision i).count // (P.subdivision i).keep j = true},
      f j) = ∑ j, if (P.subdivision i).keep j then f j else 0
    rw [← Finset.sum_subtype (Finset.univ.filter (fun j => (P.subdivision i).keep j = true))
      (by simp) f, Finset.sum_filter]
  · exact (Finset.sum_subtype J (by simp)
      (fun p => F (fun t => (e p).symm (roundingArc ε (θ p) t)) 0 1)).symm


/-- Harmonic second Green identity on the supplied signed circular arrays.
The actual rounded display gives retained flux plus inserted flux equal to zero.
Exact finite subdivision and genuine removed/added parameter-length bounds give
an error at most `2 * M * C * ε`, uniformly in the number of retained pieces.
The first rounding limit therefore gives the asserted original zero sum. -/
theorem piecewise_circular_green :
    Specs.D12Complex.Ch14.PiecewiseCircularGreen.piecewise_circular_green_type := by
  classical
  intro U J hgeom n center radius start stop sign hr hs hcover hdisj hinj hside
    O hO hUO u v hu hv hLu hLv
  let f : Fin n → ℝ → ℝ := fun i t =>
    (u (arcParam (center i) (radius i) t) *
        inner ℝ (gradient v (arcParam (center i) (radius i) t))
          (sign i • Complex.exp ((t : ℂ) * Complex.I)) -
     v (arcParam (center i) (radius i) t) *
        inner ℝ (gradient u (arcParam (center i) (radius i) t))
          (sign i • Complex.exp ((t : ℂ) * Complex.I))) * radius i
  change (∀ i, IntervalIntegrable (f i) volume (start i) (stop i)) ∧
    (∑ i, ∫ t in start i..stop i, f i t) = 0
  have hfi : ∀ i, IntervalIntegrable (f i) volume (start i) (stop i) :=
    array_flux_intervalIntegrable hO hUO u v hu hv n center radius start stop sign
      (fun i => (hr i).2.1.le) hcover
  refine ⟨hfi, ?_⟩
  obtain ⟨θ, e, R, L, C, ε₀, hcharts, hC, hε₀, hε₀R, hpartition⟩ :=
    CircularSurgeryPartition.circular_surgery_partition U J hgeom n center radius start stop sign
      ⟨hr, hs, hcover, hdisj, hinj, hside⟩
  obtain ⟨M, hM, hbound⟩ := compact_scalar_flux_bound hgeom.2.1.isCompact_closure
    hO hUO u v hu hv
  have hpoint : ∀ i t, t ∈ Icc (start i) (stop i) → |f i t| ≤ M * radius i := by
    intro i t ht
    apply circle_flux_pointwise_bound u v hbound (center i) (radius i) (sign i) t (hr i).1.le
    · rcases hs i with hh | hh <;> simp [hh]
    · apply frontier_subset_closure
      rw [hcover]
      exact mem_iUnion.mpr ⟨i, mem_image_of_mem _ ht⟩
  have herr : ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      |(∑ i, ∫ t in start i..stop i, f i t)| ≤ (2 * M * C) * ε := by
    intro ε hε
    obtain ⟨hopen, hdef, hV, ⟨P⟩⟩ := hpartition ε hε.1 hε.2
    have hV' : IsClassicalRegularDomain (planeIsometry '' surgeryDomain U J e θ ε) := hV
    obtain ⟨T, hcurves⟩ := regularBoundaryCurves_of_partition P
    have hVO : closure (surgeryDomain U J e θ ε) ⊆ O :=
      (closure_mono sdiff_subset).trans hUO
    obtain ⟨hInt, hzero⟩ := ParametrizedBoundaryDisplay.parametrized_harmonic_green
      (surgeryDomain U J e θ ε) O hV' hO hVO P.m P.γ P.a P.b T hcurves
      u v hu hv (fun z hz => hLu z hz.1) (fun z hz => hLv z hz.1)
    let retained : ℝ := ∑ i, ∑ j : Fin (P.subdivision i).count,
      if (P.subdivision i).keep j then
        ∫ t in (P.subdivision i).node j.castSucc..(P.subdivision i).node j.succ, f i t
      else 0
    let inserted : ℝ := ∑ p ∈ J, ∫ t in (0 : ℝ)..1,
      literalIntegrand hV' (fun s => (e p).symm (roundingArc ε (θ p) s)) u v t
    have hsplit : retained + inserted = 0 := by
      have H := surgeryPartition_sum P
        (fun γ a b => ∫ t in a..b, literalIntegrand hV' γ u v t)
      rw [hzero] at H
      have heq : (∑ i, ∑ j : Fin (P.subdivision i).count,
          if (P.subdivision i).keep j then
            ∫ t in (P.subdivision i).node j.castSucc..(P.subdivision i).node j.succ,
              literalIntegrand hV' (arcParam (center i) (radius i)) u v t else 0) = retained := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        cases hk : (P.subdivision i).keep j
        · simp only [Bool.false_eq_true, ↓reduceIte]
        · simp only [↓reduceIte]
          exact retained_literalIntegral_eq P hV' (fun i => (hr i).1) hs i j hk u v
      rw [heq] at H
      exact H.symm
    have hretained : |retained| ≤ M * C * ε := by
      have H := inserted_flux_sum_bound P hV' u v hM.le hbound
      have he : retained = -inserted := eq_neg_of_add_eq_zero_left hsplit
      rw [he, abs_neg]
      exact H
    have hdeleted : |(∑ i, ∫ t in start i..stop i, f i t) - retained| ≤ M * C * ε := by
      calc
        _ ≤ M * (∑ i, ∑ j : Fin (P.subdivision i).count,
            if (P.subdivision i).keep j then 0 else
              radius i * ((P.subdivision i).node j.succ - (P.subdivision i).node j.castSucc)) :=
          subdivision_flux_error P.subdivision f hfi M hpoint
        _ ≤ M * (C * ε) := mul_le_mul_of_nonneg_left P.deleted_length hM.le
        _ = M * C * ε := (mul_assoc _ _ _).symm
    calc
      _ = |((∑ i, ∫ t in start i..stop i, f i t) - retained) + retained| := by
        rw [sub_add_cancel]
      _ ≤ |(∑ i, ∫ t in start i..stop i, f i t) - retained| + |retained| := abs_add_le _ _
      _ ≤ M * C * ε + M * C * ε := add_le_add hdeleted hretained
      _ = (2 * M * C) * ε := by ring
  exact tendsto_nhds_unique tendsto_const_nhds (tendsto_zero_of_linear_bound hε₀ herr)


end SurgeryAssembly

end D12Complex.PiecewiseCircularGreen
