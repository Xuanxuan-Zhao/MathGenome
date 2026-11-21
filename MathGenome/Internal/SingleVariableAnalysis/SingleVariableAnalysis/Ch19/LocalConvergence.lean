import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.LocalConvergence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.Convolution
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.RiemannLebesgueImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
namespace SingleVariableAnalysis
open Riemann Riemann.Improper Fourier
open Filter Set
open scoped Topology
namespace FourierDini
open Specs.SingleVariableAnalysis.Ch19.LocalConvergence

/-- Positivity includes the regular endpoint π. -/
theorem sine_half_pos {t : ℝ} (ht : 0 < t) (hπ : t ≤ Real.pi) :
    0 < Real.sin (t/2) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-- A uniform comparison on the whole positive half-period. -/
theorem sine_quotient_bound (z : ℂ) {t : ℝ} (ht : 0 < t) (hπ : t ≤ Real.pi) :
    ‖z / (Real.sin (t/2) : ℂ)‖ ≤ Real.pi * (‖z‖ / t) := by
  have hs := sine_half_pos ht hπ
  have hb := Real.mul_le_sin (x := t/2) (by positivity) (by linarith)
  have hb' : t ≤ Real.pi * Real.sin (t/2) := by
    have := (div_le_iff₀ Real.pi_pos).mp (show t / Real.pi ≤ Real.sin (t/2) by
      convert hb using 1; ring)
    nlinarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hs ht).mpr
  nlinarith [mul_nonneg (norm_nonneg z) (sub_nonneg.mpr hb')]

/-- The numerator is properly integrable on the closed half-period. -/
theorem symmetricError_integrable (f : ℝ → ℂ) (hf : PeriodicRiemannIntegrable f)
    (x : ℝ) (Lm Lp : ℂ) :
    ComplexIntegrable (symmetricError f x Lm Lp) 0 Real.pi := by
  obtain ⟨h, _⟩ := fourierPartialSum_even_convolution f hf
    (fourierCoeff_integrable f hf.2) 0 x
  simp only [dirichletKernel_zero, mul_one] at h
  have hc : ComplexIntegrable (fun _ : ℝ => -Lp - Lm) 0 Real.pi :=
    complexIntegrable_of_continuousOn Real.pi_pos.le continuousOn_const
  have H := (complex_add_value h hc).choose
  convert H using 1
  funext t
  dsimp [symmetricError]
  ring

/-- On every closed subinterval away from zero, the quotient is proper. -/
theorem sineQuotient_integrable (f : ℝ → ℂ) (hf : PeriodicRiemannIntegrable f)
    (x : ℝ) (Lm Lp : ℂ) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ Real.pi) :
    ComplexIntegrable (sineQuotient f x Lm Lp) u v := by
  have hn := (symmetricError_integrable f hf x Lm Lp).subinterval hu.le huv hv
  have hc : ContinuousOn (fun t : ℝ => (Real.sin (t/2) : ℂ)⁻¹) (Icc u v) := by
    apply ContinuousOn.inv₀
    · exact Complex.continuous_ofReal.comp_continuousOn
        ((Real.continuous_sin.comp (continuous_id.div_const 2)).continuousOn)
    · intro t ht
      exact Complex.ofReal_ne_zero.mpr
        (sine_half_pos (hu.trans_le ht.1) (ht.2.trans hv)).ne'
  exact complex_product hn (complexIntegrable_of_continuousOn huv hc)

theorem sineQuotient_locallyIntegrable (f : ℝ → ℂ) (hf : PeriodicRiemannIntegrable f)
    (x : ℝ) (Lm Lp : ℂ) :
    LocallyIntegrable .complex (sineQuotient f x Lm Lp)
      (0 : WithBot ℝ) (Real.pi : WithTop ℝ) := by
  intro u v hu huv hv
  exact sineQuotient_integrable f hf x Lm Lp
    (WithBot.coe_lt_coe.mp hu) huv (WithTop.coe_lt_coe.mp hv).le

/-- Domination transfers the left Cauchy tails, with proper integrability
kept explicit. No measure integral is involved. -/
theorem leftConverges_real_of_bound {f g : ℝ → ℝ} {a : WithBot ℝ} {b C : ℝ}
    (hf : LeftRegular .real f a b) (hg : LeftRegular .real g a b)
    (hgc : LeftConverges .real g a b) (hC : 0 < C)
    (hbound : ∀ t : ℝ, a < (t : WithBot ℝ) → t ≤ b → ‖f t‖ ≤ C * g t) :
    LeftConverges .real f a b := by
  apply (left_cauchy_criterion .real f a b hf).mpr
  intro ε hε
  obtain ⟨r, hr⟩ := (left_cauchy_criterion .real g a b hg).mp hgc
    (ε / C) (div_pos hε hC)
  refine ⟨r, fun u v huv hvr => ?_⟩
  have hfv := hf.2 u
  have hfi : RealIntegrable f u.val v.val :=
    RealIntegrable.subinterval hfv le_rfl huv.le v.property.2.le
  obtain ⟨hgi, hsmall⟩ := hr u v huv hvr
  obtain ⟨hfn, hnorm, _⟩ := real_norm_estimate f hfi
  obtain ⟨hcg, hval⟩ := real_mul_value hgi C
  have hm := realIntegral_mono _ _ hfn hcg (fun t ht =>
    hbound t (u.property.1.trans_le (WithBot.coe_le_coe.mpr ht.1))
      (ht.2.trans v.property.2.le))
  refine ⟨hfi, hnorm.trans hm |>.trans_lt ?_⟩
  change ‖realIntegral g hgi‖ < ε / C at hsmall
  have hgsmall : realIntegral g hgi < ε / C :=
    (le_abs_self _).trans_lt (by simpa only [Real.norm_eq_abs] using hsmall)
  exact hval.trans_lt ((mul_lt_mul_of_pos_left hgsmall hC).trans_eq (mul_div_cancel₀ ε hC.ne'))

/-- Proper real integrability at a finite right endpoint gives convergence
there. This lemma is used only for the nonsingular end of the quotient. -/
theorem rightConverges_real_of_proper {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hg : RealIntegrable g a b) :
    RightConverges .real g a (b : WithTop ℝ) := by
  have hr : RightRegular .real g a (b : WithTop ℝ) :=
    ⟨WithTop.coe_lt_coe.mpr hab, fun t =>
      hg.subinterval le_rfl t.property.1.le (WithTop.coe_lt_coe.mp t.property.2).le⟩
  apply (right_cauchy_criterion .real g a (b : WithTop ℝ) hr).mpr
  obtain ⟨M, hM⟩ := hg.bounded.abs_bound
  let B := max M 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  intro ε hε
  have hmax : max a (b - ε / B) < b :=
    max_lt hab (by linarith [div_pos hε hB])
  obtain ⟨r, hlow, hrb⟩ := exists_between hmax
  refine ⟨⟨r, (le_max_left _ _).trans_lt hlow, WithTop.coe_lt_coe.mpr hrb⟩,
    fun u v hru huv => ?_⟩
  have hgi := hg.subinterval u.property.1.le huv.le
    (WithTop.coe_lt_coe.mp v.property.2).le
  obtain ⟨hn, hb, _⟩ := real_norm_estimate g hgi
  have hbn : realIntegral _ hn ≤ (v.val - u.val) * B := by
    apply realIntegral_le_mul_bound hn
    intro t ht
    exact (hM t ⟨u.property.1.le.trans ht.1,
      ht.2.trans (WithTop.coe_lt_coe.mp v.property.2).le⟩).trans
      (show M ≤ B by dsimp [B]; linarith [le_max_left M 0])
  refine ⟨hgi, hb.trans hbn |>.trans_lt ?_⟩
  have hu : b - ε / B < u.val := (le_max_right _ _).trans_lt (hlow.trans hru)
  have hv := WithTop.coe_lt_coe.mp v.property.2
  have hlen : v.val - u.val < ε / B := by linarith
  exact (mul_lt_mul_of_pos_right hlen hB).trans_eq (div_mul_cancel₀ ε hB.ne')

/-- Absolute convergence of the quotient follows from Dini's original
hypothesis; neither one-sided limit is needed for this intermediate claim. -/
theorem sineQuotient_absolute (f : ℝ → ℂ) (hf : PeriodicRiemannIntegrable f)
    (x : ℝ) (Lm Lp : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi)
    (hd : Converges .real (diniDensity f x Lm Lp)
      (0 : WithBot ℝ) (δ : WithTop ℝ)) :
    AbsoluteConverges .complex (sineQuotient f x Lm Lp)
      (0 : WithBot ℝ) (Real.pi : WithTop ℝ) := by
  let cδ : RegularPoint (0 : WithBot ℝ) (δ : WithTop ℝ) :=
    ⟨δ/2, WithBot.coe_lt_coe.mpr (by linarith), WithTop.coe_lt_coe.mpr (by linarith)⟩
  let cπ : RegularPoint (0 : WithBot ℝ) (Real.pi : WithTop ℝ) :=
    ⟨δ/2, WithBot.coe_lt_coe.mpr (by linarith), WithTop.coe_lt_coe.mpr (by linarith)⟩
  let q := sineQuotient f x Lm Lp
  have hq := sineQuotient_locallyIntegrable f hf x Lm Lp
  have hqn : LocallyIntegrable .real (fun t => ‖q t‖)
      (0 : WithBot ℝ) (Real.pi : WithTop ℝ) := by
    intro u v hu huv hv
    exact ComplexIntegrable.norm (hq u v hu huv hv)
  obtain ⟨_, l, r, hl, hr, _⟩ :=
    (hasIntegral_at_every_split .real _ _ _ cδ _).mp hd.choose_spec
  have hg : LeftRegular .real (diniDensity f x Lm Lp) (0 : WithBot ℝ) (δ/2) := hl.choose
  have hleftreg : LeftRegular .real (fun t => ‖q t‖) (0 : WithBot ℝ) (δ/2) := by
    refine ⟨WithBot.coe_lt_coe.mpr (by linarith), fun t => ?_⟩
    exact (sineQuotient_integrable f hf x Lm Lp
      (WithBot.coe_lt_coe.mp t.property.1) t.property.2.le (by linarith)).norm
  have hleft : LeftConverges .real (fun t => ‖q t‖) (0 : WithBot ℝ) (δ/2) := by
    apply leftConverges_real_of_bound hleftreg hg ⟨l, hl⟩ Real.pi_pos
    intro t ht htc
    change ‖‖sineQuotient f x Lm Lp t‖‖ ≤ Real.pi * diniDensity f x Lm Lp t
    rw [norm_norm]
    exact sine_quotient_bound _ (WithBot.coe_lt_coe.mp ht) (by linarith)
  have hproper : RealIntegrable (fun t => ‖q t‖) (δ/2) Real.pi :=
    (sineQuotient_integrable f hf x Lm Lp (by linarith) (by linarith) le_rfl).norm
  have hright := rightConverges_real_of_proper (by linarith : δ/2 < Real.pi) hproper
  obtain ⟨l, hl⟩ := hleft
  obtain ⟨r, hr⟩ := hright
  exact ⟨l+r, hqn, cπ, l, r, hl, hr, rfl⟩

/-- The normalized integral of the even kernel on a half-period is 1/2. -/
theorem half_kernel_normalization (N : ℕ)
    (h : ComplexIntegrable (dirichletKernel N) 0 Real.pi) :
    ((1/(2*Real.pi) : ℝ) : ℂ) * complexIntegral _ h = 1/2 := by
  let hf := dirichletKernel_integrable N
  obtain ⟨hh, he⟩ := complexIntegral_fold_pi hf
  obtain ⟨h2, he2⟩ := complex_mul_value h 2
  have hfun : (fun t => dirichletKernel N (-t) + dirichletKernel N t) =
      (fun t => (2 : ℂ) * dirichletKernel N t) := by
    funext t
    have hev : dirichletKernel N (-t) = dirichletKernel N t := dirichletKernel_even N t
    rw [hev]
    ring
  have hi : complexIntegral _ hh = complexIntegral _ h2 := by
    congr 1
  rw [hi, he2] at he
  have hm := dirichletKernel_integral_mean N hf
  change ((1/(2*Real.pi) : ℝ) : ℂ) * complexIntegral _ hf = 1 at hm
  rw [← he] at hm
  linear_combination (norm := ring_nf) (1/2 : ℂ) * hm

/-- Subtraction of the constants in the even convolution is a proper
identity, so the arbitrary assigned value at t=0 is retained here. -/
theorem partialSum_error_integral (f : ℝ → ℂ) (hf : PeriodicRiemannIntegrable f)
    (h : ∀ n : ℤ, ComplexIntegrable (fun y => f y * fourierMode (-n) y)
      (-Real.pi) Real.pi) (x : ℝ) (Lm Lp : ℂ) (N : ℕ) :
    ∃ he : ComplexIntegrable
      (fun t => symmetricError f x Lm Lp t * dirichletKernel N t) 0 Real.pi,
      fourierPartialSum f h N x - (Lm+Lp)/2 =
        ((1/(2*Real.pi) : ℝ) : ℂ) * complexIntegral _ he := by
  obtain ⟨hh, hhv⟩ := fourierPartialSum_even_convolution f hf h N x
  have hk : ComplexIntegrable (dirichletKernel N) 0 Real.pi :=
    complexIntegrable_of_continuousOn Real.pi_pos.le (dirichletKernel_continuous N).continuousOn
  obtain ⟨hc, hcv⟩ := complex_mul_value hk (-(Lp+Lm))
  obtain ⟨hs, hsv⟩ := complex_add_value hh hc
  have hfun : (fun t => (f (x+t)+f (x-t))*dirichletKernel N t +
      -(Lp+Lm)*dirichletKernel N t) =
      (fun t => symmetricError f x Lm Lp t * dirichletKernel N t) := by
    funext t
    dsimp [symmetricError]
    ring
  let he := hfun ▸ hs
  refine ⟨he, ?_⟩
  have hi : complexIntegral _ he = complexIntegral _ hs := by congr 1; exact hfun.symm
  change fourierPartialSum f h N x =
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ hh at hhv
  rw [hi, hsv, hcv, hhv]
  have hn := half_kernel_normalization N hk
  linear_combination (norm := ring_nf) (Lm+Lp) * hn

/-- The sine quotient equals the nonsingular error integrand at every
positive point, including π. -/
theorem quotient_sine_eq_error (f : ℝ → ℂ) (x : ℝ) (Lm Lp : ℂ)
    (N : ℕ) {t : ℝ} (ht : 0 < t) (hπ : t ≤ Real.pi) :
    sineQuotient f x Lm Lp t * (Real.sin (((N : ℝ)+1/2)*t) : ℂ) =
      symmetricError f x Lm Lp t * dirichletKernel N t := by
  rw [← dirichletKernel_sine_mul]
  dsimp [sineQuotient]
  have hn : (Real.sin (t/2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sine_half_pos ht hπ).ne'
  field_simp

/-- On regular cutoffs, the source's strict left-endpoint limit agrees with
an order-filter limit. -/
theorem leftHasIntegral_iff_tendsto {f : ℝ → ℂ} {a : WithBot ℝ} {b : ℝ}
    (hf : LeftRegular .complex f a b) (L : ℂ) :
    LeftHasIntegral .complex f a b L ↔
      Tendsto (LeftTruncation .complex f a b hf) atBot (𝓝 L) := by
  letI : Nonempty (LeftIndex a b) := left_index_nonempty hf
  constructor
  · rintro ⟨hf', hL⟩
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨r, hr⟩ := hL ε hε
    obtain ⟨s, hsr, _⟩ := left_earlier r r
    filter_upwards [eventually_le_atBot s] with t ht
    exact hr t (lt_of_le_of_lt ht hsr)
  · intro hL
    refine ⟨hf, fun ε hε => ?_⟩
    obtain ⟨r, hr⟩ := eventually_atBot.mp (Metric.tendsto_nhds.mp hL ε hε)
    exact ⟨r, fun t ht => hr t ht.le⟩

theorem rightHasIntegral_iff_tendsto {f : ℝ → ℂ} {a : ℝ} {b : WithTop ℝ}
    (hf : RightRegular .complex f a b) (L : ℂ) :
    RightHasIntegral .complex f a b L ↔
      Tendsto (RightTruncation .complex f a b hf) atTop (𝓝 L) := by
  letI : Nonempty (RightIndex a b) := right_index_nonempty hf
  constructor
  · rintro ⟨hf', hL⟩
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨r, hr⟩ := hL ε hε
    obtain ⟨s, hrs, _⟩ := right_later r r
    filter_upwards [eventually_ge_atTop s] with t ht
    exact hr t (lt_of_lt_of_le hrs ht)
  · intro hL
    refine ⟨hf, fun ε hε => ?_⟩
    obtain ⟨r, hr⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hL ε hε)
    exact ⟨r, fun t ht => hr t ht.le⟩

/-- A convenient finite proper linear combination, with its actual value. -/
theorem complex_linear_value {f g : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexIntegrable f a b) (hg : ComplexIntegrable g a b) (α β : ℂ) :
    ∃ h : ComplexIntegrable (fun t => α*f t + β*g t) a b,
      complexIntegral _ h = α*complexIntegral _ hf + β*complexIntegral _ hg := by
  obtain ⟨hα, heα⟩ := complex_mul_value hf α
  obtain ⟨hβ, heβ⟩ := complex_mul_value hg β
  obtain ⟨h, he⟩ := complex_add_value hα hβ
  exact ⟨h, by rw [he, heα, heβ]⟩

theorem leftHasIntegral_linear {f g : ℝ → ℂ} {a : WithBot ℝ} {b : ℝ}
    {L M : ℂ} (hf : LeftHasIntegral .complex f a b L)
    (hg : LeftHasIntegral .complex g a b M) (α β : ℂ) :
    LeftHasIntegral .complex (fun t => α*f t + β*g t) a b (α*L + β*M) := by
  let hreg : LeftRegular .complex (fun t => α*f t + β*g t) a b :=
    ⟨hf.choose.1, fun t => (complex_linear_value (hf.choose.2 t) (hg.choose.2 t) α β).choose⟩
  apply (leftHasIntegral_iff_tendsto hreg _).mpr
  have hl : Tendsto (fun t : LeftIndex a b => complexIntegral f (hf.choose.2 t)) atBot (𝓝 L) :=
    (leftHasIntegral_iff_tendsto hf.choose L).mp hf
  have hm : Tendsto (fun t : LeftIndex a b => complexIntegral g (hg.choose.2 t)) atBot (𝓝 M) :=
    (leftHasIntegral_iff_tendsto hg.choose M).mp hg
  apply ((hl.const_mul α).add (hm.const_mul β)).congr
  intro t
  exact (complex_linear_value (hf.choose.2 t) (hg.choose.2 t) α β).choose_spec.symm

theorem rightHasIntegral_linear {f g : ℝ → ℂ} {a : ℝ} {b : WithTop ℝ}
    {L M : ℂ} (hf : RightHasIntegral .complex f a b L)
    (hg : RightHasIntegral .complex g a b M) (α β : ℂ) :
    RightHasIntegral .complex (fun t => α*f t + β*g t) a b (α*L + β*M) := by
  let hreg : RightRegular .complex (fun t => α*f t + β*g t) a b :=
    ⟨hf.choose.1, fun t => (complex_linear_value (hf.choose.2 t) (hg.choose.2 t) α β).choose⟩
  apply (rightHasIntegral_iff_tendsto hreg _).mpr
  have hl : Tendsto (fun t : RightIndex a b => complexIntegral f (hf.choose.2 t)) atTop (𝓝 L) :=
    (rightHasIntegral_iff_tendsto hf.choose L).mp hf
  have hm : Tendsto (fun t : RightIndex a b => complexIntegral g (hg.choose.2 t)) atTop (𝓝 M) :=
    (rightHasIntegral_iff_tendsto hg.choose M).mp hg
  apply ((hl.const_mul α).add (hm.const_mul β)).congr
  intro t
  exact (complex_linear_value (hf.choose.2 t) (hg.choose.2 t) α β).choose_spec.symm

/-- Linearity respects both independent singular endpoint limits. -/
theorem hasIntegral_linear {f g : ℝ → ℂ} {a : WithBot ℝ} {b : WithTop ℝ}
    {L M : ℂ} (hf : HasIntegral .complex f a b L)
    (hg : HasIntegral .complex g a b M) (α β : ℂ) :
    HasIntegral .complex (fun t => α*f t + β*g t) a b (α*L + β*M) := by
  obtain ⟨c, fc⟩ := hf.2
  obtain ⟨_, gc⟩ := (hasIntegral_at_every_split .complex g a b c M).mp hg
  obtain ⟨l, r, hl, hr, hL⟩ := fc
  obtain ⟨l', r', hl', hr', hM⟩ := gc
  change ℂ at l r l' r'
  refine ⟨fun u v hu huv hv =>
    (complex_linear_value (hf.1 u v hu huv hv) (hg.1 u v hu huv hv) α β).choose,
    c, α*l + β*l', α*r + β*r', leftHasIntegral_linear hl hl' α β,
    rightHasIntegral_linear hr hr' α β, ?_⟩
  change L = l+r at hL
  change M = l'+r' at hM
  change α*L + β*M = (α*l+β*l') + (α*r+β*r')
  rw [hL, hM]
  ring

/-- A proper integral has the elementary uniform length bound. -/
theorem complexIntegral_norm_le_length_mul {f : ℝ → ℂ} {a b B : ℝ}
    (hf : ComplexIntegrable f a b) (hb : ∀ t ∈ Icc a b, ‖f t‖ ≤ B) :
    ‖complexIntegral f hf‖ ≤ (b-a)*B := by
  obtain ⟨hn, hle, _⟩ := complex_norm_estimate f hf
  exact hle.trans (realIntegral_le_mul_bound hn hb)

/-- The left improper limit of a proper integral is its proper value. -/
theorem complex_proper_left_hasIntegral {f : ℝ → ℂ} {a b : ℝ}
    (hab : a < b) (hf : ComplexIntegrable f a b) :
    LeftHasIntegral .complex f (a : WithBot ℝ) b (complexIntegral f hf) := by
  let hreg : LeftRegular .complex f (a : WithBot ℝ) b :=
    ⟨WithBot.coe_lt_coe.mpr hab, fun t => hf.subinterval
      (WithBot.coe_lt_coe.mp t.property.1).le t.property.2.le le_rfl⟩
  obtain ⟨M, hM⟩ := hf.norm_bound
  let B := max M 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨hreg, fun ε hε => ?_⟩
  have hm : a < min b (a + ε/B) := lt_min hab (by linarith [div_pos hε hB])
  obtain ⟨r, har, hr⟩ := exists_between hm
  refine ⟨⟨r, WithBot.coe_lt_coe.mpr har, hr.trans_le (min_le_left _ _)⟩,
    fun t htr => ?_⟩
  have hat : a ≤ t.val := (WithBot.coe_lt_coe.mp t.property.1).le
  let hfront := hf.subinterval le_rfl hat t.property.2.le
  have hsplit := scalar_integral_split .complex f hat t.property.2.le hf hfront (hreg.2 t)
  change complexIntegral f hf = complexIntegral f hfront + complexIntegral f (hreg.2 t) at hsplit
  have hdist : dist (LeftTruncation .complex f (a : WithBot ℝ) b hreg t)
      (complexIntegral f hf) = ‖complexIntegral f hfront‖ := by
    change dist (complexIntegral f (hreg.2 t)) (complexIntegral f hf) = _
    rw [dist_eq_norm]
    rw [hsplit, show complexIntegral f (hreg.2 t) -
      (complexIntegral f hfront + complexIntegral f (hreg.2 t)) =
      -complexIntegral f hfront by abel, norm_neg]
  rw [hdist]
  have hbnd := complexIntegral_norm_le_length_mul hfront (B := B) (fun u hu =>
    (hM u ⟨hu.1, hu.2.trans t.property.2.le⟩).trans
      (show M ≤ B by dsimp [B]; linarith [le_max_left M 0]))
  apply hbnd.trans_lt
  have ht : t.val - a < ε/B := by
    have hrε := hr.trans_le (min_le_right _ _)
    dsimp at htr
    linarith
  exact (mul_lt_mul_of_pos_right ht hB).trans_eq (div_mul_cancel₀ ε hB.ne')

/-- The right improper limit also retains the proper value. -/
theorem complex_proper_right_hasIntegral {f : ℝ → ℂ} {a b : ℝ}
    (hab : a < b) (hf : ComplexIntegrable f a b) :
    RightHasIntegral .complex f a (b : WithTop ℝ) (complexIntegral f hf) := by
  let hreg : RightRegular .complex f a (b : WithTop ℝ) :=
    ⟨WithTop.coe_lt_coe.mpr hab, fun t => hf.subinterval le_rfl
      t.property.1.le (WithTop.coe_lt_coe.mp t.property.2).le⟩
  obtain ⟨M, hM⟩ := hf.norm_bound
  let B := max M 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨hreg, fun ε hε => ?_⟩
  have hm : max a (b - ε/B) < b := max_lt hab (by linarith [div_pos hε hB])
  obtain ⟨r, hr, hrb⟩ := exists_between hm
  refine ⟨⟨r, (le_max_left _ _).trans_lt hr, WithTop.coe_lt_coe.mpr hrb⟩,
    fun t hrt => ?_⟩
  have htb : t.val ≤ b := (WithTop.coe_lt_coe.mp t.property.2).le
  let htail := hf.subinterval t.property.1.le htb le_rfl
  have hsplit := scalar_integral_split .complex f t.property.1.le htb hf (hreg.2 t) htail
  change complexIntegral f hf = complexIntegral f (hreg.2 t) + complexIntegral f htail at hsplit
  have hdist : dist (RightTruncation .complex f a (b : WithTop ℝ) hreg t)
      (complexIntegral f hf) = ‖complexIntegral f htail‖ := by
    change dist (complexIntegral f (hreg.2 t)) (complexIntegral f hf) = _
    rw [dist_eq_norm]
    rw [hsplit, show complexIntegral f (hreg.2 t) -
      (complexIntegral f (hreg.2 t) + complexIntegral f htail) =
      -complexIntegral f htail by abel, norm_neg]
  rw [hdist]
  have hbnd := complexIntegral_norm_le_length_mul htail (B := B) (fun u hu =>
    (hM u ⟨t.property.1.le.trans hu.1, hu.2⟩).trans
      (show M ≤ B by dsimp [B]; linarith [le_max_left M 0]))
  apply hbnd.trans_lt
  have ht : b - t.val < ε/B := by
    have hrε := (le_max_right _ _).trans_lt hr
    dsimp at hrt
    linarith
  exact (mul_lt_mul_of_pos_right ht hB).trans_eq (div_mul_cancel₀ ε hB.ne')

/-- Proper and independently truncated improper values agree. -/
theorem complex_proper_hasIntegral {f : ℝ → ℂ} {a b : ℝ}
    (hab : a < b) (hf : ComplexIntegrable f a b) :
    HasIntegral .complex f (a : WithBot ℝ) (b : WithTop ℝ) (complexIntegral f hf) := by
  let c : RegularPoint (a : WithBot ℝ) (b : WithTop ℝ) :=
    ⟨(a+b)/2, WithBot.coe_lt_coe.mpr (by linarith), WithTop.coe_lt_coe.mpr (by linarith)⟩
  have hac : a < c.val := WithBot.coe_lt_coe.mp c.property.1
  have hcb : c.val < b := WithTop.coe_lt_coe.mp c.property.2
  let hl := hf.subinterval le_rfl hac.le hcb.le
  let hr := hf.subinterval hac.le hcb.le le_rfl
  refine ⟨fun u v hu huv hv => hf.subinterval (WithBot.coe_lt_coe.mp hu).le huv
    (WithTop.coe_lt_coe.mp hv).le, c, complexIntegral f hl, complexIntegral f hr,
    complex_proper_left_hasIntegral hac hl, complex_proper_right_hasIntegral hcb hr, ?_⟩
  exact scalar_integral_split .complex f hac.le hcb.le hf hl hr

/-- On an open interval, pointwise agreement transfers a known improper
value. Both local proper integrability predicates remain explicit. -/
theorem hasIntegral_congr_open {f g : ℝ → ℂ} {a : WithBot ℝ} {b : WithTop ℝ}
    {L : ℂ} (hf : HasIntegral .complex f a b L)
    (hg : LocallyIntegrable .complex g a b)
    (he : ∀ t : ℝ, a < (t : WithBot ℝ) → (t : WithTop ℝ) < b → f t = g t) :
    HasIntegral .complex g a b L := by
  obtain ⟨c, l, r, hl, hr, hL⟩ := hf.2
  change ℂ at l r
  let hgl := local_left_regular .complex g hg c
  let hgr := local_right_regular .complex g hg c
  have hleft : LeftHasIntegral .complex g a c.val l := by
    apply (leftHasIntegral_iff_tendsto hgl l).mpr
    have hh : Tendsto (fun t : LeftIndex a c.val => complexIntegral f (hl.choose.2 t))
        atBot (𝓝 l) := (leftHasIntegral_iff_tendsto hl.choose l).mp hl
    apply hh.congr
    intro t
    exact complexIntegral_eq_of_eqOn_open (hl.choose.2 t) (hgl.2 t)
      (fun u hu => he u (t.property.1.trans (WithBot.coe_lt_coe.mpr hu.1))
        ((WithTop.coe_lt_coe.mpr hu.2).trans c.property.2))
  have hright : RightHasIntegral .complex g c.val b r := by
    apply (rightHasIntegral_iff_tendsto hgr r).mpr
    have hh : Tendsto (fun t : RightIndex c.val b => complexIntegral f (hr.choose.2 t))
        atTop (𝓝 r) := (rightHasIntegral_iff_tendsto hr.choose r).mp hr
    apply hh.congr
    intro t
    exact complexIntegral_eq_of_eqOn_open (hr.choose.2 t) (hgr.2 t)
      (fun u hu => he u (c.property.1.trans (WithBot.coe_lt_coe.mpr hu.1))
        ((WithTop.coe_lt_coe.mpr hu.2).trans t.property.2))
  exact ⟨hg, c, l, r, hleft, hright, hL⟩

/-- The complex specialization with its canonical scalar result type. -/
def complexImproperIntegral (f : ℝ → ℂ) (a : WithBot ℝ) (b : WithTop ℝ)
    (h : Converges .complex f a b) : ℂ := Riemann.Improper.integral .complex f a b h

/-- Euler's identity expresses the sine as two real frequencies. -/
theorem sine_exponential_identity (z : ℂ) (lam t : ℝ) :
    z * (Real.sin (lam*t) : ℂ) =
      (1/(2*Complex.I)) * (z * Complex.exp (Complex.I*(lam : ℂ)*(t : ℂ))) +
      (-1/(2*Complex.I)) * (z * Complex.exp (Complex.I*((-lam : ℝ) : ℂ)*(t : ℂ))) := by
  rw [show Complex.I*(lam : ℂ)*(t : ℂ) = ((lam*t : ℝ) : ℂ)*Complex.I by push_cast; ring,
    show Complex.I*((-lam : ℝ) : ℂ)*(t : ℂ) = ((-(lam*t) : ℝ) : ℂ)*Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  field_simp
  ring

/-- Sine-weighted improper integrals have the values dictated by the two
exponential integrals; a proper representative may differ at the endpoints. -/
theorem sine_integral_eq_of_proper {q g : ℝ → ℂ} {a b lam : ℝ}
    (hab : a < b) (hq : LocallyIntegrable .complex q (a : WithBot ℝ) (b : WithTop ℝ))
    (hg : ComplexIntegrable g a b)
    (he : ∀ t ∈ Ioo a b, g t = q t * (Real.sin (lam*t) : ℂ))
    (H : ∀ lam : ℝ, Converges .complex
      (fun t => q t * Complex.exp (Complex.I*(lam : ℂ)*(t : ℂ)))
      (a : WithBot ℝ) (b : WithTop ℝ)) :
    complexIntegral g hg =
      (1/(2*Complex.I)) * FourierDini.complexImproperIntegral _ _ _ (H lam) +
      (-1/(2*Complex.I)) * FourierDini.complexImproperIntegral _ _ _ (H (-lam)) := by
  let s := fun t => q t * (Real.sin (lam*t) : ℂ)
  have hs : LocallyIntegrable .complex s (a : WithBot ℝ) (b : WithTop ℝ) := by
    intro u v hu huv hv
    apply complex_product (hq u v hu huv hv)
    apply complexIntegrable_of_continuousOn huv
    exact Complex.continuous_ofReal.comp_continuousOn
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn)
  have hproper := hasIntegral_congr_open (complex_proper_hasIntegral hab hg) hs
    (fun t ht ht' => he t ⟨WithBot.coe_lt_coe.mp ht, WithTop.coe_lt_coe.mp ht'⟩)
  have hlinear := hasIntegral_linear
    (integral_hasValue .complex _ _ _ (H lam))
    (integral_hasValue .complex _ _ _ (H (-lam))) (1/(2*Complex.I)) (-1/(2*Complex.I))
  have hfun : (fun t => (1/(2*Complex.I)) * (q t * Complex.exp (Complex.I*(lam : ℂ)*(t : ℂ))) +
      (-1/(2*Complex.I)) * (q t * Complex.exp (Complex.I*((-lam : ℝ) : ℂ)*(t : ℂ)))) = s := by
    funext t
    exact (sine_exponential_identity (q t) lam t).symm
  rw [hfun] at hlinear
  have hc : Converges .complex s (a : WithBot ℝ) (b : WithTop ℝ) := ⟨_, hproper⟩
  exact (integral_eq .complex s _ _ hc _ hproper).symm.trans
    (integral_eq .complex s _ _ hc _ hlinear)

/-- Riemann–Lebesgue decay along both half-integer frequency sequences. -/
theorem half_integer_decay {q : ℝ → ℂ}
    (hq : LocallyIntegrable .complex q (0 : WithBot ℝ) (Real.pi : WithTop ℝ))
    (ha : AbsoluteConverges .complex q (0 : WithBot ℝ) (Real.pi : WithTop ℝ)) :
    ∃ H : ∀ lam : ℝ, Converges .complex
      (fun t => q t * Complex.exp (Complex.I*(lam : ℂ)*(t : ℂ)))
      (0 : WithBot ℝ) (Real.pi : WithTop ℝ),
      Tendsto (fun N : ℕ => FourierDini.complexImproperIntegral _ _ _ (H ((N : ℝ)+1/2)))
        atTop (𝓝 (0 : ℂ)) ∧
      Tendsto (fun N : ℕ => FourierDini.complexImproperIntegral _ _ _ (H (-((N : ℝ)+1/2))))
        atTop (𝓝 (0 : ℂ)) := by
  obtain ⟨H, _, hdec⟩ := riemann_lebesgue_improper_complex q 0 Real.pi hq ha
  refine ⟨H, ?_, ?_⟩
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨R, _, hR⟩ := hdec ε hε
    obtain ⟨K, hK⟩ := exists_nat_gt R
    refine ⟨K, fun N hN => ?_⟩
    rw [dist_zero_right]
    apply hR
    rw [abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)+1/2)]
    have hKN : (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨R, _, hR⟩ := hdec ε hε
    obtain ⟨K, hK⟩ := exists_nat_gt R
    refine ⟨K, fun N hN => ?_⟩
    rw [dist_zero_right]
    apply hR
    rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)+1/2)]
    have hKN : (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith

end FourierDini
open Specs.SingleVariableAnalysis.Ch19.LocalConvergence

/-- Dini's local condition supplies the full quotient integrability needed
by the oscillatory lemma. -/
theorem fourier_dini_quotient_integrability : quotientIntegrability := by
  intro f hf x Lm Lp δ hδ hδπ _hleft _hright hd
  exact ⟨FourierDini.sineQuotient_locallyIntegrable f hf x Lm Lp,
    FourierDini.sineQuotient_absolute f hf x Lm Lp hδ hδπ hd⟩

/-- Dini convergence, with no constraint on the value assigned at the point. -/
theorem fourier_dini_local_convergence : complexLocalConvergence := by
  intro f hf h x Lm Lp δ hδ hδπ hleft hright hd
  obtain ⟨hq, ha⟩ := fourier_dini_quotient_integrability f hf x Lm Lp δ hδ hδπ hleft hright hd
  obtain ⟨H, hplus, hminus⟩ := FourierDini.half_integer_decay hq ha
  have herror : ∀ N : ℕ,
      fourierPartialSum f h N x - (Lm+Lp)/2 =
        ((1/(2*Real.pi) : ℝ) : ℂ) *
          ((1/(2*Complex.I)) * FourierDini.complexImproperIntegral _ _ _ (H ((N : ℝ)+1/2)) +
          (-1/(2*Complex.I)) * FourierDini.complexImproperIntegral _ _ _ (H (-((N : ℝ)+1/2)))) := by
    intro N
    obtain ⟨he, hev⟩ := FourierDini.partialSum_error_integral f hf h x Lm Lp N
    rw [hev]
    congr 1
    exact FourierDini.sine_integral_eq_of_proper Real.pi_pos hq he
      (fun t ht => (FourierDini.quotient_sine_eq_error f x Lm Lp N ht.1 ht.2.le).symm) H
  have hzero := ((hplus.const_mul (1/(2*Complex.I))).add
    (hminus.const_mul (-1/(2*Complex.I)))).const_mul ((1/(2*Real.pi) : ℝ) : ℂ)
  have hz : Tendsto (fun N : ℕ => fourierPartialSum f h N x - (Lm+Lp)/2)
      atTop (𝓝 (0 : ℂ)) := by
    simpa only [mul_zero, add_zero] using hzero.congr (fun N => (herror N).symm)
  have hfinal := hz.add_const ((Lm+Lp)/2)
  simpa only [sub_add_cancel, zero_add] using hfinal

/-- The real scalar statement follows through the shared complex embedding. -/
theorem fourier_dini_real_local_convergence : realLocalConvergence := by
  intro f hf h x Lm Lp δ hδ hδπ hleft hright hd
  have hfc : PeriodicRiemannIntegrable (fun y => (f y : ℂ)) :=
    ⟨hf.1.comp Complex.ofReal, fourierRealEmbedding_integrable f hf.2⟩
  have hlc : Tendsto (fun y => (f y : ℂ)) (𝓝[<] x) (𝓝 (Lm : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hleft
  have hrc : Tendsto (fun y => (f y : ℂ)) (𝓝[>] x) (𝓝 (Lp : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hright
  have hdensity : diniDensity (fun y => (f y : ℂ)) x (Lm : ℂ) (Lp : ℂ) =
      (fun t => |f (x+t)+f (x-t)-Lp-Lm| / t) := by
    funext t
    simp only [diniDensity, symmetricError, ← Complex.ofReal_add, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  have hdc : Converges .real (diniDensity (fun y => (f y : ℂ)) x (Lm : ℂ) (Lp : ℂ))
      (0 : WithBot ℝ) (δ : WithTop ℝ) := by rw [hdensity]; exact hd
  convert fourier_dini_local_convergence _ hfc h x (Lm : ℂ) (Lp : ℂ) δ hδ hδπ hlc hrc hdc using 1
  norm_cast


end SingleVariableAnalysis
