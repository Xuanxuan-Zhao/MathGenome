import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.Jordan
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.JordanLocalEstimate
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.RiemannLebesgue
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.Convolution
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.BvRiemann
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace SingleVariableAnalysis.Fourier
open Set Filter Riemann BV
open scoped Topology

/-- Increasing changes of real variable preserve finite variation. -/
theorem boundedVariation_comp_monotone {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {s t : Set ℝ} (hf : BoundedVariationOn f s)
    (φ : ℝ → ℝ) (hφ : MonotoneOn φ t) (hm : MapsTo φ t s) :
    BoundedVariationOn (fun x => f (φ x)) t :=
  ne_top_of_le_ne_top hf (eVariationOn.comp_le_of_monotoneOn f φ hφ hm)

/-- Decreasing changes of real variable preserve finite variation. -/
theorem boundedVariation_comp_antitone {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {s t : Set ℝ} (hf : BoundedVariationOn f s)
    (φ : ℝ → ℝ) (hφ : AntitoneOn φ t) (hm : MapsTo φ t s) :
    BoundedVariationOn (fun x => f (φ x)) t :=
  ne_top_of_le_ne_top hf (eVariationOn.comp_le_of_antitoneOn f φ hφ hm)

/-- Gluing closed adjacent intervals counts their common assigned value. -/
theorem boundedVariation_join {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hl : BoundedVariationOn f (Icc a c)) (hr : BoundedVariationOn f (Icc c b)) :
    BoundedVariationOn f (Icc a b) := by
  have he := eVariationOn.Icc_add_Icc f (s := univ) hac hcb (mem_univ c)
  simp only [univ_inter] at he
  change eVariationOn f (Icc a b) ≠ ⊤
  rw [← he]
  exact ENNReal.add_ne_top.mpr ⟨hl, hr⟩

/-- Transport by an actual period, with no endpoint normalization. -/
theorem boundedVariation_translate_period {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {a b c : ℝ} (hp : Function.Periodic f c)
    (hf : BoundedVariationOn f (Icc a b)) :
    BoundedVariationOn f (Icc (a+c) (b+c)) := by
  have h := boundedVariation_comp_monotone (t := Icc (a+c) (b+c)) hf (fun t => t-c)
    (by intro x hx y hy hxy; dsimp; linarith)
    (by intro t ht; constructor <;> dsimp <;> linarith [ht.1, ht.2])
  have he : (fun t => f (t-c)) = f := funext hp.sub_eq
  simpa only [he] using h

/-- A periodic BV function is BV on a period starting at any real origin. -/
theorem boundedVariation_period {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {T b : ℝ} (hT : 0 < T) (hp : Function.Periodic f T)
    (hf : BoundedVariationOn f (Icc b (b+T))) (a : ℝ) :
    BoundedVariationOn f (Icc a (a+T)) := by
  let n : ℤ := ⌊(a-b)/T⌋
  let r := a - (n : ℝ)*T
  have hr : r ∈ Icc b (b+T) := by
    have h0 := Int.sub_floor_div_mul_nonneg (a-b) hT
    have h1 := Int.sub_floor_div_mul_lt (a-b) hT
    dsimp [r, n]
    constructor <;> linarith
  have hl := hf.mono (Icc_subset_Icc hr.1 le_rfl)
  have hh := hf.mono (Icc_subset_Icc le_rfl hr.2)
  have hs := boundedVariation_translate_period hp hh
  have hnear := boundedVariation_join hr.2 (by linarith [hr.1]) hl hs
  have hn : Function.Periodic f ((n : ℝ)*T) := by
    simpa only [zsmul_eq_mul] using hp.zsmul n
  have hg := boundedVariation_translate_period hn hnear
  have ha : r + (n : ℝ)*T = a := by dsimp [r]; ring
  have hb : r + T + (n : ℝ)*T = a+T := by dsimp [r]; ring
  simpa only [ha, hb] using hg

/-- Both finite sided limits exist at every point, including seams. -/
theorem periodic_bv_sided_limits {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℝ → E} {T a : ℝ} (hT : 0 < T) (hp : Function.Periodic f T)
    (hf : HasBoundedVariation f a (a+T)) (x : ℝ) :
    ∃ Lminus Lplus : E,
      Tendsto f (𝓝[Iio x] x) (𝓝 Lminus) ∧
      Tendsto f (𝓝[Ioi x] x) (𝓝 Lplus) := by
  have hB := boundedVariation_period hT hp ((boundedVariation_iff f (by linarith)).mp hf)
    (x-T/2)
  have hn : Icc (x-T/2) (x-T/2+T) ∈ 𝓝 x := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨Lm, hm⟩ := hB.exists_tendsto_left x
  obtain ⟨Lp, hp'⟩ := hB.exists_tendsto_right x
  have he (s : Set ℝ) : 𝓝[Icc (x-T/2) (x-T/2+T) ∩ s] x = 𝓝[s] x :=
    nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hn)
  rw [he] at hm hp'
  exact ⟨Lm, Lp, hm, hp'⟩

/-- Centering at a right limit and resetting only the endpoint preserves BV.
The monotone components, rather than a complex order, justify the reset. -/
theorem rightRecenter_bv {g : ℝ → ℝ} {b L : ℝ} (hb : 0 < b)
    (hg : HasBoundedVariation g 0 b) (hL : RightRelativeLimit g (Icc 0 b) 0 L) :
    HasBoundedVariation (rightRecenter g L) 0 b ∧
    rightRecenter g L 0 = 0 ∧
    RightRelativeLimit (rightRecenter g L) (Icc 0 b) 0 0 := by
  obtain ⟨p, q, hp, hq, heq⟩ := (jordan_iff g hb.le).mp hg
  obtain ⟨Lp, hLp⟩ := monotoneOn_closedInterval_right_limit hp
    (show 0 ∈ Ico 0 b from ⟨le_rfl, hb⟩)
  obtain ⟨Lq, hLq⟩ := monotoneOn_closedInterval_right_limit hq
    (show 0 ∈ Ico 0 b from ⟨le_rfl, hb⟩)
  have := rightIntervalFilter_neBot hb
  have hdiff : Tendsto g (𝓝[Icc 0 b ∩ Ioi 0] 0) (𝓝 (Lp-Lq)) := by
    apply (((rightRelativeLimit_filter_iff _ _ _ _).mp hLp).2.sub
      ((rightRelativeLimit_filter_iff _ _ _ _).mp hLq).2).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (heq t ht.1).symm
  have hval : Lp-Lq = L := tendsto_nhds_unique hdiff
    ((rightRelativeLimit_filter_iff _ _ _ _).mp hL).2
  obtain ⟨hpu, _, hpl⟩ := rightRecenter_properties hb hp hLp
  obtain ⟨hqv, _, hql⟩ := rightRecenter_properties hb hq hLq
  have he : ∀ t ∈ Icc 0 b, rightRecenter g L t =
      rightRecenter p Lp t - rightRecenter q Lq t := by
    intro t ht
    by_cases hz : t = 0
    · simp [rightRecenter, hz]
    · simp only [rightRecenter, ite_eq_right hz]
      rw [heq t ht, ← hval]
      ring
  refine ⟨(jordan_iff _ hb.le).mpr ⟨_, _, hpu, hqv, he⟩,
    by simp [rightRecenter], ?_⟩
  apply (rightRelativeLimit_filter_iff _ _ _ _).mpr
  refine ⟨((rightRelativeLimit_filter_iff _ _ _ _).mp hL).1, ?_⟩
  have hT := ((rightRelativeLimit_filter_iff _ _ _ _).mp hL).2.sub
    (tendsto_const_nhds (x := L))
  have hT' : Tendsto (fun t => g t-L) (𝓝[Icc 0 b ∩ Ioi 0] 0) (𝓝 0) := by
    simpa only [sub_self] using hT
  apply hT'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp [rightRecenter, ne_of_gt (show 0 < t from ht.2)]

/-- The finite kernel times any properly integrable real weight is integrable. -/
theorem real_kernel_weight_integrable {g : ℝ → ℝ} {a b : ℝ}
    (hg : RealIntegrable g a b) (N : ℕ) :
    RealIntegrable (fun t => g t * (dirichletKernel N t).re) a b :=
  real_product hg (realIntegrable_of_continuousOn hg.ordered
    ((Complex.continuous_re.comp (dirichletKernel_continuous N)).continuousOn))

/-- On a closed interval bounded away from zero the Dirichlet kernel integral
against a proper real weight tends to zero by ordinary Riemann–Lebesgue. -/
theorem kernel_weight_tail_tendsto {g : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : b ≤ Real.pi) (hg : RealIntegrable g a b)
    (H : ∀ N : ℕ, RealIntegrable (fun t => g t * (dirichletKernel N t).re) a b) :
    Tendsto (fun N : ℕ => realIntegral _ (H N)) atTop (𝓝 0) := by
  have hsin : ∀ t ∈ Icc a b, Real.sin (t/2) ≠ 0 := by
    intro t ht
    exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1])
      (by linarith [ht.2, Real.pi_pos])).ne'
  have hcont : ContinuousOn (fun t : ℝ => (Real.sin (t/2))⁻¹) (Icc a b) :=
    (Real.continuous_sin.comp (continuous_id.div_const 2)).continuousOn.inv₀ hsin
  let A := fun t => g t * (Real.sin (t/2))⁻¹
  have hA : RealIntegrable A a b := real_product hg
    (realIntegrable_of_continuousOn hg.ordered hcont)
  obtain ⟨J, hJ⟩ := riemann_lebesgue_real A hA
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨R, _, hR⟩ := hJ ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt R
  refine ⟨K, fun N hN => ?_⟩
  let ν : ℝ := (N : ℝ)+1/2
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hfreq : R ≤ |ν| := by
    rw [abs_of_pos hν]
    have hKN : (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    dsimp [ν]
    linarith
  have heq : ∀ t ∈ Ioo a b,
      ((A t : ℂ) * Complex.exp (Complex.I * (ν : ℂ) * (t : ℂ))).im =
        g t * (dirichletKernel N t).re := by
    intro t ht
    have hz := hsin t (Ioo_subset_Icc_self ht)
    have he := congrArg Complex.re (dirichletKernel_sine_mul N t)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at he
    have hk : (dirichletKernel N t).re = Real.sin (ν*t) / Real.sin (t/2) := by
      apply (eq_div_iff hz).mpr
      simpa [ν, mul_comm] using he
    have hphase : Complex.I * (ν : ℂ) * (t : ℂ) = ((ν*t : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hphase]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.exp_ofReal_mul_I_im, hk]
    dsimp [A]
    ring
  have he := integral_congr (J ν).2 (H N) heq
  have hc := (complexIntegral_components _ (J ν)).2
  have hbound := Complex.abs_im_le_norm (complexIntegral _ (J ν))
  rw [hc] at hbound
  change |realIntegral _ (J ν).2| ≤ ‖complexIntegral _ (J ν)‖ at hbound
  rw [he] at hbound
  simpa only [Real.dist_eq, sub_zero] using hbound.trans_lt (hR ν hfreq)

/-- A real BV weight vanishing at zero and tending to zero there annihilates
D_N on the whole half-period. The cutoff is chosen before the frequency. -/
theorem kernel_weight_zero_tendsto {g : ℝ → ℝ}
    (hg : HasBoundedVariation g 0 Real.pi) (hg0 : g 0 = 0)
    (hlim : RightRelativeLimit g (Icc 0 Real.pi) 0 0)
    (H : ∀ N : ℕ, RealIntegrable (fun t => g t * (dirichletKernel N t).re) 0 Real.pi) :
    Tendsto (fun N : ℕ => realIntegral _ (H N)) atTop (𝓝 0) := by
  obtain ⟨C, hC, _, hlocal⟩ := jordan_local_estimate
  have hgi : RealIntegrable g 0 Real.pi := (real_bv_riemann g Real.pi_pos.le hg).2.2
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (4*C+2)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, _, hδπ, hδN⟩ := hlocal g Real.pi_pos hg hg0 hlim η hη
  let Htail (N : ℕ) := (H N).subinterval hδ.le hδπ le_rfl
  have htail := kernel_weight_tail_tendsto hδ le_rfl
    (hgi.subinterval hδ.le hδπ le_rfl) Htail
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp htail (ε/2) (half_pos hε)
  refine ⟨K, fun N hN => ?_⟩
  obtain ⟨hhead, hheadB⟩ := hδN N
  have hs := (real_split _ hδ.le hδπ (H N).bounded).2 (H N) hhead (Htail N)
  change realIntegral _ (H N) = realIntegral _ hhead + realIntegral _ (Htail N) at hs
  have ht : |realIntegral _ (Htail N)| < ε/2 := by
    simpa only [Real.dist_eq, sub_zero] using hK N hN
  have hh : 2*C*η < ε/2 := by
    have hv : (4*C+2)*η = ε := by dsimp [η]; field_simp
    nlinarith
  simpa only [Real.dist_eq, sub_zero] using
    (show |realIntegral _ (H N)| < ε from by
      rw [hs]
      exact (abs_add_le _ _).trans_lt (by linarith))

/-- Evenness and the full-period mean fix the half-period integral exactly. -/
theorem dirichletKernel_half_integral (N : ℕ)
    (hi : ComplexIntegrable (dirichletKernel N) 0 Real.pi) :
    complexIntegral _ hi = (Real.pi : ℂ) := by
  let hf := dirichletKernel_integrable N
  obtain ⟨hh, hhE⟩ := complexIntegral_fold_pi hf
  obtain ⟨hs, hsE⟩ := complex_add_value hi hi
  have he : complexIntegral _ hh = complexIntegral _ hs :=
    complexIntegral_eq_of_eqOn_open hh hs (by
      intro t ht
      change dirichletKernel N (-t) + dirichletKernel N t = _
      exact congrArg (fun z => z + dirichletKernel N t) (dirichletKernel_even N t))
  have hm := dirichletKernel_integral_mean N hf
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ hf = 1 at hm
  rw [← hhE, he, hsE] at hm
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast at hm
  field_simp at hm
  linear_combination hm / 2

theorem real_dirichletKernel_half_integral (N : ℕ)
    (hi : RealIntegrable (fun t => (dirichletKernel N t).re) 0 Real.pi) :
    realIntegral _ hi = Real.pi := by
  have hc := complexIntegrable_of_continuousOn Real.pi_pos.le
    (dirichletKernel_continuous N).continuousOn
  have he := congrArg Complex.re (dirichletKernel_half_integral N hc)
  simpa only [(complexIntegral_components _ hc).1, Complex.ofReal_re] using he

/-- Testing a real BV function against the half-period kernel gives π times
its finite right limit, regardless of its assigned value at zero. -/
theorem real_kernel_weight_tendsto {g : ℝ → ℝ} {L : ℝ}
    (hg : HasBoundedVariation g 0 Real.pi)
    (hlim : RightRelativeLimit g (Icc 0 Real.pi) 0 L)
    (H : ∀ N : ℕ, RealIntegrable (fun t => g t * (dirichletKernel N t).re) 0 Real.pi) :
    Tendsto (fun N : ℕ => realIntegral _ (H N)) atTop (𝓝 (L*Real.pi)) := by
  obtain ⟨hhBV, hh0, hhlim⟩ := rightRecenter_bv Real.pi_pos hg hlim
  have hhi := (real_bv_riemann _ Real.pi_pos.le hhBV).2.2
  let J := fun N => real_kernel_weight_integrable hhi N
  have hz := kernel_weight_zero_tendsto hhBV hh0 hhlim J
  have he (N : ℕ) : realIntegral _ (J N) = realIntegral _ (H N) - L*Real.pi := by
    have hk : RealIntegrable (fun t => (dirichletKernel N t).re) 0 Real.pi := realIntegrable_of_continuousOn Real.pi_pos.le
      ((Complex.continuous_re.comp (dirichletKernel_continuous N)).continuousOn)
    obtain ⟨hn, hnE⟩ := real_mul_value hk (-L)
    obtain ⟨hs, hsE⟩ := real_add_value (H N) hn
    have he := integral_congr (J N) hs (by
      intro t ht
      simp only [rightRecenter, ne_of_gt ht.1, ↓reduceIte]
      ring)
    rw [he, hsE, hnE, real_dirichletKernel_half_integral N hk]
    ring
  have hz' := hz.add_const (L*Real.pi)
  simpa only [zero_add] using hz'.congr' (Eventually.of_forall (fun N => by rw [he]; ring))

/-- Componentwise testing for complex BV weights. Only real Jordan
decompositions are used, and the kernel itself is real. -/
theorem complex_kernel_weight_tendsto {g : ℝ → ℂ} {L : ℂ}
    (hg : HasBoundedVariation g 0 Real.pi)
    (hlim : RightRelativeLimit g (Icc 0 Real.pi) 0 L)
    (H : ∀ N : ℕ, ComplexIntegrable (fun t => g t * dirichletKernel N t) 0 Real.pi) :
    Tendsto (fun N : ℕ => complexIntegral _ (H N)) atTop (𝓝 (L*(Real.pi : ℂ))) := by
  have hv := component_variations g 0 Real.pi
  have hrBV : HasBoundedVariation (fun t => (g t).re) 0 Real.pi := lt_of_le_of_lt hv.1 hg
  have hiBV : HasBoundedVariation (fun t => (g t).im) 0 Real.pi := lt_of_le_of_lt hv.2 hg
  have ht := (rightRelativeLimit_filter_iff _ _ _ _).mp hlim
  have hrL : RightRelativeLimit (fun t => (g t).re) (Icc 0 Real.pi) 0 L.re :=
    (rightRelativeLimit_filter_iff _ _ _ _).mpr ⟨ht.1, Complex.continuous_re.continuousAt.tendsto.comp ht.2⟩
  have hiL : RightRelativeLimit (fun t => (g t).im) (Icc 0 Real.pi) 0 L.im :=
    (rightRelativeLimit_filter_iff _ _ _ _).mpr ⟨ht.1, Complex.continuous_im.continuousAt.tendsto.comp ht.2⟩
  let Jr := fun N => real_kernel_weight_integrable (real_bv_riemann _ Real.pi_pos.le hrBV).2.2 N
  let Ji := fun N => real_kernel_weight_integrable (real_bv_riemann _ Real.pi_pos.le hiBV).2.2 N
  have hr := real_kernel_weight_tendsto hrBV hrL Jr
  have hi := real_kernel_weight_tendsto hiBV hiL Ji
  have her (N : ℕ) : (complexIntegral _ (H N)).re = realIntegral _ (Jr N) := by
    rw [(complexIntegral_components _ (H N)).1]
    apply integral_congr
    intro t ht
    simp only [Complex.mul_re, dirichletKernel_real N t, mul_zero, sub_zero]
  have hei (N : ℕ) : (complexIntegral _ (H N)).im = realIntegral _ (Ji N) := by
    rw [(complexIntegral_components _ (H N)).2]
    apply integral_congr
    intro t ht
    simp only [Complex.mul_im, dirichletKernel_real N t, mul_zero, zero_add]
  have hre : Tendsto (fun N : ℕ => (complexIntegral _ (H N)).re) atTop (𝓝 (L.re*Real.pi)) :=
    hr.congr' (Eventually.of_forall (fun N => (her N).symm))
  have him : Tendsto (fun N : ℕ => (complexIntegral _ (H N)).im) atTop (𝓝 (L.im*Real.pi)) :=
    hi.congr' (Eventually.of_forall (fun N => (hei N).symm))
  have hc := tendsto_complex_of_components hre him
  convert hc using 1
  apply congrArg nhds
  apply Complex.ext <;> simp

/-- The two translated halves of a periodic BV function are BV on [0,π]. -/
theorem periodic_bv_translated_halves {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {a : ℝ} (hp : Function.Periodic f (2*Real.pi))
    (hf : HasBoundedVariation f a (a+2*Real.pi)) (x : ℝ) :
    HasBoundedVariation (fun t => f (x+t)) 0 Real.pi ∧
      HasBoundedVariation (fun t => f (x-t)) 0 Real.pi := by
  have hB := (boundedVariation_iff f (show a ≤ a+2*Real.pi by linarith [Real.pi_pos])).mp hf
  have hplus := boundedVariation_period (by positivity : 0 < 2*Real.pi) hp hB x
  have hminus := boundedVariation_period (by positivity : 0 < 2*Real.pi) hp hB (x-2*Real.pi)
  have htplus := boundedVariation_comp_monotone (t := Icc 0 Real.pi) hplus (fun t => x+t)
    (by intro t ht u hu htu; dsimp; linarith)
    (by intro t ht; constructor <;> dsimp <;> linarith [ht.1, ht.2, Real.pi_pos])
  have htminus := boundedVariation_comp_antitone (t := Icc 0 Real.pi) hminus (fun t => x-t)
    (by intro t ht u hu htu; dsimp; linarith)
    (by intro t ht; constructor <;> dsimp <;> linarith [ht.1, ht.2, Real.pi_pos])
  exact ⟨(boundedVariation_iff _ Real.pi_pos.le).mpr htplus,
    (boundedVariation_iff _ Real.pi_pos.le).mpr htminus⟩

/-- The sum of the two translated halves has their sum of sided limits.
At zero its original assigned value is retained. -/
theorem translated_halves_right_limit {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {x : ℝ} {Lm Lp : E}
    (hm : Tendsto f (𝓝[Iio x] x) (𝓝 Lm))
    (hp : Tendsto f (𝓝[Ioi x] x) (𝓝 Lp)) :
    RightRelativeLimit (fun t => f (x+t) + f (x-t)) (Icc 0 Real.pi) 0 (Lp+Lm) := by
  let s := Icc (0 : ℝ) Real.pi ∩ Ioi 0
  have hplus : Tendsto (fun t : ℝ => x+t) (𝓝[s] 0) (𝓝[Ioi x] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousWithinAt (fun t : ℝ => x+t) s 0 :=
        (continuous_const.add continuous_id).continuousWithinAt
      change Tendsto (fun t : ℝ => x+t) (𝓝[s] 0) (𝓝 (x+0)) at hc
      simpa only [add_zero] using hc
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change x < x+t
      have ht0 : 0 < t := ht.2
      linarith
  have hminus : Tendsto (fun t : ℝ => x-t) (𝓝[s] 0) (𝓝[Iio x] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousWithinAt (fun t : ℝ => x-t) s 0 :=
        (continuous_const.sub continuous_id).continuousWithinAt
      change Tendsto (fun t : ℝ => x-t) (𝓝[s] 0) (𝓝 (x-0)) at hc
      simpa only [sub_zero] using hc
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change x-t < x
      have ht0 : 0 < t := ht.2
      linarith
  apply (rightRelativeLimit_filter_iff _ _ _ _).mpr
  exact ⟨closedInterval_right_accumulation
    (show 0 ∈ Ico 0 Real.pi from ⟨le_rfl, Real.pi_pos⟩),
    (hp.comp hplus).add (hm.comp hminus)⟩

/-- Ordinary symmetric Fourier sums converge at every point of a complex
periodic BV function, including jumps and the seams of any chosen period. -/
theorem dirichlet_jordan_complex :
    Specs.SingleVariableAnalysis.Ch19.Jordan.complexJordan := by
  intro f a hp hf
  have hB := (boundedVariation_iff f (show a ≤ a+2*Real.pi by linarith [Real.pi_pos])).mp hf
  have hBπ := boundedVariation_period (by positivity : 0 < 2*Real.pi) hp hB (-Real.pi)
  have hBVπ : HasBoundedVariation f (-Real.pi) Real.pi := by
    apply (boundedVariation_iff f (by linarith [Real.pi_pos])).mpr
    simpa only [show -Real.pi+2*Real.pi = Real.pi by ring] using hBπ
  have hfi : ComplexIntegrable f (-Real.pi) Real.pi :=
    (complex_bv_riemann f (by linarith [Real.pi_pos]) hBVπ).2.2
  refine ⟨fourierCoeff_integrable f hfi, fun x => ?_⟩
  obtain ⟨Lm, Lp, hm, hpl⟩ := periodic_bv_sided_limits
    (by positivity : 0 < 2*Real.pi) hp hf x
  refine ⟨Lm, Lp, hm, hpl, fun H => ?_⟩
  obtain ⟨hplus, hminus⟩ := periodic_bv_translated_halves hp hf x
  let g := fun t => f (x+t) + f (x-t)
  have hg : HasBoundedVariation g 0 Real.pi :=
    lt_of_le_of_lt (totalVariation_add_le _ _ Real.pi_pos.le)
      (ENNReal.add_lt_top.mpr ⟨hplus, hminus⟩)
  have hgi : ComplexIntegrable g 0 Real.pi :=
    (complex_bv_riemann g Real.pi_pos.le hg).2.2
  let J := fun N => complex_product hgi
    (complexIntegrable_of_continuousOn Real.pi_pos.le (dirichletKernel_continuous N).continuousOn)
  have hlim := complex_kernel_weight_tendsto hg (translated_halves_right_limit hm hpl) J
  have hv := hlim.const_mul (((1/(2*Real.pi) : ℝ) : ℂ))
  have htarget : ((1/(2*Real.pi) : ℝ) : ℂ) * ((Lp+Lm)*(Real.pi : ℂ)) = (Lm+Lp)/2 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
    ring
  rw [htarget] at hv
  apply hv.congr'
  apply Eventually.of_forall
  intro N
  obtain ⟨hh, he⟩ := fourierPartialSum_even_convolution f ⟨hp, hfi⟩ H N x
  exact he.symm

/-- The real scalar case uses the canonical embedding for the Fourier sums;
the two sided limits are real and are proved to exist independently. -/
theorem dirichlet_jordan_real :
    Specs.SingleVariableAnalysis.Ch19.Jordan.realJordan := by
  intro f a hp hf
  have hcomp : HasBoundedVariation (fun t => (f t : ℂ)) a (a+2*Real.pi) := by
    apply lt_of_le_of_lt (totalVariation_le_of_norm_sub_le f (fun t => (f t : ℂ)) a (a+2*Real.pi) _) hf
    intro x y
    simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, le_refl]
  obtain ⟨H, hH⟩ := dirichlet_jordan_complex (fun t => (f t : ℂ)) a (hp.comp Complex.ofReal) hcomp
  refine ⟨H, fun x => ?_⟩
  obtain ⟨Lm, Lp, hm, hpl⟩ := periodic_bv_sided_limits
    (by positivity : 0 < 2*Real.pi) hp hf x
  obtain ⟨Zm, Zp, hZm, hZp, hS⟩ := hH x
  have heM : Zm = (Lm : ℂ) := tendsto_nhds_unique hZm hm.ofReal
  have heP : Zp = (Lp : ℂ) := tendsto_nhds_unique hZp hpl.ofReal
  refine ⟨Lm, Lp, hm, hpl, fun H' => ?_⟩
  have hs := hS H'
  rw [heM, heP] at hs
  simpa only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat] using hs

end SingleVariableAnalysis.Fourier
