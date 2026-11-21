import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SchrodingerPotentialBounds
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.OneDimensionalSobolev
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace ExpandedFA.Unbounded.SchrodingerPotential
variable {𝕜 : Type} [RCLike 𝕜]

/-- Elementary Young estimate using only a squared interpolation inequality.
This avoids fractional powers when converting Sobolev estimates to relative
operator bounds. -/
theorem young_of_square_bound (U V W Q ε : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hQ : 0 ≤ Q)
    (hε : 0 < ε) (hVW : V ^ 2 ≤ U * W) :
    Q * V ≤ ε * W + (Q ^ 2 / (4 * ε)) * U := by
  let c := Q ^ 2 / (4 * ε)
  have hc : 0 ≤ c := by positivity
  have he : 4 * ε * c = Q ^ 2 := by
    dsimp [c]
    field_simp
  have he' : 4 * ε * c * U * W = Q ^ 2 * U * W := by rw [he]
  have hsq : (Q * V) ^ 2 ≤ Q ^ 2 * U * W := by
    nlinarith [mul_le_mul_of_nonneg_left hVW (sq_nonneg Q)]
  have hsq' : Q ^ 2 * U * W ≤ (ε * W + c * U) ^ 2 := by
    nlinarith [sq_nonneg (ε * W - c * U)]
  exact (sq_le_sq₀ (mul_nonneg hQ hV) (by positivity)).mp (hsq.trans hsq')

/-- The final scalar step for the potential's relative bound, from an H¹
supremum estimate and the free interpolation estimate. -/
theorem relative_young (U V W P Q R ε : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hQ : 0 ≤ Q)
    (hε : 0 < ε) (hVW : V ^ 2 ≤ U * W)
    (hP : P ≤ Q * (U + V) + R * U) :
    P ≤ ε * W + (Q + R + Q ^ 2 / (4 * ε)) * U := by
  have hy := young_of_square_bound U V W Q ε hU hV hW hQ hε hVW
  nlinarith

/-- The corresponding scalar step for the quadratic form. -/
theorem form_young (U V Q ε : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hQ : 0 ≤ Q) (hε : 0 < ε) :
    Q * U * V ≤ ε * V ^ 2 + (Q ^ 2 / (4 * ε)) * U ^ 2 := by
  simpa only [mul_assoc] using young_of_square_bound (U ^ 2) (U * V) (V ^ 2) Q ε
    (sq_nonneg U) (mul_nonneg hU hV) (sq_nonneg V) hQ hε (by ring_nf; rfl)

/-- Test distributions distinguish the actual L² classes on ℝ. -/
theorem regular_injective : Function.Injective (regular (𝕜 := 𝕜)) := by
  intro u v huv
  apply Lp.ext
  have hloc : LocallyIntegrable (fun x => u x - v x) volume :=
    ((Lp.memLp u).locallyIntegrable (by norm_num)).sub
      ((Lp.memLp v).locallyIntegrable (by norm_num))
  have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hg hgc => by
      let φ : Tests 𝕜 :=
        ⟨fun x => (g x : 𝕜), ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp hg),
          hgc.comp_left (by simp), subset_univ _⟩
      have heq := congrArg (fun T : Distribution 𝕜 => T φ) huv
      simp only [regular_apply] at heq
      have hu := φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜)
        (((Lp.memLp u).locallyIntegrable (by norm_num)).locallyIntegrableOn
          (⊤ : Opens ℝ))
      have hv := φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜)
        (((Lp.memLp v).locallyIntegrable (by norm_num)).locallyIntegrableOn
          (⊤ : Opens ℝ))
      change Integrable (fun x => φ x * u x) volume at hu
      change Integrable (fun x => φ x * v x) volume at hv
      simp only [RCLike.real_smul_eq_coe_mul]
      change (∫ x, φ x * (u x - v x)) = 0
      simp_rw [mul_sub]
      rw [integral_sub hu hv, heq, sub_self])
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

theorem weakDerivative_unique {u v w : L2 𝕜}
    (hv : WeakDerivative u v) (hw : WeakDerivative u w) : v = w :=
  regular_injective (hv.trans hw.symm)

theorem weakDerivative_zero {v : L2 𝕜} (h : WeakDerivative 0 v) : v = 0 := by
  apply regular_injective
  change regularLM v = regularLM 0
  simpa [WeakDerivative, distributionDerivative] using h

/-- The graph construction has no nonzero vertical vector. -/
theorem freeGraph_vertical (p : L2 𝕜 × L2 𝕜) (hp : p ∈ freeGraph 𝕜)
    (hz : p.1 = 0) : p.2 = 0 := by
  obtain ⟨v, hv, hw⟩ := hp
  rw [hz] at hv
  rw [weakDerivative_zero hv] at hw
  exact neg_eq_zero.mp (weakDerivative_zero hw)

theorem free_graph : Spec.FreeGraph := by
  intro 𝕜 _
  exact ⟨(freeGraph 𝕜).toLinearPMap_graph_eq freeGraph_vertical, rfl⟩

theorem mem_H2_iff (u : L2 𝕜) :
    u ∈ H2 𝕜 ↔ ∃ v w : L2 𝕜, WeakDerivative u v ∧ WeakDerivative v w := by
  change (∃ p, p ∈ freeGraph 𝕜 ∧ p.1 = u) ↔ _
  constructor
  · rintro ⟨⟨a, b⟩, ⟨v, hv, hw⟩, rfl⟩
    exact ⟨v, -b, hv, hw⟩
  · rintro ⟨v, w, hv, hw⟩
    exact ⟨(u, -w), ⟨v, hv, by simpa using hw⟩, rfl⟩

theorem potentialGraph_vertical (q : ℝ → ℝ) (p : L2 𝕜 × L2 𝕜)
    (hp : p ∈ potentialGraph 𝕜 q) (hz : p.1 = 0) : p.2 = 0 := by
  apply Lp.ext
  change (p.2 : ℝ → 𝕜) =ᵐ[volume] fun x => (q x : 𝕜) * p.1 x at hp
  rw [hz] at hp
  filter_upwards [hp, Lp.coeFn_zero 𝕜 2 volume] with x hx hzero
  simp at hx
  exact hx.trans hzero.symm

theorem potential_graph : Spec.PotentialGraph := by
  intro 𝕜 _ q
  exact (potentialGraph 𝕜 q).toLinearPMap_graph_eq (potentialGraph_vertical q)

/-- Multiplication is exactly the pointwise product on a.e. representatives. -/
theorem potential_apply_ae (q : ℝ → ℝ) (u : (potential 𝕜 q).domain) :
    (potential 𝕜 q u : ℝ → 𝕜) =ᵐ[volume] fun x => (q x : 𝕜) * u.val x := by
  have h := (potential 𝕜 q).mem_graph u
  rw [potential_graph 𝕜 q] at h
  exact h

/-- Pointwise real multiplication is formally symmetric, without needing an
unproved regularity assumption on the potential. Density is supplied separately. -/
theorem potential_inner (q : ℝ → ℝ) (u v : (potential 𝕜 q).domain) :
    inner 𝕜 (potential 𝕜 q u) v.val = inner 𝕜 u.val (potential 𝕜 q v) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [potential_apply_ae q u, potential_apply_ae q v] with x hu hv
  rw [hu, hv]
  simp [RCLike.inner_apply, mul_left_comm, mul_comm]

/-- Extract actual domain inclusion from the existential relative-bound clause. -/
theorem domain_le_of_relative_bound (h : Spec.RelativeBound) (q : ℝ → ℝ)
    (hq : Admissible q) : (freeLaplacian 𝕜).domain ≤ (potential 𝕜 q).domain := by
  obtain ⟨C, hC, hb⟩ := h 𝕜 q hq 1 zero_lt_one
  intro u hu
  obtain ⟨v, hv, _⟩ := hb ⟨u, hu⟩
  exact ((potential 𝕜 q).mem_domain_iff).mpr ⟨v, hv⟩

/-- Quantitative estimates can be read directly on the canonical partial map. -/
theorem bound_on_domain (h : Spec.RelativeBound) (q : ℝ → ℝ)
    (hq : Admissible q) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : (freeLaplacian 𝕜).domain,
      ‖potential 𝕜 q ⟨u.val, domain_le_of_relative_bound h q hq u.prop⟩‖ ≤
        ε * ‖freeLaplacian 𝕜 u‖ + C * ‖u.val‖ := by
  obtain ⟨C, hC, hb⟩ := h 𝕜 q hq ε hε
  refine ⟨C, hC, fun u => ?_⟩
  obtain ⟨v, hv, hn⟩ := hb u
  have he : potential 𝕜 q ⟨u.val, domain_le_of_relative_bound h q hq u.prop⟩ = v :=
    ((LinearPMap.image_iff _).mpr hv).symm
  rwa [he]

/-- Formal symmetry plus density gives the canonical adjoint inclusion. -/
theorem potential_symmetric (q : ℝ → ℝ)
    (hd : Dense ((potential 𝕜 q).domain : Set (L2 𝕜))) :
    Dense ((potential 𝕜 q).domain : Set (L2 𝕜)) ∧
      potential 𝕜 q ≤ HilbertAdjointSpec.adjointValue (potential 𝕜 q) := by
  refine ⟨hd, LinearPMap.IsFormalAdjoint.le_adjoint (hT := hd) ?_⟩
  exact potential_inner q

/-- The multiplication quadratic form really is the integral appearing in
its analytic estimate. -/
theorem potential_quadratic (q : ℝ → ℝ) (u : (potential 𝕜 q).domain) :
    RCLike.re (inner 𝕜 u.val (potential 𝕜 q u)) = ∫ x, q x * ‖u.val x‖ ^ 2 := by
  rw [L2.inner_def, ← integral_re (L2.integrable_inner u.val (potential 𝕜 q u))]
  apply integral_congr_ae
  filter_upwards [potential_apply_ae q u] with x hx
  rw [hx]
  change RCLike.re (inner 𝕜 (u.val x) ((q x : 𝕜) • u.val x)) = _
  rw [inner_smul_real_right]
  simp only [RCLike.real_smul_eq_coe_mul, RCLike.mul_re, RCLike.ofReal_re,
    RCLike.ofReal_im, zero_mul, sub_zero, inner_self_eq_norm_sq]

/-- The native-real-line weak derivative tested against a scalar test. -/
theorem weakDerivative_test_identity {u v : L2 𝕜} (h : WeakDerivative u v)
    (φ : Tests 𝕜) :
    (∫ x, φ x * v x) = -(∫ x, deriv φ x * u x) := by
  have he := congrArg (fun T : Distribution 𝕜 => T φ) h
  change regular v φ = -(regular u (TestFunction.lineDerivCLM 𝕜 (1 : ℝ) φ)) at he
  have hd : ∀ x, (TestFunction.lineDerivCLM 𝕜 (1 : ℝ) φ : Tests 𝕜) x =
      deriv φ x := by
    intro x
    rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
    rw [(φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]
    rfl
  simpa only [regular_apply, hd] using he

/-- A native-real-line H¹ class has a continuous, locally absolutely continuous
representative, with the given L² class as its a.e. derivative. This uses the
accepted real-variable primitive lemmas directly; no coordinate identification
or change of measure is implicit. -/
theorem weakDerivative_representative {u v : L2 𝕜} (h : WeakDerivative u v) :
    ∃ f : ℝ → 𝕜, Continuous f ∧ (u : ℝ → 𝕜) =ᵐ[volume] f ∧
      (∀ a b, AbsolutelyContinuousOnInterval f a b) ∧
      (∀ x y, f x - f y = ∫ t in y..x, v t) ∧
      (∀ᵐ x ∂volume, HasDerivAt f (v x) x) := by
  have hv : LocallyIntegrable (fun x => v x) volume :=
    (Lp.memLp v).locallyIntegrable (by norm_num)
  have hu : LocallyIntegrable (fun x => u x) volume :=
    (Lp.memLp u).locallyIntegrable (by norm_num)
  have hi (a b : ℝ) : IntervalIntegrable (fun x => v x) volume a b :=
    (hv.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  let F : ℝ → 𝕜 := fun x => ∫ t in (0 : ℝ)..x, v t
  have hFc : Continuous F := intervalIntegral.continuous_primitive hi 0
  have hz : ∀ ψ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (univ : Set ℝ) →
      (∫ t, deriv ψ t • (u t - F t)) = 0 := by
    intro ψ hd hc _
    let φ : Tests 𝕜 :=
      ⟨fun x => (ψ x : 𝕜), ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp hd),
        hc.comp_left (by simp), subset_univ _⟩
    have ht := weakDerivative_test_identity h φ
    have hp := Sobolev.OneDimensional.integral_test_mul_primitive hv 0
      φ.contDiff φ.hasCompactSupport
    have hdφ : ∀ x, deriv φ x = ((deriv ψ x : ℝ) : 𝕜) := by
      intro x
      exact ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasFDerivAt.comp_hasDerivAt x
        (hd.differentiable (by simp) x).hasDerivAt).deriv
    have hiu : Integrable (fun t => deriv ψ t • u t) volume :=
      hu.integrable_smul_left_of_hasCompactSupport
        (hd.continuous_deriv (by simp)) hc.deriv
    have hiF : Integrable (fun t => deriv ψ t • F t) volume :=
      hFc.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
        (hd.continuous_deriv (by simp)) hc.deriv
    simp_rw [hdφ] at ht hp
    simp only [smul_sub, integral_sub hiu hiF]
    simp_rw [RCLike.real_smul_eq_coe_mul]
    exact sub_eq_zero.mpr (neg_injective (ht.symm.trans hp))
  obtain ⟨c, hc⟩ := Sobolev.OneDimensional.ae_eq_const_of_integral_deriv_eq_zero
    isOpen_univ ordConnected_univ (hu.sub hFc.locallyIntegrable) hz
  rw [Measure.restrict_univ] at hc
  refine ⟨fun x => F x + c, hFc.add continuous_const, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hc] with x hx
    exact (sub_eq_iff_eq_add.mp hx).trans (add_comm _ _)
  · intro a b
    exact (Sobolev.OneDimensional.integral_primitive_absolutelyContinuous hi a b 0).add
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn.absolutelyContinuousOnInterval
  · intro x y
    simp only [add_sub_add_right_eq_sub, F]
    exact intervalIntegral.integral_interval_sub_left (hi 0 x) (hi 0 y)
  · filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hv] with x hx
    exact (hx 0).add_const c

/-- A unit interval has L¹ norm bounded by the global L² norm. -/
theorem integral_norm_unit_le (u : L2 𝕜) (x : ℝ) :
    (∫ t in Icc x (x + 1), ‖u t‖) ≤ ‖u‖ := by
  let ν : Measure ℝ := volume.restrict (Icc x (x + 1))
  have hm : MemLp (fun t => u t) 2 ν := (Lp.memLp u).mono_measure
    Measure.restrict_le_self
  have hi := Sobolev.OneDimensional.integral_norm_le_lp hm
  have hn : (eLpNorm (fun t => u t) 2 ν).toReal ≤ ‖u‖ := by
    rw [Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top u)
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hν : (ν univ).toReal = 1 := by simp [ν, Real.volume_Icc]
  rw [hν, Real.one_rpow, mul_one] at hi
  exact hi.trans hn

/-- A fixed whole-line H¹ estimate suffices for both infinitesimal bounds.
It is proved on the actual native-real-line weak-derivative graph. -/
theorem weakDerivative_ae_bound {u v : L2 𝕜} (h : WeakDerivative u v) :
    ∀ᵐ x ∂volume, ‖u x‖ ≤ ‖u‖ + ‖v‖ := by
  obtain ⟨f, hfc, huf, _, hinc, _⟩ := weakDerivative_representative h
  have hpoint (x : ℝ) : ‖f x‖ ≤ ‖u‖ + ‖v‖ := by
    let ν : Measure ℝ := volume.restrict (Icc x (x + 1))
    have hu : Integrable (fun t => u t) ν :=
      ((Lp.memLp u).mono_measure Measure.restrict_le_self).integrable (by norm_num)
    have hv : Integrable (fun t => ‖v t‖) ν :=
      (((Lp.memLp v).mono_measure Measure.restrict_le_self).integrable (by norm_num)).norm
    have hosc (y : ℝ) (hy : y ∈ Icc x (x + 1)) : ‖f x - f y‖ ≤ ‖v‖ := by
      rw [hinc x y]
      apply intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      apply (setIntegral_mono_set hv (ae_of_all _ (fun _ => norm_nonneg _))
        (ae_of_all _ (uIoc_subset_uIcc.trans
          (uIcc_subset_Icc hy ⟨le_rfl, by linarith⟩)))).trans
      exact integral_norm_unit_le v x
    have hp : ∀ᵐ t ∂ν, ‖f x‖ ≤ ‖u t‖ + ‖v‖ := by
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        (ae_restrict_of_ae huf)] with t ht he
      rw [he]
      calc
        ‖f x‖ = ‖(f x - f t) + f t‖ := by congr 1; abel
        _ ≤ ‖f x - f t‖ + ‖f t‖ := norm_add_le _ _
        _ ≤ ‖f t‖ + ‖v‖ := by linarith [hosc t ht]
    have hh := integral_mono_ae (integrable_const ‖f x‖)
      (hu.norm.add (integrable_const ‖v‖)) hp
    have hν : (ν univ).toReal = 1 := by simp [ν, Real.volume_Icc]
    simp only [Pi.add_apply] at hh
    rw [integral_add hu.norm (integrable_const ‖v‖)] at hh
    simp only [integral_const, measureReal_def, hν, smul_eq_mul, one_mul] at hh
    exact hh.trans (by dsimp [ν]; linarith [integral_norm_unit_le u x])
  filter_upwards [huf] with x hx
  rw [hx]
  exact hpoint x

/-- Actual L² multiplication by an L² real coefficient on a bounded class. -/
theorem l2_mul_of_ae_bound (a : ℝ → ℝ) (ha : MemLp a 2 volume)
    (u : L2 𝕜) (B : ℝ) (hb : ∀ᵐ x ∂volume, ‖u x‖ ≤ B) :
    ∃ w : L2 𝕜, (w : ℝ → 𝕜) =ᵐ[volume] (fun x => (a x : 𝕜) * u x) ∧
      ‖w‖ ≤ B * lpNorm a 2 volume := by
  have hm : AEStronglyMeasurable (fun x => (a x : 𝕜) * u x) volume :=
    ha.ofReal.aestronglyMeasurable.mul (Lp.memLp u).aestronglyMeasurable
  have hn : ∀ᵐ x ∂volume, ‖(a x : 𝕜) * u x‖ ≤ B * ‖a x‖ := by
    filter_upwards [hb] with x hx
    rw [norm_mul, RCLike.norm_ofReal]
    simpa only [Real.norm_eq_abs, mul_comm] using
      mul_le_mul_of_nonneg_left hx (norm_nonneg (a x))
  have hw : MemLp (fun x => (a x : 𝕜) * u x) 2 volume := ha.of_le_mul hm hn
  refine ⟨hw.toLp _, hw.coeFn_toLp, ?_⟩
  have hh : ‖hw.toLp _‖ ≤ B * ‖ha.toLp a‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hw.coeFn_toLp, ha.coeFn_toLp, hn] with x hx ha' hn'
    simpa only [hx, ha'] using hn'
  simpa only [Lp.norm_toLp, toReal_eLpNorm] using hh

/-- Actual L² multiplication by an essentially bounded real coefficient. -/
theorem linfty_mul (a : ℝ → ℝ) (ha : MemLp a ∞ volume) (u : L2 𝕜) :
    ∃ w : L2 𝕜, (w : ℝ → 𝕜) =ᵐ[volume] (fun x => (a x : 𝕜) * u x) ∧
      ‖w‖ ≤ lpNorm a ∞ volume * ‖u‖ := by
  have hm : AEStronglyMeasurable (fun x => (a x : 𝕜) * u x) volume :=
    ha.ofReal.aestronglyMeasurable.mul (Lp.memLp u).aestronglyMeasurable
  have hn : ∀ᵐ x ∂volume,
      ‖(a x : 𝕜) * u x‖ ≤ lpNorm a ∞ volume * ‖u x‖ := by
    filter_upwards [ae_le_lpNorm_exponent_top ha] with x hx
    rw [norm_mul, RCLike.norm_ofReal]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hw : MemLp (fun x => (a x : 𝕜) * u x) 2 volume :=
    (Lp.memLp u).of_le_mul hm hn
  refine ⟨hw.toLp _, hw.coeFn_toLp, ?_⟩
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hw.coeFn_toLp, hn] with x hx hn'
  simpa only [hx] using hn'

/-- An admissible potential multiplies every H¹ vector into a genuine L²
class, with the quantitative bound used by both final estimates. -/
theorem potential_h1_bound (q : ℝ → ℝ) (hq : Admissible q) :
    ∃ Q R : ℝ, 0 ≤ Q ∧ 0 ≤ R ∧ ∀ u v : L2 𝕜, WeakDerivative u v →
      ∃ w : L2 𝕜, (u, w) ∈ (potential 𝕜 q).graph ∧
        ‖w‖ ≤ Q * (‖u‖ + ‖v‖) + R * ‖u‖ := by
  obtain ⟨a, b, ha, hb, hq⟩ := hq
  refine ⟨lpNorm a 2 volume, lpNorm b ∞ volume, lpNorm_nonneg, lpNorm_nonneg, ?_⟩
  intro u v huv
  obtain ⟨wa, hwa, hna⟩ := l2_mul_of_ae_bound a ha u (‖u‖ + ‖v‖)
    (weakDerivative_ae_bound huv)
  obtain ⟨wb, hwb, hnb⟩ := linfty_mul b hb u
  refine ⟨wa + wb, ?_, ?_⟩
  · rw [potential_graph]
    change (wa + wb : L2 𝕜) =ᵐ[volume] (fun x => (q x : 𝕜) * u x)
    filter_upwards [Lp.coeFn_add wa wb, hwa, hwb, hq] with x hx ha' hb' hq'
    rw [hx, Pi.add_apply, ha', hb', hq', RCLike.ofReal_add, add_mul]
  · calc
      ‖wa + wb‖ ≤ ‖wa‖ + ‖wb‖ := norm_add_le _ _
      _ ≤ _ := by nlinarith

/-- Integrability is a consequence of actual L² multiplication, including
for arbitrary a.e. representatives of q. -/
theorem potential_integrable (q : ℝ → ℝ) (u : (potential 𝕜 q).domain) :
    Integrable (fun x => q x * ‖u.val x‖ ^ 2) volume := by
  apply (L2.integrable_inner (𝕜 := 𝕜) u.val (potential 𝕜 q u)).re.congr
  filter_upwards [potential_apply_ae q u] with x hx
  rw [hx]
  change RCLike.re (inner 𝕜 (u.val x) ((q x : 𝕜) • u.val x)) = _
  rw [inner_smul_real_right]
  simp only [RCLike.real_smul_eq_coe_mul, RCLike.mul_re, RCLike.ofReal_re,
    RCLike.ofReal_im, zero_mul, sub_zero, inner_self_eq_norm_sq]

/-- The full infinitesimal form estimate follows on every H¹ vector, not
only on vectors in the free operator's smaller H² domain. -/
theorem form_bound : Spec.FormBound := by
  intro 𝕜 _ q hq ε hε
  obtain ⟨Q, R, hQ, hR, hb⟩ := potential_h1_bound (𝕜 := 𝕜) q hq
  refine ⟨Q + R + Q ^ 2 / (4 * ε), by positivity, ?_⟩
  intro u v huv
  obtain ⟨w, hw, hn⟩ := hb u v huv
  have hud : u ∈ (potential 𝕜 q).domain :=
    ((potential 𝕜 q).mem_domain_iff).mpr ⟨w, hw⟩
  let uP : (potential 𝕜 q).domain := ⟨u, hud⟩
  have he : potential 𝕜 q uP = w := ((LinearPMap.image_iff _).mpr hw).symm
  refine ⟨potential_integrable q uP, ?_⟩
  have hi : |∫ x, q x * ‖u x‖ ^ 2| ≤ ‖u‖ * ‖w‖ := by
    rw [← potential_quadratic q uP, he]
    exact (RCLike.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have hy := form_young ‖u‖ ‖v‖ Q ε (norm_nonneg _) (norm_nonneg _) hQ hε
  have hn' := mul_le_mul_of_nonneg_left hn (norm_nonneg u)
  nlinarith

/-- The derivative of an integrable locally AC function with integrable
specified derivative has zero integral on the whole line. Integrability forces
both finite endpoint limits at infinity to be zero. -/
theorem integral_eq_zero_of_locallyAC {F g : ℝ → 𝕜}
    (hF : ∀ a b, AbsolutelyContinuousOnInterval F a b)
    (hFi : Integrable F volume) (hgi : Integrable g volume)
    (hd : ∀ᵐ x ∂volume, HasDerivAt F (g x) x) :
    (∫ x, g x) = 0 := by
  have hinc (a b : ℝ) : (∫ x in a..b, g x) = F b - F a :=
    Sobolev.OneDimensional.integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt
      (hF a b) hgi.locallyIntegrable (hd.mono (fun _ hx _ => hx))
  have ht : Filter.Tendsto F Filter.atTop (𝓝 ((∫ x in Ioi (0 : ℝ), g x) + F 0)) := by
    have hi := (intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hgi.integrableOn
      Filter.tendsto_id).add_const (F 0)
    apply hi.congr
    intro x
    rw [hinc]
    abel
  have htz : (∫ x in Ioi (0 : ℝ), g x) + F 0 = 0 := by
    apply IntegrableAtFilter.eq_zero_of_tendsto
      (show IntegrableAtFilter F Filter.atTop volume from ⟨univ, Filter.univ_mem, hFi.integrableOn⟩)
      ?_ ht
    intro s hs
    obtain ⟨b, hb⟩ := Filter.mem_atTop_sets.mp hs
    rw [← top_le_iff, ← Real.volume_Ici (a := b)]
    exact measure_mono hb
  have hb : Filter.Tendsto F Filter.atBot (𝓝 (F 0 - (∫ x in Iic (0 : ℝ), g x))) := by
    have hi := (intervalIntegral_tendsto_integral_Iic (0 : ℝ) hgi.integrableOn
      Filter.tendsto_id).const_sub (F 0)
    apply hi.congr
    intro x
    rw [hinc]
    abel
  have hbz : F 0 - (∫ x in Iic (0 : ℝ), g x) = 0 := by
    apply IntegrableAtFilter.eq_zero_of_tendsto
      (show IntegrableAtFilter F Filter.atBot volume from ⟨univ, Filter.univ_mem, hFi.integrableOn⟩)
      ?_ hb
    intro s hs
    obtain ⟨b, hb⟩ := Filter.mem_atBot_sets.mp hs
    rw [← top_le_iff, ← Real.volume_Iic (a := b)]
    exact measure_mono hb
  have he := integral_add_compl measurableSet_Iic hgi (s := Iic (0 : ℝ))
  rw [compl_Iic] at he
  rw [← he, ← sub_eq_zero.mp hbz]
  simpa only [add_comm] using htz

/-- Global integration by parts for the actual weak-derivative relation.
Both products are integrable by L² Cauchy–Schwarz. -/
theorem weakDerivative_inner {u u' v v' : L2 𝕜}
    (hu : WeakDerivative u u') (hv : WeakDerivative v v') :
    inner 𝕜 u' v = -inner 𝕜 u v' := by
  obtain ⟨f, hfc, huf, hfac, _, hfd⟩ := weakDerivative_representative hu
  obtain ⟨g, hgc, hvg, hgac, _, hgd⟩ := weakDerivative_representative hv
  let F : ℝ → 𝕜 := fun x => starRingEnd 𝕜 (f x) * g x
  let G : ℝ → 𝕜 := fun x => inner 𝕜 (u' x) (v x) + inner 𝕜 (u x) (v' x)
  have hGi : Integrable G volume :=
    (L2.integrable_inner (𝕜 := 𝕜) u' v).add (L2.integrable_inner (𝕜 := 𝕜) u v')
  have hFi : Integrable F volume := by
    apply (L2.integrable_inner (𝕜 := 𝕜) u v).congr
    filter_upwards [huf, hvg] with x hx hy
    simp only [F, RCLike.inner_apply', hx, hy]
  have hFac (a b : ℝ) : AbsolutelyContinuousOnInterval F a b := by
    have hc := (RCLike.conjLIE : 𝕜 ≃ₗᵢ[ℝ] 𝕜).lipschitzWith.comp_absolutelyContinuousOnInterval
      (hfac a b)
    exact hc.smul (hgac a b)
  have hFd : ∀ᵐ x ∂volume, HasDerivAt F (G x) x := by
    filter_upwards [hfd, hgd, huf, hvg] with x hx hy hux hvx
    have hc := (RCLike.conjCLE : 𝕜 ≃L[ℝ] 𝕜).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hx
    convert hc.mul hy using 1 <;>
      simp [F, G, RCLike.conjCLE_apply, hux, hvx,
        Pi.mul_def, Function.comp_def, mul_comm]
  have hz := integral_eq_zero_of_locallyAC hFac hFi hGi hFd
  dsimp only [G] at hz
  rw [integral_add (L2.integrable_inner (𝕜 := 𝕜) u' v)
    (L2.integrable_inner (𝕜 := 𝕜) u v')] at hz
  exact eq_neg_of_add_eq_zero_left hz

/-- The free energy is the squared norm of the actual first weak derivative. -/
theorem free_energy : Spec.FreeEnergy := by
  intro 𝕜 _ u
  have hg := (freeLaplacian 𝕜).mem_graph u
  rw [(free_graph 𝕜).1] at hg
  obtain ⟨v, huv, hvw⟩ := hg
  refine ⟨v, huv, ?_⟩
  have hi := weakDerivative_inner huv hvw
  simp only [inner_neg_right, neg_neg] at hi
  rw [← hi, inner_self_eq_norm_sq]

/-- Interpolation on the full H² domain, derived from the energy identity. -/
theorem free_interpolation (u : (freeLaplacian 𝕜).domain) :
    ∃ v : L2 𝕜, WeakDerivative u.val v ∧
      ‖v‖ ^ 2 ≤ ‖u.val‖ * ‖freeLaplacian 𝕜 u‖ := by
  obtain ⟨v, hv, he⟩ := free_energy 𝕜 u
  refine ⟨v, hv, ?_⟩
  rw [← he]
  exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)

/-- Infinitesimal operator bound, with an actual L² multiplication output
at every vector of the canonical H² domain. -/
theorem relative_bound : Spec.RelativeBound := by
  intro 𝕜 _ q hq ε hε
  obtain ⟨Q, R, hQ, hR, hb⟩ := potential_h1_bound (𝕜 := 𝕜) q hq
  refine ⟨Q + R + Q ^ 2 / (4 * ε), by positivity, ?_⟩
  intro u
  obtain ⟨v, hv, hvi⟩ := free_interpolation u
  obtain ⟨w, hw, hn⟩ := hb u.val v hv
  refine ⟨w, hw, ?_⟩
  exact relative_young ‖u.val‖ ‖v‖ ‖freeLaplacian 𝕜 u‖ ‖w‖ Q R ε
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hQ hε hvi hn

theorem regular_identification : Spec.RegularInjective := by
  intro 𝕜 _
  exact regular_injective

theorem h2_identification : Spec.H2Identification := by
  intro 𝕜 _ u
  exact mem_H2_iff u

theorem potential_symmetry : Spec.PotentialInner := by
  intro 𝕜 _ q u v
  exact potential_inner q u v

end ExpandedFA.Unbounded.SchrodingerPotential
