import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.DirichletIntegral
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.DampedSineIntegral
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.TailBounds
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.ImproperContinuity

noncomputable section
namespace SingleVariableAnalysis.DirichletIntegral
open Set Filter
open scoped Topology
open Riemann Riemann.Improper ParameterIntegral
namespace Spec
export Specs.SingleVariableAnalysis.Ch18.DirichletIntegral (damped)
end Spec
abbrev damped := Spec.damped

theorem sinc_representation :
    Specs.SingleVariableAnalysis.Ch18.DirichletIntegral.sincRepresentation :=
  ⟨Real.sinc_zero, Real.continuous_sinc, fun _x hx => Real.sinc_of_ne_zero hx⟩

theorem damped_zero (x : ℝ) : damped 0 x = Real.sinc x := by
  simp [damped, Spec.damped, Specs.SingleVariableAnalysis.Ch18.DampedSineIntegral.integrandValue]

theorem joint_continuous : Continuous (fun p : ℝ × ℝ => damped p.1 p.2) := by
  exact (Real.continuous_exp.comp (continuous_fst.neg.mul continuous_snd)).mul
    (Real.continuous_sinc.comp continuous_snd)

/-- The sine accumulation based at R has bound 2, including singleton intervals. -/
theorem sine_accumulation_bound {R S : ℝ} (hRS : R ≤ S)
    (h : RealIntegrable Real.sin R S) : |realIntegral Real.sin h| ≤ 2 := by
  have hv := DampedSineIntegral.darboux_eq_sub_of_hasDerivAt hRS
    Real.continuous_cos.neg.continuousOn (fun x _ => by simpa only [neg_neg] using (Real.hasDerivAt_cos x).neg) h
  rw [hv]
  calc
    |-Real.cos S - -Real.cos R| ≤ |-Real.cos S| + |-Real.cos R| := abs_sub _ _
    _ ≤ 2 := by simp only [abs_neg]; linarith [Real.abs_cos_le_one S, Real.abs_cos_le_one R]

def weight (a x : ℝ) : ℝ := Real.exp (-a*x) / x
def weightDerivative (a x : ℝ) : ℝ :=
  ((-a) * Real.exp (-a*x) * x - Real.exp (-a*x)) / x^2

theorem weight_derivative (a : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (weight a) (weightDerivative a x) x := by
  convert! ((((hasDerivAt_id x).const_mul (-a)).exp).div (hasDerivAt_id x) hx) using 1
  dsimp only [weightDerivative, id_eq]
  ring

theorem weight_continuousOn (a : ℝ) {R S : ℝ} (hR : 0 < R) :
    ContinuousOn (weight a) (Icc R S) ∧
    ContinuousOn (weightDerivative a) (Icc R S) := by
  have hn : ∀ x ∈ Icc R S, x ≠ 0 := fun x hx => ne_of_gt (hR.trans_le hx.1)
  have he : Continuous (fun x : ℝ => Real.exp (-a*x)) := by fun_prop
  exact ⟨he.continuousOn.div continuousOn_id hn,
    ((continuousOn_const.mul he.continuousOn).mul continuousOn_id |>.sub he.continuousOn).div
      (continuousOn_id.pow 2) (fun x hx => pow_ne_zero _ (hn x hx))⟩

theorem weight_antitone {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R) :
    AntitoneOn (weight a) (Ici R) := by
  intro x hx y hy hxy
  have hxpos := hR.trans_le hx
  have hypos := hR.trans_le hy
  change Real.exp (-a*y) / y ≤ Real.exp (-a*x) / x
  calc
    _ ≤ Real.exp (-a*x) / y := div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr (by nlinarith)) hypos.le
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le hxpos hxy

theorem finite_tail_bound :
    Specs.SingleVariableAnalysis.Ch18.DirichletIntegral.finiteTailBound := by
  intro a ha R hR S hRS
  have hc := weight_continuousOn a (S := S) hR
  obtain ⟨hi, hb⟩ := weighted_tail_bound_sharp .real Real.sin (weight a) (weightDerivative a)
    hRS (realIntegrable_of_continuousOn hRS Real.continuous_sin.continuousOn)
    (by norm_num : (0 : ℝ) ≤ 2)
    (fun x h => sine_accumulation_bound x.property.1 h)
    hc.1 hc.2 (fun x hx => weight_derivative a (ne_of_gt (hR.trans hx.1)))
    (fun x hx => div_nonneg (Real.exp_pos _).le (hR.trans_le hx.1).le)
    ((weight_antitone ha hR).mono (fun _ hx => hx.1))
  obtain ⟨hd, hv⟩ := realIntegral_congr_on hi (g := damped a) (fun x hx => by
    change Real.sin x * (Real.exp (-a*x) / x) = Real.exp (-a*x) * Real.sinc x
    rw [Real.sinc_of_ne_zero (ne_of_gt (hR.trans_le hx.1))]
    ring)
  refine ⟨hd, ?_⟩
  change |realIntegral (damped a) hd| ≤ 2 / R
  rw [hv]
  apply hb.trans
  change 2 * (Real.exp (-a*R) / R) ≤ 2 / R
  have he : Real.exp (-a*R) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  calc
    2 * (Real.exp (-a*R) / R) ≤ 2 * (1 / R) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he hR.le) (by norm_num)
    _ = 2 / R := by ring

/-- Compact uniform continuity applies to the removable value at x = 0 too. -/
theorem compact_uniform :
    Specs.SingleVariableAnalysis.Ch18.DirichletIntegral.compactUniform := by
  intro R hR ε hε
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (joint_continuous.continuousOn (s := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) R))
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨min 1 δ, lt_min zero_lt_one hδ, fun a ha haδ x hx => ?_⟩
  have haa : a ∈ Icc (0 : ℝ) 1 := ⟨ha, (haδ.trans_le (min_le_left _ _)).le⟩
  have hdist : dist (a, x) (0, x) < δ := by
    simpa only [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, abs_of_nonneg ha, max_eq_left ha] using haδ.trans_le (min_le_right 1 δ)
  simpa only [Real.dist_eq, damped_zero] using hd (a,x) ⟨haa,hx⟩ (0,x) ⟨⟨le_rfl, zero_le_one⟩,hx⟩ hdist

/-- The Cauchy criterion supplies convergence for the undamped section as well.
Its threshold is independent of a, and the finite starting point may vary. -/
theorem uniform_convergence_from (b : ℝ) (hb : 0 ≤ b) :
    RightUniformConverges .real (Ici (0 : ℝ)) (fun x a => damped a.val x) b ⊤ := by
  have hreg : RightFamilyRegular .real (Ici (0 : ℝ)) (fun x a => damped a.val x) b ⊤ :=
    ⟨WithTop.coe_lt_top _, fun a => ⟨WithTop.coe_lt_top _, fun R =>
      realIntegrable_of_continuousOn R.property.1.le
        (DampedSineIntegral.continuous_extension.1 a.val).continuousOn⟩⟩
  apply (right_uniform_cauchy_criterion .real _ _ b ⊤ hreg).mpr
  intro ε hε
  let r : RightIndex b ⊤ := ⟨max (b+1) (2/ε),
    (lt_add_one b).trans_le (le_max_left _ _), WithTop.coe_lt_top _⟩
  refine ⟨r, fun a R S hrR hRS => ?_⟩
  obtain ⟨hi, hbound⟩ := finite_tail_bound a.val a.property R.val
    (hb.trans_lt R.property.1) S.val hRS.le
  refine ⟨hi, hbound.trans_lt ?_⟩
  apply (div_lt_iff₀ (hb.trans_lt R.property.1)).mpr
  have hr : 2/ε < R.val := (le_max_right (b+1) (2/ε)).trans_lt hrR
  nlinarith [(div_lt_iff₀ hε).mp hr]

theorem uniform_truncations :
    Specs.SingleVariableAnalysis.Ch18.DirichletIntegral.uniformTruncations :=
  uniform_convergence_from 0 le_rfl

theorem infinite_tail_bound :
    Specs.SingleVariableAnalysis.Ch18.DirichletIntegral.infiniteTailBound := by
  intro a ha R hR
  obtain ⟨F, hF⟩ := uniform_convergence_from R hR.le
  have hpoint := right_uniform_pointwise .real _ _ R ⊤ F hF ⟨a, ha⟩
  let hc : RightConverges .real (damped a) R ⊤ := ⟨F ⟨a,ha⟩, hpoint⟩
  exact ⟨RightIntegral .real (damped a) R ⊤ hc,
    right_integral_hasValue .real _ R ⊤ hc,
    right_integral_norm_le .real _ hc (fun S hRS => finite_tail_bound a ha R hR S hRS)⟩

/-- Restriction to [0,1] makes parameter zero a relative endpoint. Uniform
improper continuity uses a single late truncation and its proper continuity. -/
theorem removal_of_damping :
    Specs.SingleVariableAnalysis.Ch18.DirichletIntegral.removalOfDamping := by
  obtain ⟨F, hF⟩ := uniform_truncations
  let lift : Icc (0 : ℝ) 1 → Ici (0 : ℝ) := fun a => ⟨a.val, a.property.1⟩
  let G : Icc (0 : ℝ) 1 → ℝ := fun a => F (lift a)
  let f : ℝ → Icc (0 : ℝ) 1 → ℝ := fun x a => damped a.val x
  have hreg : RightFamilyRegular .real (Icc (0 : ℝ) 1) f 0 ⊤ :=
    ⟨WithTop.coe_lt_top _, fun a => hF.1.2 (lift a)⟩
  have hlim : RightUniformHasIntegral .real (Icc (0 : ℝ) 1) f 0 ⊤ G := by
    refine ⟨hreg, fun ε hε => ?_⟩
    obtain ⟨r, hr⟩ := hF.2 ε hε
    exact ⟨r, fun R hrR a => hr R hrR (lift a)⟩
  let z : Icc (0 : ℝ) 1 := ⟨0, ⟨le_rfl, zero_le_one⟩⟩
  let z' : (univ : Set (Icc (0 : ℝ) 1)) := ⟨z, mem_univ _⟩
  have hG : ContinuousAt G z := by
    apply right_improper_continuity .real univ z' (by simp) f 0 ⊤ G
      ⟨hreg.1, fun a => hreg.2 a.val⟩
      (by
        refine ⟨⟨hreg.1, fun a => hreg.2 a.val⟩, fun ε hε => ?_⟩
        obtain ⟨r, hr⟩ := hlim.2 ε hε
        exact ⟨r, fun R hrR a => hr R hrR a.val⟩)
    intro R
    apply (continuous_integral_on_subset_of_rectangle .real R.property.1.le zero_le_one f
      (joint_continuous.comp (continuous_snd.subtype_val.prodMk continuous_fst.subtype_val))
      univ (fun a => (hreg.2 a.val).2 R)).continuousAt
  have hzero : RightHasIntegral .real Real.sinc 0 ⊤ (G z) := by
    have hp := right_uniform_pointwise .real _ _ 0 ⊤ F hF (lift z)
    simpa only [lift, z, damped_zero] using hp
  refine ⟨G z, hzero, Metric.tendsto_nhds.mpr (fun ε hε => ?_)⟩
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hG ε hε
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (lt_min hδ zero_lt_one)).filter_mono nhdsWithin_le_nhds] with a ha haδ
  have ha' : 0 < a := ha
  let t : Icc (0 : ℝ) 1 := ⟨a, ⟨ha'.le, (haδ.trans_le (min_le_right δ 1)).le⟩⟩
  have hdist : dist t z < δ := by
    simpa only [Subtype.dist_eq, Real.dist_eq, t, z, sub_zero, abs_of_pos ha']
      using haδ.trans_le (min_le_left δ 1)
  have he : G t = DampedSineIntegral.J a :=
    right_unique .real (damped a) 0 ⊤ _ _
      (right_uniform_pointwise .real _ _ 0 ⊤ F hF (lift t))
      (DampedSineIntegral.absolute_convergence a ha').1
  change dist (DampedSineIntegral.J a) (G z) < ε
  rw [← he]
  exact hd hdist

theorem evaluation :
    Specs.SingleVariableAnalysis.Ch18.DirichletIntegral.evaluation := by
  obtain ⟨L, hL, hlim⟩ := removal_of_damping
  have ht : Tendsto (fun a : ℝ => Real.pi/2 - Real.arctan a)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi/2)) := by
    simpa only [Real.arctan_zero, sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.pi/2)
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi/2))).sub
        (Real.continuous_arctan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hJ : Tendsto DampedSineIntegral.J (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi/2)) := by
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with a ha
    change Real.pi/2 - Real.arctan a =
      Specs.SingleVariableAnalysis.Ch18.DampedSineIntegral.integralValue a
    rw [DampedSineIntegral.evaluation a ha, one_div, Real.arctan_inv_of_pos ha]
  have he : L = Real.pi/2 := tendsto_nhds_unique hlim hJ
  change RightHasIntegral .real Real.sinc 0 ⊤ (Real.pi/2)
  exact he ▸ hL

end SingleVariableAnalysis.DirichletIntegral
