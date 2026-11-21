import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.ConvolutionYoung
import MathGenome.Internal.RealAnalysis.D11.Ch11.ConvolutionBound
import Mathlib.Analysis.Convolution

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Convolution
namespace D11.Ch11.ConvolutionYoung
open D11.Ch03 D11.Ch03.LebesgueMeasures
open Specs.D11.Ch03.LebesgueMeasures
open ConvolutionBound (convolution)

abbrev l1Convolution : Specs.D11.Ch11.ConvolutionYoung.l1Convolution_type :=
  Specs.D11.Ch11.ConvolutionYoung.l1Convolution_value

theorem young : Specs.D11.Ch11.ConvolutionYoung.young := ConvolutionBound.young
theorem representative_independence : Specs.D11.Ch11.ConvolutionYoung.representative_independence :=
  ConvolutionBound.representative_independence
theorem quotient_bound : Specs.D11.Ch11.ConvolutionYoung.quotient_bound := ConvolutionBound.quotient_bound
theorem quotient_independence : Specs.D11.Ch11.ConvolutionYoung.quotient_independence :=
  ConvolutionBound.quotient_independence

variable {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- On Borel functions the completed integral equals the Borel integral,
including the shared zero convention for nonintegrable sections. -/
lemma convolution_eq_borel {k f : Point d → 𝕜} (hk : Measurable k) (hf : Measurable f) :
    convolution d k f = MeasureTheory.convolution k f (ContinuousLinearMap.mul 𝕜 𝕜) volume := by
  funext x
  change (∫ y, k y * f (x-y) ∂lebesgue_value d) = ∫ y, k y * f (x-y) ∂volume
  have H := integral_trim (μ := lebesgue_value d) (native_borel_le d)
    ((hk.mul (hf.comp (measurable_id.const_sub x))).stronglyMeasurable)
  rwa [borel_restriction d (native_borel_le d)] at H

lemma integrable_borel_of_completed {k : Point d → 𝕜} (hk : Measurable k)
    (h : letI := lebesgueSpace_value d; MemLp k 1 (lebesgue_value d)) :
    Integrable k volume := by
  have H := (memLp_one_iff_integrable.mp h).trim (native_borel_le d) hk.stronglyMeasurable
  exact Eq.mp (congrArg (fun μ : Measure (Point d) => Integrable k μ)
    (borel_restriction d (native_borel_le d))) H

/-- The native convolution theorem has genuine absolute-integrability premises.
The norm convolution supplies these premises almost everywhere. -/
lemma borel_associative {k f g : Point d → 𝕜}
    (hk : Integrable k volume) (hf : Integrable f volume) (hg : Integrable g volume) :
    MeasureTheory.convolution (MeasureTheory.convolution k f (ContinuousLinearMap.mul 𝕜 𝕜) volume)
        g (ContinuousLinearMap.mul 𝕜 𝕜) volume =ᵐ[volume]
      MeasureTheory.convolution k (MeasureTheory.convolution f g (ContinuousLinearMap.mul 𝕜 𝕜) volume)
        (ContinuousLinearMap.mul 𝕜 𝕜) volume := by
  let M := ContinuousLinearMap.mul 𝕜 𝕜
  let R := ContinuousLinearMap.mul ℝ ℝ
  have hfg := hk.ae_convolution_exists M hf
  have hng := hf.norm.ae_convolution_exists R hg.norm
  have hi := hf.norm.integrable_convolution R hg.norm
  filter_upwards [hk.norm.ae_convolution_exists R hi] with x hx
  exact MeasureTheory.convolution_assoc M M M M (fun a b c => mul_assoc a b c)
    hk.aestronglyMeasurable hf.aestronglyMeasurable hg.aestronglyMeasurable hfg hng hx

lemma borel_convolution_measurable {k f : Point d → 𝕜}
    (hk : Measurable k) (hf : Measurable f) :
    Measurable (MeasureTheory.convolution k f (ContinuousLinearMap.mul 𝕜 𝕜) volume) :=
  ((hk.comp measurable_snd).mul
    (hf.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable

section Completed
local instance : MeasurableSpace (Point d) := lebesgueSpace_value d

/-- First pass to Borel versions, apply absolute Fubini there, then return to
arbitrary completed-measurable versions. Joint subtraction into the completed
sigma-algebra is never asserted to be product-measurable. -/
lemma associative {k f g : Point d → 𝕜}
    (hk : Measurable k) (hf : Measurable f) (hg : Measurable g)
    (hk1 : MemLp k 1 (lebesgue_value d)) (hf1 : MemLp f 1 (lebesgue_value d))
    (hg1 : MemLp g 1 (lebesgue_value d)) :
    convolution d (convolution d k f) g =ᵐ[lebesgue_value d]
      convolution d k (convolution d f g) := by
  obtain ⟨kB, hkB, hkkB⟩ := ConvolutionBound.borel_version k hk
  obtain ⟨fB, hfB, hffB⟩ := ConvolutionBound.borel_version f hf
  obtain ⟨gB, hgB, hggB⟩ := ConvolutionBound.borel_version g hg
  have hkb := integrable_borel_of_completed hkB (hk1.ae_eq hkkB)
  have hfb := integrable_borel_of_completed hfB (hf1.ae_eq hffB)
  have hgb := integrable_borel_of_completed hgB (hg1.ae_eq hggB)
  have hKF := (representative_independence d 𝕜 k kB f fB hkkB hffB).2.trans
    (convolution_eq_borel hkB hfB)
  have hFG := (representative_independence d 𝕜 f fB g gB hffB hggB).2.trans
    (convolution_eq_borel hfB hgB)
  have hl := (representative_independence d 𝕜 _ _ g gB
    (EventuallyEq.of_eq hKF) hggB).2.trans
      (convolution_eq_borel (borel_convolution_measurable hkB hfB) hgB)
  have hr := (representative_independence d 𝕜 k kB _ _
    hkkB (EventuallyEq.of_eq hFG)).2.trans
      (convolution_eq_borel hkB (borel_convolution_measurable hfB hgB))
  refine (EventuallyEq.of_eq hl).trans (EventuallyEq.trans ?_ (EventuallyEq.of_eq hr.symm))
  apply ae_iff.mpr
  exact (EuclideanRegularity.lebesgue_eq_volume d _).trans
    (ae_iff.mp (borel_associative hkb hfb hgb))

/-- Reflection-translation proves symmetry, even at zero-extended sections. -/
lemma commutative (k f : Point d → 𝕜) : convolution d k f = convolution d f k := by
  funext x
  change (∫ y, k y * f (x-y) ∂lebesgue_value d) = _
  let e : Point d ≃ᵐ Point d :=
    { toEquiv := ⟨fun y => x-y, fun y => x-y, fun y => sub_sub_cancel x y,
        fun y => sub_sub_cancel x y⟩
      measurable_toFun := (ConvolutionBound.measurePreserving_const_sub x).measurable
      measurable_invFun := (ConvolutionBound.measurePreserving_const_sub x).measurable }
  rw [← (ConvolutionBound.measurePreserving_const_sub x).integral_comp e.measurableEmbedding
    (fun y => k y * f (x-y))]
  simp only [sub_sub_cancel, mul_comm]
  rfl

lemma l1_mem (k f : Lp 𝕜 1 (lebesgue_value d)) :
    MemLp (convolution d (k : Point d → 𝕜) (f : Point d → 𝕜)) 1 (lebesgue_value d) :=
  (young d 𝕜 1 le_rfl k f (Lp.stronglyMeasurable k).measurable
    (Lp.stronglyMeasurable f).measurable (Lp.memLp k) (Lp.memLp f)).2.2.1

lemma l1_coe (k f : Lp 𝕜 1 (lebesgue_value d)) :
    (l1Convolution d 𝕜 k f : Point d → 𝕜) =ᵐ[lebesgue_value d]
      convolution d (k : Point d → 𝕜) (f : Point d → 𝕜) := by
  unfold l1Convolution Specs.D11.Ch11.ConvolutionYoung.l1Convolution_value
  rw [dite_eq_left (l1_mem k f)]
  exact MemLp.coeFn_toLp _

theorem l1_representatives : Specs.D11.Ch11.ConvolutionYoung.l1_representatives := by
  intro d _ 𝕜 _ _ _
  let := lebesgueSpace_value d
  intro k f hk hf hk1 hf1
  obtain ⟨hi, hm, hc, _⟩ := young d 𝕜 1 le_rfl k f hk hf hk1 hf1
  refine ⟨hi, hm, hc, ?_⟩
  apply Lp.ext
  exact (l1_coe (hk1.toLp k) (hf1.toLp f)).trans
    ((EventuallyEq.of_eq (representative_independence d 𝕜 _ k _ f
      (MemLp.coeFn_toLp hk1) (MemLp.coeFn_toLp hf1)).2).trans
        (MemLp.coeFn_toLp hc).symm)

lemma l1_commutative (k f : Lp 𝕜 1 (lebesgue_value d)) :
    l1Convolution d 𝕜 k f = l1Convolution d 𝕜 f k := by
  apply Lp.ext
  exact (l1_coe k f).trans ((EventuallyEq.of_eq (commutative _ _)).trans (l1_coe f k).symm)

lemma l1_add_left (k f g : Lp 𝕜 1 (lebesgue_value d)) :
    l1Convolution d 𝕜 (k+f) g = l1Convolution d 𝕜 k g + l1Convolution d 𝕜 f g := by
  have hi := (young d 𝕜 1 le_rfl k g (Lp.stronglyMeasurable k).measurable
    (Lp.stronglyMeasurable g).measurable (Lp.memLp k) (Lp.memLp g)).1
  have hi' := (young d 𝕜 1 le_rfl f g (Lp.stronglyMeasurable f).measurable
    (Lp.stronglyMeasurable g).measurable (Lp.memLp f) (Lp.memLp g)).1
  apply Lp.ext
  have H := (representative_independence d 𝕜 _ _ _ _
    (Lp.coeFn_add k f) (ae_eq_rfl (f := (g : Point d → 𝕜)))).2
  refine (l1_coe (k+f) g).trans ((EventuallyEq.of_eq H).trans ?_)
  refine EventuallyEq.trans ?_ (((l1_coe k g).symm.add (l1_coe f g).symm).trans
    (Lp.coeFn_add _ _).symm)
  filter_upwards [hi, hi'] with x hx hx'
  exact (ConvolutionBound.bilinearity d 𝕜 k f g g x).1 hx hx'

lemma l1_smul_left (c : 𝕜) (k f : Lp 𝕜 1 (lebesgue_value d)) :
    l1Convolution d 𝕜 (c • k) f = c • l1Convolution d 𝕜 k f := by
  apply Lp.ext
  have H := (representative_independence d 𝕜 _ _ _ _
    (Lp.coeFn_smul c k) (ae_eq_rfl (f := (f : Point d → 𝕜)))).2
  refine (l1_coe (c • k) f).trans ((EventuallyEq.of_eq H).trans ?_)
  refine EventuallyEq.trans ?_ (((l1_coe k f).symm.const_smul c).trans (Lp.coeFn_smul c _).symm)
  exact Eventually.of_forall fun x => (ConvolutionBound.bilinearity d 𝕜 k k f f x).2.2.1 c

lemma l1_associative (k f g : Lp 𝕜 1 (lebesgue_value d)) :
    l1Convolution d 𝕜 (l1Convolution d 𝕜 k f) g =
      l1Convolution d 𝕜 k (l1Convolution d 𝕜 f g) := by
  apply Lp.ext
  have hl := (representative_independence d 𝕜 _ _ _ _ (l1_coe k f)
    (ae_eq_rfl (f := (g : Point d → 𝕜)))).2
  have hr := (representative_independence d 𝕜 _ _ _ _
    (ae_eq_rfl (f := (k : Point d → 𝕜))) (l1_coe f g)).2
  exact (l1_coe (l1Convolution d 𝕜 k f) g).trans
    ((EventuallyEq.of_eq hl).trans ((associative
      (Lp.stronglyMeasurable k).measurable (Lp.stronglyMeasurable f).measurable
      (Lp.stronglyMeasurable g).measurable (Lp.memLp k) (Lp.memLp f) (Lp.memLp g)).trans
        ((EventuallyEq.of_eq hr.symm).trans (l1_coe k (l1Convolution d 𝕜 f g)).symm)))

lemma l1_norm (k f : Lp 𝕜 1 (lebesgue_value d)) :
    ‖l1Convolution d 𝕜 k f‖ ≤ ‖k‖ * ‖f‖ := by
  obtain ⟨hc, hb⟩ := quotient_bound d 𝕜 1 k f (Lp.stronglyMeasurable k).measurable
    (Lp.stronglyMeasurable f).measurable (Lp.memLp k) (Lp.memLp f)
  have he : l1Convolution d 𝕜 k f = hc.toLp (convolution d k f) := by
    apply Lp.ext
    exact (l1_coe k f).trans (MemLp.coeFn_toLp hc).symm
  rw [he]
  simpa only [Lp.toLp_coeFn] using hb

theorem l1_algebra : Specs.D11.Ch11.ConvolutionYoung.l1_algebra := by
  intro d _ 𝕜 _ _ _
  let := lebesgueSpace_value d
  dsimp only
  intro k f g
  refine ⟨l1_add_left k f g, ?_, fun c => l1_smul_left c k f, ?_,
    l1_commutative k f, l1_associative k f g, l1_norm k f⟩
  · exact (l1_commutative k (f+g)).trans ((l1_add_left f g k).trans
      (congrArg₂ (· + ·) (l1_commutative f k) (l1_commutative g k)))
  · intro c
    exact (l1_commutative k (c • f)).trans ((l1_smul_left c f k).trans
      (congrArg (c • ·) (l1_commutative f k)))

end Completed
end D11.Ch11.ConvolutionYoung
