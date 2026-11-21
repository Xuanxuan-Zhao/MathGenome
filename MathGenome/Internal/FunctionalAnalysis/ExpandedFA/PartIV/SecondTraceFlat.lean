import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SecondTraceFlat
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SharpTraceExtension

/-! Flat simultaneous boundary jets for `fa2:p4:second-trace`.
The even-mollifier formula has a uniform full second-order Sobolev bound.
Common-scale approximation preserves the actual weak gradient of the higher
fractional datum; completion then preserves both original coordinate traces.
The final representative identity is established in the ordinary Lp quotient.
-/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators

namespace ExpandedFA.PartIV.SecondTraceFlat
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open ExpandedFA.PartIV.SharpTraceExtension
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open SmoothLift

lemma jetCutoff_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) jetCutoff :=
  standardCutoff_contDiff

lemma jetCutoff_compactSupport : HasCompactSupport jetCutoff :=
  standardCutoff_compactSupport

@[simp] lemma jetCutoff_zero : jetCutoff 0 = 1 := standardCutoff_zero

lemma jetCutoff_eventually_one : jetCutoff =ᶠ[𝓝 (0 : ℝ)] fun _ => 1 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with t ht
  exact (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)).one_of_mem_closedBall
    (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp ht)))

lemma jetCutoff_hasDerivAt_zero : HasDerivAt jetCutoff 0 0 :=
  (hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq jetCutoff_eventually_one

lemma jetMollifier_contDiff (n : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (jetMollifier n) := standardMollifier_contDiff n

lemma jetMollifier_compactSupport (n : ℕ) : HasCompactSupport (jetMollifier n) :=
  standardMollifier_compactSupport n

@[simp] lemma jetMollifier_integral (n : ℕ) : ∫ y, jetMollifier n y = 1 :=
  standardMollifier_integral n

@[simp] lemma jetMollifier_neg (n : ℕ) (y : Domain n) :
    jetMollifier n (-y) = jetMollifier n y := ContDiffBump.normed_neg _ _

/-- Oddness of an even kernel times a fixed directional linear map gives
the exact cancellation needed at height zero. -/
lemma integral_even_kernel_linear_zero {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (hρ : ∀ y, ρ (-y) = ρ y) (L : Domain n →L[ℝ] 𝕜) :
    (∫ y, ρ y • L (-y)) = 0 := by
  have heq := integral_neg_eq_self (fun y : Domain n => ρ y • L (-y)) volume
  have hodd : (fun y : Domain n => ρ (-y) • L (-(-y))) =
      fun y => -(ρ y • L (-y)) := by
    funext y
    simp [hρ]
  rw [hodd, integral_neg] at heq
  exact CharZero.eq_neg_self_iff.mp heq.symm

/-- The first average has zero inward derivative at the boundary, for every
smooth compactly supported datum. No normal datum is imposed on it. -/
lemma average_hasDerivAt_zero_of_even {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρe : ∀ y, ρ (-y) = ρ y) (f : Domain n → 𝕜)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x : Domain n) :
    HasDerivAt (fun t : ℝ => average ρ f (x, t)) 0 0 := by
  have hd := average_hasDerivAt_normal ρ f hρ hρc hf hfc x 0
  simpa only [zero_smul, sub_zero,
    integral_even_kernel_linear_zero ρ hρe (fderiv ℝ f x)] using hd

lemma flatJet_eq {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f h : Domain n → 𝕜)
    (z : Domain n × ℝ) :
    flatJet χ ρ f h z = flatLift χ ρ f z + z.2 • flatLift χ ρ h z := by
  simp only [flatJet, flatLift, SmoothLift.average, smul_add, smul_smul]
  congr 1
  rw [mul_comm]

lemma flatJet_contDiff {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f h : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (flatJet χ ρ f h) := by
  rw [show flatJet χ ρ f h = (fun z => flatLift χ ρ f z + z.2 • flatLift χ ρ h z) from
    funext (flatJet_eq χ ρ f h)]
  exact (flatLift_contDiff χ ρ f hχ hρ hρc hf).add
    (contDiff_snd.smul (flatLift_contDiff χ ρ h hχ hρ hρc hh))

lemma flatJet_hasCompactSupport {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f h : Domain n → 𝕜)
    (hχc : HasCompactSupport χ) (hρc : HasCompactSupport ρ)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h) :
    HasCompactSupport (flatJet χ ρ f h) := by
  rw [show flatJet χ ρ f h = (fun z => flatLift χ ρ f z + z.2 • flatLift χ ρ h z) from
    funext (flatJet_eq χ ρ f h)]
  exact (flatLift_hasCompactSupport χ ρ f hχc hρc hfc).add
    ((flatLift_hasCompactSupport χ ρ h hχc hρc hhc).smul_left
      (f := fun z : Domain n × ℝ => z.2))

@[simp] lemma flatJet_zero_height {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f h : Domain n → 𝕜)
    (hχ : χ 0 = 1) (hρ : ∫ y, ρ y = 1) (x : Domain n) :
    flatJet χ ρ f h (x, 0) = f x := by
  simp [flatJet, integral_smul_const, hχ, hρ]

/-- Exact simultaneous classical boundary jets of the signed-scale formula.
The only cancellation hypothesis is evenness of the tangential kernel. -/
lemma flatJet_hasDerivAt_zero {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f h : Domain n → 𝕜)
    (hχ : χ 0 = 1) (hχd : HasDerivAt χ 0 0)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρe : ∀ y, ρ (-y) = ρ y) (hρm : ∫ y, ρ y = 1)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hh : ContDiff ℝ 1 h) (hhc : HasCompactSupport h) (x : Domain n) :
    HasDerivAt (fun t : ℝ => flatJet χ ρ f h (x, t)) (h x) 0 := by
  have hA := average_hasDerivAt_zero_of_even ρ hρ hρc hρe f hf hfc x
  have hB := average_hasDerivAt_normal ρ h hρ hρc hh hhc x 0
  have hd := hχd.smul (hA.add ((hasDerivAt_id (0 : ℝ)).smul hB))
  change HasDerivAt (fun t : ℝ => χ t •
    (SmoothLift.average ρ f (x, t) + t • SmoothLift.average ρ h (x, t))) _ 0 at hd
  simpa only [flatJet, SmoothLift.average, Pi.smul_apply', Pi.add_apply, id_eq, hχ, zero_smul,
    zero_add, add_zero, one_smul, sub_zero, integral_smul_const, hρm] using hd

lemma jetFunction_contDiff {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (f h : Domain n → 𝕜)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (jetFunction i f h) :=
  (flatJet_contDiff jetCutoff (jetMollifier n) f h jetCutoff_contDiff
    (jetMollifier_contDiff n) (jetMollifier_compactSupport n) hf hh).comp
      (flatCoordinates_contDiff i)

lemma jetFunction_hasCompactSupport {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (f h : Domain n → 𝕜)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h) :
    HasCompactSupport (jetFunction i f h) :=
  (flatJet_hasCompactSupport jetCutoff (jetMollifier n) f h jetCutoff_compactSupport
    (jetMollifier_compactSupport n) hfc hhc).comp_isClosedEmbedding
      (flatCoordinates i).isClosedEmbedding

@[simp] lemma jetFunction_boundary {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (f h : Domain n → 𝕜) (x : Domain n) :
    jetFunction i f h (i.insertNth 0 x) = f x := by
  simp only [jetFunction, Fin.removeNth_insertNth, Fin.insertNth_apply_same]
  exact flatJet_zero_height _ _ _ _ jetCutoff_zero (jetMollifier_integral n) x

lemma jetFunction_normal_boundary {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (f h : Domain n → 𝕜)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (hhc : HasCompactSupport h) (x : Domain n) :
    fderiv ℝ (jetFunction i f h) (i.insertNth 0 x) (coordinateVector i) = h x := by
  have hd := flatJet_hasDerivAt_zero jetCutoff (jetMollifier n) f h jetCutoff_zero
    jetCutoff_hasDerivAt_zero (jetMollifier_contDiff n).continuous
    (jetMollifier_compactSupport n) (jetMollifier_neg n) (jetMollifier_integral n)
    (hf.of_le (by simp)) hfc (hh.of_le (by simp)) hhc x
  have hcurve := ((jetFunction_contDiff i f h hf hh).differentiable (by simp)
    (coordinateLine i (transverseFinEquiv i x) 0)).hasFDerivAt.comp_hasDerivAt 0
      (coordinateLine_hasDerivAt i (transverseFinEquiv i x) 0)
  have heq : (jetFunction i f h ∘ coordinateLine i (transverseFinEquiv i x)) =
      (fun t => flatJet jetCutoff (jetMollifier n) f h (x, t)) := by
    funext t
    dsimp only [Function.comp_apply]
    rw [coordinateLine_transverseFinEquiv]
    simp [jetFunction]
  rw [heq] at hcurve
  simpa only [coordinateLine_transverseFinEquiv] using hcurve.unique hd

/-- A globally smooth compactly supported function restricted to an arbitrary
open set, in the existing derivative graph at every integer order. Compact
support is not required to lie inside the open set. -/
def smoothCompactSobolev {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Domain d → 𝕜) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hfc : HasCompactSupport f) : SpaceValue 𝕜 d Ω m p :=
  C1Extension.restrictSobolev (le_top : Ω ≤ ⊤)
    (testToSobolev m (⟨f, hf, hfc, subset_univ _⟩ : Tests 𝕜 ⊤))

lemma smoothCompactSobolev_coe {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Domain d → 𝕜) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hfc : HasCompactSupport f) (α : DerivativeIndex d m) :
    (smoothCompactSobolev Ω m p f hf hfc).val α =ᵐ[
      volume.restrict (Ω : Set (Domain d))] Smoothing.classicalDerivative α f := by
  let φ : Tests 𝕜 (⊤ : Opens (Domain d)) := ⟨f, hf, hfc, subset_univ _⟩
  have hr := C1Extension.restrictSobolev_coe (le_top : Ω ≤ ⊤)
    (testToSobolev (p := p) m φ) α
  have hc := testToDomainLp_coe (p := p)
    (testPartialCLM (multiIndexWord (natIndex α)).reverse φ)
  have hc' : (testToSobolev (p := p) m φ).val α =ᵐ[volume]
      Smoothing.classicalDerivative α f := by
    change testToDomainLp (p := p) (testPartialCLM (multiIndexWord (natIndex α)).reverse φ)
      =ᵐ[volume] partialFunction (multiIndexWord (natIndex α)).reverse f
    have hc' := hc
    simp only [Opens.coe_top, Measure.restrict_univ] at hc'
    filter_upwards [hc'] with x hx
    rw [hx]
    exact congrFun (testPartial_formula 𝕜 d ⊤ (multiIndexWord (natIndex α)).reverse φ) x
  exact hr.trans (ae_restrict_of_ae hc')

lemma classicalDerivative_zero {𝕜 : Type} [RCLike 𝕜] {d m : ℕ}
    (f : Domain d → 𝕜) : Smoothing.classicalDerivative (zeroIndex d m) f = f := by
  have hz : multiIndexWord (natIndex (zeroIndex d m)) = [] := by
    apply List.length_eq_zero_iff.mp
    simp [natIndex, zeroIndex]
  simp [Smoothing.classicalDerivative, hz, partialFunction]

lemma classicalDerivative_normal {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Domain d → 𝕜) (i : Fin d) :
    Smoothing.classicalDerivative (normalIndex i) f =
      fun x => fderiv ℝ f x (coordinateVector i) := by
  have hi : natIndex (normalIndex i) = Pi.single i 1 := by
    funext j
    by_cases h : j = i
    · subst j; simp [natIndex, normalIndex]
    · simp [natIndex, normalIndex, h]
  simp [Smoothing.classicalDerivative, hi, multiIndexWord_single, partialFunction]

/-- The explicit smooth simultaneous-jet lift in the actual order-two graph.
Its uniform full-norm estimate is proved below. -/
def smoothJetLift {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (i : Fin (n + 1))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f h : Domain n → 𝕜)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (hhc : HasCompactSupport h) :
    SpaceValue 𝕜 (n + 1) (upper i) 2 p :=
  smoothCompactSobolev (upper i) 2 p (jetFunction i f h)
    (jetFunction_contDiff i f h hf hh) (jetFunction_hasCompactSupport i f h hfc hhc)

lemma smoothJetLift_coe {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (i : Fin (n + 1))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f h : Domain n → 𝕜)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (hhc : HasCompactSupport h)
    (α : DerivativeIndex (n + 1) 2) :
    (smoothJetLift i p f h hf hfc hh hhc).val α =ᵐ[
      volume.restrict (upper i : Set (Domain (n + 1)))]
        Smoothing.classicalDerivative α (jetFunction i f h) :=
  smoothCompactSobolev_coe _ _ _ _ _ _ _

/-- Both original coordinate traces of the smooth W^{2,p} lift have the
prescribed values, including the inward sign of the derivative datum. -/
theorem smoothJetLift_boundary_jets {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (f h : Domain n → 𝕜)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (hhc : HasCompactSupport h)
    (g k : Lp 𝕜 p (volume : Measure (Domain n)))
    (hg : g =ᵐ[volume] f) (hk : k =ᵐ[volume] h)
    (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) (hT : CoordinateTraceCondition i T) :
    HasBoundaryJets i T (smoothJetLift i p f h hf hfc hh hhc) g k := by
  let F := jetFunction i f h
  have hF := jetFunction_contDiff i f h hf hh
  have hFc := jetFunction_hasCompactSupport i f h hfc hhc
  let D : Domain (n + 1) → 𝕜 := fun x => fderiv ℝ F x (coordinateVector i)
  have hD : ContDiff ℝ (↑(⊤ : ℕ∞)) D :=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  have hDc : HasCompactSupport D := hFc.fderiv_apply ℝ (coordinateVector i)
  let v := smoothCompactSobolev (upper i) 1 p F hF hFc
  let w := smoothCompactSobolev (upper i) 1 p D hD hDc
  have hv : v.val (zeroIndex (n + 1) 1) =ᵐ[
      volume.restrict (upper i : Set (Domain (n + 1)))] F := by
    simpa only [classicalDerivative_zero] using
      smoothCompactSobolev_coe (upper i) 1 p F hF hFc (zeroIndex (n + 1) 1)
  have hw : w.val (zeroIndex (n + 1) 1) =ᵐ[
      volume.restrict (upper i : Set (Domain (n + 1)))] D := by
    simpa only [classicalDerivative_zero] using
      smoothCompactSobolev_coe (upper i) 1 p D hD hDc (zeroIndex (n + 1) 1)
  refine ⟨v, w, ?_, ?_, ?_, ?_⟩
  · apply Lp.ext
    exact hv.trans (by simpa only [classicalDerivative_zero] using
      (smoothJetLift_coe i p f h hf hfc hh hhc (zeroIndex (n + 1) 2)).symm)
  · apply Lp.ext
    exact hw.trans (by simpa only [classicalDerivative_normal] using
      (smoothJetLift_coe i p f h hf hfc hh hhc (normalIndex i)).symm)
  · apply Lp.ext
    have ht := reindexedTrace_smooth i T hT v F (hF.of_le (by simp)) hv
    filter_upwards [ht, hg] with x hx hgx
    exact (hx.trans (jetFunction_boundary i f h x)).trans hgx.symm
  · apply Lp.ext
    have ht := reindexedTrace_smooth i T hT w D (hD.of_le (by simp)) hw
    filter_upwards [ht, hk] with x hx hkx
    exact (hx.trans (jetFunction_normal_boundary i f h hf hfc hh hhc x)).trans hkx.symm

open KernelEstimates

/-- A flat coordinate direction, including the inward normal. -/
def flatDirection {n : ℕ} : Option (Fin n) → Domain n × ℝ
  | none => (0, 1)
  | some j => (coordinateVector j, 0)

/-- Differentiating an ordinary scale average produces a mean-zero kernel
of order t^{-1}, for either type of coordinate direction. -/
def derivativeKernel {n : ℕ} (ρ : Domain n → ℝ) : Option (Fin n) → Domain n → ℝ
  | none => normalKernel ρ
  | some j => fun y => fderiv ℝ ρ y (coordinateVector j)

lemma normalKernel_contDiff {n : ℕ} (ρ : Domain n → ℝ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (normalKernel ρ) :=
  (contDiff_const.mul hρ).sub ((hρ.fderiv_right (by simp)).clm_apply contDiff_id)

lemma derivativeKernel_contDiff {n : ℕ} (ρ : Domain n → ℝ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (a : Option (Fin n)) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (derivativeKernel ρ a) := by
  cases a with
  | none => exact normalKernel_contDiff ρ hρ
  | some j => exact (hρ.fderiv_right (by simp)).clm_apply contDiff_const

lemma derivativeKernel_compactSupport {n : ℕ} (ρ : Domain n → ℝ)
    (hρc : HasCompactSupport ρ) (a : Option (Fin n)) :
    HasCompactSupport (derivativeKernel ρ a) := by
  cases a with
  | none => exact normalKernel_hasCompactSupport ρ hρc
  | some j => exact hρc.fderiv_apply ℝ (coordinateVector j)

lemma derivativeKernel_integral_zero {n : ℕ} (ρ : Domain n → ℝ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (a : Option (Fin n)) : (∫ y, derivativeKernel ρ a y) = 0 := by
  cases a with
  | none => exact normalKernel_integral ρ (hρ.of_le (by simp)) hρc
  | some j =>
    exact kernel_directional_integral_zero ρ hρc
      (hρ.of_le (by simp)) (coordinateVector j)

/-- The kernel after one derivative of t*(rho_t*h). Its second derivative
is an ordinary derivative kernel, regardless of the two chosen directions. -/
def firstNormalDataKernel {n : ℕ} (ρ : Domain n → ℝ) :
    Option (Fin n) → Domain n → ℝ
  | none => ρ + normalKernel ρ
  | some j => derivativeKernel ρ (some j)

lemma firstNormalDataKernel_contDiff {n : ℕ} (ρ : Domain n → ℝ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (b : Option (Fin n)) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (firstNormalDataKernel ρ b) := by
  cases b with
  | none => exact hρ.add (normalKernel_contDiff ρ hρ)
  | some j => exact derivativeKernel_contDiff ρ hρ (some j)

lemma firstNormalDataKernel_compactSupport {n : ℕ} (ρ : Domain n → ℝ)
    (hρc : HasCompactSupport ρ) (b : Option (Fin n)) :
    HasCompactSupport (firstNormalDataKernel ρ b) := by
  cases b with
  | none => exact hρc.add (normalKernel_hasCompactSupport ρ hρc)
  | some j => exact derivativeKernel_compactSupport ρ hρc (some j)

lemma average_kernel_add {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ σ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hσ : Continuous σ) (hσc : HasCompactSupport σ) (hf : Continuous f)
    (z : Domain n × ℝ) :
    SmoothLift.average (ρ + σ) f z = SmoothLift.average ρ f z + SmoothLift.average σ f z := by
  simp only [SmoothLift.average, Pi.add_apply, add_smul]
  exact integral_add (average_integrable ρ f hρ hρc hf z)
    (average_integrable σ f hσ hσc hf z)

open Metric

lemma average_hasDerivAt_normal_noncompact {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : (Domain n) → ℝ) (f : (Domain n) → 𝕜)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ 1 f) (x : Domain n) (t : ℝ) :
    HasDerivAt (fun r : ℝ => SmoothLift.average ρ f (x,r))
      (∫ z, ρ z • fderiv ℝ f (x - t • z) (-z)) t := by
  let K : Set (Domain n) :=
    (fun q : ℝ × (Domain n) => x - q.1 • q.2) '' (closedBall t 1 ×ˢ tsupport ρ)
  have hK : IsCompact K :=
    ((isCompact_closedBall t 1).prod hρc).image
      (continuous_const.sub (continuous_fst.smul continuous_snd))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (hf.continuous_fderiv one_ne_zero).continuousOn
  let F : ℝ → (Domain n) → 𝕜 := fun r z => ρ z • f (x - r • z)
  let F' : ℝ → (Domain n) → 𝕜 := fun r z => ρ z • fderiv ℝ f (x - r • z) (-z)
  let B : (Domain n) → ℝ := fun z => ‖ρ z‖ * M * ‖z‖
  have hF (r : ℝ) : Continuous (F r) := by dsimp [F]; fun_prop
  have hF' (r : ℝ) : Continuous (F' r) := by
    have hs : Continuous (fun z : Domain n => x - r • z) := by fun_prop
    exact hρ.smul (((hf.continuous_fderiv one_ne_zero).comp hs).clm_apply continuous_id.neg)
  have hBi : Integrable B := by
    apply ((hρ.norm.mul continuous_const).mul continuous_norm).integrable_of_hasCompactSupport
    exact hρc.norm.mul_right.mul_right
  have hbd : ∀ᵐ z ∂volume, ∀ r ∈ closedBall t 1, ‖F' r z‖ ≤ B z := by
    filter_upwards with z r hr
    by_cases hz : z ∈ tsupport ρ
    · dsimp [F', B]
      rw [norm_smul]
      simp only [Real.norm_eq_abs, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [norm_neg, mul_assoc] using
        ((fderiv ℝ f (x - r • z)).le_opNorm (-z)).trans
          (mul_le_mul_of_nonneg_right (hM _ ⟨(r,z), ⟨hr,hz⟩, rfl⟩) (norm_nonneg _))
    · have hz0 : ρ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [F', B, hz0]
  have hdiff : ∀ᵐ z ∂volume, ∀ r ∈ closedBall t 1, HasDerivAt (F · z) (F' r z) r := by
    filter_upwards with z r hr
    simpa only [F, F', Function.comp_def, Pi.smul_def, Pi.smul_apply, Pi.sub_apply, id_eq, one_smul, zero_sub] using
      (((hf.differentiable_one _).hasFDerivAt).comp_hasDerivAt r
        ((hasDerivAt_const r x).sub ((hasDerivAt_id r).smul_const z))).const_smul (ρ z)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := closedBall t 1) (μ := volume) (bound := B) (x₀ := t)
    (closedBall_mem_nhds t zero_lt_one) (Eventually.of_forall fun r => (hF r).aestronglyMeasurable)
    ((hF t).integrable_of_hasCompactSupport hρc.smul_right)
    (hF' t).aestronglyMeasurable hbd hBi hdiff
  exact h.2


lemma average_hasDerivAt_direction_noncompact {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : (Domain n) → ℝ) (f : (Domain n) → 𝕜)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ 1 f) (x v : Domain n) (t a : ℝ) :
    HasDerivAt (fun r : ℝ => SmoothLift.average ρ f (x + r • v,t + r * a))
      (∫ y, ρ y • fderiv ℝ f (x - t • y) (v - a • y)) 0 := by
  let K : Set (Domain n) :=
    (fun q : ℝ × (Domain n) => (x + q.1 • v) - (t + q.1 * a) • q.2) ''
      (closedBall 0 1 ×ˢ tsupport ρ)
  have hK : IsCompact K :=
    ((isCompact_closedBall 0 1).prod hρc).image (by fun_prop)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (hf.continuous_fderiv one_ne_zero).continuousOn
  let F : ℝ → (Domain n) → 𝕜 := fun r y => ρ y • f ((x + r • v) - (t + r * a) • y)
  let F' : ℝ → (Domain n) → 𝕜 := fun r y =>
    ρ y • fderiv ℝ f ((x + r • v) - (t + r * a) • y) (v - a • y)
  let B : (Domain n) → ℝ := fun y => ‖ρ y‖ * M * ‖v - a • y‖
  have hF (r : ℝ) : Continuous (F r) := by dsimp [F]; fun_prop
  have hF' (r : ℝ) : Continuous (F' r) := by
    have hs : Continuous (fun y : Domain n => (x + r • v) - (t + r * a) • y) := by fun_prop
    exact hρ.smul (((hf.continuous_fderiv one_ne_zero).comp hs).clm_apply
      (continuous_const.sub (continuous_id.const_smul a)))
  have hBi : Integrable B := by
    apply ((hρ.norm.mul continuous_const).mul
      (continuous_const.sub (continuous_id.const_smul a)).norm).integrable_of_hasCompactSupport
    exact hρc.norm.mul_right.mul_right
  have hbd : ∀ᵐ y ∂volume, ∀ r ∈ closedBall (0 : ℝ) 1, ‖F' r y‖ ≤ B y := by
    filter_upwards with y r hr
    by_cases hy : y ∈ tsupport ρ
    · dsimp [F', B]
      rw [norm_smul]
      simp only [Real.norm_eq_abs, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact ((fderiv ℝ f ((x + r • v) - (t + r * a) • y)).le_opNorm (v - a • y)).trans
        (mul_le_mul_of_nonneg_right (hM _ ⟨(r,y), ⟨hr,hy⟩, rfl⟩) (norm_nonneg _))
    · have hy0 : ρ y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [F', B, hy0]
  have hdiff : ∀ᵐ y ∂volume, ∀ r ∈ closedBall (0 : ℝ) 1,
      HasDerivAt (F · y) (F' r y) r := by
    filter_upwards with y r hr
    have hpath := ((hasDerivAt_const r x).add ((hasDerivAt_id r).smul_const v)).sub
      (((hasDerivAt_const r t).add ((hasDerivAt_id r).mul_const a)).smul_const y)
    have hdiff := ((hf.differentiable_one _).hasFDerivAt.comp_hasDerivAt r hpath).const_smul (ρ y)
    simpa only [F, F', Function.comp_def, zero_add, one_smul, one_mul, Pi.add_apply, Pi.sub_apply, Pi.smul_def, Pi.smul_apply, id_eq] using hdiff
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := closedBall (0 : ℝ) 1) (μ := volume) (bound := B) (x₀ := 0)
    (closedBall_mem_nhds 0 zero_lt_one) (Eventually.of_forall fun r => (hF r).aestronglyMeasurable)
    ((hF 0).integrable_of_hasCompactSupport hρc.smul_right)
    (hF' 0).aestronglyMeasurable hbd hBi hdiff
  simpa only [F, F', SmoothLift.average, zero_smul, add_zero, zero_mul] using h.2


lemma average_fderiv_direction_noncompact {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : (Domain n) → ℝ) (f : (Domain n) → 𝕜)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (x v : Domain n) (t a : ℝ) :
    fderiv ℝ (SmoothLift.average ρ f) (x,t) (v,a) =
      ∫ y, ρ y • fderiv ℝ f (x - t • y) (v - a • y) := by
  have hd := average_hasDerivAt_direction_noncompact ρ f hρ.continuous hρc
    (hf.of_le (by simp)) x v t a
  have hA := average_contDiff ρ f hρ hρc hf
  have hpath := ((hasDerivAt_const 0 x).add ((hasDerivAt_id (0 : ℝ)).smul_const v)).prodMk
    ((hasDerivAt_const 0 t).add ((hasDerivAt_id (0 : ℝ)).mul_const a))
  have hcomp := (hA.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0 hpath
  have heq := hcomp.unique hd
  simpa only [Pi.add_apply, Pi.smul_apply, id_eq,
    zero_add, one_smul, one_mul, zero_smul, add_zero, zero_mul] using heq


lemma average_fderiv_kernel {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (z : Domain n × ℝ) (hz : 0 < z.2) (a : Option (Fin n)) :
    fderiv ℝ (SmoothLift.average ρ f) z (flatDirection a) =
      ∫ y, derivativeScaledKernel (derivativeKernel ρ a) z.2 y • f (z.1 - y) := by
  cases a with
  | none =>
    rw [show flatDirection (none : Option (Fin n)) = (0, 1) from rfl,
      average_fderiv_normal ρ f hρ hρc hf,
      (average_hasDerivAt_normal_noncompact ρ f hρ.continuous hρc
        (hf.of_le (by simp)) z.1 z.2).deriv,
      derivativeScaledKernel_integral_smul_eq _ _ _ hz, derivativeKernel,
      normalKernel_average_derivative_identity ρ f (hρ.of_le (by simp)) hρc
        (hf.of_le (by simp)) z.1 z.2,
      smul_smul, inv_mul_cancel₀ hz.ne', one_smul]
  | some j =>
    rw [show flatDirection (some j) = (coordinateVector j, 0) from rfl,
      average_fderiv_spatial_kernel ρ f hρ hρc hf z hz]
    congr 1
    funext y
    congr 1
    simp only [derivativeScaledKernel, derivativeKernel, pow_succ, mul_inv_rev]
    ring

/-- The first derivative of the h-term has a kernel of order zero.
Consequently its next derivative costs just t^{-1}, which is the sharp
fractional energy exponent for h. -/
lemma normalData_fderiv_first {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (z : Domain n × ℝ) (hz : 0 < z.2) (b : Option (Fin n)) :
    fderiv ℝ (flatLift id ρ f) z (flatDirection b) =
      SmoothLift.average (firstNormalDataKernel ρ b) f z := by
  cases b with
  | none =>
    rw [show flatDirection (none : Option (Fin n)) = (0, 1) from rfl,
      flatLift_fderiv_normal id ρ f contDiff_id hρ hρc hf z,
      ← show flatDirection (none : Option (Fin n)) = (0, 1) from rfl,
      average_fderiv_kernel ρ f hρ hρc hf z hz none,
      derivativeScaledKernel_integral_smul_eq _ _ _ hz]
    rw [(hasDerivAt_id z.2).deriv]
    simp only [id_eq, one_smul, smul_smul, mul_inv_cancel₀ hz.ne', one_smul]
    exact (add_comm _ _).trans (average_kernel_add ρ (normalKernel ρ) f hρ.continuous hρc
      (normalKernel_contDiff ρ hρ).continuous (normalKernel_hasCompactSupport ρ hρc)
      hf.continuous z).symm
  | some j =>
    rw [show flatDirection (some j) = (coordinateVector j, 0) from rfl,
      flatLift_fderiv_tangential id ρ f contDiff_id hρ hρc hf z,
      ← show flatDirection (some j) = (coordinateVector j, 0) from rfl,
      average_fderiv_kernel ρ f hρ hρc hf z hz (some j),
      derivativeScaledKernel_integral_smul_eq _ _ _ hz]
    simp only [id_eq, smul_smul, mul_inv_cancel₀ hz.ne', one_smul,
      firstNormalDataKernel, SmoothLift.average]

lemma normalData_fderiv_second {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (z : Domain n × ℝ) (hz : 0 < z.2) (a b : Option (Fin n)) :
    fderiv ℝ (fun w => fderiv ℝ (flatLift id ρ f) w (flatDirection b)) z
        (flatDirection a) =
      ∫ y, derivativeScaledKernel (derivativeKernel (firstNormalDataKernel ρ b) a)
        z.2 y • f (z.1 - y) := by
  have heq : (fun w => fderiv ℝ (flatLift id ρ f) w (flatDirection b)) =ᶠ[𝓝 z]
      SmoothLift.average (firstNormalDataKernel ρ b) f := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hz] with w hw
    exact normalData_fderiv_first ρ f hρ hρc hf w hw b
  rw [heq.fderiv_eq]
  exact average_fderiv_kernel _ f (firstNormalDataKernel_contDiff ρ hρ b)
    (firstNormalDataKernel_compactSupport ρ hρc b) hf z hz a

/-- Every pure or mixed second derivative of t*(rho_t*h) is controlled
by the genuine order-(1-1/p) difference energy of h. This is the
uncut h-term of the simultaneous extension, in every boundary dimension. -/
theorem normalData_second_energy_bound {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (ρ : Domain n → ℝ) (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ)
    (hρc : HasCompactSupport ρ) (a b : Option (Fin n)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
      (u : Lp 𝕜 p (volume : Measure (Domain n))) (f : Domain n → 𝕜),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f →  u =ᵐ[volume] f →
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖fderiv ℝ (fun w => fderiv ℝ (flatLift id ρ f) w (flatDirection b)) (x, t)
          (flatDirection a)‖ₑ ^ p.toReal) ≤
        C * differenceEnergy (1 - 1 / p.toReal) p u := by
  let K := derivativeKernel (firstNormalDataKernel ρ b) a
  have hK := derivativeKernel_contDiff _ (firstNormalDataKernel_contDiff ρ hρ b) a
  have hKc := derivativeKernel_compactSupport _ (firstNormalDataKernel_compactSupport ρ hρc b) a
  have hK0 := derivativeKernel_integral_zero _ (firstNormalDataKernel_contDiff ρ hρ b)
    (firstNormalDataKernel_compactSupport ρ hρc b) a
  obtain ⟨C, hC, hb⟩ := derivativeScaledKernel_energy_bound p hp1 hp K hK.continuous hKc hK0
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ u f hf huf
  have heq : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
      ‖fderiv ℝ (fun w => fderiv ℝ (flatLift id ρ f) w (flatDirection b)) (x, t)
        (flatDirection a)‖ₑ ^ p.toReal) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖∫ y, derivativeScaledKernel K t y • f (x - y)‖ₑ ^ p.toReal := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply lintegral_congr
    intro x
    rw [normalData_fderiv_second ρ f hρ hρc hf (x, t) ht a b]
  rw [heq]
  exact hb 𝕜 u f hf.continuous huf

open ExpandedFA.Distributions.SmoothApproximateIdentitiesSpec

/-- Tangential differentiation can be moved onto the smooth datum. This
is distinct from differentiating the kernel and is what saves one derivative
of the Dirichlet datum in the second-order estimate. -/
lemma average_fderiv_spatial_datum {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (z : Domain n × ℝ) (hz : 0 < z.2) (v : Domain n) :
    fderiv ℝ (SmoothLift.average ρ f) z (v, 0) =
      SmoothLift.average ρ (fun x => fderiv ℝ f x v) z := by
  rw [average_fderiv_direction_noncompact ρ f hρ hρc hf z.1 v z.2 0]
  simp only [zero_smul, sub_zero, SmoothLift.average]
lemma dirichletData_second_tangential {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (z : Domain n × ℝ) (hz : 0 < z.2) (a : Option (Fin n)) (v : Domain n) :
    fderiv ℝ (fun w => fderiv ℝ (SmoothLift.average ρ f) w (v, 0)) z
        (flatDirection a) =
      ∫ y, derivativeScaledKernel (derivativeKernel ρ a) z.2 y •
        fderiv ℝ f (z.1 - y) v := by
  have heq : (fun w => fderiv ℝ (SmoothLift.average ρ f) w (v, 0)) =ᶠ[𝓝 z]
      SmoothLift.average ρ (fun x => fderiv ℝ f x v) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hz] with w hw
    exact average_fderiv_spatial_datum ρ f hρ hρc hf w hw v
  rw [heq.fderiv_eq]
  exact average_fderiv_kernel ρ _ hρ hρc
    ((hf.fderiv_right (by simp)).clm_apply contDiff_const)
    z hz a

theorem dirichletData_second_tangential_energy_bound {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (ρ : Domain n → ℝ) (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ)
    (hρc : HasCompactSupport ρ) (a : Option (Fin n)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
      (u : Lp 𝕜 p (volume : Measure (Domain n))) (f : Domain n → 𝕜) (v : Domain n),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f → 
      u =ᵐ[volume] (fun x => fderiv ℝ f x v) →
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖fderiv ℝ (fun w => fderiv ℝ (SmoothLift.average ρ f) w (v, 0)) (x, t)
          (flatDirection a)‖ₑ ^ p.toReal) ≤
        C * differenceEnergy (1 - 1 / p.toReal) p u := by
  obtain ⟨C, hC, hb⟩ := derivativeScaledKernel_energy_bound p hp1 hp
    (derivativeKernel ρ a) (derivativeKernel_contDiff ρ hρ a).continuous
    (derivativeKernel_compactSupport ρ hρc a) (derivativeKernel_integral_zero ρ hρ hρc a)
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ u f v hf huf
  have heq : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
      ‖fderiv ℝ (fun w => fderiv ℝ (SmoothLift.average ρ f) w (v, 0)) (x, t)
        (flatDirection a)‖ₑ ^ p.toReal) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖∫ y, derivativeScaledKernel (derivativeKernel ρ a) t y •
          fderiv ℝ f (x - y) v‖ₑ ^ p.toReal := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply lintegral_congr
    intro x
    rw [dirichletData_second_tangential ρ f hρ hρc hf (x, t) ht a v]
  rw [heq]
  exact hb 𝕜 u _ ((hf.continuous_fderiv (by simp)).clm_apply continuous_const) huf

/-- The moment kernel for the normal derivative of the g-term. -/
def momentKernel {n : ℕ} (ρ : Domain n → ℝ) (j : Fin n) (y : Domain n) : ℝ :=
  -y j * ρ y

lemma momentKernel_contDiff {n : ℕ} (ρ : Domain n → ℝ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (j : Fin n) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (momentKernel ρ j) :=
  (contDiff_apply ℝ (fun _ : Fin n => ℝ) j).neg.mul hρ

lemma momentKernel_compactSupport {n : ℕ} (ρ : Domain n → ℝ)
    (hρc : HasCompactSupport ρ) (j : Fin n) : HasCompactSupport (momentKernel ρ j) :=
  hρc.mul_left

/-- Normal differentiation of the Dirichlet average is a finite sum of
order-zero moment-kernel averages of the first derivatives of g. -/
lemma average_fderiv_normal_datum {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (z : Domain n × ℝ) :
    fderiv ℝ (SmoothLift.average ρ f) z (0, 1) =
      ∑ j : Fin n, SmoothLift.average (momentKernel ρ j)
        (fun x => fderiv ℝ f x (coordinateVector j)) z := by
  rw [average_fderiv_normal ρ f hρ hρc hf,
    (average_hasDerivAt_normal_noncompact ρ f hρ.continuous hρc (hf.of_le (by simp)) z.1 z.2).deriv]
  have hi (j : Fin n) : Integrable (fun y => momentKernel ρ j y •
      fderiv ℝ f (z.1 - z.2 • y) (coordinateVector j)) :=
    average_integrable _ _ (momentKernel_contDiff ρ hρ j).continuous
      (momentKernel_compactSupport ρ hρc j)
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const) z
  simp only [SmoothLift.average]
  rw [← integral_finsetSum _ (fun j _ => hi j)]
  apply integral_congr_ae
  filter_upwards with y
  have hy : (-y) = ∑ j : Fin n, (-y j) • coordinateVector j := pi_eq_sum_univ' (-y)
  rw [hy]
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul, momentKernel]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

lemma dirichletData_second_normal {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (z : Domain n × ℝ) (hz : 0 < z.2) (a : Option (Fin n)) :
    fderiv ℝ (fun w => fderiv ℝ (SmoothLift.average ρ f) w (0, 1)) z (flatDirection a) =
      ∑ j : Fin n, ∫ y,
        derivativeScaledKernel (derivativeKernel (momentKernel ρ j) a) z.2 y •
          fderiv ℝ f (z.1 - y) (coordinateVector j) := by
  let A (j : Fin n) := SmoothLift.average (momentKernel ρ j)
    (fun x => fderiv ℝ f x (coordinateVector j))
  have hA (j : Fin n) : ContDiff ℝ (↑(⊤ : ℕ∞)) (A j) :=
    average_contDiff _ _ (momentKernel_contDiff ρ hρ j) (momentKernel_compactSupport ρ hρc j)
      ((hf.fderiv_right (by simp)).clm_apply contDiff_const)
  have heq : (fun w => fderiv ℝ (SmoothLift.average ρ f) w (0, 1)) =
      fun w => ∑ j : Fin n, A j w := funext (average_fderiv_normal_datum ρ f hρ hρc hf)
  rw [heq, fderiv_fun_sum (fun j _ => (hA j).differentiable (by simp) z)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact average_fderiv_kernel _ _ (momentKernel_contDiff ρ hρ j)
    (momentKernel_compactSupport ρ hρc j)
    ((hf.fderiv_right (by simp)).clm_apply contDiff_const)
    z hz a

/-- A finite sum version of the power-integral bound. It includes an empty
index type, which is needed for the zero-dimensional tangential space. -/
lemma flat_lintegral_finite_sum_rpow_le {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    {ι : Type*} [Fintype ι] (A : ι → Domain n × ℝ → 𝕜)
    (hA : ∀ j, Continuous (A j)) (q : ℝ) (hq : 1 ≤ q) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖∑ j, A j (x, t)‖ₑ ^ q) ≤
      (Fintype.card ι : ℝ≥0∞) ^ (q - 1) *
        ∑ j, ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖A j (x, t)‖ₑ ^ q := by
  classical
  let D : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞) ^ (q - 1)
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)
  have hm (j : ι) : Measurable (fun z => ‖A j z‖ₑ ^ q) :=
    (hA j).enorm.measurable.pow_const _
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, D * ∑ j, ‖A j (x, t)‖ₑ ^ q := by
      apply lintegral_mono
      intro t
      apply lintegral_mono
      intro x
      exact (ENNReal.rpow_le_rpow (enorm_sum_le Finset.univ (fun j : ι => A j (x, t)))
        (by linarith)).trans (by
          simpa only [Finset.card_univ] using (ENNReal.rpow_sum_le_const_mul_sum_rpow
            Finset.univ (fun j : ι => ‖A j (x, t)‖ₑ) hq))
    _ = ∫⁻ t in Ioi (0 : ℝ), D * ∑ j, ∫⁻ x : Domain n, ‖A j (x, t)‖ₑ ^ q := by
      apply lintegral_congr
      intro t
      have hmt (j : ι) : Measurable (fun x : Domain n => ‖A j (x, t)‖ₑ ^ q) :=
        (hm j).comp measurable_prodMk_right
      rw [lintegral_const_mul' _ _ hD,
        lintegral_finsetSum Finset.univ (fun j _ => hmt j)]
    _ = _ := by
      rw [lintegral_const_mul' _ _ hD,
        lintegral_finsetSum _ (fun j _ => (hm j).lintegral_prod_left')]

theorem dirichletData_second_normal_energy_bound {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (ρ : Domain n → ℝ) (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ)
    (hρc : HasCompactSupport ρ) (a : Option (Fin n)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
      (u : Fin n → Lp 𝕜 p (volume : Measure (Domain n))) (f : Domain n → 𝕜),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f → 
      (∀ j, u j =ᵐ[volume] (fun x => fderiv ℝ f x (coordinateVector j))) →
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖fderiv ℝ (fun w => fderiv ℝ (SmoothLift.average ρ f) w (0, 1)) (x, t)
          (flatDirection a)‖ₑ ^ p.toReal) ≤
        C * ∑ j, differenceEnergy (1 - 1 / p.toReal) p (u j) := by
  classical
  have hq : 1 ≤ p.toReal := le_of_lt ((ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).mpr hp1)
  have hb (j : Fin n) := derivativeScaledKernel_energy_bound p hp1 hp
    (derivativeKernel (momentKernel ρ j) a)
    (derivativeKernel_contDiff _ (momentKernel_contDiff ρ hρ j) a).continuous
    (derivativeKernel_compactSupport _ (momentKernel_compactSupport ρ hρc j) a)
    (derivativeKernel_integral_zero _ (momentKernel_contDiff ρ hρ j)
      (momentKernel_compactSupport ρ hρc j) a)
  choose B hB hbound using hb
  let D : ℝ≥0∞ := (n : ℝ≥0∞) ^ (p.toReal - 1)
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)
  have hsum : (∑ j, B j) ≠ ∞ := by
    exact ne_of_lt (ENNReal.sum_lt_top.mpr (fun j _ => lt_top_iff_ne_top.mpr (hB j)))
  refine ⟨D * ∑ j, B j, ENNReal.mul_ne_top hD hsum, ?_⟩
  intro 𝕜 _ u f hf huf
  let A (j : Fin n) := fun z : Domain n × ℝ =>
    fderiv ℝ (SmoothLift.average (momentKernel ρ j)
      (fun x => fderiv ℝ f x (coordinateVector j))) z (flatDirection a)
  have hA (j : Fin n) : Continuous (A j) :=
    ((average_contDiff _ _ (momentKernel_contDiff ρ hρ j)
      (momentKernel_compactSupport ρ hρc j)
      ((hf.fderiv_right (by simp)).clm_apply contDiff_const)).continuous_fderiv (by simp)).clm_apply
        continuous_const
  have hjet (z : Domain n × ℝ) :
      fderiv ℝ (fun w => fderiv ℝ (SmoothLift.average ρ f) w (0, 1)) z (flatDirection a) =
        ∑ j, A j z := by
    have heq : (fun w => fderiv ℝ (SmoothLift.average ρ f) w (0, 1)) =
        (fun w => ∑ j : Fin n, SmoothLift.average (momentKernel ρ j)
          (fun x => fderiv ℝ f x (coordinateVector j)) w) :=
      funext (average_fderiv_normal_datum ρ f hρ hρc hf)
    rw [heq, fderiv_fun_sum]
    · simp only [sum_apply, A]
    · intro j _
      exact (average_contDiff _ _ (momentKernel_contDiff ρ hρ j)
        (momentKernel_compactSupport ρ hρc j)
        ((hf.fderiv_right (by simp)).clm_apply contDiff_const)).differentiable (by simp) z
  have hpower (j : Fin n) :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖A j (x, t)‖ₑ ^ p.toReal) ≤
        B j * differenceEnergy (1 - 1 / p.toReal) p (u j) := by
    have heq : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖A j (x, t)‖ₑ ^ p.toReal) =
        ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
          ‖∫ y, derivativeScaledKernel (derivativeKernel (momentKernel ρ j) a) t y •
            fderiv ℝ f (x - y) (coordinateVector j)‖ₑ ^ p.toReal := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply lintegral_congr
      intro x
      rw [show A j (x, t) = _ from average_fderiv_kernel _ _
        (momentKernel_contDiff ρ hρ j) (momentKernel_compactSupport ρ hρc j)
        ((hf.fderiv_right (by simp)).clm_apply contDiff_const)
        (x, t) ht a]
    rw [heq]
    exact hbound j 𝕜 (u j) _
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const) (huf j)
  simp_rw [hjet]
  calc
    _ ≤ D * ∑ j, ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖A j (x, t)‖ₑ ^ p.toReal := by
      simpa only [Fintype.card_fin] using flat_lintegral_finite_sum_rpow_le A hA p.toReal hq
    _ ≤ D * ∑ j, B j * differenceEnergy (1 - 1 / p.toReal) p (u j) := by
      gcongr with j
      exact hpower j
    _ ≤ D * ∑ j, (∑ k, B k) * differenceEnergy (1 - 1 / p.toReal) p (u j) := by
      gcongr with j
      exact Finset.single_le_sum (fun k _ => bot_le) (Finset.mem_univ j)
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

/-- Coordinate second partials in product coordinates, with both normal
and tangential directions included. -/
def secondFlatPartial {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (F : Domain n × ℝ → 𝕜) (a b : Option (Fin n)) (z : Domain n × ℝ) : 𝕜 :=
  fderiv ℝ (fun w => fderiv ℝ F w (flatDirection b)) z (flatDirection a)

lemma secondFlatPartial_continuous {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (F : Domain n × ℝ → 𝕜) (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (a b : Option (Fin n)) : Continuous (secondFlatPartial F a b) := by
  have hD : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun w => fderiv ℝ F w (flatDirection b)) :=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  exact (hD.continuous_fderiv (by simp)).clm_apply continuous_const

lemma secondFlatPartial_add {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (F G : Domain n × ℝ → 𝕜) (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (hG : ContDiff ℝ (↑(⊤ : ℕ∞)) G) (a b : Option (Fin n)) :
    secondFlatPartial (F + G) a b = secondFlatPartial F a b + secondFlatPartial G a b := by
  have hDF : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun w => fderiv ℝ F w (flatDirection b)) :=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  have hDG : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun w => fderiv ℝ G w (flatDirection b)) :=
    (hG.fderiv_right (by simp)).clm_apply contDiff_const
  have hd : (fun w => fderiv ℝ (F + G) w (flatDirection b)) =
      (fun w => fderiv ℝ F w (flatDirection b) + fderiv ℝ G w (flatDirection b)) := by
    funext w
    rw [fderiv_add ((hF.differentiable (by simp)) w) ((hG.differentiable (by simp)) w)]
    rfl
  funext z
  unfold secondFlatPartial
  rw [hd, fderiv_fun_add (hDF.differentiable (by simp) z) (hDG.differentiable (by simp) z)]
  rfl

theorem dirichletData_second_energy_bound {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (ρ : Domain n → ℝ) (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ)
    (hρc : HasCompactSupport ρ) (a b : Option (Fin n)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
      (u : Fin n → Lp 𝕜 p (volume : Measure (Domain n))) (f : Domain n → 𝕜),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f → 
      (∀ j, u j =ᵐ[volume] (fun x => fderiv ℝ f x (coordinateVector j))) →
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖secondFlatPartial (SmoothLift.average ρ f) a b (x, t)‖ₑ ^ p.toReal) ≤
        C * ∑ j, differenceEnergy (1 - 1 / p.toReal) p (u j) := by
  cases b with
  | none => exact dirichletData_second_normal_energy_bound p hp1 hp ρ hρ hρc a
  | some j =>
    obtain ⟨C, hC, hb⟩ := dirichletData_second_tangential_energy_bound p hp1 hp ρ hρ hρc a
    refine ⟨C, hC, ?_⟩
    intro 𝕜 _ u f hf huf
    have he : differenceEnergy (1 - 1 / p.toReal) p (u j) ≤
        ∑ k, differenceEnergy (1 - 1 / p.toReal) p (u k) :=
      Finset.single_le_sum
        (f := fun k : Fin n => differenceEnergy (1 - 1 / p.toReal) p (u k))
        (fun _ _ => bot_le) (Finset.mem_univ j)
    exact (hb 𝕜 (u j) f (coordinateVector j) hf (huf j)).trans
      (mul_le_mul' le_rfl he)

/-- Complete uncut simultaneous-jet formula. The normal cutoff and its
lower-order product terms are handled separately in the full-norm argument. -/
def uncutJet {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f h : Domain n → 𝕜) : Domain n × ℝ → 𝕜 :=
  SmoothLift.average ρ f + flatLift id ρ h

/-- The analytic principal part: every second derivative of the simultaneous
formula is bounded by the gradient difference energies of g and the difference
energy of h, with no additional regularity requirement on the boundary data.
Here smooth representatives are used only to state the classical derivatives.
Extending this estimate to arbitrary data is still required by the main Specs. -/
theorem uncutJet_second_energy_bound {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (ρ : Domain n → ℝ) (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ)
    (hρc : HasCompactSupport ρ) (a b : Option (Fin n)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
      (u : Fin n → Lp 𝕜 p (volume : Measure (Domain n)))
      (v : Lp 𝕜 p (volume : Measure (Domain n))) (f h : Domain n → 𝕜),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f → 
      ContDiff ℝ (↑(⊤ : ℕ∞)) h → 
      (∀ j, u j =ᵐ[volume] (fun x => fderiv ℝ f x (coordinateVector j))) →
      v =ᵐ[volume] h →
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖secondFlatPartial (uncutJet ρ f h) a b (x, t)‖ₑ ^ p.toReal) ≤
        C * ((∑ j, differenceEnergy (1 - 1 / p.toReal) p (u j)) +
          differenceEnergy (1 - 1 / p.toReal) p v) := by
  have hq : 1 ≤ p.toReal := le_of_lt ((ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).mpr hp1)
  obtain ⟨G, hG, hg⟩ := dirichletData_second_energy_bound p hp1 hp ρ hρ hρc a b
  obtain ⟨H, hH, hh⟩ := normalData_second_energy_bound p hp1 hp ρ hρ hρc a b
  let D : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (p.toReal - 1)
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  refine ⟨D * (G + H), ENNReal.mul_ne_top hD (ENNReal.add_ne_top.mpr ⟨hG, hH⟩), ?_⟩
  intro 𝕜 _ u v f h hf hhs huf hvh
  have hF := average_contDiff ρ f hρ hρc hf
  have hJ := flatLift_contDiff id ρ h contDiff_id hρ hρc hhs
  have heq := secondFlatPartial_add (SmoothLift.average ρ f) (flatLift id ρ h) hF hJ a b
  change (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
      ‖secondFlatPartial (SmoothLift.average ρ f + flatLift id ρ h) a b (x, t)‖ₑ ^ p.toReal) ≤ _
  rw [heq]
  calc
    _ ≤ D * ((∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖secondFlatPartial (SmoothLift.average ρ f) a b (x, t)‖ₑ ^ p.toReal) +
        ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
          ‖secondFlatPartial (flatLift id ρ h) a b (x, t)‖ₑ ^ p.toReal) := by
      exact flat_lintegral_sum_rpow_le _ _ p.toReal hq
        ((secondFlatPartial_continuous _ hJ a b).enorm.measurable.pow_const _)
    _ ≤ D * (G * (∑ j, differenceEnergy (1 - 1 / p.toReal) p (u j)) +
        H * differenceEnergy (1 - 1 / p.toReal) p v) := by
      exact mul_le_mul' le_rfl (add_le_add (hg 𝕜 u f hf huf) (hh 𝕜 v h hhs hvh))
    _ ≤ D * ((G + H) * ((∑ j, differenceEnergy (1 - 1 / p.toReal) p (u j)) +
        differenceEnergy (1 - 1 / p.toReal) p v)) := by
      apply mul_le_mul' le_rfl
      rw [mul_add]
      exact add_le_add (mul_le_mul' (le_add_right le_rfl) le_rfl)
        (mul_le_mul' (le_add_left le_rfl) le_rfl)
    _ = _ := (mul_assoc _ _ _).symm

set_option maxHeartbeats 800000

/-- A cutoff average has a uniform power-integral bound depending only on
the cutoff, the kernel and the exponent. This also applies to derivatives
of the cutoff and to the compactly supported cutoff `t * χ t`. -/
theorem cutoffAverage_power_bound {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (ρ : Domain n → ℝ) (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ)
    (hρc : HasCompactSupport ρ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
      (u : Lp 𝕜 p (volume : Measure (Domain n))) (f : Domain n → 𝕜),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f → u =ᵐ[volume] f →
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖χ t • SmoothLift.average ρ f (x, t)‖ₑ ^ p.toReal) ≤ C * ‖u‖ₑ ^ p.toReal := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  let C := eLpNorm χ p volume ^ p.toReal * eLpNorm ρ 1 volume ^ p.toReal
  have hχp : MemLp χ p volume := hχ.continuous.memLp_of_hasCompactSupport hχc
  have hρp : MemLp ρ 1 volume := hρ.continuous.memLp_of_hasCompactSupport hρc
  have hC : C ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hpr.le hχp.eLpNorm_ne_top)
    (ENNReal.rpow_ne_top_of_nonneg hpr.le hρp.eLpNorm_ne_top)
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ u f hf huf
  have hfp := (Lp.memLp u).ae_eq huf
  have hF := flatLift_contDiff χ ρ f hχ hρ hρc hf
  have hmass : (∫⁻ t : ℝ, ‖χ t‖ₑ ^ p.toReal) = eLpNorm χ p volume ^ p.toReal := by
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hpr,
      ← eLpNorm_eq_eLpNorm' hp0 hp hχ.continuous.aestronglyMeasurable]
  have hfnorm : eLpNorm f p volume = ‖u‖ₑ := by
    rw [← eLpNorm_congr_ae huf, Lp.enorm_def]
  calc
    _ ≤ ∫⁻ t : ℝ, ∫⁻ x : Domain n,
        ‖χ t • SmoothLift.average ρ f (x, t)‖ₑ ^ p.toReal :=
      setLIntegral_le_lintegral _ _
    _ = ∫⁻ z : Domain n × ℝ, ‖flatLift χ ρ f z‖ₑ ^ p.toReal :=
      (lintegral_prod_symm _ (hF.continuous.enorm.measurable.pow_const _).aemeasurable).symm
    _ ≤ _ := by
      have hb := flatLift_lintegral_rpow_le χ ρ f hχ hρ hρc hf p Fact.out hp hfp
      rw [hmass, hfnorm, ENNReal.mul_rpow_of_nonneg _ _ hpr.le, ← mul_assoc] at hb
      exact hb

/-- Lower-order terms coming from differentiating the normal cutoff are
bounded by the ordinary Lp norms of the two data. -/
theorem cutoff_uncutJet_power_bound {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (ρ : Domain n → ℝ) (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ)
    (hρc : HasCompactSupport ρ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
      (u v : Lp 𝕜 p (volume : Measure (Domain n))) (f h : Domain n → 𝕜),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f → ContDiff ℝ (↑(⊤ : ℕ∞)) h →
      u =ᵐ[volume] f → v =ᵐ[volume] h →
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖χ t • uncutJet ρ f h (x, t)‖ₑ ^ p.toReal) ≤
        C * (‖u‖ₑ ^ p.toReal + ‖v‖ₑ ^ p.toReal) := by
  have hq : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  obtain ⟨G, hG, hg⟩ := cutoffAverage_power_bound p hp χ hχ hχc ρ hρ hρc
  have hχt : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t => χ t * t) := hχ.mul contDiff_id
  have hχtc : HasCompactSupport (fun t => χ t * t) := hχc.mul_right
  obtain ⟨H, hH, hh⟩ := cutoffAverage_power_bound p hp _ hχt hχtc ρ hρ hρc
  let D : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (p.toReal - 1)
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  refine ⟨D * (G + H), ENNReal.mul_ne_top hD (ENNReal.add_ne_top.mpr ⟨hG, hH⟩), ?_⟩
  intro 𝕜 _ u v f h hf hhs huf hvh
  have heq : (fun z : Domain n × ℝ => χ z.2 • uncutJet ρ f h z) =
      fun z => χ z.2 • SmoothLift.average ρ f z +
        (χ z.2 * z.2) • SmoothLift.average ρ h z := by
    funext z
    simp only [uncutJet, Pi.add_apply, flatLift, id_eq, smul_add, smul_smul]
  rw [show (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖χ t • uncutJet ρ f h (x, t)‖ₑ ^ p.toReal) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖χ t • SmoothLift.average ρ f (x, t) +
          (χ t * t) • SmoothLift.average ρ h (x, t)‖ₑ ^ p.toReal from
    congrArg (fun F : Domain n × ℝ → 𝕜 =>
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖F (x, t)‖ₑ ^ p.toReal) heq]
  calc
    _ ≤ D * ((∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖χ t • SmoothLift.average ρ f (x, t)‖ₑ ^ p.toReal) +
        ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
          ‖(χ t * t) • SmoothLift.average ρ h (x, t)‖ₑ ^ p.toReal) :=
      by
      simpa only [flatLift] using flat_lintegral_sum_rpow_le
        (flatLift χ ρ f) (flatLift (fun t => χ t * t) ρ h) p.toReal hq
        ((flatLift_contDiff _ ρ h hχt hρ hρc hhs).continuous.enorm.measurable.pow_const _)
    _ ≤ D * (G * ‖u‖ₑ ^ p.toReal + H * ‖v‖ₑ ^ p.toReal) :=
      mul_le_mul' le_rfl (add_le_add (hg 𝕜 u f hf huf) (hh 𝕜 v h hhs hvh))
    _ ≤ D * ((G + H) * (‖u‖ₑ ^ p.toReal + ‖v‖ₑ ^ p.toReal)) := by
      apply mul_le_mul' le_rfl
      rw [mul_add]
      exact add_le_add (mul_le_mul' (le_add_right le_rfl) le_rfl)
        (mul_le_mul' (le_add_left le_rfl) le_rfl)
    _ = _ := (mul_assoc _ _ _).symm

section CutoffProduct
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝕜 : Type*} [RCLike 𝕜]

lemma cutoff_smul_fderiv
    (χ : ℝ → ℝ) (F : E × ℝ → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (z v : E × ℝ) :
    fderiv ℝ (fun w => χ w.2 • F w) z v =
      χ z.2 • fderiv ℝ F z v + v.2 • (deriv χ z.2 • F z) := by
  have hχc := ((hχ.differentiable (by simp) z.2).hasDerivAt).hasFDerivAt.comp z
    (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt
  change HasFDerivAt (fun w : E × ℝ => χ w.2) _ z at hχc
  rw [fderiv_fun_smul hχc.differentiableAt (hF.differentiable (by simp) z), hχc.fderiv]
  simp [smul_smul]

lemma cutoff_smul_second_fderiv
    (χ : ℝ → ℝ) (F : E × ℝ → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (z v w : E × ℝ) :
    fderiv ℝ (fun y => fderiv ℝ (fun x => χ x.2 • F x) y w) z v =
      χ z.2 • fderiv ℝ (fun y => fderiv ℝ F y w) z v +
      v.2 • (deriv χ z.2 • fderiv ℝ F z w) +
      w.2 • (deriv χ z.2 • fderiv ℝ F z v) +
      w.2 • (v.2 • (deriv (deriv χ) z.2 • F z)) := by
  have hD : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y => fderiv ℝ F y w) :=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  have hχ' : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv χ) :=
    contDiff_infty_iff_deriv.mp hχ |>.2
  have heq : (fun y => fderiv ℝ (fun x => χ x.2 • F x) y w) =
      (fun y => χ y.2 • fderiv ℝ F y w + w.2 • (deriv χ y.2 • F y)) := by
    funext y
    exact cutoff_smul_fderiv χ F hχ hF y w
  have hA : Differentiable ℝ (fun y : E × ℝ => χ y.2 • fderiv ℝ F y w) :=
    ((hχ.comp contDiff_snd).smul hD).differentiable (by simp)
  have hB : Differentiable ℝ (fun y : E × ℝ => w.2 • (deriv χ y.2 • F y)) := by
    exact (((hχ'.comp contDiff_snd).smul hF).const_smul w.2).differentiable (by simp)
  rw [heq, fderiv_fun_add (hA z) (hB z)]
  simp only [add_apply]
  rw [cutoff_smul_fderiv χ _ hχ hD,
    fderiv_fun_const_smul (f := fun y : E × ℝ => deriv χ y.2 • F y)
      (((hχ'.comp contDiff_snd).smul hF).differentiable (by simp) z) w.2]
  simp only [smul_apply]
  rw [cutoff_smul_fderiv (deriv χ) F hχ' hF]
  module

end CutoffProduct

lemma uncutJet_contDiff {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f h : Domain n → 𝕜)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (uncutJet ρ f h) :=
  (average_contDiff ρ f hρ hρc hf).add
    (flatLift_contDiff id ρ h contDiff_id hρ hρc hh)

lemma flatJet_eq_cutoff_uncut {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f h : Domain n → 𝕜) :
    flatJet χ ρ f h = (fun z => χ z.2 • uncutJet ρ f h z) := by
  rfl

lemma flatJet_second_partial {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f h : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h)
    (z : Domain n × ℝ) (a b : Option (Fin n)) :
    secondFlatPartial (flatJet χ ρ f h) a b z =
      χ z.2 • secondFlatPartial (uncutJet ρ f h) a b z +
      (flatDirection a).2 • (deriv χ z.2 • fderiv ℝ (uncutJet ρ f h) z (flatDirection b)) +
      (flatDirection b).2 • (deriv χ z.2 • fderiv ℝ (uncutJet ρ f h) z (flatDirection a)) +
      (flatDirection b).2 • ((flatDirection a).2 • (deriv (deriv χ) z.2 • uncutJet ρ f h z)) := by
  rw [flatJet_eq_cutoff_uncut]
  exact cutoff_smul_second_fderiv χ (uncutJet ρ f h) hχ
    (uncutJet_contDiff ρ f h hρ hρc hf hh) z (flatDirection a) (flatDirection b)

/-- A cutoff times any first derivative of the Dirichlet average is
controlled by the Lp norms of the actual tangential derivatives of its datum. -/
theorem cutoff_dirichletData_first_power_bound {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (ρ : Domain n → ℝ) (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ)
    (hρc : HasCompactSupport ρ) (b : Option (Fin n)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
      (u : Fin n → Lp 𝕜 p (volume : Measure (Domain n))) (f : Domain n → 𝕜),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f → 
      (∀ j, u j =ᵐ[volume] (fun x => fderiv ℝ f x (coordinateVector j))) →
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖χ t • fderiv ℝ (SmoothLift.average ρ f) (x, t) (flatDirection b)‖ₑ ^ p.toReal) ≤
        C * ∑ j, ‖u j‖ₑ ^ p.toReal := by
  classical
  have hq : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  cases b with
  | some j =>
    obtain ⟨C, hC, hb⟩ := cutoffAverage_power_bound p hp χ hχ hχc ρ hρ hρc
    refine ⟨C, hC, ?_⟩
    intro 𝕜 _ u f hf huf
    have heq : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖χ t • fderiv ℝ (SmoothLift.average ρ f) (x, t) (flatDirection (some j))‖ₑ ^ p.toReal) =
        ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
          ‖χ t • SmoothLift.average ρ (fun y => fderiv ℝ f y (coordinateVector j)) (x, t)‖ₑ ^ p.toReal := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      apply lintegral_congr
      intro x
      rw [show flatDirection (some j) = (coordinateVector j, 0) from rfl,
        average_fderiv_spatial_datum ρ f hρ hρc hf (x,t) ht]
    rw [heq]
    exact (hb 𝕜 (u j) _ ((hf.fderiv_right (by simp)).clm_apply contDiff_const) (huf j)).trans
      (mul_le_mul' le_rfl (Finset.single_le_sum (f := fun k : Fin n => ‖u k‖ₑ ^ p.toReal)
        (fun k _ => bot_le) (Finset.mem_univ j)))
  | none =>
    have hb (j : Fin n) := cutoffAverage_power_bound p hp χ hχ hχc
      (momentKernel ρ j) (momentKernel_contDiff ρ hρ j) (momentKernel_compactSupport ρ hρc j)
    choose B hB hbound using hb
    let D : ℝ≥0∞ := (n : ℝ≥0∞) ^ (p.toReal - 1)
    have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)
    have hsum : (∑ j, B j) ≠ ∞ :=
      ne_of_lt (ENNReal.sum_lt_top.mpr (fun j _ => lt_top_iff_ne_top.mpr (hB j)))
    refine ⟨D * ∑ j, B j, ENNReal.mul_ne_top hD hsum, ?_⟩
    intro 𝕜 _ u f hf huf
    let A (j : Fin n) := fun z : Domain n × ℝ =>
      χ z.2 • SmoothLift.average (momentKernel ρ j)
        (fun x => fderiv ℝ f x (coordinateVector j)) z
    have hA (j : Fin n) : Continuous (A j) :=
      (flatLift_contDiff χ _ _ hχ (momentKernel_contDiff ρ hρ j)
        (momentKernel_compactSupport ρ hρc j)
        ((hf.fderiv_right (by simp)).clm_apply contDiff_const)).continuous
    have heq : (fun z : Domain n × ℝ =>
        χ z.2 • fderiv ℝ (SmoothLift.average ρ f) z (flatDirection none)) =
        fun z => ∑ j, A j z := by
      funext z
      rw [show flatDirection (none : Option (Fin n)) = (0, 1) from rfl,
        average_fderiv_normal_datum ρ f hρ hρc hf, Finset.smul_sum]
    have hbnd (j : Fin n) :
        (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖A j (x, t)‖ₑ ^ p.toReal) ≤
          B j * ‖u j‖ₑ ^ p.toReal :=
      hbound j 𝕜 (u j) _ ((hf.fderiv_right (by simp)).clm_apply contDiff_const) (huf j)
    have heq' := congrArg (fun F : Domain n × ℝ → 𝕜 =>
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖F (x, t)‖ₑ ^ p.toReal) heq
    rw [heq']
    calc
      _ ≤ D * ∑ j, ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖A j (x, t)‖ₑ ^ p.toReal := by
        simpa only [Fintype.card_fin] using flat_lintegral_finite_sum_rpow_le A hA p.toReal hq
      _ ≤ D * ∑ j, B j * ‖u j‖ₑ ^ p.toReal := by
        gcongr with j
        exact hbnd j
      _ ≤ D * ∑ j, (∑ k, B k) * ‖u j‖ₑ ^ p.toReal := by
        gcongr with j
        exact Finset.single_le_sum (fun k _ => bot_le) (Finset.mem_univ j)
      _ = _ := by rw [← Finset.mul_sum, mul_assoc]

/-- A cutoff times the first derivative of the normal-data term only
requires the Lp norm of that datum, because its first kernel has order zero. -/
theorem cutoff_normalData_first_power_bound {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (ρ : Domain n → ℝ) (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ)
    (hρc : HasCompactSupport ρ) (b : Option (Fin n)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
      (u : Lp 𝕜 p (volume : Measure (Domain n))) (f : Domain n → 𝕜),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f →  u =ᵐ[volume] f →
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖χ t • fderiv ℝ (flatLift id ρ f) (x, t) (flatDirection b)‖ₑ ^ p.toReal) ≤
        C * ‖u‖ₑ ^ p.toReal := by
  obtain ⟨C, hC, hb⟩ := cutoffAverage_power_bound p hp χ hχ hχc
    (firstNormalDataKernel ρ b) (firstNormalDataKernel_contDiff ρ hρ b)
    (firstNormalDataKernel_compactSupport ρ hρc b)
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ u f hf huf
  have heq : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖χ t • fderiv ℝ (flatLift id ρ f) (x, t) (flatDirection b)‖ₑ ^ p.toReal) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖χ t • SmoothLift.average (firstNormalDataKernel ρ b) f (x, t)‖ₑ ^ p.toReal := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply lintegral_congr
    intro x
    rw [normalData_fderiv_first ρ f hρ hρc hf (x,t) ht b]
  rw [heq]
  exact hb 𝕜 u f hf huf

/-- All first derivatives in the cutoff product rule have uniform Lp bounds. -/
theorem cutoff_uncutJet_first_power_bound {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (ρ : Domain n → ℝ) (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ)
    (hρc : HasCompactSupport ρ) (b : Option (Fin n)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
      (u : Fin n → Lp 𝕜 p (volume : Measure (Domain n)))
      (v : Lp 𝕜 p (volume : Measure (Domain n))) (f h : Domain n → 𝕜),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f → 
      ContDiff ℝ (↑(⊤ : ℕ∞)) h → 
      (∀ j, u j =ᵐ[volume] (fun x => fderiv ℝ f x (coordinateVector j))) →
      v =ᵐ[volume] h →
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖χ t • fderiv ℝ (uncutJet ρ f h) (x, t) (flatDirection b)‖ₑ ^ p.toReal) ≤
        C * ((∑ j, ‖u j‖ₑ ^ p.toReal) + ‖v‖ₑ ^ p.toReal) := by
  have hq : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  obtain ⟨G, hG, hg⟩ := cutoff_dirichletData_first_power_bound p hp χ hχ hχc ρ hρ hρc b
  obtain ⟨H, hH, hh⟩ := cutoff_normalData_first_power_bound p hp χ hχ hχc ρ hρ hρc b
  let D : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (p.toReal - 1)
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  refine ⟨D * (G + H), ENNReal.mul_ne_top hD (ENNReal.add_ne_top.mpr ⟨hG, hH⟩), ?_⟩
  intro 𝕜 _ u v f h hf hhs huf hvh
  have hF := average_contDiff ρ f hρ hρc hf
  have hJ := flatLift_contDiff id ρ h contDiff_id hρ hρc hhs
  have heq : (fun z : Domain n × ℝ => χ z.2 • fderiv ℝ (uncutJet ρ f h) z (flatDirection b)) =
      fun z => χ z.2 • fderiv ℝ (SmoothLift.average ρ f) z (flatDirection b) +
        χ z.2 • fderiv ℝ (flatLift id ρ h) z (flatDirection b) := by
    funext z
    unfold uncutJet
    rw [fderiv_add (hF.differentiable (by simp) z) (hJ.differentiable (by simp) z)]
    simp only [add_apply, smul_add]
  have heq' := congrArg (fun F : Domain n × ℝ → 𝕜 =>
    ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖F (x, t)‖ₑ ^ p.toReal) heq
  rw [heq']
  have hB : Measurable (fun z : Domain n × ℝ =>
      ‖χ z.2 • fderiv ℝ (flatLift id ρ h) z (flatDirection b)‖ₑ ^ p.toReal) :=
    ((hχ.continuous.comp continuous_snd).smul
      ((hJ.continuous_fderiv (by simp)).clm_apply continuous_const)).enorm.measurable.pow_const _
  calc
    _ ≤ D * ((∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖χ t • fderiv ℝ (SmoothLift.average ρ f) (x,t) (flatDirection b)‖ₑ ^ p.toReal) +
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖χ t • fderiv ℝ (flatLift id ρ h) (x,t) (flatDirection b)‖ₑ ^ p.toReal) :=
      flat_lintegral_sum_rpow_le
        (fun z => χ z.2 • fderiv ℝ (SmoothLift.average ρ f) z (flatDirection b))
        (fun z => χ z.2 • fderiv ℝ (flatLift id ρ h) z (flatDirection b)) p.toReal hq hB
    _ ≤ D * (G * (∑ j, ‖u j‖ₑ ^ p.toReal) + H * ‖v‖ₑ ^ p.toReal) :=
      mul_le_mul' le_rfl (add_le_add (hg 𝕜 u f hf huf) (hh 𝕜 v h hhs hvh))
    _ ≤ D * ((G + H) * ((∑ j, ‖u j‖ₑ ^ p.toReal) + ‖v‖ₑ ^ p.toReal)) := by
      apply mul_le_mul' le_rfl
      rw [mul_add]
      exact add_le_add (mul_le_mul' (le_add_right le_rfl) le_rfl)
        (mul_le_mul' (le_add_left le_rfl) le_rfl)
    _ = _ := (mul_assoc _ _ _).symm

lemma derivativeWord_order_two_cases {d : ℕ} (α : DerivativeIndex d 2) :
    (multiIndexWord (natIndex α)).reverse = [] ∨
      (∃ j, (multiIndexWord (natIndex α)).reverse = [j]) ∨
      (∃ j k, (multiIndexWord (natIndex α)).reverse = [j, k]) := by
  have hlen : (multiIndexWord (natIndex α)).reverse.length ≤ 2 := by
    simpa only [List.length_reverse, multiIndexWord_length, natIndex] using α.property
  generalize hw : (multiIndexWord (natIndex α)).reverse = w at *
  cases w with
  | nil => exact Or.inl rfl
  | cons j w =>
      cases w with
      | nil => exact Or.inr (Or.inl ⟨j, rfl⟩)
      | cons k w =>
          cases w with
          | nil => exact Or.inr (Or.inr ⟨j, k, rfl⟩)
          | cons l w => simp only [List.length_cons] at hlen; omega

/-- Bounds for the function, every first partial and every ordered second
partial bound the full existing order-two graph norm. -/
lemma secondJet_norm_le_of_classical_bounds {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : SpaceValue 𝕜 d Ω 2 p) (f : Domain d → 𝕜)
    (hcoe : ∀ α, u.val α =ᵐ[volume.restrict (Ω : Set (Domain d))]
      partialFunction (multiIndexWord (natIndex α)).reverse f)
    (A B C N : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hzero : (eLpNorm f p (volume.restrict (Ω : Set (Domain d)))).toReal ≤ A * N)
    (hfirst : ∀ j : Fin d, (eLpNorm (fun x => fderiv ℝ f x (coordinateVector j))
      p (volume.restrict (Ω : Set (Domain d)))).toReal ≤ B * N)
    (hsecond : ∀ j k : Fin d,
      (eLpNorm (fun x => fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector k)) x
        (coordinateVector j)) p (volume.restrict (Ω : Set (Domain d)))).toReal ≤ C * N) :
    ‖u‖ ≤ (Fintype.card (DerivativeIndex d 2) : ℝ) * (A + B + C) * N := by
  change ‖u.val‖ ≤ _
  rw [PiLp.norm_eq_of_L1]
  calc
    _ ≤ ∑ _α : DerivativeIndex d 2, (A + B + C) * N := by
      apply Finset.sum_le_sum
      intro α _
      rw [Lp.norm_def, eLpNorm_congr_ae (hcoe α)]
      rcases derivativeWord_order_two_cases α with hz | ⟨j, hj⟩ | ⟨j, k, hjk⟩
      · simpa only [hz, partialFunction] using hzero.trans (by nlinarith)
      · simpa only [hj, partialFunction] using (hfirst j).trans (by nlinarith)
      · simpa only [hjk, partialFunction] using (hsecond j k).trans (by nlinarith)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

lemma fderiv_linear_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {𝕜 : Type} [RCLike 𝕜] (A : E →L[ℝ] F) (G : F → 𝕜)
    (hG : ContDiff ℝ (↑(⊤ : ℕ∞)) G) (x v : E) :
    fderiv ℝ (fun y => G (A y)) x v = fderiv ℝ G (A x) (A v) := by
  have hd := (hG.differentiable (by simp) (A x)).hasFDerivAt.comp x A.hasFDerivAt
  change HasFDerivAt (fun y => G (A y)) _ x at hd
  rw [hd.fderiv]
  rfl

lemma second_fderiv_linear_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {𝕜 : Type} [RCLike 𝕜] (A : E →L[ℝ] F) (G : F → 𝕜)
    (hG : ContDiff ℝ (↑(⊤ : ℕ∞)) G) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => G (A z)) y w) x v =
      fderiv ℝ (fun y => fderiv ℝ G y (A w)) (A x) (A v) := by
  have heq : (fun y => fderiv ℝ (fun z => G (A z)) y w) =
      fun y => fderiv ℝ G (A y) (A w) := by
    funext y
    exact fderiv_linear_comp A G hG y w
  rw [heq]
  exact fderiv_linear_comp A (fun y => fderiv ℝ G y (A w))
    ((hG.fderiv_right (by simp)).clm_apply contDiff_const) x v


lemma flatCoordinatesCLM_direction {n : ℕ} (i j : Fin (n + 1)) :
    ∃ a : Option (Fin n), flatCoordinatesCLM i (coordinateVector j) = flatDirection a := by
  rcases Fin.eq_self_or_eq_succAbove i j with hji | ⟨l, hl⟩
  · subst j
    exact ⟨none, flatCoordinatesCLM_normal i⟩
  · subst j
    exact ⟨some l, flatCoordinatesCLM_tangential i l⟩

lemma jetFunction_fderiv_flat {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i j : Fin (n + 1)) (f h : Domain n → 𝕜)
    (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) (flatJet jetCutoff (jetMollifier n) f h))
    (a : Option (Fin n))
    (ha : flatCoordinatesCLM i (coordinateVector j) = flatDirection a)
    (x : Domain (n + 1)) :
    fderiv ℝ (jetFunction i f h) x (coordinateVector j) =
      fderiv ℝ (flatJet jetCutoff (jetMollifier n) f h) (flatCoordinates i x) (flatDirection a) := by
  have heq := fderiv_linear_comp (flatCoordinatesCLM i)
    (flatJet jetCutoff (jetMollifier n) f h) hF x (coordinateVector j)
  rw [ha] at heq
  exact heq

lemma jetFunction_second_fderiv_flat {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i j k : Fin (n + 1)) (f h : Domain n → 𝕜)
    (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) (flatJet jetCutoff (jetMollifier n) f h))
    (a b : Option (Fin n))
    (ha : flatCoordinatesCLM i (coordinateVector j) = flatDirection a)
    (hb : flatCoordinatesCLM i (coordinateVector k) = flatDirection b)
    (x : Domain (n + 1)) :
    fderiv ℝ (fun y => fderiv ℝ (jetFunction i f h) y (coordinateVector k)) x
      (coordinateVector j) =
        secondFlatPartial (flatJet jetCutoff (jetMollifier n) f h) a b (flatCoordinates i x) := by
  have heq := second_fderiv_linear_comp (flatCoordinatesCLM i)
    (flatJet jetCutoff (jetMollifier n) f h) hF x (coordinateVector j) (coordinateVector k)
  rw [ha, hb] at heq
  exact heq


open Metric

/-- Total boundary power used in the smooth second-order estimate. The two
fractional energies are attached to the actual gradient and normal data. -/
def jetDataPower {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u₀ : Lp 𝕜 p (volume : Measure (Domain n)))
    (u : Fin n → Lp 𝕜 p (volume : Measure (Domain n)))
    (v : Lp 𝕜 p (volume : Measure (Domain n))) : ℝ≥0∞ :=
  ‖u₀‖ₑ ^ p.toReal + (∑ j, ‖u j‖ₑ ^ p.toReal) + ‖v‖ₑ ^ p.toReal +
    (∑ j, differenceEnergy (1 - 1 / p.toReal) p (u j)) +
      differenceEnergy (1 - 1 / p.toReal) p v

lemma jetDataPower_value_le {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u₀ : Lp 𝕜 p (volume : Measure (Domain n)))
    (u : Fin n → Lp 𝕜 p (volume : Measure (Domain n)))
    (v : Lp 𝕜 p (volume : Measure (Domain n))) :
    ‖u₀‖ₑ ^ p.toReal + ‖v‖ₑ ^ p.toReal ≤ jetDataPower p u₀ u v := by
  unfold jetDataPower
  calc
    _ ≤ ‖u₀‖ₑ ^ p.toReal + (∑ j, ‖u j‖ₑ ^ p.toReal) + ‖v‖ₑ ^ p.toReal := by
      exact add_le_add (le_add_right le_rfl) le_rfl
    _ ≤ _ := le_add_right (le_add_right le_rfl)

lemma jetDataPower_first_le {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u₀ : Lp 𝕜 p (volume : Measure (Domain n)))
    (u : Fin n → Lp 𝕜 p (volume : Measure (Domain n)))
    (v : Lp 𝕜 p (volume : Measure (Domain n))) :
    (∑ j, ‖u j‖ₑ ^ p.toReal) + ‖v‖ₑ ^ p.toReal ≤ jetDataPower p u₀ u v := by
  unfold jetDataPower
  calc
    _ ≤ ‖u₀‖ₑ ^ p.toReal + (∑ j, ‖u j‖ₑ ^ p.toReal) + ‖v‖ₑ ^ p.toReal :=
      add_le_add (le_add_left le_rfl) le_rfl
    _ ≤ _ := le_add_right (le_add_right le_rfl)

lemma jetDataPower_second_le {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u₀ : Lp 𝕜 p (volume : Measure (Domain n)))
    (u : Fin n → Lp 𝕜 p (volume : Measure (Domain n)))
    (v : Lp 𝕜 p (volume : Measure (Domain n))) :
    (∑ j, differenceEnergy (1 - 1 / p.toReal) p (u j)) +
      differenceEnergy (1 - 1 / p.toReal) p v ≤ jetDataPower p u₀ u v := by
  unfold jetDataPower
  exact add_le_add (le_add_left le_rfl) le_rfl

/-- Multiplication by the chosen normal cutoff contracts every nonnegative
power integral, including the second derivative principal term. -/
lemma jetCutoff_flat_power_le {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (F : Domain n × ℝ → 𝕜) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖jetCutoff t • F (x,t)‖ₑ ^ q) ≤
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖F (x,t)‖ₑ ^ q := by
  apply lintegral_mono
  intro t
  apply lintegral_mono
  intro x
  apply ENNReal.rpow_le_rpow _ hq
  rw [enorm_smul]
  exact (mul_le_mul' (standardCutoff_enorm_le_one t) le_rfl).trans_eq (one_mul _)

lemma jet_dataPower_le {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (g : HigherFractionalSpace 𝕜 n (2 - 1 / p.toReal) p)
    (h : FractionalSpace 𝕜 n (1 - 1 / p.toReal) p) :
    ‖wholeLp (g.val.val (zeroIndex n 1))‖ₑ ^ p.toReal +
        (∑ j : Fin n, ‖wholeLp (g.val.val (firstIndex j))‖ₑ ^ p.toReal) +
        ‖h.val‖ₑ ^ p.toReal +
        (∑ j : Fin n, differenceEnergy (1 - 1 / p.toReal) p
          (wholeLp (g.val.val (firstIndex j)))) +
        differenceEnergy (1 - 1 / p.toReal) p h.val ≤
      (2 * (n : ℝ≥0∞) + 3) *
        ENNReal.ofReal (higherFractionalNorm (2 - 1 / p.toReal) p g +
          fractionalNorm (1 - 1 / p.toReal) p h) ^ p.toReal := by
  let s : ℝ := 1 - 1 / p.toReal
  have hs : (2 - 1 / p.toReal) - 1 = s := by dsimp [s]; ring
  let G : ℝ := higherFractionalNorm (2 - 1 / p.toReal) p g
  let H : ℝ := fractionalNorm s p h
  let N : ℝ := G + H
  let R : ℝ≥0∞ := ENNReal.ofReal N ^ p.toReal
  have hG : 0 ≤ G := higherFractionalNorm_nonneg _ p g
  have hH : 0 ≤ H := fractionalNorm_nonneg s p h
  have hzero : ‖wholeLp (g.val.val (zeroIndex n 1))‖ ≤ N := by
    have h0 : ‖wholeLp (g.val.val (zeroIndex n 1))‖ ≤ G := by
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => fractionalNorm_nonneg _ _ _)
    exact h0.trans (le_add_of_nonneg_right hH)
  let grad : Fin n → FractionalSpace 𝕜 n s p := fun j =>
    ⟨wholeLp (g.val.val (firstIndex j)), by simpa only [hs] using g.property j⟩
  have hgrad : ∀ j, fractionalNorm s p (grad j) ≤ N := by
    intro j
    have hj : fractionalNorm ((2 - 1 / p.toReal) - 1) p
        ⟨wholeLp (g.val.val (firstIndex j)), g.property j⟩ ≤
        ∑ k : Fin n, fractionalNorm ((2 - 1 / p.toReal) - 1) p
          ⟨wholeLp (g.val.val (firstIndex k)), g.property k⟩ :=
      Finset.single_le_sum
        (f := fun k : Fin n => fractionalNorm ((2 - 1 / p.toReal) - 1) p
          ⟨wholeLp (g.val.val (firstIndex k)), g.property k⟩)
        (fun k _ => fractionalNorm_nonneg _ _ _) (Finset.mem_univ j)
    have hjG : fractionalNorm ((2 - 1 / p.toReal) - 1) p
        ⟨wholeLp (g.val.val (firstIndex j)), g.property j⟩ ≤ G :=
      hj.trans (le_add_of_nonneg_left (norm_nonneg _))
    have hjG' : fractionalNorm s p (grad j) ≤ G := by
      simpa only [fractionalNorm, grad, hs] using hjG
    exact hjG'.trans (le_add_of_nonneg_right hH)
  have hnorm (v : Lp 𝕜 p (volume : Measure (Domain n))) (hv : ‖v‖ ≤ N) :
      ‖v‖ₑ ^ p.toReal ≤ R := by
    apply ENNReal.rpow_le_rpow _ ENNReal.toReal_nonneg
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hv
  have hz := hnorm _ hzero
  have hg : ∀ j : Fin n, ‖wholeLp (g.val.val (firstIndex j))‖ₑ ^ p.toReal ≤ R := by
    intro j
    exact hnorm _ ((norm_le_fractionalNorm s p (grad j)).trans (hgrad j))
  have hh : ‖h.val‖ₑ ^ p.toReal ≤ R :=
    hnorm _ ((norm_le_fractionalNorm s p h).trans (le_add_of_nonneg_left hG))
  have hge : ∀ j : Fin n, differenceEnergy s p (wholeLp (g.val.val (firstIndex j))) ≤ R := by
    intro j
    exact (differenceEnergy_le_fractionalNorm_rpow s p hp (grad j)).trans
      (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hgrad j)) ENNReal.toReal_nonneg)
  have hhe : differenceEnergy s p h.val ≤ R :=
    (differenceEnergy_le_fractionalNorm_rpow s p hp h).trans
      (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hG)) ENNReal.toReal_nonneg)
  have hgs : (∑ j : Fin n, ‖wholeLp (g.val.val (firstIndex j))‖ₑ ^ p.toReal) ≤ (n : ℝ≥0∞) * R := by
    calc
      _ ≤ ∑ _j : Fin n, R := Finset.sum_le_sum fun j _ => hg j
      _ = _ := by simp
  have hges : (∑ j : Fin n, differenceEnergy s p (wholeLp (g.val.val (firstIndex j)))) ≤
      (n : ℝ≥0∞) * R := by
    calc
      _ ≤ ∑ _j : Fin n, R := Finset.sum_le_sum fun j _ => hge j
      _ = _ := by simp
  calc
    _ ≤ R + (n : ℝ≥0∞) * R + R + (n : ℝ≥0∞) * R + R :=
      add_le_add (add_le_add (add_le_add (add_le_add hz hgs) hh) hges) hhe
    _ = (2 * (n : ℝ≥0∞) + 3) * R := by ring
    _ = _ := rfl

lemma jet_dataPower_factor_ne_top (n : ℕ) : (2 * (n : ℝ≥0∞) + 3) ≠ ∞ := by
  finiteness


lemma eLpNorm_toReal_le_of_lintegral_rpow_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f : X → 𝕜) (hf : AEStronglyMeasurable f μ)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (N : ℝ) (hN : 0 ≤ N)
    (hbound : (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ≤ C * ENNReal.ofReal N ^ p.toReal) :
    (eLpNorm f p μ).toReal ≤ C.toReal ^ (1 / p.toReal) * N := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hi : 0 ≤ 1 / p.toReal := (one_div_pos.mpr hpr).le
  have hpow : p.toReal * (1 / p.toReal) = 1 := by field_simp
  have he : eLpNorm f p μ ≤ C ^ (1 / p.toReal) * ENNReal.ofReal N := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf]
    calc
      _ ≤ (C * ENNReal.ofReal N ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow hbound hi
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hi, ← ENNReal.rpow_mul, hpow, ENNReal.rpow_one]
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hi hC) ENNReal.ofReal_ne_top) he
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hN] using hreal

lemma flat_eLpNorm_toReal_le_of_power_bound {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (D : Domain n × ℝ → 𝕜) (hD : Continuous D)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (N : ℝ) (hN : 0 ≤ N)
    (hbound : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ y : Domain n, ‖D (y,t)‖ₑ ^ p.toReal) ≤
      C * ENNReal.ofReal N ^ p.toReal) :
    (eLpNorm (fun x => D (flatCoordinates i x)) p
      (volume.restrict (upper i : Set (Domain (n + 1))))).toReal ≤
      C.toReal ^ (1 / p.toReal) * N := by
  apply eLpNorm_toReal_le_of_lintegral_rpow_bound _ p hp _
    (hD.comp (flatCoordinates i).continuous).aestronglyMeasurable C hC N hN
  simp only [Function.comp_apply]
  rw [upper_lintegral_flatCoordinates i _ (hD.enorm.measurable.pow_const _)]
  exact hbound


lemma average_hasDerivAt_zero_of_even_noncompact {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρe : ∀ y, ρ (-y) = ρ y) (f : Domain n → 𝕜)
    (hf : ContDiff ℝ 1 f) (x : Domain n) :
    HasDerivAt (fun t : ℝ => average ρ f (x, t)) 0 0 := by
  have hd := average_hasDerivAt_normal_noncompact ρ f hρ hρc hf x 0
  simpa only [zero_smul, sub_zero,
    integral_even_kernel_linear_zero ρ hρe (fderiv ℝ f x)] using hd

lemma flatJet_hasDerivAt_zero_noncompact {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f h : Domain n → 𝕜)
    (hχ : χ 0 = 1) (hχd : HasDerivAt χ 0 0)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρe : ∀ y, ρ (-y) = ρ y) (hρm : ∫ y, ρ y = 1)
    (hf : ContDiff ℝ 1 f) (hh : ContDiff ℝ 1 h) (x : Domain n) :
    HasDerivAt (fun t : ℝ => flatJet χ ρ f h (x, t)) (h x) 0 := by
  have hA := average_hasDerivAt_zero_of_even_noncompact ρ hρ hρc hρe f hf x
  have hB := average_hasDerivAt_normal_noncompact ρ h hρ hρc hh x 0
  have hd := hχd.smul (hA.add ((hasDerivAt_id (0 : ℝ)).smul hB))
  change HasDerivAt (fun t : ℝ => χ t •
    (SmoothLift.average ρ f (x, t) + t • SmoothLift.average ρ h (x, t))) _ 0 at hd
  simpa only [flatJet, SmoothLift.average, Pi.smul_apply', Pi.add_apply, id_eq, hχ, zero_smul,
    zero_add, add_zero, one_smul, sub_zero, integral_smul_const, hρm] using hd

lemma jetFunction_normal_boundary_noncompact {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (f h : Domain n → 𝕜)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (x : Domain n) :
    fderiv ℝ (jetFunction i f h) (i.insertNth 0 x) (coordinateVector i) = h x := by
  have hd := flatJet_hasDerivAt_zero_noncompact jetCutoff (jetMollifier n) f h jetCutoff_zero
    jetCutoff_hasDerivAt_zero (jetMollifier_contDiff n).continuous
    (jetMollifier_compactSupport n) (jetMollifier_neg n) (jetMollifier_integral n)
    (hf.of_le (by simp)) (hh.of_le (by simp)) x
  have hcurve := ((jetFunction_contDiff i f h hf hh).differentiable (by simp)
    (coordinateLine i (transverseFinEquiv i x) 0)).hasFDerivAt.comp_hasDerivAt 0
      (coordinateLine_hasDerivAt i (transverseFinEquiv i x) 0)
  have heq : (jetFunction i f h ∘ coordinateLine i (transverseFinEquiv i x)) =
      (fun t => flatJet jetCutoff (jetMollifier n) f h (x, t)) := by
    funext t
    dsimp only [Function.comp_apply]
    rw [coordinateLine_transverseFinEquiv]
    simp [jetFunction]
  rw [heq] at hcurve
  simpa only [coordinateLine_transverseFinEquiv] using hcurve.unique hd


lemma flatJet_first_partial {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f h : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h)
    (z : Domain n × ℝ) (b : Option (Fin n)) :
    fderiv ℝ (flatJet χ ρ f h) z (flatDirection b) =
      χ z.2 • fderiv ℝ (uncutJet ρ f h) z (flatDirection b) +
      (flatDirection b).2 • (deriv χ z.2 • uncutJet ρ f h z) := by
  rw [flatJet_eq_cutoff_uncut]
  exact cutoff_smul_fderiv χ (uncutJet ρ f h) hχ
    (uncutJet_contDiff ρ f h hρ hρc hf hh) z (flatDirection b)

/-- The normal component of a flat coordinate direction is zero or one. -/
lemma flatDirection_snd_smul_power_le {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (F : Domain n × ℝ → 𝕜) (b : Option (Fin n)) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
      ‖(flatDirection b).2 • F (x,t)‖ₑ ^ q) ≤
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖F (x,t)‖ₑ ^ q := by
  apply lintegral_mono
  intro t
  apply lintegral_mono
  intro x
  apply ENNReal.rpow_le_rpow _ hq
  cases b <;> simp [flatDirection]

/-- Full zeroth-order estimate for the actual cutoff simultaneous formula. -/
theorem flatJet_power_bound {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (ρ : Domain n → ℝ) (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ)
    (hρc : HasCompactSupport ρ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
      (u₀ : Lp 𝕜 p (volume : Measure (Domain n)))
      (u : Fin n → Lp 𝕜 p (volume : Measure (Domain n)))
      (v : Lp 𝕜 p (volume : Measure (Domain n))) (f h : Domain n → 𝕜),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f → ContDiff ℝ (↑(⊤ : ℕ∞)) h →
      u₀ =ᵐ[volume] f → v =ᵐ[volume] h →
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖flatJet jetCutoff ρ f h (x,t)‖ₑ ^ p.toReal) ≤
        C * jetDataPower p u₀ u v := by
  obtain ⟨C, hC, hb⟩ := cutoff_uncutJet_power_bound p hp jetCutoff
    jetCutoff_contDiff jetCutoff_compactSupport ρ hρ hρc
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ u₀ u v f h hf hh huf hvh
  exact (hb 𝕜 u₀ v f h hf hh huf hvh).trans
    (mul_le_mul' le_rfl (jetDataPower_value_le p u₀ u v))

/-- All first derivatives of the actual cutoff simultaneous formula admit
one bound by the complete boundary-data power. -/
theorem flatJet_first_power_bound {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (ρ : Domain n → ℝ) (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ)
    (hρc : HasCompactSupport ρ) (b : Option (Fin n)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
      (u₀ : Lp 𝕜 p (volume : Measure (Domain n)))
      (u : Fin n → Lp 𝕜 p (volume : Measure (Domain n)))
      (v : Lp 𝕜 p (volume : Measure (Domain n))) (f h : Domain n → 𝕜),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f → 
      ContDiff ℝ (↑(⊤ : ℕ∞)) h → 
      u₀ =ᵐ[volume] f →
      (∀ j, u j =ᵐ[volume] (fun x => fderiv ℝ f x (coordinateVector j))) →
      v =ᵐ[volume] h →
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖fderiv ℝ (flatJet jetCutoff ρ f h) (x,t) (flatDirection b)‖ₑ ^ p.toReal) ≤
        C * jetDataPower p u₀ u v := by
  have hq : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hχ' : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv jetCutoff) :=
    contDiff_infty_iff_deriv.mp jetCutoff_contDiff |>.2
  obtain ⟨G, hG, hg⟩ := cutoff_uncutJet_first_power_bound p hp jetCutoff
    jetCutoff_contDiff jetCutoff_compactSupport ρ hρ hρc b
  obtain ⟨V, hV, hv⟩ := cutoff_uncutJet_power_bound p hp (deriv jetCutoff)
    hχ' jetCutoff_compactSupport.deriv ρ hρ hρc
  let D : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (p.toReal - 1)
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  refine ⟨D * (G + V), ENNReal.mul_ne_top hD (ENNReal.add_ne_top.mpr ⟨hG,hV⟩), ?_⟩
  intro 𝕜 _ u₀ u v f h hf hh huf hdu hvh
  have hJ := uncutJet_contDiff ρ f h hρ hρc hf hh
  let A : Domain n × ℝ → 𝕜 := fun z =>
    jetCutoff z.2 • fderiv ℝ (uncutJet ρ f h) z (flatDirection b)
  let B : Domain n × ℝ → 𝕜 := fun z =>
    (flatDirection b).2 • (deriv jetCutoff z.2 • uncutJet ρ f h z)
  have heq : (fun z => fderiv ℝ (flatJet jetCutoff ρ f h) z (flatDirection b)) =
      A + B := by
    funext z
    exact flatJet_first_partial jetCutoff ρ f h jetCutoff_contDiff hρ hρc hf hh z b
  have hB : Continuous B :=
    ((hχ'.continuous.comp continuous_snd).smul hJ.continuous).const_smul _
  have hA_bound : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖A (x,t)‖ₑ ^ p.toReal) ≤
      G * jetDataPower p u₀ u v :=
    (hg 𝕜 u v f h hf hh hdu hvh).trans
      (mul_le_mul' le_rfl (jetDataPower_first_le p u₀ u v))
  have hB_bound : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖B (x,t)‖ₑ ^ p.toReal) ≤
      V * jetDataPower p u₀ u v := by
    exact (flatDirection_snd_smul_power_le
      (fun z => deriv jetCutoff z.2 • uncutJet ρ f h z) b p.toReal (by linarith)).trans
      ((hv 𝕜 u₀ v f h hf hh huf hvh).trans
        (mul_le_mul' le_rfl (jetDataPower_value_le p u₀ u v)))
  have heq' := congrArg (fun F : Domain n × ℝ → 𝕜 =>
    ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖F (x,t)‖ₑ ^ p.toReal) heq
  rw [heq']
  calc
    _ ≤ D * ((∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖A (x,t)‖ₑ ^ p.toReal) +
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖B (x,t)‖ₑ ^ p.toReal) := by
      exact flat_lintegral_sum_rpow_le A B p.toReal hq (hB.enorm.measurable.pow_const _)
    _ ≤ D * (G * jetDataPower p u₀ u v + V * jetDataPower p u₀ u v) :=
      mul_le_mul' le_rfl (add_le_add hA_bound hB_bound)
    _ = (D * (G + V)) * jetDataPower p u₀ u v := by rw [← add_mul, mul_assoc]

lemma classicalDerivative_firstIndex {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Domain d → 𝕜) (j : Fin d) :
    Smoothing.classicalDerivative (firstIndex j) f =
      fun x => fderiv ℝ f x (coordinateVector j) := by
  simp [Smoothing.classicalDerivative, natIndex_firstIndex, multiIndexWord_single, partialFunction]

lemma higherFractional_gradient_representative {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (g : HigherFractionalSpace 𝕜 n s p) (f : Domain n → 𝕜)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (hg : wholeLp (g.val.val (zeroIndex n 1)) =ᵐ[volume] f) (j : Fin n) :
    wholeLp (g.val.val (firstIndex j)) =ᵐ[volume]
      (fun x => fderiv ℝ f x (coordinateVector j)) := by
  let v := smoothCompactSobolev (⊤ : Opens (Domain n)) 1 p f hf hfc
  have hv0 := smoothCompactSobolev_coe (⊤ : Opens (Domain n)) 1 p f hf hfc (zeroIndex n 1)
  simp only [classicalDerivative_zero, Opens.coe_top, Measure.restrict_univ] at hv0
  have hg0 : g.val.val (zeroIndex n 1) =ᵐ[volume] f :=
    (wholeLp_representative (g.val.val (zeroIndex n 1))).symm.trans hg
  have he : g.val = v := by
    apply sobolev_underlying_injective 𝕜 n ⊤ 1 p
    apply Lp.ext
    simpa only [Opens.coe_top, Measure.restrict_univ] using hg0.trans hv0.symm
  have hvj := smoothCompactSobolev_coe (⊤ : Opens (Domain n)) 1 p f hf hfc (firstIndex j)
  simp only [classicalDerivative_firstIndex, Opens.coe_top, Measure.restrict_univ] at hvj
  have hj : g.val.val (firstIndex j) =ᵐ[volume]
      (fun x => fderiv ℝ f x (coordinateVector j)) := by
    rw [he]
    exact hvj
  exact (wholeLp_representative (g.val.val (firstIndex j))).trans hj


lemma smoothJetLift_norm_le_of_flat_power_bounds {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f h : Domain n → 𝕜)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (hhc : HasCompactSupport h)
    (C₀ C₁ C₂ : ℝ≥0∞) (hC₀ : C₀ ≠ ∞) (hC₁ : C₁ ≠ ∞) (hC₂ : C₂ ≠ ∞)
    (N : ℝ) (hN : 0 ≤ N)
    (hzero : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖flatJet jetCutoff (jetMollifier n) f h (x,t)‖ₑ ^ p.toReal) ≤
      C₀ * ENNReal.ofReal N ^ p.toReal)
    (hfirst : ∀ a : Option (Fin n),
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖fderiv ℝ (flatJet jetCutoff (jetMollifier n) f h) (x,t) (flatDirection a)‖ₑ ^ p.toReal) ≤
      C₁ * ENNReal.ofReal N ^ p.toReal)
    (hsecond : ∀ a b : Option (Fin n),
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖secondFlatPartial (flatJet jetCutoff (jetMollifier n) f h) a b (x,t)‖ₑ ^ p.toReal) ≤
      C₂ * ENNReal.ofReal N ^ p.toReal) :
    ‖smoothJetLift i p f h hf hfc hh hhc‖ ≤
      (Fintype.card (DerivativeIndex (n + 1) 2) : ℝ) *
        (C₀.toReal ^ (1 / p.toReal) + C₁.toReal ^ (1 / p.toReal) +
          C₂.toReal ^ (1 / p.toReal)) * N := by
  let F := flatJet jetCutoff (jetMollifier n) f h
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F :=
    flatJet_contDiff jetCutoff (jetMollifier n) f h jetCutoff_contDiff
      (jetMollifier_contDiff n) (jetMollifier_compactSupport n) hf hh
  apply secondJet_norm_le_of_classical_bounds _ (jetFunction i f h)
    (fun α => smoothJetLift_coe i p f h hf hfc hh hhc α)
    (C₀.toReal ^ (1 / p.toReal)) (C₁.toReal ^ (1 / p.toReal))
    (C₂.toReal ^ (1 / p.toReal)) N
    (by positivity) (by positivity) (by positivity) hN
  · exact flat_eLpNorm_toReal_le_of_power_bound i p hp F hF.continuous C₀ hC₀ N hN hzero
  · intro j
    obtain ⟨a, ha⟩ := flatCoordinatesCLM_direction i j
    have hfun : (fun x => fderiv ℝ (jetFunction i f h) x (coordinateVector j)) =
        fun x => fderiv ℝ F (flatCoordinates i x) (flatDirection a) :=
      funext (jetFunction_fderiv_flat i j f h hF a ha)
    rw [hfun]
    exact flat_eLpNorm_toReal_le_of_power_bound i p hp
      (fun z => fderiv ℝ F z (flatDirection a))
      ((hF.continuous_fderiv (by simp)).clm_apply continuous_const) C₁ hC₁ N hN (hfirst a)
  · intro j k
    obtain ⟨a, ha⟩ := flatCoordinatesCLM_direction i j
    obtain ⟨b, hb⟩ := flatCoordinatesCLM_direction i k
    have hfun : (fun x => fderiv ℝ (fun y => fderiv ℝ (jetFunction i f h) y (coordinateVector k)) x
        (coordinateVector j)) =
        fun x => secondFlatPartial F a b (flatCoordinates i x) :=
      funext (jetFunction_second_fderiv_flat i j k f h hF a b ha hb)
    rw [hfun]
    exact flat_eLpNorm_toReal_le_of_power_bound i p hp
      (secondFlatPartial F a b) (secondFlatPartial_continuous F hF a b) C₂ hC₂ N hN (hsecond a b)


/-- The complete second-derivative estimate for the actual cutoff formula,
including all cutoff derivatives. The constant is independent of the scalar
field, representatives and data, in every tangential dimension. -/
theorem flatJet_second_power_bound {n : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (ρ : Domain n → ℝ) (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ)
    (hρc : HasCompactSupport ρ) (a b : Option (Fin n)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (𝕜 : Type) [RCLike 𝕜]
      (u₀ : Lp 𝕜 p (volume : Measure (Domain n)))
      (u : Fin n → Lp 𝕜 p (volume : Measure (Domain n)))
      (v : Lp 𝕜 p (volume : Measure (Domain n))) (f h : Domain n → 𝕜),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f → 
      ContDiff ℝ (↑(⊤ : ℕ∞)) h → 
      u₀ =ᵐ[volume] f →
      (∀ j, u j =ᵐ[volume] (fun x => fderiv ℝ f x (coordinateVector j))) →
      v =ᵐ[volume] h →
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖secondFlatPartial (flatJet jetCutoff ρ f h) a b (x,t)‖ₑ ^ p.toReal) ≤
        C * jetDataPower p u₀ u v := by
  have hq : 1 ≤ p.toReal :=
    le_of_lt ((ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).mpr hp1)
  have hχ' : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv jetCutoff) :=
    contDiff_infty_iff_deriv.mp jetCutoff_contDiff |>.2
  have hχ'' : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv (deriv jetCutoff)) :=
    contDiff_infty_iff_deriv.mp hχ' |>.2
  have hχ'c := jetCutoff_compactSupport.deriv
  have hχ''c := hχ'c.deriv
  obtain ⟨G, hG, hg⟩ := uncutJet_second_energy_bound p hp1 hp ρ hρ hρc a b
  obtain ⟨A, hA, ha⟩ := cutoff_uncutJet_first_power_bound p hp _ hχ' hχ'c ρ hρ hρc a
  obtain ⟨B, hB, hb⟩ := cutoff_uncutJet_first_power_bound p hp _ hχ' hχ'c ρ hρ hρc b
  obtain ⟨V, hV, hv⟩ := cutoff_uncutJet_power_bound p hp _ hχ'' hχ''c ρ hρ hρc
  let D : ℝ≥0∞ := (4 : ℝ≥0∞) ^ (p.toReal - 1)
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  have hsum : G + B + A + V ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨hG, hB⟩, hA⟩, hV⟩
  refine ⟨D * (G + B + A + V), ENNReal.mul_ne_top hD hsum, ?_⟩
  intro 𝕜 _ u₀ u v f h hf hh huf hdu hvh
  have hJ := uncutJet_contDiff ρ f h hρ hρc hf hh
  have hprincipal :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖jetCutoff t • secondFlatPartial (uncutJet ρ f h) a b (x,t)‖ₑ ^ p.toReal) ≤
        G * jetDataPower p u₀ u v := by
    exact (jetCutoff_flat_power_le _ _ (by linarith)).trans
      ((hg 𝕜 u v f h hf hh hdu hvh).trans
        (mul_le_mul' le_rfl (jetDataPower_second_le p u₀ u v)))
  have hfirstA :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖deriv jetCutoff t • fderiv ℝ (uncutJet ρ f h) (x,t) (flatDirection a)‖ₑ ^ p.toReal) ≤
        A * jetDataPower p u₀ u v :=
    (ha 𝕜 u v f h hf hh hdu hvh).trans
      (mul_le_mul' le_rfl (jetDataPower_first_le p u₀ u v))
  have hfirstB :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖deriv jetCutoff t • fderiv ℝ (uncutJet ρ f h) (x,t) (flatDirection b)‖ₑ ^ p.toReal) ≤
        B * jetDataPower p u₀ u v :=
    (hb 𝕜 u v f h hf hh hdu hvh).trans
      (mul_le_mul' le_rfl (jetDataPower_first_le p u₀ u v))
  have hvalue :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖deriv (deriv jetCutoff) t • uncutJet ρ f h (x,t)‖ₑ ^ p.toReal) ≤
        V * jetDataPower p u₀ u v :=
    (hv 𝕜 u₀ v f h hf hh huf hvh).trans
      (mul_le_mul' le_rfl (jetDataPower_value_le p u₀ u v))
  let J := uncutJet ρ f h
  let T : Fin 4 → Domain n × ℝ → 𝕜 := ![
    (fun z => jetCutoff z.2 • secondFlatPartial J a b z),
    (fun z => (flatDirection a).2 •
      (deriv jetCutoff z.2 • fderiv ℝ J z (flatDirection b))),
    (fun z => (flatDirection b).2 •
      (deriv jetCutoff z.2 • fderiv ℝ J z (flatDirection a))),
    (fun z => (flatDirection b).2 • ((flatDirection a).2 •
      (deriv (deriv jetCutoff) z.2 • J z)))]
  have hfirst (c : Option (Fin n)) :
      Continuous (fun z => fderiv ℝ J z (flatDirection c)) :=
    (hJ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hT : ∀ k, Continuous (T k) := by
    intro k
    fin_cases k
    · exact (jetCutoff_contDiff.continuous.comp continuous_snd).smul
        (secondFlatPartial_continuous J hJ a b)
    · exact ((hχ'.continuous.comp continuous_snd).smul (hfirst b)).const_smul _
    · exact ((hχ'.continuous.comp continuous_snd).smul (hfirst a)).const_smul _
    · exact (((hχ''.continuous.comp continuous_snd).smul hJ.continuous).const_smul _).const_smul _
  have heq (z : Domain n × ℝ) :
      secondFlatPartial (flatJet jetCutoff ρ f h) a b z = ∑ k, T k z := by
    simpa [Fin.sum_univ_four, T, J] using
      flatJet_second_partial jetCutoff ρ f h jetCutoff_contDiff hρ hρc hf hh z a b
  have ht0 : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖T 0 (x,t)‖ₑ ^ p.toReal) ≤
      G * jetDataPower p u₀ u v := hprincipal
  have ht1 : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖T 1 (x,t)‖ₑ ^ p.toReal) ≤
      B * jetDataPower p u₀ u v :=
    (flatDirection_snd_smul_power_le
      (fun z => deriv jetCutoff z.2 • fderiv ℝ J z (flatDirection b))
      a p.toReal (by linarith)).trans hfirstB
  have ht2 : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖T 2 (x,t)‖ₑ ^ p.toReal) ≤
      A * jetDataPower p u₀ u v :=
    (flatDirection_snd_smul_power_le
      (fun z => deriv jetCutoff z.2 • fderiv ℝ J z (flatDirection a))
      b p.toReal (by linarith)).trans hfirstA
  have ht3 : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖T 3 (x,t)‖ₑ ^ p.toReal) ≤
      V * jetDataPower p u₀ u v :=
    (flatDirection_snd_smul_power_le
      (fun z => (flatDirection a).2 • (deriv (deriv jetCutoff) z.2 • J z))
      b p.toReal (by linarith)).trans
      ((flatDirection_snd_smul_power_le
        (fun z => deriv (deriv jetCutoff) z.2 • J z)
        a p.toReal (by linarith)).trans hvalue)
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖∑ k, T k (x,t)‖ₑ ^ p.toReal := by
      apply lintegral_congr
      intro t
      apply lintegral_congr
      intro x
      rw [heq]
    _ ≤ D * ∑ k, ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, ‖T k (x,t)‖ₑ ^ p.toReal := by
      simpa [D] using flat_lintegral_finite_sum_rpow_le T hT p.toReal hq
    _ ≤ D * (G * jetDataPower p u₀ u v + B * jetDataPower p u₀ u v +
        A * jetDataPower p u₀ u v + V * jetDataPower p u₀ u v) := by
      rw [Fin.sum_univ_four]
      exact mul_le_mul' le_rfl (add_le_add (add_le_add (add_le_add ht0 ht1) ht2) ht3)
    _ = D * (G + B + A + V) * jetDataPower p u₀ u v := by
      rw [← add_mul, ← add_mul, ← add_mul, mul_assoc]


/-- Uniform full W^{2,p} estimate for the simultaneous jet formula on smooth
compactly supported data representing the original higher/fractional classes.
The arbitrary-data extension is a separate closure step. -/
theorem smoothJetLift_full_norm_bound (n : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (i : Fin (n + 1))
      (g : HigherFractionalSpace 𝕜 n (2 - 1 / p.toReal) p)
      (k : FractionalSpace 𝕜 n (1 - 1 / p.toReal) p)
      (f h : Domain n → 𝕜)
      (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
      (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (hhc : HasCompactSupport h),
      wholeLp (g.val.val (zeroIndex n 1)) =ᵐ[volume] f →
      k.val =ᵐ[volume] h →
      ‖smoothJetLift i p f h hf hfc hh hhc‖ ≤ C *
        (higherFractionalNorm (2 - 1 / p.toReal) p g + fractionalNorm (1 - 1 / p.toReal) p k) := by
  classical
  obtain ⟨A, hA, ha⟩ := flatJet_power_bound (n := n) p hp (jetMollifier n)
    (jetMollifier_contDiff n) (jetMollifier_compactSupport n)
  have hb (a : Option (Fin n)) := flatJet_first_power_bound p hp (jetMollifier n)
    (jetMollifier_contDiff n) (jetMollifier_compactSupport n) a
  choose B hB hb using hb
  have hc (ab : Option (Fin n) × Option (Fin n)) := flatJet_second_power_bound p hp1 hp
    (jetMollifier n) (jetMollifier_contDiff n) (jetMollifier_compactSupport n) ab.1 ab.2
  choose D hD hd using hc
  let K : ℝ≥0∞ := 2 * (n : ℝ≥0∞) + 3
  have hK : K ≠ ∞ := jet_dataPower_factor_ne_top n
  let C₀ : ℝ≥0∞ := A * K
  let C₁ : ℝ≥0∞ := (∑ a, B a) * K
  let C₂ : ℝ≥0∞ := (∑ ab, D ab) * K
  have hC₀ : C₀ ≠ ∞ := ENNReal.mul_ne_top hA hK
  have hC₁ : C₁ ≠ ∞ := ENNReal.mul_ne_top
    (ne_of_lt (ENNReal.sum_lt_top.mpr (fun a _ => lt_top_iff_ne_top.mpr (hB a)))) hK
  have hC₂ : C₂ ≠ ∞ := ENNReal.mul_ne_top
    (ne_of_lt (ENNReal.sum_lt_top.mpr (fun ab _ => lt_top_iff_ne_top.mpr (hD ab)))) hK
  refine ⟨(Fintype.card (DerivativeIndex (n + 1) 2) : ℝ) *
    (C₀.toReal ^ (1 / p.toReal) + C₁.toReal ^ (1 / p.toReal) + C₂.toReal ^ (1 / p.toReal)),
    by positivity, ?_⟩
  intro 𝕜 _ i g k f h hf hfc hh hhc hgf hkh
  let N := higherFractionalNorm (2 - 1 / p.toReal) p g + fractionalNorm (1 - 1 / p.toReal) p k
  have hN : 0 ≤ N := add_nonneg (higherFractionalNorm_nonneg _ p g) (fractionalNorm_nonneg _ p k)
  have hgrad : ∀ j, wholeLp (g.val.val (firstIndex j)) =ᵐ[volume]
      (fun x => fderiv ℝ f x (coordinateVector j)) := by
    exact fun j => higherFractional_gradient_representative g f hf hfc hgf j
  have hpower : jetDataPower p (wholeLp (g.val.val (zeroIndex n 1)))
      (fun j => wholeLp (g.val.val (firstIndex j))) k.val ≤ K * ENNReal.ofReal N ^ p.toReal :=
    jet_dataPower_le p hp g k
  apply smoothJetLift_norm_le_of_flat_power_bounds i p hp f h hf hfc hh hhc
    C₀ C₁ C₂ hC₀ hC₁ hC₂ N hN
  · exact (ha 𝕜 (wholeLp (g.val.val (zeroIndex n 1)))
        (fun j => wholeLp (g.val.val (firstIndex j))) k.val f h hf hh hgf hkh).trans
      (by simpa only [C₀, mul_assoc] using mul_le_mul' (le_refl A) hpower)
  · intro a
    have hba : B a ≤ ∑ b, B b :=
      Finset.single_le_sum (fun b _ => bot_le) (Finset.mem_univ a)
    exact (hb a 𝕜 (wholeLp (g.val.val (zeroIndex n 1)))
        (fun j => wholeLp (g.val.val (firstIndex j))) k.val f h hf hh hgf hgrad hkh).trans
      (by simpa only [C₁, mul_assoc] using mul_le_mul' hba hpower)
  · intro a b
    have hdb : D (a,b) ≤ ∑ ab, D ab :=
      Finset.single_le_sum (fun ab _ => bot_le) (Finset.mem_univ (a,b))
    exact (hd (a,b) 𝕜 (wholeLp (g.val.val (zeroIndex n 1)))
        (fun j => wholeLp (g.val.val (firstIndex j))) k.val f h hf hh hgf hgrad hkh).trans
      (by simpa only [C₂, mul_assoc] using mul_le_mul' hdb hpower)

lemma flatJet_add {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f₁ f₂ h₁ h₂ : Domain n → 𝕜)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hh₁ : Continuous h₁) (hh₂ : Continuous h₂) (z : Domain n × ℝ) :
    flatJet χ ρ (f₁ + f₂) (h₁ + h₂) z =
      flatJet χ ρ f₁ h₁ z + flatJet χ ρ f₂ h₂ z := by
  change χ z.2 • (SmoothLift.average ρ (f₁ + f₂) z +
    z.2 • SmoothLift.average ρ (h₁ + h₂) z) =
      χ z.2 • (SmoothLift.average ρ f₁ z + z.2 • SmoothLift.average ρ h₁ z) +
        χ z.2 • (SmoothLift.average ρ f₂ z + z.2 • SmoothLift.average ρ h₂ z)
  rw [average_add ρ f₁ f₂ hρ hρc hf₁ hf₂, average_add ρ h₁ h₂ hρ hρc hh₁ hh₂]
  module

lemma flatJet_smul {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (c : 𝕜) (f h : Domain n → 𝕜)
    (z : Domain n × ℝ) :
    flatJet χ ρ (c • f) (c • h) z = c • flatJet χ ρ f h z := by
  change χ z.2 • (SmoothLift.average ρ (c • f) z + z.2 • SmoothLift.average ρ (c • h) z) =
    c • (χ z.2 • (SmoothLift.average ρ f z + z.2 • SmoothLift.average ρ h z))
  rw [average_smul, average_smul]
  simp only [smul_add, smul_comm (χ z.2) c, smul_comm z.2 c]

lemma jetFunction_add {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (f₁ f₂ h₁ h₂ : Domain n → 𝕜)
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hh₁ : Continuous h₁) (hh₂ : Continuous h₂) (x : Domain (n + 1)) :
    jetFunction i (f₁ + f₂) (h₁ + h₂) x =
      jetFunction i f₁ h₁ x + jetFunction i f₂ h₂ x :=
  flatJet_add jetCutoff (jetMollifier n) f₁ f₂ h₁ h₂
    (jetMollifier_contDiff n).continuous (jetMollifier_compactSupport n) hf₁ hf₂ hh₁ hh₂ _

lemma jetFunction_smul {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (c : 𝕜) (f h : Domain n → 𝕜) (x : Domain (n + 1)) :
    jetFunction i (c • f) (c • h) x = c • jetFunction i f h x :=
  flatJet_smul jetCutoff (jetMollifier n) c f h _

/-- Simultaneous addition of the two smooth data respects the actual
order-two derivative-graph lift, including all its components. -/
lemma smoothJetLift_add {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (i : Fin (n + 1))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f₁ f₂ h₁ h₂ : Domain n → 𝕜)
    (hf₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) f₁) (hfc₁ : HasCompactSupport f₁)
    (hf₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) f₂) (hfc₂ : HasCompactSupport f₂)
    (hh₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) h₁) (hhc₁ : HasCompactSupport h₁)
    (hh₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) h₂) (hhc₂ : HasCompactSupport h₂) :
    smoothJetLift i p (f₁ + f₂) (h₁ + h₂) (hf₁.add hf₂) (hfc₁.add hfc₂)
        (hh₁.add hh₂) (hhc₁.add hhc₂) =
      smoothJetLift i p f₁ h₁ hf₁ hfc₁ hh₁ hhc₁ +
        smoothJetLift i p f₂ h₂ hf₂ hfc₂ hh₂ hhc₂ := by
  apply sobolev_underlying_injective 𝕜 (n + 1) (upper i) 2 p
  change (smoothJetLift i p (f₁ + f₂) (h₁ + h₂) (hf₁.add hf₂) (hfc₁.add hfc₂)
      (hh₁.add hh₂) (hhc₁.add hhc₂)).val (zeroIndex (n + 1) 2) =
    (smoothJetLift i p f₁ h₁ hf₁ hfc₁ hh₁ hhc₁).val (zeroIndex (n + 1) 2) +
      (smoothJetLift i p f₂ h₂ hf₂ hfc₂ hh₂ hhc₂).val (zeroIndex (n + 1) 2)
  apply Lp.ext
  have hs := smoothJetLift_coe i p (f₁ + f₂) (h₁ + h₂) (hf₁.add hf₂)
    (hfc₁.add hfc₂) (hh₁.add hh₂) (hhc₁.add hhc₂) (zeroIndex (n + 1) 2)
  have hae₁ := smoothJetLift_coe i p f₁ h₁ hf₁ hfc₁ hh₁ hhc₁ (zeroIndex (n + 1) 2)
  have hae₂ := smoothJetLift_coe i p f₂ h₂ hf₂ hfc₂ hh₂ hhc₂ (zeroIndex (n + 1) 2)
  simp only [classicalDerivative_zero] at hs hae₁ hae₂
  filter_upwards [hs, hae₁, hae₂,
    Lp.coeFn_add ((smoothJetLift i p f₁ _ hf₁ hfc₁ hh₁ hhc₁).val (zeroIndex (n + 1) 2))
      ((smoothJetLift i p f₂ _ hf₂ hfc₂ hh₂ hhc₂).val (zeroIndex (n + 1) 2))]
      with x hsx h₁x h₂x hadd
  simp only [Pi.add_apply] at hadd
  rw [hsx, hadd, h₁x, h₂x]
  exact jetFunction_add i _ _ _ _ hf₁.continuous hf₂.continuous hh₁.continuous hh₂.continuous x

/-- Scalar multiplication of both data respects the actual smooth lift. -/
lemma smoothJetLift_smul {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (i : Fin (n + 1))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (c : 𝕜) (f h : Domain n → 𝕜)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (hhc : HasCompactSupport h) :
    smoothJetLift i p (c • f) (c • h) (hf.const_smul c) hfc.smul_left
        (hh.const_smul c) hhc.smul_left = c • smoothJetLift i p f h hf hfc hh hhc := by
  apply sobolev_underlying_injective 𝕜 (n + 1) (upper i) 2 p
  change (smoothJetLift i p (c • f) (c • h) (hf.const_smul c) hfc.smul_left
      (hh.const_smul c) hhc.smul_left).val (zeroIndex (n + 1) 2) =
    c • (smoothJetLift i p f h hf hfc hh hhc).val (zeroIndex (n + 1) 2)
  apply Lp.ext
  have hs := smoothJetLift_coe i p (c • f) (c • h) (hf.const_smul c) hfc.smul_left
    (hh.const_smul c) hhc.smul_left (zeroIndex (n + 1) 2)
  have hu := smoothJetLift_coe i p f h hf hfc hh hhc (zeroIndex (n + 1) 2)
  simp only [classicalDerivative_zero] at hs hu
  filter_upwards [hs, hu,
    Lp.coeFn_smul c ((smoothJetLift i p f h hf hfc hh hhc).val (zeroIndex (n + 1) 2))]
      with x hsx hux hsmul
  simp only [Pi.smul_apply] at hsmul
  rw [hsx, hsmul, hux]
  exact jetFunction_smul i c f h x

end ExpandedFA.PartIV.SecondTraceFlat



noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal Distributions

namespace ExpandedFA.PartIV.SecondTraceFlat
open ExpandedFA.Distributions ExpandedFA.Sobolev
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

lemma smoothDistribution_partial {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} (f : Domain d → 𝕜)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) :
    regularDistribution (Ω := Ω) volume (partialFunction [i] f) =
      -(regularDistribution (Ω := Ω) volume f).comp (testPartialCLM [i]) := by
  ext φ
  have hdf : Continuous (partialFunction [i] f) :=
    (Smoothing.partialFunction_contDiff [i] f hf).continuous
  have h₁ : Integrable (fun x => fderiv ℝ φ x (coordinateVector i) * f x) := by
    have hi := (testPartialCLM [i] φ).integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜)
      ((hf.continuous.locallyIntegrable (μ := volume)).locallyIntegrableOn Ω)
    change Integrable (fun x => testPartialCLM [i] φ x * f x) at hi
    simpa only [testPartial_single_apply] using hi
  have h₂ : Integrable (fun x => φ x * fderiv ℝ f x (coordinateVector i)) := by
    exact φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜)
      (hdf.locallyIntegrable.locallyIntegrableOn _)
  have h₃ : Integrable (fun x => φ x * f x) :=
    φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜)
      ((hf.continuous.locallyIntegrable (μ := volume)).locallyIntegrableOn Ω)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h₁ h₂ h₃
    (fun x _ => φ.contDiff.differentiable (by simp) x)
    (fun x _ => hf.differentiable (by simp) x)
  rw [regularDistribution_apply volume _ (hdf.locallyIntegrable.locallyIntegrableOn _)]
  change (∫ x, partialFunction [i] f x * φ x) =
    -(regularDistribution (Ω := Ω) volume f (testPartialCLM [i] φ))
  rw [regularDistribution_apply volume f (hf.continuous.locallyIntegrable.locallyIntegrableOn _)]
  simpa only [partialFunction, testPartial_single_apply, mul_comm] using h

lemma smoothDistribution_derivative {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} (w : List (Fin d)) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    distributionDerivative 𝕜 d Ω w (regularDistribution volume f) =
      regularDistribution volume (partialFunction w.reverse f) := by
  induction w generalizing f with
  | nil => exact distributionDerivative_nil _
  | cons i w ih =>
    rw [distributionDerivative_cons, ← smoothDistribution_partial f hf i,
      ih (partialFunction [i] f) (Smoothing.partialFunction_contDiff [i] f hf)]
    congr 1
    funext x
    simp only [List.reverse_cons]
    have ha : ∀ (a b : List (Fin d)) (q : Domain d → 𝕜),
        partialFunction (a ++ b) q = partialFunction a (partialFunction b q) := by
      intro a b q
      induction a with
      | nil => rfl
      | cons j a ih =>
        change (fun x => fderiv ℝ (partialFunction (a ++ b) q) x (coordinateVector j)) = _
        rw [ih]
        rfl
    exact congrFun (ha w.reverse [i] f).symm x

lemma lpDistribution_smooth_toLp {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Domain d → 𝕜) (hf : Continuous f)
    (hfp : MemLp f p (volume.restrict (Ω : Set (Domain d)))) :
    lpDistribution (hfp.toLp f) = regularDistribution volume f := by
  ext φ
  rw [lpDistribution_apply,
    regularDistribution_apply volume f (hf.locallyIntegrable.locallyIntegrableOn _)]
  calc
    (∫ x in (Ω : Set (Domain d)), φ x * hfp.toLp f x) =
        ∫ x in (Ω : Set (Domain d)), f x * φ x := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hfp] with x hx
      rw [hx, mul_comm]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by simp [φ.zero_on_compl hx])

/-- An ambient smooth function with all its prescribed derivatives in Lp
defines an element of the actual Sobolev graph, without a support assumption. -/
def smoothLpSobolev {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Domain d → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hmem : ∀ α : DerivativeIndex d m, MemLp (Smoothing.classicalDerivative α f)
      p (volume.restrict (Ω : Set (Domain d)))) : SpaceValue 𝕜 d Ω m p :=
  ⟨WithLp.toLp 1 (fun α => (hmem α).toLp (Smoothing.classicalDerivative α f)), by
    intro α
    change lpDistribution ((hmem α).toLp (Smoothing.classicalDerivative α f)) =
      distributionDerivative 𝕜 d Ω (multiIndexWord (natIndex α))
        (lpDistribution ((hmem (zeroIndex d m)).toLp
          (Smoothing.classicalDerivative (zeroIndex d m) f)))
    have hz : Smoothing.classicalDerivative (zeroIndex d m) f = f := by
      have hw : multiIndexWord (natIndex (zeroIndex d m)) = [] := by
        apply List.length_eq_zero_iff.mp
        simp [natIndex, zeroIndex]
      simp [Smoothing.classicalDerivative, hw, partialFunction]
    have ha : lpDistribution ((hmem α).toLp (Smoothing.classicalDerivative α f)) =
        regularDistribution volume (Smoothing.classicalDerivative α f) :=
      lpDistribution_smooth_toLp _ (Smoothing.partialFunction_contDiff _ f hf).continuous _
    have h0 : lpDistribution ((hmem (zeroIndex d m)).toLp
        (Smoothing.classicalDerivative (zeroIndex d m) f)) =
        regularDistribution volume (Smoothing.classicalDerivative (zeroIndex d m) f) :=
      lpDistribution_smooth_toLp _ (Smoothing.partialFunction_contDiff _ f hf).continuous _
    have h0' := h0.trans (congrArg (regularDistribution (Ω := Ω) volume) hz)
    exact ha.trans ((smoothDistribution_derivative
        (Ω := Ω) (multiIndexWord (natIndex α)) f hf).symm.trans
          (congrArg (distributionDerivative 𝕜 d Ω (multiIndexWord (natIndex α))) h0'.symm))
⟩

lemma smoothLpSobolev_coe {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Domain d → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hmem : ∀ α : DerivativeIndex d m, MemLp (Smoothing.classicalDerivative α f)
      p (volume.restrict (Ω : Set (Domain d)))) (α : DerivativeIndex d m) :
    (smoothLpSobolev Ω m p f hf hmem).val α =ᵐ[
      volume.restrict (Ω : Set (Domain d))] Smoothing.classicalDerivative α f :=
  MemLp.coeFn_toLp (hmem α)

end ExpandedFA.PartIV.SecondTraceFlat


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace ExpandedFA.PartIV.SecondTraceFlat
open ExpandedFA.Distributions ExpandedFA.Sobolev
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- The same multi-index in the order-two graph. -/
def orderOneToTwo {d : ℕ} (α : DerivativeIndex d 1) : DerivativeIndex d 2 :=
  boundedIndex (natIndex α) (α.property.trans (by omega))

@[simp] lemma natIndex_orderOneToTwo {d : ℕ} (α : DerivativeIndex d 1) :
    natIndex (orderOneToTwo α) = natIndex α := rfl

@[simp] lemma orderOneToTwo_zero (d : ℕ) :
    orderOneToTwo (zeroIndex d 1) = zeroIndex d 2 := by
  apply Subtype.ext
  funext j
  apply Fin.ext
  rfl

def orderOnePart {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 2 p) : SpaceValue 𝕜 d Ω 1 p :=
  ⟨WithLp.toLp 1 (fun α => u.val (orderOneToTwo α)), by
    intro α
    change lpDistributionLM (u.val (orderOneToTwo α)) = _
    simpa only [natIndex_orderOneToTwo, orderOneToTwo_zero] using u.property (orderOneToTwo α)⟩

@[simp] lemma orderOnePart_apply {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 2 p) (α : DerivativeIndex d 1) :
    (orderOnePart u).val α = u.val (orderOneToTwo α) := rfl

lemma orderOnePart_norm_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 2 p) :
    ‖orderOnePart u‖ ≤ Fintype.card (DerivativeIndex d 1) * ‖u‖ := by
  rw [sobolev_norm_formula]
  calc
    (∑ α : DerivativeIndex d 1, ‖(orderOnePart u).val α‖) ≤ ∑ _ : DerivativeIndex d 1, ‖u‖ :=
      Finset.sum_le_sum (fun α _ => PiLp.norm_apply_le u.val (orderOneToTwo α))
    _ = _ := by simp

def orderOnePartCLM (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : SpaceValue 𝕜 d Ω 2 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p :=
  LinearMap.mkContinuous
    { toFun := orderOnePart
      map_add' := fun u v => by apply Subtype.ext; apply PiLp.ext; intro α; rfl
      map_smul' := fun c u => by apply Subtype.ext; apply PiLp.ext; intro α; rfl }
    (Fintype.card (DerivativeIndex d 1)) orderOnePart_norm_le

/-- Add one coordinate derivative to an order-one multi-index. -/
def derivativePartIndex {d : ℕ} (i : Fin d) (α : DerivativeIndex d 1) : DerivativeIndex d 2 :=
  boundedIndex (natIndex α + Pi.single i 1) (by
    classical
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    simpa [natIndex] using Nat.add_le_add_right α.property 1)

@[simp] lemma natIndex_derivativePartIndex {d : ℕ} (i : Fin d) (α : DerivativeIndex d 1) :
    natIndex (derivativePartIndex i α) = natIndex α + Pi.single i 1 := rfl

@[simp] lemma derivativePartIndex_zero {d : ℕ} (i : Fin d) :
    derivativePartIndex i (zeroIndex d 1) = normalIndex i := by
  classical
  apply Subtype.ext
  funext j
  apply Fin.ext
  by_cases h : j = i <;> simp [derivativePartIndex, boundedIndex, natIndex, zeroIndex, normalIndex, Pi.single_apply, h]

lemma distributionDerivative_perm {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {w z : List (Fin d)} (h : w.Perm z) (u : ScalarDistribution 𝕜 Ω) :
    distributionDerivative 𝕜 d Ω w u = distributionDerivative 𝕜 d Ω z u := by
  ext φ
  simp only [distributionDerivative_apply, h.length_eq,
    Smoothing.testPartial_perm h φ]

lemma derivativePartIndex_distribution {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (i : Fin d) (α : DerivativeIndex d 1) (u : ScalarDistribution 𝕜 Ω) :
    Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
        𝕜 d Ω (natIndex (derivativePartIndex i α)) u =
      Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
        𝕜 d Ω (natIndex α)
        (Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
          𝕜 d Ω (natIndex (normalIndex i)) u) := by
  classical
  have hp : (multiIndexWord (natIndex (derivativePartIndex i α))).Perm
      (i :: multiIndexWord (natIndex α)) := by
    apply List.perm_iff_count.mpr
    intro j
    simp only [multiIndexWord_count, natIndex_derivativePartIndex, Pi.add_apply,
      List.count_cons]
    simp only [Pi.single_apply, beq_iff_eq]
    congr 1
    exact if_congr eq_comm (by rfl) (by rfl)
  change distributionDerivative 𝕜 d Ω (multiIndexWord (natIndex (derivativePartIndex i α))) u = _
  rw [distributionDerivative_perm hp, distributionDerivative_cons]
  have hn : natIndex (normalIndex i) = Pi.single i 1 := by
    funext j
    simp [natIndex, normalIndex, Pi.single_apply, apply_ite]
  change distributionDerivative 𝕜 d Ω (multiIndexWord (natIndex α)) (-u.comp (testPartialCLM [i])) =
    distributionDerivative 𝕜 d Ω (multiIndexWord (natIndex α))
      (distributionDerivative 𝕜 d Ω (multiIndexWord (natIndex (normalIndex i))) u)
  rw [hn, ExpandedFA.Sobolev.Lines.multiIndexWord_single,
    distributionDerivative_cons, distributionDerivative_nil]

def derivativePart {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (i : Fin d) (u : SpaceValue 𝕜 d Ω 2 p) :
    SpaceValue 𝕜 d Ω 1 p :=
  ⟨WithLp.toLp 1 (fun α => u.val (derivativePartIndex i α)), by
    intro α
    change lpDistributionLM (u.val (derivativePartIndex i α)) = _
    change lpDistributionLM (u.val (derivativePartIndex i α)) =
      Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
        𝕜 d Ω (natIndex α) (lpDistributionLM (u.val (derivativePartIndex i (zeroIndex d 1))))
    rw [u.property (derivativePartIndex i α), derivativePartIndex_distribution,
      derivativePartIndex_zero, u.property (normalIndex i)]⟩

@[simp] lemma derivativePart_apply {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (i : Fin d) (u : SpaceValue 𝕜 d Ω 2 p)
    (α : DerivativeIndex d 1) :
    (derivativePart i u).val α = u.val (derivativePartIndex i α) := rfl

lemma derivativePart_norm_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (i : Fin d) (u : SpaceValue 𝕜 d Ω 2 p) :
    ‖derivativePart i u‖ ≤ Fintype.card (DerivativeIndex d 1) * ‖u‖ := by
  rw [sobolev_norm_formula]
  calc
    (∑ α : DerivativeIndex d 1, ‖(derivativePart i u).val α‖) ≤ ∑ _ : DerivativeIndex d 1, ‖u‖ :=
      Finset.sum_le_sum (fun α _ => PiLp.norm_apply_le u.val (derivativePartIndex i α))
    _ = _ := by simp

def derivativePartCLM (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin d) : SpaceValue 𝕜 d Ω 2 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p :=
  LinearMap.mkContinuous
    { toFun := derivativePart i
      map_add' := fun u v => by apply Subtype.ext; apply PiLp.ext; intro α; rfl
      map_smul' := fun c u => by apply Subtype.ext; apply PiLp.ext; intro α; rfl }
    (Fintype.card (DerivativeIndex d 1)) (derivativePart_norm_le i)

end ExpandedFA.PartIV.SecondTraceFlat
namespace ExpandedFA.PartIV.SecondTraceFlat
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.SharpTraceBound
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

lemma hasBoundaryJets_iff {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i)))
    (u : SpaceValue 𝕜 (n + 1) (upper i) 2 p)
    (g h : Lp 𝕜 p (volume : Measure (Domain n))) :
    HasBoundaryJets i T u g h ↔
      reindexedTrace i T (orderOnePart u) = g ∧
      reindexedTrace i T (derivativePart i u) = h := by
  constructor
  · rintro ⟨v, w, hv, hw, hvg, hwh⟩
    have hv' : v = orderOnePart u := by
      apply sobolev_underlying_injective 𝕜 (n + 1) (upper i) 1 p
      simpa only [orderOnePart_apply, orderOneToTwo_zero] using hv
    have hw' : w = derivativePart i u := by
      apply sobolev_underlying_injective 𝕜 (n + 1) (upper i) 1 p
      simpa only [derivativePart_apply, derivativePartIndex_zero] using hw
    exact ⟨hv' ▸ hvg, hw' ▸ hwh⟩
  · rintro ⟨hg, hh⟩
    exact ⟨orderOnePart u, derivativePart i u,
      by simp only [orderOnePart_apply, orderOneToTwo_zero],
      by simp only [derivativePart_apply, derivativePartIndex_zero], hg, hh⟩

lemma hasBoundaryJets_of_tendsto {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i)))
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : ι → SpaceValue 𝕜 (n + 1) (upper i) 2 p}
    {G H : ι → Lp 𝕜 p (volume : Measure (Domain n))}
    {u : SpaceValue 𝕜 (n + 1) (upper i) 2 p}
    {g h : Lp 𝕜 p (volume : Measure (Domain n))}
    (hu : Filter.Tendsto U l (nhds u)) (hg : Filter.Tendsto G l (nhds g))
    (hh : Filter.Tendsto H l (nhds h))
    (hjets : ∀ᶠ k in l, HasBoundaryJets i T (U k) (G k) (H k)) :
    HasBoundaryJets i T u g h := by
  rw [hasBoundaryJets_iff]
  have hv := ((reindexedTrace i T).continuous.comp
    (orderOnePartCLM 𝕜 (n+1) (upper i) p).continuous).continuousAt.tendsto.comp hu
  have hw := ((reindexedTrace i T).continuous.comp
    (derivativePartCLM 𝕜 (n+1) (upper i) p i).continuous).continuousAt.tendsto.comp hu
  have hvg : (fun k => reindexedTrace i T (orderOnePart (U k))) =ᶠ[l] G :=
    hjets.mono (fun k hk => (hasBoundaryJets_iff i T _ _ _).mp hk |>.1)
  have hwh : (fun k => reindexedTrace i T (derivativePart i (U k))) =ᶠ[l] H :=
    hjets.mono (fun k hk => (hasBoundaryJets_iff i T _ _ _).mp hk |>.2)
  exact ⟨tendsto_nhds_unique hv (hg.congr' hvg.symm),
    tendsto_nhds_unique hw (hh.congr' hwh.symm)⟩

end ExpandedFA.PartIV.SecondTraceFlat



noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
namespace ExpandedFA.PartIV.HigherDensity
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.FractionalSobolev
open ExpandedFA.PartIV.SharpTraceExtension
open ExpandedFA.Distributions.SmoothApproximateIdentitiesSpec

lemma regularize_derivative_whole {𝕜 : Type} [RCLike 𝕜] {d m : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (ρ : Domain d → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (u : SobolevSpace 𝕜 d ⊤ m p) (α : DerivativeIndex d m) :
    Smoothing.classicalDerivative α (Smoothing.regularize ρ ε (u.val (zeroIndex d m))) =
      Smoothing.regularize ρ ε (u.val α) := by
  rw [Smoothing.regularize_eq_kernelTest ρ hρ hε,
    Smoothing.regularize_eq_kernelTest ρ hρ hε]
  funext x
  exact Smoothing.interior_convolution_identity u α _ x (subset_univ _)

lemma smooth_first_order_graph {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p)
    (f : Domain d → 𝕜) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hu : u =ᵐ[volume.restrict (Ω : Set (Domain d))] f)
    (hg : ∀ i, g i =ᵐ[volume.restrict (Ω : Set (Domain d))]
      fun x => fderiv ℝ f x (coordinateVector i)) :
    ∃ v : SobolevSpace 𝕜 d Ω 1 p,
      v.val (zeroIndex d 1) = u ∧ ∀ i, v.val (firstIndex i) = g i := by
  have hacl : HasACLDerivatives Ω f g := by
    intro i
    filter_upwards [ae_on_fibers i (hg i)] with y hy
    refine ⟨?_, ?_⟩
    · intro a b _
      exact ((hf.comp (coordinateLine_contDiff i y)).of_le (by simp) :
        ContDiff ℝ 1 (fun t => f (coordinateLine i y t))).contDiffOn.absolutelyContinuousOnInterval
    · filter_upwards [hy] with t ht
      rw [ht]
      exact ((hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
        (coordinateLine_hasDerivAt i y t))
  have hw := acl_to_weak u g f hu hacl
  obtain ⟨v, hv⟩ := (first_order_membership_iff u).mpr ⟨g, hw⟩
  refine ⟨v, hv, fun i => ?_⟩
  apply lpDistribution_injective
  have hvd := v.property (firstIndex i)
  change lpDistribution (v.val (firstIndex i)) = distributionDerivative 𝕜 d Ω
    (multiIndexWord (natIndex (firstIndex i))) (lpDistribution (v.val (zeroIndex d 1))) at hvd
  rw [hv] at hvd
  simp only [natIndex_firstIndex, multiIndexWord_single, distributionDerivative_cons,
    distributionDerivative_nil] at hvd
  exact hvd.trans (hw i).symm

lemma regularize_graph_exists {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (ρ : Domain d → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (u : SobolevSpace 𝕜 d ⊤ 1 p) :
    ∃ v : SobolevSpace 𝕜 d ⊤ 1 p,
      (∀ α : DerivativeIndex d 1, v.val α =ᵐ[volume]
        Smoothing.regularize ρ ε (u.val α)) ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (Smoothing.regularize ρ ε (u.val (zeroIndex d 1))) := by
  let f := Smoothing.regularize ρ ε (u.val (zeroIndex d 1))
  have hf := Smoothing.regularize_contDiff ρ hρ hε (u.val (zeroIndex d 1))
  have hflp : MemLp f p (volume.restrict ((⊤ : Opens (Domain d)) : Set (Domain d))) := by
    simpa using Smoothing.regularize_memLp ρ hρ hε (u.val (zeroIndex d 1))
  let u0 : DomainLp 𝕜 (⊤ : Opens (Domain d)) p := hflp.toLp f
  have hjlp (i : Fin d) : MemLp (Smoothing.regularize ρ ε (u.val (firstIndex i))) p
      (volume.restrict ((⊤ : Opens (Domain d)) : Set (Domain d))) := by
    simpa using Smoothing.regularize_memLp ρ hρ hε (u.val (firstIndex i))
  let g : Fin d → DomainLp 𝕜 (⊤ : Opens (Domain d)) p :=
    fun i => (hjlp i).toLp (Smoothing.regularize ρ ε (u.val (firstIndex i)))
  have hder (i : Fin d) : Smoothing.regularize ρ ε (u.val (firstIndex i)) =
      fun x => fderiv ℝ f x (coordinateVector i) := by
    rw [← regularize_derivative_whole ρ hρ hε u (firstIndex i)]
    simp [Smoothing.classicalDerivative, natIndex_firstIndex, multiIndexWord_single, partialFunction, f]
  obtain ⟨v, hv0, hvi⟩ := smooth_first_order_graph u0 g f hf hflp.coeFn_toLp
    (fun i => by rw [← hder i]; exact (hjlp i).coeFn_toLp)
  refine ⟨v, fun α => ?_, hf⟩
  rcases multiIndex_order_one_cases (natIndex α) α.property with hz | ⟨i, hi⟩
  · have ha : α = zeroIndex d 1 := by
      apply Subtype.ext; funext i; apply Fin.ext; exact congrFun hz i
    subst α
    rw [hv0]
    simpa only [Opens.coe_top, Measure.restrict_univ] using hflp.coeFn_toLp
  · have ha : α = firstIndex i := by
      apply Subtype.ext; funext j; apply Fin.ext
      exact congrFun (hi.trans (natIndex_firstIndex i).symm) j
    subst α
    rw [hvi]
    simpa only [Opens.coe_top, Measure.restrict_univ] using (hjlp i).coeFn_toLp

lemma regularize_whole_eq {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (ρ : Domain d → ℝ) (ε : ℝ)
    (u : DomainLp 𝕜 (⊤ : Opens (Domain d)) p) :
    Smoothing.regularize ρ ε u = MollifyValue ρ ε (u : Domain d → 𝕜) := by
  simp [Smoothing.regularize, Smoothing.zeroExtend]

@[simp] lemma wholeLp_sub {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u v : DomainLp 𝕜 (⊤ : Opens (Domain d)) p) :
    wholeLp (u-v) = wholeLp u - wholeLp v := wholeLpLI.map_sub u v

/-- Common-scale mollification respects the actual gradient compatibility in
    the higher fractional space and converges in its full norm. -/
theorem smooth_higher_density_with_gradient {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (u : HigherFractionalSpace 𝕜 d s p) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (v : HigherFractionalSpace 𝕜 d s p) (f : Domain d → 𝕜),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧
      wholeLp (v.val.val (zeroIndex d 1)) =ᵐ[volume] f ∧
      (∀ i, wholeLp (v.val.val (firstIndex i)) =ᵐ[volume]
        fun x => fderiv ℝ f x (coordinateVector i)) ∧
      ‖v-u‖ < δ := by
  have hp : p ≠ ∞ := Fact.out
  letI : MeasurableSpace 𝕜 := borel 𝕜
  obtain ⟨ρ, hρ⟩ := Smoothing.exists_mollifier d
  let lpErr (ε : ℝ) (α : DerivativeIndex d 1) :=
    (eLpNorm (Smoothing.regularize ρ ε (u.val.val α) - (u.val.val α : Domain d → 𝕜))
      p volume).toReal
  let rawErr (ε : ℝ) (i : Fin d) := rawSeminorm (s-1) p
    (Smoothing.regularize ρ ε (u.val.val (firstIndex i)) -
      (u.val.val (firstIndex i) : Domain d → 𝕜))
  have htlp (α : DerivativeIndex d 1) : Tendsto (fun ε => lpErr ε α)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht := Smoothing.regularize_zeroExtend_tendsto hp ρ hρ (u.val.val α)
    simp only [Smoothing.zeroExtend, Opens.coe_top, Set.indicator_univ] at ht
    simpa only [lpErr, ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  have htraw (i : Fin d) : Tendsto (fun ε => rawErr ε i)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [rawErr, regularize_whole_eq] using
      mollify_rawSeminorm_tendsto (s-1) p hp ρ hρ
        (⟨wholeLp (u.val.val (firstIndex i)), u.property i⟩ : FractionalSpace 𝕜 d (s-1) p)
        (u.val.val (firstIndex i)) (Lp.stronglyMeasurable _).measurable
        (wholeLp_representative _)
  have ht := (htlp (zeroIndex d 1)).add
    (tendsto_finsetSum Finset.univ (fun i _ => (htlp (firstIndex i)).add
      ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (htraw i))))
  simp only [ENNReal.toReal_zero, zero_add, Finset.sum_const_zero, add_zero] at ht
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i : Fin d, rawErr ε i < 1 :=
    Filter.eventually_all.mpr (fun i => (htraw i).eventually (Iio_mem_nhds (by simp)))
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, herr, hsmall⟩ :=
    (hpos.and ((ht.eventually (Iio_mem_nhds hδ)).and hsmall)).exists
  obtain ⟨v₁, hv₁, hvc⟩ := regularize_graph_exists ρ hρ hε u.val
  let w (α : DerivativeIndex d 1) := wholeLp (v₁.val α) - wholeLp (u.val.val α)
  have hwr (α : DerivativeIndex d 1) : w α =ᵐ[volume]
      Smoothing.regularize ρ ε (u.val.val α) - (u.val.val α : Domain d → 𝕜) := by
    filter_upwards [Lp.coeFn_sub (wholeLp (v₁.val α)) (wholeLp (u.val.val α)),
      wholeLp_representative (v₁.val α), hv₁ α, wholeLp_representative (u.val.val α)]
      with x hx hv hv' hu
    change (wholeLp (v₁.val α) - wholeLp (u.val.val α)) x = _
    rw [hx]
    simp only [Pi.sub_apply, hv, hv', hu]
  have hwnorm (α : DerivativeIndex d 1) : ‖w α‖ = lpErr ε α := by
    rw [← toReal_enorm, Lp.enorm_def, eLpNorm_congr_ae (hwr α)]
  have hwraw (i : Fin d) : rawErr ε i =
      differenceEnergy (s-1) p (w (firstIndex i)) ^ (1 / p.toReal) := by
    exact rawSeminorm_eq (s-1) p hp _ _
      ((Smoothing.regularize_contDiff ρ hρ hε _).continuous.measurable.sub
        (Lp.stronglyMeasurable _).measurable) (hwr _)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp
  have hwfin (i : Fin d) : differenceEnergy (s-1) p (w (firstIndex i)) < ∞ := by
    apply (ENNReal.rpow_lt_top_iff_of_pos (one_div_pos.mpr hpr)).mp
    rw [← hwraw]
    exact (hsmall i).trans (by simp)
  have hvfin (i : Fin d) : differenceEnergy (s-1) p (wholeLp (v₁.val (firstIndex i))) < ∞ := by
    have hh := finite_energy_add (s-1) p hp _ _ (hwfin i) (u.property i)
    simpa only [w, sub_add_cancel] using hh
  let v : HigherFractionalSpace 𝕜 d s p := ⟨v₁, hvfin⟩
  refine ⟨v, Smoothing.regularize ρ ε (u.val.val (zeroIndex d 1)), hvc,
    (wholeLp_representative _).trans (hv₁ _), ?_, ?_⟩
  · intro i
    have hder : Smoothing.regularize ρ ε (u.val.val (firstIndex i)) =
        fun x => fderiv ℝ (Smoothing.regularize ρ ε (u.val.val (zeroIndex d 1))) x
          (coordinateVector i) := by
      rw [← regularize_derivative_whole ρ hρ hε u.val (firstIndex i)]
      simp [Smoothing.classicalDerivative, natIndex_firstIndex, multiIndexWord_single, partialFunction]
    rw [← hder]
    exact (wholeLp_representative _).trans (hv₁ _)
  change higherFractionalNorm s p (v-u) < δ
  have hsub (α : DerivativeIndex d 1) : (v-u).val.val α = v₁.val α - u.val.val α := rfl
  simp only [higherFractionalNorm, fractionalNorm, hsub, wholeLp_sub]
  change ‖w (zeroIndex d 1)‖ + ∑ i : Fin d,
    (‖w (firstIndex i)‖ + (differenceEnergy (s-1) p (w (firstIndex i))).toReal ^
      (1 / p.toReal)) < δ
  simpa only [hwnorm, ENNReal.toReal_rpow, ← hwraw, Function.comp_def] using herr

theorem smooth_higher_density {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (u : HigherFractionalSpace 𝕜 d s p) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (v : HigherFractionalSpace 𝕜 d s p) (f : Domain d → 𝕜),
      ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧
      wholeLp (v.val.val (zeroIndex d 1)) =ᵐ[volume] f ∧ ‖v-u‖ < δ := by
  obtain ⟨v, f, hf, hv, _, herr⟩ := smooth_higher_density_with_gradient s p u δ hδ
  exact ⟨v, f, hf, hv, herr⟩

section DenseSubmodules
variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (s σ : ℝ) (p : ℝ≥0∞)
  [Fact (1 ≤ p)] [Fact (p ≠ ∞)]

/-- The smooth higher data retain the actual gradient representatives. -/
def smoothHigherSubmodule : Submodule 𝕜 (HigherFractionalSpace 𝕜 n σ p) where
  carrier := {u | ∃ f : Domain n → 𝕜, ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧
    wholeLp (u.val.val (zeroIndex n 1)) =ᵐ[volume] f ∧
    ∀ i, wholeLp (u.val.val (firstIndex i)) =ᵐ[volume]
      fun x => fderiv ℝ f x (coordinateVector i)}
  zero_mem' := by
    refine ⟨0, contDiff_const, ?_, fun i => ?_⟩
    · have hz : (0 : HigherFractionalSpace 𝕜 n σ p).val.val (zeroIndex n 1) = 0 := rfl
      rw [hz, wholeLp_zero]
      exact Lp.coeFn_zero 𝕜 p volume
    · have hz : (0 : HigherFractionalSpace 𝕜 n σ p).val.val (firstIndex i) = 0 := rfl
      rw [hz, wholeLp_zero]
      filter_upwards [Lp.coeFn_zero 𝕜 p volume] with x hx
      simpa using hx
  add_mem' := by
    rintro u v ⟨f, hf, huf, hufd⟩ ⟨g, hg, hvg, hvgd⟩
    have hval (α : DerivativeIndex n 1) : (u+v).val.val α =
        u.val.val α + v.val.val α := rfl
    refine ⟨f+g, hf.add hg, ?_, fun i => ?_⟩
    · rw [hval, wholeLp_add]
      filter_upwards [Lp.coeFn_add (wholeLp (u.val.val (zeroIndex n 1)))
        (wholeLp (v.val.val (zeroIndex n 1))), huf, hvg] with x hx hu hv
      simpa only [Pi.add_apply, hu, hv] using hx
    · rw [hval, wholeLp_add]
      filter_upwards [Lp.coeFn_add (wholeLp (u.val.val (firstIndex i)))
        (wholeLp (v.val.val (firstIndex i))), hufd i, hvgd i] with x hx hu hv
      rw [hx]
      simp only [Pi.add_apply, hu, hv, fderiv_add (hf.differentiable (by simp) x)
        (hg.differentiable (by simp) x), ContinuousLinearMap.add_apply]
  smul_mem' := by
    rintro c u ⟨f, hf, huf, hufd⟩
    have hval (α : DerivativeIndex n 1) : (c • u).val.val α = c • u.val.val α := rfl
    refine ⟨c • f, hf.const_smul c, ?_, fun i => ?_⟩
    · rw [hval, wholeLp_smul]
      filter_upwards [Lp.coeFn_smul c (wholeLp (u.val.val (zeroIndex n 1))), huf]
        with x hx hu
      simpa only [Pi.smul_apply, hu] using hx
    · rw [hval, wholeLp_smul]
      filter_upwards [Lp.coeFn_smul c (wholeLp (u.val.val (firstIndex i))), hufd i]
        with x hx hu
      rw [hx]
      simp only [Pi.smul_apply, hu, fderiv_const_smul (hf.differentiable (by simp) x),
        ContinuousLinearMap.smul_apply]

lemma smoothHigher_denseRange :
    DenseRange (smoothHigherSubmodule (𝕜 := 𝕜) (n := n) σ p).subtype := by
  intro u
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨v, f, hf, hv, hvg, herr⟩ := smooth_higher_density_with_gradient σ p u ε hε
  refine ⟨v, ⟨⟨v, f, hf, hv, hvg⟩, rfl⟩, ?_⟩
  rw [dist_comm, dist_eq_norm]
  exact herr

/-- Smooth noncompact finite-energy functions form a submodule. -/
def smoothFractionalSubmodule : Submodule 𝕜 (FractionalSpace 𝕜 n s p) where
  carrier := {u | ∃ f : Domain n → 𝕜, ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ u.val =ᵐ[volume] f}
  zero_mem' := ⟨0, contDiff_const, Lp.coeFn_zero 𝕜 p volume⟩
  add_mem' := by
    rintro u v ⟨f, hf, hu⟩ ⟨g, hg, hv⟩
    refine ⟨f+g, hf.add hg, ?_⟩
    filter_upwards [Lp.coeFn_add u.val v.val, hu, hv] with x hx hux hvx
    change (u.val+v.val) x = (f+g) x
    simpa only [Pi.add_apply, hux, hvx] using hx
  smul_mem' := by
    rintro c u ⟨f, hf, hu⟩
    refine ⟨c • f, hf.const_smul c, ?_⟩
    filter_upwards [Lp.coeFn_smul c u.val, hu] with x hx hux
    change (c • u.val) x = (c • f) x
    simpa only [Pi.smul_apply, hux] using hx

lemma smoothFractional_denseRange (hs0 : 0 < s) (hs1 : s < 1) :
    DenseRange (smoothFractionalSubmodule (𝕜 := 𝕜) (n := n) s p).subtype := by
  intro u
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨v, f, hf, _, hv, herr⟩ := smooth_density 𝕜 n s hs0 hs1 p Fact.out u ε hε
  refine ⟨v, ⟨⟨v, f, hf, hv⟩, rfl⟩, ?_⟩
  rw [dist_comm, dist_eq_norm, ← fractionalError_eq_norm]
  exact herr

/-- The common smooth domain for the two simultaneous boundary data. -/
def smoothJetDataSubmodule : Submodule 𝕜
    (HigherFractionalSpace 𝕜 n σ p × FractionalSpace 𝕜 n s p) :=
  (smoothHigherSubmodule σ p).prod (smoothFractionalSubmodule s p)

lemma smoothJetData_denseRange (hs0 : 0 < s) (hs1 : s < 1) :
    DenseRange (smoothJetDataSubmodule (𝕜 := 𝕜) (n := n) s σ p).subtype := by
  intro u
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨v, f, hf, hv, hvg, herrv⟩ := smooth_higher_density_with_gradient σ p u.1 ε hε
  obtain ⟨w, h, hh, _, hw, herrw⟩ := smooth_density 𝕜 n s hs0 hs1 p Fact.out u.2 ε hε
  refine ⟨(v,w), ⟨⟨(v,w), ⟨⟨f, hf, hv, hvg⟩, ⟨h, hh, hw⟩⟩⟩, rfl⟩, ?_⟩
  rw [dist_comm, dist_eq_norm, Prod.norm_def]
  exact max_lt herrv herrw

lemma jetData_norm_sum_le (u : HigherFractionalSpace 𝕜 n σ p × FractionalSpace 𝕜 n s p) :
    higherFractionalNorm σ p u.1 + fractionalNorm s p u.2 ≤ 2 * ‖u‖ := by
  change ‖u.1‖ + ‖u.2‖ ≤ _
  rw [Prod.norm_def]
  linarith [le_max_left ‖u.1‖ ‖u.2‖, le_max_right ‖u.1‖ ‖u.2‖]
end DenseSubmodules

end ExpandedFA.PartIV.HigherDensity



noncomputable section
open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal Topology BigOperators
namespace ExpandedFA.PartIV.SecondTraceFlat
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open ExpandedFA.PartIV.SharpTraceExtension
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open SmoothLift

lemma flat_memLp_of_power_finite {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (F : Domain n × ℝ → 𝕜) (hF : Continuous F)
    (hfin : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
      ‖F (x,t)‖ₑ ^ p.toReal) < ∞) :
    MemLp (fun x => F (flatCoordinates i x)) p
      (volume.restrict (upper i : Set (Domain (n + 1)))) := by
  have hmeas : AEStronglyMeasurable (fun x => F (flatCoordinates i x))
      (volume.restrict (upper i : Set (Domain (n + 1)))) :=
    (hF.comp (flatCoordinates_contDiff i).continuous).aestronglyMeasurable
  change eLpNorm (fun x => F (flatCoordinates i x)) p
    (volume.restrict (upper i : Set (Domain (n + 1)))) < ∞
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp hmeas]
  rw [upper_lintegral_flatCoordinates i
    (fun z => ‖F z‖ₑ ^ p.toReal) (hF.enorm.measurable.pow_const _)]
  exact hfin

lemma jetFunction_memLp_of_flat_power_finite {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f h : Domain n → 𝕜)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h)
    (hzero : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
      ‖flatJet jetCutoff (jetMollifier n) f h (x,t)‖ₑ ^ p.toReal) < ∞)
    (hfirst : ∀ a : Option (Fin n),
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖fderiv ℝ (flatJet jetCutoff (jetMollifier n) f h) (x,t)
          (flatDirection a)‖ₑ ^ p.toReal) < ∞)
    (hsecond : ∀ a b : Option (Fin n),
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖secondFlatPartial (flatJet jetCutoff (jetMollifier n) f h) a b (x,t)‖ₑ ^ p.toReal) < ∞)
    (α : DerivativeIndex (n + 1) 2) :
    MemLp (Smoothing.classicalDerivative α (jetFunction i f h)) p
      (volume.restrict (upper i : Set (Domain (n + 1)))) := by
  let F := flatJet jetCutoff (jetMollifier n) f h
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F :=
    flatJet_contDiff jetCutoff (jetMollifier n) f h jetCutoff_contDiff
      (jetMollifier_contDiff n) (jetMollifier_compactSupport n) hf hh
  change MemLp (partialFunction (multiIndexWord (natIndex α)).reverse
    (jetFunction i f h)) p _
  rcases derivativeWord_order_two_cases α with hz | ⟨j,hj⟩ | ⟨j,k,hjk⟩
  · rw [hz]
    exact flat_memLp_of_power_finite i p hp F hF.continuous hzero
  · obtain ⟨a,ha⟩ := flatCoordinatesCLM_direction i j
    have he : partialFunction [j] (jetFunction i f h) =
        fun x => fderiv ℝ F (flatCoordinates i x) (flatDirection a) :=
      funext (jetFunction_fderiv_flat i j f h hF a ha)
    rw [hj, he]
    exact flat_memLp_of_power_finite i p hp _
      ((hF.continuous_fderiv (by simp)).clm_apply continuous_const) (hfirst a)
  · obtain ⟨a,ha⟩ := flatCoordinatesCLM_direction i j
    obtain ⟨b,hb⟩ := flatCoordinatesCLM_direction i k
    have he : partialFunction [j,k] (jetFunction i f h) =
        fun x => secondFlatPartial F a b (flatCoordinates i x) :=
      funext (jetFunction_second_fderiv_flat i j k f h hF a b ha hb)
    rw [hjk, he]
    exact flat_memLp_of_power_finite i p hp _
      (secondFlatPartial_continuous F hF a b) (hsecond a b)

lemma jet_norm_le_of_flat_power_bounds {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f h : Domain n → 𝕜)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h)
    (u : SpaceValue 𝕜 (n + 1) (upper i) 2 p)
    (hcoe : ∀ α, u.val α =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))]
      Smoothing.classicalDerivative α (jetFunction i f h))
    (C₀ C₁ C₂ : ℝ≥0∞) (hC₀ : C₀ ≠ ∞) (hC₁ : C₁ ≠ ∞) (hC₂ : C₂ ≠ ∞)
    (N : ℝ) (hN : 0 ≤ N)
    (hzero : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖flatJet jetCutoff (jetMollifier n) f h (x,t)‖ₑ ^ p.toReal) ≤
      C₀ * ENNReal.ofReal N ^ p.toReal)
    (hfirst : ∀ a : Option (Fin n),
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖fderiv ℝ (flatJet jetCutoff (jetMollifier n) f h) (x,t) (flatDirection a)‖ₑ ^ p.toReal) ≤
      C₁ * ENNReal.ofReal N ^ p.toReal)
    (hsecond : ∀ a b : Option (Fin n),
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖secondFlatPartial (flatJet jetCutoff (jetMollifier n) f h) a b (x,t)‖ₑ ^ p.toReal) ≤
      C₂ * ENNReal.ofReal N ^ p.toReal) :
    ‖u‖ ≤
      (Fintype.card (DerivativeIndex (n + 1) 2) : ℝ) *
        (C₀.toReal ^ (1 / p.toReal) + C₁.toReal ^ (1 / p.toReal) +
          C₂.toReal ^ (1 / p.toReal)) * N := by
  let F := flatJet jetCutoff (jetMollifier n) f h
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F :=
    flatJet_contDiff jetCutoff (jetMollifier n) f h jetCutoff_contDiff
      (jetMollifier_contDiff n) (jetMollifier_compactSupport n) hf hh
  apply secondJet_norm_le_of_classical_bounds _ (jetFunction i f h)
    hcoe
    (C₀.toReal ^ (1 / p.toReal)) (C₁.toReal ^ (1 / p.toReal))
    (C₂.toReal ^ (1 / p.toReal)) N
    (by positivity) (by positivity) (by positivity) hN
  · exact flat_eLpNorm_toReal_le_of_power_bound i p hp F hF.continuous C₀ hC₀ N hN hzero
  · intro j
    obtain ⟨a, ha⟩ := flatCoordinatesCLM_direction i j
    have hfun : (fun x => fderiv ℝ (jetFunction i f h) x (coordinateVector j)) =
        fun x => fderiv ℝ F (flatCoordinates i x) (flatDirection a) :=
      funext (jetFunction_fderiv_flat i j f h hF a ha)
    rw [hfun]
    exact flat_eLpNorm_toReal_le_of_power_bound i p hp
      (fun z => fderiv ℝ F z (flatDirection a))
      ((hF.continuous_fderiv (by simp)).clm_apply continuous_const) C₁ hC₁ N hN (hfirst a)
  · intro j k
    obtain ⟨a, ha⟩ := flatCoordinatesCLM_direction i j
    obtain ⟨b, hb⟩ := flatCoordinatesCLM_direction i k
    have hfun : (fun x => fderiv ℝ (fun y => fderiv ℝ (jetFunction i f h) y (coordinateVector k)) x
        (coordinateVector j)) =
        fun x => secondFlatPartial F a b (flatCoordinates i x) :=
      funext (jetFunction_second_fderiv_flat i j k f h hF a b ha hb)
    rw [hfun]
    exact flat_eLpNorm_toReal_le_of_power_bound i p hp
      (secondFlatPartial F a b) (secondFlatPartial_continuous F hF a b) C₂ hC₂ N hN (hsecond a b)

theorem smooth_noncompact_jet_lift (n : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (i : Fin (n + 1))
      (g : HigherFractionalSpace 𝕜 n (2 - 1 / p.toReal) p)
      (k : FractionalSpace 𝕜 n (1 - 1 / p.toReal) p)
      (f h : Domain n → 𝕜)
      (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
      (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h),
      wholeLp (g.val.val (zeroIndex n 1)) =ᵐ[volume] f →
      (∀ j, wholeLp (g.val.val (firstIndex j)) =ᵐ[volume]
        (fun x => fderiv ℝ f x (coordinateVector j))) →
      k.val =ᵐ[volume] h →
      ∃ u : SpaceValue 𝕜 (n + 1) (upper i) 2 p,
        (∀ α, u.val α =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))]
          Smoothing.classicalDerivative α (jetFunction i f h)) ∧
      ‖u‖ ≤ C *
        (higherFractionalNorm (2 - 1 / p.toReal) p g + fractionalNorm (1 - 1 / p.toReal) p k) := by
  classical
  obtain ⟨A, hA, ha⟩ := flatJet_power_bound (n := n) p hp (jetMollifier n)
    (jetMollifier_contDiff n) (jetMollifier_compactSupport n)
  have hb (a : Option (Fin n)) := flatJet_first_power_bound p hp (jetMollifier n)
    (jetMollifier_contDiff n) (jetMollifier_compactSupport n) a
  choose B hB hb using hb
  have hc (ab : Option (Fin n) × Option (Fin n)) := flatJet_second_power_bound p hp1 hp
    (jetMollifier n) (jetMollifier_contDiff n) (jetMollifier_compactSupport n) ab.1 ab.2
  choose D hD hd using hc
  let K : ℝ≥0∞ := 2 * (n : ℝ≥0∞) + 3
  have hK : K ≠ ∞ := jet_dataPower_factor_ne_top n
  let C₀ : ℝ≥0∞ := A * K
  let C₁ : ℝ≥0∞ := (∑ a, B a) * K
  let C₂ : ℝ≥0∞ := (∑ ab, D ab) * K
  have hC₀ : C₀ ≠ ∞ := ENNReal.mul_ne_top hA hK
  have hC₁ : C₁ ≠ ∞ := ENNReal.mul_ne_top
    (ne_of_lt (ENNReal.sum_lt_top.mpr (fun a _ => lt_top_iff_ne_top.mpr (hB a)))) hK
  have hC₂ : C₂ ≠ ∞ := ENNReal.mul_ne_top
    (ne_of_lt (ENNReal.sum_lt_top.mpr (fun ab _ => lt_top_iff_ne_top.mpr (hD ab)))) hK
  refine ⟨(Fintype.card (DerivativeIndex (n + 1) 2) : ℝ) *
    (C₀.toReal ^ (1 / p.toReal) + C₁.toReal ^ (1 / p.toReal) + C₂.toReal ^ (1 / p.toReal)),
    by positivity, ?_⟩
  intro 𝕜 _ i g k f h hf hh hgf hgrad hkh
  let N := higherFractionalNorm (2 - 1 / p.toReal) p g + fractionalNorm (1 - 1 / p.toReal) p k
  have hN : 0 ≤ N := add_nonneg (higherFractionalNorm_nonneg _ p g) (fractionalNorm_nonneg _ p k)
  have hpower : jetDataPower p (wholeLp (g.val.val (zeroIndex n 1)))
      (fun j => wholeLp (g.val.val (firstIndex j))) k.val ≤ K * ENNReal.ofReal N ^ p.toReal :=
    jet_dataPower_le p hp g k
  have hzero : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
      ‖flatJet jetCutoff (jetMollifier n) f h (x,t)‖ₑ ^ p.toReal) ≤
      C₀ * ENNReal.ofReal N ^ p.toReal := by
    exact (ha 𝕜 (wholeLp (g.val.val (zeroIndex n 1)))
        (fun j => wholeLp (g.val.val (firstIndex j))) k.val f h hf hh hgf hkh).trans
      (by simpa only [C₀, mul_assoc] using mul_le_mul' (le_refl A) hpower)
  have hfirst : ∀ a : Option (Fin n),
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖fderiv ℝ (flatJet jetCutoff (jetMollifier n) f h) (x,t) (flatDirection a)‖ₑ ^ p.toReal) ≤
        C₁ * ENNReal.ofReal N ^ p.toReal := by
    intro a
    have hba : B a ≤ ∑ b, B b :=
      Finset.single_le_sum (fun b _ => bot_le) (Finset.mem_univ a)
    exact (hb a 𝕜 (wholeLp (g.val.val (zeroIndex n 1)))
        (fun j => wholeLp (g.val.val (firstIndex j))) k.val f h hf hh hgf hgrad hkh).trans
      (by simpa only [C₁, mul_assoc] using mul_le_mul' hba hpower)
  have hsecond : ∀ a b : Option (Fin n),
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖secondFlatPartial (flatJet jetCutoff (jetMollifier n) f h) a b (x,t)‖ₑ ^ p.toReal) ≤
        C₂ * ENNReal.ofReal N ^ p.toReal := by
    intro a b
    have hdb : D (a,b) ≤ ∑ ab, D ab :=
      Finset.single_le_sum (fun ab _ => bot_le) (Finset.mem_univ (a,b))
    exact (hd (a,b) 𝕜 (wholeLp (g.val.val (zeroIndex n 1)))
        (fun j => wholeLp (g.val.val (firstIndex j))) k.val f h hf hh hgf hgrad hkh).trans
      (by simpa only [C₂, mul_assoc] using mul_le_mul' hdb hpower)
  have hP : ENNReal.ofReal N ^ p.toReal ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  have hmem := jetFunction_memLp_of_flat_power_finite i p hp f h hf hh
    (lt_of_le_of_lt hzero (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hC₀ hP)))
    (fun a => lt_of_le_of_lt (hfirst a)
      (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hC₁ hP)))
    (fun a b => lt_of_le_of_lt (hsecond a b)
      (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hC₂ hP)))
  let u := smoothLpSobolev (upper i) 2 p (jetFunction i f h)
    (jetFunction_contDiff i f h hf hh) hmem
  have hcoe := smoothLpSobolev_coe (upper i) 2 p (jetFunction i f h)
    (jetFunction_contDiff i f h hf hh) hmem
  refine ⟨u, hcoe, ?_⟩
  exact jet_norm_le_of_flat_power_bounds i p hp f h hf hh u hcoe
    C₀ C₁ C₂ hC₀ hC₁ hC₂ N hN hzero hfirst hsecond

lemma smooth_boundary_jets_of_classical {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f h : Domain n → 𝕜)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h)
    (u : SpaceValue 𝕜 (n + 1) (upper i) 2 p)
    (hcoe : ∀ α, u.val α =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))]
      Smoothing.classicalDerivative α (jetFunction i f h))
    (g k : Lp 𝕜 p (volume : Measure (Domain n)))
    (hg : g =ᵐ[volume] f) (hk : k =ᵐ[volume] h)
    (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) (hT : CoordinateTraceCondition i T) :
    HasBoundaryJets i T u g k := by
  let F := jetFunction i f h
  have hF := jetFunction_contDiff i f h hf hh
  let D : Domain (n + 1) → 𝕜 := fun x => fderiv ℝ F x (coordinateVector i)
  have hD : ContDiff ℝ (↑(⊤ : ℕ∞)) D :=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  have hv : (orderOnePart u).val (zeroIndex (n + 1) 1) =ᵐ[
      volume.restrict (upper i : Set (Domain (n + 1)))] F := by
    simpa only [orderOnePart_apply, orderOneToTwo_zero, classicalDerivative_zero]
      using hcoe (zeroIndex (n + 1) 2)
  have hw : (derivativePart i u).val (zeroIndex (n + 1) 1) =ᵐ[
      volume.restrict (upper i : Set (Domain (n + 1)))] D := by
    simpa only [derivativePart_apply, derivativePartIndex_zero, classicalDerivative_normal]
      using hcoe (normalIndex i)
  apply (hasBoundaryJets_iff i T u g k).mpr
  constructor
  · apply Lp.ext
    have ht := reindexedTrace_smooth i T hT (orderOnePart u) F (hF.of_le (by simp)) hv
    filter_upwards [ht, hg] with x hx hgx
    exact (hx.trans (jetFunction_boundary i f h x)).trans hgx.symm
  · apply Lp.ext
    have ht := reindexedTrace_smooth i T hT (derivativePart i u) D (hD.of_le (by simp)) hw
    filter_upwards [ht, hk] with x hx hkx
    exact (hx.trans (jetFunction_normal_boundary_noncompact i f h hf hh x)).trans hkx.symm

end ExpandedFA.PartIV.SecondTraceFlat


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace ExpandedFA.PartIV.SecondTraceFlat
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceExtension
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Each component projection from the actual derivative graph is contractive. -/
def sobolevComponentCLM (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (α : DerivativeIndex d m) :
    SpaceValue 𝕜 d Ω m p →L[𝕜] DomainLp 𝕜 Ω p :=
  (show SpaceValue 𝕜 d Ω m p →ₗ[𝕜] DomainLp 𝕜 Ω p from
    { toFun := fun u => u.val α
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).mkContinuous 1 (fun u => by
        change ‖u.val α‖ ≤ 1 * ‖u.val‖
        simpa only [one_mul] using PiLp.norm_apply_le u.val α)

@[simp] lemma sobolevComponentCLM_apply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (α : DerivativeIndex d m) (u : SpaceValue 𝕜 d Ω m p) :
    sobolevComponentCLM 𝕜 d Ω m p α u = u.val α := rfl

lemma sobolevComponentCLM_norm_le_one {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (α : DerivativeIndex d m) : ‖sobolevComponentCLM 𝕜 d Ω m p α‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖u.val α‖ ≤ 1 * ‖u.val‖
  simpa only [one_mul] using PiLp.norm_apply_le u.val α

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (σ s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (p ≠ ∞)]

/-- The zeroth component of higher fractional data, in whole-space Lp. -/
def higherValueCLM : HigherFractionalSpace 𝕜 n σ p →L[𝕜]
    Lp 𝕜 p (volume : Measure (Domain n)) :=
  (show HigherFractionalSpace 𝕜 n σ p →ₗ[𝕜] Lp 𝕜 p volume from
    { toFun := fun g => wholeLp (g.val.val (zeroIndex n 1))
      map_add' := fun g h => by
        change wholeLp (g.val.val (zeroIndex n 1) + h.val.val (zeroIndex n 1)) = _
        exact wholeLp_add _ _
      map_smul' := fun c g => by
        change wholeLp (c • g.val.val (zeroIndex n 1)) = _
        exact wholeLp_smul _ _ }).mkContinuous 1 (fun g => by
      change ‖wholeLp (g.val.val (zeroIndex n 1))‖ ≤ 1 * higherFractionalNorm σ p g
      rw [one_mul]
      exact le_add_of_nonneg_right
        (Finset.sum_nonneg (fun j _ => fractionalNorm_nonneg _ _ _)))

@[simp] lemma higherValueCLM_apply (g : HigherFractionalSpace 𝕜 n σ p) :
    higherValueCLM σ p g = wholeLp (g.val.val (zeroIndex n 1)) := rfl

lemma higherValueCLM_norm_apply_le (g : HigherFractionalSpace 𝕜 n σ p) :
    ‖higherValueCLM σ p g‖ ≤ ‖g‖ := by
  change ‖wholeLp (g.val.val (zeroIndex n 1))‖ ≤ higherFractionalNorm σ p g
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg (fun j _ => fractionalNorm_nonneg _ _ _))

lemma higherValueCLM_norm_le_one : ‖higherValueCLM (𝕜 := 𝕜) (n := n) σ p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  simpa only [one_mul] using higherValueCLM_norm_apply_le σ p g

/-- Forget both fractional energies while retaining the actual Lp data. -/
def jetDataInclusionCLM :
    (HigherFractionalSpace 𝕜 n σ p × FractionalSpace 𝕜 n s p) →L[𝕜]
      (Lp 𝕜 p (volume : Measure (Domain n)) × Lp 𝕜 p (volume : Measure (Domain n))) :=
  (higherValueCLM σ p).prodMap (fractionalInclusion s p)

@[simp] lemma jetDataInclusionCLM_apply
    (g : HigherFractionalSpace 𝕜 n σ p) (h : FractionalSpace 𝕜 n s p) :
    jetDataInclusionCLM σ s p (g, h) = (wholeLp (g.val.val (zeroIndex n 1)), h.val) := rfl

lemma jetDataInclusionCLM_norm_apply_le
    (z : HigherFractionalSpace 𝕜 n σ p × FractionalSpace 𝕜 n s p) :
    ‖jetDataInclusionCLM σ s p z‖ ≤ ‖z‖ := by
  change max ‖higherValueCLM σ p z.1‖ ‖z.2.val‖ ≤ max ‖z.1‖ ‖z.2‖
  exact max_le_max (higherValueCLM_norm_apply_le σ p z.1) (norm_le_fractionalNorm s p z.2)

lemma jetDataInclusionCLM_norm_le_one :
    ‖jetDataInclusionCLM (𝕜 := 𝕜) (n := n) σ s p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [one_mul] using jetDataInclusionCLM_norm_apply_le σ s p z

end ExpandedFA.PartIV.SecondTraceFlat



noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
namespace ExpandedFA.PartIV.SecondTraceFlat
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open ExpandedFA.PartIV.SharpTraceExtension
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

theorem bounded_jet_extension_clm (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (i : Fin (n + 1)),
      letI : Fact (p ≠ ∞) := ⟨hp⟩
      ∃ E : (HigherFractionalSpace 𝕜 n (2 - 1 / p.toReal) p ×
          FractionalSpace 𝕜 n (1 - 1 / p.toReal) p) →L[𝕜]
          SpaceValue 𝕜 (n + 1) (upper i) 2 p,
        (∀ g k, ‖E (g,k)‖ ≤ C *
          (higherFractionalNorm (2 - 1 / p.toReal) p g + fractionalNorm (1 - 1 / p.toReal) p k)) ∧
        (∀ g k (f h : Domain n → 𝕜)
          (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h),
          wholeLp (g.val.val (zeroIndex n 1)) =ᵐ[volume] f →
          (∀ j, wholeLp (g.val.val (firstIndex j)) =ᵐ[volume]
            fun x => fderiv ℝ f x (coordinateVector j)) →
          k.val =ᵐ[volume] h →
          ∀ α, (E (g,k)).val α =ᵐ[volume.restrict (upper i : Set (Domain (n+1)))]
            Smoothing.classicalDerivative α (jetFunction i f h)) ∧
        (∀ (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
            Lp 𝕜 p (volume : Measure (Transverse i))), CoordinateTraceCondition i T →
          ∀ g k, HasBoundaryJets i T (E (g,k))
            (wholeLp (g.val.val (zeroIndex n 1))) k.val) := by
  classical
  obtain ⟨C, hC, hLift⟩ := smooth_noncompact_jet_lift n p hp1 hp
  refine ⟨2*C, mul_nonneg (by norm_num) hC, ?_⟩
  intro 𝕜 _ i
  letI : Fact (p ≠ ∞) := ⟨hp⟩
  let σ := 2 - 1 / p.toReal
  let s := 1 - 1 / p.toReal
  let X := HigherFractionalSpace 𝕜 n σ p × FractionalSpace 𝕜 n s p
  let S := HigherDensity.smoothJetDataSubmodule (𝕜 := 𝕜) (n := n) s σ p
  have hS : DenseRange S.subtype :=
    HigherDensity.smoothJetData_denseRange s σ p (endpoint_exponent hp1 hp).1 (endpoint_exponent hp1 hp).2
  have hex (u : S) : ∃ U : SpaceValue 𝕜 (n+1) (upper i) 2 p,
      (∀ (f h : Domain n → 𝕜)
        (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h),
        wholeLp (u.val.1.val.val (zeroIndex n 1)) =ᵐ[volume] f →
        u.val.2.val =ᵐ[volume] h →
        ∀ α, U.val α =ᵐ[volume.restrict (upper i : Set (Domain (n+1)))]
          Smoothing.classicalDerivative α (jetFunction i f h)) ∧
      ‖U‖ ≤ C * (higherFractionalNorm σ p u.val.1 + fractionalNorm s p u.val.2) := by
    obtain ⟨f, hf, hgf, hgrad⟩ := u.property.1
    obtain ⟨h, hh, hkh⟩ := u.property.2
    obtain ⟨U, hU, hBound⟩ := hLift 𝕜 i u.val.1 u.val.2 f h hf hh hgf hgrad hkh
    refine ⟨U, ?_, hBound⟩
    intro f' h' hf' hh' hgf' hkh' α
    have heqf : f = f' := Measure.eq_of_ae_eq (hgf.symm.trans hgf') hf.continuous hf'.continuous
    have heqh : h = h' := Measure.eq_of_ae_eq (hkh.symm.trans hkh') hh.continuous hh'.continuous
    simpa only [← heqf, ← heqh] using hU α
  choose E₀ hRep hBound using hex
  have hAdd (u v : S) : E₀ (u+v) = E₀ u + E₀ v := by
    obtain ⟨f₁, hf₁, hgf₁, _⟩ := u.property.1
    obtain ⟨h₁, hh₁, hkh₁⟩ := u.property.2
    obtain ⟨f₂, hf₂, hgf₂, _⟩ := v.property.1
    obtain ⟨h₂, hh₂, hkh₂⟩ := v.property.2
    have hgf : wholeLp ((u+v).val.1.val.val (zeroIndex n 1)) =ᵐ[volume] f₁+f₂ := by
      change wholeLp (u.val.1.val.val (zeroIndex n 1) + v.val.1.val.val (zeroIndex n 1)) =ᵐ[volume] _
      rw [wholeLp_add]
      filter_upwards [Lp.coeFn_add (wholeLp (u.val.1.val.val (zeroIndex n 1)))
        (wholeLp (v.val.1.val.val (zeroIndex n 1))), hgf₁, hgf₂] with x hx h₁x h₂x
      simpa only [Pi.add_apply, h₁x, h₂x] using hx
    have hkh : (u+v).val.2.val =ᵐ[volume] h₁+h₂ := by
      change u.val.2.val + v.val.2.val =ᵐ[volume] _
      filter_upwards [Lp.coeFn_add u.val.2.val v.val.2.val, hkh₁, hkh₂] with x hx h₁x h₂x
      simpa only [Pi.add_apply, h₁x, h₂x] using hx
    apply sobolev_underlying_injective 𝕜 (n+1) (upper i) 2 p
    apply Lp.ext
    have h₃ := hRep (u+v) (f₁+f₂) (h₁+h₂) (hf₁.add hf₂) (hh₁.add hh₂) hgf hkh (zeroIndex (n+1) 2)
    have h₁ := hRep u f₁ h₁ hf₁ hh₁ hgf₁ hkh₁ (zeroIndex (n+1) 2)
    have h₂ := hRep v f₂ h₂ hf₂ hh₂ hgf₂ hkh₂ (zeroIndex (n+1) 2)
    simp only [classicalDerivative_zero] at h₃ h₁ h₂
    filter_upwards [h₃, h₁, h₂, Lp.coeFn_add
      ((E₀ u).val (zeroIndex (n+1) 2)) ((E₀ v).val (zeroIndex (n+1) 2))]
      with x hx h₁x h₂x hadd
    change (E₀ (u+v)).val (zeroIndex (n+1) 2) x =
      ((E₀ u).val (zeroIndex (n+1) 2) + (E₀ v).val (zeroIndex (n+1) 2)) x
    rw [hx, hadd]
    simp only [Pi.add_apply, h₁x, h₂x]
    exact jetFunction_add i _ _ _ _ hf₁.continuous hf₂.continuous hh₁.continuous hh₂.continuous x
  have hSmul (c : 𝕜) (u : S) : E₀ (c • u) = c • E₀ u := by
    obtain ⟨f, hf, hgf, _⟩ := u.property.1
    obtain ⟨h, hh, hkh⟩ := u.property.2
    have hgfc : wholeLp ((c • u).val.1.val.val (zeroIndex n 1)) =ᵐ[volume] c • f := by
      change wholeLp (c • u.val.1.val.val (zeroIndex n 1)) =ᵐ[volume] _
      rw [wholeLp_smul]
      filter_upwards [Lp.coeFn_smul c (wholeLp (u.val.1.val.val (zeroIndex n 1))), hgf] with x hx hfx
      simpa only [Pi.smul_apply, hfx] using hx
    have hkhc : (c • u).val.2.val =ᵐ[volume] c • h := by
      change c • u.val.2.val =ᵐ[volume] _
      filter_upwards [Lp.coeFn_smul c u.val.2.val, hkh] with x hx hhx
      simpa only [Pi.smul_apply, hhx] using hx
    apply sobolev_underlying_injective 𝕜 (n+1) (upper i) 2 p
    apply Lp.ext
    have h₁ := hRep (c • u) (c • f) (c • h) (hf.const_smul c) (hh.const_smul c)
      hgfc hkhc (zeroIndex (n+1) 2)
    have h₂ := hRep u f h hf hh hgf hkh (zeroIndex (n+1) 2)
    simp only [classicalDerivative_zero] at h₁ h₂
    filter_upwards [h₁, h₂, Lp.coeFn_smul c ((E₀ u).val (zeroIndex (n+1) 2))]
      with x hx hux hsmul
    change (E₀ (c • u)).val (zeroIndex (n+1) 2) x =
      (c • (E₀ u).val (zeroIndex (n+1) 2)) x
    rw [hx, hsmul]
    simp only [Pi.smul_apply, hux]
    exact jetFunction_smul i c f h x
  let L : S →ₗ[𝕜] SpaceValue 𝕜 (n+1) (upper i) 2 p :=
    { toFun := E₀
      map_add' := hAdd
      map_smul' := hSmul }
  have hL : ∀ u : S, ‖L u‖ ≤ (2*C) * ‖S.subtype u‖ := by
    intro u
    exact (hBound u).trans (by
      calc
        _ ≤ C * (2 * ‖u.val‖) := mul_le_mul_of_nonneg_left
          (HigherDensity.jetData_norm_sum_le s σ p u.val) hC
        _ = _ := by
          change C * (2 * ‖u.val‖) = (2*C) * ‖u.val‖
          ring)
  letI : CompleteSpace (SpaceValue 𝕜 (n+1) (upper i) 2 p) :=
    sobolev_complete 𝕜 (n+1) (upper i) 2 p
  let E := L.extendOfNorm S.subtype
  have hAgree (u : S) : E (S.subtype u) = E₀ u :=
    L.extendOfNorm_eq hS ⟨2*C, hL⟩ u
  have hSmooth : ∀ g k (f h : Domain n → 𝕜)
      (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hh : ContDiff ℝ (↑(⊤ : ℕ∞)) h),
      wholeLp (g.val.val (zeroIndex n 1)) =ᵐ[volume] f →
      (∀ j, wholeLp (g.val.val (firstIndex j)) =ᵐ[volume]
        fun x => fderiv ℝ f x (coordinateVector j)) →
      k.val =ᵐ[volume] h →
      ∀ α, (E (g,k)).val α =ᵐ[volume.restrict (upper i : Set (Domain (n+1)))]
        Smoothing.classicalDerivative α (jetFunction i f h) := by
    intro g k f h hf hh hgf hgrad hkh α
    let u : S := ⟨(g,k), ⟨⟨f,hf,hgf,hgrad⟩,⟨h,hh,hkh⟩⟩⟩
    change (E (S.subtype u)).val α =ᵐ[volume.restrict (upper i : Set (Domain (n+1)))] _
    rw [hAgree u]
    exact hRep u f h hf hh hgf hkh α
  refine ⟨E, ?_, hSmooth, ?_⟩
  · intro g k
    refine (L.norm_extendOfNorm_apply_le hS (2*C) hL (g,k)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hC)
    change ‖(g,k)‖ ≤ ‖g‖ + ‖k‖
    rw [Prod.norm_def]
    exact max_le (le_add_of_nonneg_right (norm_nonneg k)) (le_add_of_nonneg_left (norm_nonneg g))
  · intro T hT
    let G : X →L[𝕜] Lp 𝕜 p (volume : Measure (Domain n)) :=
      (higherValueCLM σ p).comp (ContinuousLinearMap.fst 𝕜 _ _)
    let H : X →L[𝕜] Lp 𝕜 p (volume : Measure (Domain n)) :=
      (fractionalInclusion s p).comp (ContinuousLinearMap.snd 𝕜 _ _)
    have hjet (u : S) : HasBoundaryJets i T (E (S.subtype u)) (G u.val) (H u.val) := by
      obtain ⟨f, hf, hgf, hgrad⟩ := u.property.1
      obtain ⟨h, hh, hkh⟩ := u.property.2
      exact smooth_boundary_jets_of_classical i p f h hf hh (E u.val)
        (hSmooth u.val.1 u.val.2 f h hf hh hgf hgrad hkh)
        _ _ hgf hkh T hT
    have heqG : (fun u : X => reindexedTrace i T (orderOnePart (E u))) = G := by
      apply hS.equalizer
        ((reindexedTrace i T).continuous.comp
          ((orderOnePartCLM 𝕜 (n+1) (upper i) p).continuous.comp E.continuous)) G.continuous
      funext u
      exact ((hasBoundaryJets_iff i T _ _ _).mp (hjet u)).1
    have heqH : (fun u : X => reindexedTrace i T (derivativePart i (E u))) = H := by
      apply hS.equalizer
        ((reindexedTrace i T).continuous.comp
          ((derivativePartCLM 𝕜 (n+1) (upper i) p i).continuous.comp E.continuous)) H.continuous
      funext u
      exact ((hasBoundaryJets_iff i T _ _ _).mp (hjet u)).2
    intro g k
    apply (hasBoundaryJets_iff i T _ _ _).mpr
    exact ⟨congrFun heqG (g,k), congrFun heqH (g,k)⟩
end ExpandedFA.PartIV.SecondTraceFlat


noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
namespace ExpandedFA.PartIV.SecondTraceFlat
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open ExpandedFA.PartIV.SharpTraceExtension
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open SmoothLift
open ExpandedFA.Distributions.SmoothApproximateIdentitiesSpec

lemma average_stronglyMeasurable_raw {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : Continuous ρ) (hf : StronglyMeasurable f) :
    StronglyMeasurable (SmoothLift.average ρ f) := by
  have hs : Continuous (fun q : (Domain n × ℝ) × Domain n =>
      q.1.1 - q.1.2 • q.2) := by fun_prop
  exact ((hρ.stronglyMeasurable.comp_measurable measurable_snd).smul
    (hf.comp_measurable hs.measurable)).integral_prod_right'

lemma flatLift_stronglyMeasurable_raw {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : Continuous χ) (hρ : Continuous ρ) (hf : StronglyMeasurable f) :
    StronglyMeasurable (flatLift χ ρ f) :=
  (hχ.stronglyMeasurable.comp_measurable measurable_snd).smul
    (average_stronglyMeasurable_raw ρ f hρ hf)

lemma average_eLpNorm_le_raw {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hf : StronglyMeasurable f)
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hfp : MemLp f p volume) (t : ℝ) :
    eLpNorm (fun x => average ρ f (x, t)) p volume ≤
      eLpNorm ρ 1 volume * eLpNorm f p volume := by
  let : MeasurableSpace 𝕜 := borel 𝕜
  let F : Domain n × Domain n → 𝕜 := fun z => ρ z.2 • f (z.1 - t • z.2)
  have hF : Measurable F :=
    (hρ.comp continuous_snd).measurable.smul
      (hf.measurable.comp (continuous_fst.sub (continuous_snd.const_smul t)).measurable)
  have hρp : MemLp ρ 1 volume := hρ.memLp_of_hasCompactSupport hρc
  have hs (y : Domain n) : eLpNorm (fun x => F (x, y)) p volume =
      ‖ρ y‖ₑ * eLpNorm f p volume := by
    change eLpNorm ((ρ y) • (fun x => f (x - t • y))) p volume = _
    rw [eLpNorm_const_smul]
    exact congrArg (‖ρ y‖ₑ * ·) (eLpNorm_comp_measurePreserving hfp.aestronglyMeasurable
      (measurePreserving_sub_right volume (t • y)))
  have hmass : (∫⁻ y, eLpNorm (fun x => F (x, y)) p volume) =
      eLpNorm ρ 1 volume * eLpNorm f p volume := by
    simp_rw [hs]
    rw [lintegral_mul_const _ hρ.measurable.enorm,
      ← eLpNorm_one_eq_lintegral_enorm hρp.aestronglyMeasurable]
  obtain ⟨_, hb⟩ := minkowski_integral_eLpNorm volume volume p hp1 hp F hF
    (by rw [hmass]; exact ENNReal.mul_lt_top hρp.eLpNorm_lt_top hfp.eLpNorm_lt_top)
  exact hb.trans_eq hmass

lemma flatLift_lintegral_rpow_le_raw {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : StronglyMeasurable f)
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hfp : MemLp f p volume) :
    (∫⁻ z : Domain n × ℝ, ‖flatLift χ ρ f z‖ₑ ^ p.toReal) ≤
      (∫⁻ t : ℝ, ‖χ t‖ₑ ^ p.toReal) * (eLpNorm ρ 1 volume * eLpNorm f p volume) ^ p.toReal := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hA := average_stronglyMeasurable_raw ρ f hρ.continuous hf
  have hF := flatLift_stronglyMeasurable_raw χ ρ f hχ.continuous hρ.continuous hf
  have hAc (t : ℝ) : StronglyMeasurable (fun x : Domain n => average ρ f (x, t)) :=
    hA.comp_measurable measurable_prodMk_right
  have hs (t : ℝ) : (∫⁻ x : Domain n, ‖average ρ f (x, t)‖ₑ ^ p.toReal) ≤
      (eLpNorm ρ 1 volume * eLpNorm f p volume) ^ p.toReal := by
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hpr,
      ← eLpNorm_eq_eLpNorm' hp0 hp (hAc t).aestronglyMeasurable]
    exact ENNReal.rpow_le_rpow (average_eLpNorm_le_raw ρ f hρ.continuous hρc hf
      p hp1 hp hfp t) hpr.le
  calc
    _ = ∫⁻ t : ℝ, ∫⁻ x : Domain n, ‖flatLift χ ρ f (x, t)‖ₑ ^ p.toReal := by
      exact lintegral_prod_symm _ (hF.measurable.enorm.pow_const _).aemeasurable
    _ = ∫⁻ t : ℝ, ‖χ t‖ₑ ^ p.toReal * ∫⁻ x : Domain n, ‖average ρ f (x, t)‖ₑ ^ p.toReal := by
      apply lintegral_congr
      intro t
      simp only [flatLift, enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hpr.le]
      rw [lintegral_const_mul _ ((hAc t).measurable.enorm.pow_const _)]
    _ ≤ ∫⁻ t : ℝ, ‖χ t‖ₑ ^ p.toReal *
        (eLpNorm ρ 1 volume * eLpNorm f p volume) ^ p.toReal := by
      apply lintegral_mono
      intro t
      exact mul_le_mul' le_rfl (hs t)
    _ = _ := by rw [lintegral_mul_const _ (hχ.continuous.enorm.measurable.pow_const _)]

lemma flatLift_eLpNorm_le_raw {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : StronglyMeasurable f)
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hfp : MemLp f p volume) :
    eLpNorm (flatLift χ ρ f) p volume ≤
      eLpNorm χ p volume * eLpNorm ρ 1 volume * eLpNorm f p volume := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hi : 0 ≤ 1 / p.toReal := (one_div_pos.mpr hpr).le
  have hpow : p.toReal * (1 / p.toReal) = 1 := by field_simp
  rw [mul_assoc]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp
    (flatLift_stronglyMeasurable_raw χ ρ f hχ.continuous hρ.continuous hf).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hχ.continuous.aestronglyMeasurable]
  calc
    _ ≤ ((∫⁻ t : ℝ, ‖χ t‖ₑ ^ p.toReal) *
        (eLpNorm ρ 1 volume * eLpNorm f p volume) ^ p.toReal) ^ (1 / p.toReal) :=
      ENNReal.rpow_le_rpow (flatLift_lintegral_rpow_le_raw χ ρ f hχ hρ hρc hf p hp1 hp hfp) hi
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hi, ← ENNReal.rpow_mul, hpow, ENNReal.rpow_one]


lemma liftFunction_stronglyMeasurable_raw {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : Continuous χ) (hρ : Continuous ρ) (hf : StronglyMeasurable f) :
    StronglyMeasurable (liftFunction i χ ρ f) :=
  (flatLift_stronglyMeasurable_raw χ ρ f hχ hρ hf).comp_measurable
    (flatCoordinates i).continuous.measurable

lemma liftFunction_eLpNorm_le_raw {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : StronglyMeasurable f)
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hfp : MemLp f p volume) :
    eLpNorm (liftFunction i χ ρ f) p (volume.restrict (upper i : Set (Domain (n + 1)))) ≤
      eLpNorm χ p volume * eLpNorm ρ 1 volume * eLpNorm f p volume := by
  apply (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
  have he := eLpNorm_comp_measurePreserving (p := p)
    (liftFunction_stronglyMeasurable_raw i χ ρ f hχ.continuous hρ.continuous hf).aestronglyMeasurable
    (flatCoordinates_symm_measurePreserving i)
  have hfun : liftFunction i χ ρ f ∘ (flatCoordinates i).symm = flatLift χ ρ f := by
    funext z
    simp only [Function.comp_apply, liftFunction, Homeomorph.apply_symm_apply]
  rw [hfun] at he
  rw [← he]
  exact flatLift_eLpNorm_le_raw χ ρ f hχ hρ hρc hf p hp1 hp hfp

lemma liftFunction_memLp_raw {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
    (hf : StronglyMeasurable f)
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hfp : MemLp f p volume) :
    MemLp (liftFunction i χ ρ f) p (volume.restrict (upper i : Set (Domain (n + 1)))) := by
  exact (liftFunction_eLpNorm_le_raw i χ ρ f hχ hρ hρc hf p hp1 hp hfp).trans_lt
    (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top
        (hχ.continuous.memLp_of_hasCompactSupport hχc).eLpNorm_lt_top
        (hρ.continuous.memLp_of_hasCompactSupport hρc).eLpNorm_lt_top)
      hfp.eLpNorm_lt_top)

lemma average_congr_ae_raw {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f g : Domain n → 𝕜) (hfg : f =ᵐ[volume] g)
    (x : Domain n) {t : ℝ} (ht : 0 < t) :
    SmoothLift.average ρ f (x,t) = SmoothLift.average ρ g (x,t) := by
  change (∫ y, ρ y • f (x - t • y)) = ∫ y, ρ y • g (x - t • y)
  rw [← mollify_eq_signed_average ρ f t ht x, ← mollify_eq_signed_average ρ g t ht x]
  exact congrFun (convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) Filter.EventuallyEq.rfl hfg) x

lemma average_integrable_raw {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f : Domain n → 𝕜)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hfp : MemLp f p volume)
    (x : Domain n) {t : ℝ} (ht : 0 < t) :
    Integrable (fun y => ρ y • f (x - t • y)) := by
  have hk : Continuous (ScaledKernelValue ρ t) :=
    continuous_const.mul (hρ.comp (continuous_id.const_smul t⁻¹))
  have hkc : HasCompactSupport (ScaledKernelValue ρ t) :=
    (hρc.comp_isClosedEmbedding
      (Homeomorph.smul (Units.mk0 t⁻¹ (inv_ne_zero ht.ne'))).isClosedEmbedding).mul_left
  have hi := hkc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hk
    (hfp.locallyIntegrable hp1) x
  have hi' := hi.integrable.comp_smul ht.ne'
  convert hi'.smul (t ^ n) using 1
  funext y
  simp [ScaledKernelValue, smul_smul, inv_smul_smul₀ ht.ne', ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero n ht.ne')]

lemma average_add_raw {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (ρ : Domain n → ℝ) (f g : Domain n → 𝕜)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hfp : MemLp f p volume) (hgp : MemLp g p volume)
    (x : Domain n) {t : ℝ} (ht : 0 < t) :
    SmoothLift.average ρ (f+g) (x,t) = SmoothLift.average ρ f (x,t) + SmoothLift.average ρ g (x,t) := by
  simp only [SmoothLift.average, Pi.add_apply, smul_add]
  exact integral_add (average_integrable_raw ρ f hρ hρc p hp1 hfp x ht)
    (average_integrable_raw ρ g hρ hρc p hp1 hgp x ht)


lemma liftFunction_congr_ae_raw {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f g : Domain n → 𝕜)
    (hfg : f =ᵐ[volume] g) :
    liftFunction i χ ρ f =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))]
      liftFunction i χ ρ g := by
  filter_upwards [ae_restrict_mem (upper i).isOpen.measurableSet] with x hx
  exact congrArg (χ (flatCoordinates i x).2 • ·)
    (average_congr_ae_raw ρ f g hfg (flatCoordinates i x).1 hx)

lemma liftFunction_add_ae_raw {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ) (f g : Domain n → 𝕜)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hfp : MemLp f p volume) (hgp : MemLp g p volume) :
    liftFunction i χ ρ (f+g) =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))]
      liftFunction i χ ρ f + liftFunction i χ ρ g := by
  filter_upwards [ae_restrict_mem (upper i).isOpen.measurableSet] with x hx
  change χ (x i) • SmoothLift.average ρ (f+g) (i.removeNth x,x i) =
    χ (x i) • SmoothLift.average ρ f (i.removeNth x,x i) +
      χ (x i) • SmoothLift.average ρ g (i.removeNth x,x i)
  rw [average_add_raw ρ f g hρ hρc p hp1 hfp hgp (i.removeNth x) hx, smul_add]

section RawLiftOperator
variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
variable (i : Fin (n + 1)) (χ : ℝ → ℝ) (ρ : Domain n → ℝ)
variable (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hχc : HasCompactSupport χ)
variable (hρ : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ) (hρc : HasCompactSupport ρ)
variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)

/-- The raw formula considered only as an operator into ordinary Lp. -/
def rawLiftLp (u : Lp 𝕜 p (volume : Measure (Domain n))) :
    Lp 𝕜 p (volume.restrict (upper i : Set (Domain (n + 1)))) :=
  (liftFunction_memLp_raw i χ ρ u hχ hχc hρ hρc (Lp.stronglyMeasurable u)
    p Fact.out hp (Lp.memLp u)).toLp (liftFunction i χ ρ u)

lemma rawLiftLp_representative (u : Lp 𝕜 p (volume : Measure (Domain n))) :
    rawLiftLp i χ ρ hχ hχc hρ hρc p hp u =ᵐ[
      volume.restrict (upper i : Set (Domain (n + 1)))] liftFunction i χ ρ u :=
  MemLp.coeFn_toLp _

lemma rawLiftLp_add (u v : Lp 𝕜 p (volume : Measure (Domain n))) :
    rawLiftLp i χ ρ hχ hχc hρ hρc p hp (u+v) =
      rawLiftLp i χ ρ hχ hχc hρ hρc p hp u + rawLiftLp i χ ρ hχ hχc hρ hρc p hp v := by
  apply Lp.ext
  have heq := (liftFunction_congr_ae_raw i χ ρ (u+v) (u+v : Domain n → 𝕜)
    (Lp.coeFn_add u v)).trans
      (liftFunction_add_ae_raw i χ ρ u v hρ.continuous hρc p Fact.out (Lp.memLp u) (Lp.memLp v))
  filter_upwards [rawLiftLp_representative i χ ρ hχ hχc hρ hρc p hp (u+v),
    rawLiftLp_representative i χ ρ hχ hχc hρ hρc p hp u,
    rawLiftLp_representative i χ ρ hχ hχc hρ hρc p hp v,
    Lp.coeFn_add (rawLiftLp i χ ρ hχ hχc hρ hρc p hp u)
      (rawLiftLp i χ ρ hχ hχc hρ hρc p hp v), heq] with x huv hu hv hadd he
  simp only [Pi.add_apply] at he hadd
  rw [huv, hadd, hu, hv, he]

lemma rawLiftLp_smul (c : 𝕜) (u : Lp 𝕜 p (volume : Measure (Domain n))) :
    rawLiftLp i χ ρ hχ hχc hρ hρc p hp (c • u) =
      c • rawLiftLp i χ ρ hχ hχc hρ hρc p hp u := by
  apply Lp.ext
  have heq := liftFunction_congr_ae_raw i χ ρ (c • u) (c • (u : Domain n → 𝕜))
    (Lp.coeFn_smul c u)
  filter_upwards [rawLiftLp_representative i χ ρ hχ hχc hρ hρc p hp (c • u),
    rawLiftLp_representative i χ ρ hχ hχc hρ hρc p hp u,
    Lp.coeFn_smul c (rawLiftLp i χ ρ hχ hχc hρ hρc p hp u), heq] with x hcu hu hsmul he
  simp only [Pi.smul_apply] at hsmul
  rw [hcu, hsmul, hu, he, liftFunction_smul]

lemma rawLiftLp_norm_le (u : Lp 𝕜 p (volume : Measure (Domain n))) :
    ‖rawLiftLp i χ ρ hχ hχc hρ hρc p hp u‖ ≤
      (eLpNorm χ p volume).toReal * (eLpNorm ρ 1 volume).toReal * ‖u‖ := by
  have hχp : MemLp χ p volume := hχ.continuous.memLp_of_hasCompactSupport hχc
  have hρp : MemLp ρ 1 volume := hρ.continuous.memLp_of_hasCompactSupport hρc
  have hb := liftFunction_eLpNorm_le_raw i χ ρ u hχ hρ hρc (Lp.stronglyMeasurable u)
    p Fact.out hp (Lp.memLp u)
  rw [← eLpNorm_congr_ae (rawLiftLp_representative i χ ρ hχ hχc hρ hρc p hp u),
    ← Lp.enorm_def, ← Lp.enorm_def] at hb
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hχp.eLpNorm_ne_top hρp.eLpNorm_ne_top) (by finiteness)) hb
  simpa only [ENNReal.toReal_mul, toReal_enorm] using hreal

/-- Boundedness and representative independence of the literal kernel formula. -/
def rawLiftOperator : Lp 𝕜 p (volume : Measure (Domain n)) →L[𝕜]
    Lp 𝕜 p (volume.restrict (upper i : Set (Domain (n + 1)))) :=
  ({ toFun := rawLiftLp i χ ρ hχ hχc hρ hρc p hp
     map_add' := rawLiftLp_add i χ ρ hχ hχc hρ hρc p hp
     map_smul' := rawLiftLp_smul i χ ρ hχ hχc hρ hρc p hp } :
      Lp 𝕜 p (volume : Measure (Domain n)) →ₗ[𝕜]
        Lp 𝕜 p (volume.restrict (upper i : Set (Domain (n + 1))))).mkContinuous
          ((eLpNorm χ p volume).toReal * (eLpNorm ρ 1 volume).toReal)
          (rawLiftLp_norm_le i χ ρ hχ hχc hρ hρc p hp)

lemma rawLiftOperator_representative (u : Lp 𝕜 p (volume : Measure (Domain n))) :
    rawLiftOperator i χ ρ hχ hχc hρ hρc p hp u =ᵐ[
      volume.restrict (upper i : Set (Domain (n + 1)))] liftFunction i χ ρ u :=
  rawLiftLp_representative i χ ρ hχ hχc hρ hρc p hp u

end RawLiftOperator

/-- The literal simultaneous formula respects arbitrary a.e. representatives. -/
lemma jetFunction_congr_ae {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (f₁ f₂ h₁ h₂ : Domain n → 𝕜)
    (hf : f₁ =ᵐ[volume] f₂) (hh : h₁ =ᵐ[volume] h₂) :
    jetFunction i f₁ h₁ =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))]
      jetFunction i f₂ h₂ := by
  filter_upwards [ae_restrict_mem (upper i).isOpen.measurableSet] with x hx
  have hfa := average_congr_ae_raw (jetMollifier n) f₁ f₂ hf (i.removeNth x) hx
  have hha := average_congr_ae_raw (jetMollifier n) h₁ h₂ hh (i.removeNth x) hx
  change jetCutoff (x i) • (SmoothLift.average (jetMollifier n) f₁ (i.removeNth x,x i) +
      (x i) • SmoothLift.average (jetMollifier n) h₁ (i.removeNth x,x i)) = _
  rw [hfa, hha]
  rfl

/-- Zeroth-order Lp operator of the prescribed simultaneous kernel formula. -/
def rawJetOperator {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    (Lp 𝕜 p (volume : Measure (Domain n)) × Lp 𝕜 p (volume : Measure (Domain n))) →L[𝕜]
      Lp 𝕜 p (volume.restrict (upper i : Set (Domain (n + 1)))) :=
  (rawLiftOperator i jetCutoff (jetMollifier n) jetCutoff_contDiff jetCutoff_compactSupport
    (jetMollifier_contDiff n) (jetMollifier_compactSupport n) p hp).comp (ContinuousLinearMap.fst 𝕜 _ _) +
  (rawLiftOperator i (fun t => jetCutoff t * t) (jetMollifier n)
    (jetCutoff_contDiff.mul contDiff_id) jetCutoff_compactSupport.mul_right
    (jetMollifier_contDiff n) (jetMollifier_compactSupport n) p hp).comp (ContinuousLinearMap.snd 𝕜 _ _)

lemma rawJetOperator_representative {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u v : Lp 𝕜 p (volume : Measure (Domain n))) :
    rawJetOperator i p hp (u,v) =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))]
      jetFunction i u v := by
  let A := rawLiftOperator i jetCutoff (jetMollifier n) jetCutoff_contDiff jetCutoff_compactSupport
    (jetMollifier_contDiff n) (jetMollifier_compactSupport n) p hp u
  let B := rawLiftOperator i (fun t => jetCutoff t * t) (jetMollifier n)
    (jetCutoff_contDiff.mul contDiff_id) jetCutoff_compactSupport.mul_right
    (jetMollifier_contDiff n) (jetMollifier_compactSupport n) p hp v
  change A + B =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))] jetFunction i u v
  filter_upwards [Lp.coeFn_add A B,
    rawLiftOperator_representative i jetCutoff (jetMollifier n) jetCutoff_contDiff jetCutoff_compactSupport
      (jetMollifier_contDiff n) (jetMollifier_compactSupport n) p hp u,
    rawLiftOperator_representative i (fun t => jetCutoff t * t) (jetMollifier n)
      (jetCutoff_contDiff.mul contDiff_id) jetCutoff_compactSupport.mul_right
      (jetMollifier_contDiff n) (jetMollifier_compactSupport n) p hp v] with x hadd ha hb
  change (A+B) x = _
  rw [hadd]
  change A x + B x = _
  rw [show A x = _ from ha, show B x = _ from hb]
  change jetCutoff (x i) • SmoothLift.average (jetMollifier n) u (i.removeNth x,x i) +
      (jetCutoff (x i) * x i) • SmoothLift.average (jetMollifier n) v (i.removeNth x,x i) =
    jetCutoff (x i) • (SmoothLift.average (jetMollifier n) u (i.removeNth x,x i) +
      x i • SmoothLift.average (jetMollifier n) v (i.removeNth x,x i))
  rw [smul_add, smul_smul]

lemma rawJetOperator_representative_of_ae {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u v : Lp 𝕜 p (volume : Measure (Domain n)))
    (f h : Domain n → 𝕜) (hf : u =ᵐ[volume] f) (hh : v =ᵐ[volume] h) :
    rawJetOperator i p hp (u,v) =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))]
      jetFunction i f h :=
  (rawJetOperator_representative i p hp u v).trans (jetFunction_congr_ae i u f v h hf hh)

end ExpandedFA.PartIV.SecondTraceFlat


noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
namespace ExpandedFA.PartIV.SecondTraceFlat
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open ExpandedFA.PartIV.SharpTraceExtension
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- The simultaneous value and inward-normal trace extension, with the
prescribed even-mollifier formula for arbitrary fractional boundary data. -/
theorem bounded_jet_extension : Specs.ExpandedFA.PartIV.SecondTraceFlat.BoundedJetExtension := by
  intro n p _ hp1 hp
  obtain ⟨C, hC, hE⟩ := bounded_jet_extension_clm n p hp1 hp
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ i
  letI : Fact (p ≠ ∞) := ⟨hp⟩
  refine ⟨(coordinate_trace_exists i hp).exists, ?_⟩
  obtain ⟨E, hBound, hSmooth, hJets⟩ := hE 𝕜 i
  let σ := 2 - 1 / p.toReal
  let s := 1 - 1 / p.toReal
  let X := HigherFractionalSpace 𝕜 n σ p × FractionalSpace 𝕜 n s p
  let S := HigherDensity.smoothJetDataSubmodule (𝕜 := 𝕜) (n := n) s σ p
  have hS : DenseRange S.subtype := HigherDensity.smoothJetData_denseRange s σ p
    (endpoint_exponent hp1 hp).1 (endpoint_exponent hp1 hp).2
  let V := sobolevComponentCLM 𝕜 (n+1) (upper i) 2 p (zeroIndex (n+1) 2)
  let R : X →L[𝕜] DomainLp 𝕜 (upper i) p :=
    (rawJetOperator i p hp).comp (jetDataInclusionCLM σ s p)
  have heq : (fun z : X => V (E z)) = R := by
    apply hS.equalizer (V.continuous.comp E.continuous) R.continuous
    funext u
    obtain ⟨f, hf, hgf, hgrad⟩ := u.property.1
    obtain ⟨h, hh, hkh⟩ := u.property.2
    apply Lp.ext
    have hsmooth := hSmooth u.val.1 u.val.2 f h hf hh hgf hgrad hkh (zeroIndex (n+1) 2)
    simp only [classicalDerivative_zero] at hsmooth
    exact hsmooth.trans (rawJetOperator_representative_of_ae i p hp
      (wholeLp (u.val.1.val.val (zeroIndex n 1))) u.val.2.val f h hgf hkh).symm
  refine ⟨fun g h => E (g,h), ?_, ?_, hBound, ?_, hJets⟩
  · intro g₁ g₂ g₃ h₁ h₂ h₃ hg hh
    have hgeq : g₃ = g₁+g₂ := Subtype.ext hg
    have hheq : h₃ = h₁+h₂ := Subtype.ext hh
    rw [hgeq, hheq]
    exact E.map_add (g₁,h₁) (g₂,h₂)
  · intro c g₁ g₂ h₁ h₂ hg hh
    have hgeq : g₂ = c • g₁ := Subtype.ext hg
    have hheq : h₂ = c • h₁ := Subtype.ext hh
    rw [hgeq, hheq]
    exact E.map_smul c (g₁,h₁)
  · intro g h
    have hv : (E (g,h)).val (zeroIndex (n+1) 2) =
        rawJetOperator i p hp (wholeLp (g.val.val (zeroIndex n 1)), h.val) :=
      congrFun heq (g,h)
    rw [hv]
    exact rawJetOperator_representative i p hp _ _
end ExpandedFA.PartIV.SecondTraceFlat
