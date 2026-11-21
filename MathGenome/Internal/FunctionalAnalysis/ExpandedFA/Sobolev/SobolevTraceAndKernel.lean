import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.C1DomainExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.OneDimensionalSobolev
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Algebra.Group.ContinuousDiv
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Operator.Extend
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.LpTranslationContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Topology

namespace ExpandedFA.Sobolev.Trace
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open OneDimensional

/-- Density determines at most one bounded extension of smooth restriction. -/
theorem trace_uniqueness :
    Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel.TraceUniqueness := by
  intro 𝕜 _ d Ω hΩ hc p _ hp T S hT hS
  have hd := C1Extension.smooth_density 𝕜 d Ω hΩ hc p hp
  have heq : EqOn T S (C1Extension.SmoothUpToBoundary (𝕜 := 𝕜) Ω p) := by
    rintro u ⟨f, hf, hu⟩
    exact Lp.ext ((hT u f hf hu).trans (hS u f hf hu).symm)
  apply ContinuousLinearMap.ext
  intro u
  exact heq.closure T.continuous S.continuous (hd u)

/-- Surface measure carries only frontier data. -/
theorem surfaceMeasure_ae_frontier {d : ℕ} (Ω : Opens (Domain d)) :
    ∀ᵐ x ∂surfaceMeasure Ω, x ∈ frontier (Ω : Set (Domain d)) := by
  exact Measure.ae_smul_measure (ae_restrict_mem isClosed_frontier.measurableSet) _

/-- Compact tests vanish on the boundary and bounded maps preserve their
norm closure. This needs no regularity assumption on the boundary. -/
theorem kernel_contains_zeroSpace :
    Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel.KernelContainsZeroSpace := by
  intro 𝕜 _ d Ω p _ hp T hT
  apply (smoothSubmodule 𝕜 d Ω 1 p).topologicalClosure_minimal _ T.isClosed_ker
  rintro u ⟨φ, hφ⟩
  change T u = 0
  apply Lp.ext
  filter_upwards [hT u φ φ.contDiff hφ, surfaceMeasure_ae_frontier Ω,
    Lp.coeFn_zero 𝕜 p (surfaceMeasure Ω)] with x hx hxf hz
  rw [hx, hz]
  exact φ.zero_on_compl ((Ω.isOpen.frontier_eq ▸ hxf).2)

section ZeroExtension
variable {𝕜 : Type} [RCLike 𝕜] {d m : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Zero extend each entry of a derivative tuple as Lp data, before asserting
any distributional identities. -/
def zeroExtensionTuple (u : SpaceValue 𝕜 d Ω m p) : DerivativeTuple 𝕜 (⊤ : Opens (Domain d)) m p :=
  WithLp.toLp 1 (fun α => C1Extension.zeroLp ⊤ (u.val α))

theorem continuous_zeroExtensionTuple :
    Continuous (zeroExtensionTuple : SpaceValue 𝕜 d Ω m p → DerivativeTuple 𝕜 (⊤ : Opens (Domain d)) m p) := by
  let Z : DomainLp 𝕜 Ω p →L[𝕜] DomainLp 𝕜 ⊤ p :=
    (C1Extension.zeroLpLM (𝕜 := 𝕜) (Ω := Ω) (p := p) ⊤).mkContinuous 1 (fun u => by
      change ‖C1Extension.zeroLp (⊤ : Opens (Domain d)) u‖ ≤ 1 * ‖u‖
      rw [C1Extension.zeroLp_norm le_top, one_mul])
  apply (PiLp.continuous_toLp 1 _).comp
  apply continuous_pi
  intro α
  exact Z.continuous.comp ((PiLp.continuous_apply 1 _ α).comp continuous_subtype_val)

/-- Every smooth jet has some compact support in the domain. Taking the
finite union of its derivative supports avoids any support convention. -/
theorem smooth_jet_supported (u : SpaceValue 𝕜 d Ω m p)
    (hu : u ∈ smoothSubmodule 𝕜 d Ω m p) :
    ∃ K : Set (Domain d), IsCompact K ∧ K ⊆ Ω ∧
      ∀ α, ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))), x ∉ K → u.val α x = 0 := by
  classical
  obtain ⟨φ, hφ⟩ := hu
  have he : u = testToSobolev m φ := by
    apply sobolev_underlying_injective 𝕜 d Ω m p
    change u.val (zeroIndex d m) = (testToSobolev (p := p) m φ).val (zeroIndex d m)
    rw [testToSobolev_underlying]
    exact Lp.ext (hφ.trans (testToDomainLp_coe φ).symm)
  subst u
  let ψ : DerivativeIndex d m → Tests 𝕜 Ω :=
    fun α => testPartialCLM (multiIndexWord (natIndex α)).reverse φ
  let K : Set (Domain d) := ⋃ α, tsupport (ψ α)
  refine ⟨K, isCompact_iUnion (fun α => (ψ α).hasCompactSupport), ?_, ?_⟩
  · exact iUnion_subset (fun α => (ψ α).tsupport_subset)
  · intro α
    filter_upwards [testToDomainLp_coe (p := p) (ψ α)] with x hx
    intro hxK
    change testToDomainLp (p := p) (ψ α) x = 0
    rw [hx]
    exact image_eq_zero_of_notMem_tsupport (fun hxψ => hxK (mem_iUnion.mpr ⟨α, hxψ⟩))

/-- Weak derivative identities are closed under norm limits of zero-extended
jets; this is the forward zero-extension theorem on arbitrary open sets. -/
theorem zeroExtensionTuple_mem (hp : p ≠ ∞) (u : SpaceValue 𝕜 d Ω m p)
    (hu : u ∈ ZeroSpaceValue 𝕜 d Ω m p hp) :
    zeroExtensionTuple u ∈ derivativeGraph 𝕜 ⊤ m p := by
  have hclosed : IsClosed {v : SpaceValue 𝕜 d Ω m p |
      zeroExtensionTuple v ∈ derivativeGraph 𝕜 ⊤ m p} :=
    Smoothing.derivativeGraph_isClosed.preimage continuous_zeroExtensionTuple
  apply closure_minimal (t := {v : SpaceValue 𝕜 d Ω m p |
    zeroExtensionTuple v ∈ derivativeGraph 𝕜 ⊤ m p}) ?_ hclosed hu
  intro v hv
  obtain ⟨K, hK, hKΩ, hvs⟩ := smooth_jet_supported v hv
  exact C1Extension.zeroJet_mem le_top K (by simpa using hK.isClosed) hKΩ v hvs

end ZeroExtension

/-- Isometric zero extension of every weak derivative, proved by closure,
without any boundary regularity assumption. -/
theorem zero_extension_of_zeroSpace :
    Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel.ZeroExtensionOfZeroSpace := by
  intro 𝕜 _ d Ω m p _ hp u hu
  refine ⟨⟨zeroExtensionTuple u, zeroExtensionTuple_mem hp u hu⟩, ?_, ?_⟩
  · intro α
    change C1Extension.zeroLp ⊤ (u.val α) =ᵐ[volume] _
    simpa using (C1Extension.zeroLp_coe (Λ := ⊤) (u.val α))
  · change ‖zeroExtensionTuple u‖ = ‖u.val‖
    rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
    exact Finset.sum_congr rfl (fun α _ => C1Extension.zeroLp_norm le_top (u.val α))

theorem interval_frontier {a b : ℝ} (hab : a < b) :
    frontier (lineDomain ⟨Ioo a b, isOpen_Ioo⟩ : Set (Domain 1)) =
      {linePoint a, linePoint b} := by
  rw [show (lineDomain ⟨Ioo a b, isOpen_Ioo⟩ : Set (Domain 1)) =
    (Homeomorph.funUnique (Fin 1) ℝ) ⁻¹' Ioo a b from rfl,
    ← Homeomorph.preimage_frontier, frontier_Ioo hab]
  ext z
  simp only [mem_preimage, mem_insert_iff, mem_singleton_iff]
  change (z 0 = a ∨ z 0 = b) ↔ _
  constructor
  · rintro (h | h)
    · left
      rw [← h, linePoint_coordinate]
    · right
      rw [← h, linePoint_coordinate]
  · rintro (rfl | rfl) <;> simp

theorem interval_isC1 {a b : ℝ} (hab : a < b) :
    C1Extension.IsC1Domain (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) := by
  intro x hx
  rw [interval_frontier hab] at hx
  rcases hx with (rfl | hx)
  · let Φ := (Homeomorph.subRight (linePoint a)).toOpenPartialHomeomorph.restrOpen
        {z : Domain 1 | z 0 < b} (isOpen_lt (continuous_apply 0) continuous_const)
    refine ⟨0, Φ, ?_, ?_, ?_, ?_, ?_⟩
    · change linePoint a ∈ univ ∩ _
      exact ⟨mem_univ _, hab⟩
    · change a - a = 0
      ring
    · exact (contDiff_id.sub contDiff_const).contDiffOn
    · exact (contDiff_id.add contDiff_const).contDiffOn
    · intro y hy
      change y ∈ univ ∩ {z : Domain 1 | z 0 < b} at hy
      change (a < y 0 ∧ y 0 < b) ↔ 0 < y 0 - a
      exact ⟨fun h => sub_pos.mpr h.1, fun h => ⟨sub_pos.mp h, hy.2⟩⟩
  · have hxb : x = linePoint b := hx
    subst x
    let Φ := (Homeomorph.subLeft (linePoint b)).toOpenPartialHomeomorph.restrOpen
        {z : Domain 1 | a < z 0} (isOpen_lt continuous_const (continuous_apply 0))
    refine ⟨0, Φ, ?_, ?_, ?_, ?_, ?_⟩
    · change linePoint b ∈ univ ∩ _
      exact ⟨mem_univ _, hab⟩
    · change b - b = 0
      ring
    · exact (contDiff_const.sub contDiff_id).contDiffOn
    · exact (contDiff_id.neg.add contDiff_const).contDiffOn
    · intro y hy
      change y ∈ univ ∩ {z : Domain 1 | a < z 0} at hy
      change (a < y 0 ∧ y 0 < b) ↔ 0 < b - y 0
      exact ⟨fun h => sub_pos.mpr h.2, fun h => ⟨hy.2, sub_pos.mp h⟩⟩

theorem surfaceMeasure_singleton_le_one {a b : ℝ} (x : Domain 1) :
    surfaceMeasure (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) {x} ≤ 1 := by
  have hunit : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (1 - 1))) (1 / 2)) = 1 := by
    change volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) (1 / 2)) = 1
    rw [volume_euclideanSpace_eq_dirac]
    simp
  simp only [surfaceMeasure, hunit, one_smul, Nat.sub_self, Nat.cast_zero]
  apply le_trans (Measure.restrict_le_self _)
  have he : MeasurableEmbedding (WithLp.toLp 2 : Domain 1 → EuclideanSpace ℝ (Fin 1)) :=
    (PiLp.homeomorph 2 (fun _ : Fin 1 => ℝ)).symm.measurableEmbedding
  rw [he.comap_apply,
    image_singleton, Measure.hausdorffMeasure_zero_singleton]


/-- In dimension one each boundary point has its usual counting mass one
under the normalized Hausdorff surface measure. -/
theorem surfaceMeasure_singleton_of_frontier {Ω : Opens (Domain 1)}
    {x : Domain 1} (hx : x ∈ frontier (Ω : Set (Domain 1))) :
    surfaceMeasure Ω {x} = 1 := by
  have hunit : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (1 - 1))) (1 / 2)) = 1 := by
    change volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) (1 / 2)) = 1
    rw [volume_euclideanSpace_eq_dirac]
    simp
  simp only [surfaceMeasure, hunit, one_smul, Nat.sub_self, Nat.cast_zero]
  rw [Measure.restrict_apply (measurableSet_singleton _),
    inter_eq_left.mpr (singleton_subset_iff.mpr hx)]
  have he : MeasurableEmbedding (WithLp.toLp 2 : Domain 1 → EuclideanSpace ℝ (Fin 1)) :=
    (PiLp.homeomorph 2 (fun _ : Fin 1 => ℝ)).symm.measurableEmbedding
  rw [he.comap_apply, image_singleton, Measure.hausdorffMeasure_zero_singleton]

/-- An a.e. equality determines the value at every atom of positive mass. -/
theorem eq_at_of_ae_eq_of_singleton_ne_zero {X Y : Type*} [MeasurableSpace X]
    {μ : Measure X} {f g : X → Y} (h : f =ᵐ[μ] g) {x : X} (hx : μ {x} ≠ 0) :
    f x = g x := by
  by_contra hne
  have hle : μ {x} ≤ μ {y | f y ≠ g y} := measure_mono (singleton_subset_iff.mpr hne)
  have hz : μ {y | f y ≠ g y} = 0 := ae_iff.mp h
  exact hx (le_antisymm (hz ▸ hle) bot_le)

section Interval
variable {𝕜 : Type} [RCLike 𝕜] {a b : ℝ} (hab : a < b)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A chosen continuous representative is used only to define the endpoint
operator. Uniqueness below removes all dependence on this choice. -/
def intervalRepresentative (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p) : ℝ → 𝕜 :=
  Classical.choose (representative_existence 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ ordConnected_Ioo p u)

theorem intervalRepresentative_spec (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p) :
    PrimitiveRepresentative u (intervalRepresentative u) :=
  Classical.choose_spec (representative_existence 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ ordConnected_Ioo p u)

include hab

/-- All continuous versions of the underlying a.e. class have the same
values on the closed interval, including its endpoints. -/
theorem intervalRepresentative_eq (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p)
    (f : ℝ → 𝕜) (hf : ContinuousOn f (Icc a b))
    (hu : Represents (baseLp u) f) :
    EqOn (intervalRepresentative u) f (Icc a b) := by
  have hcl : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  have hs := intervalRepresentative_spec u
  have he := representative_uniqueness 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p
    (baseLp u) (intervalRepresentative u) f hs.1 (by
      change ContinuousOn f (closure (Ioo a b))
      rwa [hcl]) hs.2.1 hu
  change EqOn _ _ (closure (Ioo a b)) at he
  rwa [hcl] at he

/-- Left and right endpoint evaluations. The target uses its finite product
norm; in particular it has the same topology as Lp on the two endpoint atoms. -/
def endpointValues (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p) : Fin 2 → 𝕜 :=
  fun i => intervalRepresentative u (endpoint a b i)

theorem endpoint_mem (i : Fin 2) : endpoint a b i ∈ Icc a b := by
  simp only [endpoint]
  split_ifs <;> exact ⟨by linarith, by linarith⟩

theorem endpointValues_eq (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p)
    (f : ℝ → 𝕜) (hf : PrimitiveRepresentative u f) (i : Fin 2) :
    endpointValues u i = f (endpoint a b i) := by
  apply intervalRepresentative_eq hab u f
    (by
      have hc := hf.1
      change ContinuousOn f (closure (Ioo a b)) at hc
      rwa [closure_Ioo hab.ne] at hc) hf.2.1
  exact endpoint_mem hab i

/-- Linearity follows from a.e. linearity and uniqueness of continuous
representatives, so no pointwise choice of Lp representatives is assumed. -/
def endpointValuesLM : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p →ₗ[𝕜] (Fin 2 → 𝕜) where
  toFun := endpointValues
  map_add' u v := by
    let f := intervalRepresentative u
    let g := intervalRepresentative v
    have hf := intervalRepresentative_spec u
    have hg := intervalRepresentative_spec v
    have he : EqOn (intervalRepresentative (u + v)) (fun t => f t + g t) (Icc a b) := by
      apply intervalRepresentative_eq hab (u + v)
      · have hc := hf.1.add hg.1
        change ContinuousOn (fun t => f t + g t) (closure (Ioo a b)) at hc
        rwa [closure_Ioo hab.ne] at hc
      · filter_upwards [hf.2.1, hg.2.1, Lp.coeFn_add (baseLp u) (baseLp v)] with z hu hv huv
        change (baseLp u + baseLp v : DomainLp 𝕜 _ p) z = _
        rw [huv]
        exact congrArg₂ (· + ·) hu hv
    funext i
    exact he (endpoint_mem hab i)
  map_smul' c u := by
    let f := intervalRepresentative u
    have hf := intervalRepresentative_spec u
    have he : EqOn (intervalRepresentative (c • u)) (fun t => c • f t) (Icc a b) := by
      apply intervalRepresentative_eq hab (c • u)
      · have hc := hf.1.const_smul c
        change ContinuousOn (fun t => c • f t) (closure (Ioo a b)) at hc
        rwa [closure_Ioo hab.ne] at hc
      · filter_upwards [hf.2.1, Lp.coeFn_smul c (baseLp u)] with z hu hcu
        change (c • baseLp u : DomainLp 𝕜 _ p) z = _
        rw [hcu]
        exact congrArg (c • ·) hu
    funext i
    exact he (endpoint_mem hab i)

/-- An explicit bound inherited from the source's interval estimate. -/
theorem endpointValues_norm_le (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p) :
    ‖endpointValues u‖ ≤
      ((b - a) ^ (-reciprocalExponent p) + (b - a) ^ (1 - reciprocalExponent p)) * ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg
    (add_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hab.le) _)
      (Real.rpow_nonneg (sub_nonneg.mpr hab.le) _)) (norm_nonneg _))).mpr
  intro i
  have hi := finite_interval_estimate 𝕜 a b hab p u (intervalRepresentative u)
    (intervalRepresentative_spec u) (endpoint a b i) (endpoint_mem hab i)
  have hbase : ‖baseLp u‖ ≤ ‖u‖ := PiLp.norm_apply_le u.val (zeroIndex 1 1)
  have hder : ‖derivativeLp u‖ ≤ ‖u‖ := PiLp.norm_apply_le u.val firstIndex
  calc
    ‖endpointValues u i‖ ≤ _ := hi
    _ ≤ (b - a) ^ (-reciprocalExponent p) * ‖u‖ +
        (b - a) ^ (1 - reciprocalExponent p) * ‖u‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg (sub_nonneg.mpr hab.le) _))
        (mul_le_mul_of_nonneg_left hder (Real.rpow_nonneg (sub_nonneg.mpr hab.le) _))
    _ = _ := (add_mul _ _ _).symm

/-- Bounded scalar-linear evaluation at both endpoints, including p=1. -/
def intervalTrace : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p →L[𝕜] (Fin 2 → 𝕜) :=
  (endpointValuesLM (𝕜 := 𝕜) (p := p) hab).mkContinuous
    ((b - a) ^ (-reciprocalExponent p) + (b - a) ^ (1 - reciprocalExponent p))
    (endpointValues_norm_le (𝕜 := 𝕜) (p := p) hab)

theorem intervalTrace_apply (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p)
    (f : ℝ → 𝕜) (hf : PrimitiveRepresentative u f) (i : Fin 2) :
    intervalTrace hab u i = f (endpoint a b i) := endpointValues_eq hab u f hf i

/-- The endpoint operator also agrees with any continuous representative,
without asking for its primitive formula a second time. -/
theorem intervalTrace_of_continuous (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p)
    (f : ℝ → 𝕜) (hf : ContinuousOn f (Icc a b))
    (hu : Represents (baseLp u) f) (i : Fin 2) :
    intervalTrace hab u i = f (endpoint a b i) :=
  intervalRepresentative_eq hab u f hf hu (endpoint_mem hab i)

/-- Put the two endpoint values into the actual boundary Lp space. Each
endpoint atom has finite measure, so this is a bounded linear map. -/
def endpointBoundaryMap : (Fin 2 → 𝕜) →L[𝕜]
    BoundaryLp 𝕜 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) p :=
  (ContinuousLinearMap.proj (0 : Fin 2)).smulRight
      (indicatorConstLp p (measurableSet_singleton (linePoint a))
        (ne_top_of_le_ne_top ENNReal.one_ne_top (surfaceMeasure_singleton_le_one _)) (1 : 𝕜)) +
    (ContinuousLinearMap.proj (1 : Fin 2)).smulRight
      (indicatorConstLp p (measurableSet_singleton (linePoint b))
        (ne_top_of_le_ne_top ENNReal.one_ne_top (surfaceMeasure_singleton_le_one _)) (1 : 𝕜))

theorem endpointBoundaryMap_coe (c : Fin 2 → 𝕜) (g : Domain 1 → 𝕜)
    (ha : g (linePoint a) = c 0) (hb : g (linePoint b) = c 1) :
    endpointBoundaryMap (a := a) (b := b) (p := p) c =ᵐ[
      surfaceMeasure (lineDomain ⟨Ioo a b, isOpen_Ioo⟩)] g := by
  let A : BoundaryLp 𝕜 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) p :=
    indicatorConstLp p (measurableSet_singleton (linePoint a))
      (ne_top_of_le_ne_top ENNReal.one_ne_top (surfaceMeasure_singleton_le_one _)) (1 : 𝕜)
  let B : BoundaryLp 𝕜 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) p :=
    indicatorConstLp p (measurableSet_singleton (linePoint b))
      (ne_top_of_le_ne_top ENNReal.one_ne_top (surfaceMeasure_singleton_le_one _)) (1 : 𝕜)
  have hAc : A =ᵐ[surfaceMeasure (lineDomain ⟨Ioo a b, isOpen_Ioo⟩)]
      ({linePoint a} : Set (Domain 1)).indicator (fun _ => (1 : 𝕜)) := indicatorConstLp_coeFn
  have hBc : B =ᵐ[surfaceMeasure (lineDomain ⟨Ioo a b, isOpen_Ioo⟩)]
      ({linePoint b} : Set (Domain 1)).indicator (fun _ => (1 : 𝕜)) := indicatorConstLp_coeFn
  change (c 0 • A + c 1 • B : BoundaryLp 𝕜 _ p) =ᵐ[_] g
  filter_upwards [Lp.coeFn_add (c 0 • A) (c 1 • B), Lp.coeFn_smul (c 0) A,
    Lp.coeFn_smul (c 1) B, hAc, hBc,
    surfaceMeasure_ae_frontier (lineDomain ⟨Ioo a b, isOpen_Ioo⟩)] with z hsum hA hB hAc hBc hz
  rw [hsum]
  change (c 0 • A : BoundaryLp 𝕜 _ p) z + (c 1 • B : BoundaryLp 𝕜 _ p) z = _
  rw [hA, hB]
  change c 0 • A z + c 1 • B z = _
  rw [hAc, hBc]
  rw [interval_frontier hab] at hz
  have hne : linePoint a ≠ linePoint b := fun h => hab.ne (congrFun h 0)
  rcases hz with (rfl | hz)
  · simp [hne, ha]
  · have he : z = linePoint b := hz
    subst z
    simp [hne.symm, hb]

/-- Interval trace with precisely the ambient Hausdorff boundary measure used
by the general theorem. -/
def intervalBoundaryTrace : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p →L[𝕜]
    BoundaryLp 𝕜 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) p :=
  (endpointBoundaryMap (a := a) (b := b) (p := p)).comp (intervalTrace hab)

theorem intervalBoundaryTrace_coe (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p)
    (f : ℝ → 𝕜) (hf : ContinuousOn f (Icc a b)) (hu : Represents (baseLp u) f) :
    intervalBoundaryTrace hab u =ᵐ[surfaceMeasure (lineDomain ⟨Ioo a b, isOpen_Ioo⟩)]
      (fun z => f (z 0)) := by
  apply endpointBoundaryMap_coe hab
  · exact (intervalTrace_of_continuous hab u f hf hu (0 : Fin 2)).symm
  · exact (intervalTrace_of_continuous hab u f hf hu (1 : Fin 2)).symm

theorem intervalBoundaryTrace_isTrace :
    IsTrace (intervalBoundaryTrace (𝕜 := 𝕜) (p := p) hab) := by
  intro u f hf hu
  apply (intervalBoundaryTrace_coe hab u (fun t => f (linePoint t))
    (hf.continuous.comp (continuous_pi (fun _ => continuous_id))).continuousOn ?_).trans
  · filter_upwards [] with z
    rw [linePoint_coordinate]
  · filter_upwards [hu] with z hz
    simpa only [linePoint_coordinate] using hz

/-- Integrating the zero-extended derivative gives the zero extension of
the continuous representative exactly when both endpoint values vanish. -/
theorem interval_zeroExtension_primitive
    (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p)
    (f : ℝ → 𝕜) (hf : PrimitiveRepresentative u f) (ha : f a = 0) (hb : f b = 0) :
    ∀ x : ℝ, (∫ t in a..x, extendedLineFunction (derivativeLp u) t) =
      (Ioo a b).indicator f x := by
  let g := extendedLineFunction (derivativeLp u)
  have hi (x : ℝ) (hx : x ∈ Icc a b) : (∫ t in a..x, g t) = f x := by
    have hxc : x ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
    have hac : a ∈ closure (Ioo a b) := by rw [closure_Ioo hab.ne]; exact ⟨le_rfl, hab.le⟩
    have he := (hf.2.2.2 x hxc a hac).2
    rw [ha, sub_zero] at he
    rw [he]
    exact intervalIntegral.integral_congr_ae_restrict
      (extendedLineFunction_ae_on_segment ordConnected_Ioo (derivativeLp u) hxc hac)
  intro x
  by_cases hax : a < x
  · by_cases hxb : x < b
    · rw [indicator_of_mem (show x ∈ Ioo a b from ⟨hax, hxb⟩)]
      exact hi x ⟨hax.le, hxb.le⟩
    · rw [indicator_of_notMem (show x ∉ Ioo a b from fun h => hxb h.2)]
      have hbx := le_of_not_gt hxb
      have hright : (∫ t in b..x, g t) = 0 := by
        calc
          _ = ∫ t in b..x, (0 : 𝕜) := by
            apply intervalIntegral.integral_congr
            intro t ht
            rw [uIcc_of_le hbx] at ht
            exact indicator_of_notMem (show t ∉ Ioo a b from fun h => (ht.1.trans_lt h.2).false) _
          _ = 0 := intervalIntegral.integral_zero
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (extendedLineFunction_intervalIntegrable (derivativeLp u) a b)
        (extendedLineFunction_intervalIntegrable (derivativeLp u) b x), hi b ⟨hab.le, le_rfl⟩,
        hb, hright, add_zero]
  · rw [indicator_of_notMem (show x ∉ Ioo a b from fun h => hax h.1)]
    calc
      _ = ∫ t in a..x, (0 : 𝕜) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_ge (le_of_not_gt hax)] at ht
        exact indicator_of_notMem (show t ∉ Ioo a b from fun h => (h.1.trans_le ht.2).false) _
      _ = 0 := intervalIntegral.integral_zero

/-- Zero endpoint values suffice for global weak differentiability of the
zero extension; its weak derivative is the zero-extended interval derivative. -/
theorem interval_zeroExtension_of_endpoints
    (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p)
    (f : ℝ → 𝕜) (hf : PrimitiveRepresentative u f) (ha : f a = 0) (hb : f b = 0) :
    HasSobolevZeroExtension u := by
  let v : DomainLp 𝕜 (lineDomain ⊤) p := C1Extension.zeroLp ⊤ (baseLp u)
  let g : DomainLp 𝕜 (lineDomain ⊤) p := C1Extension.zeroLp ⊤ (derivativeLp u)
  have hv : v =ᵐ[volume]
      (lineDomain ⟨Ioo a b, isOpen_Ioo⟩ : Set (Domain 1)).indicator (baseLp u) := by
    have he := C1Extension.zeroLp_coe (Λ := (⊤ : Opens (Domain 1))) (baseLp u)
    change (C1Extension.zeroLp (⊤ : Opens (Domain 1)) (baseLp u)) =ᵐ[volume] _
    simpa only [Opens.coe_top, Measure.restrict_univ] using he
  have hg : g =ᵐ[volume]
      (fun z : Domain 1 => extendedLineFunction (derivativeLp u) (z 0)) := by
    have he := C1Extension.zeroLp_coe (Λ := (⊤ : Opens (Domain 1))) (derivativeLp u)
    change (C1Extension.zeroLp (⊤ : Opens (Domain 1)) (derivativeLp u)) =ᵐ[volume] _
    have he' : (C1Extension.zeroLp (⊤ : Opens (Domain 1)) (derivativeLp u)) =ᵐ[volume]
        (lineDomain ⟨Ioo a b, isOpen_Ioo⟩ : Set (Domain 1)).indicator (derivativeLp u) :=
      by simpa only [Opens.coe_top, Measure.restrict_univ] using he
    exact he'.mono (fun z hz => by
      rw [hz]
      change (lineDomain ⟨Ioo a b, isOpen_Ioo⟩ : Set (Domain 1)).indicator (derivativeLp u) z =
        (Ioo a b).indicator (lineFunction (derivativeLp u)) (z 0)
      by_cases hzi : z ∈ lineDomain ⟨Ioo a b, isOpen_Ioo⟩
      · rw [indicator_of_mem hzi, indicator_of_mem (show z 0 ∈ Ioo a b from hzi)]
        simp only [lineFunction, linePoint_coordinate]
      · rw [indicator_of_notMem hzi, indicator_of_notMem (show z 0 ∉ Ioo a b from hzi)])
  have hvf : v =ᵐ[volume] (fun z : Domain 1 =>
      ∫ t in a..z 0, extendedLineFunction (derivativeLp u) t) := by
    have hid' : (lineDomain ⟨Ioo a b, isOpen_Ioo⟩ : Set (Domain 1)).indicator (baseLp u) =ᵐ[volume]
        (fun z : Domain 1 => (Ioo a b).indicator f (z 0)) := by
      filter_upwards [ae_imp_of_ae_restrict hf.2.1] with z hz
      by_cases hzi : z ∈ lineDomain ⟨Ioo a b, isOpen_Ioo⟩
      · rw [indicator_of_mem hzi, indicator_of_mem (show z 0 ∈ Ioo a b from hzi)]
        exact hz hzi
      · rw [indicator_of_notMem hzi, indicator_of_notMem (show z 0 ∉ Ioo a b from hzi)]
    exact (hv.trans hid').trans (Filter.Eventually.of_forall (fun z =>
      (interval_zeroExtension_primitive hab u f hf ha hb (z 0)).symm))
  have hweak : lpDistribution g = -(lpDistribution v).comp (testPartialCLM [0]) := by
    apply ContinuousLinearMap.ext
    intro φ
    simp only [lpDistribution_apply, neg_apply, ContinuousLinearMap.comp_apply]
    change (∫ z : Domain 1 in univ, φ z * g z) =
      -(∫ z : Domain 1 in univ, testPartialCLM [0] φ z * v z)
    rw [Measure.restrict_univ]
    rw [integral_congr_ae (hg.mono (fun z hz => congrArg (φ z * ·) hz)),
      integral_congr_ae (hvf.mono (fun z hz => congrArg (testPartialCLM [0] φ z * ·) hz))]
    let e := (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
    have hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t => φ (linePoint t)) :=
      φ.contDiff.comp e.contDiff
    have hcψ : HasCompactSupport (fun t => φ (linePoint t)) :=
      φ.hasCompactSupport.comp_homeomorph e.toHomeomorph
    have he := integral_test_mul_primitive
      (extendedLineFunction_locallyIntegrable (derivativeLp u)) a hψ hcψ
    simp_rw [test_line_deriv] at he
    have hmp : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
        (volume : Measure ℝ) (volume : Measure (Domain 1)) :=
      MeasurePreserving.symm (MeasurableEquiv.funUnique (Fin 1) ℝ)
        (volume_preserving_funUnique (Fin 1) ℝ)
    rw [← hmp.integral_comp' (fun z : Domain 1 => φ z * extendedLineFunction (derivativeLp u) (z 0)),
      ← hmp.integral_comp' (fun z : Domain 1 => testPartialCLM [0] φ z *
        ∫ t in a..z 0, extendedLineFunction (derivativeLp u) t)]
    exact he
  refine ⟨ofWeakDerivative v g hweak, ?_⟩
  change v =ᵐ[volume] _
  exact hv

/-- Global one-dimensional Sobolev representatives are continuous across
the boundary. A zero extension therefore forces both endpoint values to zero. -/
theorem interval_endpoints_zero_of_zeroExtension
    (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p) (hu : HasSobolevZeroExtension u)
    (f : ℝ → 𝕜) (hf : PrimitiveRepresentative u f) : f a = 0 ∧ f b = 0 := by
  obtain ⟨v, hv⟩ := hu
  obtain ⟨F, hF⟩ := representative_existence 𝕜 ⊤ ordConnected_univ p v
  have hFc : Continuous F := by
    simpa using hF.1
  have hFa : (fun z : Domain 1 => F (z 0)) =ᵐ[volume]
      (lineDomain ⟨Ioo a b, isOpen_Ioo⟩ : Set (Domain 1)).indicator (baseLp u) := by
    have hrep : v.val (zeroIndex 1 1) =ᵐ[volume] (fun z => F (z 0)) := by
      have hr := hF.2.1
      change v.val (zeroIndex 1 1) =ᵐ[volume.restrict univ] (fun z => F (z 0)) at hr
      simpa only [Measure.restrict_univ] using hr
    exact hrep.symm.trans hv
  have hFu : Represents (baseLp u) F := by
    filter_upwards [ae_restrict_of_ae hFa,
      ae_restrict_mem (lineDomain ⟨Ioo a b, isOpen_Ioo⟩).isOpen.measurableSet] with z hz hzi
    rw [indicator_of_mem hzi] at hz
    exact hz.symm
  have he : EqOn F f (Icc a b) := by
    have he := representative_uniqueness 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p
      (baseLp u) F f hFc.continuousOn hf.1 hFu hf.2.1
    change EqOn F f (closure (Ioo a b)) at he
    rwa [closure_Ioo hab.ne] at he
  have hreal : ∀ᵐ t : ℝ ∂volume,
      F t = (Ioo a b).indicator (lineFunction (baseLp u)) t := by
    have hmp : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
        (volume : Measure ℝ) (volume : Measure (Domain 1)) :=
      MeasurePreserving.symm (MeasurableEquiv.funUnique (Fin 1) ℝ)
        (volume_preserving_funUnique (Fin 1) ℝ)
    exact hmp.quasiMeasurePreserving.ae hFa
  have hleft : EqOn F (fun _ => 0) (Iio a) := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_Iio
      hFc.continuousOn continuous_const.continuousOn
    filter_upwards [ae_restrict_of_ae hreal, ae_restrict_mem measurableSet_Iio] with t ht hta
    rw [ht, indicator_of_notMem (show t ∉ Ioo a b from fun h => (h.1.trans hta).false)]
  have hright : EqOn F (fun _ => 0) (Ioi b) := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_Ioi
      hFc.continuousOn continuous_const.continuousOn
    filter_upwards [ae_restrict_of_ae hreal, ae_restrict_mem measurableSet_Ioi] with t ht hbt
    rw [ht, indicator_of_notMem (show t ∉ Ioo a b from fun h => (hbt.trans h.2).false)]
  constructor
  · rw [← he ⟨le_rfl, hab.le⟩]
    exact hleft.closure hFc continuous_const (by simp)
  · rw [← he ⟨hab.le, le_rfl⟩]
    exact hright.closure hFc continuous_const (by simp)

/-- Both endpoint evaluations vanish on the test-function closure. -/
theorem intervalTrace_zero_of_zeroSpace (hp : p ≠ ∞)
    (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p)
    (hu : u ∈ ZeroSpaceValue 𝕜 1 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) 1 p hp) :
    intervalTrace hab u = 0 := by
  have hsub : ZeroSpaceValue 𝕜 1 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) 1 p hp ≤
      (intervalTrace (𝕜 := 𝕜) (p := p) hab).ker := by
    apply (smoothSubmodule 𝕜 1 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) 1 p).topologicalClosure_minimal _
      (intervalTrace hab).isClosed_ker
    rintro v ⟨φ, hφ⟩
    change intervalTrace hab v = 0
    funext i
    have he := intervalTrace_of_continuous hab v (fun t => φ (linePoint t))
      (φ.continuous.comp (continuous_pi (fun _ => continuous_id))).continuousOn
      (by
        filter_upwards [hφ] with z hz
        simpa only [linePoint_coordinate] using hz) i
    rw [he]
    apply φ.zero_on_compl
    change ¬(a < endpoint a b i ∧ endpoint a b i < b)
    by_cases hi : i = 0 <;> simp [endpoint, hi]
  exact hsub hu

end Interval

/-- Existence and uniqueness of the endpoint trace on any nondegenerate
bounded interval, for both scalar fields and every 1 ≤ p ≤ ∞. -/
theorem interval_endpoint_operator :
    Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel.IntervalEndpointOperator := by
  intro 𝕜 _ a b hab p _
  refine ⟨intervalTrace hab, ?_, ?_⟩
  · exact fun u f hf i => intervalTrace_apply hab u f hf i
  · intro S hS
    ext u i
    have hf := intervalRepresentative_spec u
    exact (hS u _ hf i).trans (intervalTrace_apply hab u _ hf i).symm

/-- The general boundary trace agrees with both endpoint values of every
continuous primitive representative, using the same boundary measure. -/
theorem interval_identification :
    Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel.IntervalIdentification := by
  intro 𝕜 _ a b hab p _ hp T hT u f hf
  have he : T = intervalBoundaryTrace hab :=
    trace_uniqueness 𝕜 1 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) (interval_isC1 hab)
      (by rw [interval_frontier hab]; exact isCompact_singleton.insert _)
      p hp T (intervalBoundaryTrace hab) hT (intervalBoundaryTrace_isTrace hab)
  rw [he]
  exact intervalBoundaryTrace_coe hab u f (by
    have hc := hf.1
    change ContinuousOn f (closure (Ioo a b)) at hc
    rwa [closure_Ioo hab.ne] at hc) hf.2.1

/-- On intervals trace vanishing is equivalent to vanishing of both
continuous endpoint values, with no pointwise choices of Lp data. -/
theorem interval_trace_zero_iff {𝕜 : Type} [RCLike 𝕜] {a b : ℝ} (hab : a < b)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p →L[𝕜]
      BoundaryLp 𝕜 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) p) (hT : IsTrace T)
    (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p) (f : ℝ → 𝕜) (hf : PrimitiveRepresentative u f) :
    T u = 0 ↔ f a = 0 ∧ f b = 0 := by
  have he := interval_identification 𝕜 a b hab p hp T hT u f hf
  constructor
  · intro hz
    have he0 : (fun z : Domain 1 => f (z 0)) =ᵐ[
        surfaceMeasure (lineDomain ⟨Ioo a b, isOpen_Ioo⟩)] (fun _ => 0) := by
      exact he.symm.trans (hz ▸ Lp.coeFn_zero 𝕜 p _)
    have hmass (x : Domain 1) (hx : x ∈ frontier
        (lineDomain ⟨Ioo a b, isOpen_Ioo⟩ : Set (Domain 1))) :
        surfaceMeasure (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) {x} ≠ 0 := by
      rw [surfaceMeasure_singleton_of_frontier hx]
      exact one_ne_zero
    constructor
    · exact eq_at_of_ae_eq_of_singleton_ne_zero he0
        (hmass (linePoint a) (by rw [interval_frontier hab]; exact mem_insert _ _))
    · exact eq_at_of_ae_eq_of_singleton_ne_zero he0
        (hmass (linePoint b) (by rw [interval_frontier hab]; exact mem_insert_of_mem _ rfl))
  · rintro ⟨ha, hb⟩
    apply Lp.ext
    filter_upwards [he, surfaceMeasure_ae_frontier (lineDomain ⟨Ioo a b, isOpen_Ioo⟩),
      Lp.coeFn_zero 𝕜 p (surfaceMeasure (lineDomain ⟨Ioo a b, isOpen_Ioo⟩))] with z hz hzi hzero
    rw [hz, hzero]
    rw [interval_frontier hab] at hzi
    rcases hzi with (rfl | hzi)
    · exact ha
    · have hez : z = linePoint b := hzi
      subst z
      exact hb

/-- The full zero-extension equivalence on every nondegenerate bounded interval. -/
theorem interval_zero_extension_criterion :
    Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel.IntervalZeroExtensionCriterion := by
  intro 𝕜 _ a b hab p _ hp T hT u
  obtain ⟨f, hf⟩ := representative_existence 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ ordConnected_Ioo p u
  rw [interval_trace_zero_iff hab hp T hT u f hf]
  exact ⟨fun h => interval_zeroExtension_of_endpoints hab u f hf h.1 h.2,
    fun h => interval_endpoints_zero_of_zeroExtension hab u h f hf⟩

/-- Existence in the actual Hausdorff boundary Lp space on an interval. -/
theorem interval_boundary_operator :
    Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel.IntervalBoundaryOperator := by
  intro 𝕜 _ a b hab p _ hp
  refine ⟨intervalBoundaryTrace hab, intervalBoundaryTrace_isTrace hab, ?_⟩
  intro T hT
  exact trace_uniqueness 𝕜 1 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) (interval_isC1 hab)
    (by rw [interval_frontier hab]; exact isCompact_singleton.insert _)
    p hp T (intervalBoundaryTrace hab) hT (intervalBoundaryTrace_isTrace hab)

/-- In particular the continuous representative of a W₀ interval element
vanishes at the left and right endpoints. -/
theorem interval_zeroSpace_endpoints :
    Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel.IntervalZeroSpaceEndpoints := by
  intro 𝕜 _ a b hab p _ hp u hu f hf
  have hz := intervalTrace_zero_of_zeroSpace hab hp u hu
  constructor
  · have he := intervalTrace_apply hab u f hf (0 : Fin 2)
    simpa [hz, endpoint] using he.symm
  · have he := intervalTrace_apply hab u f hf (1 : Fin 2)
    simpa [hz, endpoint] using he.symm


section ZeroSpaceOperator
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d m : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)

/-- The genuine zero-extension operator on the original compact-test closure,
with its sum norm and every weak derivative. -/
def zeroSpaceExtension : ZeroSpaceValue 𝕜 d Ω m p hp →ₗᵢ[𝕜]
    SpaceValue 𝕜 d ⊤ m p where
  toFun u := ⟨zeroExtensionTuple u.val, zeroExtensionTuple_mem hp u.val u.property⟩
  map_add' u v := by
    apply Subtype.ext
    apply PiLp.ext
    intro α
    exact (C1Extension.zeroLpLM (𝕜 := 𝕜) (Ω := Ω) (p := p) ⊤).map_add _ _
  map_smul' c u := by
    apply Subtype.ext
    apply PiLp.ext
    intro α
    exact (C1Extension.zeroLpLM (𝕜 := 𝕜) (Ω := Ω) (p := p) ⊤).map_smul c _
  norm_map' u := by
    change ‖zeroExtensionTuple u.val‖ = ‖u.val.val‖
    rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
    exact Finset.sum_congr rfl (fun α _ => C1Extension.zeroLp_norm le_top (u.val.val α))

theorem zeroSpaceExtension_coe (u : ZeroSpaceValue 𝕜 d Ω m p hp)
    (α : DerivativeIndex d m) :
    (zeroSpaceExtension hp u).val α =ᵐ[volume]
      (Ω : Set (Domain d)).indicator (u.val.val α) := by
  change C1Extension.zeroLp ⊤ (u.val.val α) =ᵐ[volume] _
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    (C1Extension.zeroLp_coe (Λ := ⊤) (u.val.val α))

theorem restrict_zeroSpaceExtension (u : ZeroSpaceValue 𝕜 d Ω m p hp) :
    C1Extension.restrictSobolev (le_top : Ω ≤ ⊤) (zeroSpaceExtension hp u) = u.val := by
  apply sobolev_underlying_injective 𝕜 d Ω m p
  apply Lp.ext
  filter_upwards [C1Extension.restrictSobolev_coe le_top (zeroSpaceExtension hp u)
      (zeroIndex d m), ae_restrict_of_ae (zeroSpaceExtension_coe hp u (zeroIndex d m)),
      ae_restrict_mem Ω.isOpen.measurableSet] with x hx hz hxΩ
  rw [hx, hz, indicator_of_mem hxΩ]

theorem zeroSpaceExtension_range_closed :
    IsClosed (Set.range (zeroSpaceExtension (𝕜 := 𝕜) (Ω := Ω) (m := m) hp)) := by
  let : CompleteSpace (SpaceValue 𝕜 d Ω m p) :=
    (Smoothing.derivativeGraph_isClosed (𝕜 := 𝕜) (Ω := Ω) (p := p) (m := m)).isComplete.completeSpace_coe
  let : CompleteSpace (ZeroSpaceValue 𝕜 d Ω m p hp) :=
    (smoothSubmodule 𝕜 d Ω m p).isClosed_topologicalClosure.isComplete.completeSpace_coe
  exact (zeroSpaceExtension (𝕜 := 𝕜) (Ω := Ω) (m := m) hp).isometry.isClosedEmbedding.isClosed_range

end ZeroSpaceOperator

section BoundaryGeometry
open ExpandedFA.Distributions

lemma chart_boundary_iff {d : ℕ} (Ω : Opens (Domain d))
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    (x : Domain d) (hx : x ∈ Φ.source) :
    x ∈ frontier (Ω : Set (Domain d)) ↔ Φ x i = 0 := by
  have himage : Φ.IsImage (Ω : Set (Domain d)) {y | 0 < y i} := fun y hy => (hside y hy).symm
  have hfront : frontier {y : Domain d | 0 < y i} = {y | y i = 0} := by
    change frontier ((fun y : Domain d => y i) ⁻¹' Ioi 0) = _
    rw [← (isOpenMap_eval i).preimage_frontier_eq_frontier_preimage (continuous_apply i),
      frontier_Ioi]
    rfl
  simpa only [hfront, mem_ofPred_eq] using (himage.frontier hx).symm

lemma chart_boundary_image {d : ℕ} (Ω : Opens (Domain d))
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i) :
    Φ '' (Φ.source ∩ frontier (Ω : Set (Domain d))) =
      Φ.target ∩ {y | y i = 0} := by
  have himage : Φ.IsImage (Ω : Set (Domain d)) {y | 0 < y i} := fun y hy => (hside y hy).symm
  have hfront : frontier {y : Domain d | 0 < y i} = {y | y i = 0} := by
    change frontier ((fun y : Domain d => y i) ⁻¹' Ioi 0) = _
    rw [← (isOpenMap_eval i).preimage_frontier_eq_frontier_preimage (continuous_apply i),
      frontier_Ioi]
    rfl
  simpa only [hfront] using himage.frontier.image_eq

lemma volume_chart_frontier_null {d : ℕ} (Ω : Opens (Domain d))
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    (C : ℝ) (hC : ∀ y ∈ Φ.target, ‖fderiv ℝ Φ.symm y‖ ≤ C) :
    volume (Φ.source ∩ frontier (Ω : Set (Domain d))) = 0 := by
  let H : Set (Domain d) := {y | y i = 0}
  have hHm : MeasurableSet H := isClosed_eq (continuous_apply i) continuous_const |>.measurableSet
  have hH : volume H = 0 := by
    exact Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure ℝ)) i 0
  obtain ⟨J, hJ, hbound⟩ := C1Extension.Transport.exists_det_bound_of_norm_bound
    (E := Domain d) C
  have hmap := C1Extension.Transport.partialHomeomorph_map_measure_le_of_contDiff
    volume Φ hInv J (fun y hy => hbound _ (hC y hy))
  have hHrestrict : (volume.restrict Φ.target) H = 0 := by
    rw [Measure.restrict_apply hHm]
    exact measure_mono_null inter_subset_left hH
  have hm : (volume.restrict Φ.source).map Φ H = 0 :=
    Measure.absolutelyContinuous_of_le_smul hmap hHrestrict
  have hm' : (volume.restrict Φ.source) (Φ ⁻¹' H) = 0 := by
    rwa [Measure.map_apply_of_aemeasurable
      (Φ.continuousOn.aemeasurable Φ.open_source.measurableSet) hHm] at hm
  have hset : Φ.source ∩ frontier (Ω : Set (Domain d)) = Φ ⁻¹' H ∩ Φ.source := by
    ext x
    exact ⟨fun hx => ⟨(chart_boundary_iff Ω Φ i hside x hx.1).mp hx.2, hx.1⟩,
      fun hx => ⟨hx.2, (chart_boundary_iff Ω Φ i hside x hx.2).mpr hx.1⟩⟩
  rw [hset]
  rw [Measure.restrict_apply₀
    ((Φ.continuousOn.aemeasurable Φ.open_source.measurableSet).nullMeasurableSet_preimage hHm)] at hm'
  exact hm'

lemma volume_frontier_null {d : ℕ} (Ω : Opens (Domain d))
    (hΩ : C1Extension.IsC1Domain Ω)
    (hcompact : IsCompact (frontier (Ω : Set (Domain d)))) :
    volume (frontier (Ω : Set (Domain d))) = 0 := by
  obtain ⟨n, i, Φ, C, hC0, hcharts, hcover⟩ :=
    C1Extension.finite_bounded_boundary_charts d Ω hΩ hcompact
  apply measure_mono_null (t := ⋃ j, (Φ j).source ∩ frontier (Ω : Set (Domain d)))
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨j, hj, hx⟩
  · apply measure_iUnion_null
    intro j
    exact volume_chart_frontier_null Ω (Φ j) (i j) (hcharts j).2.1
      (hcharts j).2.2.2.2.1 C (hcharts j).2.2.2.2.2.2

lemma hausdorff_chart_boundary_lt_top {n : ℕ} (Ω : Opens (Domain (n + 1)))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    (K : ℝ≥0) (hK : LipschitzOnWith K Φ.symm Φ.target)
    (hbounded : Bornology.IsBounded Φ.target) :
    Measure.hausdorffMeasure (n : ℝ) (Φ.source ∩ frontier (Ω : Set (Domain (n + 1)))) < ∞ := by
  let ins : Domain n → Domain (n + 1) := fun z => i.insertNth (α := fun _ => ℝ) 0 z
  have hins : Isometry ins := by
    rw [isometry_iff_dist_eq]
    intro x y
    simp [ins]
  let s : Set (Domain n) := ins ⁻¹' Φ.target
  have hsbounded : Bornology.IsBounded s := hins.antilipschitzWith.isBounded_preimage hbounded
  have hsfinite : Measure.hausdorffMeasure (n : ℝ) s < ∞ := by
    have hH : (Measure.hausdorffMeasure (n : ℝ) : Measure (Domain n)) = volume := by
      simpa using (hausdorffMeasure_pi_real (ι := Fin n))
    rw [hH]
    exact hsbounded.measure_lt_top
  have hcomp : LipschitzOnWith (K * 1) (Φ.symm ∘ ins) s :=
    hK.comp hins.lipschitzWith.lipschitzOnWith (fun _ hx => hx)
  have hset : (Φ.symm ∘ ins) '' s = Φ.source ∩ frontier (Ω : Set (Domain (n + 1))) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hsrc : Φ.symm (ins z) ∈ Φ.source := Φ.map_target hz
      refine ⟨hsrc, (chart_boundary_iff Ω Φ i hside _ hsrc).mpr ?_⟩
      rw [Φ.right_inv hz]
      simp [ins]
    · rintro ⟨hxsrc, hxfront⟩
      let z : Domain n := i.removeNth (Φ x)
      have hzero : Φ x i = 0 := (chart_boundary_iff Ω Φ i hside _ hxsrc).mp hxfront
      have hz : ins z = Φ x := by
        change i.insertNth 0 (i.removeNth (Φ x)) = Φ x
        rw [← hzero, Fin.insertNth_self_removeNth]
      refine ⟨z, ?_, ?_⟩
      · change ins z ∈ Φ.target
        rw [hz]
        exact Φ.map_source hxsrc
      · change Φ.symm (ins z) = x
        rw [hz, Φ.left_inv hxsrc]
  rw [← hset]
  exact lt_of_le_of_lt (hcomp.hausdorffMeasure_image_le (Nat.cast_nonneg n))
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (Nat.cast_nonneg n) ENNReal.coe_ne_top)
      hsfinite)

lemma local_lipschitz_boundary_chart {d : ℕ} (Ω : Opens (Domain d))
    (hΩ : C1Extension.IsC1Domain Ω) (x : Domain d) (hx : x ∈ frontier (Ω : Set (Domain d))) :
    ∃ (i : Fin d) (Ψ : OpenPartialHomeomorph (Domain d) (Domain d)) (K : ℝ≥0),
      x ∈ Ψ.source ∧ (∀ y ∈ Ψ.source, y ∈ Ω ↔ 0 < Ψ y i) ∧
      LipschitzOnWith K Ψ.symm Ψ.target ∧ Bornology.IsBounded Ψ.target := by
  obtain ⟨i, Φ, hxΦ, hzero, hΦ, hInv, hside⟩ := hΩ x hx
  obtain ⟨Ψ, r, hr, hxΨ, htarget, hs, ht, hsc, htc, hsb, htb,
      hfun, hinvfun, hΨ, hΨinv, C, hC, hCsrc, hCtgt⟩ :=
    C1Extension.shrink_c1_chart Φ x hxΦ hΦ hInv
  refine ⟨i, Ψ, ⟨C, hC⟩, hxΨ, ?_, ?_, htb⟩
  · intro y hy
    rw [hfun]
    exact hside y (hs (subset_closure hy))
  · apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun y hy => (hΨinv.differentiableOn_one y hy).differentiableAt
        (Ψ.open_target.mem_nhds hy))
      (fun y hy => ?_)
    · rw [htarget]
      exact convex_ball _ _
    · exact_mod_cast hCtgt y hy

lemma hausdorff_frontier_lt_top {n : ℕ} (Ω : Opens (Domain (n + 1)))
    (hΩ : C1Extension.IsC1Domain Ω)
    (hcompact : IsCompact (frontier (Ω : Set (Domain (n + 1))))) :
    Measure.hausdorffMeasure (n : ℝ) (frontier (Ω : Set (Domain (n + 1)))) < ∞ := by
  classical
  have hpoint (x : frontier (Ω : Set (Domain (n + 1)))) :
      ∃ (Ψ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))),
        x.val ∈ Ψ.source ∧
        Measure.hausdorffMeasure (n : ℝ) (Ψ.source ∩ frontier (Ω : Set (Domain (n + 1)))) < ∞ := by
    obtain ⟨i, Ψ, K, hx, hside, hK, hbounded⟩ := local_lipschitz_boundary_chart Ω hΩ x x.property
    exact ⟨Ψ, hx, hausdorff_chart_boundary_lt_top Ω Ψ i hside K hK hbounded⟩
  choose Ψ hx hfinite using hpoint
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover
    (fun x : frontier (Ω : Set (Domain (n + 1))) => (Ψ x).source)
    (fun x => (Ψ x).open_source)
    (fun x hx' => mem_iUnion.mpr ⟨⟨x, hx'⟩, hx ⟨x, hx'⟩⟩)
  have hcover : frontier (Ω : Set (Domain (n + 1))) ⊆
      ⋃ x ∈ s, (Ψ x).source ∩ frontier (Ω : Set (Domain (n + 1))) := by
    intro x hx'
    obtain ⟨z, hzx⟩ := mem_iUnion.mp (hs hx')
    obtain ⟨hzs, hxz⟩ := mem_iUnion.mp hzx
    exact mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hzs, hxz, hx'⟩⟩
  exact (measure_mono hcover).trans_lt
    (measure_biUnion_lt_top s.finite_toSet (fun x _ => hfinite x))

lemma surfaceMeasure_univ_lt_top {d : ℕ} (Ω : Opens (Domain d))
    (hΩ : C1Extension.IsC1Domain Ω)
    (hcompact : IsCompact (frontier (Ω : Set (Domain d)))) :
    surfaceMeasure Ω Set.univ < ∞ := by
  cases d with
  | zero =>
    have hf : frontier (Ω : Set (Domain 0)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨i, _⟩ := hΩ x hx
      exact Fin.elim0 i
    simp only [surfaceMeasure, hf, Measure.restrict_empty, smul_zero, Measure.coe_zero, Pi.zero_apply, ENNReal.zero_lt_top]
  | succ n =>
    have hH := hausdorff_frontier_lt_top Ω hΩ hcompact
    have hL := PiLp.lipschitzWith_toLp 2 (fun _ : Fin (n + 1) => ℝ)
    have hHe : Measure.hausdorffMeasure (n : ℝ)
        ((WithLp.toLp 2 : Domain (n + 1) → EuclideanSpace ℝ (Fin (n + 1))) ''
          frontier (Ω : Set (Domain (n + 1)))) < ∞ := by
      exact (hL.hausdorffMeasure_image_le (Nat.cast_nonneg n) _).trans_lt
        (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (Nat.cast_nonneg n) ENNReal.coe_ne_top) hH)
    simp only [surfaceMeasure, Nat.succ_sub_succ_eq_sub, Nat.sub_zero,
      Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    have hc := (MeasurableEquiv.toLp 2 (Domain (n + 1))).measurableEmbedding.comap_apply
      (Measure.hausdorffMeasure (n : ℝ)) (frontier (Ω : Set (Domain (n + 1))))
    change (Measure.comap (WithLp.toLp 2) (Measure.hausdorffMeasure (n : ℝ)))
      (frontier (Ω : Set (Domain (n + 1)))) = _ at hc
    rw [hc]
    exact ENNReal.mul_lt_top (measure_ball_lt_top (μ := volume)) hHe
end BoundaryGeometry

section EmptyAndZeroDimension
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- In dimension zero every Sobolev vector is already a compact smooth test;
this checks the nonempty singleton as well as the empty open set. -/
theorem zeroSpace_zero_dim {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Domain 0))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ZeroSpaceValue 𝕜 0 Ω m p hp = ⊤ := by
  apply top_unique
  intro u _
  apply (smoothSubmodule 𝕜 0 Ω m p).le_topologicalClosure
  by_cases hΩ : (Ω : Set (Domain 0)).Nonempty
  · obtain ⟨x, hx⟩ := hΩ
    let φ : Tests 𝕜 Ω := ⟨fun _ => u.val (zeroIndex 0 m) x, contDiff_const,
      (Set.toFinite _).isCompact,
      fun y _ => (Subsingleton.elim y x) ▸ hx⟩
    refine ⟨φ, ?_⟩
    exact Filter.Eventually.of_forall (fun y => congrArg (u.val (zeroIndex 0 m))
      (Subsingleton.elim y x))
  · refine ⟨0, ?_⟩
    have he : (Ω : Set (Domain 0)) = ∅ := Set.not_nonempty_iff_eq_empty.mp hΩ
    simp only [he, Measure.restrict_empty, Filter.EventuallyEq, ae_zero, Filter.eventually_bot]

/-- A zero-dimensional open set has empty boundary and zero surface measure. -/
theorem surfaceMeasure_zero_dim (Ω : Opens (Domain 0)) : surfaceMeasure Ω = 0 := by
  simp [surfaceMeasure]

/-- With zero boundary measure, smooth restriction has the unique zero
realization; the statement needs no boundary regularity. -/
theorem trace_exists_of_surfaceMeasure_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (hΩ : surfaceMeasure Ω = 0)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃! T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p, IsTrace T := by
  refine ⟨0, ?_, ?_⟩
  · intro u f hf hu
    simp only [hΩ, Filter.EventuallyEq, ae_zero, Filter.eventually_bot]
  · intro T hT
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    simp only [hΩ, Filter.EventuallyEq, ae_zero, Filter.eventually_bot]

theorem zero_dim_trace_exists (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Domain 0))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃! T : SpaceValue 𝕜 0 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p, IsTrace T :=
  trace_exists_of_surfaceMeasure_zero Ω (surfaceMeasure_zero_dim Ω) p

theorem zero_dim_trace_kernel (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Domain 0))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 0 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T) :
    T.ker = ZeroSpaceValue 𝕜 0 Ω 1 p hp := by
  rw [zeroSpace_zero_dim Ω 1 p hp]
  apply top_unique
  have hs := kernel_contains_zeroSpace 𝕜 0 Ω p hp T hT
  rwa [zeroSpace_zero_dim Ω 1 p hp] at hs

theorem zero_dim_zero_extension_criterion (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Domain 0)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 0 Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (u : SpaceValue 𝕜 0 Ω 1 p) : T u = 0 ↔ HasSobolevZeroExtension u := by
  have hu : u ∈ ZeroSpaceValue 𝕜 0 Ω 1 p hp := by
    rw [zeroSpace_zero_dim Ω 1 p hp]; trivial
  have hz : T u = 0 := kernel_contains_zeroSpace 𝕜 0 Ω p hp T hT hu
  have he := zero_extension_of_zeroSpace 𝕜 0 Ω 1 p hp u hu
  exact iff_of_true hz ⟨he.choose, he.choose_spec.1 (zeroIndex 0 1)⟩

/-- The empty domain carries no data at any derivative order. -/
theorem zeroSpace_empty {𝕜 : Type} [RCLike 𝕜] (d m : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ZeroSpaceValue 𝕜 d ⊥ m p hp = ⊤ := by
  apply top_unique
  intro u _
  apply (smoothSubmodule 𝕜 d ⊥ m p).le_topologicalClosure
  refine ⟨0, ?_⟩
  simp only [Opens.coe_bot, Measure.restrict_empty, Filter.EventuallyEq, ae_zero,
    Filter.eventually_bot]

theorem empty_trace_exists (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃! T : SpaceValue 𝕜 d ⊥ 1 p →L[𝕜] BoundaryLp 𝕜 ⊥ p, IsTrace T :=
  trace_exists_of_surfaceMeasure_zero ⊥ (by simp [surfaceMeasure]) p

theorem empty_trace_kernel (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 d ⊥ 1 p →L[𝕜] BoundaryLp 𝕜 ⊥ p) (hT : IsTrace T) :
    T.ker = ZeroSpaceValue 𝕜 d ⊥ 1 p hp := by
  rw [zeroSpace_empty d 1 p hp]
  apply top_unique
  have hs := kernel_contains_zeroSpace 𝕜 d ⊥ p hp T hT
  rwa [zeroSpace_empty d 1 p hp] at hs

theorem empty_zero_extension_criterion (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 d ⊥ 1 p →L[𝕜] BoundaryLp 𝕜 ⊥ p) (hT : IsTrace T)
    (u : SpaceValue 𝕜 d ⊥ 1 p) : T u = 0 ↔ HasSobolevZeroExtension u := by
  have hu : u ∈ ZeroSpaceValue 𝕜 d ⊥ 1 p hp := by
    rw [zeroSpace_empty d 1 p hp]; trivial
  have hz : T u = 0 := kernel_contains_zeroSpace 𝕜 d ⊥ p hp T hT hu
  have he := zero_extension_of_zeroSpace 𝕜 d ⊥ 1 p hp u hu
  exact iff_of_true hz ⟨he.choose, he.choose_spec.1 (zeroIndex d 1)⟩

end EmptyAndZeroDimension


section ZeroExtensionDerivatives
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- When the boundary is Lebesgue null, locality identifies every derivative
of an existing global zero extension, including its original Lp class. -/
theorem zeroExtension_derivatives (hnull : volume (frontier (Ω : Set (Domain d))) = 0)
    (u : SpaceValue 𝕜 d Ω 1 p) (v : SpaceValue 𝕜 d ⊤ 1 p)
    (hv : v.val (zeroIndex d 1) =ᵐ[volume]
      (Ω : Set (Domain d)).indicator (u.val (zeroIndex d 1))) :
    ∀ α, v.val α =ᵐ[volume] (Ω : Set (Domain d)).indicator (u.val α) := by
  have hr : C1Extension.restrictSobolev (le_top : Ω ≤ ⊤) v = u := by
    apply sobolev_underlying_injective 𝕜 d Ω 1 p
    apply Lp.ext
    filter_upwards [C1Extension.restrictSobolev_coe le_top v (zeroIndex d 1),
      ae_restrict_of_ae hv, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hvx hxΩ
    rw [hx, hvx, indicator_of_mem hxΩ]
  let U : Opens (Domain d) := ⟨(closure (Ω : Set (Domain d)))ᶜ, isClosed_closure.isOpen_compl⟩
  have hU : C1Extension.restrictSobolev (le_top : U ≤ ⊤) v = 0 := by
    apply sobolev_underlying_injective 𝕜 d U 1 p
    apply Lp.ext
    filter_upwards [C1Extension.restrictSobolev_coe le_top v (zeroIndex d 1),
      ae_restrict_of_ae hv, ae_restrict_mem U.isOpen.measurableSet,
      Lp.coeFn_zero 𝕜 p (volume.restrict (U : Set (Domain d)))] with x hx hvx hxU hz
    rw [hx, hvx]
    change (Ω : Set (Domain d)).indicator (u.val (zeroIndex d 1)) x =
      (0 : DomainLp 𝕜 U p) x
    rw [hz]
    exact indicator_of_notMem (fun hxΩ => hxU (subset_closure hxΩ)) _
  intro α
  have hi : ∀ᵐ x ∂volume, x ∈ Ω → v.val α x = u.val α x := by
    apply ae_imp_of_ae_restrict
    have he := C1Extension.restrictSobolev_coe (le_top : Ω ≤ ⊤) v α
    rw [hr] at he
    exact he.symm
  have ho : ∀ᵐ x ∂volume, x ∈ U → v.val α x = 0 := by
    apply ae_imp_of_ae_restrict
    have he := C1Extension.restrictSobolev_coe (le_top : U ≤ ⊤) v α
    rw [hU] at he
    have hz : (0 : SpaceValue 𝕜 d U 1 p).val α =ᵐ[
      volume.restrict (U : Set (Domain d))] (fun _ => 0) :=
      Lp.coeFn_zero 𝕜 p (volume.restrict (U : Set (Domain d)))
    exact he.symm.trans hz
  filter_upwards [hi, ho, (measure_eq_zero_iff_ae_notMem.mp hnull)] with x hix hox hxfront
  by_cases hxΩ : x ∈ Ω
  · rw [indicator_of_mem hxΩ]
    exact hix hxΩ
  · rw [indicator_of_notMem hxΩ]
    apply hox
    change x ∉ closure (Ω : Set (Domain d))
    intro hxcl
    apply hxfront
    rw [Ω.isOpen.frontier_eq]
    exact ⟨hxcl, hxΩ⟩

theorem zeroExtension_tuple_eq
    (hnull : volume (frontier (Ω : Set (Domain d))) = 0)
    (u : SpaceValue 𝕜 d Ω 1 p) (v : SpaceValue 𝕜 d ⊤ 1 p)
    (hv : v.val (zeroIndex d 1) =ᵐ[volume]
      (Ω : Set (Domain d)).indicator (u.val (zeroIndex d 1))) :
    v.val = zeroExtensionTuple u := by
  apply PiLp.ext
  intro α
  apply Lp.ext
  simp only [Opens.coe_top, Measure.restrict_univ]
  change v.val α =ᵐ[volume] C1Extension.zeroLp ⊤ (u.val α)
  exact (zeroExtension_derivatives hnull u v hv α).trans
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using
      (C1Extension.zeroLp_coe (Λ := ⊤) (u.val α)).symm)

/-- Such a zero extension preserves the source sum norm exactly. -/
theorem zeroExtension_norm
    (hnull : volume (frontier (Ω : Set (Domain d))) = 0)
    (u : SpaceValue 𝕜 d Ω 1 p) (v : SpaceValue 𝕜 d ⊤ 1 p)
    (hv : v.val (zeroIndex d 1) =ᵐ[volume]
      (Ω : Set (Domain d)).indicator (u.val (zeroIndex d 1))) :
    ‖v‖ = ‖u‖ := by
  change ‖v.val‖ = ‖u.val‖
  rw [zeroExtension_tuple_eq hnull u v hv, PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
  exact Finset.sum_congr rfl (fun α _ => C1Extension.zeroLp_norm le_top (u.val α))

/-- The canonical entrywise zero extension satisfies the global graph identities
exactly when some Sobolev zero extension exists, on null-boundary domains. -/
theorem hasZeroExtension_iff_zeroExtensionTuple_mem
    (hnull : volume (frontier (Ω : Set (Domain d))) = 0)
    (u : SpaceValue 𝕜 d Ω 1 p) :
    HasSobolevZeroExtension u ↔ zeroExtensionTuple u ∈ derivativeGraph 𝕜 ⊤ 1 p := by
  constructor
  · rintro ⟨v, hv⟩
    exact zeroExtension_tuple_eq hnull u v hv ▸ v.property
  · intro hu
    refine ⟨⟨zeroExtensionTuple u, hu⟩, ?_⟩
    change C1Extension.zeroLp ⊤ (u.val (zeroIndex d 1)) =ᵐ[volume] _
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (C1Extension.zeroLp_coe (Λ := ⊤) (u.val (zeroIndex d 1)))

theorem isClosed_hasSobolevZeroExtension
    (hnull : volume (frontier (Ω : Set (Domain d))) = 0) :
    IsClosed {u : SpaceValue 𝕜 d Ω 1 p | HasSobolevZeroExtension u} := by
  have he : {u : SpaceValue 𝕜 d Ω 1 p | HasSobolevZeroExtension u} =
      zeroExtensionTuple ⁻¹' {v : DerivativeTuple 𝕜 ⊤ 1 p | v ∈ derivativeGraph 𝕜 ⊤ 1 p} := by
    ext u
    exact hasZeroExtension_iff_zeroExtensionTuple_mem hnull u
  rw [he]
  exact Smoothing.derivativeGraph_isClosed.preimage continuous_zeroExtensionTuple

theorem isClosed_hasSobolevZeroExtension_of_isC1Domain
    (hΩ : C1Extension.IsC1Domain Ω)
    (hcompact : IsCompact (frontier (Ω : Set (Domain d)))) :
    IsClosed {u : SpaceValue 𝕜 d Ω 1 p | HasSobolevZeroExtension u} :=
  isClosed_hasSobolevZeroExtension (volume_frontier_null Ω hΩ hcompact)

end ZeroExtensionDerivatives


section CompactSupportClosure
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open C1Extension

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous Sobolev map with an interior compact multiplier formula
has range in the original closure of compact tests. -/
theorem compact_multiplier_range_mem_zeroSpace (hp : p ≠ ∞)
    (F : SpaceValue 𝕜 d ⊤ 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p)
    (η : Tests 𝕜 (⊤ : Opens (Domain d))) (hη : tsupport η ⊆ Ω)
    (hF : ∀ w, (F w).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      (fun x => η x * w.val (zeroIndex d 1) x))
    (v : SpaceValue 𝕜 d ⊤ 1 p) : F v ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp := by
  have hclosed : IsClosed {w : SpaceValue 𝕜 d ⊤ 1 p |
      F w ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp} :=
    (smoothSubmodule 𝕜 d Ω 1 p).isClosed_topologicalClosure.preimage F.continuous
  have hsmooth : Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.SmoothMembers
      𝕜 d ⊤ 1 p ⊆ {w | F w ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp} := by
    rintro w ⟨f, hf, hw⟩
    have hf' : ContDiff ℝ (⊤ : ℕ∞) f := contDiffOn_univ.mp hf
    let φ : Tests 𝕜 Ω := ⟨η * f, η.contDiff.mul hf', η.hasCompactSupport.mul_right,
      tsupport_mul_subset_left.trans hη⟩
    apply (smoothSubmodule 𝕜 d Ω 1 p).le_topologicalClosure
    refine ⟨φ, ?_⟩
    have hmeasure : volume.restrict (Ω : Set (Domain d)) ≤
        volume.restrict ((⊤ : Opens (Domain d)) : Set (Domain d)) := by
      simpa using (Measure.restrict_le_self (μ := (volume : Measure (Domain d)))
        (s := (Ω : Set (Domain d))))
    filter_upwards [hF w, hw.filter_mono (ae_mono hmeasure)] with x hFx hwx
    exact hFx.trans (congrArg (η x * ·) hwx)
  exact closure_minimal hsmooth hclosed (Smoothing.smooth_density 𝕜 d ⊤ 1 p hp v)

/-- A fixed compact interior multiplier sends global W¹,p into W₀¹,p. -/
theorem ambient_cutoff_restriction_mem_zeroSpace (hp : p ≠ ∞)
    (η : Tests 𝕜 (⊤ : Opens (Domain d))) (hη : tsupport η ⊆ Ω)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖η x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] η x‖ ≤ C)
    (v : SpaceValue 𝕜 d ⊤ 1 p) :
    restrictSobolev (le_top : Ω ≤ ⊤)
      (ambientMultiply η η.contDiff C hC0 hC hD v) ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp := by
  let F : SpaceValue 𝕜 d ⊤ 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p :=
    (restrictSobolev (le_top : Ω ≤ ⊤)).comp
      (ambientMultiply η η.contDiff C hC0 hC hD)
  apply compact_multiplier_range_mem_zeroSpace hp F η hη _ v
  intro w
  have hm := ambientMultiply_coe η η.contDiff C hC0 hC hD w
  have hr := restrictSobolev_coe (le_top : Ω ≤ ⊤)
    (ambientMultiply η η.contDiff C hC0 hC hD w) (zeroIndex d 1)
  exact hr.trans (hm.filter_mono (ae_mono (Measure.restrict_mono (le_top : Ω ≤ ⊤) le_rfl)))

/-- Compact interior support of the underlying global class suffices: no
support condition on derivatives or boundary regularity is required. -/
theorem restrict_mem_zeroSpace_of_compact_support (hp : p ≠ ∞)
    (v : SpaceValue 𝕜 d ⊤ 1 p) (K : Set (Domain d)) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω)
    (hv : ∀ᵐ x ∂volume, x ∉ K → v.val (zeroIndex d 1) x = 0) :
    restrictSobolev (le_top : Ω ≤ ⊤) v ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp := by
  obtain ⟨η, hη, hηone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜) K hK Ω hKΩ
  obtain ⟨C, hC0, hC, hD⟩ := ambient_test_bounds η
  have heq : ambientMultiply η η.contDiff C hC0 hC hD v = v := by
    apply sobolev_underlying_injective 𝕜 d ⊤ 1 p
    apply Lp.ext
    have hm := ambientMultiply_coe η η.contDiff C hC0 hC hD v
    simp only [Opens.coe_top, Measure.restrict_univ] at hm ⊢
    filter_upwards [hm, hv] with x hmx hvx
    rw [hmx]
    by_cases hx : x ∈ K
    · rw [hηone x hx, one_mul]
    · rw [hvx hx, mul_zero]
  simpa only [heq] using ambient_cutoff_restriction_mem_zeroSpace hp η hη C hC0 hC hD v

end CompactSupportClosure


section GlobalTranslations
open Filter
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open C1Extension HalfSpace

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Translation of global Lp data, with τₕf(x)=f(x-h). -/
def globalLpTranslation (h : Domain d) :
    DomainLp 𝕜 (⊤ : Opens (Domain d)) p →ₗᵢ[𝕜]
      DomainLp 𝕜 (⊤ : Opens (Domain d)) p := by
  exact Lp.compMeasurePreservingₗᵢ 𝕜 (E := 𝕜) (fun x : Domain d => x - h)
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using
      measurePreserving_sub_right volume h) (p := p)


theorem globalLpTranslation_coe (h : Domain d)
    (u : DomainLp 𝕜 (⊤ : Opens (Domain d)) p) :
    globalLpTranslation h u =ᵐ[volume] fun x => u (x - h) := by
  have he : MeasurePreserving (fun x : Domain d => x - h)
      (volume.restrict ((⊤ : Opens (Domain d)) : Set (Domain d)))
      (volume.restrict ((⊤ : Opens (Domain d)) : Set (Domain d))) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      measurePreserving_sub_right volume h
  have hc : globalLpTranslation h u =ᵐ[
      volume.restrict ((⊤ : Opens (Domain d)) : Set (Domain d))]
      (fun x => u (x - h)) := Lp.coeFn_compMeasurePreserving u he
  simpa only [Opens.coe_top, Measure.restrict_univ] using hc


theorem globalLpTranslation_continuous (hp : p ≠ ∞)
    (u : DomainLp 𝕜 (⊤ : Opens (Domain d)) p) :
    Continuous (fun h => globalLpTranslation h u) := by
  let g : Domain d → C(Domain d, Domain d) :=
    fun h => ⟨fun x => x - h, continuous_id.sub continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.sub continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun h => by
      change MeasurePreserving (fun x : Domain d => x - h)
        (volume.restrict ((⊤ : Opens (Domain d)) : Set (Domain d)))
        (volume.restrict ((⊤ : Opens (Domain d)) : Set (Domain d)))
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        measurePreserving_sub_right volume h) hp


/-- Translate all components of the weak derivative tuple together. -/
def globalTupleTranslation (h : Domain d)
    (u : DerivativeTuple 𝕜 (⊤ : Opens (Domain d)) 1 p) :
    DerivativeTuple 𝕜 (⊤ : Opens (Domain d)) 1 p :=
  WithLp.toLp 1 fun α => globalLpTranslation h (u α)

theorem globalTupleTranslation_continuous (h : Domain d) :
    Continuous (globalTupleTranslation (𝕜 := 𝕜) (p := p) h) := by
  apply (PiLp.continuous_toLp 1 _).comp
  apply continuous_pi
  intro α
  exact (globalLpTranslation h).continuous.comp (PiLp.continuous_apply 1 _ α)

theorem globalTupleTranslation_norm (h : Domain d)
    (u : DerivativeTuple 𝕜 (⊤ : Opens (Domain d)) 1 p) :
    ‖globalTupleTranslation h u‖ = ‖u‖ := by
  simp only [PiLp.norm_eq_of_L1, globalTupleTranslation]
  exact Finset.sum_congr rfl fun α _ => (globalLpTranslation h).norm_map (u α)

theorem globalTupleTranslation_mem (hp : p ≠ ∞) (h : Domain d)
    (u : SpaceValue 𝕜 d ⊤ 1 p) :
    globalTupleTranslation h u.val ∈ derivativeGraph 𝕜 ⊤ 1 p := by
  have hc : IsClosed {v : SpaceValue 𝕜 d ⊤ 1 p |
      globalTupleTranslation h v.val ∈ derivativeGraph 𝕜 ⊤ 1 p} :=
    Smoothing.derivativeGraph_isClosed.preimage
      ((globalTupleTranslation_continuous h).comp continuous_subtype_val)
  apply closure_minimal (s := Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity.SmoothMembers
    𝕜 d ⊤ 1 p) (t := {v : SpaceValue 𝕜 d ⊤ 1 p |
      globalTupleTranslation h v.val ∈ derivativeGraph 𝕜 ⊤ 1 p}) ?_ hc
    (Smoothing.smooth_density 𝕜 d ⊤ 1 p hp u)
  rintro v ⟨f, hf, hv⟩
  have hf' : ContDiff ℝ (⊤ : ℕ∞) f := contDiffOn_univ.mp hf
  have hcomp : ContDiffOn ℝ 1 (fun x => f (x - h))
      ((⊤ : Opens (Domain d)) : Set (Domain d)) :=
    (hf'.comp (contDiff_id.sub contDiff_const)).contDiffOn.of_le (by simp)
  apply C1Extension.Classical.c1_firstJet_mem (fun x => f (x - h)) hcomp
  · have hz := globalLpTranslation_coe h (v.val (zeroIndex d 1))
    have hv' : v.val (zeroIndex d 1) =ᵐ[volume] f := by simpa using hv
    have ht := (measurePreserving_sub_right volume h).quasiMeasurePreserving.ae_eq_comp hv'
    simpa only [Opens.coe_top, Measure.restrict_univ, globalTupleTranslation, Function.comp_def] using hz.trans ht
  · intro j
    have hz := globalLpTranslation_coe h (v.val (coordinateIndex j))
    have hg := C1Extension.Classical.c1_representative_derivative v f
      (hf.of_le (by simp)) hv j
    have hg' : v.val (coordinateIndex j) =ᵐ[volume]
        fun x => fderiv ℝ f x (coordinateVector j) := by simpa using hg
    have ht := (measurePreserving_sub_right volume h).quasiMeasurePreserving.ae_eq_comp hg'
    simpa only [Opens.coe_top, Measure.restrict_univ, globalTupleTranslation, Function.comp_def, fderiv_comp_sub] using hz.trans ht

/-- Translation on the original first-order Sobolev derivative graph. -/
def sobolevTranslation (hp : p ≠ ∞) (h : Domain d)
    (u : SpaceValue 𝕜 d ⊤ 1 p) : SpaceValue 𝕜 d ⊤ 1 p :=
  ⟨globalTupleTranslation h u.val, globalTupleTranslation_mem hp h u⟩

theorem sobolevTranslation_coe (hp : p ≠ ∞) (h : Domain d)
    (u : SpaceValue 𝕜 d ⊤ 1 p) (α : DerivativeIndex d 1) :
    (sobolevTranslation hp h u).val α =ᵐ[volume] fun x => u.val α (x - h) :=
  globalLpTranslation_coe h (u.val α)

theorem sobolevTranslation_norm (hp : p ≠ ∞) (h : Domain d)
    (u : SpaceValue 𝕜 d ⊤ 1 p) : ‖sobolevTranslation hp h u‖ = ‖u‖ :=
  globalTupleTranslation_norm h u.val

theorem sobolevTranslation_continuous (hp : p ≠ ∞) (u : SpaceValue 𝕜 d ⊤ 1 p) :
    Continuous (fun h => sobolevTranslation hp h u) := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 1 _).comp
  exact continuous_pi fun α => globalLpTranslation_continuous hp (u.val α)

theorem sobolevTranslation_zero (hp : p ≠ ∞) (u : SpaceValue 𝕜 d ⊤ 1 p) :
    sobolevTranslation hp 0 u = u := by
  apply Subtype.ext
  apply PiLp.ext
  intro α
  apply Lp.ext
  have hc := sobolevTranslation_coe hp 0 u α
  simpa only [Opens.coe_top, Measure.restrict_univ, sub_zero] using hc

theorem sobolevTranslation_norm_tendsto_zero (hp : p ≠ ∞)
    (u : SpaceValue 𝕜 d ⊤ 1 p) :
    Tendsto (fun h => ‖sobolevTranslation hp h u - u‖) (𝓝 0) (𝓝 0) := by
  simpa only [Pi.sub_apply, sobolevTranslation_zero hp u, sub_self, norm_zero] using
    (((sobolevTranslation_continuous hp u).sub (continuous_const (y := u))).norm.tendsto (0 : Domain d))

end GlobalTranslations


section SmoothBoundaryConstruction
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

lemma continuous_boundary_memLp {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (hΩ : C1Extension.IsC1Domain Ω)
    (hcompact : IsCompact (frontier (Ω : Set (Domain d))))
    (p : ℝ≥0∞) (f : Domain d → 𝕜) (hf : Continuous f) :
    MemLp f p (surfaceMeasure Ω) := by
  let : IsFiniteMeasure (surfaceMeasure Ω) := ⟨surfaceMeasure_univ_lt_top Ω hΩ hcompact⟩
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [Measure.ae_smul_measure (ae_restrict_mem isClosed_frontier.measurableSet)
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d - 1))) (1 / 2)))] with x hx
  exact hC x hx

lemma continuous_boundary_eq_of_ae {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (f g : Domain d → 𝕜) (hf : Continuous f) (hg : Continuous g)
    (hfg : f =ᵐ[volume.restrict (Ω : Set (Domain d))] g) :
    f =ᵐ[surfaceMeasure Ω] g := by
  have heq : EqOn f g (Ω : Set (Domain d)) :=
    Measure.eqOn_open_of_ae_eq hfg Ω.isOpen hf.continuousOn hg.continuousOn
  have heq' := heq.closure hf hg
  filter_upwards [Measure.ae_smul_measure (ae_restrict_mem isClosed_frontier.measurableSet)
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d - 1))) (1 / 2)))] with x hx
  exact heq' (frontier_subset_closure hx)

section SmoothRestriction
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
  (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]

def smoothBoundarySubmodule : Submodule 𝕜 (SpaceValue 𝕜 d Ω 1 p) where
  carrier := C1Extension.SmoothUpToBoundary (𝕜 := 𝕜) Ω p
  zero_mem' := by
    refine ⟨0, contDiff_const, ?_⟩
    exact Lp.coeFn_zero 𝕜 p (volume.restrict (Ω : Set (Domain d)))
  add_mem' := by
    rintro u v ⟨f, hf, hu⟩ ⟨g, hg, hv⟩
    refine ⟨f + g, hf.add hg, ?_⟩
    filter_upwards [Lp.coeFn_add (u.val (zeroIndex d 1)) (v.val (zeroIndex d 1)), hu, hv]
      with x hx hux hvx
    change ((u.val (zeroIndex d 1) + v.val (zeroIndex d 1)) : DomainLp 𝕜 Ω p) x = _
    rw [hx]
    exact congrArg₂ (· + ·) hux hvx
  smul_mem' := by
    rintro c u ⟨f, hf, hu⟩
    refine ⟨c • f, contDiff_const.smul hf, ?_⟩
    filter_upwards [Lp.coeFn_smul c (u.val (zeroIndex d 1)), hu] with x hx hux
    change (c • u.val (zeroIndex d 1) : DomainLp 𝕜 Ω p) x = _
    rw [hx]
    exact congrArg (c • ·) hux

variable (hΩ : C1Extension.IsC1Domain Ω)
  (hc : IsCompact (frontier (Ω : Set (Domain d))))

def smoothBoundaryRepresentative (u : smoothBoundarySubmodule (𝕜 := 𝕜) Ω p) : Domain d → 𝕜 :=
  Classical.choose u.property

lemma smoothBoundaryRepresentative_contDiff (u : smoothBoundarySubmodule (𝕜 := 𝕜) Ω p) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothBoundaryRepresentative Ω p u) :=
  (Classical.choose_spec u.property).1

lemma smoothBoundaryRepresentative_ae (u : smoothBoundarySubmodule (𝕜 := 𝕜) Ω p) :
    u.val.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      smoothBoundaryRepresentative Ω p u :=
  (Classical.choose_spec u.property).2

def smoothBoundaryRestriction (u : smoothBoundarySubmodule (𝕜 := 𝕜) Ω p) : BoundaryLp 𝕜 Ω p :=
  (continuous_boundary_memLp Ω hΩ hc p (smoothBoundaryRepresentative Ω p u)
    (smoothBoundaryRepresentative_contDiff Ω p u).continuous).toLp _

lemma smoothBoundaryRestriction_coe (u : smoothBoundarySubmodule (𝕜 := 𝕜) Ω p)
    (f : Domain d → 𝕜) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hu : u.val.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f) :
    smoothBoundaryRestriction Ω p hΩ hc u =ᵐ[surfaceMeasure Ω] f := by
  apply ((continuous_boundary_memLp Ω hΩ hc p (smoothBoundaryRepresentative Ω p u)
    (smoothBoundaryRepresentative_contDiff Ω p u).continuous).coeFn_toLp).trans
  exact continuous_boundary_eq_of_ae Ω _ _ (smoothBoundaryRepresentative_contDiff Ω p u).continuous
    hf.continuous ((smoothBoundaryRepresentative_ae Ω p u).symm.trans hu)


def smoothBoundaryRestrictionLM : smoothBoundarySubmodule (𝕜 := 𝕜) Ω p →ₗ[𝕜] BoundaryLp 𝕜 Ω p where
  toFun := smoothBoundaryRestriction Ω p hΩ hc
  map_add' u v := by
    let f := smoothBoundaryRepresentative Ω p u
    let g := smoothBoundaryRepresentative Ω p v
    have hf := smoothBoundaryRepresentative_contDiff Ω p u
    have hg := smoothBoundaryRepresentative_contDiff Ω p v
    have hu := smoothBoundaryRepresentative_ae Ω p u
    have hv := smoothBoundaryRepresentative_ae Ω p v
    have huv : (u + v).val.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f + g := by
      filter_upwards [Lp.coeFn_add (u.val.val (zeroIndex d 1)) (v.val.val (zeroIndex d 1)),
        hu, hv] with x hx hux hvx
      change ((u.val.val (zeroIndex d 1) + v.val.val (zeroIndex d 1)) : DomainLp 𝕜 Ω p) x = _
      rw [hx]
      exact congrArg₂ (· + ·) hux hvx
    apply Lp.ext
    filter_upwards [smoothBoundaryRestriction_coe Ω p hΩ hc (u + v) (f + g) (hf.add hg) huv,
      Lp.coeFn_add (smoothBoundaryRestriction Ω p hΩ hc u) (smoothBoundaryRestriction Ω p hΩ hc v),
      smoothBoundaryRestriction_coe Ω p hΩ hc u f hf hu,
      smoothBoundaryRestriction_coe Ω p hΩ hc v g hg hv] with x hx hadd hux hvx
    rw [hx, hadd]
    change f x + g x = _ + _
    rw [hux, hvx]
  map_smul' c u := by
    let f := smoothBoundaryRepresentative Ω p u
    have hf := smoothBoundaryRepresentative_contDiff Ω p u
    have hu := smoothBoundaryRepresentative_ae Ω p u
    have hcu : (c • u).val.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] c • f := by
      filter_upwards [Lp.coeFn_smul c (u.val.val (zeroIndex d 1)), hu] with x hx hux
      change (c • u.val.val (zeroIndex d 1) : DomainLp 𝕜 Ω p) x = _
      rw [hx]
      exact congrArg (c • ·) hux
    apply Lp.ext
    filter_upwards [smoothBoundaryRestriction_coe Ω p hΩ hc (c • u) (c • f)
        (contDiff_const.smul hf) hcu,
      Lp.coeFn_smul c (smoothBoundaryRestriction Ω p hΩ hc u),
      smoothBoundaryRestriction_coe Ω p hΩ hc u f hf hu] with x hx hsmul hux
    change _ = (c • smoothBoundaryRestriction Ω p hΩ hc u : BoundaryLp 𝕜 Ω p) x
    rw [hx, hsmul]
    change c • f x = c • _
    rw [hux]

include hΩ hc in
/-- Extends the actual boundary restriction after its scalar norm estimate has been established.
The hypothesis is an inequality for ordinary smooth functions, not a trace certificate. -/
lemma exists_trace_of_smooth_bound (hp : p ≠ ∞) (C : ℝ)
    (hbound : ∀ (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
      ContDiff ℝ (⊤ : ℕ∞) f →
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f →
      (eLpNorm f p (surfaceMeasure Ω)).toReal ≤ C * ‖u‖) :
    ∃! T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p, IsTrace T := by
  let L := smoothBoundaryRestrictionLM (𝕜 := 𝕜) Ω p hΩ hc
  let e := (smoothBoundarySubmodule (𝕜 := 𝕜) Ω p).subtype
  have hd : DenseRange e := by
    change Dense (Set.range ((↑) : smoothBoundarySubmodule (𝕜 := 𝕜) Ω p → SpaceValue 𝕜 d Ω 1 p))
    rw [Subtype.range_coe_subtype]
    change Dense (C1Extension.SmoothUpToBoundary (𝕜 := 𝕜) Ω p)
    exact C1Extension.smooth_density 𝕜 d Ω hΩ hc p hp
  have hnorm : ∀ u, ‖L u‖ ≤ C * ‖e u‖ := by
    intro u
    have hb := smoothBoundaryRestriction_coe Ω p hΩ hc u (smoothBoundaryRepresentative Ω p u)
      (smoothBoundaryRepresentative_contDiff Ω p u) (smoothBoundaryRepresentative_ae Ω p u)
    change ‖smoothBoundaryRestriction Ω p hΩ hc u‖ ≤ _
    rw [Lp.norm_def, eLpNorm_congr_ae hb]
    exact hbound u.val _ (smoothBoundaryRepresentative_contDiff Ω p u)
      (smoothBoundaryRepresentative_ae Ω p u)
  let T := L.extendOfNorm e
  have hT : IsTrace T := by
    intro u f hf hu
    let v : smoothBoundarySubmodule (𝕜 := 𝕜) Ω p := ⟨u, f, hf, hu⟩
    change T (e v) =ᵐ[surfaceMeasure Ω] f
    rw [LinearMap.extendOfNorm_eq hd ⟨C, hnorm⟩]
    exact smoothBoundaryRestriction_coe Ω p hΩ hc v f hf hu
  refine ⟨T, hT, ?_⟩
  intro S hS
  have heq : EqOn S T (C1Extension.SmoothUpToBoundary (𝕜 := 𝕜) Ω p) := by
    rintro u ⟨f, hf, hu⟩
    exact Lp.ext ((hS u f hf hu).trans (hT u f hf hu).symm)
  apply ContinuousLinearMap.ext
  intro u
  exact heq.closure S.continuous T.continuous
    (C1Extension.smooth_density 𝕜 d Ω hΩ hc p hp u)
end SmoothRestriction
end SmoothBoundaryConstruction


section IntervalKernelClosure
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open OneDimensional

/-- Split a global zero extension into two pieces supported away from
one of the two endpoints. Only underlying classes are constrained. -/
theorem interval_split_zeroExtension {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {a b : ℝ} (hab : a < b)
    (v : SpaceValue 𝕜 1 ⊤ 1 p)
    (hv : ∀ᵐ x ∂volume, x 0 ∉ Icc a b → v.val (zeroIndex 1 1) x = 0) :
    ∃ (m c : ℝ) (vL vR : SpaceValue 𝕜 1 ⊤ 1 p),
      a < m ∧ m < c ∧ c < b ∧ vL + vR = v ∧
      (∀ᵐ x ∂volume, x 0 ∉ Icc a c → vL.val (zeroIndex 1 1) x = 0) ∧
      (∀ᵐ x ∂volume, x 0 ∉ Icc m b → vR.val (zeroIndex 1 1) x = 0) := by
  let m := (2 * a + b) / 3
  let c := (a + 2 * b) / 3
  have ham : a < m := by dsimp [m]; linarith
  have hmc : m < c := by dsimp [m, c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  let K : Set (Domain 1) := linePoint '' Icc a m
  have hK : IsCompact K := isCompact_Icc.image (continuous_pi (fun _ => continuous_id))
  let U : Opens (Domain 1) := ⟨{x | x 0 < c}, isOpen_lt (continuous_apply 0) continuous_const⟩
  have hKU : K ⊆ U := by
    rintro x ⟨t, ht, rfl⟩
    exact ht.2.trans_lt hmc
  obtain ⟨η, hηU, hηone⟩ := C1Extension.exists_compact_ambient_cutoff (𝕜 := 𝕜) K hK U hKU
  obtain ⟨C, hC0, hC, hD⟩ := C1Extension.ambient_test_bounds η
  let vL := C1Extension.ambientMultiply η η.contDiff C hC0 hC hD v
  let vR := v - vL
  have hL : vL.val (zeroIndex 1 1) =ᵐ[volume] fun x => η x * v.val (zeroIndex 1 1) x := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      C1Extension.ambientMultiply_coe η η.contDiff C hC0 hC hD v
  have hR : vR.val (zeroIndex 1 1) =ᵐ[volume]
      fun x => v.val (zeroIndex 1 1) x - vL.val (zeroIndex 1 1) x := by
    change (v.val (zeroIndex 1 1) - vL.val (zeroIndex 1 1) : DomainLp 𝕜 ⊤ p) =ᵐ[volume] _
    have hh := Lp.coeFn_sub (v.val (zeroIndex 1 1)) (vL.val (zeroIndex 1 1))
    simp only [Opens.coe_top, Measure.restrict_univ] at hh
    filter_upwards [hh] with x hx
    exact hx
  refine ⟨m, c, vL, vR, ham, hmc, hcb, by dsimp [vR]; abel, ?_, ?_⟩
  · filter_upwards [hv, hL] with x hx hLx
    intro hxc
    rw [hLx]
    by_cases hxa : a ≤ x 0
    · have hcx : c < x 0 := lt_of_not_ge (fun h => hxc ⟨hxa, h⟩)
      have hxη : x ∉ tsupport η := fun h => (hηU h).not_ge hcx.le
      rw [image_eq_zero_of_notMem_tsupport hxη, zero_mul]
    · rw [hx (fun h => hxa h.1), mul_zero]
  · filter_upwards [hv, hL, hR] with x hx hLx hRx
    intro hxm
    rw [hRx, hLx]
    by_cases hxb : x 0 ≤ b
    · have hxm' : x 0 < m := lt_of_not_ge (fun h => hxm ⟨h, hxb⟩)
      by_cases hxa : a ≤ x 0
      · have hxK : x ∈ K := by
          refine ⟨x 0, ⟨hxa, hxm'.le⟩, ?_⟩
          exact linePoint_coordinate x
        rw [hηone x hxK, one_mul, sub_self]
      · rw [hx (fun h => hxa h.1), mul_zero, sub_self]
    · rw [hx (fun h => hxb h.2), mul_zero, sub_self]


/-- A translated closed interval supports the translated Sobolev class. -/
theorem interval_translation_supported {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (l r t : ℝ) (v : SpaceValue 𝕜 1 ⊤ 1 p)
    (hv : ∀ᵐ x ∂volume, x 0 ∉ Icc l r → v.val (zeroIndex 1 1) x = 0) :
    ∀ᵐ x ∂volume, x ∉ linePoint '' Icc (l + t) (r + t) →
      (sobolevTranslation hp (linePoint t) v).val (zeroIndex 1 1) x = 0 := by
  have hvs := (measurePreserving_sub_right volume (linePoint t)).quasiMeasurePreserving.ae hv
  filter_upwards [hvs, sobolevTranslation_coe hp (linePoint t) v (zeroIndex 1 1)] with x hx hTx
  intro hxK
  rw [hTx]
  apply hx
  intro hxI
  apply hxK
  refine ⟨x 0, ?_, linePoint_coordinate x⟩
  change l ≤ x 0 - t ∧ x 0 - t ≤ r at hxI
  constructor <;> linarith [hxI.1, hxI.2]

/-- A global zero extension restricts to the original norm closure on an
interval, by splitting and translating into the two endpoint interiors. -/
theorem interval_restrict_mem_zeroSpace {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {a b : ℝ} (hab : a < b)
    (v : SpaceValue 𝕜 1 ⊤ 1 p)
    (hv : ∀ᵐ x ∂volume, x 0 ∉ Icc a b → v.val (zeroIndex 1 1) x = 0) :
    C1Extension.restrictSobolev (le_top : lineDomain ⟨Ioo a b, isOpen_Ioo⟩ ≤ ⊤) v ∈
      ZeroSpaceValue 𝕜 1 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) 1 p hp := by
  obtain ⟨m, c, vL, vR, ham, hmc, hcb, hsum, hL, hR⟩ := interval_split_zeroExtension hab v hv
  let Ω : Opens (Domain 1) := lineDomain ⟨Ioo a b, isOpen_Ioo⟩
  let R : SpaceValue 𝕜 1 ⊤ 1 p →L[𝕜] SpaceValue 𝕜 1 Ω 1 p :=
    C1Extension.restrictSobolev le_top
  let F : ℝ → SpaceValue 𝕜 1 Ω 1 p := fun t =>
    R (sobolevTranslation hp (linePoint t) vL + sobolevTranslation hp (linePoint (-t)) vR)
  have hFc : Continuous F := R.continuous.comp
    (((sobolevTranslation_continuous hp vL).comp (continuous_pi (fun _ => continuous_id))).add
      ((sobolevTranslation_continuous hp vR).comp (continuous_pi (fun _ => continuous_neg))))
  have hF0 : F 0 = R v := by
    change R (sobolevTranslation hp (linePoint 0) vL + sobolevTranslation hp (linePoint (-0)) vR) = R v
    simp only [neg_zero, show linePoint 0 = 0 from rfl, sobolevTranslation_zero hp, hsum]
  have hδ : 0 < min (b - c) (m - a) := lt_min (sub_pos.mpr hcb) (sub_pos.mpr ham)
  have hFe : ∀ᶠ t in 𝓝[>] (0 : ℝ), F t ∈ ZeroSpaceValue 𝕜 1 Ω 1 p hp := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hδ).filter_mono inf_le_left] with t ht htδ
    have ht0 : 0 < t := ht
    have htbc : t < b - c := htδ.trans_le (min_le_left _ _)
    have htma : t < m - a := htδ.trans_le (min_le_right _ _)
    have hLK : linePoint '' Icc (a + t) (c + t) ⊆ Ω := by
      rintro x ⟨s, hs, rfl⟩
      change a < s ∧ s < b
      constructor <;> linarith [hs.1, hs.2]
    have hRK : linePoint '' Icc (m + -t) (b + -t) ⊆ Ω := by
      rintro x ⟨s, hs, rfl⟩
      change a < s ∧ s < b
      constructor <;> linarith [hs.1, hs.2]
    have hLm := restrict_mem_zeroSpace_of_compact_support hp
      (sobolevTranslation hp (linePoint t) vL) (linePoint '' Icc (a + t) (c + t))
      (isCompact_Icc.image (continuous_pi (fun _ => continuous_id))) hLK
      (interval_translation_supported hp a c t vL hL)
    have hRm := restrict_mem_zeroSpace_of_compact_support hp
      (sobolevTranslation hp (linePoint (-t)) vR) (linePoint '' Icc (m + -t) (b + -t))
      (isCompact_Icc.image (continuous_pi (fun _ => continuous_id))) hRK
      (interval_translation_supported hp m b (-t) vR hR)
    change R (_ + _) ∈ _
    rw [map_add]
    exact (ZeroSpaceValue 𝕜 1 Ω 1 p hp).add_mem hLm hRm
  have hFt : Filter.Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) :=
    hFc.continuousAt.tendsto.mono_left inf_le_left
  rw [← hF0]
  exact (smoothSubmodule 𝕜 1 Ω 1 p).isClosed_topologicalClosure.mem_of_tendsto hFt hFe

/-- Vanishing endpoints imply the closure-defined zero-boundary condition. -/
theorem interval_zeroSpace_of_endpoints {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {a b : ℝ} (hab : a < b)
    (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p)
    (f : ℝ → 𝕜) (hf : PrimitiveRepresentative u f) (ha : f a = 0) (hb : f b = 0) :
    u ∈ ZeroSpaceValue 𝕜 1 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) 1 p hp := by
  obtain ⟨v, hv⟩ := interval_zeroExtension_of_endpoints hab u f hf ha hb
  have hvs : ∀ᵐ x ∂volume, x 0 ∉ Icc a b → v.val (zeroIndex 1 1) x = 0 := by
    filter_upwards [hv] with x hx
    intro hxI
    rw [hx, indicator_of_notMem (show x ∉ lineDomain ⟨Ioo a b, isOpen_Ioo⟩ from
      fun h => hxI ⟨h.1.le, h.2.le⟩)]
  have hres : C1Extension.restrictSobolev
      (le_top : lineDomain ⟨Ioo a b, isOpen_Ioo⟩ ≤ ⊤) v = u := by
    apply sobolev_underlying_injective 𝕜 1 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) 1 p
    apply Lp.ext
    filter_upwards [C1Extension.restrictSobolev_coe le_top v (zeroIndex 1 1),
      ae_restrict_of_ae hv,
      ae_restrict_mem (lineDomain ⟨Ioo a b, isOpen_Ioo⟩).isOpen.measurableSet] with x hr hx hxΩ
    rw [hr, hx, indicator_of_mem hxΩ]
  exact hres ▸ interval_restrict_mem_zeroSpace hp hab v hvs

/-- The interval closure condition is exactly zero endpoint values. -/
theorem interval_zeroSpace_iff_endpoints {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {a b : ℝ} (hab : a < b)
    (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p)
    (f : ℝ → 𝕜) (hf : PrimitiveRepresentative u f) :
    u ∈ ZeroSpaceValue 𝕜 1 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) 1 p hp ↔
      f a = 0 ∧ f b = 0 := by
  constructor
  · intro hu
    exact interval_zeroSpace_endpoints 𝕜 a b hab p hp u hu f hf
  · rintro ⟨ha, hb⟩
    exact interval_zeroSpace_of_endpoints hp hab u f hf ha hb

/-- Full closure-defined trace kernel equality on bounded intervals. -/
theorem interval_trace_kernel {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {a b : ℝ} (hab : a < b)
    (T : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p →L[𝕜]
      BoundaryLp 𝕜 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) p) (hT : IsTrace T) :
    T.ker = ZeroSpaceValue 𝕜 1 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) 1 p hp := by
  apply le_antisymm
  · intro u hu
    obtain ⟨f, hf⟩ := representative_existence 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ ordConnected_Ioo p u
    apply (interval_zeroSpace_iff_endpoints hp hab u f hf).mpr
    exact (interval_trace_zero_iff hab hp T hT u f hf).mp hu
  · exact kernel_contains_zeroSpace 𝕜 1 (lineDomain ⟨Ioo a b, isOpen_Ioo⟩) p hp T hT

end IntervalKernelClosure

/-- The complete kernel statement, specialized to the bounded interval of the
source's endpoint identification. -/
theorem interval_kernel :
    Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel.IntervalKernel := by
  intro 𝕜 _ a b hab p _ hp T hT
  exact interval_trace_kernel hp hab T hT


section InwardTranslations
open Filter
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open C1Extension HalfSpace

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Translation carries essential support into the translated set. -/
theorem sobolevTranslation_supported (hp : p ≠ ∞) (h : Domain d)
    (v : SpaceValue 𝕜 d ⊤ 1 p) (K : Set (Domain d))
    (hv : ∀ᵐ x ∂volume, x ∉ K → v.val (zeroIndex d 1) x = 0) :
    ∀ᵐ x ∂volume, x ∉ (fun y => y + h) '' K →
      (sobolevTranslation hp h v).val (zeroIndex d 1) x = 0 := by
  have hvs := (measurePreserving_sub_right volume h).quasiMeasurePreserving.ae hv
  filter_upwards [hvs, sobolevTranslation_coe hp h v (zeroIndex d 1)] with x hx hTx
  intro hxK
  rw [hTx]
  apply hx
  intro hxold
  exact hxK ⟨x - h, hxold, sub_add_cancel x h⟩

/-- Any compactly supported global Sobolev function can be approximated by
interior compact functions if its support can be translated into the domain. -/
theorem restrict_mem_zeroSpace_of_inward_translation (hp : p ≠ ∞)
    (v : SpaceValue 𝕜 d ⊤ 1 p) (K : Set (Domain d)) (hK : IsCompact K)
    (hv : ∀ᵐ x ∂volume, x ∉ K → v.val (zeroIndex d 1) x = 0)
    (a : ℝ → Domain d) (ha : Continuous a) (ha0 : a 0 = 0)
    (hin : ∀ᶠ t in 𝓝[>] (0 : ℝ), (fun y => y + a t) '' K ⊆ Ω) :
    restrictSobolev (le_top : Ω ≤ ⊤) v ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp := by
  let R : SpaceValue 𝕜 d ⊤ 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p := restrictSobolev le_top
  let F : ℝ → SpaceValue 𝕜 d Ω 1 p := fun t => R (sobolevTranslation hp (a t) v)
  have hF : Continuous F := R.continuous.comp ((sobolevTranslation_continuous hp v).comp ha)
  have hF0 : F 0 = R v := by dsimp [F]; rw [ha0, sobolevTranslation_zero]
  have hFe : ∀ᶠ t in 𝓝[>] (0 : ℝ), F t ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp := by
    filter_upwards [hin] with t ht
    exact restrict_mem_zeroSpace_of_compact_support hp (sobolevTranslation hp (a t) v)
      ((fun y => y + a t) '' K) (hK.image (continuous_id.add continuous_const)) ht
      (sobolevTranslation_supported hp (a t) v K hv)
  have hFt : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F 0)) :=
    hF.continuousAt.tendsto.mono_left inf_le_left
  rw [← hF0]
  exact (smoothSubmodule 𝕜 d Ω 1 p).isClosed_topologicalClosure.mem_of_tendsto hFt hFe

/-- The complete flat local reverse argument: compact global data supported
in the closed upper half-space restrict to its original compact-test closure. -/
theorem upper_restrict_mem_zeroSpace_of_compact_support (hp : p ≠ ∞)
    (i : Fin d) (v : SpaceValue 𝕜 d ⊤ 1 p) (K : Set (Domain d)) (hK : IsCompact K)
    (hv : ∀ᵐ x ∂volume, x ∉ K → v.val (zeroIndex d 1) x = 0)
    (hupper : ∀ᵐ x ∂volume, x i < 0 → v.val (zeroIndex d 1) x = 0) :
    restrictSobolev (le_top : upper i ≤ ⊤) v ∈ ZeroSpaceValue 𝕜 d (upper i) 1 p hp := by
  let L := K ∩ {x : Domain d | 0 ≤ x i}
  have hL : IsCompact L := hK.inter_right (isClosed_le continuous_const (continuous_apply i))
  have hvL : ∀ᵐ x ∂volume, x ∉ L → v.val (zeroIndex d 1) x = 0 := by
    filter_upwards [hv, hupper] with x hx hxupper
    intro hxL
    by_cases hxK : x ∈ K
    · exact hxupper (lt_of_not_ge (fun hh => hxL ⟨hxK, hh⟩))
    · exact hx hxK
  let a : ℝ → Domain d := fun t => t • coordinateVector i
  apply restrict_mem_zeroSpace_of_inward_translation hp v L hL hvL a
    (continuous_id.smul continuous_const) (by simp [a])
  filter_upwards [self_mem_nhdsWithin] with t ht
  rintro x ⟨y, hy, rfl⟩
  change 0 < (y + a t) i
  have hti : a t i = t := by simp [a, coordinateVector]
  change 0 < y i + a t i
  rw [hti]
  exact add_pos_of_nonneg_of_pos hy.2 ht

end InwardTranslations


section FlatTraceEstimate

lemma norm_left_endpoint_le_integrals {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (hf : ContDiff ℝ 1 f) :
    ‖f 0‖ ≤ (∫ t in (0 : ℝ)..1, ‖f t‖) + ∫ t in (0 : ℝ)..1, ‖deriv f t‖ := by
  have hd : Continuous (deriv f) := hf.continuous_deriv_one
  have hintf : IntervalIntegrable (fun t => ‖f t‖) volume 0 1 := hf.continuous.norm.intervalIntegrable _ _
  have hintd : IntervalIntegrable (fun t => ‖deriv f t‖) volume 0 1 := hd.norm.intervalIntegrable _ _
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖f 0‖ ≤ ‖f t‖ + ∫ t in (0 : ℝ)..1, ‖deriv f t‖ := by
    intro t ht
    have hFTC : ∫ s in (0 : ℝ)..t, deriv f s = f t - f 0 :=
      intervalIntegral.integral_deriv_eq_sub
        (fun _ _ => hf.differentiable_one _) (hd.intervalIntegrable _ _)
    have hsub : ‖f 0 - f t‖ ≤ ∫ s in (0 : ℝ)..1, ‖deriv f s‖ := by
      rw [norm_sub_rev, ← hFTC]
      exact (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
        (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
          (Filter.Eventually.of_forall fun x => norm_nonneg _) hintd)
    calc
      ‖f 0‖ = ‖f t + (f 0 - f t)‖ := by congr 1; abel
      _ ≤ ‖f t‖ + ‖f 0 - f t‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl hsub
  have hmono := intervalIntegral.integral_mono_on zero_le_one
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ‖f 0‖) volume 0 1)
    (hintf.add intervalIntegrable_const) hpoint
  simpa only [intervalIntegral.integral_const, intervalIntegral.integral_add hintf intervalIntegrable_const,
    sub_zero, one_smul] using hmono


lemma ofReal_integral_norm_unit_eq_lintegral {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (hf : Continuous f) :
    ENNReal.ofReal (∫ t in (0 : ℝ)..1, ‖f t‖) =
      ∫⁻ t, ‖f t‖ₑ ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    ofReal_integral_eq_lintegral_ofReal (hf.norm.intervalIntegrable 0 1).1
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
  simp only [ofReal_norm]

lemma enorm_left_endpoint_le_lintegrals {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (hf : ContDiff ℝ 1 f) :
    ‖f 0‖ₑ ≤ (∫⁻ t, ‖f t‖ₑ ∂(volume.restrict (Ioc (0 : ℝ) 1))) +
      ∫⁻ t, ‖deriv f t‖ₑ ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
  have h := ENNReal.ofReal_le_ofReal (norm_left_endpoint_le_integrals f hf)
  rwa [ofReal_norm, ENNReal.ofReal_add
    (intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _))
    (intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)),
    ofReal_integral_norm_unit_eq_lintegral f hf.continuous,
    ofReal_integral_norm_unit_eq_lintegral (deriv f) hf.continuous_deriv_one] at h

/-- The actual flat unit-slab L1 trace inequality, including the derivative term.
No boundary trace operator, kernel fact, or Sobolev certificate is assumed. -/
lemma flat_unit_slab_lintegral_bound {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure X)
    (f g : X × ℝ → E) (hf : Measurable f) (hg : Measurable g)
    (hfC1 : ∀ x, ContDiff ℝ 1 (fun t => f (x, t)))
    (hderiv : ∀ x, deriv (fun t => f (x, t)) = fun t => g (x, t)) :
    (∫⁻ x, ‖f (x, 0)‖ₑ ∂μ) ≤
      (∫⁻ z, ‖f z‖ₑ ∂μ.prod (volume.restrict (Ioc (0 : ℝ) 1))) +
      ∫⁻ z, ‖g z‖ₑ ∂μ.prod (volume.restrict (Ioc (0 : ℝ) 1)) := by
  calc
    (∫⁻ x, ‖f (x, 0)‖ₑ ∂μ) ≤
        ∫⁻ x, ((∫⁻ t, ‖f (x, t)‖ₑ ∂(volume.restrict (Ioc (0 : ℝ) 1))) +
          ∫⁻ t, ‖g (x, t)‖ₑ ∂(volume.restrict (Ioc (0 : ℝ) 1))) ∂μ := by
      apply lintegral_mono
      intro x
      simpa only [hderiv x] using enorm_left_endpoint_le_lintegrals (fun t => f (x, t)) (hfC1 x)
    _ = _ := by
      rw [lintegral_add_left hf.enorm.lintegral_prod_right']
      rw [← lintegral_prod _ hf.enorm.aemeasurable, ← lintegral_prod _ hg.enorm.aemeasurable]
end FlatTraceEstimate

end ExpandedFA.Sobolev.Trace


noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace ExpandedFA.Sobolev.Trace

lemma hausdorff_restrict_image_le_map {X Y : Type*}
    [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {K : ℝ≥0} {f : X → Y} {s : Set X} {q : ℝ} (hq : 0 ≤ q)
    (hf : LipschitzOnWith K f s)
    (hm : AEMeasurable f ((Measure.hausdorffMeasure q).restrict s)) :
    (Measure.hausdorffMeasure q).restrict (f '' s) ≤
      (K : ℝ≥0∞) ^ q • (((Measure.hausdorffMeasure q).restrict s).map f) := by
  apply Measure.le_iff.mpr
  intro A hA
  have himage : f '' (f ⁻¹' A ∩ s) = A ∩ f '' s := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxA, hxs⟩, rfl⟩
      exact ⟨hxA, mem_image_of_mem f hxs⟩
    · rintro ⟨hyA, x, hxs, rfl⟩
      exact ⟨x, ⟨hyA, hxs⟩, rfl⟩
  rw [Measure.restrict_apply hA, Measure.smul_apply,
    Measure.map_apply_of_aemeasurable hm hA,
    Measure.restrict_apply₀ (hm.nullMeasurableSet_preimage hA), ← himage]
  exact (hf.mono inter_subset_right).hausdorffMeasure_image_le hq

lemma hausdorff_comap_le {X Y : Type*}
    [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {K : ℝ≥0} {f : X → Y} {q : ℝ} (hq : 0 ≤ q)
    (hf : LipschitzWith K f) (hm : MeasurableEmbedding f) :
    (Measure.hausdorffMeasure q).comap f ≤
      (K : ℝ≥0∞) ^ q • Measure.hausdorffMeasure q := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [hm.comap_apply, Measure.smul_apply]
  exact hf.hausdorffMeasure_image_le hq A

open ExpandedFA.Distributions

lemma surfaceMeasure_le_hausdorff {n : ℕ} (Ω : TopologicalSpace.Opens (Domain (n + 1))) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ surfaceMeasure Ω ≤
      C • (Measure.hausdorffMeasure (n : ℝ)).restrict
        (frontier (Ω : Set (Domain (n + 1)))) := by
  let c := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))
  let K : ℝ≥0 := (Fintype.card (Fin (n + 1)) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal
  have hK : LipschitzWith K (WithLp.toLp 2 : Domain (n + 1) → EuclideanSpace ℝ (Fin (n + 1))) :=
    PiLp.lipschitzWith_toLp 2 (fun _ : Fin (n + 1) => ℝ)
  refine ⟨c * (K : ℝ≥0∞) ^ (n : ℝ), ?_, ?_⟩
  · exact ENNReal.mul_lt_top (measure_ball_lt_top (μ := volume))
      (ENNReal.rpow_lt_top_of_nonneg (Nat.cast_nonneg n) ENNReal.coe_ne_top)
  · have h := Measure.restrict_mono_measure
      (hausdorff_comap_le (Nat.cast_nonneg n) hK
        (MeasurableEquiv.toLp 2 (Domain (n + 1))).measurableEmbedding)
      (frontier (Ω : Set (Domain (n + 1))))
    rw [Measure.restrict_smul] at h
    have h' := smul_le_smul_left c h
    simpa only [surfaceMeasure, Nat.succ_sub_succ_eq_sub, Nat.sub_zero, smul_smul,
      NNReal.smul_def, ENNReal.smul_def] using h'

lemma hausdorff_le_comap_toLp (n : ℕ) :
    (Measure.hausdorffMeasure (n : ℝ) : Measure (Domain (n + 1))) ≤
      (Measure.hausdorffMeasure (n : ℝ)).comap
        (WithLp.toLp 2 : Domain (n + 1) → EuclideanSpace ℝ (Fin (n + 1))) := by
  apply Measure.le_iff.mpr
  intro A hA
  have hcomap := (MeasurableEquiv.toLp 2 (Domain (n + 1))).measurableEmbedding.comap_apply
    (Measure.hausdorffMeasure (n : ℝ)) A
  change (Measure.comap (WithLp.toLp 2) (Measure.hausdorffMeasure (n : ℝ))) A = _ at hcomap
  rw [hcomap]
  simpa only [MeasurableEquiv.coe_toLp, ENNReal.coe_one, ENNReal.one_rpow, one_mul] using
    (PiLp.antilipschitzWith_toLp 2 (fun _ : Fin (n + 1) => ℝ)).le_hausdorffMeasure_image
      (Nat.cast_nonneg n) A

lemma hausdorff_restrict_le_surfaceMeasure {n : ℕ}
    (Ω : TopologicalSpace.Opens (Domain (n + 1))) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ (Measure.hausdorffMeasure (n : ℝ)).restrict
      (frontier (Ω : Set (Domain (n + 1)))) ≤ C • surfaceMeasure Ω := by
  let c := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))
  have hc0 : c ≠ 0 := (Metric.measure_ball_pos volume
    (0 : EuclideanSpace ℝ (Fin n)) (by norm_num : (0 : ℝ) < 1 / 2)).ne'
  have hctop : c ≠ ∞ := (measure_ball_lt_top (μ := volume)).ne
  refine ⟨c⁻¹, ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hc0), ?_⟩
  have h := smul_le_smul_left c (Measure.restrict_mono_measure
    (hausdorff_le_comap_toLp n) (frontier (Ω : Set (Domain (n + 1)))))
  have hs : c • (Measure.hausdorffMeasure (n : ℝ)).restrict
      (frontier (Ω : Set (Domain (n + 1)))) ≤ surfaceMeasure Ω := by
    simpa only [surfaceMeasure, Nat.succ_sub_succ_eq_sub, Nat.sub_zero] using h
  have hi := smul_le_smul_left c⁻¹ hs
  simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul] using hi

lemma surfaceMeasure_mutuallyAbsolutelyContinuous_hausdorff {n : ℕ}
    (Ω : TopologicalSpace.Opens (Domain (n + 1))) :
    surfaceMeasure Ω ≪ (Measure.hausdorffMeasure (n : ℝ)).restrict
        (frontier (Ω : Set (Domain (n + 1)))) ∧
      (Measure.hausdorffMeasure (n : ℝ)).restrict
        (frontier (Ω : Set (Domain (n + 1)))) ≪ surfaceMeasure Ω := by
  obtain ⟨C, hC, hupper⟩ := surfaceMeasure_le_hausdorff Ω
  obtain ⟨D, hD, hlower⟩ := hausdorff_restrict_le_surfaceMeasure Ω
  exact ⟨Measure.absolutelyContinuous_of_le_smul hupper,
    Measure.absolutelyContinuous_of_le_smul hlower⟩

/-- Parameters of the boundary in a flattening chart. -/
def boundaryParameters {n : ℕ}
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1)) :
    Set (Domain n) :=
  (fun z => i.insertNth (α := fun _ => ℝ) 0 z) ⁻¹' Φ.target

/-- The actual inverse-chart boundary parametrization, in coordinate norm. -/
def boundaryParam {n : ℕ}
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1)) :
    Domain n → Domain (n + 1) :=
  fun z => Φ.symm (i.insertNth (α := fun _ => ℝ) 0 z)

lemma boundaryParam_image {n : ℕ} (Ω : TopologicalSpace.Opens (Domain (n + 1)))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i) :
    boundaryParam Φ i '' boundaryParameters Φ i =
      Φ.source ∩ frontier (Ω : Set (Domain (n + 1))) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hsrc := Φ.map_target hz
    refine ⟨hsrc, (chart_boundary_iff Ω Φ i hside _ hsrc).mpr ?_⟩
    rw [Φ.right_inv hz]
    simp
  · rintro ⟨hxsrc, hxfront⟩
    let z : Domain n := i.removeNth (Φ x)
    have hz : i.insertNth (α := fun _ => ℝ) 0 z = Φ x := by
      have hzero := (chart_boundary_iff Ω Φ i hside _ hxsrc).mp hxfront
      change i.insertNth 0 (i.removeNth (Φ x)) = Φ x
      rw [← hzero, Fin.insertNth_self_removeNth]
    refine ⟨z, ?_, ?_⟩
    · change i.insertNth 0 z ∈ Φ.target
      rw [hz]
      exact Φ.map_source hxsrc
    · change Φ.symm (i.insertNth 0 z) = x
      rw [hz, Φ.left_inv hxsrc]

lemma boundaryParameters_isOpen {n : ℕ}
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1)) :
    IsOpen (boundaryParameters Φ i) := by
  apply Φ.open_target.preimage
  exact (show Isometry (fun z : Domain n => i.insertNth (α := fun _ => ℝ) 0 z) from
    (isometry_iff_dist_eq.mpr fun _ _ => by simp)).continuous

lemma boundaryParam_lipschitz {n : ℕ}
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    {K : ℝ≥0} (hK : LipschitzOnWith K Φ.symm Φ.target) :
    LipschitzOnWith K (boundaryParam Φ i) (boundaryParameters Φ i) := by
  have hins : Isometry (fun z : Domain n => i.insertNth (α := fun _ => ℝ) 0 z) :=
    isometry_iff_dist_eq.mpr fun _ _ => by simp
  intro x hx y hy
  change edist (Φ.symm (i.insertNth 0 x)) (Φ.symm (i.insertNth 0 y)) ≤ _
  calc
    _ ≤ (K : ℝ≥0∞) * edist (i.insertNth (α := fun _ => ℝ) 0 x) (i.insertNth 0 y) := hK hx hy
    _ = _ := by rw [hins.edist_eq]

lemma boundaryParam_aemeasurable {n : ℕ}
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1)) :
    AEMeasurable (boundaryParam Φ i) (volume.restrict (boundaryParameters Φ i)) := by
  have hins : Continuous (fun z : Domain n => i.insertNth (α := fun _ => ℝ) 0 z) :=
    (isometry_iff_dist_eq.mpr fun _ _ => by simp).continuous
  apply (Φ.symm.continuousOn.comp hins.continuousOn (fun _ hx => hx)).aemeasurable
    (boundaryParameters_isOpen Φ i).measurableSet

lemma hausdorff_chart_restrict_le_map {n : ℕ} (Ω : TopologicalSpace.Opens (Domain (n + 1)))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    {K : ℝ≥0} (hK : LipschitzOnWith K Φ.symm Φ.target) :
    (Measure.hausdorffMeasure (n : ℝ)).restrict
        (Φ.source ∩ frontier (Ω : Set (Domain (n + 1)))) ≤
      (K : ℝ≥0∞) ^ (n : ℝ) •
        ((volume.restrict (boundaryParameters Φ i)).map (boundaryParam Φ i)) := by
  have hH : (Measure.hausdorffMeasure (n : ℝ) : Measure (Domain n)) = volume := by
    simpa using (hausdorffMeasure_pi_real (ι := Fin n))
  rw [← boundaryParam_image Ω Φ i hside]
  have hm := boundaryParam_aemeasurable Φ i
  rw [← hH] at hm
  simpa only [hH] using hausdorff_restrict_image_le_map (Nat.cast_nonneg n)
    (boundaryParam_lipschitz Φ i hK) hm

lemma surfaceMeasure_chart_le_map {n : ℕ} (Ω : TopologicalSpace.Opens (Domain (n + 1)))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    {K : ℝ≥0} (hK : LipschitzOnWith K Φ.symm Φ.target) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ (surfaceMeasure Ω).restrict Φ.source ≤
      C • ((volume.restrict (boundaryParameters Φ i)).map (boundaryParam Φ i)) := by
  obtain ⟨C, hC, hmeasure⟩ := surfaceMeasure_le_hausdorff Ω
  refine ⟨C * (K : ℝ≥0∞) ^ (n : ℝ), ENNReal.mul_lt_top hC
    (ENNReal.rpow_lt_top_of_nonneg (Nat.cast_nonneg n) ENNReal.coe_ne_top), ?_⟩
  have hloc := Measure.restrict_mono_measure hmeasure Φ.source
  rw [Measure.restrict_smul, Measure.restrict_restrict Φ.open_source.measurableSet] at hloc
  exact hloc.trans (by
    simpa only [smul_smul] using smul_le_smul_left C
      (hausdorff_chart_restrict_le_map Ω Φ i hside hK))

lemma boundary_chart_lintegral_le {n : ℕ} (Ω : TopologicalSpace.Opens (Domain (n + 1)))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    {K : ℝ≥0} (hK : LipschitzOnWith K Φ.symm Φ.target) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ f : Domain (n + 1) → ℝ≥0∞, Measurable f →
      (∫⁻ x in Φ.source, f x ∂surfaceMeasure Ω) ≤
        C * ∫⁻ z in boundaryParameters Φ i, f (boundaryParam Φ i z) ∂volume := by
  obtain ⟨C, hC, hmeasure⟩ := surfaceMeasure_chart_le_map Ω Φ i hside hK
  refine ⟨C, hC, ?_⟩
  intro f hf
  calc
    _ ≤ ∫⁻ x, f x ∂C • ((volume.restrict (boundaryParameters Φ i)).map (boundaryParam Φ i)) :=
      lintegral_mono' hmeasure le_rfl
    _ = _ := by
      rw [lintegral_smul_measure, lintegral_map' hf.aemeasurable (boundaryParam_aemeasurable Φ i)]
      rfl

lemma boundary_chart_eLpNorm_le {n : ℕ} (Ω : TopologicalSpace.Opens (Domain (n + 1)))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    {K : ℝ≥0} (hK : LipschitzOnWith K Φ.symm Φ.target) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ {E : Type} [NormedAddCommGroup E]
      [MeasurableSpace E] [BorelSpace E] (f : Domain (n + 1) → E)
      (p : ℝ≥0∞), AEStronglyMeasurable f
        ((volume.restrict (boundaryParameters Φ i)).map (boundaryParam Φ i)) →
      eLpNorm f p ((surfaceMeasure Ω).restrict Φ.source) ≤
        C ^ (1 / p).toReal * eLpNorm (f ∘ boundaryParam Φ i) p
          (volume.restrict (boundaryParameters Φ i)) := by
  obtain ⟨C, hC, hmeasure⟩ := surfaceMeasure_chart_le_map Ω Φ i hside hK
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ f p hf
  calc
    _ ≤ C ^ (1 / p).toReal * eLpNorm f p
        ((volume.restrict (boundaryParameters Φ i)).map (boundaryParam Φ i)) :=
      eLpNorm_le_of_measure_le_smul hmeasure
    _ = _ := by rw [eLpNorm_map_measure hf (boundaryParam_aemeasurable Φ i)]

lemma boundaryParam_map_le_hausdorff {n : ℕ} (Ω : TopologicalSpace.Opens (Domain (n + 1)))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    {K : ℝ≥0} (hK : LipschitzOnWith K Φ Φ.source) :
    ((volume.restrict (boundaryParameters Φ i)).map (boundaryParam Φ i)) ≤
      (K : ℝ≥0∞) ^ (n : ℝ) • (Measure.hausdorffMeasure (n : ℝ)).restrict
        (Φ.source ∩ frontier (Ω : Set (Domain (n + 1)))) := by
  let r : Domain (n + 1) → Domain n := fun x => i.removeNth (Φ x)
  have hr : LipschitzOnWith K r Φ.source := by
    intro x hx y hy
    calc
      edist (r x) (r y) ≤ edist (Φ x) (Φ y) := by
        apply edist_pi_le_iff.mpr
        intro j
        exact edist_le_pi_edist (Φ x) (Φ y) (i.succAbove j)
      _ ≤ _ := hK hx hy
  have hH : (Measure.hausdorffMeasure (n : ℝ) : Measure (Domain n)) = volume := by
    simpa using (hausdorffMeasure_pi_real (ι := Fin n))
  apply Measure.le_iff.mpr
  intro A hA
  have himage : r '' (A ∩ (Φ.source ∩ frontier (Ω : Set (Domain (n + 1))))) =
      boundaryParam Φ i ⁻¹' A ∩ boundaryParameters Φ i := by
    ext z
    constructor
    · rintro ⟨x, ⟨hxA, hxs, hxf⟩, rfl⟩
      have hzero := (chart_boundary_iff Ω Φ i hside x hxs).mp hxf
      have hxins : i.insertNth (α := fun _ => ℝ) 0 (r x) = Φ x := by
        dsimp [r]
        rw [← hzero, Fin.insertNth_self_removeNth]
      constructor
      · change Φ.symm (i.insertNth 0 (r x)) ∈ A
        rwa [hxins, Φ.left_inv hxs]
      · change i.insertNth 0 (r x) ∈ Φ.target
        rw [hxins]
        exact Φ.map_source hxs
    · rintro ⟨hzA, hzs⟩
      let x := boundaryParam Φ i z
      have hxs : x ∈ Φ.source := Φ.map_target hzs
      have hxΦ : Φ x = i.insertNth (α := fun _ => ℝ) 0 z := Φ.right_inv hzs
      refine ⟨x, ⟨hzA, hxs, (chart_boundary_iff Ω Φ i hside x hxs).mpr ?_⟩, ?_⟩
      · simp [hxΦ]
      · simp only [r, hxΦ, Fin.removeNth_insertNth]
  rw [Measure.map_apply_of_aemeasurable (boundaryParam_aemeasurable Φ i) hA,
    Measure.restrict_apply₀ ((boundaryParam_aemeasurable Φ i).nullMeasurableSet_preimage hA),
    Measure.smul_apply, Measure.restrict_apply hA, ← hH, ← himage]
  exact (hr.mono (fun _ hx => hx.2.1)).hausdorffMeasure_image_le (Nat.cast_nonneg n)

lemma boundaryParam_map_le_surfaceMeasure {n : ℕ} (Ω : TopologicalSpace.Opens (Domain (n + 1)))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    {K : ℝ≥0} (hK : LipschitzOnWith K Φ Φ.source) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ((volume.restrict (boundaryParameters Φ i)).map (boundaryParam Φ i)) ≤
        C • (surfaceMeasure Ω).restrict Φ.source := by
  obtain ⟨C, hC, hbound⟩ := hausdorff_restrict_le_surfaceMeasure Ω
  have hloc := Measure.restrict_mono_measure hbound Φ.source
  rw [Measure.restrict_restrict Φ.open_source.measurableSet, Measure.restrict_smul] at hloc
  refine ⟨(K : ℝ≥0∞) ^ (n : ℝ) * C,
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (Nat.cast_nonneg n) ENNReal.coe_ne_top) hC, ?_⟩
  exact (boundaryParam_map_le_hausdorff Ω Φ i hside hK).trans (by
    simpa only [smul_smul] using smul_le_smul_left ((K : ℝ≥0∞) ^ (n : ℝ)) hloc)

/-- A finite bounded C1 boundary atlas retaining genuine Lipschitz control of
its inverse maps. This uses convex target balls before applying the mean-value
estimate; arbitrary chart sources need not be convex. -/
lemma finite_bounded_lipschitz_boundary_charts (d : ℕ)
    (Ω : TopologicalSpace.Opens (Domain d)) (hΩ : C1Extension.IsC1Domain Ω)
    (hc : IsCompact (frontier (Ω : Set (Domain d)))) :
    ∃ (n : ℕ) (i : Fin n → Fin d)
      (Φ : Fin n → OpenPartialHomeomorph (Domain d) (Domain d))
      (B : ℝ) (K : Fin n → ℝ≥0), 0 ≤ B ∧
      (∀ j, ContDiffOn ℝ 1 (Φ j) (Φ j).source ∧
        ContDiffOn ℝ 1 (Φ j).symm (Φ j).target ∧
        Bornology.IsBounded (Φ j).source ∧ Bornology.IsBounded (Φ j).target ∧
        (∀ y ∈ (Φ j).source, y ∈ Ω ↔ 0 < Φ j y (i j)) ∧
        (∀ y ∈ (Φ j).source, ‖fderiv ℝ (Φ j) y‖ ≤ B) ∧
        (∀ y ∈ (Φ j).target, ‖fderiv ℝ (Φ j).symm y‖ ≤ B)) ∧
      (∀ j, LipschitzOnWith (K j) (Φ j).symm (Φ j).target) ∧
      frontier (Ω : Set (Domain d)) ⊆ ⋃ j, (Φ j).source := by
  classical
  have hatlas (x : frontier (Ω : Set (Domain d))) :
      ∃ (i : Fin d) (Ψ : OpenPartialHomeomorph (Domain d) (Domain d))
        (C : ℝ) (K : ℝ≥0), x.val ∈ Ψ.source ∧ 0 ≤ C ∧
        ContDiffOn ℝ 1 Ψ Ψ.source ∧ ContDiffOn ℝ 1 Ψ.symm Ψ.target ∧
        Bornology.IsBounded Ψ.source ∧ Bornology.IsBounded Ψ.target ∧
        (∀ y ∈ Ψ.source, y ∈ Ω ↔ 0 < Ψ y i) ∧
        (∀ y ∈ Ψ.source, ‖fderiv ℝ Ψ y‖ ≤ C) ∧
        (∀ y ∈ Ψ.target, ‖fderiv ℝ Ψ.symm y‖ ≤ C) ∧
        LipschitzOnWith K Ψ.symm Ψ.target := by
    obtain ⟨i, Φ, hx, hzero, hΦ, hInv, hside⟩ := hΩ x x.property
    obtain ⟨Ψ, r, hr, hxΨ, htarget, hs, ht, hsc, htc, hsb, htb,
      hfun, hinvfun, hΨ, hΨinv, C, hC, hCsrc, hCtgt⟩ :=
      C1Extension.shrink_c1_chart Φ x hx hΦ hInv
    refine ⟨i, Ψ, C, ⟨C, hC⟩, hxΨ, hC, hΨ, hΨinv, hsb, htb, ?_, hCsrc, hCtgt, ?_⟩
    · intro y hy
      rw [hfun]
      exact hside y (hs (subset_closure hy))
    · apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
        (fun y hy => (hΨinv.differentiableOn_one y hy).differentiableAt
          (Ψ.open_target.mem_nhds hy)) (fun y hy => ?_)
      · rw [htarget]
        exact convex_ball _ _
      · exact_mod_cast hCtgt y hy
  choose i Ψ C K hx hC0 hΨ hInv hsb htb hside hCsrc hCtgt hLip using hatlas
  obtain ⟨s, hcover⟩ := hc.elim_finite_subcover (fun x => (Ψ x).source)
    (fun x => (Ψ x).open_source)
    (fun x hx' => mem_iUnion.mpr ⟨⟨x, hx'⟩, hx ⟨x, hx'⟩⟩)
  let B := ∑ x ∈ s, C x
  have hCB (x : frontier (Ω : Set (Domain d))) (hx : x ∈ s) : C x ≤ B :=
    Finset.single_le_sum (fun y _ => hC0 y) hx
  refine ⟨s.card, fun j => i (s.equivFin.symm j).val,
    fun j => Ψ (s.equivFin.symm j).val, B, fun j => K (s.equivFin.symm j).val,
    Finset.sum_nonneg (fun x _ => hC0 x), ?_, ?_, ?_⟩
  · intro j
    let x := s.equivFin.symm j
    exact ⟨hΨ x.val, hInv x.val, hsb x.val, htb x.val, hside x.val,
      fun y hy => (hCsrc x.val y hy).trans (hCB x.val x.property),
      fun y hy => (hCtgt x.val y hy).trans (hCB x.val x.property)⟩
  · intro j
    exact hLip _
  · intro x hx'
    obtain ⟨z, hz⟩ := mem_iUnion.mp (hcover hx')
    obtain ⟨hzs, hxz⟩ := mem_iUnion.mp hz
    refine mem_iUnion.mpr ⟨s.equivFin ⟨z, hzs⟩, ?_⟩
    simpa using hxz

/-- Both boundary charts and inverse charts can be made genuinely Lipschitz
near a given boundary point, without a convexity assumption on their source. -/
lemma local_bilipschitz_boundary_chart {d : ℕ}
    (Ω : TopologicalSpace.Opens (Domain d)) (hΩ : C1Extension.IsC1Domain Ω)
    (x : Domain d) (hx : x ∈ frontier (Ω : Set (Domain d))) :
    ∃ (i : Fin d) (Ψ : OpenPartialHomeomorph (Domain d) (Domain d)) (K L : ℝ≥0),
      x ∈ Ψ.source ∧ ContDiffOn ℝ 1 Ψ Ψ.source ∧
      ContDiffOn ℝ 1 Ψ.symm Ψ.target ∧
      (∀ y ∈ Ψ.source, y ∈ Ω ↔ 0 < Ψ y i) ∧
      LipschitzOnWith K Ψ Ψ.source ∧ LipschitzOnWith L Ψ.symm Ψ.target := by
  obtain ⟨i, Φ, hxΦ, hzero, hΦ, hInv, hside⟩ := hΩ x hx
  obtain ⟨K, U, hUx, hLip⟩ :=
    ((hΦ x hxΦ).contDiffAt (Φ.open_source.mem_nhds hxΦ)).exists_lipschitzOnWith
  obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hUx
  let Θ := Φ.restrOpen V hVopen
  have hxΘ : x ∈ Θ.source := ⟨hxΦ, hxV⟩
  have hΘ : ContDiffOn ℝ 1 Θ Θ.source := hΦ.mono inter_subset_left
  have hΘInv : ContDiffOn ℝ 1 Θ.symm Θ.target := hInv.mono inter_subset_left
  obtain ⟨Ψ, r, hr, hxΨ, htarget, hs, ht, hsc, htc, hsb, htb,
      hfun, hinvfun, hΨ, hΨinv, C, hC, hCsrc, hCtgt⟩ :=
    C1Extension.shrink_c1_chart Θ x hxΘ hΘ hΘInv
  refine ⟨i, Ψ, K, ⟨C, hC⟩, hxΨ, hΨ, hΨinv, ?_, ?_, ?_⟩
  · intro y hy
    have hyΘ := hs (subset_closure hy)
    rw [hfun]
    exact hside y hyΘ.1
  · have hsub : Ψ.source ⊆ U := fun y hy => hVU (hs (subset_closure hy)).2
    have heq : (Ψ : Domain d → Domain d) = Φ := hfun
    rw [heq]
    exact hLip.mono hsub
  · apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun y hy => (hΨinv.differentiableOn_one y hy).differentiableAt
        (Ψ.open_target.mem_nhds hy)) (fun y hy => ?_)
    · rw [htarget]
      exact convex_ball _ _
    · exact_mod_cast hCtgt y hy

lemma boundary_chart_mutuallyAbsolutelyContinuous {n : ℕ}
    (Ω : TopologicalSpace.Opens (Domain (n + 1)))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    {K L : ℝ≥0} (hK : LipschitzOnWith K Φ Φ.source)
    (hL : LipschitzOnWith L Φ.symm Φ.target) :
    (surfaceMeasure Ω).restrict Φ.source ≪
        ((volume.restrict (boundaryParameters Φ i)).map (boundaryParam Φ i)) ∧
      ((volume.restrict (boundaryParameters Φ i)).map (boundaryParam Φ i)) ≪
        (surfaceMeasure Ω).restrict Φ.source := by
  obtain ⟨C, hC, hupper⟩ := surfaceMeasure_chart_le_map Ω Φ i hside hL
  obtain ⟨D, hD, hlower⟩ := boundaryParam_map_le_surfaceMeasure Ω Φ i hside hK
  exact ⟨Measure.absolutelyContinuous_of_le_smul hupper,
    Measure.absolutelyContinuous_of_le_smul hlower⟩

lemma local_bounded_bilipschitz_boundary_chart {d : ℕ}
    (Ω : TopologicalSpace.Opens (Domain d)) (hΩ : C1Extension.IsC1Domain Ω)
    (x : Domain d) (hx : x ∈ frontier (Ω : Set (Domain d))) :
    ∃ (i : Fin d) (Ψ : OpenPartialHomeomorph (Domain d) (Domain d))
      (B : ℝ) (K L : ℝ≥0), x ∈ Ψ.source ∧ 0 ≤ B ∧
      ContDiffOn ℝ 1 Ψ Ψ.source ∧ ContDiffOn ℝ 1 Ψ.symm Ψ.target ∧
      Bornology.IsBounded Ψ.source ∧ Bornology.IsBounded Ψ.target ∧
      (∀ y ∈ Ψ.source, y ∈ Ω ↔ 0 < Ψ y i) ∧
      (∀ y ∈ Ψ.source, ‖fderiv ℝ Ψ y‖ ≤ B) ∧
      (∀ y ∈ Ψ.target, ‖fderiv ℝ Ψ.symm y‖ ≤ B) ∧
      LipschitzOnWith K Ψ Ψ.source ∧ LipschitzOnWith L Ψ.symm Ψ.target := by
  obtain ⟨i, Φ, K, L, hxΦ, hΦ, hInv, hside, hK, hL⟩ :=
    local_bilipschitz_boundary_chart Ω hΩ x hx
  obtain ⟨Ψ, r, hr, hxΨ, htarget, hs, ht, hsc, htc, hsb, htb,
      hfun, hinvfun, hΨ, hΨinv, B, hB, hBsrc, hBtgt⟩ :=
    C1Extension.shrink_c1_chart Φ x hxΦ hΦ hInv
  refine ⟨i, Ψ, B, K, L, hxΨ, hB, hΨ, hΨinv, hsb, htb, ?_, hBsrc, hBtgt, ?_, ?_⟩
  · intro y hy
    rw [hfun]
    exact hside y (hs (subset_closure hy))
  · rw [hfun]
    exact hK.mono (fun _ hy => hs (subset_closure hy))
  · rw [hinvfun]
    exact hL.mono (fun _ hy => ht (subset_closure hy))

/-- Finite boundary atlas with uniform derivative bounds and genuine
Lipschitz constants for both directions of each local change of variables. -/
lemma finite_bounded_bilipschitz_boundary_charts (d : ℕ)
    (Ω : TopologicalSpace.Opens (Domain d)) (hΩ : C1Extension.IsC1Domain Ω)
    (hc : IsCompact (frontier (Ω : Set (Domain d)))) :
    ∃ (n : ℕ) (i : Fin n → Fin d)
      (Φ : Fin n → OpenPartialHomeomorph (Domain d) (Domain d))
      (B : ℝ) (K L : Fin n → ℝ≥0), 0 ≤ B ∧
      (∀ j, ContDiffOn ℝ 1 (Φ j) (Φ j).source ∧
        ContDiffOn ℝ 1 (Φ j).symm (Φ j).target ∧
        Bornology.IsBounded (Φ j).source ∧ Bornology.IsBounded (Φ j).target ∧
        (∀ y ∈ (Φ j).source, y ∈ Ω ↔ 0 < Φ j y (i j)) ∧
        (∀ y ∈ (Φ j).source, ‖fderiv ℝ (Φ j) y‖ ≤ B) ∧
        (∀ y ∈ (Φ j).target, ‖fderiv ℝ (Φ j).symm y‖ ≤ B)) ∧
      (∀ j, LipschitzOnWith (K j) (Φ j) (Φ j).source ∧
        LipschitzOnWith (L j) (Φ j).symm (Φ j).target) ∧
      frontier (Ω : Set (Domain d)) ⊆ ⋃ j, (Φ j).source := by
  classical
  have hatlas (x : frontier (Ω : Set (Domain d))) :=
    local_bounded_bilipschitz_boundary_chart Ω hΩ x x.property
  choose i Ψ C K L hx hC0 hΨ hInv hsb htb hside hCsrc hCtgt hLip hInvLip using hatlas
  obtain ⟨s, hcover⟩ := hc.elim_finite_subcover (fun x => (Ψ x).source)
    (fun x => (Ψ x).open_source)
    (fun x hx' => mem_iUnion.mpr ⟨⟨x, hx'⟩, hx ⟨x, hx'⟩⟩)
  let B := ∑ x ∈ s, C x
  have hCB (x : frontier (Ω : Set (Domain d))) (hx : x ∈ s) : C x ≤ B :=
    Finset.single_le_sum (fun y _ => hC0 y) hx
  refine ⟨s.card, fun j => i (s.equivFin.symm j).val,
    fun j => Ψ (s.equivFin.symm j).val, B, fun j => K (s.equivFin.symm j).val,
    fun j => L (s.equivFin.symm j).val, Finset.sum_nonneg (fun x _ => hC0 x), ?_, ?_, ?_⟩
  · intro j
    let x := s.equivFin.symm j
    exact ⟨hΨ x.val, hInv x.val, hsb x.val, htb x.val, hside x.val,
      fun y hy => (hCsrc x.val y hy).trans (hCB x.val x.property),
      fun y hy => (hCtgt x.val y hy).trans (hCB x.val x.property)⟩
  · intro j
    exact ⟨hLip _, hInvLip _⟩
  · intro x hx'
    obtain ⟨z, hz⟩ := mem_iUnion.mp (hcover hx')
    obtain ⟨hzs, hxz⟩ := mem_iUnion.mp hz
    refine mem_iUnion.mpr ⟨s.equivFin ⟨z, hzs⟩, ?_⟩
    simpa using hxz

lemma boundary_chart_pullback_eLpNorm_le {n : ℕ}
    (Ω : TopologicalSpace.Opens (Domain (n + 1)))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    {K : ℝ≥0} (hK : LipschitzOnWith K Φ Φ.source) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ {E : Type} [NormedAddCommGroup E]
      [MeasurableSpace E] [BorelSpace E] (f : Domain (n + 1) → E)
      (p : ℝ≥0∞), Continuous f →
      eLpNorm (f ∘ boundaryParam Φ i) p (volume.restrict (boundaryParameters Φ i)) ≤
        C ^ (1 / p).toReal * eLpNorm f p (surfaceMeasure Ω) := by
  obtain ⟨C, hC, hmap⟩ := boundaryParam_map_le_surfaceMeasure Ω Φ i hside hK
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ f p hf
  rw [← eLpNorm_map_measure hf.aestronglyMeasurable (boundaryParam_aemeasurable Φ i)]
  exact eLpNorm_le_of_measure_le_smul (hmap.trans (smul_le_smul_left C Measure.restrict_le_self))

end ExpandedFA.Sobolev.Trace


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Topology
namespace ExpandedFA.Sobolev.Trace
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open C1Extension HalfSpace

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Compact interior essential support gives membership in the original W0
closure, even when no global extension was provided as input. -/
theorem mem_zeroSpace_of_compact_support (hp : p ≠ ∞)
    (u : SpaceValue 𝕜 d Ω 1 p) (K : Set (Domain d)) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω)
    (hu : ∀ᵐ x ∂volume.restrict (Ω : Set (Domain d)),
      x ∉ K → u.val (zeroIndex d 1) x = 0) :
    u ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp := by
  obtain ⟨η, hη, hηone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜) K hK Ω hKΩ
  obtain ⟨C, hC0, hC, hD⟩ := ambient_test_bounds η
  have hηclosed : IsClosed (tsupport η ∪ ((⊤ : Opens (Domain d)) : Set (Domain d))ᶜ) := by
    simpa using isClosed_tsupport η
  let v := localizedZeroExtension (le_top : Ω ≤ ⊤) (tsupport η) hηclosed hη
    η η.contDiff C hC0 hC hD inter_subset_right u
  have hv : v.val (zeroIndex d 1) =ᵐ[volume]
      (Ω : Set (Domain d)).indicator (fun x => η x * u.val (zeroIndex d 1) x) := by
    simpa only [v, Opens.coe_top, Measure.restrict_univ] using
      localizedZeroExtension_coe (le_top : Ω ≤ ⊤) (tsupport η) hηclosed hη
        η η.contDiff C hC0 hC hD inter_subset_right u
  have hvη : ∀ᵐ x ∂volume, x ∉ tsupport η → v.val (zeroIndex d 1) x = 0 := by
    filter_upwards [hv] with x hx hxη
    rw [hx]
    by_cases hxΩ : x ∈ Ω
    · rw [indicator_of_mem hxΩ, image_eq_zero_of_notMem_tsupport hxη, zero_mul]
    · exact indicator_of_notMem hxΩ _
  have hr : restrictSobolev (le_top : Ω ≤ ⊤) v = u := by
    apply sobolev_underlying_injective 𝕜 d Ω 1 p
    apply Lp.ext
    filter_upwards [restrictSobolev_coe (le_top : Ω ≤ ⊤) v (zeroIndex d 1),
      ae_restrict_of_ae hv, ae_restrict_mem Ω.isOpen.measurableSet, hu] with x hx hvx hxΩ hux
    rw [hx, hvx, indicator_of_mem hxΩ]
    by_cases hxK : x ∈ K
    · rw [hηone x hxK, one_mul]
    · rw [hux hxK, mul_zero]
  rw [← hr]
  exact restrict_mem_zeroSpace_of_compact_support hp v (tsupport η) η.hasCompactSupport hη hvη

/-- A continuous localized change of variables preserves the closure-defined
zero-boundary space. C1 chart maps need not carry smooth tests to smooth tests:
compact interior essential support supplies the required approximation instead. -/
theorem localized_pullback_mem_zeroSpace (hp : p ≠ ∞)
    (Λ : Opens (Domain d))
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ Φ x ∈ Λ)
    (θ : Tests 𝕜 (⊤ : Opens (Domain d))) (hθ : tsupport θ ⊆ Φ.source)
    (F : SpaceValue 𝕜 d Λ 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p)
    (hF : ∀ (u : SpaceValue 𝕜 d Λ 1 p) (f : Domain d → 𝕜),
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (Λ : Set (Domain d))] f →
      (F u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        fun x => θ x * f (Φ x))
    (u : SpaceValue 𝕜 d Λ 1 p) (hu : u ∈ ZeroSpaceValue 𝕜 d Λ 1 p hp) :
    F u ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp := by
  have hclosed : IsClosed {w : SpaceValue 𝕜 d Λ 1 p |
      F w ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp} :=
    (smoothSubmodule 𝕜 d Ω 1 p).isClosed_topologicalClosure.preimage F.continuous
  have hsmooth : (smoothSubmodule 𝕜 d Λ 1 p : Set _) ⊆
      {w | F w ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp} := by
    rintro w ⟨φ, hw⟩
    let K : Set (Domain d) := tsupport θ ∩ Φ ⁻¹' tsupport φ
    have hKclosed : IsClosed K :=
      (Φ.continuousOn.mono hθ).preimage_isClosed_of_isClosed
        (isClosed_tsupport θ) (isClosed_tsupport φ)
    have hK : IsCompact K := θ.hasCompactSupport.of_isClosed_subset hKclosed inter_subset_left
    have hKΩ : K ⊆ Ω := by
      rintro x ⟨hxθ, hxφ⟩
      exact (hside x (hθ hxθ)).mpr (φ.tsupport_subset hxφ)
    apply mem_zeroSpace_of_compact_support hp (F w) K hK hKΩ
    filter_upwards [hF w φ hw] with x hx hxK
    rw [hx]
    by_cases hxθ : x ∈ tsupport θ
    · have hxφ : Φ x ∉ tsupport φ := fun hh => hxK ⟨hxθ, hh⟩
      rw [image_eq_zero_of_notMem_tsupport hxφ, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hxθ, zero_mul]
  exact (closure_minimal hsmooth hclosed) hu

/-- The accepted C1 Sobolev pullback and artificial-edge zero extension give
an actual continuous localized transport from the target domain to the source. -/
theorem exists_localized_chart_pullback
    (Λ : Opens (Domain d))
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (J : ℝ) (hJ1 : 1 ≤ J) (hJ : ∀ x ∈ Φ.target, |(fderiv ℝ Φ.symm x).det| ≤ J)
    (hTarget : Bornology.IsBounded Φ.target)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ Φ x ∈ Λ)
    (θ : Tests 𝕜 (⊤ : Opens (Domain d))) (hθ : tsupport θ ⊆ Φ.source) :
    ∃ F : SpaceValue 𝕜 d Λ 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p,
      ∀ (u : SpaceValue 𝕜 d Λ 1 p) (f : Domain d → 𝕜),
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (Λ : Set (Domain d))] f →
      (F u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        fun x => θ x * f (Φ x) := by
  let V := Transport.chartPreimage Φ Λ
  let W := Transport.chartTarget Φ Λ
  have hVΩ : V ≤ Ω := fun x hx => (hside x hx.1).mpr hx.2
  let K : Set (Domain d) := tsupport θ ∩ (Ω : Set (Domain d))
  have hKclosed : IsClosed (K ∪ (Ω : Set (Domain d))ᶜ) := by
    have heq : K ∪ (Ω : Set (Domain d))ᶜ = tsupport θ ∪ (Ω : Set (Domain d))ᶜ := by
      ext x
      simp only [K, mem_union, mem_inter_iff, mem_compl_iff]
      tauto
    rw [heq]
    exact (isClosed_tsupport θ).union Ω.isOpen.isClosed_compl
  have hKV : K ⊆ V := fun x hx => ⟨hθ hx.1, (hside x (hθ hx.1)).mp hx.2⟩
  have hθK : (V : Set (Domain d)) ∩ tsupport θ ⊆ K :=
    fun x hx => ⟨hx.2, hVΩ hx.1⟩
  obtain ⟨C, hC0, hC, hD⟩ := ambient_test_bounds θ
  let M : SpaceValue 𝕜 d V 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p :=
    localizedZeroExtension hVΩ K hKclosed hKV θ θ.contDiff C hC0 hC hD hθK
  let Q : SpaceValue 𝕜 d W 1 p →L[𝕜] SpaceValue 𝕜 d V 1 p :=
    Transport.chartSobolevPull Φ hΦ hInv B hB hB0 J hJ hJ1 Λ hTarget
  let R : SpaceValue 𝕜 d Λ 1 p →L[𝕜] SpaceValue 𝕜 d W 1 p :=
    restrictSobolev (show W ≤ Λ from inter_subset_left)
  refine ⟨M.comp (Q.comp R), ?_⟩
  intro u f hf
  have hr : (R u).val (zeroIndex d 1) =ᵐ[volume.restrict (W : Set (Domain d))] f :=
    (restrictSobolev_coe (show W ≤ Λ from inter_subset_left) u (zeroIndex d 1)).trans
      (hf.filter_mono (ae_mono (Measure.restrict_mono inter_subset_left le_rfl)))
  have hq := Transport.chartSobolevPull_coe Φ hΦ hInv B hB hB0 J hJ hJ1 Λ hTarget
    (R u) f hr.symm
  have hm := localizedZeroExtension_representative hVΩ K hKclosed hKV θ θ.contDiff
    C hC0 hC hD hθK (Q (R u)) (f ∘ Φ) hq.symm
  change (M (Q (R u))).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] _
  filter_upwards [hm, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  rw [hx]
  change (V : Set (Domain d)).indicator (fun y => θ y * f (Φ y)) x = θ x * f (Φ x)
  by_cases hxV : x ∈ V
  · exact indicator_of_mem hxV _
  · rw [indicator_of_notMem hxV]
    have hxθ : x ∉ tsupport θ := fun hh => hxV ⟨hθ hh, (hside x (hθ hh)).mp hxΩ⟩
    rw [image_eq_zero_of_notMem_tsupport hxθ, zero_mul]

/-- The full local reverse step in a bounded C1 boundary chart. A global
Sobolev zero extension yields a member of the original W0 closure after
multiplication by any compact smooth chart cutoff. -/
theorem localized_zeroSpace_of_zero_extension (hp : p ≠ ∞)
    (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (hBinv : ∀ x ∈ Φ.target, ‖fderiv ℝ Φ.symm x‖ ≤ B)
    (hSource : Bornology.IsBounded Φ.source) (hTarget : Bornology.IsBounded Φ.target)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    (θ : Tests 𝕜 (⊤ : Opens (Domain d))) (hθ : tsupport θ ⊆ Φ.source)
    (u : SpaceValue 𝕜 d Ω 1 p) (v : SpaceValue 𝕜 d ⊤ 1 p)
    (hv : v.val (zeroIndex d 1) =ᵐ[volume]
      (Ω : Set (Domain d)).indicator (u.val (zeroIndex d 1))) :
    ∃ w : SpaceValue 𝕜 d Ω 1 p, w ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp ∧
      w.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        fun x => θ x * u.val (zeroIndex d 1) x := by
  obtain ⟨J, hJ1, hJbound⟩ := Transport.exists_det_bound_of_norm_bound (E := Domain d) B
  have hJsrc : ∀ x ∈ Φ.source, |(fderiv ℝ Φ x).det| ≤ J :=
    fun x hx => hJbound _ (hB x hx)
  have hJtgt : ∀ x ∈ Φ.target, |(fderiv ℝ Φ.symm x).det| ≤ J :=
    fun x hx => hJbound _ (hBinv x hx)
  obtain ⟨χ, hχ, hχone⟩ := exists_chart_cutoff Φ θ hθ
  obtain ⟨H, hH⟩ := exists_localized_chart_pullback (p := p) (Ω := (⊤ : Opens (Domain d)))
    ⊤ Φ.symm hInv hΦ B hB0 hBinv J hJ1 hJsrc hSource
    (by intro x hx; simp) χ hχ
  let f : Domain d → 𝕜 := fun y => χ y *
    ((Ω : Set (Domain d)).indicator (u.val (zeroIndex d 1)) (Φ.symm y))
  have hw : (H v).val (zeroIndex d 1) =ᵐ[volume] f := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      hH v ((Ω : Set (Domain d)).indicator (u.val (zeroIndex d 1)))
        (by simpa only [Opens.coe_top, Measure.restrict_univ] using hv)
  have hwcomp : ∀ᵐ y ∂volume, y ∉ tsupport χ → (H v).val (zeroIndex d 1) y = 0 := by
    filter_upwards [hw] with y hy hyχ
    rw [hy]
    dsimp [f]
    rw [image_eq_zero_of_notMem_tsupport hyχ, zero_mul]
  have hwupper : ∀ᵐ y ∂volume, y i < 0 → (H v).val (zeroIndex d 1) y = 0 := by
    filter_upwards [hw] with y hy hyneg
    rw [hy]
    dsimp [f]
    by_cases hyχ : y ∈ tsupport χ
    · have hyt : y ∈ Φ.target := hχ hyχ
      have hnot : Φ.symm y ∉ Ω := by
        intro hyΩ
        have hpos := (hside (Φ.symm y) (Φ.map_target hyt)).mp hyΩ
        rw [Φ.right_inv hyt] at hpos
        exact (not_lt_of_ge (le_of_lt hyneg)) hpos
      rw [indicator_of_notMem hnot, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hyχ, zero_mul]
  let z := restrictSobolev (le_top : upper i ≤ ⊤) (H v)
  have hz : z ∈ ZeroSpaceValue 𝕜 d (upper i) 1 p hp :=
    upper_restrict_mem_zeroSpace_of_compact_support hp i (H v) (tsupport χ)
      χ.hasCompactSupport hwcomp hwupper
  have hzf : z.val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))] f :=
    (restrictSobolev_coe (le_top : upper i ≤ ⊤) (H v) (zeroIndex d 1)).trans
      (ae_restrict_of_ae hw)
  obtain ⟨F, hF⟩ := exists_localized_chart_pullback (p := p) (upper i) Φ hΦ hInv B hB0 hB
    J hJ1 hJtgt hTarget hside θ hθ
  refine ⟨F z, localized_pullback_mem_zeroSpace hp (upper i) Φ hside θ hθ F hF z hz, ?_⟩
  filter_upwards [hF z f hzf, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  rw [hx]
  by_cases hxθ : x ∈ tsupport θ
  · have hxs : x ∈ Φ.source := hθ hxθ
    dsimp [f]
    rw [hχone x hxθ, one_mul, Φ.left_inv hxs, indicator_of_mem hxΩ]
  · rw [image_eq_zero_of_notMem_tsupport hxθ, zero_mul, zero_mul]

/-- The full C1 reverse characterization, with the original compact-test
closure and the original hypotheses. Finite chart localization combines the
flat inward-translation argument with the compact interior piece. -/
theorem zeroSpace_of_hasSobolevZeroExtension (hp : p ≠ ∞)
    (hΩ : IsC1Domain Ω) (hb : Bornology.IsBounded (Ω : Set (Domain d)))
    (u : SpaceValue 𝕜 d Ω 1 p) (hu : HasSobolevZeroExtension u) :
    u ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp := by
  classical
  obtain ⟨v, hv⟩ := hu
  have hcompact : IsCompact (frontier (Ω : Set (Domain d))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨n, i, Φ, B, hB0, hcharts, hcover⟩ :=
    finite_bounded_boundary_charts d Ω hΩ hcompact
  obtain ⟨a, S, C, ha, hC0, hC, hD, hsum, hsupp, hSc, hSΩ, hS⟩ :=
    finite_scalar_boundary_localization (𝕜 := 𝕜) Ω (fun j => (Φ j).source)
      (fun j => (Φ j).open_source) hcover hcompact
  have hpiece (k : Option (Fin n)) :
      ∃ w : SpaceValue 𝕜 d Ω 1 p, w ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp ∧
        w.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
          fun x => a k x * u.val (zeroIndex d 1) x := by
    cases k with
    | none =>
      let w := ambientMultiply (a none) (ha none) C hC0 (hC none) (hD none) u
      let K : Set (Domain d) := closure (Ω : Set (Domain d)) ∩ tsupport (a none)
      have hK : IsCompact K := hb.isCompact_closure.inter_right (isClosed_tsupport _)
      have hKΩ : K ⊆ Ω := hS.trans hSΩ
      have hw := ambientMultiply_coe (a none) (ha none) C hC0 (hC none) (hD none) u
      refine ⟨w, mem_zeroSpace_of_compact_support hp w K hK hKΩ ?_, hw⟩
      filter_upwards [hw, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ hxK
      rw [hx]
      have hxnone : x ∉ tsupport (a none) := fun hh => hxK ⟨subset_closure hxΩ, hh⟩
      rw [image_eq_zero_of_notMem_tsupport hxnone, zero_mul]
    | some j =>
      let θ : Tests 𝕜 (⊤ : Opens (Domain d)) :=
        ⟨a (some j), ha (some j), (hsupp j).1, by simp⟩
      obtain ⟨hΦ, hInv, hbsource, hbtarget, hside, hder, hderInv⟩ := hcharts j
      exact localized_zeroSpace_of_zero_extension hp (i j) (Φ j) hΦ hInv B hB0
        hder hderInv hbsource hbtarget hside θ (hsupp j).2 u v hv
  choose w hw hrep using hpiece
  have hsum_mem : (∑ k, w k) ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp :=
    Submodule.sum_mem _ (fun k _ => hw k)
  have heq : (∑ k, w k) = u := by
    apply sobolev_underlying_injective 𝕜 d Ω 1 p
    apply Lp.ext
    let P : SpaceValue 𝕜 d Ω 1 p →ₗ[𝕜] DomainLp 𝕜 Ω p :=
      (PiLp.projₗ 1 _ (zeroIndex d 1)).comp (derivativeGraph 𝕜 Ω 1 p).subtype
    have hproj : (∑ k, w k).val (zeroIndex d 1) = ∑ k, (w k).val (zeroIndex d 1) :=
      map_sum P w Finset.univ
    change (∑ k, w k).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      u.val (zeroIndex d 1)
    rw [hproj]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun k => (w k).val (zeroIndex d 1)),
      ae_all_iff.mpr hrep] with x hx hk
    rw [hx]
    simp only [Finset.sum_apply, hk]
    rw [← Finset.sum_mul]
    have hsumx : ∑ k, a k x = 1 := by simpa only [Fintype.sum_option] using hsum x
    rw [hsumx, one_mul]
  simpa only [heq] using hsum_mem

/-- On bounded C1 domains, existence of a Sobolev zero extension is
precisely membership in the paper's closure-defined zero-boundary space. -/
theorem hasSobolevZeroExtension_iff_mem_zeroSpace (hp : p ≠ ∞)
    (hΩ : IsC1Domain Ω) (hb : Bornology.IsBounded (Ω : Set (Domain d)))
    (u : SpaceValue 𝕜 d Ω 1 p) :
    HasSobolevZeroExtension u ↔ u ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp := by
  constructor
  · exact zeroSpace_of_hasSobolevZeroExtension hp hΩ hb u
  · intro hu
    obtain ⟨v, hv, hnorm⟩ := zero_extension_of_zeroSpace 𝕜 d Ω 1 p hp u hu
    exact ⟨v, hv (zeroIndex d 1)⟩

end ExpandedFA.Sobolev.Trace


noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace ExpandedFA.Sobolev.Trace
open ExpandedFA.Distributions
open Lines HalfSpace
/-- Jensen's power inequality on a unit interval, derived from Hölder. -/
lemma lintegral_enorm_unit_rpow_le {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (hf : Continuous f) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ t, ‖f t‖ₑ ∂(volume.restrict (Ioc (0 : ℝ) 1))) ^ p ≤
      ∫⁻ t, ‖f t‖ₑ ^ p ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have : IsProbabilityMeasure μ := by
    constructor
    simp [μ, Real.volume_Ioc]
  have h := eLpNorm'_le_eLpNorm'_of_exponent_le (by norm_num : (0 : ℝ) < 1) hp μ
    (hf.aestronglyMeasurable (μ := μ))
  simp only [eLpNorm'_eq_lintegral_enorm, ENNReal.rpow_one, div_one] at h
  have h' := ENNReal.rpow_le_rpow h (le_trans zero_le_one hp)
  simpa only [← ENNReal.rpow_mul, one_div_mul_cancel (by linarith : p ≠ 0),
    ENNReal.rpow_one] using h'

/-- Unit-normal-segment finite-power trace bound, with the valid endpoint p=1. -/
lemma enorm_left_endpoint_rpow_le_lintegrals {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (hf : ContDiff ℝ 1 f)
    {p : ℝ} (hp : 1 ≤ p) :
    ‖f 0‖ₑ ^ p ≤ (2 : ℝ≥0∞) ^ (p - 1) *
      ((∫⁻ t, ‖f t‖ₑ ^ p ∂(volume.restrict (Ioc (0 : ℝ) 1))) +
      ∫⁻ t, ‖deriv f t‖ₑ ^ p ∂(volume.restrict (Ioc (0 : ℝ) 1))) := by
  calc
    ‖f 0‖ₑ ^ p ≤ ((∫⁻ t, ‖f t‖ₑ ∂(volume.restrict (Ioc (0 : ℝ) 1))) +
        ∫⁻ t, ‖deriv f t‖ₑ ∂(volume.restrict (Ioc (0 : ℝ) 1))) ^ p :=
      ENNReal.rpow_le_rpow (enorm_left_endpoint_le_lintegrals f hf) (by linarith)
    _ ≤ (2 : ℝ≥0∞) ^ (p - 1) *
        (((∫⁻ t, ‖f t‖ₑ ∂(volume.restrict (Ioc (0 : ℝ) 1)))) ^ p +
        (∫⁻ t, ‖deriv f t‖ₑ ∂(volume.restrict (Ioc (0 : ℝ) 1))) ^ p) :=
      ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp
    _ ≤ _ := by
      gcongr
      · exact lintegral_enorm_unit_rpow_le f hf.continuous hp
      · exact lintegral_enorm_unit_rpow_le (deriv f) hf.continuous_deriv_one hp

/-- The flat unit-slab trace bound for every finite real exponent p≥1.
The target may be any real Banach space, in particular ℝ or ℂ. -/
lemma flat_unit_slab_lintegral_rpow_bound {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure X)
    (f g : X × ℝ → E) (hf : Measurable f) (hg : Measurable g)
    (hfC1 : ∀ x, ContDiff ℝ 1 (fun t => f (x, t)))
    (hderiv : ∀ x, deriv (fun t => f (x, t)) = fun t => g (x, t))
    {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, ‖f (x, 0)‖ₑ ^ p ∂μ) ≤ (2 : ℝ≥0∞) ^ (p - 1) *
      ((∫⁻ z, ‖f z‖ₑ ^ p ∂μ.prod (volume.restrict (Ioc (0 : ℝ) 1))) +
      ∫⁻ z, ‖g z‖ₑ ^ p ∂μ.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  calc
    (∫⁻ x, ‖f (x, 0)‖ₑ ^ p ∂μ) ≤
        ∫⁻ x, (2 : ℝ≥0∞) ^ (p - 1) *
          ((∫⁻ t, ‖f (x, t)‖ₑ ^ p ∂(volume.restrict (Ioc (0 : ℝ) 1))) +
          ∫⁻ t, ‖g (x, t)‖ₑ ^ p ∂(volume.restrict (Ioc (0 : ℝ) 1))) ∂μ := by
      apply lintegral_mono
      intro x
      simpa only [hderiv x] using
        enorm_left_endpoint_rpow_le_lintegrals (fun t => f (x, t)) (hfC1 x) hp
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by finiteness)]
      rw [lintegral_add_left (hf.enorm.pow_const p).lintegral_prod_right']
      rw [← lintegral_prod _ (hf.enorm.pow_const p).aemeasurable,
        ← lintegral_prod _ (hg.enorm.pow_const p).aemeasurable]


/-- Unsplit normal/transverse coordinates preserve ambient Lebesgue volume. -/
lemma coordinateUnsplit_measurePreserving {d : ℕ} (i : Fin d) :
    MeasurePreserving (fun z : Transverse i × ℝ => coordinateLine i z.1 z.2)
      (volume.prod volume) volume := by
  have h := ((coordinateEquiv_measurePreserving i).symm (coordinateEquiv i)).comp
    (Measure.measurePreserving_swap (μ := (volume : Measure (Transverse i)))
      (ν := (volume : Measure ℝ)))
  simpa only [Function.comp_def, Prod.swap, coordinateEquiv_symm_apply] using h

/-- Integration over the unit normal slab is bounded by integration over the
actual coordinate upper half-space. -/
lemma coordinate_slab_lintegral_le_upper {d : ℕ} (i : Fin d)
    (F : Domain d → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z : Transverse i × ℝ, F (coordinateLine i z.1 z.2)
      ∂(volume.prod (volume.restrict (Ioc (0 : ℝ) 1)))) ≤
      ∫⁻ x in (upper i : Set (Domain d)), F x := by
  calc
    _ ≤ ∫⁻ z : Transverse i × ℝ, F (coordinateLine i z.1 z.2)
        ∂(volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
      exact lintegral_mono' (Measure.prod_mono le_rfl
        (Measure.restrict_mono_set volume fun _ ht => ht.1)) le_rfl
    _ = _ := by
      have hpre : (fun z : Transverse i × ℝ => coordinateLine i z.1 z.2) ⁻¹'
          (upper i : Set (Domain d)) = univ ×ˢ Ioi (0 : ℝ) := by
        ext z
        simp [upper]
      have hm := (coordinateUnsplit_measurePreserving i).setLIntegral_comp_preimage
        (upper i).isOpen.measurableSet hF
      rw [hpre, ← Measure.prod_restrict, Measure.restrict_univ] at hm
      exact hm

/-- The actual finite-power trace estimate on a coordinate upper half-space,
for an ambient C1 Banach-valued function and its actual coordinate derivative. -/
lemma coordinate_upper_trace_lintegral_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {d : ℕ} (i : Fin d) (f : Domain d → E) (hf : ContDiff ℝ 1 f)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ y : Transverse i, ‖f (coordinateLine i y 0)‖ₑ ^ p) ≤
      (2 : ℝ≥0∞) ^ (p - 1) *
        ((∫⁻ x in (upper i : Set (Domain d)), ‖f x‖ₑ ^ p) +
        ∫⁻ x in (upper i : Set (Domain d)),
          ‖fderiv ℝ f x (coordinateVector i)‖ₑ ^ p) := by
  let e : Transverse i × ℝ → Domain d := fun z => coordinateLine i z.1 z.2
  have he : Measurable e :=
    (coordinateUnsplit_measurePreserving i).measurable
  have hd : Continuous (fun x => fderiv ℝ f x (coordinateVector i)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h := flat_unit_slab_lintegral_rpow_bound volume (f ∘ e)
    ((fun x => fderiv ℝ f x (coordinateVector i)) ∘ e)
    (hf.continuous.measurable.comp he) (hd.measurable.comp he)
    (fun y => hf.comp ((coordinateLine_contDiff i y).of_le (by simp)))
    (fun y => funext fun t =>
      ((hf.differentiable_one _).hasFDerivAt.comp_hasDerivAt t
        (coordinateLine_hasDerivAt i y t)).deriv) hp
  refine h.trans ?_
  dsimp only [Function.comp_def, e]
  gcongr
  · exact coordinate_slab_lintegral_le_upper i _ (hf.continuous.measurable.enorm.pow_const p)
  · exact coordinate_slab_lintegral_le_upper i _ (hd.measurable.enorm.pow_const p)


/-- Numerical passage from a p-th-power bound to a convenient linear norm bound. -/
lemma rpow_root_trace_bound {A B D : ℝ≥0∞} {p : ℝ} (hp : 1 ≤ p)
    (h : A ≤ (2 : ℝ≥0∞) ^ (p - 1) * (B + D)) :
    A ^ (1 / p) ≤ 2 * (B ^ (1 / p) + D ^ (1 / p)) := by
  have hp0 : 0 < p := by linarith
  have hi0 : 0 ≤ 1 / p := by positivity
  have hi1 : 1 / p ≤ 1 := by rw [div_le_iff₀ hp0]; linarith
  calc
    A ^ (1 / p) ≤ ((2 : ℝ≥0∞) ^ (p - 1) * (B + D)) ^ (1 / p) :=
      ENNReal.rpow_le_rpow h hi0
    _ = (2 : ℝ≥0∞) ^ ((p - 1) * (1 / p)) * (B + D) ^ (1 / p) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hi0, ← ENNReal.rpow_mul]
    _ ≤ 2 * (B ^ (1 / p) + D ^ (1 / p)) := by
      apply mul_le_mul
      · calc
          (2 : ℝ≥0∞) ^ ((p - 1) * (1 / p)) ≤ (2 : ℝ≥0∞) ^ (1 : ℝ) := by
            apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
            rw [one_div, ← div_eq_mul_inv, div_le_iff₀ hp0]
            linarith
          _ = _ := ENNReal.rpow_one _
      · exact ENNReal.rpow_add_le_add_rpow _ _ hi0 hi1
      · positivity
      · positivity

/-- Flat half-space trace estimate in the same finite exponent eLpNorm used
by the manuscript Sobolev graph. -/
lemma coordinate_upper_trace_eLpNorm_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {d : ℕ} (i : Fin d) (f : Domain d → E) (hf : ContDiff ℝ 1 f)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) :
    eLpNorm (fun y : Transverse i => f (coordinateLine i y 0)) p volume ≤
      2 * (eLpNorm f p (volume.restrict (upper i : Set (Domain d))) +
        eLpNorm (fun x => fderiv ℝ f x (coordinateVector i)) p
          (volume.restrict (upper i : Set (Domain d)))) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)
  have hpR : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp hp1
  have hc : Continuous (fun y : Transverse i => f (coordinateLine i y 0)) := by
    apply hf.continuous.comp
    apply continuous_pi
    intro j
    dsimp [coordinateLine]
    split_ifs
    · exact continuous_const
    · exact continuous_apply _
  have hd : Continuous (fun x => fderiv ℝ f x (coordinateVector i)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  rw [eLpNorm_eq_eLpNorm' hp0 hp hc.aestronglyMeasurable,
    eLpNorm_eq_eLpNorm' hp0 hp hf.continuous.aestronglyMeasurable,
    eLpNorm_eq_eLpNorm' hp0 hp hd.aestronglyMeasurable]
  simp only [eLpNorm'_eq_lintegral_enorm]
  exact rpow_root_trace_bound hpR (coordinate_upper_trace_lintegral_bound i f hf hpR)


section FlatTraceConstruction
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

section C1BoundaryRepresentatives
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
  (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Sobolev graph members with an ambient C1 representative. -/
def c1BoundarySubmodule : Submodule 𝕜 (SpaceValue 𝕜 d Ω 1 p) where
  carrier := {u | ∃ f : Domain d → 𝕜, ContDiff ℝ 1 f ∧
    u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f}
  zero_mem' := by
    refine ⟨0, contDiff_const, ?_⟩
    exact Lp.coeFn_zero 𝕜 p (volume.restrict (Ω : Set (Domain d)))
  add_mem' := by
    rintro u v ⟨f, hf, hu⟩ ⟨g, hg, hv⟩
    refine ⟨f + g, hf.add hg, ?_⟩
    filter_upwards [Lp.coeFn_add (u.val (zeroIndex d 1)) (v.val (zeroIndex d 1)), hu, hv]
      with x hx hux hvx
    change ((u.val (zeroIndex d 1) + v.val (zeroIndex d 1)) : DomainLp 𝕜 Ω p) x = _
    rw [hx]
    exact congrArg₂ (· + ·) hux hvx
  smul_mem' := by
    rintro c u ⟨f, hf, hu⟩
    refine ⟨c • f, contDiff_const.smul hf, ?_⟩
    filter_upwards [Lp.coeFn_smul c (u.val (zeroIndex d 1)), hu] with x hx hux
    change (c • u.val (zeroIndex d 1) : DomainLp 𝕜 Ω p) x = _
    rw [hx]
    exact congrArg (c • ·) hux

def c1BoundaryRepresentative (u : c1BoundarySubmodule (𝕜 := 𝕜) Ω p) : Domain d → 𝕜 :=
  Classical.choose u.property

lemma c1BoundaryRepresentative_contDiff (u : c1BoundarySubmodule (𝕜 := 𝕜) Ω p) :
    ContDiff ℝ 1 (c1BoundaryRepresentative Ω p u) :=
  (Classical.choose_spec u.property).1

lemma c1BoundaryRepresentative_ae (u : c1BoundarySubmodule (𝕜 := 𝕜) Ω p) :
    u.val.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      c1BoundaryRepresentative Ω p u :=
  (Classical.choose_spec u.property).2
end C1BoundaryRepresentatives

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (i : Fin d)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Smooth a.e. equality inside the upper half-space determines every
pointwise boundary value. -/
lemma coordinate_boundary_eq_of_ae (f g : Domain d → 𝕜)
    (hf : Continuous f) (hg : Continuous g)
    (hfg : f =ᵐ[volume.restrict (upper i : Set (Domain d))] g) :
    ∀ y : Transverse i, f (coordinateLine i y 0) = g (coordinateLine i y 0) := by
  have heq : EqOn f g (upper i : Set (Domain d)) :=
    Measure.eqOn_open_of_ae_eq hfg (upper i).isOpen hf.continuousOn hg.continuousOn
  intro y
  apply heq.closure hf hg
  apply map_mem_closure (coordinateLine_contDiff i y).continuous
    (show (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) by simp [closure_Ioi])
  intro t ht
  simpa [upper] using ht

/-- Ambient smooth restrictions are dense in the actual half-space graph,
using the accepted reflection extension and whole-space smooth density. -/
lemma coordinate_upper_smooth_density (hp : p ≠ ∞) :
    Dense (C1Extension.SmoothUpToBoundary (𝕜 := 𝕜) (upper i) p) := by
  obtain ⟨E, _, hE, _⟩ := halfSpace_extension 𝕜 d i p
  exact C1Extension.smooth_up_to_boundary_density_of_extension 𝕜 d (upper i) p hp E hE

/-- The boundary restriction of each smooth graph member belongs to Lp;
its norm is bounded solely by the given Sobolev graph norm. -/
lemma coordinate_upper_c1_trace_bound (hp : p ≠ ∞)
    (u : SpaceValue 𝕜 d (upper i) 1 p) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ 1 f)
    (hu : u.val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))] f) :
    MemLp (fun y : Transverse i => f (coordinateLine i y 0)) p volume ∧
      (eLpNorm (fun y : Transverse i => f (coordinateLine i y 0)) p volume).toReal ≤
        4 * ‖u‖ := by
  have hf1 : ContDiff ℝ 1 f := hf
  have hd := C1Extension.Classical.c1_representative_derivative u f hf1.contDiffOn hu i
  have h := coordinate_upper_trace_eLpNorm_bound i f hf1 Fact.out hp
  rw [← eLpNorm_congr_ae hu, ← eLpNorm_congr_ae hd] at h
  have hfin : 2 * (eLpNorm (u.val (zeroIndex d 1)) p
      (volume.restrict (upper i : Set (Domain d))) +
      eLpNorm (u.val (coordinateIndex i)) p
      (volume.restrict (upper i : Set (Domain d)))) < ∞ := by finiteness
  have hc : Continuous (fun y : Transverse i => f (coordinateLine i y 0)) := by
    apply hf.continuous.comp
    apply continuous_pi
    intro j
    dsimp [coordinateLine]
    split_ifs
    · exact continuous_const
    · exact continuous_apply _
  refine ⟨lt_of_le_of_lt h hfin, ?_⟩
  have hr := ENNReal.toReal_mono hfin.ne h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_add
    (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _), ← Lp.norm_def, ← Lp.norm_def] at hr
  exact hr.trans (by
    have hzero := PiLp.norm_apply_le u.val (zeroIndex d 1)
    have hnormal := PiLp.norm_apply_le u.val (coordinateIndex i)
    change _ ≤ 4 * ‖u.val‖
    linarith)

/-- The actual flat-boundary Lp restriction on the existing smooth submodule. -/
def coordinateC1Trace (hp : p ≠ ∞)
    (u : c1BoundarySubmodule (𝕜 := 𝕜) (upper i) p) : Lp 𝕜 p (volume : Measure (Transverse i)) :=
  ((coordinate_upper_c1_trace_bound i hp u.val _
    (c1BoundaryRepresentative_contDiff (upper i) p u)
    (c1BoundaryRepresentative_ae (upper i) p u)).1).toLp _

lemma coordinateC1Trace_coe (hp : p ≠ ∞)
    (u : c1BoundarySubmodule (𝕜 := 𝕜) (upper i) p)
    (f : Domain d → 𝕜) (hf : ContDiff ℝ 1 f)
    (hu : u.val.val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))] f) :
    coordinateC1Trace i hp u =ᵐ[volume]
      fun y : Transverse i => f (coordinateLine i y 0) := by
  apply (MemLp.coeFn_toLp _).trans
  exact Filter.Eventually.of_forall (coordinate_boundary_eq_of_ae i _ _
    (c1BoundaryRepresentative_contDiff (upper i) p u).continuous hf.continuous
    ((c1BoundaryRepresentative_ae (upper i) p u).symm.trans hu))

/-- The transverse restriction is scalar-linear, with no trace certificate assumed. -/
def coordinateC1TraceLM (hp : p ≠ ∞) :
    c1BoundarySubmodule (𝕜 := 𝕜) (upper i) p →ₗ[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i)) where
  toFun := coordinateC1Trace i hp
  map_add' u v := by
    let f := c1BoundaryRepresentative (upper i) p u
    let g := c1BoundaryRepresentative (upper i) p v
    have hf := c1BoundaryRepresentative_contDiff (upper i) p u
    have hg := c1BoundaryRepresentative_contDiff (upper i) p v
    have hu := c1BoundaryRepresentative_ae (upper i) p u
    have hv := c1BoundaryRepresentative_ae (upper i) p v
    have huv : (u + v).val.val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        f + g := by
      filter_upwards [Lp.coeFn_add (u.val.val (zeroIndex d 1))
        (v.val.val (zeroIndex d 1)), hu, hv] with x hx hux hvx
      change ((u.val.val (zeroIndex d 1) + v.val.val (zeroIndex d 1)) : DomainLp 𝕜 (upper i) p) x = _
      rw [hx]
      exact congrArg₂ (· + ·) hux hvx
    apply Lp.ext
    filter_upwards [coordinateC1Trace_coe i hp (u + v) (f + g) (hf.add hg) huv,
      Lp.coeFn_add (coordinateC1Trace i hp u) (coordinateC1Trace i hp v),
      coordinateC1Trace_coe i hp u f hf hu,
      coordinateC1Trace_coe i hp v g hg hv] with y hy hadd huy hvy
    rw [hy, hadd]
    exact (congrArg₂ (· + ·) huy hvy).symm
  map_smul' c u := by
    let f := c1BoundaryRepresentative (upper i) p u
    have hf := c1BoundaryRepresentative_contDiff (upper i) p u
    have hu := c1BoundaryRepresentative_ae (upper i) p u
    have hcu : (c • u).val.val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        c • f := by
      filter_upwards [Lp.coeFn_smul c (u.val.val (zeroIndex d 1)), hu] with x hx hux
      change (c • u.val.val (zeroIndex d 1) : DomainLp 𝕜 (upper i) p) x = _
      rw [hx]
      exact congrArg (c • ·) hux
    apply Lp.ext
    filter_upwards [coordinateC1Trace_coe i hp (c • u) (c • f)
      (contDiff_const.smul hf) hcu,
      Lp.coeFn_smul c (coordinateC1Trace i hp u),
      coordinateC1Trace_coe i hp u f hf hu] with y hy hsmul huy
    change _ = (c • coordinateC1Trace i hp u : Lp 𝕜 p (volume : Measure (Transverse i))) y
    rw [hy, hsmul]
    exact (congrArg (c • ·) huy).symm

end FlatTraceConstruction


/-- Reindexing the transverse coordinates gives the usual Fin n coordinates. -/
def transverseFinEquiv {n : ℕ} (i : Fin (n + 1)) :
    Domain n ≃ᵐ Transverse i :=
  MeasurableEquiv.piCongrLeft (fun _ : {j : Fin (n + 1) // j ≠ i} => ℝ)
    (finSuccAboveEquiv i)

lemma transverseFinEquiv_measurePreserving {n : ℕ} (i : Fin (n + 1)) :
    MeasurePreserving (transverseFinEquiv i) volume volume :=
  volume_measurePreserving_piCongrLeft _ _

lemma coordinateLine_transverseFinEquiv {n : ℕ} (i : Fin (n + 1)) (z : Domain n) (t : ℝ) :
    coordinateLine i (transverseFinEquiv i z) t = i.insertNth t z := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp
  · simp [coordinateLine, transverseFinEquiv, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply, ← finSuccAboveEquiv_apply]

/-- The flat numerical estimate in the Fin n boundary coordinates used by
C1 graph charts. -/
lemma coordinate_upper_insertNth_eLpNorm_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ} (i : Fin (n + 1)) (f : Domain (n + 1) → E) (hf : ContDiff ℝ 1 f)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) :
    eLpNorm (fun z : Domain n => f (i.insertNth 0 z)) p volume ≤
      2 * (eLpNorm f p (volume.restrict (upper i : Set (Domain (n + 1)))) +
        eLpNorm (fun x => fderiv ℝ f x (coordinateVector i)) p
          (volume.restrict (upper i : Set (Domain (n + 1))))) := by
  have hc : Continuous (fun y : Transverse i => f (coordinateLine i y 0)) := by
    apply hf.continuous.comp
    apply continuous_pi
    intro j
    dsimp [coordinateLine]
    split_ifs
    · exact continuous_const
    · exact continuous_apply _
  have he := eLpNorm_comp_measurePreserving (p := p) hc.aestronglyMeasurable
    (transverseFinEquiv_measurePreserving i)
  have hf' : (fun y : Transverse i => f (coordinateLine i y 0)) ∘ transverseFinEquiv i =
      fun z : Domain n => f (i.insertNth 0 z) := by
    funext z
    simp only [Function.comp_apply, coordinateLine_transverseFinEquiv]
  rw [hf'] at he
  rw [he]
  exact coordinate_upper_trace_eLpNorm_bound i f hf hp1 hp


section CoordinateC1TraceExistence
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (i : Fin d)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma coordinate_upper_c1_density (hp : p ≠ ∞) :
    Dense (c1BoundarySubmodule (𝕜 := 𝕜) (upper i) p : Set (SpaceValue 𝕜 d (upper i) 1 p)) := by
  apply (coordinate_upper_smooth_density (𝕜 := 𝕜) i hp).mono
  rintro u ⟨f, hf, hu⟩
  exact ⟨f, hf.of_le (by simp), hu⟩

/-- A genuine half-space trace agrees with every ambient C1 representative. -/
def IsCoordinateTrace
    (T : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] Lp 𝕜 p (volume : Measure (Transverse i))) : Prop :=
  ∀ (u : SpaceValue 𝕜 d (upper i) 1 p) (f : Domain d → 𝕜),
    ContDiff ℝ 1 f →
    u.val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))] f →
    T u =ᵐ[volume] fun y : Transverse i => f (coordinateLine i y 0)

/-- The actual trace on a coordinate upper half-space exists uniquely for
both scalar fields and every finite p≥1, and agrees for global C1 data. -/
theorem coordinate_upper_trace_exists (hp : p ≠ ∞) :
    ∃! T : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i)), IsCoordinateTrace i T := by
  let L := coordinateC1TraceLM (𝕜 := 𝕜) i hp
  let e := (c1BoundarySubmodule (𝕜 := 𝕜) (upper i) p).subtype
  have hd : DenseRange e := by
    change Dense (Set.range ((↑) : c1BoundarySubmodule (𝕜 := 𝕜) (upper i) p →
      SpaceValue 𝕜 d (upper i) 1 p))
    rw [Subtype.range_coe_subtype]
    exact coordinate_upper_c1_density i hp
  have hnorm : ∀ u, ‖L u‖ ≤ 4 * ‖e u‖ := by
    intro u
    change ‖coordinateC1Trace i hp u‖ ≤ 4 * ‖u.val‖
    rw [coordinateC1Trace, Lp.norm_toLp]
    exact (coordinate_upper_c1_trace_bound i hp u.val _
      (c1BoundaryRepresentative_contDiff (upper i) p u)
      (c1BoundaryRepresentative_ae (upper i) p u)).2
  let T := L.extendOfNorm e
  have hT : IsCoordinateTrace i T := by
    intro u f hf hu
    let v : c1BoundarySubmodule (𝕜 := 𝕜) (upper i) p := ⟨u, f, hf, hu⟩
    change T (e v) =ᵐ[volume] _
    rw [LinearMap.extendOfNorm_eq hd ⟨4, hnorm⟩]
    exact coordinateC1Trace_coe i hp v f hf hu
  refine ⟨T, hT, ?_⟩
  intro S hS
  have heq : EqOn S T (c1BoundarySubmodule (𝕜 := 𝕜) (upper i) p :
      Set (SpaceValue 𝕜 d (upper i) 1 p)) := by
    rintro u ⟨f, hf, hu⟩
    exact Lp.ext ((hS u f hf hu).trans (hT u f hf hu).symm)
  apply ContinuousLinearMap.ext
  intro u
  exact heq.closure S.continuous T.continuous (coordinate_upper_c1_density i hp u)

/-- Quantitative boundary bound for an actual C1 representative of the graph. -/
lemma coordinate_upper_c1_trace_enorm_bound (hp : p ≠ ∞)
    (u : SpaceValue 𝕜 d (upper i) 1 p) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ 1 f)
    (hu : u.val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))] f) :
    eLpNorm (fun y : Transverse i => f (coordinateLine i y 0)) p volume ≤
      ENNReal.ofReal (4 * ‖u‖) := by
  have h := coordinate_upper_c1_trace_bound i hp u f hf hu
  rw [← ENNReal.ofReal_toReal h.1.ne]
  exact ENNReal.ofReal_le_ofReal h.2

/-- The C1 Sobolev graph bound in the finite-coordinate boundary parametrization. -/
lemma coordinate_upper_insertNth_c1_trace_bound {n : ℕ} (j : Fin (n + 1))
    (hp : p ≠ ∞) (u : SpaceValue 𝕜 (n + 1) (upper j) 1 p)
    (f : Domain (n + 1) → 𝕜) (hf : ContDiff ℝ 1 f)
    (hu : u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (upper j : Set (Domain (n + 1)))] f) :
    eLpNorm (fun z : Domain n => f (j.insertNth 0 z)) p volume ≤
      ENNReal.ofReal (4 * ‖u‖) := by
  have hc : Continuous (fun y : Transverse j => f (coordinateLine j y 0)) := by
    apply hf.continuous.comp
    apply continuous_pi
    intro k
    dsimp [coordinateLine]
    split_ifs
    · exact continuous_const
    · exact continuous_apply _
  have he := eLpNorm_comp_measurePreserving (p := p) hc.aestronglyMeasurable
    (transverseFinEquiv_measurePreserving j)
  have hf' : (fun y : Transverse j => f (coordinateLine j y 0)) ∘ transverseFinEquiv j =
      fun z : Domain n => f (j.insertNth 0 z) := by
    funext z
    simp only [Function.comp_apply, coordinateLine_transverseFinEquiv]
  rw [hf'] at he
  rw [he]
  exact coordinate_upper_c1_trace_enorm_bound j hp u f hf hu

end CoordinateC1TraceExistence

end ExpandedFA.Sobolev.Trace


namespace ExpandedFA.Sobolev.Trace
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open C1Extension Lines HalfSpace

section BoundedLpMultiplier
variable {𝕜 : Type} [RCLike 𝕜] {X : Type*} [MeasurableSpace X]
  (μ : Measure X) {p : ℝ≥0∞} [Fact (1 ≤ p)]
  (a : X → 𝕜) (ha : AEStronglyMeasurable a μ) (C : ℝ) (hC : ∀ x, ‖a x‖ ≤ C)

def boundedLpMultiply (u : Lp 𝕜 p μ) : Lp 𝕜 p μ :=
  ((Lp.memLp u).of_le_mul (f := fun x => a x * u x) (c := C)
    (ha.mul (Lp.aestronglyMeasurable u))
    (Filter.Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))).toLp _

omit [Fact (1 ≤ p)] in
lemma boundedLpMultiply_coe (u : Lp 𝕜 p μ) :
    boundedLpMultiply μ a ha C hC u =ᵐ[μ] fun x => a x * u x :=
  MemLp.coeFn_toLp _

omit [Fact (1 ≤ p)] in
lemma boundedLpMultiply_norm_le (u : Lp 𝕜 p μ) :
    ‖boundedLpMultiply μ a ha C hC u‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedLpMultiply_coe μ a ha C hC u] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

def boundedLpMultiplyCLM : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ :=
  LinearMap.mkContinuous
    { toFun := boundedLpMultiply μ a ha C hC
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [boundedLpMultiply_coe μ a ha C hC (u + v),
          boundedLpMultiply_coe μ a ha C hC u, boundedLpMultiply_coe μ a ha C hC v,
          Lp.coeFn_add u v,
          Lp.coeFn_add (boundedLpMultiply μ a ha C hC u) (boundedLpMultiply μ a ha C hC v)]
          with x h₁ h₂ h₃ h₄ h₅
        rw [h₁, h₅, h₄]
        simp only [Pi.add_apply, h₂, h₃]
        exact mul_add _ _ _
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [boundedLpMultiply_coe μ a ha C hC (c • u),
          boundedLpMultiply_coe μ a ha C hC u,
          Lp.coeFn_smul c u, Lp.coeFn_smul c (boundedLpMultiply μ a ha C hC u)]
          with x h₁ h₂ h₃ h₄
        change boundedLpMultiply μ a ha C hC (c • u) x =
          (c • boundedLpMultiply μ a ha C hC u) x
        rw [h₁, h₄, h₃]
        simp only [Pi.smul_apply, h₂, smul_eq_mul]
        ring }
    C (boundedLpMultiply_norm_le μ a ha C hC)

lemma boundedLpMultiplyCLM_coe (u : Lp 𝕜 p μ) :
    boundedLpMultiplyCLM μ a ha C hC u =ᵐ[μ] fun x => a x * u x :=
  boundedLpMultiply_coe μ a ha C hC u

end BoundedLpMultiplier

/-- Multiplying an ambient representative also multiplies its boundary trace.
Only the density of ambient smooth restrictions and actual trace agreement are used. -/
lemma trace_ambientMultiply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C)
    (u : SpaceValue 𝕜 d Ω 1 p) :
    T (ambientMultiply a ha C hC0 hC hD u) =ᵐ[surfaceMeasure Ω]
      fun x => a x * T u x := by
  let M := ambientMultiply (Ω := Ω) (p := p) a ha C hC0 hC hD
  let B := boundedLpMultiplyCLM (p := p) (surfaceMeasure Ω) a
    ha.continuous.aestronglyMeasurable C hC
  have heq : EqOn (T.comp M) (B.comp T) (SmoothUpToBoundary (𝕜 := 𝕜) Ω p) := by
    rintro v ⟨f, hf, hv⟩
    have hMv : (M v).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        fun x => a x * f x := by
      filter_upwards [ambientMultiply_coe a ha C hC0 hC hD v, hv] with x hx hfx
      exact hx.trans (congrArg (a x * ·) hfx)
    apply Lp.ext
    filter_upwards [hT (M v) (a * f) (ha.mul hf) hMv,
      boundedLpMultiplyCLM_coe (surfaceMeasure Ω) a ha.continuous.aestronglyMeasurable C hC (T v),
      hT v f hf hv] with x h₁ h₂ h₃
    change T (M v) x = B (T v) x
    rw [h₁, h₂, h₃]
    rfl
  have h := heq.closure (T.comp M).continuous (B.comp T).continuous (hdense u)
  change T (M u) = B (T u) at h
  rw [h]
  exact boundedLpMultiplyCLM_coe (surfaceMeasure Ω) a ha.continuous.aestronglyMeasurable C hC (T u)

/-- Zero trace is preserved by bounded smooth ambient localization. -/
lemma trace_zero_ambientMultiply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C)
    (u : SpaceValue 𝕜 d Ω 1 p) (hu : T u = 0) :
    T (ambientMultiply a ha C hC0 hC hD u) = 0 := by
  apply Lp.ext
  filter_upwards [trace_ambientMultiply Ω hdense T hT a ha C hC0 hC hD u,
    Lp.coeFn_zero 𝕜 p (surfaceMeasure Ω)] with x hx hzero
  simpa only [hu, hzero, Pi.zero_apply, mul_zero] using hx


/-- The flat C1 trace also commutes with bounded smooth ambient multiplication. -/
lemma coordinate_trace_ambientMultiply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (i : Fin d) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] Lp 𝕜 p (volume : Measure (Transverse i)))
    (hT : IsCoordinateTrace i T)
    (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C)
    (u : SpaceValue 𝕜 d (upper i) 1 p) :
    T (ambientMultiply a ha C hC0 hC hD u) =ᵐ[volume]
      fun y : Transverse i => a (coordinateLine i y 0) * T u y := by
  let b := fun y : Transverse i => a (coordinateLine i y 0)
  have hb : Continuous b := by
    apply ha.continuous.comp
    apply continuous_pi
    intro j
    dsimp [coordinateLine]
    split_ifs
    · exact continuous_const
    · exact continuous_apply _
  let M := ambientMultiply (Ω := upper i) (p := p) a ha C hC0 hC hD
  let B := boundedLpMultiplyCLM (p := p) volume b hb.aestronglyMeasurable C (fun y => hC _)
  have heq : EqOn (T.comp M) (B.comp T)
      (c1BoundarySubmodule (𝕜 := 𝕜) (upper i) p : Set (SpaceValue 𝕜 d (upper i) 1 p)) := by
    rintro v ⟨f, hf, hv⟩
    have hMv : (M v).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        fun x => a x * f x := by
      filter_upwards [ambientMultiply_coe a ha C hC0 hC hD v, hv] with x hx hfx
      exact hx.trans (congrArg (a x * ·) hfx)
    apply Lp.ext
    filter_upwards [hT (M v) (a * f) ((ha.of_le (by simp)).mul hf) hMv,
      boundedLpMultiplyCLM_coe volume b hb.aestronglyMeasurable C (fun y => hC _) (T v),
      hT v f hf hv] with y h₁ h₂ h₃
    change T (M v) y = B (T v) y
    rw [h₁, h₂, h₃]
    rfl
  have h := heq.closure (T.comp M).continuous (B.comp T).continuous
    (coordinate_upper_c1_density i hp u)
  change T (M u) = B (T u) at h
  rw [h]
  exact boundedLpMultiplyCLM_coe volume b hb.aestronglyMeasurable C (fun y => hC _) (T u)

lemma coordinate_trace_zero_ambientMultiply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (i : Fin d) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] Lp 𝕜 p (volume : Measure (Transverse i)))
    (hT : IsCoordinateTrace i T)
    (a : Domain d → 𝕜) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] a x‖ ≤ C)
    (u : SpaceValue 𝕜 d (upper i) 1 p) (hu : T u = 0) :
    T (ambientMultiply a ha C hC0 hC hD u) = 0 := by
  apply Lp.ext
  filter_upwards [coordinate_trace_ambientMultiply i hp T hT a ha C hC0 hC hD u,
    Lp.coeFn_zero 𝕜 p (volume : Measure (Transverse i))] with y hy hzero
  simpa only [hu, hzero, Pi.zero_apply, mul_zero] using hy


end ExpandedFA.Sobolev.Trace


noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ExpandedFA.Sobolev.Trace
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open OneDimensional

/-- The primitive based at zero of a locally integrable density vanishing on
negative numbers vanishes there, including the joining point. -/
lemma primitive_zero_on_nonpos {𝕜 : Type} [RCLike 𝕜] {G : ℝ → 𝕜}
    (hzero : ∀ᵐ t ∂volume, t < 0 → G t = 0) (t : ℝ) (ht : t ≤ 0) :
    (∫ s in (0 : ℝ)..t, G s) = 0 := by
  rw [intervalIntegral.integral_symm]
  have hz : (∫ s in t..(0 : ℝ), G s) = 0 := by
    calc
      (∫ s in t..(0 : ℝ), G s) = ∫ s in t..(0 : ℝ), (0 : 𝕜) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hzero, volume.ae_ne (0 : ℝ)] with s hs hs0 hst
        have hsle : s ≤ 0 := (by simpa only [uIoc_of_le ht] using hst : s ∈ Ioc t 0).2
        exact hs (lt_of_le_of_ne hsle hs0)
      _ = 0 := by simp
  rw [hz, neg_zero]

/-- A positive-ray AC function with zero right limit glues by zero across the
endpoint. The derivative class is the actual locally integrable zero extension;
no norm approximation or p>1 assumption is used. -/
theorem exists_zero_AC_representative {𝕜 : Type} [RCLike 𝕜] {H G f : ℝ → 𝕜}
    (hg : LocallyIntegrable G volume)
    (hf : Lines.LocallyAbsolutelyContinuousOn f (Ioi 0))
    (hd : ∀ᵐ t ∂volume.restrict (Ioi 0), HasDerivAt f (G t) t)
    (hrep : H =ᵐ[volume.restrict (Ioi 0)] f)
    (hHzero : ∀ᵐ t ∂volume, t < 0 → H t = 0)
    (hGzero : ∀ᵐ t ∂volume, t < 0 → G t = 0)
    (htrace : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∃ F : ℝ → 𝕜, Continuous F ∧
      (∀ a b, AbsolutelyContinuousOnInterval F a b) ∧ H =ᵐ[volume] F ∧
      (∀ᵐ t ∂volume, HasDerivAt F (G t) t) ∧ F 0 = 0 := by
  let P : ℝ → 𝕜 := fun t => ∫ s in (0 : ℝ)..t, G s
  let C : 𝕜 := f 1 - P 1
  let F : ℝ → 𝕜 := fun t => P t + C
  have hi (a b : ℝ) : IntervalIntegrable G volume a b :=
    (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hmatch (t : ℝ) (ht : 0 < t) : f t = F t := by
    have hs : uIcc 1 t ⊆ Ioi (0 : ℝ) := by
      intro s hs
      exact (lt_min (by norm_num : (0 : ℝ) < 1) ht).trans_le hs.1
    have hdt : ∀ᵐ s ∂volume, s ∈ uIcc 1 t → HasDerivAt f (G s) s := by
      filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mp hd] with s hds hst
      exact hds (hs hst)
    have he := OneDimensional.integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt
      (hf 1 t hs) hg hdt
    have hp := intervalIntegral.integral_interval_sub_left (hi 0 t) (hi 0 1)
    change P t - P 1 = _ at hp
    change f t = P t + (f 1 - P 1)
    linear_combination -he - hp
  have hFc : Continuous F :=
    (intervalIntegral.continuous_primitive hi 0).add continuous_const
  have hFzero : F 0 = 0 := by
    apply tendsto_nhds_unique (f := F) (l := 𝓝[>] (0 : ℝ))
      (hFc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    apply htrace.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hmatch t ht
  have hC : C = 0 := by simpa [F, P] using hFzero
  have hnonpos (t : ℝ) (ht : t ≤ 0) : F t = 0 := by
    change P t + C = 0
    rw [hC, add_zero]
    exact primitive_zero_on_nonpos hGzero t ht
  have hFrep : H =ᵐ[volume] F := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mp hrep,
      hHzero, volume.ae_ne (0 : ℝ)] with t hpos hneg ht0
    rcases lt_or_gt_of_ne ht0 with ht | ht
    · exact (hneg ht).trans (hnonpos t ht.le).symm
    · exact (hpos ht).trans (hmatch t ht)
  refine ⟨F, hFc, ?_, hFrep, ?_, hFzero⟩
  · intro a b
    exact (OneDimensional.integral_primitive_absolutelyContinuous hi a b 0).add
      contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  · filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hg] with t ht
    exact (ht 0).add_const C

end ExpandedFA.Sobolev.Trace

namespace ExpandedFA.Sobolev.Trace
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open HalfSpace

section FlatZeroGluing
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Zero extension creates no tangential boundary derivative on the flat
half-space. There is no boundary hypothesis in this coordinate direction. -/
theorem tangent_weak_zero_extension (i j : Fin d) (hij : i ≠ j)
    (u : DomainLp 𝕜 (upper i) p) (g : Fin d → DomainLp 𝕜 (upper i) p)
    (hw : Lines.HasWeakCoordinateDerivatives u g)
    (v h : DomainLp 𝕜 (⊤ : Opens (Domain d)) p)
    (hv : v =ᵐ[volume] (upper i : Set (Domain d)).indicator u)
    (hh : h =ᵐ[volume] (upper i : Set (Domain d)).indicator (g j)) :
    lpDistribution h = -(lpDistribution v).comp (testPartialCLM [j]) := by
  classical
  apply coordinate_weak_of_line_representatives v h j
  filter_upwards [Lines.ae_coordinate_line_representative u g hw j,
    ae_full_lines j hv, ae_full_lines j hh] with y hy hvy hhy
  by_cases hpos : 0 < y ⟨i, hij⟩
  · obtain ⟨f, hfrep, hfac, hfder⟩ := hy
    have hfib := fiber_tangent_pos i j hij y hpos
    rw [hfib, Measure.restrict_univ] at hfrep hfder
    rw [hfib] at hfac
    have hpoint (t : ℝ) : Lines.coordinateLine j y t ∈ (upper i : Set (Domain d)) := by
      simpa [upper, Lines.coordinateLine, hij] using hpos
    refine ⟨f, continuousOn_univ.mp (hfac.continuousOn isOpen_univ),
      fun a b => hfac a b (subset_univ _), ?_, ?_⟩
    · filter_upwards [hvy, hfrep] with t hvt hft
      exact hvt.trans ((indicator_of_mem (hpoint t) u).trans hft)
    · filter_upwards [hhy, hfder] with t hht hdt
      rw [hht, indicator_of_mem (hpoint t)]
      exact hdt
  · have hpoint (t : ℝ) : Lines.coordinateLine j y t ∉ (upper i : Set (Domain d)) := by
      simpa [upper, Lines.coordinateLine, hij] using hpos
    refine ⟨fun _ => 0, continuous_const, fun a b => ?_, ?_, ?_⟩
    · exact contDiff_const.contDiffOn.absolutelyContinuousOnInterval
    · filter_upwards [hvy] with t hvt
      exact hvt.trans (indicator_of_notMem (hpoint t) _)
    · filter_upwards [hhy] with t hht
      rw [hht, indicator_of_notMem (hpoint t)]
      exact hasDerivAt_const t 0

/-- The precise normal boundary hypothesis is the zero right limit of AC
representatives of the original class on almost every normal line. -/
theorem normal_weak_zero_extension (i : Fin d)
    (u : DomainLp 𝕜 (upper i) p) (g : Fin d → DomainLp 𝕜 (upper i) p)
    (v h : DomainLp 𝕜 (⊤ : Opens (Domain d)) p)
    (hv : v =ᵐ[volume] (upper i : Set (Domain d)).indicator u)
    (hh : h =ᵐ[volume] (upper i : Set (Domain d)).indicator (g i))
    (hnormal : ∀ᵐ y : Lines.Transverse i ∂volume, ∃ f : ℝ → 𝕜,
      (fun t => u (Lines.coordinateLine i y t)) =ᵐ[volume.restrict (Ioi 0)] f ∧
      Lines.LocallyAbsolutelyContinuousOn f (Ioi 0) ∧
      (∀ᵐ t ∂volume.restrict (Ioi 0),
        HasDerivAt f (g i (Lines.coordinateLine i y t)) t) ∧
      Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    lpDistribution h = -(lpDistribution v).comp (testPartialCLM [i]) := by
  apply coordinate_weak_of_line_representatives v h i
  filter_upwards [hnormal, ae_full_lines i hv, ae_full_lines i hh,
    locallyIntegrable_full_lines i h] with y hy hvy hhy hgy
  obtain ⟨f, hfrep, hfac, hfder, hfzero⟩ := hy
  have hpoint (t : ℝ) : Lines.coordinateLine i y t ∈ (upper i : Set (Domain d)) ↔ 0 < t := by
    simp [upper, Lines.coordinateLine]
  have hposv : (fun t => v (Lines.coordinateLine i y t)) =ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [hvy.filter_mono (ae_mono Measure.restrict_le_self), hfrep,
      ae_restrict_mem measurableSet_Ioi] with t hvt hft ht
    exact hvt.trans ((indicator_of_mem ((hpoint t).mpr ht) u).trans hft)
  have hposd : ∀ᵐ t ∂volume.restrict (Ioi 0),
      HasDerivAt f (h (Lines.coordinateLine i y t)) t := by
    filter_upwards [hhy.filter_mono (ae_mono Measure.restrict_le_self), hfder,
      ae_restrict_mem measurableSet_Ioi] with t hht hdt ht
    rw [hht, indicator_of_mem ((hpoint t).mpr ht)]
    exact hdt
  have hzv : ∀ᵐ t ∂volume, t < 0 → v (Lines.coordinateLine i y t) = 0 := by
    filter_upwards [hvy] with t ht hneg
    exact ht.trans (indicator_of_notMem (fun h => (not_lt_of_gt hneg) ((hpoint t).mp h)) _)
  have hzd : ∀ᵐ t ∂volume, t < 0 → h (Lines.coordinateLine i y t) = 0 := by
    filter_upwards [hhy] with t ht hneg
    exact ht.trans (indicator_of_notMem (fun h => (not_lt_of_gt hneg) ((hpoint t).mp h)) _)
  obtain ⟨F, hFc, hFac, hFrep, hFd, _⟩ :=
    exists_zero_AC_representative hgy hfac hposd hposv hzv hzd hfzero
  exact ⟨F, hFc, hFac, hFrep, hFd⟩

/-- Flat weak-derivative gluing for any p >= 1, including infinity. The normal
endpoint condition is explicit and tangential conditions require no extra trace. -/
theorem weak_zero_extension_of_normal_limits (i : Fin d)
    (u : DomainLp 𝕜 (upper i) p) (g : Fin d → DomainLp 𝕜 (upper i) p)
    (hw : Lines.HasWeakCoordinateDerivatives u g)
    (v : DomainLp 𝕜 (⊤ : Opens (Domain d)) p)
    (h : Fin d → DomainLp 𝕜 (⊤ : Opens (Domain d)) p)
    (hv : v =ᵐ[volume] (upper i : Set (Domain d)).indicator u)
    (hh : ∀ j, h j =ᵐ[volume] (upper i : Set (Domain d)).indicator (g j))
    (hnormal : ∀ᵐ y : Lines.Transverse i ∂volume, ∃ f : ℝ → 𝕜,
      (fun t => u (Lines.coordinateLine i y t)) =ᵐ[volume.restrict (Ioi 0)] f ∧
      Lines.LocallyAbsolutelyContinuousOn f (Ioi 0) ∧
      (∀ᵐ t ∂volume.restrict (Ioi 0),
        HasDerivAt f (g i (Lines.coordinateLine i y t)) t) ∧
      Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Lines.HasWeakCoordinateDerivatives v h := by
  intro j
  by_cases hj : j = i
  · subst j
    exact normal_weak_zero_extension i u g v (h i) hv (hh i) hnormal
  · exact tangent_weak_zero_extension i j (Ne.symm hj) u g hw v (h j) hv (hh j)

end FlatZeroGluing
end ExpandedFA.Sobolev.Trace

namespace ExpandedFA.Sobolev.Trace
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open HalfSpace

/-- Entrywise zero extension is in the original graph whenever the actual
normal AC representatives have zero right endpoint limits. -/
theorem firstJet_zero_extension_mem_of_normal_limits
    {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (i : Fin d)
    (u : SpaceValue 𝕜 d (upper i) 1 p)
    (V : DerivativeTuple 𝕜 (⊤ : Opens (Domain d)) 1 p)
    (hV : ∀ α, V α =ᵐ[volume] (upper i : Set (Domain d)).indicator (u.val α))
    (hnormal : ∀ᵐ y : Lines.Transverse i ∂volume, ∃ f : ℝ → 𝕜,
      (fun t => u.val (zeroIndex d 1) (Lines.coordinateLine i y t)) =ᵐ[volume.restrict (Ioi 0)] f ∧
      Lines.LocallyAbsolutelyContinuousOn f (Ioi 0) ∧
      (∀ᵐ t ∂volume.restrict (Ioi 0),
        HasDerivAt f (u.val (coordinateIndex i) (Lines.coordinateLine i y t)) t) ∧
      Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    V ∈ derivativeGraph 𝕜 ⊤ 1 p := by
  apply firstJet_mem_of_coordinateWeak
  exact weak_zero_extension_of_normal_limits i _ _ (coordinate_weak_derivatives i u)
    _ _ (hV (zeroIndex d 1)) (fun j => hV (coordinateIndex j)) hnormal

/-- For a continuous scalar-valued function, a.e. vanishing on the negative
half-line forces its joining value to be zero. -/
lemma continuous_zero_at_join {𝕜 : Type} [RCLike 𝕜] {F : ℝ → 𝕜}
    (hF : Continuous F) (hzero : ∀ᵐ t ∂volume, t < 0 → F t = 0) : F 0 = 0 := by
  have he : EqOn F (fun _ => 0) (Iio 0) := by
    apply Measure.eqOn_open_of_ae_eq (μ := (volume : Measure ℝ)) _ isOpen_Iio hF.continuousOn continuousOn_const
    exact (ae_restrict_iff' measurableSet_Iio).mpr hzero
  exact he.closure hF continuous_const (by simp)

/-- Every existing global Sobolev zero extension has zero endpoint values on
almost all normal ACL lines; this direction uses only global ACL and support. -/
theorem global_normal_limits_zero_of_supported
    {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (i : Fin d)
    (v : SpaceValue 𝕜 d ⊤ 1 p)
    (hv : ∀ᵐ x ∂volume, x i < 0 → v.val (zeroIndex d 1) x = 0) :
    ∀ᵐ y : Lines.Transverse i ∂volume, ∃ f : ℝ → 𝕜,
      (fun t => v.val (zeroIndex d 1) (Lines.coordinateLine i y t)) =ᵐ[volume] f ∧
      (∀ a b, AbsolutelyContinuousOnInterval f a b) ∧
      (∀ᵐ t ∂volume,
        HasDerivAt f (v.val (coordinateIndex i) (Lines.coordinateLine i y t)) t) ∧
      f 0 = 0 ∧ Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hv' : v.val (zeroIndex d 1) =ᵐ[volume]
      (fun x => if x i < 0 then 0 else v.val (zeroIndex d 1) x) := by
    filter_upwards [hv] with x hx
    split_ifs with hneg
    · exact hx hneg
    · rfl
  filter_upwards [Lines.ae_coordinate_line_representative (v.val (zeroIndex d 1))
    (fun j => v.val (coordinateIndex j)) (coordinate_weak_derivatives_on v) i,
    ae_full_lines i hv'] with y hy hvy
  obtain ⟨f, hfrep, hfac, hfder⟩ := hy
  simp only [fiber_top, Measure.restrict_univ] at hfrep hfder
  simp only [fiber_top] at hfac
  have hfc : Continuous f := continuousOn_univ.mp (hfac.continuousOn isOpen_univ)
  have hfzero : f 0 = 0 := by
    apply continuous_zero_at_join hfc
    filter_upwards [hfrep, hvy] with t hft hvt hneg
    rw [← hft, hvt]
    simp [Lines.coordinateLine, hneg]
  refine ⟨f, hfrep, (fun a b => hfac a b (subset_univ _)), hfder, hfzero, ?_⟩
  simpa only [hfzero] using hfc.continuousAt.tendsto.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)

end ExpandedFA.Sobolev.Trace

namespace ExpandedFA.Sobolev.Trace
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open HalfSpace C1Extension

section FlatNormalZeroExtension
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Zero normal limits suffice for Sobolev zero extension of the original
half-space graph. Both real and complex scalars, p=1 and p=infinity are included. -/
theorem hasSobolevZeroExtension_of_normal_limits (i : Fin d)
    (u : SpaceValue 𝕜 d (upper i) 1 p)
    (hnormal : ∀ᵐ y : Lines.Transverse i ∂volume, ∃ f : ℝ → 𝕜,
      (fun t => u.val (zeroIndex d 1) (Lines.coordinateLine i y t)) =ᵐ[volume.restrict (Ioi 0)] f ∧
      Lines.LocallyAbsolutelyContinuousOn f (Ioi 0) ∧
      (∀ᵐ t ∂volume.restrict (Ioi 0),
        HasDerivAt f (u.val (coordinateIndex i) (Lines.coordinateLine i y t)) t) ∧
      Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    HasSobolevZeroExtension u := by
  let V : DerivativeTuple 𝕜 (⊤ : Opens (Domain d)) 1 p :=
    WithLp.toLp 1 (fun α => zeroLp ⊤ (u.val α))
  have hV (α) : V α =ᵐ[volume] (upper i : Set (Domain d)).indicator (u.val α) := by
    simpa using (zeroLp_coe (Λ := ⊤) (u.val α))
  exact ⟨⟨V, firstJet_zero_extension_mem_of_normal_limits i u V hV hnormal⟩,
    hV (zeroIndex d 1)⟩

/-- Conversely, global ACL identifies the zero right limits of an existing
Sobolev zero extension along almost every normal line of the original graph. -/
theorem normal_limits_of_hasSobolevZeroExtension (i : Fin d)
    (u : SpaceValue 𝕜 d (upper i) 1 p) (hu : HasSobolevZeroExtension u) :
    ∀ᵐ y : Lines.Transverse i ∂volume, ∃ f : ℝ → 𝕜,
      (fun t => u.val (zeroIndex d 1) (Lines.coordinateLine i y t)) =ᵐ[volume.restrict (Ioi 0)] f ∧
      Lines.LocallyAbsolutelyContinuousOn f (Ioi 0) ∧
      (∀ᵐ t ∂volume.restrict (Ioi 0),
        HasDerivAt f (u.val (coordinateIndex i) (Lines.coordinateLine i y t)) t) ∧
      Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨v, hv⟩ := hu
  have hr : restrictSobolev (le_top : upper i ≤ ⊤) v = u := by
    apply sobolev_underlying_injective 𝕜 d (upper i) 1 p
    apply Lp.ext
    filter_upwards [restrictSobolev_coe le_top v (zeroIndex d 1),
      ae_restrict_of_ae hv, ae_restrict_mem (upper i).isOpen.measurableSet]
      with x hx hvx hxΩ
    rw [hx, hvx, indicator_of_mem hxΩ]
  have hrv (α) : u.val α =ᵐ[volume.restrict (upper i : Set (Domain d))] v.val α := by
    simpa only [hr] using restrictSobolev_coe (le_top : upper i ≤ ⊤) v α
  have hsupport : ∀ᵐ x ∂volume, x i < 0 → v.val (zeroIndex d 1) x = 0 := by
    filter_upwards [hv] with x hvx hneg
    exact hvx.trans (indicator_of_notMem (show x ∉ (upper i : Set (Domain d)) from
      not_lt_of_gt hneg) _)
  filter_upwards [global_normal_limits_zero_of_supported i v hsupport,
    Lines.ae_on_fibers i (hrv (zeroIndex d 1)),
    Lines.ae_on_fibers i (hrv (coordinateIndex i))] with y hy hbase hder
  simp only [fiber_normal] at hbase hder
  obtain ⟨f, hfrep, hfac, hfder, _, hfzero⟩ := hy
  refine ⟨f, ?_, (fun a b _ => hfac a b), ?_, hfzero⟩
  · filter_upwards [hbase, ae_restrict_of_ae hfrep] with t hbt hft
    exact hbt.trans hft
  · filter_upwards [hder, ae_restrict_of_ae hfder] with t hdt hft
    rw [hdt]
    exact hft

/-- An exact flat normal-line criterion, expressed through representatives
of the actual Sobolev graph rather than through an assumed trace operator. -/
theorem upper_zero_extension_iff_normal_limits (i : Fin d)
    (u : SpaceValue 𝕜 d (upper i) 1 p) :
    HasSobolevZeroExtension u ↔
    ∀ᵐ y : Lines.Transverse i ∂volume, ∃ f : ℝ → 𝕜,
      (fun t => u.val (zeroIndex d 1) (Lines.coordinateLine i y t)) =ᵐ[volume.restrict (Ioi 0)] f ∧
      Lines.LocallyAbsolutelyContinuousOn f (Ioi 0) ∧
      (∀ᵐ t ∂volume.restrict (Ioi 0),
        HasDerivAt f (u.val (coordinateIndex i) (Lines.coordinateLine i y t)) t) ∧
      Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  ⟨normal_limits_of_hasSobolevZeroExtension i u,
    hasSobolevZeroExtension_of_normal_limits i u⟩

end FlatNormalZeroExtension
end ExpandedFA.Sobolev.Trace


noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace ExpandedFA.Sobolev.Trace
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open HalfSpace C1Extension

lemma normalBoundaryInsertion_isClosedEmbedding {d : ℕ} (i : Fin d) :
    Topology.IsClosedEmbedding (fun y : Lines.Transverse i => Lines.coordinateLine i y 0) := by
  classical
  have hprod : Isometry (fun y : Lines.Transverse i => ((0 : ℝ), y)) := by
    intro y z
    simp [Prod.edist_eq]
  have he := (Lines.coordinateIsometryEquiv i).symm.isometry.isClosedEmbedding.comp
    hprod.isClosedEmbedding
  convert he using 1
  funext y
  change Lines.coordinateLine i y 0 = (Lines.coordinateEquiv i).symm (0, y)
  exact (Lines.coordinateEquiv_symm_apply i 0 y).symm

lemma normalBoundaryTest_hasCompactSupport {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (i : Fin d) (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    HasCompactSupport (fun y : Lines.Transverse i => φ (Lines.coordinateLine i y 0)) :=
  φ.hasCompactSupport.comp_isClosedEmbedding (normalBoundaryInsertion_isClosedEmbedding i)

section NormalGreen
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Smooth normal Green formula expressed directly through global zero-extended
Lp classes. The boundary measure here is transverse Lebesgue measure. -/
lemma smooth_zero_extension_normal_green (i : Fin d)
    (u : SpaceValue 𝕜 d (upper i) 1 p) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ 1 f)
    (hu : u.val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))] f)
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    lpDistribution (zeroLp ⊤ (u.val (coordinateIndex i))) φ +
      lpDistribution (zeroLp ⊤ (u.val (zeroIndex d 1))) (testPartialCLM [i] φ) =
    -(∫ y : Lines.Transverse i, φ (Lines.coordinateLine i y 0) * f (Lines.coordinateLine i y 0)) := by
  let zg := zeroLp (⊤ : Opens (Domain d)) (u.val (coordinateIndex i))
  let zu := zeroLp (⊤ : Opens (Domain d)) (u.val (zeroIndex d 1))
  have hzg : zg =ᵐ[volume] (upper i : Set (Domain d)).indicator (u.val (coordinateIndex i)) := by
    simpa [zg] using zeroLp_coe (Λ := ⊤) (u.val (coordinateIndex i))
  have hzu : zu =ᵐ[volume] (upper i : Set (Domain d)).indicator (u.val (zeroIndex d 1)) := by
    simpa [zu] using zeroLp_coe (Λ := ⊤) (u.val (zeroIndex d 1))
  have hd := Classical.c1_representative_derivative u f hf.contDiffOn hu i
  have h₁ : Integrable (fun x => φ x * zg x) volume := by
    simpa using Lines.integrable_test_mul_lp φ zg
  have h₂ : Integrable (fun x => testPartialCLM [i] φ x * zu x) volume := by
    simpa using Lines.integrable_test_mul_lp (testPartialCLM [i] φ) zu
  have he : ∀ᵐ y : Lines.Transverse i ∂volume,
      (∫ t, φ (Lines.coordinateLine i y t) * zg (Lines.coordinateLine i y t) +
        testPartialCLM [i] φ (Lines.coordinateLine i y t) * zu (Lines.coordinateLine i y t)) =
        -(φ (Lines.coordinateLine i y 0) * f (Lines.coordinateLine i y 0)) := by
    filter_upwards [ae_full_lines i hzg, ae_full_lines i hzu,
      Lines.ae_on_fibers i hu, Lines.ae_on_fibers i hd] with y hzgy hzuy huy hdy
    simp only [fiber_normal] at huy hdy
    let ψ : ℝ → 𝕜 := fun t => φ (Lines.coordinateLine i y t)
    let F : ℝ → 𝕜 := fun t => f (Lines.coordinateLine i y t)
    have hψ : ContDiff ℝ 1 ψ :=
      (φ.contDiff.of_le (by simp)).comp ((Lines.coordinateLine_contDiff i y).of_le (by simp))
    have hF : ContDiff ℝ 1 F :=
      hf.comp ((Lines.coordinateLine_contDiff i y).of_le (by simp))
    have hcψ : HasCompactSupport ψ :=
      φ.hasCompactSupport.comp_isClosedEmbedding (Lines.coordinateLine_isClosedEmbedding i y)
    have hmatch : (fun t => φ (Lines.coordinateLine i y t) * zg (Lines.coordinateLine i y t) +
        testPartialCLM [i] φ (Lines.coordinateLine i y t) * zu (Lines.coordinateLine i y t)) =ᵐ[volume]
        (Ioi (0 : ℝ)).indicator (deriv (ψ * F)) := by
      filter_upwards [hzgy, hzuy, (ae_restrict_iff' measurableSet_Ioi).mp huy,
        (ae_restrict_iff' measurableSet_Ioi).mp hdy] with t hzgt hzut hut hdt
      have hpoint : Lines.coordinateLine i y t ∈ (upper i : Set (Domain d)) ↔ 0 < t := by
        simp [upper, Lines.coordinateLine]
      by_cases ht : 0 < t
      · rw [hzgt, hzut, indicator_of_mem (hpoint.mpr ht), indicator_of_mem (hpoint.mpr ht),
          indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht), hut ht, hdt ht]
        have hderF : deriv F t = fderiv ℝ f (Lines.coordinateLine i y t) (coordinateVector i) :=
          ((hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
            (Lines.coordinateLine_hasDerivAt i y t)).deriv
        rw [deriv_mul (hψ.differentiable one_ne_zero t) (hF.differentiable one_ne_zero t), hderF]
        rw [Lines.testPartial_on_coordinateLine]
        simp only [ψ, F]
        ring
      · rw [hzgt, hzut, indicator_of_notMem (mt hpoint.mp ht),
          indicator_of_notMem (mt hpoint.mp ht),
          indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
        simp
    rw [integral_congr_ae hmatch, integral_indicator measurableSet_Ioi]
    exact (hcψ.mul_right).integral_Ioi_deriv_eq (hψ.mul hF) 0
  simp only [lpDistribution_apply, Opens.coe_top, Measure.restrict_univ]
  change (∫ x, φ x * zg x) + (∫ x, testPartialCLM [i] φ x * zu x) = _
  rw [← integral_add h₁ h₂]
  change (∫ x, ((fun x => φ x * zg x) + (fun x => testPartialCLM [i] φ x * zu x)) x) = _
  rw [Lines.integral_coordinateLines i (h₁.add h₂)]
  change (∫ y : Lines.Transverse i, ∫ t, φ (Lines.coordinateLine i y t) * zg (Lines.coordinateLine i y t) +
    testPartialCLM [i] φ (Lines.coordinateLine i y t) * zu (Lines.coordinateLine i y t)) = _
  rw [integral_congr_ae he, integral_neg]

end NormalGreen
end ExpandedFA.Sobolev.Trace

namespace ExpandedFA.Sobolev.Trace
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open HalfSpace C1Extension

section FlatGreenContinuity
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma continuous_zeroLp_testPairing (i : Fin d)
    (α : DerivativeIndex d 1) (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    Continuous (fun u : SpaceValue 𝕜 d (upper i) 1 p =>
      lpDistribution (zeroLp ⊤ (u.val α)) φ) := by
  let Z : DomainLp 𝕜 (upper i) p →L[𝕜] DomainLp 𝕜 ⊤ p :=
    (zeroLpLM (𝕜 := 𝕜) (Ω := upper i) (p := p) ⊤).mkContinuous 1 (fun v => by
      change ‖zeroLp (⊤ : Opens (Domain d)) v‖ ≤ 1 * ‖v‖
      rw [zeroLp_norm le_top, one_mul])
  have he : Continuous (fun u : SpaceValue 𝕜 d (upper i) 1 p => u.val α) :=
    (PiLp.continuous_apply 1 _ α).comp continuous_subtype_val
  apply ((Smoothing.testLpPairing (p := p) φ).continuous.comp (Z.continuous.comp he)).congr
  intro u
  change Smoothing.testLpPairing φ (zeroLp ⊤ (u.val α)) = _
  exact Smoothing.testLpPairing_apply _ _

lemma continuous_normalBoundaryPairing (i : Fin d)
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    Continuous (fun v : Lp 𝕜 p (volume : Measure (Lines.Transverse i)) =>
      ∫ y : Lines.Transverse i, φ (Lines.coordinateLine i y 0) * v y) := by
  let ψ : Lines.Transverse i → 𝕜 := fun y => φ (Lines.coordinateLine i y 0)
  have hψ : MemLp ψ p.conjExponent volume :=
    (φ.continuous.comp (normalBoundaryInsertion_isClosedEmbedding i).continuous).memLp_of_hasCompactSupport
      (normalBoundaryTest_hasCompactSupport i φ)
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p⟩
  let P : Lp 𝕜 p (volume : Measure (Lines.Transverse i)) →L[𝕜] 𝕜 :=
    ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing
      (volume : Measure (Lines.Transverse i)) p p.conjExponent).flip (hψ.toLp ψ)
  have he (v : Lp 𝕜 p (volume : Measure (Lines.Transverse i))) :
      P v = ∫ y : Lines.Transverse i, ψ y * v y := by
    dsimp only [P, ContinuousLinearMap.flip_apply]
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hψ.coeFn_toLp] with y hy
    rw [hy, mul_comm]
    rfl
  exact P.continuous.congr (fun v => he v)

end FlatGreenContinuity
end ExpandedFA.Sobolev.Trace

namespace ExpandedFA.Sobolev.Trace
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open HalfSpace C1Extension

section FlatTraceZeroExtension
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Green's normal formula for the actual coordinate trace, obtained by
continuity from ambient C1 representatives. -/
theorem coordinate_trace_normal_green (i : Fin d) (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] Lp 𝕜 p (volume : Measure (Lines.Transverse i)))
    (hT : IsCoordinateTrace i T) (u : SpaceValue 𝕜 d (upper i) 1 p)
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) :
    lpDistribution (zeroLp ⊤ (u.val (coordinateIndex i))) φ +
      lpDistribution (zeroLp ⊤ (u.val (zeroIndex d 1))) (testPartialCLM [i] φ) =
    -(∫ y : Lines.Transverse i, φ (Lines.coordinateLine i y 0) * T u y) := by
  let E : Set (SpaceValue 𝕜 d (upper i) 1 p) := {v |
    lpDistribution (zeroLp ⊤ (v.val (coordinateIndex i))) φ +
      lpDistribution (zeroLp ⊤ (v.val (zeroIndex d 1))) (testPartialCLM [i] φ) =
    -(∫ y : Lines.Transverse i, φ (Lines.coordinateLine i y 0) * T v y)}
  have hclosed : IsClosed E :=
    isClosed_eq ((continuous_zeroLp_testPairing i (coordinateIndex i) φ).add
      (continuous_zeroLp_testPairing i (zeroIndex d 1) (testPartialCLM [i] φ)))
      (((continuous_normalBoundaryPairing i φ).comp T.continuous).neg)
  have hsub : (c1BoundarySubmodule (𝕜 := 𝕜) (upper i) p : Set (SpaceValue 𝕜 d (upper i) 1 p)) ⊆ E := by
    rintro v ⟨f, hf, hv⟩
    change _ = _
    rw [smooth_zero_extension_normal_green i v f hf hv φ]
    congr 1
    apply integral_congr_ae
    filter_upwards [hT v f hf hv] with y hy
    rw [hy]
  exact closure_minimal hsub hclosed (coordinate_upper_c1_density (𝕜 := 𝕜) i hp u)

/-- A zero coordinate trace eliminates the boundary term in the weak normal
derivative. This is actual zero gluing, with no extra regularity hypothesis. -/
theorem normal_weak_zero_extension_of_coordinate_trace_zero (i : Fin d) (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] Lp 𝕜 p (volume : Measure (Lines.Transverse i)))
    (hT : IsCoordinateTrace i T) (u : SpaceValue 𝕜 d (upper i) 1 p) (hu : T u = 0) :
    lpDistribution (zeroLp ⊤ (u.val (coordinateIndex i))) =
      -(lpDistribution (zeroLp ⊤ (u.val (zeroIndex d 1)))).comp (testPartialCLM [i]) := by
  ext φ
  simp only [neg_apply, ContinuousLinearMap.comp_apply]
  apply eq_neg_of_add_eq_zero_left
  have he := coordinate_trace_normal_green i hp T hT u φ
  have hz : (∫ y : Lines.Transverse i, φ (Lines.coordinateLine i y 0) * T u y) = 0 := by
    rw [hu]
    have hfun : (fun y : Lines.Transverse i => φ (Lines.coordinateLine i y 0) *
        (0 : Lp 𝕜 p (volume : Measure (Lines.Transverse i))) y) =ᵐ[volume]
          (fun _ : Lines.Transverse i => (0 : 𝕜)) := by
      filter_upwards [Lp.coeFn_zero 𝕜 p (volume : Measure (Lines.Transverse i))] with y hy
      rw [hy]
      simp
    rw [integral_congr_ae hfun, integral_zero]
  simpa only [hz, neg_zero] using he

/-- Vanishing of the actual flat trace implies membership of its zero extension
in the original global weak-derivative graph, for every finite p >= 1. -/
theorem hasSobolevZeroExtension_of_coordinate_trace_zero (i : Fin d) (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] Lp 𝕜 p (volume : Measure (Lines.Transverse i)))
    (hT : IsCoordinateTrace i T) (u : SpaceValue 𝕜 d (upper i) 1 p) (hu : T u = 0) :
    HasSobolevZeroExtension u := by
  let V : DerivativeTuple 𝕜 (⊤ : Opens (Domain d)) 1 p :=
    WithLp.toLp 1 (fun α => zeroLp ⊤ (u.val α))
  have hV (α) : V α =ᵐ[volume] (upper i : Set (Domain d)).indicator (u.val α) := by
    simpa using (zeroLp_coe (Λ := ⊤) (u.val α))
  have hmem : V ∈ derivativeGraph 𝕜 ⊤ 1 p := by
    apply firstJet_mem_of_coordinateWeak
    intro j
    by_cases hj : j = i
    · subst j
      exact normal_weak_zero_extension_of_coordinate_trace_zero i hp T hT u hu
    · exact tangent_weak_zero_extension i j (Ne.symm hj) _ _ (coordinate_weak_derivatives i u)
        _ _ (hV (zeroIndex d 1)) (hV (coordinateIndex j))
  exact ⟨⟨V, hmem⟩, hV (zeroIndex d 1)⟩

end FlatTraceZeroExtension
end ExpandedFA.Sobolev.Trace


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Topology
namespace ExpandedFA.Sobolev.Trace
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open C1Extension HalfSpace

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Multiplication by a compact cutoff inside the chart target glues a C1
pullback to a global C1 function, despite the chart being defined only locally. -/
lemma contDiff_chart_cutoff_comp
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (χ : Tests 𝕜 (⊤ : Opens (Domain d))) (hχ : tsupport χ ⊆ Φ.target)
    (f : Domain d → 𝕜) (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (fun y => χ y * f (Φ.symm y)) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hyt : y ∈ Φ.target
  · exact ((χ.contDiff.of_le (by simp)).contDiffAt).mul
      (hf.contDiffAt.comp y (hInv.contDiffAt (Φ.open_target.mem_nhds hyt)))
  · have hyχ : y ∉ tsupport χ := fun hh => hyt (hχ hh)
    have hzero := notMem_tsupport_iff_eventuallyEq.mp hyχ
    apply (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : Domain d => (0 : 𝕜)) y).congr_of_eventuallyEq
    filter_upwards [hzero] with x hx
    simp only [hx, zero_mul, Pi.zero_apply]

/-- Actual bounded flattening of a localized domain member. For ambient smooth
representatives, the output has a global C1 representative with the correct
boundary values. -/
theorem exists_flattened_localization
    (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (hBinv : ∀ x ∈ Φ.target, ‖fderiv ℝ Φ.symm x‖ ≤ B)
    (hSource : Bornology.IsBounded Φ.source)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    (θ : Tests 𝕜 (⊤ : Opens (Domain d))) (hθ : tsupport θ ⊆ Φ.source) :
    ∃ χ : Tests 𝕜 (⊤ : Opens (Domain d)), tsupport χ ⊆ Φ.target ∧
      (∀ x ∈ tsupport θ, χ (Φ x) = 1) ∧
      ∃ E : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d (upper i) 1 p,
      ∀ (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
      ContDiff ℝ (⊤ : ℕ∞) f →
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f →
      ContDiff ℝ 1 (fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y))) ∧
      (E u).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y)) := by
  obtain ⟨J, hJ1, hJbound⟩ := Transport.exists_det_bound_of_norm_bound (E := Domain d) B
  have hJsrc : ∀ x ∈ Φ.source, |(fderiv ℝ Φ x).det| ≤ J :=
    fun x hx => hJbound _ (hB x hx)
  obtain ⟨χ, hχ, hχone⟩ := exists_chart_cutoff Φ θ hθ
  let A : Opens (Domain d) := Ω ⊓ ⟨Φ.source, Φ.open_source⟩
  let V := Transport.chartPreimage Φ.symm Ω
  have hVupper : V ≤ upper i := by
    rintro y ⟨hyt, hyΩ⟩
    have h := (hside (Φ.symm y) (Φ.map_target hyt)).mp hyΩ
    change 0 < y i
    simpa only [Φ.right_inv hyt] using h
  let K : Set (Domain d) := tsupport χ ∩ (upper i : Set (Domain d))
  have hKclosed : IsClosed (K ∪ (upper i : Set (Domain d))ᶜ) := by
    have heq : K ∪ (upper i : Set (Domain d))ᶜ = tsupport χ ∪ (upper i : Set (Domain d))ᶜ := by
      ext x
      simp only [K, mem_union, mem_inter_iff, mem_compl_iff]
      tauto
    rw [heq]
    exact (isClosed_tsupport χ).union (upper i).isOpen.isClosed_compl
  have hKV : K ⊆ V := by
    rintro y ⟨hyχ, hyupper⟩
    have hyt := hχ hyχ
    refine ⟨hyt, (hside (Φ.symm y) (Φ.map_target hyt)).mpr ?_⟩
    change 0 < y i at hyupper
    simpa only [Φ.right_inv hyt] using hyupper
  have hχK : (V : Set (Domain d)) ∩ tsupport χ ⊆ K :=
    fun y hy => ⟨hy.2, hVupper hy.1⟩
  obtain ⟨Cχ, hCχ0, hCχ, hDχ⟩ := ambient_test_bounds χ
  obtain ⟨Cθ, hCθ0, hCθ, hDθ⟩ := ambient_test_bounds θ
  let Mθ : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p :=
    ambientMultiply θ θ.contDiff Cθ hCθ0 hCθ hDθ
  let R : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d A 1 p := restrictSobolev inf_le_left
  let P : SpaceValue 𝕜 d A 1 p →L[𝕜] SpaceValue 𝕜 d V 1 p :=
    Transport.chartSobolevPull Φ.symm hInv hΦ B hBinv hB0 J hJsrc hJ1 Ω hSource
  let Mχ : SpaceValue 𝕜 d V 1 p →L[𝕜] SpaceValue 𝕜 d (upper i) 1 p :=
    localizedZeroExtension hVupper K hKclosed hKV χ χ.contDiff Cχ hCχ0 hCχ hDχ hχK
  let E := Mχ.comp (P.comp (R.comp Mθ))
  refine ⟨χ, hχ, hχone, E, ?_⟩
  intro u f hf hu
  have hg : ContDiff ℝ 1 (fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y))) :=
    contDiff_chart_cutoff_comp Φ hInv χ hχ (fun x => θ x * f x)
      ((θ.contDiff.mul hf).of_le (by simp))
  refine ⟨hg, ?_⟩
  have hθu : (Mθ u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      (fun x => θ x * f x) := by
    filter_upwards [ambientMultiply_coe θ θ.contDiff Cθ hCθ0 hCθ hDθ u, hu] with x hx hux
    exact hx.trans (congrArg (θ x * ·) hux)
  have hr : (R (Mθ u)).val (zeroIndex d 1) =ᵐ[volume.restrict (A : Set (Domain d))]
      (fun x => θ x * f x) :=
    (restrictSobolev_coe inf_le_left (Mθ u) (zeroIndex d 1)).trans
      (hθu.filter_mono (ae_mono (Measure.restrict_mono inter_subset_left le_rfl)))
  have hpull := Transport.chartSobolevPull_coe Φ.symm hInv hΦ B hBinv hB0 J hJsrc hJ1 Ω hSource
    (R (Mθ u)) (fun x => θ x * f x) hr.symm
  have he := localizedZeroExtension_representative hVupper K hKclosed hKV χ χ.contDiff
    Cχ hCχ0 hCχ hDχ hχK (P (R (Mθ u))) ((fun x => θ x * f x) ∘ Φ.symm) hpull.symm
  change (Mχ (P (R (Mθ u)))).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))] _
  filter_upwards [he, ae_restrict_mem (upper i).isOpen.measurableSet] with y hy hyupper
  rw [hy]
  change (V : Set (Domain d)).indicator (fun x => χ x * (θ (Φ.symm x) * f (Φ.symm x))) y = _
  by_cases hyV : y ∈ V
  · exact indicator_of_mem hyV _
  · rw [indicator_of_notMem hyV]
    have hyχ : y ∉ tsupport χ := fun hh => hyV (hKV ⟨hh, hyupper⟩)
    rw [image_eq_zero_of_notMem_tsupport hyχ, zero_mul]

/-- Numerical smooth trace estimate for one localized C1 boundary chart. The
constant is obtained from genuine bounded Sobolev transport and chart surface
measure domination; no trace theorem is assumed. -/
theorem exists_chart_smooth_trace_bound {n : ℕ} (Ω : Opens (Domain (n + 1)))
    (i : Fin (n + 1)) (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1)))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (hBinv : ∀ x ∈ Φ.target, ‖fderiv ℝ Φ.symm x‖ ≤ B)
    (hSource : Bornology.IsBounded Φ.source)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    {K : ℝ≥0} (hLip : LipschitzOnWith K Φ.symm Φ.target)
    (θ : Tests 𝕜 (⊤ : Opens (Domain (n + 1)))) (hθ : tsupport θ ⊆ Φ.source)
    (hp : p ≠ ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SpaceValue 𝕜 (n + 1) Ω 1 p) (f : Domain (n + 1) → 𝕜),
      ContDiff ℝ (⊤ : ℕ∞) f →
      u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n + 1)))] f →
      (eLpNorm (fun x => θ x * f x) p (surfaceMeasure Ω)).toReal ≤ C * ‖u‖ := by
  obtain ⟨χ, hχ, hχone, E, hE⟩ := exists_flattened_localization (p := p) i Φ hΦ hInv B hB0
    hB hBinv hSource hside θ hθ
  obtain ⟨D, hD, hDbound⟩ := boundary_chart_eLpNorm_le Ω Φ i hside hLip
  let Q : ℝ≥0∞ := D ^ (1 / p).toReal
  have hQ : Q ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hD.ne).ne
  refine ⟨Q.toReal * 4 * ‖E‖, by positivity, ?_⟩
  intro u f hf hu
  let h : Domain (n + 1) → 𝕜 := fun x => θ x * f x
  let g : Domain (n + 1) → 𝕜 := fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y))
  obtain ⟨hg, hEu⟩ := hE u f hf hu
  have hh : Continuous h := θ.contDiff.continuous.mul hf.continuous
  have hindicator : Φ.source.indicator h = h := by
    funext x
    by_cases hx : x ∈ Φ.source
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      have hxθ : x ∉ tsupport θ := fun hh => hx (hθ hh)
      dsimp [h]
      rw [image_eq_zero_of_notMem_tsupport hxθ, zero_mul]
  have hnorm_source : eLpNorm h p (surfaceMeasure Ω) =
      eLpNorm h p ((surfaceMeasure Ω).restrict Φ.source) := by
    calc
      _ = eLpNorm (Φ.source.indicator h) p (surfaceMeasure Ω) :=
        congrArg (fun F : Domain (n + 1) → 𝕜 => eLpNorm F p (surfaceMeasure Ω)) hindicator.symm
      _ = _ := eLpNorm_indicator_eq_eLpNorm_restrict Φ.open_source.measurableSet.nullMeasurableSet
  have hparam : h ∘ boundaryParam Φ i =ᵐ[volume.restrict (boundaryParameters Φ i)]
      (fun z : Domain n => g (i.insertNth 0 z)) := by
    filter_upwards [ae_restrict_mem (boundaryParameters_isOpen Φ i).measurableSet] with z hz
    let x := boundaryParam Φ i z
    have hyt : i.insertNth (α := fun _ => ℝ) 0 z ∈ Φ.target := hz
    change θ x * f x = χ (i.insertNth 0 z) * (θ x * f x)
    by_cases hxθ : x ∈ tsupport θ
    · have hc := hχone x hxθ
      change χ (Φ (Φ.symm (i.insertNth 0 z))) = 1 at hc
      rw [Φ.right_inv hyt] at hc
      rw [hc, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hxθ, zero_mul, mul_zero]
  have hbound : eLpNorm h p (surfaceMeasure Ω) ≤ Q * ENNReal.ofReal (4 * ‖E u‖) := by
    rw [hnorm_source]
    apply (hDbound h p hh.aestronglyMeasurable).trans
    change Q * eLpNorm (h ∘ boundaryParam Φ i) p (volume.restrict (boundaryParameters Φ i)) ≤ _
    rw [eLpNorm_congr_ae hparam]
    gcongr
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      (coordinate_upper_insertNth_c1_trace_bound i hp (E u) g hg hEu)
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hQ ENNReal.ofReal_ne_top) hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hreal
  exact hreal.trans (by
    have hnorm := E.le_opNorm u
    have hmul := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ Q.toReal * 4 by positivity)
    nlinarith)

/-- A finite C1 boundary atlas gives the actual scalar norm estimate for
ambient smooth restriction. Compact boundary suffices for this estimate. -/
theorem exists_smooth_trace_bound (hp : p ≠ ∞)
    (hΩ : IsC1Domain Ω) (hc : IsCompact (frontier (Ω : Set (Domain d)))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
      ContDiff ℝ (⊤ : ℕ∞) f →
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f →
      (eLpNorm f p (surfaceMeasure Ω)).toReal ≤ C * ‖u‖ := by
  classical
  cases d with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intro u f hf hu
    simp [surfaceMeasure_zero_dim Ω]
  | succ n =>
    obtain ⟨m, i, Φ, B, K, hB0, hcharts, hLip, hcover⟩ :=
      finite_bounded_lipschitz_boundary_charts (n + 1) Ω hΩ hc
    obtain ⟨a, S, A, ha, hA0, hA, hDA, hsum, hsupp, hSc, hSΩ, hS⟩ :=
      finite_scalar_boundary_localization (𝕜 := 𝕜) Ω (fun j => (Φ j).source)
        (fun j => (Φ j).open_source) hcover hc
    have hlocal (j : Fin m) :
        ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SpaceValue 𝕜 (n + 1) Ω 1 p) (f : Domain (n + 1) → 𝕜),
          ContDiff ℝ (⊤ : ℕ∞) f →
          u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n + 1)))] f →
          (eLpNorm (fun x => a (some j) x * f x) p (surfaceMeasure Ω)).toReal ≤ C * ‖u‖ := by
      let θ : Tests 𝕜 (⊤ : Opens (Domain (n + 1))) :=
        ⟨a (some j), ha (some j), (hsupp j).1, by simp⟩
      obtain ⟨hΦ, hInv, hbs, hbt, hside, hder, hderInv⟩ := hcharts j
      exact exists_chart_smooth_trace_bound Ω (i j) (Φ j) hΦ hInv B hB0
        hder hderInv hbs hside (hLip j) θ (hsupp j).2 hp
    choose C hC0 hC using hlocal
    refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC0 j), ?_⟩
    intro u f hf hu
    have heq : f =ᵐ[surfaceMeasure Ω] ∑ j, (fun x => a (some j) x * f x) := by
      filter_upwards [surfaceMeasure_ae_frontier Ω] with x hx
      have hxnone : x ∉ tsupport (a none) := by
        intro hxnone
        have hxΩ : x ∈ Ω := hSΩ (hS ⟨frontier_subset_closure hx, hxnone⟩)
        exact (Ω.isOpen.frontier_eq ▸ hx).2 hxΩ
      have hnone : a none x = 0 := image_eq_zero_of_notMem_tsupport hxnone
      have hs : ∑ j, a (some j) x = 1 := by simpa only [hnone, zero_add] using hsum x
      simp only [Finset.sum_apply]
      rw [← Finset.sum_mul, hs, one_mul]
    have hnorm : eLpNorm f p (surfaceMeasure Ω) ≤
        ∑ j, eLpNorm (fun x => a (some j) x * f x) p (surfaceMeasure Ω) := by
      rw [eLpNorm_congr_ae heq]
      exact eLpNorm_sum_le Fact.out
    have hfinite (j : Fin m) :
        eLpNorm (fun x => a (some j) x * f x) p (surfaceMeasure Ω) ≠ ∞ :=
      (continuous_boundary_memLp Ω hΩ hc p (fun x => a (some j) x * f x)
        ((ha (some j)).continuous.mul hf.continuous)).ne
    have hreal := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun j _ => hfinite j)) hnorm
    rw [ENNReal.toReal_sum (fun j _ => hfinite j)] at hreal
    apply hreal.trans
    calc
      _ ≤ ∑ j, C j * ‖u‖ := Finset.sum_le_sum (fun j _ => hC j u f hf hu)
      _ = _ := (Finset.sum_mul _ _ _).symm

/-- Compact C1 boundary trace existence, with no assumed numerical inequality. -/
theorem trace_exists_of_compact_boundary (hp : p ≠ ∞)
    (hΩ : IsC1Domain Ω) (hc : IsCompact (frontier (Ω : Set (Domain d)))) :
    ∃! T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p, IsTrace T := by
  obtain ⟨C, hC0, hC⟩ := exists_smooth_trace_bound (𝕜 := 𝕜) hp hΩ hc
  exact exists_trace_of_smooth_bound Ω p hΩ hc hp C hC

/-- The full bounded-domain trace existence obligation. -/
theorem trace_exists : Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel.TraceExists := by
  intro 𝕜 _ d Ω hb hΩ p _ hp
  exact trace_exists_of_compact_boundary hp hΩ
    (hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure)

end ExpandedFA.Sobolev.Trace


namespace ExpandedFA.Sobolev.Trace
open ExpandedFA.Distributions C1Extension
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- The full zero-extension versus original compact-test closure characterization. -/
theorem zeroSpace_extension_criterion :
    Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel.ZeroSpaceExtensionCriterion := by
  intro 𝕜 _ d Ω hb hΩ p _ hp u
  exact hasSobolevZeroExtension_iff_mem_zeroSpace hp hΩ hb u

/-- A Sobolev zero extension forces every bounded trace agreeing with smooth
restriction to vanish, using the proved geometric closure characterization. -/
theorem trace_zero_of_hasSobolevZeroExtension {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hΩ : IsC1Domain Ω) (hb : Bornology.IsBounded (Ω : Set (Domain d)))
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (u : SpaceValue 𝕜 d Ω 1 p) (hu : HasSobolevZeroExtension u) : T u = 0 := by
  exact kernel_contains_zeroSpace 𝕜 d Ω p hp T hT
    (zeroSpace_of_hasSobolevZeroExtension hp hΩ hb u hu)

end ExpandedFA.Sobolev.Trace


namespace ExpandedFA.Sobolev.Trace
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open C1Extension HalfSpace Lines

section GeneralKernelAssembly
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma continuous_insertNth_zero {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun z : Domain n => i.insertNth (α := fun _ => ℝ) 0 z) := by
  apply continuous_pi
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simpa only [Fin.insertNth_apply_same] using
      (continuous_const : Continuous (fun _ : Domain n => (0 : ℝ)))
  · simpa only [Fin.insertNth_apply_succAbove] using
      (continuous_apply k : Continuous (fun z : Domain n => z k))

/-- A genuine bounded chart flattening transports zero general trace to zero
flat trace. The comparison is first numerical on smooth members and then
extends over the original Sobolev graph by density. -/
theorem exists_flattened_trace_comparison {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (Ω : Opens (Domain (n + 1))) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (i : Fin (n + 1))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1)))
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    {K : ℝ≥0} (hLip : LipschitzOnWith K Φ Φ.source)
    (θ χ : Tests 𝕜 (⊤ : Opens (Domain (n + 1)))) (hχ : tsupport χ ⊆ Φ.target)
    (E : SpaceValue 𝕜 (n + 1) Ω 1 p →L[𝕜] SpaceValue 𝕜 (n + 1) (upper i) 1 p)
    (hE : ∀ (u : SpaceValue 𝕜 (n + 1) Ω 1 p) (f : Domain (n + 1) → 𝕜),
      ContDiff ℝ (⊤ : ℕ∞) f →
      u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n + 1)))] f →
      ContDiff ℝ 1 (fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y))) ∧
      (E u).val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))]
        fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y)))
    (T : SpaceValue 𝕜 (n + 1) Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (S : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) (hS : IsCoordinateTrace i S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖S (E u)‖ ≤ C * ‖T u‖ := by
  obtain ⟨D, hD, hDbound⟩ := boundary_chart_pullback_eLpNorm_le Ω Φ i hside hLip
  obtain ⟨Cχ, hCχ0, hCχ, _⟩ := ambient_test_bounds χ
  obtain ⟨Cθ, hCθ0, hCθ, _⟩ := ambient_test_bounds θ
  let A : ℝ≥0∞ := ENNReal.ofReal (Cχ * Cθ) * D ^ (1 / p).toReal
  have hA : A ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hD.ne).ne
  have hsmooth : ∀ u ∈ SmoothUpToBoundary (𝕜 := 𝕜) Ω p,
      ‖S (E u)‖ ≤ A.toReal * ‖T u‖ := by
    rintro u ⟨f, hf, hu⟩
    let g : Domain (n + 1) → 𝕜 := fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y))
    let G : Domain n → 𝕜 := fun z => g (i.insertNth 0 z)
    obtain ⟨hg, hEu⟩ := hE u f hf hu
    have hG : Continuous G := hg.continuous.comp (continuous_insertNth_zero i)
    have hgB : Continuous (fun y : Transverse i => g (coordinateLine i y 0)) := by
      apply hg.continuous.comp
      apply continuous_pi
      intro j
      dsimp [coordinateLine]
      split_ifs
      · exact continuous_const
      · exact continuous_apply _
    have he := eLpNorm_comp_measurePreserving (p := p) hgB.aestronglyMeasurable
      (transverseFinEquiv_measurePreserving i)
    have heqfun : (fun y : Transverse i => g (coordinateLine i y 0)) ∘ transverseFinEquiv i = G := by
      funext z
      simp only [Function.comp_apply, coordinateLine_transverseFinEquiv]
      rfl
    rw [heqfun] at he
    have hGsource : eLpNorm G p volume =
        eLpNorm G p (volume.restrict (boundaryParameters Φ i)) := by
      have hind : (boundaryParameters Φ i).indicator G = G := by
        funext z
        by_cases hz : z ∈ boundaryParameters Φ i
        · exact indicator_of_mem hz _
        · rw [indicator_of_notMem hz]
          have hzχ : i.insertNth (α := fun _ => ℝ) 0 z ∉ tsupport χ :=
            fun hh => hz (hχ hh)
          dsimp [G, g]
          rw [image_eq_zero_of_notMem_tsupport hzχ, zero_mul]
      calc
        _ = eLpNorm ((boundaryParameters Φ i).indicator G) p volume :=
          congrArg (fun F : Domain n → 𝕜 => eLpNorm F p volume) hind.symm
        _ = _ := eLpNorm_indicator_eq_eLpNorm_restrict
          (boundaryParameters_isOpen Φ i).measurableSet.nullMeasurableSet
    have hcomp : eLpNorm G p (volume.restrict (boundaryParameters Φ i)) ≤
        ENNReal.ofReal (Cχ * Cθ) *
          eLpNorm (f ∘ boundaryParam Φ i) p (volume.restrict (boundaryParameters Φ i)) := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul hG.aestronglyMeasurable _ p
      apply Filter.Eventually.of_forall
      intro z
      change ‖χ (i.insertNth 0 z) * (θ (Φ.symm (i.insertNth 0 z)) *
        f (Φ.symm (i.insertNth 0 z)))‖ ≤ (Cχ * Cθ) * ‖f (Φ.symm (i.insertNth 0 z))‖
      simp only [norm_mul]
      calc
        _ ≤ Cχ * (Cθ * ‖f (Φ.symm (i.insertNth 0 z))‖) :=
          mul_le_mul (hCχ _) (mul_le_mul_of_nonneg_right (hCθ _) (norm_nonneg _))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCχ0
        _ = _ := by ring
    have hbound : eLpNorm G p volume ≤ A * eLpNorm f p (surfaceMeasure Ω) := by
      rw [hGsource]
      refine hcomp.trans ?_
      have hb := hDbound f p hf.continuous
      have hstep : ENNReal.ofReal (Cχ * Cθ) *
          eLpNorm (f ∘ boundaryParam Φ i) p (volume.restrict (boundaryParameters Φ i)) ≤
          ENNReal.ofReal (Cχ * Cθ) * (D ^ (1 / p).toReal * eLpNorm f p (surfaceMeasure Ω)) := by
        gcongr
      exact hstep.trans_eq (by simp only [A, mul_assoc])
    rw [← eLpNorm_congr_ae (hS (E u) g hg hEu)] at he
    rw [← eLpNorm_congr_ae (hT u f hf hu)] at hbound
    have hfin : A * eLpNorm (T u) p (surfaceMeasure Ω) ≠ ∞ :=
      ENNReal.mul_ne_top hA (Lp.eLpNorm_ne_top _)
    have hreal := ENNReal.toReal_mono hfin hbound
    rw [he, ENNReal.toReal_mul, ← Lp.norm_def, ← Lp.norm_def] at hreal
    exact hreal
  refine ⟨A.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro u
  have hc : IsClosed {v : SpaceValue 𝕜 (n + 1) Ω 1 p |
      ‖S (E v)‖ ≤ A.toReal * ‖T v‖} :=
    isClosed_le (S.continuous.comp E.continuous).norm
      (continuous_const.mul T.continuous.norm)
  exact hc.closure_subset_iff.mpr hsmooth (hdense u)



/-- A localized flattening can be transported back continuously to the original
chart. A second cutoff equal to one on the first support ensures exact
recovery of the original localized Sobolev element, including nonsmooth data. -/
theorem exists_localized_flattening_recovery (hp : p ≠ ∞)
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (hBinv : ∀ x ∈ Φ.target, ‖fderiv ℝ Φ.symm x‖ ≤ B)
    (hTarget : Bornology.IsBounded Φ.target)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    (θ : Tests 𝕜 (⊤ : Opens (Domain d))) (hθ : tsupport θ ⊆ Φ.source)
    (χ : Tests 𝕜 (⊤ : Opens (Domain d)))
    (hχone : ∀ x ∈ tsupport θ, χ (Φ x) = 1)
    (E : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d (upper i) 1 p)
    (hE : ∀ (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
      ContDiff ℝ (⊤ : ℕ∞) f →
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f →
      ContDiff ℝ 1 (fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y))) ∧
      (E u).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y))) :
    ∃ F : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p,
      (∀ z, z ∈ ZeroSpaceValue 𝕜 d (upper i) 1 p hp →
        F z ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp) ∧
      ∀ u, (F (E u)).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        fun x => θ x * u.val (zeroIndex d 1) x := by
  obtain ⟨η, hη, hηone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜)
    (tsupport θ) θ.hasCompactSupport ⟨Φ.source, Φ.open_source⟩ hθ
  obtain ⟨J, hJ1, hJbound⟩ := Transport.exists_det_bound_of_norm_bound (E := Domain d) B
  have hJtgt : ∀ x ∈ Φ.target, |(fderiv ℝ Φ.symm x).det| ≤ J :=
    fun x hx => hJbound _ (hBinv x hx)
  obtain ⟨F, hF⟩ := exists_localized_chart_pullback (p := p) (Ω := Ω) (upper i)
    Φ hΦ hInv B hB0 hB J hJ1 hJtgt hTarget hside η hη
  obtain ⟨Cθ, hCθ0, hCθ, hDθ⟩ := ambient_test_bounds θ
  let M : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p :=
    ambientMultiply θ θ.contDiff Cθ hCθ0 hCθ hDθ
  have hrecovery : F.comp E = M := by
    have heq : EqOn (F.comp E) M (SmoothUpToBoundary (𝕜 := 𝕜) Ω p) := by
      rintro u ⟨f, hf, hu⟩
      let g : Domain d → 𝕜 := fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y))
      have hEu := (hE u f hf hu).2
      have hFE := hF (E u) g hEu
      have hM := ambientMultiply_coe θ θ.contDiff Cθ hCθ0 hCθ hDθ u
      apply sobolev_underlying_injective 𝕜 d Ω 1 p
      apply Lp.ext
      filter_upwards [hFE, hM, hu] with x hx hMx hux
      change (F (E u)).val (zeroIndex d 1) x = (M u).val (zeroIndex d 1) x
      rw [hx, hMx, hux]
      change η x * (χ (Φ x) * (θ (Φ.symm (Φ x)) * f (Φ.symm (Φ x)))) = θ x * f x
      by_cases hxs : x ∈ Φ.source
      · rw [Φ.left_inv hxs]
        by_cases hxθ : x ∈ tsupport θ
        · rw [hηone x hxθ, hχone x hxθ, one_mul, one_mul]
        · rw [image_eq_zero_of_notMem_tsupport hxθ, zero_mul, mul_zero, mul_zero]
      · have hxη : x ∉ tsupport η := fun hh => hxs (hη hh)
        have hxθ : x ∉ tsupport θ := fun hh => hxs (hθ hh)
        rw [image_eq_zero_of_notMem_tsupport hxη, zero_mul,
          image_eq_zero_of_notMem_tsupport hxθ, zero_mul]
    apply ContinuousLinearMap.ext
    intro u
    exact heq.closure (F.comp E).continuous M.continuous (hdense u)
  refine ⟨F, ?_, ?_⟩
  · intro z hz
    exact localized_pullback_mem_zeroSpace hp (upper i) Φ hside η hη F hF z hz
  · intro u
    have heq := congrArg (fun L : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p => L u) hrecovery
    change F (E u) = M u at heq
    rw [heq]
    exact ambientMultiply_coe θ θ.contDiff Cθ hCθ0 hCθ hDθ u



lemma flattened_localization_supported
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (θ χ : Tests 𝕜 (⊤ : Opens (Domain d)))
    (E : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d (upper i) 1 p)
    (hE : ∀ (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
      ContDiff ℝ (⊤ : ℕ∞) f →
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f →
      ContDiff ℝ 1 (fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y))) ∧
      (E u).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y)))
    (u : SpaceValue 𝕜 d Ω 1 p) :
    ∀ᵐ y ∂volume.restrict (upper i : Set (Domain d)),
      y ∉ tsupport χ → (E u).val (zeroIndex d 1) y = 0 := by
  let U : Opens (Domain d) := upper i ⊓ ⟨(tsupport χ)ᶜ, (isClosed_tsupport χ).isOpen_compl⟩
  let R : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] SpaceValue 𝕜 d U 1 p :=
    restrictSobolev inf_le_left
  have hc : IsClosed {w : SpaceValue 𝕜 d Ω 1 p | R (E w) = 0} :=
    isClosed_eq (R.continuous.comp E.continuous) continuous_const
  have hs : SmoothUpToBoundary (𝕜 := 𝕜) Ω p ⊆ {w | R (E w) = 0} := by
    rintro w ⟨f, hf, hw⟩
    apply sobolev_underlying_injective 𝕜 d U 1 p
    apply Lp.ext
    filter_upwards [restrictSobolev_coe (inf_le_left : U ≤ upper i) (E w) (zeroIndex d 1),
      ((hE w f hf hw).2).filter_mono (ae_mono (Measure.restrict_mono inter_subset_left le_rfl)),
      ae_restrict_mem U.isOpen.measurableSet,
      Lp.coeFn_zero 𝕜 p (volume.restrict (U : Set (Domain d)))] with y hry hey hyU hzy
    change (R (E w)).val (zeroIndex d 1) y = (0 : DomainLp 𝕜 U p) y
    rw [hry, hey, hzy, image_eq_zero_of_notMem_tsupport hyU.2, zero_mul]
    rfl
  have hRu : R (E u) = 0 := hc.closure_subset_iff.mpr hs (hdense u)
  have hz : ∀ᵐ y ∂volume.restrict (U : Set (Domain d)), (E u).val (zeroIndex d 1) y = 0 := by
    have hr := restrictSobolev_coe (inf_le_left : U ≤ upper i) (E u) (zeroIndex d 1)
    change (R (E u)).val (zeroIndex d 1) =ᵐ[volume.restrict (U : Set (Domain d))]
      (E u).val (zeroIndex d 1) at hr
    rw [hRu] at hr
    exact hr.symm.trans (Lp.coeFn_zero 𝕜 p (volume.restrict (U : Set (Domain d))))
  have hzglobal : ∀ᵐ y ∂volume, y ∈ U → (E u).val (zeroIndex d 1) y = 0 :=
    ae_imp_of_ae_restrict hz
  filter_upwards [ae_restrict_of_ae hzglobal, ae_restrict_mem (upper i).isOpen.measurableSet]
    with y hy hyupper hyχ
  exact hy ⟨hyupper, hyχ⟩

lemma coordinate_zero_trace_mem_zeroSpace_of_compact_support (hp : p ≠ ∞)
    (i : Fin d)
    (T : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] Lp 𝕜 p (volume : Measure (Transverse i)))
    (hT : IsCoordinateTrace i T) (u : SpaceValue 𝕜 d (upper i) 1 p) (hu : T u = 0)
    (K : Set (Domain d)) (hK : IsCompact K)
    (hsupp : ∀ᵐ y ∂volume.restrict (upper i : Set (Domain d)),
      y ∉ K → u.val (zeroIndex d 1) y = 0) :
    u ∈ ZeroSpaceValue 𝕜 d (upper i) 1 p hp := by
  obtain ⟨v, hv⟩ := hasSobolevZeroExtension_of_coordinate_trace_zero i hp T hT u hu
  have hsupp_global : ∀ᵐ y ∂volume, y ∈ upper i →
      y ∉ K → u.val (zeroIndex d 1) y = 0 := ae_imp_of_ae_restrict hsupp
  have hvK : ∀ᵐ y ∂volume, y ∉ K → v.val (zeroIndex d 1) y = 0 := by
    filter_upwards [hv, hsupp_global] with y hvy hsy hyK
    rw [hvy]
    by_cases hyH : y ∈ upper i
    · rw [indicator_of_mem hyH, hsy hyH hyK]
    · exact indicator_of_notMem hyH _
  have hvH : ∀ᵐ y ∂volume, y i < 0 → v.val (zeroIndex d 1) y = 0 := by
    filter_upwards [hv] with y hvy hyneg
    rw [hvy]
    apply indicator_of_notMem
    intro hyH
    change 0 < y i at hyH
    exact (not_lt_of_ge (le_of_lt hyneg)) hyH
  have hmem := upper_restrict_mem_zeroSpace_of_compact_support hp i v K hK hvK hvH
  have hr : restrictSobolev (le_top : upper i ≤ ⊤) v = u := by
    apply sobolev_underlying_injective 𝕜 d (upper i) 1 p
    apply Lp.ext
    filter_upwards [restrictSobolev_coe (le_top : upper i ≤ ⊤) v (zeroIndex d 1),
      ae_restrict_of_ae hv, ae_restrict_mem (upper i).isOpen.measurableSet] with y hy hvy hyH
    rw [hy, hvy, indicator_of_mem hyH]
  simpa only [hr] using hmem



/-- A zero general trace gives an original W0 member after any compact
boundary-chart localization. -/
theorem localized_zeroSpace_of_trace_zero {n : ℕ} (Ω : Opens (Domain (n + 1)))
    (hp : p ≠ ∞) (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (i : Fin (n + 1)) (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1)))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (hBinv : ∀ x ∈ Φ.target, ‖fderiv ℝ Φ.symm x‖ ≤ B)
    (hSource : Bornology.IsBounded Φ.source) (hTarget : Bornology.IsBounded Φ.target)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    {K : ℝ≥0} (hLip : LipschitzOnWith K Φ Φ.source)
    (θ : Tests 𝕜 (⊤ : Opens (Domain (n + 1)))) (hθ : tsupport θ ⊆ Φ.source)
    (T : SpaceValue 𝕜 (n + 1) Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (u : SpaceValue 𝕜 (n + 1) Ω 1 p) (hu : T u = 0) :
    ∃ w : SpaceValue 𝕜 (n + 1) Ω 1 p, w ∈ ZeroSpaceValue 𝕜 (n + 1) Ω 1 p hp ∧
      w.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n + 1)))]
        fun x => θ x * u.val (zeroIndex (n + 1) 1) x := by
  obtain ⟨χ, hχ, hχone, E, hE⟩ := exists_flattened_localization (p := p) i Φ hΦ hInv B hB0
    hB hBinv hSource hside θ hθ
  obtain ⟨S, hS, hSuniq⟩ := coordinate_upper_trace_exists (𝕜 := 𝕜) i hp
  obtain ⟨C, hC0, hcomp⟩ := exists_flattened_trace_comparison Ω hdense i Φ hside hLip
    θ χ hχ E hE T hT S hS
  have hzero : S (E u) = 0 := norm_le_zero_iff.mp (by simpa only [hu, norm_zero, mul_zero] using hcomp u)
  have hflat : E u ∈ ZeroSpaceValue 𝕜 (n + 1) (upper i) 1 p hp :=
    coordinate_zero_trace_mem_zeroSpace_of_compact_support hp i S hS (E u) hzero
      (tsupport χ) χ.hasCompactSupport (flattened_localization_supported hdense i Φ θ χ E hE u)
  obtain ⟨F, hFW0, hFrec⟩ := exists_localized_flattening_recovery hp hdense i Φ hΦ hInv
    B hB0 hB hBinv hTarget hside θ hθ χ hχone E hE
  exact ⟨F (E u), hFW0 (E u) hflat, hFrec u⟩

theorem zeroSpace_of_trace_zero (hp : p ≠ ∞)
    (hΩ : IsC1Domain Ω) (hb : Bornology.IsBounded (Ω : Set (Domain d)))
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (u : SpaceValue 𝕜 d Ω 1 p) (hu : T u = 0) :
    u ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp := by
  classical
  cases d with
  | zero =>
    rw [zeroSpace_zero_dim Ω 1 p hp]
    trivial
  | succ r =>
    have hcompact : IsCompact (frontier (Ω : Set (Domain (r + 1)))) :=
      hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
    obtain ⟨n, i, Φ, B, K, L, hB0, hcharts, hLip, hcover⟩ :=
      finite_bounded_bilipschitz_boundary_charts (r + 1) Ω hΩ hcompact
    have hdense := C1Extension.smooth_density 𝕜 (r + 1) Ω hΩ hcompact p hp
    obtain ⟨a, S, C, ha, hC0, hC, hD, hsum, hsupp, hSc, hSΩ, hS⟩ :=
      finite_scalar_boundary_localization (𝕜 := 𝕜) Ω (fun j => (Φ j).source)
        (fun j => (Φ j).open_source) hcover hcompact
    have hpiece (k : Option (Fin n)) :
        ∃ w : SpaceValue 𝕜 (r + 1) Ω 1 p, w ∈ ZeroSpaceValue 𝕜 (r + 1) Ω 1 p hp ∧
          w.val (zeroIndex (r + 1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (r + 1)))]
            fun x => a k x * u.val (zeroIndex (r + 1) 1) x := by
      cases k with
      | none =>
        let w := ambientMultiply (a none) (ha none) C hC0 (hC none) (hD none) u
        let K : Set (Domain (r + 1)) := closure (Ω : Set (Domain (r + 1))) ∩ tsupport (a none)
        have hK : IsCompact K := hb.isCompact_closure.inter_right (isClosed_tsupport _)
        have hKΩ : K ⊆ Ω := hS.trans hSΩ
        have hw := ambientMultiply_coe (a none) (ha none) C hC0 (hC none) (hD none) u
        refine ⟨w, mem_zeroSpace_of_compact_support hp w K hK hKΩ ?_, hw⟩
        filter_upwards [hw, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ hxK
        rw [hx]
        have hxnone : x ∉ tsupport (a none) := fun hh => hxK ⟨subset_closure hxΩ, hh⟩
        rw [image_eq_zero_of_notMem_tsupport hxnone, zero_mul]
      | some j =>
        let θ : Tests 𝕜 (⊤ : Opens (Domain (r + 1))) :=
          ⟨a (some j), ha (some j), (hsupp j).1, by simp⟩
        obtain ⟨hΦ, hInv, hbsource, hbtarget, hside, hder, hderInv⟩ := hcharts j
        exact localized_zeroSpace_of_trace_zero Ω hp hdense (i j) (Φ j) hΦ hInv B hB0
          hder hderInv hbsource hbtarget hside (hLip j).1 θ (hsupp j).2 T hT u hu
    choose w hw hrep using hpiece
    have hsum_mem : (∑ k, w k) ∈ ZeroSpaceValue 𝕜 (r + 1) Ω 1 p hp :=
      Submodule.sum_mem _ (fun k _ => hw k)
    have heq : (∑ k, w k) = u := by
      apply sobolev_underlying_injective 𝕜 (r + 1) Ω 1 p
      apply Lp.ext
      let P : SpaceValue 𝕜 (r + 1) Ω 1 p →ₗ[𝕜] DomainLp 𝕜 Ω p :=
        (PiLp.projₗ 1 _ (zeroIndex (r + 1) 1)).comp (derivativeGraph 𝕜 Ω 1 p).subtype
      have hproj : (∑ k, w k).val (zeroIndex (r + 1) 1) = ∑ k, (w k).val (zeroIndex (r + 1) 1) :=
        map_sum P w Finset.univ
      change (∑ k, w k).val (zeroIndex (r + 1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (r + 1)))]
        u.val (zeroIndex (r + 1) 1)
      rw [hproj]
      filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun k => (w k).val (zeroIndex (r + 1) 1)),
        ae_all_iff.mpr hrep] with x hx hk
      rw [hx]
      simp only [Finset.sum_apply, hk]
      rw [← Finset.sum_mul]
      have hsumx : ∑ k, a k x = 1 := by simpa only [Fintype.sum_option] using hsum x
      rw [hsumx, one_mul]
    simpa only [heq] using hsum_mem
  


/-- The complete trace kernel is the original compact-test Sobolev closure. -/
theorem trace_kernel : Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel.TraceKernel := by
  intro 𝕜 _ d Ω hb hΩ p _ hp T hT
  apply le_antisymm
  · intro u hu
    exact zeroSpace_of_trace_zero hp hΩ hb T hT u hu
  · exact kernel_contains_zeroSpace 𝕜 d Ω p hp T hT

/-- Zero trace is equivalent to existence of the actual Sobolev zero extension. -/
theorem zero_extension_criterion :
    Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel.ZeroExtensionCriterion := by
  intro 𝕜 _ d Ω hb hΩ p _ hp T hT u
  rw [hasSobolevZeroExtension_iff_mem_zeroSpace hp hΩ hb u]
  change u ∈ T.ker ↔ u ∈ ZeroSpaceValue 𝕜 d Ω 1 p hp
  rw [trace_kernel 𝕜 d Ω hb hΩ p hp T hT]



end GeneralKernelAssembly
end ExpandedFA.Sobolev.Trace
