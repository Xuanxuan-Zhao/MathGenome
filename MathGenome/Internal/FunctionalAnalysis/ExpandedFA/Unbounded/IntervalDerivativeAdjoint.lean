import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.IntervalDerivativeAdjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.HilbertAdjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.OneDimensionalSobolev
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevTraceAndKernel
import Mathlib.Analysis.Calculus.Deriv.Star

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal Topology

namespace ExpandedFA.Unbounded.IntervalDerivative
open ExpandedFA.Sobolev ExpandedFA.Sobolev.OneDimensional

lemma baseMap_injective : Function.Injective baseMap :=
  sobolev_underlying_injective ℂ 1 (lineDomain interval) 1 2

lemma maximalGraph_vertical (x : L2 × L2) (hx : x ∈ maximalGraph)
    (hzero : x.1 = 0) : x.2 = 0 := by
  obtain ⟨u, rfl⟩ := hx
  change baseMap u = 0 at hzero
  have hu : u = 0 := baseMap_injective (hzero.trans (map_zero baseMap).symm)
  simp [hu]

lemma minimalGraph_le : minimalGraph ≤ maximalGraph := by
  rintro x ⟨u, rfl⟩
  exact ⟨u.val, rfl⟩

theorem graphs : Specs.ExpandedFA.Unbounded.IntervalDerivativeAdjoint.Graphs := by
  constructor
  · exact Submodule.toLinearPMap_graph_eq _
      (fun x hx hzero => maximalGraph_vertical x (minimalGraph_le hx) hzero)
  · exact Submodule.toLinearPMap_graph_eq _ maximalGraph_vertical

theorem domains : Specs.ExpandedFA.Unbounded.IntervalDerivativeAdjoint.Domains := by
  constructor
  · ext x
    change x ∈ minimalGraph.map (LinearMap.fst ℂ L2 L2) ↔ _
    constructor
    · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
      exact ⟨u.val, u.property, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨momentumPair u, ⟨⟨u, hu⟩, rfl⟩, rfl⟩
  · change maximalGraph.map (LinearMap.fst ℂ L2 L2) = _
    rw [maximalGraph, ← LinearMap.range_comp]
    rfl

lemma minimal_graph_mem (u : H1) (hu : u ∈ zeroBoundary) :
    (baseLp u, (-Complex.I) • derivativeLp u) ∈ minimal.graph := by
  rw [graphs.1]
  exact ⟨⟨u, hu⟩, rfl⟩

lemma maximal_graph_mem (u : H1) :
    (baseLp u, (-Complex.I) • derivativeLp u) ∈ maximal.graph := by
  rw [graphs.2]
  exact ⟨u, rfl⟩

lemma closure_interval : _root_.closure (interval : Set ℝ) = Icc 0 1 :=
  closure_Ioo (by norm_num)

/-- An extension used in the proof only; its restriction is every specified
primitive representative. Its derivative is the zero-extended weak derivative. -/
def primitiveExtension (u : H1) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  canonicalPrimitive (derivativeLp u) t + f 0

lemma primitiveExtension_eq (u : H1) (f : ℝ → ℂ)
    (hf : PrimitiveRepresentative u f) :
    EqOn (primitiveExtension u f) f (Icc 0 1) := by
  intro t ht
  have ht' : t ∈ _root_.closure (interval : Set ℝ) := closure_interval.symm ▸ ht
  have h0 : (0 : ℝ) ∈ _root_.closure (interval : Set ℝ) := by rw [closure_interval]; norm_num
  have hp := canonicalPrimitive_sub_eq ordConnected_Ioo (derivativeLp u) ht' h0
  have hf' := (hf.2.2.2 t ht' 0 h0).2
  simp only [canonicalPrimitive, intervalIntegral.integral_same] at hp
  dsimp [primitiveExtension, canonicalPrimitive]
  linear_combination hp - hf'

lemma primitiveExtension_continuous (u : H1) (f : ℝ → ℂ) :
    Continuous (primitiveExtension u f) :=
  (canonicalPrimitive_continuous (derivativeLp u)).add continuous_const

lemma primitiveExtension_ac (u : H1) (f : ℝ → ℂ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (primitiveExtension u f) a b :=
  (canonicalPrimitive_absolutelyContinuous (derivativeLp u) a b).add
    (contDiff_const.contDiffOn.absolutelyContinuousOnInterval (f := fun _ : ℝ => f 0))

lemma primitiveExtension_deriv (u : H1) (f : ℝ → ℂ) :
    ∀ᵐ t ∂volume, HasDerivAt (primitiveExtension u f)
      (extendedLineFunction (derivativeLp u) t) t := by
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral
    (extendedLineFunction_locallyIntegrable (derivativeLp u))] with t ht
  change HasDerivAt (fun x => (∫ s in 0..x, extendedLineFunction (derivativeLp u) s) + f 0) _ _
  exact (ht 0).add_const (f 0)

theorem absolutelyContinuous_representatives :
    Specs.ExpandedFA.Unbounded.IntervalDerivativeAdjoint.AbsolutelyContinuousRepresentatives := by
  intro u f hf
  apply (primitiveExtension_ac u f 0 1).congr
  simpa only [uIcc_of_le zero_le_one] using primitiveExtension_eq u f hf

lemma inner_lineIntegral (v w : L2) :
    inner ℂ v w = ∫ t in (0 : ℝ)..1, star (lineFunction v t) * lineFunction w t := by
  rw [L2.inner_def]
  simp_rw [RCLike.inner_apply']
  change (∫ z, star (v z) * w z ∂volume.restrict (lineDomain interval : Set (ExpandedFA.Distributions.Domain 1))) = _
  have hp : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
      (volume.restrict (interval : Set ℝ))
      (volume.restrict (lineDomain interval : Set (ExpandedFA.Distributions.Domain 1))) :=
    linePoint_measurePreserving interval
  rw [← hp.integral_comp' (fun z => star (v z) * w z)]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rfl

lemma extendedLineFunction_ae (v : L2) :
    extendedLineFunction v =ᵐ[volume.restrict (interval : Set ℝ)] lineFunction v := by
  filter_upwards [ae_restrict_mem isOpen_Ioo.measurableSet] with t ht
  exact indicator_of_mem ht _

lemma primitiveExtension_ae (u : H1) (f : ℝ → ℂ)
    (hf : PrimitiveRepresentative u f) :
    lineFunction (baseLp u) =ᵐ[volume.restrict (interval : Set ℝ)]
      primitiveExtension u f := by
  filter_upwards [represents_lineFunction_ae (baseLp u) hf.2.1,
    ae_restrict_mem isOpen_Ioo.measurableSet] with t ht hti
  exact ht.trans (primitiveExtension_eq u f hf (Ioo_subset_Icc_self hti)).symm

lemma inner_lineIntegral_congr (v w : L2) (f g : ℝ → ℂ)
    (hf : lineFunction v =ᵐ[volume.restrict (interval : Set ℝ)] f)
    (hg : lineFunction w =ᵐ[volume.restrict (interval : Set ℝ)] g) :
    inner ℂ v w = ∫ t in (0 : ℝ)..1, star (f t) * g t := by
  rw [inner_lineIntegral]
  simp only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [hf, hg] with t ht ht'
  rw [ht, ht']

/-- Integration by parts for the AC extensions of the two H¹ classes. -/
lemma weak_derivative_inner_sum (u v : H1) (f g : ℝ → ℂ)
    (hf : PrimitiveRepresentative u f) (hg : PrimitiveRepresentative v g) :
    inner ℂ (derivativeLp u) (baseLp v) + inner ℂ (baseLp u) (derivativeLp v) =
      star (f 1) * g 1 - star (f 0) * g 0 := by
  let F := primitiveExtension u f
  let G := primitiveExtension v g
  let du := extendedLineFunction (derivativeLp u)
  let dv := extendedLineFunction (derivativeLp v)
  have hdu : LocallyIntegrable (fun t => star (du t)) volume :=
    fun t => Complex.conjCLE.toContinuousLinearMap.integrableAtFilter_comp
      (extendedLineFunction_locallyIntegrable (derivativeLp u) t)
  have h₁ : LocallyIntegrable (fun t => star (du t) * G t) volume :=
    hdu.mul_continuous (primitiveExtension_continuous v g)
  have h₂ : LocallyIntegrable (fun t => star (F t) * dv t) volume :=
    (extendedLineFunction_locallyIntegrable (derivativeLp v)).continuous_mul
      (primitiveExtension_continuous u f).star
  have hac : AbsolutelyContinuousOnInterval (fun t => star (F t) * G t) 0 1 := by
    have hs := Complex.isometry_conj.lipschitzWith.comp_absolutelyContinuousOnInterval
      (primitiveExtension_ac u f 0 1)
    convert! hs.smul (primitiveExtension_ac v g 0 1) using 1
  have hd : ∀ᵐ t ∂volume, t ∈ uIcc (0 : ℝ) 1 →
      HasDerivAt (fun t => star (F t) * G t)
        (star (du t) * G t + star (F t) * dv t) t := by
    filter_upwards [primitiveExtension_deriv u f, primitiveExtension_deriv v g] with t ht ht' _
    exact ht.star.mul ht'
  have he := integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt hac (h₁.add h₂) hd
  have hi₁ : IntervalIntegrable (fun t => star (du t) * G t) volume 0 1 :=
    (h₁.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hi₂ : IntervalIntegrable (fun t => star (F t) * dv t) volume 0 1 :=
    (h₂.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  simp only [Pi.add_apply] at he
  rw [intervalIntegral.integral_add hi₁ hi₂] at he
  rw [← inner_lineIntegral_congr (derivativeLp u) (baseLp v) du G
      (extendedLineFunction_ae _).symm (primitiveExtension_ae v g hg),
    ← inner_lineIntegral_congr (baseLp u) (derivativeLp v) F dv
      (primitiveExtension_ae u f hf) (extendedLineFunction_ae _).symm] at he
  have hu0 := primitiveExtension_eq u f hf (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
  have hu1 := primitiveExtension_eq u f hf (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  have hv0 := primitiveExtension_eq v g hg (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
  have hv1 := primitiveExtension_eq v g hg (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  simpa only [F, G, hu0, hu1, hv0, hv1] using he

theorem boundary_form : Specs.ExpandedFA.Unbounded.IntervalDerivativeAdjoint.BoundaryForm := by
  intro u v f g hf hg
  have he := weak_derivative_inner_sum u v f g hf hg
  rw [inner_smul_left, inner_smul_right]
  simp only [map_neg, Complex.conj_I]
  linear_combination Complex.I * he

open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Complex conjugation preserves test functions on this real domain. -/
def conjugateTest (φ : Tests ℂ (lineDomain interval)) : Tests ℂ (lineDomain interval) :=
  ⟨fun z => star (φ z), Complex.conjCLE.contDiff.comp φ.contDiff,
    φ.hasCompactSupport.comp_left (by simp),
    (tsupport_comp_subset (g := star) (by simp) φ).trans φ.tsupport_subset⟩

@[simp] lemma conjugateTest_apply (φ : Tests ℂ (lineDomain interval)) (z : Domain 1) :
    conjugateTest φ z = star (φ z) := rfl

lemma conjugateTest_partial (φ : Tests ℂ (lineDomain interval)) (z : Domain 1) :
    testPartialCLM [0] (conjugateTest φ) z = star (testPartialCLM [0] φ z) := by
  rw [← linePoint_coordinate z, ← test_line_deriv, ← test_line_deriv]
  exact deriv.star

lemma testToSobolev_zeroBoundary (φ : Tests ℂ (lineDomain interval)) :
    testToSobolev (p := 2) 1 φ ∈ zeroBoundary := by
  apply (smoothSubmodule ℂ 1 (lineDomain interval) 1 2).le_topologicalClosure
  exact ⟨φ, by rw [testToSobolev_underlying]; exact testToDomainLp_coe φ⟩

lemma test_mem_minimal (φ : Tests ℂ (lineDomain interval)) :
    testToDomainLp (p := 2) φ ∈ minimal.domain := by
  rw [domains.1]
  exact ⟨testToSobolev (p := 2) 1 φ, testToSobolev_zeroBoundary φ,
    testToSobolev_underlying 1 φ⟩

lemma inner_conjugateTest (φ : Tests ℂ (lineDomain interval)) (v : L2) :
    inner ℂ (testToDomainLp (p := 2) (conjugateTest φ)) v = lpDistribution v φ := by
  rw [L2.inner_def, lpDistribution_apply]
  apply integral_congr_ae
  filter_upwards [testToDomainLp_coe (p := 2) (conjugateTest φ)] with z hz
  rw [RCLike.inner_apply', hz, conjugateTest_apply]
  simp

theorem dense_domain : Specs.ExpandedFA.Unbounded.IntervalDerivativeAdjoint.DenseDomain := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hv0 : v = 0 := by
    apply lpDistribution_injective
    change lpDistributionLM v = lpDistributionLM 0
    rw [map_zero]
    ext φ
    change lpDistribution v φ = 0
    rw [← inner_conjugateTest]
    exact (minimal.domain.mem_orthogonal v).mp hv _ (test_mem_minimal (conjugateTest φ))
  exact hv0

lemma minimal_apply (u : H1) (hu : u ∈ zeroBoundary) (h : baseLp u ∈ minimal.domain) :
    minimal ⟨baseLp u, h⟩ = (-Complex.I) • derivativeLp u := by
  obtain ⟨h', he⟩ := (mem_graph_iff minimal _).mp (minimal_graph_mem u hu)
  exact he

lemma minimal_pairing (u v : H1) (hu : u ∈ zeroBoundary) :
    inner ℂ ((-Complex.I) • derivativeLp u) (baseLp v) =
      inner ℂ (baseLp u) ((-Complex.I) • derivativeLp v) := by
  obtain ⟨f, hf⟩ := representative_existence ℂ interval ordConnected_Ioo 2 u
  obtain ⟨g, hg⟩ := representative_existence ℂ interval ordConnected_Ioo 2 v
  have hend := Trace.interval_zeroSpace_endpoints ℂ 0 1 (by norm_num) 2 (by norm_num)
    u hu f hf
  have he := boundary_form u v f g hf hg
  simpa only [hend.1, hend.2, star_zero, zero_mul, sub_self, mul_zero, sub_eq_zero] using he

lemma maximal_in_adjoint (v : H1) :
    (baseLp v, (-Complex.I) • derivativeLp v) ∈ (hilbertAdjoint minimal).graph := by
  apply (mem_hilbertAdjoint_graph_iff minimal dense_domain _ _).mpr
  intro x
  have hx : (x : L2) ∈ zeroBoundary.map baseMap := domains.1 ▸ x.property
  obtain ⟨u, hu, hux⟩ := hx
  have h' : baseLp u ∈ minimal.domain := by
    change baseMap u ∈ minimal.domain
    rw [hux]
    exact x.property
  have he : (⟨baseLp u, h'⟩ : minimal.domain) = x := Subtype.ext hux
  rw [← he, minimal_apply u hu h']
  exact minimal_pairing u v hu

lemma test_derivative_inner (φ : Tests ℂ (lineDomain interval)) (v : L2) :
    inner ℂ (derivativeLp (testToSobolev (p := 2) 1 (conjugateTest φ))) v =
      lpDistribution v (testPartialCLM [0] φ) := by
  have he : derivativeLp (testToSobolev (p := 2) 1 (conjugateTest φ)) =
      testToDomainLp (p := 2) (testPartialCLM [0] (conjugateTest φ)) := by
    change testToDomainLp (testPartialCLM _ _) = _
    rw [multiIndexWord_firstIndex, List.reverse_singleton]
  rw [he, L2.inner_def, lpDistribution_apply]
  apply integral_congr_ae
  filter_upwards [testToDomainLp_coe (p := 2) (testPartialCLM [0] (conjugateTest φ))] with z hz
  rw [RCLike.inner_apply', hz, conjugateTest_partial]
  simp

/-- Compact interior tests force the weak derivative of an adjoint vector to
be i times the adjoint value. This is the reverse-domain argument. -/
lemma weakDerivative_of_formal (v z : L2)
    (h : ∀ x : minimal.domain, inner ℂ (minimal x) v = inner ℂ (x : L2) z) :
    lpDistribution (Complex.I • z) = -(lpDistribution v).comp (testPartialCLM [0]) := by
  change lpDistributionLM (Complex.I • z) = _
  rw [map_smul]
  ext φ
  have ht := h ⟨testToDomainLp (p := 2) (conjugateTest φ),
    test_mem_minimal (conjugateTest φ)⟩
  have hu := testToSobolev_zeroBoundary (conjugateTest φ)
  have hb := testToSobolev_underlying (p := 2) 1 (conjugateTest φ)
  have ha : minimal ⟨testToDomainLp (p := 2) (conjugateTest φ),
      test_mem_minimal (conjugateTest φ)⟩ =
        (-Complex.I) • derivativeLp (testToSobolev (p := 2) 1 (conjugateTest φ)) := by
    exact minimal_apply _ hu (by simpa only [hb] using test_mem_minimal (conjugateTest φ))
  rw [ha, inner_smul_left, test_derivative_inner, inner_conjugateTest] at ht
  simp only [map_neg, Complex.conj_I, neg_neg] at ht
  change Complex.I * lpDistribution z φ = -lpDistribution v (testPartialCLM [0] φ)
  rw [← ht]
  simp [← mul_assoc, Complex.I_mul_I]

theorem adjoint_equality : Specs.ExpandedFA.Unbounded.IntervalDerivativeAdjoint.AdjointEquality := by
  change hilbertAdjoint minimal = maximal
  apply LinearPMap.eq_of_eq_graph
  ext ⟨v, z⟩
  constructor
  · intro hmem
    have hformal := (mem_hilbertAdjoint_graph_iff minimal dense_domain v z).mp hmem
    have hw := weakDerivative_of_formal v z hformal
    let u : H1 := ofWeakDerivative v (Complex.I • z) hw
    have hb : baseLp u = v := ofWeakDerivative_base _ _ _
    have hd : (-Complex.I) • derivativeLp u = z := by
      rw [show derivativeLp u = Complex.I • z from ofWeakDerivative_derivative _ _ _]
      simp [smul_smul, neg_mul, Complex.I_mul_I]
    simpa only [hb, hd] using maximal_graph_mem u
  · intro hmem
    rw [graphs.2] at hmem
    obtain ⟨u, hu⟩ := hmem
    change (baseLp u, (-Complex.I) • derivativeLp u) = (v, z) at hu
    rw [← hu]
    exact maximal_in_adjoint u

theorem adjoint_domain : Specs.ExpandedFA.Unbounded.IntervalDerivativeAdjoint.AdjointDomain := by
  intro v
  rw [adjoint_equality, domains.2]
  rfl

theorem adjoint_action : Specs.ExpandedFA.Unbounded.IntervalDerivativeAdjoint.AdjointAction := by
  intro u hu
  have hm : (baseLp u, (-Complex.I) • derivativeLp u) ∈
      (HilbertAdjointSpec.adjointValue minimal).graph := by
    rw [adjoint_equality]
    exact maximal_graph_mem u
  obtain ⟨hx, he⟩ := (mem_graph_iff (HilbertAdjointSpec.adjointValue minimal) _).mp hm
  exact he

theorem representative_derivative :
    Specs.ExpandedFA.Unbounded.IntervalDerivativeAdjoint.RepresentativeDerivative := by
  intro u f hf
  filter_upwards [ae_restrict_of_ae (primitiveExtension_deriv u f),
    ae_restrict_mem isOpen_Ioo.measurableSet] with t hdt ht
  have he : f =ᶠ[𝓝 t] primitiveExtension u f := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact (primitiveExtension_eq u f hf (Ioo_subset_Icc_self hs)).symm
  have hd := hdt.congr_of_eventuallyEq he
  simpa only [extendedLineFunction, indicator_of_mem ht] using hd

end ExpandedFA.Unbounded.IntervalDerivative
