import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PrimitivePeriodCriterion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PrimitiveConstruction
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PrimitiveStieltjesEndpoint
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace D12Complex.Primitives

def IsPrimitive (Ω : Set ℂ) (f F : ℂ → ℂ) : Prop :=
  HolomorphicOn Ω F ∧ ∀ z ∈ Ω, deriv F z = f z

def EndpointIndependent (Ω : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ γ η : PiecewiseC1Path, γ.trace ⊆ Ω → η.trace ⊆ Ω →
    γ.path.source = η.path.source → γ.path.target = η.path.target →
    γ.integral f = η.integral f

def ZeroPeriods (Ω : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ γ : PiecewiseC1Path, γ.trace ⊆ Ω → γ.IsClosed → γ.integral f = 0

/-- The complex chain rule, restricted to the real parameter of a contour. -/
theorem primitive_comp_hasDerivAt {Ω : Set ℂ} {f F : ℂ → ℂ}
    (hF : IsPrimitive Ω f F) {γ : ℝ → ℂ} {t : ℝ}
    (ht : γ t ∈ Ω) (hγ : DifferentiableAt ℝ γ t) :
    HasDerivAt (F ∘ γ) (f (γ t) * deriv γ t) t := by
  have h := ((hF.1.2 _ ht).hasDerivAt)
  rw [hF.2 _ ht] at h
  simpa using h.complexToReal_fderiv.comp_hasDerivAt t hγ.hasDerivAt

/-- Real FTC on each smooth piece followed by telescoping. No regularity of
F′ beyond the given continuity of f is assumed. -/
theorem piecewise_endpoint :
    Specs.D12Complex.Ch03.PrimitivePeriodCriterion.piecewise_endpoint_type := by
  intro Ω f F hf hF γ hγ
  have hfγ : ContinuousOn f γ.trace := hf.mono hγ
  have hFc : ContinuousOn F Ω := fun z hz => (hF.1.2 z hz).continuousAt.continuousWithinAt
  have hcomp : ContinuousOn (F ∘ γ) (Icc γ.path.a γ.path.b) :=
    hFc.comp γ.path.continuousOn (fun t ht => hγ ⟨t, ht, rfl⟩)
  let P := γ.partition
  have hpieces (i : Fin P.count) :
      (∫ t in P.node i.castSucc..P.node i.succ, f (γ t) * deriv γ t) =
        F (γ (P.node i.succ)) - F (γ (P.node i.castSucc)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (P.piece_lt i).le
      (hcomp.mono (P.piece_subset i))
    · intro t ht
      exact primitive_comp_hasDerivAt hF
        (hγ ⟨t, P.piece_subset i ⟨ht.1.le, ht.2.le⟩, rfl⟩)
        (P.differentiableAt_piece i ht)
    · exact P.piece_integrable_deriv f hfγ i
  rw [PiecewiseC1Path.integral_eq_partition γ P f hfγ]
  rw [C1Partition.integral_eq_intervalIntegral γ.path P f hfγ]
  rw [← P.first, ← P.last]
  rw [← (intervalIntegral_fin_partition P.node
    (fun t => f (γ t) * deriv γ t) (P.piece_integrable_deriv f hfγ)).2]
  simp_rw [hpieces]
  have htel : (∑ i : Fin P.count,
      (F (γ (P.node i.succ)) - F (γ (P.node i.castSucc)))) =
        F (γ (P.node (Fin.last P.count))) - F (γ (P.node 0)) := by
    rw [Finset.sum_sub_distrib]
    have h := (Fin.sum_univ_succ (fun i => F (γ (P.node i)))).symm.trans
      (Fin.sum_univ_castSucc (fun i => F (γ (P.node i))))
    linear_combination h
  simpa only [P.first, P.last, ComplexPath.source, ComplexPath.target] using htel

/-- A primitive therefore makes the integral depend only on its endpoints. -/
theorem primitive_endpointIndependent :
    Specs.D12Complex.Ch03.PrimitivePeriodCriterion.primitive_endpointIndependent_type := by
  intro Ω f F hf hF γ η hγ hη hs ht
  rw [piecewise_endpoint Ω f F hf hF γ hγ,
    piecewise_endpoint Ω f F hf hF η hη, hs, ht]

/-- Reverse the traversal while keeping its trace in the original open set. -/
theorem exists_reversed_path_in (Ω : Set ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Path) (hγ : γ.trace ⊆ Ω) (hf : ContinuousOn f Ω) :
    ∃ η : PiecewiseC1Path, η.trace ⊆ Ω ∧
      η.path.source = γ.path.target ∧ η.path.target = γ.path.source ∧
      η.integral f = -γ.integral f := by
  obtain ⟨η, ha, hb, he, hi⟩ := PiecewiseC1Path.reversal γ f (hf.mono hγ)
  refine ⟨η, ?_, ?_, ?_, hi⟩
  · rintro z ⟨t, ht, rfl⟩
    rw [ha, hb] at ht
    rw [he ht]
    apply hγ
    refine ⟨γ.path.a + γ.path.b - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  · change η η.path.a = γ γ.path.b
    rw [ha, he ⟨le_rfl, γ.path.ordered⟩]
    ring_nf
  · change η η.path.b = γ γ.path.a
    rw [hb, he ⟨γ.path.ordered, le_rfl⟩]
    ring_nf

/-- Concatenation with its endpoint and trace properties made explicit. -/
theorem exists_concatenated_path_in (Ω : Set ℂ) (f : ℂ → ℂ)
    (γ η : PiecewiseC1Path) (hγ : γ.trace ⊆ Ω) (hη : η.trace ⊆ Ω)
    (hf : ContinuousOn f Ω) (hjoin : γ.path.target = η.path.source) :
    ∃ κ : PiecewiseC1Path, κ.trace ⊆ Ω ∧
      κ.path.source = γ.path.source ∧ κ.path.target = η.path.target ∧
      κ.integral f = γ.integral f + η.integral f := by
  obtain ⟨κ, ha, hb, h₁, h₂, hi⟩ :=
    PiecewiseC1Path.concatenation γ η f hjoin (hf.mono hγ) (hf.mono hη)
  refine ⟨κ, ?_, ?_, ?_, hi⟩
  · rintro z ⟨t, ht, rfl⟩
    rw [ha, hb] at ht
    by_cases h : t ≤ 1
    · rw [h₁ ⟨ht.1, h⟩]
      apply hγ
      refine ⟨_, ⟨?_, ?_⟩, rfl⟩
      · nlinarith [mul_nonneg (sub_nonneg.mpr γ.path.ordered) ht.1]
      · nlinarith [mul_nonneg (sub_nonneg.mpr γ.path.ordered) (sub_nonneg.mpr h)]
    · rw [h₂ ⟨by linarith, ht.2⟩]
      apply hη
      refine ⟨_, ⟨?_, ?_⟩, rfl⟩
      · nlinarith [mul_nonneg (sub_nonneg.mpr η.path.ordered)
          (show 0 ≤ t - 1 by linarith)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr η.path.ordered)
          (show 0 ≤ 2 - t by linarith [ht.2])]
  · change κ κ.path.a = γ γ.path.a
    rw [ha, h₁ (by norm_num : (0 : ℝ) ∈ Icc 0 1)]
    simp
  · change κ κ.path.b = η η.path.b
    rw [hb, h₂ (by norm_num : (2 : ℝ) ∈ Icc 1 2)]
    ring_nf

/-- Path independence and the vanishing of all closed periods are equivalent,
including constant paths and degenerate parameter intervals. -/
theorem endpointIndependent_iff_zeroPeriods :
    Specs.D12Complex.Ch03.PrimitivePeriodCriterion.endpointIndependent_iff_zeroPeriods_type := by
  intro Ω f hf
  constructor
  · intro hind γ hγ hclosed
    let η := PiecewiseC1Path.const 0 0 le_rfl γ.path.source
    have hs : γ.path.source ∈ Ω := hγ ⟨γ.path.a, ⟨le_rfl, γ.path.ordered⟩, rfl⟩
    have hη : η.trace ⊆ Ω := by
      change (ComplexPath.const 0 0 le_rfl γ.path.source).trace ⊆ Ω
      rw [ComplexPath.const_trace]
      exact singleton_subset_iff.mpr hs
    have hi := hind γ η hγ hη rfl hclosed
    exact hi.trans (PiecewiseC1Path.const_integral 0 0 le_rfl γ.path.source f)
  · intro hz γ η hγ hη hs ht
    obtain ⟨ηr, hηr, hrs, hrt, hri⟩ := exists_reversed_path_in Ω f η hη hf
    obtain ⟨κ, hκ, hks, hkt, hki⟩ :=
      exists_concatenated_path_in Ω f γ ηr hγ hηr hf (ht.trans hrs.symm)
    have hclosed : κ.IsClosed := hkt.trans (hrt.trans (hs.symm.trans hks.symm))
    have hi := hz κ hκ hclosed
    rw [hki, hri] at hi
    exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hi)

/-- A zero complex derivative gives a constant on an open connected domain. -/
theorem zero_derivative_constant :
    Specs.D12Complex.Ch03.PrimitivePeriodCriterion.zero_derivative_constant_type := by
  intro Ω F hΩ hF hd
  exact hΩ.2.1.exists_is_const_of_deriv_eq_zero hΩ.2.2
    (fun z hz => (hF.2 z hz).differentiableWithinAt) hd

/-- Two actual primitives differ by a single constant throughout the domain. -/
theorem primitive_unique :
    Specs.D12Complex.Ch03.PrimitivePeriodCriterion.primitive_unique_type := by
  intro Ω f F G hΩ hF hG
  exact hΩ.2.1.exists_eq_add_of_deriv_eq hΩ.2.2
    (fun z hz => (hF.1.2 z hz).differentiableWithinAt)
    (fun z hz => (hG.1.2 z hz).differentiableWithinAt)
    (fun z hz => (hF.2 z hz).trans (hG.2 z hz).symm)

/-- Construct a primitive from path independence using the polygonal path
potential and its small-segment difference quotient. -/
theorem exists_primitive_of_endpointIndependent :
    Specs.D12Complex.Ch03.PrimitivePeriodCriterion.exists_primitive_of_endpointIndependent_type := by
  intro Ω f hΩ hf hind
  exact PrimitiveConstruction.exists_primitive Ω f hΩ hf hind

/-- The three equivalent conditions for a continuous function on a domain. -/
theorem primitive_criterion :
    Specs.D12Complex.Ch03.PrimitivePeriodCriterion.primitive_criterion_type := by
  intro Ω f hΩ hf
  refine ⟨⟨?_, exists_primitive_of_endpointIndependent Ω f hΩ hf⟩,
    endpointIndependent_iff_zeroPeriods Ω f hf⟩
  rintro ⟨F, hF⟩
  exact primitive_endpointIndependent Ω f F hf hF

/-- The mesh-limit Stieltjes endpoint formula applies to every rectifiable
path, without requiring absolute continuity of its parametrization. -/
theorem rectifiable_endpoint :
    Specs.D12Complex.Ch03.PrimitivePeriodCriterion.rectifiable_endpoint_type := by
  intro Ω f F hf hF γ hγ htrace
  apply PrimitiveStieltjesEndpoint.contourIntegral_endpoint Ω hF.1.1 f F hf
    (γ := γ) _ hγ htrace
  intro z hz
  simpa only [hF.2 z hz] using (hF.1.2 z hz).hasDerivAt

end D12Complex.Primitives
