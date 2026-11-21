import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.GlobalLogarithmCriterion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskCauchyDerivatives
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PrimitivePeriodCriterion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.LogarithmUniquenessObstruction

/-! Global logarithms from the primitive criterion, paper.tex:1163–1194.
The auxiliary function f exp(-H), for a primitive H of f′/f, has zero
complex derivative on the domain. Connectedness supplies one nonzero
constant; a logarithm of that constant normalizes H. -/
noncomputable section
open Set
open scoped Topology
namespace D12Complex.GlobalLogarithmCriterion

theorem holomorphicOn_logarithmicDerivative :
    Specs.D12Complex.Ch04.GlobalLogarithmCriterion.holomorphicOn_logarithmicDerivative_type := by
  intro Ω f hf hn
  have hd : HolomorphicOn Ω (deriv f) := by
    simpa using (DiskCauchyDerivatives.holomorphicOn_iteratedDeriv Ω f hf 1).1
  exact ⟨hf.1, fun z hz => (hd.2 z hz).div (hf.2 z hz) (hn z hz)⟩

theorem logarithm_hasDerivAt :
    Specs.D12Complex.Ch04.GlobalLogarithmCriterion.logarithm_hasDerivAt_type := by
  intro Ω f L _hf hL hn he z hz
  have hd := (Exponential.hasDerivAt_E (L z)).comp z (hL.2 z hz).hasDerivAt
  have heq : f =ᶠ[𝓝 z] (fun w => E (L w)) :=
    Filter.eventuallyEq_of_mem (hL.1.mem_nhds hz) (fun w hw => (he w hw).symm)
  have h := (hd.congr_of_eventuallyEq heq).deriv
  rw [he z hz] at h
  have hdL : deriv L z = deriv f z / f z := by
    apply (eq_div_iff (hn z hz)).mpr
    exact (mul_comm _ _).trans h.symm
  rw [← hdL]
  exact (hL.2 z hz).hasDerivAt

theorem global_logarithm_criterion :
    Specs.D12Complex.Ch04.GlobalLogarithmCriterion.global_logarithm_criterion_type := by
  intro Ω f hΩ hf hn
  have hg := holomorphicOn_logarithmicDerivative Ω f hf hn
  have hgc : ContinuousOn (fun z => deriv f z / f z) Ω :=
    fun z hz => (hg.2 z hz).continuousAt.continuousWithinAt
  constructor
  · rintro ⟨L, hL, he⟩ γ hγ hclosed
    have hp : Primitives.IsPrimitive Ω (fun z => deriv f z / f z) L :=
      ⟨hL, fun z hz => (logarithm_hasDerivAt Ω f L hf hL hn he z hz).deriv⟩
    rw [Primitives.piecewise_endpoint Ω _ L hgc hp γ hγ, hclosed, sub_self]
  · intro hperiod
    obtain ⟨H, hH⟩ := (Primitives.primitive_criterion Ω _ hΩ hgc).1.mpr
      ((Primitives.primitive_criterion Ω _ hΩ hgc).2.mpr hperiod)
    let q : ℂ → ℂ := fun z => f z * E (-H z)
    have hq : HolomorphicOn Ω q := by
      refine ⟨hΩ.2.1, fun z hz => ?_⟩
      have hE : DifferentiableAt ℂ E (-H z) :=
        (Exponential.hasDerivAt_E (-H z)).differentiableAt
      have hcomp : DifferentiableAt ℂ (fun w : ℂ => E (-H w)) z :=
        DifferentiableAt.comp (f := fun w : ℂ => -H w) (g := E) z hE
          (hH.1.2 z hz).neg
      exact (hf.2 z hz).mul hcomp
    have hqd : ∀ z ∈ Ω, deriv q z = 0 := by
      intro z hz
      have hdH : HasDerivAt H (deriv f z / f z) z := by
        simpa only [hH.2 z hz] using (hH.1.2 z hz).hasDerivAt
      have hdq := (hf.2 z hz).hasDerivAt.mul
        ((Exponential.hasDerivAt_E (-H z)).comp z hdH.neg)
      change HasDerivAt q
        (deriv f z * E (-H z) + f z * (E (-H z) * -(deriv f z / f z))) z at hdq
      have hdq0 : HasDerivAt q 0 z := by
        apply hdq.congr_deriv
        field_simp [hn z hz]
        ring
      exact hdq0.deriv
    obtain ⟨c, hc⟩ := Primitives.zero_derivative_constant Ω q hΩ hq hqd
    obtain ⟨a, ha⟩ := hΩ.1
    have hcn : c ≠ 0 := by
      rw [← hc a ha]
      exact mul_ne_zero (hn a ha) (Exponential.E_ne_zero _)
    refine ⟨fun z => H z + Complex.log c, ?_, ?_⟩
    · exact ⟨hΩ.2.1, fun z hz => (hH.1.2 z hz).add_const _⟩
    · intro z hz
      have helog : E (Complex.log c) = c := by
        rw [Exponential.E_eq_exp, Complex.exp_log hcn]
      calc
        E (H z + Complex.log c) = E (H z) * c := by rw [Exponential.E_add, helog]
        _ = E (H z) * (f z * E (-H z)) := by rw [← hc z hz]
        _ = f z * (E (H z) * E (-H z)) := by ring
        _ = f z := by rw [← Exponential.E_add, add_neg_cancel, Exponential.E_zero, mul_one]

theorem holomorphic_logarithms_difference :
    Specs.D12Complex.Ch04.GlobalLogarithmCriterion.holomorphic_logarithms_difference_type := by
  intro Ω f L₁ L₂ hΩ _hf hn h₁ h₂ he₁ he₂
  have hc₁ : ContinuousOn L₁ Ω :=
    fun z hz => (h₁.2 z hz).continuousAt.continuousWithinAt
  have hc₂ : ContinuousOn L₂ Ω :=
    fun z hz => (h₂.2 z hz).continuousAt.continuousWithinAt
  obtain ⟨k, hk⟩ := LogarithmUniquenessObstruction.continuous_logarithms_difference Ω hΩ.2.2
    (fun z => f z) (fun z => L₁ z) (fun z => L₂ z)
    (fun z => hn z z.property) hc₁.domRestrict hc₂.domRestrict
    (fun z => he₁ z z.property) (fun z => he₂ z z.property)
  exact ⟨k, fun z hz => hk ⟨z, hz⟩⟩

end D12Complex.GlobalLogarithmCriterion
