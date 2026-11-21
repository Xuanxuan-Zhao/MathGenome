import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.SimplyConnectedCalculus
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.HomotopyIntegrals
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PrimitivePeriodCriterion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.GlobalLogarithmCriterion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.GlobalRootCriterion

/-! Simple connectivity supplies a continuous contraction of each loop.
Homotopy invariance gives zero periods; the proved primitive and period
criteria then give primitives, logarithms and roots. The primitive endpoint
formula covers every rectifiable parametrization, including non-AC ones.
-/
noncomputable section
open Set
open scoped unitInterval
namespace D12Complex.SimplyConnectedCalculus

/-- The affine traversal of any compact parameter interval stays in it,
including when its endpoints coincide. -/
lemma affine_parameter_mem (γ : ComplexPath) (t : I) :
    γ.a + (γ.b - γ.a) * (t : ℝ) ∈ Icc γ.a γ.b := by
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr γ.ordered) t.property.1)
  · nlinarith [mul_nonneg (sub_nonneg.mpr γ.ordered) (sub_nonneg.mpr t.property.2)]

/-- A closed canonical path, with its given traversal, as a topological loop. -/
def normalizedLoop (γ : ComplexPath) (hc : γ.IsClosed) : Path γ.source γ.source where
  toFun t := γ (γ.a + (γ.b - γ.a) * (t : ℝ))
  continuous_toFun := γ.continuousOn.comp_continuous
    (continuous_const.add (continuous_const.mul continuous_subtype_val))
    (affine_parameter_mem γ)
  source' := by simp [ComplexPath.source]
  target' := by simpa [ComplexPath.IsClosed, ComplexPath.target] using hc

/-- Topological simple connectivity yields exactly the continuous square
needed by the already proved homotopy-Cauchy theorem. -/
lemma loop_contraction {Ω : Set ℂ} (hsc : IsSimplyConnected Ω)
    (γ : ComplexPath) (hγ : γ.trace ⊆ Ω) (hc : γ.IsClosed) :
    ∃ (z : ℂ) (H : C(I × I, ℂ)), (∀ p, H p ∈ Ω) ∧
      (∀ t : I, H (0, t) = γ (γ.a + (γ.b - γ.a) * (t : ℝ))) ∧
      (∀ t : I, H (1, t) = z) ∧ (∀ s : I, H (s, 0) = H (s, 1)) := by
  obtain ⟨F, hF⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hsc).2
    γ.source (normalizedLoop γ hc)
    (fun t => hγ ⟨_, affine_parameter_mem γ t, rfl⟩)
  refine ⟨γ.source, F.toContinuousMap, hF, ?_, ?_, ?_⟩
  · intro t
    exact F.apply_zero t
  · intro t
    exact F.apply_one t
  · intro s
    exact (F.source s).trans (F.target s).symm

theorem zero_periods :
    Specs.D12Complex.Ch04.SimplyConnectedCalculus.zero_periods_type := by
  intro Ω f _hΩ hsc hf γ hγ hc
  exact HomotopyIntegrals.null_homotopic_integral Ω f hf γ hγ hc
    (loop_contraction hsc γ.path hγ hc)

theorem exists_primitive :
    Specs.D12Complex.Ch04.SimplyConnectedCalculus.exists_primitive_type := by
  intro Ω f hΩ hsc hf
  have hfc : ContinuousOn f Ω :=
    fun z hz => (hf.2 z hz).continuousAt.continuousWithinAt
  exact (Primitives.primitive_criterion Ω f hΩ hfc).1.mpr
    ((Primitives.primitive_criterion Ω f hΩ hfc).2.mpr (zero_periods Ω f hΩ hsc hf))

theorem closed_rectifiable_integral :
    Specs.D12Complex.Ch04.SimplyConnectedCalculus.closed_rectifiable_integral_type := by
  intro Ω f hΩ hsc hf γ hr hγ hc
  obtain ⟨F, hF⟩ := exists_primitive Ω f hΩ hsc hf
  have hfc : ContinuousOn f Ω :=
    fun z hz => (hf.2 z hz).continuousAt.continuousWithinAt
  rw [Primitives.rectifiable_endpoint Ω f F hfc hF γ hr hγ, hc, sub_self]

theorem exists_logarithm :
    Specs.D12Complex.Ch04.SimplyConnectedCalculus.exists_logarithm_type := by
  intro Ω f hΩ hsc hf hn
  apply (GlobalLogarithmCriterion.global_logarithm_criterion Ω f hΩ hf hn).mpr
  exact zero_periods Ω _ hΩ hsc
    (GlobalLogarithmCriterion.holomorphicOn_logarithmicDerivative Ω f hf hn)

theorem exists_root :
    Specs.D12Complex.Ch04.SimplyConnectedCalculus.exists_root_type := by
  intro Ω f hΩ hsc hf hn n hnpos
  apply (GlobalRootCriterion.root_criterion Ω f n hΩ hf hn hnpos).mpr
  intro γ hγ hc
  refine ⟨0, ?_⟩
  rw [zero_periods Ω _ hΩ hsc
    (GlobalLogarithmCriterion.holomorphicOn_logarithmicDerivative Ω f hf hn) γ hγ hc]
  simp

end D12Complex.SimplyConnectedCalculus
