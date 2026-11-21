import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.GenericFourierDivergence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.DirichletKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07Baire

noncomputable section
open Set Filter TopologicalSpace
open scoped Topology

namespace ExpandedFA.PartIV.GenericFourierDivergence

/-- Unbounded unit-ball evaluations give dense open sets of vectors on which
some evaluation exceeds a prescribed threshold. No completeness is needed here. -/
theorem dense_open_exceeds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : ℕ → E →L[ℝ] F)
    (hu : ∀ B : ℝ, ∃ N f, ‖f‖ ≤ 1 ∧ B < ‖L N f‖) (M : ℕ) :
    IsOpen {f : E | ∃ N, (M : ℝ) < ‖L N f‖} ∧
      Dense {f : E | ∃ N, (M : ℝ) < ‖L N f‖} := by
  constructor
  · simp only [ofPred_exists]
    exact isOpen_iUnion fun N => isOpen_lt continuous_const (L N).continuous.norm
  · intro f
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    by_cases hf : ∃ N, (M : ℝ) < ‖L N f‖
    · exact ⟨f, hf, by simpa using hε⟩
    have hbound : ∀ N, ‖L N f‖ ≤ (M : ℝ) := by simpa using hf
    obtain ⟨N, u, hu, hbig⟩ := hu (4 * (M : ℝ) / ε)
    let v : E := (ε / 2) • u
    have hv : ‖v‖ < ε := by
      calc
        ‖v‖ = (ε / 2) * ‖u‖ := by simp [v, norm_smul, abs_of_pos hε]
        _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hu (by positivity)
        _ < ε := by linarith
    have hvbig : 2 * (M : ℝ) < ‖L N v‖ := by
      have hmul := (div_lt_iff₀ hε).mp hbig
      rw [show L N v = (ε / 2) • L N u from (L N).map_smul _ _]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ε / 2)]
      nlinarith
    have hsum : (M : ℝ) < ‖L N (f + v)‖ := by
      have htri : ‖L N v‖ ≤ ‖L N (f + v)‖ + ‖L N f‖ := by
        simpa only [map_add, add_sub_cancel_left] using norm_sub_le (L N (f + v)) (L N f)
      linarith [hbound N]
    refine ⟨f + v, ⟨N, hsum⟩, ?_⟩
    simpa only [dist_eq_norm, sub_add_cancel_left, norm_neg] using hv

/-- The category argument: countably many dense open conditions on a dense
sequence of points yield residual unboundedness on the whole point space. -/
theorem residual_unbounded_on_residual_points
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [BaireSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace X] [SeparableSpace X] [Nonempty X]
    (S : ℕ → E → C(X, F)) (L : ℕ → X → E →L[ℝ] F)
    (hL : ∀ N x f, L N x f = S N f x)
    (hu : ∀ x B, ∃ N f, ‖f‖ ≤ 1 ∧ B < ‖L N x f‖) :
    ∃ G : Set E, G ∈ residual E ∧ Dense G ∧ IsGδ G ∧
      ∀ f ∈ G, {x : X | ∀ B : ℝ, ∃ N : ℕ, B < ‖S N f x‖} ∈ residual X := by
  obtain ⟨d, hd⟩ := exists_dense_seq X
  let U : ℕ × ℕ → Set E := fun p => {f | ∃ N, (p.2 : ℝ) < ‖L N (d p.1) f‖}
  have hU : ∀ p, IsOpen (U p) ∧ Dense (U p) := fun p =>
    dense_open_exceeds (fun N => L N (d p.1)) (hu (d p.1)) p.2
  let G : Set E := ⋂ p, U p
  have hGδ : IsGδ G := IsGδ.iInter_of_isOpen fun p => (hU p).1
  have hGdense : Dense G := dense_iInter_of_isOpen (fun p => (hU p).1) (fun p => (hU p).2)
  refine ⟨G, residual_of_dense_Gδ hGδ hGdense, hGdense, hGδ, ?_⟩
  intro f hf
  let O : ℕ → Set X := fun M => {x | ∃ N, (M : ℝ) < ‖S N f x‖}
  have hOopen : ∀ M, IsOpen (O M) := by
    intro M
    simp only [O, ofPred_exists]
    exact isOpen_iUnion fun N => isOpen_lt continuous_const (S N f).continuous.norm
  have hOdense : ∀ M, Dense (O M) := by
    intro M
    apply hd.mono
    rintro x ⟨j, rfl⟩
    obtain ⟨N, hN⟩ := mem_iInter.mp hf (j, M)
    exact ⟨N, by simpa only [hL] using hN⟩
  have hres : (⋂ M, O M) ∈ residual X :=
    (countable_iInter_mem.mpr fun M => residual_of_dense_open (hOopen M) (hOdense M))
  apply mem_of_superset hres
  intro x hx B
  obtain ⟨M, hM⟩ := exists_nat_gt B
  obtain ⟨N, hN⟩ := mem_iInter.mp hx M
  exact ⟨N, hM.trans hN⟩

open DirichletKernelSpec
abbrev Circle := DirichletKernelSpec.Circle

theorem complex_divergence : GenericFourierDivergenceSpec.ComplexDivergence := by
  exact residual_unbounded_on_residual_points
    (fun N (f : C(Circle, ℂ)) => partialSum N f)
    (fun N x => (DirichletKernel.evaluation N x).restrictScalars ℝ)
    (fun N x f => DirichletKernel.evaluation_apply N x f)
    (by
      intro x B
      obtain ⟨N, f, hf, hbig⟩ := DirichletKernel.evaluation_unbounded x B
      refine ⟨N, f, hf, ?_⟩
      change B < ‖DirichletKernel.evaluation N x f‖
      simpa only [DirichletKernel.evaluation_apply] using hbig)

theorem real_divergence : GenericFourierDivergenceSpec.RealDivergence := by
  let S : ℕ → C(Circle, ℝ) → C(Circle, ℝ) := fun N f =>
    ⟨fun x => (partialSum N (fun t => (f t : ℂ)) x).re,
      Complex.continuous_re.comp (partialSum N (fun t => (f t : ℂ))).continuous⟩
  obtain ⟨G, hGr, hGd, hGδ, hG⟩ := residual_unbounded_on_residual_points S
    DirichletKernel.realEvaluation DirichletKernel.realEvaluation_apply
    (by
      intro x B
      obtain ⟨N, f, hf, hbig⟩ := DirichletKernel.real_evaluation_unbounded x B
      exact ⟨N, f, hf, by simpa only [DirichletKernel.realEvaluation_apply] using hbig⟩)
  refine ⟨G, hGr, hGd, hGδ, ?_⟩
  intro f hf
  apply mem_of_superset (hG f hf)
  intro x hx B
  obtain ⟨N, hN⟩ := hx B
  refine ⟨N, hN.trans_le ?_⟩
  exact Complex.abs_re_le_norm _

end ExpandedFA.PartIV.GenericFourierDivergence
