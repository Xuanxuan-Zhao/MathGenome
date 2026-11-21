import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.TransformObjects
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.LaplaceUniqueness
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

/-! Laplace uniqueness, using the separating algebra of bounded Laplace
kernels directly on the orthant. The finite-measure determination theorem
encapsulates the Stone–Weierstrass argument, so no compactification is needed. -/

open MeasureTheory BoundedContinuousFunction
open scoped RealInnerProductSpace

namespace ProbabilityFoundations.Ch07

noncomputable section

lemma orthant_inner_nonneg {d : ℕ} (t x : PositiveOrthant d) :
    0 ≤ inner ℝ (t : Euclidean d) (x : Euclidean d) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (x.property j) (t.property j)

/-- Every Laplace kernel is bounded between zero and one on the closed orthant. -/
def laplaceKernel {d : ℕ} (t : PositiveOrthant d) : PositiveOrthant d →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => Real.exp (- inner ℝ (t : Euclidean d) (x : Euclidean d)), by fun_prop⟩
    1 (by
      intro x y
      have hx := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (orthant_inner_nonneg t x))
      have hy := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (orthant_inner_nonneg t y))
      change dist (Real.exp (- inner ℝ (t : Euclidean d) (x : Euclidean d)))
        (Real.exp (- inner ℝ (t : Euclidean d) (y : Euclidean d))) ≤ 1
      rw [Real.dist_eq]
      exact abs_le.mpr ⟨by linarith [Real.exp_pos (- inner ℝ (t : Euclidean d) (x : Euclidean d))],
        by linarith [Real.exp_pos (- inner ℝ (t : Euclidean d) (y : Euclidean d))]⟩)

@[simp] lemma laplaceKernel_apply {d : ℕ} (t x : PositiveOrthant d) :
    laplaceKernel t x = Real.exp (- inner ℝ (t : Euclidean d) (x : Euclidean d)) := rfl

private def orthantAdd {d : ℕ} (t s : PositiveOrthant d) : PositiveOrthant d :=
  ⟨(t : Euclidean d) + (s : Euclidean d),
    fun j => add_nonneg (t.property j) (s.property j)⟩

private lemma laplaceKernel_zero {d : ℕ} : laplaceKernel (0 : PositiveOrthant d) = 1 := by
  ext x
  change Real.exp (- inner ℝ (0 : Euclidean d) (x : Euclidean d)) = 1
  simp

private lemma laplaceKernel_add {d : ℕ} (t s : PositiveOrthant d) :
    laplaceKernel (orthantAdd t s) = laplaceKernel t * laplaceKernel s := by
  ext x
  simp [laplaceKernel_apply, orthantAdd, inner_add_left, Real.exp_add, mul_comm]

/-- The multiplicatively closed family of Laplace kernels includes the constant one. -/
private def laplaceKernelMonoid (d : ℕ) : Submonoid (PositiveOrthant d →ᵇ ℝ) where
  carrier := Set.range laplaceKernel
  one_mem' := ⟨0, laplaceKernel_zero⟩
  mul_mem' := by
    rintro f g ⟨t, rfl⟩ ⟨s, rfl⟩
    exact ⟨orthantAdd t s, laplaceKernel_add t s⟩

/-- The linear span is also an algebra because products of kernels are kernels. -/
private def laplaceKernelAlgebra (d : ℕ) : StarSubalgebra ℝ (PositiveOrthant d →ᵇ ℝ) where
  toSubalgebra := Algebra.adjoin ℝ (laplaceKernelMonoid d : Set (PositiveOrthant d →ᵇ ℝ))
  star_mem' := by
    intro f hf
    have h : star f = f := by ext x; simp
    rwa [h]

private lemma laplaceKernelAlgebra_integrals {d : ℕ}
    (μ ν : Measure (PositiveOrthant d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : PositiveOrthant d, laplaceTransform μ t = laplaceTransform ν t)
    (f : PositiveOrthant d →ᵇ ℝ) (hf : f ∈ laplaceKernelAlgebra d) :
    ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
  change f ∈ (Algebra.adjoin ℝ (laplaceKernelMonoid d : Set _)).toSubmodule at hf
  rw [Algebra.adjoin_eq_span, (laplaceKernelMonoid d).closure_eq] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨t, rfl⟩ := hf
      exact h t
  | zero => simp
  | add f g hf hg ihf ihg =>
      simp only [coe_add, Pi.add_apply, integral_add (f.integrable μ) (g.integrable μ),
        integral_add (f.integrable ν) (g.integrable ν), ihf, ihg]
  | smul c f hf ih =>
      simp only [coe_smul, integral_smul, ih]

private lemma laplaceKernelAlgebra_separatesPoints (d : ℕ) :
    ((laplaceKernelAlgebra d).map (toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  classical
  intro x y hxy
  have hcoord : ∃ j : Fin d, (x : Euclidean d) j ≠ (y : Euclidean d) j := by
    by_contra! h
    apply hxy
    apply Subtype.ext
    exact PiLp.ext h
  obtain ⟨j, hj⟩ := hcoord
  let t : PositiveOrthant d := ⟨EuclideanSpace.single j 1, by
    intro k
    simp only [PiLp.single_apply]
    split_ifs <;> norm_num⟩
  refine ⟨laplaceKernel t, ?_, ?_⟩
  · refine ⟨(laplaceKernel t).toContinuousMap, ?_, rfl⟩
    exact ⟨laplaceKernel t, Algebra.subset_adjoin ⟨t, rfl⟩, rfl⟩
  · change Real.exp (- inner ℝ (t : Euclidean d) (x : Euclidean d)) ≠
      Real.exp (- inner ℝ (t : Euclidean d) (y : Euclidean d))
    simpa only [t, EuclideanSpace.inner_single_left, conj_trivial, one_mul,
      ne_eq, Real.exp_injective.eq_iff, neg_inj] using hj

/-- Borel probability laws on the closed orthant are determined by their
Laplace transforms at all parameters in the same orthant. -/
theorem measure_eq_of_laplaceTransform_eq {d : ℕ}
    (μ ν : Measure (PositiveOrthant d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ t : PositiveOrthant d, laplaceTransform μ t = laplaceTransform ν t) : μ = ν := by
  let : PolishSpace (PositiveOrthant d) := (isClosed_positiveOrthantSet d).polishSpace
  exact ext_of_forall_mem_subalgebra_integral_eq_of_polish
    (laplaceKernelAlgebra_separatesPoints d) (laplaceKernelAlgebra_integrals μ ν h)

end
end ProbabilityFoundations.Ch07
