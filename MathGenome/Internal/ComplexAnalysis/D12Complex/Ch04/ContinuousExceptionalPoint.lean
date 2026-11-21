import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.ContinuousExceptionalPoint
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.WeakGoursat
import Mathlib.Analysis.Complex.HasPrimitives

/-! The continuous exceptional-point triangle lemma (paper.tex:859–873).

We use a different, acyclic proof route from the affine-grid proof in the
paper. Mathlib's rectangle Goursat theorem allows a countable exceptional
set and follows from the real divergence theorem, without removability.
Thus every rectangle in U has zero integral. The rectangle version of
Morera, proved by constructing local wedge primitives, gives complex
differentiability on U. The already established triangle Goursat theorem
then applies to the original, partition-defined boundary integral.

No removable-singularity theorem or assumed extension is used. In
particular, the value at p is controlled by the continuity hypothesis.
-/

noncomputable section
open Set

namespace D12Complex.ContinuousExceptionalPoint

private theorem conservativeOn_of_continuous_exceptionalPoint
    {U : Set ℂ} {f : ℂ → ℂ} {p : ℂ}
    (hf : ContinuousOn f U) (hd : HolomorphicOn (U \ {p}) f) :
    Complex.IsConservativeOn f U := by
  intro z w hzw
  rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq]
  apply Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    f z w {p} (countable_singleton p)
  · exact hf.mono hzw
  · intro x hx
    apply hd.2 x
    refine ⟨hzw ?_, hx.2⟩
    exact ⟨⟨le_of_lt hx.1.1.1, le_of_lt hx.1.1.2⟩,
      ⟨le_of_lt hx.1.2.1, le_of_lt hx.1.2.2⟩⟩

/-- Continuity on a neighborhood of a closed triangle and holomorphy there
away from one arbitrary point suffice for its boundary integral to vanish.
No nondegeneracy or location hypothesis is needed. -/
theorem goursat_triangle :
    Specs.D12Complex.Ch04.ContinuousExceptionalPoint.goursat_triangle_type := by
  intro a b c p U f hU hf hd hT
  have hdiff : DifferentiableOn ℂ f U :=
    (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
      ⟨conservativeOn_of_continuous_exceptionalPoint hf hd, hf⟩
  exact WeakGoursat.goursat_triangle a b c U f
    ⟨hU, fun z hz => (hdiff z hz).differentiableAt (hU.mem_nhds hz)⟩ hT

end D12Complex.ContinuousExceptionalPoint
