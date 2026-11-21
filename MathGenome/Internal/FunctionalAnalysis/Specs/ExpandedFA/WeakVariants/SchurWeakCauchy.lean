import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.Schur
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-! Independent statements for the first two assertions of
`fa2:p2:schur-cauchy-sphere` (paper.tex:8901–8930).
The scalar field is real or complex and weak convergence tests the continuous
scalar-linear dual. The interval carries ordinary restricted Lebesgue measure.
Natural index n denotes the manuscript's Rademacher index n+1. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.WeakVariants.SchurWeakCauchy

/-- Lebesgue measure on the open unit interval, viewed as a measure on ℝ. -/
def intervalMeasure : Measure ℝ := volume.restrict (Set.Ioo 0 1)

instance : IsProbabilityMeasure intervalMeasure where
  measure_univ := by simp [intervalMeasure, Real.volume_Ioo]

/-- The real sign of sin(2^(n+1) π t), with sign(0)=0. -/
def rademacherReal (n : ℕ) (t : ℝ) : ℝ :=
  if 0 < Real.sin ((2 : ℝ) ^ (n + 1) * Real.pi * t) then 1
  else if Real.sin ((2 : ℝ) ^ (n + 1) * Real.pi * t) < 0 then -1 else 0

/-- The same Rademacher function, taking values in the chosen scalar field. -/
def rademacher (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) (t : ℝ) : 𝕜 :=
  RCLike.ofReal (rademacherReal n t)

lemma rademacherReal_measurable (n : ℕ) : Measurable (rademacherReal n) := by
  have hs : Continuous (fun t : ℝ => Real.sin ((2 : ℝ) ^ (n+1) * Real.pi * t)) := by
    fun_prop
  exact Measurable.ite (isOpen_lt continuous_const hs).measurableSet measurable_const
    (Measurable.ite (isOpen_lt hs continuous_const).measurableSet
      measurable_const measurable_const)

lemma rademacherReal_norm_le (n : ℕ) (t : ℝ) : ‖rademacherReal n t‖ ≤ 1 := by
  unfold rademacherReal
  split_ifs <;> norm_num

lemma rademacher_memLp (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) (n : ℕ) :
    MemLp (rademacher 𝕜 n) p intervalMeasure := by
  apply MemLp.of_bound
    ((RCLike.continuous_ofReal.measurable.comp (rademacherReal_measurable n)).aestronglyMeasurable)
    1
  exact Eventually.of_forall fun t => by
    simpa only [rademacher, Function.comp_apply, RCLike.norm_ofReal, Real.norm_eq_abs] using
      rademacherReal_norm_le n t

/-- The ordinary a.e. class of the stated Rademacher function. -/
def rademacherLp (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) (n : ℕ) :
    Lp 𝕜 p intervalMeasure := (rademacher_memLp 𝕜 p n).toLp (rademacher 𝕜 n)

namespace Spec

/-- Weakly Cauchy ℓ¹ sequences have a norm limit, over either scalar field. -/
def WeakCauchyNormConvergence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜]
    (x : ℕ → ExpandedFA.P1.C01SequenceSpaces.SequenceLp 𝕜 1),
    ExpandedFA.P1.Schur.WeakCauchy 𝕜 x → ∃ l, Tendsto x atTop (𝓝 l)

/-- The specified functions have L¹ norm one. -/
def RademacherNorm : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ), ‖rademacherLp 𝕜 1 n‖ = 1

/-- Weak nullity is with respect to all continuous scalar-linear functionals. -/
def RademacherWeakNull : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ExpandedFA.P1.Schur.WeakConverges 𝕜 (rademacherLp 𝕜 1) 0

/-- The source's counterexample to the Schur property of nonatomic L¹(0,1). -/
def L1WeakNullUnitSequence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ x : ℕ → Lp 𝕜 1 intervalMeasure,
      ExpandedFA.P1.Schur.WeakConverges 𝕜 x 0 ∧ ∀ n, ‖x n‖ = 1

end Spec
end ExpandedFA.WeakVariants.SchurWeakCauchy
