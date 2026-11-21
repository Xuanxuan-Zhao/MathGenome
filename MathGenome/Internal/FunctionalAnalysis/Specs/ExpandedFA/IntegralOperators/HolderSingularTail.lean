import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.HilbertSchmidtBasis
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceClassDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.L2Kernel
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Independent statements for the quantitative sufficient condition in
`fa2:p2:holder-trace-class`, paper.tex 11877–11945. The square is the actual
compact unit square with its ordinary product Lebesgue measure. The ordered
singular sequence and the trace norm are the accepted canonical definitions.
No trace, determinant or differentiability claims are allocated to this helper.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ExpandedFA.IntegralOperators.HolderSingularTail.Spec

abbrev I := Set.Icc (0 : ℝ) 1
abbrev μ : Measure I := (volume : Measure ℝ).comap Subtype.val
abbrev L2 (𝕜 : Type) [RCLike 𝕜] := Lp 𝕜 2 μ

-- Lebesgue measure restricted to the compact interval is finite.
instance unitInterval_finite : IsFiniteMeasure μ := by
  constructor
  change (volume.comap (Subtype.val : I → ℝ)) Set.univ < ∞
  rw [comap_subtype_coe_apply measurableSet_Icc]
  rw [Set.image_univ, Subtype.range_coe]
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

abbrev kernelClass {𝕜 : Type} [RCLike 𝕜] (k : C(I × I, 𝕜)) :
    Lp 𝕜 2 (μ.prod μ) := ContinuousMap.toLp (𝕜 := 𝕜) 2 (μ.prod μ) k

abbrev kernel {𝕜 : Type} [RCLike 𝕜] (k : C(I × I, 𝕜)) : L2 𝕜 →L[𝕜] L2 𝕜 :=
  ExpandedFA.PartV.L2KernelSpec.OperatorValue μ μ (kernelClass k)

/-- Half-open cells; omitting the endpoint 1 has no effect in L². -/
def cell (n : ℕ) (i : Fin n) : Set I :=
  {x | (i.val : ℝ) / n ≤ (x : ℝ) ∧ (x : ℝ) < ((i.val : ℝ) + 1) / n}

lemma cell_measurable (n : ℕ) (i : Fin n) : MeasurableSet (cell n i) :=
  (measurableSet_le measurable_const measurable_subtype_coe).inter
    (measurableSet_lt measurable_subtype_coe measurable_const)

/-- Ordinary indicator classes of the cells. -/
def cellVector {𝕜 : Type} [RCLike 𝕜] (n : ℕ) (i : Fin n) : L2 𝕜 :=
  ((memLp_const (1 : 𝕜) : MemLp (fun _ : I => (1 : 𝕜)) 2 μ).indicator
    (cell_measurable n i).nullMeasurableSet).toLp ((cell n i).indicator (fun _ => (1 : 𝕜)))

def stepSubspace (𝕜 : Type) [RCLike 𝕜] (n : ℕ) : Submodule 𝕜 (L2 𝕜) :=
  Submodule.span 𝕜 (Set.range (cellVector (𝕜 := 𝕜) n))

instance stepSubspace_finiteDimensional (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    FiniteDimensional 𝕜 (stepSubspace 𝕜 n) :=
  FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)

/-- Orthogonal projection onto the actual equal-cell step functions. -/
def cellProjection (𝕜 : Type) [RCLike 𝕜] (n : ℕ) : L2 𝕜 →L[𝕜] L2 𝕜 :=
  (stepSubspace 𝕜 n).subtypeL.comp (stepSubspace 𝕜 n).orthogonalProjectionOnto

def HolderFirst {𝕜 : Type} [RCLike 𝕜] (k : C(I × I, 𝕜)) (α H : ℝ) : Prop :=
  ∀ x x' y : I, ‖k (x,y) - k (x',y)‖ ≤ H * |(x : ℝ) - (x' : ℝ)| ^ α

def HolderSecond {𝕜 : Type} [RCLike 𝕜] (k : C(I × I, 𝕜)) (α H : ℝ) : Prop :=
  ∀ x y y' : I, ‖k (x,y) - k (x,y')‖ ≤ H * |(y : ℝ) - (y' : ℝ)| ^ α

/-- Includes the rank bound needed for the tail inequality. -/
def AveragingError : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (k : C(I × I, 𝕜)) (α H : ℝ),
    1 / 2 < α → α ≤ 1 → HolderFirst k α H →
    ∀ n : ℕ, 0 < n →
      (cellProjection 𝕜 n).toLinearMap.rank ≤ (n : Cardinal) ∧
      ∃ h : TraceIdeals.HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue
          ((ContinuousLinearMap.id 𝕜 (L2 𝕜) - cellProjection 𝕜 n).comp (kernel k)),
        TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtNormValue
          ⟨_, h⟩ ≤ H * (n : ℝ) ^ (-α)

universe u v w
/-- Squared singular tail after a rank-at-most-n orthogonal projection, using
an extended nonnegative sum so no summability is silently assumed. -/
def ProjectionTail : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (E : Type v) (F : Type w)
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]
    [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F),
    TraceIdeals.HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue T →
    ∀ (M : Submodule 𝕜 F) [FiniteDimensional 𝕜 M] (n : ℕ),
      Module.rank 𝕜 M ≤ (n : Cardinal) →
      (∑' j : ℕ, ENNReal.ofReal
        (TraceIdeals.TraceClassDefinitions.Spec.singularSequence T (j + n) ^ 2)) ≤
      TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue
        ((ContinuousLinearMap.id 𝕜 F - M.subtypeL.comp M.orthogonalProjectionOnto).comp T)

/-- Numerical dyadic estimate, isolated from operator and kernel constructions.
Index zero denotes s₁. Thus `s (j+n)` is the tail strictly after sₙ. -/
def DyadicEstimate : Prop :=
  ∀ (s : ℕ → ℝ) (α H B : ℝ),
    (∀ j, 0 ≤ s j) → Summable (fun j => s j ^ 2) →
    1 / 2 < α → 0 ≤ H → s 0 ≤ B →
    (∀ n : ℕ, 0 < n → (∑' j : ℕ, s (j+n) ^ 2) ≤ H ^ 2 * (n : ℝ) ^ (-2 * α)) →
    Summable s ∧ (∑' j, s j) ≤ B + H / (1 - (2 : ℝ) ^ (1 / 2 - α))

/-- The required quantitative sufficient condition in the first variable. -/
def FirstVariable : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (k : C(I × I, 𝕜)) (α H : ℝ),
    1 / 2 < α → α ≤ 1 → HolderFirst k α H →
    TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (kernel k) ∧
      TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue (kernel k) ≤
        ‖kernelClass k‖ + H / (1 - (2 : ℝ) ^ (1 / 2 - α))

/-- The same constant for regularity in the second variable, via the adjoint. -/
def SecondVariable : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (k : C(I × I, 𝕜)) (α H : ℝ),
    1 / 2 < α → α ≤ 1 → HolderSecond k α H →
    TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (kernel k) ∧
      TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue (kernel k) ≤
        ‖kernelClass k‖ + H / (1 - (2 : ℝ) ^ (1 / 2 - α))

/-- Assembly of the trace-class conclusion from the cell projection estimate. -/
def FirstVariableAssembly : Prop := AveragingError → FirstVariable

def SecondVariableAssembly : Prop := FirstVariable → SecondVariable

end ExpandedFA.IntegralOperators.HolderSingularTail.Spec
