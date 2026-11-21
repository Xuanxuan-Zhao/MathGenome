import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15PartialSums
import Mathlib.Analysis.Normed.Operator.Extend

/-! Independent statements for paper.tex:4131–4146. A basic sequence is a
Schauder basis of its own closed linear span, with the inherited norm.
Equivalence means a bounded linear isomorphism of those closed spans carrying
each specified vector to the corresponding vector. All scalars are ℝ or ℂ.
The finite and empty basis cases of the dense-subset conclusion are explicit. -/
open Filter Topology
open scoped BigOperators
noncomputable section
universe u v w
namespace ExpandedFA.P1.EquivalentBases.Spec

variable {𝕜 : Type u} [RCLike 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The closed span, not the algebraic span or an assumed ambient basis. -/
def closedSpan {ι : Type*} (x : ι → E) : Submodule 𝕜 E :=
  (Submodule.span 𝕜 (Set.range x)).topologicalClosure

instance {ι : Type*} (x : ι → E) [CompleteSpace E] :
    CompleteSpace (closedSpan (𝕜 := 𝕜) x) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

def spanVector {ι : Type*} (x : ι → E) (i : ι) : closedSpan (𝕜 := 𝕜) x :=
  ⟨x i, Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self i))⟩

def IsBasicSequence (x : ℕ → E) : Prop :=
  C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) (spanVector (𝕜 := 𝕜) x)

def EquivalentFamilies {ι : Type*} (x : ι → E) (y : ι → F) : Prop :=
  ∃ U : closedSpan (𝕜 := 𝕜) x ≃L[𝕜] closedSpan (𝕜 := 𝕜) y,
    ∀ i, U (spanVector x i) = spanVector y i

/-- The exact two-sided inequality for every finitely supported scalar family. -/
def FiniteSumBounds {ι : Type*} (x : ι → E) (y : ι → F) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ a : ι →₀ 𝕜,
    c * ‖Finsupp.linearCombination 𝕜 x a‖ ≤ ‖Finsupp.linearCombination 𝕜 y a‖ ∧
    ‖Finsupp.linearCombination 𝕜 y a‖ ≤ C * ‖Finsupp.linearCombination 𝕜 x a‖

def EquivalenceCriterion : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} {F : Type w} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {x : ℕ → E} {y : ℕ → F},
    IsBasicSequence (𝕜 := 𝕜) x → IsBasicSequence (𝕜 := 𝕜) y →
    (EquivalentFamilies (𝕜 := 𝕜) x y ↔ FiniteSumBounds (𝕜 := 𝕜) x y)

/-- Summability is explicit: a divergent real `tsum` must not satisfy the
smallness condition by the convention that such a `tsum` is zero. The maps T
are required to be the actual coordinate truncations of the given basic
sequence, so `basisConstant T` is precisely its basis constant. -/
def SmallPerturbation : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {x y : ℕ → E} (h : IsBasicSequence (𝕜 := 𝕜) x)
    (T : ℕ → closedSpan (𝕜 := 𝕜) x →L[𝕜] closedSpan (𝕜 := 𝕜) x),
    (∀ N z, T N z = C15Basis.Spec.rawPartialSum h N z) →
    Summable (fun n => ‖y n - x n‖ / ‖x n‖) →
    2 * C15PartialSums.Spec.basisConstant T * (∑' n, ‖y n - x n‖ / ‖x n‖) < 1 →
    IsBasicSequence (𝕜 := 𝕜) y ∧ EquivalentFamilies (𝕜 := 𝕜) x y ∧
      ∃ U : E ≃L[𝕜] E, ∀ n, U (x n) = y n

def DenseBasis : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {x : ℕ → E}, C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) x →
    ∀ D : Set E, Dense D → ∃ y : ℕ → E,
      (∀ n, y n ∈ D) ∧ C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) y ∧
      ∃ U : E ≃L[𝕜] E, ∀ n, U (x n) = y n

def DenseFiniteBasis : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} {x : Fin d → E}, C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) x →
    ∀ D : Set E, Dense D → ∃ y : Fin d → E,
      (∀ n, y n ∈ D) ∧ C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) y ∧
      ∃ U : E ≃L[𝕜] E, ∀ n, U (x n) = y n

end ExpandedFA.P1.EquivalentBases.Spec
