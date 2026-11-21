import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.BigOperators.Module

/-!
Independent specification for `fa2:p1:c15:unconditional`, paper.tex 3977–3984.
All finite subsets are ordered by inclusion. The topology is the metric topology
of the displayed norm. As in C01Banach, index 0 denotes the manuscript's index 1.

The predicates below make sense without completeness, so their definitions and
basic bridges apply in particular to the real and complex Banach spaces of this
chapter. `HasUniqueOrderedExpansions` spells out exactly the Schauder-basis
hypothesis from lines 3810–3815, without assuming coordinate continuity. No
unaccepted basis implementation is imported. Quantifying over every expansion
avoids choosing coordinates; uniqueness makes this the same basis property.
Finite bases are included separately, with length zero permitted.
-/

open Filter
open scoped Topology

namespace ExpandedFA.P1.C15Unconditional

/-- The raw Schauder property needed to interpret the unconditional-basis
predicate. The ordered convergence is the accepted C01Banach definition. -/
def HasUniqueOrderedExpansions (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (e : ℕ → E) : Prop :=
  (∀ n, e n ≠ 0) ∧ ∀ x : E, ∃! a : ℕ → 𝕜,
    C01Banach.Spec.HasSequentialSumValue E (fun n => a n • e n) x

/-- The analogous finite expansion property; the empty list is allowed. -/
def HasUniqueFiniteExpansions (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {d : ℕ} (e : Fin d → E) : Prop :=
  (∀ n, e n ≠ 0) ∧ ∀ x : E, ∃! a : Fin d → 𝕜, ∑ n, a n • e n = x

namespace Spec

def finiteSubsumType :=
  ∀ {ι E : Type*} [NormedAddCommGroup E], (ι → E) → Finset ι → E

def finiteSubsumValue : finiteSubsumType :=
  fun {_ _} [_] v F => ∑ n ∈ F, v n

def HasUnconditionalSumType :=
  ∀ {ι E : Type*} [NormedAddCommGroup E], (ι → E) → E → Prop

/-- Convergence in norm of the finite-subset net, with its actual limit. -/
def HasUnconditionalSumValue : HasUnconditionalSumType :=
  fun {_ _} [_] v x => Tendsto (finiteSubsumValue v) atTop (𝓝 x)

def UnconditionallyConvergentType :=
  ∀ {ι E : Type*} [NormedAddCommGroup E], (ι → E) → Prop

def UnconditionallyConvergentValue : UnconditionallyConvergentType :=
  fun {_ _} [_] v => ∃ x, HasUnconditionalSumValue v x

def IsUnconditionalSchauderBasisType :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    (ℕ → E) → Prop

/-- A Schauder basis whose every expansion has a convergent finite-subset net. -/
def IsUnconditionalSchauderBasisValue : IsUnconditionalSchauderBasisType :=
  fun 𝕜 E _ _ _ e => HasUniqueOrderedExpansions 𝕜 E e ∧
    ∀ (x : E) (a : ℕ → 𝕜),
      C01Banach.Spec.HasSequentialSumValue E (fun n => a n • e n) x →
      UnconditionallyConvergentValue (fun n => a n • e n)

def IsUnconditionalFiniteBasisType :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {d : ℕ}, (Fin d → E) → Prop

def IsUnconditionalFiniteBasisValue : IsUnconditionalFiniteBasisType :=
  fun 𝕜 E _ _ _ _ e => HasUniqueFiniteExpansions 𝕜 E e ∧
    ∀ (x : E) (a : _ → 𝕜), (∑ n, a n • e n) = x →
      UnconditionallyConvergentValue (fun n => a n • e n)

def HasUnconditionalSumIdentification : Prop :=
  ∀ {ι E : Type*} [NormedAddCommGroup E] (v : ι → E) (x : E),
    HasUnconditionalSumValue v x ↔ HasSum v x (SummationFilter.unconditional ι)

def UnconditionalConvergenceIdentification : Prop :=
  ∀ {ι E : Type*} [NormedAddCommGroup E] (v : ι → E),
    UnconditionallyConvergentValue v ↔ Summable v (SummationFilter.unconditional ι)

def NormNetIdentification : Prop :=
  ∀ {ι E : Type*} [NormedAddCommGroup E] (v : ι → E) (x : E),
    HasUnconditionalSumValue v x ↔
      ∀ ε > (0 : ℝ), ∃ F₀ : Finset ι, ∀ F ≥ F₀, ‖finiteSubsumValue v F - x‖ < ε

def UnconditionalSumIsOrderedSum : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (v : ℕ → E) (x : E),
    HasUnconditionalSumValue v x → C01Banach.Spec.HasSequentialSumValue E v x

def UnconditionalConvergenceIsOrderedConvergence : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (v : ℕ → E),
    UnconditionallyConvergentValue v → C01Banach.Spec.SequentiallySummableValue E v

/-- Strictness already occurs for scalar series in the real Banach space. -/
def OrderedConvergenceIsStrictlyWeaker : Prop :=
  ∃ v : ℕ → ℝ, C01Banach.Spec.SequentiallySummableValue ℝ v ∧
    ¬ UnconditionallyConvergentValue v

def UnconditionalSumUnique : Prop :=
  ∀ {ι E : Type*} [NormedAddCommGroup E] (v : ι → E) (x y : E),
    HasUnconditionalSumValue v x → HasUnconditionalSumValue v y → x = y

def UnconditionalSchauderBasisIdentification : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (e : ℕ → E),
    IsUnconditionalSchauderBasisValue 𝕜 E e ↔
      HasUniqueOrderedExpansions 𝕜 E e ∧ ∀ (x : E) (a : ℕ → 𝕜),
        C01Banach.Spec.HasSequentialSumValue E (fun n => a n • e n) x →
        HasUnconditionalSumValue (fun n => a n • e n) x

/-- A coordinate choice with the expansion property gives exactly the same
notion; the choice need not be linear or continuous as an extra assumption. -/
def UnconditionalBasisCoordinateIdentification : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (e : ℕ → E) (h : HasUniqueOrderedExpansions 𝕜 E e)
    (a : E → ℕ → 𝕜)
    (ha : ∀ x, C01Banach.Spec.HasSequentialSumValue E (fun n => a x n • e n) x),
    IsUnconditionalSchauderBasisValue 𝕜 E e ↔
      ∀ x, UnconditionallyConvergentValue (fun n => a x n • e n)

def FiniteFamilySum : Prop :=
  ∀ {ι E : Type*} [NormedAddCommGroup E] [Fintype ι] (v : ι → E),
    HasUnconditionalSumValue v (∑ n, v n)

def FiniteBasisIsUnconditional : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {d : ℕ} (e : Fin d → E), HasUniqueFiniteExpansions 𝕜 E e →
      IsUnconditionalFiniteBasisValue 𝕜 E e

def FiniteExpansionSum : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {d : ℕ} (e : Fin d → E) (x : E) (a : Fin d → 𝕜),
    (∑ n, a n • e n) = x → HasUnconditionalSumValue (fun n => a n • e n) x

def EmptyBasisIsUnconditional : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [Subsingleton E], IsUnconditionalFiniteBasisValue 𝕜 E (Fin.elim0 : Fin 0 → E)

def EmptySubsum : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (v : Fin 0 → E) (F : Finset (Fin 0)),
    finiteSubsumValue v F = 0

end Spec
end ExpandedFA.P1.C15Unconditional
