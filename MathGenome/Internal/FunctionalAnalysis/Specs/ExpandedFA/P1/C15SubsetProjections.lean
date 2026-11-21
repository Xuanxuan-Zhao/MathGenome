import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15CoordinateContinuity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Unconditional
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.OrthonormalExpansion

/-! Independent statements for paper.tex 4027–4056. Index n represents n+1.
The projections sum the actual continuous scalar-linear coordinates, over an
arbitrary subset, in the finite-subset norm topology. Finite lists include
length zero. The sequence examples use the shared displayed sequence norms,
all finite real exponents p ≥ 1, and both real and complex scalars. Hilbert
completeness means density of the linear span; finite and empty systems are
included, without padding finite bases with zero vectors. -/

noncomputable section
open Filter Topology
open scoped BigOperators ENNReal Classical
universe u v w
namespace ExpandedFA.P1.C15SubsetProjections.Spec
open C15Basis.Spec C15Unconditional.Spec C01SequenceSpaces

variable {𝕜 : Type u} {E : Type v} {ι : Type w} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Bounded idempotents with exactly the required ranges and one common bound. -/
def SubsetProjections (e : ι → E) (a : E → ι → 𝕜) : Prop :=
  ∃ P : Set ι → E →L[𝕜] E,
    (∀ A x, HasUnconditionalSumValue (A.indicator (fun i => a x i • e i)) (P A x)) ∧
    (∀ A x i, a (P A x) i = if i ∈ A then a x i else 0) ∧
    (∀ A x, P A (P A x) = P A x) ∧
    (∀ A, (P A).range = (Submodule.span 𝕜 (e '' A)).topologicalClosure) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ A, ‖P A‖ ≤ C) ∧
    P ∅ = 0 ∧ P Set.univ = ContinuousLinearMap.id 𝕜 E

def NativeSubsetProjections : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} {ι : Type w} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (b : UnconditionalSchauderBasis ι 𝕜 E),
    SubsetProjections b.basis (fun x i => b.coord i x)

def RawSubsetProjections : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E} (h : IsRawSchauderBasis (𝕜 := 𝕜) e),
    IsUnconditionalSchauderBasisValue 𝕜 E e → SubsetProjections e (rawCoordinates h)

/-- Only unconditionality is assumed; raw coordinates are constructed. -/
def UnconditionalSubsetProjections : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E}, IsUnconditionalSchauderBasisValue 𝕜 E e →
    ∃ h : IsRawSchauderBasis (𝕜 := 𝕜) e, SubsetProjections e (rawCoordinates h)

def FiniteSubsetProjections : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} {e : Fin d → E} (h : IsRawFiniteBasis (𝕜 := 𝕜) e),
    SubsetProjections e (finiteCoordinates h)

/-- The canonical unit vector in the shared normed subspace of bounded null sequences. -/
def c0Unit (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : SequenceC0 𝕜 :=
  ⟨lp.single ∞ n 1, by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop n] with k hk
    exact (lp.single_apply_ne (E := fun _ : ℕ => 𝕜) ∞ n 1 (ne_of_gt hk)).symm⟩

def LpExpansion : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ x : SequenceLp 𝕜 p,
      HasUnconditionalSumValue (fun n => x n • lp.single p n (1 : 𝕜)) x

def C0Expansion : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (x : SequenceC0 𝕜),
    HasUnconditionalSumValue (fun n => x.val n • c0Unit 𝕜 n) x

def LpUnconditional : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    IsUnconditionalSchauderBasisValue 𝕜 (SequenceLp 𝕜 p)
      (fun n => lp.single (E := fun _ : ℕ => 𝕜) p n 1)

def C0Unconditional : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    IsUnconditionalSchauderBasisValue 𝕜 (SequenceC0 𝕜) (c0Unit 𝕜)

/-- Stronger arbitrary-index expansion includes every countable system. -/
def HilbertExpansion : Prop :=
  ∀ {I : Type u} {𝕜 : Type v} {H : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : I → H), Orthonormal 𝕜 e →
    (Submodule.span 𝕜 (Set.range e)).topologicalClosure = ⊤ →
    ∀ x : H, HasUnconditionalSumValue (fun i => inner 𝕜 (e i) x • e i) x

def HilbertSequence : Prop :=
  ∀ {I : Type u} {𝕜 : Type v} {H : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : I → H), Orthonormal 𝕜 e →
    (Submodule.span 𝕜 (Set.range e)).topologicalClosure = ⊤ →
    ∀ σ : ℕ ≃ I, IsUnconditionalSchauderBasisValue 𝕜 H (e ∘ σ) ∧
      ∀ (x : H) (a : ℕ → 𝕜),
        C01Banach.Spec.HasSequentialSumValue H (fun n => a n • e (σ n)) x →
        a = fun n => inner 𝕜 (e (σ n)) x

def HilbertFinite : Prop :=
  ∀ {I : Type u} {𝕜 : Type v} {H : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : I → H), Orthonormal 𝕜 e →
    (Submodule.span 𝕜 (Set.range e)).topologicalClosure = ⊤ →
    ∀ (d : ℕ) (σ : Fin d ≃ I),
      IsUnconditionalFiniteBasisValue 𝕜 H (e ∘ σ) ∧
      ∀ (x : H) (a : Fin d → 𝕜), (∑ n, a n • e (σ n)) = x →
        a = fun n => inner 𝕜 (e (σ n)) x

/-- Countability supplies a finite list (possibly empty) or an infinite enumeration. -/
def HilbertCountable : Prop :=
  ∀ {I : Type u} {𝕜 : Type v} {H : Type w} [Countable I] [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : I → H), Orthonormal 𝕜 e →
    (Submodule.span 𝕜 (Set.range e)).topologicalClosure = ⊤ →
    (∃ (d : ℕ) (σ : Fin d ≃ I), IsUnconditionalFiniteBasisValue 𝕜 H (e ∘ σ)) ∨
    (∃ σ : ℕ ≃ I, IsUnconditionalSchauderBasisValue 𝕜 H (e ∘ σ))

end ExpandedFA.P1.C15SubsetProjections.Spec
