import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Basis
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Unconditional
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
Independent statements for paper.tex 3962–3974 (fa2:p1:c15:three-bases).
The native ℓ² space has its full square-summable elements, not finite supports.
Index n denotes the manuscript's positive index n+1. Complete orthonormal
systems mean dense linear span. A countable system is enumerated either by
Fin d (including d=0) or by ℕ, without repetition or omitted vectors.
All inner products are conjugate-linear in the first variable.
-/

noncomputable section
open Filter Topology
open scoped BigOperators ENNReal InnerProductSpace
universe u v w

namespace ExpandedFA.P1.BasisNotHamel.Spec

abbrev unitVector (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : lp (fun _ : ℕ => 𝕜) 2 :=
  lp.single 2 n 1

/-- Algebraic span consists of finite linear combinations. -/
def HamelExpansionFinite : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    {I : Type w} (e : I → E) (x : E),
    x ∈ Submodule.span 𝕜 (Set.range e) ↔
      ∃ a : I →₀ 𝕜, (∑ i ∈ a.support, a i • e i) = x

/-- The particular vector 1/n belongs to ℓ² and has every coordinate nonzero.
It admits no finite unit-vector synthesis and is outside their algebraic span. -/
def ReciprocalVector : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], ∃ x : lp (fun _ : ℕ => 𝕜) 2,
    (∀ n : ℕ, x n = ((n + 1 : ℕ) : 𝕜)⁻¹) ∧
    Function.support (fun n => x n) = Set.univ ∧
    (∀ (s : Finset ℕ) (a : ℕ → 𝕜), x ≠ ∑ n ∈ s, a n • unitVector 𝕜 n) ∧
    x ∉ Submodule.span 𝕜 (Set.range (unitVector 𝕜))

/-- These same unit vectors are orthonormal, total, and a Schauder basis.
Their expansions are also unconditional. -/
def StandardSystem : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    Orthonormal 𝕜 (unitVector 𝕜) ∧
    (Submodule.span 𝕜 (Set.range (unitVector 𝕜))).topologicalClosure = ⊤ ∧
    C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) (unitVector 𝕜) ∧
    C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜
      (lp (fun _ : ℕ => 𝕜) 2) (unitVector 𝕜)

def NotHamel : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    Submodule.span 𝕜 (Set.range (unitVector 𝕜)) ≠ ⊤

/-- Every enumeration of a complete orthonormal system by ℕ gives an
unconditional Schauder basis, with Fourier coefficients as its coordinates. -/
def HilbertSequence : Prop :=
  ∀ {I : Type u} {𝕜 : Type v} {H : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : I → H), Orthonormal 𝕜 e →
    (Submodule.span 𝕜 (Set.range e)).topologicalClosure = ⊤ →
    ∀ σ : ℕ ≃ I,
      ∃ h : C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) (e ∘ σ),
        C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜 H (e ∘ σ) ∧
        ∀ (x : H) (n : ℕ), C15Basis.Spec.rawCoordinates h x n = ⟪e (σ n), x⟫_𝕜

/-- The finite version uses finite lists, including the empty list. -/
def HilbertFinite : Prop :=
  ∀ {I : Type u} {𝕜 : Type v} {H : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : I → H), Orthonormal 𝕜 e →
    (Submodule.span 𝕜 (Set.range e)).topologicalClosure = ⊤ →
    ∀ (d : ℕ) (σ : Fin d ≃ I),
      ∃ h : C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) (e ∘ σ),
        C15Unconditional.Spec.IsUnconditionalFiniteBasisValue 𝕜 H (e ∘ σ) ∧
        ∀ (x : H) (n : Fin d), C15Basis.Spec.finiteCoordinates h x n = ⟪e (σ n), x⟫_𝕜

/-- Countability yields either a finite list or an infinite sequence. -/
def HilbertCountable : Prop :=
  ∀ {I : Type u} {𝕜 : Type v} {H : Type w} [Countable I] [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : I → H), Orthonormal 𝕜 e →
    (Submodule.span 𝕜 (Set.range e)).topologicalClosure = ⊤ →
    (∃ (d : ℕ) (σ : Fin d ≃ I),
      C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) (e ∘ σ) ∧
      C15Unconditional.Spec.IsUnconditionalFiniteBasisValue 𝕜 H (e ∘ σ)) ∨
    (∃ σ : ℕ ≃ I,
      C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) (e ∘ σ) ∧
      C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜 H (e ∘ σ))

/-- Arbitrary index sets use the norm limit over all finite subsets. -/
def HilbertFiniteSubsetExpansion : Prop :=
  ∀ {I : Type u} {𝕜 : Type v} {H : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : I → H), Orthonormal 𝕜 e →
    (Submodule.span 𝕜 (Set.range e)).topologicalClosure = ⊤ →
    ∀ x : H, Tendsto (fun s : Finset I => ∑ i ∈ s, ⟪e i, x⟫_𝕜 • e i)
      atTop (𝓝 x)

/-- An uncountable orthonormal family cannot be enumerated by a sequence,
hence cannot itself be an ordered Schauder sequence. -/
def UncountableNotSequence : Prop :=
  ∀ {I : Type u} {𝕜 : Type v} {H : Type w} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (e : I → H), Orthonormal 𝕜 e → ¬ Countable I →
    ¬ ∃ s : ℕ → H, Set.range s = Set.range e

end ExpandedFA.P1.BasisNotHamel.Spec
