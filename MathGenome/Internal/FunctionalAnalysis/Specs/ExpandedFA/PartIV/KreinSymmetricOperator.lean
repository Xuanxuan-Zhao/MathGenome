import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinSolutions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SymmetryAndDeficiencies
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
The Gram-space and symmetric-operator construction in the first three paragraphs
of the proof of `fa2:p4:krein-kernel` (paper.tex:21124–21147).
`true` denotes the plus/even case, `false` the minus/odd case. Positivity is the
upstream real finite-quadratic-sum condition; complex positivity is not assumed.
The zero Hilbert space is permitted. The final assertion is existence of an
extension of the closure, with no essential self-adjointness or uniqueness claim.
-/
noncomputable section
open scoped InnerProductSpace ComplexConjugate ContDiff
open MeasureTheory

namespace ExpandedFA.PartIV.KreinSymmetricOperator.Spec
open ExpandedFA.Unbounded

/-- Select one of the two original real kernels. -/
def kernel (p : Bool) (F : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  if p then KreinSolutions.Specs.KernelPlusValue F else KreinSolutions.Specs.KernelMinusValue F

/-- The scalar implementing the chosen parity. -/
def paritySign (p : Bool) : ℂ := if p then 1 else -1

/-- Smooth complex tests of the chosen parity, compactly supported in ℝ. -/
def SmoothTest (p : Bool) :=
  {f : ℝ → ℂ // ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    ∀ t, f (-t) = paritySign p * f t}

/-- The actual vector-valued Lebesgue integral, also used for second derivatives. -/
def testIntegral {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (v : ℝ → H) (f : ℝ → ℂ) : H :=
  ∫ t : ℝ, f t • v t

/-- The complete Gram realization, including totality, continuity, parity and a
conjugation. These are conclusions to be constructed from kernel positivity. -/
structure GramData (p : Bool) (F : ℝ → ℝ) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  vectors : ℝ → H
  gram : ∀ s t, ⟪vectors s, vectors t⟫_ℂ = (kernel p F s t : ℂ)
  total : (Submodule.span ℂ (Set.range vectors)).topologicalClosure = ⊤
  continuous_vectors : Continuous vectors
  parity : ∀ t, vectors (-t) = paritySign p • vectors t
  conjugation : H →ₗᵢ⋆[ℂ] H
  conjugation_involutive : Function.Involutive conjugation
  conjugation_vectors : ∀ t, conjugation (vectors t) = vectors t

/-- Domain preservation and the commutation identity for the actual partial map. -/
def CommutesWith {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : Operator ℂ H H) (C : H →ₗᵢ⋆[ℂ] H) : Prop :=
  ∀ x : A.domain, ∃ hx : C x ∈ A.domain, A ⟨C x, hx⟩ = C (A x)

/-- Exact domain, action on every test, symmetry, realness and extension of the
closure. Well-definedness follows from the action of a single partial linear map
on its domain; it is not an assumed identity about the tests. -/
def OperatorConclusion {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {p : Bool} {F : ℝ → ℝ} (G : GramData p F H) : Prop :=
  ∃ S₀ : Operator ℂ H H,
    (S₀.domain : Set H) = Set.range (fun f : SmoothTest p => testIntegral G.vectors f.val) ∧
    (∀ f : SmoothTest p, ∃ hf : testIntegral G.vectors f.val ∈ S₀.domain,
      S₀ ⟨testIntegral G.vectors f.val, hf⟩ = testIntegral G.vectors (deriv (deriv f.val))) ∧
    SymmetryAndDeficienciesSpec.symmetricValue S₀ ∧
    CommutesWith S₀ G.conjugation ∧
    S₀.IsClosable ∧
    ∃ S : Operator ℂ H H, S₀.closure ≤ S ∧ SymmetryAndDeficienciesSpec.selfAdjointValue S

/-- Construction of all the geometric data, with the original hypotheses. -/
def GramExists : Prop :=
  ∀ (p : Bool) (F : ℝ → ℝ), Continuous F → Function.Even F →
    KreinSolutions.Specs.PositiveDefiniteValue (kernel p F) →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H), Nonempty (GramData p F H)

/-- Full assigned obligation. All original assumptions occur before the
existentially constructed Hilbert space, vectors, conjugation and operators. -/
def Main : Prop :=
  ∀ (p : Bool) (F : ℝ → ℝ), Continuous F → Function.Even F →
    KreinSolutions.Specs.PositiveDefiniteValue (kernel p F) →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H)
      (G : GramData p F H), OperatorConclusion G

/-- Algebraic descent of a symmetric integral formula through a dense synthesis
map. This is a helper for the construction, not a replacement of `Main`. -/
def SymmetricDescent : Prop :=
  ∀ (T H : Type) [AddCommGroup T] [Module ℂ T]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J L : T →ₗ[ℂ] H), DenseRange J →
    (∀ f g, ⟪L f, J g⟫_ℂ = ⟪J f, L g⟫_ℂ) →
    ∃ A : Operator ℂ H H, A.domain = J.range ∧
      (∀ f, ∃ hf : J f ∈ A.domain, A ⟨J f, hf⟩ = L f) ∧
      SymmetryAndDeficienciesSpec.symmetricValue A ∧ A.IsClosable

/-- The general conjugation criterion used in the source's extension step. -/
def RealSymmetricExtension : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : Operator ℂ H H), SymmetryAndDeficienciesSpec.symmetricValue A →
    ∀ (C : H →ₗᵢ⋆[ℂ] H), Function.Involutive C → CommutesWith A C →
    ∃ B : Operator ℂ H H, A.closure ≤ B ∧ SymmetryAndDeficienciesSpec.selfAdjointValue B

end ExpandedFA.PartIV.KreinSymmetricOperator.Spec
