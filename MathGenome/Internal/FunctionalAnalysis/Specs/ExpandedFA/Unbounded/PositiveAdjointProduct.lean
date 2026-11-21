import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.ClosabilityAndDoubleAdjoint
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The adjoint-product stage of paper.tex:13879–13892. Products below use
exact product domains; normality is product equality, not a domain/norm
characterization. Both Hilbert spaces may be nonseparable and may be zero. -/
noncomputable section
namespace ExpandedFA.Unbounded.PositiveAdjointProductSpec
open OperatorDomainsSpec HilbertAdjointSpec

/-- The canonical exact-domain product A*A. -/
abbrev adjointProduct {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    (A : Operator 𝕜 H K) := productValue (adjointValue A) A

def ShiftSurjective : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) → A.IsClosed →
    ∀ f : H, ∃ x : (adjointProduct A).domain, (x : H) + adjointProduct A x = f

def ProductProperties : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) → A.IsClosed →
    Dense ((adjointProduct A).domain : Set H) ∧
    adjointProduct A = adjointValue (adjointProduct A) ∧
    ∀ x : (adjointProduct A).domain, 0 ≤ RCLike.re (inner 𝕜 (x : H) (adjointProduct A x))

/-- B is an everywhere defined bounded inverse on precisely D(A*A),
with both inverse laws, positivity, injectivity, self-adjointness and norm ≤ 1. -/
def InverseProperties : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) → A.IsClosed →
    ∃ B : H →L[𝕜] H,
      (∀ f : H, ∃ hx : B f ∈ (adjointProduct A).domain,
        B f + adjointProduct A ⟨B f, hx⟩ = f) ∧
      (∀ x : (adjointProduct A).domain, B ((x : H) + adjointProduct A x) = (x : H)) ∧
      Function.Injective B ∧ B.adjoint = B ∧ ‖B‖ ≤ 1 ∧
      ∀ f : H, 0 ≤ RCLike.re (inner 𝕜 f (B f))

def GraphCore : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) → A.IsClosed →
    coreValue A (adjointProduct A).domain

/-- No domain equality or norm equality is included among these hypotheses. -/
def NormalDomainNorm : Prop :=
  ∀ {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (N : Operator 𝕜 H H), Dense (N.domain : Set H) → N.IsClosed →
    productValue (adjointValue N) N = productValue N (adjointValue N) →
    N.domain = (adjointValue N).domain ∧
      ∀ (x : N.domain) (y : (adjointValue N).domain),
        (x : H) = (y : H) → ‖N x‖ = ‖adjointValue N y‖
end ExpandedFA.Unbounded.PositiveAdjointProductSpec
