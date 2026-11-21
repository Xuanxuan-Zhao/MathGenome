import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SymmetryAndDeficiencies

/-! Relative symmetric perturbations, paper.tex:13781–13801.
The graph-continuous extension in the core clause is the restriction of the
closure of B to D(closure A). All equalities are equalities of partial maps,
and therefore include their domains. No sign condition on a or b is added. -/
noncomputable section
universe u
namespace ExpandedFA.Unbounded.KatoRellichSpec
open SymmetryAndDeficienciesSpec OperatorDomainsSpec

def KatoRellich : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : Operator ℂ H H), selfAdjointValue A → symmetricValue B →
    (hD : A.domain ≤ B.domain) → ∀ a b : ℝ, a < 1 →
    (∀ x : A.domain, ‖B ⟨x, hD x.prop⟩‖ ≤ a * ‖A x‖ + b * ‖(x : H)‖) →
    selfAdjointValue (A + B) ∧ (A + B).domain = A.domain

def KatoRellichCore : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : Operator ℂ H H) (D₀ : Submodule ℂ H),
    essentiallySelfAdjointValue A → coreValue A D₀ → symmetricValue B →
    (hB : D₀ ≤ B.domain) → ∀ a b : ℝ, a < 1 →
    (∀ x : (A.domRestrict D₀).domain,
      ‖B ⟨x, hB x.prop.1⟩‖ ≤
        a * ‖(A.domRestrict D₀) x‖ + b * ‖(x : H)‖) →
    ∃ hD : A.closure.domain ≤ B.closure.domain,
      (∃ F : GraphDomain A.closure →L[ℂ] H,
        ∀ x : GraphDomain A.closure,
          F x = B.closure ⟨GraphDomain.toDomain A.closure x, hD x.prop⟩) ∧
      (∀ x : A.closure.domain,
        ‖B.closure ⟨x, hD x.prop⟩‖ ≤ a * ‖A.closure x‖ + b * ‖(x : H)‖) ∧
      selfAdjointValue (A.closure + B.closure) ∧
      ((A + B).domRestrict D₀).IsClosable ∧
      ((A + B).domRestrict D₀).closure = A.closure + B.closure ∧
      (((A + B).domRestrict D₀).closure).domain = A.closure.domain

section RealPredicates
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The real version of the shared complex symmetry predicate, with the same adjoint. -/
def realSymmetricValue (S : Operator ℝ H H) : Prop :=
  Dense (S.domain : Set H) ∧ S ≤ HilbertAdjointSpec.adjointValue S

/-- Equality of real partial maps includes equality of their domains. -/
def realSelfAdjointValue (S : Operator ℝ H H) : Prop :=
  Dense (S.domain : Set H) ∧ S = HilbertAdjointSpec.adjointValue S

def realEssentiallySelfAdjointValue (S : Operator ℝ H H) : Prop :=
  Dense (S.domain : Set H) ∧ S.IsClosable ∧ realSelfAdjointValue S.closure
end RealPredicates

def KatoRellichReal : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A B : Operator ℝ H H), realSelfAdjointValue A → realSymmetricValue B →
    (hD : A.domain ≤ B.domain) → ∀ a b : ℝ, a < 1 →
    (∀ x : A.domain, ‖B ⟨x, hD x.prop⟩‖ ≤ a * ‖A x‖ + b * ‖(x : H)‖) →
    realSelfAdjointValue (A + B) ∧ (A + B).domain = A.domain

def KatoRellichCoreReal : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A B : Operator ℝ H H) (D₀ : Submodule ℝ H),
    realEssentiallySelfAdjointValue A → coreValue A D₀ → realSymmetricValue B →
    (hB : D₀ ≤ B.domain) → ∀ a b : ℝ, a < 1 →
    (∀ x : (A.domRestrict D₀).domain,
      ‖B ⟨x, hB x.prop.1⟩‖ ≤
        a * ‖(A.domRestrict D₀) x‖ + b * ‖(x : H)‖) →
    ∃ hD : A.closure.domain ≤ B.closure.domain,
      (∃ F : GraphDomain A.closure →L[ℝ] H,
        ∀ x : GraphDomain A.closure,
          F x = B.closure ⟨GraphDomain.toDomain A.closure x, hD x.prop⟩) ∧
      (∀ x : A.closure.domain,
        ‖B.closure ⟨x, hD x.prop⟩‖ ≤ a * ‖A.closure x‖ + b * ‖(x : H)‖) ∧
      realSelfAdjointValue (A.closure + B.closure) ∧
      ((A + B).domRestrict D₀).IsClosable ∧
      ((A + B).domRestrict D₀).closure = A.closure + B.closure ∧
      (((A + B).domRestrict D₀).closure).domain = A.closure.domain

end ExpandedFA.Unbounded.KatoRellichSpec
