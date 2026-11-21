import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06Conjugates

/-!
Independent specifications for the definitions in paper.tex:8053–8077.
The primal value space is the shared `WithTop ℝ`, with no −∞, and the
functionals are the continuous real-linear dual. The definitions extend to
all extended functions and all sets; in particular they apply to the proper
convex functions of the manuscript without extra regularity assumptions.
-/
namespace ExpandedFA.BanachConvex.Spec

open ExpandedFA.P1.ExtendedConvexFunctions

universe u

/-- The subdifferential is set-valued, even at points of finite energy. -/
def SubdifferentialType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    ExtendedFunction X → X → Set (X →L[ℝ] ℝ)

/-- The finite-domain guard makes the subdifferential empty at +∞. Addition
here is only of a half-extended primal value and a finite real number. -/
def SubdifferentialValue : SubdifferentialType.{u} :=
  fun X _ _ φ x => {f | x ∈ ExpandedFA.P1.ExtendedConvexFunctions.Spec.finiteDomainValue X φ ∧
    ∀ y : X, φ x + (f (y - x) : WithTop ℝ) ≤ φ y}

def SubgradientDomainType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    ExtendedFunction X → Set X

/-- D(∂φ) is defined by existence of a subgradient. -/
def SubgradientDomainValue : SubgradientDomainType.{u} :=
  fun X _ _ φ => {x | (SubdifferentialValue X φ x).Nonempty}

def NormalConeType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    Set X → X → Set (X →L[ℝ] ℝ)

/-- Membership of the base point is required, including for empty sets C. -/
def NormalConeValue : NormalConeType.{u} :=
  fun X _ _ C x => {f | x ∈ C ∧ ∀ y ∈ C, f (y - x) ≤ 0}

def DualityMapType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    X → Set (X →L[ℝ] ℝ)

/-- The normalized duality map is a set; no smoothness is assumed. -/
def DualityMapValue : DualityMapType.{u} :=
  fun _ _ _ x => {f | ‖f‖ = ‖x‖ ∧ f x = ‖x‖ ^ 2}

/-- At a finite value the definition is exactly the displayed supporting
inequality, with every competitor y (including infinite-valued ones). -/
def SubdifferentialAtFiniteValue : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (x : X) (r : ℝ), φ x = (r : WithTop ℝ) →
    SubdifferentialValue X φ x =
      {f | ∀ y : X, ((r + f (y - x) : ℝ) : WithTop ℝ) ≤ φ y}

def SubdifferentialAtInfinity : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (x : X), φ x = ⊤ →
    SubdifferentialValue X φ x = ∅

def SubgradientDomainIdentification : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (x : X),
    x ∈ SubgradientDomainValue X φ ↔ ∃ f, f ∈ SubdifferentialValue X φ x

def SubgradientDomainSubset : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X),
    SubgradientDomainValue X φ ⊆ ExpandedFA.P1.ExtendedConvexFunctions.Spec.finiteDomainValue X φ

def NormalConeOutside : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (x : X), x ∉ C → NormalConeValue X C x = ∅

def NormalConeAtMember : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (x : X), x ∈ C →
    NormalConeValue X C x = {f | ∀ y ∈ C, f (y - x) ≤ 0}

def DualityMapAtZero : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    DualityMapValue X 0 = {0}

end ExpandedFA.BanachConvex.Spec
