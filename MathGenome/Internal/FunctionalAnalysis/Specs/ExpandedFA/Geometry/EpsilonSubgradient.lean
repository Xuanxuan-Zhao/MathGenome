import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.Definitions

/-!
Independent statements for the epsilon-subgradient definition at
paper.tex:12937–12943 and the dual-ball identity used at 12970–12973.
The statements extend to arbitrary half-extended functions on real normed
spaces, hence apply to all the proper lsc convex functions on real Banach
spaces in the source. No change to the canonical conjugate or exact
subdifferential is made.
-/
namespace ExpandedFA.Geometry.EpsilonSubgradient.Spec

open ExpandedFA.P1.ExtendedConvexFunctions

universe u

def EpsilonSubdifferentialType :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    ExtendedFunction X → ℝ → X → Set (X →L[ℝ] ℝ)

/-- The finite-domain guard excludes supporting inequalities based at +∞.
The formula makes sense for every real epsilon; in the approximation theorem
one specializes to epsilon > 0. -/
def EpsilonSubdifferentialValue : EpsilonSubdifferentialType.{u} :=
  fun X _ _ φ ε x =>
    {f | x ∈ ExpandedFA.P1.ExtendedConvexFunctions.Spec.finiteDomainValue X φ ∧
      ∀ y : X, φ x + ((f (y - x) - ε : ℝ) : WithTop ℝ) ≤ φ y}

/-- The source's defining inequality, including competitors of infinite value. -/
def AtFiniteValue : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (ε : ℝ) (x : X) (r : ℝ),
    φ x = (r : WithTop ℝ) →
      EpsilonSubdifferentialValue X φ ε x =
        {f | ∀ y : X, ((r + f (y - x) - ε : ℝ) : WithTop ℝ) ≤ φ y}

def AtInfinity : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (ε : ℝ) (x : X),
    φ x = ⊤ → EpsilonSubdifferentialValue X φ ε x = ∅

/-- Epsilon zero recovers the already established exact subgradient interface. -/
def AtZeroEpsilon : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (x : X),
    EpsilonSubdifferentialValue X φ 0 x =
      ExpandedFA.BanachConvex.Spec.SubdifferentialValue X φ x

/-- Approximate Fenchel equality uses the existing full EReal conjugate.
Only the base value is finite; other values may be +∞. -/
def ConjugateCriterion : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : ExtendedFunction X) (ε : ℝ) (x : X) (r : ℝ),
    φ x = (r : WithTop ℝ) → ∀ f : X →L[ℝ] ℝ,
      f ∈ EpsilonSubdifferentialValue X φ ε x ↔
        ExpandedFA.P1.C06Conjugates.Spec.ConvexConjugateValue X φ f ≤
          ((f x - r + ε : ℝ) : EReal)

/-- The norm subgradient at zero is exactly the closed unit ball of the
continuous real-linear dual, also for the zero space. -/
def NormAtZero : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    ExpandedFA.BanachConvex.Spec.SubdifferentialValue X
      (fun y : X => (‖y‖ : WithTop ℝ)) 0 =
        Metric.closedBall (0 : X →L[ℝ] ℝ) 1

end ExpandedFA.Geometry.EpsilonSubgradient.Spec
