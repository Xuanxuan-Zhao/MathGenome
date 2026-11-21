import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.PositiveConeSquareRoots

/-!
The full positivity and order theorem, paper.tex:12235–12243.
The five qualitative clauses retain the prerequisite's independent statements.
The quantitative clause uses the same spectral positivity and difference order,
with the original norm. Algebras may be nonunital or zero; no order structure
or faithful representation is an additional hypothesis.
-/

namespace ExpandedFA.CStar.OrderNormMonotonicity.Spec
universe u

def SelfAdjointSquareCharacterization : Prop :=
  PositiveConeSquareRoots.Spec.SelfAdjointSquareCharacterization.{u}

def StarSquareCharacterization : Prop :=
  PositiveConeSquareRoots.Spec.StarSquareCharacterization.{u}

def ClosedProperConvexCone : Prop :=
  PositiveConeSquareRoots.Spec.ClosedProperConvexCone.{u}

def UniquePositiveSquareRoot : Prop :=
  PositiveConeSquareRoots.Spec.UniquePositiveSquareRoot.{u}

def OperatorQuadraticCharacterization : Prop :=
  PositiveConeSquareRoots.Spec.OperatorQuadraticCharacterization.{u}

/-- `PositiveValue A a` means `0 ≤ a`, and `OrderRelationValue A a b`
means that `b - a` is positive. Both use the shared spectral definition. -/
def OrderNormMonotonicity : Prop :=
  ∀ (A : Type u) [NonUnitalCStarAlgebra A] (a b : A),
    Conventions.Spec.PositiveValue A a →
    Conventions.Spec.OrderRelationValue A a b → ‖a‖ ≤ ‖b‖

end ExpandedFA.CStar.OrderNormMonotonicity.Spec
