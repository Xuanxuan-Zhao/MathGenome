import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.Conventions

/-! Independent statement of paper.tex, fa2:p2:cstar-unitization.
`Unitization` stores (scalar, algebra element), reversing the printed pair order.
Having no identity is an algebraic condition, rather than absence of an instance. -/
noncomputable section
namespace ExpandedFA.CStar.Unitization.Spec
universe u

def NoIdentityType := ∀ (A : Type u) [NonUnitalCStarAlgebra A], Prop
def NoIdentityValue : NoIdentityType.{u} := fun A _ =>
  ¬ ∃ e : A, ∀ a : A, e * a = a ∧ a * e = a

def LeftActionType := ∀ (A : Type u) [NonUnitalCStarAlgebra A],
  Unitization ℂ A →ₐ[ℂ] (A →L[ℂ] A)
def LeftActionValue : LeftActionType.{u} := fun A _ =>
  Unitization.lift (NonUnitalAlgHom.Lmul ℂ A)

def LeftActionFormula : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A]
  (x : Unitization ℂ A) (a : A), LeftActionValue A x a = x.snd * a + x.fst • a

def LeftMultiplicationNorm : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A]
  (a : A), ‖ContinuousLinearMap.mul ℂ A a‖ = ‖a‖

def ScalarBound : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A]
  [Nontrivial A], NoIdentityValue A → ∀ x : Unitization ℂ A,
  ‖x.fst‖ ≤ ‖LeftActionValue A x‖

def FaithfulAction : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A]
  [Nontrivial A], NoIdentityValue A → Function.Injective (LeftActionValue A)

def ActionNorm : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A]
  [Nontrivial A], NoIdentityValue A → ∀ x : Unitization ℂ A,
  ‖x‖ = ‖LeftActionValue A x‖

def SumNormComparison : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A]
  [Nontrivial A], NoIdentityValue A → ∀ x : Unitization ℂ A,
  ‖LeftActionValue A x‖ ≤ ‖x.snd‖ + ‖x.fst‖ ∧
  ‖x.snd‖ + ‖x.fst‖ ≤ 3 * ‖LeftActionValue A x‖

def CStarStructure : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A],
  CompleteSpace (Unitization ℂ A) ∧
  ∀ x : Unitization ℂ A, ‖star x * x‖ = ‖x‖ ^ 2

def ClosedIdealEmbedding : Prop := ∀ (A : Type u) [NonUnitalCStarAlgebra A],
  Isometry (Unitization.inrNonUnitalStarAlgHom ℂ A) ∧
  IsClosed (Set.range (Unitization.inrNonUnitalStarAlgHom ℂ A)) ∧
  (∀ (x : Unitization ℂ A) (a : A),
    x * (a : Unitization ℂ A) ∈ Set.range (Unitization.inrNonUnitalStarAlgHom ℂ A) ∧
    (a : Unitization ℂ A) * x ∈ Set.range (Unitization.inrNonUnitalStarAlgHom ℂ A))

def ZeroAlternative : Prop := ExpandedFA.CStar.Conventions.Spec.ZeroUnitizationAlternative.{u}
def UnitalAlternative : Prop := ExpandedFA.CStar.Conventions.Spec.UnitalUnitizationAlternative.{u}

end ExpandedFA.CStar.Unitization.Spec
