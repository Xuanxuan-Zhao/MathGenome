import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.RCLike.Basic

/-! Independent algebraic tensor interface for paper.tex:12664–12676.
The underlying quotient is the algebraic tensor product, never an operator quotient.
Completeness is unnecessary for these finite constructions. -/
noncomputable section

namespace ExpandedFA.AP.AlgebraicRankOneTensorsSpec

open scoped TensorProduct

universe u v
variable (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

abbrev Tensor := (X →L[𝕜] 𝕜) ⊗[𝕜] X

variable {𝕜 X}

/-- A finite algebraic representation, with repetitions and zero terms permitted. -/
def tensorSum (l : List ((X →L[𝕜] 𝕜) × X)) : Tensor 𝕜 X :=
  (l.map fun p => p.1 ⊗ₜ[𝕜] p.2).sum

def cost (l : List ((X →L[𝕜] 𝕜) × X)) : ℝ :=
  (l.map fun p => ‖p.1‖ * ‖p.2‖).sum

/-- Equality here is tensor equality, before applying the operator map. -/
def Representation (t : Tensor 𝕜 X) :=
  {l : List ((X →L[𝕜] 𝕜) × X) // tensorSum l = t}

noncomputable def nu (t : Tensor 𝕜 X) : ℝ :=
  ⨅ r : Representation t, cost r.val

/-- Bilinear evaluation of the continuous linear (not conjugate linear) dual. -/
def tracePairing : (X →L[𝕜] 𝕜) →ₗ[𝕜] X →ₗ[𝕜] 𝕜 where
  toFun f := f.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def trace : Tensor 𝕜 X →ₗ[𝕜] 𝕜 := TensorProduct.lift tracePairing

def operator : Tensor 𝕜 X →ₗ[𝕜] (X →L[𝕜] X) :=
  TensorProduct.lift (ContinuousLinearMap.smulRightLₗ 𝕜 X X)

/-- All tensors have finite algebraic representations, including zero. -/
def Representable : Prop := ∀ t : Tensor 𝕜 X, Nonempty (Representation t)

def TraceFormula : Prop := ∀ l : List ((X →L[𝕜] 𝕜) × X),
  trace (tensorSum l) = (l.map fun p => p.1 p.2).sum

def OperatorFormula : Prop := ∀ (l : List ((X →L[𝕜] 𝕜) × X)) (x : X),
  operator (tensorSum l) x = (l.map fun p => (p.1 x) • p.2).sum

def InfimumBound : Prop := ∀ l : List ((X →L[𝕜] 𝕜) × X),
  nu (tensorSum l) ≤ cost l

def Nonnegative : Prop := ∀ t : Tensor 𝕜 X, 0 ≤ nu t

def ZeroValue : Prop := nu (0 : Tensor 𝕜 X) = 0

def TraceBound : Prop := ∀ t : Tensor 𝕜 X, ‖trace t‖ ≤ nu t

def OperatorBound : Prop := ∀ t : Tensor 𝕜 X, ‖operator t‖ ≤ nu t

def Subadditive : Prop := ∀ s t : Tensor 𝕜 X, nu (s + t) ≤ nu s + nu t

def FiniteRank : Prop := ∀ t : Tensor 𝕜 X,
  FiniteDimensional 𝕜 (LinearMap.range (operator t).toLinearMap)

/-- Near-minimal representations needed to use the infimum quantitatively. -/
def NearInfimum : Prop := ∀ (t : Tensor 𝕜 X) (ε : ℝ), 0 < ε →
  ∃ r : Representation t, cost r.val < nu t + ε

namespace Expected

/-- Full independent types, including the scalar and space quantifiers. -/
def TensorType := ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X], Type (max u v)
def TensorValue : TensorType.{u,v} := fun 𝕜 X _ _ _ => Tensor 𝕜 X

def NuType := ∀ {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X], Tensor 𝕜 X → ℝ
def NuValue : NuType.{u,v} := @nu

def TraceType := ∀ {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X], Tensor 𝕜 X →ₗ[𝕜] 𝕜
def TraceValue : TraceType.{u,v} := @trace

def OperatorType := ∀ {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X], Tensor 𝕜 X →ₗ[𝕜] (X →L[𝕜] X)
def OperatorValue : OperatorType.{u,v} := @operator

def RepresentableStatement : Prop := ∀ {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X], Representable (𝕜 := 𝕜) (X := X)

def TraceFormulaStatement : Prop := ∀ {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X], TraceFormula (𝕜 := 𝕜) (X := X)

def OperatorFormulaStatement : Prop := ∀ {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X], OperatorFormula (𝕜 := 𝕜) (X := X)

def InfimumBoundStatement : Prop := ∀ {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X], InfimumBound (𝕜 := 𝕜) (X := X)

def NonnegativeStatement : Prop := ∀ {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X], Nonnegative (𝕜 := 𝕜) (X := X)

def ZeroValueStatement : Prop := ∀ {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X], ZeroValue (𝕜 := 𝕜) (X := X)

def TraceBoundStatement : Prop := ∀ {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X], TraceBound (𝕜 := 𝕜) (X := X)

def OperatorBoundStatement : Prop := ∀ {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X], OperatorBound (𝕜 := 𝕜) (X := X)

def SubadditiveStatement : Prop := ∀ {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X], Subadditive (𝕜 := 𝕜) (X := X)

def FiniteRankStatement : Prop := ∀ {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X], FiniteRank (𝕜 := 𝕜) (X := X)

def NearInfimumStatement : Prop := ∀ {𝕜 : Type u} {X : Type v} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X], NearInfimum (𝕜 := 𝕜) (X := X)

end Expected

end ExpandedFA.AP.AlgebraicRankOneTensorsSpec
