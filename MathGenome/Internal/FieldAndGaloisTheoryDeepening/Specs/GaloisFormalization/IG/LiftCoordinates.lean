import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.ExtensionClass

/-! Weak lift coordinates and the obstruction in Theorem IG04. -/

namespace Specs.GaloisFormalization.IG.FiniteEmbeddingProblem

open _root_.GaloisFormalization.GH.Model
open scoped IsMulCommutative

universe u v w

noncomputable section

variable {Γ : Type u} {B : Type v} {Q : Type w}
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
  [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
  (P : FiniteEmbeddingProblem Γ B Q) [IsMulCommutative P.kernel]

local notation "A" => Additive P.kernel

local instance : DistribMulAction Q A := P.quotientKernelActionValue
local instance : DistribMulAction Γ A := P.pullbackKernelActionValue

local instance : ContinuousSMul Γ A :=
  ⟨(continuous_smul (M := Q) (X := A)).comp
    ((P.rho.continuous.comp continuous_fst).prodMk continuous_snd)⟩

private theorem rho_equivariant (g : Γ) (a : A) :
    AddMonoidHom.id A (P.rho g • a) = g • AddMonoidHom.id A a := rfl

/-- The factor cocycle pulled back along the prescribed quotient map. -/
def pullbackFactorCocycle (s : NormalizedSection P) : continuousCocycles Γ A 2 :=
  continuousCocycleMap P.rho.toMonoidHom P.rho.continuous
    (AddMonoidHom.id A) (rho_equivariant P) 2 (factorCocycle P s)

/-- The image of the extension class under pullback along the prescribed quotient map. -/
def weakLiftObstruction : ContinuousH Γ A 2 :=
  continuousCohomologyMap P.rho.toMonoidHom P.rho.continuous
    (AddMonoidHom.id A) (rho_equivariant P) 2 (continuousExtensionClass P)

/-- Continuous one-cochains whose differential cancels the pulled-back factor cocycle. -/
def LiftCoordinateSolutions (s : NormalizedSection P) :=
  {z : continuousCochains Γ A 1 //
    continuousDifferential Γ A 1 z = -(pullbackFactorCocycle P s).val}

namespace Specification

private abbrev declarationType {α : Sort*} (_ : α) : Sort _ := α

set_option linter.checkUnivs false

def PullbackFactorCocycleType := declarationType (@pullbackFactorCocycle.{u,v,w})
def WeakLiftObstructionType := declarationType (@weakLiftObstruction.{u,v,w})
def LiftCoordinateSolutionsType := declarationType (@LiftCoordinateSolutions.{u,v,w})

variable (s : NormalizedSection P)

def PullbackFactorCocycleFormula : Prop :=
  ∀ g h : Γ, (pullbackFactorCocycle P s).val.val ![g, h] = factorSet P s (P.rho g) (P.rho h)

def ObstructionClassOfSection : Prop :=
  continuousClass Γ A 2 (pullbackFactorCocycle P s) = weakLiftObstruction P

def LiftCoordinateEquation : Prop :=
  ∀ z : continuousCochains Γ A 1,
    continuousDifferential Γ A 1 z = -(pullbackFactorCocycle P s).val ↔
      ∀ g h : Γ,
        z.val ![g] + g • z.val ![h] - z.val ![g * h] = -factorSet P s (P.rho g) (P.rho h)

def WeakSolutionCoordinateEquiv : Prop :=
  ∃ e : P.WeakSolution ≃ LiftCoordinateSolutions P s,
    (∀ (solution : P.WeakSolution) (g : Γ),
      (e solution).val.val ![g] = kernelCoordinate P s (solution.lift g)) ∧
    (∀ (z : LiftCoordinateSolutions P s) (g : Γ),
      (e.symm z).lift g = (z.val.val ![g]).toMul.val * s (P.rho g))

def LiftCoordinateAtOne : Prop :=
  ∀ z : LiftCoordinateSolutions P s, z.val.val ![1] = 0

def LiftCoordinateConjugation : Prop :=
  ∀ (a : A) (g : Γ) (b : B), P.pi b = P.rho g →
    kernelCoordinate P s (a.toMul.val * b * (a.toMul.val)⁻¹) =
      kernelCoordinate P s b + a - g • a

def LiftCoordinateTranslation : Prop :=
  ∀ (z : LiftCoordinateSolutions P s) (w : continuousCochains Γ A 1),
    continuousDifferential Γ A 1 (z.val + w) = -(pullbackFactorCocycle P s).val ↔
      w ∈ continuousCocycles Γ A 1

def WeakSolutionObstruction : Prop :=
  Nonempty P.WeakSolution ↔ weakLiftObstruction P = 0

private abbrev forEveryAbelianProblem
    (statement : ∀ {Γ : Type u} {B : Type v} {Q : Type w}
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
      [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
      [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
      [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
      (P : FiniteEmbeddingProblem Γ B Q) [IsMulCommutative P.kernel], Prop) : Prop :=
  ∀ {Γ : Type u} {B : Type v} {Q : Type w}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (P : FiniteEmbeddingProblem Γ B Q) [IsMulCommutative P.kernel], statement P

def PullbackFactorCocycleFormulaStatement : Prop :=
  forEveryAbelianProblem.{u,v,w} fun P => ∀ s : NormalizedSection P, PullbackFactorCocycleFormula P s

def ObstructionClassOfSectionStatement : Prop :=
  forEveryAbelianProblem.{u,v,w} fun P => ∀ s : NormalizedSection P, ObstructionClassOfSection P s

def LiftCoordinateEquationStatement : Prop :=
  forEveryAbelianProblem.{u,v,w} fun P => ∀ s : NormalizedSection P, LiftCoordinateEquation P s

def WeakSolutionCoordinateEquivStatement : Prop :=
  forEveryAbelianProblem.{u,v,w} fun P => ∀ s : NormalizedSection P, WeakSolutionCoordinateEquiv P s

def LiftCoordinateAtOneStatement : Prop :=
  forEveryAbelianProblem.{u,v,w} fun P => ∀ s : NormalizedSection P, LiftCoordinateAtOne P s

def LiftCoordinateConjugationStatement : Prop :=
  forEveryAbelianProblem.{u,v,w} fun P => ∀ s : NormalizedSection P, LiftCoordinateConjugation P s

def LiftCoordinateTranslationStatement : Prop :=
  forEveryAbelianProblem.{u,v,w} fun P => ∀ s : NormalizedSection P, LiftCoordinateTranslation P s

def WeakSolutionObstructionStatement : Prop :=
  forEveryAbelianProblem.{u,v,w} fun P => WeakSolutionObstruction P

end Specification
end
end Specs.GaloisFormalization.IG.FiniteEmbeddingProblem
