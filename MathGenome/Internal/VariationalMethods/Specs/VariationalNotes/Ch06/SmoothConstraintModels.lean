import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.PolyhedralTangentNormal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
Independent specifications for paper.tex §§v06-03, v06-04, and the opening of v06-06.
All finite index types may be empty. The scalar functions represent data on U by
ambient extensions; derivatives at points of the open U are the ordinary Fréchet
derivatives. The algebraic definitions and KKT identities hold in any real normed
space, and in particular in every finite-dimensional real space in the source.
No constraint qualification or optimization theorem is assumed by these Specs.
-/
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
universe u v w
namespace VariationalNotes.Ch06.Specs

 /-- Regularity on the open domain. The definitions below also make sense without regularity. -/
def SmoothConstraintData {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) : Prop :=
  IsOpen U ∧ ContDiffOn ℝ 1 f U ∧
    (∀ i, ContDiffOn ℝ 1 (g i) U) ∧ (∀ j, ContDiffOn ℝ 1 (h j) U)

def SmoothConstraintDataType :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J] (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ), Prop

 /-- The open domain is part of feasibility. -/
def feasibleSet {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (g : I → X → ℝ) (h : J → X → ℝ) : Set X :=
  {x | x ∈ U ∧ (∀ i, g i x ≤ 0) ∧ (∀ j, h j x = 0)}

def feasibleSetType :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J] (U : Set X) (g : I → X → ℝ) (h : J → X → ℝ), Set X

def activeSet {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v}
    (g : I → X → ℝ) (x : X) : Set I :=
  {i | g i x = 0}

def activeSetType :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} (g : I → X → ℝ) (x : X), Set I

 /-- The coordinate assembly of the actual equality differentials. -/
def equalityDerivative {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {J : Type w} [Fintype J]
    (h : J → X → ℝ) (x : X) : X →L[ℝ] (J → ℝ) :=
  ContinuousLinearMap.pi (fun j => fderiv ℝ (h j) x)

def equalityDerivativeType :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {J : Type w} [Fintype J] (h : J → X → ℝ) (x : X), X →L[ℝ] (J → ℝ)

def linearizedCone {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (g : I → X → ℝ) (h : J → X → ℝ) (x : X) : Set X :=
  {d | equalityDerivative h x d = 0 ∧
    ∀ i ∈ activeSet g x, fderiv ℝ (g i) x d ≤ 0}

def linearizedConeType :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J] (g : I → X → ℝ) (h : J → X → ℝ) (x : X), Set X

 /-- Exactly the chapter 1 positive-time feasible-sequence tangent, including scales tending to zero. -/
def constraintTangentCone {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (g : I → X → ℝ) (h : J → X → ℝ) (x : X) : Set X :=
  VariationalNotes.ConvexGeometry.Specs.contingentTangent (feasibleSet U g h) x

def constraintTangentConeType :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J] (U : Set X) (g : I → X → ℝ) (h : J → X → ℝ) (x : X), Set X

 /-- Independence is of the combined active-inequality and equality family. -/
def LICQ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (g : I → X → ℝ) (h : J → X → ℝ) (x : X) : Prop :=
  x ∈ feasibleSet U g h ∧
    LinearIndependent ℝ
      (Sum.elim (fun i : {i // i ∈ activeSet g x} => fderiv ℝ (g i.val) x)
        (fun j : J => fderiv ℝ (h j) x))

def LICQType :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J] (U : Set X) (g : I → X → ℝ) (h : J → X → ℝ) (x : X), Prop

def MFCQ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (g : I → X → ℝ) (h : J → X → ℝ) (x : X) : Prop :=
  x ∈ feasibleSet U g h ∧ Function.Surjective (equalityDerivative h x) ∧
    ∃ w : X, equalityDerivative h x w = 0 ∧
      ∀ i ∈ activeSet g x, fderiv ℝ (g i) x w < 0

def MFCQType :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J] (U : Set X) (g : I → X → ℝ) (h : J → X → ℝ) (x : X), Prop

 /-- The equality multipliers are unrestricted real numbers. -/
def KKT {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X) (lam : I → ℝ) (nu : J → ℝ) : Prop :=
  x ∈ feasibleSet U g h ∧ (∀ i, 0 ≤ lam i) ∧
    (∀ i, lam i * g i x = 0) ∧
    fderiv ℝ f x + (∑ i, lam i • fderiv ℝ (g i) x) +
      (∑ j, nu j • fderiv ℝ (h j) x) = 0

def KKTType :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J] (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X) (lam : I → ℝ) (nu : J → ℝ), Prop

 /-- Nonnegative objective and inequality coefficients, free equalities, and joint nonzeroness. -/
def FritzJohn {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X) (lam0 : ℝ) (lam : I → ℝ) (nu : J → ℝ) : Prop :=
  x ∈ feasibleSet U g h ∧ 0 ≤ lam0 ∧ (∀ i, 0 ≤ lam i) ∧
    (∀ i, lam i * g i x = 0) ∧
    (lam0 ≠ 0 ∨ (∃ i, lam i ≠ 0) ∨ (∃ j, nu j ≠ 0)) ∧
    lam0 • fderiv ℝ f x + (∑ i, lam i • fderiv ℝ (g i) x) +
      (∑ j, nu j • fderiv ℝ (h j) x) = 0

def FritzJohnType :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J] (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X) (lam0 : ℝ) (lam : I → ℝ) (nu : J → ℝ), Prop

def lagrangian {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (lam : I → ℝ) (nu : J → ℝ) : X → ℝ :=
  fun y => f y + (∑ i, lam i * g i y) + ∑ j, nu j * h j y

def lagrangianType :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J] (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (lam : I → ℝ) (nu : J → ℝ), X → ℝ

def criticalCone {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X) : Set X :=
  {d | d ∈ linearizedCone g h x ∧ fderiv ℝ f x d ≤ 0}

def criticalConeType :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J] (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X), Set X

/-- C¹ on an open domain gives the actual derivatives used in all systems. -/
def smoothConstraintData_hasFDerivAt : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    SmoothConstraintData U f g h → x ∈ U →
    HasFDerivAt f (fderiv ℝ f x) x ∧
      (∀ i, HasFDerivAt (g i) (fderiv ℝ (g i) x) x) ∧
      (∀ j, HasFDerivAt (h j) (fderiv ℝ (h j) x) x)

/-- Coordinate derivatives assemble to the derivative of the actual vector of equalities. -/
def equalityDerivative_hasFDerivAt : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {J : Type w} [Fintype J] (h : J → X → ℝ) (x : X),
    (∀ j, DifferentiableAt ℝ (h j) x) →
      HasFDerivAt (fun y j => h j y) (equalityDerivative h x) x

def constraintTangentCone_eq : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    constraintTangentCone U g h x =
      VariationalNotes.ConvexGeometry.Specs.contingentTangent (feasibleSet U g h) x

def kkt_inactive_multiplier : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ)
    (x : X) (lam : I → ℝ) (nu : J → ℝ),
    KKT U f g h x lam nu → ∀ i, i ∉ activeSet g x → lam i = 0

/-- The active-index sum and the sign of the objective differential on Clin. -/
def kkt_linearized_identity : Prop := by
  classical
  exact ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ)
    (x : X) (lam : I → ℝ) (nu : J → ℝ),
    KKT U f g h x lam nu → ∀ d ∈ linearizedCone g h x,
      fderiv ℝ f x d =
        -(∑ i : {i // i ∈ activeSet g x}, lam i.val * fderiv ℝ (g i.val) x d) ∧
      0 ≤ fderiv ℝ f x d

def criticalCone_eq_zero : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ)
    (x : X) (lam : I → ℝ) (nu : J → ℝ),
    KKT U f g h x lam nu →
      criticalCone f g h x = {d | d ∈ linearizedCone g h x ∧ fderiv ℝ f x d = 0}

def criticalCone_eq_positive_multipliers : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ)
    (x : X) (lam : I → ℝ) (nu : J → ℝ),
    KKT U f g h x lam nu →
      criticalCone f g h x =
        {d | d ∈ linearizedCone g h x ∧ ∀ i, 0 < lam i → fderiv ℝ (g i) x d = 0}

end VariationalNotes.Ch06.Specs
