import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.PolyhedraElimination

/-! Models for paper.tex §§v04-06–07. `WithTop ℝ` excludes minus infinity
from the data; `EReal` allows both infinite optimal values. Index types are
finite but may be empty. These algebraic definitions and weak duality work
in arbitrary dimension, hence in particular in the stipulated finite dimension.
The dual infimum always uses the common domain, independently of multipliers. -/
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open Set
open scoped BigOperators
universe u v w z
namespace VariationalNotes.Ch04.ConvexProgramSpecs

/-- Canonical data shared by the independent statements and implementation. -/
structure ConvexProgram (X : Type u) [AddCommGroup X] [Module ℝ X]
    (I : Type v) (A : Type w) (J : Type z) where
  f : X → WithTop ℝ
  g : I → X → WithTop ℝ
  a : A → X →ᵃ[ℝ] ℝ
  b : A → ℝ
  e : J → X →ᵃ[ℝ] ℝ
  d : J → ℝ
  convex_f : VariationalNotes.ConvexAnalysis.Specs.IsConvex f
  convex_g : ∀ i, VariationalNotes.ConvexAnalysis.Specs.IsConvex (g i)

/-- Equality multipliers are unrestricted real numbers. -/
structure Multipliers (I : Type v) (A : Type w) (J : Type z) where
  lam : I → ℝ
  mu : A → ℝ
  nu : J → ℝ

def ConvexProgramValue := ConvexProgram
def MultipliersValue := Multipliers

def ConvexProgramType :=
  ∀ (X : Type u) [AddCommGroup X] [Module ℝ X]
    (I : Type v) (A : Type w) (J : Type z), Type (max u v w z)

def MultipliersType :=
  ∀ (I : Type v) (A : Type w) (J : Type z), Type (max v w z)

section Models
variable {X : Type u} [AddCommGroup X] [Module ℝ X]
  {I : Type v} {A : Type w} {J : Type z}
  [Fintype I] [Fintype A] [Fintype J]

def commonDomain (p : ConvexProgram X I A J) : Set X :=
  VariationalNotes.ConvexAnalysis.Specs.effectiveDomain p.f ∩
    {x | ∀ i, x ∈ VariationalNotes.ConvexAnalysis.Specs.effectiveDomain (p.g i)}

def affinePolyhedron (p : ConvexProgram X I A J) : Set X :=
  {x | (∀ l, p.a l x ≤ p.b l) ∧ ∀ j, p.e j x = p.d j}

def feasibleSet (p : ConvexProgram X I A J) : Set X :=
  {x | x ∈ commonDomain p ∧ x ∈ affinePolyhedron p ∧ ∀ i, p.g i x ≤ 0}

def admissible (m : Multipliers I A J) : Prop :=
  (∀ i, 0 ≤ m.lam i) ∧ ∀ l, 0 ≤ m.mu l

/-- Real expression for the Lagrangian on the common domain. The extractor's
arbitrary default outside that domain is never used in the dual infimum;
`lagrangian` is the extended function to use at ambient points. -/
def lagrangianReal (p : ConvexProgram X I A J) (m : Multipliers I A J) (x : X) : ℝ :=
  (WithTop.untopD (α := ℝ) 0 (p.f x)) + ∑ i, m.lam i * (WithTop.untopD (α := ℝ) 0 (p.g i x)) +
    ∑ l, m.mu l * (p.a l x - p.b l) + ∑ j, m.nu j * (p.e j x - p.d j)

def lagrangian (p : ConvexProgram X I A J) (m : Multipliers I A J) (x : X) : WithTop ℝ :=
  by
    classical
    exact if x ∈ commonDomain p then (lagrangianReal p m x : WithTop ℝ) else ⊤

def primalValue (p : ConvexProgram X I A J) : EReal :=
  ⨅ x : feasibleSet p, VariationalNotes.ConvexAnalysis.Specs.toEReal (p.f x)

/-- The infimum is over exactly `D`, even for a zero multiplier. -/
def dualFunction (p : ConvexProgram X I A J) (m : Multipliers I A J) : EReal :=
  ⨅ x : commonDomain p, (lagrangianReal p m x : EReal)

def dualValue (p : ConvexProgram X I A J) : EReal :=
  ⨆ m : {m : Multipliers I A J // admissible m}, dualFunction p m

def IsDualMaximizer (p : ConvexProgram X I A J) (m : Multipliers I A J) : Prop :=
  admissible m ∧ dualFunction p m = dualValue p

/-- The inequality products at a common-domain point. `KKTConditions` includes
feasibility, so these real extractions are the actual finite constraint values. -/
def complementarity (p : ConvexProgram X I A J) (m : Multipliers I A J) (x : X) : Prop :=
  (∀ i, m.lam i * (WithTop.untopD (α := ℝ) 0 (p.g i x)) = 0) ∧
    ∀ l, m.mu l * (p.a l x - p.b l) = 0

def IsPrimalMinimizer (p : ConvexProgram X I A J) (x : X) : Prop :=
  x ∈ feasibleSet p ∧ ∀ y ∈ feasibleSet p, p.f x ≤ p.f y

def IsLagrangianMinimizer (p : ConvexProgram X I A J) (m : Multipliers I A J) (x : X) : Prop :=
  x ∈ commonDomain p ∧ ∀ y ∈ commonDomain p, lagrangianReal p m x ≤ lagrangianReal p m y

def KKTConditions (p : ConvexProgram X I A J) (m : Multipliers I A J) (x : X) : Prop :=
  x ∈ feasibleSet p ∧ admissible m ∧ IsLagrangianMinimizer p m x ∧ complementarity p m x

end Models

def commonDomainType :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] {I : Type v} {A : Type w} {J : Type z} , ∀ (p : ConvexProgram X I A J), Set X

def affinePolyhedronType :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] {I : Type v} {A : Type w} {J : Type z} , ∀ (p : ConvexProgram X I A J), Set X

def feasibleSetType :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] {I : Type v} {A : Type w} {J : Type z} , ∀ (p : ConvexProgram X I A J), Set X

def admissibleType :=
  ∀ {I : Type v} {A : Type w} {J : Type z}, ∀ (m : Multipliers I A J), Prop

def lagrangianRealType :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J] , ∀ (p : ConvexProgram X I A J) (m : Multipliers I A J) (x : X), ℝ

def lagrangianType :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J] , ∀ (p : ConvexProgram X I A J) (m : Multipliers I A J) (x : X), WithTop ℝ

def primalValueType :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] {I : Type v} {A : Type w} {J : Type z} , ∀ (p : ConvexProgram X I A J), EReal

def dualFunctionType :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J] , ∀ (p : ConvexProgram X I A J) (m : Multipliers I A J), EReal

def dualValueType :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J] , ∀ (p : ConvexProgram X I A J), EReal

def IsDualMaximizerType :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J] , ∀ (p : ConvexProgram X I A J) (m : Multipliers I A J), Prop

def complementarityType :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] {I : Type v} {A : Type w} {J : Type z} , ∀ (p : ConvexProgram X I A J) (m : Multipliers I A J) (x : X), Prop

def IsPrimalMinimizerType :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] {I : Type v} {A : Type w} {J : Type z} , ∀ (p : ConvexProgram X I A J) (x : X), Prop

def IsLagrangianMinimizerType :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J] , ∀ (p : ConvexProgram X I A J) (m : Multipliers I A J) (x : X), Prop

def KKTConditionsType :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J] , ∀ (p : ConvexProgram X I A J) (m : Multipliers I A J) (x : X), Prop

def commonDomain_finite : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J], ∀ (p : ConvexProgram X I A J) (x : X), x ∈ commonDomain p →
    p.f x = ((WithTop.untopD (α := ℝ) 0 (p.f x)) : WithTop ℝ) ∧
    ∀ i, p.g i x = ((WithTop.untopD (α := ℝ) 0 (p.g i x)) : WithTop ℝ)

def affinePolyhedron_isPolyhedron : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J], ∀ (p : ConvexProgram X I A J),
    VariationalNotes.ConvexGeometry.Specs.IsPolyhedron (affinePolyhedron p)

def lagrangian_on_domain : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J], ∀ (p : ConvexProgram X I A J) (m : Multipliers I A J) (x : X),
    x ∈ commonDomain p → lagrangian p m x = (lagrangianReal p m x : WithTop ℝ)

def lagrangian_outside_domain : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J], ∀ (p : ConvexProgram X I A J) (m : Multipliers I A J) (x : X),
    x ∉ commonDomain p → lagrangian p m x = ⊤

def lagrangian_formula : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J], ∀ (p : ConvexProgram X I A J) (m : Multipliers I A J) (x : X),
    x ∈ commonDomain p → lagrangian p m x = p.f x +
      ∑ i, VariationalNotes.ConvexAnalysis.Specs.weightedValue (m.lam i) (p.g i x) +
      ((∑ l, m.mu l * (p.a l x - p.b l) : ℝ) : WithTop ℝ) +
      ((∑ j, m.nu j * (p.e j x - p.d j) : ℝ) : WithTop ℝ)

def lagrangian_le_objective : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J], ∀ (p : ConvexProgram X I A J) (m : Multipliers I A J) (x : X),
    admissible m → x ∈ feasibleSet p → lagrangianReal p m x ≤ (WithTop.untopD (α := ℝ) 0 (p.f x))

def weak_duality_point : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J], ∀ (p : ConvexProgram X I A J) (m : Multipliers I A J) (x : X),
    admissible m → x ∈ feasibleSet p →
    dualFunction p m ≤ VariationalNotes.ConvexAnalysis.Specs.toEReal (p.f x)

def weak_duality : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J], ∀ (p : ConvexProgram X I A J) (m : Multipliers I A J),
    admissible m → dualFunction p m ≤ primalValue p

def dualValue_le_primalValue : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J], ∀ (p : ConvexProgram X I A J), dualValue p ≤ primalValue p

def dualFunction_eq_inf_extended : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X]
  {I : Type v} {A : Type w} {J : Type z} [Fintype I] [Fintype A] [Fintype J], ∀ (p : ConvexProgram X I A J) (m : Multipliers I A J),
    dualFunction p m = ⨅ x : X, VariationalNotes.ConvexAnalysis.Specs.toEReal (lagrangian p m x)

end VariationalNotes.Ch04.ConvexProgramSpecs
