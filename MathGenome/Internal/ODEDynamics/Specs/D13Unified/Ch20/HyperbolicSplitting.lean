import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.MatrixExponential
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Complex.Basic

noncomputable section
namespace D13Unified.Ch20

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The complexification acts on complex coordinate vectors. -/
def complexification (A : Matrix n n ℝ) : Module.End ℂ (n → ℂ) :=
  Matrix.toLinAlgEquiv' (A.map Complex.ofReal)

/-- The real coordinate space inside its complexification. -/
def realEmbedding : (n → ℝ) →ₗ[ℝ] (n → ℂ) where
  toFun v := fun i => (v i : ℂ)
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp [Complex.real_smul]

/-- Generalized spectral sums for the two open half-planes. No eigenbasis or
spectral gap certificate is part of this definition. -/
def complexSpectralSpace (A : Matrix n n ℝ) (stable : Bool) : Submodule ℂ (n → ℂ) :=
  ⨆ μ : {μ : ℂ // if stable then μ.re < 0 else 0 < μ.re},
    (complexification A).maxGenEigenspace μ.val

/-- Real form of the complex generalized spectral sum, retaining conjugate pairs. -/
def realSpectralSpace (A : Matrix n n ℝ) (stable : Bool) : Submodule ℝ (n → ℝ) :=
  ((complexSpectralSpace A stable).restrictScalars ℝ).comap realEmbedding

end D13Unified.Ch20

namespace Specs.D13Unified.Ch20.HyperbolicSplitting
open Classical
open _root_.D13Unified.Ch20
universe u
variable {n : Type u} [Fintype n] [DecidableEq n]

def hyperbolicValue (A : Matrix n n ℝ) : Prop :=
  ∀ μ : ℂ, (complexification A).HasEigenvalue μ → μ.re ≠ 0

def stableSpaceValue (A : Matrix n n ℝ) := realSpectralSpace A true
def unstableSpaceValue (A : Matrix n n ℝ) := realSpectralSpace A false

/-- Total definitions: the complementary projections are used whenever the
spectral sums are complementary. The theorem establishes this for every
hyperbolic matrix; this definition assumes no dichotomy. -/
def projectionValue (A : Matrix n n ℝ) (stable : Bool) : Module.End ℝ (n → ℝ) :=
  if h : IsCompl (realSpectralSpace A stable) (realSpectralSpace A (!stable)) then
    (realSpectralSpace A stable).projection (realSpectralSpace A (!stable)) h
  else 0

def stableProjectionValue (A : Matrix n n ℝ) := projectionValue A true
def unstableProjectionValue (A : Matrix n n ℝ) := projectionValue A false

/-- Closed expected types quantify over every finite coordinate index type,
including the empty type. -/
def hyperbolicType := ∀ {n : Type u} [Fintype n] [DecidableEq n], Matrix n n ℝ → Prop
def spaceType := ∀ {n : Type u} [Fintype n] [DecidableEq n],
  Matrix n n ℝ → Submodule ℝ (n → ℝ)
def projectionType := ∀ {n : Type u} [Fintype n] [DecidableEq n],
  Matrix n n ℝ → Module.End ℝ (n → ℝ)

def splittingType : Prop := ∀ (A : Matrix n n ℝ), hyperbolicValue A →
  IsCompl (stableSpaceValue A) (unstableSpaceValue A)

def conjugateType : Prop := ∀ (A : Matrix n n ℝ) (μ : ℂ) (z : n → ℂ),
  z ∈ (complexification A).maxGenEigenspace μ →
    star z ∈ (complexification A).maxGenEigenspace (star μ)

/-- This explicitly identifies the real form: both real and imaginary parts
of a complex spectral vector lie in the corresponding real subspace. -/
def realFormType : Prop := ∀ (A : Matrix n n ℝ) (stable : Bool) (z : n → ℂ),
  z ∈ complexSpectralSpace A stable ↔
    (fun i => (z i).re) ∈ realSpectralSpace A stable ∧
    (fun i => (z i).im) ∈ realSpectralSpace A stable

def invariantType : Prop := ∀ (A : Matrix n n ℝ) (stable : Bool) (x : n → ℝ),
  x ∈ realSpectralSpace A stable → A.mulVec x ∈ realSpectralSpace A stable

def projectionLawsType : Prop := ∀ (A : Matrix n n ℝ), hyperbolicValue A →
  projectionValue A true + projectionValue A false = 1 ∧
  LinearMap.range (projectionValue A true) = stableSpaceValue A ∧
  LinearMap.ker (projectionValue A true) = unstableSpaceValue A ∧
  LinearMap.range (projectionValue A false) = unstableSpaceValue A ∧
  LinearMap.ker (projectionValue A false) = stableSpaceValue A ∧
  projectionValue A true * projectionValue A true = projectionValue A true ∧
  projectionValue A false * projectionValue A false = projectionValue A false ∧
  projectionValue A true * projectionValue A false = 0 ∧
  projectionValue A false * projectionValue A true = 0

def commutationType : Prop := ∀ (A : Matrix n n ℝ), hyperbolicValue A →
  ∀ stable : Bool,
    Commute (projectionValue A stable) (Matrix.toLinAlgEquiv' A) ∧
    ∀ t : ℝ, Commute (projectionValue A stable)
      (Matrix.toLinAlgEquiv'
        (Specs.D13Unified.Ch07.MatrixExponential.exponentialValue A t))

/-- Closed theorem propositions for binding checks. -/
def splittingExpected : Prop := ∀ {n : Type u} [Fintype n] [DecidableEq n], splittingType (n := n)
def conjugateExpected : Prop := ∀ {n : Type u} [Fintype n] [DecidableEq n], conjugateType (n := n)
def realFormExpected : Prop := ∀ {n : Type u} [Fintype n] [DecidableEq n], realFormType (n := n)
def invariantExpected : Prop := ∀ {n : Type u} [Fintype n] [DecidableEq n], invariantType (n := n)
def projectionLawsExpected : Prop := ∀ {n : Type u} [Fintype n] [DecidableEq n], projectionLawsType (n := n)
def commutationExpected : Prop := ∀ {n : Type u} [Fintype n] [DecidableEq n], commutationType (n := n)

end Specs.D13Unified.Ch20.HyperbolicSplitting
