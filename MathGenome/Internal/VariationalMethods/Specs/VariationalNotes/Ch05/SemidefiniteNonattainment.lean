import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.NonclosedPSDImage
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.EReal.Operations

/-! Independent statements for paper.tex, Proposition `prop:sdp-nonattainment`.
Matrices remain positive semidefinite, with symmetry included in the shared cone.
The dual uses the positive trace dual, so no choice of a matrix norm or inner
product instance changes the pairing. -/
noncomputable section
namespace VariationalNotes.Ch05.SemidefiniteNonattainment.Specs
open VariationalNotes.ConvexGeometry.Specs.PSDImage

abbrev Matrix2 := VariationalNotes.ConvexGeometry.Specs.PSDImage.Matrix2

def feasible : Set Matrix2 := {M | M ∈ psdCone ∧ M 0 1 = 1}
def primalValue : EReal := ⨅ M ∈ feasible, (M 0 0 : EReal)
def tracePair (S M : Matrix2) : ℝ := Matrix.trace (S * M)
def constraintMap : Matrix2 →ₗ[ℝ] ℝ where
  toFun M := M 0 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cost : Matrix2 := symmetricMatrix 1 0 0
def traceAdjoint (y : ℝ) : Matrix2 := symmetricMatrix 0 (y / 2) 0
def slack (y : ℝ) : Matrix2 := cost - traceAdjoint y
def tracePositiveDual : Set Matrix2 :=
  {S | S.IsSymm ∧ ∀ M ∈ psdCone, 0 ≤ tracePair S M}
def dualFeasible : Set ℝ := {y | slack y ∈ tracePositiveDual}
def dualValue : EReal := ⨆ y ∈ dualFeasible, (y : EReal)

def feasible_iff : Prop := ∀ M : Matrix2,
  M ∈ feasible ↔ ∃ a c : ℝ, M = symmetricMatrix a 1 c ∧ symmetricMatrix a 1 c ∈ psdCone

def strict_feasibility : Prop :=
  symmetricMatrix 2 1 2 ∈ feasible ∧
  ∀ u v : ℝ, (u, v) ≠ (0, 0) → 0 < quadraticForm (symmetricMatrix 2 1 2) u v

def relative_strict_feasibility : Prop :=
  symmetricMatrix 2 1 2 ∈ VariationalNotes.ConvexGeometry.Specs.relativeInterior psdCone ∧
  constraintMap (symmetricMatrix 2 1 2) = 1

def feasible_first_pos : Prop := ∀ M ∈ feasible, 0 < M 0 0

def feasible_lifts : Prop := ∀ a : ℝ, 0 < a → symmetricMatrix a 1 (1 / a) ∈ feasible

def primal_value_zero : Prop := primalValue = 0

def primal_unattained : Prop := ¬ ∃ M ∈ feasible, (M 0 0 : EReal) = primalValue

/-- The constraint adjoint and objective are computed under tr(SM), on the
symmetric ambient space of the conic program. -/
def trace_adjoint_identity : Prop := ∀ (y : ℝ) (M : Matrix2), M.IsSymm →
  tracePair (traceAdjoint y) M = y * constraintMap M

def cost_identity : Prop := ∀ M : Matrix2, tracePair cost M = M 0 0

def lagrangian_identity : Prop := ∀ (y : ℝ) (M : Matrix2), M.IsSymm →
  M 0 0 + y * (1 - constraintMap M) = y + tracePair (slack y) M

/-- The concrete conic dual is max y with [[1,-y/2],[-y/2,0]] PSD. -/
def dual_derivation : Prop := ∀ y : ℝ,
  slack y = symmetricMatrix 1 (-y / 2) 0 ∧
  (y ∈ dualFeasible ↔ symmetricMatrix 1 (-y / 2) 0 ∈ psdCone)

def dual_feasible_iff : Prop := ∀ y : ℝ, y ∈ dualFeasible ↔ y = 0

def dual_zero_feasible : Prop := (0 : ℝ) ∈ dualFeasible

def dual_value_zero : Prop := dualValue = 0

def dual_attained : Prop := (0 : ℝ) ∈ dualFeasible ∧
  (∀ y ∈ dualFeasible, y ≤ 0) ∧ ((0 : ℝ) : EReal) = dualValue

def values_equal : Prop := primalValue = dualValue

end VariationalNotes.Ch05.SemidefiniteNonattainment.Specs
