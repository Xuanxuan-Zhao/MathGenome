import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.VariationSpaces
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Topology.Order.LocalExtr

/-!
Independent statements for paper.tex:3374–3414. Fields on an open domain are
represented by ambient functions with no conditions outside the domain. The
Fréchet derivative at an interior point is therefore intrinsic. Gradient
matrices are represented by linear operators between the Euclidean spaces.
-/
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff

namespace VariationalNotes.Classical.LegendreHadamardData

abbrev Gradient (d m : ℕ) := State d →L[ℝ] State m
abbrev StateGradient (d m : ℕ) := State m × Gradient d m

/-- The integrand may have only a local open domain. -/
structure FieldLagrangian (d m : ℕ) where
  domain : Set (State d × StateGradient d m)
  isOpen_domain : IsOpen domain
  value : (State d × StateGradient d m) → ℝ

def graphPoint {d m : ℕ} (u : State d → State m) (x : State d) :
    State d × StateGradient d m := (x, u x, fderiv ℝ u x)

def graphAdmissible {d m : ℕ} (L : FieldLagrangian d m)
    (Ω : Set (State d)) (u : State d → State m) : Prop :=
  ∀ x ∈ Ω, graphPoint u x ∈ L.domain

/-- Only a neighborhood of the graph is required to have C² regularity. -/
def regularNearGraph {d m : ℕ} (L : FieldLagrangian d m)
    (Ω : Set (State d)) (u : State d → State m) : Prop :=
  ∃ U : Set (State d × StateGradient d m), IsOpen U ∧
    (∀ x ∈ Ω, graphPoint u x ∈ U) ∧ U ⊆ L.domain ∧ ContDiffOn ℝ 2 L.value U

/-- Finite energy means Lebesgue integrability, not merely a totalized integral. -/
def finiteEnergy {d m : ℕ} (L : FieldLagrangian d m)
    (Ω : Set (State d)) (u : State d → State m) : Prop :=
  IntegrableOn (fun x => L.value (graphPoint u x)) Ω

def energy {d m : ℕ} (L : FieldLagrangian d m)
    (Ω : Set (State d)) (u : State d → State m) : ℝ :=
  ∫ x in Ω, L.value (graphPoint u x)

def smoothTest {d m : ℕ} (Ω : Set (State d)) (η : State d → State m) : Prop :=
  ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ Ω

/-- Weak refers to a C¹ neighborhood, restricted to smooth compactly supported
finite-energy perturbations whose graphs are admissible. No boundedness of Ω is imposed. -/
def weakLocalMinimum {d m : ℕ} (L : FieldLagrangian d m)
    (Ω : Set (State d)) (u : State d → State m) : Prop :=
  graphAdmissible L Ω u ∧ ∃ ε > 0, ∀ η : State d → State m,
    smoothTest Ω η → graphAdmissible L Ω (u + η) → finiteEnergy L Ω (u + η) →
    (∀ x ∈ Ω, ‖(η x, fderiv ℝ η x)‖ < ε) →
    energy L Ω u ≤ energy L Ω (u + η)

/-- The Hessian in the state and gradient variables, with x held fixed. -/
def stateGradientHessian {d m : ℕ} (L : FieldLagrangian d m)
    (u : State d → State m) (x : State d) :
    StateGradient d m →L[ℝ] StateGradient d m →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (fun zF : StateGradient d m => L.value (x, zF)))
    (u x, fderiv ℝ u x)

/-- L_FF is the restriction of the state–gradient Hessian to gradient directions. -/
def gradientHessian {d m : ℕ} (L : FieldLagrangian d m)
    (u : State d → State m) (x : State d) (R S : Gradient d m) : ℝ :=
  stateGradientHessian L u x (0, R) (0, S)

/-- e ⊗ b, including the zero directions. Its application is v ↦ ⟪b,v⟫e. -/
def rankOne {d m : ℕ} (e : State m) (b : State d) : Gradient d m :=
  InnerProductSpace.rankOne ℝ e b

/-- Ordinary 2×2 matrices; this is the same rank-one tensor in coordinates. -/
def outerMatrix (e b : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => e i * b j

end VariationalNotes.Classical.LegendreHadamardData

namespace VariationalNotes.Classical.LegendreHadamardSpec
open LegendreHadamardData

/-- Full necessary condition, without bounded-domain or global-C² hypotheses. -/
def necessityType : Prop :=
  ∀ (d m : ℕ) (Ω : Set (State d)), IsOpen Ω →
  ∀ (L : FieldLagrangian d m) (u : State d → State m),
    ContDiffOn ℝ 1 u Ω → LegendreHadamardData.regularNearGraph L Ω u → finiteEnergy L Ω u →
    LegendreHadamardData.weakLocalMinimum L Ω u →
    ∀ x ∈ Ω, ∀ (e : State m) (b : State d),
      0 ≤ gradientHessian L u x (rankOne e b) (rankOne e b)

/-- The finite-energy C¹ minimum gives a scalar minimum along each test. -/
def directionMinimumType : Prop :=
  ∀ {d m : ℕ} {Ω : Set (State d)}, IsOpen Ω →
  ∀ (L : FieldLagrangian d m) {u η : State d → State m},
    ContDiffOn ℝ 1 u Ω → smoothTest Ω η →
    LegendreHadamardData.regularNearGraph L Ω u → finiteEnergy L Ω u →
    LegendreHadamardData.weakLocalMinimum L Ω u →
    IsLocalMin (fun s : ℝ => energy L Ω (u + s • η)) 0

/-- All parts of the substantive determinant example in one statement. -/
def determinantExampleType : Prop :=
  (∃ Q : QuadraticForm ℝ (Matrix (Fin 2) (Fin 2) ℝ),
    ∀ F, Q F = Matrix.det F) ∧
  (∀ e b : Fin 2 → ℝ, Matrix.det (outerMatrix e b) = 0) ∧
  (∀ F : Matrix (Fin 2) (Fin 2) ℝ, F.rank ≤ 1 → Matrix.det F = 0) ∧
  (∃ F : Matrix (Fin 2) (Fin 2) ℝ, 0 < Matrix.det F) ∧
  (∃ F : Matrix (Fin 2) (Fin 2) ℝ, Matrix.det F < 0)

end VariationalNotes.Classical.LegendreHadamardSpec
