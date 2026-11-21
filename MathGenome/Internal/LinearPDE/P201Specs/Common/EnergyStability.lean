import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
Independent interface for paper.tex, §C03, through Energy control of differences.
The solution type is the stated solution class; observation maps are supplied by
that problem. An initial observation includes every required initial derivative.
It may evaluate a classical solution or its continuous time representative. A
boundary observation may be classical restriction or the appropriate Sobolev
trace. Their domains must already be chosen so these observations are defined.
No existence, trace, regularity, or PDE theorem is assumed by these definitions.
-/
namespace P201Specs.Common.EnergyStability

universe u v w

/-- Prescribing a Cauchy datum through the chosen initial observation. -/
def CauchyDataType :=
  {S : Type u} → {I : Type v} → (S → I) → S → I → Prop

def CauchyDataValue : CauchyDataType.{u,v} :=
  fun observation solution datum => observation solution = datum

/-- Prescribing a boundary datum through the chosen boundary observation. -/
def BoundaryDataType :=
  {S : Type u} → {B : Type v} → (S → B) → S → B → Prop

def BoundaryDataValue : BoundaryDataType.{u,v} :=
  fun observation solution datum => observation solution = datum

/-- Both initial (including derivatives) and spatial boundary observations. -/
def InitialBoundaryDataType :=
  {S : Type u} → {I : Type v} → {B : Type w} →
    (S → I) → (S → B) → S → I × B → Prop

def InitialBoundaryDataValue : InitialBoundaryDataType.{u,v,w} :=
  fun initial boundary solution datum =>
    initial solution = datum.1 ∧ boundary solution = datum.2

/-- The data type can itself be a subtype of compatible/admissible data.
The solution type fixes the class in which uniqueness is required. -/
def HadamardWellPosedType :=
  {D : Type u} → {S : Type v} → [TopologicalSpace D] → [TopologicalSpace S] →
    (D → S → Prop) → Prop

/-- Existence, uniqueness in the chosen class, and a continuous solution map
for exactly the specified data and solution topologies. -/
def HadamardWellPosedValue : HadamardWellPosedType.{u,v} :=
  fun {D} {S} _ _ solves =>
    (∀ d, ∃ s, solves d s) ∧
    (∀ d s₁ s₂, solves d s₁ → solves d s₂ → s₁ = s₂) ∧
    ∃ solutionMap : D → S, Continuous solutionMap ∧ ∀ d, solves d (solutionMap d)

/-- An equivalent formulation identifies the complete graph of the unique
continuous solution map, so continuity cannot refer to an unrelated map. -/
def HadamardGraphStatement : Prop :=
  ∀ {D : Type u} {S : Type v} [TopologicalSpace D] [TopologicalSpace S]
    (solves : D → S → Prop),
    HadamardWellPosedValue solves ↔
      ∃ solutionMap : D → S, Continuous solutionMap ∧
        ∀ d s, solves d s ↔ s = solutionMap d

/-- Time may be any index type, in particular any real time interval with its
initial time as a distinguished point. No time regularity is needed here. -/
def EnergyVanishesStatement : Prop :=
  ∀ {T : Type u} (t₀ : T) (E : T → ℝ) (C : ℝ),
    (∀ t, 0 ≤ E t) → (∀ t, E t ≤ C * E t₀) → E t₀ = 0 → ∀ t, E t = 0

/-- The full solution norm is controlled with the explicit real constant K.
Even its sign is unnecessary for this zero-energy implication. The hypotheses
must concern the whole state, not merely a nonseparating energy seminorm. -/
def EnergyUniquenessStatement : Prop :=
  ∀ {T : Type u} {X : Type v} [NormedAddCommGroup X]
    (t₀ : T) (u v : T → X) (E : T → ℝ) (C K : ℝ),
    (∀ t, 0 ≤ E t) →
    (∀ t, ‖u t - v t‖ ^ 2 ≤ K * E t) →
    (∀ t, E t ≤ C * E t₀) → E t₀ = 0 → u = v

/-- Identical data give zero initial difference energy. Quantification over the
relation retains uniqueness only in the chosen solution class. -/
def SameDataUniquenessStatement : Prop :=
  ∀ {T : Type u} {X : Type v} {D : Type w} [NormedAddCommGroup X]
    (solves : D → (T → X) → Prop) (t₀ : T)
    (energy : (T → X) → (T → X) → T → ℝ) (C K : ℝ),
    (∀ d u v, solves d u → solves d v →
      (∀ t, 0 ≤ energy u v t) ∧
      (∀ t, ‖u t - v t‖ ^ 2 ≤ K * energy u v t) ∧
      (∀ t, energy u v t ≤ C * energy u v t₀) ∧ energy u v t₀ = 0) →
    ∀ d u v, solves d u → solves d v → u = v

/-- Scalar square-root estimate, with the full data and state norms.
The statement also covers C < 0 when the estimate's premises can hold. -/
def NormStabilityStatement : Prop :=
  ∀ {D : Type u} {X : Type v} [NormedAddCommGroup D] [NormedAddCommGroup X]
    (d e : D) (x y : X) (C : ℝ),
    ‖x - y‖ ^ 2 ≤ C * ‖d - e‖ ^ 2 →
    ‖x - y‖ ≤ Real.sqrt C * ‖d - e‖

/-- The exact-energy version of the source's quantitative stability statement. -/
def EnergyStabilityStatement : Prop :=
  ∀ {T : Type u} {D : Type v} {X : Type w}
    [NormedAddCommGroup D] [NormedAddCommGroup X]
    (t₀ : T) (d e : D) (u v : T → X) (E : T → ℝ) (C : ℝ),
    E t₀ = ‖d - e‖ ^ 2 →
    (∀ t, E t = ‖u t - v t‖ ^ 2) →
    (∀ t, E t ≤ C * E t₀) →
    ∀ t, ‖u t - v t‖ ≤ Real.sqrt C * ‖d - e‖

/-- If the solution norm itself satisfies the difference estimate, the chosen
solution map is Lipschitz, hence continuous in the norm topologies. -/
def StabilityContinuityStatement : Prop :=
  ∀ {D : Type u} {X : Type v} [NormedAddCommGroup D] [NormedAddCommGroup X]
    (solutionMap : D → X) (C : ℝ),
    (∀ d e, ‖solutionMap d - solutionMap e‖ ^ 2 ≤ C * ‖d - e‖ ^ 2) →
    LipschitzWith ⟨Real.sqrt C, Real.sqrt_nonneg C⟩ solutionMap ∧
      Continuous solutionMap

end P201Specs.Common.EnergyStability
