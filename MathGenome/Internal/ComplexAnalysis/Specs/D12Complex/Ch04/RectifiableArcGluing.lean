import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.ArclengthFactorization
import Mathlib.Topology.LocallyFinite

/-! Independent statements for the finite-length part of D12.04.08,
paper.tex:1196–1237. Compact rectifiable arcs are represented by the canonical
continuous interval paths. We allow every rectifiable path, a stronger result
which includes arcs without imposing smoothness, separation or disjointness.
Local finiteness is required only at points of the open set Ω.
-/

noncomputable section
open Set Metric

namespace Specs.D12Complex.Ch04.RectifiableArcGluing
open _root_.D12Complex _root_.D12Complex.Stieltjes

def HasLinearCoverBound_type := Set ℂ → Prop
def HasLinearCoverBound_value : HasLinearCoverBound_type :=
  fun E => ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
    ∃ (n : ℕ) (c : Fin n → ℂ),
      (n : ℝ) * h ≤ C ∧ E ⊆ ⋃ j, closedBall (c j) h

def LocallyFiniteTracesOn_type.{u} := {ι : Type u} → Set ℂ → (ι → ComplexPath) → Prop
def LocallyFiniteTracesOn_value.{u} : LocallyFiniteTracesOn_type.{u} :=
  fun {_ι} Ω γ => ∀ z ∈ Ω, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
    {i | ((γ i).trace ∩ U).Nonempty}.Finite

def lipschitz_interval_cover_type : Prop :=
  ∀ (L h : ℝ), 0 ≤ L → 0 < h → ∀ σ : ℝ → ℂ,
    LipschitzOnWith 1 σ (Icc 0 L) →
    ∃ (n : ℕ) (c : Fin n → ℂ),
      (n : ℝ) * h ≤ L + h ∧ σ '' Icc 0 L ⊆ ⋃ j, closedBall (c j) h

def rectifiable_trace_cover_type : Prop :=
  ∀ γ : ComplexPath, Rectifiable γ → HasLinearCoverBound_value γ.trace

def finite_rectifiable_traces_cover_type : Prop :=
  ∀ (n : ℕ) (γ : Fin n → ComplexPath), (∀ i, Rectifiable (γ i)) →
    HasLinearCoverBound_value (⋃ i, (γ i).trace)

/-- The analytic core: continuity removes a compact exceptional
set with the stated elementary covering bound. No differentiability or
analyticity certificate for f on the exceptional set is assumed. -/
def linear_cover_gluing_type : Prop :=
  ∀ (Ω E : Set ℂ) (f : ℂ → ℂ), IsOpen Ω → IsCompact E →
    HasLinearCoverBound_value E → ContinuousOn f Ω →
    HolomorphicOn (Ω \ E) f → HolomorphicOn Ω f

def finite_rectifiable_arc_gluing_type : Prop :=
  ∀ (n : ℕ) (γ : Fin n → ComplexPath) (Ω : Set ℂ) (f : ℂ → ℂ),
    (∀ i, Rectifiable (γ i)) → IsOpen Ω → ContinuousOn f Ω →
    HolomorphicOn (Ω \ ⋃ i, (γ i).trace) f → HolomorphicOn Ω f

/-- Full original obligation. Neither Ω nor the family need be nonempty or
connected. Every path already has compact trace by its actual definition. -/
def rectifiable_arc_gluing_type.{u} : Prop :=
  ∀ (ι : Type u) (γ : ι → ComplexPath) (Ω : Set ℂ) (f : ℂ → ℂ),
    (∀ i, Rectifiable (γ i)) → (∀ i, (γ i).trace ⊆ Ω) →
    IsOpen Ω → LocallyFiniteTracesOn_value Ω γ → ContinuousOn f Ω →
    HolomorphicOn (Ω \ ⋃ i, (γ i).trace) f → HolomorphicOn Ω f

def finite_gluing_of_linear_cover_gluing_type : Prop :=
  linear_cover_gluing_type → finite_rectifiable_arc_gluing_type

def locally_finite_gluing_of_finite_gluing_type.{u} : Prop :=
  finite_rectifiable_arc_gluing_type → rectifiable_arc_gluing_type.{u}

end Specs.D12Complex.Ch04.RectifiableArcGluing
