import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.BarrierSqueeze
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.ChosenPowers
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-! Geometric hypotheses and strict local barriers for paper.tex:2643–2651.
The cone is given by a rotated strict angular inequality, truncated by an
open ball. Its aperture is `2 * (π - β) > 0`; the vertex is not in its
open part. No barrier or regularity is included in a geometric hypothesis. -/
noncomputable section
open Set Metric

namespace D12Complex

/-- A nontrivial open exterior cone with vertex `ξ`, in a neighborhood of `ξ`. -/
def LocalExteriorCone (Ω : Set ℂ) (ξ : ℂ) : Prop :=
  ∃ (q : ℂ) (β r : ℝ), ‖q‖ = 1 ∧ 0 < β ∧ β < Real.pi ∧ 0 < r ∧
    ∀ z ∈ ball ξ r,
      (q * (z - ξ)).re < Real.cos β * ‖q * (z - ξ)‖ → z ∉ Ω

/-- An open disk outside the domain with the vertex on its circle. -/
def ExteriorTangentDisk (Ω : Set ℂ) (ξ c : ℂ) (R : ℝ) : Prop :=
  0 < R ∧ dist ξ c = R ∧ Disjoint Ω (ball c R)

/-- The supporting linear harmonic function of a disk at `ξ`. -/
def diskLinearBarrier (c ξ : ℂ) (R : ℝ) (z : ℂ) : ℝ :=
  R - (starRingEnd ℂ ((ξ - c) / (R : ℂ)) * (z - c)).re

/-- Real part of the selected power in a wedge symmetric about its positive axis.
After rotating the wedge by `ω/2`, this is `r^(π/ω) sin(π t/ω)`. -/
def wedgePowerBarrier (ξ q : ℂ) (ω : ℝ) (z : ℂ) : ℝ :=
  ((q * (z - ξ)) ^ ((Real.pi / ω : ℝ) : ℂ)).re

/-- Use the strictly internally tangent disk, of half the original radius. -/
def tangentLogBarrier (ξ c : ℂ) (R : ℝ) (z : ℂ) : ℝ :=
  Real.log (dist z ((c + ξ) / 2) / (R / 2))

end D12Complex

namespace Specs.D12Complex.Ch14.GeometricBarriers
open _root_.D12Complex
open Specs.D12Complex.Ch14.BarrierSqueeze

def LocalExteriorCone_type := Set ℂ → ℂ → Prop
def LocalExteriorCone_value : LocalExteriorCone_type := fun Ω ξ =>
  ∃ (q : ℂ) (β r : ℝ), ‖q‖ = 1 ∧ 0 < β ∧ β < Real.pi ∧ 0 < r ∧
    ∀ z ∈ ball ξ r,
      (q * (z - ξ)).re < Real.cos β * ‖q * (z - ξ)‖ → z ∉ Ω

def ExteriorTangentDisk_type := Set ℂ → ℂ → ℂ → ℝ → Prop
def ExteriorTangentDisk_value : ExteriorTangentDisk_type := fun Ω ξ c R =>
  0 < R ∧ dist ξ c = R ∧ Disjoint Ω (ball c R)

def diskLinearBarrier_type := ℂ → ℂ → ℝ → ℂ → ℝ
def diskLinearBarrier_value : diskLinearBarrier_type := fun c ξ R z =>
  R - (starRingEnd ℂ ((ξ - c) / (R : ℂ)) * (z - c)).re

def wedgePowerBarrier_type := ℂ → ℂ → ℝ → ℂ → ℝ
def wedgePowerBarrier_value : wedgePowerBarrier_type := fun ξ q ω z =>
  ((q * (z - ξ)) ^ ((Real.pi / ω : ℝ) : ℂ)).re

def tangentLogBarrier_type := ℂ → ℂ → ℝ → ℂ → ℝ
def tangentLogBarrier_value : tangentLogBarrier_type := fun ξ c R z =>
  Real.log (dist z ((c + ξ) / 2) / (R / 2))

def disk_linear_barrier_type : Prop :=
  ∀ (c ξ : ℂ) (R : ℝ), 0 < R → ξ ∈ sphere c R →
    ∀ r : ℝ, 0 < r →
      PositiveLocalBarrier_value (ball c R) ξ r (diskLinearBarrier c ξ R)

def disk_boundary_regular_type : Prop :=
  ∀ (c ξ : ℂ) (R : ℝ), 0 < R → ξ ∈ frontier (ball c R) →
    RegularBoundaryPoint_value (ball c R) ξ

/-- The opening is selected strictly between the allowed angular width and `2π`.
The conclusion supplies the explicit selected power, with strict positivity on
all of the cap closure. -/
def exterior_cone_barrier_type : Prop :=
  ∀ (Ω : Set ℂ) (ξ : ℂ), IsOpen Ω → ξ ∈ frontier Ω →
    LocalExteriorCone Ω ξ →
    ∃ (q : ℂ) (ω r : ℝ), ‖q‖ = 1 ∧ 0 < ω ∧ ω < 2 * Real.pi ∧
      PositiveLocalBarrier_value Ω ξ r (wedgePowerBarrier ξ q ω)

/-- Identification with the chosen logarithm power at every nonzero point
of the allowed wedge. -/
def wedge_power_selected_branch_type : Prop :=
  ∀ (ξ q z : ℂ) (ω : ℝ), q * (z - ξ) ∈ PrincipalSlitPlane →
    wedgePowerBarrier ξ q ω z =
      (principalPower ((Real.pi / ω : ℝ) : ℂ) (q * (z - ξ))).re

/-- The real-part representation is exactly the sine barrier in wedge
coordinates `0 < t < ω`, with the wedge centered on the positive real axis. -/
def wedge_power_polar_type : Prop :=
  ∀ (ξ q z : ℂ) (ω ρ t : ℝ), 0 < ω → ω < 2 * Real.pi →
    0 < ρ → 0 < t → t < ω →
    q * (z - ξ) = (ρ : ℂ) *
      ((Real.cos (t - ω / 2) : ℂ) + (Real.sin (t - ω / 2) : ℂ) * Complex.I) →
    wedgePowerBarrier ξ q ω z =
      ρ ^ (Real.pi / ω) * Real.sin (Real.pi * t / ω)

def exterior_cone_regular_type : Prop :=
  ∀ (Ω : Set ℂ) (ξ : ℂ), IsOpen Ω → ξ ∈ frontier Ω →
    LocalExteriorCone Ω ξ → RegularBoundaryPoint_value Ω ξ

def exterior_tangent_disk_barrier_type : Prop :=
  ∀ (Ω : Set ℂ) (ξ c : ℂ) (R : ℝ), IsOpen Ω → ξ ∈ frontier Ω →
    ExteriorTangentDisk Ω ξ c R →
    ∃ r : ℝ, PositiveLocalBarrier_value Ω ξ r (tangentLogBarrier ξ c R)

def exterior_tangent_disk_regular_type : Prop :=
  ∀ (Ω : Set ℂ) (ξ c : ℂ) (R : ℝ), IsOpen Ω → ξ ∈ frontier Ω →
    ExteriorTangentDisk Ω ξ c R → RegularBoundaryPoint_value Ω ξ

end Specs.D12Complex.Ch14.GeometricBarriers
