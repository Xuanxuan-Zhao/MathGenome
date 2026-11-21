import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.GeometricBarriers
import Mathlib.Data.Finset.Basic

/-! Sector/cone part of paper.tex:2660–2669. No boundary geometry is an
arrangement assumption. The empty family and disconnected unions are included. -/
noncomputable section
open Set Metric

namespace Specs.D12Complex.Ch14.DiskUnionBoundarySectors
open _root_.D12Complex

def diskUnion (s : Finset ℂ) (r : ℂ → ℝ) : Set ℂ :=
  ⋃ c ∈ s, ball c (r c)

def GeneralPosition (s : Finset ℂ) (r : ℂ → ℝ) : Prop :=
  (∀ c ∈ s, 0 < r c) ∧
  (∀ c ∈ s, ∀ d ∈ s, c ≠ d →
    dist c d ≠ r c + r d ∧ dist c d ≠ |r c - r d|) ∧
  (∀ c ∈ s, ∀ d ∈ s, ∀ e ∈ s, c ≠ d → c ≠ e → d ≠ e →
    ¬ ∃ z : ℂ, dist z c = r c ∧ dist z d = r d ∧ dist z e = r e)

def SectorChart (D : Set ℂ) (ξ : ℂ) (θ : ℝ) : Prop :=
  ∃ (U V : Set ℂ) (f g : ℂ → ℂ), ξ ∈ U ∧
    BiholomorphicPair U V f g ∧ f ξ = 0 ∧ deriv f ξ ≠ 0 ∧
    ∀ z ∈ U, z ∈ D ↔
      ∃ ρ : ℝ, 0 < ρ ∧ ∃ t : ℝ, 0 < t ∧ t < θ ∧
        f z = (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)

def BoundarySectors (D : Set ℂ) : Prop :=
  ∃ F : Set ℂ, F.Finite ∧ F ⊆ frontier D ∧
    (∀ ξ ∈ frontier D \ F, SectorChart D ξ Real.pi) ∧
    (∀ ξ ∈ F, ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧ SectorChart D ξ θ)

end Specs.D12Complex.Ch14.DiskUnionBoundarySectors

namespace Specs.D12Complex.Ch14.DiskUnionBoundarySectors
open _root_.D12Complex

def diskUnion_type := Finset ℂ → (ℂ → ℝ) → Set ℂ
def diskUnion_value : diskUnion_type := fun s r => ⋃ c ∈ s, ball c (r c)
def GeneralPosition_type := Finset ℂ → (ℂ → ℝ) → Prop
def GeneralPosition_value : GeneralPosition_type := fun s r =>
  (∀ c ∈ s, 0 < r c) ∧
  (∀ c ∈ s, ∀ d ∈ s, c ≠ d →
    dist c d ≠ r c + r d ∧ dist c d ≠ |r c - r d|) ∧
  (∀ c ∈ s, ∀ d ∈ s, ∀ e ∈ s, c ≠ d → c ≠ e → d ≠ e →
    ¬ ∃ z : ℂ, dist z c = r c ∧ dist z d = r d ∧ dist z e = r e)
def SectorChart_type := Set ℂ → ℂ → ℝ → Prop
def SectorChart_value : SectorChart_type := fun D ξ θ =>
  ∃ (U V : Set ℂ) (f g : ℂ → ℂ), ξ ∈ U ∧
    BiholomorphicPair U V f g ∧ f ξ = 0 ∧ deriv f ξ ≠ 0 ∧
    ∀ z ∈ U, z ∈ D ↔
      ∃ ρ : ℝ, 0 < ρ ∧ ∃ t : ℝ, 0 < t ∧ t < θ ∧
        f z = (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I)
def BoundarySectors_type := Set ℂ → Prop
def BoundarySectors_value : BoundarySectors_type := fun D =>
  ∃ F : Set ℂ, F.Finite ∧ F ⊆ frontier D ∧
    (∀ ξ ∈ frontier D \ F, SectorChart D ξ Real.pi) ∧
    (∀ ξ ∈ F, ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧ SectorChart D ξ θ)

/-- Complete obligation, including the actual canonical exterior cone. -/
def disk_union_boundary_sectors_type : Prop :=
  ∀ (s : Finset ℂ) (r : ℂ → ℝ), GeneralPosition s r →
    BoundarySectors (diskUnion s r) ∧
    ∀ ξ ∈ frontier (diskUnion s r), LocalExteriorCone (diskUnion s r) ξ

def disk_union_exterior_cones_type : Prop :=
  ∀ (s : Finset ℂ) (r : ℂ → ℝ), GeneralPosition s r →
    ∀ ξ ∈ frontier (diskUnion s r), LocalExteriorCone (diskUnion s r) ξ

/-- At a frontier point the union is exactly one or two active disks locally. -/
def local_boundary_disk_model_type : Prop :=
  ∀ (s : Finset ℂ) (r : ℂ → ℝ), GeneralPosition s r →
    ∀ ξ ∈ frontier (diskUnion s r), ∃ c ∈ s, dist ξ c = r c ∧
      ∃ ε : ℝ, 0 < ε ∧
      ((∀ z ∈ ball ξ ε, z ∈ diskUnion s r ↔ z ∈ ball c (r c)) ∨
        ∃ d ∈ s, c ≠ d ∧ dist ξ d = r d ∧
          ∀ z ∈ ball ξ ε,
            z ∈ diskUnion s r ↔ z ∈ ball c (r c) ∪ ball d (r d))

end Specs.D12Complex.Ch14.DiskUnionBoundarySectors
