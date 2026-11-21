import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.Polarization

/-! Independent scope of paper.tex:2038–2143. In particular, the gradient
uses the Euclidean norm and every positive level is quantified, including
levels whose level set has positive measure. No polarization hypothesis is
part of any target below. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal
namespace P102.Sobolev
open P102.U4 Polarization
namespace Rearrangement

/-- Positive superlevel sets are centered balls up to null sets. Radius zero
represents the empty ball. Each radius is finite. -/
def HasCenteredSuperlevels {d : ℕ} (g : Space d → ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → ∃ r : ℝ, 0 ≤ r ∧
    {x | s < g x} =ᵐ[volume] Metric.ball (0 : Space d) r

/-- A radial, nonincreasing representative away from the origin. The profile
is finite at every positive radius; its value at zero is irrelevant to the
Lp class and is not constrained (Sobolev functions may be unbounded there). -/
def IsRadiallyNonincreasing {d : ℕ} (g : Space d → ℝ) : Prop :=
  ∃ φ : ℝ → ℝ, AntitoneOn φ (Ioi 0) ∧ (∀ r > 0, 0 ≤ φ r) ∧
    g =ᵐ[volume] (fun x => φ ‖x‖)

/-- The nonnegative symmetric decreasing rearrangement, specified intrinsically
without assuming either existence or Sobolev membership. -/
def IsRearrangement {d : ℕ} (f g : Space d → ℝ) : Prop :=
  (∀ᵐ x ∂volume, 0 ≤ g x) ∧ HasCenteredSuperlevels g ∧
    ∀ s : ℝ, 0 < s → volume {x | s < g x} = volume {x | s < f x}

end Rearrangement
namespace PolyaSzegoExpected
open Rearrangement

/-- The complete bounded-support Pólya–Szegő existence and energy assertion. -/
def Existence : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ (R : ℝ), 0 < R → ∀ f : Polarization.WholeSobolev d p,
      SupportedNonnegative R f → ∃ g : Polarization.WholeSobolev d p,
        SupportedNonnegative R g ∧
        IsRearrangement (sobolevUnderlying f) (sobolevUnderlying g) ∧
        IsRadiallyNonincreasing (sobolevUnderlying g) ∧
        eLpNorm (gradient g) p volume ≤ eLpNorm (gradient f) p volume

/-- The radial nonincreasing characterization on the class in the source. -/
def RadialCharacterization : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ (R : ℝ), 0 < R → ∀ g : Polarization.WholeSobolev d p,
      SupportedNonnegative R g →
        (HasCenteredSuperlevels (sobolevUnderlying g) ↔
          IsRadiallyNonincreasing (sobolevUnderlying g))

/-- Centered superlevels of the prescribed measures determine the nonnegative
function up to null sets. No continuity of the distribution function is assumed. -/
def Uniqueness : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ f g h : Space d → ℝ,
    IsRearrangement f g → IsRearrangement f h → g =ᵐ[volume] h

end PolyaSzegoExpected
end P102.Sobolev
