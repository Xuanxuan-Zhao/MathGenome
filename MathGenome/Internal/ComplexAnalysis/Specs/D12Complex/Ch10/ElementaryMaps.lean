import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.ChosenPowers

/-! Explicit maps in paper.tex:2354–2361. Sector angles are lifted real angles;
all boundary inequalities are strict. The parameter `a` permits arbitrary rotation.
The logarithm is centered at `a + θ/2`, so it also covers θ = 2π without
identifying the two banks of its cut. -/
noncomputable section
namespace D12Complex

def upperHalfPlane : Set ℂ := {z | 0 < z.im}
def unitDisk : Set ℂ := {z | ‖z‖ < 1}
def cayley (z : ℂ) : ℂ := (z - Complex.I) / (z + Complex.I)
def cayleyInverse (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)
def horizontalStrip (a θ : ℝ) : Set ℂ := {z | a < z.im ∧ z.im < a + θ}
def sector (a θ : ℝ) : Set ℂ :=
   {w | ∃ r : ℝ, 0 < r ∧ ∃ t : ℝ, a < t ∧ t < a + θ ∧
      w = (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)}
def sectorArg (a θ : ℝ) (w : ℂ) : ℝ :=
   Complex.arg (w * Complex.exp (-((a + θ / 2 : ℝ) : ℂ) * Complex.I)) + a + θ / 2
def sectorLog (a θ : ℝ) (w : ℂ) : ℂ :=
   Complex.log (w * Complex.exp (-((a + θ / 2 : ℝ) : ℂ) * Complex.I)) +
     ((a + θ / 2 : ℝ) : ℂ) * Complex.I
/-- The selected power after rotating the sector's first boundary ray to angle zero. -/
def sectorPower (a θ : ℝ) (z : ℂ) : ℂ :=
   powerWithLog (fun w => sectorLog a θ w - (a : ℂ) * Complex.I) ((Real.pi / θ : ℝ) : ℂ) z
def sectorPowerInverse (a θ : ℝ) (w : ℂ) : ℂ :=
   E ((a : ℂ) * Complex.I + ((θ / Real.pi : ℝ) : ℂ) * sectorLog 0 Real.pi w)
end D12Complex

namespace Specs.D12Complex.Ch10.ElementaryMaps
open _root_.D12Complex

def upperHalfPlane_type := Set ℂ
def upperHalfPlane_value : upperHalfPlane_type := {z | 0 < z.im}

def unitDisk_type := Set ℂ
def unitDisk_value : unitDisk_type := {z | ‖z‖ < 1}

def cayley_type := ℂ → ℂ
def cayley_value : cayley_type := fun z => (z - Complex.I) / (z + Complex.I)

def cayleyInverse_type := ℂ → ℂ
def cayleyInverse_value : cayleyInverse_type := fun w => Complex.I * (1 + w) / (1 - w)

def horizontalStrip_type := ℝ → ℝ → Set ℂ
def horizontalStrip_value : horizontalStrip_type := fun a θ => {z | a < z.im ∧ z.im < a + θ}

def sector_type := ℝ → ℝ → Set ℂ
def sector_value : sector_type := fun a θ => {w | ∃ r : ℝ, 0 < r ∧ ∃ t : ℝ, a < t ∧ t < a + θ ∧
    w = (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)}

def sectorArg_type := ℝ → ℝ → ℂ → ℝ
def sectorArg_value : sectorArg_type := fun a θ w =>
    Complex.arg (w * Complex.exp (-((a + θ / 2 : ℝ) : ℂ) * Complex.I)) + a + θ / 2

def sectorLog_type := ℝ → ℝ → ℂ → ℂ
def sectorLog_value : sectorLog_type := fun a θ w =>
    Complex.log (w * Complex.exp (-((a + θ / 2 : ℝ) : ℂ) * Complex.I)) +
    ((a + θ / 2 : ℝ) : ℂ) * Complex.I

def sectorPower_type := ℝ → ℝ → ℂ → ℂ
def sectorPower_value : sectorPower_type := fun a θ z => powerWithLog (fun w => sectorLog a θ w - (a : ℂ) * Complex.I)
    ((Real.pi / θ : ℝ) : ℂ) z

def sectorPowerInverse_type := ℝ → ℝ → ℂ → ℂ
def sectorPowerInverse_value : sectorPowerInverse_type := fun a θ w => E ((a : ℂ) * Complex.I + ((θ / Real.pi : ℝ) : ℂ) * sectorLog 0 Real.pi w)

def cayley_biholomorphicPair_type : Prop :=
  BiholomorphicPair upperHalfPlane unitDisk cayley cayleyInverse

def exponential_biholomorphicPair_type : Prop :=
  ∀ (a θ : ℝ), 0 < θ → θ ≤ 2 * Real.pi →
    BiholomorphicPair (horizontalStrip a θ) (sector a θ) E (sectorLog a θ)

def sectorLog_polar_type : Prop :=
  ∀ (a θ : ℝ) (w : ℂ),
    sectorLog a θ w = (Real.log ‖w‖ : ℂ) + (sectorArg a θ w : ℂ) * Complex.I

def sectorArg_bounds_type : Prop :=
  ∀ (a θ : ℝ), 0 < θ → θ ≤ 2 * Real.pi →
    ∀ w ∈ sector a θ, a < sectorArg a θ w ∧ sectorArg a θ w < a + θ

def sector_boundary_excluded_type : Prop :=
  ∀ (a θ : ℝ), 0 < θ → θ ≤ 2 * Real.pi → ∀ r : ℝ, 0 < r →
    (r : ℂ) * Complex.exp ((a : ℂ) * Complex.I) ∉ sector a θ ∧
    (r : ℂ) * Complex.exp (((a + θ : ℝ) : ℂ) * Complex.I) ∉ sector a θ

def sector_zero_pi_type : Prop := sector 0 Real.pi = upperHalfPlane

/-- The normalized map differs from the chosen power of z only by an explicit rotation. -/
def sectorPower_rotation_type : Prop :=
   ∀ (a θ : ℝ) (z : ℂ), sectorPower a θ z =
     E (-((Real.pi / θ : ℝ) : ℂ) * (a : ℂ) * Complex.I) *
       powerWithLog (sectorLog a θ) ((Real.pi / θ : ℝ) : ℂ) z

def sectorPower_biholomorphicPair_type : Prop :=
  ∀ (a θ : ℝ), 0 < θ → θ < 2 * Real.pi →
    BiholomorphicPair (sector a θ) upperHalfPlane
      (sectorPower a θ) (sectorPowerInverse a θ)
end Specs.D12Complex.Ch10.ElementaryMaps
