import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.ElementaryMaps
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.Joukowski
import Mathlib.Analysis.Convex.Segment

/-! Independent full statements for paper.tex:2378–2383 (D12.10.06).
`d ≠ 0` gives an arbitrary oriented line in the half-plane statement and
an arbitrary ray direction in the slit statement. The latter removes t = 0 too.
Sectors allow arbitrary vertices and lifted initial angles. A segment uses
Mathlib's closed real segment, with distinct endpoints. The exterior is a
plane domain: infinity is not adjoined. All inverses are specified explicitly.
-/
noncomputable section
namespace Specs.D12Complex.Ch10.ClassicalDomains
open _root_.D12Complex

def disk_biholomorphicPair_type : Prop :=
  ∀ (a : ℂ) (r : ℝ), 0 < r →
    BiholomorphicPair (Metric.ball a r) unitDisk
      (fun z => (z - a) / (r : ℂ)) (fun w => a + (r : ℂ) * w)

def halfPlane_biholomorphicPair_type : Prop :=
  ∀ (a d : ℂ), d ≠ 0 →
    BiholomorphicPair {z | 0 < ((z - a) / d).im} unitDisk
      (fun z => cayley ((z - a) / d)) (fun w => a + d * cayleyInverse w)

def strip_biholomorphicPair_type : Prop :=
  ∀ (a θ : ℝ), 0 < θ →
    BiholomorphicPair (horizontalStrip a θ) unitDisk
      (fun z => cayley (E (((Real.pi / θ : ℝ) : ℂ) * (z - (a : ℂ) * Complex.I))))
      (fun w => (a : ℂ) * Complex.I + ((θ / Real.pi : ℝ) : ℂ) *
        sectorLog 0 Real.pi (cayleyInverse w))

def sector_biholomorphicPair_type : Prop :=
  ∀ (v : ℂ) (a θ : ℝ), 0 < θ → θ < 2 * Real.pi →
    BiholomorphicPair {z | z - v ∈ sector a θ} unitDisk
      (fun z => cayley (sectorPower a θ (z - v)))
      (fun w => v + sectorPowerInverse a θ (cayleyInverse w))

/-- A logarithm followed by the strip map, on the plane minus one closed ray.
For the slit of direction d we normalize by -d to the principal negative cut. -/
def raySlit_biholomorphicPair_type : Prop :=
  ∀ (v d : ℂ), d ≠ 0 →
    BiholomorphicPair ((fun t : ℝ => v + (t : ℂ) * d) '' Set.Ici 0)ᶜ unitDisk
      (fun z => cayley (E (((Real.pi / (2 * Real.pi) : ℝ) : ℂ) *
        (PrincipalLog ((z - v) / (-d)) - ((-Real.pi : ℝ) : ℂ) * Complex.I))))
      (fun w => v + (-d) * E (((-Real.pi : ℝ) : ℂ) * Complex.I +
        (((2 * Real.pi) / Real.pi : ℝ) : ℂ) *
          sectorLog 0 Real.pi (cayleyInverse w)))

def exterior_segment_biholomorphicPair_type : Prop :=
  ∀ (a : ℂ) (r : ℝ) (p q : ℂ), 0 < r → p ≠ q →
    BiholomorphicPair {z | r < ‖z - a‖} (segment ℝ p q)ᶜ
      (fun z => (p + q) / 2 + ((q - p) / 2) * Joukowski.map ((z - a) / (r : ℂ)))
      (fun w => a + (r : ℂ) * Joukowski.inverse ((w - (p + q) / 2) / ((q - p) / 2)))

end Specs.D12Complex.Ch10.ClassicalDomains
