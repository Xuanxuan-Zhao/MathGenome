import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.Residue
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Sphere

/-! The differential, rather than just its scalar coefficient, is pulled back
by the infinity coordinate z = 1/w (paper.tex:1992–2001, D12.08.03).
No meromorphic extension at infinity is required: essential singularities are
included. Values of the total functions at the puncture are immaterial. -/
noncomputable section
open scoped Topology ENNReal

namespace D12Complex.InfinityResidue

/-- Coefficient of f(z) dz in the coordinate w = 1/z. -/
def pullbackCoefficient (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  -reciprocalPullback f w * w ^ (-2 : ℤ)

/-- Residue at infinity, with the Jacobian minus sign. -/
def residueAtInfinity (f : ℂ → ℂ) : ℂ :=
  Residue.residue (pullbackCoefficient f) 0

/-- The same construction for a complex differential given as a field of
complex-linear functionals. Its coefficient in the finite chart is ω(z)(1). -/
def differentialResidueAtInfinity (ω : ℂ → ℂ →L[ℂ] ℂ) : ℂ :=
  residueAtInfinity (fun z => ω z 1)

/-- Under inversion with its differential, exponent n becomes -n-2. -/
def transformedLaurentCoefficients (c : ℤ → ℂ) (n : ℤ) : ℂ := -c (-n - 2)

end D12Complex.InfinityResidue

namespace Specs.D12Complex.Ch08.InfinityResidue
open _root_.D12Complex _root_.D12Complex.Laurent _root_.D12Complex.InfinityResidue

def pullbackCoefficient_type := (ℂ → ℂ) → ℂ → ℂ
def pullbackCoefficient_value : pullbackCoefficient_type :=
  fun f w => -reciprocalPullback f w * w ^ (-2 : ℤ)

def residueAtInfinity_type := (ℂ → ℂ) → ℂ
def residueAtInfinity_value : residueAtInfinity_type :=
  fun f => Residue.residue (pullbackCoefficient f) 0

def differentialResidueAtInfinity_type := (ℂ → ℂ →L[ℂ] ℂ) → ℂ
def differentialResidueAtInfinity_value : differentialResidueAtInfinity_type :=
  fun ω => residueAtInfinity (fun z => ω z 1)

def transformedLaurentCoefficients_type := (ℤ → ℂ) → ℤ → ℂ
def transformedLaurentCoefficients_value : transformedLaurentCoefficients_type :=
  fun c n => -c (-n - 2)

/-- This identifies the multiplier with the actual derivative of inversion. -/
def pullbackCoefficient_eq_deriv_type : Prop :=
  ∀ (f : ℂ → ℂ) (w : ℂ), w ≠ 0 →
    pullbackCoefficient f w = f w⁻¹ * deriv (fun z : ℂ => z⁻¹) w

def differentialResidueAtInfinity_differential_type : Prop :=
  ∀ f : ℂ → ℂ,
    differentialResidueAtInfinity (Residue.differential f) = residueAtInfinity f

/-- Holomorphy is only required on the entire exterior, with no boundary
extension. Inversion gives a punctured disk for the transformed differential. -/
def holomorphicOn_pullbackCoefficient_type : Prop :=
  ∀ (f : ℂ → ℂ) (R : ℝ), 0 < R → HolomorphicOn (exterior R) f →
    HolomorphicOn (annulus 0 0 (ENNReal.ofReal R⁻¹)) (pullbackCoefficient f)

/-- Actual convergent Laurent expansions transform with the differential's
Jacobian. The two one-sided series are absolutely summable in the interior. -/
def hasLaurentSeriesOn_pullbackCoefficient_type : Prop :=
  ∀ (f : ℂ → ℂ) (R : ℝ) (c : ℤ → ℂ), 0 < R →
    HasLaurentSeriesOn f 0 R ⊤ c →
    HasLaurentSeriesOn (pullbackCoefficient f) 0 0 (ENNReal.ofReal R⁻¹)
      (transformedLaurentCoefficients c)

/-- The coefficient assertion, also for an exterior with inner radius zero.
Ordinary convergence is enough; no coefficient identity is assumed. -/
def residueAtInfinity_eq_neg_laurentCoefficient_type : Prop :=
  ∀ (f : ℂ → ℂ) (R : ℝ) (c : ℤ → ℂ), 0 ≤ R →
    ConvergentLaurentSeriesOn f 0 R ⊤ c → residueAtInfinity f = -c (-1)

/-- Every function holomorphic on some entire exterior has the expansion
appearing in the coefficient assertion, including at essential singularities. -/
def exists_exterior_laurent_with_residue_type : Prop :=
  ∀ f : ℂ → ℂ, IsolatedSingularityAtInfinity f →
    ∃ (R : ℝ) (c : ℤ → ℂ), 0 < R ∧
      HasLaurentSeriesOn f 0 R ⊤ c ∧ residueAtInfinity f = -c (-1)

end Specs.D12Complex.Ch08.InfinityResidue
