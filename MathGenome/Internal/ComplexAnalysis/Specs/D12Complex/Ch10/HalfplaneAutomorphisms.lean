import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch06.DiskAutomorphisms
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.ElementaryMaps
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.Mobius

/-! Automorphisms in paper.tex:2344–2351. Equality of plane maps is restricted
 to their actual open domains; no behavior of total representatives outside
 those domains is prescribed. -/
noncomputable section
namespace D12Complex.HalfplaneAutomorphisms

abbrev RealCoefficients := Matrix (Fin 2) (Fin 2) ℝ

def realFraction (M : RealCoefficients) (z : ℂ) : ℂ :=
  ((M 0 0 : ℂ) * z + M 0 1) / ((M 1 0 : ℂ) * z + M 1 1)

end D12Complex.HalfplaneAutomorphisms

namespace Specs.D12Complex.Ch10.HalfplaneAutomorphisms
open _root_.D12Complex _root_.D12Complex.HalfplaneAutomorphisms Set

def realFraction_type := RealCoefficients → ℂ → ℂ
def realFraction_value : realFraction_type := fun M z =>
  ((M 0 0 : ℂ) * z + M 0 1) / ((M 1 0 : ℂ) * z + M 1 1)

def disk_classification_type : Prop :=
  ∀ f : ℂ → ℂ, IsBiholomorphism unitDisk unitDisk f ↔
    ∃ (a : ℂ) (θ : ℝ), ‖a‖ < 1 ∧
      EqOn f (fun z => Complex.exp ((θ : ℂ) * Complex.I) * DiskPhi a z) unitDisk

def imaginary_part_type : Prop :=
  ∀ (M : RealCoefficients) (z : ℂ),
    (realFraction M z).im = M.det * z.im / ‖(M 1 0 : ℂ) * z + M 1 1‖ ^ 2

def denominator_ne_zero_type : Prop :=
  ∀ M : RealCoefficients, M.det ≠ 0 → ∀ z ∈ upperHalfPlane,
    (M 1 0 : ℂ) * z + M 1 1 ≠ 0

def positive_biholomorphicPair_type : Prop :=
  ∀ M : RealCoefficients, 0 < M.det →
    BiholomorphicPair upperHalfPlane upperHalfPlane (realFraction M)
      (realFraction !![M 1 1, -M 0 1; -M 1 0, M 0 0])

def classification_type : Prop :=
  ∀ f : ℂ → ℂ, IsBiholomorphism upperHalfPlane upperHalfPlane f ↔
    ∃ M : RealCoefficients, 0 < M.det ∧ EqOn f (realFraction M) upperHalfPlane

/-- This includes invertible matrices of either determinant sign. In particular
it gives precisely the ambiguity for the positive determinant representatives. -/
def real_scalar_iff_type : Prop :=
  ∀ M N : RealCoefficients, M.det ≠ 0 → N.det ≠ 0 →
    (EqOn (realFraction M) (realFraction N) upperHalfPlane ↔
      ∃ r : ℝ, r ≠ 0 ∧ M = r • N)

end Specs.D12Complex.Ch10.HalfplaneAutomorphisms
