import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootTriples
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! LA-D04, source lines 1700–1746; standing hypotheses at 1559–1565.
Root spaces and the Killing-normalized coroot are the shared LA-D02/LA-U07
objects. The exponential below is the finite exponential series. Its arguments
are proved nilpotent in the lift theorem, so this is the ordinary matrix
exponential, whose terms past the nilpotency index vanish. Multiplication of
endomorphisms means composition, with the rightmost factor applied first. -/

universe u
namespace Specs.LieAlgebrasAndRepresentations.RootStrings
open RootDecomposition RootForm

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

noncomputable def reflection_value (H : LieSubalgebra ℂ L)
    (α β : Module.Dual ℂ H) : Module.Dual ℂ H :=
  β - β (coroot_value H α) • α

noncomputable def reflectionLiftLinear_value (e f : L) : Module.End ℂ L := by
  letI := Module.restrictScalars ℚ ℂ L
  letI := IsScalarTower.restrictScalars ℚ ℂ L
  exact IsNilpotent.exp (LieAlgebra.ad ℂ L e) *
    IsNilpotent.exp (-LieAlgebra.ad ℂ L f) * IsNilpotent.exp (LieAlgebra.ad ℂ L e)

def reflection_type := ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L]
  [FiniteDimensional ℂ L] (H : LieSubalgebra ℂ L),
  Module.Dual ℂ H → Module.Dual ℂ H → Module.Dual ℂ H

def reflectionLiftLinear_type := ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L],
  L → L → Module.End ℂ L

def root_string_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ α β : Module.Dual ℂ H, α ∈ rootSet_value H → β ∈ rootSet_value H →
    β ≠ α → β ≠ -α →
      ∃ p q : ℕ, β (coroot_value H α) = (p : ℂ) - (q : ℂ) ∧
        ∀ k : ℤ, β + k • α ∈ rootSet_value H ↔ -(p : ℤ) ≤ k ∧ k ≤ (q : ℤ)

/-- Stronger than successive raising/lowering along a string: any two nonzero
root vectors have nonzero bracket whenever their sum is a root. -/
def root_bracket_ne_zero_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ α β : Module.Dual ℂ H, α ∈ rootSet_value H → β ∈ rootSet_value H →
    α + β ∈ rootSet_value H →
      ∀ e x : L, e ∈ rootSpace_value H α → x ∈ rootSpace_value H β →
        e ≠ 0 → x ≠ 0 → ⁅e, x⁆ ≠ 0

/-- Applied to γ = β + k • α, these are exactly the successive raising and
lowering brackets at every interior step of the interval in root_string. -/
def successive_root_brackets_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ α γ : Module.Dual ℂ H, α ∈ rootSet_value H → γ ∈ rootSet_value H →
    ∀ e f x : L,
      e ∈ rootSpace_value H α → f ∈ rootSpace_value H (-α) → x ∈ rootSpace_value H γ →
      e ≠ 0 → f ≠ 0 → x ≠ 0 →
      (α + γ ∈ rootSet_value H → ⁅e, x⁆ ≠ 0) ∧
      (-α + γ ∈ rootSet_value H → ⁅f, x⁆ ≠ 0)

def coroot_pairing_integral_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ α β : Module.Dual ℂ H, α ∈ rootSet_value H → β ∈ rootSet_value H →
      ∃ z : ℤ, β (coroot_value H α) = (z : ℂ) ∧
        2 * rootForm_value H β α / rootForm_value H α α = (z : ℂ)

def reflection_mem_rootSet_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ α β : Module.Dual ℂ H, α ∈ rootSet_value H → β ∈ rootSet_value H →
      reflection_value H α β ∈ rootSet_value H

/-- The displayed product of three inner exponentials is a Lie automorphism,
with the asserted restriction to H and equality of entire root spaces. This
holds for every choice of normalized raising and lowering vectors. -/
def reflection_lift_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), MaximalTori.IsMaximalToral_value H →
    ∀ α : Module.Dual ℂ H, α ∈ rootSet_value H →
    ∀ e f : L, e ∈ rootSpace_value H α → f ∈ rootSpace_value H (-α) →
      ⁅e, f⁆ = (coroot_value H α : L) →
      IsNilpotent (LieAlgebra.ad ℂ L e) ∧ IsNilpotent (LieAlgebra.ad ℂ L f) ∧
      ∃ n : L ≃ₗ⁅ℂ⁆ L, n.toLinearMap = reflectionLiftLinear_value e f ∧
        (∀ h : H, n (h : L) = (h : L) - α h • (coroot_value H α : L)) ∧
        ∀ β : Module.Dual ℂ H,
          (rootSpace_value H β).map n.toLinearMap = rootSpace_value H (reflection_value H α β)

/-- In every finite basis, the algebraic expression used above is precisely
formula (4.2) with ordinary convergent complex matrix exponentials. -/
def reflection_lift_matrix_exponential_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (d : ℕ) (b : Module.Basis (Fin d) ℂ L) (e f : L),
    IsNilpotent (LieAlgebra.ad ℂ L e) → IsNilpotent (LieAlgebra.ad ℂ L f) →
    LinearMap.toMatrixAlgEquiv b (reflectionLiftLinear_value e f) =
      NormedSpace.exp (LinearMap.toMatrixAlgEquiv b (LieAlgebra.ad ℂ L e)) *
      NormedSpace.exp (-LinearMap.toMatrixAlgEquiv b (LieAlgebra.ad ℂ L f)) *
      NormedSpace.exp (LinearMap.toMatrixAlgEquiv b (LieAlgebra.ad ℂ L e))

end Specs.LieAlgebrasAndRepresentations.RootStrings
