import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealFormsOrthogonal
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealFormsSymplectic
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealFormsTypeA

/-! Real matrix identifications and the nonsimple rank-two case of LA-J07,
notes/005/lie-algebras-and-representations.tex, lines 5084–5121. -/

noncomputable section

open scoped TensorProduct
open LieAlgebra Matrix
open LieAlgebrasAndRepresentations.RealForms
open LieAlgebrasAndRepresentations.RealFormsOrthogonal

namespace Specs.LieAlgebrasAndRepresentations.RealFormLowRanks

open RealFormsTypeA (SL Blocks)
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The literal trace-zero skew-Hermitian matrices. -/
abbrev su (n : ℕ) : LieSubalgebra ℝ (SL (Fin n)) :=
  (_root_.LieAlgebrasAndRepresentations.OrthogonalCompactGeometry.unitaryAlgebra n).comap {
    toLinearMap := (SL (Fin n)).incl.toLinearMap.restrictScalars ℝ
    map_lie' := rfl }

abbrev sl₂ℝ := SpecialLinear.sl (Fin 2) ℝ
abbrev sl₂ℂ := SL (Fin 2)

/-- A conjugation in the actual signed unitary coordinates, with its defining formula. -/
def HasUnitaryFormula {p q : ℕ} (σ : Conjugation (SL (Blocks p q))) : Prop :=
  ∀ X, (σ.map X).val =
    -(RealFormsTypeA.signatureMatrix p q * X.valᴴ * RealFormsTypeA.signatureMatrix p q)

def b1_compact_type : Prop := Nonempty (Orthogonal.so (Fin 3) ℝ ≃ₗ⁅ℝ⁆ su 2)
def b1_split_type : Prop := Nonempty (soSignature 2 1 ≃ₗ⁅ℝ⁆ sl₂ℝ)

def b2_compact_type : Prop :=
  Nonempty (Orthogonal.so (Fin 5) ℝ ≃ₗ⁅ℝ⁆ RealFormsSymplectic.quaternionicSkewLie_value 2 2)
def b2_quaternionic_type : Prop :=
  Nonempty (soSignature 4 1 ≃ₗ⁅ℝ⁆ RealFormsSymplectic.quaternionicSkewLie_value 2 1)
def b2_split_type : Prop :=
  Nonempty (soSignature 3 2 ≃ₗ⁅ℝ⁆ Symplectic.sp (Fin 2) ℝ)

def d3_compact_type : Prop := Nonempty (Orthogonal.so (Fin 6) ℝ ≃ₗ⁅ℝ⁆ su 4)
def d3_quaternionic_type : Prop :=
  Nonempty (soSignature 5 1 ≃ₗ⁅ℝ⁆ RealFormsTypeA.quaternionicSL (Fin 2))
def d3_unitary_type : Prop :=
  ∃ σ : Conjugation (SL (Blocks 2 2)), HasUnitaryFormula σ ∧
    Nonempty (soSignature 4 2 ≃ₗ⁅ℝ⁆ σ.fixed)
def d3_split_type : Prop :=
  Nonempty (soSignature 3 3 ≃ₗ⁅ℝ⁆ SpecialLinear.sl (Fin 4) ℝ)
def d3_orthogonal_quaternionic_type : Prop :=
  ∃ σ : Conjugation (SL (Blocks 3 1)), HasUnitaryFormula σ ∧
    Nonempty (soStar 3 ≃ₗ⁅ℝ⁆ σ.fixed)

def d4_triality_type : Prop := Nonempty (soStar 4 ≃ₗ⁅ℝ⁆ soSignature 6 2)

def d2_complex_type : Prop := Nonempty (Orthogonal.so (Fin 4) ℂ ≃ₗ⁅ℂ⁆ (sl₂ℂ × sl₂ℂ))

def d2_compact_type : Prop := Nonempty (Orthogonal.so (Fin 4) ℝ ≃ₗ⁅ℝ⁆ (su 2 × su 2))
def d2_split_type : Prop := Nonempty (soSignature 2 2 ≃ₗ⁅ℝ⁆ (sl₂ℝ × sl₂ℝ))
def d2_lorentz_type : Prop := Nonempty (soSignature 3 1 ≃ₗ⁅ℝ⁆ sl₂ℂ)
def d2_quaternionic_type : Prop := Nonempty (soStar 2 ≃ₗ⁅ℝ⁆ (su 2 × sl₂ℝ))

def d2_quaternionic_compact_type : Prop :=
  let K := compactSubalgebra (coefficientConjugation (Fin 2 ⊕ Fin 2)) (quaternionicConjugation 2)
  IsMaximalCompact K ∧ Nonempty (K ≃ₗ⁅ℝ⁆ (su 2 × _root_.LieAlgebrasAndRepresentations.OrthogonalCompactGeometry.unitaryAlgebra 1))

inductive OrthogonalFourKind
  | compact | split | lorentz | quaternionic
  deriving DecidableEq

/-- The four actual orthogonal models at size four. -/
def OrthogonalFourModel : OrthogonalFourKind → Type
  | .compact => Orthogonal.so (Fin 4) ℝ
  | .split => soSignature 2 2
  | .lorentz => soSignature 3 1
  | .quaternionic => soStar 2

instance (i : OrthogonalFourKind) : LieRing (OrthogonalFourModel i) := by
  cases i <;> unfold OrthogonalFourModel <;> infer_instance

instance (i : OrthogonalFourKind) : LieAlgebra ℝ (OrthogonalFourModel i) := by
  cases i <;> unfold OrthogonalFourModel <;> infer_instance

def d2_models_real_forms_type : Prop :=
  ∀ i : OrthogonalFourKind, ∃ S : LieSubalgebra ℝ (Orthogonal.so (Fin 4) ℂ),
    IsRealForm S ∧ Nonempty (OrthogonalFourModel i ≃ₗ⁅ℝ⁆ S)

def d2_classification_type : Prop :=
  ∀ S : LieSubalgebra ℝ (Orthogonal.so (Fin 4) ℂ), IsRealForm S →
    ∃ i : OrthogonalFourKind, Nonempty (S ≃ₗ⁅ℝ⁆ OrthogonalFourModel i)

def d2_abstract_classification_type : Prop :=
  ∀ (A : Type*) [LieRing A] [LieAlgebra ℝ A],
    Nonempty ((ℂ ⊗[ℝ] A) ≃ₗ⁅ℂ⁆ Orthogonal.so (Fin 4) ℂ) ↔
      ∃ i : OrthogonalFourKind, Nonempty (A ≃ₗ⁅ℝ⁆ OrthogonalFourModel i)

def d2_distinct_type : Prop :=
  ∀ i j : OrthogonalFourKind, Nonempty (OrthogonalFourModel i ≃ₗ⁅ℝ⁆ OrthogonalFourModel j) ↔ i = j

end Specs.LieAlgebrasAndRepresentations.RealFormLowRanks
