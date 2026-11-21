import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.DerivedTensorAction
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.Matrix
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! LA-G09, the polynomial comparison, source lines 3458–3463 and 3488–3502.
Coordinates are numbered from zero. The underlying polynomial modules are the
original Schur–Weyl multiplicity spaces, including the degree-zero module.
The index type for adjacent differences is empty in dimensions zero and one. -/

noncomputable section
open scoped BigOperators Matrix
open Matrix LieAlgebra.SpecialLinear
attribute [local instance] LieRing.ofAssociativeRing

namespace Specs.LieAlgebrasAndRepresentations.PolynomialGroupLieComparison

open Specs.AdvancedFiniteGroupRepresentations

abbrev Coordinates (d : ℕ) := Fin d → ℂ
abbrev SpecialLinear (d : ℕ) := ↥(sl (Fin d) ℂ)
abbrev GeneralLinear (d : ℕ) := Matrix.GeneralLinearGroup (Fin d) ℂ
abbrev SchurModule (d : ℕ) {n : ℕ} (p : Partition n) := TensorMultiplicity (Coordinates d) p

def matrixAction (d : ℕ) : GeneralLinear d ≃* LinearGroup (Coordinates d) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv ℂ (Coordinates d))

def diagonalGroup {d : ℕ} (x : Fin d → ℂˣ) : GeneralLinear d :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal fun i => (x i : ℂ))
    (by rw [det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun i _ => (x i).ne_zero)

def elementaryGroup {d : ℕ} (i j : Fin d) (h : i ≠ j) (t : ℂ) : GeneralLinear d :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j t)
    (by rw [Matrix.det_transvection_of_ne i j h]; exact one_ne_zero)

def sumCoordinates (d : ℕ) : Coordinates d →ₗ[ℂ] ℂ :=
  ∑ i, LinearMap.proj i

abbrev Cartan (d : ℕ) := LinearMap.ker (sumCoordinates d)

def diagonalLie {d : ℕ} (h : Cartan d) : SpecialLinear d :=
  ⟨Matrix.diagonal h.val, by
    change Matrix.trace (Matrix.diagonal h.val) = 0
    have hh := LinearMap.mem_ker.mp h.property
    simpa [sumCoordinates] using hh⟩

def upperLie {d : ℕ} (i j : Fin d) (h : i < j) : SpecialLinear d :=
  LieAlgebra.SpecialLinear.single i j h.ne 1

def restrictedWeight {d n : ℕ} (p : Partition n) : Module.Dual ℂ (Cartan d) :=
  ∑ i : Fin d, (rowLength p i.val : ℂ) •
    ((LinearMap.proj i : Coordinates d →ₗ[ℂ] ℂ).comp (sumCoordinates d).ker.subtype)

def fundamentalWeight {d : ℕ} (j : Fin (d - 1)) : Module.Dual ℂ (Cartan d) :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val ≤ j.val),
    ((LinearMap.proj i : Coordinates d →ₗ[ℂ] ℂ).comp (sumCoordinates d).ker.subtype)

def adjacentDifference {d n : ℕ} (p : Partition n) (i : Fin (d - 1)) : ℤ :=
  (rowLength p i.val : ℤ) - (rowLength p (i.val + 1) : ℤ)

def diagonalCharacter {d n : ℕ} (p : Partition n) (x : Fin d → ℂˣ) : ℂ :=
  ∏ i, (x i : ℂ) ^ rowLength p i.val

def groupOnSchur {d n : ℕ} (p : Partition n) (g : GeneralLinear d) :
    Module.End ℂ (SchurModule d p) :=
  tensorMultiplicityOperator (Coordinates d) p (matrixAction d g)

def IsDifferentiatedAction {d n : ℕ} (p : Partition n)
    (ρ : SpecialLinear d →ₗ⁅ℂ⁆ Module.End ℂ (SchurModule d p)) : Prop :=
  ∀ (A : SpecialLinear d) (f : SchurModule d p) (v : SpechtModule p),
    (ρ A f).val v =
      derivedTensorOperator (Coordinates d) n
        (Matrix.toLin' (A : Matrix (Fin d) (Fin d) ℂ)) (f.val v)

def IsGroupStable {d n : ℕ} (p : Partition n) (W : Submodule ℂ (SchurModule d p)) : Prop :=
  ∀ (g : GeneralLinear d) f, f ∈ W → groupOnSchur p g f ∈ W

def IsLieStable {d n : ℕ} {p : Partition n}
    (ρ : SpecialLinear d →ₗ⁅ℂ⁆ Module.End ℂ (SchurModule d p))
    (W : Submodule ℂ (SchurModule d p)) : Prop :=
  ∀ A f, f ∈ W → ρ A f ∈ W

def differentiationType : Prop :=
  ∀ {d n : ℕ} (p : Partition n),
    ∃! ρ : SpecialLinear d →ₗ⁅ℂ⁆ Module.End ℂ (SchurModule d p),
      IsDifferentiatedAction p ρ

def stable_iffType : Prop :=
  ∀ {d n : ℕ} (p : Partition n)
    (ρ : SpecialLinear d →ₗ⁅ℂ⁆ Module.End ℂ (SchurModule d p)),
    IsDifferentiatedAction p ρ →
    ∀ W : Submodule ℂ (SchurModule d p), IsLieStable ρ W ↔ IsGroupStable p W

def simple_restrictionType : Prop :=
  ∀ {d n : ℕ} (p : Partition n), length p ≤ d →
    ∀ ρ : SpecialLinear d →ₗ⁅ℂ⁆ Module.End ℂ (SchurModule d p),
      IsDifferentiatedAction p ρ →
      Nontrivial (SchurModule d p) ∧
      ∀ W : Submodule ℂ (SchurModule d p), IsLieStable ρ W → W = ⊥ ∨ W = ⊤

def highest_lineType : Prop :=
  ∀ {d n : ℕ} (p : Partition n), length p ≤ d →
    ∀ ρ : SpecialLinear d →ₗ⁅ℂ⁆ Module.End ℂ (SchurModule d p),
      IsDifferentiatedAction p ρ →
      ∃ v : SchurModule d p, v ≠ 0 ∧
        (∀ f : SchurModule d p,
          (∀ x : Fin d → ℂˣ, groupOnSchur p (diagonalGroup x) f =
            diagonalCharacter p x • f) ↔ f ∈ ℂ ∙ v) ∧
        (∀ i j h, ρ (upperLie i j h) v = 0) ∧
        (∀ h : Cartan d, ρ (diagonalLie h) v = restrictedWeight p h • v) ∧
        restrictedWeight p = ∑ i : Fin (d - 1),
          (adjacentDifference (d := d) p i : ℂ) • fundamentalWeight (d := d) i

def constant_shiftType : Prop :=
  ∀ {d n m : ℕ} (p : Partition n) (q : Partition m),
    (∀ i : Fin (d - 1), adjacentDifference (d := d) p i = adjacentDifference (d := d) q i) ↔
      ∃ k : ℤ, ∀ i : Fin d,
        (rowLength p i.val : ℤ) - (rowLength q i.val : ℤ) = k

def determinant_twistType : Prop :=
  ∀ {d n m : ℕ} (p : Partition n) (q : Partition m),
    length p ≤ d → length q ≤ d → ∀ k : ℤ,
      (∃ e : SchurModule d q ≃ₗ[ℂ] SchurModule d p,
        ∀ g v, groupOnSchur p g (e v) =
          ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ) ^ k • e (groupOnSchur q g v)) ↔
      ∀ i : Fin d, (rowLength p i.val : ℤ) - (rowLength q i.val : ℤ) = k

def weight_twist_iffType : Prop :=
  ∀ {d n m : ℕ} (p : Partition n) (q : Partition m),
    length p ≤ d → length q ≤ d →
    ((restrictedWeight p : Module.Dual ℂ (Cartan d)) = restrictedWeight q ↔
      ∃ k : ℤ, ∀ i : Fin d,
        (rowLength p i.val : ℤ) - (rowLength q i.val : ℤ) = k) ∧
    ((restrictedWeight p : Module.Dual ℂ (Cartan d)) = restrictedWeight q ↔
      ∃ k : ℤ, ∃ e : SchurModule d q ≃ₗ[ℂ] SchurModule d p,
        ∀ g v, groupOnSchur p g (e v) =
          ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ) ^ k • e (groupOnSchur q g v))


/-- The Cartan of diagonal trace-zero matrices. -/
def diagonalCartan (d : ℕ) : LieSubalgebra ℂ (SpecialLinear d) where
  carrier := {A | ∀ i j, i ≠ j → A.val i j = 0}
  zero_mem' := by simp
  add_mem' := by intro A B hA hB i j hij; exact by simp [hA i j hij, hB i j hij]
  smul_mem' := by intro c A hA i j hij; exact by simp [hA i j hij]
  lie_mem' := by
    intro A B hA hB i j hij
    have asDiagonal (C : SpecialLinear d) (hC : ∀ i j, i ≠ j → C.val i j = 0) :
        C.val = Matrix.diagonal (Matrix.diag C.val) := by
      ext i j
      by_cases h : i = j
      · subst j; simp
      · rw [hC i j h, Matrix.diagonal_apply_ne _ h]
    change (A.val * B.val - B.val * A.val) i j = 0
    rw [asDiagonal A hA, asDiagonal B hB, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.sub_apply,
      Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, sub_self]

/-- Read the entries on the diagonal of that Cartan. -/
def cartanCoordinates (d : ℕ) : diagonalCartan d →ₗ[ℂ] Cartan d where
  toFun A := ⟨Matrix.diag A.val.val, by
    have ht := A.val.property
    change Matrix.trace A.val.val = 0 at ht
    exact LinearMap.mem_ker.mpr (by simpa [sumCoordinates, Matrix.trace] using ht)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The direction giving the usual positive roots is evaluation, followed by
real part, at the trace-zero diagonal of decreasing coordinate indices. -/
def positiveDirection (d : ℕ) :
    Specs.LieAlgebrasAndRepresentations.VermaModules.Direction (diagonalCartan d) :=
  { toFun := fun μ => (μ ⟨diagonalLie (heightCoordinates d), by
      intro i j hij
      exact Matrix.diagonal_apply_ne _ hij⟩).re
    map_add' _ _ := by simp
    map_smul' _ _ := by simp [Complex.real_smul] }
where
  heightCoordinates (d : ℕ) : Cartan d :=
    let x : Coordinates d := fun i => -(i.val : ℂ)
    let c := (sumCoordinates d x) / (d : ℂ)
    ⟨x - fun _ => c, LinearMap.mem_ker.mpr (by
      by_cases hd : d = 0
      · subst d; simp [sumCoordinates]
      · rw [map_sub]
        have hc : sumCoordinates d (fun _ => c) = (d : ℂ) * c := by
          simp [sumCoordinates, nsmul_eq_mul]
        rw [hc, mul_comm]
        rw [show c * (d : ℂ) = sumCoordinates d x from
          div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hd), sub_self])⟩

/-- The fixed matrix Cartan and positive direction used by the existing
Verma-module construction. The stated isomorphism is to its simple quotient. -/
def highest_quotientType : Prop :=
  ∀ {d n : ℕ} (p : Partition n), length p ≤ d →
    ∀ ρ : SpecialLinear d →ₗ⁅ℂ⁆ Module.End ℂ (SchurModule d p),
      IsDifferentiatedAction p ρ →
      let H := diagonalCartan d
      let φ := positiveDirection d
      let μ := (restrictedWeight p).comp (cartanCoordinates d)
      letI := LieRingModule.compLieHom (SchurModule d p) ρ
      letI := LieModule.compLieHom (SchurModule d p) ρ
      ∃ χ : Specs.LieAlgebrasAndRepresentations.VermaModules.U
          (Specs.LieAlgebrasAndRepresentations.VermaModules.borel_value H φ) →ₐ[ℂ] ℂ,
        Specs.LieAlgebrasAndRepresentations.VermaModules.IsWeightCharacter H φ μ χ ∧
        letI := Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal.inducedLieRingModule H φ χ
        letI := Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal.inducedLieModule H φ χ
        Nonempty (SchurModule d p ≃ₗ⁅ℂ, SpecialLinear d⁆
          Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient.simpleQuotient_value H φ χ)

end Specs.LieAlgebrasAndRepresentations.PolynomialGroupLieComparison
