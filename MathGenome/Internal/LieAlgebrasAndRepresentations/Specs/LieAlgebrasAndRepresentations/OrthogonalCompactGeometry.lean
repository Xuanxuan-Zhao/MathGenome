import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature
import Mathlib.Algebra.Lie.Classical

/-! Compact orthogonal matrix algebras and the J-centralizer in LA-J07. -/

noncomputable section

open Matrix LieAlgebra
open LieAlgebrasAndRepresentations.RealForms (Conjugation Intertwines)
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures
open Specs.LieAlgebrasAndRepresentations.CartanDecompositionSignature

namespace LieAlgebrasAndRepresentations.OrthogonalCompactGeometry

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The compact conjugation on complex skew-symmetric matrices. -/
def coefficientConjugation (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Conjugation (Orthogonal.so ι ℂ) where
  map :=
    { toFun X := ⟨Complex.conjAe.toRingEquiv.mapMatrix X.val,
        (Orthogonal.mem_so _ _ _).2 <| by
          change Complex.conjAe.toRingEquiv.mapMatrix X.valᵀ =
            -(Complex.conjAe.toRingEquiv.mapMatrix X.val)
          rw [(Orthogonal.mem_so _ _ _).1 X.property, map_neg]⟩
      map_add' X Y := Subtype.ext (map_add (Complex.conjAe.toRingEquiv.mapMatrix) X.val Y.val)
      map_smul' r X := Subtype.ext <| Matrix.ext fun i j => by
        change (starRingEnd ℂ) ((r : ℂ) * X.val i j) = r • star (X.val i j)
        rw [map_mul, Complex.conj_ofReal, Complex.real_smul]
        rfl
      map_lie' {X Y} := Subtype.ext <| by
        change Complex.conjAe.toRingEquiv.mapMatrix (X.val * Y.val - Y.val * X.val) = _
        rw [map_sub, map_mul, map_mul]
        rfl }
  antilinear a X := Subtype.ext <| Matrix.ext fun i j => by
    change star (a * X.val i j) = star a * star (X.val i j)
    rw [star_mul, mul_comm]
  involutive X := Subtype.ext <| Matrix.ext fun i j => star_star (X.val i j)

/-- The source's standard complex structure, with positive upper-right block. -/
abbrev sourceJ (n : ℕ) (R : Type*) [CommRing R] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  -Matrix.J (Fin n) R

/-- The commuting skew-symmetric matrices, as a Lie subalgebra of the actual matrix model. -/
def skewCentralizer {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (J : Matrix ι ι R) : LieSubalgebra R (Orthogonal.so ι R) where
  carrier := {X | Commute X.val J}
  zero_mem' := Commute.zero_left J
  add_mem' := fun hx hy => hx.add_left hy
  smul_mem' := fun r _ hx => hx.smul_left r
  lie_mem' hx hy := (hx.mul_left hy).sub_left (hy.mul_left hx)

/-- The compact real unitary Lie algebra of skew-Hermitian matrices. -/
def unitaryAlgebra (n : ℕ) : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Xᴴ = -X}
  zero_mem' := by
    change (0 : Matrix _ _ ℂ)ᴴ = -0
    simp
  add_mem' := by
    intro X Y hX hY
    change (X + Y)ᴴ = -(X + Y)
    rw [Matrix.conjTranspose_add, hX, hY, neg_add]
  smul_mem' := by
    intro r X hX
    change (r • X)ᴴ = -(r • X)
    rw [Matrix.conjTranspose_smul, star_trivial, hX, smul_neg]
  lie_mem' := by
    intro X Y hX hY
    change (X * Y - Y * X)ᴴ = -(X * Y - Y * X)
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hX, hY, neg_mul_neg, neg_mul_neg, neg_sub]

end LieAlgebrasAndRepresentations.OrthogonalCompactGeometry

namespace Specs.LieAlgebrasAndRepresentations.OrthogonalCompactGeometry

open _root_.LieAlgebrasAndRepresentations.OrthogonalCompactGeometry
attribute [local instance 100] LieRing.ofAssociativeRing

def compact_type : Prop :=
  ∀ N : ℕ, (N = 3 ∨ 5 ≤ N) → IsCompact (coefficientConjugation (Fin N))

def semisimple_type : Prop :=
  ∀ N : ℕ, (N = 3 ∨ 5 ≤ N) →
    LieAlgebra.IsSemisimple ℂ (Orthogonal.so (Fin N) ℂ) ∧
      SolvableRadical.IsSemisimple_value ℂ (Orthogonal.so (Fin N) ℂ)

def coefficient_fixed_type : Prop :=
  ∀ N : ℕ, ∃ e : Orthogonal.so (Fin N) ℝ ≃ₗ⁅ℝ⁆ (coefficientConjugation (Fin N)).fixed,
    ∀ X i j, (e X).val.val i j = (X.val i j : ℂ)

def quaternionic_complex_type : Prop :=
  ∀ n : ℕ, ∃ e : skewCentralizer (sourceJ n ℂ) ≃ₗ⁅ℂ⁆ Matrix (Fin n) (Fin n) ℂ,
    ∀ X, e X = Matrix.toBlocks₁₁ X.val.val + Complex.I • Matrix.toBlocks₁₂ X.val.val

def quaternionic_real_type : Prop :=
  ∀ n : ℕ, ∃ e : skewCentralizer (sourceJ n ℝ) ≃ₗ⁅ℝ⁆ unitaryAlgebra n,
    ∀ X, (e X).val =
      (Matrix.toBlocks₁₁ X.val.val).map Complex.ofReal +
        Complex.I • (Matrix.toBlocks₁₂ X.val.val).map Complex.ofReal

def quaternionic_automorphism_type : Prop :=
  ∀ (n : ℕ) (a : Orthogonal.so (Fin n ⊕ Fin n) ℂ ≃ₗ⁅ℂ⁆ Orthogonal.so (Fin n ⊕ Fin n) ℂ),
    (∀ X, (a X).val = sourceJ n ℂ * X.val * (sourceJ n ℂ)ᵀ) →
      Nonempty (complexFixed a ≃ₗ⁅ℂ⁆ Matrix (Fin n) (Fin n) ℂ)

def quaternionic_real_fixed_type : Prop :=
  ∀ (n : ℕ) (a : Orthogonal.so (Fin n ⊕ Fin n) ℂ ≃ₗ⁅ℂ⁆ Orthogonal.so (Fin n ⊕ Fin n) ℂ)
    (hcomm : Intertwines
      (coefficientConjugation (Fin n ⊕ Fin n)) (coefficientConjugation (Fin n ⊕ Fin n)) a),
    (∀ X, (a X).val = sourceJ n ℂ * X.val * (sourceJ n ℂ)ᵀ) →
      Nonempty ((fixedConjugation (coefficientConjugation (Fin n ⊕ Fin n)) a hcomm).fixed
        ≃ₗ⁅ℝ⁆ unitaryAlgebra n)

def orthogonal_dimensions_type : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (m : ℕ),
    Module.finrank K (Orthogonal.so (Fin m) K) = m * (m - 1) / 2 ∧
    Module.finrank K (LieAlgebra.center K (Orthogonal.so (Fin m) K)) =
      if m = 2 then 1 else 0

def signed_dimensions_type : Prop :=
  ∀ p q : ℕ,
    Module.finrank ℂ (Orthogonal.so (Fin p) ℂ × Orthogonal.so (Fin q) ℂ) =
      p * (p - 1) / 2 + q * (q - 1) / 2 ∧
    Module.finrank ℂ (LieAlgebra.center ℂ (Orthogonal.so (Fin p) ℂ × Orthogonal.so (Fin q) ℂ)) =
      (if p = 2 then 1 else 0) + (if q = 2 then 1 else 0)

def general_linear_dimensions_type : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ),
    Module.finrank K (Matrix (Fin n) (Fin n) K) = n ^ 2 ∧
    (0 < n → Module.finrank K (LieAlgebra.center K (Matrix (Fin n) (Fin n) K)) = 1)

end Specs.LieAlgebrasAndRepresentations.OrthogonalCompactGeometry
