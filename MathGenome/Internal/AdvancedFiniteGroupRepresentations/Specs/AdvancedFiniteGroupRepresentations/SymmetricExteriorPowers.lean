import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TensorEvaluation
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-! FR-D09, source lines 1634–1681. Both powers are the usual multilinear
quotients of the actual tensor power; the universal-property targets below
identify the sign quotient with the universal exterior power. `a = false`
means the trivial character, `a = true` the sign character. -/
noncomputable section
open scoped BigOperators
universe u v
namespace Specs.AdvancedFiniteGroupRepresentations

def tensorParity {n : ℕ} (a : Bool) (s : SymmetricGroup n) : ℂ :=
  if a then permutationSign s else 1

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

def parityTensors (n : ℕ) (a : Bool) : Submodule ℂ (TensorPower V n) where
  carrier := {x | ∀ s, slotOperator V n s x = tensorParity a s • x}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy s; simp [hx s, hy s, smul_add]
  smul_mem' := by
    intro c x hx s
    rw [map_smul, hx s, smul_comm]

def parityRelations (n : ℕ) (a : Bool) : Submodule ℂ (TensorPower V n) :=
  Submodule.span ℂ {z | ∃ (s : SymmetricGroup n) (x : TensorPower V n),
    z = x - tensorParity a s • slotOperator V n s x}

abbrev ParityPower (n : ℕ) (a : Bool) := TensorPower V n ⧸ parityRelations V n a
abbrev SymmetricTensorPower (n : ℕ) := ParityPower V n false
abbrev ExteriorTensorPower (n : ℕ) := ParityPower V n true

def parityPure (n : ℕ) (a : Bool) :
    MultilinearMap ℂ (fun _ : Fin n => V) (ParityPower V n a) :=
  (parityRelations V n a).mkQ.compMultilinearMap (PiTensorProduct.tprod ℂ)

def tensorAverage (n : ℕ) (a : Bool) : Module.End ℂ (TensorPower V n) :=
  (n.factorial : ℂ)⁻¹ • ∑ s : SymmetricGroup n, tensorParity a s • slotOperator V n s

open private slot_diagonal_commute from MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TensorEvaluation

/-- The diagonal action induced on the quotient by its defining relations. -/
def parityPowerOperator (n : ℕ) (a : Bool) (g : LinearGroup V) :
    Module.End ℂ (ParityPower V n a) :=
  (parityRelations V n a).mapQ (parityRelations V n a) (diagonalOperator V n g) (by
    apply Submodule.span_le.mpr
    rintro z ⟨s, x, rfl⟩
    change diagonalOperator V n g (x - tensorParity a s • slotOperator V n s x) ∈ parityRelations V n a
    rw [map_sub, map_smul]
    have he := DFunLike.congr_fun (slot_diagonal_commute V n s g) x
    change slotOperator V n s (diagonalOperator V n g x) =
      diagonalOperator V n g (slotOperator V n s x) at he
    rw [← he]
    exact Submodule.subset_span ⟨s, diagonalOperator V n g x, rfl⟩)

/-- The averaging isomorphism has the specified actual forward map and
intertwines the diagonal action, in every degree including zero. -/
def tensorAverage_quotientType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ) (a : Bool),
    LinearMap.ker (tensorAverage V n a) = parityRelations V n a ∧
    (∀ x, tensorAverage V n a x ∈ parityTensors V n a) ∧
    (∀ x : parityTensors V n a, tensorAverage V n a x.val = x.val) ∧
    ∃ e : ParityPower V n a ≃ₗ[ℂ] parityTensors V n a,
      (∀ x, (e ((parityRelations V n a).mkQ x)).val = tensorAverage V n a x) ∧
      ∀ (g : LinearGroup V) (q : ParityPower V n a),
        (e (parityPowerOperator V n a g q)).val = diagonalOperator V n g (e q).val

/-- Hom from a row or column Specht module is the corresponding power,
with its actual diagonal GL action. -/
def multiplicity_parityPowerType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (n : ℕ), 0 < n →
    (∃ e : TensorMultiplicity V (Nat.Partition.indiscrete n) ≃ₗ[ℂ]
        SymmetricTensorPower V n,
      ∀ (g : LinearGroup V) f,
        e (tensorMultiplicityOperator V _ g f) = parityPowerOperator V n false g (e f)) ∧
    (∃ e : TensorMultiplicity V (transpose (Nat.Partition.indiscrete n)) ≃ₗ[ℂ]
        ExteriorTensorPower V n,
      ∀ (g : LinearGroup V) f,
        e (tensorMultiplicityOperator V _ g f) = parityPowerOperator V n true g (e f))

/-- Universal symmetric multilinear quotient. -/
def symmetricTensorPower_universalType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ),
    (∀ (s : SymmetricGroup n) (v : Fin n → V),
      parityPure V n false (v ∘ s) = parityPure V n false v) ∧
    ∀ (W : Type v) [AddCommGroup W] [Module ℂ W]
      (f : MultilinearMap ℂ (fun _ : Fin n => V) W),
      (∀ (s : SymmetricGroup n) v, f (v ∘ s) = f v) →
      ∃! l : SymmetricTensorPower V n →ₗ[ℂ] W, ∀ v, l (parityPure V n false v) = f v

/-- Universal alternating multilinear quotient; this is the defining
universal property of the exterior power, including in degrees zero and one. -/
def exteriorTensorPower_universalType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ),
    (∀ (v : Fin n → V) (i j : Fin n), v i = v j → i ≠ j →
      parityPure V n true v = 0) ∧
    ∀ (W : Type v) [AddCommGroup W] [Module ℂ W]
      (f : V [⋀^Fin n]→ₗ[ℂ] W),
      ∃! l : ExteriorTensorPower V n →ₗ[ℂ] W, ∀ v, l (parityPure V n true v) = f v

/-- The sign quotient agrees with the library exterior power on pure wedges
and for the natural GL action. -/
def exteriorTensorPower_equivType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ),
    ∃ e : ExteriorTensorPower V n ≃ₗ[ℂ] (⋀[ℂ]^n V),
      (∀ v, e (parityPure V n true v) = exteriorPower.ιMulti ℂ n v) ∧
      ∀ (g : LinearGroup V) q, e (parityPowerOperator V n true g q) =
        exteriorPower.map n g.toLinearMap (e q)

/-- The two identifications of FR-D09, with Mathlib's exterior power as the
column target and the universal symmetric multilinear quotient as the row target. -/
def symmetricExteriorPowersType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (n : ℕ), 0 < n →
    (∃ e : TensorMultiplicity V (Nat.Partition.indiscrete n) ≃ₗ[ℂ]
        SymmetricTensorPower V n,
      ∀ (g : LinearGroup V) f,
        e (tensorMultiplicityOperator V _ g f) = parityPowerOperator V n false g (e f)) ∧
    (∃ e : TensorMultiplicity V (transpose (Nat.Partition.indiscrete n)) ≃ₗ[ℂ]
        (⋀[ℂ]^n V),
      ∀ (g : LinearGroup V) f,
        e (tensorMultiplicityOperator V _ g f) = exteriorPower.map n g.toLinearMap (e f))

def parityPower_zeroType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V],
    (∀ a, ∃ e : ParityPower V 0 a ≃ₗ[ℂ] ℂ,
      (∀ v, e (parityPure V 0 a v) = 1) ∧
      ∀ g q, e (parityPowerOperator V 0 a g q) = e q) ∧
    ∃ e : TensorMultiplicity V emptyPartition ≃ₗ[ℂ] ℂ,
      ∀ g f, e (tensorMultiplicityOperator V emptyPartition g f) = e f

/-- Complete d=2,n=3 shape cutoff and the stated dimensions. The actual
Specht and Hom spaces, not only a numerical equality, occur here. -/
def degreeThree_twoDimensionalType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    Module.finrank ℂ V = 2 →
    ∃ p : Partition 3, parts p = [2, 1] ∧
      (∀ q : Partition 3, Nontrivial (TensorMultiplicity V q) ↔
        q = Nat.Partition.indiscrete 3 ∨ q = p) ∧
      Module.finrank ℂ (SpechtModule (Nat.Partition.indiscrete 3)) = 1 ∧
      Module.finrank ℂ (SpechtModule p) = 2 ∧
      Module.finrank ℂ (TensorMultiplicity V (Nat.Partition.indiscrete 3)) = 4 ∧
      Module.finrank ℂ (TensorMultiplicity V p) = 2 ∧
      Module.finrank ℂ (TensorMultiplicity V (transpose (Nat.Partition.indiscrete 3))) = 0 ∧
      Module.finrank ℂ (TensorPower V 3) = 8 ∧
      Module.finrank ℂ (TensorPower V 3) =
        Module.finrank ℂ (SpechtModule (Nat.Partition.indiscrete 3)) *
          Module.finrank ℂ (TensorMultiplicity V (Nat.Partition.indiscrete 3)) +
        Module.finrank ℂ (SpechtModule p) * Module.finrank ℂ (TensorMultiplicity V p)

end Specs.AdvancedFiniteGroupRepresentations
