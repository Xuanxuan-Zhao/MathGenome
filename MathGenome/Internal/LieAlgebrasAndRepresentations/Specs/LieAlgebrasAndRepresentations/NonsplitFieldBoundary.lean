import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RealFormLowRanks
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ClassicalRootsA
import Mathlib.Algebra.Lie.Killing
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The nonsplit real action and the two real forms in LA-J09,
`notes/005/lie-algebras-and-representations.tex`, under “A nonsplit real action.” -/

noncomputable section

open scoped TensorProduct Matrix
open LieAlgebra Matrix

namespace Specs.LieAlgebrasAndRepresentations.NonsplitFieldBoundary

open RealFormLowRanks (su sl₂ℝ sl₂ℂ)
open _root_.LieAlgebrasAndRepresentations.RealForms (IsRealForm)

attribute [local instance 100] LieRing.ofAssociativeRing

abbrev Plane (k : Type*) := Fin 2 → k

/-- The rotation in the ordered coordinate basis. -/
def rotation (k : Type*) [Field k] : Module.End k (Plane k) :=
  (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) k).mulVecLin

/-- The one-dimensional Lie algebra acts by scalar multiples of the rotation. -/
def rotationAction (k : Type*) [Field k] : k →ₗ⁅k⁆ Module.End k (Plane k) where
  toFun t := t • rotation k
  map_add' _ _ := add_smul _ _ _
  map_smul' _ _ := smul_assoc _ _ _
  map_lie' {x y} := by
    change (x * y - y * x) • rotation k = ⁅x • rotation k, y • rotation k⁆
    rw [mul_comm x y, sub_self, zero_smul, LieRing.of_associative_ring_bracket]
    exact (sub_eq_zero.mpr (((Commute.refl (rotation k)).smul_left x).smul_right y).eq).symm

@[instance_reducible] def rotationLieRingModule : LieRingModule ℝ (Plane ℝ) :=
  LieRingModule.compLieHom _ (rotationAction ℝ)

theorem rotationLieModule : @LieModule ℝ ℝ (Plane ℝ) _ _ _ _ _ rotationLieRingModule :=
  LieModule.compLieHom _ (rotationAction ℝ)

/-- The real Lie algebra is abelian and has no invariant line in this representation.
In particular the action admits no common upper triangular basis over the reals. -/
def rotation_real_type : Prop :=
  Module.finrank ℝ ℝ = 1 ∧ IsLieAbelian ℝ ∧
  (∀ W : Submodule ℝ (Plane ℝ), Module.finrank ℝ W = 1 →
    ¬ ∀ (t : ℝ) (v : Plane ℝ), v ∈ W → rotationAction ℝ t v ∈ W) ∧
  ¬ ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ (Plane ℝ)),
    ∀ (t : ℝ) (i j : Fin n), j < i → b.repr (rotationAction ℝ t (b j)) i = 0

/-- The complexified action is the complex rotation action in the extended coordinates.
Its two eigenspaces are exactly the indicated distinct lines, and span the plane. -/
def rotation_complex_type : Prop :=
  letI := rotationLieRingModule
  letI := rotationLieModule
  (∃ e : (ℂ ⊗[ℝ] Plane ℝ) ≃ₗ[ℂ] Plane ℂ,
    (∀ (c : ℂ) (v : Plane ℝ) (i : Fin 2), e (c ⊗ₜ[ℝ] v) i = c * (v i : ℂ)) ∧
    (∀ (s t : ℂ) (r : ℝ) (v : Plane ℝ),
      e ⁅s ⊗ₜ[ℝ] r, t ⊗ₜ[ℝ] v⁆ = rotationAction ℂ (s * (r : ℂ)) (e (t ⊗ₜ[ℝ] v)))) ∧
  (∀ z : ℂ, (rotation ℂ).eigenspace z =
    if z = Complex.I then ℂ ∙ (![1, -Complex.I] : Plane ℂ)
    else if z = -Complex.I then ℂ ∙ (![1, Complex.I] : Plane ℂ)
    else ⊥) ∧
  IsCompl (ℂ ∙ (![1, -Complex.I] : Plane ℂ)) (ℂ ∙ (![1, Complex.I] : Plane ℂ))

/-- Inclusion by coefficient extension, in the actual traceless complex matrices. -/
def splitEmbedding : sl₂ℝ →ₗ⁅ℝ⁆ sl₂ℂ where
  toFun X := ⟨X.val.map Complex.ofReal, by
    change (∑ i, (X.val i i : ℂ)) = 0
    rw [← Complex.ofReal_sum]
    exact_mod_cast (show (∑ i, X.val i i) = 0 from X.property)⟩
  map_add' X Y := Subtype.ext (Matrix.ext fun _ _ => Complex.ofReal_add _ _)
  map_smul' c X := Subtype.ext (Matrix.ext fun _ _ => Complex.ofReal_mul _ _)
  map_lie' {X Y} := Subtype.ext (Matrix.ext fun i j => by
    simp [LieRing.of_associative_ring_bracket, Matrix.mul_apply])

/-- Both concrete real matrix algebras complexify to the same model by their
specified inclusions. Their Killing forms distinguish their real isomorphism classes. -/
def real_forms_type : Prop :=
  IsRealForm (su 2) ∧
  (∃ e : (ℂ ⊗[ℝ] sl₂ℝ) ≃ₗ⁅ℂ⁆ sl₂ℂ,
    ∀ c x, e (c ⊗ₜ[ℝ] x) = c • splitEmbedding x) ∧
  (∀ x : su 2, x ≠ 0 → _root_.killingForm ℝ (su 2) x x < 0) ∧
  (∃ e : sl₂ℝ ≃ₗ[ℝ] (Fin 3 → ℝ),
    ∀ x, _root_.killingForm ℝ sl₂ℝ x x =
      8 * ((e x 0)^2 + (e x 1)^2 - (e x 2)^2)) ∧
  ¬ Nonempty (su 2 ≃ₗ⁅ℝ⁆ sl₂ℝ)

/-- The real diagonal Cartan line in the compact form. -/
def compactCartan : LieSubalgebra ℝ (su 2) where
  carrier := {X | X.val ∈ ClassicalRootsA.cartan 1}
  zero_mem' := (ClassicalRootsA.cartan 1).zero_mem
  add_mem' hX hY := (ClassicalRootsA.cartan 1).add_mem hX hY
  smul_mem' t _ hX := (ClassicalRootsA.cartan 1).smul_mem (t : ℂ) hX
  lie_mem' hX hY := (ClassicalRootsA.cartan 1).lie_mem hX hY

/-- In the diagonal Cartan the root system consists of the opposite coordinate roots.
Their value on the coroot is 2, giving the one-vertex Cartan matrix of type A₁. -/
def complex_type_A1_type : Prop :=
  let H := ClassicalRootsA.cartan 1
  let α := ClassicalRootsA.root 1 0 1
  let h := ClassicalRootsA.coroot 1 0 1
  H.IsCartanSubalgebra ∧
  RootDecomposition.rootSet_value H = {α, -α} ∧ α h = 2

/-- The compact Cartan complexifies to the diagonal Cartan. A nonzero real
element has exactly two nonzero eigenvalues in the complex adjoint action,
the opposite imaginary values given by its upper diagonal entry. -/
def compact_cartan_type : Prop :=
  compactCartan.IsCartanSubalgebra ∧
  (∃ e : (ℂ ⊗[ℝ] compactCartan) ≃ₗ⁅ℂ⁆ ClassicalRootsA.cartan 1,
    ∀ (c : ℂ) (x : compactCartan), (e (c ⊗ₜ[ℝ] x)).val = c • x.val.val) ∧
  ∀ x : compactCartan, x ≠ 0 →
    let t := (x.val.val.val 0 0).im
    t ≠ 0 ∧
    ∀ z : ℂ, z ≠ 0 →
      ((LieAlgebra.ad ℂ sl₂ℂ x.val.val).eigenspace z ≠ ⊥ ↔
        z = 2 * (t : ℂ) * Complex.I ∨ z = -(2 * (t : ℂ) * Complex.I))

end Specs.LieAlgebrasAndRepresentations.NonsplitFieldBoundary
