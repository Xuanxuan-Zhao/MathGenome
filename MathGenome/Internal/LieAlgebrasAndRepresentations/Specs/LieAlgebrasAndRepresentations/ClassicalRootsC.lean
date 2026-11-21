import Mathlib.Algebra.Lie.Classical
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.SupIndep
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Basic.Complex.Basic

/-!
LA-D08-C, notes/005/lie-algebras-and-representations.tex:1930–1983.
We use Mathlib's symplectic Lie algebra, in the ordered coordinates
`Fin n ⊕ Fin n`. The parameter space identifies the displayed diagonal
Cartan with ℂⁿ. Its dual is used to index ordinary simultaneous eigenspaces.
The Euclidean form on root coordinates is extended complex bilinearly.
All definitions also make sense at rank zero; the assertions in particular
apply for every n ≥ 1, without additional hypotheses.
-/

namespace Specs.LieAlgebrasAndRepresentations.ClassicalRootsC

open Matrix

noncomputable section
attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

abbrev V (n : ℕ) := Fin n → ℂ
abbrev Mat (n : ℕ) := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ
abbrev Weight (n : ℕ) := Module.Dual ℂ (V n)
abbrev sp (n : ℕ) := LieAlgebra.Symplectic.sp (Fin n) ℂ

def eps {n : ℕ} (i : Fin n) : Weight n := LinearMap.proj i

def signed {n : ℕ} : Fin n ⊕ Fin n → Weight n
  | Sum.inl i => eps i
  | Sum.inr i => -eps i

def diagonal {n : ℕ} (t : V n) : Mat n := Matrix.diagonal (Sum.elim t (-t))

def diagonalMap (n : ℕ) : V n →ₗ[ℂ] Mat n where
  toFun := diagonal
  map_add' t u := by ext (i | i) (j | j) <;> simp [diagonal, Matrix.diagonal] <;> split_ifs <;> simp_all [add_comm]
  map_smul' c t := by ext (i | i) (j | j) <;> simp [diagonal, Matrix.diagonal]

/-- The displayed diagonal Cartan, as a subspace of the matrix algebra. -/
def cartan (n : ℕ) : Submodule ℂ (Mat n) := LinearMap.range (diagonalMap n)

/-- Ordinary root spaces, with the Cartan parametrized by t ↦ diag(t,-t).
The symplectic condition is part of this definition, not an assumption
on an arbitrary ambient matrix. -/
def rootSpace {n : ℕ} (α : Weight n) : Submodule ℂ (Mat n) where
  carrier := {X | X ∈ sp n ∧ ∀ t : V n, ⁅diagonal t, X⁆ = α t • X}
  zero_mem' := by simp
  add_mem' := by
    rintro X Y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨(sp n).add_mem hx hy, fun t => by rw [lie_add, hx' t, hy' t, smul_add]⟩
  smul_mem' := by
    rintro c X ⟨hx, hx'⟩
    exact ⟨(sp n).smul_mem c hx, fun t => by rw [lie_smul, hx' t, smul_comm]⟩

def rootSet (n : ℕ) : Set (Weight n) := {α | α ≠ 0 ∧ rootSpace α ≠ ⊥}

def listedRoots (n : ℕ) : Set (Weight n) := {α |
  (∃ i, α = (2 : ℂ) • eps i ∨ α = -((2 : ℂ) • eps i)) ∨
  ∃ i j : Fin n, i < j ∧
    (α = eps i - eps j ∨ α = -(eps i - eps j) ∨
      α = eps i + eps j ∨ α = -(eps i + eps j))}

/-- E_ij in A, together with the forced entry -E_ji in the last block. -/
def aRoot {n : ℕ} (i j : Fin n) : Mat n :=
  fromBlocks (Matrix.single i j 1) 0 0 (-Matrix.single j i 1)

/-- The symmetric upper-right block for a short root. -/
def bRoot {n : ℕ} (i j : Fin n) : Mat n :=
  fromBlocks 0 (Matrix.single i j 1 + Matrix.single j i 1) 0 0

def cRoot {n : ℕ} (i j : Fin n) : Mat n := (bRoot i j)ᵀ

def bLong {n : ℕ} (i : Fin n) : Mat n := fromBlocks 0 (Matrix.single i i 1) 0 0

def cLong {n : ℕ} (i : Fin n) : Mat n := (bLong i)ᵀ

def coordinates {n : ℕ} (α : Weight n) : V n := fun i => α (Pi.single i 1)

/-- Complex bilinear extension of the Euclidean coordinate form. -/
def euclidean {n : ℕ} (α β : Weight n) : ℂ :=
  ∑ i, coordinates α i * coordinates β i

/-- The Euclidean coroot, embedded in the displayed diagonal Cartan. -/
def coroot {n : ℕ} (α : Weight n) : Mat n :=
  diagonal (fun i => (2 / euclidean α α) * coordinates α i)

/-- Defining symplectic equation in the specified block coordinates. -/
def block_form_type : Prop := ∀ (n : ℕ) (A B C D : Matrix (Fin n) (Fin n) ℂ),
  fromBlocks A B C D ∈ sp n ↔ Cᵀ = C ∧ Bᵀ = B ∧ D = -Aᵀ

def diagonal_mem_type : Prop := ∀ (n : ℕ) (t : V n), diagonal t ∈ sp n

/-- A single exact formula also describes absent root spaces. -/
def rootSpace_entries_type : Prop := ∀ (n : ℕ) (α : Weight n) (X : Mat n),
  X ∈ rootSpace α ↔ X ∈ sp n ∧ ∀ a b, X a b ≠ 0 → α = signed a - signed b

def zero_space_type : Prop := ∀ n : ℕ, rootSpace (0 : Weight n) = cartan n

def roots_type : Prop := ∀ n : ℕ, rootSet n = listedRoots n

def a_space_type : Prop := ∀ (n : ℕ) (i j : Fin n), i ≠ j →
  rootSpace (eps i - eps j) = Submodule.span ℂ {aRoot i j}

def b_space_type : Prop := ∀ (n : ℕ) (i j : Fin n), i ≠ j →
  rootSpace (eps i + eps j) = Submodule.span ℂ {bRoot i j}

def c_space_type : Prop := ∀ (n : ℕ) (i j : Fin n), i ≠ j →
  rootSpace (-(eps i + eps j)) = Submodule.span ℂ {cRoot i j}

def b_long_space_type : Prop := ∀ (n : ℕ) (i : Fin n),
  rootSpace ((2 : ℂ) • eps i) = Submodule.span ℂ {bLong i}

def c_long_space_type : Prop := ∀ (n : ℕ) (i : Fin n),
  rootSpace (-((2 : ℂ) • eps i)) = Submodule.span ℂ {cLong i}

/-- Independence and spanning give the full root decomposition. -/
def independent_type : Prop := ∀ n : ℕ, iSupIndep (@rootSpace n)

def spanning_type : Prop := ∀ n : ℕ, (⨆ α : Weight n, rootSpace α) = (sp n).toSubmodule

/-- Opposite-root brackets fix the coroot normalization in the original Lie algebra. -/
def a_coroot_type : Prop := ∀ (n : ℕ) (i j : Fin n), i ≠ j →
  ⁅aRoot i j, aRoot j i⁆ = coroot (eps i - eps j) ∧
  coroot (eps i - eps j) = diagonal (Pi.single i 1 - Pi.single j 1)

def b_coroot_type : Prop := ∀ (n : ℕ) (i j : Fin n), i ≠ j →
  ⁅bRoot i j, cRoot i j⁆ = coroot (eps i + eps j) ∧
  coroot (eps i + eps j) = diagonal (Pi.single i 1 + Pi.single j 1)

def long_coroot_type : Prop := ∀ (n : ℕ) (i : Fin n),
  ⁅bLong i, cLong i⁆ = coroot ((2 : ℂ) • eps i) ∧
  coroot ((2 : ℂ) • eps i) = diagonal (Pi.single i 1)

def neg_coroot_type : Prop := ∀ (n : ℕ) (α : Weight n), coroot (-α) = -coroot α

/-- The parameter computation is the ordinary root decomposition of the
actual displayed Cartan subalgebra inside sp, transported by a linear
isomorphism whose ambient matrix is exactly diag(t,-t). -/
def cartan_transport_type : Prop := ∀ n : ℕ,
  ∃ H : LieSubalgebra ℂ (sp n), H.IsCartanSubalgebra ∧
    ∃ e : V n ≃ₗ[ℂ] H,
      (∀ t : V n, ((e t : sp n) : Mat n) = diagonal t) ∧
      ∀ α : Weight n,
        ((LieModule.weightSpace (sp n) (fun h : H => α (e.symm h))).toSubmodule.map
          (sp n).toSubmodule.subtype) = rootSpace α

end
end Specs.LieAlgebrasAndRepresentations.ClassicalRootsC
