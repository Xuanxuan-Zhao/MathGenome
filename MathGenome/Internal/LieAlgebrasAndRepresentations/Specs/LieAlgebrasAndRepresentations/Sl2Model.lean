import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
LA-U05, source notes/005/lie-algebras-and-representations.tex, lines 1109–1121.
The canonical model is the Lie subalgebra of trace-zero matrices, with its
inherited commutator. The definitions and bracket relations make sense over
any field; simplicity is asserted over every characteristic-zero field.
-/

universe u

namespace Specs.LieAlgebrasAndRepresentations.Sl2Model

/-- Shared canonical objects, independent of the candidate implementation. -/
abbrev Model (k : Type u) [Field k] := LieAlgebra.SpecialLinear.sl (Fin 2) k

def E (k : Type u) [Field k] : Model k :=
  LieAlgebra.SpecialLinear.single 0 1 (by decide) 1

def F (k : Type u) [Field k] : Model k :=
  LieAlgebra.SpecialLinear.single 1 0 (by decide) 1

def H (k : Type u) [Field k] : Model k :=
  LieAlgebra.SpecialLinear.singleSubSingle 0 1 1

def sl2_type := ∀ (k : Type u) [Field k], Type u
def sl2_value (k : Type u) [Field k] : Type u := Model k

def sl2_e_type := ∀ (k : Type u) [Field k], Model k
def sl2_e_value (k : Type u) [Field k] : Model k := E k

def sl2_f_type := ∀ (k : Type u) [Field k], Model k
def sl2_f_value (k : Type u) [Field k] : Model k := F k

def sl2_h_type := ∀ (k : Type u) [Field k], Model k
def sl2_h_value (k : Type u) [Field k] : Model k := H k

/-- The displayed matrix representatives, in the source's order. -/
def sl2_matrices_type : Prop :=
  ∀ (k : Type u) [Field k],
    (E k).val = !![0, 1; 0, 0] ∧
    (F k).val = !![0, 0; 1, 0] ∧
    (H k).val = !![1, 0; 0, -1]

/-- Existence of a basis with exactly the three specified matrix vectors. -/
def sl2_basis_type : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ b : Module.Basis (Fin 3) k (Model k), b 0 = E k ∧ b 1 = F k ∧ b 2 = H k

def sl2_relations_type : Prop :=
  ∀ (k : Type u) [Field k],
    ⁅H k, E k⁆ = (2 : k) • E k ∧
    ⁅H k, F k⁆ = (-2 : k) • F k ∧
    ⁅E k, F k⁆ = H k

def sl2_nonabelian_type : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k], ¬IsLieAbelian (Model k)

/-- Mathlib's simplicity includes both the ideal dichotomy and nonabelianness. -/
def sl2_simple_type : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k], LieAlgebra.IsSimple k (Model k)

end Specs.LieAlgebrasAndRepresentations.Sl2Model
