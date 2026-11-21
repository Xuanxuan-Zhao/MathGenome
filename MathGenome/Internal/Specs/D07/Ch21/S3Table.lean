import MathGenome.Internal.Specs.D07.Ch21.HomPairing
import MathGenome.Internal.Specs.D07.Ch17.CharacterDirectSum
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Notation

/-! The complete S₃ example, paper.tex:6464–6500. Coordinates 0,1,2
correspond to the paper's 1,2,3, and permutations compose rightmost first.
The representation of the plane and its basis are existentially constructed,
not assumed. Completeness ranges over arbitrary dimensional representations. -/
namespace Specs.D07.Ch21.S3Table
noncomputable section
open scoped BigOperators

abbrev S3 := Equiv.Perm (Fin 3)
abbrev V3 := Fin 3 → ℂ
abbrev s : S3 := Equiv.swap 0 1
abbrev a : S3 := Equiv.swap 0 1 * Equiv.swap 1 2

def coordinateSum : V3 →ₗ[ℂ] ℂ where
  toFun v := ∑ i, v i
  map_add' _ _ := Finset.sum_add_distrib
  map_smul' c v := by simp [Finset.mul_sum]

def plane : Submodule ℂ V3 := coordinateSum.ker

def line : Submodule ℂ V3 := Submodule.span ℂ {fun _ => (1 : ℂ)}

def permRep : Representation ℂ S3 V3 where
  toFun g :=
    { toFun := fun v i => v (g⁻¹ i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext; rfl
  map_mul' g h := by ext; rfl

abbrev triv := Specs.D07.Ch17.Examples.trivialValue ℂ S3 ℂ
abbrev sign := Specs.D07.Ch17.Examples.signValue ℂ (Fin 3)
abbrev χ {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ S3 V) :=
  Specs.D07.Ch17.Characters.characterValue ℂ S3 V ρ

/-- Class sizes, exhaustion, and distinctness are all part of the assertion. -/
def Classes : Prop :=
  Fintype.card S3 = 6 ∧
  (∀ g : S3, IsConj g 1 ∨ IsConj g s ∨ IsConj g a) ∧
  ¬ IsConj (1 : S3) s ∧ ¬ IsConj (1 : S3) a ∧ ¬ IsConj s a ∧
  Nat.card {g : S3 // IsConj g 1} = 1 ∧
  Nat.card {g : S3 // IsConj g s} = 3 ∧
  Nat.card {g : S3 // IsConj g a} = 2

/-- The stated mean-coordinate splitting includes uniqueness and the trivial
line action. Fixed-point character counts use the actual permutation action. -/
def Geometry : Prop :=
  (∀ g v, v ∈ plane → permRep g v ∈ plane) ∧
  (∀ g v, v ∈ line → permRep g v = v) ∧
  IsCompl line plane ∧
  (∀ v : V3,
    (fun _ : Fin 3 => coordinateSum v / 3) ∈ line ∧
    (v - fun _ : Fin 3 => coordinateSum v / 3) ∈ plane ∧
    ∃! p : line × plane, (p.1 : V3) + (p.2 : V3) = v) ∧
  (∀ g : S3, χ permRep g = (Nat.card {i : Fin 3 // g i = i} : ℂ)) ∧
  χ permRep 1 = 3 ∧ χ permRep s = 1 ∧ χ permRep a = 0

/-- Every row comes from a genuine representation; the last row is the
restriction to the specified plane, with the specified ordered basis. -/
def CompleteTable : Prop :=
  Classes ∧ Geometry ∧
  ∃ (ρ : Representation ℂ S3 plane) (b : Module.Basis (Fin 2) ℂ plane),
    (∀ g v i, (ρ g v : V3) i = (v : V3) (g⁻¹ i)) ∧
    ((b 0 : V3) = ![1, 0, -1]) ∧ ((b 1 : V3) = ![0, 1, -1]) ∧
    LinearMap.toMatrix b b (ρ s) = !![0, 1; 1, 0] ∧
    LinearMap.toMatrix b b (ρ a) = !![-1, -1; 1, 0] ∧
    Module.finrank ℂ plane = 2 ∧
    (χ triv 1 = 1 ∧ χ triv s = 1 ∧ χ triv a = 1) ∧
    (χ sign 1 = 1 ∧ χ sign s = -1 ∧ χ sign a = 1) ∧
    (χ ρ 1 = 2 ∧ χ ρ s = 0 ∧ χ ρ a = -1) ∧
    (∀ g, χ permRep g = χ triv g + χ ρ g) ∧
    Specs.D07.Ch21.HomPairing.pairingValue S3 (χ ρ) (χ ρ) = 1 ∧
    Representation.IsIrreducible triv ∧ Representation.IsIrreducible sign ∧
    Representation.IsIrreducible ρ ∧
    ¬ Nonempty (triv.Equiv sign) ∧ ¬ Nonempty (triv.Equiv ρ) ∧
    ¬ Nonempty (sign.Equiv ρ) ∧
    (Module.finrank ℂ ℂ)^2 + (Module.finrank ℂ ℂ)^2 +
      (Module.finrank ℂ plane)^2 = Fintype.card S3 ∧
    ∀ (V : Type*) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ S3 V),
      Representation.IsIrreducible τ →
      FiniteDimensional ℂ V ∧
      (Nonempty (triv.Equiv τ) ∨ Nonempty (sign.Equiv τ) ∨ Nonempty (ρ.Equiv τ))

end
end Specs.D07.Ch21.S3Table
