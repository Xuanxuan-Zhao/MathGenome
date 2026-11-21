import Mathlib.RepresentationTheory.Invariants
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.StdBasis

/-! The characteristic-two example in FR-A09 (Corollary 1.9).
The function model on the finite group is the regular module: the delta
functions are its group basis, and left translation sends δ_h to δ_(gh). -/
namespace AdvancedFiniteGroupRepresentations.ModularMaschke

abbrev G := Equiv.Perm (Fin 2)
abbrev K := ZMod 2
abbrev V := G → K

def s : G := Equiv.swap 0 1

/-- Left regular action, in coefficient coordinates. -/
def regular : Representation K G V where
  toFun g :=
    { toFun v h := v (g⁻¹ * h)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

noncomputable def groupBasis : Module.Basis G K V := Pi.basisFun K G

def eOne : V := Pi.single 1 1
def eSwap : V := Pi.single s 1

def fixedLine : Submodule K V := Submodule.span K {eOne + eSwap}

def IsInvariant (U : Submodule K V) : Prop :=
  ∀ g v, v ∈ U → regular g v ∈ U

/-- The explicit two-element regular-module model and its nonzero fixed generator. -/
def ModelStatement : Prop :=
  (∀ g : G, g = 1 ∨ g = s) ∧
  eOne = groupBasis 1 ∧ eSwap = groupBasis s ∧
  regular s eOne = eSwap ∧ regular s eSwap = eOne ∧
  eOne + eSwap ≠ 0

def FixedSpaceStatement : Prop := regular.invariants = fixedLine

def NoComplementStatement : Prop :=
  ¬ ∃ U : Submodule K V, IsInvariant U ∧ IsCompl fixedLine U

end AdvancedFiniteGroupRepresentations.ModularMaschke
