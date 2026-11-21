import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.VectorRepresentation
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation

/-! The seven indexed nonzero binary columns in paper.tex W74.
The order is a₁,a₂,a₃,d,f,g,h. The characteristic criterion uses an
ambient space in the universe of K; its necessity statement below also
quantifies over representations in arbitrary universes.
-/
namespace FiniteCombinatorics.Matroid
open Set
universe u w

/-- The seven original point indices are retained, even after changing fields. -/
abbrev FanoPoint := Fin 7

def fanoColumns : FanoPoint → Fin 3 → ZMod 2 :=
  ![![1,0,0], ![0,1,0], ![0,0,1], ![1,1,0], ![1,0,1], ![0,1,1], ![1,1,1]]

namespace Expected

def fanoMatroid : _root_.Matroid FanoPoint :=
  vectorMatroid (ZMod 2) univ finite_univ fanoColumns

def fanoMatroidType := _root_.Matroid FanoPoint

/-- Enumeration is a bijection onto precisely the seven nonzero binary vectors. -/
def fanoColumnsComplete : Prop :=
  Function.Injective fanoColumns ∧ Set.range fanoColumns = {x | x ≠ 0}

def fanoRepresentableOfCharTwo : Prop :=
  ∀ (K : Type u) [Field K], ringChar K = 2 →
    Representable.{0,u,u} K fanoMatroid

def fanoRepresentationCharTwo : Prop :=
  ∀ (K : Type u) [Field K] {V : Type w} [AddCommGroup V] [Module K V]
    (v : FanoPoint → V), Represents K fanoMatroid v → ringChar K = 2

def fanoRepresentableIff : Prop :=
  ∀ (K : Type u) [Field K],
    Representable.{0,u,u} K fanoMatroid ↔ ringChar K = 2

end Expected
end FiniteCombinatorics.Matroid
