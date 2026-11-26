import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open scoped TensorProduct

namespace LinearAlgebraicGroups

universe u v w

/-- A right coaction of a coalgebra on a vector space. -/
structure RightComodule (k : Type u) (C : Type v) (V : Type w)
    [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]
    [AddCommGroup V] [Module k V] where
  coaction : V →ₗ[k] V ⊗[k] C
  coassoc (x : V) :
    TensorProduct.assoc k V C C (coaction.rTensor C (coaction x)) =
      (Coalgebra.comul (R := k) (A := C)).lTensor V (coaction x)
  counit (x : V) :
    TensorProduct.rid k V ((Coalgebra.counit (R := k) (A := C)).lTensor V (coaction x)) = x

namespace RightComodule

variable {k : Type u} {C : Type v} {V : Type w}
    [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]
    [AddCommGroup V] [Module k V]

/-- The comultiplication makes a coalgebra a right comodule over itself. -/
def regular : RightComodule k C C where
  coaction := Coalgebra.comul
  coassoc := Coalgebra.coassoc_apply
  counit x := by rw [Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]

/-- The ambient coaction of every element of the subspace lies in the image of its tensor
inclusion. -/
def IsSubcomodule (ρ : RightComodule k C V) (W : Submodule k V) : Prop :=
  ∀ x : W, ρ.coaction (x : V) ∈ LinearMap.range (W.subtype.rTensor C)

/-- The family of finite-dimensional subcomodules, indexed by their underlying subspaces. -/
def FiniteSubcomodule (ρ : RightComodule k C V) :=
  { W : Submodule k V // ρ.IsSubcomodule W ∧ FiniteDimensional k W }

end RightComodule

namespace Specs

def isSubcomodule_iff_exists_coaction : Prop :=
  ∀ {k : Type u} {C : Type v} {V : Type w}
    [Field k] [AddCommGroup C] [Module k C] [AddCommGroup V] [Module k V] [Coalgebra k C]
    (ρ : RightComodule k C V) (W : Submodule k V), ρ.IsSubcomodule W ↔
    ∃ σ : RightComodule k C W,
      (W.subtype.rTensor C).comp σ.coaction = ρ.coaction.comp W.subtype

def exists_finiteSubcomodule : Prop :=
  ∀ {k : Type u} {C : Type v} {V : Type w}
    [Field k] [AddCommGroup C] [Module k C] [AddCommGroup V] [Module k V] [Coalgebra k C]
    (ρ : RightComodule k C V) (x : V),
    ∃ W : ρ.FiniteSubcomodule, x ∈ W.val

def directed_finiteSubcomodules : Prop :=
  ∀ {k : Type u} {C : Type v} {V : Type w}
    [Field k] [AddCommGroup C] [Module k C] [AddCommGroup V] [Module k V] [Coalgebra k C]
    (ρ : RightComodule k C V),
    Directed (· ≤ ·) (fun W : ρ.FiniteSubcomodule ↦ W.val)

def iUnion_finiteSubcomodules : Prop :=
  ∀ {k : Type u} {C : Type v} {V : Type w}
    [Field k] [AddCommGroup C] [Module k C] [AddCommGroup V] [Module k V] [Coalgebra k C]
    (ρ : RightComodule k C V),
    (⋃ W : ρ.FiniteSubcomodule, (W.val : Set V)) = Set.univ

def exists_finiteSubcomodule_containing : Prop :=
  ∀ {k : Type u} {C : Type v} {V : Type w}
    [Field k] [AddCommGroup C] [Module k C] [AddCommGroup V] [Module k V] [Coalgebra k C]
    (ρ : RightComodule k C V) (s : Set V), s.Finite →
    ∃ W : ρ.FiniteSubcomodule, s ⊆ (W.val : Set V)

def exists_finiteSubcomodule_containing_range : Prop :=
  ∀ {k : Type u} {C : Type v} {V : Type w}
    [Field k] [AddCommGroup C] [Module k C] [AddCommGroup V] [Module k V] [Coalgebra k C]
    (ρ : RightComodule k C V) {ι : Type*} [Finite ι] (f : ι → V),
    ∃ W : ρ.FiniteSubcomodule, ∀ i, f i ∈ W.val

end Specs
end LinearAlgebraicGroups
