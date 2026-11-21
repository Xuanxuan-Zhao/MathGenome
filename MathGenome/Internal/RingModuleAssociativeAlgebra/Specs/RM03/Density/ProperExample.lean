import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Density.FiniteQuotient
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Density.FiniteRankModule
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! The proper dense image in RM03-C03.03. -/

universe u v

namespace RM03.Specs.Density.ProperExample

open FiniteRankModule

set_option linter.checkUnivs false in
def finiteTopologyType :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V],
    TopologicalSpace (Module.End k V)

/-- The topology induced by the inclusion into the product of discrete copies of V. -/
def finiteTopologyValue : finiteTopologyType :=
  fun k V _ _ _ ↦
    letI : TopologicalSpace V := ⊥
    TopologicalSpace.induced (fun T : Module.End k V ↦ (T : V → V)) inferInstance

set_option linter.checkUnivs false in
def shiftType :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V],
    Module.Basis ℕ k V → Module.End k V

noncomputable def shiftValue : shiftType :=
  fun k _ _ _ _ b ↦ b.constr k (fun i ↦ b (i + 1))

def shift_applyType : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]
    (b : Module.Basis ℕ k V) (i : ℕ), shiftValue k V b (b i) = b (i + 1)

def shift_sub_scalar_infinite_rankType : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]
    (b : Module.Basis ℕ k V) (c : k),
    ¬ FiniteDimensional k (shiftValue k V b - algebraMap k (Module.End k V) c).range

def shift_not_memType : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]
    (b : Module.Basis ℕ k V), shiftValue k V b ∉ scalarPlusFiniteRankValue k V

def scalarPlusFiniteRank_lt_topType : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]
    (_b : Module.Basis ℕ k V), scalarPlusFiniteRankValue k V < ⊤

/-- The canonical action, viewed through the commutant identification, has dense image
equal to the given subalgebra. The identification leaves evaluation on each vector intact. -/
def action_image_denseType : Prop :=
  ∀ (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]
    (_b : Module.Basis ℕ k V),
    let R := scalarPlusFiniteRankValue k V
    letI : TopologicalSpace (Module.End k V) := finiteTopologyValue k V
    ∃ e : RightEndValue R V ≃ₐ[k] Module.End k V,
      (∀ (T : RightEndValue R V) (x : V), e T x = T x) ∧
      e '' Set.range (actionValue R V) = (R : Set (Module.End k V)) ∧
      Dense (R : Set (Module.End k V))

end RM03.Specs.Density.ProperExample
