import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SimpleIdealDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Enveloping
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! LA-C02, source lines 1187–1257. The coefficient field is arbitrary of
characteristic zero. Nontrivial means that the action is not the trivial action;
irreducibility separately implies the carrier is nonzero. The support is the
Killing-orthogonal complementary ideal to the representation kernel. -/

noncomputable section
open scoped Classical
attribute [local instance 100] LieRing.ofAssociativeRing
universe u v w t
namespace LieAlgebrasAndRepresentations.ModuleCasimir
open _root_.Shared.Lie
attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) (G : Type v) (M : Type w)
  [Field k] [LieRing G] [LieAlgebra k G]
  [AddCommGroup M] [Module k M] [LieRingModule G M] [LieModule k G M]

abbrev image := (LieModule.toEnd k G M).range
abbrev support : LieIdeal k G := (LieModule.toEnd k G M).ker.killingCompl
noncomputable def action : U k G →ₐ[k] Module.End k M :=
  representationEquiv k G M (LieModule.toEnd k G M)

noncomputable def casimirSum (I : LieIdeal k G)
    (hB : (LieModule.traceForm k I M).Nondegenerate)
    {ι : Type t} [Fintype ι] (b : Module.Basis ι k I) : U k G :=
  ∑ i, inclusion k G (b i : G) *
    inclusion k G ((LieModule.traceForm k I M).dualBasis hB b i : G)

/-- The entire conclusion for a specified element, including its actual action
on the given carrier and on the augmentation (trivial) module. -/
def CasimirProperties (C : U k G) : Prop :=
  C ∈ Subalgebra.center k (U k G) ∧
  augmentation k G C = 0 ∧
  LinearMap.trace k M (action k G M C) = (Module.finrank k (image k G M) : k) ∧
  Function.Bijective (action k G M C)

end LieAlgebrasAndRepresentations.ModuleCasimir

namespace Specs.LieAlgebrasAndRepresentations.ModuleCasimir
open _root_.LieAlgebrasAndRepresentations.ModuleCasimir
open SolvableRadical (IsSemisimple_value)


def image_traceForm_nondegenerate_type : Prop :=
  ∀ (k : Type u) (G : Type v) (M : Type w)
  [Field k] [CharZero k] [LieRing G] [LieAlgebra k G] [FiniteDimensional k G]
  [AddCommGroup M] [Module k M] [FiniteDimensional k M]
  [LieRingModule G M] [LieModule k G M],
  IsSemisimple_value k G → (LieModule.traceForm k (image k G M) M).Nondegenerate

def support_isCompl_type : Prop :=
  ∀ (k : Type u) (G : Type v) (M : Type w)
  [Field k] [CharZero k] [LieRing G] [LieAlgebra k G] [FiniteDimensional k G]
  [AddCommGroup M] [Module k M] [FiniteDimensional k M]
  [LieRingModule G M] [LieModule k G M],
  IsSemisimple_value k G → IsCompl (LieModule.toEnd k G M).ker (support k G M)

def support_traceForm_nondegenerate_type : Prop :=
  ∀ (k : Type u) (G : Type v) (M : Type w)
  [Field k] [CharZero k] [LieRing G] [LieAlgebra k G] [FiniteDimensional k G]
  [AddCommGroup M] [Module k M] [FiniteDimensional k M]
  [LieRingModule G M] [LieModule k G M],
  IsSemisimple_value k G → (LieModule.traceForm k (support k G M) M).Nondegenerate

/-- All finite bases are allowed, so no choice of coordinates is built into the result. -/
def casimir_basis_independent_type : Prop :=
  ∀ (k : Type u) (G : Type v) (M : Type w)
  [Field k] [CharZero k] [LieRing G] [LieAlgebra k G] [FiniteDimensional k G]
  [AddCommGroup M] [Module k M] [FiniteDimensional k M]
  [LieRingModule G M] [LieModule k G M],
  ∀ (I : LieIdeal k G) (hB : (LieModule.traceForm k I M).Nondegenerate)
    {ι : Type t} {κ : Type t} [Fintype ι] [Fintype κ]
    (b : Module.Basis ι k I) (c : Module.Basis κ k I),
    casimirSum k G M I hB b = casimirSum k G M I hB c

def module_casimir_type : Prop :=
  ∀ (k : Type u) (G : Type v) (M : Type w)
  [Field k] [CharZero k] [LieRing G] [LieAlgebra k G] [FiniteDimensional k G]
  [AddCommGroup M] [Module k M] [FiniteDimensional k M]
  [LieRingModule G M] [LieModule k G M] [LieModule.IsIrreducible k G M],
  IsSemisimple_value k G → ¬ LieModule.IsTrivial G M →
  ∃ hB : (LieModule.traceForm k (support k G M) M).Nondegenerate,
    ∀ {ι : Type t} [Fintype ι] (b : Module.Basis ι k (support k G M)),
      CasimirProperties k G M (casimirSum k G M (support k G M) hB b)

/-- The source's existence statement, without a basis parameter. -/
def exists_module_casimir_type : Prop :=
  ∀ (k : Type u) (G : Type v) (M : Type w)
  [Field k] [CharZero k] [LieRing G] [LieAlgebra k G] [FiniteDimensional k G]
  [AddCommGroup M] [Module k M] [FiniteDimensional k M]
  [LieRingModule G M] [LieModule k G M] [LieModule.IsIrreducible k G M],
  IsSemisimple_value k G → ¬ LieModule.IsTrivial G M →
    ∃ C : _root_.Shared.Lie.U k G, CasimirProperties k G M C

def module_casimir_scalar_type : Prop :=
  ∀ (k : Type u) (G : Type v) (M : Type w)
  [Field k] [CharZero k] [LieRing G] [LieAlgebra k G] [FiniteDimensional k G]
  [AddCommGroup M] [Module k M] [FiniteDimensional k M]
  [LieRingModule G M] [LieModule k G M] [IsAlgClosed k] [LieModule.IsIrreducible k G M],
  IsSemisimple_value k G → ¬ LieModule.IsTrivial G M →
  ∀ (hB : (LieModule.traceForm k (support k G M) M).Nondegenerate)
    {ι : Type t} [Fintype ι] (b : Module.Basis ι k (support k G M)),
    let c : k := (Module.finrank k (image k G M) : k) / (Module.finrank k M : k)
    c ≠ 0 ∧ action k G M (casimirSum k G M (support k G M) hB b) =
      c • (LinearMap.id : Module.End k M)

end Specs.LieAlgebrasAndRepresentations.ModuleCasimir
