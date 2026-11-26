import Mathlib.FieldTheory.IsSepClosed
import Mathlib.NumberTheory.LocalField.Basic
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Defs

/-! Brauer vanishing over finite separable extensions of the maximal unramified field. -/

namespace LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer

open ValuativeRel
universe u v w

/-- For finite extensions of local fields the residue extension is automatically
separable. Ramification index one means that the base field already attains every
value of the extended valuation. -/
def IsUnramified (F : Type u) (E : Type v) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [Algebra F E] : Prop :=
  FiniteDimensional F E ∧ Algebra.IsSeparable F E ∧
    ∃ (r : ValuativeRel E) (T : TopologicalSpace E),
      letI : ValuativeRel E := r
      letI : TopologicalSpace E := T
      IsNonarchimedeanLocalField E ∧ ValuativeExtension F E ∧
        Function.Surjective (fun x : F => valuation E (algebraMap F E x))

/-- The compositum of the finite unramified subextensions in a fixed separable closure. -/
noncomputable def maximalUnramified (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    IntermediateField F (SeparableClosure F) :=
  ⨆ E : {E : IntermediateField F (SeparableClosure F) // IsUnramified F E}, E.val

/-- Membership in the maximal unramified field amounts to membership in a
finite unramified subextension. -/
def MaximalUnramifiedIsUnion : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {x : SeparableClosure F},
    x ∈ maximalUnramified F ↔
      ∃ E : IntermediateField F (SeparableClosure F), IsUnramified F E ∧ x ∈ E

/-- Every central simple algebra over a finite separable extension of the maximal
unramified extension is split. This is the vanishing of the Brauer group. -/
def BrauerVanishing : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (M : Type v) [Field M] [Algebra (maximalUnramified F) M]
    [FiniteDimensional (maximalUnramified F) M] [Algebra.IsSeparable (maximalUnramified F) M]
    (A : Type w) [Ring A] [Algebra M A],
    _root_.Specs.RM03.CSA.isCentralSimple M A → _root_.Specs.RM03.CSA.isSplit M A

/-- There is exactly one class in the Brauer quotient of each such extension. -/
def BrauerGroupTrivial : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (M : Type v) [Field M] [Algebra (maximalUnramified F) M]
    [FiniteDimensional (maximalUnramified F) M] [Algebra.IsSeparable (maximalUnramified F) M],
    ∃ z : BrauerGroup.{v, max v w} M, ∀ x, x = z

end LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer
