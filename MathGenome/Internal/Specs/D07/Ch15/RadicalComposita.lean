import MathGenome.Internal.Specs.D07.Ch15.RadicalDefinition
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
The three assertions of paper.tex:4370–4377, `lem:radical-composita`.
All fields use specified compatible embeddings. Radical means a finite tower
of simple adjunctions with a positive power in the preceding field, exactly
as in the upstream specification. No separability or characteristic condition
is present. A supremum is the compositum in the specified ambient field.
-/

universe u v w t
namespace Specs.D07.Ch15.RadicalComposita
open Specs.D07.Ch15.RadicalDefinition

def StepMap : Prop :=
  ∀ (K : Type u) (Ω : Type v) (Ω' : Type w) [Field K] [Field Ω] [Field Ω']
    [Algebra K Ω] [Algebra K Ω'] [Algebra.IsAlgebraic K Ω]
    [Algebra.IsAlgebraic K Ω'] (σ : Ω →ₐ[K] Ω') (E F : IntermediateField K Ω),
    radicalStepValue K Ω E F → radicalStepValue K Ω' (E.map σ) (F.map σ)

def TowerMap : Prop :=
  ∀ (K : Type u) (Ω : Type v) (Ω' : Type w) [Field K] [Field Ω] [Field Ω']
    [Algebra K Ω] [Algebra K Ω'] [Algebra.IsAlgebraic K Ω]
    [Algebra.IsAlgebraic K Ω'] (σ : Ω →ₐ[K] Ω') (r : ℕ)
    (T : Fin (r + 1) → IntermediateField K Ω),
    radicalTowerValue K Ω r T →
      radicalTowerValue K Ω' r (fun i => (T i).map σ)

def ExtensionMap : Prop :=
  ∀ (K : Type u) (Ω : Type v) (Ω' : Type w) [Field K] [Field Ω] [Field Ω']
    [Algebra K Ω] [Algebra K Ω'] [Algebra.IsAlgebraic K Ω]
    [Algebra.IsAlgebraic K Ω'] (σ : Ω →ₐ[K] Ω') (E : IntermediateField K Ω),
    radicalExtensionValue K Ω E → radicalExtensionValue K Ω' (E.map σ)

/-- An embedding need only be defined on the final field of the tower. -/
def ExtensionImage : Prop :=
  ∀ (K : Type u) (Ω : Type v) (Ω' : Type w) [Field K] [Field Ω] [Field Ω']
    [Algebra K Ω] [Algebra K Ω'] [Algebra.IsAlgebraic K Ω]
    [Algebra.IsAlgebraic K Ω'] (E : IntermediateField K Ω) (σ : E →ₐ[K] Ω'),
    radicalExtensionValue K Ω E → radicalExtensionValue K Ω' σ.fieldRange

def Compositum : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (E F : IntermediateField K Ω),
    radicalExtensionValue K Ω E → radicalExtensionValue K Ω F →
      radicalExtensionValue K Ω (E ⊔ F)

/-- Includes an empty family, whose compositum is the base field. -/
def FiniteCompositum : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (ι : Type t) [Finite ι]
    (E : ι → IntermediateField K Ω),
    (∀ i, radicalExtensionValue K Ω (E i)) → radicalExtensionValue K Ω (⨆ i, E i)

def ExtensionFinite : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (E : IntermediateField K Ω),
    radicalExtensionValue K Ω E → FiniteDimensional K E

/-- The actual normal closure, not an arbitrary normal overextension. The
library predicate also records splitting of every minimal polynomial and
that its roots generate the closure. Algebraic closedness is used only here,
where the source takes the normal closure in the fixed algebraic closure. -/
def NormalClosure : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] (E : IntermediateField K Ω),
    radicalExtensionValue K Ω E →
      let N := IntermediateField.normalClosure K E Ω
      FiniteDimensional K N ∧ Normal K N ∧ radicalExtensionValue K Ω N ∧
        E ≤ N ∧ IsNormalClosure K E N

end Specs.D07.Ch15.RadicalComposita
