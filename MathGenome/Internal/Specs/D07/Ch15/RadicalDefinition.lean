import MathGenome.Internal.Specs.D07.Ch12.AdjoinDefinition
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Order.Fin.Basic

/-!
Independent specification of K07.15.radical_definition (paper.tex:4366–4369).
The `Algebra K Ω` is the specified embedding, and `Algebra.IsAlgebraic K Ω`
expresses the source's algebraic overfield. No algebraic closedness,
characteristic, separability, or roots-of-unity assumption is imposed.

All fields in a tower are intermediate fields in the same Ω. A sequence with
`r` steps has domain `Fin (r + 1)`; the base field is its embedded image `⊥`.
The union in the adjunction below expresses exactly `E(a)` inside Ω. Positive
exponents include 1, field inclusions need not be strict, and `r = 0` is allowed.
The predicates are specified by their values, not by assumed certificates.
-/

universe u v

namespace Specs.D07.Ch15.RadicalDefinition

def RadicalStepType : Type (max u v + 1) :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω], IntermediateField K Ω → IntermediateField K Ω → Prop

def radicalStepValue : RadicalStepType.{u, v} :=
  fun K Ω _ _ _ _ E F =>
    ∃ (a : Ω) (n : ℕ), 0 < n ∧ a ^ n ∈ E ∧
      F = IntermediateField.adjoin K ((E : Set Ω) ∪ {a})

def RadicalTowerType : Type (max u v + 1) :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω], ∀ r : ℕ,
      (Fin (r + 1) → IntermediateField K Ω) → Prop

def radicalTowerValue : RadicalTowerType.{u, v} :=
  fun K Ω _ _ _ _ r T =>
    T 0 = ⊥ ∧ ∀ i : Fin r, radicalStepValue K Ω (T i.castSucc) (T i.succ)

def RadicalExtensionType : Type (max u v + 1) :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω], IntermediateField K Ω → Prop

def radicalExtensionValue : RadicalExtensionType.{u, v} :=
  fun K Ω _ _ _ _ E =>
    ∃ (r : ℕ) (T : Fin (r + 1) → IntermediateField K Ω),
      radicalTowerValue K Ω r T ∧ T (Fin.last r) = E

def SolvableByRadicalsType : Type (max u v + 1) :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω], Ω → Prop

def solvableByRadicalsValue : SolvableByRadicalsType.{u, v} :=
  fun K Ω _ _ _ _ x =>
    ∃ E : IntermediateField K Ω, radicalExtensionValue K Ω E ∧ x ∈ E

/-- This checks that the union adjunction is genuinely simple adjunction over E,
with all scalar actions supplied by inclusions in the specified ambient field. -/
def StepIffSimpleAdjoin : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (E F : IntermediateField K Ω),
    radicalStepValue K Ω E F ↔
      ∃ (a : Ω) (n : ℕ), 0 < n ∧ a ^ n ∈ E ∧
        F = (IntermediateField.adjoin E {a}).restrictScalars K

def StepInclusion : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (E F : IntermediateField K Ω),
    radicalStepValue K Ω E F → E ≤ F

def TowerMonotone : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (r : ℕ) (T : Fin (r + 1) → IntermediateField K Ω),
    radicalTowerValue K Ω r T → Monotone T

/-- Every element of a field can be used for a repeated step, with exponent 1. -/
def RepeatedStep : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (E : IntermediateField K Ω) (a : Ω),
    a ∈ E → a ^ (1 : ℕ) ∈ E ∧
      E = IntermediateField.adjoin K ((E : Set Ω) ∪ {a}) ∧
      radicalStepValue K Ω E E

/-- For any number of steps (including zero), the constant base tower is allowed. -/
def ConstantBaseTower : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (r : ℕ),
    radicalTowerValue K Ω r (fun _ => ⊥)

def BaseRadicalExtension : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω], radicalExtensionValue K Ω ⊥

def BaseSolvable : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (a : K),
    solvableByRadicalsValue K Ω (algebraMap K Ω a)

/-- Membership in the last field is equivalent to membership somewhere in the
tower, since `TowerMonotone` makes all its fields contained in the last. -/
def SolvableIffTower : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (x : Ω),
    solvableByRadicalsValue K Ω x ↔
      ∃ (r : ℕ) (T : Fin (r + 1) → IntermediateField K Ω),
        radicalTowerValue K Ω r T ∧ ∃ i, x ∈ T i

end Specs.D07.Ch15.RadicalDefinition
