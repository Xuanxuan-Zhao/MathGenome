import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.CartanQuotient
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.MinimalRealization
import Mathlib.LinearAlgebra.Matrix.Trace

/-! The infinite rank-two root orbit of Example KM07. -/

namespace Specs.LieNotes.Contragredient.InfiniteRankTwo

open CartanData CartanQuotient WeightExtraction

noncomputable section

universe v

/-- The rank-two matrix with the coroot indexing the row. -/
def cartanMatrix (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, -a; -b, 2]

def CartanMatrixType := ℤ → ℤ → Matrix (Fin 2) (Fin 2) ℤ

def IsCartanMatrix : Prop :=
  ∀ (a b : ℤ), 0 < a → 0 < b → IsGeneralizedCartanMatrix (cartanMatrix a b)

/-- The product of the first and second simple reflections, in that order. -/
def reflectionProduct (a b : ℤ) : Module.End ℤ (Q (Fin 2)) :=
  rootReflection (cartanMatrix a b) 0 * rootReflection (cartanMatrix a b) 1

def ReflectionProductType := ℤ → ℤ → Module.End ℤ (Q (Fin 2))

/-- The two output coordinates give the rows of the matrix of the reflection product. -/
def ReflectionProductCoordinates : Prop :=
  ∀ (a b : ℤ) (q : Q (Fin 2)),
    reflectionProduct a b q 0 = (a * b - 1) * q 0 - a * q 1 ∧
    reflectionProduct a b q 1 = b * q 0 - q 1

def ReflectionProductDetTrace : Prop :=
  ∀ a b : ℤ,
    let T : Matrix (Fin 2) (Fin 2) ℤ := !![a * b - 1, -a; b, -1]
    T.det = 1 ∧ T.trace = a * b - 2

def ReflectionProductAtFour : Prop :=
  ∀ a b : ℤ, a * b = 4 →
    (reflectionProduct a b - 1) ^ 2 = 0 ∧
      (reflectionProduct a b - 1) (simpleDegree 0) ≠ 0

/-- The orbit of the first simple root under nonnegative powers of the reflection product. -/
def orbitWeight {a b : ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H]
    (R : Realization (cartanMatrix a b) H) (n : ℕ) : Module.Dual ℂ H :=
  ((R.weightReflection 0 * R.weightReflection 1) ^ n) (R.α 0)

def OrbitWeightType :=
  ∀ {a b : ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H],
    Realization (cartanMatrix a b) H → ℕ → Module.Dual ℂ H

def InfiniteRootOrbit : Prop :=
  ∀ {a b : ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H],
    0 < a → 0 < b → 4 ≤ a * b → ∀ (R : Realization (cartanMatrix a b) H),
      Function.Injective (orbitWeight R) ∧ (∀ n, orbitWeight R n ≠ 0) ∧
        (∀ n, weightSpace (cartanAdjoint R) (orbitWeight R n) ≠ ⊥) ∧
        iSupIndep (fun n ↦ weightSpace (cartanAdjoint R) (orbitWeight R n))

def InfiniteDimensional : Prop :=
  ∀ {a b : ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H],
    0 < a → 0 < b → 4 ≤ a * b → ∀ (R : Realization (cartanMatrix a b) H),
      ¬ FiniteDimensional ℂ (Algebra R)

def MinimalInfiniteDimensional : Prop :=
  ∀ {a b : ℤ}, 0 < a → 0 < b → 4 ≤ a * b →
    ∃ (H : Type) (add : AddCommGroup H) (mod : @Module ℂ H _ add.toAddCommMonoid),
      letI := add
      letI := mod
      ∃ R : Realization (cartanMatrix a b) H,
        R.IsMinimal ∧ ¬ FiniteDimensional ℂ (Algebra R)

end
end Specs.LieNotes.Contragredient.InfiniteRankTwo
