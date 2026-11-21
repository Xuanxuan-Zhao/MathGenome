import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Defs
import Mathlib.Data.Nat.Sqrt
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Specifications for the degree and algebraic-closure assertions of RM03-C04.05. -/

namespace Specs.RM03.CSA

universe u v w

-- Quantify over independent universes for the base field and the algebra.
set_option linter.checkUnivs false in
def DegreeType :=
  ∀ (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A], ℕ

noncomputable def degree (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] : ℕ :=
  Nat.sqrt (Module.finrank k A)

def DegreePos : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A],
    isCentralSimple k A → 0 < degree k A

def FinrankEqDegreeSq : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A],
    isCentralSimple k A → Module.finrank k A = (degree k A) ^ 2

def DegreeEqIff : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A],
    isCentralSimple k A → ∀ {n : ℕ},
      degree k A = n ↔ 0 < n ∧ Module.finrank k A = n ^ 2

def AlgEquivMatrixAlgebraicClosure : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A],
    isCentralSimple k A →
    Nonempty (baseChange k (AlgebraicClosure k) A ≃ₐ[AlgebraicClosure k]
      Matrix (Fin (degree k A)) (Fin (degree k A)) (AlgebraicClosure k))

def CentralDivisionDegree : Prop :=
  ∀ {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D],
    isCentralDivision k D →
    0 < degree k D ∧ Module.finrank k D = (degree k D) ^ 2 ∧
      Nonempty (baseChange k (AlgebraicClosure k) D ≃ₐ[AlgebraicClosure k]
        Matrix (Fin (degree k D)) (Fin (degree k D)) (AlgebraicClosure k))

def DegreeMatrixDivision : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {D : Type w} [DivisionRing D] [Algebra k D] {r : ℕ},
    isCentralSimple k A → isCentralDivision k D → 0 < r →
    (A ≃ₐ[k] Matrix (Fin r) (Fin r) D) → degree k A = r * degree k D

def DegreeEqMatrixSize : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {L : Type w} [Field L] [Algebra k L] {n : ℕ},
    isCentralSimple k A → (baseChange k L A ≃ₐ[L] Matrix (Fin n) (Fin n) L) →
    degree k A = n

end Specs.RM03.CSA
