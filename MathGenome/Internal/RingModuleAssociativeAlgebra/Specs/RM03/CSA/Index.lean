import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Degree
import Mathlib.FieldTheory.Separable
import Mathlib.Order.Lattice.Nat

/-! Specifications for RM03-C04.06. -/

namespace Specs.RM03.CSA

universe u v w

set_option linter.checkUnivs false in
def IndexType :=
  ∀ (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A], ℕ

/-- The least degree among division factors in positive-size matrix presentations.
For a central simple algebra this set is nonempty and has just one element. -/
noncomputable def index (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] : ℕ :=
  sInf {d : ℕ | ∃ (r : ℕ) (D : Type v) (_ : DivisionRing D) (_ : Algebra k D),
    isCentralDivision k D ∧ 0 < r ∧ Nonempty (A ≃ₐ[k] Matrix (Fin r) (Fin r) D) ∧
    degree k D = d}

def IndexEqDegree : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {D : Type w} [DivisionRing D] [Algebra k D] {r : ℕ},
    isCentralSimple k A → isCentralDivision k D → 0 < r →
    (A ≃ₐ[k] Matrix (Fin r) (Fin r) D) → index k A = degree k D

def IndexDvdFinrankOfSplits : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {L : Type w} [Field L] [Algebra k L] [FiniteDimensional k L],
    isCentralSimple k A → splits k L A → index k A ∣ Module.finrank k L

def ExistsSeparableSplittingFieldOfFinrankIndex : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A],
    isCentralSimple k A →
    ∃ (E : Type v) (_ : Field E) (_ : Algebra k E),
      FiniteDimensional k E ∧ Algebra.IsSeparable k E ∧ splits k E A ∧
        Module.finrank k E = index k A

end Specs.RM03.CSA
