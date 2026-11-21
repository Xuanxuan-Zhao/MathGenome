import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
Independent specification of K07.15.kummer_converse (paper.tex:4401–4410).
The chosen `Algebra K L` is the specified field embedding. The roots-of-unity
hypothesis refers to all solutions in an algebraic closure, as in the source's
definition of μ_n, and says that each lies in the image of K. It does not
assume the existence of the radical generator being sought.

Finite dimension is explicit; the equality with n specifies the degree.
`adjoin K {u} = ⊤` means L = K(u) inside L, and the final equality records
membership of u^n in the image of the specified base embedding. Degree one
is included, and no characteristic-zero restriction is added.
-/

namespace Specs.D07.Ch15.KummerConverse

universe u v

def CyclicExtensionIsRadical : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (n : ℕ), Module.finrank K L = n → (n : K) ≠ 0 →
    (∀ ζ : AlgebraicClosure K, ζ ^ n = 1 →
      ∃ a : K, algebraMap K (AlgebraicClosure K) a = ζ) →
    ∃ u : L, u ≠ 0 ∧ IntermediateField.adjoin K {u} = ⊤ ∧
      ∃ a : K, u ^ n = algebraMap K L a

end Specs.D07.Ch15.KummerConverse
