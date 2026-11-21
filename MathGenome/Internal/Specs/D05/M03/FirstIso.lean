import MathGenome.Internal.Specs.D05.M03.Image
import MathGenome.Internal.Specs.D05.M03.Kernel
import MathGenome.Internal.Specs.D05.M03.Isomorphism
import MathGenome.Internal.Specs.D05.M06.QuotientLift

/-!
Independent statements for K05.03.first_iso (paper.tex:600–606).

The domain is the algebraic quotient by the actual kernel, and the codomain
is the actual image subspace, with the inherited scalar action. The formula
on every representative specifies the isomorphism, rather than asserting
only that the two spaces happen to be isomorphic. No dimension, complement,
injectivity, or surjectivity hypothesis on the original map is imposed.
-/

namespace Specs.D05.M03.FirstIso

/-- The representative formula is independent of representatives modulo the kernel. -/
def representative_independence : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W) (v w : V),
    v - w ∈ LinearMap.ker T → T v = T w

/-- The first isomorphism theorem, including the specified coset formula.
Uniqueness records that this formula determines the map on the whole quotient.
The `LinearEquiv` conclusion includes linearity and a two-sided linear inverse. -/
def first_iso : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (T : V →ₗ[K] W),
    ∃! e : (V ⧸ LinearMap.ker T) ≃ₗ[K] LinearMap.range T,
      ∀ v : V, e (Submodule.Quotient.mk v) =
        (⟨T v, LinearMap.mem_range_self T v⟩ : LinearMap.range T)

end Specs.D05.M03.FirstIso
