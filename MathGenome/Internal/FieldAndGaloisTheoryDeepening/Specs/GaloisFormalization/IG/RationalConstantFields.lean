import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Basic

namespace GaloisFormalization.IG

open IntermediateField

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

/-- The compositum of the constant field `D` and the rational base `k(t)`,
viewed as an intermediate field over the rational base in the same ambient field. -/
def rationalWithConstants (t : Ω) (D : IntermediateField k Ω) :
    IntermediateField (adjoin k {t}) Ω :=
  extendScalars (show adjoin k {t} ≤ D ⊔ adjoin k {t} from le_sup_right)

/-- The elements of `L` algebraic over the field of constants `k`, viewed in `Ω`. -/
def rationalConstantField (t : Ω) (L : IntermediateField (adjoin k {t}) Ω) :
    IntermediateField k Ω :=
  L.restrictScalars k ⊓ algebraicClosure k Ω

namespace Specs

/-- The constant field is finite, and adjoining the variable to it gives the
intersection with the rational extension of the algebraic closure of constants. -/
def constantIntersection : Prop :=
  ∀ (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
    (t : Ω) (_ : Transcendental k t) [Algebra.IsAlgebraic (adjoin k {t}) Ω]
    (L : IntermediateField (adjoin k {t}) Ω) [FiniteDimensional (adjoin k {t}) L]
    [IsGalois (adjoin k {t}) L],
    let C := rationalConstantField t L
    let M := L ⊓ rationalWithConstants t (algebraicClosure k Ω)
    FiniteDimensional k C ∧
      M = rationalWithConstants t C ∧
      (M = ⊥ ↔ ∀ x : L, IsAlgebraic k x → x ∈ Set.range (algebraMap k L))

end Specs
end GaloisFormalization.IG
