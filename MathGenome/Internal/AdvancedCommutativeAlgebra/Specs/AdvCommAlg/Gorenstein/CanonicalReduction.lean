import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.SupportAndParameters
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-! GC-11, canonical reduction assertion (paper.tex:4742–4760).
The quotient module and its quotient-ring action are the canonical ones.
A nonempty system of parameters is written as `x :: xs`; no presentation
of the ring or of its canonical module is required. -/

universe u
open scoped Pointwise
namespace AdvCommAlg.Gorenstein

/-- The quotient by an element of the maximal ideal is a nonzero local ring. -/
@[instance_reducible] def principalQuotientLocalRing {R : Type u} [CommRing R]
    [IsLocalRing R] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) :
    IsLocalRing (R ⧸ Ideal.span {x}) := by
  have hle : Ideal.span {x} ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr (by simpa using hx)
  letI : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

namespace Specs

/-- Reduction of an arbitrary canonical module by the first parameter. -/
def canonical_reductionType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    IsCanonicalModuleValue R M → ∀ (x : R) (xs : List R)
      (hsop : CohenMacaulay.Specs.IsSystemOfParametersValue R R (x :: xs)),
    letI := principalQuotientLocalRing x (hsop.1 x (by simp))
    IsCanonicalModuleValue (R ⧸ Ideal.span {x})
      (M ⧸ (Ideal.span {x} • (⊤ : Submodule R M)))

end Specs
end AdvCommAlg.Gorenstein
