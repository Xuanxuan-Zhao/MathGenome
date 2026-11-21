import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Universal
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.SurjectiveBase

/-! Surjective structural maps have zero relative differentials (KD-06). -/
namespace AdvCommAlg.Differentials

universe u v

/-- If every element comes from the base, every differential vanishes.
Mathlib proves this using the spanning family of universal differentials. -/
theorem subsingleton_of_surjective (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B]
    (h : Function.Surjective (algebraMap A B)) : Subsingleton (Omega A B) := by
  exact KaehlerDifferential.subsingleton_of_surjective A B h

/-- In particular, Ω_{A/A} is zero. -/
theorem subsingleton_self (A : Type u) [CommRing A] :
    Subsingleton (Omega A A) := by
  exact subsingleton_of_surjective A A (fun a => ⟨a, rfl⟩)

/-- In particular, Ω_{(A/I)/A} is zero for every ideal I. -/
theorem subsingleton_quotient (A : Type u) [CommRing A] (I : Ideal A) :
    Subsingleton (Omega A (A ⧸ I)) := by
  exact subsingleton_of_surjective A (A ⧸ I) Ideal.Quotient.mk_surjective

end AdvCommAlg.Differentials
