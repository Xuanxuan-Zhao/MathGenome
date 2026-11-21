import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.FinitePresentationDescent
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.UnramifiedDescent

/-! Faithfully flat descent in finite presentation (FL-17).

Mathlib's smooth descent theorem descends projectivity of differentials
(using their finite presentation and descent of flatness) and vanishing of
the first cotangent homology. Its formal smoothness conclusion is equivalent
to actual square-zero lifting by the accepted FL-01 equivalence. Thus this
argument supplies the existence part of descent, as well as uniqueness.
-/
namespace AdvCommAlg.FormalLifting

open TensorProduct

universe u v w

/-- Formal smoothness descends along faithfully flat base change when
the original algebra is finitely presented. -/
theorem formallySmooth_of_faithfullyFlat
    (A : Type u) (A' : Type v) (B : Type w)
    [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] [Module.FaithfullyFlat A A']
    [Algebra.FinitePresentation A B]
    (h : FormallySmooth A' (A' ⊗[A] B)) : FormallySmooth A B := by
  let : Algebra.FormallySmooth A' (A' ⊗[A] B) :=
    (formallySmooth_iff A' (A' ⊗[A] B)).mp h
  let : Algebra.Smooth A' (A' ⊗[A] B) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth A B :=
    Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat (R := A) (S := B) A'
  apply (AdvCommAlg.FormalLifting.formallySmooth_iff A B).mpr
  exact (inferInstance : Algebra.FormallySmooth A B)

/-- Formal étaleness descends under the same finite-presentation hypothesis. -/
theorem formallyEtale_of_faithfullyFlat
    (A : Type u) (A' : Type v) (B : Type w)
    [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] [Module.FaithfullyFlat A A']
    [Algebra.FinitePresentation A B]
    (h : FormallyEtale A' (A' ⊗[A] B)) : FormallyEtale A B := by
  have hs : FormallySmooth A' (A' ⊗[A] B) := fun N hN => (h N hN).2
  have hu : FormallyUnramified A' (A' ⊗[A] B) := fun N hN => (h N hN).1
  have hs' : FormallySmooth A B := formallySmooth_of_faithfullyFlat A A' B hs
  have hu' : FormallyUnramified A B := formallyUnramified_of_faithfullyFlat A A' B hu
  intro C _ _ N hN
  exact ⟨hu' N hN, hs' N hN⟩

end AdvCommAlg.FormalLifting
