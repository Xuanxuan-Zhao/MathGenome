import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

open CategoryTheory

universe u v

namespace LinearAlgebraicGroups.Specs

/-- Any lifts of a basis of the kernel coordinate ring form a basis over the
source Hopf algebra when its augmentation ideal is nilpotent. -/
def NilpotentAugmentationBasis : Prop :=
  ∀ (k : Type u) [Field k] {A B : HopfAlgebraCategory k}
    [Algebra.FiniteType k A] [Algebra.FiniteType k B] (f : A ⟶ B),
    Function.Injective f.hom → IsNilpotent (augmentationIdeal A) →
    letI : Algebra A B := f.hom.toAlgHom.toRingHom.toAlgebra
    ∀ (ι : Type v) (b : Module.Basis ι k (B ⧸ kernelIdeal f)) (e : ι → B),
      (∀ i, Ideal.Quotient.mk (kernelIdeal f) (e i) = b i) →
      ∃ b' : Module.Basis ι A B, ∀ i, b' i = e i

/-- Faithful flatness of the module induced by an injective Hopf algebra map
whose source has nilpotent augmentation ideal. -/
def NilpotentAugmentationFaithfullyFlat : Prop :=
  ∀ (k : Type u) [Field k] {A B : HopfAlgebraCategory k}
    [Algebra.FiniteType k A] [Algebra.FiniteType k B] (f : A ⟶ B),
    Function.Injective f.hom → IsNilpotent (augmentationIdeal A) →
    letI : Algebra A B := f.hom.toAlgHom.toRingHom.toAlgebra
    Module.FaithfullyFlat A B

end LinearAlgebraicGroups.Specs
