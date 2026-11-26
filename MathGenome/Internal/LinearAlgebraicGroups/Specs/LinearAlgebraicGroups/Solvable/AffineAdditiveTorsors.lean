import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.FppfTorsors
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.AdditiveDescent

noncomputable section

open Algebra.TensorProduct

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The first Čech differential for a single affine cover. -/
def d₀ : B →ₗ[A] B ⊗[A] B :=
  (includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap - includeLeft.toLinearMap

/-- Pullback to entries 1 and 2 of the triple overlap, indexed from 0. -/
def face₀ : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) := includeRight

/-- Pullback to entries 0 and 2 of the triple overlap. -/
def face₁ : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
  map (.id A B) includeRight

/-- Pullback to entries 0 and 1 of the triple overlap. -/
def face₂ : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
  map (.id A B) includeLeft

/-- The alternating differential from the double to the triple overlap. -/
def d₁ : B ⊗[A] B →ₗ[A] B ⊗[A] (B ⊗[A] B) :=
  (face₀ A B).toLinearMap - (face₁ A B).toLinearMap + (face₂ A B).toLinearMap

def CechExactAtOne : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B],
    Function.Exact (d₀ A B) (d₁ A B)

/-- Any group scheme identified naturally on all affine test algebras with the
additive group has trivial fppf torsors over every affine base. -/
def AffineAdditiveTorsorSection : Prop :=
  ∀ {k : Type u} [Field k] {H : GroupScheme k},
    ((groupPointsFunctor k).obj H ≅ StandardGroups.additivePoints k) →
    ∀ (S : SchemeOver k), IsAffine S.left →
      ∀ P : Fppf.FppfTorsor S H, Nonempty (P.1.Section (Over.mk (𝟙 S)))

end

end LinearAlgebraicGroups.Specs.AdditiveDescent
