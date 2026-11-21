import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Universal
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.ZMod

/-! KD-11: the conormal sequence for an arbitrary surjective compatible tower.
The shared extension uses the given algebra structures. Its Cotangent is the
quotient of the kernel by its square, with scalars descended to B. -/
namespace Specs.AdvCommAlg.Differentials

universe u v w
noncomputable section
open TensorProduct

/-- Package the given tower, without changing any of its structural maps. -/
def conormalExtension (A : Type u) (P : Type v) (B : Type w)
    [CommRing A] [CommRing P] [CommRing B]
    [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]
    (h : Function.Surjective (algebraMap P B)) : Algebra.Extension.{v} A B where
  Ring := P
  σ b := (h b).choose
  algebraMap_σ b := (h b).choose_spec

abbrev Conormal (A : Type u) (P : Type v) (B : Type w)
    [CommRing A] [CommRing P] [CommRing B]
    [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]
    (h : Function.Surjective (algebraMap P B)) := (conormalExtension A P B h).Cotangent

def conormalMapType := ∀ (A : Type u) (P : Type v) (B : Type w)
  [CommRing A] [CommRing P] [CommRing B]
  [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]
  (h : Function.Surjective (algebraMap P B)),
  Conormal A P B h →ₗ[B] B ⊗[P] KaehlerDifferential A P

def conormalMapValue : conormalMapType.{u,v,w} :=
  fun A P B _ _ _ _ _ _ _ h => (conormalExtension A P B h).cotangentComplex

def conormalProjectionType := ∀ (A : Type u) (P : Type v) (B : Type w)
  [CommRing A] [CommRing P] [CommRing B]
  [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B],
  B ⊗[P] KaehlerDifferential A P →ₗ[B] KaehlerDifferential A B

def conormalProjectionValue : conormalProjectionType.{u,v,w} :=
  fun A P B _ _ _ _ _ _ _ => KaehlerDifferential.mapBaseChange A P B

/-- Explicit bridge to the ordinary quotient I/I² and its class map. -/
def conormalQuotient : Prop := ∀ (A : Type u) (P : Type v) (B : Type w)
  [CommRing A] [CommRing P] [CommRing B]
  [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]
  (h : Function.Surjective (algebraMap P B)),
  ∃ e : Conormal A P B h ≃ₗ[P] (RingHom.ker (algebraMap P B)).Cotangent,
    (∀ f, e (Algebra.Extension.Cotangent.mk (P := conormalExtension A P B h) f) =
      Ideal.toCotangent _ f) ∧
    (∀ f : RingHom.ker (algebraMap P B),
      Algebra.Extension.Cotangent.mk (P := conormalExtension A P B h) f = 0 ↔
        f.val ∈ (RingHom.ker (algebraMap P B)) ^ 2) ∧
    (∀ (p : P) (x : Conormal A P B h), e (algebraMap P B p • x) = p • e x)

def conormalMapApply : Prop := ∀ (A : Type u) (P : Type v) (B : Type w)
  [CommRing A] [CommRing P] [CommRing B]
  [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]
  (h : Function.Surjective (algebraMap P B)) (f : RingHom.ker (algebraMap P B)),
  conormalMapValue A P B h (Algebra.Extension.Cotangent.mk f) =
    1 ⊗ₜ[P] KaehlerDifferential.D A P f.val

def conormalProjectionApply : Prop := ∀ (A : Type u) (P : Type v) (B : Type w)
  [CommRing A] [CommRing P] [CommRing B]
  [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]
  (b : B) (p : P),
  conormalProjectionValue A P B (b ⊗ₜ[P] KaehlerDifferential.D A P p) =
    b • KaehlerDifferential.D A B (algebraMap P B p)

def conormalExact : Prop := ∀ (A : Type u) (P : Type v) (B : Type w)
  [CommRing A] [CommRing P] [CommRing B]
  [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]
  (h : Function.Surjective (algebraMap P B)),
  Function.Exact (conormalMapValue A P B h) (conormalProjectionValue A P B) ∧
    Function.Surjective (conormalProjectionValue A P B)

/-- The example uses the actual structural map Z → F_p, not a different ideal. -/
def primeConormalExample : Prop := ∀ (p : ℕ), p.Prime →
  RingHom.ker (algebraMap ℤ (ZMod p)) = Ideal.span ({(p : ℤ)} : Set ℤ) ∧
  Nontrivial (Ideal.span ({(p : ℤ)} : Set ℤ)).Cotangent ∧
  Function.Surjective (algebraMap ℤ (ZMod p)) ∧
  Subsingleton ((ZMod p) ⊗[ℤ] KaehlerDifferential ℤ ℤ) ∧
  ∀ h : Function.Surjective (algebraMap ℤ (ZMod p)),
    ¬ Function.Injective (conormalMapValue ℤ ℤ (ZMod p) h)

end
end Specs.AdvCommAlg.Differentials
