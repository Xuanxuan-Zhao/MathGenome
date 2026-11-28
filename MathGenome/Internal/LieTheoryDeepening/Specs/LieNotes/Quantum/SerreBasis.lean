import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.SerrePresentation
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

/-! The ordered presentation and basis of the type A₂ Serre algebra. -/

namespace Specs.LieNotes.Quantum.SerreBasis

open SerrePresentation
open scoped TensorProduct

universe u v
variable {A : Type u} [CommRing A]

/-- The two-sided ideal expressing the ordered relations on the letters x, z, y. -/
def orderedIdeal (q : Aˣ) : TwoSidedIdeal (FreeAlgebra A (Fin 3)) :=
  let X := FreeAlgebra.ι A (0 : Fin 3)
  let Z := FreeAlgebra.ι A (1 : Fin 3)
  let Y := FreeAlgebra.ι A (2 : Fin 3)
  TwoSidedIdeal.span
    {Z * X - (↑(q⁻¹) : A) • (X * Z),
     Y * Z - (↑(q⁻¹) : A) • (Z * Y),
     Y * X - ((↑q : A) • (X * Y) - (↑q : A) • Z)}

abbrev OrderedAlgebra (A : Type u) [CommRing A] (q : Aˣ) : Type u :=
  FreeAlgebra A (Fin 3) ⧸ (orderedIdeal q).asIdeal

def orderedGenerator (q : Aˣ) (i : Fin 3) : OrderedAlgebra A q :=
  Ideal.Quotient.mkₐ A (orderedIdeal q).asIdeal (FreeAlgebra.ι A i)

def orderedMonomial (q : Aˣ) (i : ℕ × ℕ × ℕ) : SerreAlgebra A q :=
  x q ^ i.1 * z q ^ i.2.1 * y q ^ i.2.2

def relationsProp : Prop :=
  ∀ {A : Type u} [CommRing A] (q : Aˣ),
    x q * z q = (↑q : A) • (z q * x q) ∧
    z q * y q = (↑q : A) • (y q * z q) ∧
    y q * x q = (↑q : A) • (x q * y q) - (↑q : A) • z q

def orderedPresentationProp : Prop :=
  ∀ {A : Type u} [CommRing A] (q : Aˣ),
    ∃ e : OrderedAlgebra A q ≃ₐ[A] SerreAlgebra A q,
      e (orderedGenerator q 0) = x q ∧ e (orderedGenerator q 1) = z q ∧
      e (orderedGenerator q 2) = y q

def basisProp : Prop :=
  ∀ {A : Type u} [CommRing A] (q : Aˣ),
    ∃ b : Module.Basis (ℕ × ℕ × ℕ) A (SerreAlgebra A q),
      ∀ i, b i = orderedMonomial q i

def baseChangeProp : Prop :=
  ∀ {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B] (q : Aˣ),
    let q' := Units.map (algebraMap A B) q
    ∃ e : B ⊗[A] SerreAlgebra A q ≃ₐ[B] SerreAlgebra B q',
      (∀ i, e (1 ⊗ₜ[A] generator q i) = generator q' i) ∧
      e (1 ⊗ₜ[A] z q) = z q' ∧
      (∀ i, e (1 ⊗ₜ[A] orderedMonomial q i) = orderedMonomial q' i) ∧
      ∃ (b : Module.Basis (ℕ × ℕ × ℕ) A (SerreAlgebra A q))
        (b' : Module.Basis (ℕ × ℕ × ℕ) B (SerreAlgebra B q')),
        (∀ i, b i = orderedMonomial q i) ∧ (∀ i, b' i = orderedMonomial q' i) ∧
        ∀ i, e (b.baseChange B i) = b' i

def orderedBaseChangeProp : Prop :=
  ∀ {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B] (q : Aˣ),
    let q' := Units.map (algebraMap A B) q
    ∃ e : B ⊗[A] OrderedAlgebra A q ≃ₐ[B] OrderedAlgebra B q',
      ∀ i, e (1 ⊗ₜ[A] orderedGenerator q i) = orderedGenerator q' i

end Specs.LieNotes.Quantum.SerreBasis
