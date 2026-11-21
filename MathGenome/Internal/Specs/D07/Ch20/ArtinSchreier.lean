import MathGenome.Internal.Specs.D07.Ch20.ArtinSchreierTranslationDichotomy
import MathGenome.Internal.Specs.D07.Ch20.ArtinSchreierCyclicDegreePConverse
import MathGenome.Internal.Specs.D07.Ch20.ArtinSchreierParameterClassification

/-!
Independent specification for K07.20.artin_schreier (paper.tex:6026–6047).
The polynomial is the shared `asPolynomial K p a = X^p-X-C a`.
No finiteness or perfection of the base field is imposed. FiniteDimensional
always refers to the extension degree. The prime-field scalar in the
classification is nonzero, and all isomorphisms fix the specified base.
-/

noncomputable section
universe u v
namespace Specs.D07.Ch20.ArtinSchreier
open Polynomial
open ArtinSchreierTranslationDichotomy (asPolynomial)

/-- The split branch displays exactly p distinct linear factors; the other
branch excludes precisely the image of the Artin–Schreier map. -/
def PolynomialDichotomy : Prop :=
  ∀ (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (a : K),
    (∃ θ : K, θ ^ p - θ = a ∧
      Function.Injective (fun c : ZMod p => θ + ZMod.cast c) ∧
      asPolynomial K p a = ∏ c : ZMod p, (X - C (θ + ZMod.cast c)) ∧
      (asPolynomial K p a).roots.card = p) ∨
    ((¬ ∃ u : K, u ^ p - u = a) ∧ Irreducible (asPolynomial K p a))

/-- The exact splitting criterion, including both directions. -/
def SplitsIff : Prop :=
  ∀ (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (a : K),
    (asPolynomial K p a).Splits ↔ ∃ u : K, u ^ p - u = a

/-- Every root in every extension generates a cyclic Galois extension of
finite degree p in the nontrivial branch. -/
def RootExtension : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] (a : K) (θ : L),
    (¬ ∃ u : K, u ^ p - u = a) → θ ^ p - θ = algebraMap K L a →
    let E := IntermediateField.adjoin K {θ}
    FiniteDimensional K E ∧ IsGalois K E ∧ Module.finrank K E = p ∧
      IsCyclic (E ≃ₐ[K] E) ∧ minpoly K θ = asPolynomial K p a

/-- The converse quantifies over cyclic Galois extensions, without requiring
a chosen automorphism generator as additional input. -/
def CyclicConverse : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)],
    Module.finrank K L = p →
    ∃ (θ : L) (a : K),
      (¬ ∃ u : K, u ^ p - u = a) ∧
      θ ^ p - θ = algebraMap K L a ∧
      IntermediateField.adjoin K {θ} = ⊤ ∧
      minpoly K θ = asPolynomial K p a

/-- Equality in a common overfield, base-field isomorphism, and the affine
parameter relation are equivalent, uniformly in the choices of roots. -/
def RootFieldsClassification : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    (p : ℕ) [Fact p.Prime] [CharP K p] (a b : K) (θ η : Ω),
    (¬ ∃ u : K, u ^ p - u = a) → (¬ ∃ u : K, u ^ p - u = b) →
    θ ^ p - θ = algebraMap K Ω a → η ^ p - η = algebraMap K Ω b →
    (IntermediateField.adjoin K {θ} = IntermediateField.adjoin K {η} ↔
      Nonempty (IntermediateField.adjoin K {θ} ≃ₐ[K]
        IntermediateField.adjoin K {η})) ∧
    (Nonempty (IntermediateField.adjoin K {θ} ≃ₐ[K]
        IntermediateField.adjoin K {η}) ↔
      ∃ (c : ZMod p) (u : K), c ≠ 0 ∧ b = ZMod.cast c * a + (u ^ p - u))

/-- The two extensions actually exist in the same chosen algebraic closure. -/
def CommonClosureClassification : Prop :=
  ∀ (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (a b : K),
    (¬ ∃ u : K, u ^ p - u = a) → (¬ ∃ u : K, u ^ p - u = b) →
    ∃ θ η : AlgebraicClosure K,
      θ ^ p - θ = algebraMap K (AlgebraicClosure K) a ∧
      η ^ p - η = algebraMap K (AlgebraicClosure K) b ∧
      (IntermediateField.adjoin K {θ} = IntermediateField.adjoin K {η} ↔
        Nonempty (IntermediateField.adjoin K {θ} ≃ₐ[K]
          IntermediateField.adjoin K {η})) ∧
      (Nonempty (IntermediateField.adjoin K {θ} ≃ₐ[K]
          IntermediateField.adjoin K {η}) ↔
        ∃ (c : ZMod p) (u : K), c ≠ 0 ∧ b = ZMod.cast c * a + (u ^ p - u))

/-- All assertions of the source theorem together. -/
def ArtinSchreierTheorem : Prop :=
  PolynomialDichotomy.{u} ∧ SplitsIff.{u} ∧ RootExtension.{u, v} ∧
    CyclicConverse.{u, v} ∧ RootFieldsClassification.{u, v} ∧
    CommonClosureClassification.{u}

end Specs.D07.Ch20.ArtinSchreier
