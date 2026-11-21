import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-! Independent statements for the first paragraph of K07.20.artin_schreier,
paper.tex:6026–6040. All base fields are arbitrary, including imperfect and
infinite fields. `Multiplicative (ZMod p)` is the additive group of F_p
written multiplicatively solely to match the automorphism group API. -/

noncomputable section
universe u v
namespace Specs.D07.Ch20.ArtinSchreierTranslationDichotomy
open Polynomial

/-- The original polynomial, with its original parameter and sign. -/
def asPolynomial (K : Type u) [Field K] (p : ℕ) (a : K) : K[X] :=
  X ^ p - X - C a

def DegreeAndSeparability : Prop :=
  ∀ (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (a : K),
    (asPolynomial K p a).Monic ∧ (asPolynomial K p a).natDegree = p ∧
      (asPolynomial K p a).Separable

/-- The p translates are distinct and exhaust the roots; the displayed
product also records that every root has multiplicity one. -/
def TranslatedRoots : Prop :=
  ∀ (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (a θ : K), θ ^ p - θ = a →
    Function.Injective (fun c : ZMod p => θ + ZMod.cast c) ∧
      (∀ x : K, x ^ p - x = a ↔ ∃ c : ZMod p, x = θ + ZMod.cast c) ∧
      asPolynomial K p a = ∏ c : ZMod p, (X - C (θ + ZMod.cast c))

/-- In every splitting field the root used for the translation description
exists, and the displayed list has exactly p distinct members. -/
def SplittingFieldRoots : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] (a : K)
    [Polynomial.IsSplittingField K L (asPolynomial K p a)],
    ∃ θ : L, θ ^ p - θ = algebraMap K L a ∧
      Function.Injective (fun c : ZMod p => θ + ZMod.cast c) ∧
      (asPolynomial K p a).map (algebraMap K L) =
        ∏ c : ZMod p, (X - C (θ + ZMod.cast c)) ∧
      ((asPolynomial K p a).map (algebraMap K L)).roots.card = p

/-- Adjoining any one root, even inside a larger arbitrary extension,
gives a splitting field. -/
def RootGeneratesSplittingField : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] (a : K) (θ : L),
    θ ^ p - θ = algebraMap K L a →
    Polynomial.IsSplittingField K (IntermediateField.adjoin K {θ}) (asPolynomial K p a)

/-- In every realization of the splitting field, each root generates it,
and the translation of that root embeds its automorphism group into F_p. -/
def TranslationEmbedding : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] (a : K)
    [Polynomial.IsSplittingField K L (asPolynomial K p a)] (θ : L),
    θ ^ p - θ = algebraMap K L a →
    IntermediateField.adjoin K {θ} = ⊤ ∧
      ∃ t : (L ≃ₐ[K] L) →* Multiplicative (ZMod p),
        Function.Injective t ∧
          ∀ σ, ZMod.cast (Multiplicative.toAdd (t σ)) = σ θ - θ

/-- Membership in wp(K) means existence of a preimage under u ↦ u^p-u. -/
def SplitsIffParameterInImage : Prop :=
  ∀ (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (a : K),
    (asPolynomial K p a).Splits ↔ ∃ u : K, u ^ p - u = a

def IrreducibleOfParameterNotInImage : Prop :=
  ∀ (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (a : K),
    (¬ ∃ u : K, u ^ p - u = a) → Irreducible (asPolynomial K p a)

/-- The nontrivial branch includes the full degree, Galois and cyclic
conclusions for any root in any extension, and identifies its minimal polynomial. -/
def NontrivialRootExtension : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] (a : K) (θ : L),
    (¬ ∃ u : K, u ^ p - u = a) → θ ^ p - θ = algebraMap K L a →
    let E := IntermediateField.adjoin K {θ}
    FiniteDimensional K E ∧ IsGalois K E ∧ Module.finrank K E = p ∧
      IsCyclic (E ≃ₐ[K] E) ∧ minpoly K θ = asPolynomial K p a

end Specs.D07.Ch20.ArtinSchreierTranslationDichotomy
