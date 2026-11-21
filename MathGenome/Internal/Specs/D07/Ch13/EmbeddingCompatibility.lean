import MathGenome.Internal.Specs.D07.Ch13.Embeddings
import MathGenome.Internal.Specs.D07.Ch13.Uniqueness
import Mathlib.Data.PNat.Basic

/-!
Independent statements for K07.13.embedding_compatibility,
paper.tex:3966–3974. All abstract copies carry their specified K-algebra
structures; the base field is finite and the extension degrees are finite.
No compatibility of independently chosen arrows is assumed. The last
statement constructs one simultaneous family on the already specified root
fields in one fixed algebraic closure, with inclusions, identities and
composition laws. Positive degrees include 1 and repeated endpoints.
-/

universe u v w z

namespace Specs.D07.Ch13.EmbeddingCompatibility

/-- A prescribed base-preserving embedding factors through the middle field. -/
def PrescribedTriangle : Prop :=
  ∀ (K : Type u) (Ea : Type v) (Eb : Type w) (Ec : Type z)
    [Field K] [Field Ea] [Field Eb] [Field Ec]
    [Algebra K Ea] [Algebra K Eb] [Algebra K Ec]
    [Finite K] [FiniteDimensional K Ea] [FiniteDimensional K Eb]
    [FiniteDimensional K Ec]
    (a b c : ℕ), 1 ≤ a → 1 ≤ b → 1 ≤ c →
    Module.finrank K Ea = a → Module.finrank K Eb = b →
    Module.finrank K Ec = c → a ∣ b → b ∣ c →
    ∀ σ : Ea →ₐ[K] Ec,
      ∃ (ι : Ea →ₐ[K] Eb) (τ : Eb →ₐ[K] Ec), τ.comp ι = σ

/-- Compatible arrows exist without prescribing the long arrow in advance. -/
def CompatibleTower : Prop :=
  ∀ (K : Type u) (Ea : Type v) (Eb : Type w) (Ec : Type z)
    [Field K] [Field Ea] [Field Eb] [Field Ec]
    [Algebra K Ea] [Algebra K Eb] [Algebra K Ec]
    [Finite K] [FiniteDimensional K Ea] [FiniteDimensional K Eb]
    [FiniteDimensional K Ec]
    (a b c : ℕ), 1 ≤ a → 1 ≤ b → 1 ≤ c →
    Module.finrank K Ea = a → Module.finrank K Eb = b →
    Module.finrank K Ec = c → a ∣ b → b ∣ c →
      ∃ (ι : Ea →ₐ[K] Eb) (τ : Eb →ₐ[K] Ec) (σ : Ea →ₐ[K] Ec),
        τ.comp ι = σ

/-- A single simultaneous system of literal inclusions in the fixed closure.
The last equality compares maps, including their chosen base embeddings. -/
def CoherentEmbeddedFamily : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Finite K] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
    (q : ℕ), Nat.card K = q →
    let F := fun n : ℕ+ => Existence.rootFieldValue K Ω q (n : ℕ)
    ∃ j : ∀ a b : ℕ+, (a : ℕ) ∣ (b : ℕ) → F a →ₐ[K] F b,
      (∀ (a b : ℕ+) (h : (a : ℕ) ∣ (b : ℕ)) (x : F a),
        (j a b h x : Ω) = (x : Ω)) ∧
      (∀ a : ℕ+, j a a (dvd_refl _) = AlgHom.id K (F a)) ∧
      (∀ (a b c : ℕ+) (hab : (a : ℕ) ∣ (b : ℕ)) (hbc : (b : ℕ) ∣ (c : ℕ)),
        (j b c hbc).comp (j a b hab) = j a c (hab.trans hbc))

end Specs.D07.Ch13.EmbeddingCompatibility
