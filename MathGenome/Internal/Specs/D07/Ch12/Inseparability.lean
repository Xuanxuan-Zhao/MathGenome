import MathGenome.Internal.Specs.D07.Ch12.DerivativeCriterion
import MathGenome.Internal.Specs.D07.Ch12.SimpleDegree
import MathGenome.Internal.Specs.D07.Ch12.SimpleEmbeddings
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
Independent specification for K07.12.inseparability, paper.tex:3760–3767.
`RatFunc (ZMod p)` is the rational function field F_p(t), with t = RatFunc.X.
All extensions use their specified algebra maps. The ambient field containing
u need not be finite, algebraic, normal or algebraically closed. The degree
assertion is cardinal dimension. Closedness is used only for existence of a
root and of an embedding into the chosen target. No perfectness assumption
is imposed on the arbitrary characteristic-p field in the final statement.
-/

universe u v w

namespace Specs.D07.Ch12.Inseparability

open Polynomial

/-- The source's polynomial X^p-t over the prime rational function field. -/
noncomputable def examplePolynomial (p : ℕ) [Fact p.Prime] :
    Polynomial (RatFunc (ZMod p)) := X ^ p - C RatFunc.X

def ExampleIrreducible : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Irreducible (examplePolynomial p)

def ExampleRootExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Ω : Type v) [Field Ω]
    [Algebra (RatFunc (ZMod p)) Ω] [IsAlgClosed Ω],
      ∃ u : Ω, aeval u (examplePolynomial p) = 0

/-- Applies to every root, with no extra restriction on its ambient field. -/
def ExampleDegree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : Type v) [Field L]
    [Algebra (RatFunc (ZMod p)) L] (u : L),
      aeval u (examplePolynomial p) = 0 →
        Module.rank (RatFunc (ZMod p))
          (IntermediateField.adjoin (RatFunc (ZMod p)) {u}) = (p : Cardinal.{v})

def ExampleFactorization : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : Type v) [Field L]
    [Algebra (RatFunc (ZMod p)) L] (u : L),
      aeval u (examplePolynomial p) = 0 →
        (examplePolynomial p).map (algebraMap (RatFunc (ZMod p)) L) = (X - C u) ^ p

/-- Distinct roots are counted without multiplicity. -/
def ExampleUniqueRoot : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : Type v) [Field L]
    [Algebra (RatFunc (ZMod p)) L] (u : L),
      aeval u (examplePolynomial p) = 0 →
        ∀ v : L, aeval v (examplePolynomial p) = 0 ↔ v = u

/-- Exactly one embedding, not just at most one; the root and the target may
live in independent overfields of the same specified base field. -/
def ExampleUniqueEmbedding : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : Type v) (Ω : Type w) [Field L] [Field Ω]
    [Algebra (RatFunc (ZMod p)) L] [Algebra (RatFunc (ZMod p)) Ω]
    [IsAlgClosed Ω] (u : L), aeval u (examplePolynomial p) = 0 →
      ∃! _f : IntermediateField.adjoin (RatFunc (ZMod p)) {u} →ₐ[RatFunc (ZMod p)] Ω,
        True

/-- Includes the source's closing observation: the simple extension is
normal but inseparable, and its generator is inseparable over the base. -/
def ExampleNormalInseparable : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : Type v) [Field L]
    [Algebra (RatFunc (ZMod p)) L] (u : L), aeval u (examplePolynomial p) = 0 →
      Normal (RatFunc (ZMod p)) (IntermediateField.adjoin (RatFunc (ZMod p)) {u}) ∧
      ¬ IsSeparable (RatFunc (ZMod p)) u ∧
      ¬ Algebra.IsSeparable (RatFunc (ZMod p))
          (IntermediateField.adjoin (RatFunc (ZMod p)) {u})

/-- Uniqueness concerns both r and g; substitution acts on exponents and
leaves coefficients unchanged. The case r = 0 is included. -/
def UniqueSeparableDecomposition : Prop :=
  ∀ (K : Type u) [Field K] (p : ℕ) [CharP K p], p.Prime →
    ∀ f : Polynomial K, f.Monic → Irreducible f →
      ∃! rg : ℕ × Polynomial K,
        rg.2.Monic ∧ Irreducible rg.2 ∧ rg.2.Separable ∧
          f = rg.2.comp (X ^ (p ^ rg.1))

end Specs.D07.Ch12.Inseparability
