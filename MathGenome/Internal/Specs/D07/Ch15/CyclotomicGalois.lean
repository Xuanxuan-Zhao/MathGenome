import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
Independent specification of K07.15.cyclotomic_galois,
paper.tex:4353–4364. The field is the concrete intermediate field
`IntermediateField.adjoin ℚ {ζ}` in the specified overfield Ω. Rational
scalars use their unique embedding in a characteristic-zero field.

No algebraic-closedness or global algebraicity hypothesis on Ω is needed:
the primitive root itself is algebraic. In particular the statements apply
in the source's specified algebraic closure and to every primitive complex
root. Positivity includes n = 1 and n = 2. The exponent is the natural
representative of a unit class modulo n; the action is asserted on ζ.
-/

namespace Specs.D07.Ch15.CyclotomicGalois

universe u

/-- The generated extension has finite degree, equal to Euler's totient. -/
def CyclotomicDegree : Prop :=
  ∀ (Ω : Type u) [Field Ω] [CharZero Ω] (n : ℕ), 0 < n →
    ∀ ζ : Ω, IsPrimitiveRoot ζ n →
      FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) ∧
        Module.finrank ℚ (IntermediateField.adjoin ℚ {ζ}) = Nat.totient n

/-- This concrete field is a separable splitting field, hence Galois. -/
def CyclotomicSplittingGalois : Prop :=
  ∀ (Ω : Type u) [Field Ω] [CharZero Ω] (n : ℕ), 0 < n →
    ∀ ζ : Ω, IsPrimitiveRoot ζ n →
      Polynomial.IsSplittingField ℚ (IntermediateField.adjoin ℚ {ζ})
        (Polynomial.X ^ n - 1) ∧
      (Polynomial.X ^ n - 1 : Polynomial ℚ).Separable ∧
      IsGalois ℚ (IntermediateField.adjoin ℚ {ζ})

/-- The group isomorphism has the stated exponent action for the chosen root,
and its inverse extends every unit substitution to an automorphism. -/
def CyclotomicGaloisEquivalence : Prop :=
  ∀ (Ω : Type u) [Field Ω] [CharZero Ω] (n : ℕ), 0 < n →
    ∀ ζ : Ω, IsPrimitiveRoot ζ n →
      let E := IntermediateField.adjoin ℚ ({ζ} : Set Ω)
      let root : E := ⟨ζ, IntermediateField.subset_adjoin ℚ {ζ} (Set.mem_singleton ζ)⟩
      ∃ e : (E ≃ₐ[ℚ] E) ≃* (ZMod n)ˣ,
        (∀ σ, (σ root : Ω) = ζ ^ (e σ : ZMod n).val) ∧
        (∀ a, (e.symm a root : Ω) = ζ ^ (a : ZMod n).val)

/-- The Galois group has the same finite order as the unit group. -/
def CyclotomicGaloisOrder : Prop :=
  ∀ (Ω : Type u) [Field Ω] [CharZero Ω] (n : ℕ), 0 < n →
    ∀ ζ : Ω, IsPrimitiveRoot ζ n →
      let E := IntermediateField.adjoin ℚ ({ζ} : Set Ω)
      Finite (E ≃ₐ[ℚ] E) ∧ Nat.card (E ≃ₐ[ℚ] E) = Nat.totient n

/-- In particular, the automorphism group is abelian. -/
def CyclotomicGaloisAbelian : Prop :=
  ∀ (Ω : Type u) [Field Ω] [CharZero Ω] (n : ℕ), 0 < n →
    ∀ ζ : Ω, IsPrimitiveRoot ζ n →
      let E := IntermediateField.adjoin ℚ ({ζ} : Set Ω)
      ∀ σ τ : E ≃ₐ[ℚ] E, σ * τ = τ * σ

/-- Both groups in the isomorphism are trivial at n = 1 and n = 2. -/
def CyclotomicSmallCases : Prop :=
  ∀ (Ω : Type u) [Field Ω] [CharZero Ω] (n : ℕ), n = 1 ∨ n = 2 →
    ∀ ζ : Ω, IsPrimitiveRoot ζ n →
      let E := IntermediateField.adjoin ℚ ({ζ} : Set Ω)
      Subsingleton (E ≃ₐ[ℚ] E) ∧ Subsingleton (ZMod n)ˣ

end Specs.D07.Ch15.CyclotomicGalois
