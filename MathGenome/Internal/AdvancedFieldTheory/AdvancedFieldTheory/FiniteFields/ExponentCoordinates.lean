import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.ExponentCoordinates
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteFields.FiniteFrobenius
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.RestrictionSystem

/-! # Restriction in exponent coordinates (FT-E05) -/

universe u v
noncomputable section
namespace AdvancedFieldTheory

/-- The ordinary reduction map on residue classes for divisibility of moduli. -/
abbrev finiteResidueReduction {m n : ℕ} (h : m ∣ n) : ZMod n →+* ZMod m :=
  Specs.AdvancedFieldTheory.residueReduction h

@[simp] theorem finiteResidueReduction_intCast {m n : ℕ} (h : m ∣ n) (a : ℤ) :
    finiteResidueReduction h (a : ZMod n) = (a : ZMod m) :=
  map_intCast (finiteResidueReduction h) a

variable (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]

/-- Coordinates with the specified arithmetic Frobenius as generator. -/
def frobeniusExponentCoordinates (n : ℕ) (hn : 0 < n) :
    Multiplicative (ZMod n) ≃*
      (finiteRootField k Ω n ≃ₐ[k] finiteRootField k Ω n) :=
  zmodMulEquivOfGenerator
    (fun σ => by rw [finiteFrobenius_generates k Ω n hn]; trivial)
    (finiteGaloisGroup_card k Ω n hn)

@[simp] theorem frobeniusExponentCoordinates_intCast (n : ℕ) (hn : 0 < n) (a : ℤ) :
    frobeniusExponentCoordinates k Ω n hn (Multiplicative.ofAdd (a : ZMod n)) =
      finiteFrobenius k Ω n ^ a :=
  zmodMulEquivOfGenerator_apply_ofAdd_intCast _ _ a

@[simp] theorem frobeniusExponentCoordinates_one (n : ℕ) (hn : 0 < n) :
    frobeniusExponentCoordinates k Ω n hn (Multiplicative.ofAdd (1 : ZMod n)) =
      finiteFrobenius k Ω n :=
  zmodMulEquivOfGenerator_apply_ofAdd_one _ _

/-- Restriction carries the distinguished generator to the generator below. -/
theorem stageRestriction_finiteFrobenius {m n : ℕ} (h : m ∣ n)
    [IsGalois k (finiteRootField k Ω m)] [IsGalois k (finiteRootField k Ω n)] :
    stageRestriction (finiteRootField_le_of_dvd k Ω h) (finiteFrobenius k Ω n) =
      finiteFrobenius k Ω m := by
  apply DFunLike.ext
  intro x
  apply Subtype.ext
  rw [stageRestriction_apply]
  rfl

/-- The commuting square is an equality of group homomorphisms. -/
theorem frobeniusExponentCoordinates_restriction {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : m ∣ n) [IsGalois k (finiteRootField k Ω m)]
    [IsGalois k (finiteRootField k Ω n)] :
    (stageRestriction (finiteRootField_le_of_dvd k Ω h)).comp
        (frobeniusExponentCoordinates k Ω n hn).toMonoidHom =
      (frobeniusExponentCoordinates k Ω m hm).toMonoidHom.comp
        (AddMonoidHom.toMultiplicative (finiteResidueReduction h).toAddMonoidHom) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective x.toAdd
  have hx : x = Multiplicative.ofAdd (a : ZMod n) :=
    congrArg Multiplicative.ofAdd ha.symm
  -- Every residue has an integer representative; the homomorphism laws
  -- therefore handle negative exponents without a separate inverse argument.
  rw [hx]
  change stageRestriction (finiteRootField_le_of_dvd k Ω h)
      (frobeniusExponentCoordinates k Ω n hn (Multiplicative.ofAdd (a : ZMod n))) =
    frobeniusExponentCoordinates k Ω m hm
      (Multiplicative.ofAdd (finiteResidueReduction h (a : ZMod n)))
  rw [finiteResidueReduction_intCast, frobeniusExponentCoordinates_intCast,
    frobeniusExponentCoordinates_intCast, map_zpow,
    stageRestriction_finiteFrobenius k Ω h]

/-- All positive levels admit compatible Frobenius exponent coordinates. -/
theorem exists_frobeniusExponentCoordinates :
    ∃ coords : ∀ (n : ℕ), 0 < n →
        Multiplicative (ZMod n) ≃*
          (finiteRootField k Ω n ≃ₐ[k] finiteRootField k Ω n),
      (∀ (n : ℕ) (hn : 0 < n) (a : ℤ),
        coords n hn (Multiplicative.ofAdd (a : ZMod n)) = finiteFrobenius k Ω n ^ a) ∧
      (∀ (n : ℕ) (hn : 0 < n),
        coords n hn (Multiplicative.ofAdd (1 : ZMod n)) = finiteFrobenius k Ω n) ∧
      (∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h : m ∣ n),
        ∃ r : (finiteRootField k Ω n ≃ₐ[k] finiteRootField k Ω n) →*
            (finiteRootField k Ω m ≃ₐ[k] finiteRootField k Ω m),
          (∀ (σ : finiteRootField k Ω n ≃ₐ[k] finiteRootField k Ω n)
              (x : finiteRootField k Ω m),
            finiteRootFieldInclusion k Ω h (r σ x) =
              σ (finiteRootFieldInclusion k Ω h x)) ∧
          r.comp (coords n hn).toMonoidHom =
            (coords m hm).toMonoidHom.comp
              (AddMonoidHom.toMultiplicative (finiteResidueReduction h).toAddMonoidHom)) := by
  refine ⟨frobeniusExponentCoordinates k Ω, frobeniusExponentCoordinates_intCast k Ω,
    frobeniusExponentCoordinates_one k Ω, ?_⟩
  intro m n hm hn h
  let := (finiteRootField_finite_galois k Ω m hm).2
  let := (finiteRootField_finite_galois k Ω n hn).2
  refine ⟨stageRestriction (finiteRootField_le_of_dvd k Ω h), ?_,
    frobeniusExponentCoordinates_restriction k Ω hm hn h⟩
  intro σ x
  apply Subtype.ext
  exact stageRestriction_apply (finiteRootField_le_of_dvd k Ω h) σ x

end AdvancedFieldTheory
