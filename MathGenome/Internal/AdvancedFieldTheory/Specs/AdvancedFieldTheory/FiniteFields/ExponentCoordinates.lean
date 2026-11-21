import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.FiniteFrobenius
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
Independent specification of FT-E05 (notes/003/advanced-field-theory.tex:
1161–1188). The additive residue groups use the `Multiplicative` wrapper.
The restriction homomorphisms are characterized by their action along the
literal inclusions, so no additional Galois-instance hypotheses are needed.
The conclusion constructs one family of coordinates simultaneously at all
positive levels, together with its commuting restriction squares.
-/

universe u v
noncomputable section
namespace Specs.AdvancedFieldTheory

/-- Ordinary residue reduction, retaining its canonical ring structure. -/
def residueReduction {m n : ℕ} (h : m ∣ n) : ZMod n →+* ZMod m :=
  ZMod.castHom h (ZMod m)

set_option linter.checkUnivs false in
def finiteResidueReduction_type := ∀ {m n : ℕ}, m ∣ n → (ZMod n →+* ZMod m)

def finiteResidueReduction_value : finiteResidueReduction_type := @residueReduction

def finiteResidueReduction_intCast_type : Prop :=
  ∀ {m n : ℕ} (h : m ∣ n) (a : ℤ), residueReduction h (a : ZMod n) = (a : ZMod m)

/-- Full exponent-coordinate isomorphisms, including all integer exponents
and literal restriction, as an equality of homomorphisms. The action condition
identifies each `r` uniquely with restriction to the included smaller field. -/
def exists_frobeniusExponentCoordinates_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
  ∃ coords : ∀ (n : ℕ), 0 < n →
      Multiplicative (ZMod n) ≃* (rootField k Ω n ≃ₐ[k] rootField k Ω n),
    (∀ (n : ℕ) (hn : 0 < n) (a : ℤ),
      coords n hn (Multiplicative.ofAdd (a : ZMod n)) = layerFrobenius k Ω n ^ a) ∧
    (∀ (n : ℕ) (hn : 0 < n),
      coords n hn (Multiplicative.ofAdd (1 : ZMod n)) = layerFrobenius k Ω n) ∧
    (∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h : m ∣ n),
      ∃ r : (rootField k Ω n ≃ₐ[k] rootField k Ω n) →*
          (rootField k Ω m ≃ₐ[k] rootField k Ω m),
        (∀ (σ : rootField k Ω n ≃ₐ[k] rootField k Ω n) (x : rootField k Ω m),
          rootFieldInclusion k Ω h (r σ x) = σ (rootFieldInclusion k Ω h x)) ∧
        r.comp (coords n hn).toMonoidHom =
          (coords m hm).toMonoidHom.comp
            (AddMonoidHom.toMultiplicative (residueReduction h).toAddMonoidHom))

end Specs.AdvancedFieldTheory
