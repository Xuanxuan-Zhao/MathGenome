import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.FieldTheory.Galois.Basic
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.SubfieldSplitting

open scoped WithZero
open ValuativeRel

namespace LinearAlgebraicGroups.Arithmetic.LocalDivisionCyclicPresentation

universe u v w z

/-- The base valuation, normalized to give a uniformizer value `exp (-1)`. -/
noncomputable abbrev normalizedValue (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a : F) : ℤᵐ⁰ :=
  IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F (valuation F a)

noncomputable abbrev BaseResidue (F : Type u) [Field F] [ValuativeRel F] :=
  IsLocalRing.ResidueField (valuation F).valuationSubring

/-- The normalizing uniformizer and its ordered right basis, for the given
embedded subfield and the specified residue action. -/
def CyclicPresentation : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {B : Type v} [DivisionRing B] [Algebra F B],
    _root_.Specs.RM03.CSA.isCentralSimple F B →
    let n := _root_.Specs.RM03.CSA.degree F B
    ∀ (vB : Valuation B ℤᵐ⁰),
      (∀ a : F, vB (algebraMap F B a) = normalizedValue F a ^ n) →
      Function.Surjective vB →
    ∀ {L : Type w} [Field L] [Algebra F L] [IsGalois F L] (i : L →ₐ[F] B),
      Module.finrank F L = n →
    ∀ (vL : Valuation L ℤᵐ⁰), Function.Surjective vL →
      (∀ a : L, vB (i a) = vL a ^ n) →
    ∀ {ℓ : Type z} [Field ℓ] [Finite ℓ] [Algebra (BaseResidue F) ℓ]
      (red : vB.integer →+* ℓ),
      Function.Surjective red →
      (∀ x : vB.integer, red x = 0 ↔ vB (x : B) < 1) →
      (∀ (a : (valuation F).valuationSubring) (x : vB.integer),
        (x : B) = algebraMap F B (a : F) →
        red x = algebraMap (BaseResidue F) ℓ (IsLocalRing.residue _ a)) →
    ∀ (res : IsLocalRing.ResidueField vL.valuationSubring ≃+* ℓ),
      (∀ (a : vL.valuationSubring) (x : vB.integer), (x : B) = i (a : L) →
        res (IsLocalRing.residue _ a) = red x) →
    ∀ (reduce : Gal(L/F) ≃* Gal(ℓ/BaseResidue F)),
      (∀ (σ : Gal(L/F)) (a b : vL.valuationSubring), (b : L) = σ (a : L) →
        res (IsLocalRing.residue _ b) = reduce σ (res (IsLocalRing.residue _ a))) →
    letI := _root_.Specs.RM03.CSA.rightSubfieldModule i
    Subalgebra.centralizer F (Set.range i) = i.range ∧
    ∃ (pi : Bˣ) (τ : Gal(L/F)) (t : F) (basis : Module.Basis (Fin n) L B),
      vB (pi : B) = WithZero.exp (-1) ∧
      (∀ a : L, (pi : B) * i a = i (τ a) * (pi : B)) ∧
      (∀ a : L, vL (τ a) = vL a) ∧
      Subgroup.zpowers τ = ⊤ ∧
      (∃ m : ℕ, Nat.Coprime m n ∧
        ∀ y : ℓ, reduce τ y = y ^ (Nat.card (BaseResidue F) ^ m)) ∧
      normalizedValue F t = WithZero.exp (-1) ∧
      (pi : B) ^ n = algebraMap F B t ∧
      (∀ j, basis j = (pi : B) ^ j.val) ∧
      (∀ x : B, x ∈ vB.integer ↔ ∀ j, basis.equivFun x j ∈ vL.valuationSubring)

end LinearAlgebraicGroups.Arithmetic.LocalDivisionCyclicPresentation
