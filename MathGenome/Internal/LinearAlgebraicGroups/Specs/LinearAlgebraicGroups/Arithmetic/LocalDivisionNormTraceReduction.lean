import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.NormTrace
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.ReducedNorm
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.SubfieldSplitting

open scoped WithZero
open ValuativeRel

namespace LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction

universe u v w z

variable {F : Type u} [Field F] {B : Type v} [DivisionRing B] [Algebra F B]

/-- The multiplicative valuation sending a base uniformizer to `exp (-1)`. -/
noncomputable def baseValue (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (a : F) : ℤᵐ⁰ :=
  IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F (valuation F a)

noncomputable abbrev Integers (F : Type u) [Field F] [ValuativeRel F] :=
  (valuation F).valuationSubring

noncomputable abbrev BaseResidue (F : Type u) [Field F] [ValuativeRel F] :=
  IsLocalRing.ResidueField (Integers F)

/-- The reduced trace is the negative coefficient immediately below the leading term. -/
noncomputable def reducedTrace (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (x : B) : F :=
  -(_root_.Specs.RM03.CSA.reducedCharpoly hB x).coeff (_root_.Specs.RM03.CSA.degree F B - 1)

/-- In an integral cyclic presentation, reduced norm and trace descend to the
field norm and trace on the residue extension. -/
def ReductionOfNormTrace : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (vB : Valuation B ℤᵐ⁰),
    let n := _root_.Specs.RM03.CSA.degree F B
    (∀ a, vB (algebraMap F B a) = baseValue F a ^ n) →
    ∀ {L : Type w} [Field L] [Algebra F L] [IsGalois F L] (i : L →ₐ[F] B)
      (vL : Valuation L ℤᵐ⁰),
    Module.finrank F L = n →
    Function.Surjective vL →
    (∀ a, vB (i a) = vL a ^ n) →
    ∀ (τ : L ≃ₐ[F] L), Subgroup.zpowers τ = ⊤ →
    ∀ (π : Bˣ) (t : F),
    vB (π : B) = WithZero.exp (-1) →
    baseValue F t = WithZero.exp (-1) →
    (∀ a, (π : B) * i a = i (τ a) * (π : B)) →
    (π : B) ^ n = algebraMap F B t →
    letI := _root_.Specs.RM03.CSA.rightSubfieldModule i
    ∀ (b : Module.Basis (Fin n) L B),
    (∀ j, b j = (π : B) ^ (j : ℕ)) →
    (∀ x : B, x ∈ vB.integer ↔ ∀ j, b.repr x j ∈ vL.valuationSubring) →
    ∀ {ℓ : Type z} [Field ℓ] [Finite ℓ] [Algebra (BaseResidue F) ℓ]
      (r : vB.integer →+* ℓ),
    (∀ x : vB.integer, r x = 0 ↔ vB (x : B) < 1) →
    (∀ (a : Integers F) (x : vB.integer), (x : B) = algebraMap F B (a : F) →
      r x = algebraMap (BaseResidue F) ℓ (IsLocalRing.residue _ a)) →
    ∀ (e : IsLocalRing.ResidueField vL.valuationSubring ≃+* ℓ),
    (∀ (a : vL.valuationSubring) (x : vB.integer), (x : B) = i (a : L) →
      r x = e (IsLocalRing.residue _ a)) →
    ∀ (g : (L ≃ₐ[F] L) ≃* (ℓ ≃ₐ[BaseResidue F] ℓ)),
    (∀ (σ : L ≃ₐ[F] L) (a a' : vL.valuationSubring), (a' : L) = σ (a : L) →
      e (IsLocalRing.residue _ a') = g σ (e (IsLocalRing.residue _ a))) →
    ∀ x : vB.integer, ∃ a b : Integers F,
      (a : F) = _root_.Specs.RM03.CSA.reducedNorm hB (x : B) ∧
      (b : F) = reducedTrace hB (x : B) ∧
      IsLocalRing.residue _ a = Algebra.norm (BaseResidue F) (r x) ∧
      IsLocalRing.residue _ b = Algebra.trace (BaseResidue F) ℓ (r x)

end LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction
