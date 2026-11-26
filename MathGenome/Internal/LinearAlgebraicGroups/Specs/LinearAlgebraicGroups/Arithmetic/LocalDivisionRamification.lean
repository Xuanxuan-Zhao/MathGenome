import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.FieldTheory.Galois.Basic
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Degree

open scoped WithZero
open ValuativeRel

namespace LinearAlgebraicGroups.Arithmetic.LocalDivisionRamification

universe u v z

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {B : Type v} [DivisionRing B] [Algebra F B]

noncomputable abbrev Integers (F : Type*) [Field F] [ValuativeRel F] :=
  (valuation F).valuationSubring

noncomputable abbrev BaseResidue (F : Type*) [Field F] [ValuativeRel F] :=
  IsLocalRing.ResidueField (Integers F)

/-- The normalized multiplicative valuation of a local field. -/
noncomputable def normalizedValuation (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : Valuation K ℤᵐ⁰ :=
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  (valuation K).map ⟨e.toMulEquiv.toMonoidWithZeroHom, e.toOrderIso.monotone⟩

/-- Input from the construction of the division valuation and its residue quotient.
The exponents of the division valuation are scaled by the degree `n`. -/
structure IntegralReduction (n : ℕ) (w : Valuation B ℤᵐ⁰)
    (κ : Type z) [Field κ] [Algebra (BaseResidue F) κ] where
  scalar_value : ∀ a : F, w (algebraMap F B a) = normalizedValuation F a ^ n
  lattice : ∃ b : Module.Basis (Fin (Module.finrank F B)) F B,
    ∀ x, x ∈ w.integer ↔ ∀ j, b.equivFun x j ∈ Integers F
  reduction : w.integer →+* κ
  onto : Function.Surjective reduction
  ker : ∀ x : w.integer, reduction x = 0 ↔ w (x : B) < 1
  scalar_reduction : ∀ (a : Integers F) (x : w.integer), (x : B) = algebraMap F B (a : F) →
    reduction x = algebraMap (BaseResidue F) κ (IsLocalRing.residue _ a)

/-- An unramified subfield with residue field identified with the division residue
field. The value comparison on base scalars gives ramification index one, and
the identified residue field is separable over the base residue field. -/
structure UnramifiedSubfield {n : ℕ} {w : Valuation B ℤᵐ⁰} {κ : Type z}
    [Field κ] [Algebra (BaseResidue F) κ] (r : IntegralReduction (F := F) n w κ) where
  L : Type v
  fieldL : Field L
  algebraL : letI := fieldL; Algebra F L
  embed : letI := fieldL; letI := algebraL; L →ₐ[F] B
  degree : letI := fieldL; letI := algebraL; Module.finrank F L = n
  galois : letI := fieldL; letI := algebraL; IsGalois F L
  cyclic : letI := fieldL; letI := algebraL; IsCyclic (L ≃ₐ[F] L)
  residue_separable : Algebra.IsSeparable (BaseResidue F) κ
  vL : letI := fieldL; Valuation L ℤᵐ⁰
  onto_vL : Function.Surjective vL
  base_value : ∀ a : F, vL (@algebraMap F L _ _ algebraL a) = normalizedValuation F a
  restrict_value : ∀ a : L, w (embed a) = vL a ^ n
  residueEquiv : letI := fieldL; IsLocalRing.ResidueField vL.valuationSubring ≃+* κ
  residue_eq : ∀ (a : vL.valuationSubring) (x : w.integer), (x : B) = embed (a : L) →
    residueEquiv (IsLocalRing.residue _ a) = r.reduction x
  residue_scalar : ∀ (a : Integers F) (b : vL.valuationSubring),
    (b : L) = @algebraMap F L _ _ algebraL (a : F) →
    residueEquiv (IsLocalRing.residue _ b) =
      algebraMap (BaseResidue F) κ (IsLocalRing.residue _ a)
  autEquiv : letI := fieldL; letI := algebraL; (L ≃ₐ[F] L) ≃* (κ ≃ₐ[BaseResidue F] κ)
  value_aut : letI := fieldL; letI := algebraL; ∀ (σ : L ≃ₐ[F] L) (a : L), vL (σ a) = vL a
  residue_aut : letI := fieldL; letI := algebraL
    ∀ (σ : L ≃ₐ[F] L) (a b : vL.valuationSubring), (b : L) = σ (a : L) →
      autEquiv σ (residueEquiv (IsLocalRing.residue _ a)) =
        residueEquiv (IsLocalRing.residue _ b)

/-- The division value group is all of the scaled integer group, the residue
degree is the degree of the algebra, and the embedded unramified field realizes
that residue extension with its full Galois action. -/
def Ramification : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {B : Type v} [DivisionRing B] [Algebra F B]
    (_ : _root_.Specs.RM03.CSA.isCentralSimple F B)
    {κ : Type z} [Field κ] [Finite κ] [Algebra (BaseResidue F) κ]
    {w : Valuation B ℤᵐ⁰} (r : IntegralReduction (F := F) (_root_.Specs.RM03.CSA.degree F B) w κ),
    Function.Surjective w ∧ Module.finrank (BaseResidue F) κ = _root_.Specs.RM03.CSA.degree F B ∧
      Nonempty (UnramifiedSubfield r)

end LinearAlgebraicGroups.Arithmetic.LocalDivisionRamification
