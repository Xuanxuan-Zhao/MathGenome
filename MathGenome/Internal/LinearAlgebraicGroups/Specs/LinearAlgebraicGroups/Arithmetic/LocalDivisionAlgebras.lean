import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalDivisionRamification
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction

open scoped WithZero
open ValuativeRel

namespace LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {B : Type v} [DivisionRing B] [Algebra F B]

/-- The valuation normalized so that a base uniformizer has value `exp (-1)`. -/
noncomputable abbrev baseValue (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (x : F) : ℤᵐ⁰ :=
  LocalDivisionRamification.normalizedValuation F x

/-- This multiplicative value records `n * w` in additive notation. Thus the
actual value of a nonzero element is minus its logarithm divided by the degree. -/
noncomputable def scaledValue (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (x : B) : ℤᵐ⁰ :=
  baseValue F (_root_.Specs.RM03.CSA.reducedNorm hB x)

/-- Reduced trace is minus the coefficient of degree `n - 1` in the reduced
characteristic polynomial, where `n` is the degree of the algebra. -/
noncomputable abbrev reducedTrace (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (x : B) : F :=
  LocalDivisionNormTraceReduction.reducedTrace hB x

noncomputable abbrev Integers (F : Type u) [Field F] [ValuativeRel F] :=
  LocalDivisionRamification.Integers F

noncomputable abbrev BaseResidue (F : Type u) [Field F] [ValuativeRel F] :=
  LocalDivisionRamification.BaseResidue F

/-- The positive additive valuation ideal in the ring of integers of a division ring. -/
def maximalIdeal (w : Valuation B ℤᵐ⁰) : TwoSidedIdeal w.integer :=
  TwoSidedIdeal.mk' {x | w (x : B) < 1}
    (by simp)
    (fun hx hy => w.map_add_lt hx hy)
    (fun hx => (w.map_neg _).trans_lt hx)
    (fun {x y} hy => by
      change w ((x : B) * (y : B)) < 1
      rw [map_mul]
      exact (mul_le_of_le_one_left' x.2).trans_lt hy)
    (fun {x y} hx => by
      change w ((x : B) * (y : B)) < 1
      rw [map_mul]
      exact (mul_le_of_le_one_right' y.2).trans_lt hx)

abbrev ResidueRing (w : Valuation B ℤᵐ⁰) := (maximalIdeal w).ringCon.Quotient

def residue (w : Valuation B ℤᵐ⁰) : w.integer →+* ResidueRing w :=
  (maximalIdeal w).ringCon.mk'

/-- The bundled valuation satisfies the norm formula and extends the given
valuation, with its exponents multiplied by the degree in this codomain. -/
def IsDivisionValuation (hB : _root_.Specs.RM03.CSA.isCentralSimple F B)
    (w : Valuation B ℤᵐ⁰) : Prop :=
  (∀ x, w x = scaledValue hB x) ∧
  ∀ a, w (algebraMap F B a) = (baseValue F a) ^ _root_.Specs.RM03.CSA.degree F B

def ValuationExists : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B),
    ∃! w : Valuation B ℤᵐ⁰, IsDivisionValuation hB w

/-- Restriction to any commutative subfield yields the unique prolongation of
the base valuation up to equivalence. No separability is imposed. -/
def RestrictionToSubfields : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (w : Valuation B ℤᵐ⁰),
    IsDivisionValuation hB w →
    ∀ {L : Type v} [Field L] [Algebra F L] (i : L →ₐ[F] B)
      {Γ : Type v} [LinearOrderedCommGroupWithZero Γ] (s : Valuation L Γ),
      ((valuation F).IsEquiv (s.comap (algebraMap F L))) → (w.comap i.toRingHom).IsEquiv s

/-- The ring of integers is compact open in the finite-dimensional vector space
topology. Its lattice basis is expressed as an `F`-basis of `B` with integral coordinates. -/
def IntegerLattice : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (w : Valuation B ℤᵐ⁰),
    IsDivisionValuation hB w →
    (∀ b : Module.Basis (Fin (Module.finrank F B)) F B,
      letI : TopologicalSpace B := TopologicalSpace.induced b.equivFun inferInstance
      IsCompact (w.integer : Set B) ∧ IsOpen (w.integer : Set B)) ∧
    ∃ b : Module.Basis (Fin (Module.finrank F B)) F B,
      ∀ x, x ∈ w.integer ↔ ∀ j, b.equivFun x j ∈ Integers F

/-- A field structure on the actual quotient with the scalar map induced by reduction. -/
structure ResidueData (w : Valuation B ℤᵐ⁰) where
  isField : IsField (ResidueRing w)
  finite : Finite (ResidueRing w)
  algebra : letI := isField.toField; Algebra (BaseResidue F) (ResidueRing w)
  map_scalar : letI := isField.toField; letI := algebra
    ∀ (a : Integers F) (x : w.integer), (x : B) = algebraMap F B (a : F) →
      residue w x = algebraMap (BaseResidue F) (ResidueRing w) (IsLocalRing.residue _ a)

def ResidueField : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (w : Valuation B ℤᵐ⁰),
    IsDivisionValuation hB w → Nonempty (ResidueData (F := F) w)

variable (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (w : Valuation B ℤᵐ⁰)

/-- Integral cyclic presentation with right coefficients and the specified residue identification.
The normalized valuation restricts to the base valuation, and the residue extension is separable. -/
structure CyclicPresentation (r : ResidueData (F := F) w) where
  L : Type v
  fieldL : Field L
  algebraL : letI := fieldL; Algebra F L
  embed : letI := fieldL; letI := algebraL; L →ₐ[F] B
  degree : letI := fieldL; letI := algebraL; Module.finrank F L = _root_.Specs.RM03.CSA.degree F B
  centralizer_eq : letI := fieldL; letI := algebraL
    Subalgebra.centralizer F (Set.range embed) = embed.range
  galois : letI := fieldL; letI := algebraL; IsGalois F L
  vL : letI := fieldL; Valuation L ℤᵐ⁰
  surj_vL : Function.Surjective vL
  base_value : ∀ a : F, vL (@algebraMap F L _ _ algebraL a) = baseValue F a
  restrict_val : ∀ a : L, w (embed a) = vL a ^ _root_.Specs.RM03.CSA.degree F B
  residueEquiv : letI := fieldL; letI := r.isField.toField
    IsLocalRing.ResidueField vL.valuationSubring ≃+* ResidueRing w
  residue_separable : letI := r.isField.toField; letI := r.algebra
    Algebra.IsSeparable (BaseResidue F) (ResidueRing w)
  residue_eq : ∀ (a : vL.valuationSubring) (x : w.integer), (x : B) = embed (a : L) →
    residueEquiv (IsLocalRing.residue _ a) = residue w x
  residue_scalar : letI := r.isField.toField; letI := r.algebra
    ∀ (a : Integers F) (b : vL.valuationSubring),
      (b : L) = @algebraMap F L _ _ algebraL (a : F) →
      residueEquiv (IsLocalRing.residue _ b) =
        algebraMap (BaseResidue F) (ResidueRing w) (IsLocalRing.residue _ a)
  residueAutEquiv : letI := fieldL; letI := algebraL
    letI := r.isField.toField; letI := r.algebra
    Gal(L/F) ≃* Gal(ResidueRing w / BaseResidue F)
  residue_aut : letI := fieldL; letI := algebraL
    letI := r.isField.toField; letI := r.algebra
    ∀ (σ : Gal(L/F)) (a b : vL.valuationSubring), (b : L) = σ (a : L) →
      residueEquiv (IsLocalRing.residue _ b) =
        residueAutEquiv σ (residueEquiv (IsLocalRing.residue _ a))
  τ : letI := fieldL; letI := algebraL; L ≃ₐ[F] L
  τ_preserves_value : ∀ a : L, vL (τ a) = vL a
  gen : letI := fieldL; letI := algebraL
    Subgroup.zpowers τ = ⊤
  frobenius : letI := fieldL; letI := r.isField.toField
    ∃ m : ℕ, Nat.Coprime m (_root_.Specs.RM03.CSA.degree F B) ∧
      ∀ (a b : vL.valuationSubring), (b : L) = τ (a : L) →
        residueEquiv (IsLocalRing.residue _ b) =
          residueEquiv (IsLocalRing.residue _ a) ^ (Nat.card (BaseResidue F) ^ m)
  uniformizer : Bˣ
  value_uniformizer : w (uniformizer : B) = WithZero.exp (-1)
  conjugation : ∀ a : L, (uniformizer : B) * embed a = embed (τ a) * (uniformizer : B)
  parameter : F
  value_parameter : baseValue F parameter = WithZero.exp (-1)
  power_uniformizer :
    (uniformizer : B) ^ _root_.Specs.RM03.CSA.degree F B = algebraMap F B parameter
  basis : letI := fieldL; letI := algebraL
    letI := _root_.Specs.RM03.CSA.rightSubfieldModule embed
    Module.Basis (Fin (_root_.Specs.RM03.CSA.degree F B)) L B
  basis_eq : ∀ j, basis j = (uniformizer : B) ^ j.val
  integral_coordinates : letI := fieldL; letI := algebraL
    letI := _root_.Specs.RM03.CSA.rightSubfieldModule embed
    ∀ x : B, x ∈ w.integer ↔ ∀ j, basis.equivFun x j ∈ vL.valuationSubring

/-- The residue and ramification degrees are both the degree of the division
algebra, and an unramified maximal subfield provides the ordered lattice decomposition. -/
def CyclicStructure : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (w : Valuation B ℤᵐ⁰),
    IsDivisionValuation hB w →
    ∀ r : ResidueData (F := F) w, letI := r.isField.toField; letI := r.algebra
      Function.Surjective w ∧
      Module.finrank (BaseResidue F) (ResidueRing w) = _root_.Specs.RM03.CSA.degree F B ∧
      Nonempty (CyclicPresentation (F := F) w r)

/-- Reduced norm and trace on the integral order descend to the ordinary norm
and trace for the residue field extension. -/
def ReductionOfNormTrace : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {B : Type v} [DivisionRing B] [Algebra F B]
    (hB : _root_.Specs.RM03.CSA.isCentralSimple F B) (w : Valuation B ℤᵐ⁰),
    IsDivisionValuation hB w →
    ∀ r : ResidueData (F := F) w, letI := r.isField.toField; letI := r.algebra
      ∀ x : w.integer, ∃ a b : Integers F,
        (a : F) = _root_.Specs.RM03.CSA.reducedNorm hB (x : B) ∧
        (b : F) = reducedTrace hB (x : B) ∧
        IsLocalRing.residue _ a = Algebra.norm (BaseResidue F) (residue w x) ∧
        IsLocalRing.residue _ b = Algebra.trace (BaseResidue F) (ResidueRing w) (residue w x)

end LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras
