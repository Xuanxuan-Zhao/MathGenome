import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.MatlisDualFunctor
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.FiniteLength

/-! The finite stages of the residue-field injective hull in M02. -/

noncomputable section

open IsLocalRing

namespace CommutativeAlgebraNotes.InjectiveHullTruncationSpecs

open MatlisDualFunctorSpecs

universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The (n)-th maximal-ideal quotient, with its usual (R)-algebra structure. -/
abbrev TruncationRing (R : Type u) [CommRing R] [IsLocalRing R] (n : ℕ) :=
  R ⧸ (maximalIdeal R ^ n)

/-- The annihilator of the (n)-th power inside the displayed injective hull. -/
abbrev hullTruncation (E : residueFieldEnvelopeValue R) (n : ℕ) : Submodule R E.carrier :=
  Submodule.torsionBySet R E.carrier (↑(maximalIdeal R ^ n) : Set R)

abbrev TruncationRingType :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R], ℕ → Type u

abbrev HullTruncationType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R),
    ℕ → Submodule R E.carrier

def unionType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue R), (⨆ n : ℕ, hullTruncation E (n + 1)) = ⊤

def unionMembershipType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue R) (x : E.carrier), ∃ n : ℕ, 1 ≤ n ∧ x ∈ hullTruncation E n

def quotientScalarType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    (n : ℕ) (r : R) (x : hullTruncation E n),
      Ideal.Quotient.mk (maximalIdeal R ^ n) r • x = r • x

/-- The canonical action on (k) is via the quotient map (A_n 	o k). -/
abbrev truncationResidueMap (n : ℕ) (hn : 1 ≤ n) : TruncationRing R n →+* ResidueField R :=
  Ideal.Quotient.factor (Ideal.pow_le_self (Nat.ne_of_gt hn))

abbrev TruncationResidueMapType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (n : ℕ), 1 ≤ n →
    (TruncationRing R n →+* ResidueField R)

abbrev truncationResidueModule (n : ℕ) (hn : 1 ≤ n) :
    Module (TruncationRing R n) (ResidueField R) :=
  Module.compHom (ResidueField R) (truncationResidueMap n hn)

abbrev TruncationResidueModuleType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (n : ℕ), 1 ≤ n →
    Module (TruncationRing R n) (ResidueField R)

theorem truncationResidueTower (n : ℕ) (hn : 1 ≤ n) :
    letI := truncationResidueModule (R := R) n hn
    IsScalarTower R (TruncationRing R n) (ResidueField R) := by
  let _ := truncationResidueModule (R := R) n hn
  constructor
  intro r a x
  change truncationResidueMap n hn (r • a) * x =
    residue R r * (truncationResidueMap n hn a * x)
  rw [Algebra.smul_def, map_mul, mul_assoc]
  rfl

/-- The given inclusion (khookrightarrow E), corestricted and made linear over (A_n). -/
def truncationResidueInclusion (E : residueFieldEnvelopeValue R) (n : ℕ) (hn : 1 ≤ n) :
    letI := truncationResidueModule (R := R) n hn
    ResidueField R →ₗ[TruncationRing R n] hullTruncation E n := by
  letI := truncationResidueModule (R := R) n hn
  letI := truncationResidueTower (R := R) n hn
  refine LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    (E.inclusion.codRestrict (hullTruncation E n) fun x => ?_)
  apply (Submodule.mem_torsionBySet_iff _ _).2
  intro a
  have h : residue R a = 0 :=
    (residue_eq_zero_iff _).2 (Ideal.pow_le_self (Nat.ne_of_gt hn) a.property)
  change (a : R) • E.inclusion x = 0
  rw [← map_smul, show (a : R) • x = residue R a * x from rfl, h, zero_mul, map_zero]

abbrev TruncationResidueInclusionType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    (n : ℕ) (hn : 1 ≤ n), letI := truncationResidueModule (R := R) n hn
    ResidueField R →ₗ[TruncationRing R n] hullTruncation E n

def truncationEnvelopeType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    (n : ℕ) (hn : 1 ≤ n), letI := truncationResidueModule (R := R) n hn
    AdvCommAlg.Gorenstein.IsInjectiveEnvelope (truncationResidueInclusion E n hn)

def truncationResidueInclusionApplyType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    (n : ℕ) (hn : 1 ≤ n) (x : ResidueField R),
      (truncationResidueInclusion E n hn x).val = E.inclusion x

/-- An (A_n)-module is annihilated by (mathfrak m^n) after restriction. -/
theorem pow_smul_zero (n : ℕ) {T : Type v} [AddCommGroup T]
    [Module R T] [Module (TruncationRing R n) T] [IsScalarTower R (TruncationRing R n) T]
    {r : R} (hr : r ∈ maximalIdeal R ^ n) (t : T) : r • t = 0 := by
  rw [algebra_compatible_smul (TruncationRing R n)]
  change Ideal.Quotient.mk (maximalIdeal R ^ n) r • t = 0
  rw [(Ideal.Quotient.eq_zero_iff_mem).2 hr, zero_smul]

/-- Restriction of scalars followed by the submodule inclusion identifies the two Hom modules. -/
def truncationHomEquiv (E : residueFieldEnvelopeValue R) (n : ℕ)
    (T : Type v) [AddCommGroup T] [Module R T] [Module (TruncationRing R n) T]
    [IsScalarTower R (TruncationRing R n) T] :
    (T →ₗ[TruncationRing R n] hullTruncation E n) ≃ₗ[R] matlisDualModuleValue E T where
  toFun f := (hullTruncation E n).subtype.comp (f.restrictScalars R)
  invFun f := LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    (f.codRestrict (hullTruncation E n) fun t => by
      apply (Submodule.mem_torsionBySet_iff _ _).2
      intro a
      change (a : R) • f t = 0
      rw [← f.map_smul, pow_smul_zero n a.property t, f.map_zero])
  left_inv f := LinearMap.ext fun x => Subtype.ext rfl
  right_inv f := LinearMap.ext fun x => rfl
  map_add' f g := LinearMap.ext fun x => rfl
  map_smul' r f := LinearMap.ext fun x => rfl

set_option linter.checkUnivs false in
abbrev TruncationHomEquivType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R) (n : ℕ)
    (T : Type v) [AddCommGroup T] [Module R T] [Module (TruncationRing R n) T]
    [IsScalarTower R (TruncationRing R n) T],
    (T →ₗ[TruncationRing R n] hullTruncation E n) ≃ₗ[R] matlisDualModuleValue E T

def truncationHomNaturalityType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R) (n : ℕ)
    {T : Type v} {U : Type w} [AddCommGroup T] [AddCommGroup U]
    [Module R T] [Module R U] [Module (TruncationRing R n) T] [Module (TruncationRing R n) U]
    [IsScalarTower R (TruncationRing R n) T] [IsScalarTower R (TruncationRing R n) U]
    (g : T →ₗ[TruncationRing R n] U) (f : U →ₗ[TruncationRing R n] hullTruncation E n),
      truncationHomEquiv E n T (f.comp g) =
      (truncationHomEquiv E n U f).comp (g.restrictScalars R)

/-- The Hom identification on (A_n) is evaluation at its unit. -/
def truncationEval (E : residueFieldEnvelopeValue R) (n : ℕ) :
    matlisDualModuleValue E (TruncationRing R n) ≃ₗ[R] hullTruncation E n :=
  (truncationHomEquiv E n (TruncationRing R n)).symm.trans
    (LinearMap.ringLmapEquivSelf (TruncationRing R n) R (hullTruncation E n))

abbrev TruncationEvalType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R) (n : ℕ),
    matlisDualModuleValue E (TruncationRing R n) ≃ₗ[R] hullTruncation E n

def truncationEvalApplyType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    (n : ℕ) (f : matlisDualModuleValue E (TruncationRing R n)),
      (truncationEval E n f).val = f 1

def truncationEvalNaturalityType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    {m n : ℕ} (h : m ≤ n) (f : matlisDualModuleValue E (TruncationRing R m)),
      truncationEval E n
        (matlisDualMapValue E (Submodule.factor (Ideal.pow_le_pow_right h)) f) =
      Submodule.inclusion (Submodule.torsionBySet_le_torsionBySet_pow m n h (maximalIdeal R))
        (truncationEval E m f)

private theorem dualTorsion (E : residueFieldEnvelopeValue R) (n : ℕ) :
    Module.IsTorsionBySet R (matlisDualModuleValue E (TruncationRing R n))
      (↑(maximalIdeal R ^ n) : Set R) := by
  intro f r
  apply LinearMap.ext
  intro x
  change (r : R) • f x = 0
  rw [← f.map_smul, pow_smul_zero n r.property x, f.map_zero]

/-- The ordinary (R)-action on the Matlis dual of (A_n) descends to (A_n). -/
abbrev truncationDualModule (E : residueFieldEnvelopeValue R) (n : ℕ) :
    Module (TruncationRing R n) (matlisDualModuleValue E (TruncationRing R n)) :=
  (dualTorsion E n).module

abbrev TruncationDualModuleType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R) (n : ℕ),
    Module (TruncationRing R n) (matlisDualModuleValue E (TruncationRing R n))

def truncationDualScalarType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R)
    (n : ℕ) (a x : TruncationRing R n) (f : matlisDualModuleValue E (TruncationRing R n)),
    letI := truncationDualModule E n
    (a • f) x = f (a * x)

/-- Evaluation is linear over the quotient for the descended action on the dual. -/
def truncationEvalOverQuotient (E : residueFieldEnvelopeValue R) (n : ℕ) :
    letI := truncationDualModule E n
    matlisDualModuleValue E (TruncationRing R n) ≃ₗ[TruncationRing R n] hullTruncation E n :=
  letI := truncationDualModule E n
  letI := (dualTorsion E n).isScalarTower (S := R)
  (truncationEval E n).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

abbrev TruncationEvalOverQuotientType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (E : residueFieldEnvelopeValue R) (n : ℕ),
    letI := truncationDualModule E n
    matlisDualModuleValue E (TruncationRing R n) ≃ₗ[TruncationRing R n] hullTruncation E n

def truncationRingLocalType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (n : ℕ), 1 ≤ n →
    IsLocalRing (TruncationRing R n)

def truncationResidueMapSurjectiveKerType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (n : ℕ) [IsLocalRing (TruncationRing R n)]
    (hn : 1 ≤ n), Function.Surjective (truncationResidueMap (R := R) n hn) ∧
      RingHom.ker (truncationResidueMap (R := R) n hn) = maximalIdeal (TruncationRing R n)

def truncationFiniteLengthType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (E : residueFieldEnvelopeValue R) (n : ℕ), 1 ≤ n →
    IsFiniteLength (TruncationRing R n) (TruncationRing R n) ∧
    IsFiniteLength (TruncationRing R n) (hullTruncation E n) ∧
    IsFiniteLength R (TruncationRing R n) ∧ IsFiniteLength R (hullTruncation E n)

end CommutativeAlgebraNotes.InjectiveHullTruncationSpecs
