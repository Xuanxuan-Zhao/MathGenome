import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CanonicalModuleAndConcentration
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.HypersurfaceExample
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Inverse

noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs
  (residueFieldEnvelopeValue)

namespace Specs.CommutativeAlgebraNotes.HypersurfaceLocalDualityExample

universe u

variable (k : Type u) [Field k]

abbrev Cover := MvPowerSeries (Fin 2) k
abbrev equation : Cover k := MvPowerSeries.X 0 * MvPowerSeries.X 1
abbrev Node := Cover k ⧸ Ideal.span {equation k}
abbrev projection : Cover k →+* Node k := Ideal.Quotient.mk _
abbrev x : Node k := projection k (MvPowerSeries.X 0)
abbrev y : Node k := projection k (MvPowerSeries.X 1)
abbrev generators : List (Node k) := [x k, y k]

instance : IsLocalRing (Node k) :=
  AdvCommAlg.Gorenstein.RegularReduction.quotientLocalRing (equation k) (by
    change ¬ IsUnit (equation k)
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simp [equation])

/-- Regard the sole remaining variable as the variable of a univariate series. -/
def variableEquiv : MvPowerSeries (Fin 1) k ≃+* PowerSeries k :=
  (MvPowerSeries.renameEquiv k (Equiv.ofUnique (Fin 1) PUnit)).toRingEquiv

/-- The outer variable is (x), and the coefficient variable is (y). -/
def iterated : Cover k ≃+* PowerSeries (PowerSeries k) :=
  let e := variableEquiv k
  (MvPowerSeries.finSuccEquiv k 1).toRingEquiv.trans <|
    RingEquiv.ofBijective (PowerSeries.map e.toRingHom)
      ⟨PowerSeries.map_injective _ e.injective, PowerSeries.map_surjective _ e.surjective⟩

@[simp] theorem iterated_X_zero : iterated k (MvPowerSeries.X 0) = PowerSeries.X := by
  change PowerSeries.map (variableEquiv k).toRingHom
    (MvPowerSeries.finSuccEquiv k 1 (MvPowerSeries.X 0)) = _
  simp

@[simp] theorem iterated_X_one : iterated k (MvPowerSeries.X 1) = PowerSeries.C PowerSeries.X := by
  change PowerSeries.map (variableEquiv k).toRingHom
    (MvPowerSeries.finSuccEquiv k 1 (MvPowerSeries.X (Fin.succ 0))) = _
  rw [MvPowerSeries.finSuccEquiv_X_succ, PowerSeries.map_C]
  simp [PowerSeries.X, variableEquiv]

def xBranchOnCover : Cover k →+* PowerSeries k :=
  (PowerSeries.map PowerSeries.constantCoeff).comp (iterated k).toRingHom

def yBranchOnCover : Cover k →+* PowerSeries k :=
  PowerSeries.constantCoeff.comp (iterated k).toRingHom

def xBranch : Node k →+* PowerSeries k :=
  Ideal.Quotient.lift _ (xBranchOnCover k) (by
    change Ideal.span {equation k} ≤ RingHom.ker (xBranchOnCover k)
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    simp [xBranchOnCover, equation])

def yBranch : Node k →+* PowerSeries k :=
  Ideal.Quotient.lift _ (yBranchOnCover k) (by
    change Ideal.span {equation k} ≤ RingHom.ker (yBranchOnCover k)
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    simp [yBranchOnCover, equation])

def branches : Node k →+* PowerSeries k × PowerSeries k :=
  (xBranch k).prod (yBranch k)

abbrev SeriesFraction := LaurentSeries k
def xFraction : Node k →+* SeriesFraction k :=
  (algebraMap (PowerSeries k) (SeriesFraction k)).comp (xBranch k)
def yFraction : Node k →+* SeriesFraction k :=
  (algebraMap (PowerSeries k) (SeriesFraction k)).comp (yBranch k)

def fractionPair : Node k →+* SeriesFraction k × SeriesFraction k :=
  (xFraction k).prod (yFraction k)

instance : Algebra (Node k) (SeriesFraction k × SeriesFraction k) :=
  (fractionPair k).toAlgebra

instance (priority := 1200) : Module (Node k) (SeriesFraction k × SeriesFraction k) :=
  Algebra.toModule

def diagonal : Node k →ₗ[Node k] SeriesFraction k × SeriesFraction k :=
  Algebra.linearMap _ _

abbrev ExplicitHull := (SeriesFraction k × SeriesFraction k) ⧸ (diagonal k).range
abbrev ringModule := ModuleCat.of (Node k) (Node k)
abbrev residueModule := ModuleCat.of (Node k) (ResidueField (Node k))
abbrev cohomology (i : ℤ) :=
  IdealTorsion.localCohomology (maximalIdeal (Node k)) i
abbrev ringCech := AugmentedCechComplex.complex (Node k) (generators k)
abbrev residueCech :=
  AugmentedCechComplex.coefficients (Node k) (generators k) (residueModule k)

def StructureType : Prop :=
  ∀ (k : Type u) [Field k],
    IsAdicComplete (maximalIdeal (Node k)) (Node k) ∧
    ringKrullDim (Node k) = 1 ∧
    AdvCommAlg.Gorenstein.Specs.LocalGorensteinValue (Node k) ∧
    Ideal.span {a | a ∈ generators k} = maximalIdeal (Node k) ∧
    ∃ e : ResidueField (Node k) ≃+* k, ∀ a : Node k,
      e (residue (Node k) a) = PowerSeries.constantCoeff (xBranch k a)

def CoordinatesType : Prop :=
  ∀ (k : Type u) [Field k], Function.Injective (branches k) ∧
    ∀ (a b : PowerSeries k),
      (∃ r : Node k, branches k r = (a, b)) ↔
        PowerSeries.constantCoeff a = PowerSeries.constantCoeff b

def BranchLocalizationsType : Prop :=
  ∀ (k : Type u) [Field k],
    (letI := (xFraction k).toAlgebra
     IsLocalization.Away (x k) (SeriesFraction k)) ∧
    (letI := (yFraction k).toAlgebra
     IsLocalization.Away (y k) (SeriesFraction k))

def RingCechType : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ (e₀ : (ringCech k).X 0 ≅ ringModule k)
      (e₁ : (ringCech k).X 1 ≅ ModuleCat.of (Node k) (SeriesFraction k × SeriesFraction k)),
      (ringCech k).d 0 1 ≫ e₁.hom = e₀.hom ≫ ModuleCat.ofHom (diagonal k) ∧
      ∀ i : ℤ, i ≠ 0 → i ≠ 1 → IsZero ((ringCech k).X i)

def CoverExtType : Prop :=
  ∀ (k : Type u) [Field k],
    Nonempty (AdvCommAlg.Gorenstein.ConcentratedChangeOfRings.coefficient
      (projection k) (ModuleCat.of (Cover k) (Cover k)) 1 ≃ₗ[Node k] Node k)

def CanonicalType : Prop :=
  ∀ (k : Type u) [Field k] (E : residueFieldEnvelopeValue (Node k)),
    Nonempty (CanonicalModuleAndConcentration.canonicalModule
      (CechDualizingComplexModel.cechDual E (generators k)) 1 ≅ ringModule k) ∧
    ∀ J : RegularCoverDualizingModel.ShiftedRingResolution (Cover k) 2,
      Nonempty (CanonicalModuleAndConcentration.canonicalModule
        (RegularCoverDualizingModel.dualizingComplex (projection k) J.complex) 1 ≅
          ringModule k)

def CohomologyType : Prop :=
  ∀ (k : Type u) [Field k],
    IsZero ((cohomology k 0).obj (ringModule k)) ∧
    Nonempty ((cohomology k 1).obj (ringModule k) ≅ ModuleCat.of (Node k) (ExplicitHull k)) ∧
    (∀ E : residueFieldEnvelopeValue (Node k),
      Nonempty ((cohomology k 1).obj (ringModule k) ≅ ModuleCat.of (Node k) E.carrier)) ∧
    (∀ i : ℤ, 0 < i → IsZero ((residueCech k).X i)) ∧
    Nonempty ((cohomology k 0).obj (residueModule k) ≅ residueModule k) ∧
    IsZero ((cohomology k 1).obj (residueModule k))

end Specs.CommutativeAlgebraNotes.HypersurfaceLocalDualityExample
