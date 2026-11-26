import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.DerivedCechComparison
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Inverse

open CategoryTheory HomologicalComplex

namespace Specs.CommutativeAlgebraNotes.TwoDegreeExampleCechCalculation

universe u

noncomputable section

variable (k : Type u) [Field k]

abbrev S := MvPowerSeries (Fin 2) k
abbrev SX : S k := MvPowerSeries.X 0
abbrev SY : S k := MvPowerSeries.X (Fin.succ (0 : Fin 1))
abbrev J : Ideal (S k) := Ideal.span {SX k ^ 2, SX k * SY k}
abbrev R := S k ⧸ J k
abbrev x : R k := Ideal.Quotient.mk (J k) (SX k)
abbrev y : R k := Ideal.Quotient.mk (J k) (SY k)
abbrev A := PowerSeries k
abbrev L := LaurentSeries k

/-- Identifying the remaining one-variable series with ordinary formal power series. -/
def oneVariable : MvPowerSeries (Fin 1) k →+* A k :=
  (PowerSeries.map (MvPowerSeries.constantCoeff (σ := Fin 0) (R := k))).comp
    (MvPowerSeries.finSuccEquiv k 0).toRingHom

/-- Specializing the variable x to zero, with y retained as the power-series variable. -/
noncomputable def projectS : S k →+* A k :=
  (oneVariable k).comp
    (PowerSeries.constantCoeff.comp (MvPowerSeries.finSuccEquiv k 1).toRingHom)

@[simp] theorem projectS_X : projectS k (SX k) = 0 := by
  simp [projectS, SX]

@[simp] theorem projectS_Y : projectS k (SY k) = PowerSeries.X := by
  change PowerSeries.map MvPowerSeries.constantCoeff
    (MvPowerSeries.finSuccEquiv k 0
      (PowerSeries.constantCoeff (MvPowerSeries.finSuccEquiv k 1
        (MvPowerSeries.X (Fin.succ (0 : Fin 1)))))) = PowerSeries.X
  rw [MvPowerSeries.finSuccEquiv_X_succ, PowerSeries.constantCoeff_C,
    MvPowerSeries.finSuccEquiv_X_zero, PowerSeries.map_X]

noncomputable def project : R k →+* A k :=
  Ideal.Quotient.lift (J k) (projectS k) fun _ h =>
    (Ideal.span_le.2 (by simp [Set.insert_subset_iff, RingHom.mem_ker]) h :
      _ ∈ RingHom.ker (projectS k))

def oneVariableInverse : A k →+* MvPowerSeries (Fin 1) k :=
  (MvPowerSeries.finSuccEquiv k 0).symm.toRingHom.comp
    (PowerSeries.map (MvPowerSeries.C (σ := Fin 0) (R := k)))

/-- The inclusion of series in y alone before passing to the quotient. -/
noncomputable def sectionS : A k →+* S k :=
  (MvPowerSeries.finSuccEquiv k 1).symm.toRingHom.comp
    (PowerSeries.C.comp (oneVariableInverse k))

noncomputable def sectionR : A k →+* R k := (Ideal.Quotient.mk (J k)).comp (sectionS k)

instance : Nontrivial (R k) := (project k).domain_nontrivial

instance : IsLocalRing (R k) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (J k)) Ideal.Quotient.mk_surjective

noncomputable instance : Algebra (R k) (A k) := (project k).toAlgebra
noncomputable instance : Algebra (R k) (L k) :=
  ((algebraMap (A k) (L k)).comp (project k)).toAlgebra
instance : IsScalarTower (R k) (A k) (L k) := IsScalarTower.of_algebraMap_eq' rfl

noncomputable def powerSeriesInLaurent : Submodule (R k) (L k) :=
  ((Algebra.linearMap (A k) (L k)).restrictScalars (R k)).range

abbrev xLine : Ideal (R k) := Ideal.span {x k}

noncomputable abbrev cohomology (q : ℤ) : ModuleCat.{u} (R k) :=
  (IdealTorsion.localCohomology (IsLocalRing.maximalIdeal (R k)) q).obj (ModuleCat.of (R k) (R k))

def RingStructure : Prop :=
  ∀ (k : Type u) [Field k],
    IsLocalRing.maximalIdeal (R k) = Ideal.span {x k, y k} ∧
    x k ^ 2 = 0 ∧ x k * y k = 0 ∧
    RingHom.ker (project k) = xLine k ∧ project k (y k) = PowerSeries.X ∧
    ∃ e : (A k × k) ≃ₗ[k] R k, ∀ (a : A k) (c : k), e (a, c) = sectionR k a + c • x k

def Localization : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ e : _root_.Localization.Away (y k) ≃ₐ[R k] L k,
      (∀ r : R k, e (algebraMap (R k) (_root_.Localization.Away (y k)) r) =
        algebraMap (A k) (L k) (project k r)) ∧
      LinearMap.ker (Algebra.linearMap (R k) (_root_.Localization.Away (y k))) = xLine k

def CechReduction : Prop :=
  ∀ (k : Type u) [Field k],
    Nonempty (AugmentedCechComplex.coefficients (R k) [x k, y k] (ModuleCat.of (R k) (R k)) ≅
      AugmentedCechComplex.factor (R k) (y k))

def LocalCohomology : Prop :=
  ∀ (k : Type u) [Field k],
    Nonempty (cohomology k 0 ≅ ModuleCat.of (R k) (xLine k)) ∧
    Nonempty (cohomology k 1 ≅ ModuleCat.of (R k) (L k ⧸ powerSeriesInLaurent k))

end

end Specs.CommutativeAlgebraNotes.TwoDegreeExampleCechCalculation
