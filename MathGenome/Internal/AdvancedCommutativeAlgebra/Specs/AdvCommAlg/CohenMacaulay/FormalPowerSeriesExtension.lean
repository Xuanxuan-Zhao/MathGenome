import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.FlatLocalCohenMacaulay
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Ideal

/-! Independent CM-15 formal-series specifications, paper.tex:3762–3768,
3791–3813. The global module predicate includes zero modules. The actual
finite-variable series ring is used, also for zero variables. -/
universe u
open scoped TensorProduct
noncomputable section
namespace AdvCommAlg.CohenMacaulay.Specs

def formalPowerSeries_noetherianType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ),
    IsNoetherianRing (MvPowerSeries (Fin n) R)

def formalPowerSeries_flatType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ),
    Module.Flat R (MvPowerSeries (Fin n) R)

def powerSeries_X_mem_maximalType : Prop :=
  ∀ (R : Type u) [CommRing R] (q : Ideal (PowerSeries R)) [q.IsMaximal],
    (PowerSeries.X : PowerSeries R) ∈ q

def powerSeries_maximal_correspondenceType : Prop :=
  ∀ (R : Type u) [CommRing R] (q : Ideal (PowerSeries R)) [q.IsMaximal],
    (q.comap PowerSeries.C).IsMaximal ∧
      q = (q.comap PowerSeries.C).comap PowerSeries.constantCoeff

def powerSeries_maximal_liftType : Prop :=
  ∀ (R : Type u) [CommRing R] (m : Ideal R) [m.IsMaximal],
    (m.comap (PowerSeries.constantCoeff : PowerSeries R →+* R)).IsMaximal

/-- A quotient description with the canonical coefficient map, valid for
all ideals of a Noetherian base, not only for complete local bases. -/
def powerSeries_quotient_equivType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    ∃ e : (PowerSeries R ⧸ I.map PowerSeries.C) ≃+* PowerSeries (R ⧸ I),
      ∀ f : PowerSeries R,
        e (Ideal.Quotient.mk (I.map PowerSeries.C) f) =
          PowerSeries.map (Ideal.Quotient.mk I) f

/-- The fiber of the localized series ring over a maximal ideal of the
base. For maximal m, R/m is its residue field. -/
def powerSeries_local_fiber_equivType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (m : Ideal R) [m.IsMaximal],
  let q := m.comap (PowerSeries.constantCoeff : PowerSeries R →+* R)
  letI : q.IsMaximal := Ideal.comap_isMaximal_of_surjective _ PowerSeries.constantCoeff_surj
  let B := Localization.AtPrime q
  let J := (m.map PowerSeries.C).map (algebraMap (PowerSeries R) B)
  ∃ e : (B ⧸ J) ≃+* PowerSeries (R ⧸ m),
    ∀ f : PowerSeries R,
      e (Ideal.Quotient.mk J (algebraMap (PowerSeries R) B f)) =
        PowerSeries.map (Ideal.Quotient.mk m) f

/-- The same local fiber with the canonical residue-field type κ(m). -/
def powerSeries_residueField_fiber_equivType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (m : Ideal R) [m.IsMaximal],
  let q := m.comap (PowerSeries.constantCoeff : PowerSeries R →+* R)
  letI : q.IsMaximal := Ideal.comap_isMaximal_of_surjective _ PowerSeries.constantCoeff_surj
  let B := Localization.AtPrime q
  let J := (m.map PowerSeries.C).map (algebraMap (PowerSeries R) B)
  Nonempty ((B ⧸ J) ≃+* PowerSeries m.ResidueField)

/-- The nonzero closed fiber in one formal variable is a CM local ring. -/
def powerSeries_field_cohenMacaulayType : Prop :=
  ∀ (K : Type u) [Field K],
    LocalCohenMacaulayValue (PowerSeries K) (PowerSeries K)

/-- The full global assertion in CM-15. No nonzero or completeness
hypothesis is imposed. The tensor has its action on the series factor. -/
def formalPowerSeries_cohenMacaulayType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (n : ℕ),
  let S := MvPowerSeries (Fin n) R
  letI := AdvCommAlg.RegularSequence.Specs.rightTensorModule (R := R) (S := S) M S
  letI := rightTensorFinite R S M S
  IsCohenMacaulayValue S (M ⊗[R] S) ↔ IsCohenMacaulayValue R M

end AdvCommAlg.CohenMacaulay.Specs
