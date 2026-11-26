import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompleteLocalDuality
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.LocalRing.RingHom.Basic

noncomputable section

open CategoryTheory IsLocalRing AdvCommAlg.Depth
open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs (residueFieldEnvelopeValue)

namespace Specs.CommutativeAlgebraNotes.ArtinianDualizingModuleExample

universe u w

variable (k : Type u) [Field k]

abbrev Series := MvPowerSeries (Fin 2) k

abbrev variableIdeal : Ideal (Series k) :=
  Ideal.span (Set.range MvPowerSeries.X)

abbrev QuotientRing := Series k ⧸ variableIdeal k ^ 2

abbrev quotientMap : Series k →+* QuotientRing k := Ideal.Quotient.mk _

abbrev coordinate (i : Fin 2) : QuotientRing k := quotientMap k (MvPowerSeries.X i)

instance : Nontrivial (QuotientRing k) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  have h : variableIdeal k ≤ RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin 2) (R := k)) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact MvPowerSeries.constantCoeff_X i
  exact ne_top_of_le_ne_top (RingHom.ker_ne_top _) ((Ideal.pow_le_self (by decide)).trans h)

instance : IsLocalRing (QuotientRing k) :=
  IsLocalRing.of_surjective' (quotientMap k) Ideal.Quotient.mk_surjective

/-- The scalar action on the k-dual is the argument action of coinduction. -/
abbrev Dual := (ModuleCat.coextendScalars (algebraMap k (QuotientRing k))).obj (ModuleCat.of k k)

abbrev dualApply (φ : Dual k) (r : QuotientRing k) : k :=
  ModuleCat.CoextendScalars.equiv (algebraMap k (QuotientRing k)) (ModuleCat.of k k) φ r

/-- The quotient acts on functionals by precomposition with multiplication. -/
def DualAction : Prop :=
  ∀ (k : Type u) [Field k] (a r : QuotientRing k) (φ : Dual k),
    dualApply k (a • φ) r = dualApply k φ (a * r)

def Coordinates : Prop :=
  ∀ (k : Type u) [Field k],
    maximalIdeal (QuotientRing k) = Ideal.span (Set.range (coordinate k)) ∧
    maximalIdeal (QuotientRing k) ^ 2 = ⊥ ∧
    ∃ b : Module.Basis (Option (Fin 2)) k (QuotientRing k),
      b none = 1 ∧ ∀ i, b (some i) = coordinate k i

def RingStructure : Prop :=
  ∀ (k : Type u) [Field k], IsArtinianRing (QuotientRing k) ∧ IsNoetherianRing (QuotientRing k) ∧
    IsAdicComplete (maximalIdeal (QuotientRing k)) (QuotientRing k)

def Socles : Prop :=
  ∀ (k : Type u) [Field k],
    (∃ e : ResidueField (QuotientRing k) ≃ₐ[k] k,
      ∀ f : Series k, e (residue (QuotientRing k) (quotientMap k f)) = MvPowerSeries.constantCoeff f) ∧
    Socle (QuotientRing k) (QuotientRing k) = (maximalIdeal (QuotientRing k) : Submodule (QuotientRing k) (QuotientRing k)) ∧
    (∀ φ : Dual k, φ ∈ Socle (QuotientRing k) (Dual k) ↔
      ∀ a ∈ maximalIdeal (QuotientRing k), dualApply k φ a = 0) ∧
    Module.finrank (ResidueField (QuotientRing k)) (Socle (QuotientRing k) (QuotientRing k)) = 2 ∧
    Module.finrank (ResidueField (QuotientRing k)) (Socle (QuotientRing k) (Dual k)) = 1

def DualEnvelope : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ ι : ResidueField (QuotientRing k) →ₗ[QuotientRing k] Dual k,
      AdvCommAlg.Gorenstein.IsInjectiveEnvelope ι ∧
      LinearMap.range ι = Socle (QuotientRing k) (Dual k)

def CechConcentration : Prop :=
  ∀ (k : Type u) [Field k],
    Nonempty (AugmentedCechComplex.complex (QuotientRing k) [coordinate k 0, coordinate k 1] ≅
      RegularCoverDualizingModel.stalk (QuotientRing k) 0 (ModuleCat.of (QuotientRing k) (QuotientRing k)))

def DualizingObject : Prop :=
  ∀ (k : Type u) [Field k] [HasDerivedCategory.{w} (ModuleCat.{u} (QuotientRing k))],
    Nonempty (RegularCoverDualizingModel.ShiftedRingResolution (Series k) 2) ∧
    ∀ (J : RegularCoverDualizingModel.ShiftedRingResolution (Series k) 2),
      Nonempty (RegularCoverDualizingModel.dualizingObject (quotientMap k) J ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} (QuotientRing k)) 0).obj (Dual k))

def NotGorenstein : Prop :=
  ∀ (k : Type u) [Field k], ¬ AdvCommAlg.Gorenstein.Specs.LocalGorensteinValue (QuotientRing k)

end Specs.CommutativeAlgebraNotes.ArtinianDualizingModuleExample
