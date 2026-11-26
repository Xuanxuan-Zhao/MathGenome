import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse

noncomputable section

open CategoryTheory CategoryTheory.Limits
open IsLocalRing (maximalIdeal)

namespace Specs.CommutativeAlgebraNotes.TwoDegreeExampleDualizingCalculation

open RegularCoverDualizingModel (ShiftedRingResolution dualizingComplex)

universe u

abbrev Series (k : Type u) [Field k] := MvPowerSeries (Fin 2) k

abbrev x (k : Type u) [Field k] : Series k := MvPowerSeries.X 0
abbrev y (k : Type u) [Field k] : Series k := MvPowerSeries.X 1

def definingIdeal (k : Type u) [Field k] : Ideal (Series k) :=
  Ideal.span {x k ^ 2, x k * y k}

abbrev ExampleRing (k : Type u) [Field k] := Series k ⧸ definingIdeal k

abbrev quotientMap (k : Type u) [Field k] : Series k →+* ExampleRing k :=
  Ideal.Quotient.mk (definingIdeal k)

abbrev XQuotient (k : Type u) [Field k] := Series k ⧸ Ideal.span {x k}

/-- The action of the example ring on `S/(x)` factors through this quotient map. -/
def toXQuotient (k : Type u) [Field k] : ExampleRing k →+* XQuotient k :=
  Ideal.Quotient.factor (show definingIdeal k ≤ Ideal.span {x k} from by
    refine Ideal.span_le.mpr ?_
    intro z hz
    have hx : x k ∈ Ideal.span ({x k} : Set (Series k)) :=
      Ideal.subset_span (Set.mem_singleton _)
    rcases Set.mem_insert_iff.mp hz with h | h
    · rw [h, pow_two]
      exact Ideal.mul_mem_left _ _ hx
    · rw [Set.mem_singleton_iff] at h
      rw [h, mul_comm]
      exact Ideal.mul_mem_left _ _ hx)

/-- The action of the example ring on the coefficient field is by constant term. -/
def constantTerm (k : Type u) [Field k] : ExampleRing k →+* k :=
  Ideal.Quotient.lift (definingIdeal k) MvPowerSeries.constantCoeff (by
    have h : definingIdeal k ≤ RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin 2) (R := k)) :=
      Ideal.span_le.mpr (by
        intro z hz
        rcases Set.mem_insert_iff.mp hz with h | h
        · simp [h, x]
        · rw [Set.mem_singleton_iff] at h
          simp [h, x, y])
    exact fun z hz => h hz)

abbrev xQuotientModule (k : Type u) [Field k] : ModuleCat.{u} (ExampleRing k) :=
  (ModuleCat.restrictScalars (toXQuotient k)).obj (ModuleCat.of (XQuotient k) (XQuotient k))

abbrev coefficientModule (k : Type u) [Field k] : ModuleCat.{u} (ExampleRing k) :=
  (ModuleCat.restrictScalars (constantTerm k)).obj (ModuleCat.of k k)

/-- The stated quotient is a complete Noetherian local ring with the indicated
two-dimensional complete regular cover. -/
def CompleteRegularCover : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ (_ : IsRegularLocalRing (Series k)) (_ : IsLocalRing (ExampleRing k)),
      IsAdicComplete (maximalIdeal (Series k)) (Series k) ∧
      ringKrullDim (Series k) = (2 : WithBot ℕ∞) ∧
      IsNoetherianRing (ExampleRing k) ∧
      IsAdicComplete (maximalIdeal (ExampleRing k)) (ExampleRing k) ∧
      IsLocalHom (quotientMap k) ∧ Function.Surjective (quotientMap k) ∧
      ∃ e : IsLocalRing.ResidueField (ExampleRing k) ≃+* k,
        ∀ r : ExampleRing k, e (IsLocalRing.residue (ExampleRing k) r) = constantTerm k r

/-- Every bounded injective model of the shifted cover ring yields the asserted
cohomology with its quotient-ring module actions. -/
def DualizingCohomology : Prop :=
  ∀ (k : Type u) [Field k], ∀ J : ShiftedRingResolution (Series k) 2,
    let D := dualizingComplex (quotientMap k) J.complex
    Nonempty (D.homology (-1) ≅ xQuotientModule k) ∧
    Nonempty (D.homology 0 ≅ coefficientModule k) ∧
    ∀ q : ℤ, q ≠ -1 → q ≠ 0 → IsZero (D.homology q)

end Specs.CommutativeAlgebraNotes.TwoDegreeExampleDualizingCalculation
