import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.SerreKoszulEulerFormula

/-! The Euler characteristic with one complete-intersection factor. -/

namespace CommutativeAlgebraNotes.Intersection.CompleteIntersectionEuler.Specs

open CategoryTheory
open AdvCommAlg.Koszul (listIdeal)
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)
open CommutativeAlgebraNotes.Intersection.IsolatedTorSupport.Specs (Tor)
open CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler.Specs
  (cutoffEuler intersectionEuler)
open _root_.Specs.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity (degreeMultiplicity)

universe u v

/-- Each Tor module contributing to the complete-intersection calculation has finite length. -/
def torFiniteLength : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (z : List R) (N : ModuleCat.{v} R) [Module.Finite R N],
    RingTheory.Sequence.IsRegular R z →
    listIdeal z ≤ IsLocalRing.maximalIdeal R →
    IsFiniteLength R (N ⧸ (listIdeal z • (⊤ : Submodule R N))) →
    ∀ i : ℕ, IsFiniteLength R (Tor (ModuleCat.of R (R ⧸ listIdeal z)) N i)

/-- The higher Tor groups vanish above the length of the regular list. -/
def torVanishesAbove : Prop :=
  ∀ {R : Type u} [CommRing R] (z : List R) (N : ModuleCat.{v} R),
    RingTheory.Sequence.IsRegular R z →
    ∀ i : ℕ, z.length < i → Subsingleton (Tor (ModuleCat.of R (R ⧸ listIdeal z)) N i)

/-- The alternating Tor length through the length of the list is its
specified-degree multiplicity on the coefficient module. -/
def eulerFormula : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (z : List R) (N : ModuleCat.{v} R) [Module.Finite R N] [Nontrivial N],
    RingTheory.Sequence.IsRegular R z →
    listIdeal z ≤ IsLocalRing.maximalIdeal R →
    IsFiniteLength R (N ⧸ (listIdeal z • (⊤ : Submodule R N))) →
    (cutoffEuler (ModuleCat.of R (R ⧸ listIdeal z)) N z.length : ℚ) =
      degreeMultiplicity (listIdeal z) N z.length

/-- The dimension bound and the two sign cases over a Noetherian local ring. -/
def eulerSigns : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (z : List R) (N : ModuleCat.{v} R) [Module.Finite R N] [Nontrivial N],
    RingTheory.Sequence.IsRegular R z →
    listIdeal z ≤ IsLocalRing.maximalIdeal R →
    IsFiniteLength R (N ⧸ (listIdeal z • (⊤ : Submodule R N))) →
    let χ := cutoffEuler (ModuleCat.of R (R ⧸ listIdeal z)) N z.length
    moduleDimensionValue R N ≤ (z.length : WithBot ℕ∞) ∧
      (χ = 0 ↔ moduleDimensionValue R N < (z.length : WithBot ℕ∞)) ∧
      (0 < χ ↔ moduleDimensionValue R N = (z.length : WithBot ℕ∞))

/-- A regular list of length `r` in a Noetherian local ring of dimension `d`
has a quotient of dimension `d - r`. -/
def quotientDimension : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (z : List R) (d : ℕ), RingTheory.Sequence.IsRegular R z →
    ringKrullDim R = (d : WithBot ℕ∞) →
    z.length ≤ d ∧ ringKrullDim (R ⧸ listIdeal z) = ((d - z.length : ℕ) : WithBot ℕ∞)

/-- The finite-colength hypothesis is equivalent to isolated intersection of the two supports. -/
def finiteLengthQuotientIffIsolated : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (z : List R) (N : ModuleCat.{v} R) [Module.Finite R N],
    IsFiniteLength R (N ⧸ (listIdeal z • (⊤ : Submodule R N))) ↔
      Module.support R (R ⧸ listIdeal z) ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R}

/-- In the regular local case, the cutoff sum is the shared intersection
Euler characteristic, whose signs are determined by the dimension sum. -/
def regularLocalIntersection : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (z : List R) (N : ModuleCat.{v} R) [Module.Finite R N] [Nontrivial N] (d : ℕ),
    RingTheory.Sequence.IsRegular R z →
    listIdeal z ≤ IsLocalRing.maximalIdeal R →
    IsFiniteLength R (N ⧸ (listIdeal z • (⊤ : Submodule R N))) →
    ringKrullDim R = (d : WithBot ℕ∞) →
    let M := ModuleCat.of R (R ⧸ listIdeal z)
    let χ := intersectionEuler M N
    let s := moduleDimensionValue R M + moduleDimensionValue R N
    χ = cutoffEuler M N z.length ∧
      s ≤ (d : WithBot ℕ∞) ∧ (χ = 0 ↔ s < (d : WithBot ℕ∞)) ∧
      (0 < χ ↔ s = (d : WithBot ℕ∞))

end CommutativeAlgebraNotes.Intersection.CompleteIntersectionEuler.Specs
