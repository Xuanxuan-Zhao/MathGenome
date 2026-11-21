import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.RieszSplitting
import Mathlib.Analysis.Meromorphic.Order

/-! The isolated-point clause of `fa2:p2:riesz-projection` (paper.tex:10131–10156).
All operators are bounded on arbitrary complex Banach spaces. There is no
compactness or Fredholm hypothesis. The upstream splitting uses the actual
Riesz–Dunford integral and the actual ranges with their inherited norms. -/
noncomputable section
namespace ExpandedFA.BanachAlgebra.RieszPoles.Spec
open Set
open scoped Topology
open Specs.ExpandedFA.BanachAlgebra.Conventions
open ContourCalculus.Spec
universe u

/-- A spectral point isolated in the full spectrum, with no finite multiplicity
condition. -/
def IsolatedSpectralPoint {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →L[ℂ] X) (lam : ℂ) : Prop :=
  lam ∈ spectrum ℂ T ∧ ∃ U : Set ℂ, IsOpen U ∧ lam ∈ U ∧
    U ∩ spectrum ℂ T = {lam}

/-- Exact positive pole order of the operator-valued resolvent. The native
meromorphic order uses the punctured germ, so the zero extension of the
resolvent on its spectrum has no effect. Negative order entails meromorphy;
Mathlib's order junk value for nonmeromorphic germs is zero. -/
def PoleOfOrder {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →L[ℂ] X) (lam : ℂ) (m : ℕ) : Prop :=
  0 < m ∧ meromorphicOrderAt (AlgebraResolventValue ℂ (X →L[ℂ] X) T) lam =
    ((-(m : ℤ) : ℤ) : WithTop ℤ)

/-- Exact nilpotency order, including the required nonzero last power.
The positivity condition rules out the zero-th power convention. -/
def NilpotentOfOrder {A : Type*} [MonoidWithZero A] (a : A) (m : ℕ) : Prop :=
  0 < m ∧ a ^ m = 0 ∧ a ^ (m - 1) ≠ 0

/-- Isolation makes the complementary spectral piece compact; every local
cutoff on disjoint neighborhoods gives the upstream spectral splitting. -/
def IsolatedSplitting : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : X →L[ℂ] X) (lam : ℂ), IsolatedSpectralPoint T lam →
    IsCompact (spectrum ℂ T \ {lam}) ∧
    ∃ U₁ U₂ : Set ℂ, IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧
      lam ∈ U₁ ∧ spectrum ℂ T \ {lam} ⊆ U₂ ∧
      ∀ f : ℂ → ℂ, EqOn f (fun _ => 1) U₁ → EqOn f (fun _ => 0) U₂ →
        RieszSplitting.Spec.SplittingData T
          (HolomorphicValueValue (X →L[ℂ] X) T (U₁ ∪ U₂) f)
          {lam} (spectrum ℂ T \ {lam})

/-- On the complementary Riesz subspace T-lam is invertible. The assertion is
for every bounded restriction agreeing with T, including a zero subspace. -/
def ComplementInvertible : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T P : X →L[ℂ] X) (lam : ℂ) (K : Set ℂ),
    RieszSplitting.Spec.SplittingData T P {lam} K → lam ∉ K →
    ∀ S : (1 - P).range →L[ℂ] (1 - P).range,
      (∀ x : (1 - P).range, (S x : X) = T x) →
      IsUnit (S - algebraMap ℂ ((1 - P).range →L[ℂ] (1 - P).range) lam)

/-- Pole order of the full resolvent equals nilpotency order of the shifted
restriction to the Riesz subspace. `SplittingData` supplies the closed direct
sum and the exact spectra; the preceding isolated-cutoff theorem supplies it
for every isolated spectral point. No pole or nilpotence certificate is assumed. -/
def PoleNilpotence : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T P : X →L[ℂ] X) (lam : ℂ) (K : Set ℂ),
    RieszSplitting.Spec.SplittingData T P {lam} K → lam ∉ K →
    ∀ S : P.range →L[ℂ] P.range,
      (∀ x : P.range, (S x : X) = T x) → ∀ m : ℕ,
      PoleOfOrder T lam m ↔
        NilpotentOfOrder (S - algebraMap ℂ (P.range →L[ℂ] P.range) lam) m

/-- The complete isolated-point conclusion for every admissible local cutoff.
In particular the projection is the actual contour-calculus value, rather
than an unspecified projection with an assumed pole property. -/
def IsolatedPoleSplitting : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : X →L[ℂ] X) (lam : ℂ), IsolatedSpectralPoint T lam →
    ∀ (U₁ U₂ : Set ℂ) (f : ℂ → ℂ),
      IsOpen U₁ → IsOpen U₂ → Disjoint U₁ U₂ → lam ∈ U₁ →
      spectrum ℂ T \ {lam} ⊆ U₂ →
      EqOn f (fun _ => 1) U₁ → EqOn f (fun _ => 0) U₂ →
      let P := HolomorphicValueValue (X →L[ℂ] X) T (U₁ ∪ U₂) f
      RieszSplitting.Spec.SplittingData T P {lam} (spectrum ℂ T \ {lam}) ∧
      ∃ (S₁ : P.range →L[ℂ] P.range) (S₂ : (1 - P).range →L[ℂ] (1 - P).range),
        (∀ x : P.range, (S₁ x : X) = T x) ∧
        (∀ x : (1 - P).range, (S₂ x : X) = T x) ∧
        IsUnit (S₂ - algebraMap ℂ ((1 - P).range →L[ℂ] (1 - P).range) lam) ∧
        ∀ m : ℕ, PoleOfOrder T lam m ↔
          NilpotentOfOrder (S₁ - algebraMap ℂ (P.range →L[ℂ] P.range) lam) m

end ExpandedFA.BanachAlgebra.RieszPoles.Spec
