import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IsolatedTorSupport
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.RegularLocalRing.Defs

noncomputable section

open scoped BigOperators TensorProduct
open CommutativeAlgebraNotes.Intersection.IsolatedTorSupport.Specs (Tor)

namespace CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler.Specs

universe u v w

/-- The integer Tor Euler sum through degree `d`, inclusive. In the
finite-length applications, `toNat` recovers the natural number length. -/
def cutoffEuler {R : Type u} [CommRing R] (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (d : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (d + 1), (-1 : ℤ) ^ i * ((Module.length R (Tor M N i)).toNat : ℤ)

set_option linter.checkUnivs false in
def cutoffEulerType :=
  ∀ {R : Type u} [CommRing R], ModuleCat.{v} R → ModuleCat.{w} R → ℕ → ℤ

/-- The Krull dimension as a natural number for a regular local ring. -/
def regularLocalDimension (R : Type u) [CommRing R] [IsRegularLocalRing R] : ℕ :=
  (IsLocalRing.maximalIdeal R).spanFinrank

def regularLocalDimensionType :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R], ℕ

def ringKrullDimEqRegularLocalDimension : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
    ringKrullDim R = (regularLocalDimension R : WithBot ℕ∞)

def intersectionEuler {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) : ℤ :=
  cutoffEuler M N (regularLocalDimension R)

set_option linter.checkUnivs false in
def intersectionEulerType :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R],
    ModuleCat.{v} R → ModuleCat.{w} R → ℤ

def intersectionEulerEqCutoff : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (d : ℕ),
    ringKrullDim R = (d : WithBot ℕ∞) →
      intersectionEuler M N = cutoffEuler M N d

def torFiniteLength : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N],
    IsFiniteLength R (M ⊗[R] N) → ∀ i, IsFiniteLength R (Tor M N i)

def torVanishesAbove : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) [Module.Finite R M] (d : ℕ),
    ringKrullDim R = (d : WithBot ℕ∞) → ∀ i : ℕ, d < i → Subsingleton (Tor M N i)

def cutoffEulerSymm : Prop :=
  ∀ {R : Type u} [CommRing R] (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (d : ℕ),
    cutoffEuler M N d = cutoffEuler N M d

def cutoffEulerEqOfVanishesAbove : Prop :=
  ∀ {R : Type u} [CommRing R] (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (d d' : ℕ), d ≤ d' → (∀ i : ℕ, d < i → Subsingleton (Tor M N i)) →
      cutoffEuler M N d' = cutoffEuler M N d

def intersectionEulerSymm : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N],
    IsFiniteLength R (M ⊗[R] N) → intersectionEuler M N = intersectionEuler N M

end CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler.Specs
