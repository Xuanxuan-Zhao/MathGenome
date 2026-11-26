import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import Mathlib.Algebra.Module.Lattice

noncomputable section

open IsDedekindDomain
open scoped NumberField Polynomial RatFunc

namespace LinearAlgebraicGroups.Arithmetic

/-- Apply the scalar embedding to each coordinate of a rational vector. -/
def embedCoordinates {K L ι : Type*} [Field K] [Field L]
    (f : K →+* L) (x : ι → K) : ι → L :=
  fun i => f (x i)

section Dedekind

variable {R K ι : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The completion of the reference lattice is the local integer span of its diagonal image. -/
def completedLattice (v : HeightOneSpectrum R) (L : Submodule R (ι → K)) :
    Submodule (v.adicCompletionIntegers K) (ι → v.adicCompletion K) :=
  Submodule.span _ (embedCoordinates (algebraMap K (v.adicCompletion K)) '' (L : Set (ι → K)))

/-- Rational vectors satisfying the lattice condition at each prime of the integer ring. -/
def rationalLatticeIntersection
    (P : ∀ v : HeightOneSpectrum R, Submodule (v.adicCompletionIntegers K)
      (ι → v.adicCompletion K)) : Submodule R (ι → K) where
  carrier := {x | ∀ v, embedCoordinates (algebraMap K (v.adicCompletion K)) x ∈ P v}
  zero_mem' := by
    intro v
    rw [show embedCoordinates (algebraMap K (v.adicCompletion K)) (0 : ι → K) = 0 by
      ext i; simp [embedCoordinates]]
    exact (P v).zero_mem
  add_mem' {x y} hx hy := by
    intro v
    convert (P v).add_mem (hx v) (hy v) using 1
    apply funext; intro i
    simp [embedCoordinates]
  smul_mem' a x hx := by
    intro v
    convert (P v).smul_mem (algebraMap R (v.adicCompletionIntegers K) a) (hx v) using 1
    apply funext; intro i
    change algebraMap K (v.adicCompletion K) (a • x i) =
      (algebraMap R (v.adicCompletionIntegers K) a : v.adicCompletionIntegers K) •
        algebraMap K (v.adicCompletion K) (x i)
    rw [Algebra.smul_def, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply R K, ← IsScalarTower.algebraMap_apply R (v.adicCompletionIntegers K)]

variable {B : Type*} [CommRing B] [Algebra B R]

/-- A single base denominator gives both sandwiches. Multiplying the second
inclusion by the inverse denominator gives its usual fractional-lattice form. -/
def LatticeIntersectionConclusion (L : Submodule R (ι → K))
    (P : ∀ v : HeightOneSpectrum R, Submodule (v.adicCompletionIntegers K)
      (ι → v.adicCompletion K)) : Prop :=
  let I := rationalLatticeIntersection P
  ∃ m : B, m ≠ 0 ∧ Submodule.IsLattice K I ∧
    (∀ x ∈ L, algebraMap B R m • x ∈ I) ∧
    (∀ x ∈ I, algebraMap B R m • x ∈ L) ∧
    ∀ v : HeightOneSpectrum R,
      (∀ y ∈ completedLattice v L, algebraMap B R m • y ∈ P v) ∧
      (∀ y ∈ P v, algebraMap B R m • y ∈ completedLattice v L) ∧
      closure (embedCoordinates (algebraMap K (v.adicCompletion K)) '' (I : Set (ι → K))) =
        (P v : Set (ι → v.adicCompletion K)) ∧
      completedLattice v I = P v

end Dedekind

namespace LocalLatticeIntersectionSpec

def completedLatticeClosure : Prop :=
  ∀ {R K ι : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Finite ι]
    (L : Submodule R (ι → K)) [Submodule.IsLattice K L] (v : HeightOneSpectrum R),
    closure (embedCoordinates (algebraMap K (v.adicCompletion K)) '' (L : Set (ι → K))) =
      (completedLattice v L : Set (ι → v.adicCompletion K))

/-- The comparison with the intrinsic function-field completion carries
diagonal points and local integer spans to their adic counterparts. -/
def functionCompletionTransport : Prop :=
  ∀ {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    (t : SeparatingParameter F K) (v : HeightOneSpectrum t.integerRing),
    let w := GlobalPlacesSpec.placeOfPrimeValue t v
    ∃ h : (ι → w.Completion) ≃ₜ (ι → v.adicCompletion K),
      (∀ x : ι → K, h (embedCoordinates w.embedding x) =
        embedCoordinates (algebraMap K (v.adicCompletion K)) x) ∧
      (∀ (a : K) (x : ι → w.Completion),
        h (w.embedding a • x) = algebraMap K (v.adicCompletion K) a • h x) ∧
      ∀ S : Set (ι → w.Completion),
        h '' (Submodule.span w.integers S : Set (ι → w.Completion)) =
          (Submodule.span (v.adicCompletionIntegers K) (h '' S) : Set (ι → v.adicCompletion K))

def dedekindIntersection : Prop :=
  ∀ {B R K ι : Type*} [CommRing B] [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra B R] [FaithfulSMul B R] [Algebra.IsIntegral B R] [Algebra R K]
    [IsFractionRing R K] [Finite ι]
    (L : Submodule R (ι → K)) [Submodule.IsLattice K L]
    (P : ∀ v : HeightOneSpectrum R,
      Submodule (v.adicCompletionIntegers K) (ι → v.adicCompletion K))
    [∀ v, Submodule.IsLattice (v.adicCompletion K) (P v)],
    {v | P v ≠ completedLattice v L}.Finite →
      LatticeIntersectionConclusion (B := B) L P

def numberIntersection : Prop :=
  ∀ {K ι : Type*} [Field K] [NumberField K] [Finite ι]
    (L : Submodule (𝓞 K) (ι → K)) [Submodule.IsLattice K L]
    (P : ∀ v : NumberFinitePlace K,
      Submodule (v.adicCompletionIntegers K) (ι → v.adicCompletion K))
    [∀ v, Submodule.IsLattice (v.adicCompletion K) (P v)],
    {v | P v ≠ completedLattice v L}.Finite →
      LatticeIntersectionConclusion (B := ℤ) L P

def functionIntersection : Prop :=
  ∀ {F K ι : Type*} [Field F] [Finite F] [Field K] [Algebra F K] [Finite ι]
    (t : SeparatingParameter F K)
    (L : Submodule t.integerRing (ι → K)) [Submodule.IsLattice K L]
    (P : ∀ v : HeightOneSpectrum t.integerRing,
      Submodule (v.adicCompletionIntegers K) (ι → v.adicCompletion K))
    [∀ v, Submodule.IsLattice (v.adicCompletion K) (P v)],
    {v | P v ≠ completedLattice v L}.Finite →
      LatticeIntersectionConclusion (B := F[X]) L P

open Classical in
def functionPlaceIndex : Prop :=
  ∀ {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
    (t : SeparatingParameter F K),
    Function.Injective (GlobalPlacesSpec.placeOfPrimeValue t) ∧
    Set.range (GlobalPlacesSpec.placeOfPrimeValue t) =
      {v : FunctionPlace K | t.element ∈ v.1} ∧
    Set.range (GlobalPlacesSpec.placeOfPrimeValue t) =
      {v : FunctionPlace K | v.1.comap t.rationalMap.toRingHom ≠
        (RatFunc.inftyValuation F).valuationSubring}

end LocalLatticeIntersectionSpec

end LinearAlgebraicGroups.Arithmetic
