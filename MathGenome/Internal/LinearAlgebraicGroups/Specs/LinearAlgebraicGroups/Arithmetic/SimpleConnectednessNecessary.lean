import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.KummerObstructions
import Mathlib.Topology.Algebra.Group.Quotient

noncomputable section

universe u v

namespace LinearAlgebraicGroups.Specs.SimpleConnectednessNecessary

open Arithmetic Arithmetic.AdelicGroups
open IntegralModels (MatrixRealization RationalPoints)
open GeometricRadicals (IsSemisimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- A nonempty restricted-product basic open avoiding the rational diagonal. -/
def HasObstruction {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (S : Finset D.Place) : Prop :=
  ∃ B ∈ basicBoxes D i S, B.Nonempty ∧
    ∀ g : RationalPoints G, ¬ ∃ x ∈ B, ∀ w : Outside D S, x w = localPoint D i w.1 g

/-- The simply connectedness necessity of F12, in the slightly more general
semisimple form. The geometric simply connectedness predicate concerns the
full scheme kernel, including in inseparable characteristic. -/
def Statement : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    (G : AffineAlgebraicGroup K), IsSemisimple G →
    ¬ GeometricallySimplyConnected G →
    ∀ (i : MatrixRealization G) (S : Finset D.Place), S.Nonempty →
      HasObstruction D i S

/-- Local separation at one finite place, for rational points integral outside
a finite exceptional set, gives separation in the actual restricted product. -/
def ObstructionFromLocalOpen : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (S : Finset D.Place)
    (T : Finset D.Place) (w : D.FinitePlace),
    S ⊆ T → Sum.inl w ∉ T →
    ∀ U : Set (LocalPoints D i (.inl w)), IsOpen U → U.Nonempty →
      U ⊆ integralPoints D i w →
      (∀ g : RationalPoints G,
        (∀ v : D.FinitePlace, Sum.inl v ∉ T → localPoint D i (.inl v) g ∈ integralPoints D i v) →
        localPoint D i (.inl w) g ∉ U) →
      HasObstruction D i S

open AlgebraicGeometry CategoryTheory
open CentralCover (MatrixEmbedding matrixCoordinates)
open IntegralCentralQuotient (spectrumOfAlgHom)
open StandardGroups (universalMatrix)
open Unipotent (Index)

/-- The matrix realization in the adelic topology is also a closed
immersion into the determinant localization used for the integral cover. -/
def MatrixEmbeddingWithEvaluation : Prop :=
  ∀ {K : Type u} [Field K] {G : AffineAlgebraicGroup K} (i : MatrixRealization G),
    ∃ j : MatrixEmbedding G i.size,
      ∀ (L : Type u) [CommRing L] [Algebra K L] (g : PointsIn i L),
        ∃ p : matrixCoordinates K i.size →ₐ[K] L,
          spectrumOfAlgHom p = g ≫ j.inclusion ∧
            p.mapMatrix (universalMatrix K (Index.{u} i.size)) = (asMatrix i L g).val

/-- Evaluate regular functions using an affine presentation of the group. -/
def evaluateAffinePoint {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    {G : AffineAlgebraicGroup K} {i : MatrixRealization G} {B : TestAlgebra K}
    (e : (testSpec K).obj (Opposite.op B) ≅ G.val.X) (g : PointsIn i L) : B →ₐ[K] L :=
  ((algSpec.fullyFaithful (R := CommRingCat.of K)).preimage (g ≫ e.inv)).unop.hom

/-- Regular-function evaluation agrees with continuity in the chosen matrix
topology, independent of the affine coordinate presentation. -/
def ContinuousAffineEvaluation : Prop :=
  ∀ {K L : Type u} [Field K] [CommRing L] [Algebra K L] [TopologicalSpace L]
    [IsTopologicalRing L] {G : AffineAlgebraicGroup K} (i : MatrixRealization G)
    {B : TestAlgebra K} (e : (testSpec K).obj (Opposite.op B) ≅ G.val.X),
    ∀ b : B, Continuous (fun g : PointsIn i L => evaluateAffinePoint e g b)

/-- The valuation ring on the global field defined by a finite completion. -/
def globalValuationRing {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    (w : D.FinitePlace) : ValuationSubring K :=
  (D.integers w).comap (D.embedding (.inl w))

/-- Restricting a finite place along a finite extension preserves integrality.
At a split place the embedding of the extension to the base completion
takes integers outside the exceptional set to local integers. -/
def FinitePlaceRestriction : Prop :=
  ∀ {K E : Type u} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
    (D : GlobalFieldData.{u, v} K) (D' : GlobalFieldData.{u, v} E),
    ∃ r : D'.FinitePlace → D.FinitePlace,
      (∀ w, globalValuationRing D (r w) = (globalValuationRing D' w).comap (algebraMap K E)) ∧
      ∀ (T : Set D'.FinitePlace) (w : D.FinitePlace), w ∉ r '' T →
        ∀ (e : E →+* D.FiniteCompletion w),
          e.comp (algebraMap K E) = D.embedding (.inl w) →
          ∀ x : CentralCover.integersOutside D' T, e x ∈ D.integers w

open scoped ValuativeRel

/-- The local quotient of integral units by (p)-th powers in equal
characteristic (p) is infinite and Hausdorff in its quotient group topology. -/
def EqualCharacteristicUnitClasses : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime] [CharP K p],
    Infinite (Arithmetic.Kummer.Classes 𝒪[K] p) ∧
      T2Space (Arithmetic.Kummer.Classes 𝒪[K] p)

/-- A nontrivial root of unity of order prime to the residue characteristic
gives a nontrivial unit class over a finite residue field. -/
def PrimeToResidueUnitClasses : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    [Finite (IsLocalRing.ResidueField R)] (n : ℕ)
    (_ : (n : IsLocalRing.ResidueField R) ≠ 0) (ζ : Rˣ),
    ζ ≠ 1 → ζ ^ n = 1 → Nontrivial (Arithmetic.Kummer.Classes R n)

/-- Passing from the valuation ring to the field preserves distinct classes
of units, since a field element whose positive power is an integral unit
already lies in the unit group of the valuation ring. -/
def IntegralUnitClassesInject : Prop :=
  ∀ {F : Type u} [Field F] (V : ValuationSubring F) (n : ℕ), 0 < n →
    Function.Injective (Arithmetic.Kummer.map V.subtype n)

/-- In a nonarchimedean local field the field-unit power subgroup is
closed and the corresponding Kummer quotient is Hausdorff. -/
def LocalFieldUnitClassesHausdorff : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n →
    T2Space (Arithmetic.Kummer.Classes F n)

section Pullback

open Arithmetic.Kummer
open IntegralCentralQuotient (IsRightTorsor)
open CentralCoverSpreading (KernelCoordinates)

/-- The Kummer coordinates of a finite flat split-kernel cover are continuous
on field-valued points with the topology of regular-function evaluation. -/
def ContinuousPullbackClass : Prop :=
  ∀ {R B A F : Type u} [CommRing R] [CommRing B] [CommRing A] [HopfAlgebra R B]
    [HopfAlgebra R A] [Field F] [Algebra R F]
    [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    {I : Type} (n : I → ℕ) (q : B →ₐc[R] A) (π : A →ₐc[R] KernelCoordinates R n),
    IsRightTorsor q π →
    letI : Algebra B A := q.toAlgHom.toAlgebra
    ∀ (i : I), 0 < n i → ∀ (X : Type u) [TopologicalSpace X] (f : X → B →ₐ[R] F),
      (∀ b : B, Continuous fun x => f x b) →
      ∀ c : X → Classes F (n i),
        (∀ x, PullbackHasClass n π (f x) i (c x) ∧
          ∀ d, PullbackHasClass n π (f x) i d → d = c x) →
        Continuous c

end Pullback

end LinearAlgebraicGroups.Specs.SimpleConnectednessNecessary
