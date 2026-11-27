import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainTensorTransport

/-! The tensor assertions of U03 in the original cochain category and their
comparisons with the diagonal model. -/

namespace Specs.DerivedFormalization.CochainTensorInvariance

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Cochains (compValue)
open CochainTensor (isKFlat map)
open CochainModels (isKFlatValue tensorMapValue)
open CochainRingTransport (complexFunctorValue)
open CochainTensorTransport (AdequateModel)

universe u v

/-- Tensoring on the left by a K-flat complex preserves quasi-isomorphisms at
the original module level. -/
def tensorMapQuasiIsoType : Prop :=
  ∀ {R : Type u} [CommRing R] (P : compValue.{v} R), isKFlat P →
    ∀ {X Y : compValue.{v} R} (g : X ⟶ Y), QuasiIso g →
      QuasiIso (map (𝟙 P) g)

/-- The boundedness and termwise flatness assumptions of U03. -/
abbrev boundedAboveFlat {R : Type u} [CommRing R] (P : compValue.{v} R) : Prop :=
  (∀ q : ℤ, Module.Flat R (P.X q)) ∧
    (∃ N : ℤ, ∀ q : ℤ, N < q → IsZero (P.X q))

/-- A bounded-above flat complex passes the test against every acyclic complex
at the same level. -/
def boundedAboveFlatIsKFlatType : Prop :=
  ∀ (R : Type u) [CommRing R] (P : compValue.{v} R),
    (∀ q : ℤ, Module.Flat R (P.X q)) →
    (∃ N : ℤ, ∀ q : ℤ, N < q → IsZero (P.X q)) → isKFlat P

/-- The compatibility of the two U03 assertions with the adequate model and
the diagonal theorem over the ring representative. -/
structure AdequateTests {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    {e : R ≃+* A} (M : AdequateModel e) : Prop where
  boundedFlat_iff (P : compValue.{v} R) :
    boundedAboveFlat P ↔ boundedAboveFlat ((complexFunctorValue e).obj P)
  kFlat_iff_diagonal (P : compValue.{v} R) :
    isKFlat P ↔ isKFlatValue ((complexFunctorValue e).obj P)
  kFlat_iff_monoidal (P : compValue.{v} R) :
    letI := M.chainMonoidal
    isKFlat P ↔ ∀ E : compValue.{v} R, E.Acyclic → (E ⊗ P).Acyclic
  quasiIso_iff_diagonal {X Y : compValue.{v} R} (g : X ⟶ Y) :
    QuasiIso g ↔ QuasiIso ((complexFunctorValue e).map g)
  tensorQuasiIso_iff_diagonal (P : compValue.{v} R) {X Y : compValue.{v} R} (g : X ⟶ Y) :
    QuasiIso (map (𝟙 P) g) ↔
      QuasiIso (tensorMapValue (𝟙 ((complexFunctorValue e).obj P)) ((complexFunctorValue e).map g))
  tensorQuasiIso_iff_monoidal (P : compValue.{v} R) {X Y : compValue.{v} R} (g : X ⟶ Y) :
    letI := M.chainMonoidal
    QuasiIso (map (𝟙 P) g) ↔ QuasiIso ((𝟙 P) ⊗ₘ g)

/-- An adequate ring representation realizes the U03 tests in both models,
with no change of module level. -/
def adequateTestsType : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [CommRing A] (e : R ≃+* A),
    ∃ M : AdequateModel e, AdequateTests M

/-- At the native diagonal level the test and the actual tensor arrow agree
with the ones in the diagonal U03 theorems on the original complexes. -/
def diagonalTestsType : Prop :=
  ∀ {R : Type u} [CommRing R] (P : compValue.{u} R),
    (isKFlat P ↔ isKFlatValue P) ∧
    ∀ {X Y : compValue.{u} R} (g : X ⟶ Y),
      QuasiIso (map (𝟙 P) g) ↔ QuasiIso (tensorMapValue (𝟙 P) g)

end Specs.DerivedFormalization.CochainTensorInvariance
