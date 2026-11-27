import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Cochains
import Mathlib.CategoryTheory.Functor.OfSequence

/-! The graded-split exhaustive filtration in Result U02. -/

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Specs.DerivedFormalization.SemifreeFiltration

universe u

open Specs.DerivedFormalization.Cochains (compValue stalkValue shiftValue)

variable {R : Type u} [CommRing R]

/-- The coproduct of shifts of the degree-zero stalk of the free rank-one module. -/
noncomputable abbrev stalkSum {I : Type u} (s : I → ℤ) : compValue.{u} R :=
  ∐ fun a => (shiftValue R (s a)).obj ((stalkValue R).obj (ModuleCat.of R R))

/-- Each stage represents its image subcomplex in `F` by a degreewise injective
cochain map. Exhaustiveness is the degreewise union condition. Splittings are
required in each degree, with no compatibility with the differentials. -/
structure Filtration (F : compValue.{u} R) where
  stages : ℕ ⥤ compValue.{u} R
  inclusions : stages ⟶ (Functor.const ℕ).obj F
  injective (n : ℕ) (i : ℤ) : Function.Injective ((inclusions.app n).f i)
  exhaustive (i : ℤ) (x : F.X i) :
    ∃ (n : ℕ) (y : (stages.obj n).X i), (inclusions.app n).f i y = x
  split (n : ℕ) (i : ℤ) :
    ∃ r : (stages.obj (n + 1)).X i ⟶ (stages.obj n).X i,
      (stages.map (homOfLE (Nat.le_succ n))).f i ≫ r = 𝟙 _
  initial :
    ∃ (I : Type u) (s : I → ℤ),
      Nonempty (cokernel (0 : (0 : compValue.{u} R) ⟶ stages.obj 0) ≅ stalkSum (R := R) s)
  successive (n : ℕ) :
    ∃ (I : Type u) (s : I → ℤ),
      Nonempty (cokernel (stages.map (homOfLE (Nat.le_succ n))) ≅ stalkSum (R := R) s)

def filtrationType :=
  ∀ {R : Type u} [CommRing R], compValue.{u} R → Type (u + 1)

abbrev filtrationValue (F : compValue.{u} R) := Filtration F

def isSemifreeType :=
  ∀ {R : Type u} [CommRing R], compValue.{u} R → Prop

/-- A complex is semifree if it admits such a filtration. -/
def isSemifreeValue (F : compValue.{u} R) : Prop :=
  Nonempty (Filtration F)

/-- The ambient complex with its inclusion maps is a colimit of the stages. -/
def unionIsColimitType : Prop :=
  ∀ {R : Type u} [CommRing R] {F : compValue.{u} R} (P : Filtration F),
    Nonempty (IsColimit ({ pt := F, ι := P.inclusions } : Cocone P.stages))

/-- Transport of a chosen filtration along a cochain isomorphism preserves the
stage diagram and postcomposes the embeddings with the given isomorphism. -/
def existsTransportType : Prop :=
  ∀ {R : Type u} [CommRing R] {F G : compValue.{u} R} (P : Filtration F) (e : F ≅ G),
    ∃ (T : Filtration G) (h : T.stages = P.stages),
      T.inclusions = eqToHom h ≫ P.inclusions ≫ (Functor.const ℕ).map e.hom

def isSemifreeIsoType : Prop :=
  ∀ {R : Type u} [CommRing R] {F G : compValue.{u} R} (_ : F ≅ G),
    isSemifreeValue F ↔ isSemifreeValue G

end Specs.DerivedFormalization.SemifreeFiltration
