import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Cochains
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.SemifreeFiltration
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! Semifree cochain complexes and transport of their filtrations. -/

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace DerivedFormalization

universe u

variable {R : Type u} [CommRing R]

/-- The coproduct of the indicated shifts of the stalk `R[0]`. -/
noncomputable abbrev shiftedStalkSum {I : Type u} (s : I → ℤ) : Comp.{u} R :=
  Specs.DerivedFormalization.SemifreeFiltration.stalkSum s

/-- A chosen graded-split exhaustive semifree filtration. -/
abbrev SemifreeFiltration (F : Comp.{u} R) :=
  Specs.DerivedFormalization.SemifreeFiltration.Filtration F

/-- A cochain complex admits an exhaustive graded-split filtration with
successive quotients direct sums of shifts of `R[0]`. -/
def IsSemifree (F : Comp.{u} R) : Prop :=
  Nonempty (SemifreeFiltration F)

namespace SemifreeFiltration

variable {F G : Comp.{u} R} (P : SemifreeFiltration F)

/-- The inclusion of stage `n` into stage `n + 1`. -/
abbrev step (n : ℕ) : P.stages.obj n ⟶ P.stages.obj (n + 1) :=
  P.stages.map (homOfLE (Nat.le_succ n))

/-- The union complex with its compatible inclusions from all stages. -/
def cocone : Cocone P.stages where
  pt := F
  ι := P.inclusions

/-- The first quotient `F₀ / 0` is canonically isomorphic to `F₀`. -/
noncomputable def initialQuotientIso :
    cokernel (0 : (0 : Comp.{u} R) ⟶ P.stages.obj 0) ≅ P.stages.obj 0 :=
  cokernelZeroIsoTarget

/-- The stage inclusions exhibit the complex as the colimit of the filtration. -/
noncomputable def isColimit : IsColimit P.cocone := by
  apply HomologicalComplex.isColimitOfEval
  intro i
  let forgetModule := forget (ModuleCat.{u} R)
  letI := reflectsSmallestFilteredColimits_of_reflectsFilteredColimits forgetModule
  apply isColimitOfReflects forgetModule
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨n, y, hy⟩ := P.exhaustive i x
    exact ⟨n, y, hy.symm⟩
  · intro n x y h
    have hxy : x = y := P.injective n i h
    exact ⟨n, 𝟙 n, congrArg _ hxy⟩

theorem union_isColimit : Nonempty (IsColimit P.cocone) :=
  ⟨P.isColimit⟩

/-- Transport a chosen filtration by composing every inclusion into the ambient
complex with the given cochain isomorphism. -/
def transport (e : F ≅ G) : SemifreeFiltration G := by
  refine {
    stages := P.stages
    inclusions := P.inclusions ≫ (Functor.const ℕ).map e.hom
    injective := ?_
    exhaustive := ?_
    split := P.split
    initial := P.initial
    successive := P.successive
  }
  · intro n i
    have he : Function.Injective (e.hom.f i) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    exact he.comp (P.injective n i)
  · intro i x
    have he : Function.Surjective (e.hom.f i) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    obtain ⟨z, hz⟩ := he x
    obtain ⟨n, y, hy⟩ := P.exhaustive i z
    exact ⟨n, y, (congrArg (e.hom.f i) hy).trans hz⟩

/-- Transport keeps the stages and changes the inclusions by the ambient isomorphism. -/
theorem exists_transport (e : F ≅ G) :
    ∃ (T : SemifreeFiltration G) (h : T.stages = P.stages),
      T.inclusions = eqToHom h ≫ P.inclusions ≫ (Functor.const ℕ).map e.hom :=
  ⟨P.transport e, rfl, by
    change _ = eqToHom (rfl : P.stages = P.stages) ≫ _
    simp [transport]⟩

end SemifreeFiltration

theorem isSemifree_iso {F G : Comp.{u} R} (e : F ≅ G) :
    IsSemifree F ↔ IsSemifree G :=
  ⟨fun ⟨P⟩ => ⟨P.transport e⟩, fun ⟨P⟩ => ⟨P.transport e.symm⟩⟩

end DerivedFormalization
