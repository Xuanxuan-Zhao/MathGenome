import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

open CategoryTheory
open scoped ChangeOfRings

namespace Specs.CommutativeAlgebraNotes.LocalCohomologyCompletion

open IdealTorsion (localCohomology)
open CompletionOfTorsionModules
  (Completion IsPowerTorsion completionModule exists_killing_power
    scalar_eq_of_eval mk_representative)

universe u v

local notation "𝔪[" R "]" => IsLocalRing.maximalIdeal R

section Action

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

local notation "S" => Completion R

/-- Regard a functor with power-torsion values as a functor of completed modules.
The action is the canonical one on the original module and the maps keep their
underlying functions. -/
noncomputable def completedAction (F : ModuleCat.{v} R ⥤ ModuleCat.{v} R)
    (h : ∀ M, IsPowerTorsion R (F.obj M)) : ModuleCat.{v} R ⥤ ModuleCat.{v} S where
  obj M :=
    letI := completionModule (h M)
    ModuleCat.of S (F.obj M)
  map {M N} f := by
    letI := completionModule (h M)
    letI := completionModule (h N)
    exact ModuleCat.ofHom {
      toFun := F.map f
      map_add' := (F.map f).hom.map_add
      map_smul' := by
        intro s x
        obtain ⟨n, hx⟩ := exists_killing_power (h M) x
        have hy : ∀ r ∈ 𝔪[R] ^ n, r • F.map f x = 0 := by
          intro r hr
          rw [← (F.map f).hom.map_smul, hx r hr, LinearMap.map_zero]
        change F.map f (CompletionOfTorsionModules.scalar (h M) s x) =
          CompletionOfTorsionModules.scalar (h N) s (F.map f x)
        rw [scalar_eq_of_eval (h M) hx (mk_representative s n),
          scalar_eq_of_eval (h N) hy (mk_representative s n)]
        exact (F.map f).hom.map_smul _ _ }
  map_id M := by
    ext x
    change F.map (𝟙 M) x = x
    simp
  map_comp f g := by
    ext x
    change F.map (f ≫ g) x = F.map g (F.map f x)
    simp

end Action

/-- The canonical module completion with morphisms induced by adic completion. -/
noncomputable def adicCompletionFunctor (R : Type u) [CommRing R] [IsLocalRing R] :
    ModuleCat.{u} R ⥤ ModuleCat.{u} (Completion R) where
  obj M := ModuleCat.of _ (AdicCompletion 𝔪[R] M)
  map f := ModuleCat.ofHom (AdicCompletion.map 𝔪[R] f.hom)
  map_id M := by
    ext : 1
    exact AdicCompletion.map_id 𝔪[R] M
  map_comp f g := by
    ext : 1
    exact (AdicCompletion.map_comp 𝔪[R] f.hom g.hom).symm

set_option linter.checkUnivs false in
def CompletedActionType :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (F : ModuleCat.{v} R ⥤ ModuleCat.{v} R),
    (∀ M, IsPowerTorsion R (F.obj M)) → ModuleCat.{v} R ⥤ ModuleCat.{v} (Completion R)

def AdicCompletionFunctorType :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R], ModuleCat.{u} R ⥤ ModuleCat.{u} (Completion R)

/-- The object property defining the full subcategory of finite modules. -/
abbrev finiteModules (R : Type u) [CommRing R] : ObjectProperty (ModuleCat.{u} R) :=
  fun M => Module.Finite R M

/-- The natural completed-linear comparison in any integer degree and
for arbitrary coefficient modules. -/
def CompletionComparison : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (q : ℤ),
    ∃ h : ∀ M, IsPowerTorsion R ((localCohomology 𝔪[R] q).obj M),
      Nonempty
        (completedAction (localCohomology 𝔪[R] q) h ≅
          ModuleCat.extendScalars.{u, u, u} (algebraMap R (Completion R)) ⋙
            localCohomology (IsLocalRing.maximalIdeal (Completion R)) q)

/-- On finite modules the canonical map from the extended module to its
adic completion is a natural isomorphism. -/
def FiniteTensorComparison : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
    ∃ e : (finiteModules R).ι ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap R (Completion R)) ≅
        (finiteModules R).ι ⋙ adicCompletionFunctor R,
      ∀ (M : (finiteModules R).FullSubcategory) (s : Completion R) (x : M.obj),
        e.hom.app M (s ⊗ₜ[R, algebraMap R (Completion R)] x) =
          s • AdicCompletion.of 𝔪[R] M.obj x

/-- The finite-module comparison with actual adic module completion. -/
def FiniteCompletionComparison : Prop :=
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (q : ℤ),
    ∃ h : ∀ M, IsPowerTorsion R ((localCohomology 𝔪[R] q).obj M),
      Nonempty
        ((finiteModules R).ι ⋙ completedAction (localCohomology 𝔪[R] q) h ≅
          (finiteModules R).ι ⋙ adicCompletionFunctor R ⋙
            localCohomology (IsLocalRing.maximalIdeal (Completion R)) q)

end Specs.CommutativeAlgebraNotes.LocalCohomologyCompletion
