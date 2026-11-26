import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.AugmentedCechComplex
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

namespace Specs.CommutativeAlgebraNotes.InjectiveCechComparison

universe u

variable {R : Type u} [CommRing R]

open AugmentedCechComplex (Complex complex factor tensorFunctor)

noncomputable abbrev singleZero (R : Type u) [CommRing R] :=
  single (ModuleCat.{u} R) (.up ℤ) 0

/-- The degree-zero projection of one Čech factor to the tensor unit. -/
noncomputable def factorProjection (r : R) :
    factor R r ⟶ tensorUnit (ModuleCat.{u} R) (.up ℤ) :=
  mkHomToSingle (𝟙 (ModuleCat.of R R)) (fun i hi => by
    have hi' : i = -1 := by
      change i + 1 = (0 : ℤ) at hi
      omega
    subst i
    rfl)

/-- Project away a first Čech factor, using its degree-zero projection. -/
noncomputable def dropFactor (r : R) (K : Complex R) :
    factor R r ⊗ K ⟶ K :=
  (factorProjection r ⊗ₘ 𝟙 K) ≫ (λ_ K).hom

/-- Project the Čech tensor product onto its empty-subset term. -/
noncomputable def projection : (rs : List R) → (K : Complex R) →
    complex R rs ⊗ K ⟶ K
  | [], K => (λ_ K).hom
  | r :: rs, K =>
    (α_ (factor R r) (complex R rs) K).hom ≫
      dropFactor r (complex R rs ⊗ K) ≫ projection rs K

/-- The empty-subset projection identifies degree zero with the coefficient module. -/
def ProjectionDegreeZero : Prop :=
  ∀ {R : Type u} [CommRing R] (rs : List R) (M : ModuleCat.{u} R),
    IsIso ((projection rs ((singleZero R).obj M)).f 0)

/-- The natural lift of the torsion inclusion along the Čech projection is a
quasi-isomorphism on injective modules. -/
def Comparison : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (rs : List R),
    Ideal.span {r | r ∈ rs} = I →
      ∃ η : IdealTorsion.idealTorsionFunctor I ⋙ singleZero R ⟶
          singleZero R ⋙ tensorFunctor R rs,
        (∀ M, η.app M ≫ projection rs ((singleZero R).obj M) =
          (singleZero R).map ((IdealTorsion.idealTorsionInclusion I).app M)) ∧
        ∀ (Q : ModuleCat.{u} R), CategoryTheory.Injective Q → QuasiIso (η.app Q)

end Specs.CommutativeAlgebraNotes.InjectiveCechComparison
