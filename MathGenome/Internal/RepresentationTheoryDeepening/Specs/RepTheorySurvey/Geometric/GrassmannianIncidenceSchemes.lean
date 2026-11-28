import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.LatticeModels
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace RepTheorySurvey.Geometric.GrassmannianIncidenceSpecs

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups (Points SchemeOver)
open LatticeModelSpecs

section Grassmannian

variable {U W A C : Type} [AddCommGroup U] [Module ℂ U] [Module.Finite ℂ U]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup A] [Module ℂ A] [Module.Finite ℂ A]
  [AddCommGroup C] [Module ℂ C] [Module.Finite ℂ C]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem incidenceDimension_le (e : W ≃ₗ[ℂ] U × (A × C)) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ U) : d + Module.finrank ℂ A ≤ Module.finrank ℂ W := by
  rw [e.finrank_eq, Module.finrank_prod, Module.finrank_prod, ← Nat.add_assoc]
  exact (Nat.add_le_add_right hd _).trans (Nat.le_add_right _ _)

/-- On complex points the incidence morphism takes the inverse image of the
plane in the fixed upper subspace, including the entire lower summand. -/
def IncidencePointFormula (e : W ≃ₗ[ℂ] U × (A × C))
    (bu : Module.Basis ι ℂ U) (bw : Module.Basis κ ℂ W) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ U)
    (j : (grassmannianCharts bu hd).scheme ⟶
      (grassmannianCharts bw (incidenceDimension_le e hd)).scheme) : Prop :=
  ∀ (p : GrassmannianPoints bu hd) (w : W),
    w ∈ grassmannianSubspace bw (incidenceDimension_le e hd) (p ≫ j) ↔
      (e w).1 ∈ grassmannianSubspace bu hd p ∧ (e w).2.2 = 0

end Grassmannian

def GrassmannianIncidence : Prop :=
  ∀ {U W A C : Type} [AddCommGroup U] [Module ℂ U] [Module.Finite ℂ U]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup A] [Module ℂ A] [Module.Finite ℂ A]
    [AddCommGroup C] [Module ℂ C] [Module.Finite ℂ C]
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : W ≃ₗ[ℂ] U × (A × C))
    (bu : Module.Basis ι ℂ U) (bw : Module.Basis κ ℂ W) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ U),
  ∃ j : (grassmannianCharts bu hd).scheme ⟶
      (grassmannianCharts bw (incidenceDimension_le e hd)).scheme,
    IsClosedImmersion j.left ∧ IncidencePointFormula e bu bw hd j

/-- A closed immersion taking the given complex points into the target set
restricts to a closed immersion of their reduced closures. -/
def ReducedClosureIncidence : Prop :=
  ∀ {X Y : SchemeOver ℂ} (j : X ⟶ Y)
    (S : Set (Points X complexAlgebra)) (T : Set (Points Y complexAlgebra)),
    IsClosedImmersion j.left →
    (∀ q ∈ S, q ≫ j ∈ T) →
    ∃ i : reducedClosureScheme X S ⟶ reducedClosureScheme Y T,
      IsClosedImmersion i.left ∧
        i ≫ reducedClosureInclusion Y T = reducedClosureInclusion X S ≫ j

/-- The same incidence morphism restricts to the reduced stable schemes when
it carries stable complex points to stable complex points. -/
def StableGrassmannianIncidence : Prop :=
  ∀ {U W A C : Type} [AddCommGroup U] [Module ℂ U] [Module.Finite ℂ U]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup A] [Module ℂ A] [Module.Finite ℂ A]
    [AddCommGroup C] [Module ℂ C] [Module.Finite ℂ C]
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : W ≃ₗ[ℂ] U × (A × C))
    (bu : Module.Basis ι ℂ U) (bw : Module.Basis κ ℂ W) {d : ℕ}
    (hd : d ≤ Module.finrank ℂ U)
    (j : (grassmannianCharts bu hd).scheme ⟶
      (grassmannianCharts bw (incidenceDimension_le e hd)).scheme)
    (Tu : U →ₗ[ℂ] U) (Tw : W →ₗ[ℂ] W),
  let hw := incidenceDimension_le e hd
  let X := (grassmannianCharts bu hd).scheme
  let Y := (grassmannianCharts bw hw).scheme
  let S : Set (Points X complexAlgebra) := {p | StablePlane bu hd Tu p}
  let T : Set (Points Y complexAlgebra) := {p | StablePlane bw hw Tw p}
  IsClosedImmersion j.left →
    IncidencePointFormula e bu bw hd j →
    (∀ p ∈ S, p ≫ j ∈ T) →
    ∃ i : stableScheme bu hd Tu ⟶ stableScheme bw hw Tw,
      IsClosedImmersion i.left ∧
        i ≫ reducedClosureInclusion Y T = reducedClosureInclusion X S ≫ j ∧
        ∀ (q : Points (stableScheme bu hd Tu) complexAlgebra) (w : W),
          w ∈ grassmannianSubspace bw hw ((q ≫ i) ≫ reducedClosureInclusion Y T) ↔
            (e w).1 ∈ grassmannianSubspace bu hd (q ≫ reducedClosureInclusion X S) ∧
              (e w).2.2 = 0

end RepTheorySurvey.Geometric.GrassmannianIncidenceSpecs
