import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Topology.Connected.Basic

open CategoryTheory CategoryTheory.Limits Topology
open scoped ZeroObject

universe u v

namespace RepTheorySurvey.Geometric.FiniteFaceDevissage

open Analytic

namespace Expected

/-- A property closed under isomorphisms and two-out-of-three for short exact
sequences holds on all sheaves with finite constant restrictions if it holds
on zero and on the direct images of finite constant sheaves from the pieces. -/
def FiniteFaceGeneration : Prop :=
  ∀ (I : Type v) [Finite I] [PartialOrder I] (X : TopCat.{u})
    (Z : I → TopCat.{u}) [∀ i, ConnectedSpace (Z i)] (e : ∀ i, Z i ⟶ X),
    (∀ i, IsInducing (e i)) →
    (∀ x : X, ∃ (i : I) (z : Z i), e i z = x) →
    (∀ (i j : I) (V : Coeff.{u}), Module.Finite ℚ V →
      let R := (inverseImage (e j)).obj ((directImage (e i)).obj (constant (Z i) V))
      (¬ j ≤ i → IsZero R) ∧
        (j ≤ i → ∃ W : Coeff.{u}, Module.Finite ℚ W ∧ Nonempty (R ≅ constant (Z j) W))) →
    ∀ P : Sheaves X → Prop,
      P 0 →
      (∀ ⦃F G : Sheaves X⦄, (F ≅ G) → P F → P G) →
      (∀ S : ShortComplex (Sheaves X), S.ShortExact →
        (P S.X₁ → P S.X₂ → P S.X₃) ∧
        (P S.X₁ → P S.X₃ → P S.X₂) ∧
        (P S.X₂ → P S.X₃ → P S.X₁)) →
      (∀ (i : I) (V : Coeff.{u}), Module.Finite ℚ V →
        P ((directImage (e i)).obj (constant (Z i) V))) →
      ∀ F : Sheaves X,
        (∀ i, ∃ V : Coeff.{u}, Module.Finite ℚ V ∧
          Nonempty ((inverseImage (e i)).obj F ≅ constant (Z i) V)) →
        P F

end Expected
end RepTheorySurvey.Geometric.FiniteFaceDevissage
