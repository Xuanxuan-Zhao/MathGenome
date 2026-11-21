import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.InteriorHomotopyEquivalence

/-! The two smoothing clauses of M06.06, paper.tex:1407–1420.
Both manifolds may have ordinary boundary. The cylinder test is the shared
ambient local-extension test, including its simultaneous time/spatial faces.
There are no compactness or endpoint-neighborhood smoothness hypotheses. -/
namespace Specs.SmoothManifolds.Ch06.SmoothingHomotopies
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.AtlasData
  _root_.SmoothManifolds.MapData _root_.SmoothManifolds.InteriorHomotopyData
universe u v

/-- Every continuous map is continuously homotopic to a smooth map. -/
def continuous_map_homotopic_smoothType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {P : Type v} {N : Type u}
    [TopologicalSpace P] [TopologicalSpace N]
    (S : SmoothManifold n a P) (T : SmoothManifold m b N)
    (F : P → N), Continuous F →
    ∃ G : P → N, IsSmoothMap S T G ∧
      ∃ H : HomotopyTime × P → N, Continuous H ∧
        (∀ x, H (timeZero, x) = F x) ∧
        (∀ x, H (timeOne, x) = G x)

/-- Continuous homotopies between smooth maps admit smooth replacements with
exactly the original endpoints, even when those endpoints meet the boundary. -/
def continuous_homotopy_smoothingType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {P : Type v} {N : Type u}
    [TopologicalSpace P] [TopologicalSpace N]
    (S : SmoothManifold n a P) (T : SmoothManifold m b N)
    (F₀ F₁ : P → N), IsSmoothMap S T F₀ → IsSmoothMap S T F₁ →
    (∃ H : HomotopyTime × P → N, Continuous H ∧
      (∀ x, H (timeZero, x) = F₀ x) ∧
      (∀ x, H (timeOne, x) = F₁ x)) →
    ∃ K : HomotopyTime × P → N,
      SmoothHomotopy S.smoothStructure.val T.smoothStructure.val K ∧
      (∀ x, K (timeZero, x) = F₀ x) ∧
      (∀ x, K (timeOne, x) = F₁ x)

end Specs.SmoothManifolds.Ch06.SmoothingHomotopies
