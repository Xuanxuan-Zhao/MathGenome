import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.SmoothMaps

/-! Smooth descent uses actual sections on open subspaces, with the restricted
atlas. No rank or boundary condition is substituted for section existence. -/
namespace SmoothManifolds.SmoothDescentData
open ModelData AtlasData MapData Set
universe u v

/-- Each target point has a smooth section on an open neighborhood. -/
def HasSmoothLocalSections {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (q : M → N) : Prop :=
  ∀ y : N, ∃ U : Set N, ∃ hU : IsOpen U, y ∈ U ∧
    ∃ s : U → M,
      ManifoldSmooth (openSubsetAtlas T.smoothStructure.val U hU)
        S.smoothStructure.val s ∧ ∀ z : U, q (s z) = z.val

end SmoothManifolds.SmoothDescentData

namespace Specs.SmoothManifolds.Ch03.SmoothDescent
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.SmoothDescentData Set
universe u v w

def HasSmoothLocalSectionsType :=
  {m n : ℕ} → {a b : ModelKind} → {M : Type u} → {N : Type v} →
  [TopologicalSpace M] → [TopologicalSpace N] →
  SmoothManifold m a M → SmoothManifold n b N → (M → N) → Prop

def HasSmoothLocalSectionsValue : HasSmoothLocalSectionsType := @HasSmoothLocalSections

/-- The explicit open-set criterion for a quotient map. -/
def quotientType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N],
  ∀ (S : SmoothManifold m a M) (T : SmoothManifold n b N) (q : M → N),
    Function.Surjective q → IsSmoothMap S T q → HasSmoothLocalSections S T q →
    ∀ B : Set N, IsOpen B ↔ IsOpen (q ⁻¹' B)

/-- Existence and uniqueness quantify over actual maps into any allowed target. -/
def descentType : Prop :=
  ∀ {m n p : ℕ} {a b c : ModelKind} {M : Type u} {N : Type v} {P : Type w}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P],
  ∀ (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (R : SmoothManifold p c P) (q : M → N),
    Function.Surjective q → IsSmoothMap S T q → HasSmoothLocalSections S T q →
    ∀ h : M → P, IsSmoothMap S R h →
      (∀ x x', q x = q x' → h x = h x') →
      ∃! hbar : N → P, IsSmoothMap T R hbar ∧ hbar ∘ q = h

/-- Both induced directions and uniqueness of the diffeomorphism are explicit. -/
def sameFibers_diffeomorphType : Prop :=
  ∀ {m n p : ℕ} {a b c : ModelKind} {M : Type u} {N : Type v} {P : Type w}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P],
  ∀ (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (R : SmoothManifold p c P) (q₁ : M → N) (q₂ : M → P),
    Function.Surjective q₁ → Function.Surjective q₂ →
    IsSmoothMap S T q₁ → IsSmoothMap S R q₂ →
    HasSmoothLocalSections S T q₁ → HasSmoothLocalSections S R q₂ →
    (∀ x x', q₁ x = q₁ x' ↔ q₂ x = q₂ x') →
    ∃ e : Diffeomorph T.smoothStructure.val R.smoothStructure.val,
      e.toEquiv ∘ q₁ = q₂ ∧ e.toEquiv.symm ∘ q₂ = q₁ ∧
      ∀ d : Diffeomorph T.smoothStructure.val R.smoothStructure.val,
        d.toEquiv ∘ q₁ = q₂ → d = e

end Specs.SmoothManifolds.Ch03.SmoothDescent
