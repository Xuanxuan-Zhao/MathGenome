import MathGenome.Internal.RealAnalysis.D11.Ch23.VectorLatticeStone
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.ElementaryIntegral

/-!
The positive order-continuous elementary integral of paper.tex:6190–6192.
The domain consists of actual functions in the canonical subspace `V`.
Lattice closure and Stone truncation are separate conditions on that subspace.
-/

universe u

open Filter Topology

namespace D11.Ch23

/-- A real-linear functional is elementary when it is positive and sends
every sequence decreasing pointwise to zero to a scalar sequence tending to zero. -/
abbrev IsElementaryIntegral {X : Type u} (V : Submodule ℝ (X → ℝ))
    (L : V →ₗ[ℝ] ℝ) : Prop :=
  Specs.IsElementaryIntegral V L

theorem isElementaryIntegral_iff {X : Type u} (V : Submodule ℝ (X → ℝ))
    (L : V →ₗ[ℝ] ℝ) :
    IsElementaryIntegral V L ↔
      (∀ f : V, (∀ x : X, 0 ≤ (f : X → ℝ) x) → 0 ≤ L f) ∧
      (∀ f : ℕ → V,
        (∀ x : X, Antitone (fun n => (f n : X → ℝ) x)) →
        (∀ x : X, Tendsto (fun n => (f n : X → ℝ) x) atTop (𝓝 0)) →
        Tendsto (fun n => L (f n)) atTop (𝓝 0)) :=
  Iff.rfl

namespace IsElementaryIntegral

variable {X : Type u} {V : Submodule ℝ (X → ℝ)} {L : V →ₗ[ℝ] ℝ}

theorem nonneg (hL : IsElementaryIntegral V L) (f : V)
    (hf : ∀ x : X, 0 ≤ (f : X → ℝ) x) : 0 ≤ L f :=
  hL.1 f hf

theorem tendsto_zero (hL : IsElementaryIntegral V L) (f : ℕ → V)
    (hanti : ∀ x : X, Antitone (fun n => (f n : X → ℝ) x))
    (hlim : ∀ x : X, Tendsto (fun n => (f n : X → ℝ) x) atTop (𝓝 0)) :
    Tendsto (fun n => L (f n)) atTop (𝓝 0) :=
  hL.2 f hanti hlim

end IsElementaryIntegral

theorem empty_domain_integral_value {X : Type u} [IsEmpty X]
    (V : Submodule ℝ (X → ℝ)) (L : V →ₗ[ℝ] ℝ) (f : V) : L f = 0 := by
  have hf : f = 0 := Subtype.ext (empty_domain_function (f : X → ℝ))
  rw [hf, map_zero]

theorem empty_domain_elementary_integral {X : Type u} [IsEmpty X]
    (V : Submodule ℝ (X → ℝ)) (L : V →ₗ[ℝ] ℝ) : IsElementaryIntegral V L := by
  constructor
  · intro f _
    rw [empty_domain_integral_value V L f]
  · intro f _ _
    have hzero : (fun n => L (f n)) = fun _ => (0 : ℝ) := by
      funext n
      exact empty_domain_integral_value V L (f n)
    rw [hzero]
    exact tendsto_const_nhds

end D11.Ch23
