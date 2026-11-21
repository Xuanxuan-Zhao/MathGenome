import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch15.PoleMovement

/-!
Runge's theorem with specified spherical poles (paper.tex:2730–2741).
The rational map is the canonical filled quotient, so cancelled roots
are not counted as poles. Its finite coordinate is used only after
asserting finiteness on K. No regularity or cardinality is imposed on A.
-/
noncomputable section
open Set TopologicalSpace

namespace Specs.D12Complex.Ch15.RungeAllowedPoles
open _root_.D12Complex _root_.D12Complex.PoleMovement
open Specs.D12Complex.Ch07.RationalInfinity.Objects

/-- The holomorphic restriction belongs to the uniform closure of permitted
rational restrictions, including for the empty compact set. -/
def holomorphic_mem_uniformClosure_type : Prop :=
  ∀ (K : Compacts ℂ) (U : Set ℂ) (f : ℂ → ℂ),
    IsOpen U → (K : Set ℂ) ⊆ U → HolomorphicOn U f →
    ∀ (A : Set RiemannSphere), A ⊆ sphericalComplement K →
      (∀ p ∈ sphericalComplement K,
        (connectedComponentIn (sphericalComplement K) p ∩ A).Nonempty) →
    ∀ F : C(K, ℂ), (∀ z : K, F z = f z) → F ∈ uniformClosure K A

/-- For every tolerance there is a rational function, finite on K, with
all spherical poles in A and ordinary uniform error strictly less than ε.
In particular infinity is a possible pole only when it belongs to A.
Constants, empty K, and disconnected neighborhoods are included. -/
def runge_allowed_poles_type : Prop :=
  ∀ (K U : Set ℂ) (f : ℂ → ℂ) (A : Set RiemannSphere),
    IsCompact K → IsOpen U → K ⊆ U → HolomorphicOn U f →
    A ⊆ (sphereFinite '' K)ᶜ →
    (∀ p ∈ (sphereFinite '' K)ᶜ,
      (connectedComponentIn (sphereFinite '' K)ᶜ p ∩ A).Nonempty) →
    ∀ ε : ℝ, 0 < ε → ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
      (∀ p : RiemannSphere, extension P Q p = sphereInfty → p ∈ A) ∧
      (∀ z ∈ K, extension P Q (sphereFinite z) =
        sphereFinite (finiteCoordinate (extension P Q (sphereFinite z)))) ∧
      (∀ z ∈ K, ‖f z - finiteCoordinate (extension P Q (sphereFinite z))‖ < ε) ∧
      sSup ((fun z => ‖f z - finiteCoordinate (extension P Q (sphereFinite z))‖) '' K) < ε

end Specs.D12Complex.Ch15.RungeAllowedPoles
