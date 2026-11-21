import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.RationalInfinity
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Connected.LocallyConnected

/-!
Independent statements for the componentwise resolvent argument in
paper.tex:2730–2741 and its use in 2750–2755.  In particular, the allowed
set need not meet all complementary components.  Pole restrictions are
tested on the canonical *filled spherical rational function*, including
infinity, rather than on an arbitrary denominator of a presentation.
-/

noncomputable section
open Set TopologicalSpace
open scoped Topology

namespace D12Complex.PoleMovement

/-- The spherical complement of a compact subset of the finite plane. -/
def sphericalComplement (K : Compacts ℂ) : Set RiemannSphere :=
  (sphereFinite '' (K : Set ℂ))ᶜ

/-- Allowed rational functions, restricted to the compact set.  Values at
cancelled denominator zeros are the canonical filled values.  Constants
are allowed, while a pole at infinity is allowed exactly when it is in A. -/
def rationalRestrictions (K : Compacts ℂ) (A : Set RiemannSphere) : Set C(K, ℂ) :=
  {f | ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
    (∀ p : RiemannSphere,
      Specs.D12Complex.Ch07.RationalInfinity.Objects.extension P Q p = sphereInfty → p ∈ A) ∧
    ∀ z : K, Specs.D12Complex.Ch07.RationalInfinity.Objects.extension P Q
      (sphereFinite z) = sphereFinite (f z)}

/-- Uniform closure on K. The compact-open topology on C(K,ℂ) is the
uniform topology, also for the empty compact set. -/
def uniformClosure (K : Compacts ℂ) (A : Set RiemannSphere) : Set C(K, ℂ) :=
  closure (rationalRestrictions K A)

/-- The finite resolvent, with its actual continuous restriction to K. -/
def resolvent (K : Compacts ℂ) (a : ℂ) (ha : a ∉ (K : Set ℂ)) : C(K, ℂ) :=
  ⟨fun z => ((z : ℂ) - a)⁻¹,
    (continuous_subtype_val.sub continuous_const).inv₀
      (fun z h => by
        apply ha
        have hz : (z : ℂ) = a := sub_eq_zero.mp h
        have hzK : (z : ℂ) ∈ (K : Set ℂ) := z.2
        exact hz ▸ hzK)⟩

/-- The coordinate function on K. -/
def coordinate (K : Compacts ℂ) : C(K, ℂ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

end D12Complex.PoleMovement

namespace Specs.D12Complex.Ch15.PoleMovement
open _root_.D12Complex _root_.D12Complex.PoleMovement

def sphericalComplement_type := Compacts ℂ → Set RiemannSphere
def sphericalComplement_value : sphericalComplement_type :=
  fun K => (sphereFinite '' (K : Set ℂ))ᶜ

def rationalRestrictions_type := (K : Compacts ℂ) → Set RiemannSphere → Set C(K, ℂ)
def rationalRestrictions_value : rationalRestrictions_type := fun K A =>
  {f | ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
    (∀ p : RiemannSphere,
      Specs.D12Complex.Ch07.RationalInfinity.Objects.extension P Q p = sphereInfty → p ∈ A) ∧
    ∀ z : K, Specs.D12Complex.Ch07.RationalInfinity.Objects.extension P Q
      (sphereFinite z) = sphereFinite (f z)}

def uniformClosure_type := (K : Compacts ℂ) → Set RiemannSphere → Set C(K, ℂ)
def uniformClosure_value : uniformClosure_type := fun K A => closure (rationalRestrictions K A)

def resolvent_type := (K : Compacts ℂ) → (a : ℂ) → a ∉ (K : Set ℂ) → C(K, ℂ)
def resolvent_value : resolvent_type := fun K a ha => resolvent K a ha

def coordinate_type := (K : Compacts ℂ) → C(K, ℂ)
def coordinate_value : coordinate_type := fun K => ⟨Subtype.val, continuous_subtype_val⟩

def uniformClosure_isClosed_type : Prop :=
  ∀ (K : Compacts ℂ) (A : Set RiemannSphere), IsClosed (uniformClosure K A)

def uniformClosure_iff_approximation_type : Prop :=
  ∀ (K : Compacts ℂ) (A : Set RiemannSphere) (f : C(K, ℂ)),
    f ∈ uniformClosure K A ↔
      ∀ ε : ℝ, 0 < ε → ∃ g ∈ rationalRestrictions K A,
        ∀ z : K, ‖f z - g z‖ < ε

/-- Every permitted filled rational function really has a continuous finite
restriction; the use of C(K,ℂ) does not discard any permitted rational. -/
def permitted_rational_restriction_type : Prop :=
  ∀ (K : Compacts ℂ) (A : Set RiemannSphere), A ⊆ sphericalComplement K →
    ∀ P Q : Polynomial ℂ, Q ≠ 0 →
      (∀ p : RiemannSphere,
        Specs.D12Complex.Ch07.RationalInfinity.Objects.extension P Q p = sphereInfty → p ∈ A) →
      ∃ f ∈ rationalRestrictions K A, ∀ z : K,
        Specs.D12Complex.Ch07.RationalInfinity.Objects.extension P Q (sphereFinite z) =
          sphereFinite (f z)

def uniformClosure_algebra_type : Prop :=
  ∀ (K : Compacts ℂ) (A : Set RiemannSphere), A ⊆ sphericalComplement K →
    ∃ S : Subalgebra ℂ C(K, ℂ), (S : Set C(K, ℂ)) = uniformClosure K A

def constants_mem_type : Prop :=
  ∀ (K : Compacts ℂ) (A : Set RiemannSphere) (c : ℂ),
    ContinuousMap.const K c ∈ uniformClosure K A

/-- A norm formulation of the finite-pole geometric series; its HasSum
conclusion is convergence in the uniform norm on K. -/
def resolvent_geometric_series_type : Prop :=
  ∀ (K : Compacts ℂ) (a b : ℂ) (ha : a ∉ (K : Set ℂ))
    (hb : b ∉ (K : Set ℂ)),
    ‖(b - a) • resolvent K a ha‖ < 1 →
    HasSum (fun n : ℕ => (b - a) ^ n • resolvent K a ha ^ (n + 1))
      (resolvent K b hb)

def closedAlgebra_resolvent_near_type : Prop :=
  ∀ (K : Compacts ℂ) (S : Subalgebra ℂ C(K, ℂ)),
    IsClosed (S : Set C(K, ℂ)) →
    ∀ (a b : ℂ) (ha : a ∉ (K : Set ℂ)) (hb : b ∉ (K : Set ℂ)),
    resolvent K a ha ∈ S → ‖(b - a) • resolvent K a ha‖ < 1 →
    resolvent K b hb ∈ S

def resolvent_polynomial_series_type : Prop :=
  ∀ (K : Compacts ℂ) (b : ℂ) (hb : b ∉ (K : Set ℂ)),
    ‖coordinate K‖ < ‖b‖ →
    HasSum (fun n : ℕ => -(b ^ (n + 1))⁻¹ • coordinate K ^ n)
      (resolvent K b hb)

def closedAlgebra_resolvent_far_type : Prop :=
  ∀ (K : Compacts ℂ) (S : Subalgebra ℂ C(K, ℂ)),
    IsClosed (S : Set C(K, ℂ)) → coordinate K ∈ S →
    ∀ (b : ℂ) (hb : b ∉ (K : Set ℂ)), ‖coordinate K‖ < ‖b‖ →
      resolvent K b hb ∈ S

/-- The finite part of the spherical component containing infinity is
connected and is the unique unbounded plane complementary component. -/
def unbounded_component_type : Prop :=
  ∀ K : Compacts ℂ,
    IsConnected (sphereFinite ⁻¹'
      connectedComponentIn (sphericalComplement K) sphereInfty) ∧
    ¬ Bornology.IsBounded (sphereFinite ⁻¹'
      connectedComponentIn (sphericalComplement K) sphereInfty) ∧
    ∀ a : ℂ, a ∉ (K : Set ℂ) →
      (¬ Bornology.IsBounded (connectedComponentIn (K : Set ℂ)ᶜ a) ↔
        sphereFinite a ∈ connectedComponentIn (sphericalComplement K) sphereInfty)

def resolvent_mem_uniformClosure_type : Prop :=
  ∀ (K : Compacts ℂ) (A : Set RiemannSphere), A ⊆ sphericalComplement K →
    ∀ (a : ℂ) (ha : a ∉ (K : Set ℂ)),
    (connectedComponentIn (sphericalComplement K) (sphereFinite a) ∩ A).Nonempty →
      resolvent K a ha ∈ uniformClosure K A

/-- The polynomial-hull application needs approximation by actual
polynomials on just the unbounded component. -/
def resolvent_polynomial_approximation_type : Prop :=
  ∀ (K : Compacts ℂ) (a : ℂ), a ∉ (K : Set ℂ) →
    ¬ Bornology.IsBounded (connectedComponentIn (K : Set ℂ)ᶜ a) →
    ∀ ε : ℝ, 0 < ε → ∃ P : Polynomial ℂ,
      ∀ z ∈ (K : Set ℂ), ‖(z - a)⁻¹ - P.eval z‖ < ε

end Specs.D12Complex.Ch15.PoleMovement
