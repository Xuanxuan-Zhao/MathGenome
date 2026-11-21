import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.AsymptoticScale
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.Composition

/-!
Independent full proposition types for K03.17.operations, paper.tex:4335–4371.
Only libraries and upstream Specs are imported. The inherited finite sums,
expansion predicates, and polynomial operations retain their canonical values.

The domain and direction are represented by a filter, with a scalar parameter
`t` tending to zero. Thus real/complex, one-sided, punctured and relative
approaches are covered. The arbitrary-scale identities keep every product
scale. Truncation is justified only for the power-scale theorems. Division
proves eventual invertibility after exposing a nonzero leading coefficient.
Composition retains compatible domains and the actual outer value at inner
zeros. Every order m, including zero, is quantified explicitly.
-/
namespace Specs.SingleVariableAnalysis.Ch17.Operations
open Filter Asymptotics Polynomial
open scoped Topology BigOperators
universe u v w

def expansion_add_exact : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (P Q r s : X → K) (x : X),
    (P x + r x) + (Q x + s x) = (P x + Q x) + (r x + s x)

def expansion_mul_exact : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (P Q r s : X → K) (x : X),
    (P x + r x) * (Q x + s x) =
      P x * Q x + (P x * s x + Q x * r x + r x * s x)

def expansion_add : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (φ : ℕ → X → K)
    (a b : ℕ → K) (f g : X → K) (m : ℕ)
    (hf : Specs.SingleVariableAnalysis.Ch17.AsymptoticScale.hasScalarExpansionThroughValue l φ a f m)
    (hg : Specs.SingleVariableAnalysis.Ch17.AsymptoticScale.hasScalarExpansionThroughValue l φ b g m),
    Specs.SingleVariableAnalysis.Ch17.AsymptoticScale.hasScalarExpansionThroughValue l φ (fun j => a j + b j) (fun x => f x + g x) m

def partialSum_mul_scales : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (φ ψ : ℕ → X → K) (a b : ℕ → K)
    (m n : ℕ) (x : X),
    Specs.SingleVariableAnalysis.Ch17.AsymptoticScale.asymptoticPartialSumValue φ a m x * Specs.SingleVariableAnalysis.Ch17.AsymptoticScale.asymptoticPartialSumValue ψ b n x =
      ∑ i ∈ Finset.range (m+1), ∑ j ∈ Finset.range (n+1),
        (a i * b j) * (φ i x * ψ j x)

def expansion_product_errors : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (P Q r s p q α β : X → K)
    (hP : Specs.SingleVariableAnalysis.Ch02.BigO.scalarBigOValue l P p) (hQ : Specs.SingleVariableAnalysis.Ch02.BigO.scalarBigOValue l Q q)
    (hr : Specs.SingleVariableAnalysis.Ch02.BigO.scalarLittleOValue l r α) (hs : Specs.SingleVariableAnalysis.Ch02.BigO.scalarLittleOValue l s β),
    Specs.SingleVariableAnalysis.Ch02.BigO.scalarLittleOValue l (fun x => P x * s x) (fun x => p x * β x) ∧
    Specs.SingleVariableAnalysis.Ch02.BigO.scalarLittleOValue l (fun x => Q x * r x) (fun x => q x * α x) ∧
    Specs.SingleVariableAnalysis.Ch02.BigO.scalarLittleOValue l (fun x => r x * s x) (fun x => α x * β x)

def finite_reciprocal_identity : Prop :=
  ∀ {K : Type v} [NormedField K] (z : K) (m : ℕ) (hz : 1 + z ≠ 0),
    (1 + z)⁻¹ = (∑ j ∈ Finset.range (m+1), (-z)^j) +
      (-z)^(m+1) / (1+z)

def finite_reciprocal_remainder : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (u : X → K)
    (hu : Tendsto u l (𝓝 0)) (m : ℕ),
    (∀ᶠ x in l, 1 + u x ≠ 0) ∧
    (fun x => (1 + u x)⁻¹ - ∑ j ∈ Finset.range (m+1), (-u x)^j)
      =o[l] (fun x => u x^m)

def factored_division : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (f g ψ u : X → K) (a : K) (m : ℕ)
    (ha : a ≠ 0) (hψ : ∀ᶠ x in l, ψ x ≠ 0)
    (hu : Tendsto u l (𝓝 0))
    (hg : ∀ᶠ x in l, g x = (a * ψ x) * (1 + u x)),
    (∀ᶠ x in l, g x ≠ 0) ∧
    (fun x => f x / g x - (f x / (a * ψ x)) *
      (∑ j ∈ Finset.range (m+1), (-u x)^j))
      =o[l] (fun x => (f x / (a * ψ x)) * u x^m)

def leading_scale_factorization : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (g ψ : X → K) (a : K)
    (ha : a ≠ 0) (hψ : ∀ᶠ x in l, ψ x ≠ 0)
    (hg : Specs.SingleVariableAnalysis.Ch02.BigO.scalarLittleOValue l (fun x => g x - a * ψ x) ψ),
    ∃ u : X → K, Tendsto u l (𝓝 0) ∧
      (∀ᶠ x in l, g x = (a * ψ x) * (1 + u x)) ∧
      (∀ᶠ x in l, g x ≠ 0)

def expansion_leading_term : Prop :=
  ∀ {X : Type u} {K : Type v} [NormedField K] (l : Filter X) (φ : ℕ → X → K)
    (hφ : Specs.SingleVariableAnalysis.Ch17.AsymptoticScale.isScalarAsymptoticScaleValue l φ) (a : ℕ → K) (f : X → K) (m : ℕ)
    (hf : Specs.SingleVariableAnalysis.Ch17.AsymptoticScale.hasScalarExpansionThroughValue l φ a f m),
    Specs.SingleVariableAnalysis.Ch02.BigO.scalarLittleOValue l (fun x => f x - a 0 * φ 0 x) (φ 0)

def compose_remainder : Prop :=
  ∀ {X : Type u} {K : Type v} {L : Type w} [NormedField K] [NormedField L] (l : Filter X) (D : Set K) (t u : X → K)
    (r : K → L) (m : ℕ) (ht : Tendsto t l (𝓝 0)) (hu : u =O[l] t)
    (hD : ∀ᶠ x in l, u x ∈ insert 0 D) (h0 : r 0 = 0)
    (hr : r =o[𝓝[D \ {0}] 0] (fun z => z^m)),
    (fun x => r (u x)) =o[l] (fun x => t x^m)

def power_polynomial_truncation : Prop :=
  ∀ {X : Type u} {K : Type v} [RCLike K] {l : Filter X} (t : X → K)
    (ht : Tendsto t l (𝓝 0)) (m : ℕ) (P : Polynomial K),
    (fun x => P.eval (t x) - (Specs.SingleVariableAnalysis.Ch06.Composition.truncatePolynomialValue m P).eval (t x))
      =o[l] (fun x => t x^m)

def power_polynomial_mul : Prop :=
  ∀ {X : Type u} {K : Type v} [RCLike K] {l : Filter X} (t : X → K) (ht : Tendsto t l (𝓝 0))
    (m : ℕ) (f g : X → K) (P Q : Polynomial K)
    (hf : (fun x => f x - P.eval (t x)) =o[l] (fun x => t x^m))
    (hg : (fun x => g x - Q.eval (t x)) =o[l] (fun x => t x^m)),
    (fun x => f x * g x - (Specs.SingleVariableAnalysis.Ch06.Composition.truncatePolynomialValue m (P*Q)).eval (t x))
      =o[l] (fun x => t x^m)

def power_product_coeff : Prop :=
  ∀ {K : Type v} [RCLike K] (m : ℕ) (P Q : Polynomial K) (k : ℕ) (hk : k ≤ m),
    (Specs.SingleVariableAnalysis.Ch06.Composition.truncatePolynomialValue m (P*Q)).coeff k =
      ∑ j ∈ Finset.range (k+1), P.coeff j * Q.coeff (k-j)

def power_expansion_mul : Prop :=
  ∀ {X : Type u} {K : Type v} [RCLike K] {l : Filter X} (t : X → K) (ht : Tendsto t l (𝓝 0))
    (a b : ℕ → K) (f g : X → K) (m : ℕ)
    (hf : Specs.SingleVariableAnalysis.Ch17.AsymptoticScale.hasScalarExpansionThroughValue l (fun j x => t x^j) a f m)
    (hg : Specs.SingleVariableAnalysis.Ch17.AsymptoticScale.hasScalarExpansionThroughValue l (fun j x => t x^j) b g m),
    Specs.SingleVariableAnalysis.Ch17.AsymptoticScale.hasScalarExpansionThroughValue l (fun j x => t x^j)
      (fun k => ∑ j ∈ Finset.range (k+1), a j * b (k-j)) (fun x => f x * g x) m

def power_polynomial_division : Prop :=
  ∀ {X : Type u} {K : Type v} [RCLike K] {l : Filter X} (t : X → K) (ht : Tendsto t l (𝓝 0))
    (m : ℕ) (f g : X → K) (P Q : Polynomial K) (hq : Q.coeff 0 ≠ 0)
    (hf : (fun x => f x - P.eval (t x)) =o[l] (fun x => t x^m))
    (hg : (fun x => g x - Q.eval (t x)) =o[l] (fun x => t x^m)),
    (∀ᶠ x in l, g x ≠ 0) ∧
    (fun x => f x / g x - (Specs.SingleVariableAnalysis.Ch06.Composition.quotientPolynomialValue m P Q).eval (t x))
      =o[l] (fun x => t x^m)

def power_polynomial_composition : Prop :=
  ∀ {X : Type u} {K : Type v} {L : Type w} [RCLike K] [RCLike L] [NormedAlgebra K L] {l : Filter X} (t : X → K)
    (ht : Tendsto t l (𝓝 0)) (D : Set K) (m : ℕ) (u : X → K) (b : K)
    (P : Polynomial K) (Q : Polynomial L) (F : K → L)
    (hP : P.coeff 0 = 0) (hu : (fun x => u x - b) =O[l] t)
    (hi : (fun x => u x - b - P.eval (t x)) =o[l] (fun x => t x^m))
    (hF : (fun z => F (b+z) - Q.eval (algebraMap K L z))
      =o[𝓝[D \ {0}] 0] (fun z => z^m))
    (hF0 : F b = Q.eval 0) (hD : ∀ᶠ x in l, u x - b ∈ insert 0 D),
    (fun x => F (u x) - (Specs.SingleVariableAnalysis.Ch06.Composition.compositionPolynomialValue m P Q).eval (algebraMap K L (t x)))
      =o[l] (fun x => t x^m)

end Specs.SingleVariableAnalysis.Ch17.Operations
