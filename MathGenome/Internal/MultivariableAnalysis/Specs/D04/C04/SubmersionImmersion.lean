import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.ConstantRank
import Mathlib.Topology.Maps.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! Independent specification of d04:04:submersion-immersion. Ambient functions
represent functions on the displayed open domain, as in the derivative interface.
Rank normal forms use exactly the shared first-coordinate projection/inclusion.
All dimensions, including zero, are permitted. No global surjectivity or global
embedding is included. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace Specs.D04.C04.SubmersionImmersion
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C04.ConstantRank
namespace Model

def SubmersionAt {n m : ℕ} (f : E n → E m) (a : E n) : Prop :=
  Function.Surjective (totalDerivative f a)

def ImmersionAt {n m : ℕ} (f : E n → E m) (a : E n) : Prop :=
  Function.Injective (totalDerivative f a)

/-- An embedding uses the relative topology on its domain and image. An
IsEmbedding is precisely a homeomorphism onto the range with its subspace topology. -/
def EmbeddingOn {n m : ℕ} (f : E n → E m) (X : Set (E n)) : Prop :=
  Topology.IsEmbedding (fun x : X => f x)

end Model
open Model
abbrev SubmersionAtType := {n m : ℕ} → (E n → E m) → E n → Prop
def SubmersionAtValue : SubmersionAtType := @Model.SubmersionAt
abbrev ImmersionAtType := {n m : ℕ} → (E n → E m) → E n → Prop
def ImmersionAtValue : ImmersionAtType := @Model.ImmersionAt
abbrev EmbeddingOnType := {n m : ℕ} → (E n → E m) → Set (E n) → Prop
def EmbeddingOnValue : EmbeddingOnType := @Model.EmbeddingOn

/-- Explicit realization of the relative-topology meaning of EmbeddingOn. -/
def embeddingOn_homeomorphType : Prop :=
  ∀ {n m : ℕ} (f : E n → E m) (X : Set (E n)), EmbeddingOn f X →
    ∃ e : X ≃ₜ (f '' X), ∀ x : X, (e x).val = f x

/-- These are derivatives of the actual scalar component functions, not an
unrelated family of covectors. Differentiability is explicitly required. -/
def submersion_iff_componentsType : Prop :=
  ∀ {n m : ℕ} (f : E n → E m) (a : E n), DifferentiableAt ℝ f a →
    (SubmersionAt f a ↔ LinearIndependent ℝ
      (fun i : Fin m => (totalDerivative (fun x => f x i) a).toLinearMap))

def submersion_finiteType : Prop :=
  ∀ {n m : ℕ} (r : ℕ) (U : Set (E n)) (f : E n → E m) (a : E n),
    1 ≤ r → IsOpen U → CrOn r U f → a ∈ U → SubmersionAt f a →
    m ≤ n ∧ RankNormalForm (r : ℕ∞ω) U f a m ∧
      ∀ᶠ x in 𝓝 a, SubmersionAt f x

def submersion_smoothType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m) (a : E n),
    IsOpen U → SmoothOn U f → a ∈ U → SubmersionAt f a →
    m ≤ n ∧ RankNormalForm ∞ U f a m ∧ ∀ᶠ x in 𝓝 a, SubmersionAt f x

def immersion_finiteType : Prop :=
  ∀ {n m : ℕ} (r : ℕ) (U : Set (E n)) (f : E n → E m) (a : E n),
    1 ≤ r → IsOpen U → CrOn r U f → a ∈ U → ImmersionAt f a →
    n ≤ m ∧ RankNormalForm (r : ℕ∞ω) U f a n ∧
      (∀ᶠ x in 𝓝 a, ImmersionAt f x) ∧
      ∃ X : Set (E n), IsOpen X ∧ a ∈ X ∧ X ⊆ U ∧ EmbeddingOn f X

def immersion_smoothType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m) (a : E n),
    IsOpen U → SmoothOn U f → a ∈ U → ImmersionAt f a →
    n ≤ m ∧ RankNormalForm ∞ U f a n ∧
      (∀ᶠ x in 𝓝 a, ImmersionAt f x) ∧
      ∃ X : Set (E n), IsOpen X ∧ a ∈ X ∧ X ⊆ U ∧ EmbeddingOn f X

/-- Openness of every open subset of the domain. In particular f(U) is open.
For any open target V containing f(U), these images are also open in V;
there is no assertion that f(U) equals that target. -/
def submersion_open_finiteType : Prop :=
  ∀ {n m : ℕ} (r : ℕ) (U : Set (E n)) (f : E n → E m),
    1 ≤ r → IsOpen U → CrOn r U f → (∀ a ∈ U, SubmersionAt f a) →
    ∀ X : Set (E n), IsOpen X → X ⊆ U → IsOpen (f '' X)

def submersion_open_smoothType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m),
    IsOpen U → SmoothOn U f → (∀ a ∈ U, SubmersionAt f a) →
    ∀ X : Set (E n), IsOpen X → X ⊆ U → IsOpen (f '' X)
end Specs.D04.C04.SubmersionImmersion
