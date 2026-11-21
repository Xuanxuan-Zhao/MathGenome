import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.DirichletResolvent
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Independent spectral statements for paper.tex 2402–2450. Natural index j
represents manuscript index j+1. All coefficient spaces and inclusions are the
actual L²(Ω) and H¹₀(Ω) of the shared interfaces. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace P201Specs.DirichletEigenbasis
open P201Specs.Dirichlet

/-- The associated operator is fixed by the actual coefficient energy form. -/
def IsCoefficientForm {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (a : P201.Elliptic.DenseForm ℝ (Lp ℝ Ω 2)) : Prop :=
  a.domain = (hZeroUnderlying (𝕜 := ℝ) Ω).range ∧
  ∀ (u v : H10 ℝ Ω) (hu : hZeroUnderlying Ω u ∈ a.domain)
    (hv : hZeroUnderlying Ω v ∈ a.domain),
    a.form ⟨hZeroUnderlying Ω u, hu⟩ ⟨hZeroUnderlying Ω v, hv⟩ =
      ellipticEnergyForm Ω A u.val v.val

/-- An eigenspace of a partial operator, including its domain requirement. -/
def operatorEigenspace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (L : ExpandedFA.Unbounded.Operator ℝ H H) (r : ℝ) : Submodule ℝ H :=
  L.graph.comap ((LinearMap.id : H →ₗ[ℝ] H).prod (r • LinearMap.id))

/-- Infinite-dimensional compact inverse, with an actual ℕ enumeration and
normalization, rather than a presumed sorted eigenbasis. -/
def CompactBasisStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    ¬FiniteDimensional ℝ H → ∀ S : H →L[ℝ] H,
      IsCompactOperator S → S.IsPositive → Function.Injective S →
      ∃ (e : HilbertBasis ℕ ℝ H) (μ : ℕ → ℝ),
        (∀ j, 0 < μ j) ∧ Antitone μ ∧
        (∀ j, S (e j) = μ j • e j) ∧
        (∀ u, HasSum (fun j => (μ j * inner ℝ (e j) u) • e j) (S u)) ∧
        (∀ ε : ℝ, 0 < ε → {j | ε ≤ μ j}.Finite) ∧
        (∀ r : ℝ, 0 < r → Module.End.eigenspace S.toLinearMap r =
          Submodule.span ℝ (e '' {j | μ j = r})) ∧
        Tendsto μ atTop (𝓝 0) ∧
        Monotone (fun j => (μ j)⁻¹) ∧
        Tendsto (fun j => (μ j)⁻¹) atTop atTop

/-- Exact diagonal domain for the inverse relation of a bounded operator. -/
def DiagonalInverseStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : H →L[ℝ] H) (L : ExpandedFA.Unbounded.Operator ℝ H H)
    (e : HilbertBasis ℕ ℝ H) (μ : ℕ → ℝ),
    S.IsSymmetric → (∀ j, μ j ≠ 0) →
    (∀ j, S (e j) = μ j • e j) →
    (∀ u f : H, (u, f) ∈ L.graph ↔ S f = u) →
    (∀ u : H, u ∈ L.domain ↔
      Summable (fun j => (μ j)⁻¹ ^ 2 * (inner ℝ (e j) u) ^ 2)) ∧
    (∀ u : L.domain, HasSum
      (fun j => ((μ j)⁻¹ * inner ℝ (e j) (u : H)) • e j) (L u))

/-- Operator part of the resolution, on one fixed common spectral sequence. -/
def OperatorData {n : ℕ} (Ω : Domain n)
    (a : P201.Elliptic.DenseForm ℝ (Lp ℝ Ω 2))
    (e : HilbertBasis ℕ ℝ (Lp ℝ Ω 2)) (ev : ℕ → ℝ) (v : ℕ → H10 ℝ Ω) : Prop :=
    (∀ j, 0 < ev j) ∧ Monotone ev ∧ Tendsto ev atTop atTop ∧
    (∀ j, hZeroUnderlying Ω (v j) = e j ∧
      (e j, ev j • e j) ∈ a.associatedOperator.graph) ∧
    (∀ r : ℝ, 0 < r → {j | ev j = r}.Finite ∧
      operatorEigenspace a.associatedOperator r =
        Submodule.span ℝ (e '' {j | ev j = r})) ∧
    (∀ u : Lp ℝ Ω 2, u ∈ a.associatedOperator.domain ↔
      Summable (fun j => ev j ^ 2 * (inner ℝ (e j) u) ^ 2)) ∧
    (∀ u : a.associatedOperator.domain,
      HasSum (fun j => (ev j * inner ℝ (e j) (u : Lp ℝ Ω 2)) • e j)
        (a.associatedOperator u))

/-- Form part, using the actual H¹₀ topology and the same L² sequence. -/
def FormData {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (e : HilbertBasis ℕ ℝ (Lp ℝ Ω 2)) (ev : ℕ → ℝ) (v : ℕ → H10 ℝ Ω) : Prop :=
    (let w : ℕ → H10 ℝ Ω := fun j => (Real.sqrt (ev j))⁻¹ • v j
     (∀ i j, ellipticEnergyForm Ω A (w i).val (w j).val =
       if i = j then 1 else 0) ∧
     (Submodule.span ℝ (Set.range w)).topologicalClosure = ⊤) ∧
    (∀ u : H10 ℝ Ω,
      HasSum (fun j => ev j * (inner ℝ (e j) (hZeroUnderlying Ω u)) ^ 2)
        (ellipticEnergyForm Ω A u.val u.val)) ∧
    (∀ u : Lp ℝ Ω 2, u ∈ (hZeroUnderlying (𝕜 := ℝ) Ω).range ↔
      Summable (fun j => ev j * (inner ℝ (e j) u) ^ 2))

/-- Full resolution including the exact operator and form domains. -/
def Resolution {n : ℕ} (Ω : Domain n) (A : MatrixField n)
    (a : P201.Elliptic.DenseForm ℝ (Lp ℝ Ω 2)) : Prop :=
  ∃ (e : HilbertBasis ℕ ℝ (Lp ℝ Ω 2)) (ev : ℕ → ℝ) (v : ℕ → H10 ℝ Ω),
    OperatorData Ω a e ev v ∧ FormData Ω A e ev v

/-- The physical eigenbasis and complete operator-domain characterization. -/
def OperatorStatement : Prop :=
  ∀ (m : ℕ) (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
    (Ω : Set (Space (m + 1))).Nonempty →
    ∀ A : MatrixField (m + 1), MemLp A ∞ (domainMeasure Ω) →
      ∀ lam : ℝ, 0 < lam → Elliptic Ω A lam → Symmetric Ω A →
        ∀ a : P201.Elliptic.DenseForm ℝ (Lp ℝ Ω 2),
          IsCoefficientForm Ω A a →
          ∃ (e : HilbertBasis ℕ ℝ (Lp ℝ Ω 2)) (ev : ℕ → ℝ) (v : ℕ → H10 ℝ Ω),
            OperatorData Ω a e ev v

def InfiniteDimensionStatement : Prop :=
  ∀ (m : ℕ) (Ω : Domain (m + 1)),
    (Ω : Set (Space (m + 1))).Nonempty → ¬FiniteDimensional ℝ (Lp ℝ Ω 2)

/-- Universal over realizations of the same coefficient form; it therefore
applies to the exact realization constructed upstream. No spectral assumption
or domain certificate is among its hypotheses. -/
def Statement : Prop :=
  ∀ (m : ℕ) (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
    (Ω : Set (Space (m + 1))).Nonempty →
    ∀ A : MatrixField (m + 1), MemLp A ∞ (domainMeasure Ω) →
      ∀ lam : ℝ, 0 < lam → Elliptic Ω A lam → Symmetric Ω A →
        ∀ a : P201.Elliptic.DenseForm ℝ (Lp ℝ Ω 2),
          IsCoefficientForm Ω A a → Resolution Ω A a

end P201Specs.DirichletEigenbasis
