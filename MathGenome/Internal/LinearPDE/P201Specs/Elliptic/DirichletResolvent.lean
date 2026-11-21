import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.WeakDirichlet
import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.ClosedForm

/-! The real Dirichlet realization in paper.tex, 2402–2434.  The inclusion
below is the actual zeroth weak-derivative coordinate, with the full H¹ norm.
The statements do not assume density, compactness, or a PDE solution map. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace P201Specs.DirichletResolvent
open P201Specs.Dirichlet

def EmbeddingStatement : Prop :=
  ∀ (m : ℕ) (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
    Function.Injective (hZeroUnderlying (𝕜 := ℝ) Ω) ∧
    DenseRange (hZeroUnderlying (𝕜 := ℝ) Ω) ∧
    IsCompactOperator (hZeroUnderlying (𝕜 := ℝ) Ω)

def InverseStatement : Prop :=
  ∀ (m : ℕ) (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
    ∀ A : MatrixField (m + 1), MemLp A ∞ (domainMeasure Ω) →
      ∀ lam : ℝ, 0 < lam → Elliptic Ω A lam → Symmetric Ω A →
        ∃ T : Lp ℝ Ω 2 →L[ℝ] H10 ℝ Ω,
          (∀ (f : Lp ℝ Ω 2) (v : H10 ℝ Ω),
            ellipticEnergyForm Ω A (T f).val v.val = pivot Ω f v) ∧
          (∀ (f : Lp ℝ Ω 2) (u : H10 ℝ Ω),
            Solves Ω A (pivot Ω f) u.val ↔ u = T f) ∧
          let S := (hZeroUnderlying Ω).comp T
          IsCompactOperator S ∧ S.adjoint = S ∧
          (∀ f, 0 ≤ inner ℝ f (S f)) ∧
          Function.Injective S ∧ DenseRange S

/-- The full operator assertion.  `a` is uniquely fixed by its domain and
the displayed energy identity, and `a.associatedOperator` is exactly the
canonical operator of E10_closed_form. -/
def RealizationStatement : Prop :=
  ∀ (m : ℕ) (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
    (Ω : Set (Space (m + 1))).Nonempty →
    ∀ A : MatrixField (m + 1), MemLp A ∞ (domainMeasure Ω) →
      ∀ lam : ℝ, 0 < lam → Elliptic Ω A lam → Symmetric Ω A →
        ∃ (a : P201.Elliptic.DenseForm ℝ (Lp ℝ Ω 2))
          (T : Lp ℝ Ω 2 →L[ℝ] H10 ℝ Ω),
          a.domain = (hZeroUnderlying (𝕜 := ℝ) Ω).range ∧
          (∀ (u v : H10 ℝ Ω)
            (hu : hZeroUnderlying Ω u ∈ a.domain)
            (hv : hZeroUnderlying Ω v ∈ a.domain),
            a.form ⟨hZeroUnderlying Ω u, hu⟩ ⟨hZeroUnderlying Ω v, hv⟩ =
              ellipticEnergyForm Ω A u.val v.val) ∧
          let L := a.associatedOperator
          let S := (hZeroUnderlying Ω).comp T
          (∀ u f : Lp ℝ Ω 2, (u, f) ∈ L.graph ↔
            ∃ v : H10 ℝ Ω, hZeroUnderlying Ω v = u ∧
              Solves Ω A (pivot Ω f) v.val) ∧
          (∀ u f : Lp ℝ Ω 2, (u, f) ∈ L.graph ↔
            ∃ v : H10 ℝ Ω, hZeroUnderlying Ω v = u ∧
              negativeDivergenceDistribution Ω
                (fun x => WithLp.toLp 2 (fun i =>
                  ∑ j, A x i j * hFirstDerivative v.val j x)) =
                regularDistribution Ω f) ∧
          (∀ u : Lp ℝ Ω 2, u ∈ L.domain ↔ ∃ f, (u, f) ∈ L.graph) ∧
          Dense (L.domain : Set (Lp ℝ Ω 2)) ∧ L = L.adjoint ∧
          (∀ u : L.domain, 0 ≤ inner ℝ (u : Lp ℝ Ω 2) (L u)) ∧
          (∀ f : Lp ℝ Ω 2, (S f, f) ∈ L.graph) ∧
          (∀ u : L.domain, S (L u) = (u : Lp ℝ Ω 2)) ∧
          (L.domain : Set (Lp ℝ Ω 2)) = Set.range S ∧
          IsCompactOperator S ∧ S.adjoint = S ∧
          (∀ f, 0 ≤ inner ℝ f (S f)) ∧
          Function.Injective S ∧ DenseRange S

end P201Specs.DirichletResolvent
