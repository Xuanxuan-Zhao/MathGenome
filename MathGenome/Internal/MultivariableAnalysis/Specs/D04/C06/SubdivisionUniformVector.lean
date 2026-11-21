import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.BoxAlgebra
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Remaining assertions of paper.tex, d04:06:algebra. Ambient extensions are
ignored outside the closed box. All dimensions may be zero. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Specs.D04.C06.SubdivisionUniformVector.Model
open Specs.D04.C06.DarbouxIntegral.Model

def VectorBounded {n k : ℕ} (f : E n → E k) (Q : Box n) : Prop :=
  ∃ M : ℝ, ∀ x ∈ carrier Q, ‖f x‖ ≤ M

def VectorIntegrable {n k : ℕ} (f : E n → E k) (Q : Box n) : Prop :=
  ∀ i : Fin k, Integrable (fun x => f x i) Q

def vectorIntegral {n k : ℕ} (f : E n → E k) (Q : Box n)
    (h : VectorIntegrable f Q) : E k :=
  WithLp.toLp 2 (fun i => integral (fun x => f x i) Q (h i))

def vectorTaggedSum {n k : ℕ} (f : E n → E k) {Q : Box n}
    (P : Grid Q) (ξ : Tagging P) : E k :=
  ∑ c, cellContent P c • f (ξ c)

def HasVectorTaggedIntegral {n k : ℕ} (f : E n → E k) (Q : Box n) (I : E k) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (P : Grid Q) (ξ : Tagging P),
    mesh P < δ → ‖vectorTaggedSum f P ξ - I‖ < ε
end Specs.D04.C06.SubdivisionUniformVector.Model

namespace Specs.D04.C06.SubdivisionUniformVector
open Specs.D04.C06.DarbouxIntegral.Model Model

abbrev VectorBoundedType := {n k : ℕ} → (E n → E k) → Box n → Prop
abbrev VectorIntegrableType := {n k : ℕ} → (E n → E k) → Box n → Prop
abbrev vectorIntegralType := {n k : ℕ} → (f : E n → E k) → (Q : Box n) →
  VectorIntegrable f Q → E k
abbrev vectorTaggedSumType := {n k : ℕ} → (E n → E k) → {Q : Box n} →
  (P : Grid Q) → Tagging P → E k
abbrev HasVectorTaggedIntegralType := {n k : ℕ} → (E n → E k) → Box n → E k → Prop

def VectorBoundedValue : VectorBoundedType := @Model.VectorBounded
def VectorIntegrableValue : VectorIntegrableType := @Model.VectorIntegrable
def vectorIntegralValue : vectorIntegralType := @Model.vectorIntegral
def vectorTaggedSumValue : vectorTaggedSumType := @Model.vectorTaggedSum
def HasVectorTaggedIntegralValue : HasVectorTaggedIntegralType := @Model.HasVectorTaggedIntegral

def subdivision_integrableType : Prop := ∀ {n} (f : E n → ℝ) (Q : Box n),
  Bounded f Q → ∀ P : Grid Q,
  (Integrable f Q ↔ ∀ c, Integrable f (cellBox P c))

def subdivision_integralType : Prop := ∀ {n} (f : E n → ℝ) (Q : Box n)
  (P : Grid Q) (hf : Integrable f Q) (hc : ∀ c, Integrable f (cellBox P c)),
  integral f Q hf = ∑ c, integral f (cellBox P c) (hc c)

def integral_sub_le_supType : Prop := ∀ {n} {Q : Box n} {f g : E n → ℝ}
  (hf : Integrable f Q) (hg : Integrable g Q),
  |integral f Q hf - integral g Q hg| ≤
    content Q * sSup ((fun x => |f x - g x|) '' carrier Q)

def uniform_limitType : Prop := ∀ {n} {Q : Box n} (F : ℕ → E n → ℝ)
  (f : E n → ℝ) (hF : ∀ j, Integrable (F j) Q),
  TendstoUniformlyOn F f atTop (carrier Q) →
  ∃ hf : Integrable f Q,
    Tendsto (fun j => integral (F j) Q (hF j)) atTop (𝓝 (integral f Q hf))

def vector_bounded_iffType : Prop := ∀ {n k} (f : E n → E k) (Q : Box n),
  VectorBounded f Q ↔ ∀ i : Fin k, Bounded (fun x => f x i) Q

def vector_integral_coordinateType : Prop := ∀ {n k} (f : E n → E k) (Q : Box n)
  (hf : VectorIntegrable f Q) (i : Fin k),
  vectorIntegral f Q hf i = integral (fun x => f x i) Q (hf i)

def vector_tagged_criteriaType : Prop := ∀ {n k} (f : E n → E k) (Q : Box n),
  VectorBounded f Q →
  (VectorIntegrable f Q ↔ ∃ I, HasVectorTaggedIntegral f Q I) ∧
  (∀ hf : VectorIntegrable f Q, HasVectorTaggedIntegral f Q (vectorIntegral f Q hf)) ∧
  ∀ I, HasVectorTaggedIntegral f Q I →
    ∃ hf : VectorIntegrable f Q, I = vectorIntegral f Q hf

def integrable_normType : Prop := ∀ {n k} {Q : Box n} {f : E n → E k},
  VectorIntegrable f Q → Integrable (fun x => ‖f x‖) Q

def vector_integral_norm_leType : Prop := ∀ {n k} {Q : Box n} {f : E n → E k}
  (hf : VectorIntegrable f Q) (hn : Integrable (fun x => ‖f x‖) Q),
  ‖vectorIntegral f Q hf‖ ≤ integral (fun x => ‖f x‖) Q hn

def vector_integrable_linearType : Prop := ∀ {n k m} {Q : Box n} {f : E n → E k}
  (A : E k →ₗ[ℝ] E m), VectorIntegrable f Q → VectorIntegrable (fun x => A (f x)) Q

def vector_integral_linearType : Prop := ∀ {n k m} {Q : Box n} {f : E n → E k}
  (A : E k →ₗ[ℝ] E m) (hf : VectorIntegrable f Q)
  (hA : VectorIntegrable (fun x => A (f x)) Q),
  vectorIntegral (fun x => A (f x)) Q hA = A (vectorIntegral f Q hf)

def vector_degenerateType : Prop := ∀ {n k} {Q : Box n} (f : E n → E k)
  (hf : VectorIntegrable f Q), Degenerate Q → vectorIntegral f Q hf = 0

def vector_zero_domainType : Prop := ∀ {k} (Q : Box 0) (f : E 0 → E k),
  ∃ hf : VectorIntegrable f Q, vectorIntegral f Q hf = f 0

def vector_zero_targetType : Prop := ∀ {n} (Q : Box n) (f : E n → E 0),
  ∃ hf : VectorIntegrable f Q, vectorIntegral f Q hf = 0

end Specs.D04.C06.SubdivisionUniformVector
