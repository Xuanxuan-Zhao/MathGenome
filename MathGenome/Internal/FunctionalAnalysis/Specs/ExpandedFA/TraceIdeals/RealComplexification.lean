import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.PreHilbertCompactSpectral
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceClassDefinitions

/-! The existing Hilbert complexification, with its original inner product and
norm. No new space or scalar/metric instances are introduced here. -/
noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.TraceIdeals.RealComplexification
universe v w z
abbrev Space := Hilbert.PreHilbertCompactSpectral.Spec.Complexification.Space
open Hilbert.PreHilbertCompactSpectral.Spec.Complexification

namespace Spec
variable {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]

lemma norm_sq (p : Space H) : ‖p‖ ^ 2 = ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change inner ℝ p.1 p.1 + inner ℝ p.2 p.2 = _
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- The canonical inclusion on the owner's exact pair model. -/
def inclusion : H →ₗᵢ[ℝ] Space H where
  toFun x := complexPair H x 0
  map_add' x y := by change (x + y, (0:H)) = (x + y, 0 + 0); simp
  map_smul' a x := by change (a • x, (0:H)) = (a • x, a • 0); simp
  norm_map' x := by
    change ‖complexPair H x 0‖ = ‖x‖
    have h := norm_sq (complexPair H x 0)
    change ‖complexPair H x 0‖ ^ 2 = ‖x‖ ^ 2 + ‖(0:H)‖ ^ 2 at h
    rw [norm_zero, zero_pow (by decide : (2:ℕ) ≠ 0), add_zero] at h
    nlinarith [norm_nonneg (complexPair H x 0), norm_nonneg x]

def realPart : Space H →L[ℝ] H :=
  ({ toFun := Prod.fst, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl } : Space H →ₗ[ℝ] H).mkContinuous 1 (fun p => by
        have h := norm_sq p
        change ‖p.1‖ ≤ 1 * ‖p‖
        nlinarith [norm_nonneg p, norm_nonneg p.1, sq_nonneg ‖p.2‖])

def imagPart : Space H →L[ℝ] H :=
  ({ toFun := Prod.snd, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl } : Space H →ₗ[ℝ] H).mkContinuous 1 (fun p => by
        have h := norm_sq p
        change ‖p.2‖ ≤ 1 * ‖p‖
        nlinarith [norm_nonneg p, norm_nonneg p.2, sq_nonneg ‖p.1‖])

def conjugation : Space H →ₗᵢ[ℝ] Space H where
  toFun p := complexPair H p.1 (-p.2)
  map_add' p q := by
    change (p.1 + q.1, -(p.2 + q.2)) = (p.1 + q.1, -p.2 + -q.2)
    simp [add_comm]
  map_smul' a p := by
    change (a • p.1, -(a • p.2)) = (a • p.1, a • (-p.2))
    simp
  norm_map' p := by
    change ‖complexPair H p.1 (-p.2)‖ = ‖p‖
    have h₁ := norm_sq (complexPair H p.1 (-p.2))
    have h₂ := norm_sq p
    change ‖complexPair H p.1 (-p.2)‖ ^ 2 = ‖p.1‖ ^ 2 + ‖-p.2‖ ^ 2 at h₁
    rw [norm_neg] at h₁
    nlinarith [norm_nonneg p, norm_nonneg (complexPair H p.1 (-p.2))]

def operator (T : H →L[ℝ] K) : Space H →L[ℂ] Space K :=
  ({ toFun := fun p => complexPair K (T p.1) (T p.2)
     map_add' := by intro p q; change (T (p.1 + q.1), T (p.2 + q.2)) = _; simp [map_add]; rfl
     map_smul' := by
       intro a p
       change complexPair K (T (a • p).1) (T (a • p).2) = a • complexPair K (T p.1) (T p.2)
       rw [csmul, csmul]
       simp only [complexPair, map_sub, map_smul, map_add]
       rfl } : Space H →ₗ[ℂ] Space K).mkContinuous
    ‖T‖ (fun p => by
      have h := norm_sq (complexPair K (T p.1) (T p.2))
      have hp := norm_sq p
      have h₁ := T.le_opNorm p.1
      have h₂ := T.le_opNorm p.2
      have hs₁ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T) (norm_nonneg p.1))).mpr h₁
      have hs₂ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T) (norm_nonneg p.2))).mpr h₂
      change ‖complexPair K (T p.1) (T p.2)‖ ≤ ‖T‖ * ‖p‖
      change ‖complexPair K (T p.1) (T p.2)‖ ^ 2 = ‖T p.1‖ ^ 2 + ‖T p.2‖ ^ 2 at h
      have hs : ‖complexPair K (T p.1) (T p.2)‖ ^ 2 ≤ (‖T‖ * ‖p‖) ^ 2 := by
        rw [h, mul_pow, hp, mul_add]
        simp only [mul_pow] at hs₁ hs₂
        nlinarith
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T) (norm_nonneg p))).mp hs
      )

lemma norm_le_add (p : Space H) : ‖p‖ ≤ ‖p.1‖ + ‖p.2‖ := by
  have h := norm_sq p
  nlinarith [norm_nonneg p, norm_nonneg p.1, norm_nonneg p.2]

def InclusionType := ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
  H →ₗᵢ[ℝ] Space H

def RealPartType := ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
  Space H →L[ℝ] H

def ImagPartType := ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
  Space H →L[ℝ] H

def ConjugationType := ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
  Space H →ₗᵢ[ℝ] Space H

def OperatorType := ∀ {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace ℝ H] [InnerProductSpace ℝ K],
  (H →L[ℝ] K) → (Space H →L[ℂ] Space K)

/-- A proof term for use in independent types; this is deliberately not a new
instance. The implementation uses the owner's existing completeness instance. -/
@[instance_reducible] def completeSpace [CompleteSpace H] : CompleteSpace (Space H) := by
  let l : Space H ≃ₗ[ℝ] H × H := LinearEquiv.refl ℝ (H × H)
  let e : Space H ≃L[ℝ] H × H :=
    l.toContinuousLinearEquivOfBounds 1 2
      (fun p => by
        rw [one_mul]
        have h := norm_sq p
        change max ‖p.1‖ ‖p.2‖ ≤ ‖p‖
        apply max_le <;> nlinarith [norm_nonneg p, norm_nonneg p.1,
          norm_nonneg p.2, sq_nonneg ‖p.1‖, sq_nonneg ‖p.2‖])
      (fun p => by
        have hh := norm_le_add (l.symm p)
        exact hh.trans (by
          change ‖p.1‖ + ‖p.2‖ ≤ 2 * max ‖p.1‖ ‖p.2‖
          linarith [le_max_left ‖p.1‖ ‖p.2‖, le_max_right ‖p.1‖ ‖p.2‖]))
  exact e.isUniformEmbedding.isUniformInducing.completeSpace_congr e.surjective |>.mpr inferInstance

local instance [CompleteSpace H] : CompleteSpace (Space H) := completeSpace

open TraceClassDefinitions.Spec
open CompactSpectral.SingularApproximation.Spec

def Coordinates : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    (∀ p : Space H, p = inclusion p.1 + Complex.I • inclusion p.2) ∧
    (∀ p : Space H, conjugation p = p ↔ ∃ x : H, inclusion x = p) ∧
    (∀ p : Space H, conjugation (conjugation p) = p) ∧
    (∀ (a : ℂ) (p : Space H), conjugation (a • p) = star a • conjugation p) ∧
    (∀ (p : Space H) (x y : H),
      p = inclusion x + Complex.I • inclusion y ↔ realPart p = x ∧ imagPart p = y)

def OperatorFormula : Prop :=
  ∀ (H : Type v) (K : Type w) [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K] (T : H →L[ℝ] K),
    (∀ p : Space H, operator T p = complexPair K (T p.1) (T p.2)) ∧
    (∀ S : Space H →L[ℂ] Space K,
      (∀ x, S (inclusion x) = inclusion (T x)) → S = operator T) ∧
    ‖operator T‖ = ‖T‖

def OperatorAlgebra : Prop :=
  (∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    operator (ContinuousLinearMap.id ℝ H) = ContinuousLinearMap.id ℂ (Space H)) ∧
  (∀ (H : Type v) (K : Type w) [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K] (S T : H →L[ℝ] K) (r : ℝ),
    operator (S + T) = operator S + operator T ∧
    operator (r • T) = (r : ℂ) • operator T) ∧
  (∀ (H : Type v) (K : Type w) (G : Type z)
    [NormedAddCommGroup H] [NormedAddCommGroup K] [NormedAddCommGroup G]
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K] [InnerProductSpace ℝ G]
    (T : H →L[ℝ] K) (S : K →L[ℝ] G),
    operator (S.comp T) = (operator S).comp (operator T))

def Adjoint : Prop :=
  ∀ (H : Type v) (K : Type w) [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[ℝ] K),
    (operator T).adjoint = operator T.adjoint

def Compactness : Prop :=
  ∀ (H : Type v) (K : Type w) [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K] (T : H →L[ℝ] K),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap ↔
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue (operator T).toLinearMap

def BasisExtension : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ι : Type z) (b : HilbertBasis ι ℝ H),
    ∃ B : HilbertBasis ι ℂ (Space H), ∀ i, B i = inclusion (b i)

def SingularValues : Prop :=
  ∀ (H : Type v) (K : Type w) [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[ℝ] K),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∀ n : ℕ, SingularValueValue (operator T) n = SingularValueValue T n

def TraceIdeal : Prop :=
  ∀ (H : Type v) (K : Type w) [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[ℝ] K),
    (IsTraceClassValue T ↔ IsTraceClassValue (operator T)) ∧
    (IsTraceClassValue T → TraceNormValue (operator T) = TraceNormValue T)

def Trace : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T : H →L[ℝ] H), IsTraceClassValue T →
    TraceValue (operator T) = ((TraceValue (𝕜 := ℝ) T : ℝ) : ℂ)

/-- Two-sided bounded inverses, with the actual inverse transported. -/
def Invertibility : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A : H →L[ℝ] H),
    ((∃ B : H →L[ℝ] H, A.comp B = ContinuousLinearMap.id ℝ H ∧
      B.comp A = ContinuousLinearMap.id ℝ H) ↔
    (∃ C : Space H →L[ℂ] Space H, (operator A).comp C = ContinuousLinearMap.id ℂ (Space H) ∧
      C.comp (operator A) = ContinuousLinearMap.id ℂ (Space H))) ∧
    (∀ B : H →L[ℝ] H, A.comp B = ContinuousLinearMap.id ℝ H →
      B.comp A = ContinuousLinearMap.id ℝ H →
      (operator A).comp (operator B) = ContinuousLinearMap.id ℂ (Space H) ∧
      (operator B).comp (operator A) = ContinuousLinearMap.id ℂ (Space H))

/-- Compatibility with the already allocated compact symmetric witness. -/
def EarlierWitness : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (S : Space H →L[ℂ] Space H),
    (∀ p, S p = complexPair H (T p.1) (T p.2)) → S = operator T

end Spec
end ExpandedFA.TraceIdeals.RealComplexification
