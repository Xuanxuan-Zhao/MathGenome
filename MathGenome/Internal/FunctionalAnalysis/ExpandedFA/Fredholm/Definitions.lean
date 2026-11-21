import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.CompactIdeal
import Mathlib.Tactic.Linarith

/-!
Fredholm and algebraic finite-index maps, Hilbert semi-Fredholm maps, their
indices, and the canonical Calkin algebra. Definitions apply to both scalar
fields, without separability or nonzero-space assumptions. The normed-space
formulas extend the stated Banach-space definitions without changing them.
-/

noncomputable section
namespace ExpandedFA.Fredholm
universe u v w

/-- Algebraic finiteness imposes no topology and asserts no bounded splitting. -/
def IsAlgebraicFiniteIndex : DefinitionsSpec.IsAlgebraicFiniteIndexType :=
  fun {𝕜} _ {_} {F} _ _ _ _ T =>
    FiniteDimensional 𝕜 T.ker ∧ FiniteDimensional 𝕜 (F ⧸ T.range)

/-- Both dimensions are finite; subtraction takes place in ℤ. -/
def algebraicIndex : DefinitionsSpec.algebraicIndexType :=
  fun {𝕜} _ {_} {F} _ _ _ _ T _ =>
    (Module.finrank 𝕜 T.ker : ℤ) - (Module.finrank 𝕜 (F ⧸ T.range) : ℤ)

/-- Closed actual range, finite kernel and finite actual cokernel. -/
def IsFredholm : DefinitionsSpec.IsFredholmType :=
  fun {𝕜} _ {_} {F} _ _ _ _ T =>
    IsClosed (T.range : Set F) ∧
      FiniteDimensional 𝕜 T.ker ∧ FiniteDimensional 𝕜 (F ⧸ T.range)

/-- The Fredholm witness rules out infinite-dimensional `finrank` defaults. -/
def fredholmIndex : DefinitionsSpec.fredholmIndexType :=
  fun {𝕜} _ {_} {F} _ _ _ _ T _ =>
    (Module.finrank 𝕜 T.ker : ℤ) - (Module.finrank 𝕜 (F ⧸ T.range) : ℤ)

abbrev ExtendedIndex : DefinitionsSpec.ExtendedIndexType := WithBot (WithTop ℤ)

/-- Hilbert left semi-Fredholmness: closed range and finite kernel. -/
def IsLeftSemiFredholm : DefinitionsSpec.HilbertPredicateType :=
  fun {𝕜} _ {_} {K} _ _ _ _ T =>
    IsClosed (T.range : Set K) ∧ FiniteDimensional 𝕜 T.ker

/-- Hilbert right semi-Fredholmness: closed range and finite cokernel. -/
def IsRightSemiFredholm : DefinitionsSpec.HilbertPredicateType :=
  fun {𝕜} _ {_} {K} _ _ _ _ T =>
    IsClosed (T.range : Set K) ∧ FiniteDimensional 𝕜 (K ⧸ T.range)

def IsSemiFredholm : DefinitionsSpec.HilbertPredicateType :=
  fun T => IsLeftSemiFredholm T ∨ IsRightSemiFredholm T

/-- Finite difference, −∞ for infinite deficiency, +∞ for infinite nullity.
The witness excludes having both defects infinite. -/
def semiFredholmIndex : DefinitionsSpec.semiFredholmIndexType := by
  classical
  exact fun {𝕜} _ {_} {K} _ _ _ _ T _ =>
    if FiniteDimensional 𝕜 T.ker then
      if FiniteDimensional 𝕜 (K ⧸ T.range) then
        let n : ℤ := (Module.finrank 𝕜 T.ker : ℤ) - (Module.finrank 𝕜 (K ⧸ T.range) : ℤ)
        ((n : WithTop ℤ) : WithBot (WithTop ℤ))
      else ⊥
    else ⊤

/-- All compact endomorphisms, in the canonical native ideal representation. -/
abbrev compactIdeal : DefinitionsSpec.compactIdealType := DefinitionsSpec.compactIdealValue

/-- B(E)/K(E), with the quotient ring operations and the distance quotient norm.
This also covers Hilbert spaces and the zero quotient in finite dimension. -/
abbrev Calkin : DefinitionsSpec.CalkinType := DefinitionsSpec.CalkinValue

/-- The canonical unital scalar-algebra quotient homomorphism. -/
def calkinProjection : DefinitionsSpec.calkinProjectionType :=
  DefinitionsSpec.calkinProjectionValue

section Algebraic
variable {𝕜 : Type u} [Field 𝕜] {E : Type v} {F : Type w}
  [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]

theorem algebraicIndex_eq (T : E →ₗ[𝕜] F) (h : IsAlgebraicFiniteIndex T) :
    algebraicIndex T h =
      (Module.finrank 𝕜 T.ker : ℤ) - (Module.finrank 𝕜 (F ⧸ T.range) : ℤ) := rfl
end Algebraic

section Hilbert
variable {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]

theorem fredholm_iff_left_and_right (T : H →L[𝕜] K) :
    IsFredholm T ↔ IsLeftSemiFredholm T ∧ IsRightSemiFredholm T := by
  simp only [IsFredholm, IsLeftSemiFredholm, IsRightSemiFredholm]
  tauto

theorem semiFredholm_iff (T : H →L[𝕜] K) :
    IsSemiFredholm T ↔ IsClosed (T.range : Set K) ∧
      (FiniteDimensional 𝕜 T.ker ∨ FiniteDimensional 𝕜 (K ⧸ T.range)) := by
  simp only [IsSemiFredholm, IsLeftSemiFredholm, IsRightSemiFredholm]
  tauto

/-- The extended index agrees with the integer index on Fredholm maps. -/
theorem semiFredholmIndex_of_fredholm (T : H →L[𝕜] K) (h : IsFredholm T)
    (hs : IsSemiFredholm T) :
    semiFredholmIndex T hs = ((fredholmIndex T h : WithTop ℤ) : ExtendedIndex) := by
  simp only [semiFredholmIndex, ite_eq_left h.2.1, ite_eq_left h.2.2, fredholmIndex]

theorem semiFredholmIndex_eq_bot (T : H →L[𝕜] K) (h : IsSemiFredholm T)
    (hc : ¬ FiniteDimensional 𝕜 (K ⧸ T.range)) :
    semiFredholmIndex T h = ⊥ := by
  have hk : FiniteDimensional 𝕜 T.ker := h.elim (fun h => h.2) (fun h => (hc h.2).elim)
  simp only [semiFredholmIndex, ite_eq_left hk, ite_eq_right hc]

theorem semiFredholmIndex_eq_top (T : H →L[𝕜] K) (h : IsSemiFredholm T)
    (hk : ¬ FiniteDimensional 𝕜 T.ker) :
    semiFredholmIndex T h = ⊤ := by
  simp only [semiFredholmIndex, ite_eq_right hk]
end Hilbert

section Calkin
variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem mem_compactIdeal (T : E →L[𝕜] E) :
    T ∈ compactIdeal 𝕜 E ↔ Compactness.IsCompactLinearMap T.toLinearMap :=
  (Compactness.compact_iff_isCompactOperator T.toLinearMap).symm

/-- Closedness uses the complete original target, not any approximation property. -/
instance compactIdeal_isClosed [CompleteSpace E] :
    IsClosed (compactIdeal 𝕜 E : Set (E →L[𝕜] E)) :=
  isClosed_setOfPred_isCompactOperator

instance calkinNormedAddCommGroup [CompleteSpace E] : NormedAddCommGroup (Calkin 𝕜 E) :=
  Submodule.Quotient.normedAddCommGroup (compactIdeal 𝕜 E)

theorem calkin_complete [CompleteSpace E] : CompleteSpace (Calkin 𝕜 E) := inferInstance

theorem calkinProjection_surjective : Function.Surjective (calkinProjection 𝕜 E) :=
  (compactIdeal 𝕜 E).mkQ_surjective

theorem calkinProjection_eq_zero (T : E →L[𝕜] E) :
    calkinProjection 𝕜 E T = 0 ↔ Compactness.IsCompactLinearMap T.toLinearMap := by
  exact (Ideal.Quotient.eq_zero_iff_mem).trans (mem_compactIdeal T)

theorem calkinProjection_eq_iff (S T : E →L[𝕜] E) :
    calkinProjection 𝕜 E S = calkinProjection 𝕜 E T ↔
      Compactness.IsCompactLinearMap (S - T).toLinearMap := by
  exact (Ideal.Quotient.eq).trans (mem_compactIdeal (S - T))

theorem calkinProjection_mul (S T : E →L[𝕜] E) :
    calkinProjection 𝕜 E (S * T) = calkinProjection 𝕜 E S * calkinProjection 𝕜 E T := rfl

theorem calkinProjection_norm (T : E →L[𝕜] E) :
    ‖calkinProjection 𝕜 E T‖ = Metric.infDist T
      (compactIdeal 𝕜 E : Set (E →L[𝕜] E)) :=
  QuotientAddGroup.norm_mk T

/-- Approximate representatives prove the quotient product estimate without
assuming existence of a minimum-norm representative. -/
theorem calkin_norm_mul_le (x y : Calkin 𝕜 E) : ‖x * y‖ ≤ ‖x‖ * ‖y‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc := ((Metric.nhds_basis_ball.prod_nhds Metric.nhds_basis_ball).tendsto_iff
    Metric.nhds_basis_ball).mp (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
  simp only [Set.mem_prod, Metric.mem_ball, and_imp, Prod.forall, Prod.exists] at hc
  obtain ⟨δ₁, δ₂, ⟨hδ₁, hδ₂⟩, hbound⟩ := hc
  obtain ⟨a, rfl, ha⟩ := Submodule.Quotient.norm_mk_lt x hδ₁
  obtain ⟨b, rfl, hb⟩ := Submodule.Quotient.norm_mk_lt y hδ₂
  simp only [Real.dist_eq, abs_sub_lt_iff] at hbound
  specialize hbound ‖a‖ ‖b‖
    ⟨by linarith, by linarith [Submodule.Quotient.norm_mk_le (compactIdeal 𝕜 E) a]⟩
    ⟨by linarith, by linarith [Submodule.Quotient.norm_mk_le (compactIdeal 𝕜 E) b]⟩
  calc
    ‖(Submodule.Quotient.mk a : Calkin 𝕜 E) * Submodule.Quotient.mk b‖
        ≤ ‖a‖ * ‖b‖ :=
      (Submodule.Quotient.norm_mk_le (compactIdeal 𝕜 E) (a * b)).trans (norm_mul_le a b)
    _ ≤ _ := (sub_lt_iff_lt_add'.mp hbound.1).le

/-- The norm, metric, addition and multiplication are all the native quotient ones. -/
instance calkinNormedRing [CompleteSpace E] : NormedRing (Calkin 𝕜 E) :=
  { (inferInstance : Ring (Calkin 𝕜 E)), calkinNormedAddCommGroup with
    norm_mul_le := calkin_norm_mul_le }

instance calkinNormedAlgebra [CompleteSpace E] : NormedAlgebra 𝕜 (Calkin 𝕜 E) :=
  { (inferInstance : Algebra 𝕜 (Calkin 𝕜 E)),
    (inferInstance : NormedSpace 𝕜 (Calkin 𝕜 E)) with }
end Calkin
end ExpandedFA.Fredholm

/- Mathlib proof attribution
Adapted portion near line 158:
The approximate-representative proof of quotient norm submultiplicativity,
adapted from an ideal quotient to the operator quotient.

Upstream: Mathlib/Analysis/Normed/Group/Quotient.lean (around line 498)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Riccardo Brasca

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
