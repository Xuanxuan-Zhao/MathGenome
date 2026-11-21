import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompactConjugation
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealFormsConjugations
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CompactRealForm
import Batteries.Tactic.OpenPrivate

open scoped ComplexConjugate TensorProduct

universe u

namespace LieAlgebrasAndRepresentations.CompactRealForm

open RealForms
open Specs.LieAlgebrasAndRepresentations.CompactRealForm
open Specs.LieAlgebrasAndRepresentations.CompactConjugation
  (ConjugateMap PreservesBracket opposite)
open Specs.LieAlgebrasAndRepresentations.ChevalleyBasis (Root)
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value)
open Specs.LieAlgebrasAndRepresentations.TraceCriterion (killingForm_value)

private def toConjugation {L : Type u} [LieRing L] [LieAlgebra ℂ L]
    (τ : ConjugateMap L) (hτ : PreservesBracket τ) (hi : Function.Involutive τ) :
    Conjugation L where
  map :=
    { toFun := τ
      map_add' := map_add τ
      map_smul' := fun r x => by
        change τ ((r : ℂ) • x) = (r : ℂ) • τ x
        rw [map_smulₛₗ, Complex.conj_ofReal]
      map_lie' := fun {x y} => hτ x y }
  antilinear := map_smulₛₗ τ
  involutive := hi

open private positive_pairing from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompactConjugation

theorem compact_chevalley_real_form : compact_chevalley_real_formType.{u} := by
  intro L _ _ _ hss
  obtain ⟨H, hH⟩ := exists_maximal_toral L hss
  let : Finite (Root H) := (rootSet_finite H hH.1).to_subtype
  obtain ⟨φ, hφ⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ)
    (fun α : Root H => α.val) (fun α => α.property.1)
  have hregular : ∀ α ∈ rootSet_value H, φ α ≠ 0 := fun α hα => hφ ⟨α, hα⟩
  obtain ⟨negRoot, x, b, τ, hτ, c, hx, hbr, hbH, hbx, hbInt, hi, hτH, hτx,
    hcH, hcDiff, hcSum, hB, hneg, _, _, _⟩ :=
    CompactConjugation.construction hss H hH φ hregular
  let ω := toConjugation τ hτ hi
  obtain ⟨e, he⟩ := fixed_complexification ω
  have hpair (α : Root H) : ∃ k : ℝ, 0 < k ∧
      killingForm_value ℂ L (x α) (x (opposite negRoot α)) = (k : ℂ) :=
    positive_pairing hss hH (RealRootSpace.realization_of_maximalToral hss H hH) α
      (hx (opposite negRoot α)).1 (hbr α)
  exact ⟨H, φ, negRoot, x, b, ω, c, e, hH, hregular, hx, hbr, hpair, hbH, hbx, hbInt,
    hτH, hτx, hcH, hcDiff, hcSum, hB, hneg, he⟩

theorem compact_real_form : compact_real_formType.{u} := by
  intro L _ _ _ hss
  obtain ⟨_, _, _, _, _, ω, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hneg, _⟩ :=
    compact_chevalley_real_form hss
  exact ⟨ω, fixed_isRealForm ω, hneg⟩

end LieAlgebrasAndRepresentations.CompactRealForm
