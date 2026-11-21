import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DominanceNecessary
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealRootSpace
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootTriples
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Tactic.Choose

noncomputable section

namespace LieAlgebrasAndRepresentations.DominanceNecessary

open Specs.LieAlgebrasAndRepresentations.DominanceNecessary
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
  (inducedLieRingModule inducedLieModule)
open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)
open Specs.LieAlgebrasAndRepresentations.HighestWeightData (dominantWeights_value)

universe u v

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

private theorem isSl2Triple_of_root_vectors (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    {α : Module.Dual ℂ H} (hα : α ∈ rootSet H) {e f : L}
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α))
    (hef : ⁅e, f⁆ = (coroot_value H α : L)) :
    IsSl2Triple (coroot_value H α : L) e f := by
  have hpair : α (coroot_value H α) = (2 : ℂ) := by
    change α (killingCoroot H α) = 2
    rw [killingCoroot_pairing hss H hH, mul_div_cancel_right₀ _
      (rootForm_self_ne_zero hss H hH α hα)]
  refine ⟨?_, hef, ?_, ?_⟩
  · intro hz
    have hz' : coroot_value H α = 0 := Subtype.ext hz
    exact (two_ne_zero : (2 : ℂ) ≠ 0) (by simpa only [hz', map_zero] using hpair.symm)
  · simpa only [hpair, two_smul] using
      (mem_rootSpace H α e).mp he (coroot_value H α)
  · simpa only [LinearMap.neg_apply, hpair, neg_smul, two_smul] using
      (mem_rootSpace H (-α) f).mp hf (coroot_value H α)

private theorem dominance_of_highest_vector (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) (φ : Direction H)
    (e f : simple H φ → L)
    (htriple : ∀ i, e i ∈ rootSpace H i.val ∧ f i ∈ rootSpace H (-i.val) ∧
      e i ≠ 0 ∧ f i ≠ 0 ∧ ⁅e i, f i⁆ = (coroot_value H i.val : L))
    (V : Type v) [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [FiniteDimensional ℂ V] (lam : Module.Dual ℂ H) (x : V)
    (hx : IsHighestWeight e lam x) :
    lam ∈ dominantWeights_value (fun i : simple H φ => coroot_value H i.val) ∧
    ∀ i : simple H φ, ∃ n : ℕ, lam (coroot_value H i.val) = (n : ℂ) ∧
      (LieModule.toEnd ℂ L V (f i) ^ (n + 1)) x = 0 := by
  have hstring (i : simple H φ) :
      ∃ n : ℕ, lam (coroot_value H i.val) = (n : ℂ) ∧
        (LieModule.toEnd ℂ L V (f i) ^ (n + 1)) x = 0 := by
    obtain ⟨he, hf, _, _, hef⟩ := htriple i
    have ht := isSl2Triple_of_root_vectors hss H hH i.property.1.1 he hf hef
    have hp : ht.HasPrimitiveVectorWith x (lam (coroot_value H i.val)) :=
      ⟨hx.1, hx.2.1 (coroot_value H i.val), hx.2.2.1 i⟩
    obtain ⟨n, hn⟩ := hp.exists_nat
    exact ⟨n, hn, hp.pow_toEnd_f_eq_zero_of_eq_nat hn⟩
  exact ⟨fun i => (hstring i).imp (fun _ hn => hn.1), hstring⟩

theorem highest_weight_dominant : highest_weight_dominant_type.{u, v} := by
  intro L _ _ _ hss H _ φ _ e f htriple V _ _ _ _ _ lam x hx
  obtain ⟨hx, hweight, hpositive, hspan⟩ := hx
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  refine dominance_of_highest_vector hss H hH φ e f htriple V lam x ⟨hx, hweight, ?_, hspan⟩
  intro i
  have he : e i ∈ positive_value H φ :=
    LieSubalgebra.subset_lieSpan ⟨i.val, i.property.1.2, (htriple i).1⟩
  exact hpositive ⟨e i, he⟩

local instance {H : LieSubalgebra ℂ L} {φ : Direction H}
    {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ

local instance {H : LieSubalgebra ℂ L} {φ : Direction H}
    {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

theorem finite_simple_quotient_dominant : finite_simple_quotient_dominant_type.{u} := by
  intro L _ _ _ hss H _ φ hregular lam χ hχ hfinite
  let := hfinite
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  have hex (i : simple H φ) := exists_root_triple hss H hH i.val i.property.1.1
  choose e f he hf hne hnf hef _ _ using hex
  have hx := (LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient.simple_quotient
    hss H φ hregular lam χ hχ e
    (fun i => ⟨he i, hne i⟩)).2
  exact (dominance_of_highest_vector hss H hH φ e f
    (fun i => ⟨he i, hf i, hne i, hnf i, hef i⟩)
    (simpleQuotient_value H φ χ) lam (quotientHighestVector H φ χ) hx).1

end LieAlgebrasAndRepresentations.DominanceNecessary
