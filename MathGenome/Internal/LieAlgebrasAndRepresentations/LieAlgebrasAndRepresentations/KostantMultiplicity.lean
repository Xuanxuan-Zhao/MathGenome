import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.KostantMultiplicity
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FormalCharacters
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeylCharacter
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace LieAlgebrasAndRepresentations.KostantMultiplicity

open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.KostantMultiplicity
open Specs.LieAlgebrasAndRepresentations.FormalCharacters
open SolvableRadical (IsSemisimple_value)
open VermaModules (Direction Regular U borel_value induced_value IsWeightCharacter)
open SerreRelations (positive)
open SimpleHighestWeightQuotient (simpleQuotient_value quotientMap)
open FiniteModuleWeights (weightWeylGroup)
open VermaWeightsUniversal (inducedLieRingModule inducedLieModule)
open HighestWeightData (weightSpace_value)
open WeylDenominatorSpecs
open scoped Classical
open private finite_positive exponentSum geometricUnit geometricProductFamily
  map_weightSpace_eq from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FormalCharacters
open LieAlgebrasAndRepresentations.FormalCharacters (integralInclusion integralInclusion_character)
open private complete complete_single complete_coeff coeffLinear complete_coeff_mul_single
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeylCharacter
open private positiveRoot_mem_cone from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)

/-- The Kostant partition function on the complex Cartan dual. -/
abbrev partition :=
  @Specs.LieAlgebrasAndRepresentations.KostantMultiplicity.partition

section Partitions

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]
variable (hss : IsSemisimple_value ℂ L) (hS : (positive H φ).Finite)

private def rootUnit (a : positive H φ) : (Completion H φ)ˣ :=
  geometricUnit H φ a.val (positiveRoot_mem_cone H φ hss a) a.property.2

private def partitionSeries : Completion H φ :=
  letI := hS.fintype
  ∏ a : positive H φ, ((rootUnit H φ hss a)⁻¹).val

open HahnSeries (SummableFamily)

private theorem partitionFamily :
    ∃ F : SummableFamily (Exponent H φ) ℤ (positive H φ → ℕ),
      (∀ n, F n = HahnSeries.single (exponent H φ (-(∑ᶠ a, n a • a.val))) 1) ∧
      F.hsum = (partitionSeries H φ hss hS).val := by
  let A := positive H φ
  let _ := hS.fintype
  obtain ⟨F, hF, hs⟩ := geometricProductFamily H φ (A := A) Subtype.val
    (positiveRoot_mem_cone H φ hss) (fun a => a.property.2) Finset.univ
  let e : (A → ℕ) ≃ (∀ a ∈ (Finset.univ : Finset A), ℕ) :=
    { toFun := fun n a _ => n a
      invFun := fun n a => n a (Finset.mem_univ a)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨F.Equiv e.symm, ?_, ?_⟩
  · intro n
    rw [HahnSeries.SummableFamily.Equiv_toFun]
    change F (e n) = _
    rw [hF, finsum_eq_sum_of_fintype]
    have hsum : exponentSum H Subtype.val Finset.univ (e n) = ∑ a : A, n a • a.val :=
      (Finset.sum_subtype Finset.univ (fun _ => Iff.rfl) (fun a : A => n a • a.val)).symm
    rw [hsum]
  · rw [HahnSeries.SummableFamily.hsum_equiv, hs]
    change _ = (↑(∏ a : A, ((rootUnit H φ hss a)⁻¹).val) : Series H φ)
    rw [SubmonoidClass.coe_finsetProd]
    rfl

private theorem partitionSeries_coeff (β : Module.Dual ℂ H) :
    Finite (Decomposition H φ β) ∧
      coeff H φ (partitionSeries H φ hss hS) (-β) = (partition H φ β : ℤ) := by
  obtain ⟨F, hF, hs⟩ := partitionFamily H φ hss hS
  let D : Set (positive H φ → ℕ) := {n | (∑ᶠ a, n a • a.val) = β}
  have hc (n : positive H φ → ℕ) :
      (F n).coeff (exponent H φ (-β)) = if n ∈ D then 1 else 0 := by
    rw [hF, HahnSeries.coeff_single]
    simp [D, (exponent H φ).injective.eq_iff, eq_comm]
  have hD : D.Finite := (F.finite_co_support (exponent H φ (-β))).subset fun n hn => by
    change (F n).coeff (exponent H φ (-β)) ≠ 0
    rw [hc, ite_eq_left hn]
    exact one_ne_zero
  let _ : Fintype ↑D := hD.fintype
  change Finite ↑D ∧ _
  refine ⟨Finite.of_fintype _, ?_⟩
  change (partitionSeries H φ hss hS).val.coeff (exponent H φ (-β)) = (Nat.card ↑D : ℤ)
  rw [← hs, HahnSeries.SummableFamily.coeff_hsum_eq_sum_of_subset (t := hD.toFinset)]
  · have hcard : Fintype.card ↑D = hD.toFinset.card :=
      (Set.Finite.card_toFinset hD).symm
    simp only [Nat.card_eq_fintype_card, hcard, hc]
    rw [Finset.sum_congr rfl (fun n hn => ite_eq_left (hD.mem_toFinset.mp hn))]
    simp
  · intro n hn
    by_contra hm
    apply hn
    rw [hc, ite_eq_right (show n ∉ D from fun hd => hm (hD.mem_toFinset.mpr hd))]

omit [FiniteDimensional ℂ L] [H.IsCartanSubalgebra] in
include hS in
private theorem partition_zero : partition H φ 0 = 1 := by
  let _ := hS.fintype
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨fun _ => 0, ?_⟩, fun n => Subtype.ext (funext fun a => ?_)⟩
  · change (∑ᶠ a : positive H φ, (0 : ℕ) • a.val) = 0
    simp
  · have he : (∑ᶠ b : positive H φ, n.val b • b.val) = 0 := n.property
    rw [finsum_eq_sum_of_fintype] at he
    have hz : (∑ b : positive H φ, (n.val b : ℝ) * φ b.val) = 0 := by
      simpa only [map_sum, map_nsmul, nsmul_eq_mul, map_zero] using congrArg φ he
    have hle : (n.val a : ℝ) * φ a.val ≤ ∑ b : positive H φ, (n.val b : ℝ) * φ b.val :=
      Finset.single_le_sum (fun b _ => mul_nonneg (Nat.cast_nonneg _) b.property.2.le)
        (Finset.mem_univ a)
    rw [hz] at hle
    change n.val a = 0
    by_contra hne
    exact (not_lt_of_ge hle)
      (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hne)) a.property.2)

include hss hS in
private theorem partition_outside_cone {β : Module.Dual ℂ H} (hβ : β ∉ cone H φ) :
    partition H φ β = 0 := by
  let _ := hS.fintype
  let _ : IsEmpty (Decomposition H φ β) := ⟨fun n => hβ (by
    have hn : (∑ᶠ a : positive H φ, n.val a • a.val) = β := n.property
    rw [← hn, finsum_eq_sum_of_fintype]
    exact (cone H φ).sum_mem fun a _ =>
      (cone H φ).smul_mem (n.val a) (positiveRoot_mem_cone H φ hss a))⟩
  exact Nat.card_of_isEmpty

end Partitions

/-- Each partition fibre is finite. The empty decomposition is the unique
partition of zero, and a weight outside the positive root cone has no partitions. -/
theorem partition_properties : partitionPropertiesType.{u} := by
  intro L _ _ _ hss H _ φ _
  let hS := finite_positive H φ hss
  exact ⟨hS, fun β => (partitionSeries_coeff H φ hss hS β).1,
    partition_zero H φ hS, fun _ => partition_outside_cone H φ hss hS⟩

section GroupRing

variable [FiniteDimensional ℂ L]

private def completeCharacter : IntegralGroupRing H φ →+* Completion H φ :=
  (complete H φ).toRingHom.comp (integralInclusion H φ)

private theorem completeCharacter_single (a : integralWeights H φ) (z : ℤ) :
    completeCharacter H φ (AddMonoidAlgebra.single a z) = z • monomial H φ a.val := by
  change complete H φ (integralInclusion H φ (AddMonoidAlgebra.single a z)) = _
  rw [show integralInclusion H φ (AddMonoidAlgebra.single a z) =
    AddMonoidAlgebra.single a.val z from AddMonoidAlgebra.mapDomain_single, complete_single]

end GroupRing

section Formula

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]

omit [H.IsCartanSubalgebra] in
private theorem completeDenominator (hS : (positive H φ).Finite)
    (hρ : cartanRho H φ hS ∈ integralWeights H φ)
    (hP : ∀ a ∈ positive H φ, a ∈ integralWeights H φ) :
    letI := hS.fintype
    completeCharacter H φ (cartanDenominator H φ hS hρ hP) =
      monomial H φ (cartanRho H φ hS) *
        ∏ a : positive H φ, (1 - monomial H φ (-a.val)) := by
  let _ := hS.fintype
  simp only [cartanDenominator, denominator, map_mul, map_prod, map_sub, map_one,
    completeCharacter_single, one_zsmul]
  congr 1
  rw [← Finset.prod_subtype hS.toFinset (fun _ => Set.mem_toFinset)
    (fun a => 1 - monomial H φ (-a))]
  apply Finset.prod_congr rfl
  intro a ha
  simp only [dite_eq_left (Set.Finite.mem_toFinset hS |>.mp ha)]
  rfl

private theorem partitionSeries_cancel (hss : IsSemisimple_value ℂ L)
    (hS : (positive H φ).Finite) :
    letI := hS.fintype
    partitionSeries H φ hss hS * ∏ a : positive H φ, (1 - monomial H φ (-a.val)) = 1 := by
  let _ := hS.fintype
  change (∏ a : positive H φ, ((rootUnit H φ hss a)⁻¹).val) *
    (∏ a : positive H φ, (rootUnit H φ hss a).val) = 1
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun a _ => (rootUnit H φ hss a).inv_val

private theorem multiplicity_of_cleared (hss : IsSemisimple_value ℂ L)
    (hφ : Regular H φ) (lam : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ)
    (hχ : IsWeightCharacter H φ lam χ) (hw : WeylCharacter.ClearedFormula H φ lam χ) :
    MultiplicityFormula H φ lam χ := by
  obtain ⟨fd, hS, hρ, hP, hW, htop, hchar, _⟩ := hw
  obtain ⟨_, _, _, _, hWF, _, _⟩ := WeylDenominator.cartan_identity hss H φ hφ
  refine ⟨fd, hS, hWF, ?_⟩
  let _ := inducedLieRingModule H φ χ
  let _ := inducedLieModule H φ χ
  let _ := fd
  let _ := hS.fintype
  let _ : Fintype (weightWeylGroup H) := Fintype.ofFinite _
  let ρ := cartanRho H φ hS
  let G := partitionSeries H φ hss hS
  let V := simpleQuotient_value H φ χ
  let F := character H φ V
  let A := cartanAlternant H φ hW ⟨lam + ρ, htop⟩
  let P := ∏ a : positive H φ, (1 - monomial H φ (-a.val))
  have hG : G * P = 1 := partitionSeries_cancel H φ hss hS
  have hden : completeCharacter H φ (cartanDenominator H φ hS hρ hP) =
      monomial H φ ρ * P := completeDenominator H φ hS hρ hP
  -- Multiply the denominator-cleared identity by the partition series.
  have he : monomial H φ ρ * completeCharacter H φ F = G * completeCharacter H φ A := by
    calc
      monomial H φ ρ * completeCharacter H φ F =
          (G * P) * (monomial H φ ρ * completeCharacter H φ F) := by rw [hG, one_mul]
      _ = G * ((monomial H φ ρ * P) * completeCharacter H φ F) := by ac_rfl
      _ = G * completeCharacter H φ A := by rw [← hden, ← map_mul, hchar]
  have hA : completeCharacter H φ A =
      ∑ w : weightWeylGroup H, complete H φ
        (AddMonoidAlgebra.single (w.val (lam + ρ)) (cartanSign H w)) := by
    simp [A, cartanAlternant, alternant, finsum_eq_sum_of_fintype, completeCharacter_single,
      complete_single]
  intro μ
  have houtside (hμ : lam - μ ∉ cone H φ) : multiplicity H V μ = 0 := by
    obtain ⟨hint, _, hs, _⟩ := VermaWeightsUniversal.verma_weights hss H φ hφ lam χ hχ
    have hbot : weightSpace_value (induced_value H φ χ) H μ = ⊥ :=
      not_not.mp (fun hn => hμ ((hs μ).mp hn))
    have hm := map_weightSpace_eq H (quotientMap H φ χ)
      (LieSubmodule.Quotient.surjective_mk' _) hint μ
    rw [hbot, Submodule.map_bot] at hm
    simp [FormalCharacters.multiplicity, V, ← hm]
  refine ⟨?_, houtside⟩
  rw [finsum_eq_sum_of_fintype]
  calc
    multiplicity H V μ =
        coeff H φ (monomial H φ ρ * completeCharacter H φ F) (μ + ρ) := by
      have hshift := complete_coeff_mul_single H φ ρ (μ + ρ) 1 (completeCharacter H φ F)
      rw [complete_single, one_zsmul, one_mul, add_sub_cancel_right] at hshift
      rw [hshift]
      change multiplicity H V μ =
        coeff H φ (complete H φ (integralInclusion H φ (character H φ V))) μ
      rw [integralInclusion_character H φ V hss, complete_coeff]
      rfl
    _ = coeff H φ (G * completeCharacter H φ A) (μ + ρ) := by rw [he]
    _ = ∑ w : weightWeylGroup H, cartanSign H w *
        (partition H φ (w.val (lam + ρ) - (μ + ρ)) : ℤ) := by
      rw [hA, Finset.mul_sum]
      change coeffLinear H φ (∑ w : weightWeylGroup H, _) (μ + ρ) = _
      rw [map_sum, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro w _
      change coeff H φ (G * complete H φ _) (μ + ρ) = _
      rw [mul_comm G, complete_coeff_mul_single, ← neg_sub]
      congr 1
      exact (partitionSeries_coeff H φ hss hS _).2

end Formula

/-- The Kostant multiplicity formula for any realization of the Borel character. -/
theorem formula : Specs.LieAlgebrasAndRepresentations.KostantMultiplicity.formulaType.{u} := by
  intro L _ _ _ hss H _ φ hφ lam χ hdom hχ
  exact multiplicity_of_cleared H φ hss hφ lam χ hχ
    (LieAlgebrasAndRepresentations.WeylCharacter.formula hss H φ hφ lam χ hdom hχ)

/-- Every dominant integral weight has a Borel character and its simple
quotient satisfies the Kostant multiplicity formula. -/
theorem formula_for_dominant :
    Specs.LieAlgebrasAndRepresentations.KostantMultiplicity.formulaForDominantType.{u} := by
  intro L _ _ _ hss H _ φ hφ lam hdom
  obtain ⟨χ, hχ, hw⟩ :=
    LieAlgebrasAndRepresentations.WeylCharacter.formula_for_dominant hss H φ hφ lam hdom
  exact ⟨χ, hχ, multiplicity_of_cleared H φ hss hφ lam χ hχ hw⟩

end LieAlgebrasAndRepresentations.KostantMultiplicity
