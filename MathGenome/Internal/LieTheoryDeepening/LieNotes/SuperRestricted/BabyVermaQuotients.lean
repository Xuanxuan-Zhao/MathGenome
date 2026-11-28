import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.BabyVermaQuotients
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.BabyVermaInduction
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! Every simple reduced `sl₂`-module is a quotient of an induced baby Verma module. -/

namespace LieNotes.SuperRestricted.BabyVermaQuotients

open _root_.Specs.LieNotes.SuperRestricted.BabyVermaQuotients
open _root_.Specs.LieNotes.SuperRestricted.BabyVermaInduction
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Specs.LieNotes.SuperRestricted.ReducedEnveloping (quotientMapValue)
open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (Model E H)
open private matrix_basis_powers from MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.BabyVermaInduction

universe u w

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem exists_highest_weight
    {k : Type u} [Field k] [IsAlgClosed k] {p : ℕ} [CharP k p] [NeZero p]
    {P : restrictedPowerValue k p (Model k)} (hP : MatrixPower P)
    {χ : Model k →ₗ[k] k} (hχ : χ (E k) = 0)
    (V : Type w) [AddCommGroup V] [Module (Ambient P χ) V] [IsSimpleModule (Ambient P χ) V] :
    letI : Module k V := Module.compHom V (algebraMap k (Ambient P χ))
    ∃ (weight : k) (v : V), weight ^ p - weight = χ (H k) ^ p ∧ v ≠ 0 ∧
      generator P χ (H k) • v = weight • v ∧ generator P χ (E k) • v = 0 := by
  let A := Ambient P χ
  let : Module k V := Module.compHom V (algebraMap k A)
  let : IsScalarTower k A V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : SMulCommClass A k V := ⟨fun a c v => by
    change a • (algebraMap k A c • v) = algebraMap k A c • (a • v)
    rw [← mul_smul, ← mul_smul, Algebra.commutes c a]⟩
  have : Nontrivial V := IsSimpleModule.nontrivial A V
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨b, _, _, _⟩ := RestrictedSlTwo.basis k
  obtain ⟨B, _⟩ := ReducedPbw.reducedBasis P b χ
  have : Module.Finite k A := Module.Finite.of_basis B
  have : Module.Finite k V :=
    Module.Finite.of_surjective ((LinearMap.toSpanSingleton A V v₀).restrictScalars k)
      (IsSimpleModule.toSpanSingleton_surjective A hv₀)

  let ρ : Model k →ₗ⁅k⁆ A :=
    (quotientMapValue P χ).toLieHom.comp (UniversalEnvelopingAlgebra.ι k)
  let e := ρ (E k)
  let h := ρ (H k)
  obtain ⟨hEP, _, hHP⟩ := matrix_basis_powers hP
  have e_pow : e ^ p = 0 := by
    have he := BabyVermaInduction.generator_pow P χ (E k)
    change e ^ p = ρ (P.val (E k)) + algebraMap k A (χ (E k) ^ p) at he
    simpa [hEP, hχ, NeZero.ne p] using he
  have h_pow : h ^ p = h + algebraMap k A (χ (H k) ^ p) := by
    have hh := BabyVermaInduction.generator_pow P χ (H k)
    change h ^ p = ρ (P.val (H k)) + algebraMap k A (χ (H k) ^ p) at hh
    rwa [hHP] at hh
  have h_comm : h * e - e * h = (2 : k) • e := calc
    _ = ρ ⁅H k, E k⁆ := (ρ.map_lie _ _).symm
    _ = _ := by rw [(RestrictedSlTwo.brackets k).1, map_smul]
  have eh : e * h = h * e - (2 : k) • e :=
    eq_sub_iff_add_eq'.mpr (sub_eq_iff_eq_add.mp h_comm).symm

  let action : A →ₐ[k] Module.End k V := Algebra.lsmul k k V
  let eAction := action e
  let K := LinearMap.ker eAction
  have : Nontrivial K := by
    apply Submodule.nontrivial_iff_ne_bot.mpr
    intro hK
    have hinj := (LinearMap.ker_eq_bot.mp hK).iterate p
    have hnil : eAction ^ p = 0 := by
      change (action e) ^ p = 0
      rw [← map_pow, e_pow, map_zero]
    rw [← Module.End.coe_pow, hnil] at hinj
    exact hv₀ (hinj (by simp))
  have stable : ∀ x ∈ K, (action h) x ∈ K := by
    intro x hx
    change e • x = 0 at hx
    change e • (h • x) = 0
    rw [← mul_smul, eh, sub_smul, mul_smul, smul_assoc, hx]
    simp
  let hOnKernel : Module.End k K := (action h).restrict stable
  obtain ⟨weight, hweight⟩ := hOnKernel.exists_eigenvalue
  obtain ⟨v, hv⟩ := hweight.exists_hasEigenvector
  have hv_ne : (v : V) ≠ 0 := fun hz => hv.2 (Subtype.ext hz)
  have hv_h : h • (v : V) = weight • (v : V) :=
    congrArg (fun x : K => (x : V)) hv.apply_eq_smul
  have hv_e : e • (v : V) = 0 := v.property
  have hv_eigen : (action h).HasEigenvector weight (v : V) :=
    ⟨Module.End.mem_eigenspace_iff.mpr hv_h, hv_ne⟩
  have hscalar : weight ^ p • (v : V) = (weight + χ (H k) ^ p) • (v : V) := calc
    _ = (action h ^ p) (v : V) := (hv_eigen.pow_apply p).symm
    _ = h ^ p • (v : V) := by
      rw [← map_pow]
      rfl
    _ = _ := by rw [h_pow, add_smul, IsScalarTower.algebraMap_smul, hv_h, add_smul]
  have hroot : weight ^ p - weight = χ (H k) ^ p := by
    rw [sub_eq_iff_eq_add, add_comm]
    exact smul_left_injective k hv_ne hscalar
  exact ⟨weight, v, hroot, hv_ne, hv_h, hv_e⟩

/-- The induced family with the prescribed actions exhausts the simple modules by quotients. -/
theorem babyVermaQuotients : babyVermaQuotientsType.{u, w} := by
  intro k _ _ p _ hp
  let : NeZero p := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hp)⟩
  intro P hP χ hχ
  obtain ⟨Q, j, hQ, hj, hj_inj, hright, hweights⟩ :=
    BabyVermaInduction.babyVermaInduction.{u, w} (k := k) hp P hP χ hχ
  let Weights := {weight : k // weight ^ p - weight = χ (H k) ^ p}
  let θ (weight : Weights) := Classical.choose (hweights weight.val weight.property)
  have hθ (weight : Weights) :
      LineCharacter Q χ weight.val (θ weight) ∧ BasisAndActions j (θ weight) weight.val ∧
        InductionProperty.{u, w} j (θ weight) weight.val :=
    Classical.choose_spec (hweights weight.val weight.property)
  refine ⟨Q, j, hQ, hj, hj_inj, hright, θ, hθ, ?_⟩
  intro V _ _ _
  obtain ⟨weight, v, hroot, hv_ne, hv_h, hv_e⟩ := exists_highest_weight hP hχ V
  let root : Weights := ⟨weight, hroot⟩
  obtain ⟨f, _, hf⟩ := ((hθ root).2.2 V v hv_h hv_e).2
    (IsSimpleModule.span_singleton_eq_top (Ambient P χ) hv_ne)
  exact ⟨root, f, hf⟩

end LieNotes.SuperRestricted.BabyVermaQuotients
