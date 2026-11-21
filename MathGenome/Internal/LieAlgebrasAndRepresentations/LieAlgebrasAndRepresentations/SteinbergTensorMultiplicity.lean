import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SteinbergTensorMultiplicity
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.KostantMultiplicity
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightClassification
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace LieAlgebrasAndRepresentations.SteinbergTensorMultiplicity

open _root_.Specs.LieAlgebrasAndRepresentations
open _root_.Specs.LieAlgebrasAndRepresentations.SteinbergTensorMultiplicity
open _root_.Specs.LieAlgebrasAndRepresentations.FormalCharacters
open _root_.Specs.LieAlgebrasAndRepresentations.RealRootSpace
open SolvableRadical (IsSemisimple_value)
open VermaModules (Direction Regular U borel_value induced_value IsWeightCharacter)
open VermaWeightsUniversal (inducedLieRingModule inducedLieModule)
open SimpleHighestWeightQuotient (simpleQuotient_value)
open IntegrableHighestWeightQuotient (IsDominant)
open SerreRelations (positive)
open HighestWeightData (weightSpace_value)
open FiniteModuleWeights (weightWeylGroup)
open WeylDenominatorSpecs AddMonoidAlgebra
open FormalCharacters (finiteCharacter_coeff integralInclusion integralInclusion_character)
open scoped Classical DirectSum TensorProduct

open private mem_weight weightMap map_mem_weight
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FormalCharacters
open private strict_chamber_orbit_injective from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeylCharacter
open private extension_image_positive rho_in_simpleChamber
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeylDenominator
open private extension_injective from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteModuleWeights
open private direction_vector simple_equiv vector_regular
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence
open private cartan_lattice_comparison_of_realization
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightData

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) [H.IsCartanSubalgebra] (φ : Direction H)

local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ

local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

section Characters

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
  [FiniteDimensional ℂ V]

private theorem finiteCharacter_equiv
    {W : Type w} [AddCommGroup W] [Module ℂ W] [LieRingModule L W] [LieModule ℂ L W]
    [FiniteDimensional ℂ W] (e : V ≃ₗ⁅ℂ,L⁆ W) :
    finiteCharacter H V = finiteCharacter H W := by
  ext a
  let f := weightMap H e.toLieModuleHom a
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact Subtype.ext (e.injective (congrArg Subtype.val hxy))
    · intro y
      refine ⟨⟨e.symm y, map_mem_weight H e.symm.toLieModuleHom y.property⟩, ?_⟩
      apply Subtype.ext
      exact e.apply_symm_apply (y : W)
  exact congrArg (fun n : ℕ => (n : ℤ)) (LinearEquiv.ofBijective f hf).finrank_eq

private theorem finiteCharacter_directSum
    {ι : Type w} [Fintype ι] (M : ι → Type v) [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] [∀ i, LieRingModule L (M i)] [∀ i, LieModule ℂ L (M i)]
    [∀ i, FiniteDimensional ℂ (M i)] (e : (⨁ i, M i) ≃ₗ⁅ℂ,L⁆ V) :
    finiteCharacter H V = ∑ i, finiteCharacter H (M i) := by
  ext a
  let p (i : ι) := (DirectSum.lieModuleComponent ℂ ι L M i).comp e.symm.toLieModuleHom
  let f := LinearMap.pi (fun i => weightMap H (p i) a)
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply e.symm.injective
      apply DFinsupp.ext
      intro i
      exact congrArg (fun t => (t i).val) hxy
    · intro t
      let c := DirectSum.linearEquivFunOnFintype ℂ ι M
      let z := c.symm (fun i => (t i : M i))
      have hz (i : ι) : z i = (t i : M i) :=
        congrFun (c.apply_symm_apply (fun i => (t i : M i))) i
      have hza : z ∈ weightSpace_value (⨁ i, M i) H a := by
        apply (mem_weight H).mpr
        intro h
        apply DFinsupp.ext
        intro i
        rw [DirectSum.lie_module_bracket_apply, DFinsupp.smul_apply, hz]
        exact (mem_weight H).mp (t i).property h
      refine ⟨⟨e z, map_mem_weight H e.toLieModuleHom hza⟩, ?_⟩
      funext i
      apply Subtype.ext
      change (e.symm (e z)) i = (t i : M i)
      rw [e.symm_apply_apply, hz]
  have he := (LinearEquiv.ofBijective f hf).finrank_eq
  rw [Module.finrank_pi_fintype] at he
  simp only [coeff_sum, Finsupp.finsetSum_apply]
  change (Module.finrank ℂ (weightSpace_value V H a) : ℤ) =
    ∑ i, (Module.finrank ℂ (weightSpace_value (M i) H a) : ℤ)
  simpa only [Nat.cast_sum] using congrArg (fun n : ℕ => (n : ℤ)) he

end Characters

variable [FiniteDimensional ℂ L]

private def ambientAlternant (a : Module.Dual ℂ H) : GroupRing H :=
  alternant (cartanSign H) (fun w : weightWeylGroup H => w.val a)

private theorem cleared_ambient (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    [Fintype (weightWeylGroup H)] (hS : (positive H φ).Finite)
    (a : Module.Dual ℂ H) (χ : U (borel_value H φ) →ₐ[ℂ] ℂ)
    (ha : IsDominant H φ a) (hχ : IsWeightCharacter H φ a χ)
    [FiniteDimensional ℂ (simpleQuotient_value H φ χ)] :
    ambientAlternant H (cartanRho H φ hS) *
        finiteCharacter H (simpleQuotient_value H φ χ) =
      ambientAlternant H (a + cartanRho H φ hS) := by
  obtain ⟨_, _, hρ, _, hW, _, _, he⟩ := WeylCharacter.formula hss H φ hφ a χ ha hχ
  have hm (b : integralWeights H φ) :
      integralInclusion H φ (cartanAlternant H φ hW b) = ambientAlternant H b.val := by
    simp only [integralInclusion, cartanAlternant, ambientAlternant, alternant,
      finsum_eq_sum_of_fintype, map_sum, mapDomainRingHom_apply, mapDomain_single]
    rfl
  have h := congrArg (integralInclusion H φ) he
  rwa [map_mul, hm, hm, integralInclusion_character H φ _ hss] at h

private theorem shifted_dominant_orbit (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (hS : (positive H φ).Finite) (a b : {x : Module.Dual ℂ H // IsDominant H φ x})
    (w : weightWeylGroup H) :
    w.val (a.val + cartanRho H φ hS) = b.val + cartanRho H φ hS ↔ a = b ∧ w = 1 := by
  let d := RealRootSpace.realization hss H
  let _ := d.normedAddCommGroup
  let _ := d.innerProductSpace
  let _ : Fact (Realization H) := ⟨d⟩
  obtain ⟨p, hp⟩ := direction_vector d φ
  obtain ⟨s, hs⟩ := simple_equiv d φ hp
  have hreg := vector_regular d φ hp hφ
  obtain ⟨basis, _, _, _, _, _, _, _, _, _, hdom, _, _⟩ :=
    cartan_lattice_comparison_of_realization.{u,u} d p hreg s
  simp only [hs] at hdom
  let r := rootRho (realRoots H) p
  have hr : cartanRho H φ hS = d.j r := by
    have himage := extension_image_positive d φ p (fun x => (hp x).symm)
    have hf := positiveRoots_finite d.root_system.toRootAxioms p
    have hfin : hS.toFinset = hf.toFinset.image d.j := by
      ext x
      simp only [Set.Finite.mem_toFinset, Finset.mem_image]
      rw [← himage]
      rfl
    unfold cartanRho r rootRho
    rw [hfin, Finset.sum_image (extension_injective d).injOn,
      finsum_mem_eq_finite_toFinset_sum _ hf, map_smul, map_sum,
      ← IsScalarTower.algebraMap_smul ℂ (1 / 2 : ℝ)]
    congr 1
    norm_num [Complex.coe_algebraMap]
  have hshift (c : {x : Module.Dual ℂ H // IsDominant H φ x}) :
      ∃ x ∈ simpleChamber (realRoots H) p, d.j x = c.val + cartanRho H φ hS := by
    have hm : c.val ∈ d.j '' {x | x ∈ weightLattice basis ∧
        x ∈ closedSimpleChamber (realRoots H) p} := by
      rw [hdom]
      exact c.property
    obtain ⟨x, hx, hxc⟩ := hm
    refine ⟨x + r, ?_, by rw [map_add, hxc, hr]⟩
    intro α hα
    rw [inner_add_left]
    exact add_pos_of_nonneg_of_pos (hx.2 α hα)
      (rho_in_simpleChamber d.root_system hreg α hα)
  obtain ⟨x, hx, hxa⟩ := hshift a
  obtain ⟨y, hy, hyb⟩ := hshift b
  obtain ⟨_, G, hG⟩ := FiniteModuleWeights.weyl_complexification H d
  constructor
  · intro he
    obtain ⟨z, rfl⟩ := G.surjective w
    have hz : z.val x = y := extension_injective d (by rw [hG, hxa, hyb, he])
    have hy' : z.val x ∈ closedSimpleChamber (realRoots H) p := by
      rw [hz]
      exact fun α hα => (hy α hα).le
    have hzx : z.val x = x :=
      dominant_weyl_eq d.root_system hreg (fun α hα => (hx α hα).le) z hy'
    have hxy : x = y := hzx.symm.trans hz
    rw [← hxy] at hyb
    have ha : a = b := Subtype.ext (add_right_cancel (hxa.symm.trans hyb))
    have hz1 : z = 1 := strict_chamber_orbit_injective d.root_system hreg hx
      (show z.val x = (1 : rootWeylGroup (realRoots H)).val x from hzx)
    exact ⟨ha, by rw [hz1, map_one]⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem alternant_coeff_dominant (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    [Fintype (weightWeylGroup H)] (hS : (positive H φ).Finite)
    (a b : {x : Module.Dual ℂ H // IsDominant H φ x}) :
    (ambientAlternant H (a.val + cartanRho H φ hS)).coeff (b.val + cartanRho H φ hS) =
      if a = b then 1 else 0 := by
  simp only [ambientAlternant, alternant, finsum_eq_sum_of_fintype, coeff_sum,
    Finsupp.finsetSum_apply, coeff_single, Finsupp.single_apply, shifted_dominant_orbit H φ hss hφ hS]
  by_cases h : a = b
  · simp [h, Finset.sum_ite_eq', cartanSign]
  · simp [h]

/-- Steinberg's formula for the multiplicity in any finite internal simple
decomposition of the tensor product of the two prescribed simple quotients. -/
theorem formula : formula_type.{u} := by
  intro L _ _ _ hss H _ φ hφ lam mu χ ψ hlam hmu hχ hψ
  obtain ⟨fd, hS, hW, hK⟩ := KostantMultiplicity.formula hss H φ hφ lam χ hlam hχ
  let X := simpleQuotient_value H φ χ
  let Y := simpleQuotient_value H φ ψ
  let V := X ⊗[ℂ] Y
  let _ : FiniteDimensional ℂ X := fd
  let _ : FiniteDimensional ℂ Y :=
    ((HighestWeightClassification.finite_simple_iff_dominant hss H φ hφ mu ψ hψ).mpr hmu).1
  let _ := hW
  let _ := Fintype.ofFinite (weightWeylGroup H)
  have hex : ∃ (S : Set (LieSubmodule ℂ L V)) (label : S → {a // IsDominant H φ a}),
      IsDecomposition H φ S label := by
    obtain ⟨S, hF, hsum, hlabels⟩ :=
      HighestWeightClassification.finite_decomposition hss H φ hφ V
    choose a ξ ha hξ he using fun i : S => hlabels i.val i.property
    exact ⟨S, fun i => ⟨a i, ha i⟩, hF, hsum, fun i => ⟨ξ i, hξ i, he i⟩⟩
  refine ⟨hS, hW, hex, ?_⟩
  intro S label hSlabel nu η hη
  obtain ⟨hfinite, ⟨e, _⟩, hlabel⟩ := hSlabel
  let _ := hfinite.fintype
  let ρ := cartanRho H φ hS
  let F := finiteCharacter H X
  have hprod : finiteCharacter H V = F * finiteCharacter H Y := by
    have h := congrArg (integralInclusion H φ) (FormalCharacters.multiplicativity hss H φ X Y)
    rwa [map_mul, integralInclusion_character H φ V hss,
      integralInclusion_character H φ X hss, integralInclusion_character H φ Y hss] at h
  have hμC : ambientAlternant H ρ * finiteCharacter H Y = ambientAlternant H (mu + ρ) :=
    cleared_ambient H φ hss hφ hS mu ψ hmu hψ
  -- Clear the denominator on the tensor product and on each summand.
  have hsum : F * ambientAlternant H (mu + ρ) =
      ∑ i : S, ambientAlternant H ((label i).val + ρ) := by
    calc
      F * ambientAlternant H (mu + ρ) = ambientAlternant H ρ * finiteCharacter H V := by
        rw [← hμC, hprod]
        ac_rfl
      _ = ∑ i : S, ambientAlternant H ((label i).val + ρ) := by
        rw [finiteCharacter_directSum H (fun i : S => ↥i.val) e, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        obtain ⟨ξ, hξ, ⟨j⟩⟩ := hlabel i
        let _ : FiniteDimensional ℂ (simpleQuotient_value H φ ξ) :=
          Module.Finite.equiv j.toLinearEquiv
        rw [finiteCharacter_equiv H j]
        exact cleared_ambient H φ hss hφ hS (label i).val ξ (label i).property hξ
  have hcount : Nat.card {i : S // Nonempty (↥i.val ≃ₗ⁅ℂ,L⁆ simpleQuotient_value H φ η)} =
      Nat.card {i : S // label i = nu} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro i
    obtain ⟨ξ, hξ, ⟨j⟩⟩ := hlabel i
    have hclass := HighestWeightClassification.simple_quotients_equiv_iff
      hss H φ hφ (label i).val nu.val ξ η hξ hη
    constructor
    · rintro ⟨k⟩
      exact Subtype.ext (hclass.mp ⟨j.symm.trans k⟩)
    · intro hi
      obtain ⟨k⟩ := hclass.mpr (congrArg Subtype.val hi)
      exact ⟨j.trans k⟩
  calc
    (Nat.card {i : S // Nonempty (↥i.val ≃ₗ⁅ℂ,L⁆ simpleQuotient_value H φ η)} : ℤ) =
        (Nat.card {i : S // label i = nu} : ℤ) := by rw [hcount]
    _ = (∑ i : S, ambientAlternant H ((label i).val + ρ)).coeff (nu.val + ρ) := by
      have hcoeff (i : S) :
          (ambientAlternant H ((label i).val + ρ)).coeff (nu.val + ρ) =
            if label i = nu then 1 else 0 :=
        alternant_coeff_dominant H φ hss hφ hS (label i) nu
      simp only [coeff_sum, Finsupp.finsetSum_apply, hcoeff,
        Finset.sum_boole, Nat.card_eq_fintype_card]
      exact congrArg (fun n : ℕ => (n : ℤ))
        (Fintype.card_of_subtype (Finset.univ.filter (fun i : S => label i = nu))
          (fun i => by simp))
    _ = (F * ambientAlternant H (mu + ρ)).coeff (nu.val + ρ) := by rw [hsum]
    _ = signedPartitionSum H φ hS lam mu nu.val := by
      simp only [ambientAlternant, alternant, finsum_eq_sum_of_fintype, Finset.mul_sum,
        coeff_sum, Finsupp.finsetSum_apply, coeff_mul_single_apply, F, finiteCharacter_coeff,
        signedPartitionSum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      rw [(hK _).1, finsum_eq_sum_of_fintype, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      have harg :
          u.val (lam + ρ) - ((nu.val + ρ + -w.val (mu + ρ)) + ρ) =
            u.val (lam + ρ) + w.val (mu + ρ) - (nu.val + 2 • ρ) := by
        abel
      rw [harg, mul_right_comm]

/-- Every pair of dominant integral weights has the requisite simple factors
and satisfies the tensor multiplicity formula. -/
theorem formula_for_dominant : formula_for_dominant_type.{u} := by
  intro L _ _ _ hss H _ φ hφ lam mu hlam hmu
  obtain ⟨χ, hχ, _, _⟩ := HighestWeightClassification.dominant_has_simple_quotient hss H φ hφ lam hlam
  obtain ⟨ψ, hψ, _, _⟩ := HighestWeightClassification.dominant_has_simple_quotient hss H φ hφ mu hmu
  exact ⟨χ, ψ, hχ, hψ, formula hss H φ hφ lam mu χ ψ hlam hmu hχ hψ⟩

end LieAlgebrasAndRepresentations.SteinbergTensorMultiplicity
