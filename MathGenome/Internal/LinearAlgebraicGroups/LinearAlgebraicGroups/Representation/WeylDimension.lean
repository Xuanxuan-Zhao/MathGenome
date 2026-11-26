import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.WeylDimension
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.WeylCharacter
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.WeylDenominator
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SpecialLinearDatum
import Mathlib.RingTheory.PowerSeries.Exp
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory
open scoped BigOperators CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.WeylDimension

open _root_.LinearAlgebraicGroups.Specs
open Specs.WeylDimension
open Specs.WeylDenominator (GroupRing monomial alternant rho weylSign positiveRoots denominator)
open Specs.DominantOrder (IsBaseFor)
open Specs.CharacterDescent (Character)
open Specs.AbstractPairing (Datum Root)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.FlagLineBundle (OppositeBorelPair)
open Specs.FlagEulerCharacteristic (halfWeightDomain includeCharacters)
open Specs.FormalCharacters (formalCharacter)
open Specs.RootWeightAction (Representation)
open Specs.WeylCharacter (SatisfiesFormula)
open PowerSeries (constantCoeff coeff)

noncomputable section

open private formula exists_word from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.WeylDenominator
open private laws positive_flip eval_pos_root_strict sum_coroot_pairing
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.DominantOrder
open private internalWeights characterOfBasis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FormalCharacters
open private includeCharacters_eChar includeCharacters_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagEulerCharacteristic
open private weylAction_of_normalizer from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelPositivity

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
set_option linter.style.haveILetI false

section Specialization

private def expSeries (a : ℚ) : PowerSeries ℚ :=
  PowerSeries.rescale a (PowerSeries.exp ℚ)

@[simp] private theorem constantCoeff_expSeries (a : ℚ) : constantCoeff (expSeries a) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [expSeries]

private theorem expSeries_zero : expSeries 0 = 1 := by
  ext n
  cases n <;> simp [expSeries]

private def specialize {X : Type*} [AddCommGroup X] (f : X →+ ℚ) :
    GroupRing X →+* PowerSeries ℚ :=
  (AddMonoidAlgebra.lift ℤ (PowerSeries ℚ) X
    { toFun := fun x => expSeries (f x.toAdd)
      map_one' := by change expSeries (f 0) = 1; rw [map_zero, expSeries_zero]
      map_mul' := fun x y => by
        change expSeries (f (x.toAdd + y.toAdd)) = _
        rw [map_add]
        exact (PowerSeries.exp_mul_exp_eq_exp_add _ _).symm }).toRingHom

@[simp] private theorem specialize_monomial {X : Type*} [AddCommGroup X] (f : X →+ ℚ) (x : X) :
    specialize f (monomial x) = expSeries (f x) := by
  simp [specialize]

/-- Each denominator factor has a single explicit factor of the series variable,
with the required linear coefficient after division. -/
private theorem exp_factor (a : ℚ) :
    ∃ F : PowerSeries ℚ, 1 - expSeries (-a) = PowerSeries.X * F ∧ constantCoeff F = a := by
  obtain ⟨F, hF⟩ := PowerSeries.X_dvd_iff.mpr
    (show constantCoeff (1 - expSeries (-a)) = 0 by simp)
  refine ⟨F, hF, ?_⟩
  have h := congrArg (coeff 1) hF
  rw [show (PowerSeries.X : PowerSeries ℚ) = PowerSeries.X ^ 1 by simp,
    show (1 : ℕ) = 0 + 1 by rfl, PowerSeries.coeff_X_pow_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  simpa [expSeries] using h.symm

private theorem specialized_product {I : Type*} (s : Finset I) (a : I → ℚ) (c : ℚ) :
    ∃ F : PowerSeries ℚ,
      expSeries c * (∏ i ∈ s, (1 - expSeries (-(a i)))) = PowerSeries.X ^ s.card * F ∧
      constantCoeff F = ∏ i ∈ s, a i := by
  classical
  choose F hF hC using exp_factor
  refine ⟨expSeries c * ∏ i ∈ s, F (a i), ?_, by simp [hC]⟩
  simp only [hF, Finset.prod_mul_distrib, Finset.prod_const]
  ac_rfl

private theorem compare_specialized_products {I : Type*} (s : Finset I) (a b : I → ℚ)
    (c d : ℚ) (f : PowerSeries ℚ)
    (h : (expSeries c * (∏ i ∈ s, (1 - expSeries (-(a i))))) * f =
      expSeries d * (∏ i ∈ s, (1 - expSeries (-(b i)))))
    (ha : ∀ i ∈ s, a i ≠ 0) :
    constantCoeff f = ∏ i ∈ s, b i / a i := by
  obtain ⟨A, hA, hAc⟩ := specialized_product s a c
  obtain ⟨B, hB, hBc⟩ := specialized_product s b d
  rw [hA, hB, mul_assoc] at h
  have he := mul_left_cancel₀ (pow_ne_zero s.card PowerSeries.X_ne_zero) h
  have hc := congrArg (constantCoeff (R := ℚ)) he
  rw [map_mul, hAc, hBc] at hc
  rw [Finset.prod_div_distrib, eq_div_iff (Finset.prod_ne_zero_iff.mpr ha), mul_comm]
  exact hc

end Specialization

section DualDatum

variable {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing I ℤ X Y)

/-- Transposition exchanges the two lattices and reverses the order of composition. -/
private def transposeAut (w : P.Aut) : P.flip.Aut where
  weightMap := w.coweightEquiv
  coweightMap := w.weightEquiv
  indexEquiv := w.indexEquiv.symm
  weight_coweight_transpose := by
    ext x y
    exact (w.toLinearMap_weightEquiv x y).symm
  root_weightMap := by
    funext i
    exact RootPairing.Hom.coroot_coweightMap_apply P P i w.toHom
  coroot_coweightMap := by
    funext i
    exact RootPairing.Hom.root_weightMap_apply P P i w.toHom
  bijective_weightMap := w.coweightEquiv.bijective
  bijective_coweightMap := w.weightEquiv.bijective

private theorem transposeAut_one : transposeAut P 1 = 1 := by
  apply RootPairing.Equiv.weightHom_injective P.flip
  rfl

private theorem transposeAut_mul (w v : P.Aut) :
    transposeAut P (w * v) = transposeAut P v * transposeAut P w := by
  apply RootPairing.Equiv.weightHom_injective P.flip
  rfl

private theorem transposeAut_reflection (i : I) :
    transposeAut P (RootPairing.Equiv.reflection P i) =
      RootPairing.Equiv.reflection P.flip i := by
  apply RootPairing.Equiv.weightHom_injective P.flip
  rfl

private theorem transposeAut_mem {w : P.Aut} (h : w ∈ P.weylGroup) :
    transposeAut P w ∈ P.flip.weylGroup := by
  induction h using RootPairing.weylGroup.induction P with
  | mem i => rw [transposeAut_reflection]; exact P.flip.reflection_mem_weylGroup i
  | one => rw [transposeAut_one]; exact one_mem _
  | mul w v hw hv ihw ihv =>
    rw [transposeAut_mul]
    exact mul_mem ihv ihw

private def transposeWeyl : P.weylGroup ≃ P.flip.weylGroup where
  toFun w := ⟨transposeAut P w.val, transposeAut_mem P w.property⟩
  invFun w := ⟨transposeAut P.flip w.val, transposeAut_mem P.flip w.property⟩
  left_inv w := by
    apply Subtype.ext
    apply RootPairing.Equiv.weightHom_injective P
    rfl
  right_inv w := by
    apply Subtype.ext
    apply RootPairing.Equiv.weightHom_injective P.flip
    rfl

private theorem transposeWeyl_mul (w v : P.weylGroup) :
    transposeWeyl P (w * v) = transposeWeyl P v * transposeWeyl P w :=
  Subtype.ext (transposeAut_mul P w.val v.val)

private theorem transposeWeyl_reflection (i : I) :
    transposeWeyl P (RootPairing.weylGroup.ofIdx P i) =
      RootPairing.weylGroup.ofIdx P.flip i :=
  Subtype.ext (transposeAut_reflection P i)

private theorem transposeWeyl_permutation (w : P.weylGroup) :
    P.flip.weylGroupToPerm (transposeWeyl P w) = (P.weylGroupToPerm w).symm := rfl

private theorem transposeWeyl_stabilizer (S : Set I)
    (h : ∀ w : P.weylGroup, P.weylGroupToPerm w '' S = S → w = 1)
    (w : P.flip.weylGroup) (hw : P.flip.weylGroupToPerm w '' S = S) : w = 1 := by
  obtain ⟨v, rfl⟩ := (transposeWeyl P).surjective w
  rw [transposeWeyl_permutation, Equiv.image_symm_eq_preimage] at hw
  have hv : P.weylGroupToPerm v '' S = S := by
    nth_rw 1 [← hw]
    exact Set.image_preimage_eq _ (P.weylGroupToPerm v).surjective
  rw [h v hv]
  exact Subtype.ext (transposeAut_one P)

variable [Finite I] [P.IsReduced] [Finite P.weylGroup] [Finite P.flip.weylGroup]
    {S : Set I} {b : P.Base}

private theorem transposeWeyl_sign (h : Specs.WeylDenominator.Laws P S b)
    (h' : Specs.WeylDenominator.Laws P.flip S b.flip) (w : P.weylGroup) :
    weylSign P.flip b.flip (transposeWeyl P w) = weylSign P b w := by
  obtain ⟨word, rfl⟩ := exists_word P b w
  induction word with
  | nil =>
    change weylSign P.flip b.flip (transposeWeyl P 1) = weylSign P b 1
    rw [show transposeWeyl P 1 = 1 from Subtype.ext (transposeAut_one P), h.sign_one, h'.sign_one]
  | cons i word ih =>
    change weylSign P.flip b.flip
      (transposeWeyl P (RootPairing.weylGroup.ofIdx P i.val *
        Specs.WeylDenominator.wordProduct P b word)) = _
    rw [transposeWeyl_mul, transposeWeyl_reflection, h'.sign_mul, ih,
      h'.sign_simple _ i.property]
    change _ = weylSign P b (RootPairing.weylGroup.ofIdx P i.val *
      Specs.WeylDenominator.wordProduct P b word)
    rw [h.sign_mul, h.sign_simple _ i.property, mul_comm]

/-- In doubled coordinates this specializes a half-weight along an integral
cocharacter. The same definition on the dual datum reverses the two entries. -/
private def evaluatePair (y : Y) : X →+ ℚ where
  toFun x := (P.toLinearMap x y : ℚ) / 2
  map_zero' := by simp
  map_add' x z := by
    simp only [map_add, LinearMap.add_apply, Int.cast_add, add_div]

omit [Finite I] [P.IsReduced] [Finite P.weylGroup] [Finite P.flip.weylGroup] in
@[simp] private theorem evaluatePair_doubled (x : X) (y : Y) :
    evaluatePair P y (2 • x) = (P.toLinearMap x y : ℚ) := by
  change (P.toLinearMap (2 • x) y : ℚ) / 2 = _
  simp [two_nsmul, add_div]

private theorem specialize_alternant_swap (h : Specs.WeylDenominator.Laws P S b)
    (h' : Specs.WeylDenominator.Laws P.flip S b.flip) (x : X) (y : Y) :
    specialize (evaluatePair P y) (alternant P b x) =
      specialize (evaluatePair P.flip x) (alternant P.flip b.flip y) := by
  classical
  let := Fintype.ofFinite P.weylGroup
  let := Fintype.ofFinite P.flip.weylGroup
  simp only [alternant, map_sum, map_zsmul, specialize_monomial]
  rw [← Equiv.sum_comp (transposeWeyl P)]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [transposeWeyl_sign P h h']
  congr 2
  change (P.toLinearMap (w.val.weightEquiv x) y : ℚ) / 2 =
    (P.toLinearMap x (w.val.coweightEquiv y) : ℚ) / 2
  rw [w.val.toLinearMap_weightEquiv]

omit [P.IsReduced] [Finite P.weylGroup] [Finite P.flip.weylGroup] in
private theorem specialize_denominator (y : Y) :
    specialize (evaluatePair P y) (monomial (rho P S) * denominator P S) =
      expSeries (evaluatePair P y (rho P S)) *
        ∏ i ∈ positiveRoots S, (1 - expSeries (-(P.toLinearMap (P.root i) y : ℚ))) := by
  simp [denominator, map_prod]

variable [P.flip.IsReduced] [Module.IsTorsionFree ℤ X] [Module.IsTorsionFree ℤ Y]

/-- Evaluate a Weyl quotient by specializing along the sum of the positive
coroots. Transposition turns the numerator into the dual Weyl denominator. -/
private theorem constantCoeff_of_weyl_quotient
    (hb : IsBaseFor P S b)
    (hfree : ∀ w : P.weylGroup, P.weylGroupToPerm w '' S = S → w = 1)
    (x : X) (F : GroupRing X)
    (hF : alternant P b (rho P S) * F = alternant P b x) :
    constantCoeff (specialize (evaluatePair P (rho P.flip S)) F) =
      ∏ i ∈ positiveRoots S,
        (P.toLinearMap x (P.coroot i) : ℚ) /
          (P.toLinearMap (rho P S) (P.coroot i) : ℚ) := by
  have hb' : IsBaseFor P.flip S b.flip :=
    fun i ↦ (positive_flip P b i).trans (hb i)
  have h := formula P hb (laws P S b hb hfree)
  have h' := formula P.flip hb' (laws P.flip S b.flip hb'
    (transposeWeyl_stabilizer P S hfree))
  let r := rho P S
  let y := rho P.flip S
  have hr : r = DominantOrder.twoRhoCoroot P.flip S := rfl
  have hregular (i : I) (hi : i ∈ positiveRoots S) :
      (P.toLinearMap r (P.coroot i) : ℚ) ≠ 0 := by
    have hpos := (eval_pos_root_strict P.flip b.flip (P.toLinearMap r)
      (fun j hj ↦ by
        change 0 < P.flip.toLinearMap (P.flip.root j) r
        rw [hr, sum_coroot_pairing P.flip b.flip hb' hj]
        decide) i).2 ((hb' i).2 (by simpa [positiveRoots] using hi))
    exact_mod_cast hpos.ne'
  have he := congrArg (specialize (evaluatePair P y)) hF
  rw [map_mul, specialize_alternant_swap P h h' (rho P S) y,
    specialize_alternant_swap P h h' x y, h'.identity,
    specialize_denominator, specialize_denominator] at he
  exact compare_specialized_products (positiveRoots S)
    (fun i ↦ (P.toLinearMap r (P.coroot i) : ℚ))
    (fun i ↦ (P.toLinearMap x (P.coroot i) : ℚ)) _ _
    (specialize (evaluatePair P y) F) he hregular


end DualDatum

section Representations

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (P : OppositeBorelPair G)

private theorem specialize_character_dimension {I : Type u} [Fintype I] [DecidableEq I]
    (V : Representation G.val I) (f : Additive (Character P.torus.group) →+ ℚ) :
    constantCoeff (specialize f (includeCharacters P.torus.group (formalCharacter P.torus V))) =
      (Module.finrank k (I → k) : ℚ) := by
  classical
  let internal := internalWeights P.torus P.split V
  let b := internal.collectedBasis (fun χ ↦ Module.finBasis k (Specs.RootWeightAction.weightSpace V P.torus χ))
  letI := Module.Finite.finite_basis b
  letI := Fintype.ofFinite (Σ χ : Character P.torus.group,
    Fin (Module.finrank k (Specs.RootWeightAction.weightSpace V P.torus χ)))
  have hw (i : _) : b i ∈ Specs.RootWeightAction.weightSpace V P.torus i.1 :=
    internal.collectedBasis_mem _ i
  rw [characterOfBasis P.torus P.split V b Sigma.fst hw, map_sum, map_sum, map_sum,
    Module.finrank_eq_card_basis b]
  change (∑ i, constantCoeff (specialize f (includeCharacters P.torus.group
    (Specs.EquivariantAffineModules.eChar (Sigma.fst i))))) = _
  simp only [includeCharacters_eChar, specialize_monomial, constantCoeff_expSeries,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

variable [IsCommMonObj P.torus.group.X]
    {D : Datum P.torus}
    [Finite (Root P.torus)] [Finite D.rootDatum.weylGroup]
    {b : D.rootDatum.Base}

omit [Finite (Root P.torus)] [Finite D.rootDatum.weylGroup] in
private theorem stabilizer_positive_roots (e : DatumAndWeyl.Identification D) (w : D.rootDatum.weylGroup)
    (hw : D.rootDatum.weylGroupToPerm w '' subgroupRoots P.torus P.positive =
      subgroupRoots P.torus P.positive) : w = 1 := by
  have action := weylAction_of_normalizer RootData.BorelNormalizer.weylSimplyTransitiveOnPositiveSystems
    P.reductive P.split P.maximal e
  obtain ⟨_, _, _, hBorel, _, _, _⟩ :=
    RootData.BorelPositivity.borelPositivity G P.reductive P.torus P.split P.maximal
  have hpos := hBorel.1 P.positive P.positiveBorel P.inPositive
  obtain ⟨_, _, huniq⟩ := action.2.2 _ _ hpos hpos
  exact (huniq w hw).trans (huniq 1 (by simp)).symm

private theorem cross_mul_formula (χ : Character P.torus.group)
    (c : Specs.EquivariantAffineModules.CharacterRing P.torus.group)
    (h : SatisfiesFormula D b χ c) :
    alternant D.rootDatum b (rho D.rootDatum (subgroupRoots P.torus P.positive)) *
      includeCharacters P.torus.group c =
    alternant D.rootDatum b (2 • Additive.ofMul χ +
      rho D.rootDatum (subgroupRoots P.torus P.positive)) := by
  letI := D.freeCharacters
  letI := halfWeightDomain P.torus.group
  let A := GroupRing (Additive (Character P.torus.group))
  apply IsFractionRing.injective A (FractionRing A)
  rw [map_mul, mul_comm]
  exact (eq_div_iff h.1).mp h.2

private theorem dimension_of_formula (e : DatumAndWeyl.Identification D)
    (hb : IsBaseFor D.rootDatum (subgroupRoots P.torus P.positive) b)
    (χ : Character P.torus.group) {I : Type u} [Fintype I] [DecidableEq I]
    (V : Representation G.val I)
    (h : SatisfiesFormula D b χ (formalCharacter P.torus V)) :
    (Module.finrank k (I → k) : ℚ) = dimensionProduct D χ := by
  letI := D.reduced
  letI := D.reducedCoroots
  letI := D.freeCharacters
  letI := D.freeCocharacters
  letI : Finite D.rootDatum.flip.weylGroup :=
    Finite.of_equiv _ (transposeWeyl D.rootDatum)
  have hdim := constantCoeff_of_weyl_quotient D.rootDatum hb
    (stabilizer_positive_roots P e) _ _
    (cross_mul_formula P χ (formalCharacter P.torus V) h)
  rw [specialize_character_dimension] at hdim
  exact hdim

/-- The Weyl formula for both highest-weight modules, and for the simple
socle in the cases where it is the induced module. -/
theorem weylDimension : Statement.{u} := by
  intro k _ G P U hU
  obtain ⟨comm, D, e, hRoots, hW, b, w₀, hb, hw, hh⟩ :=
    WeylCharacter.weylCharacter G P U hU
  letI := comm
  letI := hRoots
  letI := hW
  refine ⟨comm, D, e, hRoots, hW, b, w₀, hb, hw, ?_⟩
  intro χ hχ
  obtain ⟨hχ', hExists, h⟩ := hh χ hχ
  refine ⟨hχ', hExists, ?_⟩
  intro V
  obtain ⟨hV, hWeyl, hSimple, hZero⟩ := h V
  refine ⟨hV, dimension_of_formula P e hb χ V.inducedAction hV, ?_, ?_, ?_⟩
  · intro S' Δ hΔ
    have hChar := hWeyl S' Δ hΔ
    exact ⟨hChar, dimension_of_formula P e hb χ Δ (hChar.symm ▸ hV)⟩
  · intro hs
    exact ⟨hSimple hs, dimension_of_formula P e hb χ V.socleAction (hSimple hs)⟩
  · intro hz
    exact ⟨hZero hz, dimension_of_formula P e hb χ V.socleAction (hZero hz)⟩

end Representations

section RankOne

variable {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing I ℤ X Y) [Finite I] [Finite P.weylGroup] [P.IsReduced]
    {S : Set I} {b : P.Base} {a : I}

omit [Finite I] [Finite P.weylGroup] [P.IsReduced] in
private theorem rankOne_pairing (l : X ≃ₗ[ℤ] ℤ) (ha : l (P.root a) = 2) (z : X) :
    P.toLinearMap z (P.coroot a) = l z := by
  have hz (v : X) : (l v) • l.symm 1 = v := by
    apply l.injective
    simp
  have hroot : (2 : ℤ) • l.symm 1 = P.root a := by simpa only [ha] using hz (P.root a)
  have htwo := P.root_coroot_two a
  rw [← hroot, map_smul, LinearMap.smul_apply, zsmul_eq_mul] at htwo
  norm_num at htwo
  have hunit : P.toLinearMap (l.symm 1) (P.coroot a) = 1 := by omega
  calc
    _ = P.toLinearMap ((l z) • l.symm 1) (P.coroot a) := by rw [hz]
    _ = _ := by simp [hunit]

omit [Finite I] [Finite P.weylGroup] [P.IsReduced] in
private theorem rankOne_reflection (l : X ≃ₗ[ℤ] ℤ) (ha : l (P.root a) = 2) (z : X) :
    P.reflection a z = -z := by
  apply l.injective
  rw [P.reflection_apply]
  change l (z - P.toLinearMap z (P.coroot a) • P.root a) = l (-z)
  rw [rankOne_pairing P l ha, map_sub, map_smul, map_neg, ha, zsmul_eq_mul, Int.cast_id]
  ring

private theorem rankOne_alternant (hb : IsBaseFor P S b)
    (hS : ∀ i, i ∈ S ↔ i = a)
    (h : Specs.WeylDenominator.Laws P S b)
    (l : X ≃ₗ[ℤ] ℤ) (ha : l (P.root a) = 2) (z : X) :
    alternant P b z = monomial z - monomial (-z) := by
  classical
  letI := Fintype.ofFinite P.weylGroup
  letI : Nonempty I := ⟨a⟩
  have hsimple (i : I) (hi : i ∈ b.support) : i = a :=
    (hS i).1 ((hb i).1 (b.isPos_of_mem_support hi))
  obtain ⟨i, hi⟩ := b.support_nonempty
  have has : a ∈ b.support := hsimple i hi ▸ hi
  let s := RootPairing.weylGroup.ofIdx P a
  have hs : s * s = 1 := by
    apply Subtype.ext
    change RootPairing.Equiv.reflection P a * RootPairing.Equiv.reflection P a = 1
    rw [mul_eq_one_iff_inv_eq, RootPairing.Equiv.reflection_inv]
  have hsne : (1 : P.weylGroup) ≠ s := by
    intro he
    have hv := congrArg (fun w : P.weylGroup ↦ w.val.weightEquiv (P.root a)) he
    change P.root a = P.reflection a (P.root a) at hv
    rw [rankOne_reflection P l ha] at hv
    have hv' := congrArg l hv
    rw [map_neg, ha] at hv'
    omega
  have hex (w : P.weylGroup) : w = 1 ∨ w = s := by
    obtain ⟨word, rfl⟩ := exists_word P b w
    induction word with
    | nil => exact Or.inl rfl
    | cons j word ih =>
      change RootPairing.weylGroup.ofIdx P j.val * Specs.WeylDenominator.wordProduct P b word = 1 ∨
        RootPairing.weylGroup.ofIdx P j.val * Specs.WeylDenominator.wordProduct P b word = s
      rw [hsimple j.val j.property]
      change s * _ = 1 ∨ s * _ = s
      rcases ih with hh | hh
      · exact Or.inr (by rw [hh, mul_one])
      · exact Or.inl (by rw [hh, hs])
  have hUniv : (Finset.univ : Finset P.weylGroup) = {1, s} := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hex w
  change (∑ w : P.weylGroup, weylSign P b w • monomial (w.val.weightEquiv z)) = _
  rw [hUniv, Finset.sum_pair hsne, h.sign_one, h.sign_simple _ has, one_smul, neg_one_zsmul]
  change monomial z + -monomial (P.reflection a z) = _
  rw [rankOne_reflection P l ha, sub_eq_add_neg]

omit P [Finite I] [Finite P.weylGroup] [P.IsReduced] in
private theorem rankOne_geometric_sum (l : X ≃ₗ[ℤ] ℤ) (m : ℕ) :
    (monomial (l.symm 2) - monomial (l.symm (-2))) *
      (∑ i ∈ Finset.range (m + 1), monomial (l.symm (2 * ((m : ℤ) - 2 * (i : ℤ))))) =
      monomial (l.symm (2 * ((m : ℤ) + 1))) -
        monomial (l.symm (-(2 * ((m : ℤ) + 1)))) := by
  let f (i : ℕ) : GroupRing X := monomial (l.symm (2 * ((m : ℤ) + 1 - 2 * (i : ℤ))))
  rw [Finset.mul_sum]
  calc
    _ = ∑ i ∈ Finset.range (m + 1), (f i - f (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [sub_mul, AddMonoidAlgebra.single_mul_single, mul_one, ← map_add, f]
      congr 3 <;> push_cast <;> ring
    _ = _ := by
      rw [Finset.sum_range_sub']
      simp only [f, Nat.cast_zero, mul_zero, sub_zero, Nat.cast_add, Nat.cast_one]
      congr 3
      ring

end RankOne

section SpecialLinear

open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.InducedNonvanishing (Dominant)
open Specs.SpecialLinearDatum
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.EquivariantAffineModules (eChar)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {s : SpecialMatrixPoints G 2} {T : DiagonalTorus s}
    {L : LatticeIdentification T} {M : RootIdentification T L}
    (B : UpperTriangularBorel T L M)

private def matrixPositiveIndex : RootIndices 2 := ⟨(0, 1), by decide⟩

private theorem matrixPositiveRoot (i : Root T.subgroup) :
    i ∈ subgroupRoots T.subgroup B.limits.parabolic ↔ i = M.indices matrixPositiveIndex := by
  obtain ⟨p, rfl⟩ := M.indices.surjective i
  rw [B.positive_iff, M.indices.apply_eq_iff_eq]
  constructor
  · intro hp
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> simp [matrixPositiveIndex] <;> omega
  · rintro rfl
    decide

private theorem exists_matrix_opposite :
    ∃ (Q : MatrixOpposite B) (U : ClosedSubgroup Q.pair.positive.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup Q.pair.positive) U := by
  obtain ⟨comm, _, _, hBorel, _, _, hRadical⟩ :=
    RootData.BorelPositivity.borelPositivity G B.reductive T.subgroup T.split B.maximal
  letI := comm
  let S := subgroupRoots T.subgroup B.limits.parabolic
  obtain ⟨f, hf, he⟩ := hBorel.1 B.limits.parabolic B.isBorel B.containsTorus
  have hS : Specs.BorelsAndChambers.IsPositiveSystem T.subgroup Sᶜ := by
    refine ⟨-f, fun a ↦ neg_ne_zero.mpr (hf a), ?_⟩
    rw [show S = _ from he]
    ext a
    change (¬ 0 < f (Additive.ofMul a.val)) ↔ 0 < -f (Additive.ofMul a.val)
    exact ⟨fun hn ↦ neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hn) (hf a)),
      fun hp hpos ↦ (not_lt_of_ge (neg_pos.mp hp).le) hpos⟩
  obtain ⟨N, hN, hNT, hroots⟩ := hBorel.2.1 Sᶜ hS
  let Q : MatrixOpposite B := ⟨N, hN, hNT, hroots⟩
  obtain ⟨U, _, _, hU, _⟩ := hRadical B.limits.parabolic B.isBorel B.containsTorus
  exact ⟨Q, U, hU⟩

private theorem coordinate_power (l : Additive (Character T.subgroup.group) ≃ₗ[ℤ] ℤ)
    {x : Character T.subgroup.group} (h : l (Additive.ofMul x) = 1) (m : ℤ) :
    l (Additive.ofMul (x ^ m)) = m := by
  change l (m • Additive.ofMul x) = m
  simp [h]

private theorem matrix_dominant (Q : MatrixOpposite B) (E : Specs.Pinning.AttachedDatum B.pair)
    (hE : IsMatrixBasedDatum B E)
    (l₀ : CharacterLattice 2 ≃ₗ[ℤ] ℤ) (y : CocharacterLattice 2 ≃ₗ[ℤ] ℤ)
    (hgen : l₀ ((Submodule.span ℤ ({(1 : Fin 2 → ℤ)} : Set (Fin 2 → ℤ))).mkQ
      (coordinate 2 0)) = 1)
    (hy : y (coroot 2 0 1) = 1)
    (hpair : ∀ a b, dotPairing 2 a b = l₀ a * y b) (m : ℕ) :
    Dominant Q.pair (firstDiagonalCharacter L ^ m) := by
  letI := E.comm
  apply (InducedNonvanishing.dominant_iff_datum
    Classification.CentralIsogenies.centralIsogenyComparison Q.pair E.datum _).2
  intro α
  let a := M.indices matrixPositiveIndex
  have hα : α.val = a := (matrixPositiveRoot B _).1 α.property.1
  change 0 ≤ E.datum.rootDatum.toLinearMap
    (Additive.ofMul (firstDiagonalCharacter L ^ m)) (E.datum.rootDatum.coroot α.val)
  rw [hα]
  have hp := E.datum.pairing_eq (firstDiagonalCharacter L ^ m)
    (Additive.toMul (E.datum.rootDatum.coroot a))
  change E.datum.rootDatum.toLinearMap (Additive.ofMul (firstDiagonalCharacter L ^ m))
    (E.datum.rootDatum.coroot a) = Specs.CharacterPairing.pairing T.subgroup.group
      (firstDiagonalCharacter L ^ m) (Additive.toMul (E.datum.rootDatum.coroot a)) at hp
  rw [hp, L.pairing_eq, hpair]
  change 0 ≤ l₀ (L.characters (Additive.ofMul (firstDiagonalCharacter L ^ m))) *
    y (L.cocharacters (E.datum.rootDatum.coroot a))
  rw [show L.cocharacters (E.datum.rootDatum.coroot a) = coroot 2 0 1 from
    hE.1 matrixPositiveIndex, hy, mul_one]
  let l := L.characters.trans l₀
  have hl : l (Additive.ofMul (firstDiagonalCharacter L)) = 1 := by
    simpa [l, firstDiagonalCharacter] using hgen
  change 0 ≤ l (Additive.ofMul (firstDiagonalCharacter L ^ (m : ℤ)))
  rw [coordinate_power l hl]
  positivity

private theorem matrix_character_and_dimension (Q : MatrixOpposite B)
    [IsCommMonObj T.subgroup.group.X] (D : Datum T.subgroup)
    (e : DatumAndWeyl.Identification D) [Finite (Root T.subgroup)]
    [Finite D.rootDatum.weylGroup] (b : D.rootDatum.Base)
    (hb : IsBaseFor D.rootDatum (subgroupRoots T.subgroup B.limits.parabolic) b)
    (l₀ : CharacterLattice 2 ≃ₗ[ℤ] ℤ)
    (hgen : l₀ ((Submodule.span ℤ ({(1 : Fin 2 → ℤ)} : Set (Fin 2 → ℤ))).mkQ
      (coordinate 2 0)) = 1)
    (hroot : l₀ (root 2 0 1) = 2) (m : ℕ)
    {I : Type u} [Fintype I] [DecidableEq I] (V : Representation G.val I)
    (hV : SatisfiesFormula (P := Q.pair) D b (firstDiagonalCharacter L ^ m)
      (formalCharacter T.subgroup V)) :
    formalCharacter T.subgroup V =
      ∑ i ∈ Finset.range (m + 1),
        eChar (firstDiagonalCharacter L ^ ((m : ℤ) - 2 * (i : ℤ))) ∧
    Module.finrank k (I → k) = m + 1 := by
  classical
  letI := D.reduced
  letI := D.reducedCoroots
  letI := D.freeCharacters
  letI := D.freeCocharacters
  letI := halfWeightDomain T.subgroup.group
  let P := D.rootDatum
  let S := subgroupRoots T.subgroup B.limits.parabolic
  let a := M.indices matrixPositiveIndex
  let l := L.characters.trans l₀
  let x := firstDiagonalCharacter L
  have hx : l (Additive.ofMul x) = 1 := by simpa [l, x, firstDiagonalCharacter] using hgen
  have ha : l (P.root a) = 2 := by
    change l (D.rootDatum.root (M.indices matrixPositiveIndex)) = 2
    rw [D.root_eq]
    change l₀ (L.characters (Additive.ofMul (M.indices matrixPositiveIndex).val)) = 2
    rw [M.character_eq]
    exact hroot
  have ht : positiveRoots S = {a} := by
    ext i
    simpa [positiveRoots, a, S] using matrixPositiveRoot B i
  have hr : rho P S = P.root a := by simp [rho, ht]
  have hr' : rho P S = l.symm 2 := l.toEquiv.eq_symm_apply.mpr (hr ▸ ha)
  have hpowers (n : ℤ) : (2 : ℕ) • Additive.ofMul (x ^ n) = l.symm (2 * n) := by
    apply l.injective
    change l.toLinearMap ((2 : ℤ) • Additive.ofMul (x ^ n)) = l (l.symm (2 * n))
    rw [LinearMap.map_smul]
    change (2 : ℤ) • l (Additive.ofMul (x ^ n)) = _
    rw [coordinate_power l hx, LinearEquiv.apply_symm_apply, zsmul_eq_mul, Int.cast_id]
  have hν : 2 • Additive.ofMul (x ^ m) + rho P S = l.symm (2 * ((m : ℤ) + 1)) := by
    rw [← zpow_natCast, hpowers, hr', ← map_add]
    congr 1
  have hLaws := formula P hb (laws P S b hb (stabilizer_positive_roots Q.pair e))
  have hAlt := rankOne_alternant P hb (matrixPositiveRoot B) hLaws l ha
  have hF := cross_mul_formula Q.pair (x ^ m) (formalCharacter T.subgroup V) hV
  have hNZ : alternant P b (rho P S) ≠ 0 := by
    intro h
    exact hV.1 (by rw [show alternant D.rootDatum b
      (rho D.rootDatum (subgroupRoots Q.pair.torus Q.pair.positive)) = 0 from h, map_zero])
  constructor
  · apply includeCharacters_injective T.subgroup.group
    apply mul_left_cancel₀ hNZ
    rw [hF, map_sum, hAlt (rho P S), hAlt (2 • Additive.ofMul (x ^ m) + rho P S), hν, hr']
    change _ = (monomial (l.symm 2) - monomial (-l.symm 2)) *
      ∑ i ∈ Finset.range (m + 1), includeCharacters T.subgroup.group
        (eChar (x ^ ((m : ℤ) - 2 * (i : ℤ))))
    simp only [includeCharacters_eChar, hpowers, ← map_neg]
    exact (rankOne_geometric_sum l m).symm
  · have hd := dimension_of_formula Q.pair e hb (x ^ m) V hV
    change (Module.finrank k (I → k) : ℚ) =
      ∏ i ∈ positiveRoots S, (P.toLinearMap (2 • Additive.ofMul (x ^ m) + rho P S)
        (P.coroot i) : ℚ) / (P.toLinearMap (rho P S) (P.coroot i) : ℚ) at hd
    rw [ht, Finset.prod_singleton, rankOne_pairing P l ha, rankOne_pairing P l ha,
      hν, hr', l.apply_symm_apply, l.apply_symm_apply] at hd
    push_cast at hd
    have he : (Module.finrank k (I → k) : ℚ) = (m : ℚ) + 1 := by linarith
    exact_mod_cast he

/-- The formula on the actual determinant-one group with its upper triangular
Borel and the first diagonal-entry character. -/
theorem specialLinearRankOne : SpecialLinearRankOne.{u} := by
  intro k _ G s
  obtain ⟨T, L, M, B, E, hE, _, _⟩ := RootData.SpecialLinearDatum.matrixPinnedDatum k 1 G s
  obtain ⟨Q, U, hU⟩ := exists_matrix_opposite B
  obtain ⟨l₀, y, hgen, hy, hroot, hpair⟩ := RootData.SpecialLinearDatum.sizeTwoLattices
  obtain ⟨comm, D, e, hRoots, hW, b, _, hb, _, h⟩ := WeylCharacter.weylCharacter G Q.pair U hU
  letI := comm
  letI := hRoots
  letI := hW
  refine ⟨T, L, M, B, Q, U, hU, ?_⟩
  intro m
  dsimp only
  have hd := matrix_dominant B Q E hE l₀ y hgen hy hpair m
  obtain ⟨_, ⟨V, _, _, _⟩, hf⟩ := h _ hd
  refine ⟨hd, ⟨V⟩, fun W ↦ ?_⟩
  exact matrix_character_and_dimension B Q D e b hb l₀ hgen hroot m W.inducedAction (hf W).1

end SpecialLinear

end

end LinearAlgebraicGroups.Representation.WeylDimension
