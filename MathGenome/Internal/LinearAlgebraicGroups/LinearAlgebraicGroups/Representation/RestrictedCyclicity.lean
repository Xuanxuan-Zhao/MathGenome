import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.RestrictedCyclicity
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SimpleClassification
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FiniteDistributions
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.BruhatCells
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelPositivity
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic.Group
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Representation.RestrictedCyclicity

open _root_.LinearAlgebraicGroups.Specs
open Specs.RestrictedCyclicity
open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character)
open CharacterPairing (characterValue pairing)
open RootGroups (AdditiveLine CorootReflection rankOneWord rootPoint)
open RootWeightAction (Representation act extendVector fixedSpace weightSpace
  mem_fixedSpace mem_weightSpace)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

open private act_mul act_one act_smul act_extend_natural
  rootPoint_natural rootPoint_zero characterValue_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.RootWeightAction
open private additivePoints_add characterValue_eq_unit characterEvaluation characterUnit
  characterUnit_cocharacter from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
variable {G : AffineAlgebraicGroup k}

local notation "K" => CommAlgCat.of k k

omit [Fintype I] [DecidableEq I] in
private theorem extend_ground (v : I → k) : extendVector K v = v := rfl

private theorem orbitPolynomial_eval {H : GroupScheme k} (ρ : Representation H I)
    {A : AdditiveLine k} (x : A.group ⟶ H) (v : I → k)
    (R : TestAlgebra k) (c : R) :
    act ρ R (rootPoint x R c) (extendVector R v) =
      fun i ↦ Polynomial.aeval c (orbitPolynomial ρ x v i) := by
  let P := CommAlgCat.of k (Polynomial k)
  let a : P ⟶ R := CommAlgCat.ofHom (Polynomial.aeval c)
  have h := act_extend_natural ρ a (rootPoint x P Polynomial.X) v
  rw [rootPoint_natural] at h
  change act ρ R (rootPoint x R (Polynomial.aeval c Polynomial.X)) (extendVector R v) = _ at h
  rw [Polynomial.aeval_X] at h
  exact h

private theorem orbitPolynomial_coeff_zero {H : GroupScheme k} (ρ : Representation H I)
    {A : AdditiveLine k} (x : A.group ⟶ H) (v : I → k) (i : I) :
    (orbitPolynomial ρ x v i).coeff 0 = v i := by
  have h := orbitPolynomial_eval ρ x v K 0
  rw [rootPoint_zero, act_one, extend_ground] at h
  have hi := congrFun h i
  simpa [Polynomial.aeval_def, Polynomial.eval₂_at_zero] using hi.symm

private theorem rootPoint_add {H : GroupScheme k} {A : AdditiveLine k}
    (x : A.group ⟶ H) (R : TestAlgebra k) (a b : R) :
    rootPoint x R (a + b) = rootPoint x R a * rootPoint x R b := by
  let f := (((groupPointsFunctor k).map x).app R).hom
  change f (LinearAlgebraicGroups.RootData.RootGroups.additivePoints A R (a + b)) =
    f (LinearAlgebraicGroups.RootData.RootGroups.additivePoints A R a) *
      f (LinearAlgebraicGroups.RootData.RootGroups.additivePoints A R b)
  rw [additivePoints_add, map_mul]

private theorem rootPoint_neg {H : GroupScheme k} {A : AdditiveLine k}
    (x : A.group ⟶ H) (R : TestAlgebra k) (a : R) :
    rootPoint x R (-a) = (rootPoint x R a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← rootPoint_add, neg_add_cancel, rootPoint_zero]

private def torusPoint (T : ClosedSubgroup G.val) (R : TestAlgebra k)
    (t : GroupPoints T.group R) : GroupPoints G.val R := t ≫ T.inclusion.hom.hom

private def representativePoint (T : ClosedSubgroup G.val) (α : Character T.group)
    {A : AdditiveLine k} {x y : A.group ⟶ G.val} (D : CorootReflection T α x y) :
    GroupPoints G.val K := toUnit _ ≫ D.representative

private theorem rootWord_factor (T : ClosedSubgroup G.val) (α : Character T.group)
    {A : AdditiveLine k} {x y : A.group ⟶ G.val} (D : CorootReflection T α x y)
    (u : kˣ) :
    rootPoint y K (u : k) =
      rootPoint x K (↑u⁻¹ : k) *
        (torusPoint T K (cocharacterPoint D.coroot K (-u⁻¹))) *
        representativePoint T α D *
        rootPoint x K (↑u⁻¹ : k) := by
  have ht := D.coroot_word K (-u⁻¹)
  change torusPoint T K _ = _ at ht
  rw [representativePoint, D.representative_word, ht]
  have he :
      rootPoint x K (↑u⁻¹ : k) *
        (rankOneWord x y K (-u⁻¹) * (rankOneWord x y K 1)⁻¹) * rankOneWord x y K 1 =
      rootPoint x K (↑u⁻¹ : k) * rankOneWord x y K (-u⁻¹) := by group
  rw [he, rankOneWord]
  simp only [Units.val_neg, inv_neg, inv_inv, neg_neg]
  rw [rootPoint_neg]
  group

private theorem representative_coroot_action (T : ClosedSubgroup G.val) (α χ : Character T.group)
    (ρ : Representation G.val I) {A : AdditiveLine k} {x y : A.group ⟶ G.val}
    (D : CorootReflection T α x y) (v : I → k) (hv : v ∈ weightSpace ρ T χ)
    (m : ℕ) (hm : pairing T.group χ D.coroot = (m : ℤ)) (b : kˣ) :
    let n : GroupPoints G.val K := toUnit _ ≫ D.representative
    act ρ K (cocharacterPoint D.coroot K b ≫ T.inclusion.hom.hom) (act ρ K n v) =
      ((↑(b⁻¹ ^ m) : k)) • act ρ K n v := by
  let n : GroupPoints G.val K := toUnit _ ≫ D.representative
  let t := cocharacterPoint D.coroot K b
  let s : GroupPoints T.group K := t ≫ D.conjugation.inv.hom.hom
  have hconj := congrArg (s ≫ ·) D.conjugates
  simp only [MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc] at hconj
  change s ≫ D.conjugation.hom.hom.hom ≫ T.inclusion.hom.hom =
    n * torusPoint T K s * n⁻¹ at hconj
  have hcancel :
      D.conjugation.inv.hom.hom ≫ D.conjugation.hom.hom.hom = 𝟙 T.group.X :=
    (Grp.forget (SchemeOver k)).congr_map D.conjugation.inv_hom_id
  have hs : s ≫ D.conjugation.hom.hom.hom ≫ T.inclusion.hom.hom =
      t ≫ T.inclusion.hom.hom := by
    change (t ≫ D.conjugation.inv.hom.hom) ≫ D.conjugation.hom.hom.hom ≫
      T.inclusion.hom.hom = _
    rw [← Category.assoc (t ≫ D.conjugation.inv.hom.hom), Category.assoc t, hcancel]
    erw [Category.comp_id]
  rw [hs] at hconj
  change torusPoint T K t = _ at hconj
  have hmul : torusPoint T K t * n = n * torusPoint T K s := by
    rw [hconj, inv_mul_cancel_right]
  have hv' := mem_weightSpace.mp hv K s
  change act ρ K (torusPoint T K s) v = _ at hv'
  have hchar : characterValue χ K s = (↑(b⁻¹ ^ m) : k) := by
    change characterValue χ K (t ≫ D.conjugation.inv.hom.hom) = _
    rw [← characterValue_comp, D.reflection, characterValue_eq_unit]
    let E := characterEvaluation K t
    change (↑(E (χ * α ^ (-pairing T.group χ D.coroot))) : k) = _
    rw [map_mul E, map_zpow E]
    change (↑(characterUnit χ K
        (cocharacterPoint D.coroot K b) *
        characterUnit α K
          (cocharacterPoint D.coroot K b) ^ (-pairing T.group χ D.coroot)) : k) = _
    rw [characterUnit_cocharacter, characterUnit_cocharacter, hm, D.root_pairing, ← zpow_mul, ← zpow_add]
    rw [show (m : ℤ) + 2 * -(m : ℤ) = -(m : ℤ) by omega, zpow_neg, zpow_natCast, inv_pow]
  change act ρ K (torusPoint T K t) (act ρ K n v) = _ • act ρ K n v
  rw [← act_mul, hmul, act_mul, hv', hchar, act_smul, extend_ground]

private theorem rankOne_eval (T : ClosedSubgroup G.val) (α χ : Character T.group)
    (ρ : Representation G.val I) {A : AdditiveLine k} {x y : A.group ⟶ G.val}
    (D : CorootReflection T α x y) (v : I → k) (hx : v ∈ fixedSpace ρ x)
    (hv : v ∈ weightSpace ρ T χ) (m : ℕ) (hm : pairing T.group χ D.coroot = (m : ℤ))
    (u : kˣ) :
    act ρ K (rootPoint y K (u : k)) v =
      (-(u : k)) ^ m • act ρ K (rootPoint x K (↑u⁻¹ : k))
        (act ρ K (toUnit _ ≫ D.representative) v) := by
  let z : GroupPoints A.group K :=
    (testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval (↑u⁻¹ : k))).op
  have hfix : act ρ K (rootPoint x K (↑u⁻¹ : k)) v = v :=
    mem_fixedSpace.mp hx K z
  have hc := representative_coroot_action T α χ ρ D v hv m hm (-u⁻¹)
  change act ρ K (torusPoint T K (cocharacterPoint D.coroot K (-u⁻¹)))
      (act ρ K (representativePoint T α D) v) = _ •
      act ρ K (representativePoint T α D) v at hc
  change _ = _ • act ρ K (rootPoint x K (↑u⁻¹ : k)) (act ρ K (representativePoint T α D) v)
  rw [rootWord_factor T α D u, act_mul, hfix, act_mul, act_mul, hc, act_smul]
  simp only [inv_neg, inv_inv, Units.val_pow_eq_pow_val, Units.val_neg]

private theorem polynomial_bound_of_inversion [Infinite k] (P Q : Polynomial k) (m : ℕ)
    (h : ∀ u : kˣ, P.eval (u : k) = (-(u : k)) ^ m * Q.eval (↑u⁻¹ : k)) :
    P.natDegree ≤ m ∧ P.coeff m = (-1 : k) ^ m * Q.coeff 0 := by
  open Polynomial in
  let N := Q.natDegree
  open Polynomial in
  have heq : P * X ^ N = C ((-1 : k) ^ m) * (Q.reflect N * X ^ m) := by
    apply eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ (Set.infinite_univ.sdiff (Set.finite_singleton (0 : k)))
    intro a ha
    have ha' : a ≠ 0 := by simpa using ha.2
    let u := Units.mk0 a ha'
    letI := invertibleOfNonzero (inv_ne_zero ha')
    have hr := eval₂_reflect_mul_pow (RingHom.id k) a⁻¹ N Q le_rfl
    change (Q.reflect N).eval (⅟a⁻¹) * (a⁻¹) ^ N = Q.eval a⁻¹ at hr
    rw [invOf_eq_inv, inv_inv] at hr
    have hp := h u
    change P.eval a = (-a) ^ m * Q.eval a⁻¹ at hp
    change (P * X ^ N).eval a = (C ((-1 : k) ^ m) * (Q.reflect N * X ^ m)).eval a
    rw [eval_mul, eval_mul, eval_mul, eval_C, eval_pow, eval_pow, eval_X, hp, ← hr]
    rw [mul_assoc, mul_assoc ((Q.reflect N).eval a), ← mul_pow, inv_mul_cancel₀ ha', one_pow, mul_one]
    rw [show -a = (-1 : k) * a by ring, mul_pow]
    ring
  open Polynomial in
  have hcoeff (j : ℕ) (hj : m ≤ j) :
      P.coeff j = (-1 : k) ^ m * (Q.reflect N).coeff (j + N - m) := by
    have e := congrArg (fun p : Polynomial k ↦ p.coeff (j + N)) heq
    rw [coeff_mul_X_pow, coeff_C_mul, coeff_mul_X_pow',
      ite_eq_left (show m ≤ j + N by omega)] at e
    exact e
  open Polynomial in
  refine ⟨natDegree_le_iff_coeff_eq_zero.mpr fun j hj ↦ ?_, ?_⟩
  · rw [hcoeff j hj.le, coeff_eq_zero_of_natDegree_lt (p := Q.reflect N), mul_zero]
    exact lt_of_le_of_lt (natDegree_reflect_le.trans (max_self N).le) (by omega)
  · rw [hcoeff m le_rfl, show m + N - m = N by omega, coeff_reflect, revAt_le le_rfl, Nat.sub_self]

theorem oppositeRootPolynomial : OppositeRootPolynomial.{u} := by
  intro k I _ _ _ _ G T α χ ρ A x y D v hx hv m hm
  let ground := CommAlgCat.of k k
  let w : I → k := act ρ ground (toUnit _ ≫ D.representative) v
  have hp (i : I) := polynomial_bound_of_inversion (orbitPolynomial ρ y v i)
    (orbitPolynomial ρ x w i) m (fun b ↦ by
      have h := rankOne_eval T α χ ρ D v hx hv m hm b
      rw [← extend_ground v, orbitPolynomial_eval ρ y v ground] at h
      have h' := orbitPolynomial_eval ρ x w ground (↑b⁻¹ : k)
      rw [extend_ground] at h'
      change _ = _ • act ρ ground (rootPoint x ground (↑b⁻¹ : k)) w at h
      rw [h'] at h
      have h' := congrFun h i
      change (orbitPolynomial ρ y v i).eval (b : k) = _ at h'
      exact h' )
  refine ⟨fun i ↦ (hp i).1, funext fun i ↦ ?_⟩
  simpa only [orbitPolynomial_coeff_zero, Pi.smul_apply, smul_eq_mul] using (hp i).2

section FrobeniusCoefficients

open WithConv Coalgebra
open Specs.RelativeFrobenius (scalarTensor)
open LinearAlgebraicGroups.FiniteDistributions (Dist FrobeniusFormula twistCoordinates pair)
open private tensorEvaluation tensorEvaluation_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FiniteDistributions
open LinearAlgebraicGroups.RationalRepresentations (tensorCoordinate evaluate)
open private augmentation_extendAlong extensionInclusion
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RelativeFrobenius
open private tensorCoordinate_evaluation tensorCoordinate_tmul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
open private affinePoint affinePointEquiv affinePoint_specGroupMap
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLineBundle

variable (p r : ℕ) [Fact p.Prime] [CharP k p]
variable {B : HopfAlgebraCategory k}

/-- The Frobenius kernel is cut out by the `q`-th powers of augmentation elements. -/
private theorem kernelIdeal_eq_span_powers
    {F : twistCoordinates k p r B ⟶ B} (hF : FrobeniusFormula k p r B F) :
    Specs.kernelIdeal F = Ideal.span ((fun b : B ↦ b ^ (p ^ r)) '' (Specs.augmentationIdeal B : Set B)) := by
  let σ := iterateFrobenius k p r
  change (Specs.augmentationIdeal (Specs.RelativeFrobenius.extendAlong σ B)).map F.hom.toAlgHom = _
  let f := F.hom.toAlgHom.toRingHom
  let j := extensionInclusion σ B
  calc
    _ = ((Specs.augmentationIdeal B).map j).map f :=
      congrArg (Ideal.map f) (augmentation_extendAlong σ B)
    _ = (Specs.augmentationIdeal B).map (f.comp j) := Ideal.map_map j f
    _ = Ideal.span ((f.comp j) '' (Specs.augmentationIdeal B : Set B)) := by
      conv_lhs => rw [← Ideal.span_eq (Specs.augmentationIdeal B), Ideal.map_span]
    _ = _ := by
      congr 1
      apply Set.image_congr
      intro b _
      change F.hom (scalarTensor σ B 1 b) = b ^ (p ^ r)
      rw [hF, one_smul]

private theorem rootPoint_pullback {L : AdditiveLine k} (e : specGroup B ≅ G.val)
    (x : L.group ⟶ G.val) :
    ∃ φ : B →ₐ[k] Polynomial k,
      affinePoint (CommAlgCat.of k (Polynomial k)) φ ≫ e.hom.hom.hom =
        rootPoint x (CommAlgCat.of k (Polynomial k)) Polynomial.X ∧
      (Polynomial.aeval (0 : k)).comp φ = Bialgebra.counitAlgHom k B := by
  let R := CommAlgCat.of k (Polynomial k)
  let g := rootPoint x R Polynomial.X
  let φ := (affinePointEquiv B R).symm (g ≫ e.inv.hom.hom)
  have he : affinePoint R φ = g ≫ e.inv.hom.hom := (affinePointEquiv B R).apply_symm_apply _
  have h : affinePoint R φ ≫ e.hom.hom.hom = g := by
    rw [he, Category.assoc]
    have hc := (Grp.forget (SchemeOver k)).congr_map e.inv_hom_id
    change e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 G.val.X at hc
    rw [hc, Category.comp_id]
  refine ⟨φ, h, ?_⟩
  apply (affinePointEquiv B K).injective
  change affinePoint K _ = affinePoint K _
  let z : R ⟶ K := CommAlgCat.ofHom (Polynomial.aeval (0 : k))
  have hz := rootPoint_natural x z (Polynomial.X : R)
  change mapPoints z g = rootPoint x K (Polynomial.aeval (0 : k) Polynomial.X) at hz
  rw [Polynomial.aeval_X, rootPoint_zero] at hz
  have hcomp : affinePoint K (z.hom.comp φ) ≫ e.hom.hom.hom = 1 := by
    rw [← hz, ← h]
    change (testSpec k).map ((CommAlgCat.ofHom (z.hom.comp φ)).op) ≫ e.hom.hom.hom =
      (testSpec k).map z.op ≫ (testSpec k).map (CommAlgCat.ofHom φ).op ≫ e.hom.hom.hom
    rw [← Functor.map_comp_assoc]
    rfl
  have he1 : affinePoint K (Bialgebra.counitAlgHom k B) = 1 :=
    (Spec.mapMulEquiv (R := k) (S := B) (T := K)).map_one
  rw [he1]
  apply (cancel_mono e.hom.hom.hom).mp
  rw [MonObj.one_comp]
  exact hcomp

private theorem coeff_pullback_annihilates
    {F : twistCoordinates k p r B ⟶ B} (hF : FrobeniusFormula k p r B F)
    (φ : B →ₐ[k] Polynomial k)
    (hφ : (Polynomial.aeval (0 : k)).comp φ = Bialgebra.counitAlgHom k B)
    {j : ℕ} (hj : j < p ^ r) :
    (Specs.kernelIdeal F).restrictScalars k ≤ LinearMap.ker ((Polynomial.lcoeff k j).comp φ.toLinearMap) := by
  have hI : Specs.kernelIdeal F ≤
      (Ideal.span {(Polynomial.X : Polynomial k) ^ (p ^ r)}).comap φ := by
    rw [kernelIdeal_eq_span_powers p r hF, Ideal.span_le]
    rintro _ ⟨b, hb, rfl⟩
    change φ (b ^ (p ^ r)) ∈ Ideal.span {(Polynomial.X : Polynomial k) ^ (p ^ r)}
    rw [map_pow, Ideal.mem_span_singleton]
    apply pow_dvd_pow_of_dvd
    apply Polynomial.X_dvd_iff.mpr
    have h := DFunLike.congr_fun hφ b
    have hb' : Bialgebra.counitAlgHom k B b = 0 := hb
    change Polynomial.aeval (0 : k) (φ b) = Bialgebra.counitAlgHom k B b at h
    rw [hb'] at h
    simpa [Polynomial.aeval_def, Polynomial.eval₂_at_zero] using h
  intro b hb
  have hd := Ideal.mem_span_singleton.mp (hI (show b ∈ Specs.kernelIdeal F from hb))
  exact LinearMap.mem_ker.mpr ((Polynomial.X_pow_dvd_iff.mp hd) j hj)

private theorem pair_lTensor {V C D : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]
    (f : C →ₗ[k] D) (ℓ : D →ₗ[k] k) (t : V ⊗[k] C) :
    pair (toConv ℓ) (f.lTensor V t) = pair (toConv (ℓ.comp f)) t := by
  induction t using TensorProduct.inductionOn with
  | tmul v a => simp
  | add t s ht hs => simp [ht, hs]

omit [DecidableEq I] in
private theorem basis_pair_apply {V C : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup C] [Module k C] (b : Module.Basis I k V)
    (ℓ : C →ₗ[k] k) (t : V ⊗[k] C) (i : I) :
    b.equivFun (pair (toConv ℓ) t) i = ℓ (tensorCoordinate b i t) := by
  induction t using TensorProduct.inductionOn with
  | tmul w c =>
    simp [tensorCoordinate_tmul, Module.Basis.equivFun_apply, smul_eq_mul, mul_comm]
  | add t s ht hs =>
    simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) ht hs

open FlagLineBundle (OppositeBorelPair)
open SimpleClassification (SocleModel)

private def orbitDistribution {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group}
    (S : SocleModel P U χ) {F : twistCoordinates k p r S.A ⟶ S.A}
    [(Specs.kernelIdeal F).IsHopfIdeal k] :
    Dist k (hopfQuotient S.A (Specs.kernelIdeal F)) →ₗ[k] S.socle :=
  let q := hopfQuotientMap S.A (Specs.kernelIdeal F)
  let t := q.hom.toAlgHom.toLinearMap.lTensor S.socle (S.socleCoaction.coaction S.highestVector)
  tensorEvaluation t

set_option maxHeartbeats 1200000 in
private theorem root_coefficients_mem_distribution {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group}
    (S : SocleModel P U χ) {F : twistCoordinates k p r S.A ⟶ S.A}
    [(Specs.kernelIdeal F).IsHopfIdeal k] (hF : FrobeniusFormula k p r S.A F)
    {L : AdditiveLine k} (x : L.group ⟶ G.val) {j : ℕ} (hj : j < p ^ r) :
    (fun i ↦ (orbitPolynomial S.socleAction x
      (S.socleBasis.equivFun S.highestVector) i).coeff j) ∈
      (LinearMap.range (orbitDistribution p r S (F := F))).map S.socleBasis.equivFun.toLinearMap := by
  obtain ⟨φ, hφ, hzero⟩ := rootPoint_pullback (B := S.A) S.groupIso x
  let ℓ := (Polynomial.lcoeff k j).comp φ.toLinearMap
  let Q := hopfQuotient S.A (Specs.kernelIdeal F)
  let q := hopfQuotientMap S.A (Specs.kernelIdeal F)
  let d : Q →ₗ[k] k :=
    ((Specs.kernelIdeal F).restrictScalars k).liftQ ℓ (coeff_pullback_annihilates p r hF φ hzero hj)
  let t := S.socleCoaction.coaction S.highestVector
  have hd : d.comp q.hom.toAlgHom.toLinearMap = ℓ := rfl
  have hp : orbitDistribution p r S (F := F) (toConv d) = pair (toConv ℓ) t := by
    change tensorEvaluation (q.hom.toAlgHom.toLinearMap.lTensor S.socle t) (toConv d) = _
    rw [tensorEvaluation_apply, pair_lTensor, hd]
  refine Submodule.mem_map.mpr ⟨_, LinearMap.mem_range.mpr ⟨toConv d, hp⟩, ?_⟩
  funext i
  change S.socleBasis.equivFun (pair (toConv ℓ) t) i = _
  rw [basis_pair_apply]
  let R := CommAlgCat.of k (Polynomial k)
  let v := S.socleBasis.equivFun S.highestVector
  have h₁ : orbitPolynomial S.socleAction x v i =
      act S.socleAction R (affinePoint R φ ≫ S.groupIso.hom.hom.hom) (extendVector R v) i :=
    congrArg (fun z : GroupPoints G.val R ↦ act S.socleAction R z (extendVector R v) i) hφ.symm
  have h₂ := S.socleAction_spec R φ (S.socleBasis.equivFun S.highestVector) i
  rw [LinearEquiv.symm_apply_apply] at h₂
  have h₃ := tensorCoordinate_evaluation S.socleBasis φ.toLinearMap t i
  have he : orbitPolynomial S.socleAction x v i = φ (tensorCoordinate S.socleBasis i t) :=
    h₁.trans (h₂.trans h₃)
  exact congrArg (Polynomial.lcoeff k j) he.symm

open LinearAlgebraicGroups.FiniteDistributions (toAction toAction_pairs distributionMap)
open private affinePoint_mul affinePoint_inv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLineBundle

private def pointDistribution (g : WithConv (B →ₐ[k] k)) : Dist k B :=
  toConv g.ofConv.toLinearMap

private theorem pointDistribution_mul (g h : WithConv (B →ₐ[k] k)) :
    pointDistribution (g * h) = pointDistribution g * pointDistribution h := rfl

private theorem convolution_contract_left {C : HopfAlgebraCategory k}
    (g : WithConv (B →ₐ[k] k)) (f : B →ₐ[k] C) (ℓ : C →ₗ[k] k) :
    toConv (ℓ.comp (toConv ((Algebra.ofId k C).comp g.ofConv) * toConv f).ofConv.toLinearMap) =
      pointDistribution g * toConv (ℓ.comp f.toLinearMap) := by
  ext b
  change ℓ ((toConv ((Algebra.ofId k C).comp g.ofConv) * toConv f) b) =
    (pointDistribution g * toConv (ℓ.comp f.toLinearMap)) b
  rw [AlgHom.convMul_apply, LinearMap.convMul_apply]
  generalize Coalgebra.comul (R := k) b = t
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    change ℓ (algebraMap k C (g a) * f b) = g a * ℓ (f b)
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  | add t s ht hs => simp only [map_add, ht, hs]

private theorem convolution_contract_right {C : HopfAlgebraCategory k}
    (f : B →ₐ[k] C) (g : WithConv (B →ₐ[k] k)) (ℓ : C →ₗ[k] k) :
    toConv (ℓ.comp (toConv f * toConv ((Algebra.ofId k C).comp g.ofConv)).ofConv.toLinearMap) =
      toConv (ℓ.comp f.toLinearMap) * pointDistribution g := by
  ext b
  change ℓ ((toConv f * toConv ((Algebra.ofId k C).comp g.ofConv)) b) =
    (toConv (ℓ.comp f.toLinearMap) * pointDistribution g) b
  rw [AlgHom.convMul_apply, LinearMap.convMul_apply]
  generalize Coalgebra.comul (R := k) b = t
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    change ℓ (f a * algebraMap k C (g b)) = ℓ (f a) * g b
    rw [mul_comm (f a), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  | add t s ht hs => simp only [map_add, ht, hs]

/-- Conjugating at a rational point preserves the distributions supported on a normal subgroup. -/
private theorem conjugate_distribution {C : HopfAlgebraCategory k} (q : B ⟶ C)
    (normal : Specs.IsNormalSubgroup (specGroupMap q)) (g : WithConv (B →ₐ[k] k))
    (d : Dist k C) :
    letI := convolutionGroup B K
    ∃ d' : Dist k C, pointDistribution g * distributionMap q.hom.toCoalgHom d *
      pointDistribution g⁻¹ = distributionMap q.hom.toCoalgHom d' := by
  letI := convolutionGroup B K
  let R := CommAlgCat.of k C
  let u := toConv ((Algebra.ofId k C).comp g.ofConv)
  let v := toConv ((Algebra.ofId k C).comp g⁻¹.ofConv)
  let t := affinePoint R (AlgHom.id k C)
  obtain ⟨c, hc⟩ := normal
  let z := lift (affinePoint R u.ofConv) t
  let f := (affinePointEquiv C R).symm (z ≫ c)
  have hf : affinePoint R f = z ≫ c := (affinePointEquiv C R).apply_symm_apply _
  have hu : affinePoint R v.ofConv = (affinePoint R u.ofConv)⁻¹ := by
    let a : K ⟶ R := CommAlgCat.ofHom (Algebra.ofId k C)
    have ha (h : WithConv (B →ₐ[k] k)) :
        affinePoint R ((Algebra.ofId k C).comp h.ofConv) =
          mapPoints a (affinePoint K h.ofConv) := by
      change (testSpec k).map (CommAlgCat.ofHom ((Algebra.ofId k C).comp h.ofConv)).op =
        (testSpec k).map a.op ≫ (testSpec k).map (CommAlgCat.ofHom h.ofConv).op
      rw [← Functor.map_comp]
      rfl
    change affinePoint R ((Algebra.ofId k C).comp g⁻¹.ofConv) =
      (affinePoint R ((Algebra.ofId k C).comp g.ofConv))⁻¹
    rw [ha, ha, affinePoint_inv (R := K) (A := B) g]
    exact map_inv (((groupPointsFunctor k).obj (specGroup B)).map a).hom _
  have hfactor : (u * toConv q.hom.toAlgHom * v).ofConv = f.comp q.hom.toAlgHom := by
    apply (affinePointEquiv B R).injective
    change affinePoint R (u * toConv q.hom.toAlgHom * v).ofConv =
      affinePoint R (f.comp q.hom.toAlgHom)
    rw [← affinePoint_specGroupMap, hf, Category.assoc, hc, affinePoint_mul, affinePoint_mul, hu]
    unfold Specs.subgroupConjugation
    simp only [MonObj.comp_mul, GrpObj.comp_inv, z, lift_fst, lift_snd_assoc]
    rw [affinePoint_specGroupMap]
    rfl
  refine ⟨toConv (d.ofConv.comp f.toLinearMap), ?_⟩
  have he : toConv (d.ofConv.comp (u * toConv q.hom.toAlgHom * v).ofConv.toLinearMap) =
      pointDistribution g * distributionMap q.hom.toCoalgHom d * pointDistribution g⁻¹ := by
    erw [convolution_contract_right _ g⁻¹, convolution_contract_left g]
    rfl
  rw [← he, hfactor]
  rfl

private theorem orbitDistribution_apply {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group}
    (S : SocleModel P U χ) {F : twistCoordinates k p r S.A ⟶ S.A}
    [(Specs.kernelIdeal F).IsHopfIdeal k] (d : Dist k (hopfQuotient S.A (Specs.kernelIdeal F))) :
    orbitDistribution p r S (F := F) d =
      toAction S.socleCoaction
        (distributionMap (hopfQuotientMap S.A (Specs.kernelIdeal F)).hom.toCoalgHom d)
        S.highestVector := by
  rw [orbitDistribution, tensorEvaluation_apply, toAction_pairs]
  exact pair_lTensor _ _ _

private theorem basis_act_point {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group}
    (S : SocleModel P U χ) (g : WithConv (S.A →ₐ[k] k)) (v : S.socle) :
    act S.socleAction K (affinePoint K g.ofConv ≫ S.groupIso.hom.hom.hom)
      (S.socleBasis.equivFun v) =
      S.socleBasis.equivFun (toAction S.socleCoaction (pointDistribution g) v) := by
  rw [toAction_pairs]
  funext i
  rw [pointDistribution, basis_pair_apply]
  have h := S.socleAction_spec K g.ofConv (S.socleBasis.equivFun v) i
  rw [LinearEquiv.symm_apply_apply, extend_ground] at h
  exact h.trans (tensorCoordinate_evaluation _ _ _ _)

private theorem distribution_span_preserved {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group}
    (S : SocleModel P U χ) {F : twistCoordinates k p r S.A ⟶ S.A}
    [(Specs.kernelIdeal F).IsHopfIdeal k]
    (g : GroupPoints G.val K)
    (hg : act S.socleAction K g (S.socleBasis.equivFun S.highestVector) ∈
      (LinearMap.range (orbitDistribution p r S (F := F))).map S.socleBasis.equivFun.toLinearMap) :
    ∀ w ∈ (LinearMap.range (orbitDistribution p r S (F := F))).map S.socleBasis.equivFun.toLinearMap,
      act S.socleAction K g w ∈
        (LinearMap.range (orbitDistribution p r S (F := F))).map S.socleBasis.equivFun.toLinearMap := by
  let e := S.groupIso
  obtain ⟨a, ha⟩ := (affinePointEquiv S.A K).surjective (g ≫ e.inv.hom.hom)
  change affinePoint K a = g ≫ e.inv.hom.hom at ha
  have he : affinePoint K a ≫ e.hom.hom.hom = g := by
    rw [ha, Category.assoc]
    have hc := (Grp.forget (SchemeOver k)).congr_map e.inv_hom_id
    change e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 G.val.X at hc
    rw [hc, Category.comp_id]
  rw [← he] at hg ⊢
  intro w hw
  obtain ⟨z, ⟨d, rfl⟩, rfl⟩ := Submodule.mem_map.mp hw
  obtain ⟨z, ⟨f, rfl⟩, hf⟩ := Submodule.mem_map.mp hg
  change S.socleBasis.equivFun (orbitDistribution p r S (F := F) f) = _ at hf
  rw [basis_act_point] at hf
  have hf' := S.socleBasis.equivFun.injective hf
  letI := convolutionGroup S.A K
  let A := toAction S.socleCoaction
  let q := hopfQuotientMap S.A (Specs.kernelIdeal F)
  let j := distributionMap q.hom.toCoalgHom
  let h := toConv a
  have hn : Specs.IsNormalSubgroup (specGroupMap q) :=
    (LinearAlgebraicGroups.schemeKernel k F).2
  obtain ⟨d', hd'⟩ := conjugate_distribution q hn h d
  have hmul : pointDistribution h * j d = j d' * pointDistribution h := by
    rw [← hd', mul_assoc (pointDistribution h * j d),
      ← pointDistribution_mul, inv_mul_cancel, show pointDistribution (1 : WithConv (S.A →ₐ[k] k)) = 1 from rfl,
      mul_one]
  refine Submodule.mem_map.mpr ⟨_, LinearMap.mem_range.mpr ⟨d' * f, rfl⟩, ?_⟩
  change S.socleBasis.equivFun (orbitDistribution p r S (F := F) (d' * f)) =
    act S.socleAction K (affinePoint K a ≫ e.hom.hom.hom)
      (S.socleBasis.equivFun (orbitDistribution p r S (F := F) d))
  rw [basis_act_point, orbitDistribution_apply, orbitDistribution_apply]
  change S.socleBasis.equivFun (A (j (d' * f)) S.highestVector) =
    S.socleBasis.equivFun (A (pointDistribution h) (A (j d) S.highestVector))
  rw [map_mul j, map_mul A, Module.End.mul_apply]
  have hfv : A (j f) S.highestVector = A (pointDistribution h) S.highestVector :=
    (orbitDistribution_apply p r S f).symm.trans hf'
  rw [hfv]
  change S.socleBasis.equivFun (A (j d') (A (pointDistribution h) S.highestVector)) = _
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul A, ← map_mul A, hmul]

private theorem rootOrbit_mem [Infinite k] {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group}
    (S : SocleModel P U χ) {F : twistCoordinates k p r S.A ⟶ S.A}
    [(Specs.kernelIdeal F).IsHopfIdeal k] (hF : FrobeniusFormula k p r S.A F)
    {L : AdditiveLine k} (x : L.group ⟶ G.val)
    (hd : ∀ i, (orbitPolynomial S.socleAction x
      (S.socleBasis.equivFun S.highestVector) i).natDegree < p ^ r)
    (a : k) :
    act S.socleAction K (rootPoint x K a) (S.socleBasis.equivFun S.highestVector) ∈
      (LinearMap.range (orbitDistribution p r S (F := F))).map S.socleBasis.equivFun.toLinearMap := by
  let v := S.socleBasis.equivFun S.highestVector
  have he := orbitPolynomial_eval S.socleAction x v K a
  rw [extend_ground] at he
  change act S.socleAction K (rootPoint x K a) v ∈ _
  rw [he]
  have h : (fun i ↦ Polynomial.aeval a (orbitPolynomial S.socleAction x v i)) =
      ∑ j ∈ Finset.range (p ^ r), a ^ j •
        (fun i ↦ (orbitPolynomial S.socleAction x v i).coeff j) := by
    funext i
    change (orbitPolynomial S.socleAction x v i).eval a = _
    rw [Polynomial.eval_eq_sum_range' (hd i), Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, mul_comm, v]
  rw [h]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact root_coefficients_mem_distribution p r S hF x (Finset.mem_range.mp hj)

end FrobeniusCoefficients

open WithConv
open FlagLineBundle (OppositeBorelPair)
open SimpleClassification (SocleModel)
open LinearAlgebraicGroups.FiniteDistributions (toAction toAction_pairs Dist pair)
open LinearAlgebraicGroups.RationalRepresentations (evaluate)
open private affinePoint from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLineBundle
open private tensorEvaluation_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FiniteDistributions

open AbstractPairing (Datum Root IsAttachedCoroot)
open BorelsAndChambers (subgroupRoots positiveRoots)
open CharacterDescent (Cocharacter)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open Unipotent (closedSubgroupAlgebraicGroup)
open RootWeightAction (SimpleRoot)
open LinearAlgebraicGroups.CocharacterDynamics (contractingSubgroupUnipotent multiplyFactors)
open private isKBorel_iff_of_isAlgClosed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private unipotent_subgroup_in_borel_radical from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private borel_of_regular_cocharacter from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private coroot_reflection_is_representative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SimpleParabolicProduct
open private normalizerLabel normalizerLabel_eq normalizerLabel_ker pointHom restrictPointHom
  doubleCosets_cover_geometric from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.BruhatCells

private theorem borelSections_le (P : OppositeBorelPair G) (U : ClosedSubgroup P.positive.group)
    (hU : Specs.GeometricRadicals.IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (Y : SchemeOver k) (H : Subgroup (Y ⟶ G.val.X))
    (ht : SubgroupSections P.torus Y ≤ H)
    (hu : SubgroupSections (subgroupOfSubgroup P.positive U) Y ≤ H) :
    SubgroupSections P.positive Y ≤ H := by
  obtain ⟨hc, D, e, hpos, hw, hroot, hdec⟩ :=
    LinearAlgebraicGroups.RootData.BorelPositivity.borelPositivity G P.reductive P.torus P.split P.maximal
  letI := hc
  obtain ⟨R, j, q, hR, _, hj, _, _, hm, _⟩ := hdec P.positive P.positiveBorel P.inPositive
  letI := hm
  obtain ⟨i, hi⟩ := hU.2.2 R hR.1 hR.2.1
  rintro _ ⟨b, rfl⟩
  let y := b ≫ inv (multiplyFactors j R.inclusion)
  have hb : y ≫ multiplyFactors j R.inclusion = b := by simp [y]
  change b ≫ P.positive.inclusion.hom.hom ∈ H
  rw [← hb]
  change (y ≫ ((fst _ _ ≫ j.hom.hom) * (snd _ _ ≫ R.inclusion.hom.hom))) ≫
    P.positive.inclusion.hom.hom ∈ H
  rw [MonObj.comp_mul, MonObj.mul_comp]
  apply H.mul_mem
  · apply ht
    refine ⟨y ≫ fst _ _, ?_⟩
    have hh := (Grp.forget (SchemeOver k)).congr_map hj
    change j.hom.hom ≫ P.positive.inclusion.hom.hom = P.torus.inclusion.hom.hom at hh
    change (y ≫ fst _ _) ≫ P.torus.inclusion.hom.hom =
      (y ≫ fst _ _ ≫ j.hom.hom) ≫ P.positive.inclusion.hom.hom
    simp only [Category.assoc, hh]
  · apply hu
    refine ⟨y ≫ snd _ _ ≫ i.hom.hom, ?_⟩
    have hh := (Grp.forget (SchemeOver k)).congr_map hi
    change i.hom.hom ≫ U.inclusion.hom.hom = R.inclusion.hom.hom at hh
    change _ ≫ (U.inclusion.hom.hom ≫ P.positive.inclusion.hom.hom) = _
    simp only [Category.assoc, ← reassoc_of% hh]

private theorem baseRoot_isSimple (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X]
    (D : Datum P.torus) (c : Cocharacter P.torus.group) (b : D.rootDatum.Base)
    (hc : positiveRoots P.torus c = subgroupRoots P.torus P.positive)
    (hb : Specs.SimpleRoots.IsBaseFor D.rootDatum (Specs.SimpleRoots.evaluate D c) b)
    (i : b.support) : ∃ α : SimpleRoot P.torus P.positive, α.val = i.val := by
  have hpos : Specs.SimpleRoots.positive D.rootDatum (Specs.SimpleRoots.evaluate D c) =
      subgroupRoots P.torus P.positive := by
    rw [← hc]
    ext a
    change 0 < D.rootDatum.toLinearMap (D.rootDatum.root a) (Additive.ofMul c) ↔
      0 < pairing P.torus.group a.val c
    rw [D.root_eq, D.pairing_eq]
  obtain ⟨hi, hind⟩ := (hb.simple_iff i.val).mp i.property
  rw [hpos] at hi hind
  refine ⟨⟨i.val, hi, ?_⟩, rfl⟩
  intro a ha b hb h
  apply hind a ha b hb
  rw [D.root_eq, D.root_eq, D.root_eq, h]
  rfl

private theorem positiveRoot_factors [IsAlgClosed k] (P : OppositeBorelPair G)
    (U : ClosedSubgroup P.positive.group)
    (hU : Specs.GeometricRadicals.IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    {α : Root P.torus} (hα : α ∈ subgroupRoots P.torus P.positive)
    (C : Specs.RankOneFlag.Centralizer P.torus α.val) (c : Cocharacter P.torus.group)
    (hC : Specs.GeometricRadicals.IsReductive (closedSubgroupAlgebraicGroup C.subgroup))
    (D : LinearAlgebraicGroups.CocharacterDynamics.LimitDecomposition
      (c ≫ C.torusIso.hom ≫ C.torus.inclusion))
    (hroot : RootGroups.IsRootSubgroup P.torus
      (subgroupOfSubgroup C.subgroup D.contracting) α.val) :
    SchemeDerivedGroup.IsSubgroupOf (subgroupOfSubgroup C.subgroup D.contracting)
      (subgroupOfSubgroup P.positive U) := by
  have hB := (isKBorel_iff_of_isAlgClosed G P.positive).mp P.positiveBorel
  have hAB :=
    (LinearAlgebraicGroups.RootData.BorelsAndChambers.geometricBorelRootSubgroups
      G P.reductive P.torus P.split P.maximal P.positive hB P.inPositive α _ hroot).mp hα
  letI := hC.1
  exact unipotent_subgroup_in_borel_radical hB hAB
    (contractingSubgroupUnipotent (closedSubgroupAlgebraicGroup C.subgroup) _ D) hU

open scoped Pointwise in
private theorem doubleProduct_subset_subgroup {M : Type*} [Group M] (B H : Subgroup M)
    (hB : B ≤ H) (n : M) (hn : n ∈ H) :
    (B : Set M) * {n} * (B : Set M) ⊆ H :=
  Subgroup.mul_subset (H := H)
    (Subgroup.mul_subset (H := H) hB (Set.singleton_subset_iff.mpr hn)) hB


private theorem matched_root_coordinates [IsAlgClosed k] (P : OppositeBorelPair G)
    {U : ClosedSubgroup P.positive.group}
    (hU : Specs.GeometricRadicals.IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (α : SimpleRoot P.torus P.positive) (c : Cocharacter P.torus.group)
    (hc : IsAttachedCoroot P.torus α.val c) :
    ∃ (L : AdditiveLine k) (x y : L.group ⟶ G.val)
      (D : CorootReflection P.torus α.val.val x y),
      D.coroot = c ∧ ∃ z : L.group ⟶ U.group, z ≫ U.inclusion ≫ P.positive.inclusion = x := by
  obtain ⟨C, t, hC, ht, L, M, hpair, Q, E, A, line, x, y, hx, _, hxs, hys, ⟨R, hR⟩⟩ := hc
  obtain ⟨z, hz⟩ := positiveRoot_factors P U hU α.property.1 C t hC L hx
  refine ⟨line, _, _, R, hR, x.root.hom ≫ z, ?_⟩
  change z ≫ (U.inclusion ≫ P.positive.inclusion) =
    L.contracting.inclusion ≫ C.subgroup.inclusion at hz
  rw [Category.assoc, hz]

private theorem lift_subgroup_membership {M N W : Type*} [Group M] [Group N] [Group W]
    (H : Subgroup M) (f : N →* M) (φ : N →* W)
    (hker : ∀ n, φ n = 1 → f n ∈ H) (hgen : (H.comap f).map φ = ⊤)
    (n : N) : f n ∈ H := by
  obtain ⟨m, hm, he⟩ := Subgroup.mem_map.mp (show φ n ∈ (H.comap f).map φ by rw [hgen]; trivial)
  have hk : f (m⁻¹ * n) ∈ H := hker _ (by rw [map_mul, map_inv, he, inv_mul_cancel])
  simpa only [map_mul, map_inv, mul_inv_cancel_left] using H.mul_mem hm hk

private def ContainsSimpleRepresentatives (P : OppositeBorelPair G)
    (U : ClosedSubgroup P.positive.group) (H : Subgroup ((testSpec k).obj (op K) ⟶ G.val.X)) : Prop :=
  ∀ (α : SimpleRoot P.torus P.positive) (c : Cocharacter P.torus.group),
    IsAttachedCoroot P.torus α.val c →
    ∀ {L : AdditiveLine k} {x y : L.group ⟶ G.val}
    (D : CorootReflection P.torus α.val.val x y), D.coroot = c →
    (∃ z : L.group ⟶ U.group, z ≫ U.inclusion ≫ P.positive.inclusion = x) →
    representativePoint P.torus α.val.val D ∈ H

private theorem lift_simple_representative (T : ClosedSubgroup G.val) [IsCommMonObj T.group.X]
    {D : Datum T} (I : DatumAndWeyl.Identification D) (α : Root T)
    {L : AdditiveLine k} {x y : L.group ⟶ G.val} (R : CorootReflection T α.val x y)
    (hR : R.coroot = Additive.toMul (D.rootDatum.coroot α))
    (H : Subgroup ((testSpec k).obj (op K) ⟶ G.val.X))
    (hw : representativePoint T α.val R ∈ H) :
    ∃ n, Specs.BruhatOrbitParametrization.IsRepresentative I
          (RootPairing.weylGroup.ofIdx D.rootDatum α) n ∧
      toUnit ((testSpec k).obj (op K)) ≫ n ≫ I.normalizer.inclusion.hom.hom ∈ H := by
  obtain ⟨n, hn, hnG⟩ := coroot_reflection_is_representative I α R hR
  refine ⟨n, hn, ?_⟩
  change toUnit ((testSpec k).obj (op K)) ≫ R.representative ∈ H at hw
  exact (congrArg (fun g : 𝟙_ (SchemeOver k) ⟶ G.val.X ↦
    toUnit ((testSpec k).obj (op K)) ≫ g ∈ H) hnG).mpr hw

private theorem contains_simple_representative [IsAlgClosed k]
    (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X] {D : Datum P.torus}
    (I : DatumAndWeyl.Identification D) {U : ClosedSubgroup P.positive.group}
    (hU : Specs.GeometricRadicals.IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (H : Subgroup ((testSpec k).obj (op K) ⟶ G.val.X)) (hs : ContainsSimpleRepresentatives P U H)
    (α : SimpleRoot P.torus P.positive) :
    ∃ n, Specs.BruhatOrbitParametrization.IsRepresentative I
          (RootPairing.weylGroup.ofIdx D.rootDatum α.val) n ∧
      toUnit ((testSpec k).obj (op K)) ≫ n ≫ I.normalizer.inclusion.hom.hom ∈ H := by
  let c := Additive.toMul (D.rootDatum.coroot α.val)
  have hc : IsAttachedCoroot P.torus α.val c := D.attached α.val
  obtain ⟨L, x, y, R, hR, hz⟩ := matched_root_coordinates P hU α c hc
  exact lift_simple_representative P.torus I α.val R hR H (hs α c hc R hR hz)

private theorem normalizer_sections_le [IsAlgClosed k]
    (P : OppositeBorelPair G) [IsCommMonObj P.torus.group.X] {D : Datum P.torus}
    (I : DatumAndWeyl.Identification D) {U : ClosedSubgroup P.positive.group}
    (hU : Specs.GeometricRadicals.IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (H : Subgroup ((testSpec k).obj (op K) ⟶ G.val.X))
    (hB : SubgroupSections P.positive ((testSpec k).obj (op K)) ≤ H)
    (hs : ContainsSimpleRepresentatives P U H)
    (c : Cocharacter P.torus.group) (b : D.rootDatum.Base)
    (hp : positiveRoots P.torus c = subgroupRoots P.torus P.positive)
    (hb : Specs.SimpleRoots.IsBaseFor D.rootDatum (Specs.SimpleRoots.evaluate D c) b)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) (hn : Normalizes P.torus.inclusion n) :
    toUnit ((testSpec k).obj (op K)) ≫ n ∈ H := by
  let Y := (testSpec k).obj (op K)
  let f := (pointHom I.normalizer.inclusion Y).comp (restrictPointHom I.normalizer.group Y)
  let φ := normalizerLabel I
  have hker (m : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X) (hm : φ m = 1) : f m ∈ H :=
    hB (normalizerLabel_ker I P.inPositive Y m hm)
  have hgen : (H.comap f).map φ = ⊤ := by
    apply top_unique
    rw [← hb.generates]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨α, hα⟩ := baseRoot_isSimple P D c b hp hb i
    change RootPairing.weylGroup.ofIdx D.rootDatum i.val ∈ (H.comap f).map φ
    obtain ⟨n, hn, hmem⟩ := contains_simple_representative P I hU H hs α
    have hn' : φ n = RootPairing.weylGroup.ofIdx D.rootDatum i.val :=
      (normalizerLabel_eq I hn).trans (congrArg (RootPairing.weylGroup.ofIdx D.rootDatum) hα)
    exact Subgroup.mem_map.mpr ⟨n, hmem, hn'⟩
  obtain ⟨m, hm⟩ := (I.representsNormalizer _ _).mp hn
  have hmem := lift_subgroup_membership H f φ hker hgen m
  change toUnit Y ≫ m ≫ I.normalizer.inclusion.hom.hom ∈ H at hmem
  rw [hm] at hmem
  exact hmem

private theorem rational_double_coset [IsAlgClosed k] (P : OppositeBorelPair G)
    {U : ClosedSubgroup P.positive.group}
    (hU : Specs.GeometricRadicals.IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (g : GroupPoints G.val K) :
    ∃ n : 𝟙_ (SchemeOver k) ⟶ G.val.X, Normalizes P.torus.inclusion n ∧
      g ∈ Specs.SimpleParabolicProduct.doubleCoset P.positive ((testSpec k).obj (op K)) n := by
  obtain ⟨hc, D, _, _, _, _, hd⟩ :=
    LinearAlgebraicGroups.RootData.BorelPositivity.borelPositivity G P.reductive P.torus P.split P.maximal
  obtain ⟨Rneg, _, _, hneg, _⟩ := hd P.negative P.negativeBorel P.inNegative
  exact doubleCosets_cover_geometric LinearAlgebraicGroups.Flag.OpenCell.openCell
    LinearAlgebraicGroups.Flag.SimpleParabolicProduct.simpleParabolicProduct
    P.reductive P.split P.maximal P.positiveBorel P.negativeBorel P.inPositive P.inNegative
    P.opposite hU hneg k g

/-- The positive Borel and the simple Weyl words generate the rational points via Bruhat coverage. -/
private theorem subgroup_eq_top_of_simple_representatives [IsAlgClosed k]
    (P : OppositeBorelPair G) {U : ClosedSubgroup P.positive.group}
    (hU : Specs.GeometricRadicals.IsUnipotentRadical (closedSubgroupAlgebraicGroup P.positive) U)
    (H : Subgroup (GroupPoints G.val K))
    (hT : SubgroupSections P.torus ((testSpec k).obj (op K)) ≤ H)
    (hR : SubgroupSections (subgroupOfSubgroup P.positive U) ((testSpec k).obj (op K)) ≤ H)
    (hs : ContainsSimpleRepresentatives P U H) : H = ⊤ := by
  let Y := (testSpec k).obj (op K)
  have hB : SubgroupSections P.positive Y ≤ H := borelSections_le P U hU Y H hT hR
  obtain ⟨c, _, hc, _, hp⟩ :=
    borel_of_regular_cocharacter G P.reductive P.torus P.split P.maximal
      P.positive P.positiveBorel P.inPositive
  obtain ⟨hcomm, D, I, hbase⟩ :=
    LinearAlgebraicGroups.RootData.SimpleRoots.simpleRoots G P.reductive P.torus P.split P.maximal
  letI := hcomm
  obtain ⟨b, hb, _⟩ := hbase c hc
  apply top_unique
  intro g _
  obtain ⟨n, hn, hg⟩ := rational_double_coset P hU g
  have hmem := normalizer_sections_le P I hU H hB hs c b hp.symm hb n hn
  let H' : Subgroup (Y ⟶ G.val.X) := H
  have hB' : SubgroupSections P.positive Y ≤ H' := hB
  have hn' : toUnit Y ≫ n ∈ H' := hmem
  have hg' : g ∈ Specs.SimpleParabolicProduct.doubleCoset P.positive Y n := hg
  change g ∈ H'
  exact doubleProduct_subset_subgroup (SubgroupSections P.positive Y) H' hB'
    (toUnit Y ≫ n) hn' hg'

private def pointStabilizer (ρ : Representation G.val I) (W : Submodule k (I → k)) :
    Subgroup (GroupPoints G.val K) where
  carrier := {g | ∀ w ∈ W, act ρ K g w ∈ W ∧ act ρ K g⁻¹ w ∈ W}
  one_mem' := by simp [act_one]
  mul_mem' := by
    intro g h hg hh w hw
    exact ⟨by rw [act_mul]; exact (hg _ (hh _ hw).1).1,
      by rw [mul_inv_rev, act_mul]; exact (hh _ (hg _ hw).2).2⟩
  inv_mem' := by
    intro g hg w hw
    simpa only [inv_inv] using (hg w hw).symm

open private realizes_unique from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SimpleClassification
open private pointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.InducedSocle
open private act_contract contract orbit_le_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.PrimitiveLine
open private contracts_mem_subcomodule from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SimpleClassification
open LinearAlgebraicGroups.RationalRepresentations (geometricStability)

private theorem stable_of_rational_points [IsAlgClosed k] {P : OppositeBorelPair G}
    {U : ClosedSubgroup P.positive.group} {χ : Character P.torus.group}
    (S : SocleModel P U χ) (M : Submodule k S.socle)
    (hM : ∀ g : GroupPoints G.val K, ∀ w ∈ M.map S.socleBasis.equivFun.toLinearMap,
      act S.socleAction K g w ∈ M.map S.socleBasis.equivFun.toLinearMap) :
    Specs.PrimitiveLine.IsStable S.socleAction (M.map S.socleBasis.equivFun.toLinearMap) := by
  classical
  have hsub : S.socleCoaction.IsSubcomodule M := by
    apply (geometricStability G S.A S.groupIso P.reductive.1 S.socleCoaction M).mp
    intro a x
    let e : k ≃ₐ[k] AlgebraicClosure k :=
      AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k))
        IsAlgClosed.algebraMap_bijective_of_isIntegral
    let g := e.symm.toAlgHom.comp a
    let w := toAction S.socleCoaction (pointDistribution (toConv g)) (x : S.socle)
    have h := hM (affinePoint K g ≫ S.groupIso.hom.hom.hom) _
      (Submodule.mem_map_of_mem x.property)
    have hact := basis_act_point S (toConv g) (x : S.socle)
    change act S.socleAction K (affinePoint K g ≫ S.groupIso.hom.hom.hom)
      (S.socleBasis.equivFun (x : S.socle)) = S.socleBasis.equivFun w at hact
    have hw' : S.socleBasis.equivFun w ∈ M.map S.socleBasis.equivFun.toLinearMap :=
      (congrArg (fun v : S.J → k ↦ v ∈ M.map S.socleBasis.equivFun.toLinearMap) hact).mp h
    obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp hw'
    have he' : y = w := S.socleBasis.equivFun.injective he
    have hw : w ∈ M := he' ▸ hy
    refine ⟨(⟨w, hw⟩ : M) ⊗ₜ[k] (1 : AlgebraicClosure k), ?_⟩
    change w ⊗ₜ[k] (1 : AlgebraicClosure k) = evaluate S.A S.socleCoaction a x
    apply (e.symm.toLinearEquiv.lTensor S.socle).injective
    change e.symm.toLinearMap.lTensor S.socle (w ⊗ₜ[k] (1 : AlgebraicClosure k)) =
      e.symm.toLinearMap.lTensor S.socle (a.toLinearMap.lTensor S.socle
        (S.socleCoaction.coaction x))
    rw [LinearMap.lTensor_tmul, AlgEquiv.toLinearMap_apply, map_one, ← LinearMap.comp_apply,
      ← LinearMap.lTensor_comp]
    change w ⊗ₜ[k] (1 : k) = g.toLinearMap.lTensor S.socle (S.socleCoaction.coaction x)
    apply (TensorProduct.rid k S.socle).injective
    rw [TensorProduct.rid_tmul, one_smul]
    exact toAction_pairs S.socleCoaction (pointDistribution (toConv g)) x
  intro w hw
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hw
  apply (orbit_le_iff _ _ _).mpr
  intro R z ℓ
  let e := pointIso S.groupIso
  obtain ⟨a, rfl⟩ := ((CategoryTheory.forget GrpCat).mapIso (e.app R)).toEquiv.surjective z
  have h := act_contract e S.socleBasis S.socleCoaction R a.ofConv ℓ x
  rw [← realizes_unique S.groupIso S.socleBasis S.socleCoaction S.socleAction S.socleAction_spec] at h
  change Specs.PrimitiveLine.orbitCoefficient S.socleAction R (e.hom.app R a) ℓ
    (S.socleBasis.equivFun x) = _ at h
  change Specs.PrimitiveLine.orbitCoefficient S.socleAction R
    (e.hom.app R a) ℓ (S.socleBasis.equivFun x) ∈ _
  rw [h]
  exact Submodule.mem_map_of_mem (contracts_mem_subcomodule hsub x hx _)

set_option maxHeartbeats 1200000 in
theorem cyclicity : Cyclicity.{u} := by
  intro k _ _ p r _ _ hr G P U hU χ hdom hrestricted S F hF hk
  letI := hk
  let K₀ := CommAlgCat.of k k
  let ρ := S.socleAction
  let v := S.socleBasis.equivFun S.highestVector
  let M := LinearMap.range (orbitDistribution p r S (F := F))
  let W := M.map S.socleBasis.equivFun.toLinearMap
  have hv : v ∈ W := by
    apply Submodule.mem_map_of_mem
    refine LinearMap.mem_range.mpr ⟨1, ?_⟩
    rw [orbitDistribution_apply, map_one, map_one]
    rfl
  let H := pointStabilizer ρ W
  have memH (g : GroupPoints G.val K₀) (hg : act ρ K₀ g v ∈ W) (hi : act ρ K₀ g⁻¹ v ∈ W) :
      g ∈ H := fun w hw ↦ ⟨distribution_span_preserved p r S g hg w hw,
        distribution_span_preserved p r S g⁻¹ hi w hw⟩
  let Y := (testSpec k).obj (op K₀)
  have hT : SubgroupSections P.torus Y ≤ H := by
    rintro g ⟨t, rfl⟩
    have h (t : GroupPoints P.torus.group K₀) :
        act ρ K₀ (torusPoint P.torus K₀ t) v ∈ W := by
      have hwt := mem_weightSpace.mp S.primitive.2.2 K₀ t
      change act ρ K₀ (torusPoint P.torus K₀ t) v = _ at hwt
      rw [extend_ground] at hwt
      rw [hwt]
      exact W.smul_mem _ hv
    apply memH
    · exact h t
    · change (act ρ K₀ (((((groupPointsFunctor k).map P.torus.inclusion).app K₀).hom t)⁻¹) v) ∈ W
      rw [← map_inv]
      exact h t⁻¹
  have hR : SubgroupSections (subgroupOfSubgroup P.positive U) Y ≤ H := by
    rintro g ⟨t, rfl⟩
    let x := U.inclusion ≫ P.positive.inclusion
    have h (t : GroupPoints U.group K₀) :
        act ρ K₀ (t ≫ x.hom.hom) v = v := by
      have hf := mem_fixedSpace.mp S.primitive.2.1 K₀ t
      rw [extend_ground] at hf
      exact hf
    apply memH
    · change act ρ K₀ (t ≫ x.hom.hom) v ∈ W
      exact (h t).symm ▸ hv
    · change act ρ K₀ (((((groupPointsFunctor k).map x).app K₀).hom t)⁻¹) v ∈ W
      rw [← map_inv]
      change act ρ K₀ (t⁻¹ ≫ x.hom.hom) v ∈ W
      rw [h]
      exact hv
  have htop : H = ⊤ := by
    apply subgroup_eq_top_of_simple_representatives P hU H hT hR
    intro α c hD L x y D hcor hz
    have hfix : v ∈ fixedSpace ρ x := by
      obtain ⟨z, hz⟩ := hz
      rw [← hz]
      apply mem_fixedSpace.mpr
      intro R a
      have hf := mem_fixedSpace.mp S.primitive.2.1 R (a ≫ z.hom.hom)
      change act ρ R (a ≫ (z.hom.hom ≫ (U.inclusion ≫ P.positive.inclusion).hom.hom))
        (extendVector R v) = extendVector R v
      simpa only [Category.assoc] using hf
    let m := (pairing P.torus.group χ c).toNat
    have hm : pairing P.torus.group χ c = (m : ℤ) :=
      (Int.toNat_of_nonneg (hdom α c hD)).symm
    have hlt : m < p ^ r := by
      have h := hrestricted α c hD
      rw [hm] at h
      exact_mod_cast h
    have hm' : pairing P.torus.group χ D.coroot = (m : ℤ) :=
      (congrArg (pairing P.torus.group χ) hcor).trans hm
    obtain ⟨hdegree, _⟩ := oppositeRootPolynomial P.torus α.val.val χ ρ D v hfix S.primitive.2.2 m hm'
    have hx (a : k) : rootPoint x K₀ a ∈ H := by
      have h (b : k) : act ρ K₀ (rootPoint x K₀ b) v = v := by
        exact mem_fixedSpace.mp hfix K₀ ((testSpec k).map (CommAlgCat.ofHom (Polynomial.aeval b)).op)
      apply memH
      · rw [h]; exact hv
      · rw [← rootPoint_neg, h]; exact hv
    have hy (a : k) : rootPoint y K₀ a ∈ H := by
      have h (b : k) : act ρ K₀ (rootPoint y K₀ b) v ∈ W :=
        rootOrbit_mem p r S hF y (fun i ↦ (hdegree i).trans_lt hlt) b
      apply memH _ (h a)
      rw [← rootPoint_neg]
      exact h (-a)
    rw [representativePoint, D.representative_word, rankOneWord]
    exact H.mul_mem (H.mul_mem (hx _) (hy _)) (hx _)
  have hstable : Specs.PrimitiveLine.IsStable ρ W :=
    stable_of_rational_points S M fun g w hw ↦
      (show g ∈ H by rw [htop]; trivial) w hw |>.1
  have hW : W = ⊤ := by
    rcases S.simple.2 W hstable with h | h
    · exact False.elim (S.primitive.1 ((Submodule.mem_bot k).mp (h ▸ hv)))
    · exact h
  dsimp only
  intro w
  have hw : S.socleBasis.equivFun w ∈ W := by rw [hW]; trivial
  obtain ⟨x, ⟨d, hd⟩, hx⟩ := Submodule.mem_map.mp hw
  have he : x = w := S.socleBasis.equivFun.injective hx
  refine ⟨d, ?_⟩
  exact (tensorEvaluation_apply _ _).symm.trans (hd.trans he)

end

end LinearAlgebraicGroups.Representation.RestrictedCyclicity
