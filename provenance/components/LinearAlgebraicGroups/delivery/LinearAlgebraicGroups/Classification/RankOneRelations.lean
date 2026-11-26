import Specs.LinearAlgebraicGroups.Classification.RankOneRelations
import LinearAlgebraicGroups.RootData.CharacterPairing
import LinearAlgebraicGroups.RootData.RankOneFlag
import LinearAlgebraicGroups.RootData.RootGroups
import LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.GroupTheory.Commutator.Basic

import LinearAlgebraicGroups.RootData.OrderedRootProducts
open AlgebraicGeometry CategoryTheory Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Classification.RankOneRelations

open _root_.LinearAlgebraicGroups.Specs
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots characterValue pairing)
open Specs.RootGroups (AdditiveLine CorootReflection HasScalarAction rankOneWord rootPoint)
open LinearAlgebraicGroups.CocharacterDynamics

open private unitPointHom unitPointHom_apply from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1400000

variable {k : Type u} [Field k] {G : GroupScheme k}

private def additivePointEquiv (A : AdditiveLine k) (R : TestAlgebra k) :
    letI := A.operations.hopf
    WithConv (Polynomial k →ₐ[k] R) ≃* GroupPoints A.group R := by
  letI := A.operations.hopf
  exact Spec.mapMulEquiv (R := k) (S := Polynomial k) (T := R)

private theorem additivePointEquiv_eval (A : AdditiveLine k) (R : TestAlgebra k) (a : R) :
    additivePointEquiv A R (toConv (Polynomial.aeval a)) = rootPoint (𝟙 A.group) R a := by
  change _ = _ ≫ 𝟙 A.group.X
  rw [Category.comp_id]
  rfl

private theorem additivePointEquiv_mul_X (A : AdditiveLine k) (R : TestAlgebra k) (a b : R) :
    letI := A.operations.hopf
    ((toConv (Polynomial.aeval a : Polynomial k →ₐ[k] R) *
      toConv (Polynomial.aeval b : Polynomial k →ₐ[k] R)).ofConv : Polynomial k →ₐ[k] R) =
        Polynomial.aeval (a + b) := by
  letI := A.operations.hopf
  apply Polynomial.algHom_ext
  rw [AlgHom.convMul_def]
  change Algebra.TensorProduct.lmul' k (((Algebra.TensorProduct.map
    (Polynomial.aeval a) (Polynomial.aeval b)) (A.operations.delta Polynomial.X))) = _
  rw [A.comultiplication]
  simp

private theorem rootPoint_add {A : AdditiveLine k} (x : A.group ⟶ G)
    (R : TestAlgebra k) (a b : R) :
    rootPoint x R (a + b) = rootPoint x R a * rootPoint x R b := by
  letI := A.operations.hopf
  let f : GroupPoints A.group R →* GroupPoints G R := (((groupPointsFunctor k).map x).app R).hom
  have he (s : R) : f (additivePointEquiv A R (toConv (Polynomial.aeval s))) =
      rootPoint x R s := by
    rw [additivePointEquiv_eval]
    change (_ ≫ 𝟙 A.group.X) ≫ x.hom.hom = _
    simp only [Category.comp_id]
    rfl
  rw [← he, ← he, ← he, ← map_mul, ← map_mul]
  simpa only [toConv_ofConv] using congrArg (fun p => f (additivePointEquiv A R (toConv p)))
    (additivePointEquiv_mul_X A R a b).symm

private theorem rootPoint_zero {A : AdditiveLine k} (x : A.group ⟶ G) (R : TestAlgebra k) :
    rootPoint x R 0 = 1 := by
  have h := rootPoint_add x R 0 0
  have e : rootPoint x R 0 * 1 = rootPoint x R 0 * rootPoint x R 0 := by simpa using h
  exact (mul_left_cancel e).symm

private theorem rootPoint_neg {A : AdditiveLine k} (x : A.group ⟶ G)
    (R : TestAlgebra k) (s : R) :
    rootPoint x R (-s) = (rootPoint x R s)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← rootPoint_add, neg_add_cancel, rootPoint_zero]

private theorem mapPoints_rootPoint {A : AdditiveLine k} (x : A.group ⟶ G)
    {R S : TestAlgebra k} (f : R ⟶ S) (a : R) :
    mapPoints f (rootPoint x R a) = rootPoint x S (f.hom a) := by
  unfold rootPoint
  rw [mapPoints, ← Category.assoc, ← Functor.map_comp]
  congr 2
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext
  simp

private theorem mapPoints_injective (hG : IsAffine G.X.left)
    {R S : TestAlgebra k} (f : R ⟶ S) (hf : Function.Injective f.hom) :
    Function.Injective (mapPoints (X := G.X) f) := by
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr hG
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  intro p q hpq
  let a := F.preimage (p ≫ e.inv)
  let b := F.preimage (q ≫ e.inv)
  have ha : (testSpec k).map a = p ≫ e.inv := F.map_preimage _
  have hb : (testSpec k).map b = q ≫ e.inv := F.map_preimage _
  have hab : f.op ≫ a = f.op ≫ b := by
    apply F.map_injective
    change (testSpec k).map (_ ≫ _) = (testSpec k).map (_ ≫ _)
    rw [Functor.map_comp, Functor.map_comp, ha, hb]
    simpa only [mapPoints, Category.assoc] using congrArg (· ≫ e.inv) hpq
  have heq : a = b := by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro s
    apply hf
    exact DFunLike.congr_fun (congrArg (fun p ↦ p.unop.hom) hab) s
  apply (cancel_mono e.inv).mp
  rw [← ha, ← hb, heq]

private abbrev pointMap (R : TestAlgebra k) {H : GroupScheme k} (f : H ⟶ G) :
    GroupPoints H R →* GroupPoints G R :=
  ((groupPointsFunctor k).map f).app R |>.hom

private abbrev changeRing {R S : TestAlgebra k} (f : R ⟶ S) :
    GroupPoints G R →* GroupPoints G S :=
  ((groupPointsFunctor k).obj G).map f |>.hom

private theorem changeRing_rootPoint {A : AdditiveLine k} (x : A.group ⟶ G)
    {R S : TestAlgebra k} (f : R ⟶ S) (a : R) :
    changeRing f (rootPoint x R a) = rootPoint x S (f.hom a) :=
  mapPoints_rootPoint x f a

private theorem changeRing_rankOneWord {A : AdditiveLine k} (xp xn : A.group ⟶ G)
    {R S : TestAlgebra k} (f : R ⟶ S) (a : Rˣ) :
    changeRing f (rankOneWord xp xn R a) =
      rankOneWord xp xn S (Units.map f.hom.toMonoidHom a) := by
  have hc : (↑(Units.map f.hom.toMonoidHom a) : S) = f.hom (a : R) := rfl
  have hi : (↑(Units.map f.hom.toMonoidHom a)⁻¹ : S) = f.hom (↑a⁻¹ : R) := rfl
  simp only [rankOneWord, map_mul, changeRing_rootPoint, map_neg, hc, hi]

private theorem rankOneWord_inv {A : AdditiveLine k} (xp xn : A.group ⟶ G)
    (R : TestAlgebra k) (a : Rˣ) :
    (rankOneWord xp xn R a)⁻¹ = rankOneWord xp xn R (-a) := by
  simp only [rankOneWord, Units.val_neg, inv_neg, neg_neg, mul_inv_rev, rootPoint_neg]
  group

private def torusPointHom (T : ClosedSubgroup G) (c : Cocharacter T.group) (R : TestAlgebra k) :
    Rˣ →* GroupPoints G R :=
  (pointMap R (c ≫ T.inclusion)).comp (unitPointHom R)

private theorem torusPointHom_apply (T : ClosedSubgroup G) (c : Cocharacter T.group)
    (R : TestAlgebra k) (a : Rˣ) :
    torusPointHom T c R a = cocharacterPoint c R a ≫ T.inclusion.hom.hom := by
  simp only [torusPointHom, MonoidHom.comp_apply, unitPointHom_apply]
  rfl

private theorem mapPoints_torusPointHom (T : ClosedSubgroup G) (c : Cocharacter T.group)
    {R S : TestAlgebra k} (f : R ⟶ S) (a : Rˣ) :
    changeRing (G := G) f (torusPointHom T c R a) =
      torusPointHom T c S (Units.map f.hom.toMonoidHom a) := by
  rw [torusPointHom_apply, torusPointHom_apply, ← mapPoints_cocharacterPoint]
  rfl

private theorem rankOneScalar {T : ClosedSubgroup G} {α : Character T.group}
    {A : AdditiveLine k} {xp xn : A.group ⟶ G} (r : CorootReflection T α xp xn)
    (hp : HasScalarAction T α xp) (R : TestAlgebra k) (c : Rˣ) (a : R) :
    torusPointHom T r.coroot R c * rootPoint xp R a *
      (torusPointHom T r.coroot R c)⁻¹ = rootPoint xp R ((c : R) ^ 2 * a) := by
  have h := hp R (cocharacterPoint r.coroot R c) a
  have he := (RootData.CharacterPairing.characterPairingComposition
    T.group α r.coroot).2 R c
  rw [r.root_pairing] at he
  rw [torusPointHom_apply]
  simpa only [he, zpow_ofNat, Units.val_pow_eq_pow_val] using h

private theorem word_eq_torus_mul {T : ClosedSubgroup G} {α : Character T.group}
    {A : AdditiveLine k} {xp xn : A.group ⟶ G} (r : CorootReflection T α xp xn)
    (R : TestAlgebra k) (c : Rˣ) :
    rankOneWord xp xn R c = torusPointHom T r.coroot R c * rankOneWord xp xn R 1 := by
  rw [torusPointHom_apply, r.coroot_word]
  group

private theorem word_ratio {T : ClosedSubgroup G} {α : Character T.group}
    {A : AdditiveLine k} {xp xn : A.group ⟶ G} (r : CorootReflection T α xp xn)
    (R : TestAlgebra k) (c d : Rˣ) :
    (rankOneWord xp xn R c)⁻¹ * rankOneWord xp xn R d =
      torusPointHom T r.coroot R (c / d) := by
  have hd : (rankOneWord xp xn R (-d))⁻¹ = rankOneWord xp xn R d := by
    rw [rankOneWord_inv, neg_neg]
  rw [rankOneWord_inv xp xn R c, ← hd, word_eq_torus_mul r R (-c),
    word_eq_torus_mul r R (-d)]
  have h : (-c) / (-d) = c / d := by apply Units.ext; simp [div_eq_mul_inv]
  rw [← h, map_div, div_eq_mul_inv]
  group

private theorem word_one_square {T : ClosedSubgroup G} {α : Character T.group}
    {A : AdditiveLine k} {xp xn : A.group ⟶ G} (r : CorootReflection T α xp xn)
    (R : TestAlgebra k) :
    (rankOneWord xp xn R 1) ^ 2 = torusPointHom T r.coroot R (-1) := by
  have h := word_ratio r R (-1) 1
  simpa only [rankOneWord_inv, neg_neg, div_one, pow_two] using h

section FieldCalculations

variable {T : ClosedSubgroup G} {α : Character T.group}
  {A : AdditiveLine k} {xp xn : A.group ⟶ G}
  (r : CorootReflection T α xp xn) (hp : HasScalarAction T α xp)
  (K : Type u) [Field K] [Algebra k K]

local notation "Rₖ" => CommAlgCat.of k K
local notation "X₊" => rootPoint xp Rₖ
local notation "X₋" => rootPoint xn Rₖ
local notation "H" => torusPointHom T r.coroot Rₖ
local notation "W" => rankOneWord xp xn Rₖ

private theorem neg_root_word (v : K) (hv : v ≠ 0) :
    X₋ v = X₊ v⁻¹ * W (Units.mk0 (-v⁻¹) (by simp [hv])) * X₊ v⁻¹ := by
  let b : Kˣ := Units.mk0 (-v⁻¹) (by simp [hv])
  have hb : (b : K) = -v⁻¹ := rfl
  have hb' : -(↑b⁻¹ : K) = v := by rw [Units.val_inv_eq_inv_val, hb, inv_neg, inv_inv, neg_neg]
  change X₋ v = X₊ v⁻¹ * W b * X₊ v⁻¹
  unfold rankOneWord
  change X₋ v = X₊ v⁻¹ * (X₊ (b : K) * X₋ (-(↑b⁻¹ : K)) * X₊ (b : K)) * X₊ v⁻¹
  rw [hb, hb', rootPoint_neg]
  group

include r hp

private theorem gauss_over_field (u v : K) (hv : v ≠ 0) (c : Kˣ)
    (hc : (c : K) = 1 + u * v) :
    X₊ u * X₋ v = X₋ (v / (c : K)) * H c * X₊ (u / (c : K)) := by
  let a : Kˣ := Units.mk0 (-v⁻¹) (by simp [hv])
  let b : Kˣ := Units.mk0 (-(c : K) / v) (by simp [hv])
  have hb : b / a = c := by
    apply Units.ext
    rw [Units.val_div_eq_div_val]
    change (-(c : K) / v) / (-v⁻¹) = (c : K)
    field_simp
  have hL : X₊ u * X₋ v = X₊ ((c : K) / v) * W a * X₊ v⁻¹ := by
    rw [neg_root_word K v hv, ← mul_assoc, ← mul_assoc, ← rootPoint_add]
    congr 3
    rw [hc]
    field_simp
    ring
  have hR : X₋ (v / (c : K)) =
      X₊ ((c : K) / v) * W b * X₊ ((c : K) / v) := by
    have hv' : v / (c : K) ≠ 0 := div_ne_zero hv (Units.ne_zero c)
    have hunit : Units.mk0 (-(v / (c : K))⁻¹) (by simp [hv]) = b := by
      apply Units.ext
      change -(v / (c : K))⁻¹ = -(c : K) / v
      rw [inv_div, neg_div]
    rw [neg_root_word (xp := xp) K _ hv', hunit, inv_div]
  have hwa : W a = W b * H c := by
    have h := word_ratio r Rₖ b a
    rw [hb] at h
    rw [← h]
    group
  have hmove : X₊ ((c : K) / v) * H c * X₊ (u / (c : K)) =
      H c * X₊ v⁻¹ := by
    have e := rankOneScalar r hp Rₖ c (u / (c : K))
    have he : H c * X₊ (u / (c : K)) = X₊ ((c : K) ^ 2 * (u / (c : K))) * H c := by
      rw [← e]
      group
    have hev := rankOneScalar r hp Rₖ c v⁻¹
    have hev' : H c * X₊ v⁻¹ = X₊ ((c : K) ^ 2 * v⁻¹) * H c := by
      rw [← hev]
      group
    rw [mul_assoc, he, hev', ← mul_assoc, ← rootPoint_add]
    congr 2
    -- c = 1 + uv gives c/v + cu = c²/v.
    have h' : (c : K) / v + (c : K) ^ 2 * (u / (c : K)) = (c : K) ^ 2 * v⁻¹ := by
      have hcn := Units.ne_zero c
      field_simp
      linear_combination -hc
    exact h'
  rw [hL, hR, hwa]
  simp only [mul_assoc] at hmove ⊢
  rw [hmove]

private theorem reverse_gauss_over_field (u v : K) (hv : v ≠ 0) (c : Kˣ)
    (hc : (c : K) = 1 + u * v) :
    X₋ v * X₊ u = X₊ (u / (c : K)) * (H c)⁻¹ * X₋ (v / (c : K)) := by
  have e := gauss_over_field r hp K (-u) (-v) (neg_ne_zero.mpr hv) c (by simpa using hc)
  have e' := congrArg Inv.inv e
  simp only [mul_inv_rev, neg_div, mul_assoc] at e'
  rw [rootPoint_neg xn Rₖ v, rootPoint_neg xp Rₖ u, rootPoint_neg xp Rₖ (u / (c : K)),
    rootPoint_neg xn Rₖ (v / (c : K))] at e'
  simpa only [inv_inv, mul_assoc] using e'

private theorem conjugation_over_field (u : K) (hu : u ≠ 0) (hu1 : 1 - u ≠ 0) :
    W 1 * X₊ u * (W 1)⁻¹ = X₋ (-u) := by
  let c : Kˣ := Units.mk0 (-u) (neg_ne_zero.mpr hu)
  let d : Kˣ := Units.mk0 (1 - u) hu1
  have hc : (c : K) = -u := rfl
  have hd : (d : K) = 1 + (c : K) := by rw [hc]; exact sub_eq_add_neg 1 u
  have hn : W 1 = X₊ 1 * X₋ (-1) * X₊ 1 := by simp [rankOneWord]
  have h₁ : W 1 * X₊ u = X₊ (1 / (c : K)) * (H c)⁻¹ * X₋ (-1 / (c : K)) := by
    have e := reverse_gauss_over_field r hp K (1 + u) (-1) (neg_ne_zero.mpr one_ne_zero) c
      (by rw [hc]; ring)
    rw [hn, mul_assoc, mul_assoc, ← rootPoint_add, e]
    simp only [← mul_assoc, ← rootPoint_add]
    congr 3
    have hcn := Units.ne_zero c
    field_simp
    linear_combination hc
  have h₂ : X₋ (c : K) * W 1 =
      X₊ (1 / (d : K)) * (H d)⁻¹ * X₋ (-1 / (d : K)) * X₊ 1 := by
    have e := reverse_gauss_over_field r hp K 1 (c : K) (Units.ne_zero c) d (by simpa using hd)
    have eq₁ : (c : K) / (d : K) + -1 = -1 / (d : K) := by
      have hdn := Units.ne_zero d
      field_simp
      linear_combination -hd
    calc
      X₋ (c : K) * W 1 = (X₋ (c : K) * X₊ 1) * (X₋ (-1) * X₊ 1) := by
        rw [hn]
        group
      _ = X₊ (1 / (d : K)) * (H d)⁻¹ * (X₋ ((c : K) / (d : K)) * X₋ (-1)) * X₊ 1 := by
        rw [e]
        group
      _ = _ := by rw [← rootPoint_add, eq₁]
  have h₃ := reverse_gauss_over_field r hp K 1 (-1 / (d : K))
      (div_ne_zero (neg_ne_zero.mpr one_ne_zero) (Units.ne_zero d)) (c / d)
      (by
        rw [Units.val_div_eq_div_val]
        change (c : K) / (d : K) = 1 + 1 * (-1 / (d : K))
        have hdn := Units.ne_zero d
        field_simp
        linear_combination -hd)
  have h_scalar : (H d)⁻¹ * X₊ (1 / (↑(c / d) : K)) =
      X₊ ((↑d⁻¹ : K)^2 * (1 / (↑(c / d) : K))) * (H d)⁻¹ := by
    have hs := rankOneScalar r hp Rₖ d⁻¹ (1 / (↑(c / d) : K))
    rw [map_inv] at hs
    rw [← hs]
    group
  have hargs : 1 / (d : K) + (↑d⁻¹ : K)^2 * (1 / (↑(c / d) : K)) = 1 / (c : K) := by
    simp only [Units.val_inv_eq_inv_val, Units.val_div_eq_div_val]
    have hc' := Units.ne_zero c
    have hd' := Units.ne_zero d
    field_simp
    linear_combination -hd
  have hargs' : (-1 / (d : K)) / (↑(c / d) : K) = -1 / (c : K) := by
    simp only [Units.val_div_eq_div_val]
    have hc' := Units.ne_zero c
    have hd' := Units.ne_zero d
    field_simp
  have htor : (H d)⁻¹ * (H (c / d))⁻¹ = (H c)⁻¹ := by
    rw [← mul_inv_rev, ← map_mul, div_mul_cancel]
  apply (mul_inv_eq_iff_eq_mul).mpr
  rw [← hc, h₁, h₂, mul_assoc (X₊ (1 / (d : K)) * (H d)⁻¹), h₃]
  rw [hargs']
  symm
  calc
    _ = X₊ (1 / (d : K)) * ((H d)⁻¹ * X₊ (1 / (↑(c / d) : K))) *
        (H (c / d))⁻¹ * X₋ (-1 / (c : K)) := by group
    _ = (X₊ (1 / (d : K)) * X₊ ((↑d⁻¹ : K)^2 * (1 / (↑(c / d) : K)))) *
        ((H d)⁻¹ * (H (c / d))⁻¹) * X₋ (-1 / (c : K)) := by
      rw [h_scalar]
      group
    _ = _ := by rw [← rootPoint_add, hargs, htor]

end FieldCalculations

private theorem fin_cases_one {A : Type*} (a b : A) :
    Fin.cases a (fun _ : Fin 1 => b) (1 : Fin 2) = b := rfl

private def bivariateEvaluation {A : Type u} [CommRing A] [Algebra k A] (a b : A) :
    MvPolynomial (Fin 2) k →ₐ[k] A :=
  MvPolynomial.aeval (Fin.cases a (fun _ : Fin 1 => b))

private theorem bivariateEvaluation_X_zero {A : Type u} [CommRing A] [Algebra k A] (a b : A) :
    bivariateEvaluation (k := k) a b (MvPolynomial.X 0) = a := by
  rw [bivariateEvaluation, MvPolynomial.aeval_X, Fin.cases_zero]

private theorem bivariateEvaluation_X_one {A : Type u} [CommRing A] [Algebra k A] (a b : A) :
    bivariateEvaluation (k := k) a b (MvPolynomial.X 1) = b := by
  rw [bivariateEvaluation, MvPolynomial.aeval_X, fin_cases_one]

section Descent

variable {T : ClosedSubgroup G} {α : Character T.group}
  {A : AdditiveLine k} {xp xn : A.group ⟶ G}
  (r : CorootReflection T α xp xn) (hp : HasScalarAction T α xp)

private theorem gauss_specialize {R S : TestAlgebra k}
    (f : R ⟶ S) (u v : R) (c : Rˣ)
    (h : rootPoint xp R u * rootPoint xn R v =
      rootPoint xn R (v * (↑c⁻¹ : R)) * torusPointHom T r.coroot R c *
        rootPoint xp R (u * (↑c⁻¹ : R))) :
    rootPoint xp S (f.hom u) * rootPoint xn S (f.hom v) =
      rootPoint xn S (f.hom v * (↑(Units.map f.hom.toMonoidHom c)⁻¹ : S)) *
        torusPointHom T r.coroot S (Units.map f.hom.toMonoidHom c) *
        rootPoint xp S (f.hom u * (↑(Units.map f.hom.toMonoidHom c)⁻¹ : S)) := by
  have e := congrArg (changeRing (G := G) f) h
  have hi : (↑(Units.map f.hom.toMonoidHom c)⁻¹ : S) = f.hom (↑c⁻¹ : R) := rfl
  simpa only [map_mul, mapPoints_torusPointHom, changeRing_rootPoint, hi] using e

include r hp

private theorem gauss_of_injection (hG : IsAffine G.X.left)
    (R : TestAlgebra k) (u v : R) (c : Rˣ) (hc : (c : R) = 1 + u * v)
    (K : Type u) [Field K] [Algebra k K] (f : R ⟶ CommAlgCat.of k K)
    (hf : Function.Injective f.hom) (hv : v ≠ 0) :
    rootPoint xp R u * rootPoint xn R v =
      rootPoint xn R (v * (↑c⁻¹ : R)) * torusPointHom T r.coroot R c *
        rootPoint xp R (u * (↑c⁻¹ : R)) := by
  let c' := Units.map f.hom.toMonoidHom c
  have hcz : (c' : K) = 1 + f.hom u * f.hom v := by
    change f.hom (c : R) = _
    rw [hc, map_add, map_one, map_mul]
  have hv' : f.hom v ≠ 0 := fun e => hv (hf (e.trans (map_zero f.hom).symm))
  have e := gauss_over_field r hp K (f.hom u) (f.hom v) hv' c' hcz
  have hi : (↑c'⁻¹ : K) = f.hom (↑c⁻¹ : R) := rfl
  apply mapPoints_injective hG f hf
  change changeRing (G := G) f (_ * _) = changeRing (G := G) f (_ * _ * _)
  simp only [map_mul, changeRing_rootPoint]
  rw [mapPoints_torusPointHom T r.coroot f c]
  rw [div_eq_mul_inv, div_eq_mul_inv, ← Units.val_inv_eq_inv_val, hi] at e
  exact e

private theorem gauss (hG : IsAffine G.X.left) (R : TestAlgebra k) (u v : R) (c : Rˣ)
    (hc : (c : R) = 1 + u * v) :
    rootPoint xp R u * rootPoint xn R v =
      rootPoint xn R (v * (↑c⁻¹ : R)) * torusPointHom T r.coroot R c *
        rootPoint xp R (u * (↑c⁻¹ : R)) := by
  let P := MvPolynomial (Fin 2) k
  let x : P := MvPolynomial.X 0
  let y : P := MvPolynomial.X 1
  let d : P := 1 + x * y
  have hd : d ≠ 0 := by
    intro h
    let e : P →ₐ[k] k := MvPolynomial.aeval (fun _ : Fin 2 => 0)
    have eq := congrArg e h
    change e (1 + x * y) = e 0 at eq
    rw [map_add, map_mul, map_one, map_zero] at eq
    have e₀ : e x = 0 := MvPolynomial.aeval_X (fun _ : Fin 2 => (0 : k)) 0
    have e₁ : e y = 0 := MvPolynomial.aeval_X (fun _ : Fin 2 => (0 : k)) 1
    rw [e₀, e₁, mul_zero, add_zero] at eq
    exact one_ne_zero eq
  let L := Localization.Away d
  letI : IsDomain L := Localization.Away.isDomain hd
  let F := FractionRing L
  let j : P →ₐ[k] L := IsScalarTower.toAlgHom k P L
  let f : CommAlgCat.of k L ⟶ CommAlgCat.of k F :=
    CommAlgCat.ofHom (IsScalarTower.toAlgHom k L F)
  have hj : Function.Injective j :=
    IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors hd)
  have hdunit : IsUnit (j d) := IsLocalization.Away.algebraMap_isUnit (S := L) d
  let C := hdunit.unit
  have hCd : (C : L) = j d := hdunit.unit_spec
  have hC : (C : L) = 1 + j x * j y := hCd.trans (by
    change j (1 + x * y) = _
    rw [map_add, map_one, map_mul])
  have hy₀ : y ≠ 0 := MvPolynomial.X_ne_zero (R := k) (1 : Fin 2)
  have hyp : rootPoint xp (CommAlgCat.of k L) (j x) * rootPoint xn (CommAlgCat.of k L) (j y) =
      rootPoint xn (CommAlgCat.of k L) (j y * (↑C⁻¹ : L)) *
        torusPointHom T r.coroot (CommAlgCat.of k L) C *
        rootPoint xp (CommAlgCat.of k L) (j x * (↑C⁻¹ : L)) := by
    exact gauss_of_injection r hp hG (CommAlgCat.of k L) (j x) (j y) C hC F f
      (IsFractionRing.injective L F) (fun e =>
        hy₀ (hj (e.trans j.map_zero.symm)))
  let a : P →ₐ[k] R := bivariateEvaluation u v
  have ax : a x = u := bivariateEvaluation_X_zero (k := k) u v
  have ay : a y = v := bivariateEvaluation_X_one (k := k) u v
  have ad : a d = (c : R) := by
    change a (1 + x * y) = _
    rw [map_add, map_one, map_mul, ax, ay, hc]
  have had : IsUnit (a d) := by rw [ad]; exact c.isUnit
  let g : L →ₐ[k] R := IsLocalization.Away.liftAlgHom d had
  have hjg (p : P) : g (j p) = a p := IsLocalization.Away.lift_eq d had p
  have gc : Units.map g.toMonoidHom C = c := by
    apply Units.ext
    change g ((C : L)) = _
    exact (congrArg g hCd).trans ((hjg d).trans ad)
  let g' : CommAlgCat.of k L ⟶ R := CommAlgCat.ofHom g
  have gu : g'.hom (j x) = u := (hjg x).trans ax
  have gv : g'.hom (j y) = v := (hjg y).trans ay
  have gc' : Units.map g'.hom.toMonoidHom C = c := gc
  have e := gauss_specialize r g' (j x) (j y) C hyp
  rw [gu, gv, gc'] at e
  exact e

private theorem conjugation (hG : IsAffine G.X.left) (R : TestAlgebra k) (u : R) :
    rankOneWord xp xn R 1 * rootPoint xp R u * (rankOneWord xp xn R 1)⁻¹ =
      rootPoint xn R (-u) := by
  let P := Polynomial k
  let F := FractionRing P
  let f : CommAlgCat.of k P ⟶ CommAlgCat.of k F := CommAlgCat.ofHom (IsScalarTower.toAlgHom k P F)
  have hf : Function.Injective f.hom := IsFractionRing.injective P F
  have hyp : rankOneWord xp xn (CommAlgCat.of k P) 1 *
      rootPoint xp (CommAlgCat.of k P) Polynomial.X *
      (rankOneWord xp xn (CommAlgCat.of k P) 1)⁻¹ =
      rootPoint xn (CommAlgCat.of k P) (-Polynomial.X) := by
    apply mapPoints_injective hG f hf
    change changeRing (G := G) f (_ * _ * _⁻¹) = changeRing (G := G) f _
    simp only [map_mul, map_inv, changeRing_rankOneWord, changeRing_rootPoint, map_one]
    rw [map_neg f.hom (Polynomial.X : P)]
    have h₀ : f.hom (Polynomial.X : P) ≠ 0 := fun e =>
      Polynomial.X_ne_zero (hf (e.trans (map_zero f.hom).symm))
    have h₁ : 1 - f.hom (Polynomial.X : P) ≠ 0 := by
      intro e
      have hX : (Polynomial.X : P) ≠ 1 := by simpa only [Polynomial.C_1] using
        (Polynomial.X_ne_C (R := k) 1)
      apply hX
      apply hf
      rw [map_one]
      exact (sub_eq_zero.mp e).symm
    exact conjugation_over_field r hp F (f.hom Polynomial.X) h₀ h₁
  let g : CommAlgCat.of k P ⟶ R := CommAlgCat.ofHom (Polynomial.aeval u)
  have e := congrArg (changeRing (G := G) g) hyp
  have heval : g.hom (Polynomial.X : P) = u := Polynomial.aeval_X u
  have hneg : g.hom (-(Polynomial.X : P)) = -u :=
    (map_neg g.hom _).trans (congrArg Neg.neg heval)
  simpa only [map_mul, map_inv, changeRing_rankOneWord, changeRing_rootPoint, map_one,
    heval, hneg] using e

end Descent

private theorem representative_eq_word {T : ClosedSubgroup G} {α : Character T.group}
    {A : AdditiveLine k} {xp xn : A.group ⟶ G} (r : CorootReflection T α xp xn)
    (R : TestAlgebra k) : (toUnit _ ≫ r.representative : GroupPoints G R) =
      rankOneWord xp xn R 1 := by
  let f : CommAlgCat.of k k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  have e := congrArg (changeRing (G := G) f) r.representative_word
  change mapPoints f (toUnit _ ≫ r.representative) = _ at e
  rw [show mapPoints f (toUnit _ ≫ r.representative) =
      (toUnit _ ≫ r.representative : GroupPoints G R) by
    change _ ≫ _ ≫ _ = _
    rw [← Category.assoc, toUnit_unique ((testSpec k).map f.op ≫ toUnit _) (toUnit _)]
    rfl] at e
  simpa only [changeRing_rankOneWord, map_one] using e

open Specs.OrderedRootProducts (BorelRadicalProduct ContractingProduct RegularRootCell)

/-- The opposite-root formulas are scheme identities in the linked coordinates. -/
theorem oppositeRootRelations_conditional
    (_ : BorelRadicalProduct.{u}) (_ : ContractingProduct.{u}) (_ : RegularRootCell.{u}) :
    Specs.RankOneRelations.OppositeRootRelations.{u} := by
  intro k _ G _ T _ _ α _ A xp xn r hp _ R
  refine ⟨?_, ?_⟩
  · intro u v c hc
    have e := gauss r hp G.property.1 R u v c hc
    rw [torusPointHom_apply] at e
    exact e
  · dsimp only
    rw [representative_eq_word r R, ← torusPointHom_apply]
    exact ⟨word_one_square r R, conjugation r hp G.property.1 R⟩

section RootProducts

open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers (positiveRoots)
open Specs.OrderedRootProducts (Enumerates Parametrizes RootSubgroupFamily product rootProduct)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.RootGroups (IsRootSubgroup Proportional)

private theorem simultaneous_positive {T : GroupScheme k} (hT : IsSplitTorus T)
    (α β : Character T) (hind : ¬ Proportional α β)
    (a b : Cocharacter T) (ha : 0 < pairing T α a) (hb : 0 < pairing T β b) :
    ∃ cochar : Cocharacter T, 0 < pairing T α cochar ∧ 0 < pairing T β cochar := by
  obtain ⟨hcomm, h⟩ := RootData.CharacterPairing.perfectCharacterPairing T hT
  letI := hcomm
  obtain ⟨_, _, _, _, P, hperf, hP⟩ := h
  let X := Additive (Character T)
  let Y := Additive (Cocharacter T)
  let f : Y →ₗ[ℤ] ℤ := P (Additive.ofMul α)
  let g : Y →ₗ[ℤ] ℤ := P (Additive.ofMul β)
  let a' : Y := Additive.ofMul a
  let b' : Y := Additive.ofMul b
  have hfa : 0 < f a' := (hP α a).symm ▸ ha
  have hgb : 0 < g b' := (hP β b).symm ▸ hb
  have hd : ∃ y : Y, f a' * g y - g a' * f y ≠ 0 := by
    by_contra! hh
    have hga : g a' ≠ 0 := by
      intro hz
      have h := hh b'
      simp only [hz, zero_mul, sub_zero] at h
      exact (mul_ne_zero (ne_of_gt hfa) (ne_of_gt hgb)) h
    have e : f a' • (Additive.ofMul β : X) = g a' • (Additive.ofMul α : X) := by
      apply hperf.bijective_left.injective
      ext y
      simp only [map_smul, LinearMap.smul_apply, zsmul_eq_mul]
      exact sub_eq_zero.mp (hh y)
    exact hind ⟨g a', f a', hga, ne_of_gt hfa,
      congrArg Additive.toMul e.symm⟩
  obtain ⟨y, hy⟩ := hd
  let z₀ : Y := f a' • y - f y • a'
  have hf₀ : f z₀ = 0 := by
    simp only [z₀, map_sub, map_smul, Int.zsmul_eq_mul]
    ring
  have hg₀ : g z₀ ≠ 0 := by
    simp only [z₀, map_sub, map_smul, Int.zsmul_eq_mul]
    rwa [mul_comm (f y) (g a')]
  let z : Y := g z₀ • z₀
  have hfz : f z = 0 := by simp only [z, map_smul, hf₀, smul_zero]
  have hgz : 0 < g z := by
    simpa only [z, map_smul, Int.zsmul_eq_mul] using mul_self_pos.mpr hg₀
  let w : Y := a' + (|g a'| + 1) • z
  refine ⟨Additive.toMul w, ?_, ?_⟩
  · rw [← hP]
    change 0 < f w
    simpa only [w, map_add, map_smul, hfz, smul_zero, add_zero] using hfa
  · rw [← hP]
    change 0 < g w
    simp only [w, map_add, map_zsmul, Int.zsmul_eq_mul]
    have h₁ : 1 ≤ g z := by omega
    have h₂ : 0 ≤ |g a'| := abs_nonneg _
    have h₃ : g a' + |g a'| ≥ 0 := by have := neg_abs_le (g a'); omega
    nlinarith [mul_nonneg (show 0 ≤ |g a'| + 1 by omega) (show 0 ≤ g z - 1 by omega)]

private def rootCoordinates (A : AdditiveLine k) (R : TestAlgebra k) :
    R ≃ GroupPoints A.group R := by
  letI := A.operations.hopf
  exact (Polynomial.aevalEquiv (R := k) (A := R)).trans
    (WithConv.equiv _ |>.symm.trans (additivePointEquiv A R).toEquiv)


private theorem rootPoint_contraction {T : ClosedSubgroup G} {α : Character T.group}
    {A : AdditiveLine k} {x : A.group ⟶ G} (hx : HasScalarAction T α x)
    (cochar : Cocharacter T.group) (hcochar : 0 < pairing T.group α cochar)
    (R : TestAlgebra k) (a : R) :
    HasLimit (cochar ≫ T.inclusion) (rootPoint x R a) 1 := by
  let n := (pairing T.group α cochar).toNat
  have hn : (n : ℤ) = pairing T.group α cochar := Int.toNat_of_nonneg (le_of_lt hcochar)
  have hn' : n ≠ 0 := by omega
  refine ⟨rootPoint x (polynomialAlgebra R) (Polynomial.X ^ n * Polynomial.C a), ?_, ?_⟩
  · rw [mapPoints_rootPoint]
    have e := hx (laurentAlgebra R) (cocharacterPoint cochar (laurentAlgebra R) (laurentParameter R))
      ((laurentConstants R).hom a)
    have hχ := (RootData.CharacterPairing.characterPairingComposition T.group α cochar).2
      (laurentAlgebra R) (laurentParameter R)
    rw [← hn, zpow_natCast] at hχ
    have hL : (polynomialToLaurent R).hom (Polynomial.X ^ n * Polynomial.C a) =
        characterValue α (laurentAlgebra R)
          (cocharacterPoint cochar (laurentAlgebra R) (laurentParameter R)) *
          (laurentConstants R).hom a := by
      rw [hχ, map_mul, map_pow, Units.val_pow_eq_pow_val]
      change Polynomial.toLaurent Polynomial.X ^ n * Polynomial.toLaurent (Polynomial.C a) =
        LaurentPolynomial.T 1 ^ n * LaurentPolynomial.C a
      simp
    rw [hL, ← e]
    unfold orbit
    rw [mapPoints_rootPoint]
    rfl
  · rw [mapPoints_rootPoint]
    have e : (polynomialEvaluate R 0).hom (Polynomial.X ^ n * Polynomial.C a) = 0 := by
      change Polynomial.aevalTower (AlgHom.id k R) 0 (Polynomial.X ^ n * Polynomial.C a) = 0
      simp [hn']
    rw [e, rootPoint_zero]

private structure RootCoordinates {G₀ : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G₀.val} (U : RootSubgroupFamily T) where
  additive : (root : Root T) → AdditiveLine k
  iso : (root : Root T) → (additive root).group ≅ (U root).1.group
  action : (root : Root T) → HasScalarAction T root.val ((iso root).hom ≫ (U root).1.inclusion)

private abbrev coordinatesType {I : Type u} (R : Type u) : List I → Type u
  | [] => PUnit
  | _ :: l => R × coordinatesType R l

private def mapCoordinates {I R S : Type u} (f : I → R → S) :
    (l : List I) → coordinatesType R l → coordinatesType S l
  | [], _ => PUnit.unit
  | i :: l, p => (f i p.1, mapCoordinates f l p.2)

private def zeroCoordinates {I : Type u} (R : Type u) [Zero R] :
    (l : List I) → coordinatesType R l
  | [] => PUnit.unit
  | _ :: l => (0, zeroCoordinates R l)

variable {G₀ : AffineAlgebraicGroup k} {T : ClosedSubgroup G₀.val}
  {U : RootSubgroupFamily T} (X : RootCoordinates U)

private abbrev coordMap (root : Root T) : (X.additive root).group ⟶ G₀.val :=
  (X.iso root).hom ≫ (U root).1.inclusion

private def evalCoordinates (R : TestAlgebra k) :
    (l : List (Root T)) → coordinatesType R l → GroupPoints G₀.val R
  | [], _ => 1
  | root :: l, p => rootPoint (coordMap X root) R p.1 * evalCoordinates R l p.2

private theorem evalCoordinates_zero (R : TestAlgebra k) (l : List (Root T)) :
    evalCoordinates X R l (zeroCoordinates R l) = 1 := by
  induction l with
  | nil => rfl
  | cons root l ih => simp [evalCoordinates, zeroCoordinates, rootPoint_zero, ih]

private theorem evalCoordinates_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (l : List (Root T)) (p : coordinatesType R l) :
    changeRing (G := G₀.val) f (evalCoordinates X R l p) =
      evalCoordinates X S l (mapCoordinates (fun _ => f.hom) l p) := by
  induction l with
  | nil => exact map_one _
  | cons root l ih =>
    change changeRing (G := G₀.val) f
        (rootPoint (coordMap X root) R p.1 * evalCoordinates X R l p.2) = _
    rw [map_mul, ih]
    change mapPoints f (rootPoint (coordMap X root) R p.1) * _ = _
    rw [mapPoints_rootPoint]
    rfl

private theorem evalCoordinates_scalar (R : TestAlgebra k) (l : List (Root T))
    (t : GroupPoints T.group R) (p : coordinatesType R l) :
    let g := pointMap R T.inclusion t
    g * evalCoordinates X R l p * g⁻¹ =
      evalCoordinates X R l (mapCoordinates (fun root a => characterValue root.val R t * a) l p) := by
  dsimp only
  induction l with
  | nil => simp [evalCoordinates]
  | cons root l ih =>
    let g := pointMap R T.inclusion t
    change g * (rootPoint (coordMap X root) R p.1 * evalCoordinates X R l p.2) * g⁻¹ =
      rootPoint (coordMap X root) R (characterValue root.val R t * p.1) *
        evalCoordinates X R l (mapCoordinates _ l p.2)
    rw [← X.action root R t p.1, ← ih]
    change g * (_ * _) * g⁻¹ = (g * _ * g⁻¹) * (g * _ * g⁻¹)
    group

private def coordinatesToPoint (R : TestAlgebra k) :
    (l : List (Root T)) → coordinatesType R l →
      Points (product (fun root => (U root).1.group.X) l) R
  | [], _ => toUnit _
  | root :: l, p => lift (rootPoint (X.iso root).hom R p.1) (coordinatesToPoint R l p.2)

private theorem coordinatesToPoint_bijective (R : TestAlgebra k) (l : List (Root T)) :
    Function.Bijective (coordinatesToPoint X R l) := by
  induction l with
  | nil =>
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun p => ⟨PUnit.unit, toUnit_unique _ p⟩⟩
  | cons root l ih =>
    have h : Function.Bijective (rootPoint (X.iso root).hom R) := by
      let e := ((groupPointsFunctor k).obj ((U root).1.group)).obj R
      let hom := ((groupPointsFunctor k).mapIso (X.iso root)).app R
      exact hom.groupIsoToMulEquiv.bijective.comp (rootCoordinates (X.additive root) R).bijective
    constructor
    · intro p q hpq
      apply Prod.ext
      · apply h.injective
        have e := congrArg (· ≫ fst _ _) hpq
        simpa only [coordinatesToPoint, lift_fst] using e
      · apply ih.injective
        have e := congrArg (· ≫ snd _ _) hpq
        simpa only [coordinatesToPoint, lift_snd] using e
    · intro p
      obtain ⟨a, ha⟩ := h.surjective (p ≫ fst _ _)
      obtain ⟨q, hq⟩ := ih.surjective (p ≫ snd _ _)
      refine ⟨(a, q), ?_⟩
      apply hom_ext
      · simp only [coordinatesToPoint, lift_fst, ha]
      · simp only [coordinatesToPoint, lift_snd, hq]

private theorem coordinatesToPoint_eval (R : TestAlgebra k) (l : List (Root T))
    (p : coordinatesType R l) :
    coordinatesToPoint X R l p ≫ rootProduct U l = evalCoordinates X R l p := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons root l ih =>
    simp only [coordinatesToPoint, rootProduct, evalCoordinates, MonObj.comp_mul,
      ← Category.assoc, lift_fst, lift_snd, ih]
    unfold rootPoint
    simp only [Category.assoc]
    rfl

private theorem evalCoordinates_injective {L : ClosedSubgroup G₀.val} {l : List (Root T)}
    (h : Parametrizes U l L.inclusion.hom.hom) (R : TestAlgebra k) :
    Function.Injective (evalCoordinates X R l) := by
  obtain ⟨e, he⟩ := h
  haveI : Mono L.inclusion.hom.hom := by
    haveI : IsClosedImmersion L.inclusion.hom.hom.left := L.isClosedImmersion
    exact Over.mono_of_mono_left _
  intro p q hpq
  apply (coordinatesToPoint_bijective X R l).injective
  apply (cancel_mono e.hom).mp
  apply (cancel_mono L.inclusion.hom.hom).mp
  simpa only [Category.assoc, he, coordinatesToPoint_eval] using hpq

private theorem evalCoordinates_range {L : ClosedSubgroup G₀.val} {l : List (Root T)}
    (h : Parametrizes U l L.inclusion.hom.hom) (R : TestAlgebra k)
    (p : GroupPoints L.group R) :
    ∃ q : coordinatesType R l, evalCoordinates X R l q = pointMap R L.inclusion p := by
  obtain ⟨e, he⟩ := h
  obtain ⟨q, hq⟩ := (coordinatesToPoint_bijective X R l).surjective (p ≫ e.inv)
  refine ⟨q, ?_⟩
  rw [← coordinatesToPoint_eval, hq, ← he, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

private abbrev Bivariate (K : Type u) [CommRing K] := MvPolynomial (Fin 2) K

private def substitute {S : Type u} [CommRing S] [Algebra k S] (s : Fin 2 → S) :
    Bivariate k →ₐ[k] Bivariate S :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (s i) * MvPolynomial.X i)

private theorem substitute_X {S : Type u} [CommRing S] [Algebra k S]
    (s : Fin 2 → S) (i : Fin 2) :
    substitute (k := k) s (MvPolynomial.X i) = MvPolynomial.C (s i) * MvPolynomial.X i :=
  MvPolynomial.aeval_X _ i

private theorem coeff_substitute {S : Type u} [CommRing S] [Algebra k S] (s : Fin 2 → S)
    (p : Bivariate k) (d : Fin 2 →₀ ℕ) :
    (substitute s p).coeff d = algebraMap k S (p.coeff d) *
      (s 0 ^ d 0 * s 1 ^ d 1) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, add_mul]
  | monomial e a =>
    have hm : substitute s (MvPolynomial.monomial e a) =
        MvPolynomial.monomial e (algebraMap k S a * (s 0 ^ e 0 * s 1 ^ e 1)) := by
      rw [substitute, MvPolynomial.aeval_monomial]
      rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two,
        MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
      rw [IsScalarTower.algebraMap_apply k S (Bivariate S)]
      change MvPolynomial.C (algebraMap k S a) * _ = _
      simp only [mul_pow, ← map_pow, map_mul]
      ring
    rw [hm]
    by_cases he : e = d
    · subst e
      simp
    · simp [MvPolynomial.coeff_monomial, he]

private theorem laurentParameter_zpow (n : ℤ) :
    (↑((laurentParameter (CommAlgCat.of k k)) ^ n) : LaurentPolynomial k) =
      LaurentPolynomial.T n := by
  let t : Multiplicative ℤ →* (LaurentPolynomial k)ˣ :=
    { toFun := fun m => {
        val := LaurentPolynomial.T m.toAdd
        inv := LaurentPolynomial.T (-m.toAdd)
        val_inv := by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
        inv_val := by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero] }
      map_one' := Units.ext LaurentPolynomial.T_zero
      map_mul' := fun a b => Units.ext (LaurentPolynomial.T_add a.toAdd b.toAdd) }
  have e := t.map_zpow (Multiplicative.ofAdd 1) n
  have hz : (Multiplicative.ofAdd 1 : Multiplicative ℤ) ^ n = Multiplicative.ofAdd n := by
    change Multiplicative.ofAdd (n • (1 : ℤ)) = _
    simp
  rw [hz] at e
  exact congrArg Units.val e.symm

private theorem polynomial_weight_zero (hT : IsSplitTorus T.group)
    (α β root : Character T.group)
    (hroot : ∀ i j : ℕ, 0 < i → 0 < j → α ^ i * β ^ j ≠ root)
    (p : Bivariate k)
    (hz₀ : substitute (k := k) (Fin.cases (0 : k) (fun _ : Fin 1 => 1)) p = 0)
    (hz₁ : substitute (k := k) (Fin.cases (1 : k) (fun _ : Fin 1 => 0)) p = 0)
    (hw : ∀ cochar : Cocharacter T.group,
      let a := pairing T.group α cochar
      let b := pairing T.group β cochar
      let c := pairing T.group root cochar
      let oneScale : Fin 2 → LaurentPolynomial k := fun _ => 1
      let scale : Fin 2 → LaurentPolynomial k :=
        Fin.cases (LaurentPolynomial.T a) (fun _ : Fin 1 => LaurentPolynomial.T b)
      substitute scale p = MvPolynomial.C (LaurentPolynomial.T c) * substitute oneScale p) :
    p = 0 := by
  classical
  ext d
  simp only [AddMonoidAlgebra.coeff_zero]
  by_contra hne
  have hi : 0 < d 0 := by
    by_contra! h
    have e := congrArg (fun q : Bivariate k => q.coeff d) hz₀
    rw [coeff_substitute] at e
    exact hne (by simpa [show d 0 = 0 by omega, fin_cases_one] using e)
  have hj : 0 < d 1 := by
    by_contra! h
    have e := congrArg (fun q : Bivariate k => q.coeff d) hz₁
    rw [coeff_substitute] at e
    exact hne (by simpa [show d 1 = 0 by omega, fin_cases_one] using e)
  have hweight (cochar : Cocharacter T.group) :
      (d 0 : ℤ) * pairing T.group α cochar + (d 1 : ℤ) * pairing T.group β cochar =
        pairing T.group root cochar := by
    have e := congrArg (fun q : Bivariate (LaurentPolynomial k) => q.coeff d) (hw cochar)
    simp only [coeff_substitute, MvPolynomial.coeff_C_mul, Fin.cases_zero, fin_cases_one,
      one_pow, mul_one, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add] at e
    rw [mul_comm (LaurentPolynomial.T _) (algebraMap k (LaurentPolynomial k) _)] at e
    have hne' : algebraMap k (LaurentPolynomial k) (p.coeff d) ≠ 0 :=
      fun h => hne ((algebraMap k (LaurentPolynomial k)).injective (h.trans (map_zero _).symm))
    have hT_eq := mul_left_cancel₀ hne' e
    by_contra hd
    have hcoeff := congrArg (fun q : LaurentPolynomial k => q.coeff (pairing T.group root cochar)) hT_eq
    simp [hd] at hcoeff
  apply hroot (d 0) (d 1) hi hj
  obtain ⟨hc, h⟩ := RootData.CharacterPairing.perfectCharacterPairing T.group hT
  letI := hc
  obtain ⟨_, _, _, _, P, hperf, hP⟩ := h
  suffices e : (Additive.ofMul (α ^ d 0 * β ^ d 1) : Additive (Character T.group)) =
      Additive.ofMul root from congrArg Additive.toMul e
  apply hperf.bijective_left.injective
  ext cochar
  change P ((d 0) • (Additive.ofMul α : Additive (Character T.group)) +
    (d 1) • (Additive.ofMul β : Additive (Character T.group))) cochar = _
  simp only [map_add, LinearMap.add_apply, map_nsmul]
  change (d 0) • (P (Additive.ofMul α) cochar) +
    (d 1) • (P (Additive.ofMul β) cochar) = P (Additive.ofMul root) cochar
  change d 0 • P (Additive.ofMul α) (Additive.ofMul (Additive.toMul cochar)) +
    d 1 • P (Additive.ofMul β) (Additive.ofMul (Additive.toMul cochar)) =
      P (Additive.ofMul root) (Additive.ofMul (Additive.toMul cochar))
  rw [hP, hP, hP, nsmul_eq_mul, nsmul_eq_mul]
  exact hweight (Additive.toMul cochar)

private theorem coordinates_weight_zero (hT : IsSplitTorus T.group)
    (α β : Character T.group)
    (hcone : ∀ i j : ℕ, 0 < i → 0 < j → α ^ i * β ^ j ∉ absoluteRoots T)
    (l : List (Root T)) (q : coordinatesType (Bivariate k) l)
    (hx : mapCoordinates (fun _ => substitute (k := k) (Fin.cases (0 : k) (fun _ : Fin 1 => 1))) l q =
      zeroCoordinates (Bivariate k) l)
    (hy : mapCoordinates (fun _ => substitute (k := k) (Fin.cases (1 : k) (fun _ : Fin 1 => 0))) l q =
      zeroCoordinates (Bivariate k) l)
    (hw : ∀ cochar : Cocharacter T.group,
      let a := pairing T.group α cochar
      let b := pairing T.group β cochar
      let scale : Fin 2 → LaurentPolynomial k :=
        Fin.cases (LaurentPolynomial.T a) (fun _ : Fin 1 => LaurentPolynomial.T b)
      mapCoordinates (fun _ => substitute scale) l q =
      mapCoordinates (fun root p =>
        MvPolynomial.C (LaurentPolynomial.T (pairing T.group root.val cochar)) *
          substitute (fun _ : Fin 2 => (1 : LaurentPolynomial k)) p) l q) :
    q = zeroCoordinates (Bivariate k) l := by
  induction l with
  | nil => exact Subsingleton.elim _ _
  | cons root l ih =>
    apply Prod.ext
    · apply polynomial_weight_zero hT α β root.val
      · intro i j hi hj e
        exact hcone i j hi hj (e ▸ root.property)
      · exact congrArg Prod.fst hx
      · exact congrArg Prod.fst hy
      · intro cochar
        exact congrArg Prod.fst (hw cochar)
    · apply ih q.2
      · exact congrArg Prod.snd hx
      · exact congrArg Prod.snd hy
      · intro cochar
        exact congrArg Prod.snd (hw cochar)

private def rootCommutator (a b : Root T) (R : TestAlgebra k) (u v : R) :
    GroupPoints G₀.val R :=
  rootPoint (coordMap X a) R u * rootPoint (coordMap X b) R v *
    (rootPoint (coordMap X a) R u)⁻¹ * (rootPoint (coordMap X b) R v)⁻¹

private theorem rootCommutator_natural (a b : Root T) {R S : TestAlgebra k}
    (f : R ⟶ S) (u v : R) :
    changeRing (G := G₀.val) f (rootCommutator X a b R u v) =
      rootCommutator X a b S (f.hom u) (f.hom v) := by
  simp only [rootCommutator, map_mul, map_inv, changeRing_rootPoint]

private theorem rootCommutator_conjugates (a b : Root T) (R : TestAlgebra k)
    (t : GroupPoints T.group R) (u v : R) :
    let g := pointMap R T.inclusion t
    g * rootCommutator X a b R u v * g⁻¹ =
      rootCommutator X a b R (characterValue a.val R t * u) (characterValue b.val R t * v) := by
  dsimp only
  let g := pointMap R T.inclusion t
  have ha : g * rootPoint (coordMap X a) R u * g⁻¹ =
      rootPoint (coordMap X a) R (characterValue a.val R t * u) := X.action a R t u
  have hb : g * rootPoint (coordMap X b) R v * g⁻¹ =
      rootPoint (coordMap X b) R (characterValue b.val R t * v) := X.action b R t v
  change g * rootCommutator X a b R u v * g⁻¹ = _
  unfold rootCommutator
  rw [← ha, ← hb]
  group

private theorem commute_coordinates (contracting : ContractingProduct.{u})
    (hG₀ : Specs.GeometricRadicals.IsReductive G₀) (hT : IsSplitTorus T.group)
    (hm : Specs.RankOneFlag.IsGeometricallyMaximal T)
    (a b : Root T) (cochar : Cocharacter T.group)
    (ha : 0 < pairing T.group a.val cochar) (hb : 0 < pairing T.group b.val cochar)
    (hcone : ∀ i j : ℕ, 0 < i → 0 < j → a.val ^ i * b.val ^ j ∉ absoluteRoots T) :
    ∀ (R : TestAlgebra k) (u v : R), rootCommutator X a b R u v = 1 := by
  classical
  obtain ⟨hf, _, h⟩ := contracting G₀ hG₀ T hT hm
  obtain ⟨⟨D⟩, hD⟩ := h cochar
  letI : Finite (Root T) := hf
  letI := Fintype.ofFinite (Root T)
  let l := (positiveRoots T cochar).toFinset.toList
  have hl : Enumerates l (positiveRoots T cochar) := by
    exact ⟨Finset.nodup_toList _, fun _ => by simp [l]⟩
  have hprod := hD D U l hl
  let R₀ := CommAlgCat.of k (Bivariate k)
  let u₀ : R₀ := MvPolynomial.X 0
  let v₀ : R₀ := MvPolynomial.X 1
  obtain ⟨p, hp⟩ := (D.contracting_points R₀ _).mp
    (rootPoint_contraction (X.action a) cochar ha R₀ u₀)
  obtain ⟨p', hp'⟩ := (D.contracting_points R₀ _).mp
    (rootPoint_contraction (X.action b) cochar hb R₀ v₀)
  obtain ⟨q, hq⟩ := evalCoordinates_range X hprod R₀ (p * p' * p⁻¹ * p'⁻¹)
  have e₀ : evalCoordinates X R₀ l q = rootCommutator X a b R₀ u₀ v₀ := by
    simpa only [map_mul, map_inv, hp, hp', rootCommutator] using hq
  have natural {R : TestAlgebra k} (f : R₀ ⟶ R) :
      evalCoordinates X R l (mapCoordinates (fun _ => f.hom) l q) =
        rootCommutator X a b R (f.hom u₀) (f.hom v₀) := by
    rw [← evalCoordinates_natural, e₀, rootCommutator_natural]
  have axis (s : Fin 2 → k) (hs : s 0 = 0 ∨ s 1 = 0) :
      mapCoordinates (fun _ => substitute (k := k) s) l q = zeroCoordinates (Bivariate k) l := by
    apply evalCoordinates_injective X hprod R₀
    rw [evalCoordinates_zero]
    have e := natural (CommAlgCat.ofHom (substitute (k := k) s))
    have e' : evalCoordinates X R₀ l (mapCoordinates (fun _ => substitute (k := k) s) l q) =
        rootCommutator X a b R₀ (substitute s u₀) (substitute s v₀) := e
    rw [e']
    simp only [u₀, v₀, substitute, MvPolynomial.aeval_X]
    rcases hs with hz | hz <;> simp [hz, rootCommutator, rootPoint_zero]
  have weight (testCochar : Cocharacter T.group) :
      let scale : Fin 2 → LaurentPolynomial k :=
        Fin.cases (LaurentPolynomial.T (pairing T.group a.val testCochar))
          (fun _ : Fin 1 => LaurentPolynomial.T (pairing T.group b.val testCochar))
      mapCoordinates (fun _ => substitute scale) l q =
      mapCoordinates (fun root p =>
        MvPolynomial.C (LaurentPolynomial.T (pairing T.group root.val testCochar)) *
          substitute (fun _ : Fin 2 => (1 : LaurentPolynomial k)) p) l q := by
    dsimp only
    let S := LaurentPolynomial k
    let R := CommAlgCat.of k (Bivariate S)
    let τ : Rˣ := Units.map (MvPolynomial.C : S →+* Bivariate S).toMonoidHom
      (laurentParameter (CommAlgCat.of k k))
    let t := cocharacterPoint testCochar R τ
    let sc : Fin 2 → S := Fin.cases (LaurentPolynomial.T (pairing T.group a.val testCochar))
      (fun _ : Fin 1 => LaurentPolynomial.T (pairing T.group b.val testCochar))
    let f₁ : R₀ ⟶ R := CommAlgCat.ofHom (substitute (fun _ : Fin 2 => (1 : S)))
    let f₂ : R₀ ⟶ R := CommAlgCat.ofHom (substitute sc)
    have hχ (root : Root T) :
        characterValue root.val R t = MvPolynomial.C (LaurentPolynomial.T (pairing T.group root.val testCochar)) := by
      rw [(RootData.CharacterPairing.characterPairingComposition T.group root.val testCochar).2 R τ]
      change (↑(Units.map (MvPolynomial.C : S →+* Bivariate S).toMonoidHom
        (laurentParameter (CommAlgCat.of k k)) ^ _) : Bivariate S) = _
      rw [← map_zpow, Units.coe_map, laurentParameter_zpow]
      rfl
    have he₀ : f₂.hom u₀ = characterValue a.val R t * f₁.hom u₀ := by
      change substitute sc (MvPolynomial.X 0) = _ * substitute (fun _ => (1 : S)) (MvPolynomial.X 0)
      rw [substitute_X, substitute_X, hχ]
      simp only [sc, Fin.cases_zero, map_one, one_mul]
      rfl
    have he₁ : f₂.hom v₀ = characterValue b.val R t * f₁.hom v₀ := by
      change substitute sc (MvPolynomial.X 1) = _ * substitute (fun _ => (1 : S)) (MvPolynomial.X 1)
      rw [substitute_X, substitute_X, hχ]
      simp only [sc, fin_cases_one, map_one, one_mul]
      rfl
    have hcomp (l' : List (Root T)) (p : coordinatesType R₀ l') :
        mapCoordinates (fun root a => characterValue root.val R t * a) l'
            (mapCoordinates (fun _ => f₁.hom) l' p) =
          mapCoordinates (fun root a =>
            MvPolynomial.C (LaurentPolynomial.T (pairing T.group root.val testCochar)) *
              substitute (fun _ : Fin 2 => (1 : S)) a) l' p := by
      induction l' with
      | nil => rfl
      | cons root l' ih =>
        apply Prod.ext
        · change characterValue root.val R t * _ = _
          rw [hχ]
          rfl
        · exact ih p.2
    apply evalCoordinates_injective X hprod R
    change evalCoordinates X R l (mapCoordinates (fun _ => f₂.hom) l q) = _
    rw [← hcomp l q, ← evalCoordinates_scalar X R l t, natural, natural, he₀, he₁,
      rootCommutator_conjugates]
  have qz := coordinates_weight_zero hT a.val b.val hcone l q
    (axis _ (Or.inl rfl)) (axis _ (Or.inr rfl)) weight
  intro R u v
  let f : R₀ ⟶ R := CommAlgCat.ofHom (bivariateEvaluation u v)
  have hf₀ : f.hom u₀ = u := bivariateEvaluation_X_zero (k := k) u v
  have hf₁ : f.hom v₀ = v := bivariateEvaluation_X_one (k := k) u v
  rw [← hf₀, ← hf₁, ← rootCommutator_natural, ← e₀, qz, evalCoordinates_zero, map_one]

private theorem rootPoint_of_subgroup {A : AdditiveLine k} {U S : ClosedSubgroup G}
    (e : A.group ≅ S.group) (j : U.group ⟶ S.group) (hj : j ≫ S.inclusion = U.inclusion)
    (R : TestAlgebra k) (p : GroupPoints U.group R) :
    ∃ a : R, rootPoint (e.hom ≫ S.inclusion) R a = p ≫ U.inclusion.hom.hom := by
  obtain ⟨a, ha⟩ := (rootCoordinates A R).surjective (p ≫ j.hom.hom ≫ e.inv.hom.hom)
  refine ⟨a, ?_⟩
  change rootCoordinates A R a ≫ (e.hom.hom.hom ≫ S.inclusion.hom.hom) = _
  let forget := Grp.forget (SchemeOver k)
  have h₁ : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ := forget.congr_map e.inv_hom_id
  have h₂ : j.hom.hom ≫ S.inclusion.hom.hom = U.inclusion.hom.hom := forget.congr_map hj
  rw [ha]
  simp only [Category.assoc]
  rw [← Category.assoc e.inv.hom.hom, h₁, Category.id_comp]
  exact congrArg (p ≫ ·) h₂

/-- If no positive mixed weight is a root, all the ordered coordinates of
the commutator vanish. -/
theorem independentRootCommutation_conditional
    (_ : BorelRadicalProduct.{u}) (contracting : ContractingProduct.{u}) (_ : RegularRootCell.{u}) :
    Specs.RankOneRelations.IndependentRootCommutation.{u} := by
  classical
  intro k _ G hG T hT hm α hα β hβ hind hcone U V hU hV R p q
  obtain ⟨a, ha⟩ := LinearAlgebraicGroups.RankOneFlag.exists_positive_cocharacter hT hα.1
  obtain ⟨b, hb⟩ := LinearAlgebraicGroups.RankOneFlag.exists_positive_cocharacter hT hβ.1
  obtain ⟨cochar, hcocharα, hcocharβ⟩ := simultaneous_positive hT α β hind a b ha hb
  have hroots := RootData.RootGroups.rootSubgroups G hG T hT hm
  have ex (root : Root T) := (hroots.2 root.val root.property).2.2
  choose S hS using ex
  let F : RootSubgroupFamily T := fun root => ⟨S root, (hS root).1⟩
  have ec (root : Root T) := (hS root).2.2.2.1
  choose A e he using ec
  let X : RootCoordinates F := ⟨A, e, he⟩
  let a₀ : Root T := ⟨α, hα⟩
  let b₀ : Root T := ⟨β, hβ⟩
  obtain ⟨jp, hjp⟩ := ((hS a₀).2.2.2.2 U hU).2
  obtain ⟨jq, hjq⟩ := ((hS b₀).2.2.2.2 V hV).2
  obtain ⟨u, hup⟩ := rootPoint_of_subgroup (e a₀) jp hjp R p
  obtain ⟨v, hvq⟩ := rootPoint_of_subgroup (e b₀) jq hjq R q
  have comm := commute_coordinates X contracting hG hT hm a₀ b₀ cochar hcocharα hcocharβ hcone R u v
  unfold rootCommutator at comm
  rw [hup, hvq] at comm
  exact (commutatorElement_eq_one_iff_commute).mp comm

end RootProducts

end
end LinearAlgebraicGroups.Classification.RankOneRelations

universe v8_closure_f9d11bd04231d797_u0
theorem _root_.«LinearAlgebraicGroups».«Classification».«RankOneRelations».«independentRootCommutation» : _root_.«LinearAlgebraicGroups».«Specs».«RankOneRelations».«IndependentRootCommutation».{v8_closure_f9d11bd04231d797_u0} :=
  @_root_.«LinearAlgebraicGroups».«Classification».«RankOneRelations».«independentRootCommutation_conditional».{v8_closure_f9d11bd04231d797_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«borelRadicalProduct».{v8_closure_f9d11bd04231d797_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«contractingProduct».{v8_closure_f9d11bd04231d797_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«regularRootCell».{v8_closure_f9d11bd04231d797_u0})
theorem _root_.«LinearAlgebraicGroups».«Classification».«RankOneRelations».«oppositeRootRelations» : _root_.«LinearAlgebraicGroups».«Specs».«RankOneRelations».«OppositeRootRelations».{v8_closure_f9d11bd04231d797_u0} :=
  @_root_.«LinearAlgebraicGroups».«Classification».«RankOneRelations».«oppositeRootRelations_conditional».{v8_closure_f9d11bd04231d797_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«borelRadicalProduct».{v8_closure_f9d11bd04231d797_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«contractingProduct».{v8_closure_f9d11bd04231d797_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«OrderedRootProducts».«regularRootCell».{v8_closure_f9d11bd04231d797_u0})
