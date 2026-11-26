import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactWeylLabels
import LinearAlgebraicGroups.Classification.TransportedRootCoordinates
import LinearAlgebraicGroups.Relative.RationalDensity
import Mathlib.Tactic.Module

import LinearAlgebraicGroups.Arithmetic.ExceptionalOuterTorus
noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Topology Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open LieAlgebrasAndRepresentations

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactWeylLabels

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup)
open AdelicGroups (PointsIn)
open Specs.ExceptionalCompactInner (fixedSubgroup)
open Specs.ExceptionalFoldedWeyl
open Specs.ExceptionalOuterTorus (MarkedPair complexTest fixedCompact)
open Specs.IntegralModels (MatrixRealization)
open Specs.RootGroups (AdditiveLine)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character Cocharacter StandardLattice)
open Specs.CharacterPairing (pairing characterValue)
open Specs.DiagonalizableGroups (groupAlgebra)
open Specs.GeometricRadicals (IsSplitTorus)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)

private theorem normalizes_compact_torus {H : Type*} [Group H]
    {ω : MulAut H} {S : Subgroup H} {n t : H}
    (hn : n ∈ fixedSubgroup ω) (hnS : n ∈ Subgroup.normalizer (S : Set H))
    (ht : t ∈ fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set H)) :
    MulAut.conj n t ∈ fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set H) := by
  refine ⟨(fixedSubgroup ω).mul_mem ((fixedSubgroup ω).mul_mem hn ht.1)
    ((fixedSubgroup ω).inv_mem hn), Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro s hs
  have hp := (Subgroup.mem_normalizer_iff''.mp hnS s).mp hs
  have heq := congrArg (MulAut.conj n) (Subgroup.mem_centralizer_iff.mp ht.2 _ hp)
  rw [map_mul, map_mul] at heq
  simpa [MulAut.conj_apply, mul_assoc] using heq

private theorem e6Inner_smul_right (β y : E6Space) (r : ℝ) :
    e6Inner β (r • y) = r * e6Inner β y := by
  unfold e6Inner
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

private theorem weyl_smul {w : Function.End E6Space} (hw : w ∈ e6Weyl) (r : ℝ) (y : E6Space) :
    w (r • y) = r • w y := by
  revert y
  induction hw using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨j, rfl⟩ := hf
    intro y
    simp only [reflection]
    rw [e6Inner_smul_right]
    module
  | one => intro y; rfl
  | mul u v _ _ hu hv =>
    intro y
    change u (v (r • y)) = r • u (v y)
    rw [hv, hu]

private theorem conj_intertwine {H : Type*} [Group H] (σ : MulAut H) (n : H) :
    σ * MulAut.conj n = MulAut.conj (σ n) * σ := by
  ext g
  change σ (n * g * n⁻¹) = σ n * σ g * (σ n)⁻¹
  rw [map_mul, map_mul, map_inv]

section Twisted

variable {H : Type*} [Group H] (e : E6Space → H)
    (ha : ∀ y z, e (y + z) = e y * e z)
    (hk : ∀ y, e y = 1 ↔ y ∈ e6Lattice)

include ha hk

private theorem vectors_eq_of_exp_smul_eq {u v : E6Space}
    (h : ∀ r : ℝ, e (r • u) = e (r • v)) : u = v := by
  have hzero : e 0 = 1 := (hk 0).2 ⟨0, by ext j; simp⟩
  have hneg (y : E6Space) : e (-y) = (e y)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← ha, neg_add_cancel, hzero]
  ext j
  by_contra hne
  have hd : u j - v j ≠ 0 := sub_ne_zero.mpr hne
  let r := (1 / 2 : ℝ) / (u j - v j)
  have hr : e (r • u - r • v) = 1 := by
    rw [sub_eq_add_neg, ha, hneg, h, mul_inv_cancel]
  obtain ⟨z, hz⟩ := (hk _).mp hr
  have hcoord : r * (u j - v j) = (z j : ℝ) := by
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub] using congrFun hz.symm j
  have hh : (z j : ℝ) = 1 / 2 := hcoord.symm.trans (div_mul_cancel₀ _ hd)
  have htwo : (2 : ℝ) * (z j : ℝ) = 1 := by rw [hh]; norm_num
  have hint : (2 : ℤ) * z j = 1 := by exact_mod_cast htwo
  omega

private theorem fixed_label_commutes (δ : MulAut H)
    (hδ : ∀ y, δ (e y) = e (e6Diagram y)) (x : E6Space)
    {n : H} (hn : (MulAut.conj (e x) * δ) n = n)
    {w : Function.End E6Space} (hw : w ∈ e6Weyl)
    (hnw : ∀ y, n * e y * n⁻¹ = e (w y)) : Function.Commute w e6Diagram := by
  let τ := MulAut.conj (e x) * δ
  have hτ (y : E6Space) : τ (e y) = e (e6Diagram y) := by
    change MulAut.conj (e x) (δ (e y)) = _
    rw [hδ, MulAut.conj_apply, ← ha, add_comm x, ha, mul_inv_cancel_right]
  have hc : τ * MulAut.conj n = MulAut.conj n * τ :=
    (conj_intertwine τ n).trans (congrArg (fun v => MulAut.conj v * τ) hn)
  have he (y : E6Space) : e (w (e6Diagram y)) = e (e6Diagram (w y)) := by
    have h := DFunLike.congr_fun hc (e y)
    change τ (MulAut.conj n (e y)) = MulAut.conj n (τ (e y)) at h
    rw [show MulAut.conj n (e y) = _ from hnw y, hτ, hτ] at h
    exact (hnw _).symm.trans h.symm
  intro y
  apply vectors_eq_of_exp_smul_eq e ha hk
  intro r
  have hdiagram (v : E6Space) : e6Diagram (r • v) = r • e6Diagram v := rfl
  simpa only [hdiagram, weyl_smul hw] using he (r • y)

end Twisted


open private unitPointHom unitPointHom_apply
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private torus_point_from_coordinates characterUnit characterUnitOnPoints
  characterValue_eq_unit characterUnit_cocharacter
  from LinearAlgebraicGroups.RootData.RootGroups
open private splitPresentation charactersOfIso characterValue_monomial algebraPoint
  from LinearAlgebraicGroups.RootData.CharacterPairing
open private affine_dense_eval dense_rationalSectionValues affineRationalSection
  factors_through_closed_of_range torus_isReduced
  from LinearAlgebraicGroups.Relative.RationalDensity

variable {G : AffineAlgebraicGroup ℝ} {i : MatrixRealization G}
  {A : AdditiveLine ℂ} (M : MarkedPair G A)

private def markedPointsEquiv : GroupPoints M.P.pair.G.val complexTest ≃* PointsIn i ℂ :=
  ((groupPointsFunctor ℂ).mapIso M.comparison).app complexTest |>.groupIsoToMulEquiv
    |>.trans (baseChangePointGroupEquiv ℂ G.val complexTest)

private theorem markedPointsEquiv_apply {Q : GroupScheme ℂ} (f : Q ⟶ M.P.pair.G.val)
    (q : GroupPoints Q complexTest) :
    markedPointsEquiv (i := i) M (q ≫ f.hom.hom) = M.onPoints f q := rfl

private def circleUnit (x : ℝ) : ℂˣ := Circle.toUnits (Circle.exp (2 * Real.pi * x))

@[simp] private theorem circleUnit_zero : circleUnit 0 = 1 := by
  simp [circleUnit]

private theorem circleUnit_add (s t : ℝ) :
    circleUnit (s + t) = circleUnit s * circleUnit t := by
  simp [circleUnit, mul_add, Circle.exp_add]

private def evalCochar {U : GroupScheme ℂ} (c : Cocharacter U) :
    ℂˣ →* GroupPoints U complexTest :=
  (((groupPointsFunctor ℂ).map c).app complexTest).hom.comp (unitPointHom complexTest)

private theorem evalCochar_apply {U : GroupScheme ℂ} (c : Cocharacter U) (v : ℂˣ) :
    evalCochar c v = cocharacterPoint c complexTest v := rfl

local instance : IsCommMonObj M.P.pair.T.group.X := M.datum.comm
local instance : CommGroup (GroupPoints M.P.pair.T.group complexTest) := by
  change CommGroup ((testSpec ℂ).obj (op complexTest) ⟶ M.P.pair.T.group.X)
  exact { __ := (inferInstance : Group (_ ⟶ _))
          mul_comm := CategoryTheory.Hom.commMonoid.mul_comm }

private theorem torusPoint_prod (y : E6Space) :
    M.torusPoint y = ∏ j, evalCochar (M.coroot j) (circleUnit (y j)) := by
  exact List.prod_ofFn (f := fun j => evalCochar (M.coroot j) (circleUnit (y j)))

private theorem torusPoint_add (y z : E6Space) :
    M.torusPoint (y + z) = M.torusPoint y * M.torusPoint z := by
  simp only [torusPoint_prod, Pi.add_apply, circleUnit_add, map_mul]
  exact Finset.prod_mul_distrib

private theorem torusPoint_single (j : Fin 6) (s : ℝ) :
    M.torusPoint (Pi.single j s) = cocharacterPoint (M.coroot j) complexTest (circleUnit s) := by
  rw [torusPoint_prod, Finset.prod_eq_single j]
  · rw [Pi.single_eq_same, evalCochar_apply]
  · intro k _ h
    rw [Pi.single_eq_of_ne h, circleUnit_zero, map_one]
  · simp

private def torusPointHom :
    Multiplicative E6Space →* GroupPoints M.P.pair.T.group complexTest where
  toFun y := M.torusPoint y.toAdd
  map_one' := by
    change M.torusPoint 0 = 1
    rw [torusPoint_prod]
    exact (Finset.prod_congr rfl (fun j _ => by
      rw [Pi.zero_apply, circleUnit_zero]
      exact (evalCochar (M.coroot j)).map_one)).trans
      Finset.prod_const_one
  map_mul' := torusPoint_add M


private theorem circleUnit_separates {m n : ℤ}
    (h : ∀ s, circleUnit s ^ m = circleUnit s ^ n) : m = n := by
  by_contra hne
  have hdiff : (m : ℝ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  let d := ((m : ℝ) - n) * (2 * Real.pi)
  have hd : d ≠ 0 := mul_ne_zero hdiff (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  let s := Real.pi / d
  have hs : Circle.exp (2 * Real.pi * s) ^ m = Circle.exp (2 * Real.pi * s) ^ n := by
    apply Subtype.ext
    have hu : Circle.toUnits (Circle.exp (2 * Real.pi * s) ^ m) =
        Circle.toUnits (Circle.exp (2 * Real.pi * s) ^ n) := by
      simpa only [circleUnit, map_zpow] using h s
    exact congrArg (fun u : ℂˣ => (u : ℂ)) hu
  rw [← Circle.exp_intCast_mul, ← Circle.exp_intCast_mul] at hs
  have hexp : Circle.exp (d * s) = 1 := by
    rw [show d * s = (m : ℝ) * (2 * Real.pi * s) - (n : ℝ) * (2 * Real.pi * s) by
      dsimp [d]; ring, Circle.exp_sub, hs, div_self']
  exact Circle.exp_pi_ne_one (by simpa only [s, mul_div_cancel₀ _ hd] using hexp)

private theorem pairing_on_basis_injective
    (b : Module.Basis (Fin 6) ℤ (Additive (Cocharacter M.P.pair.T.group)))
    (hb : ∀ j, b j = Additive.ofMul (M.coroot j))
    {χ ψ : Character M.P.pair.T.group}
    (h : ∀ j, pairing M.P.pair.T.group χ (M.coroot j) =
      pairing M.P.pair.T.group ψ (M.coroot j)) : χ = ψ := by
  let D := M.datum.datum
  apply Additive.ofMul.injective
  apply D.rootDatum.toPerfPair.injective
  apply b.ext
  intro j
  rw [hb]
  exact (D.pairing_eq _ _).trans ((h j).trans (D.pairing_eq _ _).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem torusPoint_dense
    (b : Module.Basis (Fin 6) ℤ (Additive (Cocharacter M.P.pair.T.group)))
    (hb : ∀ j, b j = Additive.ofMul (M.coroot j)) :
    Dense (Set.range fun y : E6Space =>
      (M.torusPoint y).left (IsLocalRing.closedPoint ℂ)) := by
  classical
  obtain ⟨r, ⟨f⟩⟩ := splitPresentation M.P.pair.split
  obtain ⟨χ₀, _, hχ₀, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing
    (k := ℂ) r
  let χ := χ₀.trans (charactersOfIso f)
  let F (m : StandardLattice r) : Multiplicative E6Space →* ℂ :=
    (Units.coeHom ℂ).comp ((characterUnitOnPoints (χ m) complexTest).comp (torusPointHom M))
  have hF : Function.Injective F := by
    intro m n hmn
    apply χ.injective
    apply pairing_on_basis_injective M b hb
    intro j
    apply circleUnit_separates
    intro s
    have he := congrArg (fun p : Multiplicative E6Space →* ℂ =>
      p (Multiplicative.ofAdd (Pi.single j s))) hmn
    change (characterUnit (χ m) complexTest (M.torusPoint (Pi.single j s)) : ℂ) =
      (characterUnit (χ n) complexTest (M.torusPoint (Pi.single j s)) : ℂ) at he
    rw [torusPoint_single, characterUnit_cocharacter, characterUnit_cocharacter] at he
    exact Units.ext he
  choose a ha using fun y : E6Space =>
    torus_point_from_coordinates r f complexTest (M.torusPoint y)
  have hmonomial (y : E6Space) (m : StandardLattice r) :
      a y (MonoidAlgebra.single m 1) = F m (Multiplicative.ofAdd y) := by
    change _ = (characterUnit (χ m) complexTest (M.torusPoint y) : ℂ)
    rw [← characterValue_eq_unit, ← ha y]
    change _ = characterValue (f.inv ≫ χ₀ m) complexTest
      (algebraPoint complexTest (a y) ≫ f.hom.hom.hom)
    have he : (algebraPoint complexTest (a y) ≫ f.hom.hom.hom) ≫
        (f.inv ≫ χ₀ m).hom.hom = algebraPoint complexTest (a y) ≫ (χ₀ m).hom.hom := by
      change (algebraPoint complexTest (a y) ≫ f.hom.hom.hom) ≫
        f.inv.hom.hom ≫ (χ₀ m).hom.hom = _
      rw [Category.assoc, ← Category.assoc (f := f.hom.hom.hom),
        show f.hom.hom.hom ≫ f.inv.hom.hom = 𝟙 _ from (Grp.forget _).congr_map f.hom_inv_id,
        Category.id_comp]
    unfold characterValue
    dsimp only
    rw [he]
    change _ = characterValue (χ₀ m) complexTest (algebraPoint complexTest (a y))
    rw [hχ₀, characterValue_monomial]
  have hsep (p : MonoidAlgebra ℂ (StandardLattice r)) (hp : ∀ y, a y p = 0) : p = 0 := by
    apply MonoidAlgebra.coeff_injective
    change p.coeff = 0
    apply linearIndependent_iff.mp ((linearIndependent_monoidHom _ ℂ).comp F hF)
    funext y
    have hy := hp y.toAdd
    rw [MonoidAlgebra.lift_unique' (a y.toAdd)] at hy
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, MonoidAlgebra.lift_apply,
      hmonomial] using hy
  have hd := dense_rationalSectionValues (fun y => affineRationalSection (a y))
    (affine_dense_eval a hsep)
  let u : (specGroup (groupAlgebra ℂ (StandardLattice r))).X.left ≅ M.P.pair.T.group.X.left :=
    ((Grp.forget (SchemeOver ℂ)) ⋙ Over.forget _).mapIso f
  apply (u.hom.homeomorph.surjective.denseRange.dense_image u.hom.continuous hd).mono
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  exact ⟨y, (congrArg (fun t : GroupPoints M.P.pair.T.group complexTest =>
    t.left (IsLocalRing.closedPoint ℂ)) (ha y)).symm⟩


open private isTorus_of_split from LinearAlgebraicGroups.RootData.CharacterPairing
open private conjugation conjugation_apply
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private conjugateLe_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private groundIso from LinearAlgebraicGroups.Solvable.TorusSections
open private exists_weylIdentification rationalWeylLabel weylGeneratedByBase
  from LinearAlgebraicGroups.Classification.TransportedRootCoordinates
open private labelConjugation from LinearAlgebraicGroups.RootData.DatumAndWeyl

private abbrev complexSource := (testSpec ℂ).obj (op complexTest)

private def rationalSection {U : GroupScheme ℂ} (g : GroupPoints U complexTest) :
    𝟙_ (SchemeOver ℂ) ⟶ U.X :=
  (groundIso (k := ℂ)).inv ≫ g

set_option backward.isDefEq.respectTransparency false in
@[simp] private theorem toUnit_rationalSection {U : GroupScheme ℂ} (g : GroupPoints U complexTest) :
    toUnit complexSource ≫ rationalSection g = g := by
  rw [rationalSection, ← Category.assoc,
    show toUnit complexSource = (groundIso (k := ℂ)).hom from Subsingleton.elim _ _,
    Iso.hom_inv_id, Category.id_comp]

private theorem rationalSection_inv {U : GroupScheme ℂ} (g : GroupPoints U complexTest) :
    rationalSection (g⁻¹) = (rationalSection g)⁻¹ :=
  GrpObj.comp_inv _ _

set_option backward.isDefEq.respectTransparency false in
private theorem complex_normalizer
    (b : Module.Basis (Fin 6) ℤ (Additive (Cocharacter M.P.pair.T.group)))
    (hb : ∀ j, b j = Additive.ofMul (M.coroot j))
    {ω : MulAut (PointsIn i ℂ)} {S T : Subgroup (PointsIn i ℂ)}
    (hcent : T = fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set _))
    (htori : (T : Set (PointsIn i ℂ)) = (fixedSubgroup ω : Set _) ∩
      Set.range (M.onPoints (i := i) M.P.pair.T.inclusion))
    (hexp : (T : Set (PointsIn i ℂ)) = Set.range (M.exp (i := i)))
    {n : PointsIn i ℂ} (hn : n ∈ fixedSubgroup ω)
    (hnS : n ∈ Subgroup.normalizer (S : Set _)) :
    Normalizes M.P.pair.T.inclusion (rationalSection ((markedPointsEquiv (i := i) M).symm n)) := by
  let U := M.P.pair.T
  apply (LinearAlgebraicGroups.normalizesIff ℂ U.inclusion U.isClosedImmersion _ _).2
  have aux (m : PointsIn i ℂ) (hm : m ∈ fixedSubgroup ω)
      (hmS : m ∈ Subgroup.normalizer (S : Set _)) :
      ConjugateLe U.inclusion (rationalSection ((markedPointsEquiv (i := i) M).symm m)) := by
    let g := rationalSection ((markedPointsEquiv (i := i) M).symm m)
    let f := U.inclusion ≫ conjugation g
    haveI : IsReduced U.group.X.left :=
      torus_isReduced (Specs.Unipotent.closedSubgroupAlgebraicGroup U)
        (isTorus_of_split M.P.pair.split)
    have hrange : Set.range f.hom.hom.left ⊆ Set.range U.inclusion.hom.hom.left := by
      rw [← Set.image_univ]
      apply Set.image_subset_iff.mpr
      have hc := U.isClosedImmersion.isClosedEmbedding.isClosed_range.preimage
        f.hom.hom.left.continuous
      rw [← (torusPoint_dense M b hb).closure_eq, hc.closure_subset_iff]
      rintro _ ⟨y, rfl⟩
      have hy : M.exp (i := i) y ∈ T := by
        change M.exp (i := i) y ∈ (T : Set _)
        rw [hexp]
        exact ⟨y, rfl⟩
      have hy' : MulAut.conj m (M.exp (i := i) y) ∈ T := by
        rw [hcent] at hy ⊢
        exact normalizes_compact_torus hm hmS hy
      change MulAut.conj m (M.exp (i := i) y) ∈ (T : Set _) at hy'
      rw [htori] at hy'
      obtain ⟨t, ht⟩ := hy'.2
      have hf : M.torusPoint y ≫ f.hom.hom = t ≫ U.inclusion.hom.hom := by
        apply (markedPointsEquiv (i := i) M).injective
        rw [markedPointsEquiv_apply]
        change (markedPointsEquiv (i := i) M)
          ((M.torusPoint y ≫ U.inclusion.hom.hom) ≫ (conjugation g).hom.hom) = _
        have hconj : (M.torusPoint y ≫ U.inclusion.hom.hom) ≫ (conjugation g).hom.hom =
            ((markedPointsEquiv (i := i) M).symm m) *
              (show GroupPoints M.P.pair.G.val complexTest from M.torusPoint y ≫ U.inclusion.hom.hom) *
              ((markedPointsEquiv (i := i) M).symm m)⁻¹ := by
          let p : complexSource ⟶ M.P.pair.G.val.X := M.torusPoint y ≫ U.inclusion.hom.hom
          have hh := conjugation_apply g p
          rw [show toUnit complexSource ≫ g = (markedPointsEquiv (i := i) M).symm m
            from toUnit_rationalSection _] at hh
          exact hh
        rw [hconj, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
          markedPointsEquiv_apply, markedPointsEquiv_apply]
        exact ht.symm
      exact ⟨t.left (IsLocalRing.closedPoint ℂ),
        congrArg (fun p : GroupPoints M.P.pair.G.val complexTest =>
          p.left (IsLocalRing.closedPoint ℂ)) hf.symm⟩
    obtain ⟨v, hv⟩ := factors_through_closed_of_range f U hrange
    apply (conjugateLe_iff U.inclusion g).2
    intro V a t
    have ha : a = toUnit V := Subsingleton.elim _ _
    refine ⟨t ≫ v.hom.hom, ?_⟩
    have h := congrArg (fun j : U.group ⟶ M.P.pair.G.val => t ≫ j.hom.hom) hv
    change (t ≫ v.hom.hom) ≫ U.inclusion.hom.hom =
      (t ≫ U.inclusion.hom.hom) ≫ (conjugation g).hom.hom at h
    rw [ha, ← conjugation_apply]
    exact h
  refine ⟨aux n hn hnS, ?_⟩
  rw [← rationalSection_inv, ← map_inv]
  exact aux n⁻¹ ((fixedSubgroup ω).inv_mem hn) ((Subgroup.normalizer _).inv_mem hnS)

set_option backward.isDefEq.respectTransparency false in
private theorem exists_torus_action (n : GroupPoints M.P.pair.G.val complexTest)
    (hn : Normalizes M.P.pair.T.inclusion (rationalSection n)) :
    ∃ (w : M.datum.datum.rootDatum.weylGroup) (a : M.P.pair.T.group ≅ M.P.pair.T.group),
      (∀ c : Cocharacter M.P.pair.T.group,
        w.val.coweightEquiv.symm (Additive.ofMul c) = Additive.ofMul (c ≫ a.hom)) ∧
      ∀ t : GroupPoints M.P.pair.T.group complexTest,
        (t ≫ a.hom.hom.hom) ≫ M.P.pair.T.inclusion.hom.hom =
          n * (show GroupPoints M.P.pair.G.val complexTest from t ≫ M.P.pair.T.inclusion.hom.hom) * n⁻¹ := by
  obtain ⟨I⟩ := exists_weylIdentification M.P.pair M.datum
  obtain ⟨q, hq⟩ := (I.representsNormalizer _ _).1 hn
  obtain ⟨L, hL⟩ := rationalWeylLabel I
  refine ⟨L q, I.image.conjugation (I.labelEquiv (L q)), I.cocharacterAction _, fun t => ?_⟩
  have he := labelConjugation I.image _ q (hL q).1
  rw [hq] at he
  let e := I.image.conjugation (I.labelEquiv (L q))
  change (e.hom ≫ M.P.pair.T.inclusion).hom.hom =
    (toUnit M.P.pair.T.group.X ≫ rationalSection n) * M.P.pair.T.inclusion.hom.hom *
      (toUnit M.P.pair.T.group.X ≫ rationalSection n)⁻¹ at he
  have h := congrArg (fun p : M.P.pair.T.group.X ⟶ M.P.pair.G.val.X =>
    (show complexSource ⟶ M.P.pair.T.group.X from t) ≫ p) he
  simp only [MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc] at h
  let p : complexSource ⟶ M.P.pair.G.val.X := t ≫ M.P.pair.T.inclusion.hom.hom
  change t ≫ e.hom.hom.hom ≫ M.P.pair.T.inclusion.hom.hom =
    (toUnit complexSource ≫ rationalSection n) * p * (toUnit complexSource ≫ rationalSection n)⁻¹ at h
  rw [toUnit_rationalSection] at h
  simpa only [Category.assoc] using h


private theorem simpleInner (j : Fin 6) (x : E6Space) :
    e6Inner (Pi.single j 1) x = ∑ k, (CartanMatrix.E 6 j k : ℝ) * x k := by
  unfold e6Inner
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ h
    simp [Pi.single_eq_of_ne h]
  · simp

private theorem cartan_symmetric (j k : Fin 6) :
    CartanMatrix.E 6 j k = CartanMatrix.E 6 k j := by
  fin_cases j <;> fin_cases k <;> decide

private theorem reflection_simple (j : Fin 6) (x : E6Space) :
    reflection (Pi.single j 1) x = x - e6Inner (Pi.single j 1) x • Pi.single j 1 := by
  have hd : ∀ j : Fin 6, CartanMatrix.E 6 j j = 2 := by decide
  have h : e6Inner (Pi.single j 1) (Pi.single j 1) = 2 := by
    rw [simpleInner, Finset.sum_eq_single j]
    · simp
    · intro k _ h
      simp [Pi.single_eq_of_ne h]
    · simp
  simp [reflection, foldedCoroot, h]
open Specs.AbsoluteDynkinTypes (PreservesCartan)

private abbrev MarkedCocharacters := Additive (Cocharacter M.P.pair.T.group)

private def realCoordinates (b : Module.Basis (Fin 6) ℤ (MarkedCocharacters M))
    (v : MarkedCocharacters M) : E6Space :=
  fun j => (b.repr v j : ℝ)

private theorem realCoordinates_basis
    (b : Module.Basis (Fin 6) ℤ (MarkedCocharacters M)) (j : Fin 6) :
    realCoordinates M b (b j) = Pi.single j 1 := by
  ext k
  simp only [realCoordinates, b.repr_self]
  by_cases h : k = j
  · subst k
    simp
  · rw [Pi.single_eq_of_ne h, Finsupp.single_eq_of_ne h]
    simp

private theorem realCoordinates_simple
    (b : Module.Basis (Fin 6) ℤ (MarkedCocharacters M))
    (hb : ∀ j, b j = Additive.ofMul (M.coroot j))
    (hcartan : PreservesCartan (RootData.integralCartan M.datum.datum.rootDatum M.datum.base)
      (CartanMatrix.E 6) M.numbering)
    (j : Fin 6) (v : MarkedCocharacters M) :
    realCoordinates M b ((M.datum.datum.rootDatum.coreflection (M.numbering.symm j).val) v) =
      reflection (Pi.single j 1) (realCoordinates M b v) := by
  let P := M.datum.datum.rootDatum
  let α := M.numbering.symm j
  have hcoroot (k : Fin 6) : P.coroot (M.numbering.symm k).val = b k := (hb k).symm
  have hcart (k : Fin 6) : (P.root' α.val) (b k) = CartanMatrix.E 6 j k := by
    rw [← hcoroot k, cartan_symmetric j k]
    change RootData.integralCartan P M.datum.base (M.numbering.symm k) α =
      CartanMatrix.E 6 k j
    simpa only [α, Equiv.apply_symm_apply] using hcartan (M.numbering.symm k) α
  have hpair : ((P.root' α.val) v : ℝ) = e6Inner (Pi.single j 1) (realCoordinates M b v) := by
    rw [simpleInner]
    nth_rw 1 [← b.sum_repr v]
    simp only [map_sum, map_smul, hcart, Int.zsmul_eq_mul, Int.cast_sum,
      Int.cast_mul, realCoordinates]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [RootPairing.coreflection_apply, hcoroot j, reflection_simple, ← hpair,
    ← realCoordinates_basis M b j]
  ext k
  simp only [realCoordinates, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_smul,
    Finsupp.sub_apply, Finsupp.smul_apply, Int.cast_sub, Int.cast_mul, P, α]

private theorem exists_real_weyl_action
    (b : Module.Basis (Fin 6) ℤ (MarkedCocharacters M))
    (hb : ∀ j, b j = Additive.ofMul (M.coroot j))
    (hcartan : PreservesCartan (RootData.integralCartan M.datum.datum.rootDatum M.datum.base)
      (CartanMatrix.E 6) M.numbering)
    (u : M.datum.datum.rootDatum.weylGroup) :
    ∃ w ∈ e6Weyl, ∀ v : MarkedCocharacters M,
      realCoordinates M b (u.val.coweightEquiv.symm v) = w (realCoordinates M b v) := by
  let P := M.datum.datum.rootDatum
  letI := M.datum.datum.finiteRoots
  letI := M.datum.datum.reduced
  let simple := Set.range (fun a : M.datum.base.support => RootPairing.weylGroup.ofIdx P a.val)
  have hgen : Subgroup.closure simple = ⊤ := weylGeneratedByBase P M.datum.base
  have hinv (a : P.weylGroup) (ha : a ∈ simple) : a⁻¹ = a := by
    obtain ⟨i, rfl⟩ := ha
    exact Subtype.ext (RootPairing.Equiv.reflection_inv _ _)
  have hgen' : (Subgroup.closure simple).toSubmonoid = Submonoid.closure simple := by
    rw [Subgroup.closure_toSubmonoid, show simple⁻¹ = simple from by
      ext a
      change a⁻¹ ∈ simple ↔ a ∈ simple
      constructor
      · intro ha
        have he := hinv _ ha
        rw [inv_inv] at he
        rwa [he]
      · intro ha
        rw [hinv _ ha]
        exact ha, Set.union_self]
  have hu : u ∈ Submonoid.closure simple := by
    rw [← hgen', hgen]
    trivial
  induction hu using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    let j := M.numbering i
    have hi : M.numbering.symm j = i := M.numbering.symm_apply_apply i
    refine ⟨reflection (Pi.single j 1), Submonoid.subset_closure ⟨j, rfl⟩, fun v => ?_⟩
    change realCoordinates M b ((RootPairing.Equiv.reflection P i.val).coweightEquiv.symm v) = _
    rw [RootPairing.Equiv.reflection_coweightEquiv]
    have he : (P.coreflection i.val).symm v = P.coreflection i.val v :=
      (LinearEquiv.symm_apply_eq _).2 (P.coreflection_same _ _).symm
    rw [he, ← hi]
    exact realCoordinates_simple M b hb hcartan j v
  | one =>
    refine ⟨1, e6Weyl.one_mem, fun v => ?_⟩
    change realCoordinates M b ((1 : P.Aut).coweightEquiv.symm v) = realCoordinates M b v
    have he : (1 : P.Aut).coweightEquiv = LinearEquiv.refl ℤ (MarkedCocharacters M) :=
      LinearEquiv.toLinearMap_inj.mp (RootPairing.Equiv.coweightEquiv_one P)
    rw [he, LinearEquiv.refl_symm, LinearEquiv.refl_apply]
  | mul a c _ _ ha hc =>
    obtain ⟨w, hw, hwa⟩ := ha
    obtain ⟨z, hz, hzc⟩ := hc
    refine ⟨w * z, e6Weyl.mul_mem hw hz, fun v => ?_⟩
    change realCoordinates M b ((a.val * c.val).coweightEquiv.symm v) =
      w (z (realCoordinates M b v))
    rw [RootPairing.Equiv.mul_eq_comp, RootPairing.Equiv.coweightEquiv_comp_toLin,
      LinearEquiv.trans_symm, LinearEquiv.trans_apply, hwa, hzc]


private theorem weyl_add {w : Function.End E6Space} (hw : w ∈ e6Weyl)
    (y z : E6Space) : w (y + z) = w y + w z := by
  revert y z
  induction hw using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨j, rfl⟩ := hf
    intro y z
    simp only [reflection_simple, simpleInner, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    module
  | one => intros; rfl
  | mul u v _ _ hu hv =>
    intro y z
    change u (v (y + z)) = u (v y) + u (v z)
    rw [hv, hu]

private def evalAt (u : ℂˣ) : Cocharacter M.P.pair.T.group →*
    GroupPoints M.P.pair.T.group complexTest where
  toFun c := cocharacterPoint c complexTest u
  map_one' := MonObj.comp_one (unitPoint complexTest u)
  map_mul' c d := MonObj.comp_mul (unitPoint complexTest u) c.hom.hom d.hom.hom

private theorem circleUnit_zpow (s : ℝ) (k : ℤ) :
    circleUnit s ^ k = circleUnit (s * k) := by
  simp only [circleUnit, ← map_zpow, ← Circle.exp_intCast_mul]
  congr 2
  ring

private theorem evalAt_coordinates
    (b : Module.Basis (Fin 6) ℤ (MarkedCocharacters M))
    (hb : ∀ j, b j = Additive.ofMul (M.coroot j))
    (c : Cocharacter M.P.pair.T.group) (s : ℝ) :
    cocharacterPoint c complexTest (circleUnit s) =
      M.torusPoint (s • realCoordinates M b (Additive.ofMul c)) := by
  let v := Additive.ofMul c
  have he := congrArg (fun d : MarkedCocharacters M => d.toMul) (b.sum_repr v)
  simp only [toMul_sum, toMul_zsmul, hb] at he
  let F := evalAt M (circleUnit s)
  have hprod : (∏ j, (evalCochar (M.coroot j) (circleUnit s)) ^ (b.repr v j)) =
      cocharacterPoint c complexTest (circleUnit s) := calc
    _ = ∏ j, F ((M.coroot j) ^ (b.repr v j)) :=
      Finset.prod_congr rfl fun j _ => (F.map_zpow _ _).symm
    _ = F (∏ j, (M.coroot j) ^ (b.repr v j)) := (map_prod F _ _).symm
    _ = _ := congrArg F he
  rw [← hprod, torusPoint_prod]
  apply Finset.prod_congr rfl
  intro j _
  change (evalCochar (M.coroot j) (circleUnit s)) ^ (b.repr v j) =
    evalCochar (M.coroot j) (circleUnit (s * (b.repr v j : ℝ)))
  rw [← circleUnit_zpow]
  exact ((evalCochar (M.coroot j)).map_zpow _ _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem torus_action_on_exp
    (b : Module.Basis (Fin 6) ℤ (MarkedCocharacters M))
    (hb : ∀ j, b j = Additive.ofMul (M.coroot j))
    (a : M.P.pair.T.group ≅ M.P.pair.T.group)
    (w : Function.End E6Space) (hw : w ∈ e6Weyl)
    (hc : ∀ c : Cocharacter M.P.pair.T.group,
      realCoordinates M b (Additive.ofMul (c ≫ a.hom)) =
        w (realCoordinates M b (Additive.ofMul c))) (y : E6Space) :
    M.torusPoint y ≫ a.hom.hom.hom = M.torusPoint (w y) := by
  let f : E6Space →+ Additive (GroupPoints M.P.pair.T.group complexTest) :=
    (((groupPointsFunctor ℂ).map a.hom).app complexTest).hom.comp (torusPointHom M)
      |>.toAdditiveRight
  let wAdd : E6Space →+ E6Space :=
    { toFun := w
      map_zero' := by simpa only [zero_smul] using weyl_smul hw 0 (0 : E6Space)
      map_add' := weyl_add hw }
  let g : E6Space →+ Additive (GroupPoints M.P.pair.T.group complexTest) :=
    (torusPointHom M).toAdditiveRight.comp wAdd
  change f y = g y
  have h (j : Fin 6) (s : ℝ) : f (Pi.single j s) = g (Pi.single j s) := by
    change M.torusPoint (Pi.single j s) ≫ a.hom.hom.hom = M.torusPoint (w (Pi.single j s))
    rw [torusPoint_single]
    change cocharacterPoint (M.coroot j ≫ a.hom) complexTest (circleUnit s) = _
    rw [evalAt_coordinates M b hb, hc, ← hb, realCoordinates_basis, ← weyl_smul hw]
    congr 2
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [← LinearMap.sum_single_apply (v := y), map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => h j (y j)

/-- Compact normalizers act by absolute Weyl elements, and fixing the normalized
twist makes their labels commute with the pinned diagram action. -/
theorem compactWeylLabels_conditional
    (_ : Specs.ExceptionalOuterTorus.FixedNormalizerRepresentatives)
    (_ : Specs.ExceptionalOuterTorus.FixedTorusConjugacy)
    (_ : Specs.ExceptionalOuterTorus.MaximalFixedTorusExistence)
    (_ : Specs.ExceptionalOuterTorus.OuterTorusComparison) :
    Specs.ExceptionalOuterCompactWeylLabels.CompactWeylLabels := by
  intro G i _ _ _ ω θ _ S _ T A M δ hcent htori hcartan hb ha hexp hk hδ n hn hnS
  letI := M.datum.comm
  obtain ⟨b, hb⟩ := hb
  let g := (markedPointsEquiv (i := i) M).symm n
  have hnorm := complex_normalizer M b hb hcent htori hexp hn hnS
  obtain ⟨u, a, hc, hact⟩ := exists_torus_action M g hnorm
  obtain ⟨w, hw, hwc⟩ := exists_real_weyl_action M b hb hcartan u
  have hcoords (c : Cocharacter M.P.pair.T.group) :
      realCoordinates M b (Additive.ofMul (c ≫ a.hom)) =
        w (realCoordinates M b (Additive.ofMul c)) := by
    rw [← hc, hwc]
  have hrep (y : E6Space) :
      n * M.exp y * n⁻¹ = M.exp (i := i) (w y) := by
    have h := hact (M.torusPoint y)
    rw [torus_action_on_exp M b hb a w hw hcoords] at h
    let E := markedPointsEquiv (i := i) M
    let p (z : E6Space) : GroupPoints M.P.pair.G.val complexTest :=
      M.torusPoint z ≫ M.P.pair.T.inclusion.hom.hom
    have hp (z : E6Space) : E (p z) = M.exp z := rfl
    have h' : p (w y) = E.symm n * p y * (E.symm n)⁻¹ := h
    rw [← hp y, ← hp (w y), h', map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  refine ⟨w, hw, hrep, fun x _ _ hfixed => ⟨hw, ?_⟩⟩
  exact fixed_label_commutes (M.exp (i := i)) ha hk δ hδ x hfixed.2 hw hrep

end LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactWeylLabels

theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterCompactWeylLabels».«compactWeylLabels» : _root_.«LinearAlgebraicGroups».«Specs».«ExceptionalOuterCompactWeylLabels».«CompactWeylLabels» :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterCompactWeylLabels».«compactWeylLabels_conditional» (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterTorus».«fixedNormalizerRepresentatives») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterTorus».«fixedTorusConjugacy») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterTorus».«maximalFixedTorusExistence») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalOuterTorus».«outerTorusComparison»)
