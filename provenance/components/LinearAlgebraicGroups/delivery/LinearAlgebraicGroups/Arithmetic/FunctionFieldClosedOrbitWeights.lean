import Specs.LinearAlgebraicGroups.Arithmetic.FunctionFieldClosedOrbitWeights
import LinearAlgebraicGroups.Arithmetic.RationalContraction
import LinearAlgebraicGroups.RootData.SpecialLinearDatum
import LinearAlgebraicGroups.Multiplicative.WeightDecomposition
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.FunctionFieldClosedOrbitWeights

open _root_.LinearAlgebraicGroups.Specs hiding coordinates
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.ClosedHomogeneousOrbits (vectorPoint vectorSpace)
open Specs.FunctionFieldClosedOrbitWeights
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.RootWeightAction (Representation act actLinear extendVector mem_weightSpace)
open Specs.RationalContraction
open Specs.SpecialLinearDatum (CocharacterLattice exponentDot DiagonalTorus)
open CocharacterDynamics (polynomialAlgebra laurentAlgebra polynomialToLaurent
  polynomialEvaluate laurentConstants laurentParameter)
open CocharacterDynamics (cocharacterPoint unitPoint)

open private tailModel tailCharacter tailCharacter_value latticeIdentification
  prod_index
  from LinearAlgebraicGroups.RootData.SpecialLinearDatum
open private torusPoint_weights charactersOfIso
  from LinearAlgebraicGroups.Representation.RootWeightAction
open private splitGroupHomEquiv from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private integerHomEquiv integerPointsIso
  from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private parameter_zpow from LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent
open private unitEquiv unitEquiv_unitPoint
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private act_one vectorPoint_bijective map_vectorPoint
  from LinearAlgebraicGroups.Arithmetic.ClosedHomogeneousOrbits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
  {m : ℕ} {P : AffineAlgebraicGroup k}

private def coordinateEquiv (C : Matrix.GeneralLinearGroup I k) (R : TestAlgebra k) :
    (I → R) ≃ₗ[R] (I → R) :=
  (Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.map (algebraMap k R) C)).toLinearEquiv

private theorem coordinates_inverse (C : Matrix.GeneralLinearGroup I k) (R : TestAlgebra k)
    (v : I → R) : coordinates C⁻¹ R (coordinates C R v) = v := by
  change coordinateEquiv C⁻¹ R (coordinateEquiv C R v) = v
  rw [← LinearEquiv.trans_apply]
  change ((Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.map (algebraMap k R) C⁻¹)) *
    (Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.map (algebraMap k R) C))).toLinearEquiv v = _
  rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  rfl

private theorem coordinates_map (C : Matrix.GeneralLinearGroup I k) {R S : TestAlgebra k}
    (f : R ⟶ S) (v : I → R) :
    coordinates C S (fun i => f.hom (v i)) = fun i => f.hom (coordinates C R v i) := by
  ext i
  simp only [coordinates, Matrix.mulVec, dotProduct, Matrix.GeneralLinearGroup.map_apply,
    map_sum, map_mul, AlgHom.commutes]

private theorem exists_diagonalizing_matrix (ρ : Representation P.val I)
    {T : ClosedSubgroup P.val} (d : Module.Basis I k (I → k))
    (χ : I → Specs.CharacterDescent.Character T.group)
    (hχ : ∀ i, d i ∈ Specs.RootWeightAction.weightSpace ρ T (χ i)) :
    ∃ C : Matrix.GeneralLinearGroup I k,
      ∀ (R : TestAlgebra k) (t : GroupPoints T.group R) (v : I → R) (i : I),
        coordinates C R (act ρ R (t ≫ T.inclusion.hom.hom) v) i =
          Specs.CharacterPairing.characterValue (χ i) R t * coordinates C R v i := by
  let S : Matrix.GeneralLinearGroup I k := Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv d.equivFun.symm)
  refine ⟨S⁻¹, fun R t v i => ?_⟩
  let e := Pi.basisFun R I
  let g := t ≫ T.inclusion.hom.hom
  let f := coordinateEquiv S R
  let c := coordinateEquiv S⁻¹ R
  have hcol (j : I) : f (e j) = extendVector R (d j) := by
    have hbase : coordinates S (groundField k) (Pi.single j 1) = d j := by
      change (Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.map (algebraMap k k) S)).toLinearEquiv
        (Pi.single j 1) = _
      rw [Algebra.algebraMap_self, Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply]
      rw [show Matrix.GeneralLinearGroup.toLin S = LinearMap.GeneralLinearGroup.ofLinearEquiv
        d.equivFun.symm from Matrix.GeneralLinearGroup.toLin.apply_symm_apply _]
      change d.equivFun.symm (Pi.single j 1) = _
      apply d.equivFun.injective
      simp [Module.Basis.equivFun_apply]
    let f₀ : groundField k ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
    have hn := coordinates_map S f₀ (Pi.single j 1)
    have hs : (fun l => f₀.hom ((Pi.single j 1 : I → k) l)) = e j := by
      rw [Pi.basisFun_apply]
      ext l
      by_cases h : l = j <;> simp [h]
    rw [hs, hbase] at hn
    exact hn
  have hcf (z : I → R) : c (f z) = z := coordinates_inverse S R z
  let value := Specs.CharacterPairing.characterValue (χ i) R t
  have he : (LinearMap.proj i).comp (c.toLinearMap.comp ((actLinear ρ R g).comp f.toLinearMap)) =
      value • (LinearMap.proj i : (I → R) →ₗ[R] R) := by
    apply e.ext
    intro j
    change c (act ρ R g (f (e j))) i = value * e j i
    have h := (mem_weightSpace.mp (hχ j) R t)
    change act ρ R g (extendVector R (d j)) =
      Specs.CharacterPairing.characterValue (χ j) R t • extendVector R (d j) at h
    rw [hcol j, h, ← hcol j, map_smul, hcf]
    by_cases hj : j = i
    · subst j
      rfl
    · simp [e, Pi.basisFun_apply, Ne.symm hj]
  have hv := DFunLike.congr_fun he (c v)
  have hfc : f (c v) = v := by
    change coordinates S R (coordinates S⁻¹ R v) = v
    simpa only [inv_inv] using coordinates_inverse S⁻¹ R v
  change c (act ρ R g (f (c v))) i = value * c v i at hv
  rw [hfc] at hv
  exact hv

private theorem trivial_of_cocharacter_matrix (s : SpecialMatrixPoints P m)
    (n : CocharacterLattice m) (c : Cocharacter P.val)
    (hc : ∀ (R : TestAlgebra k) (t : Rˣ), (s.hom.app R (cocharacterPoint c R t)).val =
      Matrix.diagonal (fun j => (↑(t ^ n.val j.down) : R))) :
    c.hom.hom = toUnit _ ≫ η[P.val.X] ↔ n = 0 := by
  constructor
  · intro h
    let R := laurentAlgebra (groundField k)
    have h₁ : cocharacterPoint c R (laurentParameter (groundField k)) = 1 := by
      change unitPoint R (laurentParameter (groundField k)) ≫ c.hom.hom = _
      rw [h, comp_toUnit_assoc]
      rfl
    apply Subtype.ext
    funext j
    have hm := hc R (laurentParameter (groundField k))
    rw [h₁, map_one] at hm
    have hd := congrArg (fun M : Matrix (ULift.{u} (Fin m)) _ R => M ⟨j⟩ ⟨j⟩) hm
    have ht : LaurentPolynomial.T (n.val j) = LaurentPolynomial.T (R := k) 0 := by
      have hd' : (laurentParameter (groundField k) ^ n.val j).val = 1 := by
        simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq,
          Matrix.diagonal_apply_eq] using hd.symm
      exact (parameter_zpow (groundField k) (n.val j)).symm.trans
        (hd'.trans LaurentPolynomial.T_zero.symm)
    have hsingle := congrArg (fun f : LaurentPolynomial k => f.coeff (n.val j)) ht
    change n.val j = 0
    by_contra hn
    change (AddMonoidAlgebra.single (n.val j) (1 : k)).coeff (n.val j) =
      (AddMonoidAlgebra.single 0 (1 : k)).coeff (n.val j) at hsingle
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hn, one_ne_zero] at hsingle
  · rintro rfl
    let R := CommAlgCat.of k (MonoidAlgebra k IntegerCharacters.{u})
    let t : Rˣ := (unitEquiv R) (𝟙 _)
    have ht : unitPoint R t = 𝟙 _ := (unitEquiv R).injective (unitEquiv_unitPoint R t)
    have he := hc R t
    change (s.hom.app R (unitPoint R t ≫ c.hom.hom)).val = _ at he
    rw [ht, Category.id_comp] at he
    have h₁ : (s.hom.app R (c.hom.hom : GroupPoints P.val R)).val =
        (s.hom.app R (1 : GroupPoints P.val R)).val := by
      rw [he, map_one]
      simp
    apply ((s.app R).groupIsoToMulEquiv).injective
    exact Subtype.ext h₁

private theorem coordinates_of_diagonal_torus {r : ℕ} (s : SpecialMatrixPoints P (r + 1))
    (ρ : Representation P.val I) (T : DiagonalTorus s) :
    Nonempty (DiagonalWeightCoordinates s ρ) := by
  classical
  let M := Multiplicative (ULift.{u} (Fin r) → ℤ)
  let : DecidableEq M := Classical.decEq _
  let χ₀ : M ≃* Specs.CharacterDescent.Character (specGroup (groupAlgebra k M)) :=
    (integerHomEquiv M).trans (splitGroupHomEquiv (k := k) IntegerCharacters M)
  have hχ₀ (w : M) : χ₀ w = specGroupMap (Specs.DiagonalizableGroups.groupAlgebraMap k
      ((zpowersHom M w).comp MulEquiv.ulift.toMonoidHom)) := rfl
  obtain ⟨τ, hτ⟩ := torusPoint_weights ρ (tailModel T).symm χ₀ hχ₀
  let b (w : M) := Module.Free.chooseBasis k (LinearAlgebraicGroups.WeightDecomposition.weightSpace τ w)
  let h := LinearAlgebraicGroups.WeightDecomposition.weightDecomposition τ
  let d₀ := h.collectedBasis b
  let J := Σ w : M, Module.Free.ChooseBasisIndex k (LinearAlgebraicGroups.WeightDecomposition.weightSpace τ w)
  let : Finite J := Module.Finite.finite_basis d₀
  let : Fintype J := Fintype.ofFinite J
  have hc : Fintype.card J = Fintype.card I :=
    (Module.finrank_eq_card_basis d₀).symm.trans (Module.finrank_eq_card_basis (Pi.basisFun k I))
  let e : J ≃ I := Fintype.equivOfCardEq hc
  let d := d₀.reindex e
  let w (i : I) := (e.symm i).1
  have hw (i : I) : d i ∈ Specs.RootWeightAction.weightSpace ρ T.subgroup (tailCharacter T (w i)) := by
    change d i ∈ Specs.RootWeightAction.weightSpace ρ T.subgroup
      (charactersOfIso (tailModel T).symm (χ₀ (w i)))
    rw [hτ, show d i = d₀ (e.symm i) from d₀.reindex_apply e i]
    exact h.collectedBasis_mem b (e.symm i)
  obtain ⟨C, hC⟩ := exists_diagonalizing_matrix ρ d (fun i => tailCharacter T (w i)) hw
  let a (i : I) : Fin (r + 1) → ℤ := Fin.cons 0 (fun j => (w i).toAdd ⟨j⟩)
  let L := latticeIdentification T
  let := L.comm
  let c (n : CocharacterLattice (r + 1)) : Cocharacter P.val :=
    Additive.toMul (L.cocharacters.symm n) ≫ T.subgroup.inclusion
  have hm (n : CocharacterLattice (r + 1)) (R : TestAlgebra k) (t : Rˣ) :
      (s.hom.app R (cocharacterPoint (c n) R t)).val =
        Matrix.diagonal (fun j => (↑(t ^ n.val j.down) : R)) :=
    L.cocharacterPoint_eq n R t
  have ha (R : TestAlgebra k) (dR : Fin (r + 1) → Rˣ) (g : GroupPoints P.val R)
      (hg : (s.hom.app R g).val = Matrix.diagonal (fun i => (dR i.down).val))
      (v : I → R) (i : I) :
      coordinates C R (act ρ R g v) i =
        (↑(∏ j : Fin (r + 1), dR j ^ a i j) : R) * coordinates C R v i := by
    obtain ⟨t, ht⟩ := (T.range R g).mpr (fun i j hij => by rw [hg, Matrix.diagonal_apply_ne _ hij])
    have hd := T.matrix R t
    change t ≫ T.subgroup.inclusion.hom.hom = g at ht
    rw [ht, hg] at hd
    have hentries (j : ULift.{u} (Fin (r + 1))) :
        Specs.SpecialLinearDatum.determinantOneUnits (T.pointsIso.hom.app R t) j = dR j.down := by
      apply Units.ext
      exact (congrFun (Matrix.diagonal_injective hd) j).symm
    rw [← ht, hC, tailCharacter_value, Fin.prod_univ_succ]
    change _ * _ = (↑(dR 0 ^ (0 : ℤ) * ∏ j : Fin r, dR j.succ ^ (w i).toAdd ⟨j⟩) : R) * _
    rw [zpow_zero, one_mul, prod_index]
    simp only [← hentries, Specs.SpecialLinearDatum.determinantOneUnits, Fin.cons_succ]
  refine ⟨⟨C, a, c, ha, hm, ?_, fun n => trivial_of_cocharacter_matrix s n (c n) (hm n)⟩⟩
  intro n R t v i
  rw [ha R (fun j => t ^ n.val j) _ (hm n R t)]
  congr 2
  simp only [exponentDot, LinearMap.coe_mk, AddHom.coe_mk, ← zpow_mul]
  rw [show (∏ j : Fin (r + 1), t ^ (n.val j * a i j)) =
      (zpowersHom Rˣ t) (∏ j : Fin (r + 1), Multiplicative.ofAdd (n.val j * a i j)) by
    rw [map_prod]; rfl, ← ofAdd_sum]
  change t ^ (∑ j, n.val j * a i j) = t ^ (∑ j, a i j * n.val j)
  simp only [mul_comm (n.val _) (a i _)]

theorem existsDiagonalWeightCoordinates : ExistsDiagonalWeightCoordinates.{u} := by
  intro k _ m P s I _ _ ρ
  cases m with
  | succ r =>
    obtain ⟨T, _⟩ := RootData.SpecialLinearDatum.splitDiagonalTorus k r P s
    exact coordinates_of_diagonal_torus s ρ T
  | zero =>
    let c : Cocharacter P.val := Grp.homMk'' (toUnit _ ≫ η[P.val.X])
      (by rw [comp_toUnit_assoc]; rfl) (by
        change μ[_] ≫ (1 : _ ⟶ P.val.X) =
          ((1 : _ ⟶ P.val.X) ⊗ₘ (1 : _ ⟶ P.val.X)) ≫ μ[P.val.X]
        simp only [MonObj.comp_one, ← lift_fst_comp_snd_comp, ← Hom.mul_def, one_mul])
    have hm (n : CocharacterLattice 0) (R : TestAlgebra k) (t : Rˣ) :
        (s.hom.app R (cocharacterPoint c R t)).val =
          Matrix.diagonal (fun j => (↑(t ^ n.val j.down) : R)) :=
      Matrix.ext fun i _ => Fin.elim0 i.down
    refine ⟨⟨1, 0, fun _ => c, ?_, hm, ?_,
      fun n => trivial_of_cocharacter_matrix s n c (hm n)⟩⟩
    · intro R d g _ v i
      have hg : g = 1 := by
        apply ((s.app R).groupIsoToMulEquiv).injective
        exact Subtype.ext (Matrix.ext fun j _ => Fin.elim0 j.down)
      rw [hg, act_one]
      simp
    · intro n R t v i
      have hc : cocharacterPoint c R t = 1 := by
        change unitPoint R t ≫ (toUnit _ ≫ η[P.val.X]) = _
        rw [comp_toUnit_assoc]
        rfl
      rw [hc, act_one]
      simp [exponentDot]

open private closedImmersion_over_affineSpec factorsThrough_affineQuotient quotientProjection
  from LinearAlgebraicGroups.Affine.FixedPointSchemes

/-- Polynomial points satisfy the equations of the closed subscheme if their
Laurent extensions satisfy those equations. -/
private theorem polynomial_point_factors {A R : TestAlgebra k} {X : SchemeOver k}
    (j : X ⟶ (testSpec k).obj (op A)) (hj : IsClosedImmersion j.left)
    (y : Points ((testSpec k).obj (op A)) (polynomialAlgebra R))
    (z : Points X (laurentAlgebra R))
    (hz : z ≫ j = mapPoints (polynomialToLaurent R) y) :
    ∃ x : Points X (polynomialAlgebra R), x ≫ j = y := by
  obtain ⟨J, e, he⟩ := closedImmersion_over_affineSpec j hj
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let f := (F.preimage y).unop
  have hf : (testSpec k).map f.op = y := F.map_preimage _
  have hpre :
      (F.preimage (mapPoints (polynomialToLaurent R) y)).unop = f ≫ polynomialToLaurent R := by
    apply Quiver.Hom.op_inj
    apply F.map_injective
    rw [Quiver.Hom.op_unop, F.map_preimage, op_comp, Functor.map_comp, hf]
  have hJ : J ≤ RingHom.ker (f ≫ polynomialToLaurent R).hom := by
    rw [← hpre, ← factorsThrough_affineQuotient]
    exact ⟨z ≫ e.hom, by simpa only [he, Category.assoc] using hz⟩
  obtain ⟨x, hx⟩ := (factorsThrough_affineQuotient J y).mpr
    (show J ≤ RingHom.ker f.hom from fun a ha => Polynomial.toLaurent_injective
      (show (polynomialToLaurent R).hom (f.hom a) = Polynomial.toLaurent 0 from
        (hJ ha).trans (map_zero Polynomial.toLaurent).symm))
  exact ⟨x ≫ e.inv, by rw [Category.assoc, he, e.inv_hom_id_assoc, hx]⟩

open Specs.RationalContraction (ActionHasLimit actionCurve)

private theorem action_limit_of_nonnegative_weights {s : SpecialMatrixPoints P m}
    {ρ : Representation P.val I} (D : DiagonalWeightCoordinates s ρ)
    {X : SchemeOver k} (a : ModObj P.val.X (vectorSpace k I)) (b : ModObj P.val.X X)
    (j : X ⟶ vectorSpace k I) (hj : IsClosedImmersion j.left)
    (hEq : b.smul ≫ j = (𝟙 P.val.X ⊗ₘ j) ≫ a.smul)
    (hAction : ∀ (R : TestAlgebra k) (g : GroupPoints P.val R) (v : I → R),
      lift g (vectorPoint R v) ≫ a.smul = vectorPoint R (act ρ R g v))
    (x : Points X (groundField k)) (v : I → k)
    (hv : x ≫ j = vectorPoint (groundField k) v)
    (n : CocharacterLattice m)
    (h : ∀ i, coordinates D.changeBasis (groundField k) v i ≠ 0 → 0 ≤ D.weight i n) :
    ∃ x₀, ActionHasLimit b (D.cocharacter n) x x₀ := by
  let K := groundField k
  let R := polynomialAlgebra K
  let L := laurentAlgebra K
  let p := polynomialToLaurent K
  let l := laurentConstants K
  let t := cocharacterPoint (D.cocharacter n) L (laurentParameter K)
  let vL : I → L := fun i => l.hom (v i)
  let u : I → k := coordinates D.changeBasis K v
  let w : I → R := fun i => Polynomial.monomial (D.weight i n).toNat (u i)
  let z := coordinates D.changeBasis⁻¹ R w
  have hL : (fun i => p.hom (z i)) = act ρ L t vL := by
    apply (coordinateEquiv D.changeBasis L).injective
    change coordinates D.changeBasis L (fun i => p.hom (z i)) =
      coordinates D.changeBasis L (act ρ L t vL)
    rw [coordinates_map, show coordinates D.changeBasis R z = w by
      simpa only [inv_inv] using coordinates_inverse D.changeBasis⁻¹ R w]
    funext i
    rw [D.cocharacter_action, show coordinates D.changeBasis L vL = fun j => l.hom (u j) from
      coordinates_map D.changeBasis l v]
    change Polynomial.toLaurent (Polynomial.monomial (D.weight i n).toNat (u i)) =
      (laurentParameter K ^ D.weight i n).val * LaurentPolynomial.C (u i)
    rw [parameter_zpow, Polynomial.toLaurent_C_mul_T]
    by_cases hu : u i = 0
    · rw [hu, map_zero, zero_mul, mul_zero]
    · rw [Int.toNat_of_nonneg (h i hu), mul_comm]
  let curve := actionCurve b (D.cocharacter n) x
  have hcurve : curve ≫ j = mapPoints p (vectorPoint R z) := by
    calc
      curve ≫ j = lift t (mapPoints l x ≫ j) ≫ a.smul := by
        simp only [curve, actionCurve, Category.assoc, hEq, lift_map_assoc, Category.comp_id]
        rfl
      _ = mapPoints p (vectorPoint R z) := by
        change lift t (mapPoints l (x ≫ j)) ≫ a.smul = _
        rw [hv, map_vectorPoint, hAction, map_vectorPoint, hL]
  obtain ⟨y, hy⟩ := polynomial_point_factors j hj (vectorPoint R z) curve hcurve
  refine ⟨mapPoints (polynomialEvaluate K 0) y, y, ?_, rfl⟩
  let := hj
  let : Mono j := Over.mono_of_mono_left _
  apply (cancel_mono j).mp
  exact (Category.assoc _ _ _).trans (by rw [hy, hcurve])

open private conjugation conjugation_apply conjugationIso factor_group_through_subgroup
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private groupIsoOfPointIso from LinearAlgebraicGroups.Affine.IdentityTangent

private def rankOneTorusIso :
    specGroup (groupAlgebra k IntegerCharacters.{u}) ≅
      (Specs.StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin 1))).val := by
  let J := ULift.{u} (Fin 1)
  let e : Specs.StandardGroups.multiplicativePowerPoints k J ≅
      Specs.StandardGroups.multiplicativePoints k :=
    NatIso.ofComponents (fun R => (MulEquiv.funUnique J Rˣ).toGrpIso) (by
      intro R S f
      apply GrpCat.ext
      intro x
      rfl)
  letI : IsAffine (specGroup (groupAlgebra k IntegerCharacters.{u})).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k IntegerCharacters.{u}))))
  letI := (Specs.StandardGroups.multiplicativePowerGroup k J).property.1
  exact groupIsoOfPointIso (DiagonalizableGroups.groupAlgebraPointsIso k IntegerCharacters ≪≫
    integerPointsIso ≪≫ e.symm ≪≫ (StandardGroups.multiplicativePowerGroupPointsIso k J).symm)

private theorem split_torus_in_stabilizer {H : ClosedSubgroup P.val} {X V : SchemeOver k}
    (q : P.val.X ⟶ X) (j : X ⟶ V)
    (a : ModObj P.val.X V) (b : ModObj P.val.X X)
    (hEq : b.smul ≫ j = (𝟙 P.val.X ⊗ₘ j) ≫ a.smul)
    (hProj : q ≫ j = Specs.SmoothOrbit.orbitMap a (η[P.val.X] ≫ q ≫ j))
    (hStab : RepresentsSubgroup H (fun _ g => Stabilizes a.smul (η[P.val.X] ≫ q ≫ j) g))
    (g u : GroupPoints P.val (groundField k)) (c : Cocharacter P.val)
    (hS : HasConjugateSplitTorus b c u (g⁻¹ ≫ q)) :
    ¬ HasNoPositiveRankSplitTorus H.group := by
  obtain ⟨S, _, ⟨iso⟩, _, _, hfix⟩ := hS
  let g₀ := (groundPointIso k).hom ≫ g
  let T := S.group.X
  let s := S.inclusion.hom.hom
  let d : T ⟶ P.val.X := toUnit T ≫ g₀
  let x := η[P.val.X] ≫ q ≫ j
  let y := (groundPointIso k).hom ≫ g⁻¹ ≫ q
  let := a
  have hy : toUnit T ≫ y ≫ j = d⁻¹ • (toUnit T ≫ x) := by
    let e := toUnit T ≫ (groundPointIso k).hom
    let g' : (testSpec k).obj (op (groundField k)) ⟶ P.val.X := g⁻¹
    have hd : e ≫ g' = d⁻¹ := by
      change e ≫ (g : (testSpec k).obj (op (groundField k)) ⟶ P.val.X)⁻¹ = d⁻¹
      rw [GrpObj.comp_inv]
      exact congrArg Inv.inv (Category.assoc _ _ _)
    calc
      toUnit T ≫ y ≫ j = (e ≫ g') ≫ (q ≫ j) := by simp only [e, g', y, Category.assoc]
      _ = d⁻¹ • (toUnit T ≫ x) := by
        rw [hProj, hd, Specs.SmoothOrbit.orbitMap, comp_lift_assoc, Category.comp_id,
          comp_toUnit_assoc, Hom.smul_def]
  have hs : s • (toUnit T ≫ y ≫ j) = toUnit T ≫ y ≫ j := by
    have hb := congrArg (· ≫ j) (hfix T (𝟙 T))
    change (lift (𝟙 T ≫ s) (toUnit T ≫ y) ≫ b.smul) ≫ j =
      (toUnit T ≫ y) ≫ j at hb
    simpa only [Hom.smul_def, Category.id_comp, Category.assoc, hEq, lift_map_assoc, Category.comp_id] using hb
  let f : S.group ⟶ P.val := S.inclusion ≫ conjugation g₀
  have hf : Stabilizes a.smul x f.hom.hom := by
    change (s ≫ (conjugation g₀).hom.hom) • (toUnit T ≫ x) = _
    rw [conjugation_apply]
    change (d * s * d⁻¹) • (toUnit T ≫ x) = _
    rw [hy] at hs
    rw [mul_smul, mul_smul, hs, smul_inv_smul]
  obtain ⟨i, hi⟩ := (hStab T f.hom.hom).mp hf
  obtain ⟨l, hl⟩ := factor_group_through_subgroup H f i hi
  let := S.isClosedImmersion
  let := H.isClosedImmersion
  let : IsIso (conjugation g₀).hom.hom.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso (conjugationIso g₀).hom
  have : IsClosedImmersion (l.hom.hom.left ≫ H.inclusion.hom.hom.left) := by
    rw [show l.hom.hom.left ≫ H.inclusion.hom.hom.left =
        S.inclusion.hom.hom.left ≫ (conjugation g₀).hom.hom.left from
      congrArg (fun v : S.group ⟶ P.val => v.hom.hom.left) hl]
    infer_instance
  have hClosed : IsClosedImmersion l.hom.hom.left :=
    IsClosedImmersion.of_comp_isClosedImmersion l.hom.hom.left H.inclusion.hom.hom.left
  exact fun h => h ⟨⟨S.group, l, hClosed⟩, 1, Nat.zero_lt_one, ⟨iso ≪≫ rankOneTorusIso⟩⟩

theorem closedOrbitWeightCriterion : ClosedOrbitWeightCriterion.{u} := by
  classical
  intro k _ p _ _ m P s H hH
  obtain ⟨Q, I, _, _, ρ, a, b, j, hAff, hTor, hSmooth, hClosed, hAction, hEq, hProj, hStab, hContract⟩ :=
    RationalContraction.rationalContraction k p m P s H hH
  obtain ⟨D⟩ := existsDiagonalWeightCoordinates k m P s I ρ
  let v (g : GroupPoints P.val (groundField k)) : I → k :=
    (vectorPoint_bijective (groundField k)).2 (g⁻¹ ≫ Q.projection ≫ j) |>.choose
  have hv (g : GroupPoints P.val (groundField k)) :
      vectorPoint (groundField k) (v g) = g⁻¹ ≫ Q.projection ≫ j :=
    ((vectorPoint_bijective (groundField k)).2 (g⁻¹ ≫ Q.projection ≫ j)).choose_spec
  refine ⟨Q, I, inferInstance, inferInstance, ρ, a, b, j, D, v,
    hAff, hTor, hSmooth, hClosed, hAction, hEq, hProj, hStab, hv, ?_⟩
  intro g n hn
  obtain ⟨x₀, hx₀⟩ := action_limit_of_nonnegative_weights D a b j hClosed hEq hAction
    (g⁻¹ ≫ Q.projection) (v g) ((Category.assoc _ _ _).trans (hv g).symm) n hn
  refine ⟨⟨x₀, hx₀⟩, fun hAniso => ?_⟩
  by_contra hnonzero
  obtain ⟨u, _, _, h⟩ := hContract (D.cocharacter n) (g⁻¹ ≫ Q.projection) x₀ hx₀
  have hS := h (fun ht => hnonzero ((D.trivial_iff n).mp ht))
  exact split_torus_in_stabilizer Q.projection j a b hEq hProj hStab g u
    (D.cocharacter n) hS hAniso

end
end LinearAlgebraicGroups.Arithmetic.FunctionFieldClosedOrbitWeights
