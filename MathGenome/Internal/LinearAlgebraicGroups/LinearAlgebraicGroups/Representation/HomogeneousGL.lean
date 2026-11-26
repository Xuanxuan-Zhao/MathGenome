import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.HomogeneousGL
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.NonsplitSymmetricPower
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.PolynomialGL
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.LengthBound
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Group.Int.TypeTags

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.NonsplitSymmetricPower
open CategoryTheory
open scoped BigOperators

universe u

namespace LinearAlgebraicGroups.Representation.HomogeneousGL

open LinearAlgebraicGroups.Specs
open Specs.HomogeneousGL Specs.PolynomialGL StandardGroups
open Unipotent (Index)
open RootWeightAction (extendVector)
open LaurentPolynomial (T C)

open private representationAt_natural twist_matrix evaluation_generic evaluation_comp contract_mulVec extend_mulVec
  universalPoint genericDeterminant_ne_zero away_algebraMap_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.PolynomialGL
open private orbit_le_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.PrimitiveLine

noncomputable section

variable {k m I : Type u} [Field k] [Fintype m] [DecidableEq m] [Fintype I] [DecidableEq I]

private def laurentUnits (R : Type u) [CommRing R] :
    Multiplicative ℤ →* (LaurentPolynomial R)ˣ where
  toFun d := ⟨T d.toAdd, T (-d.toAdd),
    by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero],
    by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]⟩
  map_one' := Units.ext LaurentPolynomial.T_zero
  map_mul' a b := Units.ext (LaurentPolynomial.T_add a.toAdd b.toAdd)

private abbrev variableUnit (R : Type u) [CommRing R] : (LaurentPolynomial R)ˣ :=
  laurentUnits R (Multiplicative.ofAdd 1)

private theorem variableUnit_zpow {R : Type u} [CommRing R] (d : ℤ) :
    (variableUnit R ^ d).val = (T d : LaurentPolynomial R) := by
  rw [← map_zpow]
  change T ((Multiplicative.ofAdd (1 : ℤ) ^ d).toAdd) = _
  simp

private def laurentEval (R : TestAlgebra k) (z : Rˣ) : LaurentPolynomial k →ₐ[k] R :=
  { LaurentPolynomial.eval₂ (algebraMap k R) z with
    commutes' := fun a => LaurentPolynomial.eval₂_C _ _ a }

private theorem laurentEval_unit (R : TestAlgebra k) (z : Rˣ) :
    Units.map (laurentEval R z).toMonoidHom (variableUnit k) = z := by
  apply Units.ext
  change LaurentPolynomial.eval₂ (algebraMap k R) z (T 1) = z.val
  simp

private abbrev scalarMatrix (ρ : MatrixRepresentation k m I) (R : TestAlgebra k) (z : Rˣ) :=
  (representationAt ρ R (Matrix.GeneralLinearGroup.scalar m z)).val

private theorem scalarMatrix_mul (ρ : MatrixRepresentation k m I) (R : TestAlgebra k)
    (z w : Rˣ) : scalarMatrix ρ R (z * w) = scalarMatrix ρ R z * scalarMatrix ρ R w := by
  change (representationAt ρ R ((Matrix.GeneralLinearGroup.scalar m) (z * w))).val = _
  rw [map_mul, map_mul]
  rfl

private theorem scalarMatrix_central (ρ : MatrixRepresentation k m I) (R : TestAlgebra k)
    (z : Rˣ) (g : Matrix.GeneralLinearGroup m R) :
    scalarMatrix ρ R z * (representationAt ρ R g).val =
      (representationAt ρ R g).val * scalarMatrix ρ R z :=
  calc
    _ = (representationAt ρ R (Matrix.GeneralLinearGroup.scalar m z * g)).val := by rw [map_mul]; rfl
    _ = (representationAt ρ R (g * Matrix.GeneralLinearGroup.scalar m z)).val :=
      congrArg (fun a => (representationAt ρ R a).val) (Matrix.GeneralLinearGroup.scalar_commute z g)
    _ = _ := by rw [map_mul]; rfl

/-- The orbit of a vector at the universal scalar unit. -/
private def scalarOrbit (ρ : MatrixRepresentation k m I) (v : I → k) :
    I → LaurentPolynomial k :=
  (scalarMatrix ρ (CommAlgCat.of k (LaurentPolynomial k)) (variableUnit k)).mulVec
    (extendVector (CommAlgCat.of k (LaurentPolynomial k)) v)

private theorem scalarOrbit_eval (ρ : MatrixRepresentation k m I) (v : I → k)
    (R : TestAlgebra k) (z : Rˣ) :
    (fun i => laurentEval R z (scalarOrbit ρ v i)) = (scalarMatrix ρ R z).mulVec (extendVector R v) := by
  let S := CommAlgCat.of k (LaurentPolynomial k)
  let f : S ⟶ R := CommAlgCat.ofHom (laurentEval R z)
  have h := congrArg Units.val (representationAt_natural f ρ
    (Matrix.GeneralLinearGroup.scalar m (variableUnit k)))
  rw [Matrix.GeneralLinearGroup.map_scalar] at h
  change ((scalarMatrix ρ S (variableUnit k)).map (laurentEval R z)) =
    scalarMatrix ρ R (Units.map (laurentEval R z).toMonoidHom (variableUnit k)) at h
  rw [laurentEval_unit] at h
  funext i
  change laurentEval R z ((scalarMatrix ρ S (variableUnit k)).mulVec (extendVector S v) i) = _
  have hcoeff (a : k) : laurentEval R z (algebraMap k S a) = algebraMap k R a :=
    (laurentEval R z).commutes a
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, extendVector, hcoeff]
  exact congrArg (fun A : Matrix I I R => ∑ j, A i j * algebraMap k R (v j)) h

private theorem coeff_const_mul {R : Type u} [CommRing R] (a : R) (p : LaurentPolynomial R) (d : ℤ) :
    (C a * p).coeff d = a * p.coeff d := by
  rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply, neg_zero, zero_add]

private theorem coeff_eval_scaled {R : TestAlgebra k} (z : Rˣ) (p : LaurentPolynomial k) (d : ℤ) :
    (laurentEval (CommAlgCat.of k (LaurentPolynomial R)) (Units.map C.toMonoidHom z *
      variableUnit R) p).coeff d = (z ^ d).val * algebraMap k R (p.coeff d) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, mul_add]
  | C_mul_T j a =>
    let x := Units.map (C (R := R)).toMonoidHom z * variableUnit R
    have hpower : (x ^ j).val = C (z ^ j).val * T j := by
      dsimp only [x]
      rw [mul_zpow, Units.val_mul, ← map_zpow, variableUnit_zpow]
      rfl
    change (LaurentPolynomial.eval₂ (algebraMap k (LaurentPolynomial R)) x (C a * T j)).coeff d = _
    rw [LaurentPolynomial.eval₂_C_mul_T, hpower, LaurentPolynomial.algebraMap_apply,
      ← mul_assoc, ← map_mul, coeff_const_mul, coeff_const_mul,
      LaurentPolynomial.T_apply, LaurentPolynomial.T_apply]
    by_cases h : j = d
    · subst j
      simp only [ite_true, mul_one]
      exact mul_comm _ _
    · simp only [ite_eq_right h, mul_zero, map_zero, mul_zero]

/-- Coefficient extraction in the Laurent coordinate ring projects to each scalar weight. -/
private def scalarProjection (ρ : MatrixRepresentation k m I) (d : ℤ) :
    (I → k) →ₗ[k] (I → k) where
  toFun v i := (scalarOrbit ρ v i).coeff d
  map_add' v w := by
    funext i
    let S := CommAlgCat.of k (LaurentPolynomial k)
    have he : extendVector S (v + w) = extendVector S v + extendVector S w :=
      (RootWeightAction.extendLinear S).map_add v w
    change ((scalarMatrix ρ S (variableUnit k)).mulVec (extendVector S (v + w)) i).coeff d =
      (scalarOrbit ρ v i).coeff d + (scalarOrbit ρ w i).coeff d
    rw [he, Matrix.mulVec_add]
    rfl
  map_smul' a v := by
    funext i
    change (scalarOrbit ρ (a • v) i).coeff d = a * (scalarOrbit ρ v i).coeff d
    have he : extendVector (CommAlgCat.of k (LaurentPolynomial k)) (a • v) =
        C a • extendVector (CommAlgCat.of k (LaurentPolynomial k)) v := by
      funext j
      change C (a * v j) = C a * C (v j)
      exact map_mul C a (v j)
    rw [scalarOrbit, he, Matrix.mulVec_smul]
    change (C a * scalarOrbit ρ v i).coeff d = _
    exact coeff_const_mul _ _ _

private theorem scalarProjection_mem (ρ : MatrixRepresentation k m I) (d : ℤ) (v : I → k) :
    scalarProjection ρ d v ∈ degreeSpace ρ d := by
  rw [mem_degreeSpace]
  intro R z
  let S := CommAlgCat.of k (LaurentPolynomial R)
  let f : R ⟶ S := CommAlgCat.ofHom
    { C with commutes' := fun a => (LaurentPolynomial.algebraMap_apply a).symm }
  have h := congrArg Units.val (representationAt_natural f ρ (Matrix.GeneralLinearGroup.scalar m z))
  rw [Matrix.GeneralLinearGroup.map_scalar] at h
  change (scalarMatrix ρ R z).map C = scalarMatrix ρ S (Units.map C.toMonoidHom z) at h
  have hprod := scalarOrbit_eval ρ v S (Units.map C.toMonoidHom z * variableUnit R)
  rw [scalarMatrix_mul, ← h, ← Matrix.mulVec_mulVec] at hprod
  funext i
  have hc := congrArg (fun v : I → LaurentPolynomial R => (v i).coeff d) hprod
  change _ = (((scalarMatrix ρ R z).map C).mulVec
    ((scalarMatrix ρ S (variableUnit R)).mulVec (extendVector S v)) i).coeff d at hc
  rw [← scalarOrbit_eval ρ v S (variableUnit R)] at hc
  have hcoeff (p : LaurentPolynomial k) :
      (laurentEval S (variableUnit R) p).coeff d = algebraMap k R (p.coeff d) := by
    simpa [S] using coeff_eval_scaled (1 : Rˣ) p d
  change ((laurentEval S (Units.map C.toMonoidHom z * variableUnit R)) (scalarOrbit ρ v i)).coeff d = _ at hc
  rw [coeff_eval_scaled] at hc
  simpa only [Matrix.mulVec, dotProduct, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Matrix.map_apply, coeff_const_mul, hcoeff, extendVector, scalarProjection,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul] using hc.symm

private theorem scalarProjection_of_mem {ρ : MatrixRepresentation k m I} {d : ℤ} {v : I → k}
    (hv : v ∈ degreeSpace ρ d) (b : ℤ) :
    scalarProjection ρ b v = if d = b then v else 0 := by
  have he := (mem_degreeSpace.mp hv) (CommAlgCat.of k (LaurentPolynomial k)) (variableUnit k)
  rw [variableUnit_zpow] at he
  funext i
  have h := congrArg (fun w : I → LaurentPolynomial k => (w i).coeff b) he
  change (scalarProjection ρ b v) i = (T d * C (v i)).coeff b at h
  rw [LaurentPolynomial.T_mul, coeff_const_mul, LaurentPolynomial.T_apply] at h
  split <;> simp_all

private theorem projections_sum (ρ : MatrixRepresentation k m I) (v : I → k) :
    ∃ s : Finset ℤ, ∑ d ∈ s, scalarProjection ρ d v = v := by
  classical
  let s := Finset.univ.biUnion fun i : I => (scalarOrbit ρ v i).coeff.support
  refine ⟨s, ?_⟩
  have he := scalarOrbit_eval ρ v (CommAlgCat.of k k) 1
  funext i
  have hs : (scalarOrbit ρ v i).coeff.support ⊆ s :=
    Finset.subset_biUnion_of_mem (fun j : I => (scalarOrbit ρ v j).coeff.support) (Finset.mem_univ i)
  have hsum : (∑ d ∈ s, C ((scalarOrbit ρ v i).coeff d) * T d) = scalarOrbit ρ v i := by
    apply LaurentPolynomial.ext
    intro d
    simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_const_mul, LaurentPolynomial.T_apply]
    by_cases hd : d ∈ s
    · rw [Finset.sum_eq_single_of_mem d hd (by intro j hj hne; simp [hne])]
      simp
    · have hn := Finsupp.notMem_support_iff.mp (fun hd' => hd (hs hd'))
      rw [hn, Finset.sum_eq_zero (by intro j hj; simp [show j ≠ d from fun h => hd (h ▸ hj)])]
  have hi := congrFun he i
  rw [← hsum] at hi
  change laurentEval _ _ _ = _ at hi
  simpa [laurentEval, scalarMatrix, scalarProjection, extendVector] using hi

private theorem degree_isInternal (ρ : MatrixRepresentation k m I) : DirectSum.IsInternal (degreeSpace ρ) := by
  classical
  change Function.Bijective (DirectSum.coeLinearMap (degreeSpace ρ))
  have hcheck (d : ℤ) :
      (scalarProjection ρ d).comp (DirectSum.coeLinearMap (degreeSpace ρ)) =
        (degreeSpace ρ d).subtype.comp (DirectSum.component k ℤ (fun b => ↥(degreeSpace ρ b)) d) := by
    ext b x
    by_cases hb : b = d
    · subst b
      simp [scalarProjection_of_mem x.property]
    · simp [scalarProjection_of_mem x.property, hb, DirectSum.component.of]
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply DirectSum.ext
    intro d
    apply Subtype.ext
    exact (DFunLike.congr_fun (hcheck d) a).symm.trans
      ((congrArg (scalarProjection ρ d) hab).trans (DFunLike.congr_fun (hcheck d) b))
  · intro v
    obtain ⟨s, hs⟩ := projections_sum ρ v
    refine ⟨∑ d ∈ s, DirectSum.lof k ℤ (fun b => ↥(degreeSpace ρ b)) d
      ⟨scalarProjection ρ d v, scalarProjection_mem ρ d v⟩, ?_⟩
    simpa only [map_sum, DirectSum.coeLinearMap_lof] using hs


private def scalarCoefficient (ρ : MatrixRepresentation k m I) (d : ℤ) : Matrix I I k :=
  fun i j => (scalarMatrix ρ (CommAlgCat.of k (LaurentPolynomial k)) (variableUnit k) i j).coeff d

private theorem scalarProjection_eq (ρ : MatrixRepresentation k m I) (d : ℤ) (v : I → k) :
    scalarProjection ρ d v = (scalarCoefficient ρ d).mulVec v := by
  funext i
  change (scalarOrbit ρ v i).coeff d = _
  simp only [scalarOrbit, Matrix.mulVec, dotProduct, extendVector, LaurentPolynomial.algebraMap_apply,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, scalarCoefficient]
  apply Finset.sum_congr rfl
  intro j _
  change ((scalarMatrix ρ (CommAlgCat.of k (LaurentPolynomial k)) (variableUnit k) i j)
    * C (v j)).coeff d = _
  rw [mul_comm _ (C (v j)), coeff_const_mul, mul_comm]

private theorem scalarCoefficient_commutes (ρ : MatrixRepresentation k m I) (d : ℤ)
    (R : TestAlgebra k) (g : Matrix.GeneralLinearGroup m R) :
    (scalarCoefficient ρ d).map (algebraMap k R) * (representationAt ρ R g).val =
      (representationAt ρ R g).val * (scalarCoefficient ρ d).map (algebraMap k R) := by
  let S := CommAlgCat.of k (LaurentPolynomial R)
  let f : R ⟶ S := CommAlgCat.ofHom
    { C with commutes' := fun a => (LaurentPolynomial.algebraMap_apply a).symm }
  let L := CommAlgCat.of k (LaurentPolynomial k)
  let e : L ⟶ S := CommAlgCat.ofHom (laurentEval S (variableUnit R))
  have hg := congrArg Units.val (representationAt_natural f ρ g)
  change (representationAt ρ R g).val.map C =
    (representationAt ρ S (Matrix.GeneralLinearGroup.map C g)).val at hg
  have hz := congrArg Units.val (representationAt_natural e ρ
    (Matrix.GeneralLinearGroup.scalar m (variableUnit k)))
  rw [Matrix.GeneralLinearGroup.map_scalar] at hz
  change (scalarMatrix ρ L (variableUnit k)).map (laurentEval S (variableUnit R)) =
    scalarMatrix ρ S (Units.map (laurentEval S (variableUnit R)).toMonoidHom (variableUnit k)) at hz
  rw [laurentEval_unit] at hz
  have h := scalarMatrix_central ρ S (variableUnit R) (Matrix.GeneralLinearGroup.map C g)
  rw [← hg, ← hz] at h
  ext i j
  have hc := congrArg (fun A : Matrix I I (LaurentPolynomial R) => (A i j).coeff d) h
  have hcoeff (p : LaurentPolynomial k) :
      (laurentEval S (variableUnit R) p).coeff d = algebraMap k R (p.coeff d) := by
    simpa [S] using coeff_eval_scaled (1 : Rˣ) p d
  have hcoeff' (a : R) (p : LaurentPolynomial k) :
      (laurentEval S (variableUnit R) p * C a).coeff d =
        algebraMap k R (p.coeff d) * a := by
    rw [mul_comm, coeff_const_mul, hcoeff, mul_comm]
  have hsum (p : I → LaurentPolynomial R) : (∑ i, p i).coeff d = ∑ i, (p i).coeff d := by
    simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  change (∑ a, laurentEval S (variableUnit R) (scalarMatrix ρ L (variableUnit k) i a) *
      C ((representationAt ρ R g).val a j)).coeff d =
    (∑ a, C ((representationAt ρ R g).val i a) *
      laurentEval S (variableUnit R) (scalarMatrix ρ L (variableUnit k) a j)).coeff d at hc
  rw [hsum, hsum] at hc
  simp only [Matrix.mul_apply, Matrix.map_apply, scalarCoefficient]
  refine (Finset.sum_congr rfl fun a _ => (hcoeff' ((representationAt ρ R g).val a j)
    (scalarMatrix ρ L (variableUnit k) i a)).symm).trans (hc.trans ?_)
  apply Finset.sum_congr rfl
  intro a _
  rw [coeff_const_mul, hcoeff]

private theorem degreeSpace_stable {n : ℕ} {G : AffineAlgebraicGroup k}
    (e : GeneralLinearStructure.MatrixPoints G n) (ρ : MatrixRepresentation k (Index.{u} n) I)
    (d : ℤ) : PrimitiveLine.IsStable (e.hom ≫ ρ) (degreeSpace ρ d) := by
  intro v hv
  apply (orbit_le_iff _ _ _).mpr
  intro R x ℓ
  let g : Matrix.GeneralLinearGroup (Index.{u} n) R := e.hom.app R x
  let w := (representationAt ρ R g).val.mulVec (extendVector R v)
  have hfix := scalarProjection_of_mem hv d
  simp only [ite_true, scalarProjection_eq] at hfix
  have hw : ((scalarCoefficient ρ d).map (algebraMap k R)).mulVec w = w := by
    rw [show w = _ from rfl, Matrix.mulVec_mulVec, scalarCoefficient_commutes ρ d R g, ← Matrix.mulVec_mulVec,
      ← extend_mulVec, hfix]
  let y : I → k := fun i => ℓ (w i)
  have hy : scalarProjection ρ d y = y := by
    rw [scalarProjection_eq]
    funext i
    rw [← contract_mulVec R ℓ _ w i, hw]
  change y ∈ degreeSpace ρ d
  rw [← hy]
  exact scalarProjection_mem ρ d y

private theorem simpleDegree_aux : SimpleDegree.{u} := by
  intro k I _ _ _ n G e ρ hs lam v hv
  refine ⟨?_, LinearAlgebraicGroups.Representation.PolynomialGL.simpleCriterion k I n G e ρ hs lam v hv⟩
  have hm : v ∈ degreeSpace ρ (∑ i, lam i) := by
    rw [mem_degreeSpace]
    intro R z
    have hw := hv.2.1 R (fun _ => z)
    have he : diagonalPoint (m := Index.{u} (n + 1)) (fun _ => z) =
        Matrix.GeneralLinearGroup.scalar _ z := by
      apply Units.ext
      rw [LinearAlgebraicGroups.Representation.PolynomialGL.diagonalPoint_val]
      rfl
    rwa [he, show weightValue lam (fun _ => z) = z ^ (∑ i, lam i) by
      classical
      unfold weightValue
      generalize (Finset.univ : Finset (Index.{u} (n + 1))) = s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih => simp [hi, ih, zpow_add]] at hw
  rcases hs.2 _ (degreeSpace_stable e ρ _) with h | h
  · exact (hv.1 ((Submodule.mem_bot k).mp (h ▸ hm))).elim
  · exact h

private def inverseTranspose {m R : Type u} [Fintype m] [DecidableEq m] [CommRing R] :
    Matrix.GeneralLinearGroup m R →* Matrix.GeneralLinearGroup m R where
  toFun g :=
    ⟨(g⁻¹).val.transpose, g.val.transpose,
      by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]⟩
  map_one' := by apply Units.ext; simp
  map_mul' g h := by
    apply Units.ext
    change ((g * h)⁻¹).val.transpose = (g⁻¹).val.transpose * (h⁻¹).val.transpose
    rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private def dualRepresentation (k m : Type u) [Field k] [Fintype m] [DecidableEq m] :
    MatrixRepresentation k m m where
  app _ := GrpCat.ofHom inverseTranspose
  naturality R S f := GrpCat.ext fun g => by
    change Matrix.GeneralLinearGroup m R at g
    change inverseTranspose (Matrix.GeneralLinearGroup.map f.hom.toRingHom g) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom (inverseTranspose g)
    apply Units.ext
    rw [show (inverseTranspose (Matrix.GeneralLinearGroup.map f.hom.toRingHom g)).val =
      ((Matrix.GeneralLinearGroup.map f.hom.toRingHom g)⁻¹).val.transpose from rfl,
      ← Matrix.GeneralLinearGroup.map_inv]
    rfl

private theorem extend_single_one {J : Type u} [DecidableEq J] (R : TestAlgebra k) (j : J) :
    extendVector R (Pi.single j (1 : k)) = Pi.single j (1 : R) := by
  funext i
  by_cases hi : i = j <;> simp [extendVector, hi]

private theorem dual_primitive (k : Type u) [Field k] (n : ℕ) :
    IsPrimitive (dualRepresentation k (Index.{u} (n + 1))) (dualWeight n)
      (Pi.single ⟨Fin.last n⟩ 1) := by
  let j : Index.{u} (n + 1) := ⟨Fin.last n⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact (one_ne_zero : (1 : k) ≠ 0) (by simpa [j] using congrFun h j)
  · intro R t
    change (inverseTranspose (diagonalPoint t)).val.mulVec (extendVector R (Pi.single j 1)) =
      (weightValue (Pi.single j (-1)) t).val • extendVector R (Pi.single j 1)
    have hw : weightValue (Pi.single j (-1)) t = (t j)⁻¹ := by
      classical
      unfold weightValue
      rw [Finset.prod_eq_single j]
      · simp
      · intro i _ hi
        simp [hi]
      · simp
    have hi : (diagonalPoint t)⁻¹ = diagonalPoint (fun i => (t i)⁻¹) := by
      unfold diagonalPoint
      rw [← map_inv, ← map_inv]
      rfl
    rw [hw, extend_single_one]
    change ((diagonalPoint t)⁻¹).val.transpose.mulVec _ = _
    rw [hi, LinearAlgebraicGroups.Representation.PolynomialGL.diagonalPoint_val, Matrix.diagonal_transpose]
    funext i
    by_cases h : i = j <;> simp [Matrix.mulVec_single, h]
  · intro R g hg hd
    change (g⁻¹).val.transpose.mulVec (extendVector R (Pi.single j 1)) = extendVector R (Pi.single j 1)
    rw [extend_single_one]
    have row : g.val.transpose.mulVec (Pi.single j 1) = Pi.single j 1 := by
      funext i
      rw [Matrix.mulVec_single_one]
      by_cases h : i = j
      · subst i
        simpa using hd j
      · have hj : i < j := lt_of_le_of_ne (show i ≤ j from Fin.le_last i.down) h
        simpa [Pi.single_apply, h] using hg hj
    conv_lhs => rw [← row]
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.transpose_one, Matrix.one_mulVec]

private theorem dual_primitive_weight {k : Type u} [Field k] {n : ℕ}
    {lam : Index.{u} (n + 1) → ℤ} {v : Index.{u} (n + 1) → k}
    (hv : IsPrimitive (dualRepresentation k (Index.{u} (n + 1))) lam v) :
    lam = dualWeight n := by
  classical
  let j : Index.{u} (n + 1) := ⟨Fin.last n⟩
  have hz (i : Index.{u} (n + 1)) (hij : i ≠ j) : v i = 0 := by
    let R := CommAlgCat.of k k
    let g : Matrix.GeneralLinearGroup (Index.{u} (n + 1)) R :=
      Matrix.GeneralLinearGroup.transvection i j hij (-1)
    have hup : g.val.IsUpperTriangular := by
      intro a b hba
      change Matrix.transvection i j (-1 : k) a b = 0
      have hab : a ≠ b := hba.ne'
      have hkey : i = a → j ≠ b := by
        intro ha hb
        subst a
        subst b
        exact (not_lt_of_ge (show i ≤ j from Fin.le_last i.down)) hba
      simpa [Matrix.transvection, hab, Matrix.single_apply] using hkey
    have hdiag (a : Index.{u} (n + 1)) : g.val a a = 1 := by
      change Matrix.transvection i j (-1 : k) a a = 1
      have hkey : i = a → j ≠ a := fun h₁ h₂ => hij (h₁.trans h₂.symm)
      simpa [Matrix.transvection, Matrix.single_apply] using hkey
    have h := congrFun (hv.2.2 R g hup hdiag) j
    change (Matrix.transvection i j (-(-1 : k))).transpose.mulVec v j = v j at h
    simpa [Matrix.transvection, Matrix.transpose_add, Matrix.add_mulVec,
      Matrix.single_mulVec, Pi.single_apply] using h
  have hline : v = v j • Pi.single j 1 := by
    funext i
    by_cases h : i = j
    · subst i
      simp
    · simp [hz i h, h]
  have hj : v j ≠ 0 := fun h => hv.1 (by rw [hline, h, zero_smul])
  apply LinearAlgebraicGroups.Representation.PolynomialGL.weight_exponents_eq (k := k)
  intro R t
  let A := (representationAt (dualRepresentation k (Index.{u} (n + 1))) R (diagonalPoint t)).val
  have hw := hv.2.1 R t
  have htop := (dual_primitive k n).2.1 R t
  have he : extendVector R v = algebraMap k R (v j) • extendVector R (Pi.single j 1) := by
    refine (congrArg (extendVector R) hline).trans ?_
    funext i
    exact map_mul (algebraMap k R) _ _
  change A.mulVec (extendVector R v) = (weightValue lam t).val • extendVector R v at hw
  change A.mulVec (extendVector R (Pi.single j 1)) =
    (weightValue (dualWeight n) t).val • extendVector R (Pi.single j 1) at htop
  rw [he, Matrix.mulVec_smul, htop] at hw
  have hh := congrFun hw j
  simp only [extend_single_one, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at hh
  have hu := ((isUnit_iff_ne_zero.mpr hj).map (algebraMap k R))
  apply hu.mul_right_cancel
  exact hh.symm.trans (mul_comm _ _)

private theorem naturalDual_aux : NaturalDual.{u} := by
  intro k _ n
  refine ⟨dualRepresentation k (Index.{u} (n + 1)), fun R g => rfl, dual_primitive k n, fun _ _ => dual_primitive_weight, ?_⟩
  intro R g
  rw [twist_matrix, zpow_one]
  change g.det.val • (g⁻¹).val.transpose =
    (evaluateMatrix g.val).mapMatrix (genericMatrix k (Index.{u} (n + 1))).adjugate.transpose
  rw [show (evaluateMatrix g.val).mapMatrix
      (genericMatrix k (Index.{u} (n + 1))).adjugate.transpose =
        g.val.adjugate.transpose by
      change ((evaluateMatrix g.val).mapMatrix
        (genericMatrix k (Index.{u} (n + 1))).adjugate).transpose = _
      rw [AlgHom.map_adjugate, evaluation_generic]]
  rw [← Matrix.transpose_smul]
  congr 1
  calc
    g.det.val • (g⁻¹).val = (g.val.adjugate * g.val) * (g⁻¹).val := by
      rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      rfl
    _ = g.val.adjugate := by
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.mul_one]

omit [Fintype m] [DecidableEq m] in
private theorem polynomialCoefficient_eval (P : Matrix I I (MvPolynomial (m × m) k))
    (v f : I → k) (R : TestAlgebra k) (X : Matrix m m R) :
    evaluateMatrix X (polynomialCoefficient P v f) =
      dotProduct (extendVector R f) ((evaluateCoefficients P X).mulVec (extendVector R v)) := by
  simp [polynomialCoefficient, dotProduct, Matrix.mulVec, map_sum, map_mul,
    evaluateCoefficients, extendVector, evaluateMatrix]

omit [DecidableEq m] in
private theorem eval_scaled_monomial {R : TestAlgebra k} (X : Matrix m m R)
    (a : (m × m) →₀ ℕ) (r : k) :
    evaluateMatrix ((T 1 : LaurentPolynomial R) • X.map C) (MvPolynomial.monomial a r) =
      C (evaluateMatrix X (MvPolynomial.monomial a r)) * T (a.degree : ℤ) := by
  simp only [evaluateMatrix, MvPolynomial.aeval_monomial, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, Finsupp.prod_mul, Finsupp.prod_pow, mul_pow,
    LaurentPolynomial.algebraMap_apply, map_mul, map_prod, map_pow]
  rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum,
    ← Polynomial.toLaurent_X_pow, map_pow, Polynomial.toLaurent_X]
  ac_rfl

omit [DecidableEq m] in
private theorem coefficient_eval_scaled {R : TestAlgebra k} (X : Matrix m m R)
    (p : MvPolynomial (m × m) k) (d : ℤ) :
    (evaluateMatrix ((T 1 : LaurentPolynomial R) • X.map C) p).coeff d =
      if 0 ≤ d then evaluateMatrix X (MvPolynomial.homogeneousComponent d.toNat p) else 0 := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  simp only [map_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, eval_scaled_monomial,
    coeff_const_mul, LaurentPolynomial.T_apply, mul_ite, mul_one, mul_zero]
  by_cases hd : 0 ≤ d
  · lift d to ℕ using hd
    simp only [Int.natCast_nonneg, ite_true, Int.toNat_natCast, Int.natCast_inj]
    rw [MvPolynomial.homogeneousComponent_apply, map_sum, Finset.sum_filter]
  · rw [ite_eq_right hd, Finset.sum_eq_zero]
    intro a ha
    apply ite_eq_right
    intro he
    exact hd (he ▸ Int.natCast_nonneg a.degree)

/-- Multiplication of an invertible matrix by the universal scalar on a weight vector. -/
private theorem coefficient_scalar_identity (ρ : MatrixRepresentation k m I)
    (P : Matrix I I (MvPolynomial (m × m) k)) (hP : EvaluatesTo ρ P)
    {d : ℤ} {v : I → k} (hv : v ∈ degreeSpace ρ d) (f : I → k)
    (R : TestAlgebra k) (g : Matrix.GeneralLinearGroup m R) :
    let q := polynomialCoefficient P v f
    evaluateMatrix ((T 1 : LaurentPolynomial R) • g.val.map C) q =
      T d * C (evaluateMatrix g.val q) := by
  intro q
  let S := CommAlgCat.of k (LaurentPolynomial R)
  let a : R →ₐ[k] S := { C with commutes' := fun r => (LaurentPolynomial.algebraMap_apply r).symm }
  let g₀ : Matrix.GeneralLinearGroup m S := Matrix.GeneralLinearGroup.map C g
  let z := variableUnit R
  let s := Matrix.GeneralLinearGroup.scalar m z
  have hx : (g₀ * s).val = (T 1 : LaurentPolynomial R) • g.val.map C := by
    change g.val.map C * Matrix.diagonal (fun _ : m => T 1) = _
    rw [← Matrix.smul_eq_mul_diagonal]
  have he₀ : a (evaluateMatrix g.val q) = evaluateMatrix g₀.val q := by
    exact DFunLike.congr_fun (evaluation_comp a g.val) q
  have hact := (mem_degreeSpace.mp hv) S z
  rw [variableUnit_zpow] at hact
  change evaluateMatrix ((T 1 : LaurentPolynomial R) • g.val.map C) (polynomialCoefficient P v f) =
    T d * a (evaluateMatrix g.val q)
  change a (evaluateMatrix g.val q) = evaluateMatrix g₀.val (polynomialCoefficient P v f) at he₀
  rw [← hx, he₀, polynomialCoefficient_eval P v f S, polynomialCoefficient_eval P v f S,
    ← hP S, ← hP S, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hact,
    Matrix.mulVec_smul, dotProduct_smul]
  rfl

private theorem evaluated_generic_injective :
    Function.Injective (evaluateMatrix (k := k) (universalPoint (k := k) (m := m)).val) := by
  have h := away_algebraMap_injective (genericDeterminant k m) (genericDeterminant_ne_zero (k := k) (m := m))
  have he : evaluateMatrix (universalPoint (k := k) (m := m)).val =
      IsScalarTower.toAlgHom k (MvPolynomial (m × m) k) (GLCoordinates k m) := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with ⟨i,j⟩
    simp only [evaluateMatrix, MvPolynomial.aeval_X]
    rfl
  rw [he]
  exact h

private theorem homogeneousCoefficients_aux : HomogeneousCoefficients.{u} := by
  intro k m I _ _ _ _ _ ρ P hP
  let R := CommAlgCat.of k (GLCoordinates k m)
  let g : Matrix.GeneralLinearGroup m R := universalPoint
  have hcompare (d : ℤ) (v : I → k) (hv : v ∈ degreeSpace ρ d) (f : I → k) :
      (if 0 ≤ d then MvPolynomial.homogeneousComponent d.toNat (polynomialCoefficient P v f) else 0) =
        polynomialCoefficient P v f := by
    have he := coefficient_scalar_identity ρ P hP hv f R g
    dsimp only at he
    have hc := congrArg (fun p : LaurentPolynomial R => p.coeff d) he
    rw [coefficient_eval_scaled, LaurentPolynomial.T_mul, coeff_const_mul,
      LaurentPolynomial.T_apply, ite_eq_left rfl, mul_one] at hc
    apply evaluated_generic_injective (m := m)
    simpa only [apply_ite, map_zero] using hc
  refine ⟨?_, ?_⟩
  · intro d v hv f
    have h := hcompare d v hv f
    simp only [Int.natCast_nonneg, ite_true, Int.toNat_natCast] at h
    rw [← h]
    exact MvPolynomial.homogeneousComponent_isHomogeneous _ _
  · intro d hd
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    funext i
    have h := (hcompare d v hv (Pi.single i 1)).symm
    rw [ite_eq_right (not_le.mpr hd)] at h
    have hz := congrArg (evaluateMatrix (1 : Matrix m m k)) h
    have he := polynomialCoefficient_eval P v (Pi.single i 1) (CommAlgCat.of k k) (1 : Matrix m m k)
    have hp := hP (CommAlgCat.of k k) 1
    change (representationAt ρ (CommAlgCat.of k k) 1).val = evaluateCoefficients P (1 : Matrix m m k) at hp
    rw [map_one, Units.val_one] at hp
    rw [he, ← hp, Matrix.one_mulVec] at hz
    simpa [extendVector, dotProduct, Pi.single_apply] using hz

private theorem rowLen_zero_of_row_count_le (μ : YoungDiagram) (i : ℕ)
    (hi : μ.rowLens.length ≤ i) : μ.rowLen i = 0 := by
  by_contra h
  exact (Nat.not_lt_of_ge (YoungDiagram.length_rowLens (μ := μ) ▸ hi))
    (YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h)))

private theorem row_sum (μ : YoungDiagram) (n : ℕ) (h : μ.rowLens.length ≤ n) :
    (∑ i : Fin n, μ.rowLen i) = μ.card := by
  have he : List.ofFn (fun i : Fin μ.rowLens.length => μ.rowLen i) = μ.rowLens := by
    apply List.ext_get
    · simp
    · intro i hi hj
      simp [YoungDiagram.get_rowLens]
  rw [← YoungDiagram.sum_rowLens_eq_card, ← he, List.sum_ofFn, Fin.sum_univ_eq_sum_range,
    Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono h)
  intro i _ hi
  exact rowLen_zero_of_row_count_le μ i (Nat.le_of_not_lt (fun hh => hi (Finset.mem_range.mpr hh)))

private theorem partition_labels (n d : ℕ) (lam : Index.{u} (n + 1) → ℤ) :
    (Antitone lam ∧ 0 ≤ lam ⟨Fin.last n⟩ ∧ (∑ i, lam i) = (d : ℤ)) ↔
      IsSchurWeylLabel n d lam := by
  classical
  have hdim : Module.finrank ℂ (Fin (n + 1) → ℂ) = n + 1 := by simp
  have hSW (p : Nat.Partition d) :
      Nontrivial (_root_.Specs.AdvancedFiniteGroupRepresentations.TensorMultiplicity
        (Fin (n + 1) → ℂ) p) ↔ (YoungDiagram.ofPartition p).rowLens.length ≤ n + 1 := by
    calc
      _ ↔ AdvancedFiniteGroupRepresentations.length p ≤ Module.finrank ℂ (Fin (n + 1) → ℂ) :=
        AdvancedFiniteGroupRepresentations.tensorMultiplicity_nonzero_iff (Fin (n + 1) → ℂ) p
      _ ↔ _ := by rw [hdim]; rfl
  have hsum (p : Nat.Partition d) (hp : (YoungDiagram.ofPartition p).rowLens.length ≤ n + 1) :
      (∑ i : Index.{u} (n + 1), (YoungDiagram.ofPartition p).rowLen i.down.val) = d := by
    exact (Fintype.sum_equiv Equiv.ulift _ _ (fun _ => rfl)).trans
      ((row_sum _ _ hp).trans (YoungDiagram.card_ofPartition p))
  constructor
  · rintro ⟨hmono, hlast, hs⟩
    have hnonneg (i : Index.{u} (n + 1)) : 0 ≤ lam i :=
      hlast.trans (hmono (show i ≤ (⟨Fin.last n⟩ : Index.{u} (n + 1)) from Fin.le_last _))
    let parts := List.ofFn (fun i : Fin (n + 1) => (lam ⟨i⟩).toNat)
    have hsorted : parts.SortedGE := by
      rw [List.sortedGE_ofFn_iff]
      exact fun i j hij => Int.toNat_le_toNat (hmono (show (⟨i⟩ : Index.{u} (n + 1)) ≤ ⟨j⟩ from hij))
    let μ := YoungDiagram.ofRowLens parts hsorted
    have hlen : μ.rowLens.length ≤ n + 1 := by
      by_contra! h
      have hb : (n + 1, 0) ∈ μ :=
        YoungDiagram.mem_iff_lt_colLen.mpr (by rwa [← YoungDiagram.length_rowLens])
      obtain ⟨h', _⟩ := YoungDiagram.mem_ofRowLens.mp hb
      simp [parts] at h'
    have hrows (i : Index.{u} (n + 1)) : (μ.rowLen i.down.val : ℤ) = lam i := by
      have h := YoungDiagram.rowLen_ofRowLens (hw := hsorted)
        ⟨i.down.val, by simpa [parts] using i.down.isLt⟩
      have hh : μ.rowLen i.down.val = (lam i).toNat := by
        refine h.trans ?_
        have hi : i.down.val < parts.length := by simpa [parts] using i.down.isLt
        change parts[i.down.val]'hi = _
        exact List.getElem_ofFn hi
      rw [hh, Int.toNat_of_nonneg (hnonneg i)]
    have hcard : μ.card = d := by
      have h := row_sum μ (n + 1) hlen
      have h' : (∑ i : Index.{u} (n + 1), μ.rowLen i.down.val) = μ.card :=
        (Fintype.sum_equiv Equiv.ulift _ _ (fun _ => rfl)).trans h
      exact Int.ofNat_inj.mp (by push_cast [← h']; simpa only [hrows] using hs)
    let p := μ.toPartition hcard
    have hμ : YoungDiagram.ofPartition p = μ := YoungDiagram.ofPartition_toPartition hcard
    refine ⟨p, ⟨(hSW p).mpr (hμ ▸ hlen), fun i => (hrows i).symm.trans (by rw [hμ])⟩, ?_⟩
    rintro q ⟨hq, hqrows⟩
    apply YoungDiagram.equivPartition.symm.injective
    apply Subtype.ext
    change YoungDiagram.ofPartition q = YoungDiagram.ofPartition p
    rw [hμ]
    apply SetLike.ext
    rintro ⟨i, j⟩
    simp only [YoungDiagram.mem_iff_lt_rowLen]
    by_cases hi : i < n + 1
    · have hh := (hqrows ⟨⟨i, hi⟩⟩).symm.trans (hrows ⟨⟨i, hi⟩⟩).symm
      rw [Int.ofNat_inj.mp hh]
    · rw [rowLen_zero_of_row_count_le _ i ((hSW q).mp hq |>.trans (Nat.le_of_not_lt hi)),
        rowLen_zero_of_row_count_le _ i (hlen.trans (Nat.le_of_not_lt hi))]
  · rintro ⟨p, ⟨hp, hrows⟩, _⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      rw [hrows i, hrows j]
      exact Int.ofNat_le.mpr ((YoungDiagram.ofPartition p).rowLen_anti _ _ hij)
    · rw [hrows]
      exact Int.natCast_nonneg _
    · simp only [hrows, ← Nat.cast_sum, hsum p ((hSW p).mp hp)]

private theorem schurWeylLabels_aux : SchurWeylLabels.{u} := by
  refine ⟨partition_labels, ?_⟩
  intro k I _ _ _ n d G e ρ hsimple lam v hlam hv
  obtain ⟨hspace, hpolynomial⟩ := simpleDegree_aux k I n G e ρ hsimple lam v hv
  rw [hpolynomial, ← partition_labels n d lam]
  have hdegree : degreeSpace ρ (d : ℤ) = ⊤ ↔ (∑ i, lam i) = (d : ℤ) := by
    constructor
    · intro hd
      have hv₁ : v ∈ degreeSpace ρ (∑ i, lam i) := hspace ▸ Submodule.mem_top
      have hv₂ : v ∈ degreeSpace ρ (d : ℤ) := hd ▸ Submodule.mem_top
      have he₁ := scalarProjection_of_mem hv₁ (d : ℤ)
      have he₂ := scalarProjection_of_mem hv₂ (d : ℤ)
      by_contra hne
      rw [ite_eq_right hne] at he₁
      rw [ite_eq_left rfl] at he₂
      exact hv.1 (he₂.symm.trans he₁)
    · intro h
      rwa [← h]
  simp only [hdegree, hlam, true_and]


theorem centralDegreeDecomposition_conditional
    (_frobeniusSubmodule : NonsplitSymmetricPower.FrobeniusSubmodule.{u})
    (_inductionIdentification : NonsplitSymmetricPower.InductionIdentification.{u})
    (_markedFlagAndSocle : NonsplitSymmetricPower.MarkedFlagAndSocle.{u})
    (_nonsplit : NonsplitSymmetricPower.Nonsplit.{u})
    (_polynomialAction : NonsplitSymmetricPower.PolynomialAction.{u})
    (_relativeFrobeniusComparison : NonsplitSymmetricPower.RelativeFrobeniusComparison.{u})
    : CentralDegreeDecomposition.{u} := by
  intro k I _ _ _ n G e ρ
  exact ⟨degree_isInternal ρ, degreeSpace_stable e ρ⟩

theorem simpleDegree_conditional
    (_frobeniusSubmodule : NonsplitSymmetricPower.FrobeniusSubmodule.{u})
    (_inductionIdentification : NonsplitSymmetricPower.InductionIdentification.{u})
    (_markedFlagAndSocle : NonsplitSymmetricPower.MarkedFlagAndSocle.{u})
    (_nonsplit : NonsplitSymmetricPower.Nonsplit.{u})
    (_polynomialAction : NonsplitSymmetricPower.PolynomialAction.{u})
    (_relativeFrobeniusComparison : NonsplitSymmetricPower.RelativeFrobeniusComparison.{u})
    : SimpleDegree.{u} := simpleDegree_aux

theorem homogeneousCoefficients_conditional
    (_frobeniusSubmodule : NonsplitSymmetricPower.FrobeniusSubmodule.{u})
    (_inductionIdentification : NonsplitSymmetricPower.InductionIdentification.{u})
    (_markedFlagAndSocle : NonsplitSymmetricPower.MarkedFlagAndSocle.{u})
    (_nonsplit : NonsplitSymmetricPower.Nonsplit.{u})
    (_polynomialAction : NonsplitSymmetricPower.PolynomialAction.{u})
    (_relativeFrobeniusComparison : NonsplitSymmetricPower.RelativeFrobeniusComparison.{u})
    : HomogeneousCoefficients.{u} := homogeneousCoefficients_aux

theorem naturalDual_conditional
    (_frobeniusSubmodule : NonsplitSymmetricPower.FrobeniusSubmodule.{u})
    (_inductionIdentification : NonsplitSymmetricPower.InductionIdentification.{u})
    (_markedFlagAndSocle : NonsplitSymmetricPower.MarkedFlagAndSocle.{u})
    (_nonsplit : NonsplitSymmetricPower.Nonsplit.{u})
    (_polynomialAction : NonsplitSymmetricPower.PolynomialAction.{u})
    (_relativeFrobeniusComparison : NonsplitSymmetricPower.RelativeFrobeniusComparison.{u})
    : NaturalDual.{u} := naturalDual_aux

theorem schurWeylLabels_conditional
    (_frobeniusSubmodule : NonsplitSymmetricPower.FrobeniusSubmodule.{u})
    (_inductionIdentification : NonsplitSymmetricPower.InductionIdentification.{u})
    (_markedFlagAndSocle : NonsplitSymmetricPower.MarkedFlagAndSocle.{u})
    (_nonsplit : NonsplitSymmetricPower.Nonsplit.{u})
    (_polynomialAction : NonsplitSymmetricPower.PolynomialAction.{u})
    (_relativeFrobeniusComparison : NonsplitSymmetricPower.RelativeFrobeniusComparison.{u})
    : SchurWeylLabels.{u} := schurWeylLabels_aux

end

end LinearAlgebraicGroups.Representation.HomogeneousGL

universe v8_closure_ee5d9d3687399225_u0
theorem _root_.«LinearAlgebraicGroups».«Representation».«HomogeneousGL».«centralDegreeDecomposition» : _root_.«LinearAlgebraicGroups».«Specs».«HomogeneousGL».«CentralDegreeDecomposition».{v8_closure_ee5d9d3687399225_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«HomogeneousGL».«centralDegreeDecomposition_conditional».{v8_closure_ee5d9d3687399225_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«frobeniusSubmodule».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«inductionIdentification».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«markedFlagAndSocle».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«nonsplit».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«polynomialAction».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«relativeFrobeniusComparison».{v8_closure_ee5d9d3687399225_u0})
theorem _root_.«LinearAlgebraicGroups».«Representation».«HomogeneousGL».«homogeneousCoefficients» : _root_.«LinearAlgebraicGroups».«Specs».«HomogeneousGL».«HomogeneousCoefficients».{v8_closure_ee5d9d3687399225_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«HomogeneousGL».«homogeneousCoefficients_conditional».{v8_closure_ee5d9d3687399225_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«frobeniusSubmodule».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«inductionIdentification».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«markedFlagAndSocle».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«nonsplit».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«polynomialAction».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«relativeFrobeniusComparison».{v8_closure_ee5d9d3687399225_u0})
theorem _root_.«LinearAlgebraicGroups».«Representation».«HomogeneousGL».«naturalDual» : _root_.«LinearAlgebraicGroups».«Specs».«HomogeneousGL».«NaturalDual».{v8_closure_ee5d9d3687399225_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«HomogeneousGL».«naturalDual_conditional».{v8_closure_ee5d9d3687399225_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«frobeniusSubmodule».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«inductionIdentification».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«markedFlagAndSocle».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«nonsplit».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«polynomialAction».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«relativeFrobeniusComparison».{v8_closure_ee5d9d3687399225_u0})
theorem _root_.«LinearAlgebraicGroups».«Representation».«HomogeneousGL».«schurWeylLabels» : _root_.«LinearAlgebraicGroups».«Specs».«HomogeneousGL».«SchurWeylLabels».{v8_closure_ee5d9d3687399225_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«HomogeneousGL».«schurWeylLabels_conditional».{v8_closure_ee5d9d3687399225_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«frobeniusSubmodule».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«inductionIdentification».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«markedFlagAndSocle».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«nonsplit».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«polynomialAction».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«relativeFrobeniusComparison».{v8_closure_ee5d9d3687399225_u0})
theorem _root_.«LinearAlgebraicGroups».«Representation».«HomogeneousGL».«simpleDegree» : _root_.«LinearAlgebraicGroups».«Specs».«HomogeneousGL».«SimpleDegree».{v8_closure_ee5d9d3687399225_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«HomogeneousGL».«simpleDegree_conditional».{v8_closure_ee5d9d3687399225_u0} (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«frobeniusSubmodule».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«inductionIdentification».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«markedFlagAndSocle».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«nonsplit».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«polynomialAction».{v8_closure_ee5d9d3687399225_u0}) (@_root_.«LinearAlgebraicGroups».«Representation».«NonsplitSymmetricPower».«relativeFrobeniusComparison».{v8_closure_ee5d9d3687399225_u0})
