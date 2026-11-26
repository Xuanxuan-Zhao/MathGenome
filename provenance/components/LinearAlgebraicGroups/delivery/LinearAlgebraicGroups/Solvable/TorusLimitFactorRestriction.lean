import Specs.LinearAlgebraicGroups.Solvable.TorusLimitFactorRestriction
import LinearAlgebraicGroups.Affine.ChevalleyLine
import Mathlib.Algebra.Polynomial.Laurent
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

universe u

namespace LinearAlgebraicGroups.TorusLimitFactorRestriction

open Specs Specs.StandardGroups Specs.Unipotent
open private coordinateLine_iff_unit from LinearAlgebraicGroups.Affine.ChevalleyLine

noncomputable section

private abbrev Supported {I R : Type u} [Fintype I] [LinearOrder I] [DecidableEq I]
    [CommRing R] (q : I → I → Prop) (x : upperUnitriangular I R) : Prop :=
  ∀ i j, ¬ (i < j ∧ q i j) → (x.val.val - 1) i j = 0

private theorem entry_eq_oneMatrix {I R : Type u} [Fintype I] [LinearOrder I] [DecidableEq I]
    [CommRing R] {q : I → I → Prop} {x : upperUnitriangular I R}
    (h : Supported q x) {i j : I} (hij : ¬ (i < j ∧ q i j)) :
    x.val.val i j = (1 : Matrix I I R) i j :=
  sub_eq_zero.mp (h i j hij)

private theorem polynomialConjugationChart {I R : Type u} [Fintype I] [LinearOrder I]
    [DecidableEq I] [CommRing R] (w : I → ℤ) (x : upperUnitriangular I R)
    (hx : Supported (fun i j ↦ w j < w i) x) :
    ∃ p : Matrix.GeneralLinearGroup I (Polynomial R),
      (∀ i j, (p.val i j).toLaurent =
        LaurentPolynomial.C (x.val.val i j) * LaurentPolynomial.T (w i - w j)) ∧
      Matrix.GeneralLinearGroup.map (Polynomial.evalRingHom 0) p = 1 ∧
      Matrix.GeneralLinearGroup.map (Polynomial.evalRingHom 1) p = x.val := by
  let A : Matrix I I (Polynomial R) := fun i j ↦
    if i < j ∧ w j < w i then
      Polynomial.monomial (w i - w j).toNat (x.val.val i j)
    else (1 : Matrix I I (Polynomial R)) i j
  have hA : IsUpperUnitriangular A := by
    refine ⟨fun i j h ↦ ?_, fun i ↦ ?_⟩
    · change j < i at h
      simp [A, not_lt_of_ge h.le, Matrix.one_apply_ne (ne_of_gt h)]
    · simp [A]
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hA.1]
    simp [hA.2]
  let p := Matrix.GeneralLinearGroup.mk'' A (hdet ▸ isUnit_one)
  refine ⟨p, ?_, ?_, ?_⟩
  · intro i j
    change (A i j).toLaurent = _
    by_cases h : i < j ∧ w j < w i
    · rw [show A i j = _ from ite_eq_left h, ← Polynomial.C_mul_X_pow_eq_monomial,
        Polynomial.toLaurent_C_mul_X_pow, Int.toNat_of_nonneg (sub_nonneg.mpr h.2.le)]
    · rw [show A i j = _ from ite_eq_right h, entry_eq_oneMatrix hx h]
      by_cases hij : i = j
      · subst j
        simp
      · simp [Matrix.one_apply_ne hij]
  · apply Units.ext
    apply Matrix.ext
    intro i j
    change (A i j).eval 0 = (1 : Matrix I I R) i j
    by_cases h : i < j ∧ w j < w i
    · have hne : (w i - w j).toNat ≠ 0 := by
        have := sub_pos.mpr h.2
        omega
      simp [A, h, hne, Matrix.one_apply_ne h.1.ne]
    · by_cases hij : i = j <;> simp [A, h, Matrix.one_apply, hij]
  · apply Units.ext
    apply Matrix.ext
    intro i j
    change (A i j).eval 1 = x.val.val i j
    by_cases h : i < j ∧ w j < w i
    · simp [A, h]
    · rw [entry_eq_oneMatrix hx h]
      by_cases hij : i = j <;> simp [A, h, Matrix.one_apply, hij]

private def laurentMonomialUnits (R : Type u) [CommRing R] :
    Multiplicative ℤ →* (LaurentPolynomial R)ˣ where
  toFun a := (LaurentPolynomial.isUnit_T (R := R) a.toAdd).unit
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by
    simpa only [Units.val_mul, IsUnit.unit_spec, toAdd_mul] using
      (LaurentPolynomial.T_add (R := R) a.toAdd b.toAdd))

private theorem laurentMonomialUnits_zpow (R : Type u) [CommRing R] (d : ℤ) :
    ((laurentMonomialUnits R (Multiplicative.ofAdd 1) ^ d :
      (LaurentPolynomial R)ˣ) : LaurentPolynomial R) = LaurentPolynomial.T d := by
  rw [← map_zpow, ← ofAdd_zsmul]
  simp [laurentMonomialUnits, IsUnit.unit_spec]

private theorem characterOnCocharacter {I R : Type u} [Fintype I] [CommRing R]
    (l m : I → ℤ) (a : Rˣ) :
    (∏ i, (a ^ l i) ^ m i) = a ^ (∑ i, m i * l i) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
      rw [Finset.prod_insert his, Finset.sum_insert his, ih, zpow_add, mul_comm (m i), zpow_mul]

private theorem diagonalConjugation {I R : Type u} [Fintype I] [DecidableEq I]
    [CommRing R] (w : I → ℤ) {d x y : Matrix.GeneralLinearGroup I (LaurentPolynomial R)}
    (hd : d.val = Matrix.diagonal (fun i ↦ LaurentPolynomial.T (w i)))
    (hy : ∀ i j, y.val i j = x.val i j * LaurentPolynomial.T (w i - w j)) :
    d * x * d⁻¹ = y := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Units.ext
  apply Matrix.ext
  intro i j
  change (d.val * x.val) i j = (y.val * d.val) i j
  rw [hd, Matrix.diagonal_mul, Matrix.mul_diagonal, hy, mul_assoc, ← LaurentPolynomial.T_add,
    sub_add_cancel, mul_comm]

private theorem coeff_toLaurent_of_neg {R : Type u} [CommRing R] (f : Polynomial R)
    {m : ℤ} (hm : m < 0) : f.toLaurent.coeff m = 0 := by
  apply Finsupp.notMem_support_iff.mp
  rw [LaurentPolynomial.support_coeff_toLaurent]
  rintro h
  obtain ⟨a, _, e⟩ := Finset.mem_map.mp h
  change (a : ℤ) = m at e
  omega

private theorem polynomialChartsConstant {R : Type u} [CommRing R] (f g : Polynomial R)
    (h : f.toLaurent = LaurentPolynomial.invert g.toLaurent) :
    ∃ c : R, (∀ x, f.eval x = c) ∧ ∀ x, g.eval x = c := by
  have hcoeff (m : ℤ) : f.toLaurent.coeff m = g.toLaurent.coeff (-m) :=
    (congrArg (fun p : LaurentPolynomial R ↦ p.coeff m) h).trans
      (LaurentPolynomial.invert_apply _ _)
  let c := f.toLaurent.coeff 0
  have hf : f.toLaurent = LaurentPolynomial.C c := by
    apply LaurentPolynomial.ext
    intro m
    change f.toLaurent.coeff m = (Finsupp.single 0 c) m
    rcases lt_trichotomy m 0 with hm | rfl | hm
    · rw [coeff_toLaurent_of_neg f hm, Finsupp.single_eq_of_ne hm.ne]
    · rw [Finsupp.single_eq_same]
    · rw [hcoeff, coeff_toLaurent_of_neg g (by omega), Finsupp.single_eq_of_ne hm.ne']
  have hA : f = Polynomial.C c :=
    Polynomial.toLaurent_injective (hf.trans (Polynomial.toLaurent_C _).symm)
  have hB : g = Polynomial.C c := by
    apply Polynomial.toLaurent_injective
    calc
      g.toLaurent = LaurentPolynomial.invert (LaurentPolynomial.invert g.toLaurent) :=
        (LaurentPolynomial.involutive_invert _).symm
      _ = LaurentPolynomial.invert (LaurentPolynomial.C c) :=
        congrArg LaurentPolynomial.invert (h.symm.trans hf)
      _ = (Polynomial.C c).toLaurent := by simp
  exact ⟨c, fun x ↦ by rw [hA]; simp, fun x ↦ by rw [hB]; simp⟩

private abbrev ScalesColumn {I R : Type u} [Fintype I] [DecidableEq I] [CommRing R]
    (i : I) (x : Matrix.GeneralLinearGroup I R) (c : R) : Prop :=
  ∀ j, x.val j i = c * (1 : Matrix I I R) j i

private theorem column_mul {I R : Type u} [Fintype I] [DecidableEq I] [CommRing R]
    {i : I} {x y : Matrix.GeneralLinearGroup I R} {c : R} (hy : ScalesColumn i y c) (j : I) :
    (x * y).val j i = x.val j i * c := by
  change (x.val * y.val) j i = _
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hy i, Matrix.one_apply_eq, mul_one]
  · intro s _ h
    rw [hy s, Matrix.one_apply_ne h, mul_zero, mul_zero]
  · simp

private theorem column_conj {I R : Type u} [Fintype I] [DecidableEq I] [CommRing R]
    {i : I} {x d : Matrix.GeneralLinearGroup I R} {c : R} {q : Rˣ}
    (hx : ScalesColumn i x c) (hd : ScalesColumn i d (q : R)) :
    ScalesColumn i (d * x * d⁻¹) c := by
  intro j
  apply q.mul_left_inj.mp
  rw [← column_mul (x := d * x * d⁻¹) hd, inv_mul_cancel_right,
    column_mul hx, hd]
  ac_rfl

private theorem scalesColumn_iff {I R : Type u} [Fintype I] [DecidableEq I] [CommRing R]
    (i : I) (x : Matrix.GeneralLinearGroup I R) :
    StabilizesCoordinateLine x i ↔ ∃ c : Rˣ, ScalesColumn i x (c : R) := by
  rw [coordinateLine_iff_unit]
  simp only [ScalesColumn, Matrix.one_apply]
  simp_rw [mul_ite, mul_one, mul_zero]

variable {k : Type u} [Field k]

private abbrev MatrixPoints {I : Type u} [Fintype I] [DecidableEq I] (R : TestAlgebra k) :=
  Matrix.GeneralLinearGroup I R

private abbrev mapGL {I : Type u} [Fintype I] [DecidableEq I]
    {R S : TestAlgebra k} (f : R ⟶ S) : MatrixPoints (I := I) R →* MatrixPoints (I := I) S :=
  Matrix.GeneralLinearGroup.map f.hom.toRingHom

private abbrev matrixRepresentation {I J : Type u} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (ρ : generalLinearPoints k I ⟶ generalLinearPoints k J) (R : TestAlgebra k) :
    MatrixPoints (I := I) R →* MatrixPoints (I := J) R :=
  (ρ.app R).hom

private theorem representation_natural {I J : Type u} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (ρ : generalLinearPoints k I ⟶ generalLinearPoints k J)
    {R S : TestAlgebra k} (f : R ⟶ S) (x : MatrixPoints (I := I) R) :
    matrixRepresentation ρ S (mapGL f x) = mapGL f (matrixRepresentation ρ R x) :=
  ρ.naturality_apply f x

private abbrev polynomialAlgebra (R : TestAlgebra k) : TestAlgebra k :=
  CommAlgCat.of k (Polynomial R)

private abbrev laurentAlgebra (R : TestAlgebra k) : TestAlgebra k :=
  CommAlgCat.of k (LaurentPolynomial R)

private abbrev constantPolynomial (R : TestAlgebra k) : R ⟶ polynomialAlgebra R :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (Polynomial R))

private abbrev constantLaurent (R : TestAlgebra k) : R ⟶ laurentAlgebra R :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (LaurentPolynomial R))

private abbrev zeroChart (R : TestAlgebra k) : polynomialAlgebra R ⟶ laurentAlgebra R :=
  CommAlgCat.ofHom (Polynomial.toLaurentAlg.restrictScalars k)

private abbrev infinityChart (R : TestAlgebra k) : polynomialAlgebra R ⟶ laurentAlgebra R :=
  CommAlgCat.ofHom
    ((LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg).restrictScalars k)

private abbrev evalAt {R : TestAlgebra k} (s : R) : polynomialAlgebra R ⟶ R :=
  CommAlgCat.ofHom
    { Polynomial.evalRingHom s with
      commutes' := fun x ↦ by
        rw [IsScalarTower.algebraMap_apply k R (Polynomial R)]
        exact Polynomial.eval_C }

private theorem mapGL_eval_constant {I : Type u} [Fintype I] [DecidableEq I]
    {R : TestAlgebra k} (s : R) (x : MatrixPoints (I := I) R) :
    mapGL (evalAt s) (mapGL (constantPolynomial R) x) = x := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact Polynomial.eval_C

private theorem mapGL_zeroChart_constant {I : Type u} [Fintype I] [DecidableEq I]
    {R : TestAlgebra k} (x : MatrixPoints (I := I) R) :
    mapGL (zeroChart R) (mapGL (constantPolynomial R) x) = mapGL (constantLaurent R) x := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact Polynomial.toLaurent_C _

private theorem scalesColumn_baseChange {I : Type u} [Fintype I] [DecidableEq I]
    {R S : TestAlgebra k} (f : R ⟶ S) {i : I} {x : MatrixPoints (I := I) R} {c : R}
    (h : ScalesColumn i x c) : ScalesColumn i (mapGL f x) (f.hom c) := by
  intro j
  change f.hom (x.val j i) = _
  rw [h, map_mul]
  by_cases hj : j = i <;> simp [Matrix.one_apply, hj]

private theorem compareColumns {I : Type u} [Fintype I] [DecidableEq I]
    {R : TestAlgebra k} (i : I) (p n : MatrixPoints (I := I) (polynomialAlgebra R))
    (c : Rˣ)
    (h : ∀ j, (mapGL (zeroChart R) p).val j i =
      LaurentPolynomial.C (c : R) * (mapGL (infinityChart R) n).val j i)
    (hn : mapGL (evalAt (0 : R)) n = 1) :
    ScalesColumn i (mapGL (evalAt (0 : R)) p) (c : R) ∧
      ScalesColumn i (mapGL (evalAt (1 : R)) n) 1 := by
  have constant (j : I) := polynomialChartsConstant (p.val j i)
    (Polynomial.C (c : R) * n.val j i) (by
      rw [map_mul, Polynomial.toLaurent_C, map_mul, LaurentPolynomial.invert_C]
      exact h j)
  have atZero (j : I) : (n.val j i).eval 0 = (1 : Matrix I I R) j i := by
    exact congrArg (fun M : MatrixPoints (I := I) R ↦ M.val j i) hn
  constructor
  · intro j
    obtain ⟨d, hp, hn'⟩ := constant j
    have he := (hp 0).trans (hn' 0).symm
    rw [Polynomial.eval_C_mul, atZero] at he
    exact he
  · intro j
    obtain ⟨d, _, hn'⟩ := constant j
    have he := (hn' 1).trans (hn' 0).symm
    rw [Polynomial.eval_C_mul, Polynomial.eval_C_mul, atZero] at he
    change (n.val j i).eval 1 = _
    simpa only [one_mul] using c.mul_right_inj.mp he

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The positive, negative and zero factors of a unitriangular product in the
closed subgroup all belong to the subgroup, over every test algebra. -/
theorem factorRestriction : Specs.TorusLimitFactorRestriction.FactorRestriction.{u} := by
  classical
  intro k _ n r G H j T e t m l hj hdiag R
  dsimp only
  intro a b z ha hb hz hprod
  let w (i : Index.{u} n) : ℤ := ∑ s : Index.{u} r, m i s * l s
  let K : ClosedSubgroup H.val := ⟨G.val, j, hj⟩
  obtain ⟨I, _, _, i, M, eM, f, hK⟩ := chevalleyLine k H K
  let ρ : generalLinearPoints k (Index.{u} n) ⟶ generalLinearPoints k I :=
    e.inv ≫ (groupPointsFunctor k).map f ≫ eM.hom
  let σ := (groupPointsFunctor k).map j ≫ e.hom
  let image (S : TestAlgebra k) : Subgroup (MatrixPoints (I := Index.{u} n) S) :=
    (σ.app S).hom.range
  have mem_image (S : TestAlgebra k) (x : MatrixPoints (I := Index.{u} n) S) :
      x ∈ image S ↔ ∃ c : Sˣ, ScalesColumn i (matrixRepresentation ρ S x) (c : S) := by
    rw [← scalesColumn_iff]
    change (∃ g : Points G.val.X S, e.hom.app S (g ≫ j.hom.hom) = x) ↔
      StabilizesCoordinateLine
        (eM.hom.app S (((groupPointsFunctor k).map f).app S (e.inv.app S x))) i
    rw [hK S]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, ?_⟩
      rw [← hg, e.hom_inv_id_app_apply]
    · rintro ⟨g, hg⟩
      refine ⟨g, ?_⟩
      change g ≫ j.hom.hom = e.inv.app S x at hg
      rw [hg, e.inv_hom_id_app_apply]
  let g : MatrixPoints (I := Index.{u} n) R := a.val * b.val * z.val
  have hg : g ∈ image R := hprod
  obtain ⟨c, hc⟩ := (mem_image R g).mp hg

  let P := polynomialAlgebra R
  let S := laurentAlgebra R
  let τ : Sˣ := laurentMonomialUnits R (Multiplicative.ofAdd 1)
  let torusPoint : Points T.group.X S := t.inv.app S (fun s ↦ τ ^ l s)
  have htorus : t.hom.app S torusPoint = (fun s ↦ τ ^ l s) :=
    t.inv_hom_id_app_apply S _
  let d : MatrixPoints (I := Index.{u} n) S :=
    e.hom.app S (((groupPointsFunctor k).map (T.inclusion ≫ j)).app S torusPoint)
  have hd : d.val = Matrix.diagonal (fun j ↦ LaurentPolynomial.T (w j)) := by
    apply Matrix.ext
    intro i j
    change (e.hom.app S (((groupPointsFunctor k).map (T.inclusion ≫
      K.inclusion)).app S torusPoint)).val i j = _
    rw [hdiag S torusPoint, htorus, characterOnCocharacter]
    change (if i = j then ((τ ^ w i : Sˣ) : S) else 0) =
      (Matrix.diagonal fun j ↦ LaurentPolynomial.T (w j)) i j
    rw [laurentMonomialUnits_zpow]
    by_cases h : i = j <;> simp [h]
  have hdmem : d ∈ image S := by
    refine ⟨((groupPointsFunctor k).map T.inclusion).app S torusPoint, ?_⟩
    change _ = e.hom.app S (((groupPointsFunctor k).map (T.inclusion ≫ j)).app S torusPoint)
    rw [Functor.map_comp]
    rfl
  obtain ⟨q, hq⟩ := (mem_image S d).mp hdmem

  obtain ⟨pb, hpb, hb₀, _⟩ := polynomialConjugationChart w b hb
  obtain ⟨pa, hpa, ha₀, ha₁⟩ := polynomialConjugationChart (fun i ↦ -w i) a
    (fun i j h ↦ ha i j (by simpa only [neg_lt_neg_iff] using h))
  have hbConj : d * mapGL (constantLaurent R) b.val * d⁻¹ = mapGL (zeroChart R) pb := by
    apply diagonalConjugation w hd
    exact hpb
  have haConj : d * mapGL (constantLaurent R) a.val * d⁻¹ = mapGL (infinityChart R) pa := by
    apply diagonalConjugation w hd
    intro i j
    change LaurentPolynomial.invert (pa.val i j).toLaurent = _
    rw [hpa, map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
    congr 2
    omega
  have hzConj : d * mapGL (constantLaurent R) z.val * d⁻¹ = mapGL (constantLaurent R) z.val := by
    apply diagonalConjugation w hd
    intro i j
    change LaurentPolynomial.C (z.val.val i j) =
      LaurentPolynomial.C (z.val.val i j) * LaurentPolynomial.T (w i - w j)
    by_cases hw : w i = w j
    · simp [hw]
    · have hij : i ≠ j := fun h ↦ hw (congrArg w h)
      rw [entry_eq_oneMatrix hz (fun h ↦ hw h.2), Matrix.one_apply_ne hij]
      simp

  let left := pb * mapGL (constantPolynomial R) z.val
  let right := pa⁻¹
  have hsplit : mapGL (zeroChart R) left =
      mapGL (infinityChart R) right * (d * mapGL (constantLaurent R) g * d⁻¹) := by
    dsimp only [left, right, g]
    rw [map_mul, map_inv, mapGL_zeroChart_constant, ← haConj, ← hbConj, ← hzConj]
    simp only [map_mul]
    group
  have hgS : ScalesColumn i (matrixRepresentation ρ S (d * mapGL (constantLaurent R) g * d⁻¹))
      (LaurentPolynomial.C (c : R)) := by
    simp only [map_mul, map_inv, representation_natural]
    exact column_conj (scalesColumn_baseChange (constantLaurent R) hc) hq
  let L := matrixRepresentation ρ P left
  let N := matrixRepresentation ρ P right
  have hcolumns (j : I) : (mapGL (zeroChart R) L).val j i =
      LaurentPolynomial.C (c : R) * (mapGL (infinityChart R) N).val j i := by
    rw [← representation_natural, ← representation_natural, hsplit, map_mul, column_mul hgS,
      mul_comm]
  change mapGL (evalAt (0 : R)) pb = 1 at hb₀
  change mapGL (evalAt (0 : R)) pa = 1 at ha₀
  change mapGL (evalAt (1 : R)) pa = a.val at ha₁
  have hLeft₀ : mapGL (evalAt (0 : R)) left = z.val := by
    dsimp only [left]
    rw [map_mul, mapGL_eval_constant, hb₀, one_mul]
  have hRight₀ : mapGL (evalAt (0 : R)) right = 1 := by
    dsimp only [right]
    rw [map_inv, ha₀, inv_one]
  have hRight₁ : mapGL (evalAt (1 : R)) right = a.val⁻¹ := by
    dsimp only [right]
    rw [map_inv, ha₁]
  have hN₀ : mapGL (evalAt (0 : R)) N = 1 := by
    rw [← representation_natural, hRight₀, map_one]
  obtain ⟨hL, hN⟩ := compareColumns i L N c hcolumns hN₀
  rw [← representation_natural, hLeft₀] at hL
  rw [← representation_natural, hRight₁] at hN
  have hzmem := (mem_image R z.val).mpr ⟨c, hL⟩
  have hamem := (image R).inv_mem ((mem_image R a.val⁻¹).mpr ⟨1, hN⟩)
  rw [inv_inv] at hamem
  refine ⟨hamem, ?_, hzmem⟩
  have hbmem := (image R).mul_mem ((image R).mul_mem ((image R).inv_mem hamem) hg)
    ((image R).inv_mem hzmem)
  have heq : a.val⁻¹ * g * z.val⁻¹ = b.val := by
    dsimp only [g]
    group
  rwa [heq] at hbmem

end

end LinearAlgebraicGroups.TorusLimitFactorRestriction
