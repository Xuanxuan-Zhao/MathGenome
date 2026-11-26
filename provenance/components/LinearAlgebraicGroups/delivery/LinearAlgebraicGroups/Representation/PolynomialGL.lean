import Specs.LinearAlgebraicGroups.Representation.PolynomialGL
import LinearAlgebraicGroups.Reductive.GeneralLinearStructure
import LinearAlgebraicGroups.Representation.PrimitiveLine
import LinearAlgebraicGroups.Affine.StandardGroups
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.LinearAlgebra.ExteriorPower.Basis

open CategoryTheory
open scoped BigOperators

universe u

namespace LinearAlgebraicGroups.Representation.PolynomialGL

open LinearAlgebraicGroups.Specs
open Specs.PolynomialGL
open LinearAlgebraicGroups.Specs.StandardGroups
open private matrixEvaluation matrixEvaluation_mapMatrix isUnit_matrixEvaluation_det
  glEvaluation glEvaluation_entry universalGeneralLinear from LinearAlgebraicGroups.Affine.StandardGroups

noncomputable section

variable {k m I : Type u} [Field k] [Fintype m] [DecidableEq m] [Fintype I] [DecidableEq I]

private theorem representationAt_natural {R S : TestAlgebra k} (f : R ⟶ S)
    (ρ : MatrixRepresentation k m I) (g : Matrix.GeneralLinearGroup m R) :
    Matrix.GeneralLinearGroup.map f.hom.toRingHom (representationAt ρ R g) =
      representationAt ρ S (Matrix.GeneralLinearGroup.map f.hom.toRingHom g) :=
  (ConcreteCategory.congr_hom (ρ.naturality f) g).symm

private theorem evaluation_generic {R : Type u} [CommRing R] [Algebra k R]
    (X : Matrix m m R) : (evaluateMatrix X).mapMatrix (genericMatrix k m) = X :=
  matrixEvaluation_mapMatrix X

private theorem evaluation_comp {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) (X : Matrix m m R) :
    f.comp (evaluateMatrix X) = evaluateMatrix (f.mapMatrix X) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp [evaluateMatrix]

private theorem genericDeterminant_ne_zero : genericDeterminant k m ≠ 0 := by
  have h : evaluateMatrix (1 : Matrix m m k) (genericDeterminant k m) = 1 := by
    rw [genericDeterminant, AlgHom.map_det, evaluation_generic, Matrix.det_one]
  intro hz
  rw [hz, map_zero] at h
  exact zero_ne_one h

private theorem away_algebraMap_injective {A : Type u} [CommRing A] [IsDomain A]
    (d : A) (hd : d ≠ 0) : Function.Injective (algebraMap A (Localization.Away d)) := by
  apply IsLocalization.injective (M := Submonoid.powers d)
  apply le_nonZeroDivisors_of_noZeroDivisors
  rintro ⟨n, hn⟩
  exact pow_ne_zero n hd hn

private abbrev universalPoint : Matrix.GeneralLinearGroup m (GLCoordinates k m) :=
  universalGeneralLinear

private theorem pointEvaluation_algebraMap {R : Type u} [CommRing R] [Algebra k R]
    (g : Matrix.GeneralLinearGroup m R) (p : MvPolynomial (m × m) k) :
    glEvaluation (k := k) g (algebraMap (MvPolynomial (m × m) k) (GLCoordinates k m) p) =
      evaluateMatrix g.val p :=
  IsLocalization.Away.lift_eq (S := GLCoordinates k m) (genericDeterminant k m)
    (g := (matrixEvaluation g.val).toRingHom) (isUnit_matrixEvaluation_det g) p

private theorem pointEvaluation_universal {R : Type u} [CommRing R] [Algebra k R]
    (g : Matrix.GeneralLinearGroup m R) :
    Matrix.GeneralLinearGroup.map (glEvaluation (k := k) g).toRingHom (universalPoint (k := k)) = g :=
  Matrix.GeneralLinearGroup.ext (glEvaluation_entry g)

private theorem twist_matrix (ρ : MatrixRepresentation k m I) (a : ℤ) (R : TestAlgebra k)
    (g : Matrix.GeneralLinearGroup m R) :
    (representationAt (determinantTwist ρ a) R g).val =
      (g.det ^ a).val • (representationAt ρ R g).val := by
  change Matrix.scalar I (g.det ^ a).val * (representationAt ρ R g).val = _
  exact (Matrix.smul_eq_diagonal_mul _ _).symm

/-- Finitely many coefficients of a rational representation have a common determinant denominator. -/
theorem commonDenominator : CommonDenominator.{u} := by
  intro k m I _ _ _ _ _ ρ
  classical
  let A := MvPolynomial (m × m) k
  let d := genericDeterminant k m
  let C := GLCoordinates k m
  let D := algebraMap A C d
  let R := CommAlgCat.of k C
  let g : Matrix.GeneralLinearGroup m R := universalPoint
  let c : Matrix I I C := (representationAt ρ R g).val
  have hdet : g.det.val = D := by
    change (universalMatrix k m).det = D
    exact (RingHom.map_det (algebraMap A C) (genericMatrix k m)).symm
  have frac (ij : I × I) : ∃ (p : A) (j : ℕ), c ij.1 ij.2 * D ^ j = algebraMap A C p := by
    obtain ⟨⟨p, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers d) (c ij.1 ij.2)
    obtain ⟨j, hj⟩ := s.property
    refine ⟨p, j, ?_⟩
    change c ij.1 ij.2 * algebraMap A C (s : A) = _ at hs
    rw [← hj, map_pow] at hs
    exact hs
  choose p degree hdegree using frac
  let a := Finset.univ.sup degree
  let P : Matrix I I A := fun i j => p (i, j) * d ^ (a - degree (i, j))
  refine ⟨a, P, ?_⟩
  have hcoeff : (representationAt (determinantTwist ρ (a : ℤ)) R g).val =
      (algebraMap A C).mapMatrix P := by
    rw [twist_matrix]
    ext i j
    have hle : degree (i, j) ≤ a := Finset.le_sup (Finset.mem_univ (i, j))
    change (g.det ^ (a : ℤ)).val * c i j =
      algebraMap A C (p (i, j) * d ^ (a - degree (i, j)))
    rw [zpow_natCast, Units.val_pow_eq_pow_val, hdet, map_mul, map_pow, ← hdegree (i, j),
      mul_assoc, ← pow_add, Nat.add_sub_of_le hle, mul_comm]
  intro S x
  let f : R ⟶ S := CommAlgCat.ofHom (glEvaluation x)
  have hx : Matrix.GeneralLinearGroup.map f.hom.toRingHom g = x := pointEvaluation_universal x
  have hnat := representationAt_natural f (determinantTwist ρ (a : ℤ)) g
  rw [hx] at hnat
  ext i j
  rw [← hnat]
  change glEvaluation x ((representationAt (determinantTwist ρ (a : ℤ)) R g).val i j) =
    evaluateMatrix x.val (P i j)
  rw [hcoeff]
  exact pointEvaluation_algebraMap x (P i j)

private theorem map_evaluateCoefficients {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S)
    (P : Matrix I I (MvPolynomial (m × m) k)) (X : Matrix m m R) :
    f.mapMatrix (evaluateCoefficients P X) = evaluateCoefficients P (f.mapMatrix X) := by
  ext i j
  exact DFunLike.congr_fun (evaluation_comp f X) (P i j)

private theorem point_multiplicativity (ρ : MatrixRepresentation k m I)
    {P : Matrix I I (MvPolynomial (m × m) k)} (hP : EvaluatesTo ρ P)
    (R : TestAlgebra k) (g h : Matrix.GeneralLinearGroup m R) :
    evaluateCoefficients P (g.val * h.val) =
      evaluateCoefficients P g.val * evaluateCoefficients P h.val := by
  rw [← hP R g, ← hP R h]
  change evaluateCoefficients P (g * h).val = _
  rw [← hP R (g * h), map_mul]
  rfl

private theorem generic_pair_multiplicativity (ρ : MatrixRepresentation k m I)
    {P : Matrix I I (MvPolynomial (m × m) k)} (hP : EvaluatesTo ρ P) :
    let A := MvPolynomial ((m × m) ⊕ (m × m)) k
    let X : Matrix m m A := fun i j => MvPolynomial.X (.inl (i, j))
    let Y : Matrix m m A := fun i j => MvPolynomial.X (.inr (i, j))
    evaluateCoefficients P (X * Y) = evaluateCoefficients P X * evaluateCoefficients P Y := by
  dsimp only
  let A := MvPolynomial ((m × m) ⊕ (m × m)) k
  let X : Matrix m m A := fun i j => MvPolynomial.X (.inl (i, j))
  let Y : Matrix m m A := fun i j => MvPolynomial.X (.inr (i, j))
  change evaluateCoefficients P (X * Y) = evaluateCoefficients P X * evaluateCoefficients P Y
  let d := X.det * Y.det
  let C := Localization.Away d
  let f : A →ₐ[k] C := IsScalarTower.toAlgHom k A C
  let R := CommAlgCat.of k C
  let e : A →ₐ[k] k := MvPolynomial.aeval
    (Sum.elim (fun ij => (1 : Matrix m m k) ij.1 ij.2) (fun ij => (1 : Matrix m m k) ij.1 ij.2))
  have hX : e.mapMatrix X = 1 := by
    ext i j
    change e (MvPolynomial.X (.inl (i, j))) = _
    dsimp only [e]
    rw [MvPolynomial.aeval_X]
    rfl
  have hY : e.mapMatrix Y = 1 := by
    ext i j
    change e (MvPolynomial.X (.inr (i, j))) = _
    dsimp only [e]
    rw [MvPolynomial.aeval_X]
    rfl
  have hd : d ≠ 0 := by
    have h : e d = 1 := by
      simp only [d, map_mul, AlgHom.map_det, hX, hY, Matrix.det_one, one_mul]
    intro hz
    rw [hz, map_zero] at h
    exact zero_ne_one h
  have hu : IsUnit (f d) := IsLocalization.Away.algebraMap_isUnit d
  have hu' : IsUnit ((f.mapMatrix X).det * (f.mapMatrix Y).det) := by
    rwa [← f.map_det, ← f.map_det, ← map_mul]
  let g : Matrix.GeneralLinearGroup m R :=
    Matrix.GeneralLinearGroup.mk'' (f.mapMatrix X) (isUnit_of_mul_isUnit_left hu')
  let h : Matrix.GeneralLinearGroup m R :=
    Matrix.GeneralLinearGroup.mk'' (f.mapMatrix Y) (isUnit_of_mul_isUnit_right hu')
  have hh := point_multiplicativity ρ hP R g h
  change evaluateCoefficients P (f.mapMatrix X * f.mapMatrix Y) =
    evaluateCoefficients P (f.mapMatrix X) * evaluateCoefficients P (f.mapMatrix Y) at hh
  rw [← map_mul, ← map_evaluateCoefficients, ← map_evaluateCoefficients,
    ← map_evaluateCoefficients, ← map_mul] at hh
  apply Matrix.ext
  intro i j
  exact away_algebraMap_injective d hd (congrFun (congrFun hh i) j)

private theorem evaluateCoefficients_mul (ρ : MatrixRepresentation k m I)
    {P : Matrix I I (MvPolynomial (m × m) k)} (hP : EvaluatesTo ρ P)
    (R : TestAlgebra k) (M N : Matrix m m R) :
    evaluateCoefficients P (M * N) = evaluateCoefficients P M * evaluateCoefficients P N := by
  let A := MvPolynomial ((m × m) ⊕ (m × m)) k
  let X : Matrix m m A := fun i j => MvPolynomial.X (.inl (i, j))
  let Y : Matrix m m A := fun i j => MvPolynomial.X (.inr (i, j))
  let f : A →ₐ[k] R := MvPolynomial.aeval
    (Sum.elim (fun ij => M ij.1 ij.2) (fun ij => N ij.1 ij.2))
  have hX : f.mapMatrix X = M := by
    ext i j
    change f (MvPolynomial.X (.inl (i, j))) = _
    dsimp only [f]
    rw [MvPolynomial.aeval_X]
    rfl
  have hY : f.mapMatrix Y = N := by
    ext i j
    change f (MvPolynomial.X (.inr (i, j))) = _
    dsimp only [f]
    rw [MvPolynomial.aeval_X]
    rfl
  have hh : evaluateCoefficients P (X * Y) = evaluateCoefficients P X * evaluateCoefficients P Y :=
    generic_pair_multiplicativity ρ hP
  have hf := congrArg f.mapMatrix hh
  rwa [map_mul, map_evaluateCoefficients, map_evaluateCoefficients, map_evaluateCoefficients,
    map_mul, hX, hY] at hf

private theorem evaluateCoefficients_universal
    (P : Matrix I I (MvPolynomial (m × m) k)) :
    evaluateCoefficients P (universalPoint (k := k)).val =
      (algebraMap (MvPolynomial (m × m) k) (GLCoordinates k m)).mapMatrix P := by
  let f : MvPolynomial (m × m) k →ₐ[k] GLCoordinates k m := IsScalarTower.toAlgHom _ _ _
  change evaluateCoefficients P (f.mapMatrix (genericMatrix k m)) = f.mapMatrix P
  rw [← map_evaluateCoefficients]
  change f.mapMatrix ((MvPolynomial.aeval MvPolynomial.X).mapMatrix P) = f.mapMatrix P
  rw [MvPolynomial.aeval_X_left]
  rfl

/-- Polynomial coefficients extend uniquely to the full matrix monoid. -/
theorem monoidExtension : MonoidExtension.{u} := by
  intro k m I _ _ _ _ _ ρ
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨P, ⟨hP, fun R => ⟨?_, evaluateCoefficients_mul ρ hP R⟩⟩, ?_⟩
    · rw [← Matrix.GeneralLinearGroup.coe_one, ← hP]
      rw [map_one]
      rfl
    · intro Q hQ
      let R := CommAlgCat.of k (GLCoordinates k m)
      let g : Matrix.GeneralLinearGroup m R := universalPoint
      have hh := (hQ.1 R g).symm.trans (hP R g)
      change evaluateCoefficients Q (universalPoint (k := k)).val =
        evaluateCoefficients P (universalPoint (k := k)).val at hh
      rw [evaluateCoefficients_universal, evaluateCoefficients_universal] at hh
      apply Matrix.ext
      intro i j
      exact away_algebraMap_injective _ (genericDeterminant_ne_zero (k := k) (m := m))
        (congrFun (congrFun hh i) j)
  · rintro ⟨P, hP, _⟩
    exact ⟨P, hP.1⟩

theorem diagonalPoint_val {R : Type u} [CommRing R] (t : m → Rˣ) :
    (diagonalPoint t).val = Matrix.diagonal (fun i => (t i).val) := rfl

theorem determinant_diagonalPoint {R : Type u} [CommRing R] (t : m → Rˣ) :
    (diagonalPoint t).det = ∏ i, t i := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, diagonalPoint_val, Matrix.det_diagonal]
  exact (map_prod (Units.coeHom R) _ _).symm

omit [DecidableEq m] in
private theorem weightValue_shift {R : Type u} [CommRing R]
    (lam : m → ℤ) (t : m → Rˣ) (a : ℤ) :
    weightValue (fun i => lam i + a) t = (∏ i, t i) ^ a * weightValue lam t := by
  simp only [weightValue, zpow_add, Finset.prod_mul_distrib, Finset.prod_zpow]
  exact mul_comm _ _

/-- The determinant twist adds the same integer to every weight coordinate. -/
theorem shiftWeights : ShiftWeights.{u} := by
  intro k m I _ _ _ _ _ ρ a lam v
  unfold HasWeight
  constructor <;> intro hw R t
  · have he := hw R t
    rw [twist_matrix, Matrix.smul_mulVec, determinant_diagonalPoint,
      weightValue_shift, Units.val_mul, mul_smul] at he
    let b : Rˣ := (∏ i, t i) ^ a
    change b.val • _ = b.val • _ at he
    have hh := congrArg (fun w : I → R => (b⁻¹).val • w) he
    simpa only [smul_smul, ← Units.val_mul, ← mul_assoc, inv_mul_cancel, Units.val_one, one_mul, one_smul] using hh
  · rw [twist_matrix, Matrix.smul_mulVec, hw R t, determinant_diagonalPoint,
      weightValue_shift, Units.val_mul, mul_smul]

private def laurentUnits (k : Type u) [Field k] :
    Multiplicative ℤ →* (LaurentPolynomial k)ˣ where
  toFun n :=
    { val := LaurentPolynomial.T n.toAdd
      inv := LaurentPolynomial.T (-n.toAdd)
      val_inv := by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
      inv_val := by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero] }
  map_one' := Units.ext LaurentPolynomial.T_zero
  map_mul' a b := Units.ext (LaurentPolynomial.T_add a.toAdd b.toAdd)

private theorem laurentUnits_zpow (a : ℤ) :
    ((laurentUnits k (Multiplicative.ofAdd 1)) ^ a).val =
      LaurentPolynomial.T (R := k) a := by
  rw [← map_zpow]
  change LaurentPolynomial.T ((Multiplicative.ofAdd (1 : ℤ) ^ a).toAdd) = _
  rw [Int.toAdd_zpow]
  simp

private theorem weightValue_single {R : Type u} [CommRing R]
    (lam : m → ℤ) (i : m) (z : Rˣ) :
    weightValue lam (fun j => if j = i then z else 1) = z ^ lam i := by
  unfold weightValue
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp


/-- Characters given by exponent vectors are distinguished over test algebras. -/
theorem weight_exponents_eq {lam mu : m → ℤ}
    (h : ∀ (R : TestAlgebra k) (t : m → Rˣ),
      (weightValue lam t).val = (weightValue mu t).val) : lam = mu := by
  funext i
  let R := CommAlgCat.of k (LaurentPolynomial k)
  let z := laurentUnits k (Multiplicative.ofAdd 1)
  have he := h R (fun j => if j = i then z else 1)
  rw [weightValue_single, weightValue_single, laurentUnits_zpow, laurentUnits_zpow] at he
  by_contra hne
  have hc := congrArg (fun p : LaurentPolynomial k => p.coeff (lam i)) he
  exact one_ne_zero (by simpa only [LaurentPolynomial.T_apply, ite_true, ite_eq_right (Ne.symm hne)] using hc)

/-- Restriction to a single diagonal coordinate detects each negative exponent. -/
theorem nonnegativeWeights : NonnegativeWeights.{u} := by
  intro k m I _ _ _ _ _ ρ hρ lam v hv hw i
  obtain ⟨P, hP⟩ := hρ
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  let R := CommAlgCat.of k (LaurentPolynomial k)
  let z := laurentUnits k (Multiplicative.ofAdd 1)
  let t : m → Rˣ := fun l => if l = i then z else 1
  let X : Matrix m m (Polynomial k) :=
    Matrix.diagonal (fun l => if l = i then Polynomial.X else 1)
  let f : Polynomial k →ₐ[k] LaurentPolynomial k := Polynomial.toLaurentAlg
  have hX : f.mapMatrix X = (diagonalPoint t).val := by
    rw [diagonalPoint_val]
    ext a b : 2
    by_cases hab : a = b
    · subst b
      by_cases ha : a = i <;> simp [X, f, t, z, ha, laurentUnits]
    · simp [X, f, hab]
  have hV : (RootWeightAction.extendVector R v : I → LaurentPolynomial k) =
      fun l => f (Polynomial.C (v l)) := by
    funext l
    exact (f.commutes (v l)).symm
  have hW := hw R t
  rw [hP R (diagonalPoint t), ← hX, ← map_evaluateCoefficients, weightValue_single] at hW
  have heq := congrFun hW j
  change ((f.mapMatrix (evaluateCoefficients P X)).mulVec
    (RootWeightAction.extendVector R v)) j = (z ^ lam i).val *
      RootWeightAction.extendVector R v j at heq
  rw [hV] at heq
  let p : Polynomial k := ((evaluateCoefficients P X).mulVec (fun l => Polynomial.C (v l))) j
  have hleft : ((f.mapMatrix (evaluateCoefficients P X)).mulVec
      (fun l => f (Polynomial.C (v l)))) j = f p := by
    simp [p, Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [hleft, laurentUnits_zpow] at heq
  simp only [f, Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_C] at heq
  have hmem : lam i ∈ p.toLaurent.coeff.support := by
    rw [heq, LaurentPolynomial.T_mul, LaurentPolynomial.support_coeff_C_mul_T_of_ne_zero hj]
    exact Finset.mem_singleton_self _
  rw [LaurentPolynomial.support_coeff_toLaurent, Finset.mem_map] at hmem
  obtain ⟨a, _, ha⟩ := hmem
  change (a : ℤ) = lam i at ha
  rw [← ha]
  exact Int.natCast_nonneg a

/-- Polynomial coefficients descend to stable subspaces and quotients. -/
theorem polynomialSubquotients : PolynomialSubquotients.{u} := by
  intro k m I J _ _ _ _ _ _ _ ρ σ p s hps hint ⟨P, hP⟩
  refine ⟨p.map MvPolynomial.C * P * s.map MvPolynomial.C, ?_⟩
  intro R g
  let f := evaluateMatrix (k := k) g.val
  let pR := p.map (algebraMap k R)
  let sR := s.map (algebraMap k R)
  let A := (representationAt ρ R g).val
  let B := (representationAt σ R g).val
  have heval :
      evaluateCoefficients (p.map MvPolynomial.C * P * s.map MvPolynomial.C) g.val =
        pR * A * sR := by
    change ((p.map MvPolynomial.C * P * s.map MvPolynomial.C).map f.toRingHom) = _
    simp only [Matrix.map_mul (f := f.toRingHom), Matrix.map_map, Function.comp_def]
    have hp := hP R g
    change A = P.map f.toRingHom at hp
    have hc : (fun x : k => f.toRingHom (MvPolynomial.C x)) = algebraMap k R :=
      funext f.commutes
    rw [← hp, hc]
  have hs : pR * sR = 1 := by
    change p.map (algebraMap k R) * s.map (algebraMap k R) = 1
    rw [← Matrix.map_mul (f := algebraMap k R), hps, Matrix.map_one _ (map_zero _) (map_one _)]
  change B = _
  rw [heval]
  rcases hint with hincl | hproj
  · have h : A * sR = sR * B := hincl R g
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hs, Matrix.one_mul]
  · have h : pR * A = B * pR := hproj R g
    rw [h, Matrix.mul_assoc, hs, Matrix.mul_one]

private theorem prod_characterCoordinate {R : Type u} [CommRing R] (i : m) (z : Rˣ) :
    (∏ l : m, if l = i then z else 1) = z := by
  rw [Finset.prod_eq_single i]
  · simp
  · intro l _ hl
    simp [hl]
  · simp

omit [Fintype m] in
private theorem corootPoint_factor {R : Type u} [CommRing R] {i j : m}
    (hij : i ≠ j) (z : Rˣ) (l : m) :
    corootPoint i j z l = (if l = i then z else 1) * (if l = j then z⁻¹ else 1) := by
  by_cases hi : l = i
  · subst l
    simp [corootPoint, hij]
  · simp [corootPoint, hi]

/-- The two-coordinate determinant-one diagonal pairs with an exponent vector by subtraction. -/
theorem corootEvaluation : CorootEvaluation.{u} := by
  intro m R _ _ _ i j hij z
  constructor
  · rw [determinant_diagonalPoint]
    simp only [corootPoint_factor hij z, Finset.prod_mul_distrib,
      prod_characterCoordinate, mul_inv_cancel]
  · intro lam
    unfold weightValue
    simp only [corootPoint_factor hij z, mul_zpow, Finset.prod_mul_distrib]
    change weightValue lam (fun l => if l = i then z else 1) *
      weightValue lam (fun l => if l = j then z⁻¹ else 1) = _
    rw [weightValue_single, weightValue_single, inv_zpow, zpow_sub]

private theorem rankOneMatrix_entries {R : Type u} [CommRing R] {i j : m}
    (hij : i ≠ j) (z : Rˣ) :
    Matrix.transvection i j z.val * Matrix.transvection j i (-(z⁻¹).val) *
      Matrix.transvection i j z.val =
    Matrix.diagonal (fun a => if a = i ∨ a = j then (0 : R) else 1) +
      Matrix.single i j z.val + Matrix.single j i (-(z⁻¹).val) := by
  apply Matrix.ext
  intro a b
  rw [Matrix.mul_assoc]
  have h₁ : z.val * (z⁻¹).val = 1 := z.val_inv
  have h₂ : (z⁻¹).val * z.val = 1 := z.inv_val
  by_cases hai : a = i
  · subst a
    rw [Matrix.transvection_mul_apply_same, Matrix.transvection_mul_apply_of_ne _ _ _ _ hij,
      Matrix.transvection_mul_apply_same]
    by_cases hb : b = i
    · subst b
      simp [Matrix.transvection, hij, hij.symm, h₁]
    · by_cases hb' : b = j
      · subst b
        simp [Matrix.transvection, hij, hij.symm, h₂]
      · simp [Matrix.transvection, hij, hij.symm, Ne.symm hb, Ne.symm hb']
  · rw [Matrix.transvection_mul_apply_of_ne _ _ _ _ hai]
    by_cases haj : a = j
    · subst a
      rw [Matrix.transvection_mul_apply_same]
      by_cases hb : b = i
      · subst b
        simp [Matrix.transvection, hij, hij.symm]
      · by_cases hb' : b = j
        · subst b
          simp [Matrix.transvection, hij, hij.symm,
            show -(z⁻¹).val * z.val = -1 by rw [neg_mul, h₂]]
        · simp [Matrix.transvection, hij, Ne.symm hb, Ne.symm hb']
    · rw [Matrix.transvection_mul_apply_of_ne _ _ _ _ haj]
      simp [Matrix.transvection, Matrix.one_apply, Matrix.diagonal_apply, Matrix.single_apply, hai, haj, Ne.symm haj]

/-- The coroot diagonal comes from the rank-one word in the two coordinate root groups. -/
theorem matrixCorootWord : MatrixCorootWord.{u} := by
  intro m R _ _ _ i j hij z
  dsimp only
  apply (mul_inv_eq_iff_eq_mul).2
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.transvection, diagonalPoint_val]
  rw [rankOneMatrix_entries hij z, rankOneMatrix_entries hij (1 : Rˣ)]
  apply Matrix.ext
  intro a b
  rw [Matrix.diagonal_mul]
  by_cases hai : a = i
  · subst a
    by_cases hb : b = j
    · subst b
      simp [corootPoint, hij, hij.symm]
    · simp [corootPoint, hij.symm, Ne.symm hb, Matrix.diagonal_apply]
  · by_cases haj : a = j
    · subst a
      by_cases hb : b = i <;>
        simp [corootPoint, hij.symm, hij, hb, Matrix.diagonal_apply, Matrix.single_apply]
    · simp [corootPoint, hai, haj, Ne.symm hai, Ne.symm haj, Matrix.diagonal_apply]

theorem adjacentDominance : AdjacentDominance.{u} := by
  intro n lam
  let f : Fin (n + 1) → ℤ := fun i => lam ⟨i⟩
  have hf : Antitone f ↔ Antitone lam := by
    constructor
    · intro h a b hab
      exact h (show a.down ≤ b.down from hab)
    · intro h a b hab
      exact h (show (⟨a⟩ : Unipotent.Index.{u} (n + 1)) ≤ ⟨b⟩ from hab)
  rw [← hf, Fin.antitone_iff_succ_le]
  exact forall_congr' fun i => sub_nonneg

section ExteriorPower

variable {N R S : Type u} [Fintype N] [LinearOrder N] [DecidableEq N] [CommRing R] [CommRing S]

private theorem minorMatrix_eq_toMatrix (q : ℕ) (X : Matrix N N R) :
    minorMatrix q X = (exteriorPower.map q X.mulVecLin).toMatrix
      ((Pi.basisFun R N).exteriorPower q) ((Pi.basisFun R N).exteriorPower q) := by
  apply Matrix.ext
  intro s t
  rw [LinearMap.toMatrix_apply, exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti,
    exteriorPower.ιMultiDual_apply_ιMulti, ← Matrix.det_transpose]
  unfold minorMatrix
  congr 1
  apply Matrix.ext
  intro i j
  simp [Matrix.mulVec_single]

private theorem minorMatrix_one (q : ℕ) :
    minorMatrix q (1 : Matrix N N R) = 1 := by
  rw [minorMatrix_eq_toMatrix, Matrix.mulVecLin_one, exteriorPower.map_id,
    LinearMap.toMatrix_id]

private theorem minorMatrix_mul (q : ℕ) (X Y : Matrix N N R) :
    minorMatrix q (X * Y) = minorMatrix q X * minorMatrix q Y := by
  rw [minorMatrix_eq_toMatrix, Matrix.mulVecLin_mul, exteriorPower.map_comp,
    LinearMap.toMatrix_comp _ ((Pi.basisFun R N).exteriorPower q),
    ← minorMatrix_eq_toMatrix, ← minorMatrix_eq_toMatrix]

omit [Fintype N] [DecidableEq N] in
private theorem minorMatrix_map (q : ℕ) (f : R →+* S) (X : Matrix N N R) :
    (minorMatrix q X).map f = minorMatrix q (X.map f) := by
  apply Matrix.ext
  intro s t
  exact f.map_det (X.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
    (Set.powersetCard.ofFinEmbEquiv.symm t))

private def exteriorPointHom (q : ℕ) :
    Matrix.GeneralLinearGroup N R →* Matrix.GeneralLinearGroup (Set.powersetCard N q) R :=
  Units.map
    { toFun := minorMatrix q
      map_one' := minorMatrix_one q
      map_mul' := minorMatrix_mul q }

/-- The rational exterior-power action is given by the compound matrix. -/
def exteriorRepresentation (q : ℕ) :
    MatrixRepresentation k N (Set.powersetCard N q) where
  app R := GrpCat.ofHom (exteriorPointHom q :
    Matrix.GeneralLinearGroup N R →* Matrix.GeneralLinearGroup (Set.powersetCard N q) R)
  naturality R S f := GrpCat.ext fun (g : Matrix.GeneralLinearGroup N R) => by
    apply Units.ext
    exact (minorMatrix_map q f.hom.toRingHom g.val).symm

private theorem representationAt_exterior (q : ℕ) (R : TestAlgebra k)
    (g : Matrix.GeneralLinearGroup N R) :
    (representationAt (exteriorRepresentation q) R g).val = minorMatrix q g.val := rfl

private theorem exterior_evaluates (q : ℕ) :
    EvaluatesTo (exteriorRepresentation (k := k) (N := N) q)
      (minorMatrix q (genericMatrix k N)) := by
  intro R g
  rw [representationAt_exterior]
  change minorMatrix q g.val =
    (minorMatrix q (genericMatrix k N)).map (evaluateMatrix g.val).toRingHom
  rw [minorMatrix_map]
  exact congrArg (minorMatrix q) (evaluation_generic g.val).symm

/-- Exterior-power representations have polynomial matrix entries. -/
theorem exteriorCoefficients : ExteriorCoefficients.{u} := by
  intro k N _ _ _ _ q
  exact ⟨exteriorRepresentation q, exterior_evaluates q⟩

private theorem extend_single {J : Type u} [DecidableEq J] (R : TestAlgebra k) (j : J) :
    RootWeightAction.extendVector R (Pi.single j (1 : k)) = Pi.single j (1 : R) := by
  funext i
  by_cases h : i = j <;> simp [RootWeightAction.extendVector, Pi.single, h]

open Unipotent (Index)

private theorem lt_of_not_mem_initial {n q : ℕ} (h : q ≤ n) {i : Index.{u} n}
    (hi : i ∉ Set.powersetCard.ofFinEmbEquiv (initialEmbedding h)) (j : Fin q) :
    initialEmbedding h j < i := by
  have hn : ¬ i.down.val < q := by
    intro hp
    apply hi
    rw [Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
    exact ⟨⟨i.down.val, hp⟩, rfl⟩
  change j.val < i.down.val
  omega

private theorem minor_initial_off_diagonal {n q : ℕ} (h : q ≤ n)
    (X : Matrix (Index.{u} n) (Index.{u} n) R) (hX : X.IsUpperTriangular)
    {s : Set.powersetCard (Index.{u} n) q}
    (hs : s ≠ Set.powersetCard.ofFinEmbEquiv (initialEmbedding h)) :
    minorMatrix q X s (Set.powersetCard.ofFinEmbEquiv (initialEmbedding h)) = 0 := by
  let t := Set.powersetCard.ofFinEmbEquiv (initialEmbedding h)
  obtain ⟨i, his, hit⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne s t).mp hs
  obtain ⟨j, rfl⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).2 his
  unfold minorMatrix
  rw [Equiv.symm_apply_apply]
  apply Matrix.det_eq_zero_of_row_eq_zero j
  intro l
  exact hX (lt_of_not_mem_initial h hit l)

private theorem minor_initial_diagonal {n q : ℕ} (h : q ≤ n)
    (X : Matrix (Index.{u} n) (Index.{u} n) R) (hX : X.IsUpperTriangular) :
    minorMatrix q X (Set.powersetCard.ofFinEmbEquiv (initialEmbedding h))
        (Set.powersetCard.ofFinEmbEquiv (initialEmbedding h)) =
      ∏ j : Fin q, X (initialEmbedding h j) (initialEmbedding h j) := by
  unfold minorMatrix
  rw [Equiv.symm_apply_apply, Matrix.det_of_isUpperTriangular]
  · rfl
  · intro i j hij
    exact hX ((initialEmbedding h).strictMono hij)

private theorem initial_column {n q : ℕ} (h : q ≤ n)
    (X : Matrix (Index.{u} n) (Index.{u} n) R) (hX : X.IsUpperTriangular) :
    let j := Set.powersetCard.ofFinEmbEquiv (initialEmbedding h)
    (minorMatrix q X).mulVec (Pi.single j (1 : R)) =
      (∏ a : Fin q, X (initialEmbedding h a) (initialEmbedding h a)) • Pi.single j 1 := by
  dsimp only
  let j := Set.powersetCard.ofFinEmbEquiv (initialEmbedding h)
  change (minorMatrix q X).mulVec (Pi.single j 1) = _ • Pi.single j 1
  rw [Matrix.mulVec_single_one]
  funext s
  by_cases hs : s = j
  · subst s
    simpa [j] using minor_initial_diagonal h X hX
  · simpa [Pi.single, hs] using minor_initial_off_diagonal h X hX hs

private theorem initial_weightValue {n q : ℕ} (h : q ≤ n) (t : Index.{u} n → Rˣ) :
    weightValue (fun i => if i.down.val < q then 1 else 0) t =
      ∏ i : Fin q, t (initialEmbedding h i) := by
  unfold weightValue
  have hw (i : Index.{u} n) :
      t i ^ (if i.down.val < q then (1 : ℤ) else 0) =
        if i.down.val < q then t i else 1 := by
    split_ifs <;> simp
  simp only [hw, ← Finset.prod_filter]
  have hf : Finset.univ.filter (fun i : Index.{u} n => i.down.val < q) =
      Finset.univ.map (initialEmbedding h).toEmbedding := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hi
      exact ⟨⟨i.down.val, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.isLt
  rw [hf, Finset.prod_map]
  rfl

set_option maxHeartbeats 800000 in
/-- The initial wedge is nonzero and primitive for the upper triangular Borel. -/
theorem exteriorPrimitive : ExteriorPrimitive.{u} := by
  intro k _ n q h
  let j := Set.powersetCard.ofFinEmbEquiv (initialEmbedding.{u} h)
  refine ⟨exteriorRepresentation (k := k) (N := Index.{u} n) q,
    exterior_evaluates (k := k) (N := Index.{u} n) q, ?_, ?_, ?_⟩
  · intro hz
    have hzero := congrFun hz j
    exact one_ne_zero (by simpa only [j, Pi.single_eq_same, Pi.zero_apply] using hzero)
  · intro R t
    rw [representationAt_exterior, extend_single, initial_weightValue h]
    have ht : (diagonalPoint t).val.IsUpperTriangular := by
      rw [diagonalPoint_val]
      intro a b hab
      exact Matrix.diagonal_apply_ne _ (ne_of_gt hab)
    have hh := initial_column h (diagonalPoint t).val ht
    have hp : (∏ i : Fin q, t (initialEmbedding h i)).val =
        ∏ i : Fin q, (t (initialEmbedding h i)).val :=
      map_prod (Units.coeHom R) (fun i => t (initialEmbedding h i)) Finset.univ
    rw [hp]
    simpa only [diagonalPoint_val, Matrix.diagonal_apply_eq] using hh
  · intro R g hg hgdiag
    rw [representationAt_exterior, extend_single]
    simpa only [hgdiag, Finset.prod_const_one, one_smul] using initial_column h g.val hg

end ExteriorPower

section TensorProduct

open scoped Kronecker
open Unipotent (Index)

variable {J : Type u} [Fintype J] [DecidableEq J]

/-- Tensor action on the product of the two basis index sets. -/
def tensorRepresentation (ρ : MatrixRepresentation k m I) (σ : MatrixRepresentation k m J) :
    MatrixRepresentation k m (I × J) where
  app R := GrpCat.ofHom
    (show Matrix.GeneralLinearGroup m R →* Matrix.GeneralLinearGroup (I × J) R from
      { toFun := fun g => (representationAt ρ R g).kronecker (representationAt σ R g)
        map_one' := by
          apply Units.ext
          change (representationAt ρ R 1).val ⊗ₖ (representationAt σ R 1).val = 1
          rw [map_one, map_one, Units.val_one, Units.val_one, Matrix.one_kronecker_one]
        map_mul' := by
          intro g h
          apply Units.ext
          change (representationAt ρ R (g * h)).val ⊗ₖ
            (representationAt σ R (g * h)).val = _
          simp only [map_mul, Units.val_mul, Matrix.mul_kronecker_mul]
          rfl })
  naturality R S f := GrpCat.ext fun (g : Matrix.GeneralLinearGroup m R) => by
    apply Units.ext
    let x := Matrix.GeneralLinearGroup.map f.hom.toRingHom g
    change (representationAt ρ S x).val ⊗ₖ (representationAt σ S x).val =
      ((representationAt ρ R g).val ⊗ₖ (representationAt σ R g).val).map f.hom
    rw [← representationAt_natural f ρ, ← representationAt_natural f σ]
    apply Matrix.ext
    rintro ⟨i, j⟩ ⟨a, b⟩
    exact (f.hom.map_mul _ _).symm

private theorem tensorRepresentation_val (ρ : MatrixRepresentation k m I)
    (σ : MatrixRepresentation k m J) (R : TestAlgebra k) (g : Matrix.GeneralLinearGroup m R) :
    (representationAt (tensorRepresentation ρ σ) R g).val =
      (representationAt ρ R g).val ⊗ₖ (representationAt σ R g).val := rfl

private theorem tensorRepresentation_polynomial {ρ : MatrixRepresentation k m I}
    {σ : MatrixRepresentation k m J} (hρ : IsPolynomial ρ) (hσ : IsPolynomial σ) :
    IsPolynomial (tensorRepresentation ρ σ) := by
  obtain ⟨P, hP⟩ := hρ
  obtain ⟨Q, hQ⟩ := hσ
  refine ⟨P ⊗ₖ Q, fun R g => ?_⟩
  rw [tensorRepresentation_val, hP R g, hQ R g]
  apply Matrix.ext
  rintro ⟨i, j⟩ ⟨a, b⟩
  exact ((evaluateMatrix g.val).map_mul (P i a) (Q j b)).symm

omit [DecidableEq I] [DecidableEq J] in
private theorem kronecker_mulVec_product {R : Type u} [CommRing R]
    (A : Matrix I I R) (B : Matrix J J R) (v : I → R) (w : J → R) :
    (A ⊗ₖ B).mulVec (fun p => v p.1 * w p.2) =
      fun p => (A.mulVec v) p.1 * (B.mulVec w) p.2 := by
  funext p
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

omit [DecidableEq m] in
private theorem weightValue_add {R : Type u} [CommRing R]
    (lam mu : m → ℤ) (t : m → Rˣ) :
    weightValue (lam + mu) t = weightValue lam t * weightValue mu t := by
  simp only [weightValue, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
private theorem extend_product (R : TestAlgebra k) (v : I → k) (w : J → k) :
    RootWeightAction.extendVector R (fun p : I × J => v p.1 * w p.2) =
      fun p => RootWeightAction.extendVector R v p.1 * RootWeightAction.extendVector R w p.2 := by
  funext p
  exact map_mul (algebraMap k R) (v p.1) (w p.2)

private theorem tensorRepresentation_primitive {n : ℕ}
    {ρ : MatrixRepresentation k (Index.{u} n) I} {σ : MatrixRepresentation k (Index.{u} n) J}
    {lam mu : Index.{u} n → ℤ} {v : I → k} {w : J → k}
    (hv : IsPrimitive ρ lam v) (hw : IsPrimitive σ mu w) :
    IsPrimitive (tensorRepresentation ρ σ) (lam + mu) (fun p => v p.1 * w p.2) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra! h
      exact hv.1 (funext h)
    obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
      by_contra! h
      exact hw.1 (funext h)
    intro hz
    exact mul_ne_zero hi hj (congrFun hz (i, j))
  · intro R t
    rw [tensorRepresentation_val, extend_product, kronecker_mulVec_product,
      hv.2.1 R t, hw.2.1 R t, weightValue_add]
    funext p
    change ((weightValue lam t).val * RootWeightAction.extendVector R v p.1) *
        ((weightValue mu t).val * RootWeightAction.extendVector R w p.2) =
      (weightValue lam t).val * (weightValue mu t).val *
        (RootWeightAction.extendVector R v p.1 * RootWeightAction.extendVector R w p.2)
    ac_rfl
  · intro R g hg hd
    rw [tensorRepresentation_val, extend_product, kronecker_mulVec_product,
      hv.2.2 R g hg hd, hw.2.2 R g hg hd]

private theorem upper_weight_indices {n : ℕ} {lam : Index.{u} n → ℤ}
    (hmono : Antitone lam) (b : ℤ) :
    ∃ q : ℕ, q ≤ n ∧ ∀ i : Index.{u} n, (b < lam i ↔ i.down.val < q) := by
  let low := Finset.univ.filter (fun i : Index.{u} n => lam i ≤ b)
  have hlow (i : Index.{u} n) : i ∈ low ↔ lam i ≤ b := by simp [low]
  by_cases h : low.Nonempty
  · let j := low.min' h
    have hj := (hlow j).mp (Finset.min'_mem low h)
    refine ⟨j.down.val, j.down.isLt.le, fun i => ?_⟩
    constructor
    · intro hi
      by_contra! hn
      exact not_lt_of_ge ((hmono (show j ≤ i from hn)).trans hj) hi
    · intro hi
      by_contra! hn
      have hji := Finset.min'_le low i ((hlow i).mpr hn)
      exact not_lt_of_ge (show j.down.val ≤ i.down.val from hji) hi
  · refine ⟨n, le_rfl, fun i => ⟨fun _ => i.down.isLt, fun _ => ?_⟩⟩
    by_contra! hi
    exact h ⟨i, (hlow i).mpr hi⟩

private theorem primitive_of_bounded_weight (k : Type u) [Field k] (n : ℕ) (b : ℕ) :
    ∀ (lam : Index.{u} n → ℤ), Antitone lam → (∀ i, 0 ≤ lam i ∧ lam i ≤ (b : ℤ)) →
      ∃ (J : Type u) (hJ : Fintype J) (dJ : DecidableEq J),
        letI := hJ
        letI := dJ
        ∃ (σ : MatrixRepresentation k (Index.{u} n) J) (w : J → k),
          IsPolynomial σ ∧ IsPrimitive σ lam w := by
  induction b with
  | zero =>
      intro lam hmono hbound
      have h0 : lam = fun _ => 0 := by
        funext i
        have h := hbound i
        omega
      subst lam
      obtain ⟨σ, hσ, hw⟩ := exteriorPrimitive k n 0 (Nat.zero_le n)
      let j := Set.powersetCard.ofFinEmbEquiv (initialEmbedding.{u} (Nat.zero_le n))
      refine ⟨_, inferInstance, inferInstance, σ, Pi.single j 1, ⟨_, hσ⟩, ?_⟩
      simpa only [Nat.not_lt_zero, ite_false] using hw
  | succ b ih =>
      intro lam hmono hbound
      let mu : Index.{u} n → ℤ := fun i => min (lam i) (b : ℤ)
      have hmu : Antitone mu := fun _ _ h => min_le_min_right _ (hmono h)
      have hb (i : Index.{u} n) : 0 ≤ mu i ∧ mu i ≤ (b : ℤ) :=
        ⟨le_min (hbound i).1 (Int.natCast_nonneg b), min_le_right _ _⟩
      obtain ⟨J, hJ, dJ, σ, w, hσ, hw⟩ := ih mu hmu hb
      let _ := hJ
      let _ := dJ
      obtain ⟨q, hq, hcut⟩ := upper_weight_indices hmono (b : ℤ)
      obtain ⟨τ, hτ, hv⟩ := exteriorPrimitive k n q hq
      let nu : Index.{u} n → ℤ := fun i => if i.down.val < q then 1 else 0
      have hadd : mu + nu = lam := by
        funext i
        change min (lam i) (b : ℤ) + (if i.down.val < q then 1 else 0) = lam i
        have hi := (hbound i).2
        by_cases hc : i.down.val < q
        · have hl := (hcut i).mpr hc
          rw [ite_eq_left hc, min_eq_right hl.le]
          omega
        · have hl : lam i ≤ (b : ℤ) := not_lt.mp (fun h => hc ((hcut i).mp h))
          rw [ite_eq_right hc, min_eq_left hl, add_zero]
      let j := Set.powersetCard.ofFinEmbEquiv (initialEmbedding.{u} hq)
      let y : J × Set.powersetCard (Index.{u} n) q → k :=
        fun p => w p.1 * Pi.single (M := fun _ => k) j 1 p.2
      refine ⟨_, inferInstance, inferInstance, tensorRepresentation σ τ, y,
        tensorRepresentation_polynomial hσ ⟨_, hτ⟩, ?_⟩
      rw [← hadd]
      exact tensorRepresentation_primitive hw hv

/-- Tensor products of initial wedges realize every nonnegative dominant weight. -/
theorem polynomialPrimitiveExistence : PolynomialPrimitiveExistence.{u} := by
  intro k _ n lam hmono hlast
  let b := Finset.univ.sup (fun i => (lam i).toNat)
  apply primitive_of_bounded_weight k (n + 1) b lam hmono
  intro i
  have hi := hlast.trans (hmono (show i ≤ ⟨Fin.last n⟩ from Fin.le_last _))
  have hb : (lam i).toNat ≤ b := Finset.le_sup (f := fun j : Index.{u} (n + 1) => (lam j).toNat) (Finset.mem_univ i)
  exact ⟨hi, by omega⟩

end TensorProduct


/-- The necessary condition in the simple-module criterion holds for any primitive vector. -/
theorem simpleCriterionNecessary : SimpleCriterionNecessary.{u} := by
  intro k I _ _ _ n ρ lam v hp hv
  exact nonnegativeWeights k (Unipotent.Index.{u} (n + 1)) I ρ hp lam v hv.1 hv.2.1 ⟨Fin.last n⟩

section Equivariance

variable {J : Type u} [Fintype J] [DecidableEq J]

omit [DecidableEq I] [Fintype J] [DecidableEq J] in
private theorem contract_mulVec (R : TestAlgebra k) (ℓ : R →ₗ[k] k)
    (A : Matrix J I k) (v : I → R) (j : J) :
    ℓ (((A.map (algebraMap k R)).mulVec v) j) = (A.mulVec (fun i => ℓ (v i))) j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

omit [DecidableEq I] [Fintype J] [DecidableEq J] in
private theorem extend_mulVec (R : TestAlgebra k) (A : Matrix J I k) (v : I → k) :
    RootWeightAction.extendVector R (A.mulVec v) =
      (A.map (algebraMap k R)).mulVec (RootWeightAction.extendVector R v) := by
  funext j
  simp [RootWeightAction.extendVector, Matrix.mulVec, dotProduct, map_sum, map_mul]

/-- Equivariance of a linear map yields a matrix intertwiner over every test algebra. -/
theorem intertwines_of_equivariant {n : ℕ} {G : AffineAlgebraicGroup k}
    (e : Specs.GeneralLinearStructure.MatrixPoints G n)
    {ρ : MatrixRepresentation k (Unipotent.Index.{u} n) I}
    {σ : MatrixRepresentation k (Unipotent.Index.{u} n) J}
    {F : (I → k) →ₗ[k] (J → k)}
    (hF : Specs.PrimitiveLine.IsEquivariant (e.hom ≫ ρ) (e.hom ≫ σ) F)
    (R : TestAlgebra k) (g : Matrix.GeneralLinearGroup (Unipotent.Index.{u} n) R) :
    F.toMatrix'.map (algebraMap k R) * (representationAt ρ R g).val =
      (representationAt σ R g).val * F.toMatrix'.map (algebraMap k R) := by
  let g₀ : Specs.AdjointRepresentation.GroupPoints G.val R := e.inv.app R g
  have hg₀ : (e.hom.app R g₀ : Matrix.GeneralLinearGroup (Unipotent.Index.{u} n) R) = g :=
    (e.app R).groupIsoToMulEquiv.apply_symm_apply g
  let A := (representationAt ρ R g).val
  let B := (representationAt σ R g).val
  let C := F.toMatrix'.map (algebraMap k R)
  have he (v : I → k) (j : J) (ℓ : R →ₗ[k] k) :
      ℓ ((C.mulVec (A.mulVec (RootWeightAction.extendVector R v))) j) =
        ℓ ((B.mulVec (C.mulVec (RootWeightAction.extendVector R v))) j) := by
    rw [contract_mulVec, LinearMap.toMatrix'_mulVec, ← extend_mulVec,
      LinearMap.toMatrix'_mulVec]
    have hr := congrFun (hF R g₀ ℓ v) j
    have hρ : (representationAt ρ R (e.hom.app R g₀)).val = A := by rw [hg₀]
    have hσ : (representationAt σ R (e.hom.app R g₀)).val = B := by rw [hg₀]
    change F (fun i => ℓ ((representationAt ρ R (e.hom.app R g₀)).val.mulVec
        (RootWeightAction.extendVector R v) i)) j =
      ℓ ((representationAt σ R (e.hom.app R g₀)).val.mulVec
        (RootWeightAction.extendVector R (F v)) j) at hr
    simpa only [hρ, hσ] using hr
  apply Matrix.ext
  intro j i
  by_contra hn
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero k (sub_ne_zero.mpr hn)
  apply hℓ
  have h := he (Pi.single i 1) j ℓ
  rw [extend_single, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
  exact (map_sub ℓ _ _).trans (sub_eq_zero.mpr h)

/-- An equivariant embedding into a polynomial representation preserves polynomiality. -/
theorem polynomial_of_equivariant_injective {n : ℕ} {G : AffineAlgebraicGroup k}
    (e : Specs.GeneralLinearStructure.MatrixPoints G n)
    {ρ : MatrixRepresentation k (Unipotent.Index.{u} n) I}
    {σ : MatrixRepresentation k (Unipotent.Index.{u} n) J}
    {F : (J → k) →ₗ[k] (I → k)}
    (hF : Specs.PrimitiveLine.IsEquivariant (e.hom ≫ σ) (e.hom ≫ ρ) F)
    (hinj : Function.Injective F) (hρ : IsPolynomial ρ) : IsPolynomial σ := by
  obtain ⟨P, hP⟩ := F.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  have hm : P.toMatrix' * F.toMatrix' = 1 := by
    rw [← LinearMap.toMatrix'_comp, hP, LinearMap.toMatrix'_id]
  exact polynomialSubquotients k (Unipotent.Index.{u} n) I J ρ σ P.toMatrix' F.toMatrix'
    hm (.inl fun R g => (intertwines_of_equivariant e hF R g).symm) hρ

/-- An equivariant quotient of a polynomial representation is polynomial. -/
theorem polynomial_of_equivariant_surjective {n : ℕ} {G : AffineAlgebraicGroup k}
    (e : Specs.GeneralLinearStructure.MatrixPoints G n)
    {ρ : MatrixRepresentation k (Unipotent.Index.{u} n) I}
    {σ : MatrixRepresentation k (Unipotent.Index.{u} n) J}
    {F : (I → k) →ₗ[k] (J → k)}
    (hF : Specs.PrimitiveLine.IsEquivariant (e.hom ≫ ρ) (e.hom ≫ σ) F)
    (hsurj : Function.Surjective F) (hρ : IsPolynomial ρ) : IsPolynomial σ := by
  obtain ⟨S, hS⟩ := F.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  have hm : F.toMatrix' * S.toMatrix' = 1 := by
    rw [← LinearMap.toMatrix'_comp, hS, LinearMap.toMatrix'_id]
  exact polynomialSubquotients k (Unipotent.Index.{u} n) I J ρ σ F.toMatrix' S.toMatrix'
    hm (.inr (intertwines_of_equivariant e hF)) hρ

end Equivariance

end

end LinearAlgebraicGroups.Representation.PolynomialGL


open AlgebraicGeometry CategoryTheory Opposite WithConv
open scoped BigOperators CategoryTheory.MonObj


namespace LinearAlgebraicGroups.Representation.PolynomialGL
open LinearAlgebraicGroups.Specs
open Specs.PolynomialGL
open Specs.StandardGroups
open Specs.Unipotent (Index)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (characterValue pairing adjointWeightVectors absoluteRoots)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.GeneralLinearStructure (MatrixPoints)
open Specs.DiagonalizableGroups (groupAlgebra)
open private charactersOfIso algebraPoint from LinearAlgebraicGroups.RootData.CharacterPairing
open private exponentsEquiv from LinearAlgebraicGroups.Affine.StandardGroups
open private integerHopfHomEquiv integerHopfHomEquiv_generator
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]

private def schemeIsoOfPoints {A B : GroupScheme k} (hA : IsAffine A.X.left)
    (hB : IsAffine B.X.left)
    (e : (groupPointsFunctor k).obj A ≅ (groupPointsFunctor k).obj B) : A ≅ B :=
  let F := groupPointsFunctor k
  let f := groupHomEquiv A B hA
  let g := groupHomEquiv B A hB
  { hom := f.symm e.hom
    inv := g.symm e.inv
    hom_inv_id := by
      apply (groupHomEquiv A A hA).injective
      change F.map (f.symm e.hom ≫ g.symm e.inv) = F.map (𝟙 A)
      rw [F.map_comp, show F.map (f.symm e.hom) = _ from f.apply_symm_apply _,
        show F.map (g.symm e.inv) = _ from g.apply_symm_apply _, e.hom_inv_id, F.map_id]
    inv_hom_id := by
      apply (groupHomEquiv B B hB).injective
      change F.map (g.symm e.inv ≫ f.symm e.hom) = F.map (𝟙 B)
      rw [F.map_comp, show F.map (g.symm e.inv) = _ from g.apply_symm_apply _,
        show F.map (f.symm e.hom) = _ from f.apply_symm_apply _, e.inv_hom_id, F.map_id] }

private theorem schemeIsoOfPoints_hom {A B : GroupScheme k} (hA : IsAffine A.X.left)
    (hB : IsAffine B.X.left)
    (e : (groupPointsFunctor k).obj A ≅ (groupPointsFunctor k).obj B) :
    (groupPointsFunctor k).map (schemeIsoOfPoints hA hB e).hom = e.hom :=
  (groupHomEquiv A B hA).apply_symm_apply _

private def exponentCoordinates (m : Type u) [Fintype m] [DecidableEq m] :
    convolutionPoints (groupAlgebra k (Multiplicative (m → ℤ))) ≅
      multiplicativePowerPoints k m := by
  let F := convolutionPoints (groupAlgebra k (Multiplicative (m → ℤ)))
  let e (R : TestAlgebra k) : F.obj R ≃* (multiplicativePowerPoints k m).obj R :=
    (MonoidAlgebra.liftMulEquiv k R (Multiplicative (m → ℤ))).symm.trans
      (MonoidHom.toHomUnitsMulEquiv.trans (exponentsEquiv R))
  refine NatIso.ofComponents (fun R => (e R).toGrpIso) ?_
  intro R S a
  apply GrpCat.ext
  intro f
  funext i
  apply Units.ext
  rfl

private theorem exponentCoordinates_eval {m : Type u} [Fintype m] [DecidableEq m]
    (R : TestAlgebra k) (f : MonoidAlgebra k (Multiplicative (m → ℤ)) →ₐ[k] R)
    (lam : m → ℤ) :
    f (MonoidAlgebra.single (Multiplicative.ofAdd lam) 1) =
      (weightValue lam ((exponentCoordinates m).hom.app R (toConv f))).val := by
  let φ := (MonoidAlgebra.liftMulEquiv k R (Multiplicative (m → ℤ))).symm (toConv f)
  let ψ := MonoidHom.toHomUnitsMulEquiv φ
  have h := (exponentsEquiv R).symm_apply_apply ψ
  exact congrArg (fun h : Multiplicative (m → ℤ) →* Rˣ =>
    (h (Multiplicative.ofAdd lam)).val) h.symm

private theorem characterValue_pullback {A B : GroupScheme k} (f : A ⟶ B)
    (χ : Character B) (R : TestAlgebra k) (x : GroupPoints A R) :
    characterValue (f ≫ χ) R x = characterValue χ R (x ≫ f.hom.hom) := by
  unfold characterValue
  have he : x ≫ (f ≫ χ).hom.hom = (x ≫ f.hom.hom) ≫ χ.hom.hom := by
    change x ≫ f.hom.hom ≫ χ.hom.hom = _
    rw [Category.assoc]
  rw [he]

private theorem groupLikeValue {M : Type u} [CommGroup M] (R : TestAlgebra k)
    (f : MonoidAlgebra k M →ₐ[k] R) (x : GroupLike k (groupAlgebra k M)) :
    characterValue (LinearAlgebraicGroups.CharacterDescent.groupLikeCharacterEquiv _ x)
      R (algebraPoint R f) = f x.val := by
  let h := integerHopfHomEquiv (groupAlgebra k M) x
  change ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    ((testSpec k).map (CommAlgCat.ofHom f).op ≫
      (testSpec k).map (CommAlgCat.ofHom h.hom.toAlgHom).op)).unop.hom
        (MonoidAlgebra.single Specs.DiagonalizableGroups.integerGenerator 1) = _
  rw [← Functor.map_comp, Functor.FullyFaithful.preimage_map]
  change f (h.hom (MonoidAlgebra.single Specs.DiagonalizableGroups.integerGenerator 1)) = _
  exact congrArg f (integerHopfHomEquiv_generator (groupAlgebra k M) x)

/-- The coordinate characters freely generate the character lattice of the diagonal torus. -/
theorem characterCoordinates : CharacterCoordinates.{u} := by
  intro k _ n G T t
  let m := Index.{u} n
  let M := Multiplicative (m → ℤ)
  let A := groupAlgebra k M
  let h : IsAffine T.group.X.left := by
    letI : IsAffine G.val.X.left := G.property.1
    letI := T.isClosedImmersion
    exact isAffine_of_isAffineHom T.inclusion.hom.hom.left
  let s := hopfSpecPointIso A
  let e := s.symm ≪≫ exponentCoordinates (k := k) m ≪≫ t.symm
  let hA : IsAffine (specGroup A).X.left := by
    change IsAffine (Spec (CommRingCat.of A))
    infer_instance
  let i := schemeIsoOfPoints hA h e
  let c := (LinearAlgebraicGroups.CharacterDescent.monomialCharacterEquiv (M := M) k).trans
    (LinearAlgebraicGroups.CharacterDescent.groupLikeCharacterEquiv A)
  let chars : (m → ℤ) ≃+ Additive (Character T.group) :=
    (c.trans (charactersOfIso i)).toAdditive
  refine ⟨chars, ?_⟩
  intro lam R x
  let f : MonoidAlgebra k M →ₐ[k] R :=
    (((groupPointsFunctor k).map i.inv ≫ s.inv).app R x).ofConv
  have hxi : (algebraPoint R f : GroupPoints (specGroup A) R) = x ≫ i.inv.hom.hom := by
    change s.hom.app R (s.inv.app R (((groupPointsFunctor k).map i.inv).app R x)) =
      ((groupPointsFunctor k).map i.inv).app R x
    exact (s.app R).groupIsoToMulEquiv.apply_symm_apply _
  have hix : ((groupPointsFunctor k).map i.hom).app R (algebraPoint R f) = x := by
    change (algebraPoint R f : GroupPoints (specGroup A) R) ≫ i.hom.hom.hom = x
    rw [hxi, Category.assoc, show i.inv.hom.hom ≫ i.hom.hom.hom = 𝟙 _ from
      (Grp.forget _).congr_map i.inv_hom_id, Category.comp_id]
  have hcoord : (exponentCoordinates m).hom.app R (toConv f) = t.hom.app R x := by
    rw [schemeIsoOfPoints_hom] at hix
    change t.inv.app R ((exponentCoordinates m).hom.app R (s.inv.app R (s.hom.app R (toConv f)))) = x at hix
    rw [show s.inv.app R (s.hom.app R (toConv f)) = toConv f from
      (s.app R).groupIsoToMulEquiv.symm_apply_apply _] at hix
    exact (t.app R).groupIsoToMulEquiv.symm_apply_eq.mp hix
  change characterValue (i.inv ≫ LinearAlgebraicGroups.CharacterDescent.groupLikeCharacterEquiv A
    (LinearAlgebraicGroups.CharacterDescent.monomialCharacterEquiv k (Multiplicative.ofAdd lam)))
    R x = _
  rw [characterValue_pullback, ← hxi, groupLikeValue, ← hcoord]
  exact exponentCoordinates_eval R f lam

end
end LinearAlgebraicGroups.Representation.PolynomialGL


open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped BigOperators CategoryTheory.MonObj


namespace LinearAlgebraicGroups.Representation.PolynomialGL
open LinearAlgebraicGroups.Specs
open Specs.PolynomialGL
open Specs.StandardGroups
open Specs.Unipotent (Index)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue pairing adjointWeightVectors absoluteRoots)
open Specs.AdjointRepresentation (GroupPoints dualMap constants scale)
open Specs.GeneralLinearStructure (MatrixPoints)
open LinearAlgebraicGroups.CocharacterDynamics (lieImage cocharacterPoint)

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {n : ℕ} {G : AffineAlgebraicGroup k}

private theorem matrixPoint_natural (e : MatrixPoints G n) {R S : TestAlgebra k}
    (f : R ⟶ S) (g : GroupPoints G.val R) :
    e.hom.app S (mapPoints f g) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom (e.hom.app R g) :=
  ConcreteCategory.congr_hom (e.hom.naturality f) g

private abbrev tangentMatrix (e : MatrixPoints G n) (v : Lie k G.val) :
    Matrix (Index.{u} n) (Index.{u} n) (DualNumber k) :=
  (e.hom.app (CommAlgCat.of k (DualNumber k)) v.toMul.val).val

private theorem tangentMatrix_fst (e : MatrixPoints G n) (v : Lie k G.val) (a b : Index.{u} n) :
    (tangentMatrix e v a b).fst = (1 : Matrix (Index.{u} n) (Index.{u} n) k) a b := by
  have hv : mapPoints (dualReduction k) v.toMul.val = 1 := v.toMul.property
  have hm := matrixPoint_natural e (dualReduction k) v.toMul.val
  rw [hv] at hm
  have h1 : e.hom.app (CommAlgCat.of k k) (1 : GroupPoints G.val (CommAlgCat.of k k)) = 1 :=
    (e.hom.app _).hom.map_one
  exact congrArg (fun g : Matrix.GeneralLinearGroup (Index.{u} n) k => g.val a b)
    (hm.symm.trans h1)

private theorem tangent_eq_zero (e : MatrixPoints G n) (v : Lie k G.val)
    (h : ∀ a b, (tangentMatrix e v a b).snd = 0) : v = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply (e.app (CommAlgCat.of k (DualNumber k))).groupIsoToMulEquiv.injective
  change e.hom.app _ v.toMul.val = e.hom.app _ (1 : GroupPoints G.val _)
  refine Eq.trans ?_ ((e.hom.app _).hom.map_one.symm)
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  change tangentMatrix e v a b = (1 : Matrix (Index.{u} n) (Index.{u} n) (DualNumber k)) a b
  apply TrivSqZeroExt.ext
  · rw [tangentMatrix_fst]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  · rw [h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

/-- The diagonal conjugation equations on dual-number points in matrix entries. -/
private theorem tangent_weight_iff (e : MatrixPoints G n) {T : ClosedSubgroup G.val}
    {t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n)}
    (ht : DiagonalCoordinates e T t) (χ : Character T.group) (v : Lie k G.val) :
    v ∈ adjointWeightVectors T χ ↔
    ∀ (R : TestAlgebra k) (x : GroupPoints T.group R) (a b : Index.{u} n),
      let d : Index.{u} n → Rˣ := t.hom.app R x
      let s := algebraMap k R (tangentMatrix e v a b).snd
      (d a).val * s = characterValue χ R x * s * (d b).val := by
  change (∀ (R : TestAlgebra k) (x : GroupPoints T.group R), _) ↔ _
  apply forall_congr'
  intro R
  apply forall_congr'
  intro x
  let S := CommAlgCat.of k (DualNumber R)
  let d : Index.{u} n → Rˣ := t.hom.app R x
  let A := CommAlgCat.of k k
  let f : A ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  have hsnd (z : DualNumber k) : ((dualMap f).hom z).snd = algebraMap k R z.snd := rfl
  let p : GroupPoints G.val S := mapPoints (dualMap f) v.toMul.val
  let g : GroupPoints G.val S := mapPoints (constants R) (x ≫ T.inclusion.hom.hom)
  let c := characterValue χ R x
  let q : GroupPoints G.val S := mapPoints (scale R c) p
  change g * p * g⁻¹ = q ↔ _
  refine (mul_inv_eq_iff_eq_mul : g * p * g⁻¹ = q ↔ g * p = q * g).trans ?_
  let M := (e.hom.app S).hom
  have hM : Function.Injective M := (e.app S).groupIsoToMulEquiv.injective
  refine hM.eq_iff.symm.trans ?_
  simp only [map_mul]
  have hg : (M g).val = Matrix.diagonal (fun a => TrivSqZeroExt.inl (d a).val) := by
    change (e.hom.app S (mapPoints (constants R) (x ≫ T.inclusion.hom.hom))).val = _
    rw [matrixPoint_natural, ht R x]
    change (diagonalPoint d).val.map (constants R).hom = _
    rw [diagonalPoint_val, Matrix.diagonal_map (map_zero _)]
    rfl
  have hp : (M p).val = (tangentMatrix e v).map (dualMap f).hom := by
    change (e.hom.app S (mapPoints (dualMap f) v.toMul.val)).val = _
    rw [matrixPoint_natural]
    rfl
  have hscale : (M q).val = (M p).val.map (scale R c).hom := by
    change (e.hom.app S (mapPoints (scale R c) p)).val = _
    rw [matrixPoint_natural]
    rfl
  refine Units.val_injective.eq_iff.symm.trans ?_
  change (M g).val * (M p).val = (M q).val * (M g).val ↔ _
  rw [hscale, hg, hp]
  constructor
  · intro h a b
    have hab := congrArg (fun N : Matrix (Index.{u} n) (Index.{u} n) (DualNumber R) => N a b) h
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hab
    have hs := congrArg TrivSqZeroExt.snd hab
    simp only [Matrix.map_apply, DualNumber.snd_mul, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl, zero_mul, mul_zero, zero_add, add_zero] at hs
    change (d a).val * ((dualMap f).hom (tangentMatrix e v a b)).snd =
      (c * ((dualMap f).hom (tangentMatrix e v a b)).snd) * (d b).val at hs
    rwa [hsnd] at hs
  · intro h
    apply Matrix.ext
    intro a b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    apply TrivSqZeroExt.ext
    · change (d a).val * algebraMap k R (tangentMatrix e v a b).fst =
        algebraMap k R (tangentMatrix e v a b).fst * (d b).val
      rw [tangentMatrix_fst]
      by_cases hab : a = b
      · subst b
        simp
      · simp [Matrix.one_apply_ne hab]
    · simp only [Matrix.map_apply, DualNumber.snd_mul, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.snd_inl, zero_mul, mul_zero, zero_add, add_zero]
      change (d a).val * ((dualMap f).hom (tangentMatrix e v a b)).snd =
        (c * ((dualMap f).hom (tangentMatrix e v a b)).snd) * (d b).val
      rw [hsnd]
      exact h a b

private theorem tangent_exists (e : MatrixPoints G n) {i j : Index.{u} n} (hij : i ≠ j) :
    ∃ v : Lie k G.val, ∀ a b, (tangentMatrix e v a b).snd =
      (Matrix.single i j 1 : Matrix (Index.{u} n) (Index.{u} n) k) a b := by
  let S := CommAlgCat.of k (DualNumber k)
  let A := CommAlgCat.of k k
  let h := Matrix.GeneralLinearGroup.transvection i j hij (DualNumber.eps : DualNumber k)
  let g : GroupPoints G.val S := e.inv.app S h
  have hg : e.hom.app S g = h := (e.app S).groupIsoToMulEquiv.apply_symm_apply _
  have hr : mapPoints (dualReduction k) g = 1 := by
    apply (e.app A).groupIsoToMulEquiv.injective
    change e.hom.app A (mapPoints (dualReduction k) g) = e.hom.app A
      (1 : GroupPoints G.val A)
    rw [matrixPoint_natural, hg, (e.hom.app A).hom.map_one]
    apply Matrix.GeneralLinearGroup.ext
    intro a b
    change (h.val a b).fst = _
    change ((1 + Matrix.single i j (DualNumber.eps : DualNumber k)) a b).fst =
      (1 : Matrix (Index.{u} n) (Index.{u} n) k) a b
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, TrivSqZeroExt.fst_add]
    split_ifs <;> simp only [TrivSqZeroExt.fst_zero, TrivSqZeroExt.fst_one,
      TrivSqZeroExt.fst_inr, DualNumber.eps, add_zero]
  let v : Lie k G.val := Additive.ofMul ⟨g, hr⟩
  refine ⟨v, fun a b => ?_⟩
  change ((e.hom.app S g).val a b).snd = _
  rw [hg]
  change ((1 + Matrix.single i j (DualNumber.eps : DualNumber k)) a b).snd = _
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, TrivSqZeroExt.snd_add]
  split_ifs <;> simp only [TrivSqZeroExt.snd_zero, TrivSqZeroExt.snd_one,
    TrivSqZeroExt.snd_inr, DualNumber.eps, zero_add]

private theorem subgroupPoint_injective (B : ClosedSubgroup G.val) (R : TestAlgebra k) :
    Function.Injective (fun x : GroupPoints B.group R => x ≫ B.inclusion.hom.hom) := by
  letI := B.isClosedImmersion
  letI : Mono B.inclusion.hom.hom := Over.mono_of_mono_left _
  intro x y h
  exact (cancel_mono B.inclusion.hom.hom).mp h

private theorem lieImage_iff_upper (e : MatrixPoints G n) {B : ClosedSubgroup G.val}
    (hB : UpperTriangularCoordinates e B) (v : Lie k G.val) :
    v ∈ lieImage B ↔ (tangentMatrix e v).IsUpperTriangular := by
  let R := CommAlgCat.of k (DualNumber k)
  change (∃ x : Lie k B.group, mapPointKernel B.inclusion x = v) ↔ _
  rw [← hB R v.toMul.val]
  change (∃ x : Lie k B.group, mapPointKernel B.inclusion x = v) ↔
    ∃ x : GroupPoints B.group R, x ≫ B.inclusion.hom.hom = v.toMul.val
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.toMul.val, rfl⟩
  · rintro ⟨x, hx⟩
    let F := groupPointsFunctor k
    let A := CommAlgCat.of k k
    have hred : mapPoints (dualReduction k) x = 1 := by
      apply subgroupPoint_injective B A
      have h := ConcreteCategory.congr_hom ((F.map B.inclusion).naturality (dualReduction k)) x
      change mapPoints (dualReduction k) (x ≫ B.inclusion.hom.hom) =
        mapPoints (dualReduction k) x ≫ B.inclusion.hom.hom at h
      rw [hx] at h
      exact h.symm.trans (v.toMul.property.trans (((F.map B.inclusion).app A).hom.map_one.symm))
    refine ⟨Additive.ofMul ⟨x, hred⟩, ?_⟩
    exact Subtype.ext hx

private theorem weightValue_basis {m R : Type u} [Fintype m] [DecidableEq m] [CommRing R]
    (a : m) (t : m → Rˣ) : weightValue (Pi.single a 1) t = t a := by
  unfold weightValue
  rw [Finset.prod_eq_single a]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

private theorem weightValue_root {R : Type u} [CommRing R]
    (t : Index.{u} n → Rˣ) (i j : Index.{u} n) :
    weightValue (rootExponent i j) t = t i * (t j)⁻¹ := by
  have hsub (f g : Index.{u} n → ℤ) :
      weightValue (f - g) t = weightValue f t * (weightValue g t)⁻¹ := by
    simp only [weightValue, Pi.sub_apply, zpow_sub,
      Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rw [rootExponent, hsub, weightValue_basis, weightValue_basis]

private theorem rootExponent_one {i j a : Index.{u} n} (hij : i ≠ j) :
    rootExponent i j a = 1 ↔ a = i := by
  by_cases hi : a = i
  · subst a
    simp [rootExponent, Pi.single_eq_of_ne hij]
  · by_cases hj : a = j
    · subst a
      simp [rootExponent, hij.symm]
    · simp [rootExponent, Pi.single_eq_of_ne hj, hi]

private theorem rootExponent_neg_one {i j a : Index.{u} n} (hij : i ≠ j) :
    rootExponent i j a = -1 ↔ a = j := by
  have h : rootExponent j i a = -rootExponent i j a := by
    exact (neg_sub _ _).symm
  have he := rootExponent_one (a := a) hij.symm
  rw [h] at he
  simpa only [neg_eq_iff_eq_neg] using he

private theorem rootExponent_injective {i j a b : Index.{u} n} (hij : i ≠ j)
    (hab : a ≠ b) (h : rootExponent i j = rootExponent a b) : i = a ∧ j = b := by
  have hi := (rootExponent_one (a := i) hij).mpr rfl
  have hj := (rootExponent_neg_one (a := j) hij).mpr rfl
  rw [h] at hi hj
  exact ⟨(rootExponent_one hab).mp hi, (rootExponent_neg_one hab).mp hj⟩

private abbrev characterAt {T : ClosedSubgroup G.val}
    (c : (Index.{u} n → ℤ) ≃+ Additive (Character T.group)) (lam : Index.{u} n → ℤ) :
    Character T.group := Additive.toMul (c lam)

private theorem coordinates_determine_weight {T : ClosedSubgroup G.val}
    {t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n)}
    {c : (Index.{u} n → ℤ) ≃+ Additive (Character T.group)}
    (hc : CharacterEvaluation t c) (χ : Character T.group) (lam : Index.{u} n → ℤ)
    (h : ∀ (R : TestAlgebra k) (x : GroupPoints T.group R),
      characterValue χ R x = (weightValue lam (t.hom.app R x)).val) :
    χ = characterAt c lam := by
  obtain ⟨mu, hmu⟩ := c.surjective (Additive.ofMul χ)
  have he : χ = characterAt c mu := (congrArg Additive.toMul hmu).symm
  rw [he] at h ⊢
  congr 1
  apply weight_exponents_eq (k := k)
  intro R d
  obtain ⟨x, rfl⟩ := (t.app R).groupIsoToMulEquiv.surjective d
  exact (hc mu R x).symm.trans (h R x)

private theorem nonzero_tangent_entry_weight (e : MatrixPoints G n) {T : ClosedSubgroup G.val}
    {t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n)}
    (ht : DiagonalCoordinates e T t)
    {c : (Index.{u} n → ℤ) ≃+ Additive (Character T.group)}
    (hc : CharacterEvaluation t c) {χ : Character T.group} {v : Lie k G.val}
    (hv : v ∈ adjointWeightVectors T χ) {i j : Index.{u} n}
    (hij : (tangentMatrix e v i j).snd ≠ 0) :
    χ = characterAt c (rootExponent i j) := by
  apply coordinates_determine_weight hc
  intro R x
  let d : Index.{u} n → Rˣ := t.hom.app R x
  let s := algebraMap k R (tangentMatrix e v i j).snd
  have hs : IsUnit s := (isUnit_iff_ne_zero.mpr hij).map (algebraMap k R)
  have h := (tangent_weight_iff e ht χ v).mp hv R x i j
  change (d i).val * s = characterValue χ R x * s * (d j).val at h
  have h' : (d i).val = characterValue χ R x * (d j).val :=
    hs.mul_right_cancel (h.trans (mul_right_comm _ _ _))
  rw [weightValue_root]
  symm
  apply (d j).isUnit.mul_right_cancel
  rw [← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one, h']

private theorem standard_root_witness (e : MatrixPoints G n) {T : ClosedSubgroup G.val}
    {t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n)}
    (ht : DiagonalCoordinates e T t)
    {c : (Index.{u} n → ℤ) ≃+ Additive (Character T.group)}
    (hc : CharacterEvaluation t c) {i j : Index.{u} n} (hij : i ≠ j) :
    ∃ v ∈ adjointWeightVectors T (characterAt c (rootExponent i j)),
      (tangentMatrix e v i j).snd = 1 := by
  obtain ⟨v, hv⟩ := tangent_exists e hij
  refine ⟨v, (tangent_weight_iff e ht _ v).mpr ?_, by rw [hv, Matrix.single_apply_same]⟩
  intro R x a b
  let d : Index.{u} n → Rˣ := t.hom.app R x
  dsimp only
  rw [hv, hc, weightValue_root]
  by_cases hab : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := hab
    simp only [Matrix.single_apply_same, map_one, mul_one, ← Units.val_mul,
      mul_assoc, inv_mul_cancel, mul_one]
  · simp [hab]

private theorem absoluteRoot_standard (e : MatrixPoints G n) {T : ClosedSubgroup G.val}
    {t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n)}
    (ht : DiagonalCoordinates e T t)
    {c : (Index.{u} n → ℤ) ≃+ Additive (Character T.group)}
    (hc : CharacterEvaluation t c) (χ : Character T.group) :
    χ ∈ absoluteRoots T ↔ ∃ i j : Index.{u} n, i ≠ j ∧ χ = characterAt c (rootExponent i j) := by
  constructor
  · rintro ⟨hχ, v, hv, hv0⟩
    have h : ∃ i j, (tangentMatrix e v i j).snd ≠ 0 := by
      by_contra! he
      exact hv0 (tangent_eq_zero e v he)
    obtain ⟨i, j, h⟩ := h
    have he := nonzero_tangent_entry_weight e ht hc hv h
    refine ⟨i, j, ?_, he⟩
    rintro rfl
    apply hχ
    rw [he]
    change Additive.toMul (c (Pi.single i 1 - Pi.single i 1)) = _
    rw [sub_self, map_zero]
    rfl
  · rintro ⟨i, j, hij, rfl⟩
    obtain ⟨v, hv, hv1⟩ := standard_root_witness e ht hc hij
    refine ⟨?_, v, hv, ?_⟩
    · intro h
      have he : rootExponent i j = 0 := c.injective (by
        rw [map_zero]
        exact congrArg Additive.ofMul h)
      have h1 := (rootExponent_one (a := i) hij).mpr rfl
      rw [he] at h1
      exact zero_ne_one h1
    · intro h
      have hzero : (tangentMatrix e (0 : Lie k G.val) i j).snd = 0 := by
        let R := CommAlgCat.of k (DualNumber k)
        change ((e.hom.app R (1 : GroupPoints G.val R)).val i j).snd = 0
        rw [(e.hom.app R).hom.map_one]
        simp [Matrix.one_apply_ne hij]
      exact zero_ne_one (hzero.symm.trans (h ▸ hv1))

private theorem standard_root_positive (e : MatrixPoints G n) {T B : ClosedSubgroup G.val}
    {t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n)}
    (ht : DiagonalCoordinates e T t) (hB : UpperTriangularCoordinates e B)
    {c : (Index.{u} n → ℤ) ≃+ Additive (Character T.group)}
    (hc : CharacterEvaluation t c) (α : AbstractPairing.Root T)
    {i j : Index.{u} n} (hij : i ≠ j) (hα : α.val = characterAt c (rootExponent i j)) :
    α ∈ BorelsAndChambers.subgroupRoots T B ↔ i < j := by
  change adjointWeightVectors T α.val ⊆ lieImage B ↔ _
  rw [hα]
  constructor
  · intro h
    obtain ⟨v, hv, hv1⟩ := standard_root_witness e ht hc hij
    by_contra hn
    have hji : j < i := lt_of_le_of_ne (le_of_not_gt hn) hij.symm
    have hzero := (lieImage_iff_upper e hB v).mp (h hv) hji
    exact one_ne_zero (hv1.symm.trans (congrArg TrivSqZeroExt.snd hzero))
  · intro h v hv
    apply (lieImage_iff_upper e hB v).mpr
    intro a b hba
    change b < a at hba
    apply TrivSqZeroExt.ext
    · rw [tangentMatrix_fst, Matrix.one_apply_ne (ne_of_gt hba)]
      rfl
    · change (tangentMatrix e v a b).snd = 0
      by_contra hn
      have he := nonzero_tangent_entry_weight e ht hc hv hn
      have he' : rootExponent i j = rootExponent a b :=
        c.injective (congrArg Additive.ofMul he)
      obtain ⟨rfl, rfl⟩ := rootExponent_injective hij (ne_of_gt hba) he'
      exact (not_lt_of_gt h) hba

private def exponentHeight : (Index.{u} n → ℤ) →+ ℤ where
  toFun x := ∑ a, -(a.down.val : ℤ) * x a
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]

private theorem exponentHeight_basis (i : Index.{u} n) :
    exponentHeight (Pi.single i 1) = -(i.down.val : ℤ) := by
  change (∑ a : Index.{u} n, -(a.down.val : ℤ) * (Pi.single i 1 : Index.{u} n → ℤ) a) = _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ h
    simp [Pi.single_eq_of_ne h]
  · simp

private theorem exponentHeight_root (i j : Index.{u} n) :
    exponentHeight (rootExponent i j) = (j.down.val : ℤ) - i.down.val := by
  rw [rootExponent, map_sub, exponentHeight_basis, exponentHeight_basis]
  omega

private theorem rootExponent_chain (i j l : Index.{u} n) :
    rootExponent i j + rootExponent j l = rootExponent i l := by
  unfold rootExponent
  abel

private theorem standard_root_simple (e : MatrixPoints G n) {T B : ClosedSubgroup G.val}
    {t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n)}
    (ht : DiagonalCoordinates e T t) (hB : UpperTriangularCoordinates e B)
    {c : (Index.{u} n → ℤ) ≃+ Additive (Character T.group)}
    (hc : CharacterEvaluation t c) (α : AbstractPairing.Root T)
    {i j : Index.{u} n} (hij : i ≠ j) (hα : α.val = characterAt c (rootExponent i j)) :
    (α ∈ BorelsAndChambers.subgroupRoots T B ∧
      ∀ β ∈ BorelsAndChambers.subgroupRoots T B,
      ∀ gamma ∈ BorelsAndChambers.subgroupRoots T B, α.val ≠ β.val * gamma.val) ↔
      i.down.val + 1 = j.down.val := by
  have hpos := standard_root_positive e ht hB hc α hij hα
  constructor
  · rintro ⟨hp, hs⟩
    have hlt : i.down.val < j.down.val := hpos.mp hp
    by_contra he
    let r : Index.{u} n := ⟨⟨i.down.val + 1, by have := j.down.isLt; omega⟩⟩
    have hir : i < r := Nat.lt_succ_self _
    have hrj : r < j := by change i.down.val + 1 < j.down.val; omega
    let β : AbstractPairing.Root T := ⟨characterAt c (rootExponent i r),
      (absoluteRoot_standard e ht hc _).mpr ⟨i, r, hir.ne, rfl⟩⟩
    let gamma : AbstractPairing.Root T := ⟨characterAt c (rootExponent r j),
      (absoluteRoot_standard e ht hc _).mpr ⟨r, j, hrj.ne, rfl⟩⟩
    refine hs β ((standard_root_positive e ht hB hc β hir.ne rfl).mpr hir)
      gamma ((standard_root_positive e ht hB hc gamma hrj.ne rfl).mpr hrj) ?_
    rw [hα, ← rootExponent_chain i r j]
    exact congrArg Additive.toMul (c.map_add _ _)
  · intro he
    have hi : i < j := by change i.down.val < j.down.val; omega
    refine ⟨hpos.mpr hi, ?_⟩
    intro β hpβ gamma hpgamma h
    obtain ⟨a, b, hab, hβ⟩ := (absoluteRoot_standard e ht hc _).mp β.property
    obtain ⟨a', b', hab', hgamma⟩ := (absoluteRoot_standard e ht hc _).mp gamma.property
    have hlt : a.down.val < b.down.val := (standard_root_positive e ht hB hc β hab hβ).mp hpβ
    have hlt' : a'.down.val < b'.down.val :=
      (standard_root_positive e ht hB hc gamma hab' hgamma).mp hpgamma
    rw [hα, hβ, hgamma] at h
    have hh : rootExponent i j = rootExponent a b + rootExponent a' b' :=
      c.injective ((congrArg Additive.ofMul h).trans (c.map_add _ _).symm)
    have hn := congrArg exponentHeight hh
    rw [map_add, exponentHeight_root, exponentHeight_root, exponentHeight_root] at hn
    omega

/-- A nonzero entry in a column of the rational normalizing matrix stays
invertible after any scalar extension and determines the conjugated coordinate. -/
private theorem conjugation_permuted_coordinate (e : MatrixPoints G n) {T : ClosedSubgroup G.val}
    {t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n)}
    (ht : DiagonalCoordinates e T t) (a : T.group ≅ T.group)
    (g : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (hg : (a.hom ≫ T.inclusion).hom.hom =
      (toUnit T.group.X ≫ g) * T.inclusion.hom.hom * (toUnit T.group.X ≫ g)⁻¹)
    (j : Index.{u} n) :
    ∃ i : Index.{u} n, ∀ (R : TestAlgebra k) (x : GroupPoints T.group R),
      (t.hom.app R (x ≫ a.inv.hom.hom) : Index.{u} n → Rˣ) j = (t.hom.app R x) i := by
  let K := CommAlgCat.of k k
  let g₀ : GroupPoints G.val K := toUnit _ ≫ g
  let M₀ : Matrix.GeneralLinearGroup (Index.{u} n) k := e.hom.app K g₀
  obtain ⟨i, hi⟩ : ∃ i : Index.{u} n, M₀.val i j ≠ 0 := by
    by_contra! h
    have h1 := congrArg (fun X : Matrix (Index.{u} n) (Index.{u} n) k => X j j) M₀.inv_val
    change (M₀.inv * M₀.val) j j = _ at h1
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    simp only [h, mul_zero, Finset.sum_const_zero] at h1
    exact zero_ne_one h1
  refine ⟨i, fun R x => ?_⟩
  let y : GroupPoints T.group R := x ≫ a.inv.hom.hom
  let gR : GroupPoints G.val R := toUnit _ ≫ g
  let f : K ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
  have hxy : y ≫ (a.hom ≫ T.inclusion).hom.hom = x ≫ T.inclusion.hom.hom := by
    change (x ≫ a.inv.hom.hom) ≫ a.hom.hom.hom ≫ T.inclusion.hom.hom = _
    rw [Category.assoc, ← Category.assoc (f := a.inv.hom.hom),
      show a.inv.hom.hom ≫ a.hom.hom.hom = 𝟙 _ from (Grp.forget _).congr_map a.inv_hom_id,
      Category.id_comp]
  rw [hg, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit] at hxy
  let xG : GroupPoints G.val R := x ≫ T.inclusion.hom.hom
  let yG : GroupPoints G.val R := y ≫ T.inclusion.hom.hom
  have heq : gR * yG * gR⁻¹ = xG := hxy
  have hm : e.hom.app R gR =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom M₀ := by
    have hnat := matrixPoint_natural e f g₀
    have he : mapPoints f g₀ = gR := by
      change (testSpec k).map f.op ≫ toUnit _ ≫ g = toUnit _ ≫ g
      rw [← Category.assoc, comp_toUnit]
    rwa [he] at hnat
  have hg' : xG * gR = gR * yG := (mul_inv_eq_iff_eq_mul.mp heq).symm
  have hmat := congrArg ((e.hom.app R).hom) hg'
  simp only [map_mul] at hmat
  change e.hom.app R (x ≫ T.inclusion.hom.hom) * e.hom.app R gR =
    e.hom.app R gR * e.hom.app R (y ≫ T.inclusion.hom.hom) at hmat
  rw [ht R x, ht R y, hm] at hmat
  have hij := congrArg (fun A : Matrix.GeneralLinearGroup (Index.{u} n) R => A.val i j) hmat
  change ((diagonalPoint (t.hom.app R x)).val * (M₀.val.map f.hom)) i j =
    ((M₀.val.map f.hom) * (diagonalPoint (t.hom.app R y)).val) i j at hij
  rw [diagonalPoint_val, diagonalPoint_val, Matrix.diagonal_mul, Matrix.mul_diagonal] at hij
  apply Units.ext
  have hunit : IsUnit ((M₀.val.map f.hom) i j) := (isUnit_iff_ne_zero.mpr hi).map f.hom
  exact (hunit.mul_right_cancel (hij.trans (mul_comm _ _))).symm

/-- The reflection permutes the coordinate characters, and its pairing with
its own root fixes the signs on the two affected coordinates. -/
private theorem attached_coroot_pairing (e : MatrixPoints G n) {T : ClosedSubgroup G.val}
    {t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n)}
    (ht : DiagonalCoordinates e T t)
    {c : (Index.{u} n → ℤ) ≃+ Additive (Character T.group)}
    (hc : CharacterEvaluation t c) [IsCommMonObj T.group.X] (D : AbstractPairing.Datum T)
    (α : AbstractPairing.Root T) {i j : Index.{u} n} (hij : i ≠ j)
    (hα : α.val = characterAt c (rootExponent i j)) (lam : Index.{u} n → ℤ) :
    D.rootDatum.toLinearMap (c lam) (D.rootDatum.coroot α) = lam i - lam j := by
  obtain ⟨C, mu, _, _, V, W, _, Q, F, P, A, x, y, _, _, _, _, r, hr⟩ := D.attached α
  let L : (Index.{u} n → ℤ) →ₗ[ℤ] ℤ :=
    (D.rootDatum.toLinearMap.flip (D.rootDatum.coroot α)).comp c.toIntLinearEquiv.toLinearMap
  have hL (v : Index.{u} n → ℤ) : L v = pairing T.group (characterAt c v) r.coroot := by
    change D.rootDatum.toLinearMap (c v) (D.rootDatum.coroot α) = _
    rw [hr]
    exact D.pairing_eq _ _
  let b (a : Index.{u} n) : Index.{u} n → ℤ := Pi.single a 1
  have hroot : L (b i) - L (b j) = 2 := by
    rw [← map_sub]
    change L (rootExponent i j) = 2
    rw [hL, ← hα]
    exact r.root_pairing
  have hperm (a : Index.{u} n) : ∃ l : Index.{u} n,
      b l = b a - L (b a) • rootExponent i j := by
    obtain ⟨l, hl⟩ := conjugation_permuted_coordinate e ht r.conjugation
      r.representative r.conjugates a
    refine ⟨l, c.injective ?_⟩
    have hcha : r.conjugation.inv ≫ characterAt c (b a) = characterAt c (b l) := by
      apply coordinates_determine_weight hc
      intro R z
      rw [characterValue_pullback, hc]
      simp only [b, weightValue_basis, hl R z]
    have hshift : characterAt c (b a - L (b a) • rootExponent i j) =
        characterAt c (b a) * α.val ^ (-L (b a)) := by
      rw [sub_eq_add_neg, ← neg_smul]
      change Additive.toMul (c (b a + (-L (b a)) • rootExponent i j)) = _
      rw [map_add, map_zsmul]
      change characterAt c (b a) * characterAt c (rootExponent i j) ^ (-L (b a)) = _
      rw [← hα]
    have href := r.reflection (characterAt c (b a))
    rw [← hL, hcha, ← hshift] at href
    exact congrArg Additive.ofMul href
  have hb (a d : Index.{u} n) : b a d = if d = a then 1 else 0 := by
    by_cases h : d = a <;> simp [b, h]
  have hi : rootExponent i j i = 1 := (rootExponent_one hij).mpr rfl
  have hj : rootExponent i j j = -1 := (rootExponent_neg_one hij).mpr rfl
  have h_i : 0 ≤ L (b i) ∧ L (b i) ≤ 1 := by
    obtain ⟨l, hl⟩ := hperm i
    have h := congrFun hl i
    change b l i = b i i - L (b i) * rootExponent i j i at h
    rw [hi, mul_one, hb l i, hb i i, ite_eq_left rfl] at h
    split_ifs at h <;> omega
  have h_j : -1 ≤ L (b j) ∧ L (b j) ≤ 0 := by
    obtain ⟨l, hl⟩ := hperm j
    have h := congrFun hl i
    change b l i = b j i - L (b j) * rootExponent i j i at h
    rw [hi, mul_one, hb l i, hb j i, ite_eq_right hij] at h
    split_ifs at h <;> omega
  have h_other (a : Index.{u} n) (hai : a ≠ i) (haj : a ≠ j) : L (b a) = 0 := by
    obtain ⟨l, hl⟩ := hperm a
    by_cases hil : i = l
    · have h := congrFun hl j
      change b l j = b a j - L (b a) * rootExponent i j j at h
      rw [hj, mul_neg, mul_one, hb l j, hb a j, ite_eq_right (hil ▸ hij.symm),
        ite_eq_right (Ne.symm haj)] at h
      omega
    · have h := congrFun hl i
      change b l i = b a i - L (b a) * rootExponent i j i at h
      rw [hi, mul_one, hb l i, hb a i, ite_eq_right hil, ite_eq_right (Ne.symm hai)] at h
      omega
  let N : (Index.{u} n → ℤ) →ₗ[ℤ] ℤ :=
    (LinearMap.proj i : (Index.{u} n → ℤ) →ₗ[ℤ] ℤ) - LinearMap.proj j
  have he : L = N := by
    apply (Pi.basisFun ℤ (Index.{u} n)).ext
    intro a
    rw [Pi.basisFun_apply]
    change L (b a) = b a i - b a j
    by_cases hai : a = i
    · subst a
      rw [hb i i, hb i j, ite_eq_left rfl, ite_eq_right hij.symm]
      omega
    · by_cases haj : a = j
      · subst a
        rw [hb j i, hb j j, ite_eq_right hij, ite_eq_left rfl]
        omega
      · rw [h_other a hai haj, hb a i, hb a j, ite_eq_right (Ne.symm hai), ite_eq_right (Ne.symm haj), sub_self]
  exact LinearMap.congr_fun he lam


private theorem attached_coroot_point (e : MatrixPoints G n) {T : ClosedSubgroup G.val}
    {t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n)}
    (ht : DiagonalCoordinates e T t)
    {c : (Index.{u} n → ℤ) ≃+ Additive (Character T.group)}
    (hc : CharacterEvaluation t c) [IsCommMonObj T.group.X] (D : AbstractPairing.Datum T)
    (α : AbstractPairing.Root T) {i j : Index.{u} n} (hij : i ≠ j)
    (hα : α.val = characterAt c (rootExponent i j)) (R : TestAlgebra k) (z : Rˣ) :
    e.hom.app R (cocharacterPoint (Additive.toMul (D.rootDatum.coroot α)) R z ≫
        T.inclusion.hom.hom) = diagonalPoint (corootPoint i j z) := by
  rw [ht]
  congr 1
  funext a
  apply Units.ext
  let d := Additive.toMul (D.rootDatum.coroot α)
  let v : Index.{u} n → ℤ := Pi.single a 1
  have hpair : pairing T.group (characterAt c v) d = v i - v j :=
    (D.pairing_eq (characterAt c v) d).symm.trans (attached_coroot_pairing e ht hc D α hij hα v)
  have hv := (LinearAlgebraicGroups.RootData.CharacterPairing.characterPairingComposition
    T.group (characterAt c v) d).2 R z
  rw [hc, show weightValue v _ = _ from weightValue_basis a _, hpair] at hv
  calc
    _ = (z ^ (v i - v j)).val := hv
    _ = (corootPoint i j z a).val := by
      by_cases ha : a = i
      · subst a
        simp [v, corootPoint, Pi.single_eq_of_ne hij.symm]
      · by_cases hb : a = j
        · subst a
          simp [v, corootPoint, hij.symm]
        · simp [v, corootPoint, ha, hb]

/-- The attached simple coroots are the cocharacters of the adjacent
determinant-one matrix blocks. -/
theorem standardSimpleCoroots : StandardSimpleCoroots.{u} := by
  intro k _ n G e T B t ht hB c hc _ D
  constructor
  · intro a
    obtain ⟨i, j, hij, ha⟩ := (absoluteRoot_standard e ht hc _).mp a.val.property
    exact ⟨i, j, (standard_root_simple e ht hB hc a.val hij ha).mp a.property, ha,
      attached_coroot_pairing e ht hc D a.val hij ha,
      attached_coroot_point e ht hc D a.val hij ha⟩
  · intro i j hadj
    have hij : i ≠ j := by
      intro he
      subst j
      omega
    let α : AbstractPairing.Root T := ⟨characterAt c (rootExponent i j),
      (absoluteRoot_standard e ht hc _).mpr ⟨i, j, hij, rfl⟩⟩
    exact ⟨⟨α, (standard_root_simple e ht hB hc α hij rfl).mpr hadj⟩, rfl⟩

/-- The abstract dominance condition is the weakly decreasing order on the coordinates. -/
theorem dominance : Dominance.{u} := by
  intro k _ n hn G e T B t ht hB _ D χ lam hχ
  obtain ⟨c, hc⟩ := characterCoordinates k n G T t
  have hχ' := coordinates_determine_weight hc χ lam hχ
  rw [hχ']
  cases n with
  | zero => omega
  | succ n =>
    rw [← adjacentDominance n lam]
    constructor
    · intro hd q
      let i : Index.{u} (n + 1) := ⟨q.castSucc⟩
      let j : Index.{u} (n + 1) := ⟨q.succ⟩
      have hadj : i.down.val + 1 = j.down.val := rfl
      have hij : i ≠ j := by
        intro h
        have := congrArg (fun a : Index.{u} (n + 1) => a.down.val) h
        omega
      let α : AbstractPairing.Root T := ⟨characterAt c (rootExponent i j),
        (absoluteRoot_standard e ht hc _).mpr ⟨i, j, hij, rfl⟩⟩
      let a : RootWeightAction.SimpleRoot T B :=
        ⟨α, (standard_root_simple e ht hB hc α hij rfl).mpr hadj⟩
      have h := hd a
      change 0 ≤ D.rootDatum.toLinearMap (c lam) (D.rootDatum.coroot α) at h
      rwa [attached_coroot_pairing e ht hc D α hij rfl] at h
    · intro hd a
      obtain ⟨i, j, hij, ha⟩ := (absoluteRoot_standard e ht hc _).mp a.val.property
      have hadj := (standard_root_simple e ht hB hc a.val hij ha).mp a.property
      have hq : i.down.val < n := by have := j.down.isLt; omega
      let q : Fin n := ⟨i.down.val, hq⟩
      have hi : (⟨q.castSucc⟩ : Index.{u} (n + 1)) = i := ULift.ext (Fin.ext rfl)
      have hj : (⟨q.succ⟩ : Index.{u} (n + 1)) = j := ULift.ext (Fin.ext hadj)
      change 0 ≤ D.rootDatum.toLinearMap (c lam) (D.rootDatum.coroot a.val)
      rw [attached_coroot_pairing e ht hc D a.val hij ha]
      simpa only [hi, hj] using hd q

end
end LinearAlgebraicGroups.Representation.PolynomialGL


open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Representation.PolynomialGL
open LinearAlgebraicGroups.Specs
open Specs.PolynomialGL
open Specs.StandardGroups
open Specs.Unipotent (Index closedSubgroupAlgebraicGroup)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.GeneralLinearStructure (MatrixPoints IsDiagonal)
open Specs.GeometricRadicals (IsSplitTorus IsUnipotentRadical)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Triangularization (upperTriangular upperTriangularPoints)
open private diagonalMatrixHom diagonal_units_surjective baseChangePowerTorusIso
  from LinearAlgebraicGroups.Reductive.GeneralLinearStructure
open private diagonalMap diagonalMap_eq_one_iff
  from LinearAlgebraicGroups.Solvable.Triangularization

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {n : ℕ} {G : AffineAlgebraicGroup k}

private abbrev includedPoint (e : MatrixPoints G n) (S : ClosedSubgroup G.val)
    (R : TestAlgebra k) :
    GroupPoints S.group R →* Matrix.GeneralLinearGroup (Index.{u} n) R :=
  ((e.hom.app R).hom).comp (((groupPointsFunctor k).map S.inclusion).app R).hom

private theorem includedPoint_injective (e : MatrixPoints G n) (S : ClosedSubgroup G.val)
    (R : TestAlgebra k) : Function.Injective (includedPoint e S R) :=
  (e.app R).groupIsoToMulEquiv.injective.comp (subgroupPoint_injective S R)

private theorem includedPoint_natural (e : MatrixPoints G n) (S : ClosedSubgroup G.val)
    {R A : TestAlgebra k} (f : R ⟶ A) (x : GroupPoints S.group R) :
    includedPoint e S A (mapPoints f x) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom (includedPoint e S R x) :=
  ConcreteCategory.congr_hom (((groupPointsFunctor k).map S.inclusion ≫ e.hom).naturality f) x

private theorem includedPoint_surjective (e : MatrixPoints G n) {S : ClosedSubgroup G.val}
    {R : TestAlgebra k} (g : Matrix.GeneralLinearGroup (Index.{u} n) R)
    (h : e.inv.app R g ∈ SubgroupSections S ((testSpec k).obj (op R))) :
    ∃ x : GroupPoints S.group R, includedPoint e S R x = g := by
  obtain ⟨x, hx⟩ := h
  change x ≫ S.inclusion.hom.hom = e.inv.app R g at hx
  refine ⟨x, ?_⟩
  change e.hom.app R (x ≫ S.inclusion.hom.hom) = g
  rw [hx]
  exact (e.app R).groupIsoToMulEquiv.apply_symm_apply _

private theorem diagonalPoint_injective (R : TestAlgebra k) :
    Function.Injective (diagonalPoint (m := Index.{u} n) (R := R)) := by
  intro a b h
  funext i
  apply Units.ext
  simpa only [diagonalPoint_val, Matrix.diagonal_apply_eq] using
    congrArg (fun g : Matrix.GeneralLinearGroup (Index.{u} n) R => g.val i i) h

private theorem diagonalPoint_natural {R A : TestAlgebra k} (f : R ⟶ A)
    (a : Index.{u} n → Rˣ) :
    Matrix.GeneralLinearGroup.map f.hom.toRingHom (diagonalPoint a) =
      diagonalPoint ((multiplicativePowerPoints k (Index.{u} n)).map f a) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change ((diagonalPoint a).val.map f.hom) i j = _
  rw [diagonalPoint_val, diagonalPoint_val, Matrix.diagonal_map (map_zero _)]
  rfl

private theorem diagonalCoordinates_exists (e : MatrixPoints G n) (T : ClosedSubgroup G.val)
    (hT : ∀ (R : TestAlgebra k) (g : Points G.val.X R),
      g ∈ SubgroupSections T ((testSpec k).obj (op R)) ↔ IsDiagonal (e.hom.app R g)) :
    ∃ t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n),
      DiagonalCoordinates e T t := by
  have hd (R : TestAlgebra k) (x : GroupPoints T.group R) :
      ∃ a : Index.{u} n → Rˣ, diagonalPoint a = includedPoint e T R x :=
    diagonal_units_surjective _ ((hT R _).mp ⟨x, rfl⟩)
  choose a ha using hd
  let F (R : TestAlgebra k) : GroupPoints T.group R →* (Index.{u} n → Rˣ) :=
    { toFun := a R
      map_one' := by
        apply diagonalPoint_injective R
        change diagonalPoint (a R 1) = (diagonalMatrixHom _ R) 1
        rw [ha, map_one, map_one]
      map_mul' x y := by
        apply diagonalPoint_injective R
        change diagonalPoint (a R (x * y)) = (diagonalMatrixHom _ R) (a R x * a R y)
        rw [ha, map_mul, map_mul]
        exact congrArg₂ (· * ·) (ha R x).symm (ha R y).symm }
  have hF (R : TestAlgebra k) (x : GroupPoints T.group R) :
      diagonalPoint (F R x) = includedPoint e T R x := ha R x
  have hbij (R : TestAlgebra k) : Function.Bijective (F R) := by
    constructor
    · intro x y hxy
      apply includedPoint_injective e T R
      rw [← hF, ← hF, hxy]
    · intro d
      let g := diagonalPoint d
      have hg : IsDiagonal g := by
        intro i j hij
        rw [diagonalPoint_val, Matrix.diagonal_apply_ne _ hij]
      have hg' : IsDiagonal (e.hom.app R (e.inv.app R g)) := by
        change IsDiagonal ((e.app R).groupIsoToMulEquiv ((e.app R).groupIsoToMulEquiv.symm g))
        rw [MulEquiv.apply_symm_apply]
        exact hg
      have h := (hT R (e.inv.app R g)).mpr hg'
      obtain ⟨x, hx⟩ := includedPoint_surjective e g h
      exact ⟨x, diagonalPoint_injective R ((hF R x).trans hx)⟩
  let t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n) :=
    NatIso.ofComponents (fun R => (MulEquiv.ofBijective (F R) (hbij R)).toGrpIso) (by
      intro R A f
      apply GrpCat.ext
      intro x
      apply diagonalPoint_injective A
      change diagonalPoint (F A (mapPoints f x)) =
        diagonalPoint ((multiplicativePowerPoints k (Index.{u} n)).map f (F R x))
      rw [hF, includedPoint_natural, ← diagonalPoint_natural, hF])
  exact ⟨t, fun R x => (hF R x).symm⟩

private def upperTriangularPointIso (e : MatrixPoints G n) (B : ClosedSubgroup G.val)
    (hB : UpperTriangularCoordinates e B) :
    (groupPointsFunctor k).obj B.group ≅ upperTriangularPoints k n := by
  let m (R : TestAlgebra k) : GroupPoints B.group R →* upperTriangular (Index.{u} n) R :=
    (includedPoint e B R).codRestrict _ (fun x => (hB R _).mp ⟨x, rfl⟩)
  have hb (R : TestAlgebra k) : Function.Bijective (m R) := by
    constructor
    · intro x y h
      exact includedPoint_injective e B R (congrArg Subtype.val h)
    · intro g
      let z : GroupPoints G.val R := e.inv.app R g.val
      have hz : (e.hom.app R z).val.IsUpperTriangular :=
        (e.app R).groupIsoToMulEquiv.apply_symm_apply g.val ▸ g.property
      obtain ⟨x, hx⟩ := includedPoint_surjective e g.val ((hB R z).mpr hz)
      exact ⟨x, Subtype.ext hx⟩
  refine NatIso.ofComponents (fun R => (MulEquiv.ofBijective (m R) (hb R)).toGrpIso) ?_
  intro R A f
  apply GrpCat.ext
  intro x
  apply Subtype.ext
  exact includedPoint_natural e B f x

private theorem standardBorelPair (e : MatrixPoints G n) (hn : 0 < n) :
    ∃ (T B : ClosedSubgroup G.val)
      (t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n)),
      DiagonalCoordinates e T t ∧ UpperTriangularCoordinates e B ∧
      IsSplitTorus T.group ∧ IsGeometricallyMaximal T ∧ IsKBorel B ∧ IsSubgroupOf T B := by
  obtain ⟨T, B, hT, hB, hsplit, hTB, _, _, _, _, hTc, hBc, hmax, hborel⟩ :=
    LinearAlgebraicGroups.GeneralLinearStructure.generalLinearBorelPair k n hn G e
  obtain ⟨t, ht⟩ := diagonalCoordinates_exists e T hT
  refine ⟨T, B, t, ht, hB, hsplit, ⟨hTc, hmax⟩, ⟨hBc, ?_⟩, hTB⟩
  exact ⟨⟨hborel.1, hborel.2.1, hborel.2.2.1⟩,
    fun H hH => hborel.2.2.2 H hH.1 hH.2.1 hH.2.2⟩

private theorem powerTorus_multiplicativeType (n : ℕ) :
    (Specs.CharacterDescent.multiplicativeTypeSpecFunctor k).essImage
      (LinearAlgebraicGroups.StandardGroups.multiplicativePowerGroup k (Index.{u} n)) := by
  let M := Specs.CharacterDescent.StandardLattice.{u} n
  let L : Specs.DiagonalizableGroups.FGAbelianGroup.{u} := ⟨CommGrpCat.of M, inferInstance⟩
  obtain ⟨d⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) n
  exact (LinearAlgebraicGroups.CharacterDescent.multiplicativeTypeGroupCriterion _).mpr
    ⟨k, inferInstance, inferInstance, inferInstance, L, ⟨baseChangePowerTorusIso k n ≪≫ d.symm⟩⟩

private theorem diagonalMap_comp_unipotent {B H : AffineAlgebraicGroup k}
    (b : (groupPointsFunctor k).obj B.val ≅ upperTriangularPoints k n) (f : H.val ⟶ B.val)
    (hH : Specs.Unipotent.IsUnipotent H) :
    f ≫ diagonalMap (T := B) b = 0 := by
  let D := LinearAlgebraicGroups.StandardGroups.multiplicativePowerGroup k (Index.{u} n)
  exact @LinearAlgebraicGroups.Unipotent.homFromUnipotentToMultiplicativeType.{u} k inferInstance
    H D (f ≫ diagonalMap (T := B) b) hH (powerTorus_multiplicativeType n)

private theorem radical_upperUnitriangular (e : MatrixPoints G n) {B : ClosedSubgroup G.val}
    (hB : UpperTriangularCoordinates e B) {U : ClosedSubgroup B.group}
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U)
    (R : TestAlgebra k) (x : GroupPoints U.group R) :
    Specs.Unipotent.IsUpperUnitriangular
      (e.hom.app R (x ≫ (U.inclusion ≫ B.inclusion).hom.hom)).val := by
  let B₀ : AffineAlgebraicGroup k := closedSubgroupAlgebraicGroup B
  let U₀ : AffineAlgebraicGroup k := closedSubgroupAlgebraicGroup (G := B₀) U
  let b : (groupPointsFunctor k).obj B₀.val ≅ upperTriangularPoints k n :=
    upperTriangularPointIso e B hB
  let D := LinearAlgebraicGroups.StandardGroups.multiplicativePowerGroup k (Index.{u} n)
  let q : B₀.val ⟶ D.val := diagonalMap (T := B₀) b
  have hU₀ : Specs.Unipotent.IsUnipotent U₀ := hU.2.1
  have hq : (U.inclusion : U₀.val ⟶ B₀.val) ≫ q = 0 :=
    diagonalMap_comp_unipotent b (U.inclusion : U₀.val ⟶ B₀.val) hU₀
  let y : GroupPoints B₀.val R := x ≫ U.inclusion.hom.hom
  have hk : (((groupPointsFunctor k).map q).app R).hom y = 1 := by
    change (((groupPointsFunctor k).map (U.inclusion ≫ q)).app R).hom x = 1
    rw [hq]
    change x ≫ (0 : U.group ⟶ D.val).hom.hom = 1
    exact MonObj.comp_one _
  have hy := (diagonalMap_eq_one_iff (T := B₀) b R y).mp hk
  exact hy

end
end LinearAlgebraicGroups.Representation.PolynomialGL


open AlgebraicGeometry CategoryTheory Opposite WithConv
open scoped CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Representation.PolynomialGL
open LinearAlgebraicGroups.Specs
open Specs.PolynomialGL
open Specs.Unipotent (Index closedSubgroupAlgebraicGroup)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.RootWeightAction (Representation act extendVector weightSpace mem_weightSpace mem_fixedSpace)
open Specs.PrimitiveLine (IsEquivariant orbitCoefficient IsSimple)
open Specs.CyclicHighestWeight (orbitSpan)
open Specs.CharacterPairing (characterValue)
open Specs.CharacterDescent (Character)
open private fromCoaction toCoaction orbit_properties orbit_stable act_eq_scalar_iff
  stable_map stable_ker sumRepresentation leftProjection rightProjection
  left_equivariant right_equivariant comp_equivariant inclusion_equivariant
  from LinearAlgebraicGroups.Representation.PrimitiveLine

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
  {H I J : Type u} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

private theorem action_eq_scalar_of_projections
    {τ : Representation G.val H} {ρ : Representation G.val I} {σ : Representation G.val J}
    {p : (H → k) →ₗ[k] (I → k)} {q : (H → k) →ₗ[k] (J → k)}
    (hp : IsEquivariant τ ρ p) (hq : IsEquivariant τ σ q)
    (hjoint : ∀ z, p z = 0 → q z = 0 → z = 0)
    (R : TestAlgebra k) (g : GroupPoints G.val R) (z : H → k) (c : R)
    (h₁ : act ρ R g (extendVector R (p z)) = c • extendVector R (p z))
    (h₂ : act σ R g (extendVector R (q z)) = c • extendVector R (q z)) :
    act τ R g (extendVector R z) = c • extendVector R z := by
  apply (act_eq_scalar_iff τ R g z c).mpr
  intro ℓ
  apply sub_eq_zero.mp
  apply hjoint
  · rw [map_sub, hp, map_smul, (act_eq_scalar_iff ρ R g (p z) c).mp h₁ ℓ, sub_self]
  · rw [map_sub, hq, map_smul, (act_eq_scalar_iff σ R g (q z) c).mp h₂ ℓ, sub_self]

private theorem projection_injective_of_top_weight
    {τ : Representation G.val H} {ρ : Representation G.val I} {σ : Representation G.val J}
    {p : (H → k) →ₗ[k] (I → k)} {q : (H → k) →ₗ[k] (J → k)}
    (hp : IsEquivariant τ ρ p) (hq : IsEquivariant τ σ q)
    (hjoint : ∀ z, p z = 0 → q z = 0 → z = 0) (hsimple : IsSimple σ)
    {T : ClosedSubgroup G.val} {χ : Character T.group} (z : H → k)
    (hpz : p z ≠ 0) (hqz : q z ≠ 0) (hw : q z ∈ weightSpace σ T χ)
    (htop : weightSpace τ T χ = Submodule.span k {z}) :
    Function.Injective p := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  by_contra hx0
  let C := (LinearMap.ker p).map q
  have hC : C = ⊤ := by
    rcases hsimple.2 C (stable_map hq _ (stable_ker hp)) with he | he
    · have hxC : q x ∈ C := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      exact False.elim (hx0 (hjoint x hx ((Submodule.mem_bot k).mp (he ▸ hxC))))
    · exact he
  obtain ⟨y, hyp, hyq⟩ := Submodule.mem_map.mp (show q z ∈ C from hC ▸ Submodule.mem_top)
  have hyw : y ∈ weightSpace τ T χ := by
    apply mem_weightSpace.mpr
    intro R t
    apply action_eq_scalar_of_projections hp hq hjoint
    · rw [LinearMap.mem_ker.mp hyp]
      change RootWeightAction.actLinear ρ R _ (RootWeightAction.extendLinear R 0) =
        _ • RootWeightAction.extendLinear R 0
      simp only [map_zero, smul_zero]
    · rw [hyq]
      exact mem_weightSpace.mp hw R t
  rw [htop, Submodule.mem_span_singleton] at hyw
  obtain ⟨a, ha⟩ := hyw
  have hap : a • p z = 0 := by
    rw [← map_smul, ha]
    exact hyp
  have ha0 : a = 0 := (smul_eq_zero.mp hap).resolve_right hpz
  exact hqz (by rw [← hyq, ← ha, ha0, zero_smul, map_zero])

/-- A simple module is a quotient of a submodule of any module with a primitive
vector of the same weight. -/
private theorem simple_is_subquotient
    (hC : Specs.CyclicHighestWeight.CoactionComparison.{u})
    (A : HopfAlgebraCategory k) (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    {T B : ClosedSubgroup G.val} {U : ClosedSubgroup B.group}
    (htop : ∀ {L : Type u} [Fintype L] [DecidableEq L] (τ : Representation G.val L)
      (χ : Character T.group) (z : L → k), RootWeightAction.IsPrimitive τ T B U χ z →
      orbitSpan τ (𝟙 G.val.X) z = ⊤ → weightSpace τ T χ = Submodule.span k {z})
    (ρ : Representation G.val I) (σ : Representation G.val J) (hsimple : IsSimple σ)
    (χ : Character T.group) (v : I → k) (w : J → k)
    (hv : RootWeightAction.IsPrimitive ρ T B U χ v)
    (hw : RootWeightAction.IsPrimitive σ T B U χ w) :
    ∃ (L : Type u) (hL : Fintype L) (dL : DecidableEq L),
      letI := hL
      letI := dL
      ∃ (τ : Representation G.val L) (p : (L → k) →ₗ[k] (I → k)) (q : (L → k) →ₗ[k] (J → k)),
        IsEquivariant τ ρ p ∧ Function.Injective p ∧
          IsEquivariant τ σ q ∧ Function.Surjective q := by
  classical
  let ψ := sumRepresentation ρ σ
  let s : I ⊕ J → k := Sum.elim v w
  let C := orbitSpan ψ (𝟙 G.val.X) s
  obtain ⟨hs, hsub, _⟩ := orbit_properties hC ψ A e s
  obtain ⟨δ, hδ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction
    (toCoaction e (Pi.basisFun k (I ⊕ J)) ψ) C).mp hsub
  let L := ULift.{u} (Fin (Module.finrank k C))
  let b : Module.Basis L k C := (Module.finBasis k C).reindex Equiv.ulift.symm
  let τ := fromCoaction e b δ
  let inc := C.subtype.comp b.equivFun.symm.toLinearMap
  have hinc : IsEquivariant τ ψ inc := inclusion_equivariant e ψ C b δ hδ
  have hinj : Function.Injective inc := Subtype.val_injective.comp b.equivFun.symm.injective
  let p := leftProjection.comp inc
  let q := rightProjection.comp inc
  have hp : IsEquivariant τ ρ p := comp_equivariant hinc (left_equivariant ρ σ)
  have hq : IsEquivariant τ σ q := comp_equivariant hinc (right_equivariant ρ σ)
  have hjoint (z : L → k) (hp0 : p z = 0) (hq0 : q z = 0) : z = 0 := by
    apply hinj
    rw [map_zero]
    funext i
    cases i with
    | inl i => exact congrFun hp0 i
    | inr j => exact congrFun hq0 j
  let x : L → k := b.equivFun ⟨s, hs⟩
  have hx : inc x = s := by simp [inc, x]
  have hpx : p x = v := congrArg leftProjection hx
  have hqx : q x = w := congrArg rightProjection hx
  have hprim : RootWeightAction.IsPrimitive τ T B U χ x := by
    refine ⟨fun hz => hv.1 (hpx.symm.trans (hz ▸ p.map_zero)), mem_fixedSpace.mpr ?_,
      mem_weightSpace.mpr ?_⟩
    · intro R g
      have h₁ := mem_fixedSpace.mp hv.2.1 R g
      have h₂ := mem_fixedSpace.mp hw.2.1 R g
      have h := action_eq_scalar_of_projections hp hq hjoint R
        (g ≫ (U.inclusion ≫ B.inclusion).hom.hom) x 1 (by rwa [hpx, one_smul])
        (by rwa [hqx, one_smul])
      simpa only [one_smul] using h
    · intro R t
      exact action_eq_scalar_of_projections hp hq hjoint R _ x _
        (hpx.symm ▸ mem_weightSpace.mp hv.2.2 R t) (hqx.symm ▸ mem_weightSpace.mp hw.2.2 R t)
  have hgen : orbitSpan τ (𝟙 G.val.X) x = ⊤ := by
    let N := orbitSpan τ (𝟙 G.val.X) x
    have hxN := (orbit_properties hC τ A e x).1
    have hsN : s ∈ N.map inc := Submodule.mem_map.mpr ⟨x, hxN, hx⟩
    have hle : C ≤ N.map inc := (stable_map hinc N (orbit_stable hC τ A e x)) s hsN
    apply top_unique
    intro z _
    have hz : inc z ∈ C := (b.equivFun.symm z).property
    obtain ⟨z', hz', heq⟩ := Submodule.mem_map.mp (hle hz)
    exact hinj heq ▸ hz'
  have htop' := htop τ χ x hprim hgen
  refine ⟨L, inferInstance, inferInstance, τ, p, q, hp,
    projection_injective_of_top_weight hp hq hjoint hsimple x (hpx.symm ▸ hv.1)
      (hqx.symm ▸ hw.1) (hqx.symm ▸ hw.2.2) htop', hq, ?_⟩
  apply LinearMap.range_eq_top.mp
  rcases hsimple.2 (LinearMap.range q)
      (by simpa using stable_map hq ⊤ (fun _ _ => le_top)) with he | he
  · have hz := (Submodule.mem_bot k).mp (he ▸ LinearMap.mem_range_self q x)
    exact False.elim (hw.1 (hqx.symm.trans hz))
  · exact he

end
end LinearAlgebraicGroups.Representation.PolynomialGL


namespace LinearAlgebraicGroups.Representation.PolynomialGL
open CategoryTheory
open LinearAlgebraicGroups.Specs
open Specs.PolynomialGL
open Specs.StandardGroups
open Specs.Unipotent (Index closedSubgroupAlgebraicGroup)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.GeneralLinearStructure (MatrixPoints)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.CharacterDescent (Character)
open Specs.RootWeightAction (extendVector mem_weightSpace mem_fixedSpace)
open Specs.CyclicHighestWeight (orbitSpan)
open Specs.PrimitiveLine (IsEquivariant)
open private generates_of_simple from LinearAlgebraicGroups.Representation.PrimitiveLine

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]
  {G : AffineAlgebraicGroup k} {n : ℕ}

private theorem weightSpace_iff_hasWeight (e : MatrixPoints G n) {T : ClosedSubgroup G.val}
    {t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n)}
    (ht : DiagonalCoordinates e T t)
    {c : (Index.{u} n → ℤ) ≃+ Additive (Character T.group)}
    (hc : CharacterEvaluation t c)
    (ρ : MatrixRepresentation k (Index.{u} n) I) (lam : Index.{u} n → ℤ) (v : I → k) :
    v ∈ RootWeightAction.weightSpace (e.hom ≫ ρ) T (characterAt c lam) ↔ HasWeight ρ lam v := by
  rw [mem_weightSpace]
  constructor
  · intro h R d
    obtain ⟨x, rfl⟩ := (t.app R).groupIsoToMulEquiv.surjective d
    have hx := h R x
    change (representationAt ρ R (e.hom.app R (x ≫ T.inclusion.hom.hom))).val.mulVec
      (extendVector R v) = Specs.CharacterPairing.characterValue (characterAt c lam) R x •
        extendVector R v at hx
    rwa [ht R x, hc] at hx
  · intro h R x
    change (representationAt ρ R (e.hom.app R (x ≫ T.inclusion.hom.hom))).val.mulVec
      (extendVector R v) = Specs.CharacterPairing.characterValue (characterAt c lam) R x •
        extendVector R v
    rw [ht R x, hc]
    exact h R (t.hom.app R x)

private theorem primitive_of_unitriangular {n : ℕ} (e : MatrixPoints G (n + 1))
    {T B : ClosedSubgroup G.val}
    {t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} (n + 1))}
    (ht : DiagonalCoordinates e T t) (hB : UpperTriangularCoordinates e B)
    {c : (Index.{u} (n + 1) → ℤ) ≃+ Additive (Character T.group)}
    (hc : CharacterEvaluation t c)
    {U : ClosedSubgroup B.group} (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U)
    (ρ : MatrixRepresentation k (Index.{u} (n + 1)) I)
    (lam : Index.{u} (n + 1) → ℤ) (v : I → k) (hv : IsPrimitive ρ lam v) :
    RootWeightAction.IsPrimitive (e.hom ≫ ρ) T B U (characterAt c lam) v := by
  refine ⟨hv.1, mem_fixedSpace.mpr ?_, (weightSpace_iff_hasWeight e ht hc ρ lam v).mpr hv.2.1⟩
  intro R g
  have hg := radical_upperUnitriangular e hB hU R g
  exact hv.2.2 R (e.hom.app R (g ≫ (U.inclusion ≫ B.inclusion).hom.hom)) hg.1 hg.2

/-- For the standard Borel pair the simple highest-weight module is polynomial
exactly when the last coordinate of its highest weight is nonnegative. -/
theorem simpleHighestWeightCriterion : SimpleHighestWeightCriterion.{u} := by
  intro k _ n G e
  have hn : 0 < n + 1 := Nat.succ_pos _
  have hG := LinearAlgebraicGroups.GeneralLinearStructure.generalLinearReductive k (n + 1) hn G e
  obtain ⟨T, B, t, ht, hb, hsplit, hmax, hborel, hTB⟩ := standardBorelPair e hn
  obtain ⟨c, hc⟩ := characterCoordinates k (n + 1) G T t
  obtain ⟨comm, D, U, hU, htop, _, _⟩ :=
    LinearAlgebraicGroups.Representation.PrimitiveLine.primitiveLine
      G hG T B hsplit hmax hborel hTB
  letI := comm
  refine ⟨T, B, t, c, U, ht, hb, hc, hsplit, hmax, hborel, hTB, hU, ?_⟩
  intro I _ _ ρ hs lam v hv
  constructor
  · intro hp
    exact nonnegativeWeights k (Index.{u} (n + 1)) I ρ hp lam v hv.1
      ((weightSpace_iff_hasWeight e ht hc ρ lam v).mp hv.2.2) ⟨Fin.last n⟩
  · intro hlast
    let G₀ : AffineGroupCategory k := ⟨G.val, G.property.1⟩
    let A := coordinateHopf G₀
    let e₀ : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val :=
      hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso
        ((affineGroupInclusion k).mapIso (coordinateHopfSpecIso G₀))
    have hC : Specs.CyclicHighestWeight.CoactionComparison.{u} :=
      (LinearAlgebraicGroups.Representation.CyclicHighestWeight.cyclicHighestWeight.{u}).1
    have hgen := generates_of_simple hC (e.hom ≫ ρ) A e₀ hs hv.1
    have hd := (htop (e.hom ≫ ρ) (characterAt c lam) v hv hgen).2.2.1
    have hmono : Antitone lam :=
      (dominance k (n + 1) hn G e T B t ht hb D (characterAt c lam) lam (hc lam)).mp hd
    obtain ⟨J, hJ, dJ, σ, w, hσ, hw⟩ := polynomialPrimitiveExistence k n lam hmono hlast
    letI : Fintype J := hJ
    letI : DecidableEq J := dJ
    have hw' := primitive_of_unitriangular e ht hb hc hU σ lam w hw
    obtain ⟨L, hL, dL, τ, p, q, hp, hinj, hq, hsurj⟩ :=
      simple_is_subquotient hC A e₀ (fun τ χ z hz hgen => (htop τ χ z hz hgen).1)
        (e.hom ≫ σ) (e.hom ≫ ρ) hs (characterAt c lam) w v hw' hv
    letI : Fintype L := hL
    letI : DecidableEq L := dL
    let τ₀ : MatrixRepresentation k (Index.{u} (n + 1)) L := e.inv ≫ τ
    have hτ : e.hom ≫ τ₀ = τ := by simp [τ₀]
    have hp₀ : IsEquivariant (e.hom ≫ τ₀) (e.hom ≫ σ) p := by simpa only [hτ] using hp
    have hq₀ : IsEquivariant (e.hom ≫ τ₀) (e.hom ≫ ρ) q := by simpa only [hτ] using hq
    exact polynomial_of_equivariant_surjective e hq₀ hsurj
      (polynomial_of_equivariant_injective e hp₀ hinj hσ)

/-- The same criterion in the pointwise coordinates of the standard matrix groups. -/
theorem simpleCriterion : SimpleCriterion.{u} := by
  intro k I _ _ _ n G e ρ hs lam v hv
  obtain ⟨T, B, t, c, U, ht, hb, hc, _, _, _, _, hU, H⟩ :=
    simpleHighestWeightCriterion k n G e
  exact H I ρ hs lam v (primitive_of_unitriangular e ht hb hc hU ρ lam v hv)

end
end LinearAlgebraicGroups.Representation.PolynomialGL
