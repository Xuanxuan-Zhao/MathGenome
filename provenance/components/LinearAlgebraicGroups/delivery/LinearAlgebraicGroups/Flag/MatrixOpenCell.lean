import Specs.LinearAlgebraicGroups.Flag.MatrixOpenCell

open AlgebraicGeometry Matrix
open scoped BigOperators

universe u v

namespace LinearAlgebraicGroups.MatrixOpenCell

open Specs.MatrixOpenCell

noncomputable section

variable {R : Type v} {n : ℕ}

private def border (a : R) (b c : Fin n → R) (M : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i j => Fin.cases (Fin.cases a b j) (fun i => Fin.cases (c i) (M i) j) i

@[simp] private theorem border_zero_zero (a : R) (b c : Fin n → R) (M : Matrix (Fin n) (Fin n) R) :
    border a b c M 0 0 = a := rfl

@[simp] private theorem border_zero_succ (a : R) (b c : Fin n → R) (M : Matrix (Fin n) (Fin n) R)
    (j : Fin n) : border a b c M 0 j.succ = b j := rfl

@[simp] private theorem border_succ_zero (a : R) (b c : Fin n → R) (M : Matrix (Fin n) (Fin n) R)
    (i : Fin n) : border a b c M i.succ 0 = c i := rfl

@[simp] private theorem border_succ_succ (a : R) (b c : Fin n → R) (M : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) : border a b c M i.succ j.succ = M i j := rfl

variable [CommRing R]

private def assemble (d : Rˣ) (l u : Fin n → R) (S : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  border d (fun j => (d : R) * u j) (fun i => l i * (d : R))
    (fun i j => S i j + l i * (d : R) * u j)

private theorem det_assemble (d : Rˣ) (l u : Fin n → R) (S : Matrix (Fin n) (Fin n) R) :
    (assemble d l u S).det = (d : R) * S.det := by
  have hmul : assemble d l u S =
      border 1 0 l (1 : Matrix (Fin n) (Fin n) R) *
        border (d : R) (fun j => (d : R) * u j) 0 S := by
    ext i j
    refine Fin.cases (Fin.cases ?_ (fun j => ?_) j) (fun i => Fin.cases ?_ (fun j => ?_) j) i
    all_goals simp [assemble, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, mul_assoc]
    all_goals first | rfl | exact add_comm _ _
  rw [hmul, Matrix.det_mul]
  have h₁ : (border 1 0 l (1 : Matrix (Fin n) (Fin n) R)).det = 1 := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp [Matrix.submatrix]
    exact Matrix.det_one
  have h₂ : (border (d : R) (fun j => (d : R) * u j) 0 S).det = (d : R) * S.det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp [Matrix.submatrix]
    rfl
  rw [h₁, h₂, one_mul]

private theorem leading_zero (A : Matrix (Fin n) (Fin n) R) :
    leadingMinor A 0 (Nat.zero_le _) = 1 := Matrix.det_isEmpty

private theorem leading_full (A : Matrix (Fin n) (Fin n) R) :
    leadingMinor A n le_rfl = A.det := by simp [leadingMinor, leadingBlock]

private theorem leading_assemble (d : Rˣ) (l u : Fin n → R) (S : Matrix (Fin n) (Fin n) R)
    (m : ℕ) (hm : m ≤ n) :
    leadingMinor (assemble d l u S) (m + 1) (Nat.succ_le_succ hm) =
      (d : R) * leadingMinor S m hm := by
  have h : leadingBlock (assemble d l u S) (m + 1) (Nat.succ_le_succ hm) =
      assemble d (l ∘ Fin.castLE hm) (u ∘ Fin.castLE hm) (leadingBlock S m hm) := by
    ext i j
    refine Fin.cases (Fin.cases ?_ (fun j => ?_) j) (fun i => Fin.cases ?_ (fun j => ?_) j) i
    all_goals simp only [leadingBlock, Matrix.submatrix_apply, assemble, Function.comp_apply]
    all_goals rfl
  exact (congrArg Matrix.det h).trans (det_assemble ..)

private def extend (d : Rˣ) (l u : Fin n → R) (f : Factors R n) : Factors R (n + 1) where
  lower := border 1 0 l f.lower
  diagonal := Fin.cases d f.diagonal
  upper := border 1 u 0 f.upper
  lower_zero := by
    intro i j
    refine Fin.cases (Fin.cases ?_ (fun j => ?_) j) (fun i => Fin.cases ?_ (fun j => ?_) j) i
    · simp
    · simp
    · simp
    · simpa using f.lower_zero i j
  lower_one := fun i => Fin.cases rfl (fun i => f.lower_one i) i
  upper_zero := by
    intro i j
    refine Fin.cases (Fin.cases ?_ (fun j => ?_) j) (fun i => Fin.cases ?_ (fun j => ?_) j) i
    · simp
    · simp
    · simp
    · simpa using f.upper_zero i j
  upper_one := fun i => Fin.cases rfl (fun i => f.upper_one i) i

private def tail (f : Factors R (n + 1)) : Factors R n where
  lower i j := f.lower i.succ j.succ
  diagonal i := f.diagonal i.succ
  upper i j := f.upper i.succ j.succ
  lower_zero := fun _i _j h => f.lower_zero _ _ (Fin.succ_lt_succ_iff.mpr h)
  lower_one := fun _i => f.lower_one _
  upper_zero := fun _i _j h => f.upper_zero _ _ (Fin.succ_lt_succ_iff.mpr h)
  upper_one := fun _i => f.upper_one _

private theorem factors_ext (f g : Factors R n) (hl : f.lower = g.lower)
    (hd : f.diagonal = g.diagonal) (hu : f.upper = g.upper) : f = g := by
  cases f
  cases g
  cases hl
  cases hd
  cases hu
  rfl

private theorem extend_tail (f : Factors R (n + 1)) :
    extend (f.diagonal 0) (fun i => f.lower i.succ 0) (fun j => f.upper 0 j.succ) (tail f) = f := by
  apply factors_ext
  · ext i j
    refine Fin.cases (Fin.cases ?_ (fun j => ?_) j) (fun i => Fin.cases ?_ (fun j => ?_) j) i
    · exact (f.lower_one 0).symm
    · exact (f.lower_zero 0 _ (Fin.succ_pos j)).symm
    · rfl
    · rfl
  · funext i
    exact Fin.cases rfl (fun i => rfl) i
  · ext i j
    refine Fin.cases (Fin.cases ?_ (fun j => ?_) j) (fun i => Fin.cases ?_ (fun j => ?_) j) i
    · exact (f.upper_one 0).symm
    · rfl
    · exact (f.upper_zero _ 0 (Fin.succ_pos i)).symm
    · rfl

private theorem product_apply (f : Factors R n) (i j : Fin n) :
    f.product i j = ∑ a, f.lower i a * (f.diagonal a : R) * f.upper a j := by
  rw [Factors.product, Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal]

private theorem product_extend (d : Rˣ) (l u : Fin n → R) (f : Factors R n) :
    (extend d l u f).product = assemble d l u f.product := by
  ext i j
  refine Fin.cases (Fin.cases ?_ (fun j => ?_) j) (fun i => Fin.cases ?_ (fun j => ?_) j) i
  all_goals rw [product_apply, Fin.sum_univ_succ]
  all_goals simp only [extend, assemble, border, Fin.cases_zero, Fin.cases_succ, Pi.zero_apply,
    one_mul, mul_one, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
  rw [product_apply, add_comm]

private theorem assemble_decompose (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (d : Rˣ) (hd : (d : R) = A 0 0) :
    assemble d (fun i => A i.succ 0 * (↑d⁻¹ : R)) (fun j => (↑d⁻¹ : R) * A 0 j.succ)
      (fun i j => A i.succ j.succ - A i.succ 0 * (↑d⁻¹ : R) * A 0 j.succ) = A := by
  ext i j
  refine Fin.cases (Fin.cases ?_ (fun j => ?_) j) (fun i => Fin.cases ?_ (fun j => ?_) j) i
  · exact hd
  · change (d : R) * ((↑d⁻¹ : R) * A 0 j.succ) = _
    simp [← mul_assoc]
  · change A i.succ 0 * (↑d⁻¹ : R) * (d : R) = _
    simp [mul_assoc]
  · have hcancel : A i.succ 0 * (↑d⁻¹ : R) * (d : R) = A i.succ 0 := by
      simp [mul_assoc]
    change A i.succ j.succ - A i.succ 0 * (↑d⁻¹ : R) * A 0 j.succ +
      A i.succ 0 * (↑d⁻¹ : R) * (d : R) * ((↑d⁻¹ : R) * A 0 j.succ) = _
    rw [hcancel]
    simp [mul_assoc]

theorem minorFormula : MinorFormula.{v} := by
  intro R _ n
  induction n with
  | zero =>
    intro f m hm
    have : m = 0 := by omega
    subst m
    simp [leading_zero]
  | succ n ih =>
    intro f m hm
    cases m with
    | zero => simp [leading_zero]
    | succ m =>
      have hm' : m ≤ n := Nat.le_of_succ_le_succ hm
      have h := congrArg (fun g : Factors R (n + 1) => g.product) (extend_tail f)
      rw [product_extend] at h
      rw [← h, leading_assemble _ _ _ _ m hm', ih (tail f) m hm', Fin.prod_univ_succ]
      rfl

private theorem isUnit_prod {ι : Type*} [Fintype ι] (x : ι → R) (h : ∀ i, IsUnit (x i)) :
    IsUnit (∏ i : ι, x i) := by
  exact Finset.prod_induction x IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one (fun i _ => h i)

private theorem unitMinors_product (f : Factors R n) : HasUnitMinors f.product := by
  intro m hm
  rw [minorFormula R n f m hm]
  exact isUnit_prod _ (fun i => (f.diagonal (Fin.castLE hm i)).isUnit)

private theorem factor_exists_unique (A : Matrix (Fin n) (Fin n) R)
    (hA : HasUnitMinors A) : ∃! f : Factors R n, f.product = A := by
  induction n with
  | zero =>
    let f : Factors R 0 :=
      ⟨1, Fin.elim0, 1, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
        fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    refine ⟨f, Matrix.ext (fun i => Fin.elim0 i), fun g _ => ?_⟩
    exact factors_ext g f (Matrix.ext (fun i => Fin.elim0 i))
      (funext (fun i => Fin.elim0 i)) (Matrix.ext (fun i => Fin.elim0 i))
  | succ n ih =>
    have ha : IsUnit (A 0 0) := by
      simpa [leadingMinor, leadingBlock, Matrix.det_fin_one] using hA 1 (by omega)
    let d := ha.unit
    let l : Fin n → R := fun i => A i.succ 0 * (↑d⁻¹ : R)
    let u : Fin n → R := fun j => (↑d⁻¹ : R) * A 0 j.succ
    let S : Matrix (Fin n) (Fin n) R :=
      fun i j => A i.succ j.succ - A i.succ 0 * (↑d⁻¹ : R) * A 0 j.succ
    have he : assemble d l u S = A := assemble_decompose A d ha.unit_spec
    have hS : HasUnitMinors S := by
      intro m hm
      have h := hA (m + 1) (Nat.succ_le_succ hm)
      rw [← he, leading_assemble d l u S m hm] at h
      exact isUnit_of_mul_isUnit_right h
    obtain ⟨f, hf, huniq⟩ := ih S hS
    refine ⟨extend d l u f, (product_extend d l u f).trans (by rw [hf, he]), fun g hg => ?_⟩
    change g.product = A at hg
    have hg' := congrArg (fun f : Factors R (n + 1) => f.product) (extend_tail g)
    rw [product_extend, hg, ← he] at hg'
    have hd : g.diagonal 0 = d := Units.ext (congrFun (congrFun hg' 0) 0)
    rw [hd] at hg'
    have hl : (fun i : Fin n => g.lower i.succ 0) = l := by
      funext i
      have h := congrFun (congrFun hg' i.succ) 0
      change g.lower i.succ 0 * (d : R) = l i * (d : R) at h
      simpa [mul_assoc] using congrArg (fun a : R => a * ↑d⁻¹) h
    have hu : (fun j : Fin n => g.upper 0 j.succ) = u := by
      funext j
      have h := congrFun (congrFun hg' 0) j.succ
      change (d : R) * g.upper 0 j.succ = (d : R) * u j at h
      simpa [← mul_assoc] using congrArg (fun a : R => ↑d⁻¹ * a) h
    rw [hl, hu] at hg'
    have htail : (tail g).product = S := by
      ext i j
      have h := congrFun (congrFun hg' i.succ) j.succ
      change (tail g).product i j + l i * (d : R) * u j = S i j + l i * (d : R) * u j at h
      exact add_right_cancel h
    calc
      g = extend (g.diagonal 0) (fun i => g.lower i.succ 0)
          (fun j => g.upper 0 j.succ) (tail g) := (extend_tail g).symm
      _ = extend d l u f := by rw [hd, hl, hu, huniq _ htail]

theorem factorization : Factorization.{v} := by
  intro R _ n A
  constructor
  · exact factor_exists_unique A
  · rintro ⟨f, rfl, _⟩
    exact unitMinors_product f

private theorem map_leadingMinor {S : Type*} [CommRing S] (g : R →+* S)
    (A : Matrix (Fin n) (Fin n) R) (m : ℕ) (hm : m ≤ n) :
    g (leadingMinor A m hm) = leadingMinor (g.mapMatrix A) m hm :=
  g.map_det (leadingBlock A m hm)

private theorem map_hasUnitMinors {S : Type*} [CommRing S] (g : R →+* S)
    {A : Matrix (Fin n) (Fin n) R} (h : HasUnitMinors A) :
    HasUnitMinors (g.mapMatrix A) := by
  intro m hm
  rw [← map_leadingMinor]
  exact (h m hm).map g

theorem map_product {S : Type v} [CommRing S] (g : R →+* S) (f : Factors R n) :
    (f.map g).product = g.mapMatrix f.product := by
  ext i j
  simp only [product_apply, Factors.map, RingHom.mapMatrix_apply, Matrix.map_apply,
    Units.coe_map, map_sum, map_mul, MonoidHom.coe_ofClass]

section Coordinates

variable {k : Type u} [CommRing k]

private theorem cellMatrix_unitMinors (k : Type u) [CommRing k] (n : ℕ) :
    HasUnitMinors (cellMatrix k n) := by
  intro m hm
  rw [cellMatrix, ← map_leadingMinor]
  apply IsLocalization.Away.isUnit_of_dvd (x := minorProduct k n)
  let i : Fin (n + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
  exact Finset.dvd_prod_of_mem
    (fun i : Fin (n + 1) => leadingMinor (glMatrix k n) i.val (Nat.le_of_lt_succ i.isLt))
    (Finset.mem_univ i)

private def evaluateEntries {R : Type u} [CommRing R] [Algebra k R]
    (A : Matrix.GeneralLinearGroup (Fin n) R) :
    MvPolynomial (ULift.{u} (Fin n) × ULift.{u} (Fin n)) k →ₐ[k] R :=
  MvPolynomial.aeval (fun ij => A.val ij.1.down ij.2.down)

private theorem evaluateEntries_det_unit {R : Type u} [CommRing R] [Algebra k R]
    (A : Matrix.GeneralLinearGroup (Fin n) R) :
    IsUnit (evaluateEntries (k := k) A (genericMatrix k n).det) := by
  let e := (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n)
  have he : (evaluateEntries (k := k) A).mapMatrix (genericMatrix k n) = A.val.submatrix e e :=
    Matrix.ext (fun i j => MvPolynomial.aeval_X _ (i, j))
  rw [AlgHom.map_det, he, Matrix.det_submatrix_equiv_self]
  exact (Matrix.GeneralLinearGroup.det A).isUnit

private def evaluateGL {R : Type u} [CommRing R] [Algebra k R]
    (A : Matrix.GeneralLinearGroup (Fin n) R) :
    MatrixGroupCoordinates k n →ₐ[k] R :=
  IsLocalization.Away.liftAlgHom (genericMatrix k n).det (evaluateEntries_det_unit A)

private theorem evaluateGL_entry {R : Type u} [CommRing R] [Algebra k R]
    (A : Matrix.GeneralLinearGroup (Fin n) R) (i j : Fin n) :
    evaluateGL (k := k) A (glMatrix k n i j) = A.val i j :=
  (IsLocalization.Away.lift_eq (S := MatrixGroupCoordinates k n)
    (genericMatrix k n).det (evaluateEntries_det_unit (k := k) A)
    (MvPolynomial.X (ULift.up i, ULift.up j))).trans
      (MvPolynomial.aeval_X _ (ULift.up i, ULift.up j))

private theorem cellCoordinates_ext {R : Type u} [CommRing R] [Algebra k R]
    {φ ψ : CellCoordinates k n →ₐ[k] R}
    (h : ∀ i j, φ (cellMatrix k n i j) = ψ (cellMatrix k n i j)) : φ = ψ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (minorProduct k n))
  apply IsLocalization.algHom_ext (Submonoid.powers (genericMatrix k n).det)
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  exact h i.down j.down

private theorem evaluateCell {R : Type u} [CommRing R] [Algebra k R]
    (A : Matrix.GeneralLinearGroup (Fin n) R) (hA : HasUnitMinors A.val) :
    ∃! φ : CellCoordinates k n →ₐ[k] R, ∀ i j, φ (cellMatrix k n i j) = A.val i j := by
  let ev := evaluateGL (k := k) A
  have heval : ev.toRingHom.mapMatrix (glMatrix k n) = A.val :=
    Matrix.ext (evaluateGL_entry A)
  have hunit : IsUnit (ev (minorProduct k n)) := by
    rw [minorProduct, map_prod]
    exact isUnit_prod _ (fun i => by
      rw [show ev _ = _ from map_leadingMinor ev.toRingHom (glMatrix k n) _ _, heval]
      exact hA i.val (Nat.le_of_lt_succ i.isLt))
  let φ : CellCoordinates k n →ₐ[k] R := IsLocalization.Away.liftAlgHom _ hunit
  have hφ : ∀ i j, φ (cellMatrix k n i j) = A.val i j := by
    intro i j
    exact (IsLocalization.Away.lift_eq _ hunit _).trans (evaluateGL_entry A i j)
  exact ⟨φ, hφ, fun ψ hψ => cellCoordinates_ext (fun i j => (hψ i j).trans (hφ i j).symm)⟩

theorem regularOpenCell : RegularOpenCell.{u} := by
  intro k _ n
  refine ⟨by unfold cellInclusion; infer_instance,
    ?_, ?_⟩
  · exact congrArg SetLike.coe (Scheme.Hom.opensRange_localizationAway
      (R := CommRingCat.of (MatrixGroupCoordinates k n)) (minorProduct k n))
  · obtain ⟨f, hf, _⟩ := factor_exists_unique _ (cellMatrix_unitMinors k n)
    refine ⟨f, hf, ?_, fun R _ _ => ⟨⟨?_, ?_⟩, ?_, fun A => ⟨evaluateCell A, ?_⟩⟩⟩
    · intro R S _ _ _ _ φ ψ
      apply factors_ext
      · rfl
      · funext i
        apply Units.ext
        rfl
      · rfl
    · intro φ ψ h
      have hprod := congrArg Factors.product h
      rw [map_product, map_product, hf] at hprod
      exact cellCoordinates_ext (fun i j => congrFun (congrFun hprod i) j)
    · intro g
      have h := unitMinors_product g
      let A := Matrix.GeneralLinearGroup.mk'' g.product (by
        rw [← leading_full]
        exact h n le_rfl)
      obtain ⟨φ, hφ, _⟩ := evaluateCell (k := k) A h
      refine ⟨φ, ?_⟩
      have hmap : (f.map φ.toRingHom).product = g.product := by
        rw [map_product, hf]
        exact Matrix.ext hφ
      obtain ⟨_, _, huniq⟩ := factor_exists_unique _ h
      exact (huniq _ hmap).trans (huniq _ rfl).symm
    · intro φ
      rw [map_product, hf]
    · rintro ⟨φ, hφ, _⟩
      have hmap : φ.toRingHom.mapMatrix (cellMatrix k n) = A.val := Matrix.ext hφ
      rw [← hmap]
      exact map_hasUnitMinors φ.toRingHom (cellMatrix_unitMinors k n)

theorem standardGLComparison : StandardGLComparison.{u} := by
  intro k _ n
  exact ⟨AlgEquiv.refl, fun _ _ => rfl⟩

theorem zeroSize : ZeroSize.{u} := by
  intro k _
  constructor
  · have : IsOpenImmersion (cellInclusion k 0) := by unfold cellInclusion; infer_instance
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    have h : minorProduct k 0 = 1 := by simp [minorProduct, leading_zero]
    change (Spec.map (CommRingCat.ofHom
      (algebraMap (MatrixGroupCoordinates k 0) (CellCoordinates k 0)))).opensRange = ⊤
    rw [Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (MatrixGroupCoordinates k 0))
      (minorProduct k 0), h, PrimeSpectrum.basicOpen_one]
    rfl
  · let P := MvPolynomial (ULift.{u} (Fin 0) × ULift.{u} (Fin 0)) k
    have h : (genericMatrix k 0).det = 1 := Matrix.det_isEmpty
    have : IsLocalization.Away (1 : P) (MatrixGroupCoordinates k 0) :=
      h ▸ (inferInstance : IsLocalization.Away (genericMatrix k 0).det _)
    let e : P ≃ₐ[P] MatrixGroupCoordinates k 0 := IsLocalization.atOne P (MatrixGroupCoordinates k 0)
    exact ⟨(e.symm.restrictScalars k).trans (MvPolynomial.isEmptyAlgEquiv k _)⟩

end Coordinates

end

end LinearAlgebraicGroups.MatrixOpenCell
