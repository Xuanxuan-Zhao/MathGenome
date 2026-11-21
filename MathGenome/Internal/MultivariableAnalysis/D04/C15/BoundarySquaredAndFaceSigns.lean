import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.BoundarySquaredAndFaceSigns
import MathGenome.Internal.MultivariableAnalysis.D04.C15.CellsChainsAndIntegrals
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped BigOperators Classical
namespace D04.Cells

/-- Inserting two fixed coordinates commutes, with the indices shifted to
retain the increasing order of the free coordinates. -/
theorem faceInsertion_swap {k : ℕ} (i : Fin (k+2)) (j : Fin (k+1))
    (ε δ : Bool) (x : E k) :
    faceInsertion (i.succAbove j) δ (faceInsertion (j.predAbove i) ε x) =
      faceInsertion i ε (faceInsertion j δ x) := by
  apply PiLp.ext
  intro a
  refine Fin.succAboveCases i ?_ (fun b => ?_) a
  · have h := faceInsertion_other (i.succAbove j) δ
        (faceInsertion (j.predAbove i) ε x) (j.predAbove i)
    rw [Fin.succAbove_succAbove_predAbove] at h
    rw [h, faceInsertion_same, faceInsertion_same]
  · refine Fin.succAboveCases j ?_ (fun c => ?_) b
    · simp only [faceInsertion_same, faceInsertion_other]
    · have h := faceInsertion_other (i.succAbove j) δ
          (faceInsertion (j.predAbove i) ε x) ((j.predAbove i).succAbove c)
      rw [Fin.succAbove_succAbove_succAbove_predAbove] at h
      rw [h]
      simp only [faceInsertion_other]

theorem cellFace_swap {r k n} {O : Set (E n)} (c : Cell r (k+2) O)
    (i : Fin (k+2)) (j : Fin (k+1)) (ε δ : Bool) :
    cellFace (cellFace c (i.succAbove j) δ) (j.predAbove i) ε =
      cellFace (cellFace c i ε) j δ := by
  apply cell_ext
  intro x
  simp only [cellFace_apply]
  congr 1
  apply Subtype.ext
  exact faceInsertion_swap i j ε δ x

/-- The two orders of deleting coordinates have opposite alternating signs. -/
theorem face_pair_sign {k : ℕ} (i : Fin (k+2)) (j : Fin (k+1)) :
    (-1 : ℤ)^((i.succAbove j).val + (j.predAbove i).val) =
      -(-1 : ℤ)^(i.val + j.val) := by
  by_cases h : i ≤ j.castSucc
  · rw [Fin.succAbove_of_le_castSucc _ _ h,
      Fin.predAbove_of_le_castSucc _ _ h]
    simp only [Fin.val_succ, Fin.coe_castPred]
    rw [show j.val + 1 + i.val = (i.val + j.val) + 1 by omega, pow_succ]
    ring
  · have h' : j.castSucc < i := lt_of_not_ge h
    rw [Fin.succAbove_of_castSucc_lt _ _ h',
      Fin.predAbove_of_castSucc_lt _ _ h']
    simp only [Fin.val_castSucc, Fin.val_pred]
    have hi : 0 < i.val := by have := Fin.isLt j; change j.val < i.val at h'; omega
    have he : i.val + j.val = (j.val + (i.val - 1)) + 1 := by omega
    rw [he, pow_succ]
    ring

/-- Cancellation on the ordered pairs of omitted coordinates. -/
theorem sum_face_pairs {k : ℕ} {G : Type*} [AddCommGroup G]
    (f : Fin (k+2) → Fin (k+1) → G)
    (hf : ∀ i j, f (i.succAbove j) (j.predAbove i) = -f i j) :
    ∑ i, ∑ j, f i j = 0 := by
  rw [← Fintype.sum_prod_type (fun p : Fin (k+2) × Fin (k+1) => f p.1 p.2)]
  apply Finset.sum_involution
    (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1))
  · intro p _
    exact (hf p.1 p.2).symm ▸ add_neg_cancel (f p.1 p.2)
  · intro p _ _ he
    have hh := congrArg Prod.fst he
    exact Fin.succAbove_ne p.1 p.2 hh
  · intro p _
    apply Prod.ext
    · exact Fin.succAbove_succAbove_predAbove p.1 p.2
    · exact Fin.predAbove_predAbove_succAbove p.1 p.2
  · intro p hp
    exact Finset.mem_univ (p.1.succAbove p.2, p.2.predAbove p.1)

/-- Boundary of boundary of a generator in degree at least two. -/
theorem cellBoundary_boundary {r k n} {O : Set (E n)} (c : Cell r (k+2) O) :
    chainBoundarySucc (cellBoundary c) = 0 := by
  let F (i : Fin (k+2)) (j : Fin (k+1)) : Chain r k O :=
    Finsupp.single (cellFace (cellFace c i true) j true) 1 -
    Finsupp.single (cellFace (cellFace c i true) j false) 1 -
    (Finsupp.single (cellFace (cellFace c i false) j true) 1 -
    Finsupp.single (cellFace (cellFace c i false) j false) 1)
  have hF : ∀ i j, F (i.succAbove j) (j.predAbove i) = F i j := by
    intro i j
    dsimp [F]
    simp only [cellFace_swap]
    abel
  have hc : chainBoundarySucc (cellBoundary c) =
      ∑ i, ∑ j, (-1 : ℤ)^(i.val+j.val) • F i j := by
    unfold cellBoundary Specs.D04.C15.CellsChainsAndIntegrals.Model.cellBoundary
    simp only [map_sum, map_zsmul, map_sub, boundary_single, one_smul]
    simp only [cellBoundary, Specs.D04.C15.CellsChainsAndIntegrals.Model.cellBoundary,
      Finset.smul_sum, ← Finset.sum_sub_distrib, ← smul_sub, smul_smul, ← pow_add]
    rfl
  rw [hc]
  apply sum_face_pairs
  intro i j
  rw [face_pair_sign, hF, neg_smul]

theorem chainBoundarySucc_squared {r k n} {O : Set (E n)} (C : Chain r (k+2) O) :
    chainBoundarySucc (chainBoundarySucc C) = 0 := by
  induction C using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add C D hC hD => simp only [map_add, hC, hD, add_zero]
  | single c a => rw [boundary_single, map_zsmul, cellBoundary_boundary, smul_zero]

/-- The square vanishes in every nonnegative degree; in degrees zero and
one this uses the stipulated zero boundary on zero-chains. -/
theorem chainBoundary_squared {r n} {O : Set (E n)} (k : ℕ) (C : Chain r k O) :
    chainBoundary (k-1) (chainBoundary k C) = 0 := by
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k => exact chainBoundarySucc_squared C

/-- In degree one the entire boundary consists of a terminal point minus
an initial point, with integer coefficients +1 and -1. -/
theorem cellBoundary_one {r n} {O : Set (E n)} (c : Cell r 1 O) :
    cellBoundary c = Finsupp.single (cellFace c 0 true) 1 -
      Finsupp.single (cellFace c 0 false) 1 := by
  simp [cellBoundary, Specs.D04.C15.CellsChainsAndIntegrals.Model.cellBoundary]

private def faceLinear {k : ℕ} (i : Fin (k+1)) : E k →ₗ[ℝ] E (k+1) where
  toFun := faceInsertion i false
  map_add' x y := by
    apply PiLp.ext
    intro a
    refine Fin.succAboveCases i ?_ (fun j => ?_) a <;>
      simp only [PiLp.add_apply, faceInsertion_same, faceInsertion_other, Bool.false_eq_true,
        ↓reduceIte, add_zero]
  map_smul' t x := by
    apply PiLp.ext
    intro a
    refine Fin.succAboveCases i ?_ (fun j => ?_) a <;>
      simp only [PiLp.smul_apply, faceInsertion_same, faceInsertion_other, Bool.false_eq_true,
        ↓reduceIte, smul_zero, RingHom.id_apply]

private theorem face_affine {k : ℕ} (i : Fin (k+1)) (ε : Bool) :
    faceInsertion i ε = fun x => faceLinear i x +
      (if ε then standardBasis (k+1) i else 0) := by
  funext x
  apply PiLp.ext
  intro a
  refine Fin.succAboveCases i ?_ (fun j => ?_) a
  · cases ε <;> simp [faceLinear, faceInsertion_same, standardBasis,
      EuclideanSpace.basisFun_apply]
  · cases ε <;> simp [faceLinear, faceInsertion_other, standardBasis,
      EuclideanSpace.basisFun_apply, Fin.succAbove_ne]

theorem faceInsertion_derivative {k : ℕ} (i : Fin (k+1)) (ε : Bool)
    (x : E k) (j : Fin k) :
    totalDerivative (faceInsertion i ε) x (standardBasis k j) =
      standardBasis (k+1) (i.succAbove j) := by
  have hd := ((faceLinear i).toContinuousLinearMap.hasFDerivAt (x := x)).add_const
    (if ε then standardBasis (k+1) i else 0)
  change HasFDerivAt (fun y => faceLinear i y +
    (if ε then standardBasis (k+1) i else 0)) _ x at hd
  rw [← face_affine] at hd
  change (fderiv ℝ (faceInsertion i ε) x) _ = _
  rw [hd.fderiv]
  change faceInsertion i false (standardBasis k j) = _
  apply PiLp.ext
  intro a
  refine Fin.succAboveCases i ?_ (fun l => ?_) a <;>
    simp [faceInsertion_same, faceInsertion_other, standardBasis,
      EuclideanSpace.basisFun_apply,
      PiLp.single_apply, Fin.succAbove_inj, eq_comm]

/-- The determinant of the ordered coordinate frame with the i-th vector
moved to the front and scaled by t. -/
theorem coordinate_front_determinant {k : ℕ} (i : Fin (k+1)) (t : ℝ) :
    (standardBasis (k+1)).det
      (Fin.cons (t • standardBasis (k+1) i)
        (fun j : Fin k => standardBasis (k+1) (i.succAbove j))) =
      (-1 : ℝ)^i.val * t := by
  let B := standardBasis (k+1)
  let V : Fin (k+1) → E (k+1) :=
    Fin.cons (t • B i) (fun j : Fin k => B (i.succAbove j))
  change B.det V = _
  rw [Module.Basis.det_apply, Matrix.det_succ_row _ i]
  have hz : ∀ j : Fin k, B.repr (V j.succ) i = 0 := by
    intro j
    simp [V]
  have hm : (B.toMatrix V).submatrix i.succAbove (0 : Fin (k+1)).succAbove = 1 := by
    ext a b
    simp [Module.Basis.toMatrix_apply, V, Fin.succAbove_zero,
      Matrix.one_apply, Finsupp.single_apply, eq_comm]
  rw [Fin.sum_univ_succ]
  simp only [Module.Basis.toMatrix_apply, hz, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  rw [hm]
  simp [V]

theorem cube_face_determinant {k : ℕ} (i : Fin (k+1)) (ε : Bool) (x : E k) :
    (standardBasis (k+1)).det
      (Fin.cons (if ε then standardBasis (k+1) i else -standardBasis (k+1) i)
        (fun j : Fin k => totalDerivative (faceInsertion i ε) x (standardBasis k j))) =
      if ε then (-1 : ℝ)^i.val else -(-1 : ℝ)^i.val := by
  simp only [faceInsertion_derivative]
  cases ε
  · simpa using coordinate_front_determinant i (-1)
  · simpa using coordinate_front_determinant i 1

theorem cube_face_signs : Specs.D04.C15.BoundarySquaredAndFaceSigns.cube_face_signsType := by
  intro k i ε x
  change
    let d := (standardBasis (k+1)).det
      (Fin.cons (if ε then standardBasis (k+1) i else -standardBasis (k+1) i)
        (fun j : Fin k => totalDerivative (faceInsertion i ε) x (standardBasis k j)))
    let s := if ε then (-1 : ℝ)^i.val else -(-1 : ℝ)^i.val
    d = s ∧ Real.sign d = s
  dsimp only
  rw [cube_face_determinant]
  refine ⟨rfl, ?_⟩
  rcases neg_one_pow_eq_or ℝ i.val with h | h <;> rw [h] <;>
    cases ε <;> norm_num [Real.sign_of_neg]

theorem cube_face_normal : Specs.D04.C15.BoundarySquaredAndFaceSigns.cube_face_normalType := by
  intro k i ε x hx
  change
    let ν := if ε then standardBasis (k+1) i else -standardBasis (k+1) i
    ‖ν‖ = 1 ∧
    (∀ w : E (k+1), w i = 0 → inner ℝ ν w = 0) ∧
    ∀ t : ℝ, 0 < t → faceInsertion i ε x + t • ν ∉ cube (k+1)
  dsimp only
  have hn : ‖standardBasis (k+1) i‖ = 1 := by
    simp [standardBasis, EuclideanSpace.basisFun_apply]
  have hi (w : E (k+1)) : inner ℝ (standardBasis (k+1) i) w = w i := by
    simp [standardBasis, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  have hb : standardBasis (k+1) i i = 1 := by
    simp [standardBasis, EuclideanSpace.basisFun_apply]
  cases ε
  · refine ⟨by simpa using hn, ?_, ?_⟩
    · intro w hw
      simp [inner_neg_left, hi, hw]
    · intro t ht hmem
      have hh := (mem_cube _).mp hmem i
      simp only [PiLp.add_apply, PiLp.smul_apply, faceInsertion_same,
        Bool.false_eq_true, ↓reduceIte, PiLp.neg_apply, hb, smul_eq_mul] at hh
      linarith [hh.1]
  · refine ⟨hn, ?_, ?_⟩
    · intro w hw
      simpa only [↓reduceIte, hi] using hw
    · intro t ht hmem
      have hh := (mem_cube _).mp hmem i
      simp only [PiLp.add_apply, PiLp.smul_apply, faceInsertion_same,
        ↓reduceIte, hb, smul_eq_mul] at hh
      linarith [hh.2]

end D04.Cells
