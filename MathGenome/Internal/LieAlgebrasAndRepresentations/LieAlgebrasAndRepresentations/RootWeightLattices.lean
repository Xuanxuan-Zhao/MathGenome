import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootWeightLattices
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.DominantFundamentalDomain
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanMatrix
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClassicalCoordinateRoots
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ExceptionalCoordinateGF
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Batteries.Tactic.OpenPrivate

/-! res:E07. Integral duality is computed using the simple coroot basis.
The index uses the integer-basis determinant theorem and positive Cartan
symmetrization. Coordinate Cartan matrices are compared entry by entry with
the library matrices; the classical families are computed by path recurrences.
-/
noncomputable section
namespace LieAlgebrasAndRepresentations
open Set Module
open LinearMap.BilinForm
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*}

lemma inner_coroot (x a : E) : inner ℝ x (coroot a) = rootCartan x a := by
  simp only [coroot, real_inner_smul_right, rootCartan]
  ring

lemma mem_dual_span_iff (f : ι → E) (x : E) :
    x ∈ dualSubmodule (innerₗ E) (Submodule.span ℤ (Set.range f)) ↔
      ∀ i, ∃ z : ℤ, inner ℝ x (f i) = (z : ℝ) := by
  constructor
  · intro hx i
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp (hx (f i) (Submodule.subset_span ⟨i, rfl⟩))
    exact ⟨z, hz.symm⟩
  · intro hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨z, hz⟩ := hx i
      exact Submodule.mem_one.mpr ⟨z, hz.symm⟩
    | zero => simp
    | add y z hy hz ihy ihz => simpa only [map_add] using add_mem ihy ihz
    | smul z y hy ih =>
      simpa using (1 : Submodule ℤ ℝ).smul_mem z ih

lemma weightLattice_mem_iff (b : Basis ι ℝ E) (x : E) :
    x ∈ weightLattice b ↔ ∀ i, ∃ z : ℤ, inner ℝ x (coroot (b i)) = (z : ℝ) := by
  simpa only [weightLattice, corootLattice, simpleCorootBasis_apply] using
    mem_dual_span_iff (simpleCorootBasis b) x

/-- Both lattice inclusions follow from the original crystallographic axiom. -/
theorem root_coweight_lattice_inclusions : RootWeightLatticeSpecs.inclusionsType := by
  intro E _ _ ι R hR v hv b hb
  constructor
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (weightLattice_mem_iff b (b i)).mpr
    intro j
    simpa only [inner_coroot, rootCartan] using
      hR.integral (b j) (hb.root_mem j) (b i) (hb.root_mem i)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply (mem_dual_span_iff b (simpleCorootBasis b i)).mpr
    intro j
    rw [simpleCorootBasis_apply, real_inner_comm, inner_coroot]
    exact hR.integral (b i) (hb.root_mem i) (b j) (hb.root_mem j)

lemma fundamentalWeights_repr [Finite ι] [DecidableEq ι] (b : Basis ι ℝ E) (x : E) (i : ι) :
    (fundamentalWeights b).repr x i = inner ℝ x (coroot (b i)) := by
  exact (dualBasis_repr_apply euclideanPairing_nondegenerate (simpleCorootBasis b) x i).trans
    (by rw [simpleCorootBasis_apply]; rfl)

theorem fundamental_weights_pairing : RootWeightLatticeSpecs.fundamentalPairingType := by
  intro E _ _ ι _ _ b
  have hp : ∀ i j, inner ℝ (fundamentalWeights b i) (coroot (b j)) =
      if i = j then 1 else 0 := by
    intro i j
    rw [← fundamentalWeights_repr, Basis.repr_self, Finsupp.single_apply]
  refine ⟨hp, ?_⟩
  intro i x hx
  apply (fundamentalWeights b).repr.injective
  ext j
  rw [fundamentalWeights_repr, fundamentalWeights_repr, hp, hx]

lemma weightLattice_eq_span [Finite ι] [DecidableEq ι] (b : Basis ι ℝ E) :
    weightLattice b = Submodule.span ℤ (Set.range (fundamentalWeights b)) :=
  dualSubmodule_span_of_basis (innerₗ E) euclideanPairing_nondegenerate (simpleCorootBasis b)

/-- The fundamental weights as a genuine integer basis of the dual lattice. -/
def weightLatticeBasis [Finite ι] [DecidableEq ι] (b : Basis ι ℝ E) :
    Basis ι ℤ (weightLattice b) :=
  ((fundamentalWeights b).restrictScalars ℤ).map
    (LinearEquiv.ofEq _ _ (weightLattice_eq_span b).symm)

@[simp] lemma weightLatticeBasis_apply [Finite ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (i : ι) :
    (weightLatticeBasis b i : E) = fundamentalWeights b i := by
  simp [weightLatticeBasis]

theorem fundamental_weights_integer_basis : RootWeightLatticeSpecs.weightBasisType := by
  intro E _ _ ι _ _ b
  exact ⟨weightLatticeBasis b, weightLatticeBasis_apply b⟩

/-- This reuses the upstream theorem on all real orbit points, including walls. -/
theorem weight_real_orbit_dominant : RootWeightLatticeSpecs.orbitType :=
  weyl_closed_chamber_fundamental_domain

theorem cartan_rank_zero_det : RootWeightLatticeSpecs.rankZeroType := by
  intro E _ _ ι _ _ _ b
  exact Matrix.det_isEmpty

lemma weightLatticeBasis_repr [Finite ι] [DecidableEq ι]
    (b : Basis ι ℝ E) (x : weightLattice b) (i : ι) :
    ((weightLatticeBasis b).repr x i : ℝ) = inner ℝ (x : E) (coroot (b i)) := by
  change algebraMap ℤ ℝ
    (((fundamentalWeights b).restrictScalars ℤ).repr
      ((LinearEquiv.ofEq _ _ (weightLattice_eq_span b).symm).symm x) i) = _
  rw [Basis.restrictScalars_repr_apply, fundamentalWeights_repr]
  rfl

lemma closedSimpleChamber_iff_coords [Finite ι] [DecidableEq ι]
    {R : Set E} {v : E} (b : Basis ι ℝ E) (hb : IsSimpleBasis R v b) (x : E) :
    x ∈ closedSimpleChamber R v ↔ ∀ i, 0 ≤ (fundamentalWeights b).repr x i := by
  have hi (i : ι) : 0 < 2 / inner ℝ (b i) (b i) :=
    div_pos two_pos (real_inner_self_pos.mpr (b.ne_zero i))
  constructor
  · intro hx i
    rw [fundamentalWeights_repr, coroot, real_inner_smul_right]
    exact mul_nonneg (hi i).le (hx (b i) (hb.mem i))
  · intro hx a ha
    obtain ⟨i, rfl⟩ := hb.symm ▸ ha
    have h := hx i
    rw [fundamentalWeights_repr, coroot, real_inner_smul_right] at h
    exact (mul_nonneg_iff_of_pos_left (hi i)).mp h

/-- Dominance is exactly nonnegativity of the integral dual-basis coordinates. -/
theorem dominant_integral_weights : RootWeightLatticeSpecs.dominantType := by
  intro E _ _ ι _ _ R hR v hv b hb x
  constructor
  · rintro ⟨hx, hd⟩
    let c : ι → ℤ := fun i => (weightLatticeBasis b).repr ⟨x, hx⟩ i
    have hc (i : ι) : (c i : ℝ) = (fundamentalWeights b).repr x i := by
      rw [fundamentalWeights_repr]
      exact weightLatticeBasis_repr b ⟨x, hx⟩ i
    have hn (i : ι) : 0 ≤ c i := by
      exact_mod_cast ((hc i).symm ▸ (closedSimpleChamber_iff_coords b hb x).mp hd i)
    refine ⟨fun i => (c i).toNat, ?_⟩
    conv_lhs => rw [← (fundamentalWeights b).sum_repr x]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hc i]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg (hn i)).symm
  · rintro ⟨n, rfl⟩
    have hcoords (i : ι) :
        (fundamentalWeights b).repr (∑ j, (n j : ℝ) • fundamentalWeights b j) i = (n i : ℝ) := by
      simp [Finsupp.single_apply, Finset.sum_ite_eq']
    constructor
    · apply (weightLattice_mem_iff b _).mpr
      intro i
      refine ⟨(n i : ℤ), ?_⟩
      rw [← fundamentalWeights_repr, hcoords]
      norm_cast
    · apply (closedSimpleChamber_iff_coords b hb _).mpr
      intro i
      rw [hcoords]
      positivity

lemma simple_cartan_det_pos [Fintype ι] [DecidableEq ι]
    {R : Set E} (hR : IsRootSystem R) {v : E} (hv : RootRegular R v)
    (b : Basis ι ℝ E) (hb : IsSimpleBasis R v b) : 0 < (cartanMatrix b).det := by
  have hp := (cartan_symmetrization R hR v hv b hb).2.2.det_pos
  rw [Matrix.det_mul, Matrix.det_diagonal] at hp
  have hd : 0 < ∏ i, inner ℝ (b i) (b i) :=
    Finset.prod_pos (fun i _ => real_inner_self_pos.mpr (b.ne_zero i))
  nlinarith

set_option backward.isDefEq.respectTransparency false in
/-- The index is the positive determinant, via the two actual integer bases. -/
theorem weight_root_lattice_index : RootWeightLatticeSpecs.indexType := by
  intro E _ _ ι _ _ R hR v hv b hb
  have hQP := (root_coweight_lattice_inclusions R hR v hv b hb).1
  let bQ : Basis ι ℤ (rootLattice b) := b.restrictScalars ℤ
  let bP := weightLatticeBasis b
  let a : ι → weightLattice b := fun i => ⟨b i, hQP (Submodule.subset_span ⟨i, rfl⟩)⟩
  have hi := AddSubgroup.relIndex_eq_natAbs_det
    (rootLattice b).toAddSubgroup (weightLattice b).toAddSubgroup hQP bQ bP
  have hmatrix : (bP.toMatrix a).map (Int.castRingHom ℝ) = cartanMatrix b := by
    ext i j
    change ((bP.repr (a j) i : ℤ) : ℝ) = _
    rw [weightLatticeBasis_repr]
    exact inner_coroot (b j) (b i)
  have hdet : (bP.det a : ℝ) = (cartanMatrix b).det := by
    rw [Basis.det_apply]
    change (Int.castRingHom ℝ) (bP.toMatrix a).det = _
    rw [RingHom.map_det]
    exact congrArg Matrix.det hmatrix
  have hi' : (rootLattice b).toAddSubgroup.relIndex (weightLattice b).toAddSubgroup =
      (bP.det a).natAbs := by
    convert hi using 2
    congr 2
    funext i
    apply Subtype.ext
    exact (Basis.restrictScalars_apply ℤ b i).symm
  rw [hi', Nat.cast_natAbs, Int.cast_abs, hdet, abs_of_pos (simple_cartan_det_pos hR hv b hb)]

namespace RootWeightLatticeCalculations
set_option maxHeartbeats 2000000
open Matrix
open private extendPath extendPath_det extendPath_tail from Mathlib.LinearAlgebra.Matrix.Cartan.Basic

lemma pathA_succ (n : ℕ) : CartanMatrix.A (n + 1) = extendPath (CartanMatrix.A n) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => Fin.lastCases ?_ (fun j => ?_) j) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [CartanMatrix.A, extendPath]
    · simp only [CartanMatrix.A, of_apply, extendPath, Fin.lastCases_last,
        Fin.lastCases_castSucc, Fin.val_last, Fin.val_castSucc]
      split_ifs <;> simp_all [Fin.ext_iff, Fin.val_rev, Fin.val_castSucc, Fin.val_last] <;> omega
  · simp only [CartanMatrix.A, of_apply, extendPath, Fin.lastCases_last,
      Fin.lastCases_castSucc, Fin.val_last, Fin.val_castSucc]
    split_ifs <;> simp_all [Fin.ext_iff, Fin.val_rev, Fin.val_castSucc, Fin.val_last] <;> omega
  · simp [CartanMatrix.A, extendPath]

lemma pathA_recurrence (n : ℕ) : (CartanMatrix.A (n+2)).det =
    2 * (CartanMatrix.A (n+1)).det - (CartanMatrix.A n).det := by
  rw [pathA_succ (n+1), extendPath_det, pathA_succ n, extendPath_tail]

lemma pathA_det (n : ℕ) : (CartanMatrix.A n).det = (n : ℤ) + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Matrix.det_isEmpty]
  | one => decide
  | more n hn hn1 => rw [pathA_recurrence, hn, hn1]; push_cast; ring

def reverseB (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  (CartanMatrix.B n).submatrix Fin.rev Fin.rev

def reverseD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  (CartanMatrix.D n).submatrix Fin.rev Fin.rev

lemma reverseB_succ (n : ℕ) (hn : 2 ≤ n) : reverseB (n+1) = extendPath (reverseB n) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => Fin.lastCases ?_ (fun j => ?_) j) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [reverseB, CartanMatrix.B, extendPath]
    · simp only [reverseB, CartanMatrix.B, submatrix_apply, of_apply, extendPath,
        Fin.lastCases_last, Fin.lastCases_castSucc, Fin.val_last, Fin.val_castSucc, Fin.val_rev]
      split_ifs <;> simp_all [Fin.ext_iff, Fin.val_rev, Fin.val_castSucc, Fin.val_last] <;> omega
  · simp only [reverseB, CartanMatrix.B, submatrix_apply, of_apply, extendPath,
      Fin.lastCases_last, Fin.lastCases_castSucc, Fin.val_last, Fin.val_castSucc, Fin.val_rev]
    split_ifs <;> simp_all [Fin.ext_iff, Fin.val_rev, Fin.val_castSucc, Fin.val_last] <;> omega
  · simp only [reverseB, CartanMatrix.B, submatrix_apply, of_apply, extendPath,
      Fin.lastCases_castSucc, Fin.val_castSucc, Fin.val_rev, Fin.rev_inj]
    split_ifs <;> simp_all [Fin.ext_iff, Fin.val_rev, Fin.val_castSucc, Fin.val_last] <;> omega

lemma reverseD_succ (n : ℕ) (hn : 3 ≤ n) : reverseD (n+1) = extendPath (reverseD n) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => Fin.lastCases ?_ (fun j => ?_) j) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [reverseD, CartanMatrix.D, extendPath]
    · simp only [reverseD, CartanMatrix.D, submatrix_apply, of_apply, extendPath,
        Fin.lastCases_last, Fin.lastCases_castSucc, Fin.val_last, Fin.val_castSucc, Fin.val_rev]
      split_ifs <;> simp_all [Fin.ext_iff, Fin.val_rev, Fin.val_castSucc, Fin.val_last] <;> omega
  · simp only [reverseD, CartanMatrix.D, submatrix_apply, of_apply, extendPath,
      Fin.lastCases_last, Fin.lastCases_castSucc, Fin.val_last, Fin.val_castSucc, Fin.val_rev]
    split_ifs <;> simp_all [Fin.ext_iff, Fin.val_rev, Fin.val_castSucc, Fin.val_last] <;> omega
  · simp only [reverseD, CartanMatrix.D, submatrix_apply, of_apply, extendPath,
      Fin.lastCases_castSucc, Fin.val_castSucc, Fin.val_rev, Fin.rev_inj]
    split_ifs <;> simp_all [Fin.ext_iff, Fin.val_rev, Fin.val_castSucc, Fin.val_last] <;> omega

lemma reverseB_det_eq (n : ℕ) : (reverseB n).det = (CartanMatrix.B n).det :=
  Matrix.det_submatrix_equiv_self Fin.revPerm _

lemma reverseD_det_eq (n : ℕ) : (reverseD n).det = (CartanMatrix.D n).det :=
  Matrix.det_submatrix_equiv_self Fin.revPerm _

lemma pathB_recurrence (n : ℕ) (hn : 1 ≤ n) : (reverseB (n+2)).det =
    2 * (reverseB (n+1)).det - (reverseB n).det := by
  by_cases he : n = 1
  · subst n; decide
  rw [reverseB_succ (n+1) (by omega), extendPath_det,
    reverseB_succ n (by omega), extendPath_tail]

lemma pathD_recurrence (n : ℕ) (hn : 3 ≤ n) : (reverseD (n+2)).det =
    2 * (reverseD (n+1)).det - (reverseD n).det := by
  rw [reverseD_succ (n+1) (by omega), extendPath_det,
    reverseD_succ n hn, extendPath_tail]

lemma pathB_det (n : ℕ) (hn : 1 ≤ n) : (CartanMatrix.B n).det = 2 := by
  suffices ∀ k, (reverseB (k+1)).det = 2 by
    rw [← reverseB_det_eq n]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
    have he : n = k + 1 := by omega
    clear hk
    subst n
    exact this k
  intro k
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k hk hk1 =>
    rw [show k+2+1 = (k+1)+2 by omega, pathB_recurrence (k+1) (by omega), hk1, hk]
    norm_num

lemma pathD_det (n : ℕ) (hn : 3 ≤ n) : (CartanMatrix.D n).det = 4 := by
  suffices ∀ k, (reverseD (k+3)).det = 4 by
    rw [← reverseD_det_eq n]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
    have he : n = k + 3 := by omega
    clear hk
    subst n
    exact this k
  intro k
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k hk hk1 =>
    rw [show k+2+3 = (k+3)+2 by omega, pathD_recurrence (k+3) (by omega), hk1, hk]
    norm_num

lemma pathC_transpose (n : ℕ) : (CartanMatrix.C n) = (CartanMatrix.B n).transpose := by
  ext i j
  simp only [CartanMatrix.B, CartanMatrix.C, Matrix.of_apply, Matrix.transpose_apply]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

lemma pathC_det (n : ℕ) (hn : 1 ≤ n) : (CartanMatrix.C n).det = 2 := by
  rw [pathC_transpose, Matrix.det_transpose, pathB_det n hn]


open ClassicalCoordinates Matrix

lemma coordinateA_cartan (n : ℕ) : cartanMatrix (simpleA n) =
    (CartanMatrix.A n).map (Int.castRingHom ℝ) := by
  ext i j
  rw [simpleA_cartan]
  simp only [CartanMatrix.A, Matrix.of_apply, adjacent]
  split_ifs <;> norm_num <;> simp_all

lemma coordinateB_cartan (n : ℕ) : cartanMatrix (simpleB n) =
    (CartanMatrix.C n).map (Int.castRingHom ℝ) := by
  ext i j
  change cartanMatrix (simpleB n) i j = ((CartanMatrix.C n i j : ℤ) : ℝ)
  simp only [cartanMatrix, rootCartan, simpleB_gram, ite_true, CartanMatrix.C,
    Matrix.of_apply, adjacent]
  simp only [Int.cast_ite, Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Fin.ext_iff]
  grind

lemma coordinateC_cartan (n : ℕ) : cartanMatrix (simpleC n) =
    (CartanMatrix.B n).map (Int.castRingHom ℝ) := by
  ext i j
  change cartanMatrix (simpleC n) i j = ((CartanMatrix.B n i j : ℤ) : ℝ)
  simp only [cartanMatrix, rootCartan, simpleC_gram, ite_true, CartanMatrix.B,
    Matrix.of_apply, adjacent, terminalEdge]
  simp only [Int.cast_ite, Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Fin.ext_iff]
  grind

lemma coordinateD_cartan (n : ℕ) (hn : 4 ≤ n) : cartanMatrix (simpleD n) =
    (CartanMatrix.D n).map (Int.castRingHom ℝ) := by
  ext i j
  change cartanMatrix (simpleD n) i j = ((CartanMatrix.D n i j : ℤ) : ℝ)
  simp only [cartanMatrix, rootCartan, simpleD_gram hn, ite_true, CartanMatrix.D,
    Matrix.of_apply, forkAdjacent]
  simp only [Int.cast_ite, Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Fin.ext_iff]
  grind

lemma coordinateE8_cartan : cartanMatrix ExceptionalE.e8Simple =
    (CartanMatrix.E 8).map (Int.castRingHom ℝ) := by
  ext i j
  change 2 * inner ℝ (ExceptionalGF.realize (ExceptionalE.simpleQ j))
    (ExceptionalGF.realize (ExceptionalE.simpleQ i)) /
    inner ℝ (ExceptionalGF.realize (ExceptionalE.simpleQ i))
      (ExceptionalGF.realize (ExceptionalE.simpleQ i)) = _
  rw [ExceptionalGF.realize_inner, ExceptionalGF.realize_inner]
  fin_cases i <;> fin_cases j <;>
    norm_num [ExceptionalGF.dot, ExceptionalE.simpleQ, CartanMatrix.E, Fin.sum_univ_succ]

lemma coordinateE7_cartan : cartanMatrix ExceptionalE.e7Simple =
    (CartanMatrix.E 7).map (Int.castRingHom ℝ) := by
  ext i j
  change cartanMatrix ExceptionalE.e8Simple i.castSucc j.castSucc = _
  rw [coordinateE8_cartan]
  simp only [Matrix.map_apply, CartanMatrix.E, Matrix.of_apply, Fin.castSucc_inj, Fin.val_castSucc]

lemma coordinateE6_cartan : cartanMatrix ExceptionalE.e6Simple =
    (CartanMatrix.E 6).map (Int.castRingHom ℝ) := by
  ext i j
  change cartanMatrix ExceptionalE.e8Simple (i.castLE (by decide)) (j.castLE (by decide)) = _
  rw [coordinateE8_cartan]
  simp only [Matrix.map_apply, CartanMatrix.E, Matrix.of_apply, Fin.castLE_inj, Fin.val_castLE]

lemma coordinateG2_det : (cartanMatrix ExceptionalGF.g2Simple).det = 1 := by
  rw [ExceptionalGF.g2_diagram.1, Matrix.det_fin_two]
  norm_num

lemma coordinateF4_cartan : cartanMatrix ExceptionalGF.f4Simple =
    (CartanMatrix.F₄.transpose).map (Int.castRingHom ℝ) := by
  rw [ExceptionalGF.f4_diagram.1]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [CartanMatrix.F₄, Matrix.transpose_apply]

lemma cast_matrix_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    (M.map (Int.castRingHom ℝ)).det = (M.det : ℝ) :=
  ((Int.castRingHom ℝ).map_det M).symm

end RootWeightLatticeCalculations
open RootWeightLatticeCalculations

/-- Determinants for the original coordinate models, in their source rank ranges. -/
theorem classical_cartan_determinants : RootWeightLatticeSpecs.classicalDeterminantsType := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [coordinateA_cartan, cast_matrix_det, pathA_det]
    norm_cast
  · intro n hn
    rw [coordinateB_cartan, cast_matrix_det, pathC_det n (by omega)]
    norm_num
  · intro n hn
    rw [coordinateC_cartan, cast_matrix_det, pathB_det n (by omega)]
    norm_num
  · intro n hn
    rw [coordinateD_cartan n hn, cast_matrix_det, pathD_det n (by omega)]
    norm_num

/-- The exceptional values use the actual displayed simple vectors. -/
theorem exceptional_cartan_determinants : RootWeightLatticeSpecs.exceptionalDeterminantsType := by
  refine ⟨?_, ?_, ?_, ?_, coordinateG2_det⟩
  · rw [coordinateE6_cartan, cast_matrix_det, CartanMatrix.E₆_det]
    norm_num
  · rw [coordinateE7_cartan, cast_matrix_det, CartanMatrix.E₇_det]
    norm_num
  · rw [coordinateE8_cartan, cast_matrix_det, CartanMatrix.E₈_det]
    norm_num
  · rw [coordinateF4_cartan, cast_matrix_det, Matrix.det_transpose, CartanMatrix.F₄_det]
    norm_num

end LieAlgebrasAndRepresentations
