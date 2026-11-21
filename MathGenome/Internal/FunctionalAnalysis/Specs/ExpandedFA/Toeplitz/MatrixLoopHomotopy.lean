import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Covering.FundamentalGroupCircle
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

/-! Interfaces for the matrix-loop classification in paper.tex, lines 10460–10520.
The circle has its usual positive orientation. The parameter `n` below represents
matrix dimension `n + 1`, so the statements include every positive dimension.
No homotopy or lifting certificate is an input to `Classification`. -/

noncomputable section
open scoped unitInterval
open unitInterval
open Matrix

namespace ExpandedFA.Toeplitz.MatrixLoops

abbrev MatrixGroup (n : ℕ) := Matrix.GeneralLinearGroup (Fin (n + 1)) ℂ

/-- The native unitary matrix group in dimension `n + 1`. -/
abbrev UnitaryMatrixGroup (n : ℕ) :=
  unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)

/-- A unit column, with its usual Euclidean topology and norm. -/
abbrev UnitColumn (n : ℕ) := {v : EuclideanSpace ℂ (Fin (n + 1)) | ‖v‖ = 1}

/-- Include a unitary matrix, with its adjoint inverse, into the invertible matrices. -/
def unitaryEmbedding (n : ℕ) : C(UnitaryMatrixGroup n, MatrixGroup n) where
  toFun := Unitary.toUnits
  continuous_toFun := Units.continuous_iff.mpr
    ⟨continuous_subtype_val, continuous_subtype_val.star⟩

def matrixColumn (n : ℕ) (j : Fin (n+1))
    (U : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) : EuclideanSpace ℂ (Fin (n+1)) :=
  WithLp.toLp 2 (fun i => U i j)

lemma unitary_column_norm (n : ℕ) (j : Fin (n+1)) (U : UnitaryMatrixGroup n) :
    ‖matrixColumn n j U.val‖ = 1 := by
  have hu : U.valᴴ * U.val = 1 := (Unitary.mem_iff.mp U.property).1
  have hi : inner ℂ (matrixColumn n j U.val) (matrixColumn n j U.val) = 1 := by
    change inner ℂ (WithLp.toLp 2 (U.valᵀ j)) (WithLp.toLp 2 (U.valᵀ j)) = 1
    rw [inner_matrix_col_col, hu, Matrix.one_apply_eq]
  rw [inner_self_eq_norm_sq_to_K] at hi
  have hr : ‖matrixColumn n j U.val‖ ^ 2 = 1 := by
    apply @RCLike.ofReal_injective ℂ
    simpa only [RCLike.ofReal_pow, RCLike.ofReal_one] using hi
  nlinarith [norm_nonneg (matrixColumn n j U.val)]

def unitaryColumn (n : ℕ) (j : Fin (n+1)) : C(UnitaryMatrixGroup n, UnitColumn n) where
  toFun U := ⟨matrixColumn n j U.val, unitary_column_norm n j U⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
      continuous_subtype_val.matrix_elem i j)

def standardColumn (n : ℕ) (j : Fin (n+1)) : UnitColumn n :=
  ⟨EuclideanSpace.single j 1, by
    simpa [EuclideanSpace.single] using
      (PiLp.norm_single 2 (fun _ : Fin (n+1) => ℂ) j (1 : ℂ))⟩

@[simp] lemma unitaryColumn_apply (n : ℕ) (j i : Fin (n+1)) (U : UnitaryMatrixGroup n) :
    (unitaryColumn n j U).val i = U.val i j := rfl

@[simp] lemma standardColumn_apply (n : ℕ) (j i : Fin (n+1)) :
    (standardColumn n j).val i = if i = j then 1 else 0 := by
  simp [standardColumn, EuclideanSpace.single, PiLp.single_apply, eq_comm]

@[simp] lemma unitaryColumn_one (n : ℕ) (j : Fin (n+1)) :
    unitaryColumn n j 1 = standardColumn n j := by
  apply Subtype.ext
  ext i
  simp [Matrix.one_apply]

lemma unitaryColumn_mul (n : ℕ) (j : Fin (n+1)) (U V : UnitaryMatrixGroup n) :
    (unitaryColumn n j (U * V)).val =
      Matrix.toEuclideanLin U.val (unitaryColumn n j V).val := by
  ext i
  change (U.val * V.val) i j = (U.val *ᵥ (fun k => V.val k j)) i
  rfl


/-- Radial projection of a nonzero complex number onto the unit circle. -/
def phase : C(ℂˣ, Circle) where
  toFun u := ⟨(u : ℂ) / (‖(u : ℂ)‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    simp [Complex.norm_real, u.ne_zero]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (Units.continuous_val).div
      (Complex.continuous_ofReal.comp Units.continuous_val.norm)
      (fun u => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr u.ne_zero))

/-- The usual inclusion of the unit circle into the nonzero complex numbers. -/
def unitEmbedding : C(Circle, ℂˣ) where
  toFun := Circle.toUnits
  continuous_toFun := Units.continuous_iff.mpr ⟨continuous_subtype_val, by
    simp only [← map_inv]
    exact continuous_subtype_val.comp continuous_inv⟩

/-- One positively oriented traversal of the circle. -/
def circleParam : Path (1 : Circle) 1 where
  toFun t := Circle.exp (2 * Real.pi * (t : ℝ))
  continuous_toFun := Circle.exp.continuous.comp (by fun_prop)
  source' := by simp
  target' := by simp

/-- The integer winding number of a circle-valued loop, via the universal cover
`ℝ → ℝ/(2πℤ)` and Mathlib's fundamental-group winding isomorphism. -/
def circleWinding (f : C(Circle, Circle)) : ℤ :=
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  AddCircle.windingNumber (p := 2 * Real.pi)
    (.of (.mk ((circleParam.map f.continuous).map
      AddCircle.homeomorphCircle'.symm.continuous)))

/-- Winding of a nonvanishing scalar symbol about zero. -/
def winding (f : C(Circle, ℂˣ)) : ℤ := circleWinding (phase.comp f)

/-- Determinant as a continuous map on the general linear group. -/
def determinant (n : ℕ) : C(MatrixGroup n, ℂˣ) where
  toFun := Matrix.GeneralLinearGroup.det
  continuous_toFun := Units.continuous_iff.mpr
    ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩

/-- Embed one nonzero scalar into the first diagonal entry, with all other
entries equal to one. -/
def diagonal (n : ℕ) : C(ℂˣ, MatrixGroup n) where
  toFun u :=
    { val := Matrix.diagonal (fun j => if j = 0 then (u : ℂ) else 1)
      inv := Matrix.diagonal (fun j => if j = 0 then (↑u⁻¹ : ℂ) else 1)
      val_inv := by
        rw [Matrix.diagonal_mul_diagonal]
        apply Matrix.diagonal_eq_one.mpr
        funext j
        split_ifs <;> simp
      inv_val := by
        rw [Matrix.diagonal_mul_diagonal]
        apply Matrix.diagonal_eq_one.mpr
        funext j
        split_ifs <;> simp }
  continuous_toFun := by
    apply Units.continuous_iff.mpr
    constructor
    · apply Continuous.matrix_diagonal
      apply continuous_pi
      intro j
      split_ifs
      · exact Units.continuous_val
      · exact continuous_const
    · apply Continuous.matrix_diagonal
      apply continuous_pi
      intro j
      split_ifs
      · exact Units.continuous_coe_inv
      · exact continuous_const

/-- The loop `z ↦ z^k` as a nonzero complex scalar. Negative `k` are included. -/
def powerLoop (k : ℤ) : C(Circle, ℂˣ) where
  toFun z := Circle.toUnits (z ^ k)
  continuous_toFun := Units.continuous_iff.mpr ⟨
    continuous_subtype_val.comp (continuous_id.zpow k),
    by
      simp only [← map_inv]
      exact continuous_subtype_val.comp (continuous_id.zpow k).inv⟩

/-- The standard diagonal loop with one `z^k` entry. -/
def normalForm (n : ℕ) (k : ℤ) : C(Circle, MatrixGroup n) :=
  (diagonal n).comp (powerLoop k)

namespace Spec

/-- The entire assigned classification. Homotopies take values in the actual
invertible matrix group at every parameter value. -/
def Classification : Prop :=
  ∀ (n : ℕ) (Φ : C(Circle, MatrixGroup n)),
    Φ.Homotopic (normalForm n (winding ((determinant n).comp Φ)))

/-- Every continuous invertible matrix loop deforms through invertible matrices
into an actual continuous unitary matrix loop. -/
def UnitaryReduction : Prop :=
  ∀ (n : ℕ) (Φ : C(Circle, MatrixGroup n)),
    ∃ U : C(Circle, UnitaryMatrixGroup n),
      Φ.Homotopic ((unitaryEmbedding n).comp U)

/-- A continuous local unitary transporter on an open neighborhood of every
pair of equal unit columns. It sends the first column to the second and equals
the identity when the columns agree. This is the local, not the global, lift. -/
def LocalUnitaryTransport : Prop :=
  ∀ n : ℕ, ∃ V : Set (UnitColumn n × UnitColumn n),
    IsOpen V ∧ (∀ v : UnitColumn n, (v, v) ∈ V) ∧
      ∃ L : C(V, UnitaryMatrixGroup n),
        (∀ p : V, Matrix.toEuclideanLin (L p : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
          p.val.1.val = p.val.2.val) ∧
        (∀ p : V, p.val.1 = p.val.2 → L p = 1)

/-- Sphere loops in every complex dimension at least two contract to any
specified unit vector. -/
def SphereLoopContraction : Prop :=
  ∀ (n : ℕ) (f : C(Circle, UnitColumn (n+1))) (q : UnitColumn (n+1)),
    f.Homotopic (.const Circle q)

/-- A prescribed column homotopy lifts from its actual initial unitary frame.
The lift follows the given column at every point of the homotopy square. -/
def ColumnHomotopyLift : Prop :=
  ∀ (n : ℕ) (j : Fin (n+1)) (U : C(Circle, UnitaryMatrixGroup n))
    (v : C(Circle, UnitColumn n))
    (H : ((unitaryColumn n j).comp U).Homotopy v),
    ∃ V : C(Circle, UnitaryMatrixGroup n), ∃ K : U.Homotopy V,
      ∀ p, unitaryColumn n j (K p) = H p

/-- Scalar continuous nonvanishing symbols have the usual power normal form. -/
def ScalarClassification : Prop :=
  ∀ f : C(Circle, ℂˣ), f.Homotopic (powerLoop (winding f))

/-- Winding is invariant under homotopies through nonzero scalar symbols. -/
def WindingHomotopy : Prop :=
  ∀ f g : C(Circle, ℂˣ), f.Homotopic g → winding f = winding g

/-- The assigned classification in dimension one, including every scalar winding. -/
def DimensionOneClassification : Prop :=
  ∀ Φ : C(Circle, MatrixGroup 0),
    Φ.Homotopic (normalForm 0 (winding ((determinant 0).comp Φ)))

/-- The matrix reduction stage before applying the scalar classification. -/
def ScalarReduction : Prop :=
  ∀ (n : ℕ) (Φ : C(Circle, MatrixGroup n)),
    ∃ u : C(Circle, ℂˣ), Φ.Homotopic ((diagonal n).comp u)

/-- Assembly from matrix reduction, whose premise is proved in the implementation. -/
def ClassificationFromScalarReduction : Prop := ScalarReduction → Classification

/-- Determinant of the standard embedding of a scalar. -/
def DeterminantDiagonal : Prop :=
  ∀ (n : ℕ) (u : ℂˣ), determinant n (diagonal n u) = u

/-- Winding has the standard orientation and normalization on all integer powers. -/
def WindingPower : Prop := ∀ k : ℤ, winding (powerLoop k) = k

/-- Determinant carries invertible matrix homotopies to scalar homotopies. -/
def DeterminantHomotopy : Prop :=
  ∀ (n : ℕ) (f g : C(Circle, MatrixGroup n)),
    f.Homotopic g → ((determinant n).comp f).Homotopic ((determinant n).comp g)

end Spec
end ExpandedFA.Toeplitz.MatrixLoops
