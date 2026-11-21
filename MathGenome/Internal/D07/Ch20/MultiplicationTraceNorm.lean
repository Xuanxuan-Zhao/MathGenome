import MathGenome.Internal.Specs.D07.Ch20.MultiplicationTraceNorm
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! Trace, norm, and characteristic polynomial of multiplication for every
finite extension, including inseparable extensions (paper.tex:5865–5893).
All scalars use the chosen Algebra structure. -/

universe u v w

namespace D07.Ch20.MultiplicationTraceNorm

noncomputable section

/-- Left multiplication, packaged with its K-linearity and multiplicativity. -/
def multiplication (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] : L →ₐ[K] Module.End K L :=
  Algebra.lmul K L

/-- Operator trace of multiplication, as a K-linear map. -/
def trace (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] : L →ₗ[K] K :=
  Algebra.trace K L

/-- Operator determinant of multiplication, as a multiplicative map. -/
def norm (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] : L →* K :=
  Algebra.norm K

/-- The characteristic polynomial det(TI - m_a). -/
def characteristicPolynomial (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (a : L) : Polynomial K :=
  (multiplication K L a).charpoly

/-- The norm restricted to the multiplicative groups of units. -/
def normOnUnits (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] : Lˣ →* Kˣ :=
  Units.map (norm K L)

theorem multiplication_apply (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (a x : L) :
    multiplication K L a x = a * x := rfl

theorem trace_apply (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (a : L) :
    trace K L a = LinearMap.trace K L (multiplication K L a) := rfl

theorem norm_apply (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (a : L) :
    norm K L a = LinearMap.det (multiplication K L a) := rfl

/-- In every finite basis the intrinsic objects are the matrix trace,
determinant, and determinant of TI minus the multiplication matrix. -/
theorem matrix_formulas (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (a : L) :
    trace K L a = Matrix.trace (Algebra.leftMulMatrix b a) ∧
    norm K L a = Matrix.det (Algebra.leftMulMatrix b a) ∧
    characteristicPolynomial K L a =
      Matrix.det (Matrix.charmatrix (Algebra.leftMulMatrix b a)) := by
  refine ⟨Algebra.trace_eq_matrix_trace b a, Algebra.norm_eq_matrix_det b a, ?_⟩
  exact (LinearMap.charpoly_toMatrix (Algebra.lmul K L a) b).symm

theorem trace_add (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (a b : L) :
    trace K L (a + b) = trace K L a + trace K L b :=
  (trace K L).map_add a b

theorem trace_smul (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (c : K) (a : L) :
    trace K L (c • a) = c * trace K L a :=
  (trace K L).map_smul c a

theorem norm_one (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] : norm K L (1 : L) = 1 :=
  (norm K L).map_one

theorem norm_mul (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (a b : L) :
    norm K L (a * b) = norm K L a * norm K L b :=
  (norm K L).map_mul a b

theorem trace_algebraMap (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (c : K) :
    trace K L (algebraMap K L c) = (Module.finrank K L : K) * c := by
  simpa only [trace, nsmul_eq_mul] using Algebra.trace_algebraMap (S := L) c

theorem norm_algebraMap (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (c : K) :
    norm K L (algebraMap K L c) = c ^ Module.finrank K L :=
  Algebra.norm_algebraMap c

theorem trace_scalar_mul (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (c : K) (a : L) :
    trace K L (algebraMap K L c * a) = c * trace K L a := by
  rw [← Algebra.smul_def]
  exact trace_smul K L c a

theorem norm_scalar_mul (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (c : K) (a : L) :
    norm K L (algebraMap K L c * a) = c ^ Module.finrank K L * norm K L a := by
  rw [norm_mul, norm_algebraMap]

theorem norm_eq_zero_iff (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (a : L) : norm K L a = 0 ↔ a = 0 :=
  Algebra.norm_eq_zero_iff

theorem normOnUnits_apply (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (a : Lˣ) :
    (normOnUnits K L a : K) = norm K L (a : L) := rfl

end

end D07.Ch20.MultiplicationTraceNorm
