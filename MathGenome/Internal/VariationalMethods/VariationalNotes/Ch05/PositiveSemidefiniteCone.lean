import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch05.OrthantLorentzCones
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.PositiveSemidefiniteCone
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef

noncomputable section
open Matrix
namespace VariationalNotes.Ch05.PositiveSemidefiniteCone

abbrev symmetricMatrices := Specs.symmetricMatrices
abbrev SymmetricMatrix := Specs.SymmetricMatrix

def matrix {n : ℕ} (S : SymmetricMatrix n) : Matrix (Fin n) (Fin n) ℝ := Specs.matrix S

def psdCone (n : ℕ) : Set (SymmetricMatrix n) := Specs.psdCone n

theorem matrix_symmetric : Specs.matrix_symmetric := by
  intro n S
  ext i j
  exact S.property j i

theorem matrix_range : Specs.matrix_range := by
  intro n M
  constructor
  · rintro ⟨S, rfl⟩
    exact matrix_symmetric S
  · intro hM
    refine ⟨⟨WithLp.toLp 2 (fun p => M p.1 p.2), ?_⟩, rfl⟩
    intro i j
    exact congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A j i) hM

theorem mem_psdCone_iff : Specs.mem_psdCone_iff := by
  intro n S
  change (Specs.matrix S).PosSemidef ↔ _
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  simp only [Matrix.isHermitian_iff_isSymm, matrix_symmetric S, true_and, star_trivial]

theorem trace_inner : Specs.trace_inner := by
  intro n S T
  change inner ℝ S.val T.val = _
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change T.val (i, j) * S.val (i, j) = Specs.matrix S i j * Specs.matrix T j i
  rw [mul_comm]
  congr 1
  exact T.property i j

/-- Rank-one positive semidefinite symmetric matrix `v vᵀ`. -/
def rankOne {n : ℕ} (v : Fin n → ℝ) : SymmetricMatrix n :=
  ⟨WithLp.toLp 2 (fun p => v p.1 * v p.2), by
    intro i j
    exact mul_comm _ _⟩

lemma matrix_rankOne {n : ℕ} (v : Fin n → ℝ) :
    Specs.matrix (rankOne v) = Matrix.vecMulVec v v := rfl

lemma rankOne_mem {n : ℕ} (v : Fin n → ℝ) : rankOne v ∈ Specs.psdCone n := by
  change (Specs.matrix (rankOne v)).PosSemidef
  rw [matrix_rankOne]
  simpa using Matrix.posSemidef_vecMulVec_self_star v

lemma trace_rankOne {n : ℕ} (S : SymmetricMatrix n) (v : Fin n → ℝ) :
    Matrix.trace (Specs.matrix S * Specs.matrix (rankOne v)) =
      v ⬝ᵥ (Specs.matrix S *ᵥ v) := by
  simp only [matrix_rankOne, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Nonnegative trace pairing follows by diagonalizing only the second PSD matrix. -/
lemma trace_mul_nonneg {n : ℕ} {S T : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) : 0 ≤ Matrix.trace (S * T) := by
  let U : Matrix (Fin n) (Fin n) ℝ := hT.isHermitian.eigenvectorUnitary
  have hp : (Uᴴ * S * U).PosSemidef := hS.conjTranspose_mul_mul_same U
  have he : Matrix.trace (S * T) =
      Matrix.trace ((Uᴴ * S * U) * Matrix.diagonal hT.isHermitian.eigenvalues) := by
    conv_lhs => rw [hT.isHermitian.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_real_eq_id,
      id_eq]
    change Matrix.trace (S * (U * Matrix.diagonal hT.isHermitian.eigenvalues * Uᴴ)) = _
    rw [Matrix.trace_mul_cycle']
    simp only [Matrix.mul_assoc]
  rw [he, Matrix.trace]
  exact Finset.sum_nonneg fun i _ => by
    simpa using mul_nonneg (hp.diag_nonneg (i := i)) (hT.eigenvalues_nonneg i)

lemma psd_isCone (n : ℕ) : VariationalNotes.ConvexGeometry.Specs.IsCone (Specs.psdCone n) := by
  refine ⟨?_, ?_, ?_⟩
  · change (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef
    exact Matrix.PosSemidef.zero
  · intro S T hS hT
    change (Specs.matrix S + Specs.matrix T).PosSemidef
    exact hS.add hT
  · intro r hr S hS
    change (r • Specs.matrix S).PosSemidef
    exact hS.smul hr

lemma psd_isClosed (n : ℕ) : IsClosed (Specs.psdCone n) := by
  have he : Specs.psdCone n = ⋂ v : Fin n → ℝ,
      {S : SymmetricMatrix n | 0 ≤ inner ℝ S (rankOne v)} := by
    ext S
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [mem_psdCone_iff]
    constructor
    · intro h v
      rw [trace_inner, trace_rankOne]
      exact h v
    · intro h v
      have hv := h v
      rwa [trace_inner, trace_rankOne] at hv
  rw [he]
  exact isClosed_iInter fun v => isClosed_le continuous_const (continuous_id.inner continuous_const)

lemma psd_self_dual (n : ℕ) :
    ConicProgramModels.Specs.innerPositiveDual (Specs.psdCone n) = Specs.psdCone n := by
  ext S
  change (∀ T ∈ Specs.psdCone n, 0 ≤ inner ℝ S T) ↔ S ∈ Specs.psdCone n
  constructor
  · intro h
    rw [mem_psdCone_iff]
    intro v
    have hv := h (rankOne v) (rankOne_mem v)
    rwa [trace_inner, trace_rankOne] at hv
  · intro hS T hT
    rw [trace_inner]
    exact trace_mul_nonneg hS hT

theorem psd_properties : Specs.psd_properties := by
  intro n
  exact ⟨psd_isClosed n, VariationalNotes.ConvexGeometry.cone_convex _ (psd_isCone n),
    psd_isCone n, psd_self_dual n⟩

theorem standard_self_dual_cones : Specs.standard_self_dual_cones :=
  ⟨OrthantLorentzCones.orthant_properties, OrthantLorentzCones.lorentz_properties,
    psd_properties⟩

end VariationalNotes.Ch05.PositiveSemidefiniteCone
