import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.NonclosedPSDImage
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.Foundations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Set

namespace VariationalNotes.ConvexGeometry.PSDImage

abbrev Matrix2 := Specs.PSDImage.Matrix2

def symmetricMatrix (a b c : ℝ) : Matrix2 := Specs.PSDImage.symmetricMatrix a b c

def quadraticForm (M : Matrix2) (u v : ℝ) : ℝ := Specs.PSDImage.quadraticForm M u v

def psdCone : Set Matrix2 := Specs.PSDImage.psdCone

def projection : Matrix2 →ₗ[ℝ] (ℝ × ℝ) := Specs.PSDImage.projection

def projectedCone : Set (ℝ × ℝ) := projection '' psdCone

theorem symmetricMatrix_isSymm (a b c : ℝ) : (symmetricMatrix a b c).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem symmetricMatrix_representation (M : Matrix2) (hM : M.IsSymm) :
    M = symmetricMatrix (M 0 0) (M 0 1) (M 1 1) := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · exact hM.apply 0 1
  · rfl

theorem quadraticForm_eq_matrix_sum (M : Matrix2) (w : Fin 2 → ℝ) :
    quadraticForm M (w 0) (w 1) = ∑ i, ∑ j, w i * M i j * w j := by
  simp only [quadraticForm, Specs.PSDImage.quadraticForm, Fin.sum_univ_two]
  ring

theorem psdCone_closed : IsClosed psdCone := by
  have heq : psdCone =
      (⋂ i : Fin 2, ⋂ j : Fin 2, {M : Matrix2 | M j i = M i j}) ∩
      ⋂ u : ℝ, ⋂ v : ℝ, {M : Matrix2 | 0 ≤ quadraticForm M u v} := by
    ext M
    simp [psdCone, Specs.PSDImage.psdCone, Matrix.IsSymm.ext_iff, quadraticForm]
  rw [heq]
  apply IsClosed.inter
  · exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (by fun_prop) (by fun_prop)
  · apply isClosed_iInter
    intro u
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    unfold quadraticForm Specs.PSDImage.quadraticForm
    fun_prop

theorem psdCone_isCone : IsCone psdCone := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨Matrix.isSymm_zero, ?_⟩
    intro u v
    simp [Specs.PSDImage.quadraticForm]
  · intro M N hM hN
    refine ⟨hM.1.add hN.1, ?_⟩
    intro u v
    have heq : quadraticForm (M + N) u v = quadraticForm M u v + quadraticForm N u v := by
      simp only [quadraticForm, Specs.PSDImage.quadraticForm, Matrix.add_apply]
      ring
    change 0 ≤ quadraticForm (M + N) u v
    rw [heq]
    exact add_nonneg (hM.2 u v) (hN.2 u v)
  · intro r hr M hM
    refine ⟨hM.1.smul r, ?_⟩
    intro u v
    have heq : quadraticForm (r • M) u v = r * quadraticForm M u v := by
      simp only [quadraticForm, Specs.PSDImage.quadraticForm, Matrix.smul_apply, smul_eq_mul]
      ring
    change 0 ≤ quadraticForm (r • M) u v
    rw [heq]
    exact mul_nonneg hr (hM.2 u v)

theorem psdCone_convex : Convex ℝ psdCone := cone_convex psdCone psdCone_isCone

theorem psd_first_entry_nonneg (M : Matrix2) (hM : M ∈ psdCone) : 0 ≤ M 0 0 := by
  simpa [Specs.PSDImage.quadraticForm] using hM.2 1 0

theorem psd_zero_first_entry (M : Matrix2) (hM : M ∈ psdCone) (ha : M 0 0 = 0) :
    M 0 1 = 0 := by
  by_contra hb
  have htest := hM.2 (-(M 1 1 + 1) / (2 * M 0 1)) 1
  have hsym := hM.1.apply 0 1
  have heq : Specs.PSDImage.quadraticForm M (-(M 1 1 + 1) / (2 * M 0 1)) 1 = -1 := by
    simp only [Specs.PSDImage.quadraticForm, ha, hsym, zero_mul, zero_add, one_pow, mul_one]
    field_simp
    ring
  rw [heq] at htest
  norm_num at htest

theorem positive_psd_lift (a b : ℝ) (ha : 0 < a) :
    symmetricMatrix a b (b ^ 2 / a) ∈ psdCone := by
  refine ⟨symmetricMatrix_isSymm _ _ _, ?_⟩
  intro u v
  have heq : Specs.PSDImage.quadraticForm (symmetricMatrix a b (b ^ 2 / a)) u v =
      (a * u + b * v) ^ 2 / a := by
    change a * u ^ 2 + (b + b) * u * v + (b ^ 2 / a) * v ^ 2 =
      (a * u + b * v) ^ 2 / a
    field_simp
    ring
  rw [heq]
  exact div_nonneg (sq_nonneg _) ha.le

theorem projectedCone_description :
    projectedCone = {p : ℝ × ℝ | 0 < p.1} ∪ {(0, 0)} := by
  ext p
  constructor
  · rintro ⟨M, hM, rfl⟩
    have ha := psd_first_entry_nonneg M hM
    rcases ha.eq_or_lt with ha | ha
    · right
      have hb := psd_zero_first_entry M hM ha.symm
      change (M 0 0, M 0 1) = (0, 0)
      exact Prod.ext ha.symm hb
    · exact Or.inl ha
  · rintro (hp | hp)
    · exact ⟨symmetricMatrix p.1 p.2 (p.2 ^ 2 / p.1), positive_psd_lift _ _ hp,
        by change (p.1, p.2) = p; exact Prod.mk.eta⟩
    · have hp' : p = (0, 0) := hp
      subst p
      exact ⟨0, psdCone_isCone.1, rfl⟩

theorem target_mem_closure : (0, 1) ∈ closure projectedCone := by
  have h0 : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact (show (0 : ℝ) ≤ 0 from le_rfl)
  have hf : Continuous (fun a : ℝ => (a, (1 : ℝ))) := by fun_prop
  have h := mem_closure_image hf.continuousAt h0
  apply closure_mono (s := (fun a : ℝ => (a, (1 : ℝ))) '' Ioi 0) ?_ h
  rintro p ⟨a, ha, rfl⟩
  rw [projectedCone_description]
  exact Or.inl ha

theorem target_not_mem : (0, 1) ∉ projectedCone := by
  rw [projectedCone_description]
  norm_num

theorem projectedCone_not_closed : ¬ IsClosed projectedCone := by
  intro hc
  exact target_not_mem (hc.closure_eq ▸ target_mem_closure)

end VariationalNotes.ConvexGeometry.PSDImage
