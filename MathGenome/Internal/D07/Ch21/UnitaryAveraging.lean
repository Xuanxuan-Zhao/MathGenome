import MathGenome.Internal.D07.Ch17.Characters
import MathGenome.Internal.Specs.D07.Ch21.UnitaryAveraging

namespace D07.Ch21.UnitaryAveraging

universe u v
noncomputable section
open Specs.D07.Ch21.UnitaryAveraging

variable {G : Type u} {V : Type v} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V]

lemma form_zero_left {h : V → V → ℂ} (hh : IsPositiveHermitian h)
    (y : V) : h 0 y = 0 := by
  simpa using hh.smul_left 0 0 y

lemma form_zero_right {h : V → V → ℂ} (hh : IsPositiveHermitian h)
    (x : V) : h x 0 = 0 := by
  simpa using hh.smul_right 0 x 0

lemma form_nonneg {h : V → V → ℂ} (hh : IsPositiveHermitian h)
    (x : V) : 0 ≤ (h x x).re := by
  by_cases hx : x = 0
  · simp [hx, form_zero_left hh]
  · exact (hh.positive x hx).le

/-- Swap the variables to pass from the paper's convention to Mathlib's. -/
@[instance_reducible]
def hermitianCore {h : V → V → ℂ} (hh : IsPositiveHermitian h) :
    InnerProductSpace.Core ℂ V where
  inner x y := h y x
  conj_inner_symm x y := hh.hermitian y x
  re_inner_nonneg := form_nonneg hh
  add_left x y z := hh.add_right z x y
  smul_left x y a := hh.smul_right a y x
  definite x hx := by
    by_contra hn
    have := hh.positive x hn
    simp [hx] at this

theorem positive_form_exists : PositiveFormExists.{v} := by
  intro V _ _ _
  let b := Module.finBasis ℂ V
  let e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    b.equivFun.trans (WithLp.linearEquiv 2 ℂ _).symm
  refine ⟨fun x y => inner ℂ (e y) (e x), ?_⟩
  constructor
  · intro x y z; simp only [map_add, inner_add_right]
  · intro a x y; simp only [map_smul, inner_smul_right]
  · intro x y z; simp only [map_add, inner_add_left]
  · intro a x y; simp only [map_smul, inner_smul_left]
  · intro x y; exact inner_conj_symm _ _
  · intro x hx
    exact (re_inner_self_pos (𝕜 := ℂ)).mpr (e.map_ne_zero_iff.mpr hx)

omit [Fintype G] in
lemma action_ne_zero (ρ : Representation ℂ G V) (g : G) {x : V} (hx : x ≠ 0) :
    ρ g x ≠ 0 := by
  intro h
  apply hx
  have := congrArg (ρ g⁻¹) h
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply, map_zero] using this

lemma average_positive_hermitian (ρ : Representation ℂ G V) (h₀ : V → V → ℂ)
    (hh : IsPositiveHermitian h₀) : IsPositiveHermitian (averageForm ρ h₀) := by
  constructor
  · intro x y z
    simp only [averageForm, map_add, hh.add_left, Finset.sum_add_distrib, mul_add]
  · intro a x y
    simp only [averageForm, map_smul, hh.smul_left, ← Finset.mul_sum]
    ring
  · intro x y z
    simp only [averageForm, map_add, hh.add_right, Finset.sum_add_distrib, mul_add]
  · intro a x y
    simp only [averageForm, map_smul, hh.smul_right, ← Finset.mul_sum]
    ring
  · intro x y
    simp only [averageForm, map_mul, map_inv₀, map_natCast, map_sum, hh.hermitian]
  · intro x hx
    have hc : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
    have hs : 0 < ∑ g : G, (h₀ (ρ g x) (ρ g x)).re :=
      Finset.sum_pos (fun g _ => hh.positive _ (action_ne_zero ρ g hx))
        Finset.univ_nonempty
    have he : (averageForm ρ h₀ x x).re =
        (Fintype.card G : ℝ)⁻¹ * ∑ g : G, (h₀ (ρ g x) (ρ g x)).re := by
      simp [averageForm, Complex.mul_re, Complex.inv_re, Complex.inv_im]
    rw [he]
    exact mul_pos (inv_pos.mpr hc) hs

lemma average_invariant (ρ : Representation ℂ G V) (h₀ : V → V → ℂ) (k : G)
    (x y : V) : averageForm ρ h₀ (ρ k x) (ρ k y) = averageForm ρ h₀ x y := by
  unfold averageForm
  congr 1
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight k) _ _ (fun _ => rfl)

theorem average_properties : AverageProperties.{u,v} := by
  intro G V _ _ _ _ _ ρ h₀ hh
  exact ⟨average_positive_hermitian ρ h₀ hh, average_invariant ρ h₀⟩

omit [Fintype G] in
/-- An invariant linear-first form gives an orthonormal basis and unitary matrices.
The norm and inner product here are constructed from the form, not assumed. -/
lemma unitary_basis_of_invariant [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (h : V → V → ℂ) (hh : IsPositiveHermitian h)
    (hi : ∀ k x y, h (ρ k x) (ρ k y) = h x y) :
    ∃ b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V,
      (∀ i j, h (b i) (b j) = if i = j then 1 else 0) ∧
      (∀ g, LinearMap.toMatrix b b (ρ g) ∈ Matrix.unitaryGroup _ ℂ) ∧
      (∀ g, LinearMap.toMatrix b b (ρ g⁻¹) =
        (LinearMap.toMatrix b b (ρ g)).conjTranspose) := by
  classical
  let c := hermitianCore hh
  let : NormedAddCommGroup V := c.toNormedAddCommGroup
  let : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  let b := stdOrthonormalBasis ℂ V
  have hu (g : G) : LinearMap.toMatrix b.toBasis b.toBasis (ρ g) ∈
      Matrix.unitaryGroup _ ℂ := by
    let e : V ≃ₗ[ℂ] V :=
      LinearMap.GeneralLinearGroup.generalLinearEquiv ℂ V (ρ.toHomUnits g)
    let f : V ≃ₗᵢ[ℂ] V := e.isometryOfInner (fun x y => hi g y x)
    exact f.toMatrix_mem_unitaryGroup b b
  refine ⟨b.toBasis, ?_, hu, ?_⟩
  · intro i j
    change inner ℂ (b j) (b i) = _
    rw [b.inner_eq_ite]
    simp only [eq_comm]
  · intro g
    have hNM : LinearMap.toMatrix b.toBasis b.toBasis (ρ g⁻¹) *
        LinearMap.toMatrix b.toBasis b.toBasis (ρ g) = 1 := by
      rw [← LinearMap.toMatrix_mul, ← map_mul, inv_mul_cancel, map_one,
        LinearMap.toMatrix_one]
    exact left_inv_eq_right_inv hNM (Matrix.mem_unitaryGroup_iff.mp (hu g))

theorem averaged_unitary_basis : AveragedUnitaryBasis.{u,v} := by
  intro G V _ _ _ _ _ ρ h₀ hh
  exact unitary_basis_of_invariant ρ (averageForm ρ h₀)
    (average_positive_hermitian ρ h₀ hh) (average_invariant ρ h₀)

theorem zero_space_unique_form : ZeroSpaceUniqueForm.{v} := by
  intro V _ _ _
  constructor
  · constructor
    · intros; simp
    · intros; simp
    · intros; simp
    · intros; simp
    · intros; simp
    · intro x hx; exact (hx (Subsingleton.elim x 0)).elim
  · intro h hh
    funext x y
    rw [Subsingleton.elim x 0, form_zero_left hh]

theorem character_inverse : CharacterInverse.{u,v} := by
  intro G V _ _ _ _ _ ρ g
  obtain ⟨h₀, hh⟩ := positive_form_exists V
  obtain ⟨b, _, _, hb⟩ := averaged_unitary_basis G V ρ h₀ hh
  change LinearMap.trace ℂ V (ρ g⁻¹) = starRingEnd ℂ (LinearMap.trace ℂ V (ρ g))
  rw [LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.trace_eq_matrix_trace ℂ b,
    hb g, Matrix.trace_conjTranspose]
  rfl

theorem character_dual : CharacterDual.{u,v} := by
  intro G V _ _ _ _ _ ρ g
  change LinearMap.trace ℂ (Module.Dual ℂ V) (ρ.dual g) = _
  rw [Representation.dual_apply, LinearMap.trace_transpose']
  exact character_inverse G V ρ g

end
end D07.Ch21.UnitaryAveraging
