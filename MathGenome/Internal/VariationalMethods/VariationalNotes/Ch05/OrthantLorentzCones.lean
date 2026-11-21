import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch05.ConicProgramModels
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.OrthantLorentzCones
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
universe u
namespace VariationalNotes.Ch05.OrthantLorentzCones

def orthant {ι : Type u} [Fintype ι] : Set (EuclideanSpace ℝ ι) := Specs.orthant

def lorentzCone {U : Type u} [NormedAddCommGroup U] [InnerProductSpace ℝ U] :
    Set (WithLp 2 (ℝ × U)) := Specs.lorentzCone

theorem product_pairing : Specs.product_pairing := by
  intro U _ _ z w
  simp [WithLp.prod_inner_apply, mul_comm]

theorem lorentz_axis : Specs.lorentz_axis := by
  intro U _ _ t
  simp [Specs.lorentzCone]

theorem lorentz_zero_dimension : Specs.lorentz_zero_dimension := by
  intro U _ _ _ z
  have hz : z.snd = 0 := Subsingleton.elim _ _
  simp [Specs.lorentzCone, hz]

theorem orthant_properties : Specs.orthant_properties := by
  intro ι _
  have hc : VariationalNotes.ConvexGeometry.Specs.IsCone
      (Specs.orthant : Set (EuclideanSpace ℝ ι)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i; simp
    · intro x y hx hy i
      exact add_nonneg (hx i) (hy i)
    · intro r hr x hx i
      exact mul_nonneg hr (hx i)
  refine ⟨?_, VariationalNotes.ConvexGeometry.cone_convex _ hc, hc, ?_⟩
  · have he : (Specs.orthant : Set (EuclideanSpace ℝ ι)) =
        ⋂ i, {x : EuclideanSpace ℝ ι | 0 ≤ x i} := by ext; simp [Specs.orthant]
    rw [he]
    exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
  · classical
    ext x
    change (∀ y ∈ Specs.orthant, 0 ≤ inner ℝ x y) ↔ ∀ i, 0 ≤ x i
    constructor
    · intro h i
      have hi : EuclideanSpace.single i (1 : ℝ) ∈ Specs.orthant := by
        intro j
        simp [PiLp.single_apply]
        positivity
      have hh := h _ hi
      simpa [EuclideanSpace.inner_single_right] using hh
    · intro hx y hy
      rw [PiLp.inner_apply]
      exact Finset.sum_nonneg fun i _ => by
        simpa using mul_nonneg (hy i) (hx i)

private theorem lorentz_isCone {U : Type u} [NormedAddCommGroup U] [InnerProductSpace ℝ U] :
    VariationalNotes.ConvexGeometry.Specs.IsCone
      (Specs.lorentzCone : Set (WithLp 2 (ℝ × U))) := by
  refine ⟨?_, ?_, ?_⟩
  · change ‖(0 : WithLp 2 (ℝ × U)).snd‖ ≤ (0 : WithLp 2 (ℝ × U)).fst
    simp
  · intro x y hx hy
    change ‖(x + y).snd‖ ≤ (x + y).fst
    simpa only [WithLp.add_snd, WithLp.add_fst] using
      (norm_add_le x.snd y.snd).trans (add_le_add hx hy)
  · intro r hr x hx
    change ‖(r • x).snd‖ ≤ (r • x).fst
    simpa only [WithLp.smul_snd, WithLp.smul_fst, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hr, smul_eq_mul] using mul_le_mul_of_nonneg_left hx hr

theorem lorentz_properties : Specs.lorentz_properties := by
  intro U _ _
  refine ⟨?_, VariationalNotes.ConvexGeometry.cone_convex _ lorentz_isCone, lorentz_isCone, ?_⟩
  · exact isClosed_le (WithLp.continuous_snd 2 ℝ U).norm (WithLp.continuous_fst 2 ℝ U)
  · ext z
    change (∀ w ∈ Specs.lorentzCone, 0 ≤ inner ℝ z w) ↔ ‖z.snd‖ ≤ z.fst
    constructor
    · intro h
      have ha := h (WithLp.toLp 2 (1, (0 : U))) (by simp [Specs.lorentzCone])
      rw [product_pairing] at ha
      simp only [WithLp.toLp_fst, WithLp.toLp_snd, mul_one, inner_zero_right, add_zero] at ha
      by_cases hz : z.snd = 0
      · simpa [hz] using ha
      · have hp : 0 < ‖z.snd‖ := norm_pos_iff.mpr hz
        -- A homogeneous boundary test avoids dividing by the spatial norm.
        have hw : WithLp.toLp 2 (‖z.snd‖, -z.snd) ∈ Specs.lorentzCone := by
          simp [Specs.lorentzCone]
        have hh := h _ hw
        rw [product_pairing] at hh
        simp only [WithLp.toLp_fst, WithLp.toLp_snd, inner_neg_right,
          real_inner_self_eq_norm_sq] at hh
        nlinarith
    · intro hz w hw
      rw [product_pairing]
      have hp : ‖z.snd‖ * ‖w.snd‖ ≤ z.fst * w.fst :=
        mul_le_mul hz hw (norm_nonneg w.snd) ((norm_nonneg z.snd).trans hz)
      have hi := real_inner_le_norm z.snd (-w.snd)
      simp only [inner_neg_right, norm_neg] at hi
      linarith

end VariationalNotes.Ch05.OrthantLorentzCones
