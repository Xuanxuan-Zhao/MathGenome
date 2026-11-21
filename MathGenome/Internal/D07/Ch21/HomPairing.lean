import MathGenome.Internal.D07.Ch05.AveragingBridge
import MathGenome.Internal.D07.Ch17.IntertwinersEquivalence
import MathGenome.Internal.D07.Ch21.UnitaryAveraging
import MathGenome.Internal.Specs.D07.Ch21.HomPairing
import Mathlib.LinearAlgebra.Matrix.StdBasis

namespace D07.Ch21.HomPairing

universe u v w t s
noncomputable section
open Specs.D07.Ch21.HomPairing

def pairing : PairingType.{u} := pairingValue

def homAction : HomActionType.{u,v,w} := homActionValue

def homAverage : HomAverageType.{u,v,w} := homAverageValue

/-- The diagonal value is the real average of the squared absolute values. -/
theorem pairing_square_norm : PairingSquareNorm.{u} := by
  intro G _ _ f
  simp only [pairingValue, ← Complex.normSq_eq_conj_mul_self, mul_comm (f _)]
  simp [Complex.normSq_eq_norm_sq]

theorem pairing_hermitian : PairingHermitian.{u} := by
  intro G _ _
  constructor
  · intro f k h
    simp [pairingValue, add_mul, Finset.sum_add_distrib, mul_add]
  · intro a f k
    simp only [pairingValue, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    ring
  · intro f k h
    simp [pairingValue, mul_add, Finset.sum_add_distrib]
  · intro a f k
    simp only [pairingValue, Pi.smul_apply, smul_eq_mul, map_mul]
    simp_rw [mul_left_comm (f _) (starRingEnd ℂ a)]
    rw [← Finset.mul_sum]
    ring
  · intro f k
    simp only [pairingValue, map_mul, map_inv₀, map_natCast, map_sum,
      starRingEnd_self_apply]
    simp only [mul_comm (starRingEnd ℂ (k _))]
  · intro f hf
    obtain ⟨g, hg⟩ : ∃ g, f g ≠ 0 := by
      by_contra h
      apply hf
      ext g
      simpa using not_exists.mp h g
    rw [pairing_square_norm G f, Complex.ofReal_re]
    apply mul_pos (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
    exact Finset.sum_pos' (fun g _ => sq_nonneg ‖f g‖)
      ⟨g, Finset.mem_univ _, sq_pos_of_pos (norm_pos_iff.mpr hg)⟩

theorem pairing_definite : PairingDefinite.{u} := by
  intro G _ _ f
  have hh := pairing_hermitian G
  refine ⟨D07.Ch21.UnitaryAveraging.form_nonneg hh f, ?_⟩
  constructor
  · intro h g
    by_contra hg
    have hf : f ≠ 0 := fun he => hg (congrFun he g)
    have := hh.positive f hf
    simp [h] at this
  · intro h
    simp [pairingValue, h]

theorem hom_action_laws : HomActionLaws.{u,v,w} := by
  intro G V W _ _ _ _ _ ρ σ
  exact ⟨fun _ _ => rfl, (Representation.linHom ρ σ).map_one,
    fun g h => (Representation.linHom ρ σ).map_mul g h⟩

theorem invariants_intertwiners : InvariantsIntertwiners.{u,v,w} := by
  intro G V W _ _ _ _ _ ρ σ T
  exact Representation.mem_linHom_invariants_iff_isIntertwining T

/-- The upstream averaging construction agrees with the explicit complex average. -/
lemma homAverage_eq_average {G : Type u} {V : Type v} {W : Type w}
    [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    homAverageValue G V W ρ σ =
      Specs.D07.Ch05.AveragingBridge.average (fun g => homActionValue G V W ρ σ g) := by
  have h : Specs.D07.Ch05.AveragingBridge.orderScalar ℂ G ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [homAverageValue, Specs.D07.Ch05.AveragingBridge.average,
    (D07.Ch05.AveragingBridge.normalization_cases ℂ G).1 h,
    Specs.D07.Ch05.AveragingBridge.orderScalar]

lemma hom_average_isProj {G : Type u} {V : Type v} {W : Type w}
    [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    LinearMap.IsProj (homActionValue G V W ρ σ).invariants
      (homAverageValue G V W ρ σ) := by
  have h : Specs.D07.Ch05.AveragingBridge.orderScalar ℂ G ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [homAverage_eq_average]
  refine ⟨?_, ?_⟩
  · intro T g
    exact D07.Ch05.AveragingBridge.average_invariant ℂ (V →ₗ[ℂ] W) G _
      (hom_action_laws G V W ρ σ).2.2 g T
  · intro T hT
    exact D07.Ch05.AveragingBridge.average_fixed ℂ (V →ₗ[ℂ] W) G _ h T hT

theorem average_projection : AverageProjection.{u,v,w} := by
  intro G V W _ _ _ _ _ _ ρ σ
  have h := hom_average_isProj ρ σ
  refine ⟨h.map_mem, ?_, ?_, h.range, ?_⟩
  · intro T hT
    exact h.map_id T ((invariants_intertwiners G V W ρ σ T).mpr hT)
  · exact h.isIdempotentElem
  · rw [h.range]
    exact h.isCompl

theorem trace_average : TraceAverage.{u,v,w} := by
  intro G V W _ _ _ _ _ _ _ _ ρ σ
  rw [(hom_average_isProj ρ σ).trace]
  exact congrArg Nat.cast (Representation.invariantsEquivIntertwiningMap ρ σ).finrank_eq

theorem trace_hom_action : TraceHomAction.{u,v,w} := by
  intro G V W _ _ _ _ _ _ _ _ ρ σ g
  exact (Representation.char_linHom ρ σ g).trans (mul_comm _ _)

theorem character_hom_pairing : CharacterHomPairing.{u,v,w} := by
  intro G V W _ _ _ _ _ _ _ _ ρ σ
  rw [← trace_average G V W ρ σ]
  simp only [pairingValue, homAverageValue, map_smul, map_sum, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  have hi := D07.Ch21.UnitaryAveraging.character_inverse G V ρ g
  change LinearMap.trace ℂ V (ρ g⁻¹) =
    starRingEnd ℂ (LinearMap.trace ℂ V (ρ g)) at hi
  change LinearMap.trace ℂ W (σ g) *
    starRingEnd ℂ (LinearMap.trace ℂ V (ρ g)) = _
  rw [← hi]
  exact (trace_hom_action G V W ρ σ g).symm

theorem pairing_nonnegative_integer : PairingNonnegativeInteger.{u,v,w} := by
  intro G V W _ _ _ _ _ _ _ _ ρ σ
  refine ⟨Module.finrank ℂ (Representation.IntertwiningMap ρ σ),
    character_hom_pairing G V W ρ σ, ?_⟩
  rw [character_hom_pairing G V W ρ σ]
  simp

theorem zero_space : ZeroSpace.{u,v,w} := by
  intro G V W _ _ _ _ _ _ _ _ ρ σ h
  have hz : Module.finrank ℂ (Representation.IntertwiningMap ρ σ) = 0 := by
    rcases h with h | h
    · have := h
      have : Subsingleton (Representation.IntertwiningMap ρ σ) :=
        ⟨fun f g => Representation.IntertwiningMap.ext (Subsingleton.elim _ _)⟩
      exact Module.finrank_zero_of_subsingleton
    · have := h
      have : Subsingleton (Representation.IntertwiningMap ρ σ) :=
        ⟨fun f g => Representation.IntertwiningMap.ext (Subsingleton.elim _ _)⟩
      exact Module.finrank_zero_of_subsingleton
  exact ⟨by rw [character_hom_pairing G V W ρ σ, hz, Nat.cast_zero], hz⟩

/-- A matrix unit contributes precisely the product of the two diagonal entries. -/
theorem matrix_sandwich_trace : MatrixSandwichTrace.{t,s} := by
  intro m n _ _ B A
  classical
  let b := Matrix.stdBasis ℂ m n
  have hr (T : Matrix m n ℂ) (p : m × n) : b.repr T p = T p.1 p.2 := by
    rfl
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, hr]
  change (∑ p : m × n, (B * b p * A) p.1 p.2) = _
  have hb (p : m × n) : b p = Matrix.single p.1 p.2 1 :=
    Matrix.stdBasis_eq_single ℂ p.1 p.2
  have hd (p : m × n) : (B * b p * A) p.1 p.2 = B p.1 p.1 * A p.2 p.2 := by
    rw [hb]
    simp [Matrix.mul_apply, Matrix.single, ite_and, eq_comm]
  simp_rw [hd]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

end
end D07.Ch21.HomPairing
