import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.IsotypicMatrixBlocks
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.TensorCycleTrace
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.MultiplicityTraceAverage

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped TensorProduct BigOperators
universe u
namespace AdvancedFiniteGroupRepresentations
variable (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The product action on X restricts to the tensor product action on each
canonical evaluation summand. -/
theorem tensor_action_evaluationInclusion {n : ℕ} (p : Partition n)
    (s : SymmetricGroup n) (g : LinearGroup V) :
    (slotOperator V n s * diagonalOperator V n g).comp (evaluationInclusion V p) =
      (evaluationInclusion V p).comp
        (TensorProduct.map (canonicalSpechtRepresentation p s)
          (tensorMultiplicityOperator V p g)) := by
  apply TensorProduct.ext
  ext v f
  change slotOperator V n s (diagonalOperator V n g
    (evaluationInclusion V p (v ⊗ₜ[ℂ] f))) = _
  rw [evaluationInclusion_pure]
  change _ = evaluationInclusion V p
    (canonicalSpechtRepresentation p s v ⊗ₜ[ℂ] tensorMultiplicityOperator V p g f)
  rw [evaluationInclusion_pure, tensorMultiplicityOperator_apply,
    f.property s v (canonicalSpechtRepresentation p s v) rfl]
  exact congrArg (fun T : Module.End ℂ (TensorPower V n) => T (f.val v))
    (tensor_actions_commute V n s g).eq

/-- Trace of the action followed by one canonical isotypic projector. -/
theorem tensor_trace_isotypic {n : ℕ} (p : Partition n)
    (s : SymmetricGroup n) (g : LinearGroup V) :
    LinearMap.trace ℂ (TensorPower V n)
      ((slotOperator V n s * diagonalOperator V n g) * isotypicProjector V p) =
      (canonicalSpechtRepresentation p).character s *
        LinearMap.trace ℂ (TensorMultiplicity V p) (tensorMultiplicityOperator V p g) := by
  let F := TensorProduct.map (canonicalSpechtRepresentation p s)
    (tensorMultiplicityOperator V p g)
  have h : (slotOperator V n s * diagonalOperator V n g) * isotypicProjector V p =
      ((evaluationInclusion V p).comp F).comp (evaluationProjection V p) := by
    change (slotOperator V n s * diagonalOperator V n g).comp
      ((evaluationInclusion V p).comp (evaluationProjection V p)) = _
    rw [← LinearMap.comp_assoc, tensor_action_evaluationInclusion V p s g]
  rw [h]
  rw [LinearMap.trace_comp_comm' (R := ℂ) (M := TensorPower V n)
    (N := SpechtModule p ⊗[ℂ] TensorMultiplicity V p)
    (evaluationProjection V p) ((evaluationInclusion V p).comp F)]
  have he : (evaluationProjection V p).comp ((evaluationInclusion V p).comp F) = F := by
    apply LinearMap.ext
    intro z
    exact evaluationProjection_inclusion V p (F z)
  rw [he]
  exact LinearMap.trace_tensorProduct' _ _

/-- The trace decomposition from the canonical Schur–Weyl evaluation, retaining
all zero multiplicity summands. -/
theorem tensor_trace_decomposition (n : ℕ) (s : SymmetricGroup n) (g : LinearGroup V) :
    LinearMap.trace ℂ (TensorPower V n)
      (slotOperator V n s * diagonalOperator V n g) =
      ∑ p : Partition n, (canonicalSpechtRepresentation p).character s *
        LinearMap.trace ℂ (TensorMultiplicity V p) (tensorMultiplicityOperator V p g) := by
  classical
  calc
    _ = LinearMap.trace ℂ (TensorPower V n)
        ((slotOperator V n s * diagonalOperator V n g) * ∑ p : Partition n, isotypicProjector V p) := by
      rw [isotypicProjector_sum, mul_one]
    _ = _ := by
      rw [Finset.mul_sum, map_sum]
      exact Finset.sum_congr rfl (fun p _ => tensor_trace_isotypic V p s g)

/-- Character orthogonality for the actual Specht modules. -/
theorem specht_character_orthogonality {n : ℕ} (p q : Partition n) :
    (n.factorial : ℂ)⁻¹ * ∑ s : SymmetricGroup n,
      (canonicalSpechtRepresentation p).character s⁻¹ *
        (canonicalSpechtRepresentation q).character s =
      if q = p then 1 else 0 := by
  classical
  let : Invertible (Nat.card (SymmetricGroup n) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have he : Nonempty ((canonicalSpechtRepresentation p).Equiv
      (canonicalSpechtRepresentation q)) ↔ q = p := by
    constructor
    · intro h
      exact (classification_distinct p q _ _ (fun _ _ => rfl) (fun _ _ => rfl) h).symm
    · rintro rfl
      exact ⟨Representation.Equiv.refl _⟩
  have hc : Nat.card (SymmetricGroup n) = n.factorial := by
    simp [SymmetricGroup, Specs.AdvancedFiniteGroupRepresentations.SymmetricGroup,
      Fintype.card_perm]
  simpa only [hc, he, mul_comm, Nat.cast_one, Nat.cast_zero] using
    Representation.char_orthonormal (canonicalSpechtRepresentation q)
      (canonicalSpechtRepresentation p)

/-- FR-D07: averaging against the inverse Specht character extracts the trace
on the canonical multiplicity space. -/
theorem multiplicity_trace_average :
    Specs.AdvancedFiniteGroupRepresentations.multiplicity_trace_averageType.{u} := by
  intro V _ _ _ n p σ hσ g
  have hs : σ = canonicalSpechtRepresentation p := by
    apply MonoidHom.ext
    intro s
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact hσ s v
  subst σ
  symm
  calc
    _ = (n.factorial : ℂ)⁻¹ * ∑ s : SymmetricGroup n,
        (canonicalSpechtRepresentation p).character s⁻¹ *
          ∑ q : Partition n, (canonicalSpechtRepresentation q).character s *
            LinearMap.trace ℂ (TensorMultiplicity V q) (tensorMultiplicityOperator V q g) := by
      simp_rw [← tensor_cycle_trace V n, tensor_trace_decomposition V n]
    _ = ∑ q : Partition n,
        ((n.factorial : ℂ)⁻¹ * ∑ s : SymmetricGroup n,
          (canonicalSpechtRepresentation p).character s⁻¹ *
            (canonicalSpechtRepresentation q).character s) *
          LinearMap.trace ℂ (TensorMultiplicity V q) (tensorMultiplicityOperator V q g) := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [specht_character_orthogonality]
      simp

end AdvancedFiniteGroupRepresentations
