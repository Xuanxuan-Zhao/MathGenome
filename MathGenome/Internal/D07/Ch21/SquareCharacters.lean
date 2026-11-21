import MathGenome.Internal.D07.Ch17.Characters
import MathGenome.Internal.D07.Ch21.DualTensor
import MathGenome.Internal.Specs.D07.Ch21.SquareCharacters
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

namespace D07.Ch21.SquareCharacters
universe u v w
noncomputable section
open scoped TensorProduct
open Specs.D07.Ch21.SquareCharacters

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

@[simp] theorem flip_flip (x : TensorSquare V) : flip V (flip V x) = x :=
  TensorProduct.comm_comm ℂ V V x

@[simp] theorem flip_tmul (a b : V) : flip V (a ⊗ₜ[ℂ] b) = b ⊗ₜ[ℂ] a := rfl

theorem flip_laws : FlipLaws.{u} := by
  intro V _ _
  refine ⟨flip_tmul, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    exact flip_flip x
  · intro A
    exact TensorProduct.map_comp_comm_eq A A

@[simp] theorem projector_plus_apply (x : TensorSquare V) :
    projector V 1 x = (2 : ℂ)⁻¹ • (x + flip V x) := by
  simp [projector]

@[simp] theorem projector_minus_apply (x : TensorSquare V) :
    projector V (-1) x = (2 : ℂ)⁻¹ • (x - flip V x) := by
  simp [projector, sub_eq_add_neg]

theorem plus_idempotent : IsIdempotentElem (projector V 1) := by
  apply LinearMap.ext
  intro x
  change projector V 1 (projector V 1 x) = projector V 1 x
  simp only [projector_plus_apply, map_smul, map_add, flip_flip]
  module

theorem minus_idempotent : IsIdempotentElem (projector V (-1)) := by
  apply LinearMap.ext
  intro x
  change projector V (-1) (projector V (-1) x) = projector V (-1) x
  simp only [projector_minus_apply, map_smul, map_sub, flip_flip]
  module

theorem projectors_sum : projector V 1 + projector V (-1) = 1 := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.add_apply, projector_plus_apply, projector_minus_apply,
    Module.End.one_apply]
  module

theorem plus_mul_minus : projector V 1 * projector V (-1) = 0 := by
  apply LinearMap.ext
  intro x
  change projector V 1 (projector V (-1) x) = 0
  simp only [projector_plus_apply, projector_minus_apply, map_smul, map_sub, flip_flip]
  module

theorem minus_mul_plus : projector V (-1) * projector V 1 = 0 := by
  apply LinearMap.ext
  intro x
  change projector V (-1) (projector V 1 x) = 0
  simp only [projector_plus_apply, projector_minus_apply, map_smul, map_add, flip_flip]
  module

theorem ker_plus : LinearMap.ker (projector V 1) = squareSpace V (-1) := by
  have h : 1 - projector V (-1) = projector V 1 := by
    rw [← projectors_sum (V := V)]
    abel
  rw [← h]
  exact (LinearMap.IsIdempotentElem.range_eq_ker_one_sub (minus_idempotent (V := V))).symm

theorem projectors_complementary : IsCompl (squareSpace V 1) (squareSpace V (-1)) := by
  rw [← ker_plus]
  exact LinearMap.IsIdempotentElem.isCompl (plus_idempotent (V := V))

theorem mem_plus_iff (x : TensorSquare V) :
    x ∈ squareSpace V 1 ↔ flip V x = x := by
  rw [LinearMap.IsIdempotentElem.mem_range_iff (plus_idempotent (V := V))]
  constructor
  · intro h
    have hh := congrArg (fun y => (2 : ℂ) • y) h
    simp only [projector_plus_apply, smul_smul] at hh
    norm_num at hh
    exact add_left_cancel (by simpa only [two_smul] using hh)
  · intro h
    rw [projector_plus_apply, h]
    module

theorem mem_minus_iff (x : TensorSquare V) :
    x ∈ squareSpace V (-1) ↔ flip V x = -x := by
  rw [LinearMap.IsIdempotentElem.mem_range_iff (minus_idempotent (V := V))]
  constructor
  · intro h
    have hh := congrArg (fun y => (2 : ℂ) • y) h
    simp only [projector_minus_apply, smul_smul] at hh
    norm_num at hh
    have hn : - flip V x = x := add_left_cancel (by
      simpa only [two_smul, sub_eq_add_neg] using hh)
    exact neg_eq_iff_eq_neg.mp hn
  · intro h
    rw [projector_minus_apply, h]
    module

theorem projector_laws : ProjectorLaws.{u} := by
  intro V _ _
  exact ⟨plus_idempotent, minus_idempotent, projectors_sum, plus_mul_minus,
    minus_mul_plus, projectors_complementary, mem_plus_iff, mem_minus_iff⟩

theorem square_action_laws : SquareActionLaws.{u,v} := by
  intro V G _ _ _ ρ s
  let σ := squareRepresentation ρ s
  refine ⟨fun _ _ => rfl, σ.map_one, σ.map_mul, ?_⟩
  intro g
  constructor <;> rw [← map_mul] <;> simp

/-- Commutation makes the image invariant. -/
theorem range_invariant {E : Type u} [AddCommGroup E] [Module ℂ E]
    (P T : Module.End ℂ E) (h : Commute T P) :
    ∀ x, x ∈ LinearMap.range P → T x ∈ LinearMap.range P := by
  rintro x ⟨y, rfl⟩
  exact ⟨T y, (LinearMap.congr_fun h.eq y).symm⟩

theorem kernel_invariant {E : Type u} [AddCommGroup E] [Module ℂ E]
    (P T : Module.End ℂ E) (h : Commute T P) :
    ∀ x, x ∈ LinearMap.ker P → T x ∈ LinearMap.ker P := by
  intro x hx
  change P (T x) = 0
  have hc : T (P x) = P (T x) := LinearMap.congr_fun h.eq x
  rw [← hc]
  rw [show P x = 0 from hx, map_zero]

theorem projection_blocks : ProjectionBlocks.{u} := by
  intro E _ _ P T hP hT
  refine ⟨LinearMap.IsIdempotentElem.isCompl hP,
    range_invariant P T hT, kernel_invariant P T hT, ?_, ?_⟩
  · intro x y
    exact map_add T (x : E) (y : E)
  · intro x y
    change T (P ((x : E) + y)) = T x
    rw [map_add, (LinearMap.IsIdempotentElem.mem_range_iff hP).mp x.property,
      show P y = 0 from y.property, add_zero]

/-- Cyclicity of trace between the ambient space and the image avoids choosing
adapted bases. The projection is the identity on its image. -/
theorem trace_projection {E : Type u} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (P T : Module.End ℂ E)
    (hP : IsIdempotentElem P) (hT : Commute T P) :
    LinearMap.trace ℂ E (T * P) =
      LinearMap.trace ℂ (LinearMap.range P) (T.restrict (range_invariant P T hT)) := by
  let f : E →ₗ[ℂ] LinearMap.range P := P.rangeRestrict
  let i : LinearMap.range P →ₗ[ℂ] E := (LinearMap.range P).subtype
  have hTP : T * P = (T.comp i).comp f := rfl
  rw [hTP, LinearMap.trace_comp_comm']
  congr 1
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change P (T x) = T x
  exact (LinearMap.IsIdempotentElem.mem_range_iff hP).mp (range_invariant P T hT x x.property)

theorem projection_trace : ProjectionTrace.{u} := by
  intro E _ _ _ P T hP hT
  exact ⟨range_invariant P T hT, trace_projection P T hP hT⟩

theorem flip_matrix_entries {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ V) (A : Module.End ℂ V) (i j : ι × ι) :
    LinearMap.toMatrix (b.tensorProduct b) (b.tensorProduct b)
        (TensorProduct.map A A * flip V) i j =
      LinearMap.toMatrix b b A i.1 j.2 * LinearMap.toMatrix b b A i.2 j.1 := by
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp [LinearMap.toMatrix_apply, Specs.D07.Ch21.SquareCharacters.flip, mul_comm]

theorem flip_matrix_trace : FlipMatrixTrace.{u,w} := by
  intro V _ _ ι _ _ b A
  refine ⟨flip_matrix_entries b A, ?_, ?_⟩
  · rw [LinearMap.trace_eq_matrix_trace ℂ (b.tensorProduct b)]
    simp only [Matrix.trace, Matrix.diag, flip_matrix_entries, Fintype.sum_prod_type]
  · rw [LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.toMatrix_mul]
    rfl

/-- The image of antisymmetrization is generated by the usual skew relations. -/
theorem minus_mem_symmetricRelations (x : TensorSquare V) :
    projector V (-1) x ∈ symmetricRelations V := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [projector_minus_apply, flip_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, b, rfl⟩)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- Polarization identifies symmetric tensors with the span of pure squares. -/
theorem plus_mem_exteriorRelations (x : TensorSquare V) :
    projector V 1 x ∈ exteriorRelations V := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [projector_plus_apply, flip_tmul]
    apply Submodule.smul_mem
    have ha : a ⊗ₜ[ℂ] a ∈ exteriorRelations V := Submodule.subset_span ⟨a, rfl⟩
    have hb : b ⊗ₜ[ℂ] b ∈ exteriorRelations V := Submodule.subset_span ⟨b, rfl⟩
    have hab : (a+b) ⊗ₜ[ℂ] (a+b) ∈ exteriorRelations V :=
      Submodule.subset_span ⟨a+b, rfl⟩
    have heq : a ⊗ₜ[ℂ] b + b ⊗ₜ[ℂ] a =
        (a+b) ⊗ₜ[ℂ] (a+b) - a ⊗ₜ[ℂ] a - b ⊗ₜ[ℂ] b := by
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel
    rw [heq]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ hab ha) hb
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

theorem symmetricRelations_eq_ker :
    symmetricRelations V = LinearMap.ker (projector V 1) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, b, rfl⟩
    change projector V 1 (a ⊗ₜ[ℂ] b - b ⊗ₜ[ℂ] a) = 0
    simp only [projector_plus_apply, map_sub, flip_tmul]
    module
  · intro x hx
    have hsum := LinearMap.congr_fun (projectors_sum (V := V)) x
    have hx0 : projector V 1 x = 0 := hx
    have heq : projector V (-1) x = x := by simpa [hx0] using hsum
    rw [← heq]
    exact minus_mem_symmetricRelations x

theorem exteriorRelations_eq_ker :
    exteriorRelations V = LinearMap.ker (projector V (-1)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨a, rfl⟩
    change projector V (-1) (a ⊗ₜ[ℂ] a) = 0
    simp
  · intro x hx
    have hsum := LinearMap.congr_fun (projectors_sum (V := V)) x
    have hx0 : projector V (-1) x = 0 := hx
    have heq : projector V 1 x = x := by simpa [hx0] using hsum
    rw [← heq]
    exact plus_mem_exteriorRelations x

theorem quotient_models : QuotientModels.{u} := by
  intro V _ _
  constructor
  · let e := (Submodule.quotEquivOfEq _ _ (symmetricRelations_eq_ker (V := V))).trans
      (projector V 1).quotKerEquivRange
    exact ⟨e, fun _ => rfl⟩
  · let e := (Submodule.quotEquivOfEq _ _ (exteriorRelations_eq_ker (V := V))).trans
      (projector V (-1)).quotKerEquivRange
    exact ⟨e, fun _ => rfl⟩

theorem tensor_commutes_projector (A : Module.End ℂ V) (s : ℂ) :
    Commute (TensorProduct.map A A) (projector V s) := by
  apply LinearMap.ext
  intro x
  simp [projector, Specs.D07.Ch21.SquareCharacters.flip, TensorProduct.map_comm]

/-- Transport across an identification whose value on each tensor class is
specified; the induced action on classes is then forced by commutation. -/
theorem quotient_action {G : Type v} [Group G] (ρ : Representation ℂ G V)
    (s : ℂ) (R : Submodule ℂ (TensorSquare V))
    (e : (TensorSquare V ⧸ R) ≃ₗ[ℂ] squareSpace V s)
    (he : ∀ t, (e (R.mkQ t) : TensorSquare V) = projector V s t) :
    ∃ τ : Representation ℂ G (TensorSquare V ⧸ R),
      ∃ e' : τ.Equiv (squareRepresentation ρ s),
        (∀ t, (e' (R.mkQ t) : TensorSquare V) = projector V s t) ∧
        ∀ g t, τ g (R.mkQ t) = R.mkQ ((ρ.tprod ρ) g t) := by
  let σ := squareRepresentation ρ s
  let τ : Representation ℂ G (TensorSquare V ⧸ R) := {
    toFun := fun g => e.symm.toLinearMap.comp ((σ g).comp e.toLinearMap)
    map_one' := by
      apply LinearMap.ext
      intro x
      simp
    map_mul' := by
      intro g h
      apply LinearMap.ext
      intro x
      simp [map_mul] }
  let e' : τ.Equiv σ := {
    toLinearEquiv := e
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro x
      change e (e.symm (σ g (e x))) = σ g (e x)
      exact e.apply_symm_apply _ }
  refine ⟨τ, e', he, ?_⟩
  intro g t
  apply e.injective
  change e (e.symm (σ g (e (R.mkQ t)))) = e (R.mkQ ((ρ.tprod ρ) g t))
  rw [e.apply_symm_apply]
  apply Subtype.ext
  change (ρ.tprod ρ) g (e (R.mkQ t) : TensorSquare V) =
    (e (R.mkQ ((ρ.tprod ρ) g t)) : TensorSquare V)
  rw [he, he]
  exact LinearMap.congr_fun (tensor_commutes_projector (ρ g) s).eq t

theorem quotient_actions : QuotientActions.{u,v} := by
  intro V G _ _ _ ρ
  obtain ⟨⟨es, hs⟩, ⟨ea, ha⟩⟩ := quotient_models V
  exact ⟨quotient_action ρ 1 (symmetricRelations V) es hs,
    quotient_action ρ (-1) (exteriorRelations V) ea ha⟩

theorem trace_tensor_flip [FiniteDimensional ℂ V] (A : Module.End ℂ V) :
    LinearMap.trace ℂ (TensorSquare V) (TensorProduct.map A A * flip V) =
      LinearMap.trace ℂ V (A * A) := by
  have h := flip_matrix_trace V (Fin (Module.finrank ℂ V)) (Module.finBasis ℂ V) A
  exact h.2.1.trans h.2.2

theorem trace_tensor_projector [FiniteDimensional ℂ V] (A : Module.End ℂ V) (s : ℂ) :
    LinearMap.trace ℂ (TensorSquare V) (TensorProduct.map A A * projector V s) =
      (2 : ℂ)⁻¹ * (LinearMap.trace ℂ V A ^ 2 + s * LinearMap.trace ℂ V (A * A)) := by
  rw [projector, mul_smul_comm, mul_add, mul_one, mul_smul_comm,
    map_smul, map_add, map_smul]
  rw [LinearMap.trace_tensorProduct', trace_tensor_flip]
  simp only [smul_eq_mul, pow_two]

theorem square_characters : CharacterFormulas.{u,v} := by
  intro V G _ _ _ _ _ ρ g
  have ht (s : ℂ) (hs : IsIdempotentElem (projector V s)) :
      LinearMap.trace ℂ (squareSpace V s) (squareRepresentation ρ s g) =
        (2 : ℂ)⁻¹ * (LinearMap.trace ℂ V (ρ g) ^ 2 +
          s * LinearMap.trace ℂ V (ρ (g ^ 2))) := by
    have hcomm := tensor_commutes_projector (ρ g) s
    have h := trace_projection (projector V s) (TensorProduct.map (ρ g) (ρ g)) hs hcomm
    change LinearMap.trace ℂ (squareSpace V s)
      ((TensorProduct.map (ρ g) (ρ g)).restrict
        (range_invariant (projector V s) (TensorProduct.map (ρ g) (ρ g)) hcomm)) = _
    rw [← h, trace_tensor_projector]
    simp only [pow_two, map_mul]
  constructor
  · change LinearMap.trace ℂ (squareSpace V 1) (squareRepresentation ρ 1 g) = _
    rw [ht 1 plus_idempotent]
    simp only [Specs.D07.Ch17.Characters.characterValue, one_mul, div_eq_mul_inv]
    ring
  · change LinearMap.trace ℂ (squareSpace V (-1)) (squareRepresentation ρ (-1) g) = _
    rw [ht (-1) minus_idempotent]
    simp only [Specs.D07.Ch17.Characters.characterValue, neg_one_mul, div_eq_mul_inv]
    ring

end
end D07.Ch21.SquareCharacters
