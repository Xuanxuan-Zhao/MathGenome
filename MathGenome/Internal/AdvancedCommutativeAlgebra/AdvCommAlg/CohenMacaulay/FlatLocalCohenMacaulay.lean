import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.FlatLocalDepth
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.FlatLocalCohenMacaulay
import Mathlib.RingTheory.KrullDimension.Field

/-! CM-10: the combined formulas, the Cohen–Macaulay criterion, and completion.
The two nonnegative depth defects add. Finite natural representatives ensure
that equality of the sum forces each defect to vanish. Completion is treated
as the actual inverse limit, using the canonical tensor comparison.
-/
universe u
open scoped TensorProduct Pointwise
open TensorProduct
noncomputable section
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
namespace AdvCommAlg.CohenMacaulay

/-- The CM predicate is preserved by an equivalence over the same local ring. -/
lemma localCohenMacaulay_iff_of_linearEquiv {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {U V : Type u}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [Module.Finite R U] [Module.Finite R V] (e : U ≃ₗ[R] V) :
    LocalCohenMacaulay R U ↔ LocalCohenMacaulay R V := by
  unfold LocalCohenMacaulay dimension
  rw [IsLocalRing.depth_eq_of_linearEquiv e, Module.supportDim_eq_of_equiv e]
  have hs : Subsingleton U ↔ Subsingleton V := e.toEquiv.subsingleton_congr
  rw [hs]

section Local
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Module.Finite R M] [Nontrivial M] [Module.Finite S N] [Nontrivial N]
    [Module.Flat R N]

/-- Vanishing of the total depth defect is equivalent to vanishing of both defects. -/
lemma tensor_cohenMacaulay_iff :
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
    let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
    let F := N ⧸ (J • (⊤ : Submodule S N))
    letI := Specs.closedFiberLocalRing R S
    letI : Module.Finite (S ⧸ J) F := Module.Finite.of_restrictScalars_finite S (S ⧸ J) F
    letI := Specs.rightTensorFinite R S M N
    LocalCohenMacaulay S (M ⊗[R] N) ↔
      LocalCohenMacaulay R M ∧ LocalCohenMacaulay (S ⧸ J) F := by
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  let F := N ⧸ (J • (⊤ : Submodule S N))
  letI := Specs.closedFiberLocalRing R S
  letI : Module.Finite (S ⧸ J) F := Module.Finite.of_restrictScalars_finite S (S ⧸ J) F
  letI := Specs.rightTensorFinite R S M N
  letI := closedFiber_nontrivial R S N
  letI := tensor_nontrivial_of_flatLocal R S N M
  change LocalCohenMacaulay S (M ⊗[R] N) ↔
    LocalCohenMacaulay R M ∧ LocalCohenMacaulay (S ⧸ J) F
  rw [localCohenMacaulay_iff_sourceDepth, localCohenMacaulay_iff_sourceDepth,
    localCohenMacaulay_iff_sourceDepth]
  change (Depth.depth S (M ⊗[R] N) : WithBot ℕ∞) = Module.supportDim S (M ⊗[R] N) ↔
    (Depth.depth R M : WithBot ℕ∞) = Module.supportDim R M ∧
    (Depth.depth (S ⧸ J) F : WithBot ℕ∞) = Module.supportDim (S ⧸ J) F
  have hd := flatLocal_tensor_depth R S M N
  change Depth.depth S (M ⊗[R] N) = Depth.depth R M + Depth.depth (S ⧸ J) F at hd
  rw [hd, flatLocal_tensor_dimension R S M N]
  obtain ⟨a, ha⟩ := FlatLocalDepth.exists_depth_eq_nat R M
  obtain ⟨b, hb⟩ := FlatLocalDepth.exists_depth_eq_nat (S ⧸ J) F
  obtain ⟨xs, hxs⟩ := exists_systemOfParameters R M
  obtain ⟨ys, hys⟩ := exists_systemOfParameters (S ⧸ J) F
  have hdimM : (xs.length : WithBot ℕ∞) = Module.supportDim R M := hxs.2.1
  have hdimF : (ys.length : WithBot ℕ∞) = Module.supportDim (S ⧸ J) F := hys.2.1
  have h₁ := Depth.depth_le_supportDim (R := R) M
  have h₂ := Depth.depth_le_supportDim (R := S ⧸ J) F
  rw [ha, ← hdimM] at h₁
  rw [hb, ← hdimF] at h₂
  have h₁' : a ≤ xs.length := by exact_mod_cast h₁
  have h₂' : b ≤ ys.length := by exact_mod_cast h₂
  rw [ha, hb, ← hdimM, ← hdimF]
  have he : a + b = xs.length + ys.length ↔ a = xs.length ∧ b = ys.length := by omega
  exact_mod_cast he
end Local

/-- The criterion with the source quantifiers and canonical scalar actions. -/
theorem flatLocal_tensor_cohenMacaulay : Specs.flatLocal_tensor_cohenMacaulayType.{u} := by
  intro R S _ _ _ _ _ _ _ _ M N _ _ _ _ _ _
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  intro _ _ _ _ _
  exact tensor_cohenMacaulay_iff R S M N

/-- All three conclusions of the flat local family theorem at once. -/
theorem flatLocal_tensor_formulas : Specs.flatLocal_tensor_formulasType.{u} := by
  intro R S _ _ _ _ _ _ _ _ M N _ _ _ _ _ _
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  intro _ _ _ _ _
  exact ⟨flatLocal_tensor_dimension R S M N, flatLocal_tensor_depth R S M N,
    flatLocal_tensor_cohenMacaulay R S M N⟩

/-- The quotient of the ring as a module is the usual quotient ring, linearly. -/
def quotientSelfEquiv (A : Type u) [CommRing A] (J : Ideal A) :
    (A ⧸ (J • (⊤ : Submodule A A))) ≃ₗ[A ⧸ J] (A ⧸ J) := by
  let e : (A ⧸ (J • (⊤ : Submodule A A))) ≃ₗ[A] (A ⧸ J) :=
    Submodule.quotEquivOfEq _ _ (by simp)
  refine { __ := e.toAddEquiv, map_smul' := ?_ }
  intro a x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change e (a • x) = a • e x
  exact e.map_smul a x

/-- Specialization to M = R, N = S gives the ring criterion. -/
theorem flatLocal_ring_cohenMacaulay : Specs.flatLocal_ring_cohenMacaulayType.{u} := by
  intro R S _ _ _ _ _ _ _ _ _
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  letI := Specs.closedFiberLocalRing R S
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) R S
  letI := Specs.rightTensorFinite R S R S
  let F := S ⧸ (J • (⊤ : Submodule S S))
  letI : Module.Finite (S ⧸ J) F := Module.Finite.of_restrictScalars_finite S (S ⧸ J) F
  let e : (R ⊗[R] S) ≃ₗ[S] S :=
    RegularSequence.rightTensorComm (S := S) R S ≪≫ₗ AlgebraTensorModule.rid R S S
  change LocalCohenMacaulay S S ↔
    LocalCohenMacaulay R R ∧ LocalCohenMacaulay (S ⧸ J) (S ⧸ J)
  rw [← localCohenMacaulay_iff_of_linearEquiv e]
  exact (tensor_cohenMacaulay_iff R S R S).trans
    (and_congr Iff.rfl (localCohenMacaulay_iff_of_linearEquiv (quotientSelfEquiv S J)))

/-- Faithful flatness of completion follows from its flat local map. -/
theorem completion_faithfullyFlat : Specs.completion_faithfullyFlatType.{u} := by
  intro R _ _ _
  letI := Specs.completionNoetherian R
  exact faithfullyFlat_of_flatLocal R (AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (AdicCompletion (IsLocalRing.maximalIdeal R) R)

/-- The canonical tensor comparison, with its formula on pure tensors. -/
theorem completion_tensor_comparison : Specs.completion_tensor_comparisonType.{u} := by
  intro R L _ _ _ _ _ _
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := A) L A
  let e := RegularSequence.rightTensorComm (S := A) L A ≪≫ₗ
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (IsLocalRing.maximalIdeal R) L
  exact ⟨e, fun l a => rfl⟩

/-- The completed ring has zero-dimensional closed fiber, as a module. -/
lemma completion_fiber_dimension (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] :
    let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
    let J := (IsLocalRing.maximalIdeal R).map (algebraMap R A)
    Module.supportDim (A ⧸ J) (A ⧸ (J • (⊤ : Submodule A A))) = 0 := by
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R A)
  have hJ : J = IsLocalRing.maximalIdeal A := (AdicCompletion.maximalIdeal_eq_map (R := R)).symm
  letI : J.IsMaximal := hJ ▸ IsLocalRing.maximalIdeal.isMaximal A
  change Module.supportDim (A ⧸ J) (A ⧸ (J • (⊤ : Submodule A A))) = 0
  rw [Module.supportDim_eq_of_equiv (quotientSelfEquiv A J),
    Module.supportDim_self_eq_ringKrullDim]
  letI := Ideal.Quotient.field J
  exact ringKrullDim_eq_zero_of_field (A ⧸ J)

/-- In the completed-ring fiber the source depth is zero. -/
lemma completion_fiber_depth (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] :
    let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
    let J := (IsLocalRing.maximalIdeal R).map (algebraMap R A)
    letI := Specs.closedFiberLocalRing R A
    Depth.depth (A ⧸ J) (A ⧸ (J • (⊤ : Submodule A A))) = 0 := by
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R A)
  let F := A ⧸ (J • (⊤ : Submodule A A))
  letI := Specs.completionNoetherian R
  letI := Specs.closedFiberLocalRing R A
  letI := closedFiber_nontrivial R A A
  letI : Module.Finite (A ⧸ J) F := Module.Finite.of_restrictScalars_finite A (A ⧸ J) F
  change Depth.depth (A ⧸ J) F = 0
  have hb := Depth.depth_le_supportDim (R := A ⧸ J) F
  rw [completion_fiber_dimension R] at hb
  exact le_antisymm (WithBot.coe_le_coe.mp hb) zero_le

/-- Completion of the zero module is again zero. -/
lemma completion_subsingleton (R L : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [AddCommGroup L] [Module R L] [Module.Finite R L] [Subsingleton L] :
    Subsingleton (AdicCompletion (IsLocalRing.maximalIdeal R) L) := by
  let e := AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (IsLocalRing.maximalIdeal R) L
  exact ⟨fun x y => e.symm.injective (Subsingleton.elim _ _)⟩

/-- Dimension is unchanged by completion, including bottom for the zero module. -/
theorem completion_dimension : Specs.completion_dimensionType.{u} := by
  intro R L _ _ _ _ _ _
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  letI := Specs.completionNoetherian R
  rcases subsingleton_or_nontrivial L with hL | hL
  · letI := hL
    letI := completion_subsingleton R L
    rw [Module.supportDim_eq_bot_of_subsingleton, Module.supportDim_eq_bot_of_subsingleton]
  · letI := hL
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := A) L A
    obtain ⟨e, _⟩ := completion_tensor_comparison R L
    have hd := flatLocal_tensor_dimension R A L A
    dsimp only at hd
    rw [completion_fiber_dimension R, add_zero] at hd
    exact (Module.supportDim_eq_of_equiv e).symm.trans hd

/-- Source regular-sequence depth is unchanged, including infinity for zero. -/
theorem completion_depth : Specs.completion_depthType.{u} := by
  intro R L _ _ _ _ _ _
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  letI := Specs.completionNoetherian R
  letI := Specs.completionFinite R L
  change Depth.depth A (AdicCompletion (IsLocalRing.maximalIdeal R) L) = Depth.depth R L
  rcases subsingleton_or_nontrivial L with hL | hL
  · letI := hL
    letI := completion_subsingleton R L
    rw [Depth.depth_eq_top_of_subsingleton, Depth.depth_eq_top_of_subsingleton]
  · letI := hL
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := A) L A
    letI := Specs.rightTensorFinite R A L A
    obtain ⟨e, _⟩ := completion_tensor_comparison R L
    letI := Specs.closedFiberLocalRing R A
    have hd := flatLocal_tensor_depth R A L A
    change Depth.depth A (L ⊗[R] A) = Depth.depth R L +
      Depth.depth (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))
        (A ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R A) • (⊤ : Submodule A A))) at hd
    rw [completion_fiber_depth R, add_zero] at hd
    exact (FlatLocalDepth.depth_eq_of_linearEquiv e).symm.trans hd

/-- The local Cohen–Macaulay property is equivalent before and after completion. -/
theorem completion_cohenMacaulay : Specs.completion_cohenMacaulayType.{u} := by
  intro R L _ _ _ _ _ _
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let C := AdicCompletion (IsLocalRing.maximalIdeal R) L
  letI := Specs.completionNoetherian R
  letI := Specs.completionFinite R L
  change LocalCohenMacaulay A C ↔ LocalCohenMacaulay R L
  rcases subsingleton_or_nontrivial L with hL | hL
  · letI := hL
    letI := completion_subsingleton R L
    exact iff_of_true (localCohenMacaulay_of_subsingleton A C)
      (localCohenMacaulay_of_subsingleton R L)
  · letI := hL
    letI := completion_faithfullyFlat R
    letI := RegularSequence.Specs.rightTensorModule (R := R) (S := A) L A
    obtain ⟨e, _⟩ := completion_tensor_comparison R L
    letI : Nontrivial C := e.nontrivial_congr.mp inferInstance
    rw [localCohenMacaulay_iff_sourceDepth, localCohenMacaulay_iff_sourceDepth]
    have hd := completion_depth R L
    change Depth.depth A C = Depth.depth R L at hd
    unfold dimension
    rw [hd, completion_dimension R L]

end AdvCommAlg.CohenMacaulay
