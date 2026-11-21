import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.CharacterConstructions
import MathGenome.Internal.AlgebraCore.P103.Ch08.RepresentationModules
import MathGenome.Internal.AlgebraCore.P103.Ch01.BalancedTensor

noncomputable section
namespace P103.Ch08
def character : CharacterSpecs.characterType := @CharacterSpecs.characterValue

def contragredient : CharacterSpecs.contragredientType := @CharacterSpecs.dualValue

def directSumRepresentation : CharacterSpecs.directSumRepresentationType := @CharacterSpecs.sumValue

def diagonalRepresentation : CharacterSpecs.diagonalRepresentationType := @CharacterSpecs.tensorValue

theorem character_conjugate : CharacterSpecs.character_conjugateType := by
  intro k G V _ _ _ _ _ ρ g h
  unfold CharacterSpecs.characterValue
  simp only [map_mul]
  rw [LinearMap.trace_mul_comm]
  simp only [← map_mul, inv_mul_cancel_left]

theorem contragredient_apply : CharacterSpecs.contragredient_applyType := by
  unfold CharacterSpecs.contragredient_applyType
  intros; rfl

theorem directSum_apply : CharacterSpecs.directSum_applyType := by
  unfold CharacterSpecs.directSum_applyType
  intros; rfl

theorem diagonal_apply : CharacterSpecs.diagonal_applyType := by
  unfold CharacterSpecs.diagonal_applyType
  intros
  exact TensorProduct.map_tmul ..

theorem character_contragredient : CharacterSpecs.character_contragredientType := by
  unfold CharacterSpecs.character_contragredientType
  intros
  exact LinearMap.trace_transpose' _

theorem character_directSum : CharacterSpecs.character_directSumType := by
  unfold CharacterSpecs.character_directSumType
  intros
  exact LinearMap.trace_prodMap' _ _

theorem character_diagonal : CharacterSpecs.character_diagonalType := by
  unfold CharacterSpecs.character_diagonalType
  intros
  exact LinearMap.trace_tensorProduct' _ _

theorem balancedTensor_construction : CharacterSpecs.balancedTensor_constructionType := by
  intro k G V _ _ _ _ W _ _ _ _ ρ σ
  letI := BalancedTensor.commRightModule k V
  obtain ⟨m, hr, hl, e, he, hei⟩ :=
    BalancedTensor.satisfiesCommutativeComparison k V W
  letI := m
  letI := FiniteDimensional.of_injective e.toLinearMap e.injective
  let τ : Representation k G (BalancedTensor.Tensor k V W) :=
    e.symm.conjRingEquiv.toMonoidHom.comp (CharacterSpecs.tensorValue ρ σ)
  refine ⟨m, hl, hr, inferInstance, τ, e, he, hei, ?_, ?_, ?_⟩
  · intro g a b
    change e.symm (CharacterSpecs.tensorValue ρ σ g (e (BalancedTensor.tmul k a b))) = _
    rw [he]
    change e.symm (TensorProduct.map (ρ g) (σ g) (TensorProduct.tmul k a b)) = _
    rw [TensorProduct.map_tmul, hei]
  · intro g z
    change e (e.symm (CharacterSpecs.tensorValue ρ σ g (e z))) = _
    exact e.apply_symm_apply _
  · intro g
    change LinearMap.trace k _ (e.symm.conj (CharacterSpecs.tensorValue ρ σ g)) = _
    rw [LinearMap.trace_conj']
    exact LinearMap.trace_tensorProduct' _ _

end P103.Ch08
