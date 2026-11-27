import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.OperatorRing
import Mathlib.RingTheory.TensorProduct.Maps
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.OperatorTensor

namespace GaloisFormalization.PV.Operator

open scoped TensorProduct

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

private theorem derivation_smul {d : Operator .differential R} {e : Operator .differential S}
    (h : d.IsAlgebra e) (r : R) (s : S) :
    e.toDerivation (r • s) = r • e.toDerivation s + d.toDerivation r • s := by
  have hr : algebraMap R S (d.toDerivation r) = e.toDerivation (algebraMap R S r) := h r
  rw [Algebra.smul_def r s, e.toDerivation.leibniz, ← hr]
  simp only [smul_eq_mul, Algebra.smul_def, mul_comm s]

private def derivationOnFactors (e : Derivation ℤ S S) (f : Derivation ℤ T T) :
    S →+ T →+ S ⊗[R] T where
  toFun s :=
    { toFun := fun t => e s ⊗ₜ[R] t + s ⊗ₜ[R] f t
      map_zero' := by simp
      map_add' := fun t t' => by simp only [f.map_add, TensorProduct.tmul_add]; abel }
  map_zero' := AddMonoidHom.ext fun t => by simp
  map_add' s s' := AddMonoidHom.ext fun t => by
    simp only [AddMonoidHom.coe_mk, AddMonoidHom.add_apply, ZeroHom.coe_mk,
      e.map_add, TensorProduct.add_tmul]
    abel

private theorem derivationOnFactors_balanced
    {d : Operator .differential R} {e : Operator .differential S} {f : Operator .differential T}
    (hS : d.IsAlgebra e) (hT : d.IsAlgebra f) (r : R) (s : S) (t : T) :
    derivationOnFactors (R := R) e.toDerivation f.toDerivation (r • s) t =
      derivationOnFactors e.toDerivation f.toDerivation s (r • t) := by
  -- The two Leibniz expansions match after transferring both r and its derivative.
  change e.toDerivation (r • s) ⊗ₜ[R] t + (r • s) ⊗ₜ[R] f.toDerivation t =
    e.toDerivation s ⊗ₜ[R] (r • t) + s ⊗ₜ[R] f.toDerivation (r • t)
  simp only [derivation_smul hS, derivation_smul hT, TensorProduct.add_tmul,
    TensorProduct.tmul_add, TensorProduct.smul_tmul]
  abel

private def tensorDerivationAddHom
    {d : Operator .differential R} {e : Operator .differential S} {f : Operator .differential T}
    (hS : d.IsAlgebra e) (hT : d.IsAlgebra f) : S ⊗[R] T →+ S ⊗[R] T :=
  TensorProduct.liftAddHom (derivationOnFactors e.toDerivation f.toDerivation)
    (derivationOnFactors_balanced hS hT)

private theorem tensorDerivationAddHom_tmul
    {d : Operator .differential R} {e : Operator .differential S} {f : Operator .differential T}
    (hS : d.IsAlgebra e) (hT : d.IsAlgebra f) (s : S) (t : T) :
    tensorDerivationAddHom hS hT (s ⊗ₜ[R] t) =
      e.toDerivation s ⊗ₜ[R] t + s ⊗ₜ[R] f.toDerivation t := rfl

private def tensorDerivation
    {d : Operator .differential R} {e : Operator .differential S} {f : Operator .differential T}
    (hS : d.IsAlgebra e) (hT : d.IsAlgebra f) : Derivation ℤ (S ⊗[R] T) (S ⊗[R] T) :=
  Derivation.mk' (tensorDerivationAddHom hS hT).toIntLinearMap <| by
    intro x y
    let g := tensorDerivationAddHom hS hT
    change g (x * y) = x * g y + y * g x
    induction x using TensorProduct.inductionOn with
    | tmul s t =>
      induction y using TensorProduct.inductionOn with
      | tmul s' t' =>
        simp only [g, Algebra.TensorProduct.tmul_mul_tmul, tensorDerivationAddHom_tmul,
          Derivation.leibniz, smul_eq_mul, TensorProduct.add_tmul, TensorProduct.tmul_add,
          mul_add]
        rw [mul_comm t' t, mul_comm s' s]
        abel
      | add y y' hy hy' =>
        rw [mul_add, g.map_add, hy, hy', g.map_add, mul_add, add_mul]
        abel
    | add x x' hx hx' =>
      rw [add_mul, g.map_add, hx, hx', g.map_add, mul_add, add_mul]
      abel

private def tensorDifferenceHom
    {d : Operator .difference R} {e : Operator .difference S} {f : Operator .difference T}
    (hS : d.IsAlgebra e) (hT : d.IsAlgebra f) : (S ⊗[R] T) →+* S ⊗[R] T :=
  Algebra.TensorProduct.mapRingHom d.toRingEquiv.toRingHom e.toRingEquiv.toRingHom
    f.toRingEquiv.toRingHom (RingHom.ext fun r => (hS r).symm) (RingHom.ext fun r => (hT r).symm)

private theorem tensorDifferenceHom_tmul
    {d : Operator .difference R} {e : Operator .difference S} {f : Operator .difference T}
    (hS : d.IsAlgebra e) (hT : d.IsAlgebra f) (s : S) (t : T) :
    tensorDifferenceHom hS hT (s ⊗ₜ[R] t) = e.toRingEquiv s ⊗ₜ[R] f.toRingEquiv t :=
  Algebra.TensorProduct.mapRingHom_tmul _ _ _ _ _ s t

private def tensorDifference
    {d : Operator .difference R} {e : Operator .difference S} {f : Operator .difference T}
    (hS : d.IsAlgebra e) (hT : d.IsAlgebra f) : (S ⊗[R] T) ≃+* S ⊗[R] T := by
  have hS' : (difference d.toRingEquiv.symm).IsAlgebra (difference e.toRingEquiv.symm) :=
    hS.difference_symm
  have hT' : (difference d.toRingEquiv.symm).IsAlgebra (difference f.toRingEquiv.symm) :=
    hT.difference_symm
  have eqOnTensors {g h : (S ⊗[R] T) →+* S ⊗[R] T}
      (eq : ∀ s t, g (s ⊗ₜ[R] t) = h (s ⊗ₜ[R] t)) : g = h := by
    apply _root_.RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s t => exact eq s t
    | add x y hx hy => rw [g.map_add, h.map_add, hx, hy]
  refine _root_.RingEquiv.ofRingHom (tensorDifferenceHom hS hT) (tensorDifferenceHom hS' hT')
    (eqOnTensors ?_) (eqOnTensors ?_)
  · intro s t
    rw [_root_.RingHom.comp_apply, tensorDifferenceHom_tmul hS' hT',
      tensorDifferenceHom_tmul hS hT]
    change e.toRingEquiv (e.toRingEquiv.symm s) ⊗ₜ[R]
      f.toRingEquiv (f.toRingEquiv.symm t) = s ⊗ₜ[R] t
    rw [e.toRingEquiv.apply_symm_apply, f.toRingEquiv.apply_symm_apply]
  · intro s t
    rw [_root_.RingHom.comp_apply, tensorDifferenceHom_tmul hS hT,
      tensorDifferenceHom_tmul hS' hT']
    change e.toRingEquiv.symm (e.toRingEquiv s) ⊗ₜ[R]
      f.toRingEquiv.symm (f.toRingEquiv t) = s ⊗ₜ[R] t
    rw [e.toRingEquiv.symm_apply_apply, f.toRingEquiv.symm_apply_apply]

variable {kind : OperatorKind} {D : Operator kind R} {E : Operator kind S} {F : Operator kind T}

/-- The operator on the tensor product of two algebras over a common operator ring. -/
def tensor (hS : D.IsAlgebra E) (hT : D.IsAlgebra F) : Operator kind (S ⊗[R] T) :=
  match kind with
  | .differential => differential (tensorDerivation hS hT)
  | .difference => difference (tensorDifference hS hT)

section Differential

variable {d : Operator .differential R} {e : Operator .differential S} {f : Operator .differential T}

@[simp] theorem tensor_differential_tmul (hS : d.IsAlgebra e) (hT : d.IsAlgebra f)
    (s : S) (t : T) : tensor hS hT (s ⊗ₜ[R] t) = e s ⊗ₜ[R] t + s ⊗ₜ[R] f t :=
  rfl

end Differential

section Difference

variable {d : Operator .difference R} {e : Operator .difference S} {f : Operator .difference T}

@[simp] theorem tensor_difference_tmul (hS : d.IsAlgebra e) (hT : d.IsAlgebra f)
    (s : S) (t : T) : tensor hS hT (s ⊗ₜ[R] t) = e s ⊗ₜ[R] f t :=
  tensorDifferenceHom_tmul hS hT s t

@[simp] theorem tensor_difference_symm_tmul (hS : d.IsAlgebra e) (hT : d.IsAlgebra f)
    (s : S) (t : T) :
    (tensor hS hT).toRingEquiv.symm (s ⊗ₜ[R] t) =
      e.toRingEquiv.symm s ⊗ₜ[R] f.toRingEquiv.symm t :=
  tensorDifferenceHom_tmul
    (d := difference d.toRingEquiv.symm) (e := difference e.toRingEquiv.symm)
    (f := difference f.toRingEquiv.symm) hS.difference_symm hT.difference_symm s t

end Difference

theorem tensor_commutes_includeLeft (hS : D.IsAlgebra E) (hT : D.IsAlgebra F) :
    E.Commutes (tensor hS hT) (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] T) := by
  intro s
  change E s ⊗ₜ[R] (1 : T) = tensor hS hT (s ⊗ₜ[R] (1 : T))
  cases kind with
  | differential =>
    rw [tensor_differential_tmul]
    have h : F 1 = 0 := F.toDerivation.map_one_eq_zero
    rw [h, TensorProduct.tmul_zero, add_zero]
  | difference =>
    rw [tensor_difference_tmul]
    have h : F 1 = 1 := F.toRingEquiv.map_one
    rw [h]

theorem tensor_commutes_includeRight (hS : D.IsAlgebra E) (hT : D.IsAlgebra F) :
    F.Commutes (tensor hS hT) (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T) := by
  intro t
  change (1 : S) ⊗ₜ[R] F t = tensor hS hT ((1 : S) ⊗ₜ[R] t)
  cases kind with
  | differential =>
    rw [tensor_differential_tmul]
    have h : E 1 = 0 := E.toDerivation.map_one_eq_zero
    rw [h, TensorProduct.zero_tmul, zero_add]
  | difference =>
    rw [tensor_difference_tmul]
    have h : E 1 = 1 := E.toRingEquiv.map_one
    rw [h]

/-- The base map to the tensor product also commutes with the operators. -/
theorem tensor_isAlgebra (hS : D.IsAlgebra E) (hT : D.IsAlgebra F) :
    D.IsAlgebra (tensor hS hT) :=
  (tensor_commutes_includeLeft hS hT).comp hS

theorem tensor_laws (hS : D.IsAlgebra E) (hT : D.IsAlgebra F) :
    Specs.tensorLaws E F (tensor hS hT) := by
  refine ⟨?_, tensor_commutes_includeLeft hS hT, tensor_commutes_includeRight hS hT⟩
  cases kind with
  | differential => exact tensor_differential_tmul hS hT
  | difference => exact ⟨tensor_difference_tmul hS hT, tensor_difference_symm_tmul hS hT⟩

private theorem tensor_ext {G H : Operator kind (S ⊗[R] T)}
    (h : ∀ s t, G (s ⊗ₜ[R] t) = H (s ⊗ₜ[R] t)) : G = H := by
  have hall (x : S ⊗[R] T) : G x = H x := by
    induction x using TensorProduct.inductionOn with
    | tmul s t => exact h s t
    | add x y hx hy => rw [Operator.map_add, Operator.map_add, hx, hy]
  cases kind with
  | differential => exact Derivation.ext hall
  | difference => exact _root_.RingEquiv.ext hall

theorem tensor_existsUnique : Specs.tensorExistsUnique := by
  intro kind R S T _ _ _ _ _ D E F hS hT
  refine ⟨tensor hS hT, tensor_laws hS hT, ?_⟩
  intro G hG
  apply tensor_ext
  intro s t
  cases kind with
  | differential => exact (hG.1 s t).trans (tensor_differential_tmul hS hT s t).symm
  | difference => exact (hG.1.1 s t).trans (tensor_difference_tmul hS hT s t).symm

/-- An arbitrary commutative algebra is compatible when both operators are trivial. -/
theorem trivial_isAlgebra (kind : OperatorKind) :
    (trivial kind R).IsAlgebra (trivial kind T) := by
  intro r
  cases kind with
  | differential => simp
  | difference => rfl

theorem tensor_constant_existsUnique : Specs.tensorConstantExistsUnique := by
  intro kind R S T _ _ _ _ _ E hS
  exact tensor_existsUnique hS (trivial_isAlgebra kind)

/-- Precomposition by a compatible base automorphism preserves compatibility. -/
theorem IsAlgebra.comp_operator_equiv (hS : D.IsAlgebra E) (τ : RingEquiv D D) :
    letI : Algebra R S := Algebra.compHom S τ.val.toRingHom
    D.IsAlgebra E :=
  hS.comp τ.property

theorem tensor_twisted_existsUnique : Specs.tensorTwistedExistsUnique := by
  intro kind R S T rRing sRing tRing sAlg tAlg D E F τ hS hT
  exact @tensor_existsUnique kind R S T rRing sRing tRing
    (Algebra.compHom S τ.val.toRingHom) tAlg D E F (IsAlgebra.comp_operator_equiv hS τ) hT

end GaloisFormalization.PV.Operator
