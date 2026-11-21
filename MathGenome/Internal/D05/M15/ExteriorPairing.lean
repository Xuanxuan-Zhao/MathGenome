import MathGenome.Internal.Specs.D05.M15.ExteriorPairing
import MathGenome.Internal.D05.M15.ExteriorBasis
import MathGenome.Internal.D05.M15.WedgeSign
import MathGenome.Internal.D05.M07.DualMap

noncomputable section
namespace D05.M15.ExteriorPairing

open Specs.D05.M15.ExteriorPairing

abbrev pairing := pairing_value
abbrev tensorEvaluation := tensorEvaluation_value
abbrev average := average_value

theorem elementary : Specs.D05.M15.ExteriorPairing.elementary := by
  intro K V _ _ _ p f x
  rw [pairing_value, exteriorPower.pairingDual_ιMulti_ιMulti]
  exact Matrix.det_transpose _

theorem unique_pairing : Specs.D05.M15.ExteriorPairing.unique_pairing := by
  intro K V _ _ _ p B hB
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro f
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  exact (hB f x).trans (elementary p f x).symm

theorem dual_basis : Specs.D05.M15.ExteriorPairing.dual_basis := by
  intro K V I _ _ _ _ _ b p s t
  classical
  change exteriorPower.pairingDual K V p
    (exteriorPower.ιMulti_family K p b.dualBasis s)
    (exteriorPower.ιMulti_family K p b t) = _
  rw [← exteriorPower.basis_apply, ← exteriorPower.basis_apply]
  rw [exteriorPower.pairingDual_apply_dualBasis_exteriorPower]
  simpa only [eq_comm] using (b.exteriorPower p).dualBasis_apply_self s t

theorem perfect : Specs.D05.M15.ExteriorPairing.perfect := by
  intro K V _ _ _ _ p
  exact ⟨LinearEquiv.ofBijective (pairing K V p)
    (exteriorPower.bijective_pairingDual K V p), rfl⟩

theorem naturality : Specs.D05.M15.ExteriorPairing.naturality := by
  intro K V W _ _ _ _ _ p T a x
  have h : (pairing K V p).comp (exteriorPower.map p T.dualMap) =
      (exteriorPower.map p T).dualMap.comp (pairing K W p) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro f
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change pairing K V p (exteriorPower.map p T.dualMap (exteriorPower.ιMulti K p f))
      (exteriorPower.ιMulti K p v) =
      pairing K W p (exteriorPower.ιMulti K p f)
        (exteriorPower.map p T (exteriorPower.ιMulti K p v))
    simp only [exteriorPower.map_apply_ιMulti]
    rw [elementary, elementary]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) x

theorem degree_zero : Specs.D05.M15.ExteriorPairing.degree_zero := by
  intro K V _ _ _ a b
  simp only [exteriorPower.zeroEquiv_symm_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  erw [elementary]
  erw [Matrix.det_isEmpty]
  simp only [mul_one]
  exact mul_comm _ _

theorem tensor_elementary : Specs.D05.M15.ExteriorPairing.tensor_elementary := by
  intro K V _ _ _ p f x
  exact TensorPower.pairingDual_tprod_tprod f x

theorem average_elementary : Specs.D05.M15.ExteriorPairing.average_elementary := by
  intro K V _ _ _ p x
  simp only [average_value, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [D05.M15.Exterior.projection_elementary]
  rw [exteriorPower.toTensorPower_apply_ιMulti]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun σ => by
    simp [Equiv.Perm.inv_def, Function.comp_def])

/-- One signed tensor lift is adjoint to passing to the exterior quotient. -/
theorem tensor_pairing_toTensor {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (f : Fin p → Module.Dual K V) (x : ⋀[K]^p V) :
    tensorEvaluation K V p (PiTensorProduct.tprod K f)
      (exteriorPower.toTensorPower K V p x) =
      pairing K V p (exteriorPower.ιMulti K p f) x := by
  rw [pairing, pairing_value, exteriorPower.pairingDual,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change PiTensorProduct.lift (TensorPower.multilinearMapToDual K V p)
    (PiTensorProduct.tprod K f) _ = _
  rw [PiTensorProduct.lift.tprod]
  rfl

/-- Before normalization the two signed lifts contribute precisely p!. -/
theorem tensor_pairing_antisym {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) (a : ⋀[K]^p (Module.Dual K V)) (x : ⋀[K]^p V) :
    tensorEvaluation K V p (exteriorPower.toTensorPower K (Module.Dual K V) p a)
      (exteriorPower.toTensorPower K V p x) =
      (Nat.factorial p : K) * pairing K V p a x := by
  have h : (exteriorPower.toTensorPower K V p).dualMap.comp
      ((tensorEvaluation K V p).comp (exteriorPower.toTensorPower K (Module.Dual K V) p)) =
      (Nat.factorial p : K) • pairing K V p := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro f
    apply LinearMap.ext
    intro y
    change tensorEvaluation K V p
      (exteriorPower.toTensorPower K (Module.Dual K V) p (exteriorPower.ιMulti K p f))
      (exteriorPower.toTensorPower K V p y) =
      (Nat.factorial p : K) * pairing K V p (exteriorPower.ιMulti K p f) y
    rw [exteriorPower.toTensorPower_apply_ιMulti]
    simp only [map_sum, LinearMap.sum_apply, map_zsmul_unit, LinearMap.smul_apply]
    have hs (σ : Equiv.Perm (Fin p)) :
        Equiv.Perm.sign σ • tensorEvaluation K V p
          (PiTensorProduct.tprod K (fun i => f (σ i)))
          (exteriorPower.toTensorPower K V p y) =
        pairing K V p (exteriorPower.ιMulti K p f) y := by
      change Equiv.Perm.sign σ • tensorEvaluation K V p
        (PiTensorProduct.tprod K (f ∘ σ))
        (exteriorPower.toTensorPower K V p y) = _
      rw [tensor_pairing_toTensor, (exteriorPower.ιMulti K p).map_perm]
      simp [smul_smul]
    trans ∑ _σ : Equiv.Perm (Fin p),
      pairing K V p (exteriorPower.ιMulti K p f) y
    · apply Finset.sum_congr rfl
      intro σ _
      exact hs σ
    · simp [Fintype.card_perm, nsmul_eq_mul]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) x

theorem average_pairing : Specs.D05.M15.ExteriorPairing.average_pairing := by
  intro K V _ _ _ p hp f x
  simp only [average_value, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [D05.M15.Exterior.projection_elementary, D05.M15.Exterior.projection_elementary]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [tensor_pairing_antisym, elementary]
  field_simp

theorem normalized_tensor_comparison :
    Specs.D05.M15.ExteriorPairing.normalized_tensor_comparison := by
  intro K V _ _ _ p hp a x
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [tensor_pairing_antisym]
  field_simp

end D05.M15.ExteriorPairing
