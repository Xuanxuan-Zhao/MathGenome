import MathGenome.Internal.Specs.D05.M15.Contraction

/-! Mixed-tensor contraction: construction by evaluation, its coordinate sum,
and the trace and equivariance bridges, K05.15.contraction. -/
namespace D05.M15.Contraction

open scoped TensorProduct BigOperators
set_option backward.isDefEq.respectTransparency false

open Specs.D05.M15.Contraction

abbrev contract {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {p q : ℕ} (r : Fin (p+1)) (s : Fin (q+1)) :=
  Specs.D05.M15.Contraction.contract (K := K) (V := V) r s

/-- Extensionality in the grouped model follows from the two finite-arity
universal properties and the binary tensor universal property. -/
theorem mixed_ext {K V H : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommMonoid H] [Module K H] {p q : ℕ}
    {L M : Mixed K V p q →ₗ[K] H}
    (h : ∀ f v, L (elementary f v) = M (elementary f v)) : L = M := by
  apply TensorProduct.ext
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro f
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  exact h f v

@[simp] theorem splitSlot_tprod {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {n : ℕ} (r : Fin (n+1)) (x : Fin (n+1) → M) :
    splitSlot r (PiTensorProduct.tprod K x) =
      x r ⊗ₜ[K] PiTensorProduct.tprod K (r.removeNth x) := by
  simp [splitSlot, LinearMap.uncurryMid]

theorem contraction_tprod : Specs.D05.M15.Contraction.contraction_tprod := by
  intro K V _ _ _ p q r s f v
  simp [Specs.D05.M15.Contraction.contract, elementary]

theorem contraction_universal : Specs.D05.M15.Contraction.contraction_universal := by
  intro K V _ _ _ p q r s
  refine ⟨contract r s, contraction_tprod r s, ?_⟩
  intro L hL
  apply mixed_ext (K := K) (V := V) (p := p+1) (q := q+1)
  intro f v
  rw [hL, contraction_tprod]

theorem nullary_unit : Specs.D05.M15.Contraction.nullary_unit := by
  intro K V _ _ _ f v
  simp [zeroEquiv, elementary]

theorem mixedBasis_apply {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] (b : Module.Basis I K V) {p q : ℕ}
    (i : Fin p → I) (j : Fin q → I) :
    mixedBasis b p q (i,j) = elementary (fun r => b.coord (i r)) (fun s => b (j s)) := by
  classical
  simp [mixedBasis, elementary, Basis.piTensorProduct_apply]

theorem basis_contraction : Specs.D05.M15.Contraction.basis_contraction := by
  intro K V I _ _ _ _ b p q r s i j
  classical
  rw [mixedBasis_apply, contraction_tprod, mixedBasis_apply]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [eq_comm]
  rfl

/-- Coordinate contraction is the diagonal sum, in the actual dual product bases. -/
theorem coordinate_contraction : Specs.D05.M15.Contraction.coordinate_contraction := by
  intro K V I _ _ _ _ b p q r s t i j
  classical
  let B := mixedBasis b (p+1) (q+1)
  let D := mixedBasis b p q
  have h : (D.coord (i,j)).comp (contract r s) =
      ∑ k : I, B.coord (r.insertNth k i, s.insertNth k j) := by
    apply B.ext
    rintro ⟨a,c⟩
    change D.coord (i,j) (contract r s (mixedBasis b (p+1) (q+1) (a,c))) = _
    rw [basis_contraction]
    simp only [D, B, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      LinearMap.sum_apply, Finsupp.single_apply, smul_eq_mul]
    simp only [Prod.mk.injEq, Fin.eq_insertNth_iff]
    by_cases he : a r = c s
    · by_cases ha : r.removeNth a = i <;> by_cases hc : s.removeNth c = j <;>
        simp [ha, hc, he, eq_comm]
    · simp only [ite_eq_right he, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro k _
      split_ifs with hk
      · exact False.elim (he (hk.1.1.trans hk.2.1.symm))
      · rfl
  simpa only [D, B, LinearMap.comp_apply, Module.Basis.coord_apply, LinearMap.sum_apply]
    using LinearMap.congr_fun h t

theorem rank_one_trace : Specs.D05.M15.Contraction.rank_one_trace := by
  intro K V I _ _ _ _ b f v
  have hs : (∑ i, f (b i) * b.coord i v) = f v := by
    simpa only [map_sum, map_smul, Module.Basis.coord_apply, smul_eq_mul, mul_comm]
      using congrArg f (b.sum_repr v)
  refine ⟨?_, hs⟩
  rw [hs]
  exact LinearMap.congr_fun (LinearMap.trace_eq_contract_of_basis b) (f ⊗ₜ[K] v)

theorem contraction_trace : Specs.D05.M15.Contraction.contraction_trace := by
  intro K V _ _ _ _ t
  have h : (zeroEquiv (K := K) (V := V)).toLinearMap.comp
      (contract (0 : Fin 1) (0 : Fin 1)) =
      (LinearMap.trace K V).comp ((Specs.D05.M15.TensorDualHom.phi K V V).comp
        (oneEquiv (K := K) (V := V)).toLinearMap) := by
    apply mixed_ext (K := K) (V := V) (p := 1) (q := 1)
    intro f v
    simp only [LinearMap.comp_apply]
    rw [contraction_tprod, map_smul]
    change f 0 (v 0) • zeroEquiv (elementary (Fin.removeNth 0 f) (Fin.removeNth 0 v)) = _
    rw [nullary_unit]
    simp only [smul_eq_mul, mul_one]
    simp [oneEquiv, elementary, Specs.D05.M15.TensorDualHom.phi,
      LinearMap.trace_eq_contract_apply]
  exact LinearMap.congr_fun h t

theorem action_tprod : Specs.D05.M15.Contraction.action_tprod := by
  intro K V _ _ _ g p q f v
  simp only [mixedAction, elementary, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
  rfl

theorem action_identity : Specs.D05.M15.Contraction.action_identity := by
  intro K V _ _ _ p q
  apply mixed_ext (K := K) (V := V) (p := p) (q := q)
  intro f v
  simp only [LinearMap.id_apply]
  rw [action_tprod]
  rfl

theorem action_composition : Specs.D05.M15.Contraction.action_composition := by
  intro K V _ _ _ g h p q
  apply mixed_ext (K := K) (V := V) (p := p) (q := q)
  intro f v
  simp only [LinearMap.comp_apply]
  rw [action_tprod, action_tprod, action_tprod]
  rfl

theorem action_inverse : Specs.D05.M15.Contraction.action_inverse := by
  intro K V _ _ _ g p q
  constructor
  · rw [← action_composition, LinearEquiv.self_trans_symm, action_identity]
  · rw [← action_composition, LinearEquiv.symm_trans_self, action_identity]

theorem contraction_equivariant : Specs.D05.M15.Contraction.contraction_equivariant := by
  intro K V _ _ _ g p q r s
  apply mixed_ext (K := K) (V := V) (p := p+1) (q := q+1)
  intro f v
  simp only [LinearMap.comp_apply]
  rw [action_tprod, contraction_tprod, contraction_tprod, map_smul, action_tprod]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

end D05.M15.Contraction
