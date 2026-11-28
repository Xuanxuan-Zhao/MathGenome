import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.LocallyNilpotentExponential
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Nilpotent.Exp

open scoped BigOperators TensorProduct

namespace LieNotes.Contragredient.LocallyNilpotentExponential

universe u v w

section Linear

variable {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- The exponential can be evaluated with any cutoff that annihilates the input. -/
theorem exp_apply (D : Module.End ℂ V) (hD : LocallyNilpotent D)
    {x : V} {n : ℕ} (hn : (D ^ n) x = 0) :
    exp D hD x = ∑ j ∈ Finset.range n, (j.factorial : ℂ)⁻¹ • (D ^ j) x :=
  exp_apply_of_pow_eq_zero D hD hn

private theorem exp_comp {U : Type u} [AddCommGroup U] [Module ℂ U]
    {D : Module.End ℂ U} {E : Module.End ℂ V}
    (hD : LocallyNilpotent D) (hE : LocallyNilpotent E) (f : U →ₗ[ℂ] V)
    (hf : E ∘ₗ f = f ∘ₗ D) :
    exp E hE ∘ₗ f = f ∘ₗ exp D hD := by
  ext x
  have hp (j : ℕ) : (E ^ j) (f x) = f ((D ^ j) x) :=
    LinearMap.congr_fun (Module.End.commute_pow_left_of_commute hf j) x
  obtain ⟨n, hn⟩ := hD x
  have hm : (E ^ n) (f x) = 0 := by rw [hp, hn, map_zero]
  simp only [LinearMap.comp_apply, exp_apply E hE hm, exp_apply D hD hn, map_sum, map_smul, hp]

private theorem mapsTo_powerKernel (D : Module.End ℂ V) (n : ℕ)
    (x : V) (hx : x ∈ LinearMap.ker (D ^ n)) : D x ∈ LinearMap.ker (D ^ n) := by
  change (D ^ n) (D x) = 0
  change (D ^ n) x = 0 at hx
  rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hx, map_zero]

private def restrictToPowerKernel (D : Module.End ℂ V) (n : ℕ) :
    Module.End ℂ (LinearMap.ker (D ^ n)) :=
  D.restrict (mapsTo_powerKernel D n)

private theorem nilpotent_restrictToPowerKernel (D : Module.End ℂ V) (n : ℕ) :
    IsNilpotent (restrictToPowerKernel D n) := by
  refine ⟨n, LinearMap.ext fun x ↦ Subtype.ext ?_⟩
  change ((restrictToPowerKernel D n ^ n) x : V) = 0
  rw [restrictToPowerKernel, Module.End.pow_restrict]
  exact x.property

end Linear

section NilpotentRestrictions

variable {U : Type u} {V : Type v} {W : Type w}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private theorem local_of_nilpotent {D : Module.End ℂ U} (hD : IsNilpotent D) :
    LocallyNilpotent D := by
  obtain ⟨n, hn⟩ := hD
  exact fun x ↦ ⟨n, LinearMap.congr_fun hn x⟩

private theorem exp_eq_nilpotent_exp [Module ℚ U] [IsScalarTower ℚ ℂ U]
    (D : Module.End ℂ U) (hD : LocallyNilpotent D)
    (h : IsNilpotent D) : exp D hD = IsNilpotent.exp D := by
  obtain ⟨n, hn⟩ := h
  rw [IsNilpotent.exp_eq_sum hn]
  ext x
  rw [exp_apply D hD (LinearMap.congr_fun hn x), LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, ← Rat.cast_smul_eq_qsmul ℂ, Rat.cast_inv, Rat.cast_natCast]

private theorem exp_comp_nilpotent [Module ℚ U] [IsScalarTower ℚ ℂ U]
    {D : Module.End ℂ U} {E : Module.End ℂ V}
    (hD : IsNilpotent D) (hE : LocallyNilpotent E) (f : U →ₗ[ℂ] V)
    (hf : E ∘ₗ f = f ∘ₗ D) :
    exp E hE ∘ₗ f = f ∘ₗ IsNilpotent.exp D := by
  rw [← exp_eq_nilpotent_exp D (local_of_nilpotent hD) hD]
  exact exp_comp (local_of_nilpotent hD) hE f hf

private theorem map_nilpotentExp [Module ℚ U] [IsScalarTower ℚ ℂ U]
    [Module ℚ V] [IsScalarTower ℚ ℂ V]
    (f : Module.End ℂ U →ₐ[ℂ] Module.End ℂ V)
    {D : Module.End ℂ U} (hD : IsNilpotent D) :
    f (IsNilpotent.exp D) = IsNilpotent.exp (f D) := by
  obtain ⟨n, hn⟩ := hD
  have hf : (f D) ^ n = 0 := by rw [← map_pow, hn, map_zero]
  simp only [IsNilpotent.exp_eq_sum hn, IsNilpotent.exp_eq_sum hf, map_sum,
    ← Rat.cast_smul_eq_qsmul ℂ, map_smul, map_pow]

private theorem exp_neg_mul_exp (D : Module.End ℂ V) (hD : LocallyNilpotent D)
    (hneg : LocallyNilpotent (-D)) : exp (-D) hneg * exp D hD = 1 := by
  ext x
  obtain ⟨n, hn⟩ := hD x
  let S := LinearMap.ker (D ^ n)
  let := Module.restrictScalars ℚ ℂ S
  have := IsScalarTower.restrictScalars ℚ ℂ S
  let F : Module.End ℂ S := restrictToPowerKernel D n
  let z : S := ⟨x, hn⟩
  have hF : IsNilpotent F := nilpotent_restrictToPowerKernel D n
  have hpos := exp_comp_nilpotent hF hD S.subtype (by ext; rfl)
  have hminus := exp_comp_nilpotent hF.neg hneg S.subtype (by ext; rfl)
  have hp : exp D hD x = S.subtype (IsNilpotent.exp F z) :=
    LinearMap.congr_fun hpos z
  have hm : exp (-D) hneg (S.subtype (IsNilpotent.exp F z)) =
      S.subtype ((IsNilpotent.exp (-F) * IsNilpotent.exp F) z) :=
    LinearMap.congr_fun hminus (IsNilpotent.exp F z)
  rw [Module.End.mul_apply, hp, hm, hF.exp_neg_mul_exp_self]
  rfl

/-- The two finite exponentials for opposite operators are inverse endomorphisms. -/
theorem exp_inverse (D : Module.End ℂ V) (hD : LocallyNilpotent D) :
    exp (-D) hD.neg * exp D hD = 1 ∧ exp D hD * exp (-D) hD.neg = 1 := by
  refine ⟨exp_neg_mul_exp D hD hD.neg, ?_⟩
  simpa only [neg_neg] using exp_neg_mul_exp (-D) hD.neg (by simpa only [neg_neg] using hD)

/-- Exponentiating the Leibniz rule for a bilinear map. For each pair of inputs,
the tensor product of two power kernels supplies a nilpotent source operator. -/
private theorem exp_bilinear (b : U →ₗ[ℂ] V →ₗ[ℂ] W)
    (D : Module.End ℂ U) (E : Module.End ℂ V) (F : Module.End ℂ W)
    (hD : LocallyNilpotent D) (hE : LocallyNilpotent E) (hF : LocallyNilpotent F)
    (h : ∀ x y, F (b x y) = b (D x) y + b x (E y)) (x : U) (y : V) :
    exp F hF (b x y) = b (exp D hD x) (exp E hE y) := by
  obtain ⟨m, hm⟩ := hD x
  obtain ⟨n, hn⟩ := hE y
  let S := LinearMap.ker (D ^ m)
  let T := LinearMap.ker (E ^ n)
  let := Module.restrictScalars ℚ ℂ S
  have := IsScalarTower.restrictScalars ℚ ℂ S
  let := Module.restrictScalars ℚ ℂ T
  have := IsScalarTower.restrictScalars ℚ ℂ T
  let := Module.restrictScalars ℚ ℂ (S ⊗[ℂ] T)
  have := IsScalarTower.restrictScalars ℚ ℂ (S ⊗[ℂ] T)
  let s : S := ⟨x, hm⟩
  let t : T := ⟨y, hn⟩
  let DS : Module.End ℂ S := restrictToPowerKernel D m
  let ET : Module.End ℂ T := restrictToPowerKernel E n
  have hDS : IsNilpotent DS := nilpotent_restrictToPowerKernel D m
  have hET : IsNilpotent ET := nilpotent_restrictToPowerKernel E n
  let A : Module.End ℂ (S ⊗[ℂ] T) := DS.rTensor T
  let B : Module.End ℂ (S ⊗[ℂ] T) := ET.lTensor S
  have hA : IsNilpotent A := hDS.map (Module.End.rTensorAlgHom ℂ S T)
  have hB : IsNilpotent B := hET.map (Module.End.lTensorAlgHom ℂ T S)
  have hAB : Commute A B := by ext; simp [A, B]
  let g : S ⊗[ℂ] T →ₗ[ℂ] W := TensorProduct.lift (b.compl₁₂ S.subtype T.subtype)
  have hg : F ∘ₗ g = g ∘ₗ (A + B) := by
    ext s' t'
    simp [g, A, B, DS, ET, restrictToPowerKernel, h]
  have htensor := LinearMap.congr_fun
    (exp_comp_nilpotent (hAB.isNilpotent_add hA hB) hF g hg) (s ⊗ₜ[ℂ] t)
  have hAexp : IsNilpotent.exp A = (IsNilpotent.exp DS).rTensor T :=
    (map_nilpotentExp (Module.End.rTensorAlgHom ℂ S T) hDS).symm
  have hBexp : IsNilpotent.exp B = (IsNilpotent.exp ET).lTensor S :=
    (map_nilpotentExp (Module.End.lTensorAlgHom ℂ T S) hET).symm
  rw [IsNilpotent.exp_add_of_commute hAB hA hB, hAexp, hBexp] at htensor
  have hs : exp D hD x = S.subtype (IsNilpotent.exp DS s) :=
    LinearMap.congr_fun (exp_comp_nilpotent hDS hD S.subtype (by ext; rfl)) s
  have ht : exp E hE y = T.subtype (IsNilpotent.exp ET t) :=
    LinearMap.congr_fun (exp_comp_nilpotent hET hE T.subtype (by ext; rfl)) t
  rw [hs, ht]
  simpa only [LinearMap.comp_apply, Module.End.mul_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, g, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, Submodule.subtype_apply, s, t]
    using htensor

end NilpotentRestrictions

/-- The finite exponential as a complex linear automorphism. -/
noncomputable def expEquiv {V : Type v} [AddCommGroup V] [Module ℂ V]
    (D : Module.End ℂ V) (hD : LocallyNilpotent D) : V ≃ₗ[ℂ] V where
  toLinearMap := exp D hD
  invFun := exp (-D) hD.neg
  left_inv x := LinearMap.congr_fun (exp_inverse D hD).1 x
  right_inv x := LinearMap.congr_fun (exp_inverse D hD).2 x

@[simp] theorem expEquiv_apply {V : Type v} [AddCommGroup V] [Module ℂ V]
    (D : Module.End ℂ V) (hD : LocallyNilpotent D) (x : V) :
    expEquiv D hD x = exp D hD x := rfl

@[simp] theorem expEquiv_symm_apply {V : Type v} [AddCommGroup V] [Module ℂ V]
    (D : Module.End ℂ V) (hD : LocallyNilpotent D) (x : V) :
    (expEquiv D hD).symm x = exp (-D) hD.neg x := rfl

section Lie

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- The exponential of a locally nilpotent Lie derivation preserves brackets. -/
theorem exp_map_lie (D : LieDerivation ℂ L L) (hD : LocallyNilpotent D.toLinearMap) (x y : L) :
    exp D.toLinearMap hD ⁅x, y⁆ = ⁅exp D.toLinearMap hD x, exp D.toLinearMap hD y⁆ :=
  exp_bilinear (LieAlgebra.ad ℂ L).toLinearMap D.toLinearMap D.toLinearMap D.toLinearMap
    hD hD hD (fun a b ↦ by
      change D ⁅a, b⁆ = ⁅D a, b⁆ + ⁅a, D b⁆
      rw [D.apply_lie_eq_add, add_comm]) x y

/-- The finite exponential of a locally nilpotent Lie derivation as a Lie automorphism. -/
noncomputable def lieExp (D : LieDerivation ℂ L L) (hD : LocallyNilpotent D.toLinearMap) :
    L ≃ₗ⁅ℂ⁆ L :=
  { expEquiv D.toLinearMap hD with
    map_lie' := fun {x y} ↦ exp_map_lie D hD x y }

/-- The exponential of a locally nilpotent adjoint action as a Lie automorphism. -/
noncomputable def adjointExp (x : L) (hx : LocallyNilpotent (LieAlgebra.ad ℂ L x)) :
    L ≃ₗ⁅ℂ⁆ L :=
  lieExp (LieDerivation.ad ℂ L x) (by simpa only [LieDerivation.coe_ad_apply_eq_ad_apply] using hx)

@[simp] theorem adjointExp_apply (x : L) (hx : LocallyNilpotent (LieAlgebra.ad ℂ L x)) (y : L) :
    adjointExp x hx y = exp (LieAlgebra.ad ℂ L x) hx y := by
  change exp (LieDerivation.ad ℂ L x).toLinearMap _ y = _
  simp only [LieDerivation.coe_ad_apply_eq_ad_apply]

/-- Exponentiating an adjoint action agrees with conjugating its action on the module. -/
theorem exp_conjugation {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (x : L)
    (had : LocallyNilpotent (LieAlgebra.ad ℂ L x)) (hρ : LocallyNilpotent (ρ x))
    (y : L) :
    exp (ρ x) hρ * ρ y * exp (-(ρ x)) hρ.neg = ρ (exp (LieAlgebra.ad ℂ L x) had y) := by
  have hl (a : L) (v : V) : (ρ x) ((ρ a) v) = (ρ ⁅x, a⁆) v + (ρ a) ((ρ x) v) := by
    have hcomm : ρ ⁅x, a⁆ = ρ x * ρ a - ρ a * ρ x := ρ.map_lie x a
    rw [hcomm]
    simp [Module.End.mul_apply]
  have hintertwines : exp (ρ x) hρ * ρ y = ρ (exp (LieAlgebra.ad ℂ L x) had y) * exp (ρ x) hρ :=
    LinearMap.ext (exp_bilinear ρ.toLinearMap (LieAlgebra.ad ℂ L x) (ρ x) (ρ x)
      had hρ hρ hl y)
  rw [hintertwines, mul_assoc, (exp_inverse (ρ x) hρ).2, mul_one]

end Lie
end LieNotes.Contragredient.LocallyNilpotentExponential
