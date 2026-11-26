import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.BaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.TensorAndDual
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.RingTheory.Flat.IsBaseChange
import Batteries.Tactic.OpenPrivate

open scoped TensorProduct
open TensorProduct.AlgebraTensorModule

universe u

noncomputable section

set_option maxSynthPendingDepth 4

namespace LinearAlgebraicGroups.RationalRepresentations

open private isCoactionMatrix_extension from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

variable {k K V W : Type u} [Field k] [Field K] [Algebra k K]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  (A : HopfAlgebraCategory k)

@[simp]
theorem mem_equivariantHom (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (f : V →ₗ[k] W) : f ∈ equivariantHom A ρ σ ↔ IsEquivariant A ρ σ f := by
  rw [equivariantHom, LinearMap.mem_ker, IsEquivariant]
  change σ.coaction.comp f - (f.rTensor A).comp ρ.coaction = 0 ↔ _
  rw [sub_eq_zero, eq_comm]

/-- Extend the coefficients in any basis. The coaction formula below
characterizes the result independently of the basis. -/
def extendCoaction [FiniteDimensional k V] (ρ : RightComodule k A V) :
    RightComodule K (scalarExtension A K) (K ⊗[k] V) := by
  classical
  exact scalarExtensionCoaction A (Module.Basis.ofVectorSpace k V) K ρ

private theorem scalarExtensionCoaction_isScalarExtension {ι : Type u} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι k V) (ρ : RightComodule k A V) :
    IsScalarExtension A ρ (scalarExtensionCoaction A b K ρ) := by
  let B := scalarExtension A K
  let M : Matrix ι ι B := fun i j ↦ (1 : K) ⊗ₜ[k] coefficients A b ρ i j
  let σ := scalarExtensionCoaction A b K ρ
  have hσ : coefficients B (b.baseChange K) σ = M :=
    coefficients_coactionOfMatrix B (b.baseChange K) M
      (isCoactionMatrix_extension A K (coefficients_isCoactionMatrix A b ρ))
  unfold IsScalarExtension
  change σ.coaction = _
  apply (b.baseChange K).ext
  intro j
  rw [coaction_apply_basis B (b.baseChange K) σ, hσ]
  simp only [M, Module.Basis.baseChange_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.baseChange_tmul, coaction_apply_basis A b ρ j, TensorProduct.tmul_sum, map_sum,
    distribBaseChange_tmul]

theorem extendCoaction_isScalarExtension [FiniteDimensional k V]
    (ρ : RightComodule k A V) : IsScalarExtension A ρ (extendCoaction (K := K) A ρ) := by
  classical
  exact scalarExtensionCoaction_isScalarExtension A (Module.Basis.ofVectorSpace k V) ρ

theorem scalarExtensionOfRepresentation : Specs.RationalBaseChange.ScalarExtension.{u} := by
  intro k K V _ _ _ _ _ _ A ρ
  exact ⟨extendCoaction A ρ, extendCoaction_isScalarExtension A ρ⟩

private theorem invariants_baseChange_eq (ρ : RightComodule k A V)
    (ρK : RightComodule K (scalarExtension A K) (K ⊗[k] V))
    (hρ : IsScalarExtension A ρ ρK) :
    invariants (scalarExtension A K) ρK = (invariants A ρ).baseChange K := by
  let d := distribBaseChange k K V A
  have htrivial : trivialLinearMap (V := K ⊗[k] V) (scalarExtension A K) =
      d.toLinearMap.comp ((trivialLinearMap (V := V) A).baseChange K) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a v
    simp [trivialLinearMap, d]
    rfl
  have he : invariantDifference (scalarExtension A K) ρK =
      d.toLinearMap.comp ((invariantDifference A ρ).baseChange K) := by
    unfold invariantDifference
    rw [hρ, htrivial, LinearMap.baseChange_sub]
    exact (LinearMap.comp_sub ((trivialLinearMap A).baseChange K) (ρ.coaction.baseChange K)
      d.toLinearMap).symm
  unfold invariants
  rw [he, LinearMap.ker_comp_of_ker_eq_bot _ (LinearEquiv.ker d)]
  exact Module.Flat.ker_lTensor_eq K K _

theorem invariantBaseChange : Specs.RationalBaseChange.InvariantBaseChange.{u} := by
  intro k K V _ _ _ _ _ _ A ρ ρK hρ
  let e := Submodule.toBaseChange.toLinearEquiv K (invariants A ρ)
  refine ⟨e.trans (LinearEquiv.ofEq _ _ (invariants_baseChange_eq A ρ ρK hρ).symm), ?_⟩
  intro a v
  rfl

private theorem distribBaseChange_rTensor (f : V →ₗ[k] W) :
    ((f.baseChange K).rTensor (scalarExtension A K)).comp
        (distribBaseChange k K V A).toLinearMap =
      (distribBaseChange k K W A).toLinearMap.comp ((f.rTensor A).baseChange K) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a t
  induction t using TensorProduct.inductionOn with
  | tmul v b => simp
  | add t s ht hs => simp only [TensorProduct.tmul_add, map_add, ht, hs]

private theorem equivarianceDifference_apply
    (ρ : RightComodule k A V) (σ : RightComodule k A W) (f : V →ₗ[k] W) :
    equivarianceDifference A ρ σ f =
      σ.coaction.comp f - (f.rTensor A).comp ρ.coaction := rfl

private theorem equivarianceDifference_baseChange
    (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (ρK : RightComodule K (scalarExtension A K) (K ⊗[k] V))
    (σK : RightComodule K (scalarExtension A K) (K ⊗[k] W))
    (hρ : IsScalarExtension A ρ ρK) (hσ : IsScalarExtension A σ σK) (f : V →ₗ[k] W) :
    equivarianceDifference (scalarExtension A K) ρK σK (f.baseChange K) =
      (distribBaseChange k K W A).toLinearMap.comp ((equivarianceDifference A ρ σ f).baseChange K) := by
  unfold IsScalarExtension at hρ hσ
  rw [equivarianceDifference_apply (scalarExtension A K) ρK σK (f.baseChange K)]
  simp only [equivarianceDifference_apply, hρ, hσ, LinearMap.baseChange_sub,
    LinearMap.baseChange_comp, LinearMap.comp_sub]
  rw [← LinearMap.comp_assoc, distribBaseChange_rTensor, LinearMap.comp_assoc]
  rfl

/-- The usual base change of linear maps restricts to equivariant maps. -/
theorem isEquivariant_baseChange
    {ρ : RightComodule k A V} {σ : RightComodule k A W}
    {ρK : RightComodule K (scalarExtension A K) (K ⊗[k] V)}
    {σK : RightComodule K (scalarExtension A K) (K ⊗[k] W)}
    (hρ : IsScalarExtension A ρ ρK) (hσ : IsScalarExtension A σ σK)
    {f : V →ₗ[k] W} (hf : IsEquivariant A ρ σ f) :
    IsEquivariant (scalarExtension A K) ρK σK (f.baseChange K) := by
  have hf' := LinearMap.mem_ker.mp ((mem_equivariantHom A ρ σ f).mpr hf)
  apply (mem_equivariantHom _ ρK σK _).mp
  rw [equivariantHom, LinearMap.mem_ker, equivarianceDifference_baseChange A ρ σ ρK σK hρ hσ,
    hf', LinearMap.baseChange_zero, LinearMap.comp_zero]

private theorem baseChangeHom_isBaseChange [FiniteDimensional k V] :
    IsBaseChange K (LinearMap.baseChangeHom k K V W) := by
  let hv := TensorProduct.isBaseChange k V K
  let hw := TensorProduct.isBaseChange k W K
  have h : IsBaseChange.linearMapLeftRightHom hv (TensorProduct.mk k K W 1) =
      LinearMap.baseChangeHom k K V W := by
    apply LinearMap.ext
    intro f
    apply hv.algHom_ext
    intro v
    rw [IsBaseChange.linearMapLeftRightHom_comp_apply]
    rfl
  rw [← h]
  exact IsBaseChange.linearMapLeftRight hv hw

set_option maxHeartbeats 800000 in
theorem equivariantHomBaseChange : Specs.RationalBaseChange.EquivariantHomBaseChange.{u} := by
  intro k K V W _ _ _ _ _ _ _ _ _ A ρ σ ρK σK hρ hσ
  let B := scalarExtension A K
  let g := equivarianceDifference A ρ σ
  let gK := equivarianceDifference B ρK σK
  let d := distribBaseChange k K W A
  let h₂ := LinearMap.baseChangeHom k K V W
  let h₁ : (LinearMap.ker g) →ₗ[k] (LinearMap.ker gK) :=
    { toFun := fun f ↦ ⟨h₂ f, by
        have hf : g (f : V →ₗ[k] W) = 0 := LinearMap.mem_ker.mp f.property
        rw [LinearMap.mem_ker]
        change equivarianceDifference B ρK σK ((f : V →ₗ[k] W).baseChange K) = 0
        rw [equivarianceDifference_baseChange A ρ σ ρK σK hρ hσ]
        change d.toLinearMap.comp ((g (f : V →ₗ[k] W)).baseChange K) = 0
        rw [hf, LinearMap.baseChange_zero, LinearMap.comp_zero]⟩
      map_add' := fun f g ↦ Subtype.ext (h₂.map_add (f : V →ₗ[k] W) (g : V →ₗ[k] W))
      map_smul' := fun a f ↦ Subtype.ext (h₂.map_smul a (f : V →ₗ[k] W)) }
  let β := (d.toLinearMap.restrictScalars k).comp (TensorProduct.mk k K (W ⊗[k] A) 1)
  let hv := TensorProduct.isBaseChange k V K
  let h₃ := IsBaseChange.linearMapLeftRightHom hv β
  have hβ : IsBaseChange K β := IsBaseChange.of_equiv d (fun _ ↦ rfl)
  have comm : h₃.comp g = (gK.restrictScalars k).comp h₂ := by
    apply LinearMap.ext
    intro f
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    apply hv.algHom_ext
    intro v
    have hf := DFunLike.congr_fun (equivarianceDifference_baseChange A ρ σ ρK σK hρ hσ f)
      ((1 : K) ⊗ₜ[k] v)
    rw [IsBaseChange.linearMapLeftRightHom_comp_apply]
    exact hf.symm
  have he : IsBaseChange K h₁ :=
    IsBaseChange.of_left_exact K h₁ h₂ h₃ rfl comm baseChangeHom_isBaseChange
      (IsBaseChange.linearMapLeftRight hv hβ) (LinearMap.exact_subtype_ker_map g)
      (LinearMap.ker g).injective_subtype (LinearMap.exact_subtype_ker_map gK)
      (LinearMap.ker gK).injective_subtype
  refine ⟨he.equiv, ?_⟩
  intro a f
  exact congrArg (fun x : LinearMap.ker gK ↦
    (x : (K ⊗[k] V) →ₗ[K] (K ⊗[k] W))) (he.equiv_tmul a (show LinearMap.ker g from f))

private theorem exists_preimage_of_baseChange
    {X Y : Type u} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (p : X →ₗ[k] Y) (x : K ⊗[k] X) (y : Y)
    (h : p.baseChange K x = (1 : K) ⊗ₜ[k] y) : ∃ v, p v = y := by
  obtain ⟨q, hq⟩ := (Algebra.linearMap k K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (FaithfulSMul.algebraMap_injective k K))
  have hq1 : q 1 = 1 := by simpa using DFunLike.congr_fun hq (1 : k)
  let sx := (TensorProduct.lid k X).toLinearMap.comp (q.rTensor X)
  let sy := (TensorProduct.lid k Y).toLinearMap.comp (q.rTensor Y)
  have comm : p.comp sx = sy.comp ((p.baseChange K).restrictScalars k) := by
    apply TensorProduct.ext'
    intro a v
    simp [sx, sy]
  refine ⟨sx x, ?_⟩
  have e := DFunLike.congr_fun comm x
  change p (sx x) = sy (p.baseChange K x) at e
  rw [e, h]
  simp [sy, hq1]

set_option maxHeartbeats 800000 in
theorem retractionDescent : Specs.RationalBaseChange.RetractionDescent.{u} := by
  intro k K V _ _ _ _ _ _ A ρ U τ ρK τK _ hρ hτ hr
  obtain ⟨rK, hrK, hrKi⟩ := hr
  let B := scalarExtension A K
  let i := U.subtype
  let r : equivariantHom B ρK τK := ⟨rK, (mem_equivariantHom B ρK τK rK).mpr hrK⟩
  obtain ⟨e, he⟩ := equivariantHomBaseChange A ρ τ ρK τK hρ hτ
  let p : equivariantHom A ρ τ →ₗ[k] (U →ₗ[k] U) :=
    ((LinearMap.llcomp k U V U).flip i).comp (equivariantHom A ρ τ).subtype
  let E := (baseChangeHom_isBaseChange (k := k) (K := K) (V := U) (W := U)).equiv
  have hleft (z : K ⊗[k] equivariantHom A ρ τ) : E ((p.baseChange K) z) =
      (e z : (K ⊗[k] V) →ₗ[K] (K ⊗[k] U)).comp (i.baseChange K) := by
    induction z using TensorProduct.inductionOn with
    | tmul a f =>
      rw [LinearMap.baseChange_tmul, IsBaseChange.equiv_tmul, he, LinearMap.smul_comp]
      change a • (((f : V →ₗ[k] U).comp i).baseChange K) =
        a • ((f : V →ₗ[k] U).baseChange K).comp (i.baseChange K)
      rw [LinearMap.baseChange_comp]
    | add x y hx hy =>
      change E ((p.baseChange K) (x + y)) =
        ((equivariantHom B ρK τK).subtype (e (x + y))).comp (i.baseChange K)
      simp only [map_add, LinearMap.add_comp, hx, hy]
      rfl
  obtain ⟨z, hz⟩ := e.surjective r
  have hzid : (p.baseChange K) z = (1 : K) ⊗ₜ[k] (LinearMap.id : U →ₗ[k] U) := by
    apply E.injective
    rw [hleft, hz, IsBaseChange.equiv_tmul, one_smul]
    change rK.comp (i.baseChange K) = (LinearMap.id : U →ₗ[k] U).baseChange K
    rw [LinearMap.baseChange_id]
    exact hrKi
  obtain ⟨r₀, hr₀⟩ := exists_preimage_of_baseChange p z LinearMap.id hzid
  exact ⟨r₀, (mem_equivariantHom A ρ τ r₀).mp r₀.property, hr₀⟩

private theorem split_injective_of_isSemisimple
    (ρ : RightComodule k A V) (σ : RightComodule k A W) (i : W →ₗ[k] V)
    (hi : IsEquivariant A σ ρ i) (hinj : Function.Injective i)
    (hs : IsSemisimple A ρ) :
    ∃ r : V →ₗ[k] W, IsEquivariant A ρ σ r ∧ r.comp i = LinearMap.id := by
  let P := LinearMap.range i
  let e : W ≃ₗ[k] P := LinearEquiv.ofInjective i hinj
  have factor : P.subtype.comp e.toLinearMap = i := rfl
  have hP : ρ.IsSubcomodule P := by
    intro x
    obtain ⟨w, hw⟩ := e.surjective x
    refine ⟨(e.toLinearMap.rTensor A) (σ.coaction w), ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, factor]
    rw [← LinearMap.comp_apply, hi]
    exact congrArg ρ.coaction (congrArg Subtype.val hw)
  obtain ⟨τ, hτ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction ρ P).mp hP
  have he : IsEquivariant A τ σ e.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply Module.Flat.rTensor_preserves_injective_linearMap i hinj
    have hτx := DFunLike.congr_fun hτ x
    have hix := DFunLike.congr_fun hi (e.symm x)
    simp only [LinearMap.comp_apply] at hτx hix ⊢
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    have hfactor : i.comp e.symm.toLinearMap = P.subtype := by
      rw [← factor, LinearMap.comp_assoc]
      simp
    rw [hfactor, hτx]
    change _ = (i.rTensor A) (σ.coaction (e.symm x))
    rw [hix]
    exact (congrArg ρ.coaction (DFunLike.congr_fun hfactor x)).symm
  obtain ⟨r, hr, hri⟩ := hs P τ hτ
  refine ⟨e.symm.toLinearMap.comp r, ?_, ?_⟩
  · unfold IsEquivariant at he hr ⊢
    rw [LinearMap.rTensor_comp, LinearMap.comp_assoc, hr, ← LinearMap.comp_assoc, he,
      LinearMap.comp_assoc]
  · rw [← factor]
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc e.toLinearMap P.subtype r, hri,
      LinearMap.id_comp, LinearEquiv.symm_comp]

theorem semisimplicityDescent : Specs.RationalBaseChange.SemisimplicityDescent.{u} := by
  intro k K V _ _ _ _ _ _ A ρ ρK hρ hs U τ hi
  let τK := extendCoaction (K := K) A τ
  have hτ : IsScalarExtension A τ τK := extendCoaction_isScalarExtension A τ
  apply retractionDescent A ρ U τ ρK τK hi hρ hτ
  apply split_injective_of_isSemisimple (scalarExtension A K) ρK τK (U.subtype.baseChange K)
    (isEquivariant_baseChange A hτ hρ hi) _ hs
  exact Module.Flat.lTensor_preserves_injective_linearMap U.subtype U.injective_subtype


/-- Restrict an equivariant map to invariant vectors. -/
def mapInvariants (ρ : RightComodule k A V) (σ : RightComodule k A W) (f : V →ₗ[k] W)
    (hf : IsEquivariant A ρ σ f) : invariants A ρ →ₗ[k] invariants A σ :=
  f.restrict fun v hv ↦ by
    have hρ := (invariantVectorsOperation A ρ v).1.mp hv
    apply (invariantVectorsOperation A σ (f v)).1.mpr
    have h := DFunLike.congr_fun hf v
    change (f.rTensor A) (ρ.coaction v) = σ.coaction (f v) at h
    rw [← h, hρ, LinearMap.rTensor_tmul]

theorem invariantBaseChange_natural : Specs.RationalBaseChange.InvariantNaturality.{u} := by
  intro k K V W _ _ _ _ _ _ _ A ρ σ ρK σK hρ hσ f hf
  let m := mapInvariants A ρ σ f hf
  let mK := mapInvariants (scalarExtension A K) ρK σK (f.baseChange K)
    (isEquivariant_baseChange A hρ hσ hf)
  refine ⟨m, mK, fun _ ↦ rfl, fun _ ↦ rfl, ?_⟩
  intro e e' he he'
  apply TensorProduct.AlgebraTensorModule.ext
  intro a v
  apply Subtype.ext
  change (f.baseChange K) (e (a ⊗ₜ[k] v) : K ⊗[k] V) =
    (e' (m.baseChange K (a ⊗ₜ[k] v)) : K ⊗[k] W)
  rw [he, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, he']
  rfl

section HomNaturality

variable {V' W' : Type u} [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']

private theorem isEquivariant_comp
    (ρ' : RightComodule k A V') (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (i : V' →ₗ[k] V) (f : V →ₗ[k] W)
    (hi : IsEquivariant A ρ' ρ i) (hf : IsEquivariant A ρ σ f) :
    IsEquivariant A ρ' σ (f.comp i) := by
  unfold IsEquivariant at hi hf ⊢
  rw [LinearMap.rTensor_comp, LinearMap.comp_assoc, hi, ← LinearMap.comp_assoc, hf,
    LinearMap.comp_assoc]

/-- Precomposition and postcomposition by equivariant maps on equivariant Hom. -/
def mapEquivariantHom
    (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (ρ' : RightComodule k A V') (σ' : RightComodule k A W')
    (i : V' →ₗ[k] V) (j : W →ₗ[k] W')
    (hi : IsEquivariant A ρ' ρ i) (hj : IsEquivariant A σ σ' j) :
    equivariantHom A ρ σ →ₗ[k] equivariantHom A ρ' σ' :=
  ((LinearMap.compRight k j).comp ((LinearMap.llcomp k V' V W).flip i)).restrict
    fun f hf ↦ (mem_equivariantHom A ρ' σ' _).mpr <|
      isEquivariant_comp A ρ' σ σ' (f.comp i) j
        (isEquivariant_comp A ρ' ρ σ i f hi ((mem_equivariantHom A ρ σ f).mp hf)) hj

theorem equivariantHomBaseChange_natural : Specs.RationalBaseChange.EquivariantHomNaturality.{u} := by
  intro k K V W V' W' _ _ _ _ _ _ _ _ _ _ _ A ρ σ ρ' σ' ρK σK ρK' σK' hρ hσ hρ' hσ' i j hi hj
  let m := mapEquivariantHom A ρ σ ρ' σ' i j hi hj
  let mK := mapEquivariantHom (scalarExtension A K) ρK σK ρK' σK' (i.baseChange K) (j.baseChange K)
    (isEquivariant_baseChange A hρ' hρ hi) (isEquivariant_baseChange A hσ hσ' hj)
  refine ⟨m, mK, fun _ ↦ rfl, fun _ ↦ rfl, ?_⟩
  intro e e' he he'
  apply TensorProduct.AlgebraTensorModule.ext
  intro a f
  apply Subtype.ext
  change (j.baseChange K).comp
      ((e (a ⊗ₜ[k] f) : (K ⊗[k] V) →ₗ[K] (K ⊗[k] W)).comp (i.baseChange K)) =
    (e' (m.baseChange K (a ⊗ₜ[k] f)) : (K ⊗[k] V') →ₗ[K] (K ⊗[k] W'))
  rw [he, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.baseChange_tmul, he']
  change a • ((j.baseChange K).comp (((f : V →ₗ[k] W).baseChange K).comp (i.baseChange K))) =
    a • ((j.comp ((f : V →ₗ[k] W).comp i)).baseChange K)
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp]

end HomNaturality

end LinearAlgebraicGroups.RationalRepresentations
