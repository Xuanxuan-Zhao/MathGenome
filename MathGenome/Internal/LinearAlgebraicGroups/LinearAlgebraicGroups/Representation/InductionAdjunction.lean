import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.InductionAdjunction

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLineBundle
open CategoryTheory Coalgebra HopfAlgebra WithConv
open scoped TensorProduct

universe u

noncomputable section

namespace LinearAlgebraicGroups.InductionAdjunction

open Specs.InductionAdjunction
open Specs.FlagLineBundle
open LinearAlgebraicGroups.RationalRepresentations (evaluate IsEquivariant)

section

variable {k : Type u} [Field k] {A D : HopfAlgebraCategory k}
variable {V : Type u} [AddCommGroup V] [Module k V]

local notation "S" => antipode k
local notation "Δ" => comul (R := k)
local notation "ε" => counit (R := k)

/-- The identity point on the universal algebra, inverted twice. -/
private theorem antipodeInvolutive (a : A) : S (S a) = a := by
  let := convolutionGroup A (CommAlgCat.of k A)
  let g : WithConv (A →ₐ[k] A) := toConv (AlgHom.id k A)
  exact congrArg (fun f : WithConv (A →ₐ[k] A) => f a) (inv_inv g)

/-- Inverting the universal pair reverses its product. -/
private theorem comulAntipode (a : A) :
    Δ (S a) = TensorProduct.map (antipode k (A := A)) (antipode k (A := A))
      (TensorProduct.comm k A A (Δ a)) := by
  let := convolutionGroup A (CommAlgCat.of k (A ⊗[k] A))
  let x : WithConv (A →ₐ[k] A ⊗[k] A) := toConv Algebra.TensorProduct.includeLeft
  let y : WithConv (A →ₐ[k] A ⊗[k] A) := toConv Algebra.TensorProduct.includeRight
  have h := congrArg (fun f : WithConv (A →ₐ[k] A ⊗[k] A) => f a) (mul_inv_rev x y)
  change (x * y) (S a) = (y⁻¹ * x⁻¹) a at h
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply] at h
  have hleft : (Algebra.TensorProduct.lift x.ofConv y.ofConv
      (fun _ _ => Commute.all _ _)).toLinearMap = LinearMap.id := by
    apply TensorProduct.ext'
    intro b d
    simp [x, y]
  have hright : (Algebra.TensorProduct.lift y⁻¹.ofConv x⁻¹.ofConv
      (fun _ _ => Commute.all _ _)).toLinearMap =
      TensorProduct.map (antipode k (A := A)) (antipode k (A := A)) ∘ₗ
        (TensorProduct.comm k A A).toLinearMap := by
    apply TensorProduct.ext'
    intro b d
    change ((1 : A) ⊗ₜ[k] S b) * (S d ⊗ₜ[k] (1 : A)) = S d ⊗ₜ[k] S b
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  change (Algebra.TensorProduct.lift x.ofConv y.ofConv
      (fun _ _ => Commute.all _ _)).toLinearMap (Δ (S a)) =
    (Algebra.TensorProduct.lift y⁻¹.ofConv x⁻¹.ofConv
      (fun _ _ => Commute.all _ _)).toLinearMap (Δ a) at h
  rwa [hleft, hright] at h

private theorem mapAntipode (q : A ⟶ D) (a : A) :
    q.hom (S a) = S (q.hom a) := by
  let := convolutionGroup D (CommAlgCat.of k D)
  let := convolutionGroup A (CommAlgCat.of k D)
  let m : WithConv (D →ₐ[k] D) →* WithConv (A →ₐ[k] D) :=
    { toFun := fun f => toConv (f.ofConv.comp q.hom.toAlgHom)
      map_one' := by
        apply WithConv.ofConv_injective
        ext x
        simp [CoalgHomClass.counit_comp_apply q.hom x]
      map_mul' := fun f g => WithConv.ofConv_injective
        (AlgHom.convMul_comp_bialgHom_distrib f g q.hom) }
  exact (congrArg (fun f : WithConv (A →ₐ[k] D) => f a)
    (map_inv m (toConv (AlgHom.id k D)))).symm

/-- Contract a tensor on the vector factor against a linear functional. -/
private def slice {C : Type u} [AddCommGroup C] [Module k C]
    (ℓ : V →ₗ[k] k) : V ⊗[k] C →ₗ[k] C :=
  (TensorProduct.lid k C).toLinearMap ∘ₗ ℓ.rTensor C

@[simp] private theorem slice_tmul {C : Type u} [AddCommGroup C] [Module k C]
    (ℓ : V →ₗ[k] k) (v : V) (a : C) : slice ℓ (v ⊗ₜ[k] a) = ℓ v • a := rfl

private def coefficient (τ : RightComodule k A V) (ℓ : V →ₗ[k] k) : V →ₗ[k] A :=
  slice ℓ ∘ₗ τ.coaction

private def inverseCoefficient (τ : RightComodule k A V) (ℓ : V →ₗ[k] k) : V →ₗ[k] A :=
  S ∘ₗ coefficient τ ℓ

/-- Coassociativity of a representation, paired with a functional. -/
private theorem comulCoefficient (τ : RightComodule k A V) (ℓ : V →ₗ[k] k) (v : V) :
    Δ (coefficient τ ℓ v) = ((coefficient τ ℓ).rTensor A) (τ.coaction v) := by
  have hleft : (slice ℓ : V ⊗[k] (A ⊗[k] A) →ₗ[k] _) ∘ₗ
      (TensorProduct.assoc k V A A).toLinearMap =
      (slice ℓ).rTensor A := by
    apply TensorProduct.ext'
    intro t a
    induction t using TensorProduct.inductionOn with
    | tmul w b => simp [TensorProduct.smul_tmul']
    | add t₁ t₂ h₁ h₂ =>
      simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) h₁ h₂
  have hright : (slice ℓ : V ⊗[k] (A ⊗[k] A) →ₗ[k] _) ∘ₗ (comul (R := k) (A := A)).lTensor V =
      Δ ∘ₗ (slice ℓ : V ⊗[k] A →ₗ[k] A) := by
    apply TensorProduct.ext'
    intro w a
    simp
  have h := congrArg (slice ℓ : V ⊗[k] (A ⊗[k] A) →ₗ[k] _) (τ.coassoc v)
  change ((slice ℓ).comp (TensorProduct.assoc k V A A).toLinearMap)
    (τ.coaction.rTensor A (τ.coaction v)) =
      ((slice ℓ).comp ((comul (R := k) (A := A)).lTensor V)) (τ.coaction v) at h
  rw [hleft, hright, ← LinearMap.rTensor_comp_apply] at h
  exact h.symm

private theorem regularInverseCoefficient (τ : RightComodule k A V) (ℓ : V →ₗ[k] k)
    (v : V) :
    leftRegularCoaction A (inverseCoefficient τ ℓ v) =
      (inverseCoefficient τ ℓ).rTensor A (τ.coaction v) := by
  have h : (antipode k (A := A)).lTensor A ∘ₗ (TensorProduct.comm k A A).toLinearMap ∘ₗ
      TensorProduct.map (antipode k (A := A)) (antipode k (A := A)) ∘ₗ (TensorProduct.comm k A A).toLinearMap =
      (antipode k (A := A)).rTensor A := by
    apply TensorProduct.ext'
    intro a b
    simp [antipodeInvolutive]
  change (antipode k (A := A)).lTensor A (TensorProduct.comm k A A (Δ (S (coefficient τ ℓ v)))) = _
  rw [comulAntipode]
  change ( (antipode k (A := A)).lTensor A ∘ₗ (TensorProduct.comm k A A).toLinearMap ∘ₗ
      TensorProduct.map (antipode k (A := A)) (antipode k (A := A)) ∘ₗ (TensorProduct.comm k A A).toLinearMap)
    (Δ (coefficient τ ℓ v)) = _
  rw [h, comulCoefficient, ← LinearMap.rTensor_comp_apply]
  rfl

private theorem counitInverseCoefficient (τ : RightComodule k A V) (ℓ : V →ₗ[k] k) (v : V) :
    ε (inverseCoefficient τ ℓ v) = ℓ v := by
  have h : ε ∘ₗ (slice ℓ : V ⊗[k] A →ₗ[k] A) =
      ℓ ∘ₗ (TensorProduct.rid k V).toLinearMap ∘ₗ (counit (R := k) (A := A)).lTensor V := by
    apply TensorProduct.ext'
    intro w a
    simp [mul_comm]
  change ε (S (coefficient τ ℓ v)) = ℓ v
  rw [counit_antipode]
  exact (DFunLike.congr_fun h (τ.coaction v)).trans (congrArg ℓ (τ.counit v))

private theorem sliceNatural {C C' : Type u} [AddCommGroup C] [Module k C]
    [AddCommGroup C'] [Module k C'] (f : C →ₗ[k] C') (ℓ : V →ₗ[k] k) :
    (slice ℓ).comp (f.lTensor V) = f.comp (slice ℓ) := by
  apply TensorProduct.ext'
  intro v a
  simp

private theorem sliceAfterMap {C V' : Type u} [AddCommGroup C] [Module k C]
    [AddCommGroup V'] [Module k V'] (f : V →ₗ[k] V') (ℓ : V' →ₗ[k] k) :
    (slice ℓ : V' ⊗[k] C →ₗ[k] C).comp (f.rTensor C) = slice (ℓ.comp f) := by
  apply TensorProduct.ext'
  intro v a
  simp

private theorem sliceCounitComul (a : A) : slice ε (Δ a) = a := by
  change TensorProduct.lid k A ((counit (R := k) (A := A)).rTensor A (Δ a)) = _
  rw [rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]

private theorem sliceCounitLeftRegular (a : A) : slice ε (leftRegularCoaction A a) = S a := by
  have h : (slice ε : A ⊗[k] A →ₗ[k] A) ∘ₗ (antipode k (A := A)).lTensor A ∘ₗ
      (TensorProduct.comm k A A).toLinearMap =
      S ∘ₗ (TensorProduct.rid k A).toLinearMap ∘ₗ (counit (R := k) (A := A)).lTensor A := by
    apply TensorProduct.ext'
    intro b d
    simp
  change ((slice ε : A ⊗[k] A →ₗ[k] A) ∘ₗ (antipode k (A := A)).lTensor A ∘ₗ
    (TensorProduct.comm k A A).toLinearMap) (Δ a) = _
  rw [h]
  simp [lTensor_counit_comul]

variable (q : A ⟶ D) (c : GroupLike k D)
variable (ρ₁ : RightComodule k D k) (ρ : RightComodule k A (covariantFunctions q c))
variable (τ : RightComodule k A V)

local notation "qₗ" => q.hom.toAlgHom.toLinearMap
local notation "W" => covariantFunctions q c
local notation "iW" => Submodule.subtype (covariantFunctions q c)
local notation "δH" => LinearMap.comp (LinearMap.lTensor V qₗ) τ.coaction

private theorem inverseCoefficient_mem (h₁ : ∀ z, ρ₁.coaction z = z ⊗ₜ[k] (c : D))
    (ℓ : equivariantHom δH ρ₁.coaction) (v : V) :
    inverseCoefficient τ ℓ.val v ∈ W := by
  have hq (w : V) : qₗ (coefficient τ ℓ.val w) = ℓ.val w • (c : D) := by
    have h := congrArg (TensorProduct.lid k D) (DFunLike.congr_fun ℓ.property w)
    change slice ℓ.val ((qₗ).lTensor V (τ.coaction w)) =
      TensorProduct.lid k D (ρ₁.coaction (ℓ.val w)) at h
    rw [h₁, TensorProduct.lid_tmul] at h
    exact (DFunLike.congr_fun (sliceNatural qₗ ℓ.val) (τ.coaction w)).symm.trans h
  have hmap :
      (qₗ).lTensor A ∘ₗ TensorProduct.map (antipode k (A := A)) (antipode k (A := A)) ∘ₗ
        (TensorProduct.comm k A A).toLinearMap ∘ₗ (coefficient τ ℓ.val).rTensor A =
      (TensorProduct.mk k A D).flip (↑(c⁻¹) : D) ∘ₗ S ∘ₗ slice ℓ.val := by
    apply TensorProduct.ext'
    intro w a
    simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.flip_apply,
      TensorProduct.mk_apply, slice_tmul, map_smul]
    change S a ⊗ₜ[k] q.hom (S (coefficient τ ℓ.val w)) = _
    rw [mapAntipode, show q.hom (coefficient τ ℓ.val w) = _ from hq w, map_smul]
    change S a ⊗ₜ[k] (ℓ.val w • (↑(c⁻¹) : D)) =
      (ℓ.val w • S a) ⊗ₜ[k] (↑(c⁻¹) : D)
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  change (qₗ).lTensor A (Δ (S (coefficient τ ℓ.val v))) = _
  rw [comulAntipode, comulCoefficient]
  exact DFunLike.congr_fun hmap (τ.coaction v)

private theorem eval_leftRegular (f : W) :
    TensorProduct.map (counit (R := k) (A := A)) qₗ (leftRegularCoaction A (f : A)) =
      ε (f : A) ⊗ₜ[k] (c : D) := by
  have hf : (qₗ).lTensor A (Δ (f : A)) = (f : A) ⊗ₜ[k] (↑(c⁻¹) : D) :=
    f.property
  have hq : qₗ (f : A) = ε (f : A) • (↑(c⁻¹) : D) := by
    have h := congrArg (slice ε : A ⊗[k] D →ₗ[k] D) hf
    rw [slice_tmul] at h
    exact (congrArg qₗ (sliceCounitComul (f : A))).symm.trans
      ((DFunLike.congr_fun (sliceNatural qₗ ε) (Δ (f : A))).symm.trans h)
  apply (TensorProduct.lid k D).injective
  have h : (TensorProduct.lid k D).toLinearMap ∘ₗ TensorProduct.map (counit (R := k) (A := A)) qₗ =
      qₗ ∘ₗ slice (counit (R := k) (A := A)) := by
    apply TensorProduct.ext'
    intro a b
    simp
  change ((TensorProduct.lid k D).toLinearMap ∘ₗ TensorProduct.map (counit (R := k) (A := A)) qₗ)
    (leftRegularCoaction A (f : A)) = _
  rw [h, LinearMap.comp_apply, sliceCounitLeftRegular]
  change q.hom (S (f : A)) = ε (f : A) • (c : D)
  rw [mapAntipode, show q.hom (f : A) = _ from hq, map_smul]
  change ε (f : A) • (↑((c⁻¹)⁻¹) : D) = _
  rw [inv_inv]

private theorem underlyingEquivariant
    (hρ : ((iW).rTensor A).comp ρ.coaction = (leftRegularCoaction A).comp iW)
    (f : equivariantHom τ.coaction ρ.coaction) (v : V) :
    ((iW).comp f.val).rTensor A (τ.coaction v) = leftRegularCoaction A (f.val v : A) := by
  have hf : f.val.rTensor A (τ.coaction v) = ρ.coaction (f.val v) :=
    DFunLike.congr_fun f.property v
  rw [LinearMap.rTensor_comp_apply, hf]
  exact DFunLike.congr_fun hρ (f.val v)

private def evalOne (f : V →ₗ[k] W) : V →ₗ[k] k := ε ∘ₗ iW ∘ₗ f

private theorem evalOne_mem (h₁ : ∀ z, ρ₁.coaction z = z ⊗ₜ[k] (c : D))
    (hρ : ((iW).rTensor A).comp ρ.coaction = (leftRegularCoaction A).comp iW)
    (f : equivariantHom τ.coaction ρ.coaction) :
    evalOne q c f.val ∈ equivariantHom δH ρ₁.coaction := by
  change ((evalOne q c f.val).rTensor D).comp δH = ρ₁.coaction.comp (evalOne q c f.val)
  ext v : 1
  have h : (evalOne q c f.val).rTensor D ∘ₗ (qₗ).lTensor V =
      TensorProduct.map (counit (R := k) (A := A)) qₗ ∘ₗ ((iW).comp f.val).rTensor A := by
    apply TensorProduct.ext'
    intro w a
    rfl
  change ((evalOne q c f.val).rTensor D ∘ₗ (qₗ).lTensor V) (τ.coaction v) =
    ρ₁.coaction (evalOne q c f.val v)
  rw [h, LinearMap.comp_apply, underlyingEquivariant q c ρ τ hρ, h₁,
    eval_leftRegular q c]
  rfl

private theorem inverseCoefficient_evalOne
    (hρ : ((iW).rTensor A).comp ρ.coaction = (leftRegularCoaction A).comp iW)
    (f : equivariantHom τ.coaction ρ.coaction) (v : V) :
    inverseCoefficient τ (evalOne q c f.val) v = (f.val v : A) := by
  have h := congrArg (slice ε) (underlyingEquivariant q c ρ τ hρ f v)
  change ((slice ε).comp (((iW).comp f.val).rTensor A)) (τ.coaction v) =
    slice ε (leftRegularCoaction A (f.val v : A)) at h
  rw [sliceAfterMap, sliceCounitLeftRegular] at h
  have h' : coefficient τ (evalOne q c f.val) v = S (f.val v : A) := by
    rw [show evalOne q c f.val = ε ∘ₗ ((iW).comp f.val) from rfl]
    exact h
  change S (coefficient τ (evalOne q c f.val) v) = _
  rw [h', antipodeInvolutive]

private def inverseHom (h₁ : ∀ z, ρ₁.coaction z = z ⊗ₜ[k] (c : D))
    (ℓ : equivariantHom δH ρ₁.coaction) : V →ₗ[k] W :=
  (inverseCoefficient τ ℓ.val).codRestrict W (inverseCoefficient_mem q c ρ₁ τ h₁ ℓ)

private theorem inverseHom_mem (h₁ : ∀ z, ρ₁.coaction z = z ⊗ₜ[k] (c : D))
    (hρ : ((iW).rTensor A).comp ρ.coaction = (leftRegularCoaction A).comp iW)
    (ℓ : equivariantHom δH ρ₁.coaction) :
    inverseHom q c ρ₁ τ h₁ ℓ ∈ equivariantHom τ.coaction ρ.coaction := by
  change ((inverseHom q c ρ₁ τ h₁ ℓ).rTensor A).comp τ.coaction =
    ρ.coaction.comp (inverseHom q c ρ₁ τ h₁ ℓ)
  let b := inverseHom q c ρ₁ τ h₁ ℓ
  ext v : 1
  apply Module.Flat.rTensor_preserves_injective_linearMap iW Subtype.val_injective
  change (((iW).rTensor A).comp (b.rTensor A)) (τ.coaction v) =
    (((iW).rTensor A).comp ρ.coaction) (b v)
  rw [← LinearMap.rTensor_comp, hρ]
  exact (regularInverseCoefficient τ ℓ.val v).symm

private def reciprocityEquiv (h₁ : ∀ z, ρ₁.coaction z = z ⊗ₜ[k] (c : D))
    (hρ : ((iW).rTensor A).comp ρ.coaction = (leftRegularCoaction A).comp iW) :
    equivariantHom τ.coaction ρ.coaction ≃ₗ[k] equivariantHom δH ρ₁.coaction where
  toFun f := ⟨evalOne q c f.val, evalOne_mem q c ρ₁ ρ τ h₁ hρ f⟩
  invFun ℓ := ⟨inverseHom q c ρ₁ τ h₁ ℓ, inverseHom_mem q c ρ₁ ρ τ h₁ hρ ℓ⟩
  left_inv f := by
    apply Subtype.ext
    ext v : 1
    apply Subtype.ext
    exact inverseCoefficient_evalOne q c ρ τ hρ f v
  right_inv ℓ := by
    apply Subtype.ext
    ext v : 1
    exact counitInverseCoefficient τ ℓ.val v
  map_add' f g := by
    apply Subtype.ext
    ext v : 1
    simp [evalOne]
  map_smul' a f := by
    apply Subtype.ext
    ext v : 1
    simp [evalOne]

private theorem inverseCoefficient_apply_point (ℓ : V →ₗ[k] k)
    (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)) (v : V) :
    let := convolutionGroup A R
    g (inverseCoefficient τ ℓ v) =
      TensorProduct.lid k R ((ℓ.rTensor R) (evaluate A τ (g⁻¹).ofConv v)) := by
  let := convolutionGroup A R
  change (g⁻¹).ofConv.toLinearMap (slice ℓ (τ.coaction v)) =
    (slice ℓ).comp ((g⁻¹).ofConv.toLinearMap.lTensor V) (τ.coaction v)
  exact (DFunLike.congr_fun (sliceNatural (g⁻¹).ofConv.toLinearMap ℓ) (τ.coaction v)).symm

private theorem reciprocity (h₁ : ∀ z, ρ₁.coaction z = z ⊗ₜ[k] (c : D))
    (hρ : ((iW).rTensor A).comp ρ.coaction = (leftRegularCoaction A).comp iW) :
    Reciprocity q c ρ₁ ρ := by
  refine ⟨fun _ _ _ _ t => reciprocityEquiv q c ρ₁ ρ t h₁ hρ, ?_, ?_, ?_⟩
  · intros
    rfl
  · intro V _ _ _ t ℓ R g v
    exact inverseCoefficient_apply_point t ℓ.val R g v
  · intro V V' _ _ _ _ _ _ t t' h hh f
    let f' : equivariantHom t'.coaction ρ.coaction :=
      ⟨f.val.comp h, by
        change ((f.val.comp h).rTensor A).comp t'.coaction =
          ρ.coaction.comp (f.val.comp h)
        rw [LinearMap.rTensor_comp, LinearMap.comp_assoc, hh, ← LinearMap.comp_assoc,
          show (f.val.rTensor A).comp t.coaction = ρ.coaction.comp f.val from f.property,
          LinearMap.comp_assoc]⟩
    exact ⟨f', rfl, rfl⟩

end

/-- Evaluation at the identity and the inverse orbit coefficient give Frobenius
reciprocity for the flag induction supplied by the ordered bundle premises. -/
theorem flagInductionAdjunction_conditional :
    BorelCharacterLine.{u} →
    CharacterLine.{u} →
    CovarianceOnPoints.{u} →
    CovariantCoaction.{u} →
    FlagInduction.{u} →
    FlagLineBundleAndSections.{u} →
    OppositeFlagGeometry.{u} →
    SchemeCovarianceComparison.{u} →
    SectionsAreCovariant.{u} →
    FlagInductionAdjunction.{u} := by
  intro _ _ _ _ flagInduction _ _ _ _ k _ G P χ
  obtain ⟨p, Q, a, A, D, e, d, q, ψ, c, ρ₁, L, E, ρ,
    hSmooth, hProper, hTorsor, hProjective, hAction, hInclusion, hCharacter,
    hCoordinate, hLine, hFinite, hSections, hCoaction, hTranslation⟩ :=
    flagInduction k G P χ
  exact ⟨p, Q, a, A, D, e, d, q, ψ, c, ρ₁, L, E, ρ,
    hSmooth, hProper, hTorsor, hProjective, hAction, hInclusion, hCharacter,
    hCoordinate, hLine, hFinite, hSections, hCoaction, hTranslation,
    reciprocity q c ρ₁ ρ hLine hCoaction⟩

end LinearAlgebraicGroups.InductionAdjunction

universe v8_closure_6b7c177737915fcc_u0
theorem _root_.«LinearAlgebraicGroups».«InductionAdjunction».«flagInductionAdjunction» : _root_.«LinearAlgebraicGroups».«Specs».«InductionAdjunction».«FlagInductionAdjunction».{v8_closure_6b7c177737915fcc_u0} :=
  @_root_.«LinearAlgebraicGroups».«InductionAdjunction».«flagInductionAdjunction_conditional».{v8_closure_6b7c177737915fcc_u0} (@_root_.«LinearAlgebraicGroups».«FlagLineBundle».«borelCharacterLine».{v8_closure_6b7c177737915fcc_u0}) (@_root_.«LinearAlgebraicGroups».«FlagLineBundle».«characterLine».{v8_closure_6b7c177737915fcc_u0}) (@_root_.«LinearAlgebraicGroups».«FlagLineBundle».«covarianceOnPoints».{v8_closure_6b7c177737915fcc_u0}) (@_root_.«LinearAlgebraicGroups».«FlagLineBundle».«covariantCoaction».{v8_closure_6b7c177737915fcc_u0}) (@_root_.«LinearAlgebraicGroups».«FlagLineBundle».«flagInduction».{v8_closure_6b7c177737915fcc_u0}) (@_root_.«LinearAlgebraicGroups».«FlagLineBundle».«flagLineBundleAndSections».{v8_closure_6b7c177737915fcc_u0}) (@_root_.«LinearAlgebraicGroups».«FlagLineBundle».«oppositeFlagGeometry».{v8_closure_6b7c177737915fcc_u0}) (@_root_.«LinearAlgebraicGroups».«FlagLineBundle».«schemeCovarianceComparison».{v8_closure_6b7c177737915fcc_u0}) (@_root_.«LinearAlgebraicGroups».«FlagLineBundle».«sectionsAreCovariant».{v8_closure_6b7c177737915fcc_u0})
