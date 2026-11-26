import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.ExactInvariants
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.WeightDecomposition
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

open CategoryTheory TensorProduct
open scoped TensorProduct DirectSum

universe u

namespace LinearAlgebraicGroups.ExactInvariants

open RationalRepresentations

section Restriction

variable {k U V W : Type u} [Field k] [AddCommGroup U] [Module k U]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] {A : HopfAlgebraCategory k}

private theorem exact_invariantsMap
    {ρ : RightComodule k A U} {σ : RightComodule k A V} {τ : RightComodule k A W}
    {f : U →ₗ[k] V} {g : V →ₗ[k] W}
    (hf : (f.rTensor A).comp ρ.coaction = σ.coaction.comp f)
    (hg : (g.rTensor A).comp σ.coaction = τ.coaction.comp g)
    (hi : Function.Injective f) (he : Function.Exact f g) :
    Function.Exact (invariantsMap f hf) (invariantsMap g hg) := by
  intro v
  constructor
  · intro hv
    have hv' : g (v : V) = 0 := congrArg Subtype.val hv
    obtain ⟨x, hx⟩ := (he (v : V)).mp hv'
    have hx' : x ∈ invariants A ρ := by
      apply mem_invariants.mpr
      apply Module.Flat.rTensor_preserves_injective_linearMap (M := A) f hi
      have h := DFunLike.congr_fun hf x
      change f.rTensor A (ρ.coaction x) = σ.coaction (f x) at h
      rw [h, LinearMap.rTensor_tmul, hx, mem_invariants.mp v.property]
    exact ⟨⟨x, hx'⟩, Subtype.ext hx⟩
  · rintro ⟨x, rfl⟩
    exact Subtype.ext ((he (f (x : U))).mpr ⟨x, rfl⟩)

end Restriction

section Diagonalizable

variable {k V W : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

private theorem surjective_on_weight_one {M : Type u} [CommGroup M]
    {ρ : RightComodule k (Specs.DiagonalizableGroups.groupAlgebra k M) V}
    {σ : RightComodule k (Specs.DiagonalizableGroups.groupAlgebra k M) W} {f : V →ₗ[k] W}
    (hf : (f.rTensor (Specs.DiagonalizableGroups.groupAlgebra k M)).comp ρ.coaction =
      σ.coaction.comp f) (hs : Function.Surjective f) :
    Function.Surjective (invariantsMap f hf) := by
  classical
  let P := WeightDecomposition.weightSpace ρ
  let Q := WeightDecomposition.weightSpace σ
  have hP : Function.Bijective (DirectSum.coeLinearMap P) :=
    WeightDecomposition.weightDecomposition ρ
  have hQ : Function.Bijective (DirectSum.coeLinearMap Q) :=
    WeightDecomposition.weightDecomposition σ
  obtain ⟨F, hF, hsum⟩ := WeightDecomposition.functoriality ρ σ f hf
  intro w
  let w₁ : Q 1 := ⟨w, by
    change (w : W) ∈ WeightDecomposition.weightSpace σ 1
    rw [← WeightDecomposition.invariants σ]
    exact w.property⟩
  obtain ⟨v, hv⟩ := hs (w : W)
  obtain ⟨a, ha⟩ := hP.surjective v
  have h : DirectSum.lmap F a = DirectSum.lof k M (fun m ↦ Q m) 1 w₁ := by
    apply hQ.injective
    rw [DirectSum.coeLinearMap_lof]
    have h := DFunLike.congr_fun hsum a
    change DirectSum.coeLinearMap Q (DirectSum.lmap F a) = f (DirectSum.coeLinearMap P a) at h
    rw [ha, hv] at h
    exact h
  have h₁ := congrArg (DirectSum.component k M (fun m ↦ Q m) 1) h
  rw [DirectSum.component.lof_self] at h₁
  change F 1 (a 1) = w₁ at h₁
  refine ⟨⟨a 1, (WeightDecomposition.invariants ρ).symm ▸ (a 1).property⟩, ?_⟩
  apply Subtype.ext
  rw [coe_invariantsMap, ← hF 1, h₁]

variable {A B : HopfAlgebraCategory k}

private def transportCoaction (φ : A →ₐc[k] B) (ρ : RightComodule k A V) :
    RightComodule k B V where
  coaction := (φ.toLinearMap.lTensor V).comp ρ.coaction
  coassoc x := by
    let e : A →ₗ[k] B := φ.toLinearMap
    let d := (e.lTensor V).comp ρ.coaction
    have h₁ : (d.rTensor B).comp (e.lTensor V) =
        (TensorProduct.map (e.lTensor V) e).comp (ρ.coaction.rTensor A) := by
      apply TensorProduct.ext'
      intro v a
      simp [d]
    have h₂ : ((Coalgebra.comul (R := k) (A := B)).lTensor V).comp (e.lTensor V) =
        (TensorProduct.map LinearMap.id (TensorProduct.map e e)).comp
          ((Coalgebra.comul (R := k) (A := A)).lTensor V) := by
      apply TensorProduct.ext'
      intro v a
      simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
        LinearMap.id_apply]
      exact congrArg (fun t ↦ v ⊗ₜ[k] t) (CoalgHomClass.map_comp_comul_apply φ a).symm
    change TensorProduct.assoc k V B B ((d.rTensor B) (e.lTensor V (ρ.coaction x))) =
      (Coalgebra.comul (R := k) (A := B)).lTensor V (e.lTensor V (ρ.coaction x))
    rw [show (d.rTensor B) (e.lTensor V (ρ.coaction x)) =
      TensorProduct.map (e.lTensor V) e (ρ.coaction.rTensor A (ρ.coaction x)) from
      DFunLike.congr_fun h₁ (ρ.coaction x)]
    rw [show (Coalgebra.comul (R := k) (A := B)).lTensor V (e.lTensor V (ρ.coaction x)) =
      TensorProduct.map LinearMap.id (TensorProduct.map e e)
        ((Coalgebra.comul (R := k) (A := A)).lTensor V (ρ.coaction x)) from
      DFunLike.congr_fun h₂ (ρ.coaction x)]
    rw [← ρ.coassoc x]
    exact (TensorProduct.map_map_assoc LinearMap.id e e _).symm
  counit x := by
    have h : ((Coalgebra.counit (R := k) (A := B)).lTensor V).comp (φ.toLinearMap.lTensor V) =
        (Coalgebra.counit (R := k) (A := A)).lTensor V := by
      apply TensorProduct.ext'
      intro v a
      simp
    exact (congrArg (TensorProduct.rid k V) (DFunLike.congr_fun h (ρ.coaction x))).trans (ρ.counit x)

private theorem invariants_transportCoaction (e : A ≅ B) (ρ : RightComodule k A V) :
    invariants B (transportCoaction e.hom.hom ρ) = invariants A ρ := by
  ext v
  rw [mem_invariants, mem_invariants]
  let φ : A →ₗ[k] B := e.hom.hom.toLinearMap
  have h : φ.lTensor V (v ⊗ₜ[k] (1 : A)) = v ⊗ₜ[k] (1 : B) := by
    rw [LinearMap.lTensor_tmul]
    change v ⊗ₜ[k] e.hom.hom 1 = _
    rw [map_one]
  change φ.lTensor V (ρ.coaction v) = v ⊗ₜ[k] (1 : B) ↔ _
  rw [← h, (Module.Flat.lTensor_preserves_injective_linearMap φ
    (CommHopfAlgCat.ofIso e).injective).eq_iff]

private theorem surjective_on_diagonalizable_invariants
    {ρ : RightComodule k A V} {σ : RightComodule k A W} {f : V →ₗ[k] W}
    (hf : (f.rTensor A).comp ρ.coaction = σ.coaction.comp f) (hs : Function.Surjective f)
    (hA : Specs.CharacterDescent.IsDiagonalizable A) :
    Function.Surjective (invariantsMap f hf) := by
  obtain ⟨M, ⟨e⟩⟩ := hA
  let B := Specs.DiagonalizableGroups.groupAlgebra k M.obj
  let φ : A →ₗ[k] B := e.inv.hom.toLinearMap
  let ρ' := transportCoaction e.inv.hom ρ
  let σ' := transportCoaction e.inv.hom σ
  have hf' : (f.rTensor B).comp ρ'.coaction = σ'.coaction.comp f := by
    change (f.rTensor B).comp ((φ.lTensor V).comp ρ.coaction) =
      ((φ.lTensor W).comp σ.coaction).comp f
    rw [← LinearMap.comp_assoc, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_assoc, hf, LinearMap.comp_assoc]
  intro w
  have hw : (w : W) ∈ invariants B σ' := by
    change (w : W) ∈ invariants _ (transportCoaction e.symm.hom.hom σ)
    rw [invariants_transportCoaction e.symm σ]
    exact w.property
  obtain ⟨v, hv⟩ := surjective_on_weight_one hf' hs ⟨w, hw⟩
  have hv' : (v : V) ∈ invariants A ρ := invariants_transportCoaction e.symm ρ ▸ v.property
  have hval : f (v : V) = (w : W) := congrArg Subtype.val hv
  exact ⟨⟨v, hv'⟩, Subtype.ext hval⟩

end Diagonalizable

section Descent

open TensorProduct.AlgebraTensorModule (distribBaseChange)

variable {k K V W : Type u} [Field k] [Field K] [Algebra k K]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {A : HopfAlgebraCategory k}

private theorem exists_extended_coaction [FiniteDimensional k V] (ρ : RightComodule k A V) :
    ∃ σ : RightComodule K (scalarExtension A K) (K ⊗[k] V),
      σ.coaction = (distribBaseChange k K V A).toLinearMap.comp (ρ.coaction.baseChange K) ∧
      invariants (scalarExtension A K) σ = (invariants A ρ).baseChange K := by
  classical
  let b := (Module.finBasis k V).reindex (Equiv.ulift.{u}).symm
  obtain ⟨σ, hcoeff, hinv, _⟩ := fieldExtensionComparison A b ρ (K := K)
  refine ⟨σ, ?_, hinv⟩
  apply (b.baseChange K).ext
  intro j
  rw [coaction_apply_basis _ (b.baseChange K) σ j]
  simp only [hcoeff, Module.Basis.baseChange_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.baseChange_tmul, coaction_apply_basis A b ρ j, TensorProduct.tmul_sum, map_sum,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]

private theorem distribBaseChange_natural (f : V →ₗ[k] W) :
    ((f.baseChange K).rTensor (scalarExtension A K)).comp
        (distribBaseChange k K V A).toLinearMap =
      (distribBaseChange k K W A).toLinearMap.comp ((f.rTensor A).baseChange K) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro r z
  refine TensorProduct.inductionOn z (fun v a ↦ by simp) ?_
  intro x y hx hy
  simp only [TensorProduct.tmul_add, map_add, hx, hy]

private theorem surjective_on_invariants [FiniteDimensional k V] [FiniteDimensional k W]
    {ρ : RightComodule k A V} {σ : RightComodule k A W} {f : V →ₗ[k] W}
    (hf : (f.rTensor A).comp ρ.coaction = σ.coaction.comp f) (hs : Function.Surjective f)
    (hA : Specs.CharacterDescent.IsMultiplicativeType A) :
    Function.Surjective (invariantsMap f hf) := by
  obtain ⟨K, _, _, _, hsplit⟩ := hA
  obtain ⟨ρK, hρK, hiρ⟩ := exists_extended_coaction (K := K) ρ
  obtain ⟨σK, hσK, hiσ⟩ := exists_extended_coaction (K := K) σ
  let B := scalarExtension A K
  have hfK : ((f.baseChange K).rTensor B).comp ρK.coaction = σK.coaction.comp (f.baseChange K) := by
    rw [hρK, hσK, ← LinearMap.comp_assoc, distribBaseChange_natural, LinearMap.comp_assoc,
      ← LinearMap.baseChange_comp, hf, LinearMap.baseChange_comp, LinearMap.comp_assoc]
  have hsK : Function.Surjective (f.baseChange K) := LinearMap.lTensor_surjective K hs
  have hsurj := surjective_on_diagonalizable_invariants hfK hsK hsplit
  -- Identify the restricted map after scalar extension via the tensor inclusions.
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective k K (invariantsMap f hf)).mp
  change Function.Surjective ((invariantsMap f hf).baseChange K)
  let p := invariants A ρ
  let q := invariants A σ
  have hcomp :
      (q.subtype.baseChange K).comp ((invariantsMap f hf).baseChange K) =
        (f.baseChange K).comp (p.subtype.baseChange K) := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    rfl
  intro z
  let w := q.subtype.baseChange K z
  have hw : w ∈ invariants B σK := by
    rw [hiσ]
    exact ⟨z, rfl⟩
  obtain ⟨v, hv⟩ := hsurj ⟨w, hw⟩
  have hv' : (v : K ⊗[k] V) ∈ p.baseChange K := hiρ ▸ v.property
  obtain ⟨x, hx⟩ := hv'
  have hval : f.baseChange K (v : K ⊗[k] V) = w := congrArg Subtype.val hv
  refine ⟨x, ?_⟩
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := K) q.subtype q.injective_subtype
  change (q.subtype.baseChange K) ((invariantsMap f hf).baseChange K x) = w
  exact (DFunLike.congr_fun hcomp x).trans ((congrArg (f.baseChange K) hx).trans hval)

end Descent

theorem exactInvariants : Specs.ExactInvariants.ExactInvariants.{u} := by
  intro k U V W _ _ _ _ _ _ _ _ _ _ A hA ρ σ τ f g hf hg hi he hs
  refine ⟨?_, exact_invariantsMap hf hg hi he, surjective_on_invariants hg hs hA⟩
  intro x y h
  exact Subtype.ext (hi (congrArg Subtype.val h))

end LinearAlgebraicGroups.ExactInvariants
