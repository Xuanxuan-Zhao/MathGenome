import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FullyFaithfulDifferentiation
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.LieStableSubspaces
import Mathlib.LinearAlgebra.TensorProduct.Prod

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups

noncomputable section

open RationalRepresentations
open LinearMap (fst snd)

variable {k V W C : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup C] [Module k C]

private theorem tensorProd_apply (z : (V × W) ⊗[k] C) :
    TensorProduct.prodLeft k k V W C z = ((fst k V W).rTensor C z, (snd k V W).rTensor C z) := by
  apply DFunLike.congr_fun (f := (TensorProduct.prodLeft k k V W C).toLinearMap)
    (g := ((fst k V W).rTensor C).prod ((snd k V W).rTensor C))
  apply TensorProduct.ext'
  rintro ⟨v, w⟩ c
  rfl

private theorem coassoc_after_projection [Coalgebra k C]
    {U : Type u} [AddCommGroup U] [Module k U]
    (p : U →ₗ[k] V) (δ : U →ₗ[k] U ⊗[k] C) (ρ : RightComodule k C V)
    (hp : (p.rTensor C).comp δ = ρ.coaction.comp p) (x : U) :
    p.rTensor (C ⊗[k] C) (TensorProduct.assoc k U C C (δ.rTensor C (δ x))) =
      p.rTensor (C ⊗[k] C) ((Coalgebra.comul (R := k) (A := C)).lTensor U (δ x)) := by
  have hp_apply (y : U) : p.rTensor C (δ y) = ρ.coaction (p y) := DFunLike.congr_fun hp y
  have hassoc (z : (U ⊗[k] C) ⊗[k] C) :
      p.rTensor (C ⊗[k] C) (TensorProduct.assoc k U C C z) =
        TensorProduct.assoc k V C C ((p.rTensor C).rTensor C z) := by
    simpa [LinearMap.rTensor_def] using
      TensorProduct.map_map_assoc p (LinearMap.id : C →ₗ[k] C) LinearMap.id z
  rw [hassoc, ← LinearMap.rTensor_comp_apply, hp, LinearMap.rTensor_comp_apply, hp_apply,
    ρ.coassoc]
  change _ = ((p.rTensor (C ⊗[k] C)).comp ((Coalgebra.comul (R := k) (A := C)).lTensor U)) (δ x)
  rw [LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor]
  exact congrArg _ (hp_apply x).symm

private theorem contractRight_natural {U : Type u} [AddCommGroup U] [Module k U]
    (p : U →ₗ[k] V) (c : C →ₗ[k] k) (z : U ⊗[k] C) :
    p (TensorProduct.rid k U (c.lTensor U z)) =
      TensorProduct.rid k V (c.lTensor V (p.rTensor C z)) := by
  apply DFunLike.congr_fun
    (f := p.comp ((TensorProduct.rid k U).toLinearMap.comp (c.lTensor U)))
    (g := (TensorProduct.rid k V).toLinearMap.comp ((c.lTensor V).comp (p.rTensor C)))
  apply TensorProduct.ext'
  intro x a
  simp

private theorem exists_directSumCoaction (A : HopfAlgebraCategory k)
    (ρ : RightComodule k A V) (σ : RightComodule k A W) :
    ∃ τ : RightComodule k A (V × W),
      IsEquivariant A τ ρ (fst k V W) ∧ IsEquivariant A τ σ (snd k V W) := by
  let e := TensorProduct.prodLeft k k V W A
  let δ := e.symm.toLinearMap.comp ((ρ.coaction.comp (fst k V W)).prod (σ.coaction.comp (snd k V W)))
  have hδ (x : V × W) : ((fst k V W).rTensor A (δ x), (snd k V W).rTensor A (δ x)) =
      (ρ.coaction x.1, σ.coaction x.2) := by
    rw [← tensorProd_apply]
    exact e.apply_symm_apply _
  have hl : ((fst k V W).rTensor A).comp δ = ρ.coaction.comp (fst k V W) :=
    LinearMap.ext fun x => congrArg Prod.fst (hδ x)
  have hr : ((snd k V W).rTensor A).comp δ = σ.coaction.comp (snd k V W) :=
    LinearMap.ext fun x => congrArg Prod.snd (hδ x)
  refine ⟨⟨δ, ?_, ?_⟩, hl, hr⟩
  · intro x
    apply (TensorProduct.prodLeft k k V W (A ⊗[k] A)).injective
    rw [tensorProd_apply, tensorProd_apply]
    exact Prod.ext (coassoc_after_projection _ _ ρ hl x) (coassoc_after_projection _ _ σ hr x)
  · intro x
    apply Prod.ext
    · change fst k V W (TensorProduct.rid k (V × W) _) = x.1
      rw [contractRight_natural, show (fst k V W).rTensor A (δ x) = ρ.coaction x.1 from
        congrArg Prod.fst (hδ x)]
      exact ρ.counit _
    · change snd k V W (TensorProduct.rid k (V × W) _) = x.2
      rw [contractRight_natural, show (snd k V W).rTensor A (δ x) = σ.coaction x.2 from
        congrArg Prod.snd (hδ x)]
      exact σ.counit _

private theorem tensorGraph_iff (f : V →ₗ[k] W) (z : (V × W) ⊗[k] C) :
    z ∈ LinearMap.range (f.graph.subtype.rTensor C) ↔
      (snd k V W).rTensor C z = f.rTensor C ((fst k V W).rTensor C z) := by
  let p := fst k V W
  let q := snd k V W
  let i := f.graph.subtype
  have hi : q.comp i = f.comp (p.comp i) :=
    LinearMap.ext fun w => (f.mem_graph_iff w.val).mp w.property
  constructor
  · rintro ⟨t, rfl⟩
    rw [← LinearMap.rTensor_comp_apply, hi, LinearMap.rTensor_comp_apply,
      LinearMap.rTensor_comp_apply]
  · intro h
    let j : V →ₗ[k] f.graph :=
      (LinearMap.id.prod f).codRestrict _ fun v => (f.mem_graph_iff (v, f v)).mpr rfl
    have hj₁ : p.comp (i.comp j) = LinearMap.id := rfl
    have hj₂ : q.comp (i.comp j) = f := rfl
    refine ⟨j.rTensor C (p.rTensor C z), ?_⟩
    apply (TensorProduct.prodLeft k k V W C).injective
    rw [tensorProd_apply, tensorProd_apply]
    apply Prod.ext
    · change p.rTensor C (i.rTensor C (j.rTensor C (p.rTensor C z))) = p.rTensor C z
      rw [← LinearMap.rTensor_comp_apply C i j, ← LinearMap.rTensor_comp_apply C p (i.comp j),
        hj₁, LinearMap.rTensor_id_apply]
    · change q.rTensor C (i.rTensor C (j.rTensor C (p.rTensor C z))) = q.rTensor C z
      rw [← LinearMap.rTensor_comp_apply C i j, ← LinearMap.rTensor_comp_apply C q (i.comp j),
        hj₂]
      exact h.symm

private theorem isSubcomodule_graph_iff (A : HopfAlgebraCategory k)
    (ρ : RightComodule k A V) (σ : RightComodule k A W) (τ : RightComodule k A (V × W))
    (h₁ : IsEquivariant A τ ρ (fst k V W)) (h₂ : IsEquivariant A τ σ (snd k V W))
    (f : V →ₗ[k] W) :
    τ.IsSubcomodule f.graph ↔ IsEquivariant A ρ σ f := by
  have graphCondition (w : f.graph) :
      τ.coaction w.val ∈ LinearMap.range (f.graph.subtype.rTensor A) ↔
        σ.coaction (f w.val.1) = f.rTensor A (ρ.coaction w.val.1) := by
    rw [tensorGraph_iff, show (fst k V W).rTensor A (τ.coaction w.val) = ρ.coaction w.val.1 from
      DFunLike.congr_fun h₁ w.val,
      show (snd k V W).rTensor A (τ.coaction w.val) = σ.coaction w.val.2 from
        DFunLike.congr_fun h₂ w.val,
      (f.mem_graph_iff w.val).mp w.property]
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    let w : f.graph := ⟨(v, f v), (f.mem_graph_iff _).mpr rfl⟩
    exact ((graphCondition w).mp (h w)).symm
  · intro h w
    exact (graphCondition w).mpr (DFunLike.congr_fun h w.val.1).symm

private theorem differentiatedCoaction_natural {U : Type u} [AddCommGroup U] [Module k U]
    (A : HopfAlgebraCategory k) (ρ : RightComodule k A U) (σ : RightComodule k A V)
    (x : HopfTangentPoint A) (f : U →ₗ[k] V) (h : IsEquivariant A ρ σ f) (v : U) :
    f (differentiatedCoaction A ρ x v) = differentiatedCoaction A σ x (f v) := by
  simp only [differentiatedCoaction, evaluate, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← LinearMap.lTensor_comp_apply]
  rw [contractRight_natural]
  exact congrArg (fun z => TensorProduct.rid k V
    (((TrivSqZeroExt.sndHom k k).comp x.val.toLinearMap).lTensor V z)) (DFunLike.congr_fun h v)

theorem differentiationGraphCriterion : Specs.DifferentiationGraphCriterion.{u} := by
  intro k V W _ _ _ _ _ A ρ σ
  obtain ⟨τ, h₁, h₂⟩ := exists_directSumCoaction A ρ σ
  refine ⟨τ, h₁, h₂, isSubcomodule_graph_iff A ρ σ τ h₁ h₂, ?_⟩
  intro f x
  have graphCondition (w : f.graph) :
      differentiatedCoaction A τ x w.val ∈ f.graph ↔
        differentiatedCoaction A σ x (f w.val.1) = f (differentiatedCoaction A ρ x w.val.1) := by
    rw [f.mem_graph_iff]
    change snd k V W (differentiatedCoaction A τ x w.val) =
      f (fst k V W (differentiatedCoaction A τ x w.val)) ↔ _
    rw [differentiatedCoaction_natural A τ σ x _ h₂,
      differentiatedCoaction_natural A τ ρ x _ h₁]
    change (differentiatedCoaction A σ x w.val.2 = f (differentiatedCoaction A ρ x w.val.1)) ↔ _
    rw [(f.mem_graph_iff w.val).mp w.property]
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    let w : f.graph := ⟨(v, f v), (f.mem_graph_iff _).mpr rfl⟩
    exact ((graphCondition w).mp (h w)).symm
  · intro h w
    exact (graphCondition w).mpr (DFunLike.congr_fun h w.val.1).symm

theorem fullyFaithfulDifferentiation : Specs.FullyFaithfulDifferentiation.{u} := by
  intro k V W _ _ _ _ _ _ _ _ A _ _ ρ σ f
  obtain ⟨τ, _, _, hGroup, hLie⟩ := differentiationGraphCriterion A ρ σ
  rw [← hGroup f, lieStableGraphs A τ f]
  exact forall_congr' fun x => hLie f (tangentPointOfLie A x)

theorem fullyFaithfulDifferentiationOfPresentation :
    Specs.FullyFaithfulDifferentiationOfPresentation.{u} := by
  intro k V W _ _ _ _ _ _ _ _ G _ A e ρ σ f
  obtain ⟨τ, _, _, hGroup, hLie⟩ := differentiationGraphCriterion A ρ σ
  rw [← hGroup f, lieStableSubspacesOfPresentation G e τ f.graph]
  exact forall_congr' fun x => hLie f (tangentPointOfLie A (mapPointKernel e.inv x))

end
end LinearAlgebraicGroups
