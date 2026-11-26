import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ComoduleFiniteness
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic

open scoped TensorProduct BigOperators

namespace LinearAlgebraicGroups.RightComodule

universe u v w

variable {k : Type u} {C : Type v} {V : Type w}
    [Field k] [AddCommGroup C] [Module k C]
    [AddCommGroup V] [Module k V]

private def contractRight (f : C →ₗ[k] k) (X : Type*) [AddCommGroup X] [Module k X] :
    X ⊗[k] C →ₗ[k] X :=
  (TensorProduct.rid k X).toLinearMap.comp (f.lTensor X)

@[simp]
private theorem contractRight_tmul (f : C →ₗ[k] k) (x : V) (c : C) :
    contractRight f V (x ⊗ₜ[k] c) = f c • x := by
  simp [contractRight]

private theorem map_contractRight {X Y : Type*} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] (f : C →ₗ[k] k) (g : X →ₗ[k] Y) (t : X ⊗[k] C) :
    g (contractRight f X t) = contractRight f Y (g.rTensor C t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x c => simp
  | add x y hx hy => simp [hx, hy]

private theorem assoc_contractRight (f : C →ₗ[k] k) (t : (V ⊗[k] C) ⊗[k] C) :
    contractRight f (V ⊗[k] C) t =
      (contractRight f C).lTensor V (TensorProduct.assoc k V C C t) := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul x c =>
    rw [contractRight_tmul]
    induction x using TensorProduct.inductionOn with
    | tmul x d => simp [TensorProduct.tmul_smul]
    | add x y hx hy => simp [TensorProduct.add_tmul, smul_add, hx, hy]

variable [Coalgebra k C]

private theorem coaction_contractRight (ρ : RightComodule k C V) (f : C →ₗ[k] k) (x : V) :
    ρ.coaction (contractRight f V (ρ.coaction x)) =
      (contractRight f C).lTensor V ((Coalgebra.comul (R := k) (A := C)).lTensor V
        (ρ.coaction x)) := by
  rw [map_contractRight, assoc_contractRight, ρ.coassoc]

/-- The range condition is equivalent to a compatible right coaction on the subspace. -/
theorem isSubcomodule_iff_exists_coaction (ρ : RightComodule k C V) (W : Submodule k V) :
    ρ.IsSubcomodule W ↔ ∃ σ : RightComodule k C W,
      (W.subtype.rTensor C).comp σ.coaction = ρ.coaction.comp W.subtype := by
  constructor
  · intro hW
    let i := W.subtype
    have hi : Function.Injective (i.rTensor C) :=
      Module.Flat.rTensor_preserves_injective_linearMap i W.injective_subtype
    let σ := LinearMap.codRestrictOfInjective (ρ.coaction.comp i) (i.rTensor C) hi hW
    have hσ : (i.rTensor C).comp σ = ρ.coaction.comp i :=
      LinearMap.codRestrictOfInjective_comp _ _ _ _
    have hσ_apply (x : W) : i.rTensor C (σ x) = ρ.coaction (i x) :=
      DFunLike.congr_fun hσ x
    refine ⟨⟨σ, ?_, ?_⟩, hσ⟩
    · intro x
      let Δ := Coalgebra.comul (R := k) (A := C)
      apply Module.Flat.rTensor_preserves_injective_linearMap (M := C ⊗[k] C)
        i W.injective_subtype
      have hassoc (t : (W ⊗[k] C) ⊗[k] C) :
          i.rTensor (C ⊗[k] C) (TensorProduct.assoc k W C C t) =
            TensorProduct.assoc k V C C ((i.rTensor C).rTensor C t) := by
        simpa [LinearMap.rTensor] using
          TensorProduct.map_map_assoc i (LinearMap.id : C →ₗ[k] C) LinearMap.id t
      have hcomul (t : W ⊗[k] C) :
          i.rTensor (C ⊗[k] C) (Δ.lTensor W t) = Δ.lTensor V (i.rTensor C t) := by
        exact (DFunLike.congr_fun (LinearMap.rTensor_comp_lTensor W i Δ) t).trans
          (DFunLike.congr_fun (LinearMap.lTensor_comp_rTensor W i Δ) t).symm
      calc
        _ = TensorProduct.assoc k V C C ((i.rTensor C).rTensor C (σ.rTensor C (σ x))) :=
          hassoc _
        _ = TensorProduct.assoc k V C C (ρ.coaction.rTensor C (ρ.coaction (i x))) := by
          rw [← LinearMap.rTensor_comp_apply, hσ, LinearMap.rTensor_comp_apply, hσ_apply]
        _ = Δ.lTensor V (ρ.coaction (i x)) := ρ.coassoc _
        _ = _ := by rw [hcomul, hσ_apply]
    · intro x
      apply W.injective_subtype
      change i (contractRight Coalgebra.counit W (σ x)) = i x
      rw [map_contractRight, hσ_apply]
      exact ρ.counit _
  · rintro ⟨σ, hσ⟩ x
    exact ⟨σ.coaction x, DFunLike.congr_fun hσ x⟩

/-- A sum of subcomodules is a subcomodule. -/
theorem IsSubcomodule.sup {ρ : RightComodule k C V} {W U : Submodule k V}
    (hW : ρ.IsSubcomodule W) (hU : ρ.IsSubcomodule U) : ρ.IsSubcomodule (W ⊔ U) := by
  rintro ⟨x, hx⟩
  obtain ⟨y, z, rfl⟩ := Submodule.mem_sup'.mp hx
  obtain ⟨a, ha⟩ := hW y
  obtain ⟨b, hb⟩ := hU z
  refine ⟨(Submodule.inclusion (le_sup_left : W ≤ W ⊔ U)).rTensor C a +
    (Submodule.inclusion (le_sup_right : U ≤ W ⊔ U)).rTensor C b, ?_⟩
  change _ = ρ.coaction ((y : V) + (z : V))
  rw [map_add, ← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply, map_add]
  simpa only [Submodule.subtype_comp_inclusion] using congrArg₂ (· + ·) ha hb

/-- Each vector lies in a finite-dimensional subcomodule. -/
theorem exists_finiteSubcomodule (ρ : RightComodule k C V) (x : V) :
    ∃ W : ρ.FiniteSubcomodule, x ∈ W.val := by
  classical
  let basis := Module.Free.chooseBasis k C
  let coeff := TensorProduct.equivFinsuppOfBasisRight basis (ρ.coaction x)
  let W := Submodule.span k (coeff '' (coeff.support : Set _))
  have coeff_mem (i) (hi : i ∈ coeff.support) : coeff i ∈ W :=
    Submodule.subset_span ⟨i, hi, rfl⟩
  have expansion : ∑ i ∈ coeff.support, coeff i ⊗ₜ[k] basis i = ρ.coaction x := by
    simpa only [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum] using
      (TensorProduct.equivFinsuppOfBasisRight basis).symm_apply_apply (ρ.coaction x)
  have stable : ρ.IsSubcomodule W := by
    suffices W ≤ (LinearMap.range (W.subtype.rTensor C)).comap ρ.coaction by
      exact fun z ↦ this z.property
    apply Submodule.span_le.mpr
    rintro _ ⟨i, _, rfl⟩
    change ρ.coaction (coeff i) ∈ LinearMap.range (W.subtype.rTensor C)
    have extract :
        coeff i = contractRight (basis.coord i) V (ρ.coaction x) :=
      TensorProduct.equivFinsuppOfBasisRight_apply basis _ i
    rw [extract, coaction_contractRight, ← expansion, map_sum, map_sum]
    apply Submodule.sum_mem
    intro j hj
    rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
    exact ⟨(⟨coeff j, coeff_mem j hj⟩ : W) ⊗ₜ[k] _, rfl⟩
  have finite : FiniteDimensional k W := FiniteDimensional.span_of_finite k
    (coeff.support.finite_toSet.image coeff)
  refine ⟨⟨W, stable, finite⟩, ?_⟩
  have hx : ∑ i ∈ coeff.support, Coalgebra.counit (R := k) (basis i) • coeff i = x := by
    calc
      _ = contractRight Coalgebra.counit V (ρ.coaction x) := by
        rw [← expansion, map_sum]
        simp only [contractRight_tmul]
      _ = x := ρ.counit x
  rw [← hx]
  exact W.sum_mem fun i hi ↦ W.smul_mem _ (coeff_mem i hi)

/-- The finite-dimensional subcomodules are directed under inclusion. -/
theorem directed_finiteSubcomodules (ρ : RightComodule k C V) :
    Directed (· ≤ ·) (fun W : ρ.FiniteSubcomodule ↦ W.val) := by
  intro W U
  let : FiniteDimensional k W.val := W.property.2
  let : FiniteDimensional k U.val := U.property.2
  exact ⟨⟨W.val ⊔ U.val, W.property.1.sup U.property.1, inferInstance⟩,
    le_sup_left, le_sup_right⟩

/-- The finite-dimensional subcomodules cover the underlying vector space. -/
theorem iUnion_finiteSubcomodules (ρ : RightComodule k C V) :
    (⋃ W : ρ.FiniteSubcomodule, (W.val : Set V)) = Set.univ := by
  ext x
  simpa only [Set.mem_iUnion, SetLike.mem_coe, Set.mem_univ, iff_true] using ρ.exists_finiteSubcomodule x

/-- Every finite set of vectors is contained in one finite-dimensional subcomodule. -/
theorem exists_finiteSubcomodule_containing (ρ : RightComodule k C V) (s : Set V)
    (hs : s.Finite) : ∃ W : ρ.FiniteSubcomodule, s ⊆ (W.val : Set V) := by
  induction s, hs using Set.Finite.induction_on with
  | empty =>
    obtain ⟨W, _⟩ := ρ.exists_finiteSubcomodule 0
    exact ⟨W, Set.empty_subset _⟩
  | @insert x s _ _ ih =>
    obtain ⟨W, hW⟩ := ih
    obtain ⟨U, hU⟩ := ρ.exists_finiteSubcomodule x
    obtain ⟨T, hWT, hUT⟩ := ρ.directed_finiteSubcomodules W U
    exact ⟨T, Set.insert_subset (hUT hU) (fun _ hy ↦ hWT (hW hy))⟩

/-- A family of vectors with a finite index type lies in one finite-dimensional subcomodule. -/
theorem exists_finiteSubcomodule_containing_range (ρ : RightComodule k C V)
    {ι : Type*} [Finite ι] (f : ι → V) :
    ∃ W : ρ.FiniteSubcomodule, ∀ i, f i ∈ W.val := by
  obtain ⟨W, hW⟩ := ρ.exists_finiteSubcomodule_containing (Set.range f) (Set.finite_range f)
  exact ⟨W, fun i ↦ hW (Set.mem_range_self i)⟩

end LinearAlgebraicGroups.RightComodule
