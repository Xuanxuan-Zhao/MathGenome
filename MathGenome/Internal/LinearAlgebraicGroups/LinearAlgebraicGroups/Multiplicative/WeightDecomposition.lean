import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.WeightDecomposition
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.Noetherian.Basic
import Batteries.Tactic.OpenPrivate

open scoped DirectSum TensorProduct
open CategoryTheory TensorProduct

universe u

namespace LinearAlgebraicGroups.WeightDecomposition

noncomputable section

variable {k M V W : Type u} [Field k] [CommGroup M]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

local notation "A" => MonoidAlgebra k M
local notation "e" => MonoidAlgebra.of k M

theorem diagonalRepresentationComparison :
    Specs.WeightDecomposition.DiagonalRepresentationComparison.{u} := by
  intro k M V ι _ _ _ _ _ _ _ b L l D G
  have pointIso : convolutionPoints (Specs.DiagonalizableGroups.groupAlgebra k M) ≅
      (groupPointsFunctor k).obj D.val :=
    hopfSpecPointIso (Specs.DiagonalizableGroups.groupAlgebra k M)
  obtain ⟨E, hE⟩ := RationalRepresentations.representationCoactionComparison
    (Specs.DiagonalizableGroups.groupAlgebra k M) b G L pointIso l
  exact ⟨pointIso, E, hE⟩

section Projections

variable [DecidableEq M]

/-- Coordinates in the character basis in the right tensor factor. -/
private def tensorCoefficients : V ⊗[k] A ≃ₗ[k] M →₀ V :=
  (MonoidAlgebra.coeffLinearEquiv k).lTensor V ≪≫ₗ TensorProduct.finsuppScalarRight k k V M

@[simp] private theorem tensorCoefficients_tmul (v : V) (m : M) :
    tensorCoefficients (v ⊗ₜ[k] e m) = Finsupp.single m v := by
  ext n
  simp only [tensorCoefficients, LinearEquiv.trans_apply, LinearEquiv.lTensor_tmul,
    TensorProduct.finsuppScalarRight_apply_tmul_apply]
  change Finsupp.single m (1 : k) n • v = Finsupp.single m v n
  by_cases h : m = n <;> simp [h]

private theorem tensorCoefficients_symm_single (m : M) (v : V) :
    (tensorCoefficients (k := k) (M := M) (V := V)).symm (Finsupp.single m v) =
      v ⊗ₜ[k] e m := by
  rw [LinearEquiv.symm_apply_eq, tensorCoefficients_tmul]

/-- The linear projection onto a weight obtained by extracting its coaction coefficient. -/
private def weightProjection (ρ : RightComodule k A V) (m : M) : V →ₗ[k] V :=
  Finsupp.lapply m ∘ₗ tensorCoefficients.toLinearMap ∘ₗ ρ.coaction

private theorem coaction_sum (ρ : RightComodule k A V) (v : V) :
    ∃ s : Finset M, ρ.coaction v = ∑ m ∈ s, weightProjection ρ m v ⊗ₜ[k] e m ∧
      ∀ m ∉ s, weightProjection ρ m v = 0 := by
  let c := tensorCoefficients (ρ.coaction v)
  refine ⟨c.support, ?_, fun m hm ↦ Finsupp.notMem_support_iff.mp hm⟩
  calc
    ρ.coaction v = (tensorCoefficients (k := k)).symm c :=
      (tensorCoefficients.symm_apply_apply (ρ.coaction v)).symm
    _ = ∑ m ∈ c.support, c m ⊗ₜ[k] e m := by
      conv_lhs => rw [← Finsupp.sum_single c]
      simp only [Finsupp.sum, map_sum, tensorCoefficients_symm_single]

omit [DecidableEq M] in
private theorem comul_character (m : M) :
    Coalgebra.comul (R := k) (e m) = e m ⊗ₜ[k] e m :=
  (MonoidAlgebra.isGroupLikeElem_of (R := k) m).comul_eq_tmul_self

omit [DecidableEq M] in
private theorem counit_character (m : M) : Coalgebra.counit (R := k) (e m) = 1 :=
  (MonoidAlgebra.isGroupLikeElem_of (R := k) m).counit_eq_one

private theorem projection_mem (ρ : RightComodule k A V) (m : M) (v : V) :
    weightProjection ρ m v ∈ weightSpace ρ m := by
  apply mem_weightSpace.mpr
  obtain ⟨s, hs, hz⟩ := coaction_sum ρ v
  have h := congrArg (fun t ↦ tensorCoefficients
      ((TensorProduct.assoc k V A A).symm t) m) (ρ.coassoc v)
  simp only [LinearEquiv.symm_apply_apply, hs, map_sum, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, comul_character, TensorProduct.assoc_symm_tmul,
    tensorCoefficients_tmul, Finsupp.finsetSum_apply, Finsupp.single_apply] at h
  by_cases hm : m ∈ s
  · simpa [Finset.sum_ite_eq', hm] using h
  · simp [hz m hm]

private theorem projection_of_mem {ρ : RightComodule k A V} {n : M} {v : V}
    (hv : v ∈ weightSpace ρ n) (m : M) :
    weightProjection ρ m v = if n = m then v else 0 := by
  change tensorCoefficients (ρ.coaction v) m = _
  rw [mem_weightSpace.mp hv, tensorCoefficients_tmul, Finsupp.single_apply]

private theorem sum_projections (ρ : RightComodule k A V) (v : V) :
    ∃ s : Finset M, (∑ m ∈ s, weightProjection ρ m v) = v := by
  obtain ⟨s, hs, _⟩ := coaction_sum ρ v
  have h := ρ.counit v
  rw [hs] at h
  refine ⟨s, ?_⟩
  simpa only [map_sum, LinearMap.lTensor_tmul, counit_character, TensorProduct.rid_tmul,
    one_smul] using h

private theorem projection_comp_sum (ρ : RightComodule k A V) (m : M) :
    (weightProjection ρ m).comp (DirectSum.coeLinearMap (weightSpace ρ)) =
      (weightSpace ρ m).subtype.comp (DirectSum.component k M (weightSpace ρ ·) m) := by
  apply DirectSum.linearMap_ext
  intro n
  ext v
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, projection_of_mem v.property]
  by_cases h : n = m
  · subst n
    simp
  · rw [ite_eq_right h, DirectSum.component.of, dite_eq_right h]
    rfl

private theorem weight_isInternal (ρ : RightComodule k A V) :
    DirectSum.IsInternal (weightSpace ρ) := by
  change Function.Bijective (DirectSum.coeLinearMap (weightSpace ρ))
  constructor
  · intro a b hab
    apply DirectSum.ext
    intro m
    apply Subtype.ext
    have ha := DFunLike.congr_fun (projection_comp_sum ρ m) a
    have hb := DFunLike.congr_fun (projection_comp_sum ρ m) b
    exact ha.symm.trans ((congrArg (weightProjection ρ m) hab).trans hb)
  · intro v
    obtain ⟨s, hs⟩ := sum_projections ρ v
    refine ⟨∑ m ∈ s, DirectSum.lof k M (weightSpace ρ ·) m
      ⟨weightProjection ρ m v, projection_mem ρ m v⟩, ?_⟩
    simpa only [map_sum, DirectSum.coeLinearMap_lof] using hs

end Projections

theorem weightDecomposition : Specs.WeightDecomposition.InternalWeightSum.{u} := by
  classical
  intro k M V _ _ _ _ ρ
  exact weight_isInternal ρ

theorem finiteWeights : Specs.WeightDecomposition.FiniteWeights.{u} := by
  classical
  intro k M V _ _ _ _ _ ρ
  exact Submodule.finite_ne_bot_of_iSupIndep (weight_isInternal ρ).submodule_iSupIndep

theorem invariants : Specs.WeightDecomposition.Invariants.{u} := by
  intro k M V _ _ _ _ ρ
  ext v
  rw [mem_weightSpace]
  change ρ.coaction v - RationalRepresentations.trivialLinearMap _ v = 0 ↔ _
  rw [sub_eq_zero]
  rw [map_one (MonoidAlgebra.of k M)]
  rfl

theorem functoriality : Specs.WeightDecomposition.Functoriality.{u} := by
  classical
  intro k M V W _ _ _ _ _ _ ρ σ f hf
  have h (m : M) (v : weightSpace ρ m) : f v ∈ weightSpace σ m := by
    apply mem_weightSpace.mpr
    have hv := (mem_weightSpace.mp v.property)
    have he := DFunLike.congr_fun hf (v : V)
    change f.rTensor (MonoidAlgebra k M) (ρ.coaction v) = σ.coaction (f v) at he
    rw [hv, LinearMap.rTensor_tmul] at he
    exact he.symm
  let F (m : M) : weightSpace ρ m →ₗ[k] weightSpace σ m :=
    (f.comp (weightSpace ρ m).subtype).codRestrict (weightSpace σ m) (h m)
  refine ⟨F, fun _ _ ↦ rfl, ?_⟩
  apply DirectSum.linearMap_ext
  intro m
  ext v
  simp only [LinearMap.comp_apply, DirectSum.lmap_lof, DirectSum.coeLinearMap_lof]
  rfl

section TensorWeights

private theorem tensor_coaction_exists [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : RightComodule k A V) (σ : RightComodule k A W) :
    ∃ τ : RightComodule k A (V ⊗[k] W), τ.coaction = tensorCoactionMap ρ σ := by
  classical
  let B := Specs.DiagonalizableGroups.groupAlgebra k M
  let b := (Module.finBasis k V).reindex Equiv.ulift.symm
  let c := (Module.finBasis k W).reindex Equiv.ulift.symm
  obtain ⟨τ, hτ⟩ := RationalRepresentations.tensorProductComparison B b c ρ σ
  refine ⟨τ, (b.tensorProduct c).ext ?_⟩
  intro j
  rw [RationalRepresentations.coaction_apply_basis B (b.tensorProduct c) τ j]
  simp only [hτ, Module.Basis.tensorProduct_apply', tensorCoactionMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.map_tmul]
  rw [RationalRepresentations.coaction_apply_basis B b ρ j.1,
    RationalRepresentations.coaction_apply_basis B c σ j.2]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
    TensorProduct.tensorTensorTensorComm_tmul, LinearMap.lTensor_tmul, LinearMap.mul'_apply,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

private theorem tmul_mem_weight {ρ : RightComodule k A V} {σ : RightComodule k A W}
    {τ : RightComodule k A (V ⊗[k] W)} (hτ : τ.coaction = tensorCoactionMap ρ σ)
    {m n : M} {v : V} {w : W} (hv : v ∈ weightSpace ρ m) (hw : w ∈ weightSpace σ n) :
    v ⊗ₜ[k] w ∈ weightSpace τ (m * n) := by
  rw [mem_weightSpace, hτ]
  simp [tensorCoactionMap, mem_weightSpace.mp hv, mem_weightSpace.mp hw, map_mul]

theorem tensorWeights : Specs.WeightDecomposition.TensorWeights.{u} := by
  classical
  intro k M V W _ _ _ _ _ _ _ _ ρ σ
  obtain ⟨τ, hτ⟩ := tensor_coaction_exists ρ σ
  refine ⟨τ, hτ, fun m ↦ ?_⟩
  let S : Submodule k (V ⊗[k] W) :=
    ⨆ p : {p : M × M // p.1 * p.2 = m},
      LinearMap.range (TensorProduct.mapIncl (weightSpace ρ p.val.1) (weightSpace σ p.val.2))
  change weightSpace τ m = S
  apply le_antisymm
  · have h (t : V ⊗[k] W) : weightProjection τ m t ∈ S := by
      induction t using TensorProduct.inductionOn with
      | tmul v w =>
        obtain ⟨s, hs⟩ := sum_projections ρ v
        obtain ⟨r, hr⟩ := sum_projections σ w
        rw [← hs, ← hr, TensorProduct.sum_tmul]
        simp only [TensorProduct.tmul_sum, map_sum]
        refine S.sum_mem fun a _ ↦ S.sum_mem fun b _ ↦ ?_
        have ha := projection_mem ρ a v
        have hb := projection_mem σ b w
        rw [projection_of_mem (tmul_mem_weight hτ ha hb)]
        by_cases hab : a * b = m
        · rw [ite_eq_left hab]
          exact Submodule.mem_iSup_of_mem ⟨(a, b), hab⟩
            ⟨(⟨_, ha⟩ : weightSpace ρ a) ⊗ₜ[k] (⟨_, hb⟩ : weightSpace σ b), by
              simp only [TensorProduct.map_tmul, Submodule.subtype_apply]⟩
        · rw [ite_eq_right hab]
          exact S.zero_mem
      | add t s ht hs => rw [map_add]; exact S.add_mem ht hs
    intro t ht
    simpa [projection_of_mem ht] using h t
  · refine iSup_le fun ⟨⟨a, b⟩, hab⟩ ↦ ?_
    change LinearMap.range (TensorProduct.mapIncl (weightSpace ρ a) (weightSpace σ b)) ≤
      weightSpace τ m
    rw [TensorProduct.range_map_eq_span_tmul, Submodule.span_le]
    rintro _ ⟨v, w, rfl⟩
    rw [← hab]
    exact tmul_mem_weight hτ v.property w.property

end TensorWeights

section DualWeights

open private tensor_eq_sum_basis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

@[simp] private theorem evaluateDualTensor_tmul (f : Module.Dual k V) (a : A) (v : V) :
    evaluateDualTensor (f ⊗ₜ[k] a) v = f v • a := rfl

@[simp] private theorem evaluateVectorTensor_tmul (v : V) (a : A) (f : Module.Dual k V) :
    evaluateVectorTensor (v ⊗ₜ[k] a) f = f v • a := rfl

private theorem evaluateDualTensor_eq_coordinate {ι : Type u} [Finite ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (i : ι) (t : Module.Dual k V ⊗[k] A) :
    evaluateDualTensor t (b i) = RationalRepresentations.tensorCoordinate b.dualBasis i t := by
  induction t using TensorProduct.inductionOn with
  | tmul f a => simp [RationalRepresentations.tensorCoordinate, Module.Basis.coord_apply]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

private theorem evaluateVectorTensor_eq_coordinate {ι : Type u} [Finite ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (i : ι) (t : V ⊗[k] A) :
    evaluateVectorTensor t (b.dualBasis i) = RationalRepresentations.tensorCoordinate b i t := by
  induction t using TensorProduct.inductionOn with
  | tmul v a => simp [RationalRepresentations.tensorCoordinate]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

private theorem evaluateDualTensor_injective [FiniteDimensional k V] :
    Function.Injective (evaluateDualTensor (k := k) (M := M) (V := V)) := by
  classical
  let b : Module.Basis (ULift.{u} (Fin (Module.finrank k V))) k V :=
    (Module.finBasis k V).reindex Equiv.ulift.symm
  intro t s h
  rw [← tensor_eq_sum_basis b.dualBasis t, ← tensor_eq_sum_basis b.dualBasis s]
  apply Finset.sum_congr rfl
  intro i _
  rw [← evaluateDualTensor_eq_coordinate b i, ← evaluateDualTensor_eq_coordinate b i, h]

private theorem dual_coaction_exists [FiniteDimensional k V] (ρ : RightComodule k A V) :
    ∃ τ : RightComodule k A (Module.Dual k V),
      ∀ (f : Module.Dual k V) (v : V),
        evaluateDualTensor (τ.coaction f) v =
          HopfAlgebra.antipode k (evaluateVectorTensor (ρ.coaction v) f) := by
  classical
  let B := Specs.DiagonalizableGroups.groupAlgebra k M
  let b := (Module.finBasis k V).reindex Equiv.ulift.symm
  obtain ⟨τ, hτ⟩ := RationalRepresentations.dualComparison B b ρ
  refine ⟨τ, fun f v ↦ ?_⟩
  have h : evaluateDualTensor.comp τ.coaction =
      ((evaluateVectorTensor.comp ρ.coaction).flip).compr₂ₛₗ (HopfAlgebra.antipode k) := by
    apply b.dualBasis.ext
    intro j
    apply b.ext
    intro i
    change evaluateDualTensor (τ.coaction (b.dualBasis j)) (b i) =
      HopfAlgebra.antipode k (evaluateVectorTensor (ρ.coaction (b i)) (b.dualBasis j))
    rw [evaluateDualTensor_eq_coordinate b i, evaluateVectorTensor_eq_coordinate b j]
    exact hτ i j
  exact DFunLike.congr_fun (DFunLike.congr_fun h f) v

private theorem linearMap_ext_weights [DecidableEq M] {X : Type u}
    [AddCommGroup X] [Module k X] (ρ : RightComodule k A V) {f g : V →ₗ[k] X}
    (h : ∀ n (v : weightSpace ρ n), f v = g v) : f = g := by
  ext v
  obtain ⟨s, hs⟩ := sum_projections ρ v
  have he : f (∑ n ∈ s, weightProjection ρ n v) = g (∑ n ∈ s, weightProjection ρ n v) := by
    simp only [map_sum]
    exact Finset.sum_congr rfl fun n _ ↦ h n ⟨_, projection_mem ρ n v⟩
  rwa [hs] at he

private theorem mem_dualWeight_iff [DecidableEq M] [FiniteDimensional k V]
    {ρ : RightComodule k A V} {τ : RightComodule k A (Module.Dual k V)}
    (hτ : ∀ (f : Module.Dual k V) (v : V),
      evaluateDualTensor (τ.coaction f) v =
        HopfAlgebra.antipode k (evaluateVectorTensor (ρ.coaction v) f))
    (m : M) (f : Module.Dual k V) :
    f ∈ weightSpace τ m ↔ ∀ n ≠ m⁻¹, ∀ v : weightSpace ρ n, f v = 0 := by
  have eval_weight (n : M) (v : weightSpace ρ n) :
      evaluateDualTensor (τ.coaction f) (v : V) = f v • e n⁻¹ := by
    rw [hτ, mem_weightSpace.mp v.property, evaluateVectorTensor_tmul, map_smul]
    change f v • HopfAlgebra.antipode k (MonoidAlgebra.single n 1) = _
    simp
  constructor
  · intro hf n hn v
    have h := eval_weight n v
    rw [mem_weightSpace.mp hf, evaluateDualTensor_tmul] at h
    have hnm : n⁻¹ ≠ m := fun he ↦ hn (inv_eq_iff_eq_inv.mp he)
    have hc := congrArg (fun a : A ↦ a.coeff m) h
    change (f v • (MonoidAlgebra.single m (1 : k))).coeff m =
      (f v • (MonoidAlgebra.single n⁻¹ (1 : k))).coeff m at hc
    simpa [MonoidAlgebra.smul_single', MonoidAlgebra.coeff_single, hnm, eq_comm] using hc
  · intro hf
    apply mem_weightSpace.mpr
    apply evaluateDualTensor_injective
    apply linearMap_ext_weights ρ
    intro n v
    rw [eval_weight, evaluateDualTensor_tmul]
    by_cases h : n = m⁻¹
    · simp [h]
    · simp [hf n h v]

theorem dualWeights : Specs.WeightDecomposition.DualWeights.{u} := by
  classical
  intro k M V _ _ _ _ _ ρ
  obtain ⟨τ, hτ⟩ := dual_coaction_exists ρ
  refine ⟨τ, hτ, fun m ↦ ?_⟩
  let P : V →ₗ[k] weightSpace ρ m⁻¹ :=
    (weightProjection ρ m⁻¹).codRestrict _ (projection_mem ρ m⁻¹)
  let F : weightSpace τ m →ₗ[k] Module.Dual k (weightSpace ρ m⁻¹) :=
    ((weightSpace ρ m⁻¹).subtype.dualMap).comp (weightSpace τ m).subtype
  let G : Module.Dual k (weightSpace ρ m⁻¹) →ₗ[k] weightSpace τ m :=
    P.dualMap.codRestrict _ fun f ↦ (mem_dualWeight_iff hτ m _).mpr fun n hn v ↦ by
      have h : P v = 0 := Subtype.ext (by simp [P, projection_of_mem v.property, hn])
      change f (P v) = 0
      rw [h, map_zero]
  refine ⟨LinearEquiv.ofLinearMap F G ?_ ?_, fun _ _ ↦ rfl⟩
  · ext f v
    change f (P v) = f v
    have h : P v = v := Subtype.ext (by simp [P, projection_of_mem v.property])
    rw [h]
  · ext f : 1
    apply Subtype.ext
    change (f.val.comp (weightSpace ρ m⁻¹).subtype).comp P = f.val
    apply linearMap_ext_weights ρ
    intro n v
    change f.val (weightProjection ρ m⁻¹ v) = f.val v
    by_cases h : n = m⁻¹
    · simp [projection_of_mem v.property, h]
    · simp [projection_of_mem v.property, h, (mem_dualWeight_iff hτ m _).mp f.property n h v]

end DualWeights

end
end LinearAlgebraicGroups.WeightDecomposition
