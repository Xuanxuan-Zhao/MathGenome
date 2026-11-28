import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.TorusWeights
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.WeightDecomposition
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import Mathlib.LinearAlgebra.DirectSum.Finite

open CategoryTheory LinearAlgebraicGroups Opposite AlgebraicGeometry
open LinearAlgebraicGroups.WeightDecomposition (weightSpace mem_weightSpace tensorCoactionMap)
open RepTheorySurvey.Invariants.Specs.TorusWeights
open scoped DirectSum TensorProduct

universe u

namespace RepTheorySurvey.Invariants.TorusWeights

noncomputable section

variable {k M V W : Type u} [Field k] [CommGroup M]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

local notation "H" => coordinates k M
local notation "e" => MonoidAlgebra.of k M

theorem characterBasis : CharacterBasis.{u} := by
  intro k M _ _
  obtain ⟨b, hb, h⟩ :=
    LinearAlgebraicGroups.DiagonalizableGroups.groupAlgebraBasisAndHopfStructure k M
  refine ⟨b, hb, fun m ↦ ⟨(h m).1, (h m).2.1⟩, fun m n ↦ ?_⟩
  simp only [hb, ← MonoidAlgebra.of_apply, map_mul]

open LinearAlgebraicGroups.Specs.DiagonalizableGroups (diagonalGroup)
open LinearAlgebraicGroups.Specs.StandardGroups (multiplicativePowerGroup)

theorem splitTorus : SplitTorus.{u} := by
  intro k M ι _ _ _ lattice
  let : Group.FG M := Group.fg_of_surjective (f := lattice.symm.toMonoidHom) lattice.symm.surjective
  obtain ⟨iso⟩ := LinearAlgebraicGroups.DiagonalizableGroups.diagonalIntegerPowers k ι
  let α : coordinates k M ≅ coordinates k (Multiplicative (ι → ℤ)) :=
    CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k lattice)
  let β : (diagonalGroup k M).val ≅ (diagonalGroup k (Multiplicative (ι → ℤ))).val :=
    (hopfSpec (CommRingCat.of k)).mapIso α.op.symm
  exact ⟨inferInstance, ⟨β ≪≫ iso⟩⟩

theorem representationComparison : RepresentationComparison.{u} :=
  LinearAlgebraicGroups.WeightDecomposition.diagonalRepresentationComparison

theorem splitRepresentationComparison : SplitRepresentationComparison.{u} := by
  intro k M ι V J _ _ _ _ _ _ _ lattice b L l D G
  obtain ⟨_, ⟨s⟩⟩ := splitTorus k M ι lattice
  let points := hopfSpecPointIso (coordinates k M) ≪≫ (groupPointsFunctor k).mapIso s
  obtain ⟨E, hE⟩ := RationalRepresentations.representationCoactionComparison
    (coordinates k M) b G L points l
  exact ⟨points, E, hE⟩

theorem equivarianceOnPoints : EquivarianceOnPoints.{u} :=
  fun ρ σ f ↦ RationalRepresentations.equivariantMaps _ ρ σ f

theorem weightDecomposition : InternalWeightSum.{u} :=
  LinearAlgebraicGroups.WeightDecomposition.weightDecomposition

theorem finiteWeights : FiniteWeights.{u} :=
  LinearAlgebraicGroups.WeightDecomposition.finiteWeights

theorem invariantWeight : InvariantWeight.{u} :=
  LinearAlgebraicGroups.WeightDecomposition.invariants

/-- The canonical linear isomorphism from the sum of the weight spaces. -/
def weightSum (ρ : RightComodule k H V) : (⨁ m, weightSpace ρ m) ≃ₗ[k] V := by
  classical
  exact LinearEquiv.ofBijective (DirectSum.coeLinearMap (weightSpace ρ)) (weightDecomposition ρ)

@[simp]
theorem weightSum_lof [DecidableEq M] (ρ : RightComodule k H V) (m : M) (x : weightSpace ρ m) :
    weightSum ρ (DirectSum.lof k M _ m x) = x := by
  classical
  exact DirectSum.coeLinearMap_lof _ _ _

private theorem linearMap_ext_weights {X : Type u} [AddCommGroup X] [Module k X]
    (ρ : RightComodule k H V) {f g : V →ₗ[k] X}
    (h : ∀ m (x : weightSpace ρ m), f x = g x) : f = g := by
  classical
  have he : f.comp (weightSum ρ).toLinearMap = g.comp (weightSum ρ).toLinearMap := by
    apply DirectSum.linearMap_ext
    intro m
    ext x
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, weightSum_lof] using h m x
  ext x
  obtain ⟨y, rfl⟩ := (weightSum ρ).surjective x
  exact DFunLike.congr_fun he y

theorem degreePreserving : DegreePreserving.{u} := by
  intro k M V W _ _ _ _ _ _ ρ σ f
  constructor
  · intro hf
    obtain ⟨F, hF, _⟩ :=
      LinearAlgebraicGroups.WeightDecomposition.functoriality ρ σ f hf
    intro m x hx
    change f x ∈ weightSpace σ m
    rw [← hF m ⟨x, hx⟩]
    exact (F m ⟨x, hx⟩).property
  · intro h
    unfold RepTheorySurvey.Invariants.Specs.isComoduleMap
    apply linearMap_ext_weights ρ
    intro m x
    simp only [LinearMap.comp_apply, mem_weightSpace.mp x.property, LinearMap.rTensor_tmul,
      mem_weightSpace.mp (h m x.property)]

open scoped Classical in
@[simp]
theorem gradedCoactionMap_lof (X : M → ModuleCat.{u} k)
    (m : M) (x : X m) :
    gradedCoactionMap X (DirectSum.lof k M _ m x) =
      DirectSum.lof k M (fun j ↦ X j) m x ⊗ₜ[k] e m := by
  classical
  unfold gradedCoactionMap
  rw [DirectSum.toModule_lof]
  rfl

/-- Each homogeneous summand coacts through its designated character. -/
def gradedCoaction (X : M → ModuleCat.{u} k) :
    RightComodule k H (⨁ m, X m) := by
  classical
  let f := gradedCoactionMap X
  refine { coaction := f, coassoc := ?_, counit := ?_ }
  · have he : (TensorProduct.assoc k _ H H).toLinearMap.comp ((f.rTensor H).comp f) =
        (Coalgebra.comul (R := k) (A := H)).lTensor (⨁ m, X m) ∘ₗ f := by
      apply DirectSum.linearMap_ext
      intro m
      apply LinearMap.ext
      intro x
      let z := DirectSum.lof k M (fun j ↦ X j) m x
      have hz : f z = z ⊗ₜ[k] e m := gradedCoactionMap_lof X m x
      change TensorProduct.assoc k _ H H (f.rTensor H (f z)) =
        (Coalgebra.comul (R := k) (A := H)).lTensor (⨁ m, X m) (f z)
      rw [hz, LinearMap.rTensor_tmul, hz, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul]
      exact congrArg (fun a : H ⊗[k] H ↦ z ⊗ₜ[k] a)
        (MonoidAlgebra.isGroupLikeElem_of (R := k) m).comul_eq_tmul_self.symm
    exact DFunLike.congr_fun he
  · have he : (TensorProduct.rid k _).toLinearMap.comp
        (((Coalgebra.counit (R := k) (A := H)).lTensor (⨁ m, X m)).comp f) =
        LinearMap.id := by
      apply DirectSum.linearMap_ext
      intro m
      apply LinearMap.ext
      intro x
      let z := DirectSum.lof k M (fun j ↦ X j) m x
      have hz : f z = z ⊗ₜ[k] e m := gradedCoactionMap_lof X m x
      change TensorProduct.rid k _ ((Coalgebra.counit (R := k) (A := H)).lTensor
        (⨁ m, X m) (f z)) = z
      rw [hz, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
        (MonoidAlgebra.isGroupLikeElem_of (R := k) m).counit_eq_one, one_smul]
    exact DFunLike.congr_fun he

theorem gradedCoaction_exists : GradedCoaction.{u} :=
  fun X ↦ ⟨gradedCoaction X, rfl⟩

open scoped Classical in
@[simp]
theorem gradedCoaction_lof (X : M → ModuleCat.{u} k)
    (m : M) (x : X m) :
    (gradedCoaction X).coaction (DirectSum.lof k M _ m x) =
      DirectSum.lof k M (fun j ↦ X j) m x ⊗ₜ[k] e m :=
  gradedCoactionMap_lof X m x

/-- Restrict a degree-preserving map to its weight spaces. -/
def weightMap {ρ : RightComodule k H V} {σ : RightComodule k H W}
    (f : V →ₗ[k] W) (hf : Specs.isComoduleMap ρ σ f) (m : M) :
    weightSpace ρ m →ₗ[k] weightSpace σ m :=
  (f.comp (weightSpace ρ m).subtype).codRestrict _ (fun x ↦ (degreePreserving ρ σ f).mp hf m x.property)

private theorem gradedSumFinite (X : FiniteGrading k M) : FiniteDimensional k (⨁ m, X.piece m) := by
  classical
  let S : Set M := {m | ∃ x : X.piece m, x ≠ 0}
  let : Fintype S := X.finiteSupport.fintype
  let f : (⨁ m : S, X.piece m.val) →ₗ[k] (⨁ m, X.piece m) :=
    DirectSum.toModule k S _ (fun m ↦ DirectSum.lof k M (fun n ↦ X.piece n) m.val)
  apply Module.Finite.of_surjective f
  rw [← LinearMap.range_eq_top, eq_top_iff]
  suffices h : ∀ x, x ∈ LinearMap.range f from fun x _ ↦ h x
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | of m x =>
    by_cases hx : x = 0
    · simp [hx]
    · exact ⟨DirectSum.lof k S (fun n ↦ X.piece n.val) ⟨m, ⟨x, hx⟩⟩ x,
        DirectSum.toModule_lof _ _ _⟩

/-- The weights of the homogeneous coaction are exactly the original pieces. -/
def gradedWeight (X : M → ModuleCat.{u} k) (m : M) :
    X m ≃ₗ[k] weightSpace (gradedCoaction X) m := by
  classical
  let i (n : M) : X n →ₗ[k] weightSpace (gradedCoaction X) n :=
    (DirectSum.lof k M (fun j ↦ X j) n).codRestrict _ (fun x ↦
      mem_weightSpace.mpr (gradedCoaction_lof X n x))
  have h : (weightSum (gradedCoaction X)).toLinearMap.comp (DirectSum.lmap i) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, DirectSum.lmap_lof, LinearEquiv.coe_coe, weightSum_lof,
      LinearMap.id_coe, id_eq]
    rfl
  refine LinearEquiv.ofBijective (i m) ⟨?_, ?_⟩
  · intro x y hxy
    apply DirectSum.of_injective (i := m)
    exact congrArg Subtype.val hxy
  · apply (DirectSum.lmap_surjective i).mp _ m
    intro y
    refine ⟨weightSum (gradedCoaction X) y, (weightSum (gradedCoaction X)).injective ?_⟩
    exact DFunLike.congr_fun h _

open scoped Classical in
@[simp]
theorem gradedWeight_apply (X : M → ModuleCat.{u} k) (m : M) (x : X m) :
    (gradedWeight X m x : ⨁ j, X j) = DirectSum.lof k M _ m x := rfl

/-- The finite-dimensional weight functor. -/
def weightFunctor (k M : Type u) [Field k] [CommGroup M] :
    FiniteComodule k M ⥤ FiniteGrading k M where
  obj X :=
    { piece := fun m ↦ ModuleCat.of k (weightSpace X.coaction m)
      finiteDimensional := fun m ↦ inferInstance
      finiteSupport := (finiteWeights X.coaction).subset (by
        rintro m ⟨x, hx⟩ h
        exact hx (Subtype.ext (by simpa [h] using x.property))) }
  map f := weightMap f.val f.property

/-- The functor equipping the direct sum of a finite grading with its coaction. -/
def gradedFunctor (k M : Type u) [Field k] [CommGroup M] :
    FiniteGrading k M ⥤ FiniteComodule k M := by
  classical
  refine
    { obj := fun X ↦ ⟨ModuleCat.of k (⨁ m, X.piece m), gradedSumFinite X, gradedCoaction X.piece⟩
      map := fun f ↦ ⟨DirectSum.lmap f, ?_⟩
      map_id := ?_
      map_comp := ?_ }
  · rename_i X Y
    unfold Specs.isComoduleMap
    apply DirectSum.linearMap_ext
    intro m
    apply LinearMap.ext
    intro x
    let z := DirectSum.lof k M (fun j ↦ X.piece j) m x
    change (DirectSum.lmap f).rTensor (coordinates k M) ((gradedCoaction X.piece).coaction z) =
      (gradedCoaction Y.piece).coaction (DirectSum.lmap f z)
    rw [show (gradedCoaction X.piece).coaction z = z ⊗ₜ[k] MonoidAlgebra.of k M m from gradedCoaction_lof _ _ _,
      LinearMap.rTensor_tmul, show DirectSum.lmap f z = DirectSum.lof k M _ m (f m x) from
        DirectSum.lmap_lof f m x, gradedCoaction_lof]
  · intro X
    apply Subtype.ext
    exact DirectSum.lmap_id
  · intro X Y Z f g
    apply Subtype.ext
    exact DirectSum.lmap_comp f g

private theorem comoduleMap_symm {ρ : RightComodule k H V} {σ : RightComodule k H W}
    (E : V ≃ₗ[k] W) (hf : Specs.isComoduleMap ρ σ E.toLinearMap) :
    Specs.isComoduleMap σ ρ E.symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  apply (E.rTensor H).injective
  change E.rTensor H ((E.rTensor H).symm (σ.coaction x)) =
    E.rTensor H (ρ.coaction (E.symm x))
  have h := DFunLike.congr_fun hf (E.symm x)
  change E.rTensor H (ρ.coaction (E.symm x)) = σ.coaction (E (E.symm x)) at h
  rw [E.apply_symm_apply] at h
  rw [LinearEquiv.apply_symm_apply, h]

/-- The canonical weight sum intertwines the homogeneous coaction and the original coaction. -/
theorem weightSum_isComoduleMap (ρ : RightComodule k H V) :
    Specs.isComoduleMap (gradedCoaction (fun m ↦ ModuleCat.of k (weightSpace ρ m))) ρ
      (weightSum ρ).toLinearMap := by
  classical
  apply LinearMap.ext
  intro x
  have h : (weightSum ρ).toLinearMap.rTensor H ∘ₗ
      (gradedCoaction (fun m ↦ ModuleCat.of k (weightSpace ρ m))).coaction =
      ρ.coaction.comp (weightSum ρ).toLinearMap := by
    apply DirectSum.linearMap_ext
    intro m
    apply LinearMap.ext
    intro v
    let z := DirectSum.lof k M (fun j ↦ weightSpace ρ j) m v
    change (weightSum ρ).toLinearMap.rTensor H
      ((gradedCoaction (fun j ↦ ModuleCat.of k (weightSpace ρ j))).coaction z) =
      ρ.coaction (weightSum ρ z)
    rw [show (gradedCoaction (fun j ↦ ModuleCat.of k (weightSpace ρ j))).coaction z =
      z ⊗ₜ[k] e m from gradedCoaction_lof _ _ _, LinearMap.rTensor_tmul]
    change (weightSum ρ z) ⊗ₜ[k] e m = ρ.coaction (weightSum ρ z)
    rw [show weightSum ρ z = v from weightSum_lof _ _ _]
    exact (mem_weightSpace.mp v.property).symm
  exact DFunLike.congr_fun h x

/-- The weight inclusions give a natural isomorphism of the underlying vector spaces. -/
def weightSumIso (k M : Type u) [Field k] [CommGroup M] :
    weightFunctor k M ⋙ sumGrading ≅ forgetComodule := by
  classical
  refine NatIso.ofComponents (fun X ↦ (weightSum X.coaction).toModuleIso) ?_
  intro X Y f
  apply ModuleCat.hom_ext
  obtain ⟨F, hF, hNat⟩ :=
    LinearAlgebraicGroups.WeightDecomposition.functoriality X.coaction Y.coaction f.val f.property
  have h : F = weightMap f.val f.property := by
    funext m
    apply LinearMap.ext
    intro v
    exact Subtype.ext (hF m v)
  subst F
  exact hNat

private def sumComoduleIso (k M : Type u) [Field k] [CommGroup M] :
    weightFunctor k M ⋙ gradedFunctor k M ≅ 𝟭 (FiniteComodule k M) := by
  classical
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · let L := weightSum X.coaction
    have hL := weightSum_isComoduleMap X.coaction
    exact
      { hom := ⟨L.toLinearMap, hL⟩
        inv := ⟨L.symm.toLinearMap, comoduleMap_symm L hL⟩
        hom_inv_id := Subtype.ext (LinearMap.ext L.left_inv)
        inv_hom_id := Subtype.ext (LinearMap.ext L.right_inv) }
  · intro X Y f
    apply Subtype.ext
    exact congrArg ModuleCat.Hom.hom ((weightSumIso k M).hom.naturality f)

private def gradingWeightIso (k M : Type u) [Field k] [CommGroup M] :
    𝟭 (FiniteGrading k M) ≅ gradedFunctor k M ⋙ weightFunctor k M := by
  classical
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · exact
      { hom := fun m ↦ (gradedWeight X.piece m).toLinearMap
        inv := fun m ↦ (gradedWeight X.piece m).symm.toLinearMap
        hom_inv_id := by
          funext m
          exact LinearMap.ext (gradedWeight X.piece m).left_inv
        inv_hom_id := by
          funext m
          exact LinearMap.ext (gradedWeight X.piece m).right_inv }
  · intro X Y f
    funext m
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (gradedWeight Y.piece m (f m v) : ⨁ j, Y.piece j) =
      DirectSum.lmap f (gradedWeight X.piece m v : ⨁ j, X.piece j)
    rw [gradedWeight_apply, gradedWeight_apply, DirectSum.lmap_lof]

/-- Finite-dimensional torus comodules and finite gradings are equivalent categories. -/
def gradedEquivalence (k M : Type u) [Field k] [CommGroup M] :
    FiniteComodule k M ≌ FiniteGrading k M :=
  CategoryTheory.Equivalence.mk (weightFunctor k M) (gradedFunctor k M)
    (sumComoduleIso k M).symm (gradingWeightIso k M).symm

theorem gradedEquivalence_spec : GradedEquivalence.{u} := by
  classical
  intro k M _ _
  refine ⟨gradedEquivalence k M, fun _ _ ↦ rfl, weightSumIso k M,
    Iso.refl _, ?_, ?_, ?_⟩
  · intros
    rfl
  · intro X m x
    exact weightSum_lof _ _ _
  · intro X m x
    exact gradedCoaction_lof _ _ _

/-- The linear map extracting the weight component in the canonical direct sum. -/
def weightComponent (ρ : RightComodule k H V) (m : M) : V →ₗ[k] weightSpace ρ m := by
  classical
  exact (DirectSum.component k M (fun n ↦ weightSpace ρ n) m).comp (weightSum ρ).symm.toLinearMap

open scoped Classical in
private theorem weightComponent_comp (ρ : RightComodule k H V) (m n : M) :
    (weightComponent ρ m).comp (weightSpace ρ n).subtype =
      if h : n = m then h ▸ (LinearMap.id : weightSpace ρ n →ₗ[k] weightSpace ρ n) else 0 := by
  classical
  have h : (weightSum ρ).symm.toLinearMap.comp (weightSpace ρ n).subtype =
      DirectSum.lof k M (fun j ↦ weightSpace ρ j) n := by
    apply LinearMap.ext
    intro x
    change (weightSum ρ).symm (x : V) = DirectSum.lof k M _ n x
    rw [LinearEquiv.symm_apply_eq, weightSum_lof]
  rw [weightComponent, LinearMap.comp_assoc, h, DirectSum.component_comp_lof]

open scoped Classical in
private theorem tensorInclusions_injective (ρ : RightComodule k H V) (σ : RightComodule k H W)
    (m : M) :
    Function.Injective (DirectSum.toModule k (pairs M m) (V ⊗[k] W) (fun p ↦
      TensorProduct.mapIncl (weightSpace ρ p.val.1) (weightSpace σ p.val.2))) := by
  classical
  intro x y h
  apply DirectSum.ext_component k
  intro p
  let A (q : pairs M m) := weightSpace ρ q.val.1 ⊗[k] weightSpace σ q.val.2
  let project := TensorProduct.map (weightComponent ρ p.val.1) (weightComponent σ p.val.2)
  have he : project.comp (DirectSum.toModule k (pairs M m) _ (fun q ↦
      TensorProduct.mapIncl (weightSpace ρ q.val.1) (weightSpace σ q.val.2))) =
      DirectSum.component k (pairs M m) A p := by
    apply DirectSum.linearMap_ext
    intro q
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, DirectSum.toModule_lof]
    change (project.comp (TensorProduct.mapIncl (weightSpace ρ q.val.1) (weightSpace σ q.val.2))) z =
      DirectSum.component k (pairs M m) A p (DirectSum.lof k (pairs M m) A q z)
    change ((TensorProduct.map _ _).comp (TensorProduct.map _ _)) z = _
    rw [← TensorProduct.map_comp, weightComponent_comp, weightComponent_comp, DirectSum.component.of]
    by_cases h₁ : q.val.1 = p.val.1
    · by_cases h₂ : q.val.2 = p.val.2
      · have hpq : q = p := Subtype.ext (Prod.ext h₁ h₂)
        subst q
        simp [TensorProduct.map_id]
      · have hpq : q ≠ p := fun h ↦ h₂ (congrArg (fun q : pairs M m ↦ q.val.2) h)
        simp [h₂, hpq, TensorProduct.map_zero_right]
    · have hpq : q ≠ p := fun h ↦ h₁ (congrArg (fun q : pairs M m ↦ q.val.1) h)
      simp [h₁, hpq, TensorProduct.map_zero_left]
  exact (DFunLike.congr_fun he x).symm.trans
    ((congrArg project h).trans (DFunLike.congr_fun he y))

section Tensor

variable [FiniteDimensional k V] [FiniteDimensional k W]

set_option maxHeartbeats 600000 in
/-- The tensor coaction and the canonical direct sum isomorphisms at each weight. -/
def tensorWeightIso (ρ : RightComodule k H V) (σ : RightComodule k H W) : TensorWeightIso ρ σ := by
  classical
  let existence := LinearAlgebraicGroups.WeightDecomposition.tensorWeights ρ σ
  let τ := Classical.choose existence
  have hτ := Classical.choose_spec existence
  let inc (m : M) (p : pairs M m) :=
    TensorProduct.mapIncl (weightSpace ρ p.val.1) (weightSpace σ p.val.2)
  let into (m : M) (p : pairs M m) := (inc m p).codRestrict (weightSpace τ m) (fun z ↦ by
    rw [hτ.2 m]
    exact Submodule.mem_iSup_of_mem p ⟨z, rfl⟩)
  let f (m : M) := DirectSum.toModule k (pairs M m) _ (into m)
  have hf (m : M) : (weightSpace τ m).subtype.comp (f m) =
      DirectSum.toModule k (pairs M m) _ (inc m) := by
    apply DirectSum.linearMap_ext
    intro p
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, f, DirectSum.toModule_lof]
    rfl
  have hb (m : M) : Function.Bijective (f m) := by
    constructor
    · intro x y hxy
      apply tensorInclusions_injective ρ σ m
      change DirectSum.toModule k (pairs M m) _ (inc m) x =
        DirectSum.toModule k (pairs M m) _ (inc m) y
      rw [← hf]
      exact congrArg Subtype.val hxy
    · intro z
      have hz : (z : V ⊗[k] W) ∈ LinearMap.range ((weightSpace τ m).subtype.comp (f m)) := by
        rw [hf]
        have hle : weightSpace τ m ≤ LinearMap.range (DirectSum.toModule k (pairs M m) _ (inc m)) := by
          rw [hτ.2 m]
          apply iSup_le
          intro p t ht
          obtain ⟨s, rfl⟩ := ht
          refine ⟨DirectSum.lof k (pairs M m) _ p s, ?_⟩
          rw [DirectSum.toModule_lof]
        exact hle z.property
      obtain ⟨s, hs⟩ := hz
      exact ⟨s, Subtype.ext hs⟩
  refine ⟨τ, hτ.1, fun m ↦ LinearEquiv.ofBijective (f m) (hb m), ?_⟩
  intro m p z
  change ((f m (DirectSum.lof k (pairs M m) _ p z) : weightSpace τ m) : V ⊗[k] W) = _
  simp only [f, DirectSum.toModule_lof]
  rfl

theorem tensorWeightDecomposition : TensorWeightDecomposition.{u} :=
  fun ρ σ ↦ ⟨tensorWeightIso ρ σ⟩

end Tensor

theorem coactionExpansion : CoactionExpansion.{u} := by
  classical
  intro k M V _ _ _ _ ρ v
  refine ⟨(weightSum ρ).symm v, ⟨(weightSum ρ).apply_symm_apply v, ?_⟩, ?_⟩
  · have h := DFunLike.congr_fun (weightSum_isComoduleMap ρ) ((weightSum ρ).symm v)
    change _ = ρ.coaction (weightSum ρ ((weightSum ρ).symm v)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  · intro x hx
    exact (weightSum ρ).injective (hx.1.trans ((weightSum ρ).apply_symm_apply v).symm)

private theorem tensor_ext_weights {X : Type u} [AddCommGroup X] [Module k X]
    (ρ : RightComodule k H V) (σ : RightComodule k H W) {f g : (V ⊗[k] W) →ₗ[k] X}
    (h : ∀ m n (v : weightSpace ρ m) (w : weightSpace σ n), f (v.val ⊗ₜ[k] w.val) =
      g (v.val ⊗ₜ[k] w.val)) : f = g := by
  apply TensorProduct.ext'
  intro v w
  have e₁ : f.comp ((TensorProduct.mk k V W).flip w) =
      g.comp ((TensorProduct.mk k V W).flip w) := by
    apply linearMap_ext_weights ρ
    intro m x
    have e₂ : f.comp (TensorProduct.mk k V W x.val) = g.comp (TensorProduct.mk k V W x.val) := by
      apply linearMap_ext_weights σ
      intro n y
      exact h m n x y
    exact DFunLike.congr_fun e₂ w
  exact DFunLike.congr_fun e₁ v

private theorem tensorCoaction_tmul {ρ : RightComodule k H V} {σ : RightComodule k H W}
    (T : TensorWeightIso ρ σ) {m n : M} {v : V} {w : W}
    (hv : v ∈ weightSpace ρ m) (hw : w ∈ weightSpace σ n) :
    T.coaction.coaction (v ⊗ₜ[k] w) = (v ⊗ₜ[k] w) ⊗ₜ[k] e (m * n) := by
  rw [T.coaction_eq]
  simp [tensorCoactionMap, mem_weightSpace.mp hv, mem_weightSpace.mp hw, map_mul]

theorem tensorMap_isComoduleMap {V' W' : Type u} [AddCommGroup V'] [Module k V']
    [AddCommGroup W'] [Module k W'] {ρ : RightComodule k H V} {σ : RightComodule k H W}
    {ρ' : RightComodule k H V'} {σ' : RightComodule k H W'}
    (T : TensorWeightIso ρ σ) (T' : TensorWeightIso ρ' σ') (f : V →ₗ[k] V') (g : W →ₗ[k] W')
    (hf : Specs.isComoduleMap ρ ρ' f) (hg : Specs.isComoduleMap σ σ' g) :
    Specs.isComoduleMap T.coaction T'.coaction (TensorProduct.map f g) := by
  unfold Specs.isComoduleMap
  apply tensor_ext_weights ρ σ
  intro m n v w
  have hv : f v.val ∈ weightSpace ρ' m := (degreePreserving ρ ρ' f).mp hf m v.property
  have hw : g w.val ∈ weightSpace σ' n := (degreePreserving σ σ' g).mp hg n w.property
  simp only [LinearMap.comp_apply, tensorCoaction_tmul T v.property w.property,
    LinearMap.rTensor_tmul, TensorProduct.map_tmul, tensorCoaction_tmul T' hv hw]

theorem tensorWeightNaturality : TensorWeightNaturality.{u} := by
  classical
  intro k M V W V' W' _ _ _ _ _ _ _ _ _ _ ρ σ ρ' σ' T T' f g hf hg
  refine ⟨tensorMap_isComoduleMap T T' f g hf hg, weightMap f hf, weightMap g hg,
    fun _ _ ↦ rfl, fun _ _ ↦ rfl, ?_⟩
  intro m
  apply DirectSum.linearMap_ext
  intro p
  apply LinearMap.ext
  intro t
  simp only [LinearMap.comp_apply, DirectSum.lmap_lof, LinearEquiv.coe_coe, Submodule.subtype_apply]
  rw [T.equiv_lof, T'.equiv_lof]
  suffices h :
      (TensorProduct.mapIncl (weightSpace ρ' p.val.1) (weightSpace σ' p.val.2)).comp
        (TensorProduct.map (weightMap f hf p.val.1) (weightMap g hg p.val.2)) =
      (TensorProduct.map f g).comp
        (TensorProduct.mapIncl (weightSpace ρ p.val.1) (weightSpace σ p.val.2)) from
    DFunLike.congr_fun h t
  exact TensorProduct.ext' (fun _ _ ↦ rfl)

end

end RepTheorySurvey.Invariants.TorusWeights
