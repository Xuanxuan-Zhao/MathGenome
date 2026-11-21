import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Construction
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Functoriality

open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u v
namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]
variable {E F G : Type v} [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G]

/-- The deletion formula as an equality in the degree-restricted exterior power. -/
theorem differential_ιMulti (a : E →ₗ[R] R) (n : ℕ) (e : Fin (n+1) → E) :
    differential a n (exteriorPower.ιMulti R (n+1) e) =
      ∑ i : Fin (n+1), (-1 : R)^i.val •
        (a (e i) • exteriorPower.ιMulti R n (e ∘ i.succAbove)) := by
  apply Subtype.ext
  simpa only [differential_coe, exteriorPower.ιMulti_apply_coe,
    Submodule.coe_sum, SetLike.val_smul] using contraction_formula a n e

/-- Naturality of contraction on every exterior power. -/
theorem differential_naturality (a : E →ₗ[R] R) (b : F →ₗ[R] R)
    (φ : E →ₗ[R] F) (h : b.comp φ = a) (n : ℕ) :
    (differential b n).comp (exteriorPower.map (n+1) φ) =
      (exteriorPower.map n φ).comp (differential a n) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro e
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, differential_ιMulti, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← LinearMap.congr_fun h (e i)]
  rfl

/-- The induced chain map has exactly the exterior powers as its components. -/
def chainMap (a : E →ₗ[R] R) (b : F →ₗ[R] R)
    (φ : E →ₗ[R] F) (h : b.comp φ = a) : complex a ⟶ complex b :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (exteriorPower.map n φ)) (fun n => by
    simp only [complex, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    exact differential_naturality a b φ h n)

theorem chainMap_exists : Specs.AdvCommAlg.Koszul.chainMapExists.{u,v} := by
  intro R _ E _ _ F _ _ a b φ h
  exact ⟨chainMap a b φ h, fun _ => rfl⟩

theorem chainMap_identity : Specs.AdvCommAlg.Koszul.chainMapIdentity.{u,v} := by
  intro R _ E _ _ a f hf
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change (f.f n).hom = LinearMap.id
  rw [hf n, exteriorPower.map_id]
  rfl

theorem chainMap_composition : Specs.AdvCommAlg.Koszul.chainMapComposition.{u,v} := by
  intro R _ E F G _ _ _ _ _ _ a b c φ ψ f g k hf hg hk
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change (g.f n).hom.comp (f.f n).hom = (k.f n).hom
  rw [hf n, hg n, hk n, exteriorPower.map_comp]
  rfl

/-- An isomorphism of linear forms induces an isomorphism of their complexes. -/
def complexIso (a : E →ₗ[R] R) (b : F →ₗ[R] R)
    (e : E ≃ₗ[R] F) (h : b.comp e.toLinearMap = a) : complex a ≅ complex b where
  hom := chainMap a b e.toLinearMap h
  inv := chainMap b a e.symm.toLinearMap (by
    apply LinearMap.ext
    intro x
    simpa using (LinearMap.congr_fun h (e.symm x)).symm)
  hom_inv_id := by
    apply chainMap_identity
    intro n
    change (exteriorPower.map n e.symm.toLinearMap).comp
      (exteriorPower.map n e.toLinearMap) = exteriorPower.map n LinearMap.id
    rw [← exteriorPower.map_comp]
    congr 1
    ext x
    exact e.symm_apply_apply x
  inv_hom_id := by
    apply chainMap_identity
    intro n
    change (exteriorPower.map n e.toLinearMap).comp
      (exteriorPower.map n e.symm.toLinearMap) = exteriorPower.map n LinearMap.id
    rw [← exteriorPower.map_comp]
    congr 1
    ext x
    exact e.apply_symm_apply x

theorem coordinate_iso : Specs.AdvCommAlg.Koszul.coordinateIso.{u} := by
  intro R _ x y e h
  exact ⟨complexIso (listForm x) (listForm y) e h, fun _ => rfl⟩

variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Tensor the induced maps with the identity of any coefficient module. -/
def coefficientChainMap (x y : List R)
    (φ : (Fin x.length → R) →ₗ[R] (Fin y.length → R))
    (h : (listForm y).comp φ = listForm x) :
    coefficientComplex M x ⟶ coefficientComplex M y :=
  ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (TensorProduct.map (exteriorPower.map n φ)
      (LinearMap.id : M →ₗ[R] M))) (fun n => by
    simp only [coefficientComplex, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    change (coefficientDifferential M y n).comp
        (TensorProduct.map (exteriorPower.map (n+1) φ) LinearMap.id) =
      (TensorProduct.map (exteriorPower.map n φ) LinearMap.id).comp
        (coefficientDifferential M x n)
    simp only [coefficientDifferential, ← TensorProduct.map_comp,
      differential_naturality (listForm x) (listForm y) φ h])

/-- Inverse linear coordinate changes remain inverse after tensoring, without flatness. -/
def coefficientComplexIso (x y : List R)
    (e : (Fin x.length → R) ≃ₗ[R] (Fin y.length → R))
    (h : (listForm y).comp e.toLinearMap = listForm x) :
    coefficientComplex M x ≅ coefficientComplex M y where
  hom := coefficientChainMap M x y e.toLinearMap h
  inv := coefficientChainMap M y x e.symm.toLinearMap (by
    apply LinearMap.ext
    intro z
    simpa using (LinearMap.congr_fun h (e.symm z)).symm)
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change (TensorProduct.map (exteriorPower.map n e.symm.toLinearMap) LinearMap.id).comp
      (TensorProduct.map (exteriorPower.map n e.toLinearMap) LinearMap.id) = LinearMap.id
    rw [← TensorProduct.map_comp, ← exteriorPower.map_comp]
    have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro z
      exact e.symm_apply_apply z
    rw [he, exteriorPower.map_id, LinearMap.id_comp, TensorProduct.map_id]
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change (TensorProduct.map (exteriorPower.map n e.toLinearMap) LinearMap.id).comp
      (TensorProduct.map (exteriorPower.map n e.symm.toLinearMap) LinearMap.id) = LinearMap.id
    rw [← TensorProduct.map_comp, ← exteriorPower.map_comp]
    have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro z
      exact e.apply_symm_apply z
    rw [he, exteriorPower.map_id, LinearMap.id_comp, TensorProduct.map_id]

theorem coefficient_coordinate_iso :
    Specs.AdvCommAlg.Koszul.coefficientCoordinateIso.{u,v} := by
  intro R _ M _ _ x y e h
  exact ⟨coefficientComplexIso M x y e h, fun _ => rfl⟩

variable {M}

/-- The coordinate change which sends the jth basis vector to the p(j)th. -/
def permutationCoordinates (x y : List R) (p : Fin x.length ≃ Fin y.length) :
    (Fin x.length → R) ≃ₗ[R] (Fin y.length → R) :=
  (Pi.basisFun R (Fin x.length)).equiv (Pi.basisFun R (Fin y.length)) p

/-- Reordering entries has exactly the required compatibility of linear forms. -/
theorem listForm_permutation (x y : List R) (p : Fin x.length ≃ Fin y.length)
    (h : ∀ j, y.get (p j) = x.get j) :
    (listForm y).comp (permutationCoordinates x y p).toLinearMap = listForm x := by
  apply (Pi.basisFun R (Fin x.length)).ext
  intro j
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, permutationCoordinates,
    Module.Basis.equiv_apply, listForm_basis] using h j

theorem permutation_iso : Specs.AdvCommAlg.Koszul.permutationIso.{u} := by
  intro R _ x y p h
  exact ⟨complexIso (listForm x) (listForm y) (permutationCoordinates x y p)
    (listForm_permutation x y p h)⟩

theorem coefficient_permutation_iso :
    Specs.AdvCommAlg.Koszul.coefficientPermutationIso.{u,v} := by
  intro R _ M _ _ x y p h
  exact ⟨coefficientComplexIso M x y (permutationCoordinates x y p)
    (listForm_permutation x y p h)⟩

/-- The functional of a list is the dot product with that list. -/
theorem listForm_apply (x : List R) (z : Fin x.length → R) :
    listForm x z = ∑ j, z j * x.get j := by
  simp only [listForm, Module.Basis.constr_apply_fintype, Pi.basisFun_equivFun,
    LinearEquiv.refl_apply, smul_eq_mul]

/-- The usual entrywise formula for a linear coordinate change supplies the
compatibility required by functoriality. The columns are the images of the basis. -/
theorem listForm_coordinate_change (x y : List R)
    (e : (Fin x.length → R) ≃ₗ[R] (Fin y.length → R))
    (h : ∀ i, x.get i = ∑ j, (e (Pi.basisFun R (Fin x.length) i)) j * y.get j) :
    (listForm y).comp e.toLinearMap = listForm x := by
  apply (Pi.basisFun R (Fin x.length)).ext
  intro i
  change listForm y (e (Pi.basisFun R (Fin x.length) i)) =
    listForm x (Pi.basisFun R (Fin x.length) i)
  rw [listForm_basis, listForm_apply]
  exact (h i).symm

theorem linear_coordinate_change_iso :
    Specs.AdvCommAlg.Koszul.linearCoordinateChangeIso.{u,v} := by
  intro R _ M _ _ x y e h
  have he := listForm_coordinate_change x y e h
  exact ⟨⟨complexIso (listForm x) (listForm y) e he⟩,
    ⟨coefficientComplexIso M x y e he⟩⟩

end AdvCommAlg.Koszul
