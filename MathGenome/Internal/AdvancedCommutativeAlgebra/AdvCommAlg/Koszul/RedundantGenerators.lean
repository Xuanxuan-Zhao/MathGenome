import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.RedundantGenerators
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Functoriality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.TensorDecomposition
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.RingTheory.Flat.Basic

open CategoryTheory
open scoped TensorProduct DirectSum
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w w₁ w₂ w₃
namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]

/-- A finite list generates exactly the image of its associated linear form. -/
theorem listForm_range (x : List R) : LinearMap.range (listForm x) = listIdeal x := by
  rw [listForm, Module.Basis.constr_range]
  change Submodule.span R (Set.range (fun i : Fin x.length => x.get i)) =
    Submodule.span R {r | r ∈ x}
  congr 1
  ext r
  exact List.mem_iff_get.symm

/-- Choose, simultaneously, expressions of a redundant list in the old generators. -/
theorem redundant_lift (x y : List R) (hy : ∀ a ∈ y, a ∈ listIdeal x) :
    ∃ b : (Fin y.length → R) →ₗ[R] (Fin x.length → R),
      (listForm x).comp b = listForm y := by
  classical
  have h (j : Fin y.length) : y.get j ∈ LinearMap.range (listForm x) := by
    rw [listForm_range]
    exact hy _ (List.get_mem _ _)
  choose b hb using h
  refine ⟨(Pi.basisFun R (Fin y.length)).constr R b, ?_⟩
  apply (Pi.basisFun R (Fin y.length)).ext
  intro j
  simp only [LinearMap.comp_apply, Module.Basis.constr_basis, listForm_basis]
  exact hb j

/-- Splitting a vector at the boundary between two lists. -/
def appendCoordinates (x y : List R) :
    (Fin (x ++ y).length → R) ≃ₗ[R] ((Fin x.length → R) × (Fin y.length → R)) where
  toFun z := (fun i => z ⟨i.val, by simp only [List.length_append]; omega⟩,
    fun i => z ⟨x.length + i.val, by simp only [List.length_append]; omega⟩)
  invFun z i := if h : i.val < x.length then z.1 ⟨i.val, h⟩
    else z.2 ⟨i.val - x.length, by have := i.isLt; simp at this; omega⟩
  left_inv z := by
    funext i
    dsimp
    split_ifs with h
    · rfl
    · congr 1
      apply Fin.ext
      dsimp
      omega
  right_inv z := by
    apply Prod.ext <;> funext i <;> simp
  map_add' a b := by rfl
  map_smul' c a := by rfl

/-- In split coordinates the concatenation form is the sum of the two forms. -/
theorem listForm_append (x y : List R) (z : Fin (x ++ y).length → R) :
    listForm (x ++ y) z = listForm x (appendCoordinates x y z).1 +
      listForm y (appendCoordinates x y z).2 := by
  classical
  simp only [listForm_apply]
  have hlen : (x ++ y).length = x.length + y.length := List.length_append
  rw [← (finCongr hlen).symm.sum_comp (fun j => z j * (x ++ y).get j)]
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    simp [appendCoordinates, List.get_eq_getElem, List.getElem_append_left]
    congr 2
  · apply Finset.sum_congr rfl
    intro i hi
    simp [appendCoordinates, List.get_eq_getElem, List.getElem_append_right]
    congr 2

/-- The elementary block triangular change of basis. -/
def shearCoordinates {E F : Type*} [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] (b : F →ₗ[R] E) : (E × F) ≃ₗ[R] (E × F) where
  toFun z := (z.1 + b z.2, z.2)
  invFun z := (z.1 - b z.2, z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z w := by ext <;> simp [add_add_add_comm]
  map_smul' c z := by ext <;> simp [smul_add]

@[simp] theorem listForm_append_symm (x y : List R)
    (z : (Fin x.length → R) × (Fin y.length → R)) :
    listForm (x ++ y) ((appendCoordinates x y).symm z) =
      listForm x z.1 + listForm y z.2 := by
  rw [listForm_append, LinearEquiv.apply_symm_apply]

@[simp] theorem listForm_replicate_zero (s : ℕ) :
    listForm (List.replicate s (0 : R)) = 0 := by
  apply (Pi.basisFun R (Fin (List.replicate s (0 : R)).length)).ext
  intro i
  rw [listForm_basis]
  simp

/-- Reindex the zero tail by its specified number of positions. -/
def zeroTailCoordinates (s : ℕ) :
    (Fin s → R) ≃ₗ[R] (Fin (List.replicate s (0 : R)).length → R) :=
  LinearEquiv.funCongrLeft R R (finCongr (List.length_replicate ..))

/-- Send `(a,c)` to `(a+b(c),c)`, so the redundant tail is evaluated as zero. -/
def redundantCoordinates (x y : List R)
    (b : (Fin y.length → R) →ₗ[R] (Fin x.length → R)) :
    (Fin (x ++ y).length → R) ≃ₗ[R]
      (Fin (x ++ List.replicate y.length (0 : R)).length → R) :=
  (appendCoordinates x y).trans ((shearCoordinates b).trans
    (((LinearEquiv.refl R (Fin x.length → R)).prodCongr (zeroTailCoordinates y.length)).trans
      (appendCoordinates x (List.replicate y.length (0 : R))).symm))

theorem listForm_redundantCoordinates (x y : List R)
    (b : (Fin y.length → R) →ₗ[R] (Fin x.length → R))
    (hb : (listForm x).comp b = listForm y) :
    (listForm (x ++ List.replicate y.length (0 : R))).comp
      (redundantCoordinates x y b).toLinearMap = listForm (x ++ y) := by
  apply LinearMap.ext
  intro z
  change listForm (x ++ List.replicate y.length (0 : R))
    ((appendCoordinates x (List.replicate y.length (0 : R))).symm
      ((appendCoordinates x y z).1 + b (appendCoordinates x y z).2,
        zeroTailCoordinates y.length (appendCoordinates x y z).2)) = _
  rw [listForm_append_symm, listForm_replicate_zero, LinearMap.zero_apply, add_zero,
    map_add]
  have he := LinearMap.congr_fun hb (appendCoordinates x y z).2
  change listForm x (b (appendCoordinates x y z).2) = _ at he
  rw [he]
  exact (listForm_append x y z).symm

/-- Replacing any finite redundant tail by zero gives an actual coefficient chain isomorphism. -/
theorem redundant_zero_iso (M : Type v) [AddCommGroup M] [Module R M]
    (x y : List R) (hy : ∀ a ∈ y, a ∈ listIdeal x) :
    Nonempty (coefficientComplex M (x ++ y) ≅
      coefficientComplex M (x ++ List.replicate y.length (0 : R))) := by
  obtain ⟨b, hb⟩ := redundant_lift x y hy
  exact ⟨coefficientComplexIso M _ _ (redundantCoordinates x y b)
    (listForm_redundantCoordinates x y b hb)⟩

/-- Contraction by the zero form is zero on the entire exterior algebra. -/
@[simp] private theorem contraction_zero {E : Type*} [AddCommGroup E] [Module R E]
    (a : ExteriorAlgebra R E) :
    contraction (0 : E →ₗ[R] R) a = 0 := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add a b ha hb => simp [ha, hb]
  | ι_mul a e ha => simp [contraction_generator_mul, ha]

/-- The exterior factor in the redundancy statement has zero differential. -/
theorem zero_exterior_differential :
    Specs.AdvCommAlg.Koszul.zeroExteriorDifferential.{u} := by
  intro R _ s n
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  exact contraction_zero (a : ExteriorAlgebra R (Fin s → R))

/-- Coefficient homology vanishes above the number of generators. -/
theorem homology_vanish (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) (q : ℕ) (hq : x.length < q) : Subsingleton (homology M x q) := by
  apply ModuleCat.subsingleton_of_isZero
  exact ((coefficientComplex M x).sc q).isZero_homology_of_isZero_X₂
    (ModuleCat.isZero_iff_subsingleton.mpr (coefficientComplex_vanish M x q hq))

/-- Every nonzero Koszul homology degree is at most the list length. -/
theorem homology_degree_le (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R) {q : ℕ} (hq : Nontrivial (homology M x q)) : q ≤ x.length := by
  by_contra h
  have hs := homology_vanish M x q (by omega)
  obtain ⟨a,b,hab⟩ := hq.exists_pair_ne
  exact hab (hs.elim a b)

/-- Under the source's properness condition the highest nonzero degree exists. -/
theorem homology_greatest : Specs.AdvCommAlg.Koszul.homologyGreatest.{u,v} := by
  intro R _ M _ _ x hM
  have h0 : Nontrivial (homology M x 0) :=
    (homologyZeroEquiv M x).toEquiv.nontrivial_congr.mpr hM
  have hb : BddAbove {q : ℕ | Nontrivial (homology M x q)} :=
    ⟨x.length, fun _ hq => homology_degree_le M x hq⟩
  exact hb.exists_isGreatest_of_nonempty ⟨0, h0⟩

/-- Swap the blocks of a concatenated list, with arbitrary coefficients. -/
def appendSwapIso (M : Type v) [AddCommGroup M] [Module R M] (x y : List R) :
    coefficientComplex M (x ++ y) ≅ coefficientComplex M (y ++ x) :=
  coefficientComplexIso M _ _
    ((appendCoordinates x y).trans ((LinearEquiv.prodComm R _ _).trans
      (appendCoordinates y x).symm)) (by
        apply LinearMap.ext
        intro z
        change listForm (y ++ x) ((appendCoordinates y x).symm
          ((appendCoordinates x y z).2, (appendCoordinates x y z).1)) = _
        rw [listForm_append_symm, add_comm]
        exact (listForm_append x y z).symm)

/-- A chain isomorphism identifies the sets of nonzero homology degrees. -/
theorem homology_nontrivial_iff (M : Type v) [AddCommGroup M] [Module R M]
    {x y : List R} (e : coefficientComplex M x ≅ coefficientComplex M y) (q : ℕ) :
    Nontrivial (homology M x q) ↔ Nontrivial (homology M y q) :=
  (HomologicalComplex.homologyMapIso e q).toLinearEquiv.toEquiv.nontrivial_congr

/-- Concatenation in either order has the same highest nonzero homology degree. -/
theorem appendSwap_greatest (M : Type v) [AddCommGroup M] [Module R M]
    (x y : List R) {t : ℕ}
    (ht : IsGreatest {q : ℕ | Nontrivial (homology M (x ++ y) q)} t) :
    IsGreatest {q : ℕ | Nontrivial (homology M (y ++ x) q)} t := by
  have hs : {q : ℕ | Nontrivial (homology M (x ++ y) q)} =
      {q : ℕ | Nontrivial (homology M (y ++ x) q)} := by
    ext q
    exact homology_nontrivial_iff M (appendSwapIso M x y) q
  rwa [← hs]

/-- Compare two generating lists using the exact homology shift. -/
theorem thresholdInvariant_of_shift
    (hshift : Specs.AdvCommAlg.Koszul.redundantHomologyGreatest.{u,v}) :
    Specs.AdvCommAlg.Koszul.generatorThresholdInvariant.{u,v} := by
  intro R _ M _ _ x y hI hM
  have hMy : Nontrivial (M ⧸ listSubmodule M y) := by
    simpa only [listSubmodule, hI] using hM
  obtain ⟨t, ht⟩ := homology_greatest M x hM
  obtain ⟨u, hu⟩ := homology_greatest M y hMy
  have hy : ∀ a ∈ y, a ∈ listIdeal x := by
    intro a ha
    rw [hI]
    exact Ideal.subset_span ha
  have hx : ∀ a ∈ x, a ∈ listIdeal y := by
    intro a ha
    rw [← hI]
    exact Ideal.subset_span ha
  have hxy := hshift M x y hy hM t ht
  have hyx := hshift M y x hx hMy u hu
  have he : t + y.length = u + x.length :=
    (appendSwap_greatest M x y hxy).unique hyx
  have htbound := homology_degree_le M x ht.1
  have hubound := homology_degree_le M y hu.1
  refine ⟨t, u, ht, hu, ?_⟩
  omega

/-- Homology maxima are preserved by chain isomorphisms. -/
theorem greatestHomology_iso
    {C D : ChainComplex (ModuleCat.{v} R) ℕ} (e : C ≅ D) {t : ℕ}
    (ht : IsGreatest {q : ℕ | Nontrivial (C.homology q)} t) :
    IsGreatest {q : ℕ | Nontrivial (D.homology q)} t := by
  have hs : {q : ℕ | Nontrivial (C.homology q)} =
      {q : ℕ | Nontrivial (D.homology q)} := by
    ext q
    exact (HomologicalComplex.homologyMapIso e q).toLinearEquiv.toEquiv.nontrivial_congr
  rwa [← hs]

/-- Assemble coordinate reduction and the coefficient tensor comparison. -/
theorem redundantTensor_of_zeroTail
    (hzero : ∀ {R : Type u} [CommRing R] (M : Type v)
      [AddCommGroup M] [Module R M] (x : List R) (s : ℕ),
      Nonempty (coefficientComplex M (x ++ List.replicate s (0 : R)) ≅
        HomologicalComplex.mapBifunctor (coefficientComplex M x)
          (complex (0 : (Fin s → R) →ₗ[R] R)) moduleTensor (.down ℕ))) :
    Specs.AdvCommAlg.Koszul.redundantTensorIso.{u,v} := by
  intro R _ M _ _ x y hy
  obtain ⟨e⟩ := redundant_zero_iso M x y hy
  obtain ⟨f⟩ := hzero M x y.length
  exact ⟨e ≪≫ f⟩

/-- Assemble the complex isomorphism and the finite-free zero-factor calculation. -/
theorem redundantGreatest_of_tensor
    (hiso : Specs.AdvCommAlg.Koszul.redundantTensorIso.{u,v})
    (htensor : ∀ {R : Type u} [CommRing R]
      (C : ChainComplex (ModuleCat.{max u v} R) ℕ) (s t : ℕ),
      IsGreatest {q : ℕ | Nontrivial (C.homology q)} t →
        IsGreatest {q : ℕ | Nontrivial
          ((HomologicalComplex.mapBifunctor C
            (complex (0 : (Fin s → R) →ₗ[R] R)) moduleTensor (.down ℕ)).homology q)}
          (t + s)) :
    Specs.AdvCommAlg.Koszul.redundantHomologyGreatest.{u,v} := by
  intro R _ M _ _ x y hy _ t ht
  obtain ⟨e⟩ := hiso M x y hy
  exact greatestHomology_iso e.symm (htensor (coefficientComplex M x) y.length t ht)

/-- The bidegrees contributing to one total degree. -/
abbrev DegreePairs (n : ℕ) := {i : ℕ × ℕ // i.1 + i.2 = n}

abbrev totalSummand (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) {n : ℕ} (i : DegreePairs n) :=
  C.X i.val.1 ⊗[R] D.X i.val.2

/-- The universal coproduct underlying a term of the tensor total complex. -/
def totalTermToSum (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) :
    (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).X n →ₗ[R]
      ⨁ i : DegreePairs n, totalSummand C D i :=
  (HomologicalComplex.mapBifunctorDesc (K₁ := C) (K₂ := D)
    (F := moduleTensor) (c := .down ℕ) (j := n)
    (A := ModuleCat.of R (⨁ i : DegreePairs n, totalSummand C D i))
    (fun p q h => ModuleCat.ofHom
    (DirectSum.lof R (DegreePairs n) (totalSummand C D) ⟨(p,q),h⟩))).hom

def sumToTotalTerm (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) :
    (⨁ i : DegreePairs n, totalSummand C D i) →ₗ[R]
      (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).X n :=
  DirectSum.toModule R _ _ (fun i =>
    (HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ)
      i.val.1 i.val.2 n i.property).hom)

@[simp] theorem totalTermToSum_inclusion
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n)
    (z : C.X p ⊗[R] D.X q) :
    totalTermToSum C D n
      ((HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ) p q n h).hom z) =
      DirectSum.lof R (DegreePairs n) (totalSummand C D) ⟨(p,q),h⟩ z := by
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (HomologicalComplex.ι_mapBifunctorDesc
      (K₁ := C) (K₂ := D) (F := moduleTensor) (c := .down ℕ)
      (A := ModuleCat.of R (⨁ i : DegreePairs n, totalSummand C D i))
      (fun p q h => ModuleCat.ofHom (DirectSum.lof R (DegreePairs n)
        (totalSummand C D) ⟨(p,q),h⟩)) p q h)) z

/-- Totalization here uses a direct sum, without a finiteness assumption on terms. -/
def totalTermEquiv (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) :
    (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).X n ≃ₗ[R]
      ⨁ i : DegreePairs n, totalSummand C D i := by
  apply LinearEquiv.ofLinearMap (totalTermToSum C D n) (sumToTotalTerm C D n)
  · apply DirectSum.linearMap_ext
    rintro ⟨⟨p,q⟩,h⟩
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, sumToTotalTerm, DirectSum.toModule_lof,
      LinearMap.id_apply]
    exact totalTermToSum_inclusion C D p q n h z
  · apply congrArg ModuleCat.Hom.hom (α :=
      (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).X n ⟶
        (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).X n)
    apply HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := C) (K₂ := D) (F := moduleTensor) (c := .down ℕ)
    intro p q h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change sumToTotalTerm C D n (totalTermToSum C D n
      ((HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ) p q n h).hom z)) = _
    rw [totalTermToSum_inclusion]
    simp only [sumToTotalTerm, DirectSum.toModule_lof]
    rfl

@[simp] theorem totalTermEquiv_inclusion
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n)
    (z : C.X p ⊗[R] D.X q) :
    totalTermEquiv C D n
      ((HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ) p q n h).hom z) =
      DirectSum.lof R (DegreePairs n) (totalSummand C D) ⟨(p,q),h⟩ z :=
  totalTermToSum_inclusion C D p q n h z

@[simp] theorem totalTermEquiv_symm_lof
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) (i : DegreePairs n)
    (z : totalSummand C D i) :
    (totalTermEquiv C D n).symm (DirectSum.lof R (DegreePairs n) (totalSummand C D) i z) =
      (HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ)
        i.val.1 i.val.2 n i.property).hom z :=
  DirectSum.toModule_lof _ _ _

/-- Tensoring every term on the right with the coefficient module. -/
abbrev tensorCoefficients (M : Type w) [AddCommGroup M] [Module R M]
    (C : ChainComplex (ModuleCat.{v} R) ℕ) :=
  ((moduleTensor.flip.obj (ModuleCat.of R M)).mapHomologicalComplex (.down ℕ)).obj C

/-- Move the coefficient factor past the second exterior factor. -/
def tensorMiddleSwap (A : Type*) (B : Type*) (M : Type*)
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup M] [Module R M] :
    (A ⊗[R] M) ⊗[R] B ≃ₗ[R] (A ⊗[R] B) ⊗[R] M :=
  (TensorProduct.assoc R A M B).trans
    ((TensorProduct.congr (LinearEquiv.refl R A) (TensorProduct.comm R M B)).trans
      (TensorProduct.assoc R A B M).symm)

@[simp] theorem tensorMiddleSwap_tmul (A B M : Type*)
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup M] [Module R M] (a : A) (b : B) (m : M) :
    tensorMiddleSwap (R := R) A B M ((a ⊗ₜ[R] m) ⊗ₜ[R] b) =
      (a ⊗ₜ[R] b) ⊗ₜ[R] m := rfl

@[simp] theorem directSumEquiv_lof {ι : Type*} [DecidableEq ι]
    {A B : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module R (B i)]
    (e : ∀ i, A i ≃ₗ[R] B i) (i : ι) (a : A i) :
    DirectSum.congrLinearEquiv e (DirectSum.lof R ι A i a) =
      DirectSum.lof R ι B i (e i a) := by
  change DirectSum.lmap (fun i => (e i).toLinearMap) _ = _
  exact DirectSum.lmap_lof _ _ _

/-- Distributivity and associativity move coefficients across a total term. -/
def totalCoefficientsEquiv (M : Type*) [AddCommGroup M] [Module R M]
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) :
    (HomologicalComplex.mapBifunctor (tensorCoefficients M C) D moduleTensor (.down ℕ)).X n ≃ₗ[R]
      (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).X n ⊗[R] M :=
  (totalTermEquiv (tensorCoefficients M C) D n).trans
    ((DirectSum.congrLinearEquiv (fun i : DegreePairs n =>
      tensorMiddleSwap (C.X i.val.1) (D.X i.val.2) M)).trans
      ((TensorProduct.directSumLeft R R (totalSummand C D) M).symm.trans
        (TensorProduct.congr (totalTermEquiv C D n).symm (LinearEquiv.refl R M))))

@[simp] theorem totalCoefficientsEquiv_inclusion (M : Type*) [AddCommGroup M] [Module R M]
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n)
    (a : C.X p) (b : D.X q) (m : M) :
    totalCoefficientsEquiv M C D n
      ((HomologicalComplex.ιMapBifunctor (tensorCoefficients M C) D moduleTensor (.down ℕ)
        p q n h).hom ((a ⊗ₜ[R] m) ⊗ₜ[R] b)) =
      ((HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ) p q n h).hom
        (a ⊗ₜ[R] b)) ⊗ₜ[R] m := by
  dsimp only [totalCoefficientsEquiv, LinearEquiv.trans_apply]
  rw [totalTermEquiv_inclusion]
  erw [directSumEquiv_lof]
  rw [tensorMiddleSwap_tmul, TensorProduct.directSumLeft_symm_lof_tmul,
    TensorProduct.congr_tmul, totalTermEquiv_symm_lof, LinearEquiv.refl_apply]

/-- If the second complex has zero differential, so does the second part of
its total tensor differential. -/
theorem total_d₂_zero (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (hD : ∀ i j, D.d i j = 0)
    (p q n : ℕ) :
    HomologicalComplex.mapBifunctor.d₂ C D moduleTensor (.down ℕ) p q n = 0 := by
  cases q with
  | zero => exact HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by
      intro h; change _+1=0 at h; omega)
  | succ q =>
    rw [HomologicalComplex.mapBifunctor.d₂_eq' C D moduleTensor (.down ℕ) p
      (i₂ := q+1) (i₂' := q) rfl n, hD]
    simp

/-- The first differential alone remains when the second differential is zero. -/
@[reassoc] theorem inclusion_total_d_of_zero
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (hD : ∀ i j, D.d i j = 0)
    (p q n k : ℕ) (h : p+q=n) :
    HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ) p q n h ≫
      (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).d n k =
      HomologicalComplex.mapBifunctor.d₁ C D moduleTensor (.down ℕ) p q k := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    total_d₂_zero C D hD, add_zero]

/-- Moving coefficients is compatible with the total differential. -/
theorem totalCoefficientsEquiv_comm (M : Type*) [AddCommGroup M] [Module R M]
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (hD : ∀ i j, D.d i j = 0) (n : ℕ) :
    (totalCoefficientsEquiv M C D (n+1)).toModuleIso.hom ≫
        (tensorCoefficients M (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ))).d (n+1) n =
      (HomologicalComplex.mapBifunctor (tensorCoefficients M C) D moduleTensor (.down ℕ)).d (n+1) n ≫
        (totalCoefficientsEquiv M C D n).toModuleIso.hom := by
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := tensorCoefficients M C) (K₂ := D) (F := moduleTensor) (c := .down ℕ)
  intro p q h
  change p+q=n+1 at h
  rw [← Category.assoc, inclusion_total_d_of_zero_assoc _ _ hD]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro a m b
  change TensorProduct.map
      ((HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).d (n+1) n).hom
      LinearMap.id
      (totalCoefficientsEquiv M C D (n+1)
        ((HomologicalComplex.ιMapBifunctor (tensorCoefficients M C) D moduleTensor (.down ℕ)
          p q (n+1) h).hom ((a ⊗ₜ[R] m) ⊗ₜ[R] b))) =
    totalCoefficientsEquiv M C D n
      ((HomologicalComplex.mapBifunctor.d₁ (tensorCoefficients M C) D moduleTensor (.down ℕ)
        p q n).hom ((a ⊗ₜ[R] m) ⊗ₜ[R] b))
  rw [totalCoefficientsEquiv_inclusion, TensorProduct.map_tmul, LinearMap.id_apply]
  have hd := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (inclusion_total_d_of_zero C D hD p q (n+1) n h)) (a ⊗ₜ[R] b)
  change ((HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).d (n+1) n).hom
      ((HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ) p q (n+1) h).hom
        (a ⊗ₜ[R] b)) = _ at hd
  rw [hd]
  cases p with
  | zero =>
    rw [HomologicalComplex.mapBifunctor.d₁_eq_zero C D moduleTensor (.down ℕ) 0 q n
      (by intro h; change _+1=0 at h; omega),
      HomologicalComplex.mapBifunctor.d₁_eq_zero (tensorCoefficients M C) D moduleTensor
        (.down ℕ) 0 q n (by intro h; change _+1=0 at h; omega)]
    simp
  | succ p =>
    have hpq : p+q=n := by omega
    rw [HomologicalComplex.mapBifunctor.d₁_eq C D moduleTensor (.down ℕ)
        (i₁ := p+1) (i₁' := p) rfl q n hpq,
      HomologicalComplex.mapBifunctor.d₁_eq (tensorCoefficients M C) D moduleTensor (.down ℕ)
        (i₁ := p+1) (i₁' := p) rfl q n hpq]
    have hs : ComplexShape.ε₁ (.down ℕ) (.down ℕ) (.down ℕ) (p+1,q) = 1 := rfl
    rw [hs, one_smul, one_smul]
    change ((HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ) p q n hpq).hom
      ((C.d (p+1) p).hom a ⊗ₜ[R] b)) ⊗ₜ[R] m =
      totalCoefficientsEquiv M C D n
        ((HomologicalComplex.ιMapBifunctor (tensorCoefficients M C) D moduleTensor (.down ℕ)
          p q n hpq).hom (((C.d (p+1) p).hom a ⊗ₜ[R] m) ⊗ₜ[R] b))
    exact (totalCoefficientsEquiv_inclusion M C D p q n hpq _ b m).symm

/-- The coefficient distribution is an actual chain isomorphism. -/
def totalCoefficientsIso (M : Type*) [AddCommGroup M] [Module R M]
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (hD : ∀ i j, D.d i j = 0) :
    HomologicalComplex.mapBifunctor (tensorCoefficients M C) D moduleTensor (.down ℕ) ≅
      tensorCoefficients M (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (totalCoefficientsEquiv M C D n).toModuleIso)
    (fun i j hij => by
      have hi : j+1=i := hij
      subst i
      exact totalCoefficientsEquiv_comm M C D hD j)

/-- Identify the coefficient functor with the canonical list coefficient complex. -/
def coefficientListIso (M : Type v) [AddCommGroup M] [Module R M] (x : List R) :
    tensorCoefficients M (listComplex x) ≅ coefficientComplex M x :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (LinearEquiv.refl R ((⋀[R]^n (Fin x.length → R)) ⊗[R] M)).toModuleIso)
    (fun i j hij => by
      have hi : j+1=i := hij
      subst i
      rw [show (coefficientComplex M x).d (j+1) j =
        ModuleCat.ofHom (coefficientDifferential M x j) from by
          dsimp only [coefficientComplex]
          exact ChainComplex.of_d _ _ j]
      have hd : (tensorCoefficients M (listComplex x)).d (j+1) j =
          ModuleCat.ofHom (coefficientDifferential M x j) := by
        change ModuleCat.ofHom (((listComplex x).d (j+1) j).hom.rTensor M) = _
        rw [show (listComplex x).d (j+1) j = ModuleCat.ofHom (differential (listForm x) j)
          from complex_d _ _]
        rfl
      rw [hd]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      rfl)


/-- All differentials of the zero-form complex vanish, including the boundary degree. -/
theorem zeroComplex_d (s i j : ℕ) :
    (complex (0 : (Fin s → R) →ₗ[R] R)).d i j = 0 := by
  by_cases h : j+1=i
  · subst i
    rw [complex_d, zero_exterior_differential s j]
    rfl
  · exact (complex _).shape i j h

/-- Split the appended zero coordinates into the specified rank-s free module. -/
def splitZeroCoordinates (x : List R) (s : ℕ) :
    (Fin (x ++ List.replicate s (0 : R)).length → R) ≃ₗ[R]
      ((Fin x.length → R) × (Fin s → R)) :=
  (appendCoordinates x (List.replicate s (0 : R))).trans
    ((LinearEquiv.refl R _).prodCongr (zeroTailCoordinates s).symm)

theorem sumForm_splitZeroCoordinates (x : List R) (s : ℕ) :
    (sumForm (listForm x) (0 : (Fin s → R) →ₗ[R] R)).comp
      (splitZeroCoordinates x s).toLinearMap = listForm (x ++ List.replicate s 0) := by
  apply LinearMap.ext
  intro z
  change listForm x (appendCoordinates x (List.replicate s 0) z).1 + 0 = _
  rw [listForm_append, listForm_replicate_zero, LinearMap.zero_apply]

set_option maxHeartbeats 800000 in
/-- Coefficients commute with the zero-tail tensor decomposition for arbitrary M. -/
def zeroTailTensorIso (M : Type v) [AddCommGroup M] [Module R M] (x : List R) (s : ℕ) :
    coefficientComplex M (x ++ List.replicate s (0 : R)) ≅
      HomologicalComplex.mapBifunctor (coefficientComplex M x)
        (complex (0 : (Fin s → R) →ₗ[R] R)) moduleTensor (.down ℕ) := by
  let Z := complex (0 : (Fin s → R) →ₗ[R] R)
  let T := (moduleTensor.flip.obj (ModuleCat.of R M)).mapHomologicalComplex (.down ℕ)
  let e0 : listComplex (x ++ List.replicate s 0) ≅
      complex (sumForm (listForm x) (0 : (Fin s → R) →ₗ[R] R)) :=
    complexIso _ _ (splitZeroCoordinates x s) (sumForm_splitZeroCoordinates x s)
  let e1 := T.mapIso e0
  let e2 := T.mapIso (koszulTensorIso (listForm x) (0 : (Fin s → R) →ₗ[R] R)).symm
  let e3 := totalCoefficientsIso M (listComplex x) Z (zeroComplex_d s)
  let e4 : HomologicalComplex.mapBifunctor (tensorCoefficients M (listComplex x)) Z moduleTensor (.down ℕ) ≅
      HomologicalComplex.mapBifunctor (coefficientComplex M x) Z moduleTensor (.down ℕ) :=
    (((moduleTensor.{u, max u v, u} (R := R)).map₂HomologicalComplex
      (.down ℕ) (.down ℕ) (.down ℕ)).mapIso
      (coefficientListIso M x)).app Z
  exact (coefficientListIso M _).symm ≪≫ e1 ≪≫ e2 ≪≫ e3.symm ≪≫ e4

/-- Appending any redundant list gives the asserted coefficient tensor complex. -/
theorem redundant_tensor_iso : Specs.AdvCommAlg.Koszul.redundantTensorIso.{u,v} :=
  redundantTensor_of_zeroTail (by
    intro R _ M _ _ x s
    exact ⟨zeroTailTensorIso M x s⟩)

/-- Projection to a fixed bidegree of a tensor total term. -/
def totalProjection (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n) :
    (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).X n ⟶
      (moduleTensor.obj (C.X p)).obj (D.X q) :=
  ModuleCat.ofHom ((DirectSum.component R (DegreePairs n) (totalSummand C D) ⟨(p,q),h⟩).comp
    (totalTermToSum C D n))

@[reassoc (attr := simp)] theorem inclusion_totalProjection_self
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q n : ℕ) (h : p+q=n) :
    HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ) p q n h ≫
      totalProjection C D p q n h = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change DirectSum.component R (DegreePairs n) (totalSummand C D) ⟨(p,q),h⟩
    (totalTermToSum C D n
      ((HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ) p q n h).hom z)) = z
  rw [totalTermToSum_inclusion, DirectSum.component.lof_self]

@[reassoc] theorem inclusion_totalProjection_ne
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (p q a b n : ℕ)
    (h : p+q=n) (h' : a+b=n) (hne : (a,b) ≠ (p,q)) :
    HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ) a b n h' ≫
      totalProjection C D p q n h = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change DirectSum.component R (DegreePairs n) (totalSummand C D) ⟨(p,q),h⟩
    (totalTermToSum C D n
      ((HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ) a b n h').hom z)) = 0
  rw [totalTermToSum_inclusion, DirectSum.component.of]
  split_ifs with he
  · exact (hne (congrArg Subtype.val he)).elim
  · rfl

/-- The differential preserves the second bidegree when its differential is zero. -/
@[reassoc] theorem totalProjection_d
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (hD : ∀ i j, D.d i j = 0)
    (p q n : ℕ) (h : p+q=n) :
    (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).d (n+1) n ≫
      totalProjection C D p q n h =
      totalProjection C D (p+1) q (n+1) (by change p+1+q=n+1; omega) ≫
        (moduleTensor.map (C.d (p+1) p)).app (D.X q) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := C) (K₂ := D) (F := moduleTensor) (c := .down ℕ)
  intro a b hab
  change a+b=n+1 at hab
  rw [← Category.assoc, inclusion_total_d_of_zero C D hD]
  cases a with
  | zero =>
    rw [HomologicalComplex.mapBifunctor.d₁_eq_zero C D moduleTensor (.down ℕ) 0 b n
      (by intro h; change _+1=0 at h; omega), Limits.zero_comp,
      inclusion_totalProjection_ne_assoc C D (p+1) q 0 b (n+1) _ hab (by simp)]
    simp
  | succ a =>
    have hab' : a+b=n := by omega
    rw [HomologicalComplex.mapBifunctor.d₁_eq C D moduleTensor (.down ℕ)
      (i₁ := a+1) (i₁' := a) rfl b n hab']
    have hs : ComplexShape.ε₁ (.down ℕ) (.down ℕ) (.down ℕ) (a+1,b) = 1 := rfl
    rw [hs, one_smul, Category.assoc]
    by_cases ha : a=p
    · subst a
      have hb : b=q := by omega
      subst b
      simp
    · rw [inclusion_totalProjection_ne C D p q a b n h hab' (by
        intro he; exact ha (congrArg Prod.fst he)), Limits.comp_zero,
        inclusion_totalProjection_ne_assoc C D (p+1) q (a+1) b (n+1) _ hab (by
          intro he; have := congrArg Prod.fst he; simp at this; contradiction)]
      simp

/-- An explicit cycle-boundary criterion, also at degree zero. -/
theorem exactAt_module_iff (C : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    C.ExactAt n ↔ Function.Exact (C.d (n+1) n).hom (C.d n (n-1)).hom := by
  have hn : (ComplexShape.down ℕ).next n = n-1 := by
    cases n <;> simp
  rw [C.exactAt_iff' (n+1) n (n-1) (ChainComplex.prev ℕ n) hn,
    ShortComplex.moduleCat_exact_iff_range_eq_ker, LinearMap.exact_iff]
  exact eq_comm

theorem homology_nontrivial_iff_not_exact
    (C : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    Nontrivial (C.homology n) ↔ ¬ C.ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology,
    ModuleCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial]

/-- There are n+1 bidegrees in total degree n. -/
def degreePairsEquiv (n : ℕ) : DegreePairs n ≃ Fin (n+1) where
  toFun i := ⟨i.val.1, by have := i.property; omega⟩
  invFun i := ⟨(i.val,n-i.val), by have := i.isLt; omega⟩
  left_inv i := by apply Subtype.ext; apply Prod.ext <;> dsimp; have := i.property; omega
  right_inv i := by apply Fin.ext; rfl

instance (n : ℕ) : Fintype (DegreePairs n) := Fintype.ofEquiv (Fin (n+1)) (degreePairsEquiv n).symm

/-- Reconstruct a total term from its finitely many bidegree components. -/
theorem total_sum_projection
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (n : ℕ)
    (z : (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).X n) :
    (∑ i : DegreePairs n,
      (HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ)
        i.val.1 i.val.2 n i.property).hom
          ((totalProjection C D i.val.1 i.val.2 n i.property).hom z)) = z := by
  apply (totalTermEquiv C D n).injective
  rw [map_sum]
  simp only [totalTermEquiv_inclusion]
  apply DirectSum.ext_component R
  rintro ⟨⟨p,q⟩,h⟩
  simp only [map_sum]
  simp [DirectSum.component.of, totalProjection, totalTermEquiv]
  rfl

/-- On one bidegree the surviving differential is the first factor differential. -/
@[reassoc] theorem inclusion_total_d_succ
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (hD : ∀ i j, D.d i j = 0)
    (p q n : ℕ) (h : p+q=n) :
    HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ) (p+1) q (n+1) (by change p+1+q=n+1; omega) ≫
      (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).d (n+1) n =
      (moduleTensor.map (C.d (p+1) p)).app (D.X q) ≫
        HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ) p q n h := by
  rw [inclusion_total_d_of_zero C D hD,
    HomologicalComplex.mapBifunctor.d₁_eq C D moduleTensor (.down ℕ)
      (i₁ := p+1) (i₁' := p) rfl q n h]
  have hs : ComplexShape.ε₁ (.down ℕ) (.down ℕ) (.down ℕ) (p+1,q) = 1 := rfl
  rw [hs, one_smul]

/-- Exactness of a zero-second-differential total complex implies exactness of
its fixed second-degree summand, including in degree zero. -/
theorem tensorCoefficients_exactAt_of_total_exact
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (hD : ∀ i j, D.d i j = 0)
    (p q : ℕ)
    (ht : (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).ExactAt (p+q)) :
    (tensorCoefficients (D.X q) C).ExactAt p := by
  rw [exactAt_module_iff] at ht ⊢
  intro z
  constructor
  · intro hz
    let ι := HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ) p q (p+q) rfl
    have hz' : ((HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).d
        (p+q) (p+q-1)).hom (ι.hom z) = 0 := by
      have hd := inclusion_total_d_of_zero C D hD p q (p+q) (p+q-1) rfl
      change (ι ≫ (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).d
        (p+q) (p+q-1)).hom z = 0
      rw [hd]
      cases p with
      | zero =>
        rw [HomologicalComplex.mapBifunctor.d₁_eq_zero C D moduleTensor (.down ℕ)
          0 q (0+q-1) (by intro h; change _+1=0 at h; omega)]
        rfl
      | succ p =>
        rw [HomologicalComplex.mapBifunctor.d₁_eq C D moduleTensor (.down ℕ)
          (i₁ := p+1) (i₁' := p) rfl q (p+1+q-1) (by change p+q=p+1+q-1; omega)]
        have hs : ComplexShape.ε₁ (.down ℕ) (.down ℕ) (.down ℕ) (p+1,q) = 1 := rfl
        rw [hs, one_smul]
        change (HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ)
          p q (p+1+q-1) _).hom
            (((moduleTensor.map (C.d (p+1) p)).app (D.X q)).hom z) = 0
        have hz'' : ((moduleTensor.map (C.d (p+1) p)).app (D.X q)).hom z = 0 := by
          simpa using hz
        rw [hz'', map_zero]
    obtain ⟨w, hw⟩ := (ht (ι.hom z)).mp hz'
    refine ⟨(totalProjection C D (p+1) q (p+q+1) (by omega)).hom w, ?_⟩
    have hd := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (totalProjection_d C D hD p q (p+q) rfl)) w
    change (totalProjection C D p q (p+q) rfl).hom
        (((HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).d
          (p+q+1) (p+q)).hom w) = _ at hd
    rw [hw] at hd
    have hi := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (inclusion_totalProjection_self C D p q (p+q) rfl)) z
    change (totalProjection C D p q (p+q) rfl).hom (ι.hom z) = z at hi
    rw [hi] at hd
    exact hd.symm
  · rintro ⟨w, rfl⟩
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      ((tensorCoefficients (D.X q) C).d_comp_d (p+1) p (p-1))) w


/-- A total cycle has a cycle in each fixed second bidegree. -/
theorem totalProjection_cycle
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (hD : ∀ i j, D.d i j = 0)
    (p q n : ℕ) (h : p+q=n)
    (z : (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).X n)
    (hz : ((HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).d n (n-1)).hom z = 0) :
    ((moduleTensor.map (C.d p (p-1))).app (D.X q)).hom
      ((totalProjection C D p q n h).hom z) = 0 := by
  cases p with
  | zero =>
    rw [show C.d 0 (0-1) = 0 from C.shape _ _ (by simp)]
    simp
  | succ p =>
    cases n with
    | zero => omega
    | succ n =>
      have h' : p+q=n := by omega
      have hd := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (totalProjection_d C D hD p q n h')) z
      change (totalProjection C D p q n h').hom
        (((HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).d (n+1) n).hom z) =
        ((moduleTensor.map (C.d (p+1) p)).app (D.X q)).hom
          ((totalProjection C D (p+1) q (n+1) h).hom z) at hd
      change ((HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).d (n+1) n).hom z = 0 at hz
      change ((moduleTensor.map (C.d (p+1) p)).app (D.X q)).hom
        ((totalProjection C D (p+1) q (n+1) h).hom z) = 0
      rw [hz, map_zero] at hd
      exact hd.symm

/-- If every contributing tensor column is exact, the total complex is exact. -/
theorem total_exactAt_of_columns
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : ChainComplex (ModuleCat.{w} R) ℕ) (hD : ∀ i j, D.d i j = 0)
    (n : ℕ)
    (hc : ∀ p q : ℕ, p+q=n →
      Function.Exact ((moduleTensor.map (C.d (p+1) p)).app (D.X q)).hom
        ((moduleTensor.map (C.d p (p-1))).app (D.X q)).hom) :
    (HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)).ExactAt n := by
  classical
  let T := HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)
  rw [exactAt_module_iff]
  apply Function.Exact.of_comp_of_mem_range
  · funext y
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (T.d_comp_d (n+1) n (n-1))) y
  · intro z hz
    have hi (i : DegreePairs n) : ∃ b : C.X (i.val.1+1) ⊗[R] D.X i.val.2,
        ((moduleTensor.map (C.d (i.val.1+1) i.val.1)).app (D.X i.val.2)).hom b =
          (totalProjection C D i.val.1 i.val.2 n i.property).hom z :=
      (hc i.val.1 i.val.2 i.property _).mp
        (totalProjection_cycle C D hD i.val.1 i.val.2 n i.property z hz)
    choose b hb using hi
    refine ⟨∑ i : DegreePairs n,
      (HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ)
        (i.val.1+1) i.val.2 (n+1) (by have := i.property; change i.val.1+1+i.val.2=n+1; omega)).hom
          (b i), ?_⟩
    rw [map_sum]
    calc
      _ = ∑ i : DegreePairs n,
          (HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ)
            i.val.1 i.val.2 n i.property).hom
              ((totalProjection C D i.val.1 i.val.2 n i.property).hom z) := by
        apply Finset.sum_congr rfl
        intro i _
        have hd := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
          (inclusion_total_d_succ C D hD i.val.1 i.val.2 n i.property)) (b i)
        exact hd.trans (congrArg
          (fun x => (HomologicalComplex.ιMapBifunctor C D moduleTensor (.down ℕ)
            i.val.1 i.val.2 n i.property).hom x) (hb i))
      _ = z := total_sum_projection C D n z

theorem exact_rTensor_of_exactAt
    (C : ChainComplex (ModuleCat.{v} R) ℕ) (p : ℕ) (hp : C.ExactAt p)
    (A : Type w) [AddCommGroup A] [Module R A] [Module.Free R A] :
    Function.Exact ((C.d (p+1) p).hom.rTensor A) ((C.d p (p-1)).hom.rTensor A) :=
  Module.Flat.rTensor_exact A ((exactAt_module_iff C p).mp hp)

def tensorUnitEquiv (A : Type w) [AddCommGroup A] [Module R A]
    (e : A ≃ₗ[R] R) (N : Type w₁) [AddCommGroup N] [Module R N] :
    N ⊗[R] A ≃ₗ[R] N :=
  (TensorProduct.congr (LinearEquiv.refl R N) e).trans (TensorProduct.rid R N)

@[simp] theorem tensorUnitEquiv_tmul
    {A : Type w} [AddCommGroup A] [Module R A]
    (e : A ≃ₗ[R] R) {N : Type w₁} [AddCommGroup N] [Module R N] (n : N) (a : A) :
    tensorUnitEquiv A e N (n ⊗ₜ[R] a) = e a • n := rfl

theorem tensorUnitEquiv_naturality
    {A : Type w} [AddCommGroup A] [Module R A]
    (e : A ≃ₗ[R] R) {N : Type w₁} {N' : Type w₂}
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') :
    f.comp (tensorUnitEquiv A e N).toLinearMap =
      (tensorUnitEquiv A e N').toLinearMap.comp (f.rTensor A) := by
  apply TensorProduct.ext'
  intro n a
  simp

theorem exact_rTensor_iff_of_equiv_ring
    {A : Type w} [AddCommGroup A] [Module R A] (e : A ≃ₗ[R] R)
    {N : Type w₁} {N' : Type w₂} {N'' : Type w₃}
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    [AddCommGroup N''] [Module R N'']
    (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') :
    Function.Exact (f.rTensor A) (g.rTensor A) ↔ Function.Exact f g := by
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (tensorUnitEquiv_naturality e f) (tensorUnitEquiv_naturality e g)).symm

theorem exact_rTensor_iff_exactAt_of_equiv_ring
    (C : ChainComplex (ModuleCat.{v} R) ℕ) (p : ℕ)
    {A : Type w} [AddCommGroup A] [Module R A] (e : A ≃ₗ[R] R) :
    Function.Exact ((C.d (p+1) p).hom.rTensor A) ((C.d p (p-1)).hom.rTensor A) ↔
      C.ExactAt p := by
  rw [exact_rTensor_iff_of_equiv_ring e, exactAt_module_iff]


theorem exteriorTerm_vanish (s j : ℕ) (hsj : s < j) :
    Subsingleton (⋀[R]^j (Fin s → R)) := by
  apply exteriorPower.subsingleton_of_span_eq_top_of_card_lt
    (Pi.basisFun R (Fin s)) (Module.Basis.span_eq _) j
  simpa using hsj

def exteriorTopEquiv (s : ℕ) : (⋀[R]^s (Fin s → R)) ≃ₗ[R] R := by
  classical
  letI : Unique (Set.powersetCard (Fin s) s) :=
    { default := ⟨Finset.univ, by simp⟩
      uniq t := Subtype.ext <| Finset.eq_univ_of_card _ <| by simpa using t.prop }
  exact ((Pi.basisFun R (Fin s)).exteriorPower s).equivFun.trans
    (LinearEquiv.funUnique (Set.powersetCard (Fin s) s) R R)


/-- Tensoring with the zero exterior complex raises the largest nonzero
homology degree by its rank, without assumptions on the terms of C. -/
theorem zeroExterior_greatest
    (C : ChainComplex (ModuleCat.{v} R) ℕ) (s t : ℕ)
    (ht : IsGreatest {q : ℕ | Nontrivial (C.homology q)} t) :
    IsGreatest {q : ℕ | Nontrivial
      ((HomologicalComplex.mapBifunctor C
        (complex (0 : (Fin s → R) →ₗ[R] R)) moduleTensor (.down ℕ)).homology q)}
      (t+s) := by
  classical
  let D := complex (0 : (Fin s → R) →ₗ[R] R)
  let T := HomologicalComplex.mapBifunctor C D moduleTensor (.down ℕ)
  change IsGreatest {q : ℕ | Nontrivial (T.homology q)} (t+s)
  constructor
  · change Nontrivial (T.homology (t+s))
    rw [homology_nontrivial_iff_not_exact]
    intro hT
    have hcol := tensorCoefficients_exactAt_of_total_exact C D (zeroComplex_d s) t s hT
    have hc : C.ExactAt t :=
      (exact_rTensor_iff_exactAt_of_equiv_ring C t (exteriorTopEquiv (R := R) s)).mp
        ((exactAt_module_iff _ _).mp hcol)
    exact ((homology_nontrivial_iff_not_exact C t).mp ht.1) hc
  · intro n hn
    by_contra hbound
    have hhi : t+s < n := by omega
    apply ((homology_nontrivial_iff_not_exact T n).mp hn)
    apply total_exactAt_of_columns C D (zeroComplex_d s) n
    intro p q hpq
    by_cases hq : s < q
    · have hD : Subsingleton (D.X q) := exteriorTerm_vanish s q hq
      have hm : Subsingleton (C.X p ⊗[R] D.X q) := inferInstance
      have ho : Subsingleton (C.X (p-1) ⊗[R] D.X q) := inferInstance
      intro z
      constructor
      · intro _
        exact ⟨0, by simpa only [map_zero] using (hm.elim 0 z)⟩
      · intro _
        exact ho.elim _ _
    · have hp : t < p := by omega
      have hex : C.ExactAt p := by
        by_contra hn'
        have hnt : Nontrivial (C.homology p) :=
          (homology_nontrivial_iff_not_exact C p).mpr hn'
        have := ht.2 hnt
        omega
      change Function.Exact ((C.d (p+1) p).hom.rTensor (⋀[R]^q (Fin s → R)))
        ((C.d p (p-1)).hom.rTensor (⋀[R]^q (Fin s → R)))
      exact exact_rTensor_of_exactAt C p hex (⋀[R]^q (Fin s → R))

/-- RK-06: the exact shift in the largest nonzero homology degree. -/
theorem redundant_homology_greatest :
    Specs.AdvCommAlg.Koszul.redundantHomologyGreatest.{u,v} :=
  redundantGreatest_of_tensor redundant_tensor_iso (by
    intro R _ C s t ht
    exact zeroExterior_greatest C s t ht)

/-- RK-06: length minus highest nonzero homology degree depends only on I and M. -/
theorem generator_threshold_invariant :
    Specs.AdvCommAlg.Koszul.generatorThresholdInvariant.{u,v} :=
  thresholdInvariant_of_shift redundant_homology_greatest

end AdvCommAlg.Koszul
