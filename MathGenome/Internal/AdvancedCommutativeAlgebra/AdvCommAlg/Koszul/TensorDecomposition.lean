import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.TensorDecomposition
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Construction
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.CategoryTheory.Linear.Basic

open scoped TensorProduct DirectSum
open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w

namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]
variable {E : Type v} [AddCommGroup E] [Module R E]
variable {F : Type w} [AddCommGroup F] [Module R F]

@[simp] theorem sumForm_apply (f : E →ₗ[R] R) (g : F →ₗ[R] R) (x : E × F) :
    sumForm f g x = f x.1 + g x.2 := rfl

/-- The two inclusions intertwine contraction with the corresponding summand form. -/
theorem contraction_inl (f : E →ₗ[R] R) (g : F →ₗ[R] R) (a : ExteriorAlgebra R E) :
    contraction (sumForm f g) (ExteriorAlgebra.map (LinearMap.inl R E F) a) =
      ExteriorAlgebra.map (LinearMap.inl R E F) (contraction f a) :=
  contraction_map f (sumForm f g) _ (by ext; simp [sumForm]) a

theorem contraction_inr (f : E →ₗ[R] R) (g : F →ₗ[R] R) (b : ExteriorAlgebra R F) :
    contraction (sumForm f g) (ExteriorAlgebra.map (LinearMap.inr R E F) b) =
      ExteriorAlgebra.map (LinearMap.inr R E F) (contraction g b) :=
  contraction_map g (sumForm f g) _ (by ext; simp [sumForm]) b

@[simp] theorem tensorExteriorProduct_tmul_coe (p q : ℕ)
    (a : ⋀[R]^p E) (b : ⋀[R]^q F) :
    (tensorExteriorProduct p q (a ⊗ₜ[R] b) : ExteriorAlgebra R (E × F)) =
      ExteriorAlgebra.map (LinearMap.inl R E F) a *
        ExteriorAlgebra.map (LinearMap.inr R E F) b := by
  simp only [tensorExteriorProduct, TensorProduct.lift.tmul,
    LinearMap.coe_mk, AddHom.coe_mk, exteriorPower.coe_map]

/-- This is the signed tensor differential, before restricting its target degree. -/
theorem contraction_tensorExteriorProduct (f : E →ₗ[R] R) (g : F →ₗ[R] R)
    (p q : ℕ) (a : ⋀[R]^p E) (b : ⋀[R]^q F) :
    contraction (sumForm f g) (tensorExteriorProduct p q (a ⊗ₜ[R] b)) =
      ExteriorAlgebra.map (LinearMap.inl R E F) (contraction f a) *
          ExteriorAlgebra.map (LinearMap.inr R E F) b +
        (-1 : R)^p • (ExteriorAlgebra.map (LinearMap.inl R E F) a *
          ExteriorAlgebra.map (LinearMap.inr R E F) (contraction g b)) := by
  rw [tensorExteriorProduct_tmul_coe]
  rw [contraction_leibniz (sumForm f g) p _ _
    (by simpa only [exteriorPower.coe_map] using
      (exteriorPower.map p (LinearMap.inl R E F) a).property)]
  rw [contraction_inl, contraction_inr]

private def zeroProdIsometry :
    (0 : QuadraticForm R (E × F)).IsometryEquiv
      ((0 : QuadraticForm R E).prod (0 : QuadraticForm R F)) where
  toLinearEquiv := LinearEquiv.refl R (E × F)
  map_app' x := by simp

/-- Ungraded underlying-module decomposition, valid over arbitrary commutative rings.
It is obtained from the graded tensor product of the zero Clifford forms. -/
def exteriorTensorEquiv : ExteriorAlgebra R (E × F) ≃ₗ[R]
    (ExteriorAlgebra R E ⊗[R] ExteriorAlgebra R F) :=
  ((CliffordAlgebra.equivOfIsometry zeroProdIsometry).toLinearEquiv.trans
    (CliffordAlgebra.prodEquiv (0 : QuadraticForm R E)
      (0 : QuadraticForm R F)).toLinearEquiv).trans
    (GradedTensorProduct.of R (CliffordAlgebra.evenOdd (0 : QuadraticForm R E))
      (CliffordAlgebra.evenOdd (0 : QuadraticForm R F))).symm

/-- The inverse of the module equivalence is exterior multiplication. -/
theorem exteriorTensorEquiv_symm_tmul (a : ExteriorAlgebra R E)
    (b : ExteriorAlgebra R F) :
    exteriorTensorEquiv.symm (a ⊗ₜ[R] b) =
      ExteriorAlgebra.map (LinearMap.inl R E F) a *
        ExteriorAlgebra.map (LinearMap.inr R E F) b := by
  have hl : (CliffordAlgebra.equivOfIsometry (zeroProdIsometry (R := R)
      (E := E) (F := F))).symm.toAlgHom.comp
        (CliffordAlgebra.map (QuadraticMap.Isometry.inl
          (0 : QuadraticForm R E) (0 : QuadraticForm R F))) =
      ExteriorAlgebra.map (LinearMap.inl R E F) := by
    ext e
    simp [CliffordAlgebra.equivOfIsometry, zeroProdIsometry]
    rfl
  have hr : (CliffordAlgebra.equivOfIsometry (zeroProdIsometry (R := R)
      (E := E) (F := F))).symm.toAlgHom.comp
        (CliffordAlgebra.map (QuadraticMap.Isometry.inr
          (0 : QuadraticForm R E) (0 : QuadraticForm R F))) =
      ExteriorAlgebra.map (LinearMap.inr R E F) := by
    ext e
    simp [CliffordAlgebra.equivOfIsometry, zeroProdIsometry]
    rfl
  simp only [exteriorTensorEquiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, ← AlgEquiv.toLinearEquiv_symm, AlgEquiv.toLinearEquiv_apply]
  rw [CliffordAlgebra.prodEquiv_symm_apply, CliffordAlgebra.toProd,
    GradedTensorProduct.lift_tmul, map_mul]
  exact congrArg₂ (· * ·) (AlgHom.congr_fun hl a) (AlgHom.congr_fun hr b)

theorem exteriorTensorEquiv_tensorExteriorProduct (p q : ℕ)
    (a : ⋀[R]^p E) (b : ⋀[R]^q F) :
    exteriorTensorEquiv (tensorExteriorProduct p q (a ⊗ₜ[R] b)) =
      (a : ExteriorAlgebra R E) ⊗ₜ[R] (b : ExteriorAlgebra R F) := by
  apply exteriorTensorEquiv.symm.injective
  simp [exteriorTensorEquiv_symm_tmul]

/-- Multiplication into a specified total degree. -/
def tensorExteriorProductTo (p q n : ℕ) (h : p+q=n) :
    ((⋀[R]^p E) ⊗[R] (⋀[R]^q F)) →ₗ[R] (⋀[R]^n (E × F)) := by
  subst n
  exact tensorExteriorProduct p q

@[simp] theorem tensorExteriorProductTo_coe (p q n : ℕ) (h : p+q=n)
    (a : ⋀[R]^p E) (b : ⋀[R]^q F) :
    (tensorExteriorProductTo p q n h (a ⊗ₜ[R] b) : ExteriorAlgebra R (E × F)) =
      ExteriorAlgebra.map (LinearMap.inl R E F) a *
        ExteriorAlgebra.map (LinearMap.inr R E F) b := by
  subst n
  exact tensorExteriorProduct_tmul_coe p q a b

/-- The canonical multiplication map on a term of the total complex. -/
def tensorComparisonComponent (f : E →ₗ[R] R) (g : F →ₗ[R] R) (n : ℕ) :
    (tensorTotal f g).X n ⟶ (complex (sumForm f g)).X n :=
  HomologicalComplex.mapBifunctorDesc (fun p q h =>
    ModuleCat.ofHom (tensorExteriorProductTo p q n h))

@[reassoc (attr := simp)] theorem tensorInclusion_comparison
    (f : E →ₗ[R] R) (g : F →ₗ[R] R) (p q n : ℕ) (h : p+q=n) :
    tensorInclusion f g p q n h ≫ tensorComparisonComponent f g n =
      ModuleCat.ofHom (tensorExteriorProductTo p q n h) :=
  HomologicalComplex.ι_mapBifunctorDesc _ p q h

@[simp] theorem tensorComparisonComponent_inclusion_apply
    (f : E →ₗ[R] R) (g : F →ₗ[R] R) (p q n : ℕ) (h : p+q=n)
    (z : (⋀[R]^p E) ⊗[R] (⋀[R]^q F)) :
    (tensorComparisonComponent f g n).hom ((tensorInclusion f g p q n h).hom z) =
      tensorExteriorProductTo p q n h z := by
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (tensorInclusion_comparison f g p q n h)) z

private abbrev TensorBidegree (R : Type u) [CommRing R]
    (E : Type v) [AddCommGroup E] [Module R E]
    (F : Type w) [AddCommGroup F] [Module R F] (i : ℕ × ℕ) :=
  (⋀[R]^i.1 E) ⊗[R] (⋀[R]^i.2 F)

private instance tensorBidegreeGroup (i : ℕ × ℕ) :
    AddCommGroup (TensorBidegree R E F i) := TensorProduct.addCommGroup

/-- Regrouping all bidegrees by their total degrees. -/
private def bidegreesToTotal (f : E →ₗ[R] R) (g : F →ₗ[R] R) :
    (⨁ i : ℕ × ℕ, TensorBidegree R E F i) →ₗ[R] ⨁ n, (tensorTotal f g).X n :=
  DirectSum.toModule R _ _ (fun i =>
    (DirectSum.lof R ℕ (fun n => (tensorTotal f g).X n) (i.1+i.2)).comp
      (tensorInclusion f g i.1 i.2 (i.1+i.2) rfl).hom)

private def totalToBidegrees (f : E →ₗ[R] R) (g : F →ₗ[R] R) :
    (⨁ n, (tensorTotal f g).X n) →ₗ[R] ⨁ i : ℕ × ℕ, TensorBidegree R E F i :=
  DirectSum.toModule R _ _ (fun n =>
    (HomologicalComplex.mapBifunctorDesc (K₁ := complex f) (K₂ := complex g)
      (F := moduleTensor) (c := .down ℕ) (j := n)
      (A := ModuleCat.of R (⨁ i : ℕ × ℕ, TensorBidegree R E F i)) (fun p q _ =>
        ModuleCat.ofHom (DirectSum.lof R (ℕ × ℕ) (TensorBidegree R E F) (p,q)))).hom)

@[simp] private theorem totalToBidegrees_lof_inclusion
    (f : E →ₗ[R] R) (g : F →ₗ[R] R) (p q n : ℕ) (h : p+q=n)
    (z : (⋀[R]^p E) ⊗[R] (⋀[R]^q F)) :
    totalToBidegrees f g (DirectSum.lof R ℕ (fun n => (tensorTotal f g).X n) n
      ((tensorInclusion f g p q n h).hom z)) =
      DirectSum.lof R (ℕ × ℕ) (TensorBidegree R E F) (p,q) z := by
  simp only [totalToBidegrees, DirectSum.toModule_lof]
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (HomologicalComplex.ι_mapBifunctorDesc
      (K₁ := complex f) (K₂ := complex g) (F := moduleTensor) (c := .down ℕ)
      (A := ModuleCat.of R (⨁ i : ℕ × ℕ, TensorBidegree R E F i))
      (fun p q _ => ModuleCat.ofHom
        (DirectSum.lof R (ℕ × ℕ) (TensorBidegree R E F) (p,q))) p q h)) z

private theorem bidegreesToTotal_comp (f : E →ₗ[R] R) (g : F →ₗ[R] R) :
    (bidegreesToTotal f g).comp (totalToBidegrees f g) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro n
  apply congrArg ModuleCat.Hom.hom (α :=
    (tensorTotal f g).X n ⟶ ModuleCat.of R (⨁ n, (tensorTotal f g).X n))
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := complex f) (K₂ := complex g) (F := moduleTensor) (c := .down ℕ)
  intro p q h
  subst n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change bidegreesToTotal f g (totalToBidegrees f g
      (DirectSum.lof R ℕ (fun n => (tensorTotal f g).X n) (p+q)
        ((tensorInclusion f g p q (p+q) rfl).hom z))) = _
  rw [totalToBidegrees_lof_inclusion]
  simp [bidegreesToTotal]
  rfl

private theorem totalToBidegrees_comp (f : E →ₗ[R] R) (g : F →ₗ[R] R) :
    (totalToBidegrees f g).comp (bidegreesToTotal f g) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  rintro ⟨p,q⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, bidegreesToTotal,
    DirectSum.toModule_lof, LinearMap.comp_apply, LinearMap.id_apply]
  exact totalToBidegrees_lof_inclusion f g p q (p+q) rfl (a ⊗ₜ[R] b)

private def bidegreesTotalEquiv (f : E →ₗ[R] R) (g : F →ₗ[R] R) :
    (⨁ i : ℕ × ℕ, TensorBidegree R E F i) ≃ₗ[R] ⨁ n, (tensorTotal f g).X n :=
  LinearEquiv.ofLinearMap (bidegreesToTotal f g) (totalToBidegrees f g)
    (bidegreesToTotal_comp f g) (totalToBidegrees_comp f g)

/-- Distributing tensor products over the exterior gradings. -/
private def bidegreesTensorEquiv :
    (⨁ i : ℕ × ℕ, TensorBidegree R E F i) ≃ₗ[R]
      (ExteriorAlgebra R E ⊗[R] ExteriorAlgebra R F) :=
  (TensorProduct.directSum R R (fun p => ⋀[R]^p E) (fun q => ⋀[R]^q F)).symm.trans
    (TensorProduct.congr (DirectSum.decomposeLinearEquiv (fun p => ⋀[R]^p E)).symm
      (DirectSum.decomposeLinearEquiv (fun q => ⋀[R]^q F)).symm)

@[simp] private theorem bidegreesTensorEquiv_lof (p q : ℕ)
    (a : ⋀[R]^p E) (b : ⋀[R]^q F) :
    bidegreesTensorEquiv
      (DirectSum.lof R (ℕ × ℕ) (TensorBidegree R E F) (p,q) (a ⊗ₜ[R] b)) =
      (a : ExteriorAlgebra R E) ⊗ₜ[R] (b : ExteriorAlgebra R F) := by
  simp [bidegreesTensorEquiv]

private theorem comparison_all_degrees (f : E →ₗ[R] R) (g : F →ₗ[R] R) :
    (DirectSum.decomposeLinearEquiv (fun n => ⋀[R]^n (E × F))).symm.toLinearMap.comp
      (DirectSum.lmap (fun n => (tensorComparisonComponent f g n).hom)) =
    (exteriorTensorEquiv.symm.toLinearMap.comp
      (bidegreesTensorEquiv.toLinearMap.comp (bidegreesTotalEquiv f g).symm.toLinearMap)) := by
  apply (LinearMap.cancel_right (bidegreesTotalEquiv f g).surjective).mp
  apply DirectSum.linearMap_ext
  rintro ⟨p,q⟩
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_apply]
  simp only [bidegreesTotalEquiv, LinearEquiv.coe_ofLinearMap, bidegreesToTotal,
    DirectSum.toModule_lof, LinearMap.comp_apply, DirectSum.lmap_lof,
    DirectSum.decomposeLinearEquiv_symm_lof]
  trans (tensorExteriorProductTo p q (p+q) rfl (a ⊗ₜ[R] b) : ExteriorAlgebra R (E × F))
  · exact congrArg Subtype.val (tensorComparisonComponent_inclusion_apply f g p q (p+q) rfl
      (a ⊗ₜ[R] b))
  · rw [bidegreesTensorEquiv_lof, exteriorTensorEquiv_symm_tmul]
    exact tensorExteriorProductTo_coe p q (p+q) rfl a b

/-- Every homogeneous component of the multiplication map is invertible. -/
theorem tensorComparisonComponent_bijective (f : E →ₗ[R] R) (g : F →ₗ[R] R) (n : ℕ) :
    Function.Bijective (tensorComparisonComponent f g n).hom := by
  have h := comparison_all_degrees f g
  have hb : Function.Bijective (DirectSum.lmap (fun n => (tensorComparisonComponent f g n).hom)) := by
    have he : Function.Bijective
        ((DirectSum.decomposeLinearEquiv (fun n => ⋀[R]^n (E × F))).symm.toLinearMap.comp
          (DirectSum.lmap (fun n => (tensorComparisonComponent f g n).hom))) := by
      rw [h]
      exact exteriorTensorEquiv.symm.bijective.comp
        (bidegreesTensorEquiv.bijective.comp (bidegreesTotalEquiv f g).symm.bijective)
    let d := (DirectSum.decomposeLinearEquiv (fun n => ⋀[R]^n (E × F))).symm
    refine ⟨fun x y hxy => he.injective (congrArg d hxy), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := he.surjective (d y)
    exact ⟨x, d.injective hx⟩
  exact ⟨(DirectSum.lmap_injective _).mp hb.injective n,
    (DirectSum.lmap_surjective _).mp hb.surjective n⟩

@[simp] theorem contraction_degree_zero (f : E →ₗ[R] R) (a : ⋀[R]^0 E) :
    contraction f a = 0 := by
  obtain ⟨r, rfl⟩ := (exteriorPower.zeroEquiv R E).symm.surjective a
  simp [exteriorPower.zeroEquiv_symm_apply]

private theorem tensorSign_smul {M : Type*} [AddCommGroup M] [Module R M]
    (p : ℕ) (x : M) : ((-1 : ℤˣ)^p) • x = (-1 : R)^p • x := by
  induction p with
  | zero => simp
  | succ p ih => simp [pow_succ, ih, Units.neg_smul]

private theorem comparison_d₁ (f : E →ₗ[R] R) (g : F →ₗ[R] R)
    (p q n : ℕ) (h : p+q=n+1) (a : ⋀[R]^p E) (b : ⋀[R]^q F) :
    Subtype.val (((HomologicalComplex.mapBifunctor.d₁ (complex f) (complex g) moduleTensor (.down ℕ)
        p q n ≫ tensorComparisonComponent f g n).hom (a ⊗ₜ[R] b)) : ⋀[R]^n (E × F)) =
      ExteriorAlgebra.map (LinearMap.inl R E F) (contraction f a) *
        ExteriorAlgebra.map (LinearMap.inr R E F) b := by
  cases p with
  | zero =>
    rw [HomologicalComplex.mapBifunctor.d₁_eq_zero (complex f) (complex g) moduleTensor (.down ℕ) 0 q n (by
      intro h; change _ + 1 = 0 at h; omega)]
    simp
  | succ p =>
    have hpq : p+q=n := by omega
    rw [HomologicalComplex.mapBifunctor.d₁_eq (complex f) (complex g) moduleTensor (.down ℕ)
      (i₁ := p+1) (i₁' := p) rfl q n hpq]
    have hs : ComplexShape.ε₁ (.down ℕ) (.down ℕ) (.down ℕ) (p+1,q) = 1 := rfl
    rw [hs, one_smul]
    change Subtype.val (((((moduleTensor.map ((complex f).d (p+1) p)).app ((complex g).X q)) ≫
      tensorInclusion f g p q n hpq) ≫ tensorComparisonComponent f g n).hom
        (a ⊗ₜ[R] b) : ⋀[R]^n (E × F)) = _
    rw [Category.assoc, tensorInclusion_comparison, complex_d]
    change (tensorExteriorProductTo p q n hpq
      ((differential f p a) ⊗ₜ[R] b) : ExteriorAlgebra R (E × F)) = _
    rw [tensorExteriorProductTo_coe, differential_coe]

private theorem comparison_d₂ (f : E →ₗ[R] R) (g : F →ₗ[R] R)
    (p q n : ℕ) (h : p+q=n+1) (a : ⋀[R]^p E) (b : ⋀[R]^q F) :
    Subtype.val (((HomologicalComplex.mapBifunctor.d₂ (complex f) (complex g) moduleTensor (.down ℕ)
        p q n ≫ tensorComparisonComponent f g n).hom (a ⊗ₜ[R] b)) : ⋀[R]^n (E × F)) =
      (-1 : R)^p • (ExteriorAlgebra.map (LinearMap.inl R E F) a *
        ExteriorAlgebra.map (LinearMap.inr R E F) (contraction g b)) := by
  cases q with
  | zero =>
    rw [HomologicalComplex.mapBifunctor.d₂_eq_zero (complex f) (complex g) moduleTensor (.down ℕ) p 0 n (by
      intro h; change _ + 1 = 0 at h; omega)]
    simp
  | succ q =>
    have hpq : p+q=n := by omega
    rw [HomologicalComplex.mapBifunctor.d₂_eq (complex f) (complex g) moduleTensor (.down ℕ)
      p (i₂ := q+1) (i₂' := q) rfl n hpq]
    change Subtype.val (((((-1 : ℤˣ)^p) •
      (((moduleTensor.obj ((complex f).X p)).map ((complex g).d (q+1) q)) ≫
        tensorInclusion f g p q n hpq)) ≫ tensorComparisonComponent f g n).hom
          (a ⊗ₜ[R] b) : ⋀[R]^n (E × F)) = _
    rw [CategoryTheory.Linear.units_smul_comp, Category.assoc, tensorInclusion_comparison, complex_d]
    simp only [Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, LinearMap.comp_apply]
    change (((-1 : ℤˣ)^p) •
      (tensorExteriorProductTo p q n hpq (a ⊗ₜ[R] (differential g q b)) :
        ExteriorAlgebra R (E × F))) = _
    rw [tensorSign_smul (R := R), tensorExteriorProductTo_coe, differential_coe]

/-- Multiplication intertwines the total differential with contraction. -/
theorem tensorComparisonComponent_comm (f : E →ₗ[R] R) (g : F →ₗ[R] R) (n : ℕ) :
    tensorComparisonComponent f g (n+1) ≫ (complex (sumForm f g)).d (n+1) n =
      (tensorTotal f g).d (n+1) n ≫ tensorComparisonComponent f g n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := complex f) (K₂ := complex g) (F := moduleTensor) (c := .down ℕ)
  intro p q h
  rw [← Category.assoc, tensorInclusion_comparison]
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp,
    Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, ModuleCat.hom_comp,
    ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_ofHom, LinearMap.comp_apply]
  rw [complex_d]
  change contraction (sumForm f g) (tensorExteriorProductTo p q (n+1) h (a ⊗ₜ[R] b)) = _
  rw [tensorExteriorProductTo_coe]
  rw [contraction_leibniz (sumForm f g) p _ _ (by
    simpa only [exteriorPower.coe_map] using
      (exteriorPower.map p (LinearMap.inl R E F) a).property), contraction_inl, contraction_inr]
  exact congrArg₂ (· + ·) (comparison_d₁ f g p q n h a b).symm
    (comparison_d₂ f g p q n h a b).symm

/-- The direct-sum isomorphism, oriented from the tensor total complex to the
Koszul complex of the direct sum. -/
def koszulTensorIso (f : E →ₗ[R] R) (g : F →ₗ[R] R) :
    tensorTotal f g ≅ complex (sumForm f g) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (LinearEquiv.ofBijective (tensorComparisonComponent f g n).hom
      (tensorComparisonComponent_bijective f g n)).toModuleIso)
    (fun i j hij => by
      have hi : j+1=i := hij
      subst i
      exact tensorComparisonComponent_comm f g j)

/-- RK-05: the isomorphism is exterior multiplication in every bidegree. -/
theorem tensor_decomposition : Specs.AdvCommAlg.Koszul.tensorDecomposition.{u,v,w} := by
  intro R _ E _ _ F _ _ f g
  refine ⟨koszulTensorIso f g, ?_⟩
  intro p q a b
  exact tensorComparisonComponent_inclusion_apply f g p q (p+q) rfl (a ⊗ₜ[R] b)

/-- Exterior multiplication is natural in both summands. -/
theorem tensorExteriorProduct_natural {E' : Type v} [AddCommGroup E'] [Module R E']
    {F' : Type w} [AddCommGroup F'] [Module R F']
    (φ : E →ₗ[R] E') (ψ : F →ₗ[R] F') (p q : ℕ)
    (a : ⋀[R]^p E) (b : ⋀[R]^q F) :
    exteriorPower.map (p+q) (φ.prodMap ψ) (tensorExteriorProduct p q (a ⊗ₜ[R] b)) =
      tensorExteriorProduct p q ((exteriorPower.map p φ a) ⊗ₜ[R] (exteriorPower.map q ψ b)) := by
  have hl : (ExteriorAlgebra.map (φ.prodMap ψ)).comp
        (ExteriorAlgebra.map (LinearMap.inl R E F)) =
      (ExteriorAlgebra.map (LinearMap.inl R E' F')).comp (ExteriorAlgebra.map φ) := by
    rw [ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map]
    congr 1
    ext e <;> simp
  have hr : (ExteriorAlgebra.map (φ.prodMap ψ)).comp
        (ExteriorAlgebra.map (LinearMap.inr R E F)) =
      (ExteriorAlgebra.map (LinearMap.inr R E' F')).comp (ExteriorAlgebra.map ψ) := by
    rw [ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map]
    congr 1
    ext e <;> simp
  apply Subtype.ext
  simp only [exteriorPower.coe_map, tensorExteriorProduct_tmul_coe, map_mul]
  exact congrArg₂ (· * ·) (AlgHom.congr_fun hl a) (AlgHom.congr_fun hr b)

private theorem tensorComparisonComponent_natural {E' : Type v}
    [AddCommGroup E'] [Module R E'] {F' : Type w} [AddCommGroup F'] [Module R F']
    (f : E →ₗ[R] R) (g : F →ₗ[R] R) (f' : E' →ₗ[R] R) (g' : F' →ₗ[R] R)
    (φ : E →ₗ[R] E') (ψ : F →ₗ[R] F') (hφ : f'.comp φ = f) (hψ : g'.comp ψ = g)
    (n : ℕ) :
    (HomologicalComplex.mapBifunctorMap (tensorFormMap f f' φ hφ) (tensorFormMap g g' ψ hψ)
        moduleTensor (.down ℕ)).f n ≫ tensorComparisonComponent f' g' n =
      tensorComparisonComponent f g n ≫ ModuleCat.ofHom (exteriorPower.map n (φ.prodMap ψ)) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := complex f) (K₂ := complex g) (F := moduleTensor) (c := .down ℕ)
  intro p q h
  subst n
  rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  rw [Category.assoc, Category.assoc, tensorInclusion_comparison]
  conv_rhs => rw [← Category.assoc, tensorInclusion_comparison]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  change tensorExteriorProduct p q
    ((exteriorPower.map p φ a) ⊗ₜ[R] (exteriorPower.map q ψ b)) =
      exteriorPower.map (p+q) (φ.prodMap ψ) (tensorExteriorProduct p q (a ⊗ₜ[R] b))
  exact (tensorExteriorProduct_natural φ ψ p q a b).symm

/-- The value on homogeneous tensors determines the comparison uniquely. -/
theorem tensorDecomposition_hom (f : E →ₗ[R] R) (g : F →ₗ[R] R)
    (e : tensorTotal f g ≅ complex (sumForm f g)) (he : IsTensorDecomposition f g e) (n : ℕ) :
    e.hom.f n = tensorComparisonComponent f g n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := complex f) (K₂ := complex g) (F := moduleTensor) (c := .down ℕ)
  intro p q h
  subst n
  rw [tensorInclusion_comparison]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  exact he p q a b

/-- The canonical chain isomorphisms form a natural comparison in both forms. -/
theorem tensor_naturality : Specs.AdvCommAlg.Koszul.tensorNaturality.{u,v,w} := by
  intro R _ E E' _ _ _ _ F F' _ _ _ _ f g f' g' φ ψ hφ hψ e e' he he'
  apply HomologicalComplex.Hom.ext
  funext n
  change (HomologicalComplex.mapBifunctorMap (tensorFormMap f f' φ hφ)
      (tensorFormMap g g' ψ hψ) moduleTensor (.down ℕ)).f n ≫ e'.hom.f n =
    e.hom.f n ≫ ModuleCat.ofHom (exteriorPower.map n (φ.prodMap ψ))
  rw [tensorDecomposition_hom f g e he, tensorDecomposition_hom f' g' e' he']
  exact tensorComparisonComponent_natural f g f' g' φ ψ hφ hψ n

end AdvCommAlg.Koszul
