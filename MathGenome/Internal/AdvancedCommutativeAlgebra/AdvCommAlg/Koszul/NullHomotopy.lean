import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.NullHomotopy
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.Construction
import Mathlib.Algebra.Homology.ShortComplex.Linear

open CategoryTheory
open scoped TensorProduct
noncomputable section
universe u v
namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]
variable {E : Type v} [AddCommGroup E] [Module R E]

@[simp] theorem leftWedge_coe (e : E) (n : ℕ) (a : ⋀[R]^n E) :
    (leftWedge e n a : ExteriorAlgebra R E) = ExteriorAlgebra.ι R e * a := rfl

theorem contraction_degree_zero (f : E →ₗ[R] R) (a : ⋀[R]^0 E) :
    contraction f (a : ExteriorAlgebra R E) = 0 := by
  have ha := a.property
  change (a : ExteriorAlgebra R E) ∈ (ExteriorAlgebra.ι R).range ^ 0 at ha
  rw [pow_zero, Submodule.mem_one] at ha
  obtain ⟨r, hr⟩ := ha
  rw [← hr, contraction_scalar]

theorem wedge_identity_zero (f : E →ₗ[R] R) (e : E) :
    (differential f 0).comp (leftWedge e 0) = f e • LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change contraction f (ExteriorAlgebra.ι R e * a) = f e • (a : ExteriorAlgebra R E)
  rw [contraction_generator_mul, contraction_degree_zero, mul_zero, sub_zero]

theorem wedge_identity_succ (f : E →ₗ[R] R) (e : E) (n : ℕ) :
    (differential f (n+1)).comp (leftWedge e (n+1)) +
      (leftWedge e n).comp (differential f n) = f e • LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change contraction f (ExteriorAlgebra.ι R e * a) +
    ExteriorAlgebra.ι R e * contraction f a = f e • (a : ExteriorAlgebra R E)
  rw [contraction_generator_mul, sub_add_cancel]

theorem listForm_sum : Specs.AdvCommAlg.Koszul.listFormSum.{u} := by
  intro R _ x b
  classical
  simp [listForm, Module.Basis.constr_apply_fintype]

theorem ideal_preimage : Specs.AdvCommAlg.Koszul.idealPreimage.{u} := by
  intro R _ x a ha
  change a ∈ Submodule.span R {r | r ∈ x} at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact ⟨Pi.basisFun R (Fin x.length) i, listForm_basis x i⟩
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb ia ib =>
    obtain ⟨e, rfl⟩ := ia
    obtain ⟨f, rfl⟩ := ib
    exact ⟨e+f, map_add _ _ _⟩
  | smul r a ha ia =>
    obtain ⟨e, rfl⟩ := ia
    exact ⟨r • e, map_smul _ _ _⟩

variable (M : Type v) [AddCommGroup M] [Module R M]

theorem coefficient_wedge_zero (x : List R) (e : Fin x.length → R) :
    (coefficientDifferential M x 0).comp (coefficientWedge M x e 0) =
      listForm x e • LinearMap.id := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro m
  change differential (listForm x) 0 (leftWedge e 0 a) ⊗ₜ[R] m =
    listForm x e • (a ⊗ₜ[R] m)
  have h := LinearMap.congr_fun (wedge_identity_zero (listForm x) e) a
  change differential (listForm x) 0 (leftWedge e 0 a) = listForm x e • a at h
  rw [h, TensorProduct.smul_tmul']

theorem coefficient_wedge_succ (x : List R) (e : Fin x.length → R) (n : ℕ) :
    (coefficientDifferential M x (n+1)).comp (coefficientWedge M x e (n+1)) +
      (coefficientWedge M x e n).comp (coefficientDifferential M x n) =
        listForm x e • LinearMap.id := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro m
  change (differential (listForm x) (n+1) (leftWedge e (n+1) a)) ⊗ₜ[R] m +
    (leftWedge e n (differential (listForm x) n a)) ⊗ₜ[R] m =
      listForm x e • (a ⊗ₜ[R] m)
  rw [← TensorProduct.add_tmul]
  have h := LinearMap.congr_fun (wedge_identity_succ (listForm x) e n) a
  change differential (listForm x) (n+1) (leftWedge e (n+1) a) +
    leftWedge e n (differential (listForm x) n a) = listForm x e • a at h
  rw [h, TensorProduct.smul_tmul']

theorem coefficient_wedge_identities : Specs.AdvCommAlg.Koszul.coefficientWedgeIdentities.{u,v} := by
  intro R _ M _ _ x e
  exact ⟨coefficient_wedge_zero M x e, coefficient_wedge_succ M x e⟩

/-- Package a family of explicit degree-raising maps as a categorical homotopy. -/
def chainHomotopyOfComponents (C : ChainComplex (ModuleCat R) ℕ) (f : C ⟶ C)
    (h : ∀ n, C.X n ⟶ C.X (n+1))
    (hzero : f.f 0 = h 0 ≫ C.d 1 0)
    (hsucc : ∀ n, f.f (n+1) = C.d (n+1) n ≫ h n + h (n+1) ≫ C.d (n+2) (n+1)) :
    Homotopy f 0 :=
  { hom := fun i j => if hij : i+1 = j then h i ≫ eqToHom (congrArg C.X hij) else 0
    zero := by intro i j hij; exact dite_eq_right hij
    comm := by
      intro i
      cases i with
      | zero =>
        rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
        simpa using hzero
      | succ n =>
        rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
        simpa using hsucc n }

/-- A choice of vector e yields the left-wedge null homotopy of u(e). -/
def coefficientWedgeHomotopy (x : List R) (e : Fin x.length → R) :
    Homotopy (listForm x e • 𝟙 (coefficientComplex M x)) 0 := by
  apply chainHomotopyOfComponents (coefficientComplex M x) _
    (fun n => ModuleCat.ofHom (coefficientWedge M x e n))
  · apply ModuleCat.hom_ext
    change listForm x e • LinearMap.id = (coefficientDifferential M x 0).comp (coefficientWedge M x e 0)
    exact (coefficient_wedge_zero M x e).symm
  · intro n
    have hd : (coefficientComplex M x).d (n+2) (n+1) =
        ModuleCat.ofHom (coefficientDifferential M x (n+1)) := by
      exact ChainComplex.of_d
        (fun k => ModuleCat.of R ((⋀[R]^k (Fin x.length → R)) ⊗[R] M))
        (fun k => ModuleCat.ofHom (coefficientDifferential M x k)) (n+1)
    have hd' : (coefficientComplex M x).d (n+1) n =
        ModuleCat.ofHom (coefficientDifferential M x n) := by
      exact ChainComplex.of_d
        (fun k => ModuleCat.of R ((⋀[R]^k (Fin x.length → R)) ⊗[R] M))
        (fun k => ModuleCat.ofHom (coefficientDifferential M x k)) n
    rw [hd, hd']
    apply ModuleCat.hom_ext
    change listForm x e • LinearMap.id =
      (coefficientWedge M x e n).comp (coefficientDifferential M x n) +
        (coefficientDifferential M x (n+1)).comp (coefficientWedge M x e (n+1))
    exact (coefficient_wedge_succ M x e n).symm.trans (add_comm _ _)

theorem explicit_nullHomotopy : Specs.AdvCommAlg.Koszul.explicitNullHomotopy.{u,v} := by
  intro R _ M _ _ x b a ha
  have he : listForm x (∑ i, b i • Pi.basisFun R (Fin x.length) i) = a := by
    simpa only [map_sum, map_smul, listForm_basis, smul_eq_mul] using ha
  rw [← he]
  refine ⟨coefficientWedgeHomotopy M x _, ?_⟩
  intro n
  simp [coefficientWedgeHomotopy, chainHomotopyOfComponents]
  exact Category.comp_id _

theorem coefficient_nullHomotopy : Specs.AdvCommAlg.Koszul.coefficientNullHomotopy.{u,v} := by
  intro R _ M _ _ x a ha
  obtain ⟨e, rfl⟩ := ideal_preimage x a ha
  exact ⟨coefficientWedgeHomotopy M x e⟩

theorem cochain_wedge_zero (x : List R) (e : Fin x.length → R) :
    (cochainWedge M x e 0).comp (cochainDifferential M x 0) =
      listForm x e • LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro a
  change f (differential (listForm x) 0 (leftWedge e 0 a)) = listForm x e • f a
  have h := LinearMap.congr_fun (wedge_identity_zero (listForm x) e) a
  change differential (listForm x) 0 (leftWedge e 0 a) = listForm x e • a at h
  rw [h, map_smul]

theorem cochain_wedge_succ (x : List R) (e : Fin x.length → R) (n : ℕ) :
    (cochainWedge M x e (n+1)).comp (cochainDifferential M x (n+1)) +
      (cochainDifferential M x n).comp (cochainWedge M x e n) =
        listForm x e • LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro a
  change f (differential (listForm x) (n+1) (leftWedge e (n+1) a)) +
    f (leftWedge e n (differential (listForm x) n a)) = listForm x e • f a
  rw [← map_add]
  have h := LinearMap.congr_fun (wedge_identity_succ (listForm x) e n) a
  change differential (listForm x) (n+1) (leftWedge e (n+1) a) +
    leftWedge e n (differential (listForm x) n a) = listForm x e • a at h
  rw [h, map_smul]

theorem cochain_wedge_identities : Specs.AdvCommAlg.Koszul.cochainWedgeIdentities.{u,v} := by
  intro R _ M _ _ x e
  exact ⟨cochain_wedge_zero M x e, cochain_wedge_succ M x e⟩

/-- Package degree-lowering cochain maps as a categorical homotopy. -/
def cochainHomotopyOfComponents (C : CochainComplex (ModuleCat R) ℕ) (f : C ⟶ C)
    (h : ∀ n, C.X (n+1) ⟶ C.X n)
    (hzero : f.f 0 = C.d 0 1 ≫ h 0)
    (hsucc : ∀ n, f.f (n+1) = h n ≫ C.d n (n+1) + C.d (n+1) (n+2) ≫ h (n+1)) :
    Homotopy f 0 :=
  { hom := fun i j => if hij : j+1 = i then eqToHom (congrArg C.X hij.symm) ≫ h j else 0
    zero := by intro i j hij; exact dite_eq_right hij
    comm := by
      intro i
      cases i with
      | zero =>
        rw [Homotopy.prevD_zero_cochainComplex, Homotopy.dNext_cochainComplex]
        simpa using hzero
      | succ n =>
        rw [Homotopy.prevD_succ_cochainComplex, Homotopy.dNext_cochainComplex]
        simpa [add_comm] using hsucc n }

def cochainWedgeHomotopy (x : List R) (e : Fin x.length → R) :
    Homotopy (listForm x e • 𝟙 (cochainComplex M x)) 0 := by
  apply cochainHomotopyOfComponents (cochainComplex M x) _
    (fun n => ModuleCat.ofHom (cochainWedge M x e n))
  · apply ModuleCat.hom_ext
    change listForm x e • LinearMap.id = (cochainWedge M x e 0).comp (cochainDifferential M x 0)
    exact (cochain_wedge_zero M x e).symm
  · intro n
    have hd : (cochainComplex M x).d (n+1) (n+2) =
        ModuleCat.ofHom (cochainDifferential M x (n+1)) := by
      exact CochainComplex.of_d
        (fun k => ModuleCat.of R ((⋀[R]^k (Fin x.length → R)) →ₗ[R] M))
        (fun k => ModuleCat.ofHom (cochainDifferential M x k)) (n+1)
    have hd' : (cochainComplex M x).d n (n+1) =
        ModuleCat.ofHom (cochainDifferential M x n) := by
      exact CochainComplex.of_d
        (fun k => ModuleCat.of R ((⋀[R]^k (Fin x.length → R)) →ₗ[R] M))
        (fun k => ModuleCat.ofHom (cochainDifferential M x k)) n
    rw [hd, hd']
    apply ModuleCat.hom_ext
    change listForm x e • LinearMap.id =
      (cochainDifferential M x n).comp (cochainWedge M x e n) +
        (cochainWedge M x e (n+1)).comp (cochainDifferential M x (n+1))
    exact (cochain_wedge_succ M x e n).symm.trans (add_comm _ _)

theorem cochain_nullHomotopy : Specs.AdvCommAlg.Koszul.cochainNullHomotopy.{u,v} := by
  intro R _ M _ _ x a ha
  obtain ⟨e, rfl⟩ := ideal_preimage x a ha
  exact ⟨cochainWedgeHomotopy M x e⟩

/-- Scalar multiplication on a complex induces scalar multiplication on its homology. -/
theorem homologyMap_scalar {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (a : R) (q : ι) :
    HomologicalComplex.homologyMap (a • 𝟙 C) q = a • 𝟙 (C.homology q) := by
  unfold HomologicalComplex.homologyMap
  have h : (HomologicalComplex.shortComplexFunctor (ModuleCat R) c q).map (a • 𝟙 C) =
      a • 𝟙 (C.sc q) := by
    ext <;> rfl
  rw [h, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

/-- A null homotopy of a scalar forces that scalar to act by zero on homology. -/
theorem smul_eq_zero_of_nullHomotopy {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (a : R)
    (h : Homotopy (a • 𝟙 C) 0) (q : ι) (z : C.homology q) : a • z = 0 := by
  have heq := h.homologyMap_eq q
  rw [homologyMap_scalar, HomologicalComplex.homologyMap_zero] at heq
  exact congrArg (fun f : C.homology q ⟶ C.homology q => f z) heq

theorem annihilates_homology : Specs.AdvCommAlg.Koszul.annihilatesHomology.{u,v} := by
  intro R _ M _ _ x a ha q z
  obtain ⟨h⟩ := coefficient_nullHomotopy M x a ha
  exact smul_eq_zero_of_nullHomotopy (coefficientComplex M x) a h q z

theorem annihilates_cohomology : Specs.AdvCommAlg.Koszul.annihilatesCohomology.{u,v} := by
  intro R _ M _ _ x a ha q z
  obtain ⟨h⟩ := cochain_nullHomotopy M x a ha
  exact smul_eq_zero_of_nullHomotopy (cochainComplex M x) a h q z

theorem unitIdeal_contractible : Specs.AdvCommAlg.Koszul.unitIdealContractible.{u,v} := by
  intro R _ M _ _ x hx
  have h1 : (1 : R) ∈ listIdeal x := by rw [hx]; trivial
  simpa using coefficient_nullHomotopy M x 1 h1

/-- Export the canonical constructions without introducing a second interface. -/
def koszulLeftWedge := @leftWedge.{u,v}
def koszulCoefficientWedge := @coefficientWedge.{u,v}
def koszulCochainComplex := @cochainComplex.{u,v}
def koszulCohomology := @cohomology.{u,v}

end AdvCommAlg.Koszul
