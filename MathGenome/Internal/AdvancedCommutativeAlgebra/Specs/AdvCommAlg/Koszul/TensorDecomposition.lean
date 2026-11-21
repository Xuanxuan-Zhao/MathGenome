import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Construction
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-! The direct-sum clause of RK-05, paper.tex:2204–2225.
The total complex below uses Mathlib's signed totalization, with no
freeness, flatness, finiteness, or restriction on characteristic. -/

open scoped TensorProduct
open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w

namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]

/-- Tensoring modules, allowing independent universes for the two factors. -/
def moduleTensor : ModuleCat.{v} R ⥤ ModuleCat.{w} R ⥤ ModuleCat.{max v w} R where
  obj X :=
    { obj Y := ModuleCat.of R (X ⊗[R] Y)
      map f := ModuleCat.ofHom (f.hom.lTensor X)
      map_id Y := by ext x y; rfl
      map_comp f g := by ext x y; rfl }
  map f :=
    { app Y := ModuleCat.ofHom (f.hom.rTensor Y)
      naturality := by intros Y Z g; ext x y; rfl }
  map_id X := by ext Y x y; rfl
  map_comp f g := by ext Y x y; rfl

instance moduleTensor_additive : (moduleTensor.{u,v,w} (R := R)).Additive where
  map_add := by
    intros X Y f g
    apply NatTrans.ext
    funext Z
    apply ModuleCat.hom_ext
    change (f.hom + g.hom).rTensor Z = f.hom.rTensor Z + g.hom.rTensor Z
    ext x y
    simp

instance moduleTensor_obj_additive (X : ModuleCat.{v} R) :
    ((moduleTensor.{u,v,w} (R := R)).obj X).Additive where
  map_add := by
    intros Y Z f g
    apply ModuleCat.hom_ext
    change (f.hom + g.hom).lTensor X = f.hom.lTensor X + g.hom.lTensor X
    ext x y
    simp

variable {E : Type v} [AddCommGroup E] [Module R E]
variable {F : Type w} [AddCommGroup F] [Module R F]

/-- Contraction commutes with a map preserving the linear form. -/
theorem contraction_map (f : E →ₗ[R] R) (g : F →ₗ[R] R)
    (φ : E →ₗ[R] F) (hφ : g.comp φ = f) (a : ExteriorAlgebra R E) :
    contraction g (ExteriorAlgebra.map φ a) = ExteriorAlgebra.map φ (contraction f a) := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add a b ha hb => simp [ha, hb]
  | ι_mul a e ha =>
    have he : g (φ e) = f e := LinearMap.congr_fun hφ e
    simp only [map_mul, ExteriorAlgebra.map_apply_ι,
      contraction_generator_mul, he, map_sub, map_smul, ha]

@[simp] theorem complex_d (f : E →ₗ[R] R) (n : ℕ) :
    (complex f).d (n+1) n = ModuleCat.ofHom (differential f n) :=
  by
    dsimp only [complex]
    exact ChainComplex.of_d _ _ n

/-- The form on the direct sum is `(e,f) ↦ u(e) + v(f)`. -/
def sumForm (f : E →ₗ[R] R) (g : F →ₗ[R] R) : (E × F) →ₗ[R] R := f.coprod g

/-- The total tensor product of the canonical Koszul chain complexes. -/
abbrev tensorTotal (f : E →ₗ[R] R) (g : F →ₗ[R] R) :=
  HomologicalComplex.mapBifunctor (complex f) (complex g) moduleTensor (.down ℕ)

/-- Inclusion of a bidegree in the signed total tensor complex. -/
abbrev tensorInclusion (f : E →ₗ[R] R) (g : F →ₗ[R] R)
    (p q n : ℕ) (h : p + q = n) :=
  HomologicalComplex.ιMapBifunctor (complex f) (complex g) moduleTensor (.down ℕ) p q n h

/-- Exterior multiplication after the two direct-sum inclusions. -/
def tensorExteriorProduct (p q : ℕ) :
    ((⋀[R]^p E) ⊗[R] (⋀[R]^q F)) →ₗ[R] (⋀[R]^(p+q) (E × F)) :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun b =>
            ⟨(exteriorPower.map p (LinearMap.inl R E F) a : ExteriorAlgebra R (E × F)) *
                (exteriorPower.map q (LinearMap.inr R E F) b : ExteriorAlgebra R (E × F)),
              SetLike.mul_mem_graded
                (exteriorPower.map p (LinearMap.inl R E F) a).property
                (exteriorPower.map q (LinearMap.inr R E F) b).property⟩
          map_add' := by intros; apply Subtype.ext; simp [mul_add]
          map_smul' := by intros; apply Subtype.ext; simp }
      map_add' := by intros; ext; simp [add_mul]
      map_smul' := by intros; ext; simp }


/-- The canonical exterior-power chain map used to state naturality. -/
def tensorFormMap {E' : Type v} [AddCommGroup E'] [Module R E']
    (f : E →ₗ[R] R) (f' : E' →ₗ[R] R) (φ : E →ₗ[R] E') (hφ : f'.comp φ = f) :
    complex f ⟶ complex f' :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (exteriorPower.map n φ)) (fun n => by
    rw [complex_d, complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    erw [differential_coe, exteriorPower.coe_map, exteriorPower.coe_map, differential_coe]
    exact contraction_map f f' φ hφ (Subtype.val (a : ⋀[R]^(n+1) E)))


/-- Form preservation for the product map, with the original sum convention. -/
theorem sumForm_comp {E' : Type v} [AddCommGroup E'] [Module R E']
    {F' : Type w} [AddCommGroup F'] [Module R F']
    (f : E →ₗ[R] R) (g : F →ₗ[R] R) (f' : E' →ₗ[R] R) (g' : F' →ₗ[R] R)
    (φ : E →ₗ[R] E') (ψ : F →ₗ[R] F') (hφ : f'.comp φ = f) (hψ : g'.comp ψ = g) :
    (sumForm f' g').comp (φ.prodMap ψ) = sumForm f g := by
  apply LinearMap.ext
  rintro ⟨a,b⟩
  exact congrArg₂ (· + ·) (LinearMap.congr_fun hφ a) (LinearMap.congr_fun hψ b)

/-- A comparison is canonical when its value on homogeneous tensors is exterior multiplication. -/
def IsTensorDecomposition (f : E →ₗ[R] R) (g : F →ₗ[R] R)
    (e : tensorTotal f g ≅ complex (sumForm f g)) : Prop :=
  ∀ (p q : ℕ) (a : ⋀[R]^p E) (b : ⋀[R]^q F),
    (e.hom.f (p+q)).hom ((tensorInclusion f g p q (p+q) rfl).hom (a ⊗ₜ[R] b)) =
      tensorExteriorProduct p q (a ⊗ₜ[R] b)

end AdvCommAlg.Koszul

namespace Specs.AdvCommAlg.Koszul
open _root_.AdvCommAlg.Koszul

/-- The isomorphism is specified on every pure homogeneous tensor, thereby
fixing the canonical map and its natural dependence on both modules. -/
def tensorDecomposition : Prop :=
  ∀ {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
    {F : Type w} [AddCommGroup F] [Module R F] (f : E →ₗ[R] R) (g : F →ₗ[R] R),
    ∃ e : tensorTotal f g ≅ complex (sumForm f g), IsTensorDecomposition f g e

/-- Naturality of the canonical chain isomorphisms under maps preserving the forms. -/
def tensorNaturality : Prop :=
  ∀ {R : Type u} [CommRing R] {E E' : Type v}
    [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E']
    {F F' : Type w} [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R F']
    (f : E →ₗ[R] R) (g : F →ₗ[R] R) (f' : E' →ₗ[R] R) (g' : F' →ₗ[R] R)
    (φ : E →ₗ[R] E') (ψ : F →ₗ[R] F') (hφ : f'.comp φ = f) (hψ : g'.comp ψ = g)
    (e : tensorTotal f g ≅ complex (sumForm f g))
    (e' : tensorTotal f' g' ≅ complex (sumForm f' g')),
    IsTensorDecomposition f g e → IsTensorDecomposition f' g' e' →
      HomologicalComplex.mapBifunctorMap (tensorFormMap f f' φ hφ) (tensorFormMap g g' ψ hψ)
          moduleTensor (.down ℕ) ≫ e'.hom =
        e.hom ≫ tensorFormMap (sumForm f g) (sumForm f' g') (φ.prodMap ψ)
          (sumForm_comp f g f' g' φ ψ hφ hψ)


end Specs.AdvCommAlg.Koszul
