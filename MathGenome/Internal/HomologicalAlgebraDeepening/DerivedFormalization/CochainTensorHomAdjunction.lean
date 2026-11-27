import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainTensorHomAdjunction

/-! Signed currying and the tensor–Hom adjunction before and after passage to homotopy classes. -/

namespace DerivedFormalization

open CategoryTheory
open scoped TensorProduct
open CochainComplex.HomComplex
open HomologicalComplex (ιTensorObj)
open Specs.DerivedFormalization.CochainTensorHomAdjunction
  (tensorWithValue homFromValue curryingDifferential signedCurryingType closedAdjunctionsType)

universe u

variable {R : Type u} [CommRing R]

noncomputable section

/-- Under currying, the signed Hom differential has the target, first-factor,
and second-factor terms with coefficients (1), (-(-1)^n), and (-(-1)^{n+i}). -/
theorem tensorHomIso_d_apply (X Y Z : Comp.{u} R) :
    curryingDifferential X Y Z (tensorHomIso X Y Z) := by
  intro n i j l m hi hj f x y
  have h := ConcreteCategory.congr_hom ((tensorHomIso X Y Z).hom.comm n (n + 1)) f
  change (internalHom X (internalHom Y Z)).d n (n + 1) ((tensorHomIso X Y Z).hom.f n f) =
    (tensorHomIso X Y Z).hom.f (n + 1) ((internalHom (tensorComplex X Y) Z).d n (n + 1) f) at h
  rw [h, tensorHomIso_apply]
  obtain rfl : m = i + j + n + 1 := by omega
  rw [internalHom_d_apply, tensor_d_apply i j (i + j) (i + j + 1) rfl rfl]
  change _ - n.negOnePow • (f.v _ _ _).hom (_ + i.negOnePow • _) = _
  rw [map_add]
  have mapSign {M N : ModuleCat.{u} R} (g : M →ₗ[R] N) (a : M) :
      g (i.negOnePow • a) = i.negOnePow • g a := by
    simp only [Units.smul_def, map_zsmul]
  rw [mapSign, smul_add, smul_smul, ← Int.negOnePow_add, sub_add_eq_sub_sub]

theorem signedTensorHomCurrying : signedCurryingType.{u} := by
  intro R _
  exact ⟨tensorHomIso, tensorHomIso_apply, tensorHomIso_natural, tensorHomIso_d_apply⟩

/-- Tensor with a fixed cochain complex on the right. -/
abbrev cochainTensorWith (Y : Comp.{u} R) : Comp.{u} R ⥤ Comp.{u} R :=
  tensorWithValue Y

/-- The internal Hom functor out of a fixed cochain complex. -/
abbrev cochainHomFrom (Y : Comp.{u} R) : Comp.{u} R ⥤ Comp.{u} R :=
  homFromValue Y

private def cochainTensorHomCore (Y : Comp.{u} R) :
    Adjunction.CoreHomEquiv (cochainTensorWith Y) (cochainHomFrom Y) where
  homEquiv X Z := (tensorHomEquiv X Y Z).toEquiv
  homEquiv_naturality_left_symm := by
    intro X' X Z a g
    change X ⟶ internalHom Y Z at g
    apply (tensorHomEquiv X' Y Z).injective
    change tensorHomEquiv X' Y Z ((tensorHomEquiv X' Y Z).symm (a ≫ g)) =
      tensorHomEquiv X' Y Z (tensorMap a (𝟙 Y) ≫ (tensorHomEquiv X Y Z).symm g)
    rw [LinearEquiv.apply_symm_apply]
    have h := tensorHomEquiv_natural a (𝟙 Y) (𝟙 Z) ((tensorHomEquiv X Y Z).symm g)
    rw [Category.comp_id, LinearEquiv.apply_symm_apply, internalHomMap_id, Category.comp_id] at h
    exact h.symm
  homEquiv_naturality_right := by
    intro X Z Z' f c
    change tensorHomEquiv X Y Z' (f ≫ c) =
      tensorHomEquiv X Y Z f ≫ internalHomMap (𝟙 Y) c
    simpa using tensorHomEquiv_natural (𝟙 X) (𝟙 Y) c f

/-- Ordinary closed adjunction obtained from the degree-zero cycles of currying. -/
def cochainTensorHomAdjunction (Y : Comp.{u} R) :
    cochainTensorWith Y ⊣ cochainHomFrom Y :=
  Adjunction.mkOfHomEquiv (cochainTensorHomCore Y)

@[simp]
theorem cochainTensorHomAdjunction_homEquiv (X Y Z : Comp.{u} R) :
    (cochainTensorHomAdjunction Y).homEquiv X Z = (tensorHomEquiv X Y Z).toEquiv := by
  rw [cochainTensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- Evaluation is the counit on pure homogeneous tensors. -/
theorem cochainTensorHomCounit_apply (Y Z : Comp.{u} R) (i j : ℤ)
    (f : (internalHom Y Z).X i) (y : Y.X j) :
    ((cochainTensorHomAdjunction Y).counit.app Z).f (i + j)
      (ιTensorObj (internalHom Y Z) Y i j (i + j) rfl (f ⊗ₜ[R] y)) =
    f.v j (i + j) (add_comm j i) y := by
  let adj := cochainTensorHomAdjunction Y
  let ev : tensorComplex (internalHom Y Z) Y ⟶ Z := adj.counit.app Z
  have hc : ((cochainTensorHomAdjunction Y).homEquiv (internalHom Y Z) Z).symm (𝟙 _) = ev := by
    have hm := (cochainTensorWith Y).map_id ((cochainHomFrom Y).obj Z)
    exact (congrArg (fun f => f ≫ adj.counit.app Z) hm).trans (Category.id_comp _)
  have h : tensorHomEquiv (internalHom Y Z) Y Z ev = 𝟙 _ := by
    rw [← hc, cochainTensorHomAdjunction_homEquiv]
    exact (tensorHomEquiv (internalHom Y Z) Y Z).apply_symm_apply _
  have he := tensorHomEquiv_apply (internalHom Y Z) Y Z ev i j f y
  rw [h] at he
  exact he.symm

private abbrev q := homotopyQuotient.{u} R

private theorem tensorWith_respectsHomotopy (Y X X' : Comp.{u} R) (f g : X ⟶ X')
    (h : homotopic (ModuleCat R) (.up ℤ) f g) :
    (cochainTensorWith Y ⋙ q (R := R)).map f = (cochainTensorWith Y ⋙ q (R := R)).map g := by
  rcases h with ⟨h⟩
  exact HomotopyCategory.eq_of_homotopy _ _ (tensorMapHomotopy h (Homotopy.refl _))

private theorem homFrom_respectsHomotopy (Y Z Z' : Comp.{u} R) (f g : Z ⟶ Z')
    (h : homotopic (ModuleCat R) (.up ℤ) f g) :
    (cochainHomFrom Y ⋙ q (R := R)).map f = (cochainHomFrom Y ⋙ q (R := R)).map g := by
  rcases h with ⟨h⟩
  exact HomotopyCategory.eq_of_homotopy _ _ (internalHomMapHomotopy (Homotopy.refl _) h)

/-- Tensoring with a fixed complex on cochain homotopy classes. -/
def homotopyTensorWith (Y : Comp.{u} R) : K.{u} R ⥤ K.{u} R :=
  CategoryTheory.Quotient.lift _ (cochainTensorWith Y ⋙ q) (tensorWith_respectsHomotopy Y)

/-- The internal Hom out of a fixed complex on cochain homotopy classes. -/
def homotopyHomFrom (Y : Comp.{u} R) : K.{u} R ⥤ K.{u} R :=
  CategoryTheory.Quotient.lift _ (cochainHomFrom Y ⋙ q) (homFrom_respectsHomotopy Y)

/-- The quotient comparison for tensoring with a fixed complex. -/
def homotopyTensorWithComparison (Y : Comp.{u} R) :
    q ⋙ homotopyTensorWith Y ≅ cochainTensorWith Y ⋙ q :=
  CategoryTheory.Quotient.lift.isLift _ (cochainTensorWith Y ⋙ q) (tensorWith_respectsHomotopy Y)

/-- The quotient comparison for internal Hom out of a fixed complex. -/
def homotopyHomFromComparison (Y : Comp.{u} R) :
    q ⋙ homotopyHomFrom Y ≅ cochainHomFrom Y ⋙ q :=
  CategoryTheory.Quotient.lift.isLift _ (cochainHomFrom Y ⋙ q) (homFrom_respectsHomotopy Y)

/-- The tensor–Hom adjunction on the cochain homotopy category. -/
def homotopyTensorHomAdjunction (Y : Comp.{u} R) :
    homotopyTensorWith Y ⊣ homotopyHomFrom Y where
  unit :=
    { app X := q.map ((cochainTensorHomAdjunction Y).unit.app X.as)
      naturality := by
        rintro ⟨X⟩ ⟨X'⟩ ⟨f⟩
        change q.map f ≫ q.map ((cochainTensorHomAdjunction Y).unit.app X') =
          q.map ((cochainTensorHomAdjunction Y).unit.app X) ≫
            q.map ((cochainTensorWith Y ⋙ cochainHomFrom Y).map f)
        rw [← q.map_comp, ← q.map_comp]
        exact congrArg (q.map) ((cochainTensorHomAdjunction Y).unit.naturality f) }
  counit :=
    { app Z := q.map ((cochainTensorHomAdjunction Y).counit.app Z.as)
      naturality := by
        rintro ⟨Z⟩ ⟨Z'⟩ ⟨f⟩
        change q.map ((cochainHomFrom Y ⋙ cochainTensorWith Y).map f) ≫
            q.map ((cochainTensorHomAdjunction Y).counit.app Z') =
          q.map ((cochainTensorHomAdjunction Y).counit.app Z) ≫ q.map f
        rw [← q.map_comp, ← q.map_comp]
        exact congrArg (q.map) ((cochainTensorHomAdjunction Y).counit.naturality f) }
  left_triangle_components := by
    rintro ⟨X⟩
    let adj := cochainTensorHomAdjunction Y
    change q.map ((cochainTensorWith Y).map (adj.unit.app X)) ≫
      q.map (adj.counit.app ((cochainTensorWith Y).obj X)) = 𝟙 _
    rw [← q.map_comp]
    exact (congrArg (q.map) (adj.left_triangle_components X)).trans (q.map_id _)
  right_triangle_components := by
    rintro ⟨Z⟩
    let adj := cochainTensorHomAdjunction Y
    change q.map (adj.unit.app ((cochainHomFrom Y).obj Z)) ≫
      q.map ((cochainHomFrom Y).map (adj.counit.app Z)) = 𝟙 _
    rw [← q.map_comp]
    exact (congrArg (q.map) (adj.right_triangle_components Z)).trans (q.map_id _)

theorem homotopyTensorHomAdjunction_map (X Y Z : Comp.{u} R) (f : tensorComplex X Y ⟶ Z) :
    (homotopyTensorHomAdjunction Y).homEquiv (q.obj X) (q.obj Z) (q.map f) =
      q.map ((cochainTensorHomAdjunction Y).homEquiv X Z f) := by
  exact (q.map_comp ((cochainTensorHomAdjunction Y).unit.app X)
    ((cochainHomFrom Y).map f)).symm

theorem closedTensorHomAdjunctions : closedAdjunctionsType.{u} := by
  intro R _ Y
  refine ⟨cochainTensorHomAdjunction Y, homotopyTensorWith Y, homotopyHomFrom Y,
    homotopyTensorHomAdjunction Y, homotopyTensorWithComparison Y, homotopyHomFromComparison Y,
    ?_, cochainTensorHomCounit_apply Y, ?_⟩
  · intro X Z f i j x y
    rw [cochainTensorHomAdjunction_homEquiv]
    exact tensorHomEquiv_apply X Y Z f i j x y
  · intro X Z f
    change (homotopyTensorHomAdjunction Y).homEquiv (q.obj X) (q.obj Z) (𝟙 _ ≫ q.map f) ≫ 𝟙 _ = _
    have h := congrArg ((homotopyTensorHomAdjunction Y).homEquiv (q.obj X) (q.obj Z))
      (Category.id_comp (q.map f))
    exact (Category.comp_id _).trans (h.trans (homotopyTensorHomAdjunction_map X Y Z f))

end

end DerivedFormalization
