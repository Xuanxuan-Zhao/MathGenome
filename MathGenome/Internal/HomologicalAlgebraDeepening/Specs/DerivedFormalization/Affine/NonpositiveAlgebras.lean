import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.Module
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.RingTheory.Ideal.Quotient.Operations

open CategoryTheory

universe u v

namespace DerivedFormalization.Affine

variable {k : Type u} [Field k] [CharZero k]

/-- A graded-commutative algebra on the shared, unbounded DG algebra model. -/
structure CommDGAlgebra (k : Type u) [Field k] [CharZero k] where
  toDGAlgebra : DGAlgebraModel.{u,v} k
  graded_comm (i j n : ℤ) (h : i + j = n)
      (x : (toDGAlgebra.hom () ()).X i) (y : (toDGAlgebra.hom () ()).X j) :
    toDGAlgebra.comp i j n h x y =
      (i * j).negOnePow • toDGAlgebra.comp j i n ((add_comm j i).trans h) y x

namespace CommDGAlgebra

abbrev complex (A : CommDGAlgebra.{u,v} k) := A.toDGAlgebra.hom () ()
abbrev mul (A : CommDGAlgebra.{u,v} k) (i j n : ℤ) (h : i + j = n) :=
  A.toDGAlgebra.comp i j n h (a := ()) (b := ()) (c := ())
abbrev one (A : CommDGAlgebra.{u,v} k) := A.toDGAlgebra.id ()

def IsNonpositive (A : CommDGAlgebra.{u,v} k) : Prop :=
  ∀ i : ℤ, 0 < i → Subsingleton (A.complex.X i)

/-- A unital multiplicative chain map of the underlying complexes. -/
structure Hom (A B : CommDGAlgebra.{u,v} k) where
  chainMap : A.complex ⟶ B.complex
  map_one : chainMap.f 0 A.one = B.one
  map_mul (i j n : ℤ) (h : i + j = n) (x : A.complex.X i) (y : A.complex.X j) :
    chainMap.f n (A.mul i j n h x y) =
      B.mul i j n h (chainMap.f i x) (chainMap.f j y)

@[ext] theorem Hom.ext_chainMap {A B : CommDGAlgebra.{u,v} k} {f g : Hom A B}
    (h : f.chainMap = g.chainMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

protected def Hom.id (A : CommDGAlgebra.{u,v} k) : Hom A A :=
  ⟨𝟙 A.complex, rfl, fun _ _ _ _ _ _ => rfl⟩

protected def Hom.comp {A B C : CommDGAlgebra.{u,v} k} (f : Hom A B) (g : Hom B C) :
    Hom A C :=
  ⟨f.chainMap ≫ g.chainMap,
    by change g.chainMap.f 0 (f.chainMap.f 0 _) = _; rw [f.map_one, g.map_one],
    by
      intro i j n h x y
      change g.chainMap.f n (f.chainMap.f n (A.mul i j n h x y)) =
        C.mul i j n h (g.chainMap.f i (f.chainMap.f i x)) (g.chainMap.f j (f.chainMap.f j y))
      rw [f.map_mul, g.map_mul]⟩

instance : Category (CommDGAlgebra.{u,v} k) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext_chainMap (Category.id_comp f.chainMap)
  comp_id f := Hom.ext_chainMap (Category.comp_id f.chainMap)
  assoc f g h := Hom.ext_chainMap (Category.assoc f.chainMap g.chainMap h.chainMap)

def forgetComplex (k : Type u) [Field k] [CharZero k] :
    CommDGAlgebra.{u,v} k ⥤ ModuleCochain.{u,v} k where
  obj A := A.complex
  map f := f.chainMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The right modules over a cdga are the one-object right DG modules. -/
abbrev Module (A : CommDGAlgebra.{u,v} k) :=
  RightDGModuleModel (Specs.DerivedFormalization.DG.Basic.toDGCategory A.toDGAlgebra)

/-- Degree zero with multiplication and unit from the graded algebra. -/
abbrev DegreeZero (A : CommDGAlgebra.{u,v} k) : Type v := A.complex.X 0

instance (A : CommDGAlgebra.{u,v} k) : CommRing A.DegreeZero where
  __ := (inferInstance : AddCommGroup (A.complex.X 0))
  one := A.one
  mul x y := A.mul 0 0 0 rfl x y
  mul_assoc x y z := A.toDGAlgebra.assoc 0 0 0 x y z
  one_mul x := A.toDGAlgebra.id_comp 0 x
  mul_one x := A.toDGAlgebra.comp_id 0 x
  mul_comm x y := by
    change A.mul 0 0 0 rfl x y = A.mul 0 0 0 rfl y x
    simpa only [Int.zero_mul, Int.negOnePow_zero, one_smul] using A.graded_comm 0 0 0 rfl x y
  zero_mul x := by
    change A.mul 0 0 0 rfl (0 : A.complex.X 0) x = 0
    simp only [map_zero, LinearMap.zero_apply]
  mul_zero x := map_zero (A.mul 0 0 0 rfl x)
  left_distrib x y z := map_add (A.mul 0 0 0 rfl x) y z
  right_distrib x y z := by
    change A.mul 0 0 0 rfl (x+y) z = _
    rw [map_add, LinearMap.add_apply]
    rfl

instance (A : CommDGAlgebra.{u,v} k) : Algebra k A.DegreeZero :=
  Algebra.ofModule
    (fun c x y => by
      change A.mul 0 0 0 rfl (c • x) y = _
      rw [map_smul, LinearMap.smul_apply]
      rfl)
    (fun c x y => map_smul (A.mul 0 0 0 rfl x) c y)

def degreeZeroMap {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) :
    A.DegreeZero →ₐ[k] B.DegreeZero where
  toFun x := f.chainMap.f 0 x
  map_one' := f.map_one
  map_mul' := f.map_mul 0 0 0 rfl
  map_zero' := map_zero (f.chainMap.f 0).hom
  map_add' := map_add (f.chainMap.f 0).hom
  commutes' c := by
    change f.chainMap.f 0 (c • A.one) = c • B.one
    rw [map_smul, f.map_one]

end CommDGAlgebra

/-- The full subcategory of graded-commutative DG algebras with zero positive terms. -/
structure NonpositiveCDGA (k : Type u) [Field k] [CharZero k] where
  toCommDGAlgebra : CommDGAlgebra.{u,v} k
  nonpositive : toCommDGAlgebra.IsNonpositive

namespace NonpositiveCDGA

abbrev toDGAlgebra (A : NonpositiveCDGA.{u,v} k) := A.toCommDGAlgebra.toDGAlgebra
abbrev complex (A : NonpositiveCDGA.{u,v} k) := A.toCommDGAlgebra.complex
abbrev mul (A : NonpositiveCDGA.{u,v} k) := A.toCommDGAlgebra.mul
abbrev one (A : NonpositiveCDGA.{u,v} k) := A.toCommDGAlgebra.one
abbrev Module (A : NonpositiveCDGA.{u,v} k) := A.toCommDGAlgebra.Module

instance : Category (NonpositiveCDGA.{u,v} k) where
  Hom A B := CommDGAlgebra.Hom A.toCommDGAlgebra B.toCommDGAlgebra
  id A := CommDGAlgebra.Hom.id A.toCommDGAlgebra
  comp := CommDGAlgebra.Hom.comp
  id_comp f := CommDGAlgebra.Hom.ext_chainMap (Category.id_comp f.chainMap)
  comp_id f := CommDGAlgebra.Hom.ext_chainMap (Category.comp_id f.chainMap)
  assoc f g h := CommDGAlgebra.Hom.ext_chainMap (Category.assoc f.chainMap g.chainMap h.chainMap)

abbrev Hom (A B : NonpositiveCDGA.{u,v} k) := A ⟶ B

def inclusion (k : Type u) [Field k] [CharZero k] :
    NonpositiveCDGA.{u,v} k ⥤ CommDGAlgebra.{u,v} k where
  obj A := A.toCommDGAlgebra
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

def forgetComplex (k : Type u) [Field k] [CharZero k] :
    NonpositiveCDGA.{u,v} k ⥤ ModuleCochain.{u,v} k :=
  inclusion k ⋙ CommDGAlgebra.forgetComplex k

abbrev AlgebraUnder (A : NonpositiveCDGA.{u,v} k) := Under A

/-- The category of algebras under A equipped with an augmentation to the
specified A-algebra B. -/
abbrev AlgebraUnderOver {A B : NonpositiveCDGA.{u,v} k} (b : A ⟶ B) :=
  Over (Under.mk b)

def OverBase {P Q B : NonpositiveCDGA.{u,v} k}
    (p : P ⟶ B) (q : Q ⟶ B) (f : P ⟶ Q) : Prop :=
  f ≫ q = p

def IsQuasiIso {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B) : Prop :=
  QuasiIso ((forgetComplex k).map f)

def DegreewiseSurjective {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B) : Prop :=
  ∀ i : ℤ, Function.Surjective (((forgetComplex k).map f).f i)

def quasiIsomorphisms (k : Type u) [Field k] [CharZero k] :
    MorphismProperty (NonpositiveCDGA.{u,v} k) :=
  fun _ _ f => IsQuasiIso f

abbrev DegreeZero (A : NonpositiveCDGA.{u,v} k) := A.toCommDGAlgebra.DegreeZero

theorem d_zero_apply (A : NonpositiveCDGA.{u,v} k) (x : A.complex.X 0) :
    A.complex.d 0 1 x = 0 :=
  (A.nonpositive 1 (by decide)).elim _ _

/-- The ideal of degree-zero boundaries, with carrier exactly the image of d. -/
def boundaryIdeal (A : NonpositiveCDGA.{u,v} k) : Ideal A.DegreeZero where
  carrier := {x | ∃ y : A.complex.X (-1), A.complex.d (-1) 0 y = x}
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x+y, map_add _ _ _⟩
  smul_mem' := by
    rintro a _ ⟨y, rfl⟩
    refine ⟨A.mul 0 (-1) (-1) (by decide) a y, ?_⟩
    have h := A.toDGAlgebra.leibniz (a := ()) (b := ()) (c := ()) 0 (-1) (-1)
      (by decide) a y
    change A.complex.d (-1) 0 (A.mul 0 (-1) (-1) (by decide) a y) =
      A.mul 1 (-1) 0 (by decide) (A.complex.d 0 1 a) y +
        (0 : ℤ).negOnePow • A.mul 0 0 0 rfl a (A.complex.d (-1) 0 y) at h
    change _ = A.mul 0 0 0 rfl a (A.complex.d (-1) 0 y)
    simpa only [d_zero_apply, map_zero, LinearMap.zero_apply, zero_add,
      Int.negOnePow_zero, one_smul] using h

/-- The zeroth cohomology algebra is the ordinary algebra of degree-zero
elements modulo the boundaries. -/
abbrev H0 (A : NonpositiveCDGA.{u,v} k) : Type v := A.DegreeZero ⧸ A.boundaryIdeal

abbrev h0Class (A : NonpositiveCDGA.{u,v} k) : A.DegreeZero →ₐ[k] A.H0 :=
  Ideal.Quotient.mkₐ k A.boundaryIdeal

def h0Map {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B) : A.H0 →ₐ[k] B.H0 :=
  Ideal.quotientMapₐ B.boundaryIdeal (CommDGAlgebra.degreeZeroMap f) (by
    rintro _ ⟨y, rfl⟩
    refine ⟨f.chainMap.f (-1) y, ?_⟩
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (f.chainMap.comm (-1) 0)) y)

def h0Functor (k : Type u) [Field k] [CharZero k] :
    NonpositiveCDGA.{u,v} k ⥤ CommAlgCat.{v} k where
  obj A := CommAlgCat.of k A.H0
  map f := CommAlgCat.ofHom (h0Map f)
  map_id A := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective k A.boundaryIdeal x
    rfl
  map_comp {A B C} f g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective k A.boundaryIdeal x
    rfl

section Ordinary

noncomputable section

private abbrev singleZero (k : Type u) [Field k] :=
  HomologicalComplex.single (ModuleCat.{v} k) (ComplexShape.up ℤ) (0 : ℤ)

abbrev ordinaryComplex (S : CommAlgCat.{v} k) : ModuleCochain.{u,v} k :=
  (singleZero k).obj (ModuleCat.of k S)

omit [CharZero k] in
private theorem ordinary_eq_zero (S : CommAlgCat.{v} k) (i : ℤ) (hi : i ≠ 0)
    (x : (ordinaryComplex S).X i) : x = 0 :=
  (ModuleCat.subsingleton_of_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of k S) i hi)).elim x 0

private def ordinaryMul (S : CommAlgCat.{v} k) (i j n : ℤ) (h : i+j = n) :
    (ordinaryComplex S).X i →ₗ[k] (ordinaryComplex S).X j →ₗ[k] (ordinaryComplex S).X n :=
  if e : i = 0 ∧ j = 0 then by
    obtain ⟨rfl, rfl⟩ := e
    have hn : n = 0 := h.symm
    subst n
    exact LinearMap.mul k S
  else 0

/-- Embed an ordinary k-algebra with its original multiplication in degree zero. -/
def ordinary (S : CommAlgCat.{v} k) : NonpositiveCDGA.{u,v} k where
  toCommDGAlgebra :=
    { toDGAlgebra :=
        { hom := fun _ _ => ordinaryComplex S
          comp := fun i j n h => ordinaryMul S i j n h
          id := fun _ => (1 : S)
          d_id := fun _ => rfl
          id_comp := by
            intro a b i x
            by_cases h : i = 0
            · subst i
              exact @one_mul S _ x
            · rw [ordinary_eq_zero S i h x]
              exact map_zero (ordinaryMul S 0 i i (zero_add i) (1 : S))
          comp_id := by
            intro a b i x
            by_cases h : i = 0
            · subst i
              exact @mul_one S _ x
            · rw [ordinary_eq_zero S i h x]
              simp only [map_zero]
              rfl
          assoc := by
            intro a b c e i j l x y z
            by_cases hi : i = 0
            · subst i
              by_cases hj : j = 0
              · subst j
                by_cases hl : l = 0
                · subst l
                  exact @mul_assoc S _ x y z
                · rw [ordinary_eq_zero S l hl z]
                  simp only [map_zero]
              · rw [ordinary_eq_zero S j hj y]
                simp only [map_zero]
                change 0 = ordinaryMul S 0 (j+l) (0+j+l) (add_assoc 0 j l).symm x 0
                exact (map_zero _).symm
            · rw [ordinary_eq_zero S i hi x]
              simp only [map_zero, LinearMap.zero_apply]
          leibniz := by
            intro a b c i j n h x y
            change 0 = ordinaryMul S (i+1) j (n+1) (by omega) 0 y +
              i.negOnePow • ordinaryMul S i (j+1) (n+1) (by omega) x 0
            simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero] }
      graded_comm := by
        intro i j n h x y
        by_cases hi : i = 0
        · subst i
          by_cases hj : j = 0
          · subst j
            have hn : n = 0 := h.symm
            subst n
            change ordinaryMul S 0 0 0 rfl x y =
              (0 : ℤ).negOnePow • ordinaryMul S 0 0 0 rfl y x
            rw [Int.negOnePow_zero, one_smul]
            exact @mul_comm S _ x y
          · rw [ordinary_eq_zero S j hj y]
            simp only [map_zero, LinearMap.zero_apply, smul_zero]
        · rw [ordinary_eq_zero S i hi x]
          simp only [map_zero, LinearMap.zero_apply, smul_zero] }
  nonpositive i hi := ⟨fun x y =>
    (ordinary_eq_zero S i (ne_of_gt hi) x).trans (ordinary_eq_zero S i (ne_of_gt hi) y).symm⟩

private def ordinaryLinearMap {S T : CommAlgCat.{v} k} (f : S ⟶ T) :
    ModuleCat.of k S ⟶ ModuleCat.of k T :=
  ModuleCat.ofHom f.hom.toLinearMap

/-- Ordinary algebra maps act on the only nonzero degree. -/
def ordinaryMap {S T : CommAlgCat.{v} k} (f : S ⟶ T) : ordinary S ⟶ ordinary T where
  chainMap := (singleZero k).map (ordinaryLinearMap f)
  map_one := f.hom.map_one
  map_mul := by
    intro i j n h x y
    let F := (singleZero k).map (ordinaryLinearMap f)
    change (F.f n).hom (ordinaryMul S i j n h x y) =
      ordinaryMul T i j n h ((F.f i).hom x) ((F.f j).hom y)
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · subst j
        have hn : n = 0 := h.symm
        subst n
        exact f.hom.map_mul (x : S) (y : S)
      · rw [ordinary_eq_zero S j hj y]
        simp only [map_zero]
    · rw [ordinary_eq_zero S i hi x]
      simp only [map_zero, LinearMap.zero_apply]
      change (F.f n).hom 0 = 0
      exact map_zero _

def ordinaryFunctor (k : Type u) [Field k] [CharZero k] :
    CommAlgCat.{v} k ⥤ NonpositiveCDGA.{u,v} k where
  obj := ordinary
  map := ordinaryMap
  map_id S := CommDGAlgebra.Hom.ext_chainMap ((singleZero k).map_id (ModuleCat.of k S))
  map_comp f g := CommDGAlgebra.Hom.ext_chainMap
    ((singleZero k).map_comp (ordinaryLinearMap f) (ordinaryLinearMap g))

end
end Ordinary

end NonpositiveCDGA

/-- Derived affines form the opposite of the localization at quasi-isomorphisms. -/
abbrev DerivedAffine (k : Type u) [Field k] [CharZero k] :=
  (NonpositiveCDGA.quasiIsomorphisms.{u,v} k).Localizationᵒᵖ

noncomputable def derivedSpec (k : Type u) [Field k] [CharZero k] :
    (NonpositiveCDGA.{u,v} k)ᵒᵖ ⥤ DerivedAffine.{u,v} k :=
  (NonpositiveCDGA.quasiIsomorphisms k).Q.op

end DerivedFormalization.Affine

namespace Specs.DerivedFormalization.Affine.NonpositiveAlgebras

open _root_.DerivedFormalization _root_.DerivedFormalization.Affine

set_option linter.checkUnivs false

abbrev commDGAlgebra (k : Type u) [Field k] [CharZero k] := CommDGAlgebra.{u,v} k
abbrev commDGAlgebraHom {k : Type u} [Field k] [CharZero k]
    (A B : CommDGAlgebra.{u,v} k) := CommDGAlgebra.Hom A B
abbrev nonpositiveCDGA (k : Type u) [Field k] [CharZero k] := NonpositiveCDGA.{u,v} k

def CommDGAlgebraType := ∀ (k : Type u) [Field k] [CharZero k], Type (max u (v+1))
def CommDGAlgebraHomType := ∀ {k : Type u} [Field k] [CharZero k],
  CommDGAlgebra.{u,v} k → CommDGAlgebra.{u,v} k → Type v
def NonpositiveType := ∀ {k : Type u} [Field k] [CharZero k], CommDGAlgebra.{u,v} k → Prop
def NonpositiveCDGAType := ∀ (k : Type u) [Field k] [CharZero k], Type (max u (v+1))
def InclusionType := ∀ (k : Type u) [Field k] [CharZero k],
  NonpositiveCDGA.{u,v} k ⥤ CommDGAlgebra.{u,v} k
def ForgetComplexType := ∀ (k : Type u) [Field k] [CharZero k],
  NonpositiveCDGA.{u,v} k ⥤ ModuleCochain.{u,v} k
def AlgebraUnderType := ∀ {k : Type u} [Field k] [CharZero k],
  NonpositiveCDGA.{u,v} k → Type (max u (v+1))
def AlgebraUnderOverType := ∀ {k : Type u} [Field k] [CharZero k]
  {A B : NonpositiveCDGA.{u,v} k}, (A ⟶ B) → Type (max u (v+1))
def OverBaseType := ∀ {k : Type u} [Field k] [CharZero k]
  {P Q B : NonpositiveCDGA.{u,v} k}, (P ⟶ B) → (Q ⟶ B) → (P ⟶ Q) → Prop
def MapPredicate := ∀ {k : Type u} [Field k] [CharZero k]
  {A B : NonpositiveCDGA.{u,v} k}, (A ⟶ B) → Prop
def QuasiIsomorphismsType := ∀ (k : Type u) [Field k] [CharZero k],
  MorphismProperty (NonpositiveCDGA.{u,v} k)
def BoundaryIdealType := ∀ {k : Type u} [Field k] [CharZero k]
  (A : NonpositiveCDGA.{u,v} k), Ideal A.DegreeZero
def H0Type := ∀ {k : Type u} [Field k] [CharZero k],
  NonpositiveCDGA.{u,v} k → Type v
def H0FunctorType := ∀ (k : Type u) [Field k] [CharZero k],
  NonpositiveCDGA.{u,v} k ⥤ CommAlgCat.{v} k
def OrdinaryType := ∀ {k : Type u} [Field k] [CharZero k],
  CommAlgCat.{v} k → NonpositiveCDGA.{u,v} k
def OrdinaryFunctorType := ∀ (k : Type u) [Field k] [CharZero k],
  CommAlgCat.{v} k ⥤ NonpositiveCDGA.{u,v} k
def DerivedAffineType := ∀ (k : Type u) [Field k] [CharZero k], Type (max u (v+1))
def DerivedSpecType := ∀ (k : Type u) [Field k] [CharZero k],
  (NonpositiveCDGA.{u,v} k)ᵒᵖ ⥤ DerivedAffine.{u,v} k
def ModuleType := ∀ {k : Type u} [Field k] [CharZero k],
  CommDGAlgebra.{u,v} k → Type (max u (v+1))

def OverBaseCondition : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : NonpositiveCDGA.{u,v} k}
    {b : A ⟶ B} {P Q : NonpositiveCDGA.AlgebraUnderOver b} (f : P.left ⟶ Q.left),
    (∃ g : P ⟶ Q, g.left = f) ↔ f.right ≫ Q.hom.right = P.hom.right

def QuasiIsoCriterion : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B),
    NonpositiveCDGA.IsQuasiIso f ↔ ∀ i : ℤ, IsIso (HomologicalComplex.homologyMap f.chainMap i)

def H0MapOnClasses : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : NonpositiveCDGA.{u,v} k}
    (f : A ⟶ B) (x : A.DegreeZero),
    NonpositiveCDGA.h0Map f (A.h0Class x) = B.h0Class (f.chainMap.f 0 x)

def H0Homology : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (A : NonpositiveCDGA.{u,v} k),
    Nonempty (ModuleCat.of k A.H0 ≅ A.complex.homology 0)

def OrdinaryComponents : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (S : CommAlgCat.{v} k),
    let A := NonpositiveCDGA.ordinary S
    (∀ x y : S, A.mul 0 0 0 rfl x y = x * y) ∧ A.one = (1 : S) ∧
      (∀ i : ℤ, i ≠ 0 → Subsingleton (A.complex.X i)) ∧
      (∀ i j : ℤ, A.complex.d i j = 0)

def OrdinaryEmbedding : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    (NonpositiveCDGA.ordinaryFunctor.{u,v} k).Full ∧
    (NonpositiveCDGA.ordinaryFunctor.{u,v} k).Faithful

def DerivedSpecLocalization : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    (derivedSpec.{u,v} k).IsLocalization (NonpositiveCDGA.quasiIsomorphisms.{u,v} k).op

end Specs.DerivedFormalization.Affine.NonpositiveAlgebras
