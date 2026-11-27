import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainRingTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensorMonoidal
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensorHomAdjunction
import Mathlib.CategoryTheory.Monoidal.Braided.Transport
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainTensorTransport
import Batteries.Tactic.OpenPrivate

namespace DerivedFormalization.CochainTensorTransport

open CategoryTheory
open CochainComplex.HomComplex (Cochain)
open CochainTensor (tensor pure map map_on_pure differential)
open Specs.DerivedFormalization.CochainTensorTransport (Currying)

universe u v a

variable {R : Type u} [CommRing R]

private theorem nestedHom_ext {X Y Z : Comp.{v} R} {q : ℤ}
    {f g : Cochain X (internalHom Y Z) q}
    (h : ∀ (i j l m : ℤ) (hi : i + q = l) (hj : j + l = m) (x : X.X i) (y : Y.X j),
      (f.v i l hi x).v j m hj y = (g.v i l hi x).v j m hj y) : f = g := by
  apply Cochain.ext
  intro i l hi
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Cochain.ext
  intro j m hj
  exact ModuleCat.hom_ext (LinearMap.ext (h i j l m hi hj x))

/-- The homogeneous evaluation formula determines the currying map. -/
theorem currying_hom_unique (X Y Z : Comp.{v} R) (c₁ c₂ : Currying.{u,v} R) :
    (c₁.iso X Y Z).hom = (c₂.iso X Y Z).hom := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact nestedHom_ext fun _ _ _ _ hi hj x y =>
    (c₁.on_pure X Y Z hi hj f x y).trans (c₂.on_pure X Y Z hi hj f x y).symm

private theorem map_sign {M N : ModuleCat.{v} R} (φ : M →ₗ[R] N) (s : ℤˣ) (z : M) :
    φ (s • z) = s • φ z := by
  simp only [Units.smul_def, map_zsmul]

/-- A chain isomorphism with the homogeneous currying formula also gives the
three signed terms of its differential. -/
theorem currying_differential (X Y Z : Comp.{v} R)
    (c : internalHom (tensor X Y) Z ≅ internalHom X (internalHom Y Z))
    (evaluate : ∀ {q i j l m : ℤ} (hi : i + q = l) (hj : j + l = m)
      (f : Cochain (tensor X Y) Z q) (x : X.X i) (y : Y.X j),
      (((c.hom.f q f).v i l hi x).v j m hj) y =
        f.v (i + j) m (by omega) (pure X Y rfl x y))
    {q i j l m : ℤ} (hi : i + (q + 1) = l) (hj : j + l = m)
    (f : Cochain (tensor X Y) Z q) (x : X.X i) (y : Y.X j) :
    ((((internalHom X (internalHom Y Z)).d q (q + 1) (c.hom.f q f)).v i l hi x).v
      j m hj) y =
      Z.d (i + j + q) m (f.v (i + j) (i + j + q) rfl (pure X Y rfl x y)) -
      q.negOnePow • f.v (i + j + 1) m (by omega)
        (pure X Y (by omega : i + 1 + j = i + j + 1) (X.d i (i + 1) x) y) -
      (q + i).negOnePow • f.v (i + j + 1) m (by omega)
        (pure X Y (by omega : i + (j + 1) = i + j + 1) x (Y.d j (j + 1) y)) := by
  have h := ConcreteCategory.congr_hom (c.hom.comm q (q + 1)) f
  change (internalHom X (internalHom Y Z)).d q (q + 1) (c.hom.f q f) =
    c.hom.f (q + 1) ((internalHom (tensor X Y) Z).d q (q + 1) f) at h
  rw [h, evaluate]
  obtain rfl : m = i + j + q + 1 := by omega
  rw [internalHom_d_apply, differential X Y i j (i + j) rfl]
  change _ - q.negOnePow • (f.v _ _ _).hom (_ + i.negOnePow • _) = _
  rw [map_add]
  rw [map_sign, smul_add, smul_smul, ← Int.negOnePow_add, sub_add_eq_sub_sub]

section Currying

open scoped TensorProduct
open CochainTensor (ι)
open HomologicalComplex (mapBifunctorDesc ι_mapBifunctorDesc)
open Specs.DerivedFormalization.DG.Basic (moduleTensor)

variable (X Y Z : Comp.{v} R)

private noncomputable def curryDegree (q : ℤ) :
    Cochain (tensor X Y) Z q →ₗ[R] Cochain X (internalHom Y Z) q where
  toFun f := Cochain.mk fun i l hi => ModuleCat.ofHom
    { toFun := fun x => Cochain.mk fun j m hj => ModuleCat.ofHom
        (TensorProduct.curry
          ((f.v (i + j) m (by omega)).hom.comp (ι X Y i j (i + j) rfl).hom) x)
      map_add' := by
        intro x x'
        apply Cochain.ext
        intro j m hj
        apply ModuleCat.hom_ext
        simp only [Cochain.mk_v, Cochain.add_v, ModuleCat.hom_add, ModuleCat.hom_ofHom, map_add]
      map_smul' := by
        intro r x
        apply Cochain.ext
        intro j m hj
        apply ModuleCat.hom_ext
        simp only [Cochain.mk_v, Cochain.smul_v, ModuleCat.hom_smul, ModuleCat.hom_ofHom, map_smul,
          RingHom.id_apply] }
  map_add' f g := by
    apply nestedHom_ext
    intros
    rfl
  map_smul' r f := by
    apply nestedHom_ext
    intros
    rfl

private theorem curryDegree_apply {q i j t l m : ℤ} (ht : i + j = t)
    (hi : i + q = l) (hj : j + l = m) (f : Cochain (tensor X Y) Z q) (x : X.X i) (y : Y.X j) :
    ((curryDegree X Y Z q f).v i l hi x).v j m hj y = f.v t m (by omega) (pure X Y ht x y) := by
  subst t
  rfl

private def uncurrySummand {q i j m : ℤ} (hm : i + j + q = m)
    (g : Cochain X (internalHom Y Z) q) :
    ModuleCat.of R (X.X i ⊗[R] Y.X j) ⟶ Z.X m :=
  ModuleCat.ofHom <| TensorProduct.lift
    { toFun x := ((g.v i (i + q) rfl x).v j m (by omega)).hom
      map_add' x x' := by
        rw [map_add]
        rfl
      map_smul' r x := by
        rw [map_smul]
        rfl }

private noncomputable def uncurryDegree {q : ℤ} (g : Cochain X (internalHom Y Z) q) :
    Cochain (tensor X Y) Z q :=
  Cochain.mk fun t m hm =>
    mapBifunctorDesc (K₁ := X) (K₂ := Y) (F := moduleTensor R) (c := .up ℤ)
      (j := t) fun i j (ht : i + j = t) => uncurrySummand X Y Z (by omega) g

private theorem uncurryDegree_apply {q i j t l m : ℤ} (ht : i + j = t)
    (hi : i + q = l) (hj : j + l = m)
    (g : Cochain X (internalHom Y Z) q) (x : X.X i) (y : Y.X j) :
    (uncurryDegree X Y Z g).v t m (by omega) (pure X Y ht x y) = (g.v i l hi x).v j m hj y := by
  subst l
  have w := ι_mapBifunctorDesc (K₁ := X) (K₂ := Y) (F := moduleTensor R) (c := .up ℤ)
    (j := t) (fun a b (hs : a + b = t) => uncurrySummand X Y Z (m := m) (by omega) g) i j ht
  exact ConcreteCategory.congr_hom w (x ⊗ₜ[R] y)

private noncomputable def curryLinearEquiv (q : ℤ) :
    Cochain (tensor X Y) Z q ≃ₗ[R] Cochain X (internalHom Y Z) q :=
  { curryDegree X Y Z q with
    invFun := uncurryDegree X Y Z
    left_inv := by
      intro f
      apply Cochain.ext
      intro t m hm
      apply CochainTensor.term_hom_ext
      intro i j ht x y
      change (uncurryDegree X Y Z (curryDegree X Y Z q f)).v t m hm (pure X Y ht x y) = _
      rw [uncurryDegree_apply X Y Z ht rfl (by omega : j + (i + q) = m),
        curryDegree_apply X Y Z ht]
    right_inv := by
      intro g
      apply nestedHom_ext
      intro i j l m hi hj x y
      change ((curryDegree X Y Z q (uncurryDegree X Y Z g)).v i l hi x).v j m hj y = _
      rw [curryDegree_apply X Y Z rfl hi hj, uncurryDegree_apply X Y Z rfl hi hj] }

private theorem hom_d_eval {U V : Comp.{v} R} {q i m : ℤ} (h : i + (q + 1) = m)
    (f : Cochain U V q) (x : U.X i) :
    (((internalHom U V).d q (q + 1) f).v i m h) x =
    V.d (i + q) m (f.v i (i + q) rfl x) -
      q.negOnePow • f.v (i + 1) m (by omega) (U.d i (i + 1) x) := by
  obtain rfl : m = i + q + 1 := by omega
  exact internalHom_d_apply q i f x

private theorem hom_d_eval_at {U V : Comp.{v} R} {q i k m : ℤ} (hk : i + q = k)
    (h : i + (q + 1) = m) (f : Cochain U V q) (x : U.X i) :
    (((internalHom U V).d q (q + 1) f).v i m h) x =
    V.d k m (f.v i k hk x) -
      q.negOnePow • f.v (i + 1) m (by omega) (U.d i (i + 1) x) := by
  subst k
  exact hom_d_eval h f x

private theorem curry_comm (q : ℤ) (f : Cochain (tensor X Y) Z q) :
    (internalHom X (internalHom Y Z)).d q (q + 1) (curryDegree X Y Z q f) =
      curryDegree X Y Z (q + 1) ((internalHom (tensor X Y) Z).d q (q + 1) f) := by
  apply nestedHom_ext
  intro i j l m hi hj x y
  have hi' : i + q + 1 = l := by omega
  obtain rfl : l = i + q + 1 := hi'.symm
  rw [hom_d_eval hi, curryDegree_apply X Y Z rfl hi hj, hom_d_eval (by omega),
    differential X Y i j (i + j) rfl]
  change (_ - q.negOnePow • (show Cochain Y Z (i + q + 1) from _)).v j m hj y = _
  rw [sub_eq_add_neg, Cochain.add_v, Cochain.neg_v, Cochain.units_smul_v]
  change _ + -(q.negOnePow • _) =
    _ - q.negOnePow • (f.v _ _ _).hom (_ + i.negOnePow • _)
  rw [hom_d_eval_at (by omega : j + (i + q) = i + j + q) hj,
    curryDegree_apply X Y Z rfl rfl (by omega : j + (i + q) = i + j + q)]
  rw [curryDegree_apply X Y Z (by omega : i + (j + 1) = i + j + 1) rfl (by omega : j + 1 + (i + q) = m),
    curryDegree_apply X Y Z (by omega : i + 1 + j = i + j + 1) (by omega) hj]
  rw [map_add, map_sign, smul_add, smul_smul, ← Int.negOnePow_add, add_comm q i]
  abel

/-- Signed currying on the product Hom and the direct-sum tensor. -/
noncomputable def curryIso :
    internalHom (tensor X Y) Z ≅ internalHom X (internalHom Y Z) :=
  HomologicalComplex.Hom.isoOfComponents (fun q => (curryLinearEquiv X Y Z q).toModuleIso)
    (by
      intro q m hm
      change q + 1 = m at hm
      subst m
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      exact curry_comm X Y Z q f)

theorem curryIso_apply {q i j l m : ℤ} (hi : i + q = l) (hj : j + l = m)
    (f : Cochain (tensor X Y) Z q) (x : X.X i) (y : Y.X j) :
    (((curryIso X Y Z).hom.f q f).v i l hi x).v j m hj y =
      f.v (i + j) m (by omega) (pure X Y rfl x y) :=
  curryDegree_apply X Y Z rfl hi hj f x y

theorem curryIso_natural {X X' Y Y' Z Z' : Comp.{v} R}
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c : Z ⟶ Z') :
    internalHomMap (map a b) c ≫ (curryIso X' Y' Z').hom =
      (curryIso X Y Z).hom ≫ internalHomMap a (internalHomMap b c) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply nestedHom_ext
  intro i j l m hi hj x y
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, curryIso_apply,
    internalHomMap_apply]
  rw [map_on_pure a b i j (i + j) rfl x y]

theorem currying : Specs.DerivedFormalization.CochainTensorTransport.curryingType.{u,v} :=
  fun _R _ => ⟨⟨curryIso, curryIso_apply, curryIso_natural,
    fun X Y Z => currying_differential X Y Z (curryIso X Y Z) (curryIso_apply X Y Z)⟩⟩

end Currying

section Closed

open Specs.DerivedFormalization.CochainTensorTransport (tensorWith homFrom ClosedAdjunction)
open CochainComplex.HomComplex (Cocycle)
open private internalHomIsoCocycles internalHomMapCocycles from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels

/-- Currying restricted to degree-zero cocycles. -/
noncomputable def curryEquiv (X Y Z : Comp.{v} R) :
    (tensor X Y ⟶ Z) ≃ₗ[R] (X ⟶ internalHom Y Z) :=
  (internalHomCyclesZero _ _).trans <|
    (internalHomIsoCocycles (curryIso X Y Z) 0).trans (internalHomCyclesZero _ _).symm

theorem curryEquiv_apply (X Y Z : Comp.{v} R) (f : tensor X Y ⟶ Z)
    (i j : ℤ) (x : X.X i) (y : Y.X j) :
    ((curryEquiv X Y Z f).f i x).v j (i + j) (add_comm j i) y =
      f.f (i + j) (pure X Y rfl x y) := by
  let z := internalHomMapCocycles (curryIso X Y Z).hom 0 (Cocycle.ofHom f)
  have h := congrArg Subtype.val ((internalHomCyclesZero X (internalHom Y Z)).apply_symm_apply z)
  have w := ConcreteCategory.congr_hom (Cochain.congr_v h i i (add_zero i)) x
  change (curryEquiv X Y Z f).f i x =
    ((curryIso X Y Z).hom.f 0 (Cochain.ofHom f)).v i i (add_zero i) x at w
  rw [w, curryIso_apply, Cochain.ofHom_v]

theorem curryEquiv_natural {X X' Y Y' Z Z' : Comp.{v} R}
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c : Z ⟶ Z') (f : tensor X Y ⟶ Z) :
    curryEquiv X' Y' Z' (map a b ≫ f ≫ c) =
      a ≫ curryEquiv X Y Z f ≫ internalHomMap b c := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Cochain.ext
  intro j m hj
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  obtain rfl : m = i + j := by omega
  change ((curryEquiv X' Y' Z' (map a b ≫ f ≫ c)).f i x).v j (i + j) (add_comm j i) y =
    ((internalHomMap b c).f i ((curryEquiv X Y Z f).f i (a.f i x))).v j (i + j) (add_comm j i) y
  rw [curryEquiv_apply, internalHomMap_apply, curryEquiv_apply]
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw [map_on_pure a b i j (i + j) rfl x y]

private theorem mixed_map_id (X Y : Comp.{v} R) : map (𝟙 X) (𝟙 Y) = 𝟙 (tensor X Y) := by
  apply CochainTensor.hom_ext
  intro i j n h x y
  rw [map_on_pure (𝟙 X) (𝟙 Y) i j n h x y]
  rfl

private noncomputable def adjunctionCore (Y : Comp.{v} R) :
    Adjunction.CoreHomEquiv (tensorWith Y) (homFrom Y) where
  homEquiv X Z := (curryEquiv X Y Z).toEquiv
  homEquiv_naturality_left_symm := by
    intro X' X Z a f
    change X ⟶ internalHom Y Z at f
    apply (curryEquiv X' Y Z).injective
    change curryEquiv X' Y Z ((curryEquiv X' Y Z).symm (a ≫ f)) =
      curryEquiv X' Y Z (map a (𝟙 Y) ≫ (curryEquiv X Y Z).symm f)
    rw [LinearEquiv.apply_symm_apply]
    simpa only [Category.comp_id, LinearEquiv.apply_symm_apply, internalHomMap_id] using
      (curryEquiv_natural a (𝟙 Y) (𝟙 Z) ((curryEquiv X Y Z).symm f)).symm
  homEquiv_naturality_right := by
    intro X Z Z' f c
    change curryEquiv X Y Z' (f ≫ c) = curryEquiv X Y Z f ≫ internalHomMap (𝟙 Y) c
    simpa only [mixed_map_id, Category.id_comp] using curryEquiv_natural (𝟙 X) (𝟙 Y) c f

noncomputable def chainAdj (Y : Comp.{v} R) : tensorWith Y ⊣ homFrom Y :=
  Adjunction.mkOfHomEquiv (adjunctionCore Y)

theorem chainAdj_homEquiv (Y X Z : Comp.{v} R) :
    (chainAdj Y).homEquiv X Z = (curryEquiv X Y Z).toEquiv := by
  rw [chainAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

private abbrev q (R : Type u) [CommRing R] := homotopyQuotient.{v} R

private noncomputable def tensorWithK (Y : Comp.{v} R) : K.{v} R ⥤ K.{v} R :=
  CategoryTheory.Quotient.lift _ (tensorWith Y ⋙ q R) fun _ _ _ _ ⟨h⟩ =>
    HomotopyCategory.eq_of_homotopy _ _ (CochainTensor.mapHomotopy h (Homotopy.refl (𝟙 Y)))

private def homFromK (Y : Comp.{v} R) : K.{v} R ⥤ K.{v} R :=
  CategoryTheory.Quotient.lift _ (homFrom Y ⋙ q R) fun _ _ _ _ ⟨h⟩ =>
    HomotopyCategory.eq_of_homotopy _ _ (internalHomMapHomotopy (Homotopy.refl (𝟙 Y)) h)

private noncomputable def homotopyAdj (Y : Comp.{v} R) : tensorWithK Y ⊣ homFromK Y where
  unit := CategoryTheory.Quotient.natTransLift _
    (Functor.whiskerRight (chainAdj Y).unit (q R))
  counit := CategoryTheory.Quotient.natTransLift _
    (Functor.whiskerRight (chainAdj Y).counit (q R))
  left_triangle_components X := by
    obtain ⟨P,rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    change (q R).map ((tensorWith Y).map ((chainAdj Y).unit.app P)) ≫
      (q R).map ((chainAdj Y).counit.app ((tensorWith Y).obj P)) = 𝟙 _
    rw [← (q R).map_comp]
    exact (congrArg ((q R).map) ((chainAdj Y).left_triangle_components P)).trans ((q R).map_id _)
  right_triangle_components X := by
    obtain ⟨P,rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    change (q R).map ((chainAdj Y).unit.app ((homFrom Y).obj P)) ≫
      (q R).map ((homFrom Y).map ((chainAdj Y).counit.app P)) = 𝟙 _
    rw [← (q R).map_comp]
    exact (congrArg ((q R).map) ((chainAdj Y).right_triangle_components P)).trans ((q R).map_id _)

noncomputable def closedAdjunctionModel (Y : Comp.{v} R) : ClosedAdjunction Y where
  adj := chainAdj Y
  left := tensorWithK Y
  right := homFromK Y
  adjK := homotopyAdj Y
  leftFactors := Iso.refl _
  rightFactors := Iso.refl _
  on_pure X Z f i j x y := by
    rw [chainAdj_homEquiv]
    exact curryEquiv_apply X Y Z f i j x y
  counit_on_pure Z i j f y := by
    have h : (chainAdj Y).homEquiv (internalHom Y Z) Z ((chainAdj Y).counit.app Z) =
        𝟙 (internalHom Y Z) := by
      change (chainAdj Y).homEquiv ((homFrom Y).obj Z) Z ((chainAdj Y).counit.app Z) = 𝟙 _
      rw [← (chainAdj Y).homEquiv_symm_id Z, Equiv.apply_symm_apply]
    rw [chainAdj_homEquiv] at h
    change curryEquiv (internalHom Y Z) Y Z ((chainAdj Y).counit.app Z) = 𝟙 _ at h
    have w := curryEquiv_apply (internalHom Y Z) Y Z ((chainAdj Y).counit.app Z) i j f y
    rw [h] at w
    exact w.symm
  homotopy X Z f := by
    change (homotopyAdj Y).homEquiv ((q R).obj X) ((q R).obj Z) (𝟙 _ ≫ (q R).map f) ≫
      𝟙 _ = _
    have he := congrArg ((homotopyAdj Y).homEquiv ((q R).obj X) ((q R).obj Z))
      (Category.id_comp ((q R).map f))
    exact (Category.comp_id _).trans (he.trans
      (((q R).map_comp ((chainAdj Y).unit.app X) ((homFrom Y).map f)).symm))

theorem closedAdjunction : Specs.DerivedFormalization.CochainTensorTransport.closedAdjunctionType.{u,v} :=
  fun Y => ⟨closedAdjunctionModel Y⟩

end Closed

section RingComparison

open scoped TensorProduct
open CategoryTheory.Limits
open CochainTensor (ι tensorCofanIsColimit)
open CochainRingTransport (moduleEquivalence complexEquivalence complexFunctor)
open Specs.DerivedFormalization.CochainTensor (cofan)
open Specs.DerivedFormalization.CochainTensorTransport (RingComparison)

variable {A : Type a} [CommRing A] (e : R ≃+* A)

local notation "ℱ" => (complexFunctor e)
local notation "ℳ" => (Equivalence.functor (moduleEquivalence e))
local notation "𝒢" => (Equivalence.inverse (moduleEquivalence e))

private noncomputable def tensorSummandHom (M N : ModuleCat.{a} R) :
    ModuleCat.of A ((ℳ).obj M ⊗[A] (ℳ).obj N) ⟶ (ℳ).obj (ModuleCat.of R (M ⊗[R] N)) := by
  let T := (ℳ).obj (ModuleCat.of R (M ⊗[R] N))
  let b : (ℳ).obj M →ₗ[A] ((ℳ).obj N →ₗ[A] T) :=
    { toFun := fun x =>
        { toFun := fun y => (show M from x) ⊗ₜ[R] (show N from y)
          map_add' := fun _ _ => TensorProduct.tmul_add _ _ _
          map_smul' := fun r y => by
            change (show M from x) ⊗ₜ[R] (e.symm r • (show N from y)) =
              e.symm r • ((show M from x) ⊗ₜ[R] (show N from y))
            exact TensorProduct.tmul_smul _ _ _ }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        exact TensorProduct.add_tmul _ _ _
      map_smul' := by
        intro r x
        apply LinearMap.ext
        intro y
        change (e.symm r • (show M from x)) ⊗ₜ[R] (show N from y) =
          e.symm r • ((show M from x) ⊗ₜ[R] (show N from y))
        exact TensorProduct.smul_tmul' _ _ _ }
  exact ConcreteCategory.ofHom (C := ModuleCat.{a} A)
    (X := ModuleCat.of A ((ℳ).obj M ⊗[A] (ℳ).obj N)) (Y := T) (TensorProduct.lift b)

private theorem tensorSummandHom_apply (M N : ModuleCat.{a} R)
    (x : (ℳ).obj M) (y : (ℳ).obj N) :
    tensorSummandHom e M N (x ⊗ₜ[A] y) = (show M from x) ⊗ₜ[R] (show N from y) := rfl

private noncomputable def tensorSummandInv (M N : ModuleCat.{a} R) :
    (ℳ).obj (ModuleCat.of R (M ⊗[R] N)) ⟶ ModuleCat.of A ((ℳ).obj M ⊗[A] (ℳ).obj N) := by
  let U := ModuleCat.of A ((ℳ).obj M ⊗[A] (ℳ).obj N)
  let f : M ⊗[R] N →ₗ[R] (𝒢).obj U :=
    TensorProduct.lift
      { toFun := fun x =>
          { toFun := fun y => (show (ℳ).obj M from x) ⊗ₜ[A] (show (ℳ).obj N from y)
            map_add' := fun _ _ => TensorProduct.tmul_add _ _ _
            map_smul' := fun r y => by
              have h : (show (ℳ).obj N from r • y) = e r • (show (ℳ).obj N from y) := by
                change r • y = e.symm (e r) • y
                rw [e.symm_apply_apply]
              change (show (ℳ).obj M from x) ⊗ₜ[A] (show (ℳ).obj N from r • y) =
                e r • ((show (ℳ).obj M from x) ⊗ₜ[A] (show (ℳ).obj N from y))
              rw [h, TensorProduct.tmul_smul] }
        map_add' := by
          intro x y
          apply LinearMap.ext
          intro z
          exact TensorProduct.add_tmul _ _ _
        map_smul' := by
          intro r x
          apply LinearMap.ext
          intro y
          have h : (show (ℳ).obj M from r • x) = e r • (show (ℳ).obj M from x) := by
            change r • x = e.symm (e r) • x
            rw [e.symm_apply_apply]
          change (show (ℳ).obj M from r • x) ⊗ₜ[A] (show (ℳ).obj N from y) =
            e r • ((show (ℳ).obj M from x) ⊗ₜ[A] (show (ℳ).obj N from y))
          rw [h, TensorProduct.smul_tmul'] }
  exact ConcreteCategory.ofHom (C := ModuleCat.{a} A)
    (X := (ℳ).obj (ModuleCat.of R (M ⊗[R] N))) (Y := U)
    { toFun := fun z => f (show M ⊗[R] N from z)
      map_add' := f.map_add
      map_smul' := fun r z => by
        change (show (𝒢).obj U from f (e.symm r • (show M ⊗[R] N from z))) =
          r • (show U from f (show M ⊗[R] N from z))
        rw [map_smul]
        change e (e.symm r) • (show U from f (show M ⊗[R] N from z)) = _
        rw [e.apply_symm_apply] }

private theorem tensorSummandInv_apply (M N : ModuleCat.{a} R) (x : M) (y : N) :
    tensorSummandInv e M N (x ⊗ₜ[R] y) =
      (show (ℳ).obj M from x) ⊗ₜ[A] (show (ℳ).obj N from y) := rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def tensorSummandIso (M N : ModuleCat.{a} R) :
    ModuleCat.of A ((ℳ).obj M ⊗[A] (ℳ).obj N) ≅ (ℳ).obj (ModuleCat.of R (M ⊗[R] N)) where
  hom := tensorSummandHom e M N
  inv := tensorSummandInv e M N
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change tensorSummandInv e M N (tensorSummandHom e M N (x ⊗ₜ[A] y)) = x ⊗ₜ[A] y
    rw [tensorSummandHom_apply, tensorSummandInv_apply]
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    let h := (tensorSummandInv e M N ≫ tensorSummandHom e M N).hom
    change h (show M ⊗[R] N from z) = z
    induction (show M ⊗[R] N from z) using TensorProduct.inductionOn with
    | tmul x y =>
      change tensorSummandHom e M N (tensorSummandInv e M N (x ⊗ₜ[R] y)) = _
      rw [tensorSummandInv_apply, tensorSummandHom_apply]
    | add x y hx hy =>
      have ha := h.map_add x y
      exact ha.trans (congrArg₂ (· + ·) hx hy)

private abbrev TensorDegree (n : ℤ) := {p : ℤ × ℤ // p.1 + p.2 = n}

private noncomputable def mappedCofan (X Y : Comp.{a} R) (n : ℤ) :
    Cofan (fun p : TensorDegree n => (ℳ).obj (ModuleCat.of R (X.X p.1.1 ⊗[R] Y.X p.1.2))) :=
  Cofan.mk (((ℱ).obj (tensor X Y)).X n) (fun p => (ℳ).map (ι X Y p.1.1 p.1.2 n p.2))

private noncomputable def mappedCofanIsColimit (X Y : Comp.{a} R) (n : ℤ) :
    IsColimit (mappedCofan e X Y n) :=
  isColimitCofanMkObjOfIsColimit ℳ
    (fun p : TensorDegree n => ModuleCat.of R (X.X p.1.1 ⊗[R] Y.X p.1.2))
    (fun p => ι X Y p.1.1 p.1.2 n p.2) (tensorCofanIsColimit X Y n)

private noncomputable def tensorTerm (X Y : Comp.{a} R) (n : ℤ) :
    (tensor ((ℱ).obj X) ((ℱ).obj Y)).X n ≅ ((ℱ).obj (tensor X Y)).X n := by
  let c := cofan ((ℱ).obj X) ((ℱ).obj Y) n
  let d := mappedCofan e X Y n
  let hc : IsColimit c := tensorCofanIsColimit ((ℱ).obj X) ((ℱ).obj Y) n
  let hd : IsColimit d := mappedCofanIsColimit e X Y n
  let s (p : TensorDegree n) := tensorSummandIso e (X.X p.1.1) (Y.X p.1.2)
  refine ⟨Cofan.IsColimit.desc hc (fun p => (s p).hom ≫ d.inj p),
    Cofan.IsColimit.desc hd (fun p => (s p).inv ≫ c.inj p), ?_, ?_⟩
  · apply Cofan.IsColimit.hom_ext hc
    intro p
    change c.inj p ≫ (Cofan.IsColimit.desc hc (fun p => (s p).hom ≫ d.inj p) ≫
      Cofan.IsColimit.desc hd (fun p => (s p).inv ≫ c.inj p)) = c.inj p ≫ 𝟙 c.pt
    rw [← Category.assoc, Cofan.IsColimit.fac, Category.assoc, Cofan.IsColimit.fac,
      Iso.hom_inv_id_assoc, Category.comp_id]
  · apply Cofan.IsColimit.hom_ext hd
    intro p
    change d.inj p ≫ (Cofan.IsColimit.desc hd (fun p => (s p).inv ≫ c.inj p) ≫
      Cofan.IsColimit.desc hc (fun p => (s p).hom ≫ d.inj p)) = d.inj p ≫ 𝟙 d.pt
    rw [← Category.assoc, Cofan.IsColimit.fac, Category.assoc, Cofan.IsColimit.fac,
      Iso.inv_hom_id_assoc, Category.comp_id]

private theorem tensorTerm_apply (X Y : Comp.{a} R) {i j n : ℤ} (h : i + j = n)
    (x : X.X i) (y : Y.X j) :
    (tensorTerm e X Y n).hom (pure ((ℱ).obj X) ((ℱ).obj Y) h x y) = pure X Y h x y := by
  let p : TensorDegree n := ⟨(i, j), h⟩
  have w := Cofan.IsColimit.fac (tensorCofanIsColimit ((ℱ).obj X) ((ℱ).obj Y) n)
    (fun p : TensorDegree n =>
      (tensorSummandIso e (X.X p.1.1) (Y.X p.1.2)).hom ≫ (mappedCofan e X Y n).inj p) p
  have ev := ConcreteCategory.congr_hom w ((show ((ℱ).obj X).X i from x) ⊗ₜ[A]
    (show ((ℱ).obj Y).X j from y))
  refine ev.trans ?_
  change (mappedCofan e X Y n).inj p (tensorSummandHom e (X.X i) (Y.X j)
    ((show ((ℱ).obj X).X i from x) ⊗ₜ[A] (show ((ℱ).obj Y).X j from y))) = _
  rw [tensorSummandHom_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The tensor comparison preserves homogeneous generators under a change of ring representative. -/
noncomputable def ringTensorIso (X Y : Comp.{a} R) :
    tensor ((ℱ).obj X) ((ℱ).obj Y) ≅ (ℱ).obj (tensor X Y) :=
  HomologicalComplex.Hom.isoOfComponents (tensorTerm e X Y) (by
    intro n m hm
    change n + 1 = m at hm
    subst m
    apply CochainTensor.term_hom_ext
    intro i j h x y
    change (tensor X Y).d n (n + 1)
      ((tensorTerm e X Y n).hom (pure ((ℱ).obj X) ((ℱ).obj Y) h x y)) =
        (tensorTerm e X Y (n + 1)).hom
          ((tensor ((ℱ).obj X) ((ℱ).obj Y)).d n (n + 1) (pure ((ℱ).obj X) ((ℱ).obj Y) h x y))
    rw [tensorTerm_apply, differential X Y i j n h, differential ((ℱ).obj X) ((ℱ).obj Y) i j n h]
    change _ = (tensorTerm e X Y (n + 1)).hom.hom (_ + i.negOnePow • _)
    rw [map_add, map_sign]
    change _ = (tensorTerm e X Y (n + 1)).hom
      (pure ((ℱ).obj X) ((ℱ).obj Y) (by omega : i + 1 + j = n + 1) (X.d i (i + 1) x) y) +
      i.negOnePow • (tensorTerm e X Y (n + 1)).hom
        (pure ((ℱ).obj X) ((ℱ).obj Y) (by omega : i + (j + 1) = n + 1) x (Y.d j (j + 1) y))
    rw [tensorTerm_apply, tensorTerm_apply])

theorem ringTensorIso_apply (X Y : Comp.{a} R) {i j n : ℤ} (h : i + j = n)
    (x : X.X i) (y : Y.X j) :
    (ringTensorIso e X Y).hom.f n (pure ((ℱ).obj X) ((ℱ).obj Y) h x y) = pure X Y h x y :=
  tensorTerm_apply e X Y h x y

set_option backward.isDefEq.respectTransparency false in
theorem ringTensorIso_natural {X X' Y Y' : Comp.{a} R} (f : X ⟶ X') (g : Y ⟶ Y') :
    map ((ℱ).map f) ((ℱ).map g) ≫ (ringTensorIso e X' Y').hom =
      (ringTensorIso e X Y).hom ≫ (ℱ).map (map f g) := by
  apply CochainTensor.hom_ext
  intro i j n h x y
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  rw [map_on_pure ((ℱ).map f) ((ℱ).map g) i j n h]
  erw [ringTensorIso_apply e X' Y' h (f.f i x) (g.f j y), ringTensorIso_apply e X Y h x y]
  exact (map_on_pure f g i j n h x y).symm

private noncomputable def homTermEquiv (X Y : Comp.{a} R) (q : ℤ) :
    ((ℱ).obj (internalHom X Y)).X q ≃ₗ[A] (internalHom ((ℱ).obj X) ((ℱ).obj Y)).X q where
  toFun f := Cochain.mk fun i j h => (ℳ).map (f.v i j h)
  invFun f := Cochain.mk fun i j h => (ℳ).preimage (f.v i j h)
  left_inv f := by
    apply Cochain.ext
    intro i j h
    simpa only [Cochain.mk_v] using (ℳ).preimage_map (f.v i j h)
  right_inv f := by
    apply Cochain.ext
    intro i j h
    simpa only [Cochain.mk_v] using (ℳ).map_preimage (f.v i j h)
  map_add' f g := by
    apply Cochain.ext
    intro i j h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_smul' r f := by
    apply Cochain.ext
    intro i j h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

private theorem homTermEquiv_eval (X Y : Comp.{a} R) {q i j : ℤ} (h : i + q = j)
    (f : Cochain X Y q) (x : X.X i) :
    (homTermEquiv e X Y q f).v i j h x = f.v i j h x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Homogeneous maps are unchanged as functions when both module actions are transported. -/
noncomputable def ringHomIso (X Y : Comp.{a} R) :
    (ℱ).obj (internalHom X Y) ≅ internalHom ((ℱ).obj X) ((ℱ).obj Y) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => (homTermEquiv e X Y q).toModuleIso) (by
    intro q n h
    change q + 1 = n at h
    subst n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Cochain.ext
    intro i j hj
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (((internalHom ((ℱ).obj X) ((ℱ).obj Y)).d q (q + 1) (homTermEquiv e X Y q f)).v i j hj) x =
      ((homTermEquiv e X Y (q + 1) ((internalHom X Y).d q (q + 1) f)).v i j hj) x
    rw [hom_d_eval hj]
    erw [homTermEquiv_eval e X Y rfl f x,
      homTermEquiv_eval e X Y (by omega : i + 1 + q = j) f (X.d i (i + 1) x),
      homTermEquiv_eval e X Y hj ((internalHom X Y).d q (q + 1) f) x]
    exact (hom_d_eval hj f x).symm)

theorem ringHomIso_eval (X Y : Comp.{a} R) {q i j : ℤ} (h : i + q = j)
    (f : Cochain X Y q) (x : X.X i) :
    (((ringHomIso e X Y).hom.f q f).v i j h) x = f.v i j h x :=
  homTermEquiv_eval e X Y h f x

set_option backward.isDefEq.respectTransparency false in
theorem ringHomIso_natural {X X' Y Y' : Comp.{a} R} (f : X' ⟶ X) (g : Y ⟶ Y') :
    (ℱ).map (internalHomMap f g) ≫ (ringHomIso e X' Y').hom =
      (ringHomIso e X Y).hom ≫ internalHomMap ((ℱ).map f) ((ℱ).map g) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro i j h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (((ringHomIso e X' Y').hom.f q ((internalHomMap f g).f q z)).v i j h) x =
    (((internalHomMap ((ℱ).map f) ((ℱ).map g)).f q ((ringHomIso e X Y).hom.f q z)).v i j h) x
  rw [internalHomMap_apply]
  erw [ringHomIso_eval e X' Y' h ((internalHomMap f g).f q z) x, internalHomMap_apply,
    ringHomIso_eval e X Y h z (f.f i x)]
  rfl


private theorem acyclicIso {S : Type*} [CommRing S] {X Y : Comp S} (f : X ≅ Y) :
    X.Acyclic ↔ Y.Acyclic := by
  refine ⟨fun h i => ?_, fun h i => ?_⟩
  · rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (h i).isZero_homology.of_iso (((cohomologyFunctor S i).mapIso f).symm)
  · rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (h i).isZero_homology.of_iso ((cohomologyFunctor S i).mapIso f)

private theorem ringAcyclic (X : Comp.{a} R) : ((ℱ).obj X).Acyclic ↔ X.Acyclic :=
  (CochainRingTransport.complexProperties e X X (𝟙 X)).1

private theorem transportAcyclicTest (TR : Comp.{a} R → Comp.{a} R)
    (TA : Comp.{a} A → Comp.{a} A)
    (compare : ∀ X, TA ((ℱ).obj X) ≅ (ℱ).obj (TR X))
    (congrIso : ∀ {X Y : Comp.{a} A}, (X ≅ Y) → (TA X ≅ TA Y)) :
    (∀ X : Comp.{a} A, X.Acyclic → (TA X).Acyclic) ↔
      (∀ X : Comp.{a} R, X.Acyclic → (TR X).Acyclic) := by
  refine ⟨fun h X hX => ?_, fun h Y hY => ?_⟩
  · exact (ringAcyclic e _).1 ((acyclicIso (compare X)).1 (h _ ((ringAcyclic e X).2 hX)))
  · let X := (complexEquivalence e).inverse.obj Y
    let i : (ℱ).obj X ≅ Y := (complexEquivalence e).counitIso.app Y
    have hX : X.Acyclic := (ringAcyclic e X).1 ((acyclicIso i).2 hY)
    exact (acyclicIso (congrIso i)).1 ((acyclicIso (compare X)).2 ((ringAcyclic e _).2 (h X hX)))

open Specs.DerivedFormalization.CochainTensorTransport (tensorWith homFrom)

private def precompIso {X Y Z : Comp.{v} R} (i : X ≅ Y) :
    internalHom X Z ≅ internalHom Y Z where
  hom := internalHomMap i.inv (𝟙 Z)
  inv := internalHomMap i.hom (𝟙 Z)
  hom_inv_id := by rw [internalHomMap_comp, i.hom_inv_id, Category.id_comp, internalHomMap_id]
  inv_hom_id := by rw [internalHomMap_comp, i.inv_hom_id, Category.id_comp, internalHomMap_id]

noncomputable def ringComparisonModel : RingComparison e where
  tensorIso := ringTensorIso e
  tensor_on_pure := ringTensorIso_apply e
  tensor_natural := ringTensorIso_natural e
  homIso := ringHomIso e
  hom_on_eval := ringHomIso_eval e
  hom_natural := ringHomIso_natural e
  kFlat X := transportAcyclicTest e (fun Y => tensor Y X) (fun Y => tensor Y ((ℱ).obj X))
    (fun Y => ringTensorIso e Y X) (fun i => (tensorWith ((ℱ).obj X)).mapIso i)
  kProjective X := by
    change IsKProjective ((ℱ).obj X) ↔ IsKProjective X
    rw [isKProjective_iff_internalHom_acyclic, isKProjective_iff_internalHom_acyclic]
    exact transportAcyclicTest e (internalHom X) (internalHom ((ℱ).obj X))
      (fun Y => (ringHomIso e X Y).symm) (fun i => (homFrom ((ℱ).obj X)).mapIso i)
  kInjective X := by
    change IsKInjective ((ℱ).obj X) ↔ IsKInjective X
    rw [isKInjective_iff_internalHom_acyclic, isKInjective_iff_internalHom_acyclic]
    exact transportAcyclicTest e (fun Y => internalHom Y X) (fun Y => internalHom Y ((ℱ).obj X))
      (fun Y => (ringHomIso e Y X).symm) (fun i => precompIso i)

theorem ringComparison : Specs.DerivedFormalization.CochainTensorTransport.ringComparisonType.{u,a} :=
  fun e => ⟨ringComparisonModel e⟩

end RingComparison

section AdequateModels

open CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal (μ ε)
open CategoryTheory.Functor.Monoidal (μIso εIso)
open CochainRingTransport (complexFunctor homotopyFunctor homotopyEquivalence rankOneComparison)
open Specs.DerivedFormalization.CochainTensorTransport
  (representedUnit representedUnitZero tensorWith homFrom AdequateModel)

variable {A : Type a} [CommRing A] (e : R ≃+* A)

local notation "ℱ" => (complexFunctor e)
local notation "ℱK" => (homotopyFunctor e)
private abbrev quotientOriginal (_ : R ≃+* A) : Comp.{a} R ⥤ K.{a} R := homotopyQuotient R
private abbrev quotientRepresentative (_ : R ≃+* A) : Comp.{a} A ⥤ K.{a} A := homotopyQuotient A

local notation "qR" => (quotientOriginal e)
local notation "qA" => (quotientRepresentative e)
local notation "EK" => (homotopyEquivalence e)

noncomputable section

private def assocComparison (X Y Z : Comp.{a} R) :
    (ℱ).obj (tensor (tensor X Y) Z) ≅ (ℱ).obj (tensor X (tensor Y Z)) :=
  (ringTensorIso e (tensor X Y) Z).symm ≪≫
    MonoidalCategory.tensorIso (ringTensorIso e X Y).symm (Iso.refl _) ≪≫
    α_ ((ℱ).obj X) ((ℱ).obj Y) ((ℱ).obj Z) ≪≫
    MonoidalCategory.tensorIso (Iso.refl _) (ringTensorIso e Y Z) ≪≫
    ringTensorIso e X (tensor Y Z)

private def leftUnitComparison (X : Comp.{a} R) :
    (ℱ).obj (tensor (representedUnit e) X) ≅ (ℱ).obj X :=
  (ringTensorIso e (representedUnit e) X).symm ≪≫
    MonoidalCategory.tensorIso (rankOneComparison e) (Iso.refl _) ≪≫ λ_ ((ℱ).obj X)

private def rightUnitComparison (X : Comp.{a} R) :
    (ℱ).obj (tensor X (representedUnit e)) ≅ (ℱ).obj X :=
  (ringTensorIso e X (representedUnit e)).symm ≪≫
    MonoidalCategory.tensorIso (Iso.refl _) (rankOneComparison e) ≪≫ ρ_ ((ℱ).obj X)

@[instance_reducible]
private def originalMonoidalStruct : MonoidalCategoryStruct (Comp.{a} R) where
  tensorObj := tensor
  tensorHom := map
  whiskerLeft X _ _ f := map (𝟙 X) f
  whiskerRight f Y := map f (𝟙 Y)
  tensorUnit := representedUnit e
  associator X Y Z := (ℱ).preimageIso (assocComparison e X Y Z)
  leftUnitor X := (ℱ).preimageIso (leftUnitComparison e X)
  rightUnitor X := (ℱ).preimageIso (rightUnitComparison e X)

set_option backward.isDefEq.respectTransparency false in
private def inducingData :
    letI := originalMonoidalStruct e
    Monoidal.InducingFunctorData (ℱ) := by
  letI := originalMonoidalStruct e
  refine {

    μIso := ringTensorIso e
    εIso := (rankOneComparison e).symm
    whiskerLeft_eq X {Y₁ Y₂} g := by
      change (ℱ).map (map (𝟙 X) g) = _
      apply (ringTensorIso e X Y₁).eq_inv_comp.2
      have h := (ringTensorIso_natural e (𝟙 X) g).symm
      change _ = ((ℱ).map (𝟙 X) ⊗ₘ (ℱ).map g) ≫ _ at h
      simpa only [(ℱ).map_id, id_tensorHom] using h
    whiskerRight_eq {X₁ X₂} f Y := by
      change (ℱ).map (map f (𝟙 Y)) = _
      apply (ringTensorIso e X₁ Y).eq_inv_comp.2
      have h := (ringTensorIso_natural e f (𝟙 Y)).symm
      change _ = ((ℱ).map f ⊗ₘ (ℱ).map (𝟙 Y)) ≫ _ at h
      simpa only [(ℱ).map_id, tensorHom_id] using h
    tensorHom_eq {X₁ Y₁ X₂ Y₂} f g := by
      change (ℱ).map (map f g) = _
      exact (ringTensorIso e X₁ X₂).eq_inv_comp.2 (ringTensorIso_natural e f g).symm
    associator_eq X Y Z := by
      change (ℱ).map ((ℱ).preimageIso (assocComparison e X Y Z)).hom = _
      calc
        _ = (assocComparison e X Y Z).hom := (ℱ).map_preimage _
        _ = _ := by simp only [assocComparison, Iso.trans_assoc] <;> rfl
    leftUnitor_eq X := by
      change (ℱ).map ((ℱ).preimageIso (leftUnitComparison e X)).hom = _
      calc
        _ = (leftUnitComparison e X).hom := (ℱ).map_preimage _
        _ = _ := by simp only [leftUnitComparison, Iso.trans_assoc] <;> rfl
    rightUnitor_eq X := by
      change (ℱ).map ((ℱ).preimageIso (rightUnitComparison e X)).hom = _
      calc
        _ = (rightUnitComparison e X).hom := (ℱ).map_preimage _
        _ = _ := by simp only [rightUnitComparison, Iso.trans_assoc] <;> rfl }

@[instance_reducible]
private def originalChainMonoidal : MonoidalCategory (Comp.{a} R) :=
  letI := originalMonoidalStruct e
  Monoidal.induced (ℱ) (inducingData e)

@[instance_reducible]
private def ringMonoidal :
    letI := originalChainMonoidal e
    (ℱ).Monoidal :=
  letI := originalMonoidalStruct e
  Monoidal.fromInducedMonoidal (ℱ) (inducingData e)

@[instance_reducible]
private def originalChainSymmetric :
    letI := originalChainMonoidal e
    SymmetricCategory (Comp.{a} R) :=
  letI := originalChainMonoidal e
  letI := ringMonoidal e
  SymmetricCategory.ofFullyFaithful (ℱ)

set_option backward.isDefEq.respectTransparency false in
@[instance_reducible]
private def ringBraided :
    letI := originalChainMonoidal e
    letI := originalChainSymmetric e
    (ℱ).Braided := by
  letI := originalChainMonoidal e
  letI := originalChainSymmetric e
  letI := ringMonoidal e
  refine { toMonoidal := ringMonoidal e, braided := fun X Y => ?_ }
  change μ (ℱ) X Y ≫ (ℱ).map ((ℱ).preimageIso
    ((μIso (ℱ) X Y).symm ≪≫ β_ ((ℱ).obj X) ((ℱ).obj Y) ≪≫ μIso (ℱ) Y X)).hom =
    (β_ ((ℱ).obj X) ((ℱ).obj Y)).hom ≫ μ (ℱ) Y X
  simp only [Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv, Functor.Monoidal.μ_δ_assoc]

open CochainRingTransport (homotopyFactors)

@[instance_reducible]
private def originalHomotopyMonoidal : MonoidalCategory (K.{a} R) :=
  Monoidal.transport (EK).symm

@[instance_reducible]
private def originalHomotopySymmetric :
    letI := originalHomotopyMonoidal e
    SymmetricCategory (K.{a} R) :=
  inferInstanceAs (SymmetricCategory (Monoidal.Transported (EK).symm))

@[instance_reducible]
private def ringHomotopyBraided :
    letI := originalHomotopyMonoidal e
    letI := originalHomotopySymmetric e
    (ℱK).Braided :=
  inferInstanceAs ((Monoidal.equivalenceTransported (EK).symm).inverse.Braided)

@[instance_reducible]
private def inverseHomotopyBraided :
    letI := originalHomotopyMonoidal e
    letI := originalHomotopySymmetric e
    (EK).inverse.Braided :=
  inferInstanceAs ((Monoidal.equivalenceTransported (EK).symm).functor.Braided)

private def quotientTransportIso : ((ℱ) ⋙ qA) ⋙ (EK).inverse ≅ qR :=
  Functor.isoWhiskerRight (homotopyFactors e).symm (EK).inverse ≪≫
    Functor.associator qR (ℱK) (EK).inverse ≪≫
    Functor.isoWhiskerLeft qR (EK).unitIso.symm ≪≫ (qR).rightUnitor

@[instance_reducible]
private def originalQuotientBraided :
    letI := originalChainMonoidal e
    letI := originalChainSymmetric e
    letI := originalHomotopyMonoidal e
    letI := originalHomotopySymmetric e
    (qR).Braided := by
  letI := originalChainMonoidal e
  letI := originalChainSymmetric e
  letI := ringBraided e
  letI := originalHomotopyMonoidal e
  letI := originalHomotopySymmetric e
  letI := inverseHomotopyBraided e
  letI : (qR).Monoidal := Functor.Monoidal.transport (quotientTransportIso e)
  letI := Functor.Monoidal.natTransIsMonoidal_of_transport (quotientTransportIso e)
  exact { toMonoidal := inferInstance
          braided := (Functor.LaxBraided.ofNatIso (quotientTransportIso e)).braided }

set_option backward.isDefEq.respectTransparency false in
private theorem quotientFactorsMonoidal :
    letI := originalChainMonoidal e
    letI := originalChainSymmetric e
    letI := ringBraided e
    letI := originalHomotopyMonoidal e
    letI := originalHomotopySymmetric e
    letI := ringHomotopyBraided e
    letI := originalQuotientBraided e
    NatTrans.IsMonoidal (homotopyFactors e).hom := by
  letI := originalChainMonoidal e
  letI := originalChainSymmetric e
  letI := ringBraided e
  letI := originalHomotopyMonoidal e
  letI := originalHomotopySymmetric e
  letI := ringHomotopyBraided e
  letI := inverseHomotopyBraided e
  letI := originalQuotientBraided e
  letI : NatTrans.IsMonoidal (quotientTransportIso e).hom :=
    Functor.Monoidal.natTransIsMonoidal_of_transport (quotientTransportIso e)
  letI : (EK).functor.Braided := ringHomotopyBraided e
  letI : NatTrans.IsMonoidal (EK).counitIso.hom :=
    inferInstanceAs (NatTrans.IsMonoidal (Monoidal.equivalenceTransported (EK).symm).unitIso.inv)
  let i := Functor.isoWhiskerRight (quotientTransportIso e).symm (ℱK) ≪≫
    Functor.associator ((ℱ) ⋙ qA) (EK).inverse (ℱK) ≪≫
    Functor.isoWhiskerLeft ((ℱ) ⋙ qA) (EK).counitIso ≪≫ ((ℱ) ⋙ qA).rightUnitor
  have hi : i.hom = (homotopyFactors e).hom := by
    ext X
    simp only [i, quotientTransportIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
      NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.rightUnitor_hom_app, Functor.rightUnitor_inv_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj, Functor.map_comp,
      Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc]
    have he := (EK).counit_naturality ((homotopyFactors e).hom.app X)
    erw [Category.comp_id, he]
    rw [← Category.assoc]
    exact congrArg (fun f => f ≫ (homotopyFactors e).hom.app X)
      ((EK).functor_unit_comp ((qR).obj X)) |>.trans (Category.id_comp _)
  rw [← hi]
  change NatTrans.IsMonoidal
    (Functor.whiskerRight (quotientTransportIso e).inv (ℱK) ≫
      (Functor.associator ((ℱ) ⋙ qA) (EK).inverse (ℱK)).hom ≫
      Functor.whiskerLeft ((ℱ) ⋙ qA) (EK).counitIso.hom ≫ ((ℱ) ⋙ qA).rightUnitor.hom)
  infer_instance

open Specs.DerivedFormalization.CochainTensorTransport (ClosedAdjunction)

private def exactTensorRight (Y : Comp.{a} R) :
    letI := originalChainMonoidal e
    tensorRight Y ≅ tensorWith Y := by
  letI := originalChainMonoidal e
  exact Iso.refl _

@[instance_reducible]
private def originalChainClosed :
    letI := originalChainMonoidal e
    MonoidalClosed (Comp.{a} R) := by
  letI := originalChainMonoidal e
  letI := originalChainSymmetric e
  exact ⟨fun Y => ⟨homFrom Y, (chainAdj Y).ofNatIsoLeft
    ((exactTensorRight e Y).symm ≪≫ (BraidedCategory.tensorLeftIsoTensorRight Y).symm)⟩⟩

private def quotientTensorRight (Y : Comp.{a} R) :
    letI := originalHomotopyMonoidal e
    tensorRight ((qR).obj Y) ≅ (closedAdjunctionModel Y).left := by
  letI := originalChainMonoidal e
  letI := originalChainSymmetric e
  letI := originalHomotopyMonoidal e
  letI := originalHomotopySymmetric e
  letI := originalQuotientBraided e
  exact CategoryTheory.Quotient.natIsoLift _
    (Functor.Monoidal.commTensorRight qR Y ≪≫
      Functor.isoWhiskerRight (exactTensorRight e Y) qR ≪≫ (closedAdjunctionModel Y).leftFactors.symm)

@[instance_reducible]
private def originalHomotopyClosed :
    letI := originalHomotopyMonoidal e
    MonoidalClosed (K.{a} R) := by
  letI := originalHomotopyMonoidal e
  letI := originalHomotopySymmetric e
  refine ⟨fun Y => ?_⟩
  let B := closedAdjunctionModel Y.as
  exact ⟨B.right, B.adjK.ofNatIsoLeft
    ((quotientTensorRight e Y.as).symm ≪≫ (BraidedCategory.tensorLeftIsoTensorRight Y).symm)⟩

private theorem chainClosed_homEquiv (X Y Z : Comp.{a} R) (f : tensor X Y ⟶ Z) :
    letI := originalChainMonoidal e
    letI := originalChainSymmetric e
    letI := originalChainClosed e
    ((ihom.adjunction Y).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight Y)).homEquiv X Z f =
      (chainAdj Y).homEquiv X Z f := by
  letI := originalChainMonoidal e
  letI := originalChainSymmetric e
  letI := originalChainClosed e
  change (((chainAdj Y).ofNatIsoLeft
    ((exactTensorRight e Y).symm ≪≫ (BraidedCategory.tensorLeftIsoTensorRight Y).symm)).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight Y)).homEquiv X Z f = _
  simp only [Adjunction.homEquiv_ofNatIsoLeft_apply, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  exact congrArg ((chainAdj Y).homEquiv X Z) (Category.id_comp f)

set_option backward.isDefEq.respectTransparency false in
private theorem homotopyClosed_homEquiv (X Y Z : Comp.{a} R) (f : tensor X Y ⟶ Z) :
    letI := originalChainMonoidal e
    letI := originalChainSymmetric e
    letI := originalHomotopyMonoidal e
    letI := originalHomotopySymmetric e
    letI := originalHomotopyClosed e
    letI := originalQuotientBraided e
    ((ihom.adjunction ((qR).obj Y)).ofNatIsoLeft
      (BraidedCategory.tensorLeftIsoTensorRight ((qR).obj Y))).homEquiv ((qR).obj X) ((qR).obj Z)
      (μ qR X Y ≫ (qR).map f) = (qR).map ((chainAdj Y).homEquiv X Z f) := by
  letI := originalChainMonoidal e
  letI := originalChainSymmetric e
  letI := originalHomotopyMonoidal e
  letI := originalHomotopySymmetric e
  letI := originalHomotopyClosed e
  letI := originalQuotientBraided e
  let B := closedAdjunctionModel Y
  let s := quotientTensorRight e Y
  change ((B.adjK.ofNatIsoLeft
      (s.symm ≪≫ (BraidedCategory.tensorLeftIsoTensorRight ((qR).obj Y)).symm)).ofNatIsoLeft
      (BraidedCategory.tensorLeftIsoTensorRight ((qR).obj Y))).homEquiv ((qR).obj X) ((qR).obj Z)
      (μ qR X Y ≫ (qR).map f) = _
  simp only [Adjunction.homEquiv_ofNatIsoLeft_apply, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  have hs : s.hom.app ((qR).obj X) = μ qR X Y := by
    change μ qR X Y ≫ (qR).map (𝟙 _) ≫ 𝟙 _ = _
    simp only [(qR).map_id, Category.comp_id]
  rw [← hs, Iso.inv_hom_id_app_assoc]
  have h := B.homotopy X Z f
  change B.adjK.homEquiv ((qR).obj X) ((qR).obj Z) (𝟙 _ ≫ (qR).map f) ≫ 𝟙 _ =
    (qR).map ((chainAdj Y).homEquiv X Z f) at h
  simpa only [Category.id_comp, Category.comp_id] using h

private theorem nativeTensorMap_apply {X X' Y Y' : Comp.{a} A} (f : X ⟶ X') (g : Y ⟶ Y')
    {i j n : ℤ} (h : i + j = n) (x : X.X i) (y : Y.X j) :
    (f ⊗ₘ g).f n (pure X Y h x y) = pure X' Y' h (f.f i x) (g.f j y) :=
  map_on_pure f g i j n h x y

set_option backward.isDefEq.respectTransparency false in
private theorem ringTensorInv_apply (X Y : Comp.{a} R) {i j n : ℤ} (h : i + j = n)
    (x : X.X i) (y : Y.X j) :
    (ringTensorIso e X Y).inv.f n (pure X Y h x y) = pure ((ℱ).obj X) ((ℱ).obj Y) h x y := by
  let s := ringTensorIso e X Y
  have w := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f n) s.hom_inv_id) (pure ((ℱ).obj X) ((ℱ).obj Y) h x y)
  change s.inv.f n (s.hom.f n (pure ((ℱ).obj X) ((ℱ).obj Y) h x y)) = _
    at w
  exact (congrArg (fun z => s.inv.f n z) (ringTensorIso_apply e X Y h x y)).symm.trans w

private theorem rankOneComparison_zero (r : A) :
    (rankOneComparison e).hom.f 0 ((representedUnitZero e).inv r) =
      (cochainTensorUnitZero A).inv r := by
  rfl

set_option maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency false in
private theorem assoc_on_generators (X Y Z : Comp.{a} R) (i j k : ℤ) {m l n : ℤ}
    (h : i + j = m) (hn : m + k = n) (h' : j + k = l) (hn' : i + l = n)
    (x : X.X i) (y : Y.X j) (z : Z.X k) :
    letI := originalChainMonoidal e
    (α_ X Y Z).hom.f n (pure (tensor X Y) Z hn (pure X Y h x y) z) =
      pure X (tensor Y Z) hn' x (pure Y Z h' y z) := by
  letI := originalChainMonoidal e
  have w : (ℱ).map (α_ X Y Z).hom = (assocComparison e X Y Z).hom := (ℱ).map_preimage _
  change ((ℱ).map (α_ X Y Z).hom).f n (pure (tensor X Y) Z hn (pure X Y h x y) z) = _
  rw [w]
  simp only [assocComparison, Iso.trans_hom, Iso.symm_hom, MonoidalCategory.tensorIso_hom,
    Iso.refl_hom, HomologicalComplex.comp_f, ModuleCat.comp_apply]
  erw [ringTensorInv_apply e (tensor X Y) Z hn (pure X Y h x y) z]
  erw [nativeTensorMap_apply (ringTensorIso e X Y).inv (𝟙 ((ℱ).obj Z)) hn (pure X Y h x y) z]
  erw [ringTensorInv_apply e X Y h x y]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  erw [cochainTensorAssociator_apply ((ℱ).obj X) ((ℱ).obj Y) ((ℱ).obj Z) i j k h hn h' hn' x y z]
  erw [nativeTensorMap_apply (𝟙 ((ℱ).obj X)) (ringTensorIso e Y Z).hom hn' x
    (pure ((ℱ).obj Y) ((ℱ).obj Z) h' y z)]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  erw [ringTensorIso_apply e Y Z h' y z, ringTensorIso_apply e X (tensor Y Z) hn' x (pure Y Z h' y z)]

set_option backward.isDefEq.respectTransparency false in
private theorem leftUnit_on_generators (X : Comp.{a} R) (i : ℤ) (r : A) (x : X.X i) :
    letI := originalChainMonoidal e
    (λ_ X).hom.f i (pure (representedUnit e) X (zero_add i) ((representedUnitZero e).inv r) x) =
      e.symm r • x := by
  letI := originalChainMonoidal e
  have w : (ℱ).map (λ_ X).hom = (leftUnitComparison e X).hom := (ℱ).map_preimage _
  change ((ℱ).map (λ_ X).hom).f i
    (pure (representedUnit e) X (zero_add i) ((representedUnitZero e).inv r) x) = _
  rw [w]
  simp only [leftUnitComparison, Iso.trans_hom, Iso.symm_hom, MonoidalCategory.tensorIso_hom,
    Iso.refl_hom, HomologicalComplex.comp_f, ModuleCat.comp_apply]
  erw [ringTensorInv_apply e (representedUnit e) X (zero_add i) ((representedUnitZero e).inv r) x]
  erw [nativeTensorMap_apply, rankOneComparison_zero]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  exact cochainTensorLeftUnitor_apply ((ℱ).obj X) i r x

set_option backward.isDefEq.respectTransparency false in
private theorem rightUnit_on_generators (X : Comp.{a} R) (i : ℤ) (x : X.X i) (r : A) :
    letI := originalChainMonoidal e
    (ρ_ X).hom.f i (pure X (representedUnit e) (add_zero i) x ((representedUnitZero e).inv r)) =
      e.symm r • x := by
  letI := originalChainMonoidal e
  have w : (ℱ).map (ρ_ X).hom = (rightUnitComparison e X).hom := (ℱ).map_preimage _
  change ((ℱ).map (ρ_ X).hom).f i
    (pure X (representedUnit e) (add_zero i) x ((representedUnitZero e).inv r)) = _
  rw [w]
  simp only [rightUnitComparison, Iso.trans_hom, Iso.symm_hom, MonoidalCategory.tensorIso_hom,
    Iso.refl_hom, HomologicalComplex.comp_f, ModuleCat.comp_apply]
  erw [ringTensorInv_apply e X (representedUnit e) (add_zero i) x ((representedUnitZero e).inv r)]
  erw [nativeTensorMap_apply, rankOneComparison_zero]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  exact cochainTensorRightUnitor_apply ((ℱ).obj X) i x r

set_option backward.isDefEq.respectTransparency false in
private theorem braiding_on_generators (X Y : Comp.{a} R) {i j n : ℤ} (h : i + j = n)
    (x : X.X i) (y : Y.X j) :
    letI := originalChainMonoidal e
    letI := originalChainSymmetric e
    (β_ X Y).hom.f n (pure X Y h x y) =
      (i * j).negOnePow • pure Y X (by omega : j + i = n) y x := by
  letI := originalChainMonoidal e
  letI := originalChainSymmetric e
  letI := ringBraided e
  have w : (ℱ).map (β_ X Y).hom =
      (ringTensorIso e X Y).inv ≫ (β_ ((ℱ).obj X) ((ℱ).obj Y)).hom ≫
        (ringTensorIso e Y X).hom :=
    Functor.map_braiding (ℱ) X Y
  change ((ℱ).map (β_ X Y).hom).f n (pure X Y h x y) = _
  rw [w]
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  erw [ringTensorInv_apply e X Y h x y,
    cochainTensorBraiding_apply ((ℱ).obj X) ((ℱ).obj Y) i j h x y]
  change ((ringTensorIso e Y X).hom.f n).hom
    ((i * j).negOnePow • pure ((ℱ).obj Y) ((ℱ).obj X) (by omega : j + i = n) y x) = _
  rw [map_sign]
  change (i * j).negOnePow •
    (ringTensorIso e Y X).hom.f n (pure ((ℱ).obj Y) ((ℱ).obj X) (by omega : j + i = n) y x) = _
  erw [ringTensorIso_apply e Y X (by omega : j + i = n) y x]

private theorem tensorIso_identity {C : Type*} [Category* C] [MonoidalCategory C] (X Y : C) :
    MonoidalCategory.tensorIso (Iso.refl X) (Iso.refl Y) = Iso.refl (X ⊗ Y) := by
  apply Iso.ext
  exact id_tensorHom_id X Y

set_option backward.isDefEq.respectTransparency false in
/-- The signed tensor, Hom and represented unit on the original cochain and homotopy categories. -/
def adequateModelData : AdequateModel e := by
  letI := originalChainMonoidal e
  letI := originalChainSymmetric e
  letI := originalChainClosed e
  letI := ringBraided e
  letI := originalHomotopyMonoidal e
  letI := originalHomotopySymmetric e
  letI := originalHomotopyClosed e
  letI := ringHomotopyBraided e
  letI := originalQuotientBraided e
  refine {
    toRingComparison := ringComparisonModel e
    chainMonoidal := originalChainMonoidal e
    chainSymmetric := originalChainSymmetric e
    chainClosed := originalChainClosed e
    homotopyMonoidal := originalHomotopyMonoidal e
    homotopySymmetric := originalHomotopySymmetric e
    homotopyClosed := originalHomotopyClosed e
    nativeSymmetric := cochainSymmetricCategory
    nativeKoszul := cochainTensorBraiding_apply
    nativeHomotopyMonoidal := homotopyMonoidalCategory
    nativeHomotopySymmetric := homotopySymmetricCategory
    chainTransport := ringBraided e
    homotopyTransport := ringHomotopyBraided e
    quotientBraided := originalQuotientBraided e
    nativeQuotientBraided := homotopyQuotientBraided
    nativeQuotientModels := ⟨⟨rfl, rfl⟩, fun X Y => ⟨rfl, rfl⟩⟩
    quotientTransport := quotientFactorsMonoidal e
    tensorModel := fun _ _ => Iso.refl _
    unitModel := Iso.refl _
    homModel := fun _ => Iso.refl _
    rawClosed := closedAdjunctionModel
    homotopyHomModel := fun _ => Iso.refl _
    tensorModel_transport := ?_
    unitModel_transport := ?_
    tensorModel_natural := ?_
    chainAdjunction := ?_
    homotopyAdjunction := ?_
    associator_on_pure := ?_
    leftUnitor_on_pure := ?_
    rightUnitor_on_pure := ?_
    braiding_on_pure := ?_ }
  · intro X Y
    change (ringTensorIso e X Y).hom = (ringTensorIso e X Y).hom ≫ (ℱ).map (𝟙 _)
    rw [(ℱ).map_id, Category.comp_id]
  · change (rankOneComparison e).inv = (rankOneComparison e).inv ≫ (ℱ).map (𝟙 _)
    rw [(ℱ).map_id, Category.comp_id]
  · intro X X' Y Y' f g
    change map f g ≫ 𝟙 _ = 𝟙 _ ≫ map f g
    rw [Category.comp_id, Category.id_comp]
  · intro Y X Z f
    change _ ≫ 𝟙 _ = (chainAdj Y).homEquiv X Z (𝟙 _ ≫ f)
    rw [Category.comp_id, Category.id_comp]
    exact chainClosed_homEquiv e X Y Z f
  · intro Y X Z f
    change ((ihom.adjunction ((qR).obj Y)).ofNatIsoLeft
      (BraidedCategory.tensorLeftIsoTensorRight ((qR).obj Y))).homEquiv ((qR).obj X) ((qR).obj Z)
      ((μ qR X Y ≫ (qR).map (𝟙 _)) ≫ (qR).map f) ≫ 𝟙 _ ≫ 𝟙 _ = _
    simp only [(qR).map_id, Category.comp_id]
    exact homotopyClosed_homEquiv e X Y Z f
  · intro X Y Z i j k m l n h hn h' hn' x y z
    simp only [Iso.refl_trans, Iso.trans_refl, tensorIso_identity, Iso.refl_symm, Iso.trans_hom,
      Iso.refl_hom, Category.comp_id]
    exact assoc_on_generators e X Y Z i j k h hn h' hn' x y z
  · intro X i r x
    simp only [Iso.refl_trans, tensorIso_identity]
    exact leftUnit_on_generators e X i r x
  · intro X i x r
    simp only [Iso.refl_trans, tensorIso_identity]
    exact rightUnit_on_generators e X i x r
  · intro X Y i j n h x y
    simp only [Iso.refl_trans, Iso.trans_refl, Iso.refl_symm, Iso.trans_hom, Iso.refl_hom,
      Category.comp_id]
    exact braiding_on_generators e X Y h x y

theorem adequateModel : Specs.DerivedFormalization.CochainTensorTransport.adequateModelType.{u,a} :=
  fun e => ⟨adequateModelData e⟩

end

end AdequateModels

section AdjunctionComparison

open CochainRingTransport (complexFunctor)

variable {A : Type a} [CommRing A] (e : R ≃+* A)

local notation "ℱ" => (complexFunctor e)

set_option backward.isDefEq.respectTransparency false in
/-- The represented and original adjunctions agree under the tensor and Hom comparisons. -/
theorem ringAdjunction_homEquiv (X Y Z : Comp.{a} R) (f : tensor X Y ⟶ Z) :
    (ℱ).map ((chainAdj Y).homEquiv X Z f) ≫ (ringHomIso e Y Z).hom =
      (cochainTensorHomAdjunction ((ℱ).obj Y)).homEquiv ((ℱ).obj X) ((ℱ).obj Z)
        ((ringTensorIso e X Y).hom ≫ (ℱ).map f) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Cochain.ext
  intro j n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  obtain rfl : n = i + j := by omega
  rw [cochainTensorHomAdjunction_homEquiv, chainAdj_homEquiv]
  change (((ringHomIso e Y Z).hom.f i ((curryEquiv X Y Z f).f i x)).v j (i + j) (add_comm j i)) y =
    ((tensorHomEquiv ((ℱ).obj X) ((ℱ).obj Y) ((ℱ).obj Z)
      ((ringTensorIso e X Y).hom ≫ (ℱ).map f)).f i x).v j (i + j) (add_comm j i) y
  erw [ringHomIso_eval e Y Z (add_comm j i) ((curryEquiv X Y Z f).f i x) y]
  rw [curryEquiv_apply X Y Z f i j x y, tensorHomEquiv_apply]
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  erw [ringTensorIso_apply e X Y (rfl : i + j = i + j) x y]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The same comparison holds on homotopy classes of morphisms. -/
theorem ringAdjunction_homotopy (X Y Z : Comp.{a} R) (f : tensor X Y ⟶ Z) :
    let qA := homotopyQuotient.{a} A
    qA.map ((ℱ).map ((chainAdj Y).homEquiv X Z f)) ≫ qA.map (ringHomIso e Y Z).hom =
      (homotopyTensorHomAdjunction ((ℱ).obj Y)).homEquiv (qA.obj ((ℱ).obj X)) (qA.obj ((ℱ).obj Z))
        (qA.map ((ringTensorIso e X Y).hom ≫ (ℱ).map f)) := by
  dsimp only
  rw [← (homotopyQuotient.{a} A).map_comp]
  exact (congrArg ((homotopyQuotient.{a} A).map) (ringAdjunction_homEquiv e X Y Z f)).trans
    (homotopyTensorHomAdjunction_map ((ℱ).obj X) ((ℱ).obj Y) ((ℱ).obj Z) _).symm

end AdjunctionComparison

end DerivedFormalization.CochainTensorTransport
