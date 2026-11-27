import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Cochains
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Signed tensor and internal Hom of unbounded cochain complexes of modules. -/

namespace DerivedFormalization

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ZeroObject
open CochainComplex (linearHomComplex)
open CochainComplex.HomComplex
open HomologicalComplex (ιTensorObj mapBifunctorDesc ι_mapBifunctorDesc)

universe u v

variable {R : Type u} [CommRing R]

/-- The direct-sum total tensor of cochain complexes. -/
noncomputable abbrev tensorComplex (X Y : Comp.{u} R) : Comp.{u} R :=
  HomologicalComplex.tensorObj X Y

/-- The tensor of cochain maps. -/
noncomputable abbrev tensorMap {X X' Y Y' : Comp.{u} R} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorComplex X Y ⟶ tensorComplex X' Y' :=
  HomologicalComplex.tensorHom f g

/-- The product complex of graded linear maps with its signed differential. -/
abbrev internalHom (X Y : Comp.{v} R) : Comp.{v} R :=
  linearHomComplex R X Y

/-- Tensoring with this complex on the right takes acyclic complexes to
acyclic complexes. -/
def IsKFlat (F : Comp.{u} R) : Prop :=
  ∀ E : Comp.{u} R, E.Acyclic → (tensorComplex E F).Acyclic

/-- K-projectivity in the unbounded cochain homotopy category. -/
abbrev IsKProjective (P : Comp.{v} R) : Prop := CochainComplex.IsKProjective P

/-- K-injectivity in the unbounded cochain homotopy category. -/
abbrev IsKInjective (I : Comp.{v} R) : Prop := CochainComplex.IsKInjective I

section Currying

-- The component construction of currying is adapted from MathGenome's
-- CochainLinearTensorHomAdjunction.
variable {P Q J : Comp.{u} R}

private noncomputable def curryComponent {n i u' : ℤ} (hi : i + n = u')
    (f : Cochain (HomologicalComplex.tensorObj P Q) J n) :
    P.X i ⟶ (linearHomComplex R Q J).X u' :=
  ModuleCat.ofHom
    { toFun := fun x => Cochain.mk fun j v hj => ModuleCat.ofHom
        ((f.v (i + j) v (by omega)).hom.comp
          ((ιTensorObj P Q i j (i + j) rfl).hom.comp
            (TensorProduct.mk R (P.X i) (Q.X j) x)))
      map_add' := by
        intro x y
        apply Cochain.ext
        intro j v hj
        apply ModuleCat.hom_ext
        ext z
        simp
      map_smul' := by
        intro r x
        apply Cochain.ext
        intro j v hj
        apply ModuleCat.hom_ext
        ext z
        simp only [Cochain.mk_v, Cochain.smul_v, ModuleCat.hom_smul, ModuleCat.hom_ofHom,
          LinearMap.smul_apply, LinearMap.comp_apply, map_smul, RingHom.id_apply] }

private noncomputable def curryDegree (n : ℤ) :
    Cochain (HomologicalComplex.tensorObj P Q) J n →ₗ[R] Cochain P (linearHomComplex R Q J) n where
  toFun f := Cochain.mk fun _ _ hi => curryComponent hi f
  map_add' f g := by
    apply Cochain.ext
    intro i u' hi
    apply ModuleCat.hom_ext
    ext x : 1
    apply Cochain.ext
    intro j v hj
    apply ModuleCat.hom_ext
    ext y
    rfl
  map_smul' r f := by
    apply Cochain.ext
    intro i u' hi
    apply ModuleCat.hom_ext
    ext x : 1
    apply Cochain.ext
    intro j v hj
    apply ModuleCat.hom_ext
    ext y
    rfl

private lemma curryDegree_apply {n i j u' v : ℤ} (hi : i + n = u') (hj : j + u' = v)
    (f : Cochain (HomologicalComplex.tensorObj P Q) J n) (x : P.X i) (y : Q.X j) :
    (((curryDegree n f).v i u' hi x).v j v hj) y =
      f.v (i + j) v (by omega) (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[R] y)) := rfl

private lemma curryDegree_apply_at {n i j t u' v : ℤ} (hi : i + n = u') (hj : j + u' = v)
    (ht : i + j = t) (f : Cochain (HomologicalComplex.tensorObj P Q) J n)
    (x : P.X i) (y : Q.X j) :
    (((curryDegree n f).v i u' hi x).v j v hj) y =
      f.v t v (by omega) (ιTensorObj P Q i j t ht (x ⊗ₜ[R] y)) := by
  subst t
  rfl

private def uncurryComponent {n i j v : ℤ} (h : i + j + n = v)
    (g : Cochain P (linearHomComplex R Q J) n) :
    P.X i ⊗ Q.X j ⟶ J.X v :=
  ModuleCat.ofHom <| TensorProduct.lift
    { toFun x := ((g.v i (i + n) rfl x).v j v (by omega)).hom
      map_add' x y := by
        rw [map_add]
        rfl
      map_smul' r x := by
        rw [map_smul]
        rfl }

private lemma uncurryComponent_apply {n i j u' v : ℤ} (h : i + j + n = v)
    (hi : i + n = u') (hj : j + u' = v)
    (g : Cochain P (linearHomComplex R Q J) n) (x : P.X i) (y : Q.X j) :
    uncurryComponent h g (x ⊗ₜ[R] y) = (g.v i u' hi x).v j v hj y := by
  subst u'
  rfl

private noncomputable def uncurryDegree {n : ℤ} (g : Cochain P (linearHomComplex R Q J) n) :
    Cochain (HomologicalComplex.tensorObj P Q) J n :=
  Cochain.mk fun t v htv =>
    mapBifunctorDesc (K₁ := P) (K₂ := Q) (F := curriedTensor (ModuleCat R))
      (c := ComplexShape.up ℤ) (j := t) fun i j (hij : i + j = t) =>
        uncurryComponent (by omega) g

private lemma uncurryDegree_ι {n t i j v : ℤ} (htv : t + n = v)
    (hij : i + j = t) (g : Cochain P (linearHomComplex R Q J) n) :
    ιTensorObj P Q i j t hij ≫ (uncurryDegree g).v t v htv =
      uncurryComponent (by omega) g :=
  ι_mapBifunctorDesc (K₁ := P) (K₂ := Q) (F := curriedTensor (ModuleCat R))
    (c := ComplexShape.up ℤ) (j := t) (fun a b (hab : a + b = t) =>
      uncurryComponent (n := n) (v := v) (by omega) g) i j hij

private lemma uncurryDegree_apply {n t i j u' v : ℤ} (hij : i + j = t)
    (hi : i + n = u') (hj : j + u' = v)
    (g : Cochain P (linearHomComplex R Q J) n) (x : P.X i) (y : Q.X j) :
    (uncurryDegree g).v t v (by omega) (ιTensorObj P Q i j t hij (x ⊗ₜ[R] y)) =
      (g.v i u' hi x).v j v hj y := by
  have htv : t + n = v := by omega
  have h := ConcreteCategory.congr_hom (uncurryDegree_ι htv hij g) (x ⊗ₜ[R] y)
  exact h.trans (uncurryComponent_apply (by omega) hi hj g x y)

private noncomputable def curryEquiv (n : ℤ) :
    Cochain (HomologicalComplex.tensorObj P Q) J n ≃ₗ[R] Cochain P (linearHomComplex R Q J) n :=
  { curryDegree n with
    invFun := uncurryDegree
    left_inv := by
      intro f
      apply Cochain.ext
      intro t v htv
      apply HomologicalComplex.mapBifunctor.hom_ext
        (K₁ := P) (K₂ := Q) (F := curriedTensor (ModuleCat R))
        (c := ComplexShape.up ℤ)
      intro i j hij
      change i + j = t at hij
      subst t
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      change (uncurryDegree (curryDegree n f)).v (i + j) v htv
          (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[R] y)) =
        f.v (i + j) v htv (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[R] y))
      rw [uncurryDegree_apply rfl rfl (show j + (i + n) = v by omega), curryDegree_apply]
    right_inv := by
      intro g
      apply Cochain.ext
      intro i u' hi
      apply ModuleCat.hom_ext
      ext x : 1
      apply Cochain.ext
      intro j v hj
      apply ModuleCat.hom_ext
      ext y
      exact (curryDegree_apply hi hj (uncurryDegree g) x y).trans
        (uncurryDegree_apply rfl hi hj g x y) }

private lemma add_apply {M N : ModuleCat.{v} R} (f g : M ⟶ N) (x : M) :
    (f + g) x = f x + g x := rfl

private lemma sign_apply {M N : ModuleCat.{v} R} (s : ℤˣ) (f : M ⟶ N) (x : M) :
    (s • f) x = s • f x := rfl

private lemma map_sign {M N : ModuleCat.{v} R} (s : ℤˣ) (f : M ⟶ N) (x : M) :
    f (s • x) = s • f x := by
  change f.hom (s • x) = s • f.hom x
  simp only [Units.smul_def, map_zsmul]

open HomologicalComplex.mapBifunctor in
theorem tensor_d_apply (i j t t' : ℤ) (ht : i + j = t) (ht' : t + 1 = t')
    (x : P.X i) (y : Q.X j) :
    (HomologicalComplex.tensorObj P Q).d t t' (ιTensorObj P Q i j t ht (x ⊗ₜ[R] y)) =
      ιTensorObj P Q (i + 1) j t' (by omega) (P.d i (i + 1) x ⊗ₜ[R] y) +
      i.negOnePow • ιTensorObj P Q i (j + 1) t' (by omega) (x ⊗ₜ[R] Q.d j (j + 1) y) := by
  let c := ComplexShape.up ℤ
  let F := curriedTensor (ModuleCat R)
  have h₁ : i + 1 + j = t' := by omega
  have h₂ : i + (j + 1) = t' := by omega
  have h :
      ιTensorObj P Q i j t ht ≫ (HomologicalComplex.tensorObj P Q).d t t' =
        (P.d i (i + 1) ▷ Q.X j) ≫ ιTensorObj P Q (i + 1) j t' h₁ +
        i.negOnePow • ((P.X i ◁ Q.d j (j + 1)) ≫ ιTensorObj P Q i (j + 1) t' h₂) := by
    rw [d_eq P Q F c, Preadditive.comp_add, ι_D₁, ι_D₂,
      d₁_eq P Q F c (show c.Rel i (i + 1) from rfl) j t' h₁,
      d₂_eq P Q F c i (show c.Rel j (j + 1) from rfl) t' h₂]
    exact congrArg (· + i.negOnePow •
      ((P.X i ◁ Q.d j (j + 1)) ≫ ιTensorObj P Q i (j + 1) t' h₂)) (one_smul ℤˣ _)
  simpa only [ModuleCat.comp_apply, add_apply, sign_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, ModuleCat.MonoidalCategory.whiskerRight_apply]
    using ConcreteCategory.congr_hom h (x ⊗ₜ[R] y)

private lemma differential_apply {A B : Comp.{v} R} {n m i v v₀ i₁ : ℤ}
    (hnm : n + 1 = m) (hiv : i + m = v) (hv₀ : v₀ = v - 1) (hi₁ : i + 1 = i₁)
    (f : Cochain A B n) (x : A.X i) :
    ((δ n m f).v i v hiv) x =
      B.d v₀ v (f.v i v₀ (by omega) x) +
      m.negOnePow • f.v i₁ v (by omega) (A.d i i₁ x) := by
  rw [δ_v n m hnm f i v hiv v₀ i₁ hv₀ hi₁, add_apply, sign_apply,
    ModuleCat.comp_apply, ModuleCat.comp_apply]

private lemma curry_comm {n m : ℤ} (hnm : n + 1 = m)
    (f : Cochain (HomologicalComplex.tensorObj P Q) J n) :
    δ n m (curryDegree n f) = curryDegree m (δ n m f) := by
  apply Cochain.ext
  intro i u' hi
  apply ModuleCat.hom_ext
  ext x : 1
  apply Cochain.ext
  intro j v hj
  apply ModuleCat.hom_ext
  ext y
  change ((δ n m (curryDegree n f)).v i u' hi x).v j v hj y =
    ((curryDegree m (δ n m f)).v i u' hi x).v j v hj y
  have hu : u' - 1 + 1 = u' := by omega
  have hn : i + n = u' - 1 := by omega
  have hv : j + (u' - 1) = v - 1 := by omega
  have hi₁ : (i + 1) + n = u' := by omega
  have hj₁ : (j + 1) + (u' - 1) = v := by omega
  rw [differential_apply hnm hi rfl rfl, curryDegree_apply hi hj,
    differential_apply hnm (by omega : i + j + m = v) rfl rfl]
  change (δ (u' - 1) u' ((curryDegree n f).v i (u' - 1) hn x) +
      m.negOnePow • (show Cochain Q J u' from
        (curryDegree n f).v (i + 1) u' hi₁ (P.d i (i + 1) x))).v j v hj y = _
  rw [Cochain.add_v, Cochain.units_smul_v, add_apply, sign_apply,
    differential_apply hu hj rfl rfl, curryDegree_apply hn hv,
    curryDegree_apply_at hn hj₁ (by omega : i + (j + 1) = i + j + 1),
    curryDegree_apply_at hi₁ hj (by omega : i + 1 + j = i + j + 1),
    tensor_d_apply i j (i + j) (i + j + 1) rfl rfl,
    map_add, map_sign, smul_add, smul_smul]
  -- The inner Hom differential has target degree i + m.
  have hsign : m.negOnePow * i.negOnePow = u'.negOnePow := by
    rw [← Int.negOnePow_add, add_comm, hi]
  rw [hsign, add_assoc, add_comm (u'.negOnePow • _)]

/-- Tensor–Hom currying for integer-indexed cochain complexes of modules. -/
noncomputable def tensorHomIso (P Q J : Comp.{u} R) :
    linearHomComplex R (HomologicalComplex.tensorObj P Q) J ≅
      linearHomComplex R P (linearHomComplex R Q J) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (curryEquiv n).toModuleIso)
    (fun n m h => by
      apply ModuleCat.hom_ext
      ext f : 1
      exact curry_comm h f)

@[simp]
theorem tensorHomIso_apply (P Q J : Comp.{u} R) {n i j u' v : ℤ}
    (hi : i + n = u') (hj : j + u' = v) (f : Cochain (HomologicalComplex.tensorObj P Q) J n)
    (x : P.X i) (y : Q.X j) :
    (((tensorHomIso P Q J).hom.f n f).v i u' hi x).v j v hj y =
      f.v (i + j) v (by omega) (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[R] y)) :=
  curryDegree_apply hi hj f x y

/-- Precomposition in the first variable and postcomposition in the second
variable of the linear cochain Hom. -/
def internalHomMap {A A' B B' : Comp.{v} R} (g : A' ⟶ A) (h : B ⟶ B') :
    linearHomComplex R A B ⟶ linearHomComplex R A' B' where
  f n := ModuleCat.ofHom
    { toFun := fun f => ((Cochain.ofHom g).comp f (zero_add n)).comp
        (Cochain.ofHom h) (add_zero n)
      map_add' := by intros; simp [Cochain.comp_add]
      map_smul' := by intros; simp [Cochain.comp_smul] }
  comm' := by
    intro n m _
    apply ModuleCat.hom_ext
    ext f : 1
    change δ n m (((Cochain.ofHom g).comp f (zero_add n)).comp (Cochain.ofHom h) (add_zero n)) =
      ((Cochain.ofHom g).comp (δ n m f) (zero_add m)).comp (Cochain.ofHom h) (add_zero m)
    simp

@[simp]
theorem internalHomMap_apply {A A' B B' : Comp.{v} R} (g : A' ⟶ A) (h : B ⟶ B')
    {n i v : ℤ} (hi : i + n = v) (f : Cochain A B n) (x : A'.X i) :
    ((internalHomMap g h).f n f).v i v hi x = h.f v (f.v i v hi (g.f i x)) := by
  change ((((Cochain.ofHom g).comp f (zero_add n)).comp (Cochain.ofHom h) (add_zero n)).v i v hi) x =
    _
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    ModuleCat.comp_apply]

/-- The action of a map on a pure tensor in a summand of the total tensor. -/
theorem tensorMap_apply {P' Q' : Comp.{u} R} (a : P' ⟶ P) (b : Q' ⟶ Q)
    (i j : ℤ) (x : P'.X i) (y : Q'.X j) :
    (HomologicalComplex.tensorHom a b).f (i + j)
      (ιTensorObj P' Q' i j (i + j) rfl (x ⊗ₜ[R] y)) =
      ιTensorObj P Q i j (i + j) rfl (a.f i x ⊗ₜ[R] b.f j y) := by
  have h := HomologicalComplex.ι_mapBifunctorMap
    (K₁ := P') (K₂ := Q') (L₁ := P) (L₂ := Q) (f₁ := a) (f₂ := b)
    (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) i j (i + j) rfl
  change ιTensorObj P' Q' i j (i + j) rfl ≫ (HomologicalComplex.tensorHom a b).f (i + j) =
    (a.f i ▷ Q'.X j) ≫ (P.X i ◁ b.f j) ≫ ιTensorObj P Q i j (i + j) rfl at h
  simpa only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply] using
    ConcreteCategory.congr_hom h (x ⊗ₜ[R] y)

/-- The currying isomorphism commutes with precomposition in both tensor factors
and postcomposition in the target. -/
theorem tensorHomIso_natural {P' Q' J' : Comp.{u} R}
    (a : P' ⟶ P) (b : Q' ⟶ Q) (c : J ⟶ J') :
    internalHomMap (HomologicalComplex.tensorHom a b) c ≫ (tensorHomIso P' Q' J').hom =
      (tensorHomIso P Q J).hom ≫ internalHomMap a (internalHomMap b c) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext f : 1
  apply Cochain.ext
  intro i u' hi
  apply ModuleCat.hom_ext
  ext x : 1
  apply Cochain.ext
  intro j v hj
  apply ModuleCat.hom_ext
  ext y
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, tensorHomIso_apply,
    internalHomMap_apply, tensorMap_apply]

end Currying

/-- The degree-`n` term of the internal Hom is the unrestricted product of
the modules of linear maps with degree difference `n`. -/
def internalHomProduct (X Y : Comp.{v} R) (n : ℤ) :
    (internalHom X Y).X n ≃ₗ[R] (∀ i : ℤ, X.X i →ₗ[R] Y.X (i + n)) where
  toFun f i := (f.v i (i + n) rfl).hom
  invFun f := Cochain.mk fun i j h => h ▸ ModuleCat.ofHom (f i)
  left_inv f := by
    apply Cochain.ext
    rintro i j rfl
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem internalHom_d_apply {X Y : Comp.{v} R} (n i : ℤ)
    (f : Cochain X Y n) (x : X.X i) :
    (((internalHom X Y).d n (n + 1) f).v i (i + n + 1) (by omega)) x =
      Y.d (i + n) (i + n + 1) (f.v i (i + n) rfl x) -
      n.negOnePow • f.v (i + 1) (i + n + 1) (by omega) (X.d i (i + 1) x) := by
  change (δ n (n + 1) f).v i (i + n + 1) (by omega) x = _
  rw [differential_apply rfl (by omega) (by omega : i + n = i + n + 1 - 1) rfl,
    Int.negOnePow_succ, Units.neg_smul]
  exact (sub_eq_add_neg _ _).symm

theorem tensor_d_squared (X Y : Comp.{u} R) (i j k : ℤ) :
    (tensorComplex X Y).d i j ≫ (tensorComplex X Y).d j k = 0 :=
  HomologicalComplex.d_comp_d _ _ _ _

theorem internalHom_d_squared (X Y : Comp.{v} R) (i j k : ℤ) :
    (internalHom X Y).d i j ≫ (internalHom X Y).d j k = 0 :=
  HomologicalComplex.d_comp_d _ _ _ _

/-- Degree-zero cycles are precisely cochain maps, with addition and
scalar multiplication computed componentwise. -/
def internalHomCyclesZero (X Y : Comp.{v} R) : (X ⟶ Y) ≃ₗ[R] Cocycle X Y 0 :=
  (Cocycle.equivHom X Y).toLinearEquiv (by simp)

open scoped CategoryTheory in
/-- Degree-`n` cycles are the maps to the cochain shift by `n`. -/
def internalHomCyclesShift (X Y : Comp.{v} R) (n : ℤ) :
    (X ⟶ Y⟦n⟧) ≃ₗ[R] Cocycle X Y n :=
  Cocycle.equivHomShift.toLinearEquiv (by simp)

theorem internalHom_boundary_zero_iff {X Y : Comp.{v} R} (f : X ⟶ Y) :
    (∃ h : Cochain X Y (-1), δ (-1) 0 h = Cochain.ofHom f) ↔ Nonempty (Homotopy f 0) := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨(Cochain.equivHomotopy f 0).symm ⟨h, by simpa using hh.symm⟩⟩
  · rintro ⟨h⟩
    exact ⟨Cochain.ofHomotopy h, by simp⟩

theorem internalHom_boundary_shift_iff {X Y : Comp.{v} R} (n : ℤ)
    (z : Cocycle X Y n) :
    (∃ h : Cochain X Y (n - 1), δ (n - 1) n h = z.1) ↔
      Nonempty (Homotopy ((internalHomCyclesShift X Y n).symm z) 0) := by
  rw [← mem_coboundaries_iff z (n - 1) (by omega),
    ← CohomologyClass.toHom_mk_eq_zero_iff, CohomologyClass.toHom_mk,
    HomotopyCategory.quotient_map_eq_zero_iff]
  rfl

open scoped CategoryTheory in
/-- Cohomology of internal Hom is the module of homotopy classes of maps to the shift. -/
noncomputable def internalHomCohomology (X Y : Comp.{v} R) (n : ℤ) :
    (internalHom X Y).homology n ≃ₗ[R]
      ((HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).obj X ⟶
        (HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)).obj (Y⟦n⟧)) :=
  (homologyLinearEquiv R X Y n).trans <|
    (CohomologyClass.homAddEquiv (K := X) (L := Y) (n := n)).toLinearEquiv (by
      intro r z
      obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective z
      simp [← CohomologyClass.mk_smul, CohomologyClass.toHom_mk])

private theorem internalHom_acyclic_iff (X Y : Comp.{v} R) :
    (internalHom X Y).Acyclic ↔
      ∀ (n : ℤ) (z : Cocycle X Y n), ∃ h : Cochain X Y (n - 1), δ (n - 1) n h = z.1 := by
  have h (n : ℤ) : (internalHom X Y).ExactAt n ↔
      ∀ z : Cochain X Y n, δ n (n + 1) z = 0 →
        ∃ h : Cochain X Y (n - 1), δ (n - 1) n h = z := by
    rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    rfl
  change (∀ n, (internalHom X Y).ExactAt n) ↔ _
  simp only [h]
  constructor
  · intro ha n z
    exact ha n z.1 (z.δ_eq_zero _)
  · intro ha n z hz
    exact ha n (Cocycle.mk z (n + 1) rfl hz)

open scoped CategoryTheory in
private theorem acyclic_cochainShift (Y : Comp.{v} R) (hY : Y.Acyclic) (n : ℤ) :
    (Y⟦n⟧).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hY (i + n)).isZero_homology.of_iso ((cohomologyShiftIso R n i).app Y)

/-- K-projectivity is the all-degree acyclicity test for internal Hom out of the complex. -/
theorem isKProjective_iff_internalHom_acyclic (P : Comp.{v} R) :
    IsKProjective P ↔ ∀ A : Comp.{v} R, A.Acyclic → (internalHom P A).Acyclic := by
  constructor
  · intro hP A hA
    rw [internalHom_acyclic_iff]
    intro n z
    exact (internalHom_boundary_shift_iff n z).2
      (CochainComplex.IsKProjective.nonempty_homotopy_zero _ (acyclic_cochainShift A hA n))
  · intro hP
    constructor
    intro A f hA
    apply (internalHom_boundary_zero_iff f).1
    exact (internalHom_acyclic_iff P A).1 (hP A hA) 0 (Cocycle.ofHom f)

/-- K-injectivity is the all-degree acyclicity test for internal Hom into the complex. -/
theorem isKInjective_iff_internalHom_acyclic (I : Comp.{v} R) :
    IsKInjective I ↔ ∀ A : Comp.{v} R, A.Acyclic → (internalHom A I).Acyclic := by
  constructor
  · intro hI A hA
    rw [internalHom_acyclic_iff]
    intro n z
    exact CochainComplex.IsKInjective.eq_δ_of_cocycle z hA (n - 1) (by omega)
  · intro hI
    constructor
    intro A f hA
    apply (internalHom_boundary_zero_iff f).1
    exact (internalHom_acyclic_iff A I).1 (hI A hA) 0 (Cocycle.ofHom f)

/-- The tensor term in total degree `n` is the coproduct of the modules
`X^i ⊗ Y^j` indexed by the pairs with `i + j = n`. -/
noncomputable def tensorCofan (X Y : Comp.{u} R) (n : ℤ) :
    Cofan (fun p : {p : ℤ × ℤ // p.1 + p.2 = n} => X.X p.1.1 ⊗ Y.X p.1.2) :=
  Cofan.mk ((tensorComplex X Y).X n) (fun p => ιTensorObj X Y p.1.1 p.1.2 n p.2)

theorem tensorCofan_isColimit (X Y : Comp.{u} R) (n : ℤ) :
    Nonempty (IsColimit (tensorCofan X Y n)) := by
  apply Nonempty.intro
  exact (((curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
    (.up ℤ) (.up ℤ)).obj X |>.obj Y).toGradedObject.isColimitCofanMapObj
      (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ)) n

/-- Simultaneous tensoring of homotopies in the two variables. -/
noncomputable def tensorMapHomotopy {X X' Y Y' : Comp.{u} R}
    {f f' : X ⟶ X'} {g g' : Y ⟶ Y'}
    (h : Homotopy f f') (k : Homotopy g g') :
    Homotopy (tensorMap f g) (tensorMap f' g') :=
  (HomologicalComplex.mapBifunctorMapHomotopy₁ h g (curriedTensor (ModuleCat R)) (.up ℤ)).trans
    (HomologicalComplex.mapBifunctorMapHomotopy₂ f' k (curriedTensor (ModuleCat R)) (.up ℤ))

@[simp]
theorem internalHomMap_id (X Y : Comp.{v} R) :
    internalHomMap (𝟙 X) (𝟙 Y) = 𝟙 (internalHom X Y) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext f : 1
  apply Cochain.ext
  intro i j hij
  apply ModuleCat.hom_ext
  ext x
  change ((internalHomMap (𝟙 X) (𝟙 Y)).f n f).v i j hij x = f.v i j hij x
  rw [internalHomMap_apply]
  rfl

theorem internalHomMap_comp {X X' X'' Y Y' Y'' : Comp.{v} R}
    (f : X' ⟶ X) (f' : X'' ⟶ X') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    internalHomMap f g ≫ internalHomMap f' g' = internalHomMap (f' ≫ f) (g ≫ g') := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext a : 1
  apply Cochain.ext
  intro i j hij
  apply ModuleCat.hom_ext
  ext x
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, internalHomMap_apply]

private def cochainHomotopyOfComponents {Z W : Comp.{v} R} {f g : Z ⟶ W}
    (s : ∀ i j : ℤ, i + (-1) = j → (Z.X i ⟶ W.X j))
    (hs : ∀ n : ℤ, f.f n =
      (Z.d n (n + 1) ≫ s (n + 1) n (show n + 1 + (-1) = n by omega)) +
      (s n (n - 1) (show n + (-1) = n - 1 by omega) ≫ W.d (n - 1) n) + g.f n) : Homotopy f g where
  hom i j := if h : i + (-1) = j then s i j h else 0
  zero i j h := by
    rw [dite_eq_right]
    intro hij
    apply h
    change j + 1 = i
    omega
  comm n := by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) by rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp),
      dite_eq_left (by omega : n + 1 + (-1) = n), dite_eq_left (by omega : n + (-1) = n - 1)]
    exact hs n

private def internalHomPostHomotopy {X X' Y Y' : Comp.{v} R}
    (f : X' ⟶ X) {g g' : Y ⟶ Y'} (h : Homotopy g g') :
    Homotopy (internalHomMap f g) (internalHomMap f g') := by
  let s (n m : ℤ) (hm : n + (-1) = m) :
      (internalHom X Y).X n ⟶ (internalHom X' Y').X m :=
    ModuleCat.ofHom
      { toFun := fun z => ((Cochain.ofHom f).comp z (zero_add n)).comp
          (Cochain.ofHomotopy h) hm
        map_add' := by intros; simp [Cochain.comp_add, Cochain.add_comp]
        map_smul' := by intros; simp [Cochain.comp_smul, Cochain.smul_comp] }
  apply cochainHomotopyOfComponents (Z := internalHom X Y) (W := internalHom X' Y') s
  intro n
  apply ModuleCat.hom_ext
  ext z : 1
  let z' := (Cochain.ofHom f).comp z (zero_add n)
  let b := Cochain.ofHomotopy h
  have hn : n + 1 + (-1) = n := by omega
  change z'.comp (Cochain.ofHom g) (add_zero n) =
    ((Cochain.ofHom f).comp (δ n (n + 1) z) (zero_add (n + 1))).comp b hn +
    δ (n - 1) n (z'.comp b (by omega)) + z'.comp (Cochain.ofHom g') (add_zero n)
  have hd : (Cochain.ofHom f).comp (δ n (n + 1) z) (zero_add (n + 1)) =
      δ n (n + 1) z' := by simp [z']
  rw [hd, δ_comp z' b (by omega) (n + 1) 0 n (by omega) rfl (by omega)]
  simp only [b, δ_ofHomotopy, Cochain.comp_sub, Int.negOnePow_neg, Int.negOnePow_one,
    Units.neg_smul, one_smul]
  abel

private def internalHomPreHomotopy {X X' Y Y' : Comp.{v} R}
    {f f' : X' ⟶ X} (h : Homotopy f f') (g : Y ⟶ Y') :
    Homotopy (internalHomMap f g) (internalHomMap f' g) := by
  -- Moving a degree-minus-one homotopy past a degree-n cochain contributes this sign.
  let s (n m : ℤ) (hm : n + (-1) = m) :
      (internalHom X Y).X n ⟶ (internalHom X' Y').X m :=
    ModuleCat.ofHom
      { toFun := fun z => n.negOnePow •
          (Cochain.ofHomotopy h).comp (z.comp (Cochain.ofHom g) (add_zero n))
            ((add_comm (-1) n).trans hm)
        map_add' := by intros; simp only [Cochain.comp_add, Cochain.add_comp, smul_add]
        map_smul' := by
          intros
          simp only [Cochain.comp_smul, Cochain.smul_comp, smul_comm (_ : ℤˣ) (_ : R), RingHom.id_apply] }
  apply cochainHomotopyOfComponents (Z := internalHom X Y) (W := internalHom X' Y') s
  intro n
  apply ModuleCat.hom_ext
  ext z : 1
  let z' := z.comp (Cochain.ofHom g) (add_zero n)
  let b := Cochain.ofHomotopy h
  have hn : -1 + (n + 1) = n := by omega
  change ((Cochain.ofHom f).comp z (zero_add n)).comp (Cochain.ofHom g) (add_zero n) =
    (n + 1).negOnePow • b.comp ((δ n (n + 1) z).comp (Cochain.ofHom g)
      (add_zero (n + 1))) hn +
    δ (n - 1) n (n.negOnePow • b.comp z' (by omega)) +
    ((Cochain.ofHom f').comp z (zero_add n)).comp (Cochain.ofHom g) (add_zero n)
  have hd : (δ n (n + 1) z).comp (Cochain.ofHom g) (add_zero (n + 1)) =
      δ n (n + 1) z' := by simp [z']
  rw [hd, δ_units_smul, δ_comp b z' (by omega) 0 (n + 1) n (by omega) (by omega) rfl]
  simp only [Int.negOnePow_succ, Units.neg_smul, smul_add, smul_smul, Int.units_mul_self,
    one_smul, b, δ_ofHomotopy, Cochain.sub_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  change (Cochain.ofHom f).comp z' (zero_add n) = _
  abel

/-- Simultaneous precomposition and postcomposition take homotopic maps to
homotopic maps on internal Hom. -/
def internalHomMapHomotopy {X X' Y Y' : Comp.{v} R}
    {f f' : X' ⟶ X} {g g' : Y ⟶ Y'}
    (h : Homotopy f f') (k : Homotopy g g') :
    Homotopy (internalHomMap f g) (internalHomMap f' g') :=
  (internalHomPreHomotopy h g).trans (internalHomPostHomotopy f' k)

theorem tensorMap_homotopy {X X' Y Y' : Comp.{u} R}
    {f f' : X ⟶ X'} {g g' : Y ⟶ Y'} (h : Homotopy f f') (k : Homotopy g g') :
    Nonempty (Homotopy (tensorMap f g) (tensorMap f' g')) :=
  ⟨tensorMapHomotopy h k⟩

theorem internalHomMap_homotopy {X X' Y Y' : Comp.{v} R}
    {f f' : X' ⟶ X} {g g' : Y ⟶ Y'} (h : Homotopy f f') (k : Homotopy g g') :
    Nonempty (Homotopy (internalHomMap f g) (internalHomMap f' g')) :=
  ⟨internalHomMapHomotopy h k⟩

theorem tensorHomCurrying (R : Type u) [CommRing R] :
    ∃ e : ∀ P Q J : Comp.{u} R,
        internalHom (tensorComplex P Q) J ≅ internalHom P (internalHom Q J),
      (∀ (P Q J : Comp.{u} R) {n i j l m : ℤ}
          (hi : i + n = l) (hj : j + l = m)
          (f : Cochain (tensorComplex P Q) J n) (x : P.X i) (y : Q.X j),
        (((e P Q J).hom.f n f).v i l hi x).v j m hj y =
          f.v (i + j) m (by omega) (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[R] y))) ∧
      ∀ {P P' Q Q' J J' : Comp.{u} R} (a : P' ⟶ P) (b : Q' ⟶ Q) (c : J ⟶ J'),
        internalHomMap (tensorMap a b) c ≫ (e P' Q' J').hom =
          (e P Q J).hom ≫ internalHomMap a (internalHomMap b c) :=
  by
  refine ⟨tensorHomIso, ?_, tensorHomIso_natural⟩
  intro P Q J n i j l m hi hj f x y
  exact tensorHomIso_apply P Q J hi hj f x y

private theorem internalHomMapCocycles_comm {X Y Z W : Comp.{v} R}
    (g : internalHom X Y ⟶ internalHom Z W) (n m : ℤ) (z : Cochain X Y n) :
    δ n m (g.f n z) = g.f m (δ n m z) :=
  ConcreteCategory.congr_hom (g.comm n m) z

private def internalHomMapCocycles {X Y Z W : Comp.{v} R}
    (g : internalHom X Y ⟶ internalHom Z W) (n : ℤ) :
    Cocycle X Y n →ₗ[R] Cocycle Z W n where
  toFun z := Cocycle.mk (g.f n z.1) (n + 1) rfl (by
    rw [internalHomMapCocycles_comm, z.δ_eq_zero]
    exact map_zero (g.f (n + 1)).hom)
  map_add' z z' := Cocycle.ext (map_add (g.f n).hom z.1 z'.1)
  map_smul' r z := Cocycle.ext (map_smul (g.f n).hom r z.1)

private def internalHomIsoCocycles {X Y Z W : Comp.{v} R}
    (e : internalHom X Y ≅ internalHom Z W) (n : ℤ) :
    Cocycle X Y n ≃ₗ[R] Cocycle Z W n :=
  { internalHomMapCocycles e.hom n with
    invFun := internalHomMapCocycles e.inv n
    left_inv z := by
      apply Cocycle.ext
      have he := congrArg (fun f : internalHom X Y ⟶ internalHom X Y => f.f n) e.hom_inv_id
      exact ConcreteCategory.congr_hom he z.1
    right_inv z := by
      apply Cocycle.ext
      have he := congrArg (fun f : internalHom Z W ⟶ internalHom Z W => f.f n) e.inv_hom_id
      exact ConcreteCategory.congr_hom he z.1 }

/-- The ordinary tensor–Hom correspondence, obtained by taking degree-zero
cycles of the signed currying isomorphism. -/
noncomputable def tensorHomEquiv (P Q J : Comp.{u} R) :
    (tensorComplex P Q ⟶ J) ≃ₗ[R] (P ⟶ internalHom Q J) :=
  (internalHomCyclesZero _ _).trans <|
    (internalHomIsoCocycles (tensorHomIso P Q J) 0).trans (internalHomCyclesZero _ _).symm

private def cochainMapOfInternalHomMap {X Y Z W : Comp.{v} R}
    (g : internalHom X Y ⟶ internalHom Z W) (f : X ⟶ Y) :=
  (internalHomCyclesZero Z W).symm (internalHomMapCocycles g 0 (Cocycle.ofHom f))

private theorem mapHomotopyOfInternalHomMap {X Y Z W : Comp.{v} R}
    (g : internalHom X Y ⟶ internalHom Z W) {f f' : X ⟶ Y} (h : Homotopy f f') :
    Nonempty (Homotopy (cochainMapOfInternalHomMap g f) (cochainMapOfInternalHomMap g f')) := by
  have hmap (a : X ⟶ Y) :
      Cochain.ofHom (cochainMapOfInternalHomMap g a) = g.f 0 (Cochain.ofHom a) := by
    exact congrArg Subtype.val ((internalHomCyclesZero Z W).apply_symm_apply
      (internalHomMapCocycles g 0 (Cocycle.ofHom a)))
  refine ⟨(Cochain.equivHomotopy _ _).symm ⟨g.f (-1) (Cochain.ofHomotopy h), ?_⟩⟩
  rw [hmap, hmap, internalHomMapCocycles_comm, δ_ofHomotopy]
  change (g.f 0).hom _ = (g.f 0).hom (_ - _) + (g.f 0).hom _
  rw [map_sub, sub_add_cancel]

/-- Currying and uncurrying both preserve ordinary cochain homotopies. -/
theorem tensorHomEquiv_homotopy_iff {P Q J : Comp.{u} R} (f f' : tensorComplex P Q ⟶ J) :
    Nonempty (Homotopy f f') ↔
      Nonempty (Homotopy (tensorHomEquiv P Q J f) (tensorHomEquiv P Q J f')) := by
  constructor
  · rintro ⟨h⟩
    exact mapHomotopyOfInternalHomMap (tensorHomIso P Q J).hom h
  · rintro ⟨h⟩
    have h' := mapHomotopyOfInternalHomMap (tensorHomIso P Q J).inv h
    change Nonempty (Homotopy ((tensorHomEquiv P Q J).symm (tensorHomEquiv P Q J f))
      ((tensorHomEquiv P Q J).symm (tensorHomEquiv P Q J f'))) at h'
    simpa only [LinearEquiv.symm_apply_apply] using h'

@[simp]
theorem tensorHomEquiv_apply (P Q J : Comp.{u} R) (f : tensorComplex P Q ⟶ J)
    (i j : ℤ) (x : P.X i) (y : Q.X j) :
    ((tensorHomEquiv P Q J f).f i x).v j (i + j) (add_comm j i) y =
      f.f (i + j) (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[R] y)) := by
  let z := internalHomMapCocycles (tensorHomIso P Q J).hom 0 (Cocycle.ofHom f)
  have hz : Cochain.ofHom (tensorHomEquiv P Q J f) = z.1 :=
    congrArg Subtype.val ((internalHomCyclesZero P (internalHom Q J)).apply_symm_apply z)
  have h := ConcreteCategory.congr_hom (Cochain.congr_v hz i i (add_zero i)) x
  change (tensorHomEquiv P Q J f).f i x =
    (((tensorHomIso P Q J).hom.f 0 (Cochain.ofHom f)).v i i (add_zero i)) x at h
  rw [h, tensorHomIso_apply, Cochain.ofHom_v]

theorem tensorHomEquiv_natural {P P' Q Q' J J' : Comp.{u} R}
    (a : P' ⟶ P) (b : Q' ⟶ Q) (c : J ⟶ J') (f : tensorComplex P Q ⟶ J) :
    tensorHomEquiv P' Q' J' (tensorMap a b ≫ f ≫ c) =
      a ≫ tensorHomEquiv P Q J f ≫ internalHomMap b c := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  ext x : 1
  apply Cochain.ext
  intro j m hj
  apply ModuleCat.hom_ext
  ext y
  change ((tensorHomEquiv P' Q' J' (tensorMap a b ≫ f ≫ c)).f i x).v j m hj y =
    ((internalHomMap b c).f i ((tensorHomEquiv P Q J f).f i (a.f i x))).v j m hj y
  obtain rfl : m = i + j := by omega
  simp only [internalHomMap_apply, tensorHomEquiv_apply, HomologicalComplex.comp_f,
    ModuleCat.comp_apply, tensorMap_apply]

/-- The cochain adjunction evaluates by currying on pure tensors and
identifies cochain homotopies on both sides. -/
theorem tensorHomAdjunction (R : Type u) [CommRing R] :
    ∃ e : ∀ P Q J : Comp.{u} R,
          (tensorComplex P Q ⟶ J) ≃ₗ[R] (P ⟶ internalHom Q J),
      (∀ (P Q J : Comp.{u} R) (f : tensorComplex P Q ⟶ J) (i j : ℤ)
          (x : P.X i) (y : Q.X j),
        ((e P Q J f).f i x).v j (i + j) (add_comm j i) y =
          f.f (i + j) (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[R] y))) ∧
      (∀ {P P' Q Q' J J' : Comp.{u} R} (a : P' ⟶ P) (b : Q' ⟶ Q) (c : J ⟶ J')
          (f : tensorComplex P Q ⟶ J), e P' Q' J' (tensorMap a b ≫ f ≫ c) =
          a ≫ e P Q J f ≫ internalHomMap b c) ∧
      ∀ {P Q J : Comp.{u} R} (f f' : tensorComplex P Q ⟶ J),
        Nonempty (Homotopy f f') ↔ Nonempty (Homotopy (e P Q J f) (e P Q J f')) :=
  ⟨tensorHomEquiv, tensorHomEquiv_apply, tensorHomEquiv_natural, tensorHomEquiv_homotopy_iff⟩

@[simp]
theorem tensorMap_id (X Y : Comp.{u} R) :
    tensorMap (𝟙 X) (𝟙 Y) = 𝟙 (tensorComplex X Y) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := X) (K₂ := Y) (F := curriedTensor (ModuleCat R)) (c := ComplexShape.up ℤ)
  intro i j h
  simp [tensorMap]

theorem tensorMap_comp {X X' X'' Y Y' Y'' : Comp.{u} R}
    (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    tensorMap f g ≫ tensorMap f' g' = tensorMap (f ≫ f') (g ≫ g') := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := X) (K₂ := Y) (F := curriedTensor (ModuleCat R)) (c := ComplexShape.up ℤ)
  intro i j h
  simp [tensorMap, whisker_exchange_assoc]

end DerivedFormalization
