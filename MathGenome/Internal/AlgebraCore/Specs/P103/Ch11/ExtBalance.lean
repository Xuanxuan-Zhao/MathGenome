import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtTorDefinitions
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! The Ext part of paper.tex 2619–2665. Hom is valued in integer modules.
The two indices below are nonnegative; hence the total is precisely the
first-quadrant direct-sum total, with no boundedness or rank hypothesis.
Substituting the opposite ring gives same-side right modules. -/
namespace P103.Specs.Ch11.ExtBalance
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
noncomputable section
universe u v w x y
variable {R : Type u} [Ring R]

/-- Cochain signs on nonnegative indices, with the manuscript's convention. -/
instance upNatTensorSigns : ComplexShape.TensorSigns (ComplexShape.up ℕ) where
  ε' := MonoidHom.mk' (fun (n : ℕ) => (-1 : ℤˣ) ^ n) (pow_add (-1 : ℤˣ))
  rel_add p q r (h : p + 1 = q) := by change p + r + 1 = q + r; omega
  add_rel p q r (h : p + 1 = q) := by change r + p + 1 = r + q; omega
  ε'_succ := by
    rintro p _ rfl
    change (-1 : ℤˣ) ^ (p + 1) = -((-1 : ℤˣ) ^ p)
    rw [pow_succ, mul_neg, mul_one]

/-- Covariant Hom, with only its canonical integer action. -/
def covariantHom (A : Type v) [AddCommGroup A] [Module R A] :
    ModuleCat.{w} R ⥤ ModuleCat.{max v w} ℤ where
  obj B := ModuleCat.of ℤ (A →ₗ[R] B)
  map g := ModuleCat.ofHom (P103.HomTensorExactness.post g.hom).toIntLinearMap
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

instance covariantHom_additive (A : Type v) [AddCommGroup A] [Module R A] :
    (covariantHom (R := R) A : ModuleCat.{w} R ⥤ ModuleCat.{max v w} ℤ).Additive where
  map_add := by intros; ext; rfl

/-- The cochain complex used to compute Ext with an injective resolution. -/
abbrev injectiveHom (A : Type v) [AddCommGroup A] [Module R A]
    (D : CochainComplex (ModuleCat.{w} R) ℕ) :=
  ((covariantHom A).mapHomologicalComplex (ComplexShape.up ℕ)).obj D

/-- Unsigned horizontal maps are precomposition; vertical maps are postcomposition. -/
def homBicomplex (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : CochainComplex (ModuleCat.{w} R) ℕ) :
    HomologicalComplex₂ (ModuleCat.{max v w} ℤ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) where
  X p := injectiveHom (C.X p) D
  d p p' :=
    { f q := ModuleCat.ofHom (P103.HomTensorExactness.pre (Q := D.X q)
        (C.d p' p).hom).toIntLinearMap
      comm' i j _ := by ext; rfl }
  shape p p' h := by
    apply HomologicalComplex.Hom.ext
    funext q
    have hc : ¬ (ComplexShape.down ℕ).Rel p' p := h
    rw [C.shape p' p hc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change C.X p →ₗ[R] D.X q at f
    apply LinearMap.ext
    intro a
    change f 0 = 0
    exact f.map_zero
  d_comp_d' p p' p'' _ _ := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change C.X p →ₗ[R] D.X q at f
    apply LinearMap.ext
    intro a
    change f ((C.d p' p).hom ((C.d p'' p').hom a)) = 0
    have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (C.d_comp_d p'' p' p)) a
    change (C.d p' p).hom ((C.d p'' p').hom a) = 0 at h
    rw [h, map_zero]

/-- Mathlib's coproduct total uses dh + (-1)^p dv. -/
abbrev homTotal (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : CochainComplex (ModuleCat.{w} R) ℕ) :=
  (homBicomplex C D).total (ComplexShape.up ℕ)

/-- Simultaneous contravariant change in A and covariant change of the resolution I. -/
def injectiveHomMap {A : Type v} {A' : Type v}
    [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
    {D E : CochainComplex (ModuleCat.{w} R) ℕ}
    (f : A' →ₗ[R] A) (g : D ⟶ E) : injectiveHom A D ⟶ injectiveHom A' E where
  f q := ModuleCat.ofHom
    ((P103.HomTensorExactness.post (g.f q).hom).comp
      (P103.HomTensorExactness.pre f)).toIntLinearMap
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change A →ₗ[R] D.X i at h
    apply LinearMap.ext
    intro a
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (g.comm i j)) (h (f a))

/-- The left augmentation is prescribed on every degree, not up to an arbitrary isomorphism. -/
def IsProjectiveAugmentation {A : Type v} {B : Type w}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : LeftResolution R A) (I : InjectiveResolution R B)
    (α : homComplex P.complex B ⟶ homTotal P.complex I.complex) : Prop :=
  ∀ n, α.f n = ModuleCat.ofHom
    (P103.HomTensorExactness.post (P := P.complex.X n) I.η).toIntLinearMap ≫
      (homBicomplex P.complex I.complex).ιTotal (ComplexShape.up ℕ) n 0 n (by simp)

/-- The right augmentation is precomposition with P_0 → A. -/
def IsInjectiveAugmentation {A : Type v} {B : Type w}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : LeftResolution R A) (I : InjectiveResolution R B)
    (β : injectiveHom A I.complex ⟶ homTotal P.complex I.complex) : Prop :=
  ∀ n, β.f n = ModuleCat.ofHom
    (P103.HomTensorExactness.pre (Q := I.complex.X n) P.ε).toIntLinearMap ≫
      (homBicomplex P.complex I.complex).ιTotal (ComplexShape.up ℕ) 0 n n (by simp)

/-- Both concrete augmentation maps, their quasi-isomorphism properties, and
the resulting canonical identification in every degree. -/
def balanceType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) (B : Type w)
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : LeftResolution R A) (I : InjectiveResolution R B), P.IsProjective →
    ∃ (α : homComplex P.complex B ⟶ homTotal P.complex I.complex)
      (β : injectiveHom A I.complex ⟶ homTotal P.complex I.complex),
      IsProjectiveAugmentation P I α ∧ IsInjectiveAugmentation P I β ∧
      QuasiIsomorphism α ∧ QuasiIsomorphism β ∧
      ∀ n, ∃ e : Homology (injectiveHom A I.complex) n ≃ₗ[ℤ] ExtWith P B n,
        (homologyMap α n).comp e.toLinearMap = homologyMap β n

/-- Naturality for every pair of module maps, every pair of lifts, and every
choice of resolutions. Identity coefficient maps specialize to all canonical
resolution comparisons; equality for all lifts includes lift independence. -/
def balance_naturalType : Prop :=
  ∀ (R : Type u) [Ring R] (A A' : Type v) (B B' : Type w)
    [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
    [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (P : LeftResolution R A) (Q : LeftResolution R A')
    (I : InjectiveResolution R B) (J : InjectiveResolution R B'),
    P.IsProjective → Q.IsProjective →
    ∀ (f : A' →ₗ[R] A) (g : B →ₗ[R] B')
      (l : Q.complex ⟶ P.complex) (m : I.complex ⟶ J.complex),
    ChainLift Q P f l → CochainLift (ofInjective I) J g m →
    ∀ (α : homComplex P.complex B ⟶ homTotal P.complex I.complex)
      (β : injectiveHom A I.complex ⟶ homTotal P.complex I.complex)
      (α' : homComplex Q.complex B' ⟶ homTotal Q.complex J.complex)
      (β' : injectiveHom A' J.complex ⟶ homTotal Q.complex J.complex),
    IsProjectiveAugmentation P I α → IsInjectiveAugmentation P I β →
    IsProjectiveAugmentation Q J α' → IsInjectiveAugmentation Q J β' →
    QuasiIsomorphism α → QuasiIsomorphism α' →
    ∀ n (e : Homology (injectiveHom A I.complex) n ≃ₗ[ℤ] ExtWith P B n)
      (e' : Homology (injectiveHom A' J.complex) n ≃ₗ[ℤ] ExtWith Q B' n),
    (homologyMap α n).comp e.toLinearMap = homologyMap β n →
    (homologyMap α' n).comp e'.toLinearMap = homologyMap β' n →
    e'.toLinearMap.comp (homologyMap (injectiveHomMap f m) n) =
      (homologyMap (homPreMap l B ≫ homPostMap Q.complex g) n).comp e.toLinearMap

/-- Existence of the two prescribed maps, without the assembly conclusion. -/
def augmentation_mapsType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) (B : Type w)
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : LeftResolution R A) (I : InjectiveResolution R B),
    ∃ (α : homComplex P.complex B ⟶ homTotal P.complex I.complex)
      (β : injectiveHom A I.complex ⟶ homTotal P.complex I.complex),
      IsProjectiveAugmentation P I α ∧ IsInjectiveAugmentation P I β

/-- Endpoint injectivity and exactness in every nonnegative row and column
of the augmented Hom bicomplex. Projectivity is used only for columns. -/
def augmented_exactnessType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) (B : Type w)
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : LeftResolution R A) (I : InjectiveResolution R B), P.IsProjective →
    (∀ p,
      Function.Injective (P103.HomTensorExactness.post (P := P.complex.X p) I.η) ∧
      Function.Exact (P103.HomTensorExactness.post (P := P.complex.X p) I.η)
        (P103.HomTensorExactness.post (P := P.complex.X p) (I.complex.d 0 1).hom) ∧
      ∀ q, Function.Exact
        (P103.HomTensorExactness.post (P := P.complex.X p) (I.complex.d q (q + 1)).hom)
        (P103.HomTensorExactness.post (P := P.complex.X p) (I.complex.d (q + 1) (q + 2)).hom)) ∧
    (∀ q,
      Function.Injective (P103.HomTensorExactness.pre (Q := I.complex.X q) P.ε) ∧
      Function.Exact (P103.HomTensorExactness.pre (Q := I.complex.X q) P.ε)
        (P103.HomTensorExactness.pre (Q := I.complex.X q) (P.complex.d 1 0).hom) ∧
      ∀ p, Function.Exact
        (P103.HomTensorExactness.pre (Q := I.complex.X q) (P.complex.d (p + 1) p).hom)
        (P103.HomTensorExactness.pre (Q := I.complex.X q) (P.complex.d (p + 2) (p + 1)).hom))

/-- The algebraic extraction of the canonical comparison from two proven
quasi-isomorphisms. The assembly hypotheses are not replaced by this statement. -/
def comparison_from_quasiIsomorphismsType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) (B : Type w)
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : LeftResolution R A) (I : InjectiveResolution R B)
    (α : homComplex P.complex B ⟶ homTotal P.complex I.complex)
    (β : injectiveHom A I.complex ⟶ homTotal P.complex I.complex),
    QuasiIsomorphism α → QuasiIsomorphism β →
    ∀ n, ∃ e : Homology (injectiveHom A I.complex) n ≃ₗ[ℤ] ExtWith P B n,
      (homologyMap α n).comp e.toLinearMap = homologyMap β n

/-- The same-side right module statement is the identical construction over
Rᵐᵒᵖ, including its actual augmentation maps and every nonnegative degree. -/
def right_balanceType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) (B : Type w)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] [AddCommGroup B] [Module Rᵐᵒᵖ B]
    (P : LeftResolution Rᵐᵒᵖ A) (I : InjectiveResolution Rᵐᵒᵖ B), P.IsProjective →
    ∃ (α : homComplex P.complex B ⟶ homTotal P.complex I.complex)
      (β : injectiveHom A I.complex ⟶ homTotal P.complex I.complex),
      IsProjectiveAugmentation P I α ∧ IsInjectiveAugmentation P I β ∧
      QuasiIsomorphism α ∧ QuasiIsomorphism β ∧
      ∀ n, ∃ e : Homology (injectiveHom A I.complex) n ≃ₗ[ℤ] ExtWith P B n,
        (homologyMap α n).comp e.toLinearMap = homologyMap β n


def injective_lift_independentType : Prop :=
  ∀ (R : Type u) [Ring R]
    {A A' : Type v} {B B' : Type w}
    [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
    [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (I : InjectiveResolution R B) (J : InjectiveResolution R B')
    (f : A' →ₗ[R] A) (g : B →ₗ[R] B')
    (m m' : I.complex ⟶ J.complex)
    (_hm : CochainLift (ofInjective I) J g m)
    (_hm' : CochainLift (ofInjective I) J g m') (n : ℕ),

    homologyMap (injectiveHomMap f m) n =
      homologyMap (injectiveHomMap f m') n

def injective_coherentType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A] (n : ℕ),

    Nonempty (CoherentComparison
      (fun B : ModuleCat.{w} R => InjectiveResolution R B)
      (injectiveComplex R) injectiveOver
      (appliedHomology (covariantHom (R := R) A) (ComplexShape.up ℕ) n))

def balance_natural_extMapsType : Prop :=
  ∀ (R : Type u) [Ring R]
    (n : ℕ) (E : ExtMaps.{u,v,w} R n)
    {A A' : ModuleCat.{v} R} {B B' : ModuleCat.{w} R}
    (P : ProjectiveChoice R A) (Q : ProjectiveChoice R A')
    (I : InjectiveResolution R B) (J : InjectiveResolution R B')
    (f : A' ⟶ A) (g : B ⟶ B') (m : I.complex ⟶ J.complex)
    (_hm : CochainLift (ofInjective I) J g.hom m)
    (α : homComplex P.val.complex B ⟶ homTotal P.val.complex I.complex)
    (β : injectiveHom A I.complex ⟶ homTotal P.val.complex I.complex)
    (α' : homComplex Q.val.complex B' ⟶ homTotal Q.val.complex J.complex)
    (β' : injectiveHom A' J.complex ⟶ homTotal Q.val.complex J.complex)
    (_hα : IsProjectiveAugmentation P.val I α)
    (_hβ : IsInjectiveAugmentation P.val I β)
    (_hα' : IsProjectiveAugmentation Q.val J α')
    (_hβ' : IsInjectiveAugmentation Q.val J β')
    (_hqα : QuasiIsomorphism α) (_hqα' : QuasiIsomorphism α')
    (e : Homology (injectiveHom A I.complex) n ≃ₗ[ℤ] ExtWith P.val B n)
    (e' : Homology (injectiveHom A' J.complex) n ≃ₗ[ℤ] ExtWith Q.val B' n)
    (_he : (homologyMap α n).comp e.toLinearMap = homologyMap β n)
    (_he' : (homologyMap α' n).comp e'.toLinearMap = homologyMap β' n),

    e'.toLinearMap.comp (homologyMap (injectiveHomMap f.hom m) n) =
      (E.map P Q f g).comp e.toLinearMap

end
end P103.Specs.Ch11.ExtBalance
