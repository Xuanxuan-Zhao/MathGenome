import Mathlib.Algebra.Homology.TotalComplexSymmetry
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.ExtBalance
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtTorDefinitions
import Mathlib.Algebra.Category.ModuleCat.Products

namespace P103.Ch11.ExtBalance
open CategoryTheory CategoryTheory.Limits
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions P103.Specs.Ch11.ExtBalance
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w x y
variable {R : Type u} [Ring R]

/-- The two unsigned arrows commute, over an arbitrary unital ring. -/
theorem hom_differentials_commute
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : CochainComplex (ModuleCat.{w} R) ℕ) (p p' q q' : ℕ)
    (h : C.X p →ₗ[R] D.X q) :
    (D.d q q').hom.comp (h.comp (C.d p' p).hom) =
      ((D.d q q').hom.comp h).comp (C.d p' p).hom := rfl

/-- The vertical complex at fixed p is covariant Hom into I. -/
theorem vertical_differential
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : CochainComplex (ModuleCat.{w} R) ℕ) (p q q' : ℕ)
    (h : C.X p →ₗ[R] D.X q) :
    (((homBicomplex C D).X p).d q q').hom h = (D.d q q').hom.comp h := rfl

/-- The horizontal complex at fixed q is contravariant Hom out of P. -/
theorem horizontal_differential
    (C : ChainComplex (ModuleCat.{v} R) ℕ)
    (D : CochainComplex (ModuleCat.{w} R) ℕ) (p p' q : ℕ)
    (h : C.X p →ₗ[R] D.X q) :
    ((homBicomplex C D).d p p').f q h = h.comp (C.d p' p).hom := rfl

section Exactness
open P103.HomTensorExactness
variable {L : Type v} {M : Type w} {N : Type x} {T : Type y}
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup T] [Module R T]

/-- Projective Hom preserves exactness at a middle term, without requiring
that either neighboring map be injective or surjective. -/
theorem post_exact [Module.Projective R T] (i : L →ₗ[R] M) (p : M →ₗ[R] N)
    (he : Function.Exact i p) :
    Function.Exact (post (P := T) i) (post (P := T) p) := by
  intro h
  change p.comp h = 0 ↔ ∃ k, i.comp k = h
  constructor
  · intro hh
    let i' : L →ₗ[R] LinearMap.ker p := i.codRestrict _ he.apply_apply_eq_zero
    have hi' : Function.Surjective i' := by
      intro m
      obtain ⟨a, ha⟩ := (he m.val).mp m.property
      exact ⟨a, Subtype.ext ha⟩
    let h' : T →ₗ[R] LinearMap.ker p :=
      h.codRestrict _ (fun t => LinearMap.congr_fun hh t)
    obtain ⟨k, hk⟩ := Module.projective_lifting_property i' h' hi'
    refine ⟨k, ?_⟩
    ext t
    exact congrArg Subtype.val (LinearMap.congr_fun hk t)
  · rintro ⟨k, rfl⟩
    ext t
    exact he.apply_apply_eq_zero (k t)

/-- Injective Hom preserves exactness at a middle term. The `Small`
hypothesis only says that the ring fits in the injective module's universe;
resolution terms have this property by their `max u w` universe. -/
theorem pre_exact [Small.{y} R] [Module.Injective R T]
    (i : L →ₗ[R] M) (p : M →ₗ[R] N) (he : Function.Exact i p) :
    Function.Exact (pre (Q := T) p) (pre (Q := T) i) := by
  intro h
  change h.comp i = 0 ↔ ∃ k : N →ₗ[R] T, k.comp p = h
  constructor
  · intro hh
    let p' : M →ₗ[R] LinearMap.range p := p.rangeRestrict
    have hp' : Function.Surjective p' := by
      rintro ⟨_, m, rfl⟩
      exact ⟨m, rfl⟩
    have hker : LinearMap.ker p' ≤ LinearMap.ker h := by
      intro m hm
      have hpm : p m = 0 := congrArg Subtype.val hm
      obtain ⟨a, rfl⟩ := (he m).mp hpm
      exact LinearMap.congr_fun hh a
    let h' : LinearMap.range p →ₗ[R] T := p'.liftOfSurjective hp' ⟨h, hker⟩
    obtain ⟨k, hk⟩ := Module.Injective.extension_property R T _ _
      (LinearMap.range p).subtype Subtype.val_injective h'
    refine ⟨k, ?_⟩
    ext m
    calc
      k (p m) = h' (p' m) := LinearMap.congr_fun hk (p' m)
      _ = h m := LinearMap.equivOfSurjective_apply hp' hker
  · rintro ⟨k, rfl⟩
    ext a
    change k (p (i a)) = 0
    rw [he.apply_apply_eq_zero, map_zero]

end Exactness

section Resolutions
open P103.HomTensorExactness
variable {A : Type v} {B : Type w}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- Exactness of the entire augmented column after covariant Hom. -/
theorem augmented_column_exact (P : LeftResolution R A) (I : InjectiveResolution R B)
    (hP : P.IsProjective) (p : ℕ) :
    Function.Injective (post (P := P.complex.X p) I.η) ∧
    Function.Exact (post (P := P.complex.X p) I.η)
      (post (P := P.complex.X p) (I.complex.d 0 1).hom) ∧
    ∀ q, Function.Exact (post (P := P.complex.X p) (I.complex.d q (q + 1)).hom)
      (post (P := P.complex.X p) (I.complex.d (q + 1) (q + 2)).hom) := by
  let := hP p
  obtain ⟨hi, he⟩ := P103.HomTensorExactness.homCovariant R _ _ _ (P.complex.X p)
    I.η (I.complex.d 0 1).hom I.injective_η I.exact_zero
  exact ⟨hi, he, fun q => post_exact _ _ (I.exact_succ q)⟩

/-- Exactness of the entire augmented row after contravariant Hom. -/
theorem augmented_row_exact (P : LeftResolution R A) (I : InjectiveResolution R B)
    (q : ℕ) :
    Function.Injective (pre (Q := I.complex.X q) P.ε) ∧
    Function.Exact (pre (Q := I.complex.X q) P.ε)
      (pre (Q := I.complex.X q) (P.complex.d 1 0).hom) ∧
    ∀ p, Function.Exact (pre (Q := I.complex.X q) (P.complex.d (p + 1) p).hom)
      (pre (Q := I.complex.X q) (P.complex.d (p + 2) (p + 1)).hom) := by
  let := I.injectiveTerm q
  obtain ⟨hi, he⟩ := P103.HomTensorExactness.homContravariant R _ _ _ (I.complex.X q)
    (P.complex.d 1 0).hom P.ε (LinearMap.exact_iff.mpr P.exact_zero.symm) P.surjective
  exact ⟨hi, he, fun p => pre_exact _ _ (LinearMap.exact_iff.mpr (P.exact_succ p).symm)⟩

end Resolutions

/-- Simultaneous action on the two entries of the Hom bicomplex. -/
def homBicomplexMap
    {C C' : ChainComplex (ModuleCat.{v} R) ℕ}
    {D D' : CochainComplex (ModuleCat.{w} R) ℕ}
    (l : C' ⟶ C) (m : D ⟶ D') : homBicomplex C D ⟶ homBicomplex C' D' where
  f p := injectiveHomMap (l.f p).hom m
  comm' p p' _ := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change C.X p →ₗ[R] D.X q at h
    apply LinearMap.ext
    intro a
    change (m.f q).hom (h ((l.f p).hom ((C'.d p' p).hom a))) =
      (m.f q).hom (h ((C.d p' p).hom ((l.f p').hom a)))
    congr 2
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (l.comm p' p).symm) a

abbrev homTotalMap
    {C C' : ChainComplex (ModuleCat.{v} R) ℕ}
    {D D' : CochainComplex (ModuleCat.{w} R) ℕ}
    (l : C' ⟶ C) (m : D ⟶ D') : homTotal C D ⟶ homTotal C' D' :=
  HomologicalComplex₂.total.map (homBicomplexMap l m) (ComplexShape.up ℕ)

/-- The signed differential on one summand of the nonnegative total. -/
theorem total_inclusion_d
    (K : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (p q n : ℕ) (h : p + q = n) :
    K.ιTotal (ComplexShape.up ℕ) p q n h ≫ (K.total (ComplexShape.up ℕ)).d n (n + 1) =
      (K.d p (p + 1)).f q ≫ K.ιTotal (ComplexShape.up ℕ) (p + 1) q (n + 1) (by change p + 1 + q = n + 1; omega) +
        ((-1 : ℤˣ) ^ p) • ((K.X p).d q (q + 1) ≫
          K.ιTotal (ComplexShape.up ℕ) p (q + 1) (n + 1) (by change p + (q + 1) = n + 1; omega)) := by
  change _ ≫ (K.D₁ _ _ _ + K.D₂ _ _ _) = _
  rw [Preadditive.comp_add, K.ι_D₁, K.ι_D₂,
    K.d₁_eq (ComplexShape.up ℕ) (by rfl) q (n + 1) (by change p + 1 + q = n + 1; omega),
    K.d₂_eq (ComplexShape.up ℕ) p (by rfl) (n + 1) (by change p + (q + 1) = n + 1; omega)]
  change (1 : ℤˣ) • _ + ((-1 : ℤˣ) ^ p) • _ = _
  rw [one_smul]

section Augmentations
open P103.HomTensorExactness
variable {A : Type v} {B : Type w}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

abbrev projectiveAugmentationComponent (P : LeftResolution R A)
    (I : InjectiveResolution R B) (n : ℕ) :=
  ModuleCat.ofHom (post (P := P.complex.X n) I.η).toIntLinearMap ≫
    (homBicomplex P.complex I.complex).ιTotal (ComplexShape.up ℕ) n 0 n (by simp)

abbrev injectiveAugmentationComponent (P : LeftResolution R A)
    (I : InjectiveResolution R B) (n : ℕ) :=
  ModuleCat.ofHom (pre (Q := I.complex.X n) P.ε).toIntLinearMap ≫
    (homBicomplex P.complex I.complex).ιTotal (ComplexShape.up ℕ) 0 n n (by simp)

theorem projectiveAugmentation_comm (P : LeftResolution R A)
    (I : InjectiveResolution R B) (n : ℕ) :
    projectiveAugmentationComponent P I n ≫ (homTotal P.complex I.complex).d n (n + 1) =
      (homComplex P.complex B).d n (n + 1) ≫ projectiveAugmentationComponent P I (n + 1) := by
  dsimp only [projectiveAugmentationComponent]
  rw [Category.assoc, total_inclusion_d, Preadditive.comp_add,
    Linear.comp_units_smul, ← Category.assoc, ← Category.assoc]
  have hz : ModuleCat.ofHom (post (P := P.complex.X n) I.η).toIntLinearMap ≫
      ((homBicomplex P.complex I.complex).X n).d 0 (0 + 1) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change P.complex.X n →ₗ[R] B at h
    apply LinearMap.ext
    intro a
    exact I.exact_zero.apply_apply_eq_zero (h a)
  rw [hz, zero_comp, smul_zero, add_zero]
  rfl

def projectiveAugmentation (P : LeftResolution R A) (I : InjectiveResolution R B) :
    homComplex P.complex B ⟶ homTotal P.complex I.complex :=
  CochainComplex.ofHom (projectiveAugmentationComponent P I) (projectiveAugmentation_comm P I)

theorem projectiveAugmentation_formula (P : LeftResolution R A) (I : InjectiveResolution R B) :
    IsProjectiveAugmentation P I (projectiveAugmentation P I) := fun _ => rfl

theorem injectiveAugmentation_comm (P : LeftResolution R A)
    (I : InjectiveResolution R B) (n : ℕ) :
    injectiveAugmentationComponent P I n ≫ (homTotal P.complex I.complex).d n (n + 1) =
      (injectiveHom A I.complex).d n (n + 1) ≫ injectiveAugmentationComponent P I (n + 1) := by
  dsimp only [injectiveAugmentationComponent]
  rw [Category.assoc, total_inclusion_d, Preadditive.comp_add,
    Linear.comp_units_smul, ← Category.assoc, ← Category.assoc]
  have hz : ModuleCat.ofHom (pre (Q := I.complex.X n) P.ε).toIntLinearMap ≫
      ((homBicomplex P.complex I.complex).d 0 (0 + 1)).f n = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change A →ₗ[R] I.complex.X n at h
    apply LinearMap.ext
    intro a
    change h (P.ε ((P.complex.d 1 0).hom a)) = 0
    rw [(LinearMap.exact_iff.mpr P.exact_zero.symm).apply_apply_eq_zero, map_zero]
  rw [hz, zero_comp, zero_add, pow_zero, one_smul]
  rfl

def injectiveAugmentation (P : LeftResolution R A) (I : InjectiveResolution R B) :
    injectiveHom A I.complex ⟶ homTotal P.complex I.complex :=
  CochainComplex.ofHom (injectiveAugmentationComponent P I) (injectiveAugmentation_comm P I)

theorem injectiveAugmentation_formula (P : LeftResolution R A) (I : InjectiveResolution R B) :
    IsInjectiveAugmentation P I (injectiveAugmentation P I) := fun _ => rfl

end Augmentations

section Naturality
open P103.HomTensorExactness
variable {A A' : Type v} {B B' : Type w}
  [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
  [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
  (P : LeftResolution R A) (Q : LeftResolution R A')
  (I : InjectiveResolution R B) (J : InjectiveResolution R B')
  (f : A' →ₗ[R] A) (g : B →ₗ[R] B')
  (l : Q.complex ⟶ P.complex) (m : I.complex ⟶ J.complex)

theorem projective_augmentation_naturality
    (hm : CochainLift (ofInjective I) J g m)
    (α : homComplex P.complex B ⟶ homTotal P.complex I.complex)
    (α' : homComplex Q.complex B' ⟶ homTotal Q.complex J.complex)
    (hα : IsProjectiveAugmentation P I α) (hα' : IsProjectiveAugmentation Q J α') :
    α ≫ homTotalMap l m = (homPreMap l B ≫ homPostMap Q.complex g) ≫ α' := by
  apply HomologicalComplex.Hom.ext
  funext n
  change α.f n ≫ (homTotalMap l m).f n =
    ((homPreMap l B ≫ homPostMap Q.complex g).f n) ≫ α'.f n
  rw [hα n, hα' n]
  dsimp only [homTotalMap]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc, ← Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change P.complex.X n →ₗ[R] B at h
  apply LinearMap.ext
  intro a
  exact LinearMap.congr_fun hm (h ((l.f n).hom a))

theorem injective_augmentation_naturality
    (hl : ChainLift Q P f l)
    (β : injectiveHom A I.complex ⟶ homTotal P.complex I.complex)
    (β' : injectiveHom A' J.complex ⟶ homTotal Q.complex J.complex)
    (hβ : IsInjectiveAugmentation P I β) (hβ' : IsInjectiveAugmentation Q J β') :
    β ≫ homTotalMap l m = injectiveHomMap f m ≫ β' := by
  apply HomologicalComplex.Hom.ext
  funext n
  change β.f n ≫ (homTotalMap l m).f n = (injectiveHomMap f m).f n ≫ β'.f n
  rw [hβ n, hβ' n]
  dsimp only [homTotalMap]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc, ← Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change A →ₗ[R] I.complex.X n at h
  apply LinearMap.ext
  intro a
  change (m.f n).hom (h (P.ε ((l.f 0).hom a))) = (m.f n).hom (h (f (Q.ε a)))
  exact congrArg (fun a => (m.f n).hom (h a)) (LinearMap.congr_fun hl a)

end Naturality

theorem quotient_homology_comp
    {C D E : CochainComplex (ModuleCat.{v} ℤ) ℕ} (f : C ⟶ D) (g : D ⟶ E) (n : ℕ) :
    homologyMap (f ≫ g) n = (homologyMap g n).comp (homologyMap f n) :=
  P103.Ch10.Complexes.homologyMap_comp f g n

/-- Every canonical identification arising from the two augmentation maps is
natural for all module maps and all compatible lifts. -/
theorem balance_natural : balance_naturalType.{u,v,w} := by
  intro R _ A A' B B' _ _ _ _ _ _ _ _ P Q I J _ _ f g l m hl hm
    α β α' β' hα hβ hα' hβ' _ hqα' n e e' he he'
  have ha := projective_augmentation_naturality P Q I J g l m hm α α' hα hα'
  have hb := injective_augmentation_naturality P Q I J f l m hl β β' hβ hβ'
  have haH := congrArg (fun k => homologyMap k n) ha
  have hbH := congrArg (fun k => homologyMap k n) hb
  rw [quotient_homology_comp, quotient_homology_comp] at haH hbH
  apply LinearMap.ext
  intro z
  apply (hqα' n).1
  calc
    homologyMap α' n (e' (homologyMap (injectiveHomMap f m) n z)) =
      homologyMap β' n (homologyMap (injectiveHomMap f m) n z) :=
        DFunLike.congr_fun he' _
    _ = homologyMap (homTotalMap l m) n (homologyMap β n z) :=
      (DFunLike.congr_fun hbH z).symm
    _ = homologyMap (homTotalMap l m) n (homologyMap α n (e z)) := by
      exact congrArg (homologyMap (homTotalMap l m) n) (DFunLike.congr_fun he z).symm
    _ = homologyMap α' n
        (homologyMap (homPreMap l B ≫ homPostMap Q.complex g) n (e z)) :=
      DFunLike.congr_fun haH (e z)

theorem augmentation_maps : augmentation_mapsType.{u,v,w} := by
  intro R _ A B _ _ _ _ P I
  exact ⟨projectiveAugmentation P I, injectiveAugmentation P I,
    projectiveAugmentation_formula P I, injectiveAugmentation_formula P I⟩

theorem augmented_exactness : augmented_exactnessType.{u,v,w} := by
  intro R _ A B _ _ _ _ P I hP
  exact ⟨augmented_column_exact P I hP, augmented_row_exact P I⟩

/-- Once assembly supplies the quasi-isomorphisms, this is the required
canonical comparison from injectively computed cohomology to projective Ext. -/
def comparisonOfQuasiIsomorphisms
    {A : Type v} {B : Type w} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (P : LeftResolution R A) (I : InjectiveResolution R B)
    (α : homComplex P.complex B ⟶ homTotal P.complex I.complex)
    (β : injectiveHom A I.complex ⟶ homTotal P.complex I.complex)
    (hα : QuasiIsomorphism α) (hβ : QuasiIsomorphism β) (n : ℕ) :
    Homology (injectiveHom A I.complex) n ≃ₗ[ℤ] ExtWith P B n :=
  (LinearEquiv.ofBijective (homologyMap β n) (hβ n)).trans
    (LinearEquiv.ofBijective (homologyMap α n) (hα n)).symm

theorem comparisonOfQuasiIsomorphisms_formula
    {A : Type v} {B : Type w} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (P : LeftResolution R A) (I : InjectiveResolution R B)
    (α : homComplex P.complex B ⟶ homTotal P.complex I.complex)
    (β : injectiveHom A I.complex ⟶ homTotal P.complex I.complex)
    (hα : QuasiIsomorphism α) (hβ : QuasiIsomorphism β) (n : ℕ) :
    (homologyMap α n).comp
      (comparisonOfQuasiIsomorphisms P I α β hα hβ n).toLinearMap = homologyMap β n := by
  apply DFunLike.ext
  intro z
  exact (LinearEquiv.ofBijective (homologyMap α n) (hα n)).apply_symm_apply _

/-- The characterization by the augmentation square forces uniqueness. -/
theorem comparison_unique
    {A : Type v} {B : Type w} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (P : LeftResolution R A) (I : InjectiveResolution R B)
    (α : homComplex P.complex B ⟶ homTotal P.complex I.complex)
    (β : injectiveHom A I.complex ⟶ homTotal P.complex I.complex)
    (hα : QuasiIsomorphism α) (n : ℕ)
    (e e' : Homology (injectiveHom A I.complex) n ≃ₗ[ℤ] ExtWith P B n)
    (he : (homologyMap α n).comp e.toLinearMap = homologyMap β n)
    (he' : (homologyMap α n).comp e'.toLinearMap = homologyMap β n) : e = e' := by
  ext z
  apply (hα n).1
  exact (DFunLike.congr_fun he z).trans (DFunLike.congr_fun he' z).symm

theorem comparison_from_quasiIsomorphisms : comparison_from_quasiIsomorphismsType.{u,v,w} := by
  intro R _ A B _ _ _ _ P I α β hα hβ n
  exact ⟨comparisonOfQuasiIsomorphisms P I α β hα hβ n,
    comparisonOfQuasiIsomorphisms_formula P I α β hα hβ n⟩

instance upNatTotalSymmetry : TotalComplexShapeSymmetry
    (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) where
  symm p q := Nat.add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p*q)
  σ_ε₁ := by
    rintro p _ rfl q
    change (-1 : ℤˣ) ^ (p*q) * 1 = (-1 : ℤˣ)^q * (-1 : ℤˣ)^((p+1)*q)
    rw [mul_one, Nat.add_mul, one_mul, pow_add, mul_left_comm, Int.units_mul_self, mul_one]
  σ_ε₂ := by
    rintro p q _ rfl
    change (-1 : ℤˣ) ^ (p*q) * (-1 : ℤˣ)^p = 1 * (-1 : ℤˣ)^(p*(q+1))
    rw [one_mul, Nat.mul_add, Nat.mul_one, pow_add]

namespace Native
open DirectSum
variable (K : HomologicalComplex₂ (ModuleCat.{v} R)
  (ComplexShape.up ℕ) (ComplexShape.up ℕ))
abbrev Tot := K.total (ComplexShape.up ℕ)
abbrev incl (p q n : ℕ) (h : p + q = n) :=
  K.ιTotal (ComplexShape.up ℕ) p q n h
abbrev Family (n : ℕ) (i : {i : ℕ × ℕ // i.1 + i.2 = n}) := (K.X i.val.1).X i.val.2

def termEquiv (n : ℕ) : (Tot K).X n ≃ₗ[R] (⨁ i : {i : ℕ × ℕ // i.1+i.2=n}, Family K n i) :=
  (ModuleCat.coprodIsoDirectSum (fun i => Family K n i)).toLinearEquiv

def proj (p q n : ℕ) (h : p + q = n) : (Tot K).X n ⟶ (K.X p).X q :=
  ModuleCat.ofHom ((DirectSum.component R _ (fun i => Family K n i) ⟨(p,q),h⟩).comp
    (termEquiv K n).toLinearMap)

lemma termEquiv_incl (p q n : ℕ) (h : p + q = n) (x : (K.X p).X q) :
    termEquiv K n ((incl K p q n h).hom x) =
      DirectSum.lof R _ (fun i => Family K n i) ⟨(p,q),h⟩ x :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (ModuleCat.ι_coprodIsoDirectSum_hom (fun i => Family K n i) ⟨(p,q),h⟩)) x

@[reassoc (attr := simp)] lemma incl_proj_self (p q n : ℕ) (h : p + q = n) :
    incl K p q n h ≫ proj K p q n h = 𝟙 _ := by
  apply ModuleCat.hom_ext
  ext x
  change DirectSum.component R _ (fun i => Family K n i) ⟨(p,q),h⟩
    (termEquiv K n ((incl K p q n h).hom x)) = x
  rw [termEquiv_incl, DirectSum.component.lof_self]

@[reassoc] lemma incl_proj_ne (p q i j n : ℕ) (h : p + q = n) (h' : i+j=n)
    (hne : p ≠ i ∨ q ≠ j) : incl K p q n h ≫ proj K i j n h' = 0 := by
  apply ModuleCat.hom_ext
  ext x
  change DirectSum.component R _ (fun i => Family K n i) ⟨(i,j),h'⟩
    (termEquiv K n ((incl K p q n h).hom x)) = 0
  rw [termEquiv_incl, DirectSum.component.of, dite_eq_right]
  intro he
  have he' := congrArg Subtype.val he
  exact hne.elim (fun hp => hp (congrArg Prod.fst he'))
    (fun hq => hq (congrArg Prod.snd he'))

lemma ext (n : ℕ) (x y : (Tot K).X n)
    (h : ∀ p q (hpq : p+q=n), (proj K p q n hpq).hom x = (proj K p q n hpq).hom y) :
    x = y := by
  apply (termEquiv K n).injective
  apply DirectSum.ext_component R
  rintro ⟨⟨p,q⟩,hpq⟩
  exact h p q hpq

/-- The target coordinate with positive vertical index; horizontal degree zero
has no horizontal incoming differential. -/
lemma proj_d (p q n : ℕ) (h : p+q=n) :
    (Tot K).d n (n+1) ≫ proj K p (q+1) (n+1) (by omega) =
      (if hp : p = 0 then 0 else
        proj K (p-1) (q+1) n (by omega) ≫ (K.d (p-1) p).f (q+1)) +
      ((-1 : ℤˣ)^p) • (proj K p q n h ≫ (K.X p).d q (q+1)) := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i+j=n at hij
  change incl K i j n hij ≫ ((Tot K).d n (n+1) ≫ _) = _
  rw [← Category.assoc, total_inclusion_d]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.units_smul_comp,
    Linear.comp_units_smul, Category.assoc]
  by_cases hip : i+1 = p
  · have hj : j = q+1 := by omega
    subst p j
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceDIte]
    change _ = (incl K i (q+1) n hij ≫ proj K i (q+1) n hij ≫ (K.d i (i+1)).f (q+1)) +
      ((-1 : ℤˣ)^(i+1)) • (incl K i (q+1) n hij ≫ proj K (i+1) q n h ≫ (K.X (i+1)).d q (q+1))
    rw [incl_proj_self, incl_proj_ne K i (q+1+1) (i+1) (q+1) (n+1) _ _ (Or.inl (by omega)),
      incl_proj_self_assoc K i (q+1) n hij,
      incl_proj_ne_assoc K i (q+1) (i+1) q n _ _ (Or.inl (by omega))]
    simp
  · by_cases hi : i = p
    · have hj : j=q := by omega
      subst i j
      rw [incl_proj_ne K (p+1) q p (q+1) (n+1) _ _ (Or.inl (by omega)),
        incl_proj_self, incl_proj_self_assoc]
      by_cases hp : p=0
      · simp [hp]
      · simp only [hp, ↓reduceDIte]
        rw [incl_proj_ne_assoc K p q (p-1) (q+1) n _ _ (Or.inl (by omega))]
        simp
    · rw [incl_proj_ne K (i+1) j p (q+1) (n+1) _ _ (Or.inl hip),
        incl_proj_ne K i (j+1) p (q+1) (n+1) _ _ (Or.inl hi),
        incl_proj_ne_assoc K i j p q n _ _ (Or.inl hi)]
      by_cases hp : p=0
      · simp [hp]
      · simp only [hp, ↓reduceDIte]
        rw [incl_proj_ne_assoc K i j (p-1) (q+1) n _ _ (Or.inl (by omega))]
        simp

lemma d_incl_self (p q n : ℕ) (h : p+q+1=n)
    (w : (K.X p).X q) :
    (proj K p (q+1) n (by omega)).hom
      (((Tot K).d (n-1) n).hom ((incl K p q (n-1) (by omega)).hom w)) =
        ((-1 : ℤˣ)^p) • ((K.X p).d q (q+1)).hom w := by
  subst n
  have hd := total_inclusion_d K p q (p+q) rfl
  have he := congrArg (fun f => f ≫ proj K p (q+1) (p+q+1) (by omega)) hd
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc] at he
  rw [incl_proj_ne K (p+1) q p (q+1) (p+q+1) _ _ (Or.inl (by omega)), incl_proj_self] at he
  simp only [comp_zero, Category.comp_id, zero_add] at he
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom he) w

lemma d_incl_below (p q n i j : ℕ) (h : p+q+1=n)
    (hij : i+j=n) (hi : i<p) (w : (K.X p).X q) :
    (proj K i j n hij).hom
      (((Tot K).d (n-1) n).hom ((incl K p q (n-1) (by omega)).hom w)) = 0 := by
  subst n
  have hd := total_inclusion_d K p q (p+q) rfl
  have he := congrArg (fun f => f ≫ proj K i j (p+q+1) hij) hd
  simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc] at he
  rw [incl_proj_ne K (p+1) q i j (p+q+1) _ _ (Or.inl (by omega)),
    incl_proj_ne K p (q+1) i j (p+q+1) _ _ (Or.inl (by omega))] at he
  simp only [comp_zero, smul_zero, add_zero] at he
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom he) w

lemma vertical_cycle (n P q : ℕ) (h : P+q=n) (z : (Tot K).X n)
    (hdz : ∀ p q (h : p+q=n), (proj K p (q+1) (n+1) (by omega)).hom
      (((Tot K).d n (n+1)).hom z) = 0)
    (hbelow : ∀ p q (h : p+q=n), p<P → (proj K p q n h).hom z = 0) :
    ((K.X P).d q (q+1)).hom ((proj K P q n h).hom z) = 0 := by
  have he := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (proj_d K P q n h)) z
  have hzero := hdz P q h
  change (proj K P (q+1) (n+1) _).hom (((Tot K).d n (n+1)).hom z) = _ at he
  rw [hzero] at he
  by_cases hp : P=0
  · subst P
    simp only [↓reduceDIte, zero_add, pow_zero, one_smul] at he
    exact he.symm
  · simp only [hp, ↓reduceDIte, ModuleCat.hom_add, LinearMap.add_apply,
      ModuleCat.hom_comp, LinearMap.comp_apply] at he
    rw [hbelow (P-1) (q+1) (by omega) (by omega), map_zero, zero_add] at he
    change 0 = ((-1 : ℤˣ)^P) • ((K.X P).d q (q+1)).hom
      ((proj K P q n h).hom z) at he
    exact (smul_eq_zero_iff_eq _).mp he.symm

lemma normalize
    (Y : CochainComplex (ModuleCat.{v} R) ℕ)
    (a : ∀ p, Y.X p ⟶ (K.X p).X 0)
    (α : Y ⟶ Tot K) (hα : ∀ n, α.f n = a n ≫ incl K n 0 n (by simp))
    (hex0 : ∀ p, Function.Exact (a p).hom ((K.X p).d 0 1).hom)
    (hex : ∀ p q, Function.Exact ((K.X p).d q (q+1)).hom
      ((K.X p).d (q+1) (q+2)).hom)
    (n k : ℕ) : ∀ P, P+k=n → ∀ z : (Tot K).X n,
    (∀ p q (h : p+q=n), (proj K p (q+1) (n+1) (by omega)).hom
      (((Tot K).d n (n+1)).hom z) = 0) →
    (∀ p q (h : p+q=n), p<P → (proj K p q n h).hom z = 0) →
    ∃ (b : Y.X n) (y : (Tot K).X (n-1)),
      z = (α.f n).hom b + ((Tot K).d (n-1) n).hom y := by
  induction k with
  | zero =>
    intro P hPn z hdz hbelow
    have hPn' : P=n := by omega
    subst P
    have hv := vertical_cycle K n n 0 (by omega) z hdz hbelow
    obtain ⟨b,hb⟩ := (hex0 n _).mp hv
    refine ⟨b,0,?_⟩
    rw [map_zero, add_zero, hα]
    apply ext K n
    intro p q hpq
    by_cases hp : p=n
    · have hq : q=0 := by omega
      subst p q
      have he := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (incl_proj_self K n 0 n (by simp))) ((a n).hom b)
      exact hb.symm.trans he.symm
    · have he := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
        (incl_proj_ne K n 0 p q n (by simp) hpq (Or.inl (Ne.symm hp)))) ((a n).hom b)
      exact (hbelow p q hpq (by omega)).trans he.symm
  | succ k ih =>
    intro P hPk z hdz hbelow
    have hv := vertical_cycle K n P (k+1) (by omega) z hdz hbelow
    obtain ⟨w,hw⟩ := (hex P k _).mp hv
    let w' := ((-1 : ℤˣ)^P) • w
    have hw' : ((-1 : ℤˣ)^P) • ((K.X P).d k (k+1)).hom w' =
        (proj K P (k+1) n (by omega)).hom z := by
      dsimp only [w']
      change ((-1 : ℤˣ)^P) • (((K.X P).d k (k+1)).hom
        ((((-1 : ℤˣ)^P : ℤˣ) : ℤ) • w)) = _
      rw [map_zsmul, ← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
      exact hw
    let t : (Tot K).X (n-1) := (incl K P k (n-1) (by omega)).hom w'
    let z' := z - ((Tot K).d (n-1) n).hom t
    have hdd : ((Tot K).d n (n+1)).hom (((Tot K).d (n-1) n).hom t) = 0 :=
      DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((Tot K).d_comp_d (n-1) n (n+1))) t
    have hdz' : ∀ p q (h : p+q=n), (proj K p (q+1) (n+1) (by omega)).hom
        (((Tot K).d n (n+1)).hom z') = 0 := by
      intro p q h
      dsimp only [z']
      rw [map_sub, hdd, sub_zero]
      exact hdz p q h
    have hbelow' : ∀ p q (h : p+q=n), p<P+1 → (proj K p q n h).hom z' = 0 := by
      intro p q hpq hp
      dsimp only [z']
      rw [map_sub]
      by_cases hp' : p<P
      · rw [hbelow p q hpq hp', d_incl_below K P k n p q (by omega) hpq hp' w']
        exact sub_self _
      · have hpP : p=P := by omega
        subst p
        have hqq : q=k+1 := by omega
        subst q
        dsimp only [t]
        rw [d_incl_self K P k n (by omega), hw', sub_self]
    obtain ⟨b,y,hy⟩ := ih (P+1) (by omega) z' hdz' hbelow'
    refine ⟨b,y+t,?_⟩
    rw [map_add, ← add_assoc, ← hy]
    exact (sub_add_cancel z _).symm

lemma prev_upNat (n : ℕ) : (ComplexShape.up ℕ).prev n = n-1 := by
  cases n with
  | zero => apply ComplexShape.prev_eq_self'; intro k hk; change k+1=0 at hk; omega
  | succ n => exact ComplexShape.prev_eq' _ rfl

lemma bottom_row_quasiIso
    (Y : CochainComplex (ModuleCat.{v} R) ℕ)
    (a : ∀ p, Y.X p ⟶ (K.X p).X 0)
    (α : Y ⟶ Tot K) (hα : ∀ n, α.f n = a n ≫ incl K n 0 n (by simp))
    (hmono : ∀ p, Function.Injective (a p).hom)
    (hex0 : ∀ p, Function.Exact (a p).hom ((K.X p).d 0 1).hom)
    (hex : ∀ p q, Function.Exact ((K.X p).d q (q+1)).hom
      ((K.X p).d (q+1) (q+2)).hom) : QuasiIsomorphism α := by
  have hαmono : ∀ n, Function.Injective (α.f n).hom := by
    intro n x y hxy
    have hleft : α.f n ≫ proj K n 0 n (by simp) = a n := by
      rw [hα, Category.assoc, incl_proj_self, Category.comp_id]
    have hh := congrArg (proj K n 0 n (by simp)).hom hxy
    change (α.f n ≫ proj K n 0 n (by simp)).hom x =
      (α.f n ≫ proj K n 0 n (by simp)).hom y at hh
    rw [hleft] at hh
    exact hmono n hh
  have hαpos : ∀ p q n (h : p+(q+1)=n),
      α.f n ≫ proj K p (q+1) n h = 0 := by
    intro p q n h
    rw [hα, Category.assoc, incl_proj_ne K n 0 p (q+1) n (by simp) h
      (Or.inr (by omega)), comp_zero]
  intro n
  constructor
  · apply (injective_iff_map_eq_zero (homologyMap α n)).mpr
    intro c hc
    obtain ⟨z,rfl⟩ := (cycleBoundaries Y n).mkQ_surjective c
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    have hb := (Submodule.Quotient.mk_eq_zero (cycleBoundaries (Tot K) n)).mp hc
    change ∃ y, ((Tot K).d ((ComplexShape.up ℕ).prev n) n).hom y =
      (α.f n).hom z.val at hb
    rw [prev_upNat] at hb
    obtain ⟨y,hy⟩ := hb
    change ∃ b, (Y.d ((ComplexShape.up ℕ).prev n) n).hom b = z.val
    rw [prev_upNat]
    cases n with
    | zero =>
      have hd : (Tot K).d 0 0 = 0 := (Tot K).shape _ _ (by change ¬0+1=0; omega)
      have hz : z.val = 0 := hαmono 0 (by simpa only [Nat.zero_sub, hd, ModuleCat.hom_zero,
        LinearMap.zero_apply, map_zero] using hy.symm)
      exact ⟨0, by rw [map_zero, hz]⟩
    | succ n =>
      have hdz : ∀ p q (h : p+q=n), (proj K p (q+1) (n+1) (by omega)).hom
          (((Tot K).d n (n+1)).hom y) = 0 := by
        intro p q h
        have hy' : ((Tot K).d n (n+1)).hom y = (α.f (n+1)).hom z.val := hy
        rw [hy']
        exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
          (hαpos p q (n+1) (by omega))) z.val
      obtain ⟨b,t,ht⟩ := normalize K Y a α hα hex0 hex n n 0 (by omega) y hdz
        (by intro p q h hp; omega)
      have hdd : ((Tot K).d n (n+1)).hom (((Tot K).d (n-1) n).hom t) = 0 :=
        DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
          ((Tot K).d_comp_d (n-1) n (n+1))) t
      have hdht := congrArg ((Tot K).d n (n+1)).hom ht
      rw [map_add, hdd, add_zero] at hdht
      have hcomm := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (α.comm n (n+1))) b
      refine ⟨b, ?_⟩
      apply hαmono (n+1)
      exact hcomm.symm.trans (hdht.symm.trans hy)
  · intro c
    obtain ⟨z,rfl⟩ := (cycleBoundaries (Tot K) n).mkQ_surjective c
    have hz : ((Tot K).d n (n+1)).hom z.val = 0 := by
      have hz := z.property
      change ((Tot K).d n ((ComplexShape.up ℕ).next n)).hom z.val = 0 at hz
      rw [CochainComplex.next] at hz
      exact hz
    obtain ⟨b,y,hy⟩ := normalize K Y a α hα hex0 hex n n 0 (by omega) z.val
      (by intro p q h; rw [hz, map_zero]) (by intro p q h hp; omega)
    have hdd : ((Tot K).d n (n+1)).hom (((Tot K).d (n-1) n).hom y) = 0 :=
      DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
        ((Tot K).d_comp_d (n-1) n (n+1))) y
    have hdhy := congrArg ((Tot K).d n (n+1)).hom hy
    rw [hz, map_add, hdd, add_zero] at hdhy
    have hcomm := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (α.comm n (n+1))) b
    have hb : b ∈ cycles Y n := by
      change (Y.d n ((ComplexShape.up ℕ).next n)).hom b = 0
      rw [CochainComplex.next]
      apply hαmono (n+1)
      rw [map_zero]
      exact hcomm.symm.trans hdhy.symm
    refine ⟨homologyClass Y n ⟨b,hb⟩, ?_⟩
    apply (P103.Ch10.Complexes.homologyClass_eq_iff (Tot K) n _ z).mpr
    change ∃ t, ((Tot K).d ((ComplexShape.up ℕ).prev n) n).hom t =
      (α.f n).hom b - z.val
    rw [prev_upNat]
    refine ⟨-y, ?_⟩
    rw [map_neg, hy]
    abel

end Native

namespace Native
variable (K : HomologicalComplex₂ (ModuleCat.{v} R)
  (ComplexShape.up ℕ) (ComplexShape.up ℕ))
variable (Y : CochainComplex (ModuleCat.{v} R) ℕ)
variable (a : ∀ q, Y.X q ⟶ (K.X 0).X q)
variable (β : Y ⟶ K.total (ComplexShape.up ℕ))
lemma left_column_on_flip_formula
    (hβ : ∀ n, β.f n = a n ≫ K.ιTotal (ComplexShape.up ℕ) 0 n n (by simp))
    (n : ℕ) :
    (β ≫ (K.totalFlipIso (ComplexShape.up ℕ)).inv).f n =
      a n ≫ K.flip.ιTotal (ComplexShape.up ℕ) n 0 n (by simp) := by
  rw [HomologicalComplex.comp_f, hβ n, Category.assoc,
    K.ιTotal_totalFlipIso_f_inv]
  change a n ≫ (((-1 : ℤˣ)^(0*n)) • _) = _
  simp
lemma left_column_quasiIsomorphism_of_flip
    (hflip : QuasiIsomorphism (β ≫ (K.totalFlipIso (ComplexShape.up ℕ)).inv)) :
    QuasiIsomorphism β := by
  intro n
  let e := K.totalFlipIso (ComplexShape.up ℕ)
  have hc : (homologyMap e.hom n).comp (homologyMap e.inv n) = LinearMap.id := by
    rw [← P103.Ch10.Complexes.homologyMap_comp, e.inv_hom_id,
      P103.Ch10.Complexes.homologyMap_id]
  have hi : Function.Injective (homologyMap e.inv n) := by
    intro x y hxy
    have hx := DFunLike.congr_fun hc x
    have hy := DFunLike.congr_fun hc y
    exact hx.symm.trans ((congrArg (homologyMap e.hom n) hxy).trans hy)
  have hb := hflip n
  change Function.Bijective (homologyMap (β ≫ e.inv) n) at hb
  have hcomp : homologyMap (β ≫ e.inv) n = (homologyMap e.inv n).comp (homologyMap β n) :=
    P103.Ch10.Complexes.homologyMap_comp β e.inv n
  rw [hcomp] at hb
  constructor
  · intro x y hxy
    exact hb.1 (congrArg (homologyMap e.inv n) hxy)
  · intro z
    obtain ⟨x,hx⟩ := hb.2 (homologyMap e.inv n z)
    exact ⟨x, hi hx⟩
/-- Transport the bottom-row assembly argument through signed interchange. -/
theorem left_column_quasiIso
    (hβ : ∀ n, β.f n = a n ≫ K.ιTotal (ComplexShape.up ℕ) 0 n n (by simp))
    (hmono : ∀ q, Function.Injective (a q).hom)
    (hex0 : ∀ q, Function.Exact (a q).hom ((K.d 0 1).f q).hom)
    (hex : ∀ q p, Function.Exact ((K.d p (p+1)).f q).hom
      ((K.d (p+1) (p+2)).f q).hom) : QuasiIsomorphism β := by
  apply left_column_quasiIsomorphism_of_flip K Y β
  exact bottom_row_quasiIso K.flip Y a
    (β ≫ (K.totalFlipIso (ComplexShape.up ℕ)).inv)
    (left_column_on_flip_formula K Y a β hβ) hmono hex0 hex
end Native

section Balance
open P103.HomTensorExactness
variable {A : Type v} {B : Type w}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- Exact augmented columns give the first prescribed quasi-isomorphism. -/
theorem projectiveAugmentation_quasiIso
    (P : LeftResolution R A) (I : InjectiveResolution R B) (hP : P.IsProjective) :
    QuasiIsomorphism (projectiveAugmentation P I) := by
  apply Native.bottom_row_quasiIso (homBicomplex P.complex I.complex)
    (homComplex P.complex B)
    (fun n => ModuleCat.ofHom (post (P := P.complex.X n) I.η).toIntLinearMap)
    (projectiveAugmentation P I) (fun _ => rfl)
  · exact fun n => (augmented_column_exact P I hP n).1
  · exact fun n => (augmented_column_exact P I hP n).2.1
  · exact fun p q => (augmented_column_exact P I hP p).2.2 q

/-- Exact augmented rows give the second prescribed quasi-isomorphism. -/
theorem injectiveAugmentation_quasiIso
    (P : LeftResolution R A) (I : InjectiveResolution R B) :
    QuasiIsomorphism (injectiveAugmentation P I) := by
  apply Native.left_column_quasiIso (homBicomplex P.complex I.complex)
    (injectiveHom A I.complex)
    (fun n => ModuleCat.ofHom (pre (Q := I.complex.X n) P.ε).toIntLinearMap)
    (injectiveAugmentation P I) (fun _ => rfl)
  · exact fun n => (augmented_row_exact P I n).1
  · exact fun n => (augmented_row_exact P I n).2.1
  · exact fun q p => (augmented_row_exact P I q).2.2 p

end Balance

/-- Balance for ordinary resolutions over every associative unital ring. -/
theorem balance : balanceType.{u,v,w} := by
  intro R _ A B _ _ _ _ P I hP
  refine ⟨projectiveAugmentation P I, injectiveAugmentation P I,
    projectiveAugmentation_formula P I, injectiveAugmentation_formula P I,
    projectiveAugmentation_quasiIso P I hP, injectiveAugmentation_quasiIso P I, ?_⟩
  exact comparison_from_quasiIsomorphisms R A B P I _ _
    (projectiveAugmentation_quasiIso P I hP) (injectiveAugmentation_quasiIso P I)

/-- Same-side right modules use the opposite ring throughout. -/
theorem right_balance : right_balanceType.{u,v,w} := by
  intro R _ A B _ _ _ _ P I hP
  exact balance Rᵐᵒᵖ A B P I hP

private theorem injectiveHomMap_factor
    {A A' : Type v} [AddCommGroup A] [Module R A]
    [AddCommGroup A'] [Module R A']
    {D E : CochainComplex (ModuleCat.{w} R) ℕ}
    (f : A' →ₗ[R] A) (m : D ⟶ E) :
    injectiveHomMap f m =
      ((covariantHom A).mapHomologicalComplex (ComplexShape.up ℕ)).map m ≫
        injectiveHomMap f (𝟙 E) := by
  ext n : 1
  rfl

theorem injective_lift_independent
    {A A' : Type v} {B B' : Type w}
    [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
    [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (I : InjectiveResolution R B) (J : InjectiveResolution R B')
    (f : A' →ₗ[R] A) (g : B →ₗ[R] B')
    (m m' : I.complex ⟶ J.complex)
    (hm : CochainLift (ofInjective I) J g m)
    (hm' : CochainLift (ofInjective I) J g m') (n : ℕ) :
    homologyMap (injectiveHomMap f m) n =
      homologyMap (injectiveHomMap f m') n := by
  have h := P103.Ch10.Comparison.cochain_homology_independent R ℤ (covariantHom (R := R) A) B B'
    (ofInjective I) J g m m' n hm hm'
  have h' : homologyMap
      (((covariantHom A).mapHomologicalComplex (ComplexShape.up ℕ)).map m) n =
      homologyMap
      (((covariantHom A).mapHomologicalComplex (ComplexShape.up ℕ)).map m') n :=
    congrArg ModuleCat.Hom.hom h
  rw [injectiveHomMap_factor f m, injectiveHomMap_factor f m']
  calc
    _ = (homologyMap (injectiveHomMap f (𝟙 J.complex)) n).comp
          (homologyMap (((covariantHom A).mapHomologicalComplex (ComplexShape.up ℕ)).map m) n) :=
      P103.Ch10.Complexes.homologyMap_comp _ _ n
    _ = (homologyMap (injectiveHomMap f (𝟙 J.complex)) n).comp
          (homologyMap (((covariantHom A).mapHomologicalComplex (ComplexShape.up ℕ)).map m') n) := by rw [h']
    _ = _ := (P103.Ch10.Complexes.homologyMap_comp _ _ n).symm

theorem injective_coherent (A : Type v) [AddCommGroup A] [Module R A] (n : ℕ) :
    Nonempty (CoherentComparison
      (fun B : ModuleCat.{w} R => InjectiveResolution R B)
      (injectiveComplex R) injectiveOver
      (appliedHomology (covariantHom (R := R) A) (ComplexShape.up ℕ) n)) := by
  exact P103.Ch10.Comparison.cochain_homology_functorial R ℤ (covariantHom A) n


theorem balance_natural_extMaps
    (n : ℕ) (E : ExtMaps.{u,v,w} R n)
    {A A' : ModuleCat.{v} R} {B B' : ModuleCat.{w} R}
    (P : ProjectiveChoice R A) (Q : ProjectiveChoice R A')
    (I : InjectiveResolution R B) (J : InjectiveResolution R B')
    (f : A' ⟶ A) (g : B ⟶ B') (m : I.complex ⟶ J.complex)
    (hm : CochainLift (ofInjective I) J g.hom m)
    (α : homComplex P.val.complex B ⟶ homTotal P.val.complex I.complex)
    (β : injectiveHom A I.complex ⟶ homTotal P.val.complex I.complex)
    (α' : homComplex Q.val.complex B' ⟶ homTotal Q.val.complex J.complex)
    (β' : injectiveHom A' J.complex ⟶ homTotal Q.val.complex J.complex)
    (hα : IsProjectiveAugmentation P.val I α)
    (hβ : IsInjectiveAugmentation P.val I β)
    (hα' : IsProjectiveAugmentation Q.val J α')
    (hβ' : IsInjectiveAugmentation Q.val J β')
    (hqα : QuasiIsomorphism α) (hqα' : QuasiIsomorphism α')
    (e : Homology (injectiveHom A I.complex) n ≃ₗ[ℤ] ExtWith P.val B n)
    (e' : Homology (injectiveHom A' J.complex) n ≃ₗ[ℤ] ExtWith Q.val B' n)
    (he : (homologyMap α n).comp e.toLinearMap = homologyMap β n)
    (he' : (homologyMap α' n).comp e'.toLinearMap = homologyMap β' n) :
    e'.toLinearMap.comp (homologyMap (injectiveHomMap f.hom m) n) =
      (E.map P Q f g).comp e.toLinearMap := by
  obtain ⟨l, hl⟩ := P103.Ch10.Comparison.chain_exists R A' A Q.val P.val Q.property f.hom
  rw [E.formula P Q f g l hl]
  exact balance_natural R A A' B B' P.val Q.val I J P.property Q.property
    f.hom g.hom l m hl hm α β α' β' hα hβ hα' hβ' hqα hqα' n e e' he he'


end
end P103.Ch11.ExtBalance
