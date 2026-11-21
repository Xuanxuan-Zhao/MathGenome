import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.RingTheory.Regular.Category
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Linear
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.ReesChangeOfRings

/-! Change of rings by a regular element and a regular sequence,
paper.tex:3170–3206, DP-14. The comparison is natural in both module arguments.
No finiteness, Noetherian or local hypotheses are used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped Pointwise ModuleCat.Algebra
universe u v
namespace AdvCommAlg.Depth
variable {R : Type u} [CommRing R]

/-- A scalar killing the source and injective on the target kills every map. -/
theorem linearMap_eq_zero_of_regular {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (x : R) (hM : IsSMulRegular M x) (hN : ∀ n : N, x • n = 0)
    (f : N →ₗ[R] M) : f = 0 := by
  ext n
  apply hM
  change x • f n = x • (0 : M)
  rw [← f.map_smul, hN, map_zero, smul_zero]

/-- Hom vanishing only needs regularity on M, not on R. -/
theorem hom_subsingleton_of_regular (M N : ModuleCat.{v} R)
    (x : R) (hM : IsSMulRegular M x) (hN : ∀ n : N, x • n = 0) :
    Subsingleton (N ⟶ M) := by
  refine ⟨fun f g => ?_⟩
  apply ModuleCat.hom_ext
  exact (linearMap_eq_zero_of_regular x hM hN f.hom).trans
    (linearMap_eq_zero_of_regular x hM hN g.hom).symm

variable [Small.{v} R]

/-- Degree zero of Ext is the ordinary Hom group. -/
theorem ext_zero_subsingleton_of_regular (M N : ModuleCat.{v} R)
    (x : R) (hM : IsSMulRegular M x) (hN : ∀ n : N, x • n = 0) :
    Subsingleton (Ext N M 0) := by
  have := hom_subsingleton_of_regular M N x hM hN
  exact Ext.addEquiv₀.subsingleton

/-- Lower-degree vanishing for a weakly regular sequence annihilating N.
This is stronger than the vanishing part of DP-14: regularity on R and
properness of the sequence on M are unnecessary. -/
theorem ext_subsingleton_below_length (M N : ModuleCat.{v} R)
    (xs : List R) (hM : RingTheory.Sequence.IsWeaklyRegular M xs)
    (hN : ∀ x ∈ xs, ∀ n : N, x • n = 0) :
    ∀ i : ℕ, i < xs.length → Subsingleton (Ext N M i) := by
  induction xs generalizing M with
  | nil => simp
  | cons x xs ih =>
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hM
    intro i hi
    cases i with
    | zero =>
      exact ext_zero_subsingleton_of_regular M N x hM.1 (hN x List.mem_cons_self)
    | succ i =>
      have hz : Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop x M)) i) :=
        ih _ hM.2 (fun a ha => hN a (List.mem_cons_of_mem x ha)) i
          (Nat.lt_of_succ_lt_succ hi)
      have hm : Mono (AddCommGrpCat.ofHom
          ((Ext.mk₀ (M.smulShortComplex x).f).postcomp N (add_zero (i + 1)))) :=
        (Ext.covariant_sequence_exact₁' N hM.1.smulShortComplex_shortExact i (i + 1) rfl).mono_g
          ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr hz).eq_zero_of_src _)
      have hx : x ∈ Module.annihilator R N := by
        rw [Module.mem_annihilator]
        exact hN x List.mem_cons_self
      have hzero : AddCommGrpCat.ofHom
          ((Ext.mk₀ (M.smulShortComplex x).f).postcomp N (add_zero (i + 1))) = 0 := by
        rw [ModuleCat.smulShortComplex_f_eq_smul_id]
        exact Ext.postcomp_smul_id_eq_zero_of_mem_annihilator hx (i + 1)
      exact AddCommGrpCat.subsingleton_of_isZero (IsZero.of_mono_eq_zero _ hzero)

/-- The degree-zero connecting homomorphism for 0 → M → M → M/xM → 0. -/
def regularConnecting (M N : ModuleCat.{v} R) (x : R) (hM : IsSMulRegular M x) :
    Ext N (ModuleCat.of R (QuotSMulTop x M)) 0 →ₗ[R] Ext N M 1 :=
  Ext.postcompOfLinear hM.smulShortComplex_shortExact.extClass R N (zero_add 1)

/-- The first connecting homomorphism is an isomorphism if x annihilates N. -/
theorem regularConnecting_bijective (M N : ModuleCat.{v} R) (x : R)
    (hM : IsSMulRegular M x) (hN : ∀ n : N, x • n = 0) :
    Function.Bijective (regularConnecting M N x hM) := by
  have hzero : Subsingleton (Ext N M 0) := ext_zero_subsingleton_of_regular M N x hM hN
  have hx : x ∈ Module.annihilator R N := by
    rw [Module.mem_annihilator]
    exact hN
  constructor
  · intro a b hab
    have hd : regularConnecting M N x hM (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₃ N
      hM.smulShortComplex_shortExact (a - b) (zero_add 1) hd
    have hc0 : c = 0 := hzero.elim _ _
    apply sub_eq_zero.mp
    simpa [hc0] using hc.symm
  · intro a
    apply Ext.covariant_sequence_exact₁ N hM.smulShortComplex_shortExact a _ (zero_add 1)
    have hz := Ext.postcomp_smul_id_eq_zero_of_mem_annihilator (M := M) hx 1
    have hz' := congrArg (fun f => f a) hz
    change a.comp (Ext.mk₀ (x • 𝟙 M)) (add_zero 1) = 0 at hz'
    simpa only [ModuleCat.smulShortComplex_f_eq_smul_id] using hz'

/-- Naturality of the degree-zero connecting homomorphism in the source. -/
theorem regularConnecting_naturality_source (M : ModuleCat.{v} R)
    {N N' : ModuleCat.{v} R} (f : N ⟶ N') (x : R) (hM : IsSMulRegular M x)
    (a : Ext N' (ModuleCat.of R (QuotSMulTop x M)) 0) :
    regularConnecting M N x hM ((Ext.mk₀ f).comp a (zero_add 0)) =
      (Ext.mk₀ f).comp (regularConnecting M N' x hM a) (zero_add 1) := by
  exact Ext.comp_assoc (Ext.mk₀ f) a hM.smulShortComplex_shortExact.extClass
    (zero_add 0) (zero_add 1) (zero_add 1)

/-- A coefficient map induces a map of the scalar-multiplication short complexes. -/
def smulShortComplexMap {M M' : ModuleCat.{v} R} (f : M ⟶ M') (x : R) :
    M.smulShortComplex x ⟶ M'.smulShortComplex x where
  τ₁ := f
  τ₂ := f
  τ₃ := ModuleCat.ofHom (QuotSMulTop.map x f.hom)
  comm₁₂ := by ext m; exact (f.hom.map_smul x m).symm
  comm₂₃ := by ext m; rfl

/-- Naturality of the connecting map in the coefficient module. -/
theorem regularConnecting_naturality_target {M M' : ModuleCat.{v} R}
    (f : M ⟶ M') (N : ModuleCat.{v} R) (x : R)
    (hM : IsSMulRegular M x) (hM' : IsSMulRegular M' x)
    (a : Ext N (ModuleCat.of R (QuotSMulTop x M)) 0) :
    regularConnecting M' N x hM'
        (a.comp (Ext.mk₀ (ModuleCat.ofHom (QuotSMulTop.map x f.hom))) (add_zero 0)) =
      (regularConnecting M N x hM a).comp (Ext.mk₀ f) (add_zero 1) := by
  change (a.comp (Ext.mk₀ (smulShortComplexMap f x).τ₃) (add_zero 0)).comp
      hM'.smulShortComplex_shortExact.extClass (zero_add 1) =
    (a.comp hM.smulShortComplex_shortExact.extClass (zero_add 1)).comp
      (Ext.mk₀ (smulShortComplexMap f x).τ₁) (add_zero 1)
  rw [Ext.comp_assoc_of_third_deg_zero,
    ShortComplex.ShortExact.extClass_naturality hM.smulShortComplex_shortExact
      hM'.smulShortComplex_shortExact (smulShortComplexMap f x)]
  exact Ext.comp_assoc_of_second_deg_zero a _ _ (zero_add 1)

/-- The j=0 comparison, expressed as Hom over R for the moment.
The formula is the inverse of the canonical connecting homomorphism. -/
def extOneEquivHomQuotient (M N : ModuleCat.{v} R) (x : R)
    (hM : IsSMulRegular M x) (hN : ∀ n : N, x • n = 0) :
    Ext N M 1 ≃ₗ[R] (N ⟶ ModuleCat.of R (QuotSMulTop x M)) :=
  (LinearEquiv.ofBijective (regularConnecting M N x hM)
    (regularConnecting_bijective M N x hM hN)).symm.trans Ext.linearEquiv₀

omit [Small.{v} R] in
/-- Identifying the scalar action of a quotient-ring representative. -/
theorem quotient_smul (I : Ideal R) (M : ModuleCat.{v} R) (r : R)
    (q : M ⧸ (I • ⊤ : Submodule R M)) : Ideal.Quotient.mk I r • q = r • q := by
  induction q using Submodule.Quotient.induction_on with
  | _ m => rfl

/-- R-linear maps between modules annihilated by I are R/I-linear.
The target is the canonical quotient, retaining its original R-action. -/
def quotientHomEquiv (I : Ideal R) (M : ModuleCat.{v} R)
    (N : ModuleCat.{v} (R ⧸ I)) :
    (((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N) ⟶
      ModuleCat.of R (M ⧸ (I • ⊤ : Submodule R M))) ≃ₗ[R]
      (N ⟶ Rees.quotientModule I M) where
  toFun f := ModuleCat.ofHom
    { toFun := f.hom
      map_add' := f.hom.map_add
      map_smul' := by
        intro a n
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        change f.hom (r • n) = Ideal.Quotient.mk I r • f.hom n
        rw [f.hom.map_smul, quotient_smul] }
  invFun f := ModuleCat.ofHom
    { toFun := f.hom
      map_add' := f.hom.map_add
      map_smul' := by
        intro r n
        change f.hom (Ideal.Quotient.mk I r • n) = r • f.hom n
        rw [f.hom.map_smul, quotient_smul] }
  left_inv f := by ext n; rfl
  right_inv f := by ext n; rfl
  map_add' f g := by ext n; rfl
  map_smul' r f := by
    ext n
    exact (quotient_smul I M r (f.hom n)).symm

/-- Converting M/xM into the quotient by the principal ideal (x). -/
def principalQuotientEquiv (M : ModuleCat.{v} R) (x : R) :
    QuotSMulTop x M ≃ₗ[R] (M ⧸ (Ideal.span {x} • ⊤ : Submodule R M)) :=
  Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul x ⊤).symm

/-- The j=0 Ext comparison over the quotient ring, under only x-regularity on M. -/
def reesExtOneEquiv (M : ModuleCat.{v} R) (x : R) (hM : IsSMulRegular M x)
    (N : ModuleCat.{v} (R ⧸ Ideal.span {x})) :
    Ext ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj N) M 1 ≃ₗ[R]
      Ext N (Rees.quotientModule (Ideal.span {x}) M) 0 := by
  let NR := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj N
  have hN : ∀ n : NR, x • n = 0 := by
    intro n
    change Ideal.Quotient.mk (Ideal.span {x}) x • n = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton x)), zero_smul]
  exact (extOneEquivHomQuotient M NR x hM hN).trans
    (ModuleCat.homLinearEquiv.trans
      ((LinearEquiv.arrowCongr (LinearEquiv.refl R NR) (principalQuotientEquiv M x)).trans
        (ModuleCat.homLinearEquiv.symm.trans
          ((quotientHomEquiv (Ideal.span {x}) M N).trans Ext.linearEquiv₀.symm))))

omit [Small.{v} R] in
/-- Restriction of scalars from R/I makes every element of I act by zero. -/
theorem ideal_smul_restrictScalars_eq_zero (I : Ideal R)
    (N : ModuleCat.{v} (R ⧸ I)) (r : R) (hr : r ∈ I)
    (n : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj N) : r • n = 0 := by
  change Ideal.Quotient.mk I r • n = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]

/-- The Hom assertion of DP-14 for the actual quotient-ring action. -/
theorem rees_hom_vanishing :
    Specs.AdvCommAlg.Depth.ReesChangeOfRings.homVanishing.{u,v} := by
  intro R _ x M hM N
  exact hom_subsingleton_of_regular M _ x hM
    (ideal_smul_restrictScalars_eq_zero _ N x (Ideal.subset_span (Set.mem_singleton x)))

/-- The j=0 comparison of DP-14 for the actual R/(x)-module quotient. -/
theorem rees_ext_one :
    Specs.AdvCommAlg.Depth.ReesChangeOfRings.singleDegreeZero.{u,v} := by
  intro R _ _ x M hM N
  exact ⟨reesExtOneEquiv M x hM N⟩

/-- Vanishing in all degrees below the length of the sequence. -/
theorem regularSequence_vanishing :
    Specs.AdvCommAlg.Depth.ReesChangeOfRings.regularSequenceVanishing.{u,v} := by
  intro R _ _ xs _ M hM N
  exact ext_subsingleton_below_length M _ xs hM.toIsWeaklyRegular
    (fun x hx => ideal_smul_restrictScalars_eq_zero _ N x (Ideal.subset_span hx))

/-- Multiplication by a ring nonzerodivisor is surjective on an injective module.
The extension property is applied to the injection `R --x→ R`. -/
theorem smul_surjective_of_injective (E : ModuleCat.{v} R) [Injective E]
    (x : R) (hx : IsSMulRegular R x) : Function.Surjective (fun e : E => x • e) := by
  let : Module.Injective R E := Module.injective_module_of_injective_object R E
  intro e
  obtain ⟨g, hg⟩ := Module.Injective.extension_property R E R R
    (LinearMap.lsmul R R x) hx (LinearMap.toSpanSingleton R E e)
  refine ⟨g 1, ?_⟩
  have h := DFunLike.congr_fun hg 1
  simpa using (g.map_smul x (1 : R)).symm.trans h

/-- The elements killed by x, carrying the canonical R/(x)-action.
This has the same universe as M, even when R only satisfies `Small R`. -/
abbrev torsionModule (x : R) (M : ModuleCat.{v} R) :
    ModuleCat.{v} (R ⧸ Ideal.span {x}) :=
  ModuleCat.of _ (Submodule.torsionBy R M x)

/-- The map on x-torsion induced by a coefficient map. -/
def torsionMap (x : R) {M M' : ModuleCat.{v} R} (f : M ⟶ M') :
    torsionModule x M ⟶ torsionModule x M' :=
  ModuleCat.ofHom
    { toFun := fun m => ⟨f.hom m, by
        change x • f.hom m = 0
        rw [← f.hom.map_smul, (Submodule.mem_torsionBy_iff x _).mp m.property, map_zero]⟩
      map_add' := by intros; apply Subtype.ext; exact f.hom.map_add _ _
      map_smul' := by
        intro a m
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        apply Subtype.ext
        exact f.hom.map_smul r m }

/-- The torsion construction is functorial. -/
def torsionFunctor (x : R) : ModuleCat.{v} R ⥤ ModuleCat.{v} (R ⧸ Ideal.span {x}) where
  obj := torsionModule x
  map := torsionMap x

instance (x : R) : (torsionFunctor (R := R) x).Additive where

/-- Evaluation into the x-torsion identifies the two Hom groups in the
restriction–Hom adjunction. Its inverse is the ordinary submodule inclusion. -/
def torsionHomEquiv (x : R) (M : ModuleCat.{v} R)
    (N : ModuleCat.{v} (R ⧸ Ideal.span {x})) :
    (((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj N) ⟶ M) ≃ₗ[R]
      (N ⟶ torsionModule x M) where
  toFun f := ModuleCat.ofHom
    { toFun := fun n => ⟨f.hom n, by
        change x • f.hom n = 0
        rw [← f.hom.map_smul, ideal_smul_restrictScalars_eq_zero _ N x
          (Ideal.subset_span (Set.mem_singleton x)), map_zero]⟩
      map_add' := by intros; apply Subtype.ext; exact f.hom.map_add _ _
      map_smul' := by
        intro a n
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        apply Subtype.ext
        exact f.hom.map_smul r n }
  invFun f := ModuleCat.ofHom
    { toFun := fun n => (f.hom n).val
      map_add' := by intros; exact congrArg Subtype.val (f.hom.map_add _ _)
      map_smul' := by
        intro r n
        exact congrArg Subtype.val (f.hom.map_smul (Ideal.Quotient.mk _ r) n) }
  left_inv f := by ext n; rfl
  right_inv f := by ext n; rfl
  map_add' f g := by ext n; rfl
  map_smul' r f := by ext n; rfl

omit [Small.{v} R] in
/-- Naturality of the restriction–torsion Hom comparison in the source. -/
theorem torsionHomEquiv_naturality_source (x : R) (M : ModuleCat.{v} R)
    {N N' : ModuleCat.{v} (R ⧸ Ideal.span {x})} (g : N ⟶ N')
    (f : ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj N') ⟶ M) :
    torsionHomEquiv x M N
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).map g ≫ f) =
      g ≫ torsionHomEquiv x M N' f := by
  ext n
  rfl

omit [Small.{v} R] in
/-- Naturality of the restriction–torsion Hom comparison in the coefficient. -/
theorem torsionHomEquiv_naturality_target (x : R) {M M' : ModuleCat.{v} R}
    (g : M ⟶ M') (N : ModuleCat.{v} (R ⧸ Ideal.span {x}))
    (f : ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj N) ⟶ M) :
    torsionHomEquiv x M' N (f ≫ g) = torsionHomEquiv x M N f ≫ torsionMap x g := by
  ext n
  rfl

omit [Small.{v} R] in
/-- The x-torsion of an injective R-module is injective over R/(x).
No ring regularity or finiteness is required for this adjunction argument. -/
theorem torsionModule_injective (x : R) (E : ModuleCat.{v} R) [Injective E] :
    Injective (torsionModule x E) where
  factors {N N'} g f hf := by
    let res := ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))
    have : Mono (res.map f) := by dsimp [res]; infer_instance
    obtain ⟨h, hh⟩ := Injective.factors ((torsionHomEquiv x E N).symm g) (res.map f)
    refine ⟨torsionHomEquiv x E N' h, ?_⟩
    rw [← torsionHomEquiv_naturality_source, hh]
    exact (torsionHomEquiv x E N).apply_symm_apply g

/-- Applying x-torsion term by term to a cochain complex. -/
abbrev torsionComplex (x : R) (K : CochainComplex (ModuleCat.{v} R) ℕ) :
    CochainComplex (ModuleCat.{v} (R ⧸ Ideal.span {x})) ℕ :=
  ((torsionFunctor x).mapHomologicalComplex _).obj K

omit [Small.{v} R] in
/-- All terms of the torsion complex of an injective resolution are injective. -/
theorem torsionComplex_injective (x : R) (M : ModuleCat.{v} R)
    (E : InjectiveResolution M) (n : ℕ) :
    Injective ((torsionComplex x E.cocomplex).X n) :=
  torsionModule_injective x _

omit [Small.{v} R] in
/-- If x is regular on M, the first differential of its torsion complex is mono. -/
theorem torsionComplex_mono_d_zero_one (x : R) (M : ModuleCat.{v} R)
    (hM : IsSMulRegular M x) (E : InjectiveResolution M) :
    Mono ((torsionComplex x E.cocomplex).d 0 1) := by
  rw [ModuleCat.mono_iff_injective]
  intro a b hab
  apply sub_eq_zero.mp
  apply Subtype.ext
  let t := a - b
  have ht : (E.cocomplex.d 0 1).hom t.val = 0 := by
    change (E.cocomplex.d 0 1).hom (a.val - b.val) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val hab)
  have hex := E.exact₀
  rw [ShortComplex.moduleCat_exact_iff] at hex
  change ∀ t : E.cocomplex.X 0, (E.cocomplex.d 0 1).hom t = 0 →
    ∃ m : M, (E.ι.f 0).hom m = t at hex
  obtain ⟨m, hm⟩ := hex t.val ht
  have hm0 : x • m = 0 := by
    have hi := (ModuleCat.mono_iff_injective (E.ι.f 0)).mp inferInstance
    apply hi
    rw [(E.ι.f 0).hom.map_smul, hm, map_zero]
    exact (Submodule.mem_torsionBy_iff x _).mp t.property
  have hmzero : m = 0 := hM (hm0.trans (smul_zero x).symm)
  change t.val = 0
  rw [← hm, hmzero, map_zero]

/-- The torsion complex of an injective resolution is exact in degrees at least
 two. The proof uses the surjectivity of x on the injective terms, hence only
 regularity on R (and no regularity on M). -/
theorem torsionComplex_exactAt_add_two (x : R) (hx : IsSMulRegular R x)
    (M : ModuleCat.{v} R) (E : InjectiveResolution M) (n : ℕ) :
    (torsionComplex x E.cocomplex).ExactAt (n + 2) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1) (n + 2) (n + 3) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro t ht
  have hex := E.exact_succ (n + 1)
  rw [ShortComplex.moduleCat_exact_iff] at hex
  change ∀ t : E.cocomplex.X (n + 2),
    (E.cocomplex.d (n + 2) (n + 3)).hom t = 0 →
      ∃ s : E.cocomplex.X (n + 1), (E.cocomplex.d (n + 1) (n + 2)).hom s = t at hex
  obtain ⟨s, hs⟩ := hex t.val (congrArg Subtype.val ht)
  have hsx : (E.cocomplex.d (n + 1) (n + 2)).hom (x • s) = 0 := by
    rw [map_smul, hs]
    exact (Submodule.mem_torsionBy_iff x _).mp t.property
  have hex' := E.exact_succ n
  rw [ShortComplex.moduleCat_exact_iff] at hex'
  change ∀ s : E.cocomplex.X (n + 1),
    (E.cocomplex.d (n + 1) (n + 2)).hom s = 0 →
      ∃ r : E.cocomplex.X n, (E.cocomplex.d n (n + 1)).hom r = s at hex'
  obtain ⟨r, hr⟩ := hex' (x • s) hsx
  obtain ⟨r', hr'⟩ := smul_surjective_of_injective (E.cocomplex.X n) x hx r
  change x • r' = r at hr'
  let s' := s - (E.cocomplex.d n (n + 1)).hom r'
  have hs' : x • s' = 0 := by
    dsimp [s']
    rw [smul_sub, ← map_smul, hr', hr, sub_self]
  refine ⟨⟨s', hs'⟩, ?_⟩
  apply Subtype.ext
  change (E.cocomplex.d (n + 1) (n + 2)).hom s' = t.val
  dsimp [s']
  rw [map_sub, hs]
  have hd := congrArg (fun f => f.hom r') (E.cocomplex.d_comp_d n (n + 1) (n + 2))
  change (E.cocomplex.d (n + 1) (n + 2)).hom
    ((E.cocomplex.d n (n + 1)).hom r') = 0 at hd
  rw [hd, sub_zero]

end AdvCommAlg.Depth

namespace AdvCommAlg.Depth.InjectiveTail
universe w w'
variable {C : Type w} [Category.{w'} C] [Abelian C]

/-- The first cokernel followed by the remaining terms of a cochain complex. -/
def term (K : CochainComplex C ℕ) : ℕ → C
  | 0 => K.opcycles 1
  | n + 1 => K.X (n + 2)

/-- The induced first differential, followed by the original differentials. -/
def differential (K : CochainComplex C ℕ) : ∀ n, term K n ⟶ term K (n + 1)
  | 0 => K.fromOpcycles 1 2
  | n + 1 => K.d (n + 2) (n + 3)

/-- Truncation beginning with `coker(d⁰)`, reindexed in degree zero. -/
def complex (K : CochainComplex C ℕ) : CochainComplex C ℕ :=
  CochainComplex.of (term K) (differential K) (by
    intro n
    cases n with
    | zero => exact K.fromOpcycles_d 1 2 3
    | succ n => exact K.d_comp_d (n + 2) (n + 3) (n + 4))

/-- Injectivity of the cokernel term follows by splitting the first injection. -/
theorem injective_first (K : CochainComplex C ℕ)
    [Injective (K.X 0)] [Injective (K.X 1)] [Mono (K.d 0 1)] :
    Injective (K.opcycles 1) := by
  let S := ShortComplex.mk (K.d 0 1) (K.pOpcycles 1) (K.d_pOpcycles 0 1)
  have hS : S.ShortExact :=
    { exact := S.exact_of_g_is_cokernel (K.opcyclesIsCokernel 0 1 (by simp)) }
  exact Retract.injective
    { i := _, r := _, retract := hS.splittingOfInjective.s_g }

/-- All the terms of the truncated complex are injective. -/
theorem injective_term (K : CochainComplex C ℕ)
    (hK : ∀ n, Injective (K.X n)) [Mono (K.d 0 1)] (n : ℕ) :
    Injective ((complex K).X n) := by
  let := hK 0
  let := hK 1
  cases n with
  | zero => exact injective_first K
  | succ n => exact hK (n + 2)

/-- Exactness of the original complex from degree two becomes positive-degree
exactness of the tail. -/
theorem exactAt_succ (K : CochainComplex C ℕ)
    (hK : ∀ n, K.ExactAt (n + 2)) (n : ℕ) :
    (complex K).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  cases n with
  | zero =>
    let S := ShortComplex.mk (K.fromOpcycles 1 2) (K.d 2 3) (K.fromOpcycles_d 1 2 3)
    let φ : K.sc' 1 2 3 ⟶ S :=
      { τ₁ := K.pOpcycles 1
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [S]
        comm₂₃ := by simp [S] }
    have hex : (K.sc' 1 2 3).Exact :=
      (K.exactAt_iff' 1 2 3 (by simp) (by simp)).mp (hK 0)
    have : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hex
    simpa [S, complex, CochainComplex.of.d, term, differential, HomologicalComplex.sc',
      HomologicalComplex.shortComplexFunctor'] using this
  | succ n =>
    have hex := (K.exactAt_iff' (n + 2) (n + 3) (n + 4) (by simp) (by simp)).mp (hK (n + 1))
    simpa [complex, CochainComplex.of.d, term, differential, HomologicalComplex.sc',
      HomologicalComplex.shortComplexFunctor', Nat.add_assoc] using hex

/-- The canonical augmentation of the tail by the first cohomology. -/
def augmentation (K : CochainComplex C ℕ) :
    (CochainComplex.single₀ C).obj (K.homology 1) ⟶ complex K :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨K.homologyι 1, by simp [complex, CochainComplex.of.d, differential]⟩

/-- The first cohomology is the kernel of the first induced differential. -/
theorem augmentation_exact (K : CochainComplex C ℕ) :
    (ShortComplex.mk (K.homologyι 1) ((complex K).d 0 1)
      (by simp [complex, CochainComplex.of.d, differential])).Exact := by
  have hd : (complex K).d 0 1 = K.fromOpcycles 1 2 := by
    simp [complex, CochainComplex.of.d, differential]
  simp only [hd]
  exact ShortComplex.exact_of_f_is_kernel _ (K.homologyIsKernel 1 2 (by simp))

/-- The tail is an injective resolution of the first cohomology. -/
def resolution (K : CochainComplex C ℕ) (hI : ∀ n, Injective (K.X n))
    [Mono (K.d 0 1)] (hK : ∀ n, K.ExactAt (n + 2)) :
    InjectiveResolution (K.homology 1) where
  cocomplex := complex K
  injective := injective_term K hI
  ι := augmentation K
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).mpr
          ⟨augmentation_exact K, inferInstance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [augmentation]) (by simp)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt]
      · exact exactAt_succ K hK n
      · exact CochainComplex.exactAt_succ_single_obj _ _⟩

end AdvCommAlg.Depth.InjectiveTail

namespace AdvCommAlg.Depth
variable {R : Type u} [CommRing R] [Small.{v} R]

/-- The underlying R-complex of the quotient-ring torsion complex. -/
abbrev restrictedTorsionComplex (x : R) (K : CochainComplex (ModuleCat.{v} R) ℕ) :
    CochainComplex (ModuleCat.{v} R) ℕ :=
  ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).mapHomologicalComplex _).obj
    (torsionComplex x K)

/-- Inclusion of the elements killed by x, in every degree. -/
def torsionComplexInclusion (x : R) (K : CochainComplex (ModuleCat.{v} R) ℕ) :
    restrictedTorsionComplex x K ⟶ K where
  f n := ModuleCat.ofHom
    { toFun := fun t => t.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  comm' _ _ _ := by ext t; rfl

/-- The kernel sequence for scalar multiplication on a complex. -/
def torsionShortComplex (x : R) (K : CochainComplex (ModuleCat.{v} R) ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{v} R) ℕ) :=
  ShortComplex.mk (torsionComplexInclusion x K) (x • 𝟙 K) (by
    ext n t
    exact (Submodule.mem_torsionBy_iff x _).mp t.property)

/-- Regularity on R makes this kernel sequence of injective complexes short exact. -/
theorem torsionShortComplex_shortExact (x : R) (hx : IsSMulRegular R x)
    (M : ModuleCat.{v} R) (E : InjectiveResolution M) :
    (torsionShortComplex x E.cocomplex).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro t
    constructor
    · intro ht
      exact ⟨⟨t, ht⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact (Submodule.mem_torsionBy_iff x _).mp s.property
  · intro a b hab
    exact Subtype.ext hab
  · exact smul_surjective_of_injective (E.cocomplex.X n) x hx

/-- The zeroth cohomology of an injective resolution is its resolved module. -/
def injectiveResolutionHomologyZeroIso (M : ModuleCat.{v} R) (E : InjectiveResolution M) :
    M ≅ E.cocomplex.homology 0 :=
  (HomologicalComplex.singleObjHomologySelfIso _ _ _).symm ≪≫
    isoOfQuasiIsoAt E.ι 0

/-- The degree-zero connecting map for the kernel complex of x. -/
def torsionCohomologyConnecting (x : R) (hx : IsSMulRegular R x)
    (M : ModuleCat.{v} R) (E : InjectiveResolution M) :
    M ⟶ (restrictedTorsionComplex x E.cocomplex).homology 1 :=
  (injectiveResolutionHomologyZeroIso M E).hom ≫
    (torsionShortComplex_shortExact x hx M E).δ 0 1 (by simp)

/-- The connecting map is surjective, since the resolution has zero H¹. -/
theorem torsionCohomologyConnecting_surjective (x : R) (hx : IsSMulRegular R x)
    (M : ModuleCat.{v} R) (E : InjectiveResolution M) :
    Function.Surjective (torsionCohomologyConnecting x hx M E).hom := by
  let hS := torsionShortComplex_shortExact x hx M E
  have hδ : Epi (hS.δ 0 1 (by simp)) :=
    (hS.homology_exact₁ 0 1 (by simp)).epi_f
      (((E.cocomplex.exactAt_iff_isZero_homology 1).mp (E.cocomplex_exactAt_succ 0)).eq_of_tgt _ _)
  change Function.Surjective
    ((injectiveResolutionHomologyZeroIso M E).hom ≫ hS.δ 0 1 (by simp)).hom
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

omit [Small.{v} R] in
/-- Scalar multiplication induces scalar multiplication on cohomology. -/
theorem homologyMap_smul_id (K : CochainComplex (ModuleCat.{v} R) ℕ) (x : R) (n : ℕ) :
    HomologicalComplex.homologyMap (x • 𝟙 K) n = x • 𝟙 (K.homology n) := by
  change ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (x • 𝟙 K)) = _
  have h : (HomologicalComplex.shortComplexFunctor _ _ n).map (x • 𝟙 K) =
      x • 𝟙 (K.sc n) := by ext <;> rfl
  rw [h, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

/-- The kernel of the connecting map is exactly xM. -/
theorem torsionCohomologyConnecting_ker (x : R) (hx : IsSMulRegular R x)
    (M : ModuleCat.{v} R) (E : InjectiveResolution M) :
    (torsionCohomologyConnecting x hx M E).hom.ker = x • (⊤ : Submodule R M) := by
  let hS := torsionShortComplex_shortExact x hx M E
  let e := injectiveResolutionHomologyZeroIso M E
  have hc : (x • 𝟙 M) ≫ e.hom =
      e.hom ≫ HomologicalComplex.homologyMap (torsionShortComplex x E.cocomplex).g 0 := by
    change (x • 𝟙 M) ≫ e.hom = e.hom ≫ HomologicalComplex.homologyMap (x • 𝟙 E.cocomplex) 0
    rw [homologyMap_smul_id]
    simp
  have hz : (x • 𝟙 M) ≫ torsionCohomologyConnecting x hx M E = 0 := by
    change (x • 𝟙 M) ≫ (e.hom ≫ hS.δ 0 1 (by simp)) = 0
    rw [← Category.assoc, hc, Category.assoc, hS.comp_δ, comp_zero]
  let S := ShortComplex.mk (x • 𝟙 M) (torsionCohomologyConnecting x hx M E) hz
  have he : S ≅ ShortComplex.mk _ _ (hS.comp_δ 0 1 (by simp)) :=
    ShortComplex.isoMk e e (Iso.refl _) hc.symm (by simp [S, torsionCohomologyConnecting, e])
  have hex := ShortComplex.exact_of_iso he.symm (hS.homology_exact₃ 0 1 (by simp))
  have hker := hex.moduleCat_range_eq_ker
  change (x • (𝟙 M)).hom.range = (torsionCohomologyConnecting x hx M E).hom.ker at hker
  rw [← hker]
  ext m
  simp only [LinearMap.mem_range, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
    true_and]
  rfl

/-- The first cohomology of the kernel complex is the canonical quotient M/xM,
 as an R-module. -/
def torsionCohomologyOneEquiv (x : R) (hx : IsSMulRegular R x)
    (M : ModuleCat.{v} R) (E : InjectiveResolution M) :
    QuotSMulTop x M ≃ₗ[R] (restrictedTorsionComplex x E.cocomplex).homology 1 :=
  (Submodule.quotEquivOfEq _ _ (torsionCohomologyConnecting_ker x hx M E).symm).trans
    ((torsionCohomologyConnecting x hx M E).hom.quotKerEquivOfSurjective
      (torsionCohomologyConnecting_surjective x hx M E))

end AdvCommAlg.Depth

namespace AdvCommAlg.Depth
variable {R : Type u} [CommRing R] [Small.{v} R]

/-- The cohomology identification respects the actual quotient-ring scalar action. -/
def torsionCohomologyOneQuotientEquiv (x : R) (hx : IsSMulRegular R x)
    (M : ModuleCat.{v} R) (E : InjectiveResolution M) :
    Rees.quotientModule (Ideal.span {x}) M ≃ₗ[R ⧸ Ideal.span {x}]
      (torsionComplex x E.cocomplex).homology 1 := by
  let res := ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))
  let C := torsionComplex x E.cocomplex
  let e₀ : QuotSMulTop x M ≃ₗ[R] res.obj (C.homology 1) :=
    (torsionCohomologyOneEquiv x hx M E).trans
      (((C.sc 1).mapHomologyIso res).toLinearEquiv)
  let e : (M ⧸ (Ideal.span {x} • ⊤ : Submodule R M)) ≃ₗ[R] res.obj (C.homology 1) :=
    (principalQuotientEquiv M x).symm.trans e₀
  exact
    { toEquiv := e.toEquiv
      map_add' := e.map_add
      map_smul' := by
        intro a m
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        change e (Ideal.Quotient.mk (Ideal.span {x}) r • m) =
          Ideal.Quotient.mk (Ideal.span {x}) r • e m
        rw [quotient_smul, e.map_smul]
        rfl }

/-- The tail of the torsion complex resolves its first cohomology over R/(x). -/
def torsionTailResolution (x : R) (hx : IsSMulRegular R x) (M : ModuleCat.{v} R)
    (hM : IsSMulRegular M x) (E : InjectiveResolution M) :
    InjectiveResolution ((torsionComplex x E.cocomplex).homology 1) := by
  letI := torsionComplex_mono_d_zero_one x M hM E
  exact InjectiveTail.resolution _ (torsionComplex_injective x M E)
    (torsionComplex_exactAt_add_two x hx M E)

/-- An explicit injective resolution of M/xM over R/(x), obtained by deleting
 the first contractible pair from the torsion complex of an R-injective resolution. -/
def quotientInjectiveResolution (x : R) (hx : IsSMulRegular R x) (M : ModuleCat.{v} R)
    (hM : IsSMulRegular M x) (E : InjectiveResolution M) :
    InjectiveResolution (Rees.quotientModule (Ideal.span {x}) M) := by
  let T := torsionTailResolution x hx M hM E
  let e := (torsionCohomologyOneQuotientEquiv x hx M E).toModuleIso
  exact
    { T with
      ι := (CochainComplex.single₀ _).map e.hom ≫ T.ι
      quasiIso := by infer_instance }

end AdvCommAlg.Depth

namespace AdvCommAlg.Depth
variable {R : Type u} [CommRing R] [Small.{v} R]

/-- Scalar quotient map on small copies of the two coefficient rings. -/
def smallQuotientMap (x : R) : Shrink.{v} R →ₗ[R] Shrink.{v} (R ⧸ Ideal.span {x}) :=
  (Shrink.linearEquiv R (R ⧸ Ideal.span {x})).symm.toLinearMap.comp
    (((Ideal.Quotient.mkₐ R (Ideal.span {x})).toLinearMap).comp (Shrink.linearEquiv R R).toLinearMap)

theorem smallQuotientMap_surjective (x : R) : Function.Surjective (smallQuotientMap x) :=
  ((Shrink.linearEquiv R (R ⧸ Ideal.span {x})).symm.surjective.comp
    (Ideal.Quotient.mk_surjective.comp (Shrink.linearEquiv R R).surjective))

theorem smallQuotientMap_exact (x : R) :
    Function.Exact (LinearMap.lsmul R (Shrink.{v} R) x) (smallQuotientMap x) := by
  intro a
  change smallQuotientMap x a = 0 ↔ ∃ b, x • b = a
  change (Shrink.linearEquiv R (R ⧸ Ideal.span {x})).symm
      (Ideal.Quotient.mk (Ideal.span {x}) ((Shrink.linearEquiv R R) a)) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(Shrink.linearEquiv R R).symm b, ?_⟩
    apply (Shrink.linearEquiv R R).injective
    simpa [mul_comm] using hb
  · rintro ⟨b, hb⟩
    refine ⟨(Shrink.linearEquiv R R) b, ?_⟩
    simpa [mul_comm] using congrArg (Shrink.linearEquiv R R) hb

theorem restrictedFree_hasProjectiveDimensionLE (x : R) (hx : IsSMulRegular R x)
    (P : ModuleCat.{v} (R ⧸ Ideal.span {x})) [Module.Free (R ⧸ Ideal.span {x}) P] :
    HasProjectiveDimensionLE
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj P) 1 := by
  let S := R ⧸ Ideal.span {x}
  let ι := Module.Free.ChooseBasisIndex S P
  let F := ModuleCat.of R (ι →₀ Shrink.{v} R)
  let Q := ModuleCat.of R (ι →₀ Shrink.{v} S)
  let a := LinearMap.lsmul R (Shrink.{v} R) x
  let q := smallQuotientMap.{u,v} x
  have ha : Function.Injective a :=
    IsSMulRegular.of_injective (Shrink.linearEquiv R R) (Shrink.linearEquiv R R).injective hx
  let f : F ⟶ F := ModuleCat.ofHom (Finsupp.mapRange.linearMap a)
  let g : F ⟶ Q := ModuleCat.ofHom (Finsupp.mapRange.linearMap q)
  have hex : Function.Exact f.hom g.hom := by
    rw [LinearMap.exact_iff]
    change (Finsupp.mapRange.linearMap q).ker = (Finsupp.mapRange.linearMap a).range
    rw [Finsupp.ker_mapRange, Finsupp.range_mapRange_linearMap _ (LinearMap.ker_eq_bot.mpr ha)]
    congr 1
    funext i
    exact (smallQuotientMap_exact x).linearMap_ker_eq
  let C := ModuleCat.shortComplexOfCompEqZero f.hom g.hom hex.linearMap_comp_eq_zero
  have hC : C.ShortExact :=
    ModuleCat.shortComplex_shortExact _ hex
      (Finsupp.mapRange_injective a (map_zero a) ha)
      (Finsupp.mapRange_surjective q (map_zero q) (smallQuotientMap_surjective x))
  let bF : Module.Basis ι R F := ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)⟩
  let : Projective F := ModuleCat.projective_of_free bF
  have hQ : HasProjectiveDimensionLE Q 1 :=
    hC.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance
  let b := Module.Free.chooseBasis S P
  let e : ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj P) ≃ₗ[R] Q :=
    (b.repr.restrictScalars R).trans (Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R S)).symm
  exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv e.symm 1

end AdvCommAlg.Depth

namespace AdvCommAlg.Depth
variable {R : Type u} [CommRing R] [Small.{v} R]
abbrev reesRes (x : R) := ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk (Ideal.span {x}))
instance reesRes_linear (x : R) : (reesRes (R := R) x).Linear R where
  map_smul {M N} f r := by ext n; rfl

def reesQuotientIso (x : R) (M : ModuleCat.{v} R) :
    (reesRes x).obj (Rees.quotientModule (Ideal.span {x}) M) ≅
      ModuleCat.of R (QuotSMulTop x M) where
  hom := ModuleCat.ofHom
    { toFun := (principalQuotientEquiv M x).symm
      map_add' := (principalQuotientEquiv M x).symm.map_add
      map_smul' := by
        intro r m
        exact (principalQuotientEquiv M x).symm.map_smul r m }
  inv := ModuleCat.ofHom
    { toFun := principalQuotientEquiv M x
      map_add' := (principalQuotientEquiv M x).map_add
      map_smul' := by
        intro r m
        exact (principalQuotientEquiv M x).map_smul r m }
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact (principalQuotientEquiv M x).apply_symm_apply m
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact (principalQuotientEquiv M x).symm_apply_apply m

def reesExtensionClass (x : R) (M : ModuleCat.{v} R) (hM : IsSMulRegular M x) :
    Ext ((reesRes x).obj (Rees.quotientModule (Ideal.span {x}) M)) M 1 :=
  (Ext.mk₀ (reesQuotientIso x M).hom).comp
    hM.smulShortComplex_shortExact.extClass (zero_add 1)

def reesCanonicalMap (x : R) (M : ModuleCat.{v} R) (hM : IsSMulRegular M x)
    (N : ModuleCat.{v} (R ⧸ Ideal.span {x})) (j : ℕ) :
    Ext N (Rees.quotientModule (Ideal.span {x}) M) j →ₗ[R]
      Ext ((reesRes x).obj N) M (j+1) :=
  (Ext.postcompOfLinear (reesExtensionClass x M hM) R _ rfl).comp
    ((reesRes x).mapExtLinearMap R N _ j)

lemma reesCanonicalMap_apply (x : R) (M : ModuleCat.{v} R) (hM : IsSMulRegular M x)
    (N : ModuleCat.{v} (R ⧸ Ideal.span {x})) (j : ℕ)
    (a : Ext N (Rees.quotientModule (Ideal.span {x}) M) j) :
    reesCanonicalMap x M hM N j a =
      (a.mapExactFunctor (reesRes x)).comp (reesExtensionClass x M hM) rfl := rfl

lemma reesCanonicalMap_naturality_source (x : R) (M : ModuleCat.{v} R)
    (hM : IsSMulRegular M x) {N N' : ModuleCat.{v} (R ⧸ Ideal.span {x})}
    (f : N ⟶ N') (j : ℕ) (a : Ext N' (Rees.quotientModule (Ideal.span {x}) M) j) :
    reesCanonicalMap x M hM N j ((Ext.mk₀ f).comp a (zero_add j)) =
      (Ext.mk₀ ((reesRes x).map f)).comp (reesCanonicalMap x M hM N' j a) (zero_add _) := by
  simp only [reesCanonicalMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact Ext.comp_assoc (Ext.mk₀ ((reesRes x).map f)) _ _ (zero_add j) rfl (by simp)

lemma reesCanonicalMap_naturality_connecting (x : R) (M : ModuleCat.{v} R)
    (hM : IsSMulRegular M x) {S : ShortComplex (ModuleCat.{v} (R ⧸ Ideal.span {x}))}
    (hS : S.ShortExact) (j : ℕ) (a : Ext S.X₁ (Rees.quotientModule (Ideal.span {x}) M) j) :
    reesCanonicalMap x M hM S.X₃ (j+1) (hS.extClass.comp a (add_comm 1 j)) =
      (hS.map_of_exact (reesRes x)).extClass.comp
        (reesCanonicalMap x M hM S.X₁ j a) (add_comm 1 (j+1)) := by
  simp only [reesCanonicalMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact Ext.comp_assoc _ _ _ (add_comm 1 j) rfl (by omega)
lemma principalQuotientEquiv_naturality {M M' : ModuleCat.{v} R} (f : M ⟶ M') (x : R) :
    (reesRes x).map (Rees.quotientMap (Ideal.span {x}) f) ≫
        (reesQuotientIso x M').hom =
      (reesQuotientIso x M).hom ≫
        ModuleCat.ofHom (QuotSMulTop.map x f.hom) := by
  ext q
  induction q using Submodule.Quotient.induction_on with
  | _ m => rfl

lemma reesExtensionClass_naturality (x : R) {M M' : ModuleCat.{v} R}
    (hM : IsSMulRegular M x) (hM' : IsSMulRegular M' x) (f : M ⟶ M') :
    (reesExtensionClass x M hM).comp (Ext.mk₀ f) (add_zero 1) =
      (Ext.mk₀ ((reesRes x).map (Rees.quotientMap (Ideal.span {x}) f))).comp
        (reesExtensionClass x M' hM') (zero_add 1) := by
  simp only [reesExtensionClass, Ext.comp_assoc_of_third_deg_zero]
  have hn := ShortComplex.ShortExact.extClass_naturality hM.smulShortComplex_shortExact
    hM'.smulShortComplex_shortExact (smulShortComplexMap f x)
  change hM.smulShortComplex_shortExact.extClass.comp (Ext.mk₀ f) (add_zero 1) =
    (Ext.mk₀ (ModuleCat.ofHom (QuotSMulTop.map x f.hom))).comp
      hM'.smulShortComplex_shortExact.extClass (zero_add 1) at hn
  rw [hn]
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    ← principalQuotientEquiv_naturality f x, ← Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_second_deg_zero]

lemma reesCanonicalMap_naturality_target (x : R) {M M' : ModuleCat.{v} R}
    (hM : IsSMulRegular M x) (hM' : IsSMulRegular M' x) (f : M ⟶ M')
    (N : ModuleCat.{v} (R ⧸ Ideal.span {x})) (j : ℕ)
    (a : Ext N (Rees.quotientModule (Ideal.span {x}) M) j) :
    reesCanonicalMap x M' hM' N j
        (a.comp (Ext.mk₀ (Rees.quotientMap (Ideal.span {x}) f)) (add_zero j)) =
      (reesCanonicalMap x M hM N j a).comp (Ext.mk₀ f) (add_zero (j+1)) := by
  simp only [reesCanonicalMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [Ext.comp_assoc_of_second_deg_zero, ← reesExtensionClass_naturality,
    ← Ext.comp_assoc_of_third_deg_zero]
def reesZeroComparison (x : R) (M : ModuleCat.{v} R)
    (N : ModuleCat.{v} (R ⧸ Ideal.span {x})) :
    Ext N (Rees.quotientModule (Ideal.span {x}) M) 0 ≃ₗ[R]
      Ext ((reesRes x).obj N) (ModuleCat.of R (QuotSMulTop x M)) 0 :=
  Ext.linearEquiv₀.trans
    ((quotientHomEquiv (Ideal.span {x}) M N).symm.trans
      (ModuleCat.homLinearEquiv.trans
        ((LinearEquiv.arrowCongr (LinearEquiv.refl R _) (principalQuotientEquiv M x).symm).trans
          ((ModuleCat.homLinearEquiv (R := R) (M := ((reesRes x).obj N)) (N := ModuleCat.of R (QuotSMulTop x M))).symm.trans Ext.linearEquiv₀.symm))))

lemma reesCanonicalMap_zero (x : R) (M : ModuleCat.{v} R) (hM : IsSMulRegular M x)
    (N : ModuleCat.{v} (R ⧸ Ideal.span {x}))
    (a : Ext N (Rees.quotientModule (Ideal.span {x}) M) 0) :
    reesCanonicalMap x M hM N 0 a =
      regularConnecting M ((reesRes x).obj N) x hM (reesZeroComparison x M N a) := by
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective N (Rees.quotientModule (Ideal.span {x}) M)).2 a
  simp only [reesCanonicalMap_apply, Ext.mapExactFunctor_mk₀, reesExtensionClass,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  congr 1
  apply (Ext.linearEquiv₀ (R := R)).injective
  have hmk {X Y : ModuleCat.{v} R} (g : X ⟶ Y) :
      Ext.linearEquiv₀ (R := R) (Ext.mk₀ g) = g :=
    (Ext.linearEquiv₀ (R := R)).apply_symm_apply g
  have hmkS {X Y : ModuleCat.{v} (R ⧸ Ideal.span {x})} (g : X ⟶ Y) :
      Ext.linearEquiv₀ (R := R) (Ext.mk₀ g) = g :=
    (Ext.linearEquiv₀ (R := R)).apply_symm_apply g
  simp only [reesZeroComparison, LinearEquiv.trans_apply]
  change _ = _
  simp only [Ext.linearEquiv₀_symm_apply, hmk, hmkS]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro n
  rfl

lemma reesCanonicalMap_zero_bijective (x : R) (M : ModuleCat.{v} R)
    (hM : IsSMulRegular M x) (N : ModuleCat.{v} (R ⧸ Ideal.span {x})) :
    Function.Bijective (reesCanonicalMap x M hM N 0) := by
  have hN : ∀ n : (reesRes x).obj N, x • n = 0 :=
    ideal_smul_restrictScalars_eq_zero _ N x (Ideal.subset_span (Set.mem_singleton x))
  have h := (regularConnecting_bijective M ((reesRes x).obj N) x hM hN).comp
    (reesZeroComparison x M N).bijective
  convert h using 1
  funext a
  exact reesCanonicalMap_zero x M hM N a
theorem reesCanonicalMap_bijective (x : R) (hx : IsSMulRegular R x)
    (M : ModuleCat.{v} R) (hM : IsSMulRegular M x)
    (N : ModuleCat.{v} (R ⧸ Ideal.span {x})) (j : ℕ) :
    Function.Bijective (reesCanonicalMap x M hM N j) := by
  induction j generalizing N with
  | zero => exact reesCanonicalMap_zero_bijective x M hM N
  | succ j ih =>
    let S := N.projectiveShortComplex
    have hS : S.ShortExact := N.shortExact_projectiveShortComplex
    letI := restrictedFree_hasProjectiveDimensionLE x hx S.X₂
    letI hvan : Subsingleton (Ext ((reesRes x).obj S.X₂) M ((j+1)+1)) :=
      HasProjectiveDimensionLT.subsingleton _ 2 ((j+1)+1) (by omega) M
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      ((Ext.mk₀ S.f).precomp (Rees.quotientModule (Ideal.span {x}) M) (zero_add j))
      (hS.extClass.precomp (Rees.quotientModule (Ideal.span {x}) M) (add_comm 1 j))
      ((Ext.mk₀ ((reesRes x).map S.f)).precomp M (zero_add (j+1)))
      ((hS.map_of_exact (reesRes x)).extClass.precomp M (add_comm 1 (j+1)))
      (reesCanonicalMap x M hM S.X₂ j).toAddMonoidHom
      (reesCanonicalMap x M hM S.X₁ j).toAddMonoidHom
      (reesCanonicalMap x M hM S.X₃ (j+1)).toAddMonoidHom
      (by ext a; exact (reesCanonicalMap_naturality_source x M hM S.f j a).symm)
      (by ext a; exact (reesCanonicalMap_naturality_connecting x M hM hS j a).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.contravariant_sequence_exact₁' hS _ j (j+1) (add_comm 1 j)))
      ((ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.contravariant_sequence_exact₁' (hS.map_of_exact (reesRes x)) M
          (j+1) ((j+1)+1) (add_comm 1 (j+1))))
      (ih _).surjective (ih _)
      (fun a => Ext.contravariant_sequence_exact₃ hS _ a
        (Ext.eq_zero_of_projective _) (add_comm 1 j))
      (fun a => Ext.contravariant_sequence_exact₃ (hS.map_of_exact (reesRes x)) M a
        (hvan.elim _ 0) (add_comm 1 (j+1)))
def reesAllEquiv (x : R) (hx : IsSMulRegular R x) (M : ModuleCat.{v} R)
    (hM : IsSMulRegular M x) (N : ModuleCat.{v} (R ⧸ Ideal.span {x})) (j : ℕ) :
    Ext ((reesRes x).obj N) M (j+1) ≃ₗ[R]
      Ext N (Rees.quotientModule (Ideal.span {x}) M) j :=
  (LinearEquiv.ofBijective _ (reesCanonicalMap_bijective x hx M hM N j)).symm

@[simp] lemma reesCanonicalMap_reesAllEquiv (x : R) (hx : IsSMulRegular R x)
    (M : ModuleCat.{v} R) (hM : IsSMulRegular M x)
    (N : ModuleCat.{v} (R ⧸ Ideal.span {x})) (j : ℕ)
    (a : Ext ((reesRes x).obj N) M (j+1)) :
    reesCanonicalMap x M hM N j (reesAllEquiv x hx M hM N j a) = a :=
  (LinearEquiv.ofBijective _ (reesCanonicalMap_bijective x hx M hM N j)).apply_symm_apply a

def reesSingleComparison (x : R) (hx : IsSMulRegular R x) :
    Rees.ExtShiftComparison (Ideal.span {x}) 1 (fun M : ModuleCat.{v} R => IsSMulRegular M x) where
  equiv M hM N j := reesAllEquiv x hx M hM N j
  naturality_source := by
    intro M hM N N' f j a
    apply (reesCanonicalMap_bijective x hx M hM _ j).injective
    rw [reesCanonicalMap_reesAllEquiv, reesCanonicalMap_naturality_source,
      reesCanonicalMap_reesAllEquiv]
  naturality_target := by
    intro M M' hM hM' f N j a
    apply (reesCanonicalMap_bijective x hx _ hM' N j).injective
    rw [reesCanonicalMap_reesAllEquiv, reesCanonicalMap_naturality_target (hM := hM),
      reesCanonicalMap_reesAllEquiv]

theorem rees_changeOfRings :
    Specs.AdvCommAlg.Depth.ReesChangeOfRings.singleChangeOfRings.{u,v} := by
  intro R _ _ x hx
  exact ⟨reesSingleComparison x hx⟩
end AdvCommAlg.Depth

universe w
namespace AdvCommAlg.Depth.Iterate
variable {A : Type u} [CommRing A] {R S : Type w} [CommRing R] [CommRing S]
  [Algebra A R] [Algebra A S] [Small.{v} R] [Small.{v} S]
def extRingEquiv (e : R ≃ₐ[A] S) (X : ModuleCat.{v} S) (Y : ModuleCat.{v} R) (n : ℕ) :
    Ext ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj X) Y n ≃ₗ[A]
      Ext X ((ModuleCat.restrictScalars e.symm.toRingEquiv.toRingHom).obj Y) n := by
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{_,_,v} e.toRingEquiv
  letI : E.inverse.Linear A := inferInstanceAs
    ((ModuleCat.restrictScalars e.symm.toAlgHom.toRingHom).Linear A)
  exact E.toAdjunction.extLinearEquiv A

lemma extRingEquiv_naturality_source (e : R ≃ₐ[A] S) {X X' : ModuleCat.{v} S}
    (f : X ⟶ X') (Y : ModuleCat.{v} R) (n : ℕ)
    (a : Ext ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj X') Y n) :
    extRingEquiv e X Y n
      ((Ext.mk₀ ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).map f)).comp a
        (zero_add n)) =
      (Ext.mk₀ f).comp (extRingEquiv e X' Y n a) (zero_add n) := by
  exact (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.toRingEquiv).toAdjunction.extEquiv_naturality_left₀ f a

lemma extRingEquiv_naturality_target (e : R ≃ₐ[A] S) (X : ModuleCat.{v} S)
    {Y Y' : ModuleCat.{v} R} (f : Y ⟶ Y') (n : ℕ)
    (a : Ext ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj X) Y n) :
    extRingEquiv e X Y' n (a.comp (Ext.mk₀ f) (add_zero n)) =
      (extRingEquiv e X Y n a).comp
        (Ext.mk₀ ((ModuleCat.restrictScalars e.symm.toRingEquiv.toRingHom).map f)) (add_zero n) := by
  exact (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e.toRingEquiv).toAdjunction.extEquiv_naturality_right₀ a f

variable {R : Type u} [CommRing R] [Small.{v} R]
def consRingEquiv (x : R) (xs : List R) :
    ((R ⧸ Ideal.span {x}) ⧸
      Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x})))) ≃ₐ[R]
        R ⧸ Ideal.ofList (x :: xs) :=
  (Ideal.quotientEquivAlgOfEq R
    (Ideal.map_ofList (Ideal.Quotient.mk (Ideal.span {x})) xs).symm).trans
      ((DoubleQuot.quotQuotEquivQuotSupₐ R (Ideal.span {x}) (Ideal.ofList xs)).trans
        (Ideal.quotientEquivAlgOfEq R (Ideal.ofList_cons x xs).symm))

@[simp] lemma consRingEquiv_apply_mk_mk (x : R) (xs : List R) (r : R) :
    consRingEquiv x xs (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ r)) =
      Ideal.Quotient.mk (Ideal.ofList (x :: xs)) r := rfl

def consRestrictIso (x : R) (xs : List R)
    (N : ModuleCat.{v} (R ⧸ Ideal.ofList (x :: xs))) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk
        (Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x})))))).obj
          ((ModuleCat.restrictScalars (consRingEquiv x xs).toRingEquiv.toRingHom).obj N)) ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.ofList (x :: xs)))).obj N := by
  refine LinearEquiv.toModuleIso
    (m₁ := ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk
        (Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x})))))).obj
          ((ModuleCat.restrictScalars (consRingEquiv x xs).toRingEquiv.toRingHom).obj N))).isModule)
    (m₂ := ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.ofList (x :: xs)))).obj N).isModule)
    { __ := AddEquiv.refl N
      map_smul' := by intros; rfl }

lemma consRestrictIso_naturality (x : R) (xs : List R)
    {N N' : ModuleCat.{v} (R ⧸ Ideal.ofList (x :: xs))} (f : N ⟶ N') :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).map
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk
        (Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x})))))).map
          ((ModuleCat.restrictScalars (consRingEquiv x xs).toRingEquiv.toRingHom).map f)) ≫
          (consRestrictIso x xs N').hom =
      (consRestrictIso x xs N).hom ≫
        (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.ofList (x :: xs)))).map f := by
  ext n
  rfl

def botCoefficientIso (M : ModuleCat.{v} R) :
    (ModuleCat.restrictScalars (RingEquiv.quotientBot R).toRingHom).obj M ≅
      AdvCommAlg.Depth.Rees.quotientModule (⊥ : Ideal R) M := by
  let e := (Submodule.quotEquivOfEqBot ((⊥ : Ideal R) • ⊤ : Submodule R M)
    (by rw [Submodule.bot_smul])).symm
  refine LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.restrictScalars (RingEquiv.quotientBot R).toRingHom).obj M)
    (X₂ := AdvCommAlg.Depth.Rees.quotientModule (⊥ : Ideal R) M)
    (m₁ := ((ModuleCat.restrictScalars (RingEquiv.quotientBot R).toRingHom).obj M).isModule)
    { __ := e.toAddEquiv
      map_smul' := by
        intro a m
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        change e (r • m) = Ideal.Quotient.mk (⊥ : Ideal R) r • e m
        exact e.map_smul r m }
lemma botCoefficientIso_naturality {M M' : ModuleCat.{v} R} (f : M ⟶ M') :
    (ModuleCat.restrictScalars (RingEquiv.quotientBot R).toRingHom).map f ≫
        (botCoefficientIso M').hom =
      (botCoefficientIso M).hom ≫ AdvCommAlg.Depth.Rees.quotientMap (⊥ : Ideal R) f := by
  ext m
  rfl

def botExtEquiv (M : ModuleCat.{v} R) (N : ModuleCat.{v} (R ⧸ (⊥ : Ideal R)))
    (j : ℕ) :
    Ext ((ModuleCat.restrictScalars (Ideal.Quotient.mk (⊥ : Ideal R))).obj N) M j ≃ₗ[R]
      Ext N (AdvCommAlg.Depth.Rees.quotientModule (⊥ : Ideal R) M) j := by
  exact (extRingEquiv (AlgEquiv.quotientBot R R).symm N M j).trans
    (((linearExtFunctorObj R N j).mapIso (botCoefficientIso M)).toLinearEquiv)
def botComparison (P : ModuleCat.{v} R → Prop) :
    AdvCommAlg.Depth.Rees.ExtShiftComparison (⊥ : Ideal R) 0 P where
  equiv M _ N j := botExtEquiv M N j
  naturality_source M _ := by
    intro N N' f j a
    change (extRingEquiv (AlgEquiv.quotientBot R R).symm _ M j
        ((Ext.mk₀ ((ModuleCat.restrictScalars (Ideal.Quotient.mk (⊥ : Ideal R))).map f)).comp a
          (zero_add j))).comp (Ext.mk₀ (botCoefficientIso M).hom) (add_zero j) =
      (Ext.mk₀ f).comp ((extRingEquiv (AlgEquiv.quotientBot R R).symm _ M j a).comp
        (Ext.mk₀ (botCoefficientIso M).hom) (add_zero j)) (zero_add j)
    exact (congrArg
      (fun b : Ext N ((ModuleCat.restrictScalars
          (AlgEquiv.quotientBot R R).toRingEquiv.toRingHom).obj M) j =>
        b.comp (Ext.mk₀ (botCoefficientIso M).hom) (add_zero j))
      (extRingEquiv_naturality_source (AlgEquiv.quotientBot R R).symm f M j a)).trans
        (Ext.comp_assoc _ _ _ (zero_add j) (add_zero j) (zero_add j))
  naturality_target hM hM' f N j a := by
    change (extRingEquiv (AlgEquiv.quotientBot R R).symm N _ j
        (a.comp (Ext.mk₀ f) (add_zero j))).comp (Ext.mk₀ (botCoefficientIso _).hom)
          (add_zero j) =
      ((extRingEquiv (AlgEquiv.quotientBot R R).symm N _ j a).comp
        (Ext.mk₀ (botCoefficientIso _).hom) (add_zero j)).comp
          (Ext.mk₀ (AdvCommAlg.Depth.Rees.quotientMap (⊥ : Ideal R) f)) (add_zero j)
    refine (congrArg (fun b => b.comp (Ext.mk₀ (botCoefficientIso _).hom) (add_zero j))
      (extRingEquiv_naturality_target (AlgEquiv.quotientBot R R).symm N f j a)).trans ?_
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
    have h := botCoefficientIso_naturality f
    change (ModuleCat.restrictScalars
        (AlgEquiv.quotientBot R R).symm.symm.toRingEquiv.toRingHom).map f ≫
        (botCoefficientIso _).hom = (botCoefficientIso _).hom ≫
          AdvCommAlg.Depth.Rees.quotientMap (⊥ : Ideal R) f at h
    rw [h, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero]
end AdvCommAlg.Depth.Iterate

namespace AdvCommAlg.Depth.Iterate
variable {R : Type u} [CommRing R]

def principalQuotientModuleEquiv (x : R) (M : ModuleCat.{v} R) :
    QuotSMulTop x M ≃ₗ[R ⧸ Ideal.span {x}] Rees.quotientModule (Ideal.span {x}) M :=
  { toEquiv := (principalQuotientEquiv M x).toEquiv
    map_add' := (principalQuotientEquiv M x).map_add
    map_smul' := by
      intro a m
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact (principalQuotientEquiv M x).map_smul r m }

lemma regular_cons_quotientModule (x : R) (xs : List R) (M : ModuleCat.{v} R)
    (hM : RingTheory.Sequence.IsRegular M (x::xs)) :
    IsSMulRegular M x ∧
      RingTheory.Sequence.IsRegular (Rees.quotientModule (Ideal.span {x}) M)
        (xs.map (Ideal.Quotient.mk (Ideal.span {x}))) := by
  obtain ⟨hM, hxs⟩ := (RingTheory.Sequence.isRegular_cons_iff' M x xs).mp hM
  exact ⟨hM, (principalQuotientModuleEquiv x M).isRegular_congr _ |>.mp hxs⟩

def principalQuotientRingEquiv (x : R) :
    QuotSMulTop x R ≃ₗ[R ⧸ Ideal.span {x}] (R ⧸ Ideal.span {x}) := by
  let e : QuotSMulTop x R ≃ₗ[R] (R ⧸ Ideal.span {x}) :=
    Submodule.quotEquivOfEq _ _ (by
      rw [← Submodule.ideal_span_singleton_smul]
      exact (Ideal.span {x}).mul_top)
  exact
    { toEquiv := e.toEquiv
      map_add' := e.map_add
      map_smul' := by
        intro a m
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact e.map_smul r m }

lemma regular_cons_ring (x : R) (xs : List R)
    (hR : RingTheory.Sequence.IsRegular R (x::xs)) :
    IsSMulRegular R x ∧
      RingTheory.Sequence.IsRegular (R ⧸ Ideal.span {x})
        (xs.map (Ideal.Quotient.mk (Ideal.span {x}))) := by
  obtain ⟨hx, hxs⟩ := (RingTheory.Sequence.isRegular_cons_iff' R x xs).mp hR
  exact ⟨hx, (principalQuotientRingEquiv x).isRegular_congr _ |>.mp hxs⟩
end AdvCommAlg.Depth.Iterate

namespace AdvCommAlg.Depth.Iterate
variable {R : Type u} [CommRing R] {S : Type w} [CommRing S] [Algebra R S]
  [Small.{v} S]

lemma ext_algebraMap_smul (X Y : ModuleCat.{v} S) (n : ℕ) (r : R) (a : Ext X Y n) :
    (algebraMap R S r) • a = r • a := by
  rw [Ext.smul_eq_comp_mk₀, Ext.smul_eq_comp_mk₀]
  congr 2

instance ext_isScalarTower (X Y : ModuleCat.{v} S) (n : ℕ) :
    IsScalarTower R S (Ext X Y n) where
  smul_assoc r s a := by
    rw [Algebra.smul_def, mul_smul, ext_algebraMap_smul]
end AdvCommAlg.Depth.Iterate

namespace AdvCommAlg.Depth.Iterate
variable {R : Type u} [CommRing R] [Small.{v} R]
open AdvCommAlg.Depth

def consCoefficientLinearEquiv (x : R) (xs : List R) (M : ModuleCat.{v} R) :
    (M ⧸ (Ideal.ofList (x::xs) • ⊤ : Submodule R M)) ≃ₗ[R]
      ((Rees.quotientModule (Ideal.span {x}) M) ⧸
        (Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x}))) • ⊤ :
          Submodule (R ⧸ Ideal.span {x}) (Rees.quotientModule (Ideal.span {x}) M))) := by
  let S := R ⧸ Ideal.span {x}
  let B := Rees.quotientModule (Ideal.span {x}) M
  let e₀ : QuotSMulTop x M ≃ₗ[R] B :=
    { toEquiv := (principalQuotientEquiv M x).toEquiv
      map_add' := (principalQuotientEquiv M x).map_add
      map_smul' := by
        intro r m
        exact (principalQuotientEquiv M x).map_smul r m }
  let e₁ := Submodule.Quotient.equiv
    (Ideal.ofList xs • ⊤ : Submodule R (QuotSMulTop x M))
    (Ideal.ofList xs • ⊤ : Submodule R B) e₀ (by
      rw [Submodule.map_smul'', Submodule.map_top, e₀.range])
  let J := Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x})))
  have hJ : ((J • ⊤ : Submodule S B).restrictScalars R) =
      Ideal.ofList xs • (⊤ : Submodule R B) := by
    dsimp [J]
    rw [← Ideal.map_ofList]
    exact Submodule.restrictScalars_map_smul_eq (Ideal.ofList xs) (⊤ : Submodule S B)
  exact (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x xs).trans
    (e₁.trans ((Submodule.quotEquivOfEq _ _ hJ.symm).trans
      (Submodule.Quotient.restrictScalarsEquiv R (J • ⊤ : Submodule S B))))

def consCoefficientIso (x : R) (xs : List R) (M : ModuleCat.{v} R) :
    (ModuleCat.restrictScalars (consRingEquiv x xs).toRingHom).obj
      (Rees.quotientModule (Ideal.ofList (x::xs)) M) ≅
        Rees.quotientModule
          (Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x}))))
          (Rees.quotientModule (Ideal.span {x}) M) := by
  let e := consCoefficientLinearEquiv x xs M
  refine LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.restrictScalars (consRingEquiv x xs).toRingHom).obj
      (Rees.quotientModule (Ideal.ofList (x::xs)) M))
    (X₂ := Rees.quotientModule
      (Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x}))))
      (Rees.quotientModule (Ideal.span {x}) M))
    (m₁ := ((ModuleCat.restrictScalars (consRingEquiv x xs).toRingHom).obj
      (Rees.quotientModule (Ideal.ofList (x::xs)) M)).isModule)
    { toEquiv := e.toEquiv
      map_add' := e.map_add
      map_smul' := by
        intro a m
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
        change e ((consRingEquiv x xs) (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ r)) • m) =
          Ideal.Quotient.mk _ (Ideal.Quotient.mk _ r) • e m
        rw [consRingEquiv_apply_mk_mk]
        change e (Ideal.Quotient.mk _ r • m) = _
        rw [quotient_smul]
        rw [e.map_smul]
        rfl }


lemma consCoefficientIso_naturality (x : R) (xs : List R)
    {M M' : ModuleCat.{v} R} (f : M ⟶ M') :
    (ModuleCat.restrictScalars (consRingEquiv x xs).toRingHom).map
        (Rees.quotientMap (Ideal.ofList (x::xs)) f) ≫
          (consCoefficientIso x xs M').hom =
      (consCoefficientIso x xs M).hom ≫
        Rees.quotientMap
          (Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x}))))
          (Rees.quotientMap (Ideal.span {x}) f) := by
  ext q
  induction q using Submodule.Quotient.induction_on with
  | _ m => rfl

end AdvCommAlg.Depth.Iterate

universe r
namespace AdvCommAlg.Depth.Iterate
variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C] [HasExt.{w} C]
variable {X X' X₁ X₂ X₁' X₂' Y Y' Y₁ Y₂ Y₁' Y₂' : C}

def extIsoCongr (eX : X ≅ X') (eY : Y ≅ Y') (n : ℕ) : Ext X Y n ≃ₗ[R] Ext X' Y' n where
  toFun a := (Ext.mk₀ eX.inv).comp (a.comp (Ext.mk₀ eY.hom) (add_zero n)) (zero_add n)
  invFun a := (Ext.mk₀ eX.hom).comp (a.comp (Ext.mk₀ eY.inv) (add_zero n)) (zero_add n)
  left_inv a := by
    simp only [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀, Iso.hom_inv_id, Iso.inv_hom_id, Ext.mk₀_id_comp,
      Ext.comp_mk₀_id, Ext.mk₀_comp_mk₀_assoc]
  right_inv a := by
    simp only [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀, Iso.hom_inv_id, Iso.inv_hom_id, Ext.mk₀_id_comp,
      Ext.comp_mk₀_id, Ext.mk₀_comp_mk₀_assoc]
  map_add' a b := by simp
  map_smul' r a := by simp

@[simp] lemma extIsoCongr_apply (eX : X ≅ X') (eY : Y ≅ Y') (n : ℕ) (a : Ext X Y n) :
    extIsoCongr (R := R) eX eY n a =
      (Ext.mk₀ eX.inv).comp (a.comp (Ext.mk₀ eY.hom) (add_zero n)) (zero_add n) := rfl

lemma extIsoCongr_naturality_source (e₁ : X₁ ≅ X₁') (e₂ : X₂ ≅ X₂') (eY : Y ≅ Y')
    (f : X₁ ⟶ X₂) (f' : X₁' ⟶ X₂') (hf : f ≫ e₂.hom = e₁.hom ≫ f')
    (n : ℕ) (a : Ext X₂ Y n) :
    extIsoCongr (R := R) e₁ eY n ((Ext.mk₀ f).comp a (zero_add n)) =
      (Ext.mk₀ f').comp (extIsoCongr (R := R) e₂ eY n a) (zero_add n) := by
  have hi : e₁.inv ≫ f = f' ≫ e₂.inv := by
    rw [← cancel_mono e₂.hom]
    simp [Category.assoc, hf]
  simp only [extIsoCongr_apply, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀_assoc, hi]

lemma extIsoCongr_naturality_target (eX : X ≅ X') (e₁ : Y₁ ≅ Y₁') (e₂ : Y₂ ≅ Y₂')
    (f : Y₁ ⟶ Y₂) (f' : Y₁' ⟶ Y₂') (hf : e₁.hom ≫ f' = f ≫ e₂.hom)
    (n : ℕ) (a : Ext X Y₁ n) :
    extIsoCongr (R := R) eX e₂ n (a.comp (Ext.mk₀ f) (add_zero n)) =
      (extIsoCongr (R := R) eX e₁ n a).comp (Ext.mk₀ f') (add_zero n) := by
  simp only [extIsoCongr_apply, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, hf]
section RingCongr
variable {A : Type*} [CommRing A] {T U : Type*} [CommRing T] [CommRing U]
  [Algebra A T] [Algebra A U] [Small.{w} T] [Small.{w} U]

def extRingCongr (e : T ≃ₐ[A] U) (N Q : ModuleCat.{w} U) (j : ℕ) :
    Ext ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj N)
      ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj Q) j ≃ₗ[A] Ext N Q j := by
  let F := ModuleCat.restrictScalars.{w} e.toRingEquiv.toRingHom
  letI : F.Linear A := inferInstanceAs
    ((ModuleCat.restrictScalars e.toAlgHom.toRingHom).Linear A)
  exact (LinearEquiv.ofBijective (F.mapExtLinearMap A N Q j)
    (F.mapExt_bijective_of_preservesProjectiveObjects N Q j)).symm

@[simp] lemma extMap_extRingCongr (e : T ≃ₐ[A] U) (N Q : ModuleCat.{w} U) (j : ℕ)
    (a : Ext ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj N)
      ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj Q) j) :
    (extRingCongr e N Q j a).mapExactFunctor
      (ModuleCat.restrictScalars e.toRingEquiv.toRingHom) = a := by
  let F := ModuleCat.restrictScalars.{w} e.toRingEquiv.toRingHom
  letI : F.Linear A := inferInstanceAs
    ((ModuleCat.restrictScalars e.toAlgHom.toRingHom).Linear A)
  exact (LinearEquiv.ofBijective (F.mapExtLinearMap A N Q j)
    (F.mapExt_bijective_of_preservesProjectiveObjects N Q j)).apply_symm_apply a

lemma extRingCongr_naturality_source (e : T ≃ₐ[A] U) {N N' : ModuleCat.{w} U}
    (f : N ⟶ N') (Q : ModuleCat.{w} U) (j : ℕ)
    (a : Ext ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj N')
      ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj Q) j) :
    extRingCongr e N Q j
      ((Ext.mk₀ ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).map f)).comp a (zero_add j)) =
      (Ext.mk₀ f).comp (extRingCongr e N' Q j a) (zero_add j) := by
  apply ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).mapExt_bijective_of_preservesProjectiveObjects N Q j).injective
  change (extRingCongr e N Q j _).mapExactFunctor _ =
    ((Ext.mk₀ f).comp (extRingCongr e N' Q j a) (zero_add j)).mapExactFunctor _
  simp only [extMap_extRingCongr, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]

lemma extRingCongr_naturality_target (e : T ≃ₐ[A] U) (N : ModuleCat.{w} U)
    {Q Q' : ModuleCat.{w} U} (f : Q ⟶ Q') (j : ℕ)
    (a : Ext ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj N)
      ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj Q) j) :
    extRingCongr e N Q' j
      (a.comp (Ext.mk₀ ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).map f)) (add_zero j)) =
      (extRingCongr e N Q j a).comp (Ext.mk₀ f) (add_zero j) := by
  apply ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).mapExt_bijective_of_preservesProjectiveObjects N Q' j).injective
  change (extRingCongr e N Q' j _).mapExactFunctor _ =
    ((extRingCongr e N Q j a).comp (Ext.mk₀ f) (add_zero j)).mapExactFunctor _
  simp only [extMap_extRingCongr, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
end RingCongr
end AdvCommAlg.Depth.Iterate

universe t
namespace AdvCommAlg.Depth.Iterate
variable {R : Type u} [CommRing R] {S : Type w} [CommRing S]
  {T : Type t} [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]
  [IsScalarTower R S T] [Small.{v} T]

lemma ext_algebraMap_smul_tower (X Y : ModuleCat.{v} T) (n : ℕ) (r : R) (a : Ext X Y n) :
    (algebraMap R S r) • a = r • a := by
  rw [← ext_algebraMap_smul X Y n (algebraMap R S r),
    ← ext_algebraMap_smul X Y n r, ← IsScalarTower.algebraMap_apply R S T]

instance ext_isScalarTower_tower (X Y : ModuleCat.{v} T) (n : ℕ) :
    IsScalarTower R S (Ext X Y n) where
  smul_assoc r s a := by
    rw [Algebra.smul_def, mul_smul, ext_algebraMap_smul_tower]

end AdvCommAlg.Depth.Iterate

namespace AdvCommAlg.Depth.Iterate
variable {R : Type u} [CommRing R] [Small.{v} R]

def consEquiv (x : R) (xs : List R)
    (c1 : Rees.ExtShiftComparison (Ideal.span {x}) 1 (fun M => IsSMulRegular M x))
    (c2 : Rees.ExtShiftComparison
      (Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x})))) xs.length
      (fun M => RingTheory.Sequence.IsRegular M
        (xs.map (Ideal.Quotient.mk (Ideal.span {x})))))
    (M : ModuleCat.{v} R) (hM : RingTheory.Sequence.IsRegular M (x::xs))
    (N : ModuleCat.{v} (R ⧸ Ideal.ofList (x::xs))) (j : ℕ) :
    Ext ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.ofList (x::xs)))).obj N)
      M (j + (x::xs).length) ≃ₗ[R]
        Ext N (Rees.quotientModule (Ideal.ofList (x::xs)) M) j := by
  let S := R ⧸ Ideal.span {x}
  let J := Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x})))
  let NT := (ModuleCat.restrictScalars (consRingEquiv x xs).toRingHom).obj N
  let NS := (ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj NT
  let h := regular_cons_quotientModule x xs M hM
  exact (extIsoCongr (consRestrictIso x xs N).symm (Iso.refl M) _).trans
    ((c1.equiv M h.1 NS (j + xs.length)).trans
      (((c2.equiv (Rees.quotientModule (Ideal.span {x}) M) h.2 NT j).restrictScalars R).trans
        ((extIsoCongr (Iso.refl NT) (consCoefficientIso x xs M).symm j).trans
          (extRingCongr (consRingEquiv x xs) N
            (Rees.quotientModule (Ideal.ofList (x::xs)) M) j))))
end AdvCommAlg.Depth.Iterate

namespace AdvCommAlg.Depth.Iterate
variable {R : Type u} [CommRing R] [Small.{v} R]

lemma consEquiv_naturality_source (x : R) (xs : List R)
    (c1 : Rees.ExtShiftComparison (Ideal.span {x}) 1 (fun M => IsSMulRegular M x))
    (c2 : Rees.ExtShiftComparison
      (Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x})))) xs.length
      (fun M => RingTheory.Sequence.IsRegular M
        (xs.map (Ideal.Quotient.mk (Ideal.span {x})))))
    (M : ModuleCat.{v} R) (hM : RingTheory.Sequence.IsRegular M (x::xs))
    {N N' : ModuleCat.{v} (R ⧸ Ideal.ofList (x::xs))} (f : N ⟶ N') (j : ℕ)
    (a : Ext ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.ofList (x::xs)))).obj N')
      M (j + (x::xs).length)) :
    consEquiv x xs c1 c2 M hM N j
      ((Ext.mk₀ ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.ofList (x::xs)))).map f)).comp a
        (zero_add _)) =
      (Ext.mk₀ f).comp (consEquiv x xs c1 c2 M hM N' j a) (zero_add j) := by
  let fT := (ModuleCat.restrictScalars (consRingEquiv x xs).toRingHom).map f
  let fS := (ModuleCat.restrictScalars
    (Ideal.Quotient.mk (Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x})))))).map fT
  let fR := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).map fS
  have hsource :
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.ofList (x::xs)))).map f ≫
        (consRestrictIso x xs N').inv = (consRestrictIso x xs N).inv ≫ fR := by
    ext n
    rfl
  simp only [consEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
  rw [extIsoCongr_naturality_source (consRestrictIso x xs N).symm
    (consRestrictIso x xs N').symm (Iso.refl M) _ fR hsource]
  dsimp only [fR]
  erw [c1.naturality_source M (regular_cons_quotientModule x xs M hM).1 fS
    (j + xs.length)
    ((extIsoCongr (consRestrictIso x xs N').symm (Iso.refl M) (j+(x::xs).length)) a)]
  dsimp only [fS]
  rw [c2.naturality_source (Rees.quotientModule (Ideal.span {x}) M)
    (regular_cons_quotientModule x xs M hM).2 fT j]
  rw [extIsoCongr_naturality_source
    (Iso.refl ((ModuleCat.restrictScalars (consRingEquiv x xs).toRingHom).obj N))
    (Iso.refl ((ModuleCat.restrictScalars (consRingEquiv x xs).toRingHom).obj N'))
    (consCoefficientIso x xs M).symm fT fT (by simp)]
  exact extRingCongr_naturality_source (consRingEquiv x xs) f _ j _
end AdvCommAlg.Depth.Iterate

namespace AdvCommAlg.Depth.Iterate
variable {R : Type u} [CommRing R] [Small.{v} R]

lemma consEquiv_naturality_target (x : R) (xs : List R)
    (c1 : Rees.ExtShiftComparison (Ideal.span {x}) 1 (fun M => IsSMulRegular M x))
    (c2 : Rees.ExtShiftComparison
      (Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x})))) xs.length
      (fun M => RingTheory.Sequence.IsRegular M
        (xs.map (Ideal.Quotient.mk (Ideal.span {x})))))
    {M M' : ModuleCat.{v} R}
    (hM : RingTheory.Sequence.IsRegular M (x::xs))
    (hM' : RingTheory.Sequence.IsRegular M' (x::xs)) (f : M ⟶ M')
    (N : ModuleCat.{v} (R ⧸ Ideal.ofList (x::xs))) (j : ℕ)
    (a : Ext ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.ofList (x::xs)))).obj N)
      M (j + (x::xs).length)) :
    consEquiv x xs c1 c2 M' hM' N j (a.comp (Ext.mk₀ f) (add_zero _)) =
      (consEquiv x xs c1 c2 M hM N j a).comp
        (Ext.mk₀ (Rees.quotientMap (Ideal.ofList (x::xs)) f)) (add_zero j) := by
  dsimp only [consEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
  simp only [List.length_cons, Nat.add_succ, Nat.add_zero] at a ⊢
  rw [extIsoCongr_naturality_target _ (Iso.refl M) (Iso.refl M') f f
    (by simp)]
  rw [c1.naturality_target (regular_cons_quotientModule x xs M hM).1
    (regular_cons_quotientModule x xs M' hM').1 f _ (j + xs.length)]
  rw [c2.naturality_target (regular_cons_quotientModule x xs M hM).2
    (regular_cons_quotientModule x xs M' hM').2 (Rees.quotientMap (Ideal.span {x}) f)]
  have hc : (consCoefficientIso x xs M).inv ≫
      (ModuleCat.restrictScalars (consRingEquiv x xs).toRingHom).map
        (Rees.quotientMap (Ideal.ofList (x::xs)) f) =
      Rees.quotientMap (Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x}))))
        (Rees.quotientMap (Ideal.span {x}) f) ≫ (consCoefficientIso x xs M').inv := by
    apply (cancel_mono (consCoefficientIso x xs M').hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [consCoefficientIso_naturality]
    simp
  rw [extIsoCongr_naturality_target _ (consCoefficientIso x xs M).symm
    (consCoefficientIso x xs M').symm _ _ hc]
  rw [extRingCongr_naturality_target]
end AdvCommAlg.Depth.Iterate

namespace AdvCommAlg.Depth.Iterate
variable {R : Type u} [CommRing R] [Small.{v} R]

/-- Composing the first-element and tail comparisons, with the actual quotient
by the ideal of the concatenated list and naturality in both arguments. -/
def consComparison (x : R) (xs : List R)
    (c1 : Rees.ExtShiftComparison (Ideal.span {x}) 1 (fun M => IsSMulRegular M x))
    (c2 : Rees.ExtShiftComparison
      (Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x})))) xs.length
      (fun M => RingTheory.Sequence.IsRegular M
        (xs.map (Ideal.Quotient.mk (Ideal.span {x}))))) :
    Rees.ExtShiftComparison (Ideal.ofList (x::xs)) (x::xs).length
      (fun M => RingTheory.Sequence.IsRegular M (x::xs)) where
  equiv := consEquiv x xs c1 c2
  naturality_source := consEquiv_naturality_source x xs c1 c2
  naturality_target := consEquiv_naturality_target x xs c1 c2

end AdvCommAlg.Depth.Iterate

namespace AdvCommAlg.Depth

/-- The natural change-of-rings comparison for a complete regular sequence,
including the empty sequence and the canonical quotient by the entire ideal. -/
theorem regularSequence_changeOfRings :
    Specs.AdvCommAlg.Depth.ReesChangeOfRings.iteratedChangeOfRings.{u,v} := by
  suffices ∀ n : ℕ, ∀ {R : Type u} [CommRing R] [Small.{v} R]
      (xs : List R), xs.length = n → RingTheory.Sequence.IsRegular R xs →
      Nonempty (Rees.ExtShiftComparison (Ideal.ofList xs) xs.length
        (fun M : ModuleCat.{v} R => RingTheory.Sequence.IsRegular M xs)) by
    intro R _ _ xs hxs
    exact this xs.length xs rfl hxs
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro R _ _ xs hlen hR
    cases xs with
    | nil =>
      exact ⟨by simpa using (Iterate.botComparison (R := R)
        (fun M : ModuleCat.{v} R => RingTheory.Sequence.IsRegular M []))⟩
    | cons x xs =>
      have hh := Iterate.regular_cons_ring x xs hR
      obtain ⟨c2⟩ := ih xs.length (by simpa [← hlen] using Nat.lt_succ_self xs.length)
        (R := R ⧸ Ideal.span {x})
        (xs.map (Ideal.Quotient.mk (Ideal.span {x}))) (by simp) hh.2
      have c2' : Rees.ExtShiftComparison
          (Ideal.ofList (xs.map (Ideal.Quotient.mk (Ideal.span {x})))) xs.length
          (fun M : ModuleCat.{v} (R ⧸ Ideal.span {x}) =>
            RingTheory.Sequence.IsRegular M (xs.map (Ideal.Quotient.mk (Ideal.span {x})))) := by
        simpa only [List.length_map] using c2
      exact ⟨Iterate.consComparison x xs (reesSingleComparison x hh.1) c2'⟩
end AdvCommAlg.Depth
