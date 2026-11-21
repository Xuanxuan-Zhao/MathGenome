import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.ConcentratedChangeOfRings
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ExtScalarActions
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
GC-03, general concentrated change of rings. The canonical R-action and both
functors are defined in the independent Specs file. Coextension of an injective
resolution computes Ext over the source ring. Its concentration identifies it
in the derived category with its actual cohomology module in degree c, yielding
the natural R-linear comparison. Dimension shifting proves vanishing below c.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Abelian

namespace AdvCommAlg.Gorenstein.ConcentratedChangeOfRings

variable {S R : Type u} [CommRing S] [CommRing R]

/-- The R-scalar action is precisely pullback by multiplication on M. -/
lemma firstExt_smul_def (φ : S →+* R) (M : ModuleCat.{u} R) (N : ModuleCat.{u} S)
    (n : ℕ) (r : R) (x : FirstExt φ M N n) :
    firstExtAddEquiv φ M N n (r • x) =
      (Ext.mk₀ ((ModuleCat.restrictScalars φ).map (r • 𝟙 M))).comp
        (firstExtAddEquiv φ M N n x) (zero_add n) := rfl

/-- Restricting the new action along φ recovers the ordinary S-action on Ext. -/
lemma firstExt_smul_of_base (φ : S →+* R) (M : ModuleCat.{u} R) (N : ModuleCat.{u} S)
    (n : ℕ) (s : S) (x : FirstExt φ M N n) :
    firstExtAddEquiv φ M N n (φ s • x) = s • firstExtAddEquiv φ M N n x := by
  rw [firstExt_smul_def,
    AdvCommAlg.Depth.ExtScalarActions.scalar_eq_precomposition S _ N s n]
  congr 2

/-- Restriction is exact, so its right adjoint sends injectives to injectives. -/
lemma coextend_injective (φ : S →+* R) (I : ModuleCat.{u} S) [Injective I] :
    Injective ((ModuleCat.coextendScalars φ).obj I) :=
  (ModuleCat.restrictCoextendScalarsAdj φ).map_injective I inferInstance

/-- Degree-zero Ext with its first-argument action is the usual coextension
adjunction, R-linearly. -/
def firstExtZeroEquiv (φ : S →+* R) (M : ModuleCat.{u} R) (N : ModuleCat.{u} S) :
    FirstExt φ M N 0 ≃ₗ[R] (M ⟶ (ModuleCat.coextendScalars φ).obj N) where
  toAddEquiv := (firstExtAddEquiv φ M N 0).trans
    (Ext.addEquiv₀.trans ((ModuleCat.restrictCoextendScalarsAdj φ).homAddEquiv M N))
  map_smul' r x := by
    change (ModuleCat.restrictCoextendScalarsAdj φ).homEquiv M N
        (Ext.homEquiv₀ ((Ext.mk₀ ((ModuleCat.restrictScalars φ).map (r • 𝟙 M))).comp
          (firstExtAddEquiv φ M N 0 x) (zero_add 0))) =
      r • (ModuleCat.restrictCoextendScalarsAdj φ).homEquiv M N
        (Ext.homEquiv₀ (firstExtAddEquiv φ M N 0 x))
    obtain ⟨f, hf⟩ := (Ext.mk₀_bijective ((ModuleCat.restrictScalars φ).obj M) N).surjective
      (firstExtAddEquiv φ M N 0 x)
    rw [← hf, Ext.mk₀_comp_mk₀]
    simp only [← Ext.homEquiv₀_symm_apply, Equiv.apply_symm_apply]
    ext m s
    change R at s
    change f ((r • ((s : R) • m) : M)) = f ((((s : R) * r) • m) : M)
    rw [mul_smul, smul_comm]

/-- Degree-zero vanishing already propagates from R to every R-module. -/
lemma vanishing_zero (φ : S →+* R) (N : ModuleCat.{u} S) (c : ℕ)
    (h : Concentrated φ N c) (hc : 0 < c) (M : ModuleCat.{u} R) :
    Subsingleton (Ext ((ModuleCat.restrictScalars φ).obj M) N 0) := by
  have hR := h 0 (Nat.ne_of_lt hc)
  have hhom : Subsingleton (((ModuleCat.restrictScalars φ).obj (ModuleCat.of R R)) ⟶ N) :=
    (Ext.addEquiv₀ (X := (ModuleCat.restrictScalars φ).obj (ModuleCat.of R R))
      (Y := N)).surjective.subsingleton
  have hco : Subsingleton ((ModuleCat.coextendScalars φ).obj N) := by
    exact ⟨fun f g => LinearMap.ext fun r => congrArg (fun k => k r)
      (Subsingleton.elim (ModuleCat.ofHom f) (ModuleCat.ofHom g))⟩
  have hh : Subsingleton (M ⟶ (ModuleCat.coextendScalars φ).obj N) :=
    ⟨fun f g => ModuleCat.hom_ext (LinearMap.ext fun m => hco.elim (f m) (g m))⟩
  exact (firstExtZeroEquiv φ M N).injective.subsingleton

instance coextend_additive (φ : S →+* R) : (ModuleCat.coextendScalars.{u,u,u} φ).Additive :=
  (ModuleCat.restrictCoextendScalarsAdj φ).right_adjoint_additive

/-- The bounded below injective complex representing derived coextension. -/
def coextensionComplex (φ : S →+* R) {N : ModuleCat.{u} S}
    (I : InjectiveResolution N) : CochainComplex (ModuleCat.{u} R) ℤ :=
  ((ModuleCat.coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex

instance coextensionComplex_injective (φ : S →+* R) {N : ModuleCat.{u} S}
    (I : InjectiveResolution N) (n : ℤ) :
    Injective ((coextensionComplex φ I).X n) :=
  coextend_injective φ (I.cochainComplex.X n)

instance coextensionComplex_isStrictlyGE (φ : S →+* R) {N : ModuleCat.{u} S}
    (I : InjectiveResolution N) : (coextensionComplex φ I).IsStrictlyGE 0 := by
  unfold coextensionComplex
  infer_instance

instance coextensionComplex_isKInjective (φ : S →+* R) {N : ModuleCat.{u} S}
    (I : InjectiveResolution N) : (coextensionComplex φ I).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ 0

/-- Vanishing on the restricted regular module is exactness of the
coextended injective resolution in the corresponding positive degree. -/
lemma coextend_exact (φ : S →+* R) (N : ModuleCat.{u} S)
    (I : InjectiveResolution N) (n : ℕ)
    (h : Subsingleton (Ext ((ModuleCat.restrictScalars φ).obj
      (ModuleCat.of R R)) N (n + 1))) :
    (ShortComplex.mk ((ModuleCat.coextendScalars φ).map (I.cocomplex.d n (n+1)))
      ((ModuleCat.coextendScalars φ).map (I.cocomplex.d (n+1) (n+2)))
      (by rw [← Functor.map_comp]; simp)).Exact := by
  classical
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  let f : (ModuleCat.restrictScalars φ).obj (ModuleCat.of R R) ⟶
      I.cocomplex.X (n+1) := ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars φ).obj (ModuleCat.of R R))
        ((ModuleCat.CoextendScalars.equiv φ _) x)
  have hf : f ≫ I.cocomplex.d (n+1) (n+2) = 0 := by
    ext r
    exact congrArg (fun z => z r) hx
  have hz : I.extMk f (n+2) rfl hf = 0 := h.elim _ _
  obtain ⟨g, hg⟩ := (I.extMk_eq_zero_iff f (n+2) rfl hf n rfl).mp hz
  exact ⟨(ModuleCat.CoextendScalars.equiv φ _).symm g.hom, by
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro r
    exact congrArg (fun k => k r) hg⟩

/-- Projectivity over R suffices to propagate any positive-degree vanishing
from the restricted regular module R. -/
lemma vanishing_projective (φ : S →+* R) (N : ModuleCat.{u} S)
    (P : ModuleCat.{u} R) [Projective P] (n : ℕ)
    (h : Subsingleton (Ext ((ModuleCat.restrictScalars φ).obj
      (ModuleCat.of R R)) N (n+1))) :
    Subsingleton (Ext ((ModuleCat.restrictScalars φ).obj P) N (n+1)) := by
  classical
  let I := injectiveResolution N
  have hex := coextend_exact φ N I n h
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective x (n+2) rfl
  let F := (ModuleCat.restrictCoextendScalarsAdj φ).homEquiv P (I.cocomplex.X (n+1)) f
  have hF : F ≫ (ModuleCat.coextendScalars φ).map
      (I.cocomplex.d (n+1) (n+2)) = 0 := by
    ext p r
    change R at r
    exact congrArg (fun k => k (r • p)) hf
  let G := hex.liftFromProjective F hF
  have hG := hex.liftFromProjective_comp F hF
  apply (I.extMk_eq_zero_iff f (n+2) rfl hf n rfl).mpr
  refine ⟨ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction φ G, ?_⟩
  ext p
  have he := congrArg (fun k => k p (1 : R)) hG
  change I.cocomplex.d n (n+1) (G p (1 : R)) = f ((1 : R) • p) at he
  simp only [ModuleCat.comp_apply,
    ModuleCat.RestrictionCoextensionAdj.HomEquiv.toRestriction_hom_apply]
  simpa only [one_smul] using he

/-- A complex with a single nonzero cohomology object represents that
actual cohomology object in the corresponding degree. -/
lemma exists_iso_single_homology [HasDerivedCategory (ModuleCat.{u} R)]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (c : ℤ)
    (h : ∀ n : ℤ, n ≠ c → Limits.IsZero (K.homology n)) :
    Nonempty (DerivedCategory.Q.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) c).obj (K.homology c)) := by
  have : K.IsGE c := by
    rw [CochainComplex.isGE_iff]
    intro n hn
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact h n (ne_of_lt hn)
  have : K.IsLE c := by
    rw [CochainComplex.isLE_iff]
    intro n hn
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact h n (ne_of_gt hn)
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Q.obj K) c
  let a : K.homology c ≅ Y :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) c).app K).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) c).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) c).app Y
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{u} R) c).mapIso a.symm⟩

open CochainComplex HomComplex

/-- The termwise restriction/coextension adjunction on cochains from a module. -/
def coextensionCochainEquiv (φ : S →+* R) (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) :
    Cochain ((CochainComplex.singleFunctor (ModuleCat S) 0).obj
      ((ModuleCat.restrictScalars φ).obj M)) K n ≃+
    Cochain ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M)
      (((ModuleCat.coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj K) n :=
  (Cochain.fromSingleEquiv (zero_add n)).trans
    (((ModuleCat.restrictCoextendScalarsAdj φ).homAddEquiv M (K.X n)).trans
      (Cochain.fromSingleEquiv (K := ((ModuleCat.coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj K) (zero_add n)).symm)

@[simp]
lemma coextensionCochainEquiv_fromSingleMk (φ : S →+* R) (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ)
    (f : (ModuleCat.restrictScalars φ).obj M ⟶ K.X n) :
    coextensionCochainEquiv φ M K n (Cochain.fromSingleMk f (zero_add n)) =
      Cochain.fromSingleMk ((ModuleCat.restrictCoextendScalarsAdj φ).homEquiv M _ f)
        (zero_add n) := by
  simp [coextensionCochainEquiv, Cochain.fromSingleEquiv]

/-- The adjunction commutes with the differential, in every integer degree. -/
lemma coextensionCochainEquiv_δ (φ : S →+* R) (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (n m : ℤ)
    (x : Cochain ((CochainComplex.singleFunctor (ModuleCat S) 0).obj
      ((ModuleCat.restrictScalars φ).obj M)) K n) :
    coextensionCochainEquiv φ M K m (δ n m x) =
      δ n m (coextensionCochainEquiv φ M K n x) := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective x n (zero_add n)
  simp only [Cochain.δ_fromSingleMk _ _ _ m (zero_add m),
    coextensionCochainEquiv_fromSingleMk]
  congr 1

/-- The adjunction identifies the actual groups of cocycles. -/
def coextensionCocycleEquiv (φ : S →+* R) (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) :
    Cocycle ((CochainComplex.singleFunctor (ModuleCat S) 0).obj
      ((ModuleCat.restrictScalars φ).obj M)) K n ≃+
    Cocycle ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M)
      (((ModuleCat.coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj K) n where
  toFun x := Cocycle.mk (coextensionCochainEquiv φ M K n x.1) (n+1) rfl (by
    rw [← coextensionCochainEquiv_δ, x.δ_eq_zero, map_zero])
  invFun x := Cocycle.mk ((coextensionCochainEquiv φ M K n).symm x.1) (n+1) rfl (by
    apply (coextensionCochainEquiv φ M K (n+1)).injective
    rw [coextensionCochainEquiv_δ, AddEquiv.apply_symm_apply, x.δ_eq_zero, map_zero])
  left_inv x := by ext : 1; exact (coextensionCochainEquiv φ M K n).symm_apply_apply x.1
  right_inv x := by ext : 1; exact (coextensionCochainEquiv φ M K n).apply_symm_apply x.1
  map_add' x y := by ext : 1; exact map_add (coextensionCochainEquiv φ M K n) x.1 y.1

lemma coextensionCocycleEquiv_mem_coboundaries (φ : S →+* R) (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ)
    (x : Cocycle ((CochainComplex.singleFunctor (ModuleCat S) 0).obj
      ((ModuleCat.restrictScalars φ).obj M)) K n) :
    coextensionCocycleEquiv φ M K n x ∈ coboundaries _ _ n ↔
      x ∈ coboundaries _ _ n := by
  rw [mem_coboundaries_iff _ (n-1) (by omega),
    mem_coboundaries_iff _ (n-1) (by omega)]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(coextensionCochainEquiv φ M K (n-1)).symm b, ?_⟩
    apply (coextensionCochainEquiv φ M K n).injective
    rw [coextensionCochainEquiv_δ, AddEquiv.apply_symm_apply]
    exact hb
  · rintro ⟨b, hb⟩
    exact ⟨coextensionCochainEquiv φ M K (n-1) b, by
      rw [← coextensionCochainEquiv_δ, hb]; rfl⟩

/-- Adjunction descends to cohomology, since it identifies boundaries as well
as cycles. No exactness of coextension is assumed. -/
def coextensionClassEquiv (φ : S →+* R) (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) :
    CohomologyClass ((CochainComplex.singleFunctor (ModuleCat S) 0).obj
      ((ModuleCat.restrictScalars φ).obj M)) K n ≃+
    CohomologyClass ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M)
      (((ModuleCat.coextendScalars φ).mapHomologicalComplex (.up ℤ)).obj K) n :=
  QuotientAddGroup.congr _ _ (coextensionCocycleEquiv φ M K n) (by
    ext x
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (coextensionCocycleEquiv_mem_coboundaries φ M K n y).mpr hy
    · intro hx
      refine ⟨(coextensionCocycleEquiv φ M K n).symm x, ?_,
        (coextensionCocycleEquiv φ M K n).apply_symm_apply x⟩
      apply (coextensionCocycleEquiv_mem_coboundaries φ M K n _).mp
      simpa using hx)

/-- The actual coextended injective complex computes Ext over S on every
R-module. This is the derived adjunction without a concentration hypothesis. -/
def extCoextensionClassEquiv (φ : S →+* R) (M : ModuleCat.{u} R)
    {N : ModuleCat.{u} S} (I : InjectiveResolution N) (n : ℕ) :
    Ext ((ModuleCat.restrictScalars φ).obj M) N n ≃+
      CohomologyClass ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M)
        (coextensionComplex φ I) n :=
  I.extAddEquivCohomologyClass.trans (coextensionClassEquiv φ M I.cochainComplex n)



section ClassPrecomp
variable {A : Type*} [Ring A] {C : Type u} [Category.{v} C] [Preadditive C] [Linear A C]
variable {F G K : CochainComplex C ℤ}

def classPrecomp (f : F ⟶ G) (n : ℤ) :
    CohomologyClass G K n →ₗ[A] CohomologyClass F K n where
  toFun := CohomologyClass.descAddMonoidHom
    { toFun := fun z => CohomologyClass.mk (z.precomp f)
      map_zero' := by apply congrArg CohomologyClass.mk; ext; simp [Cocycle.precomp]
      map_add' := by
        intro z w
        rw [← CohomologyClass.mk_add]
        apply congrArg CohomologyClass.mk
        ext
        simp [Cocycle.precomp, Cochain.comp_add] }
    (by
      intro z hz
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ (n-1) (by omega)]
      obtain ⟨b, hb⟩ := (mem_coboundaries_iff _ (n-1) (by omega)).mp hz
      exact ⟨(Cochain.ofHom f).comp b (zero_add _), by
        rw [δ_ofHom_comp, hb]; rfl⟩)
  map_add' := by intros; apply map_add
  map_smul' := by
    intro r x
    obtain ⟨x, rfl⟩ := x.mk_surjective
    change CohomologyClass.mk ((r • x).precomp f) = r • CohomologyClass.mk (x.precomp f)
    rw [← CohomologyClass.mk_smul]
    apply congrArg CohomologyClass.mk
    ext
    simp [Cocycle.precomp, Cochain.comp_smul]

@[simp] lemma classPrecomp_mk (f : F ⟶ G) (n : ℤ) (z : Cocycle G K n) :
    classPrecomp (A := A) f n (.mk z) = .mk (z.precomp f) := rfl

@[simp] lemma classPrecomp_id (n : ℤ) (x : CohomologyClass F K n) :
    classPrecomp (A := A) (𝟙 F) n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [classPrecomp_mk]
  apply congrArg CohomologyClass.mk
  ext
  simp [Cocycle.precomp]

lemma classPrecomp_smul_id (r : A) (n : ℤ) (x : CohomologyClass F K n) :
    classPrecomp (A := A) (r • 𝟙 F) n x = r • x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [classPrecomp_mk, ← CohomologyClass.mk_smul]
  apply congrArg CohomologyClass.mk
  ext
  simp [Cocycle.precomp, Cochain.ofHom_smul, Cochain.smul_comp]

lemma classPrecomp_homAddEquiv (f : F ⟶ G) (n : ℤ) (x : CohomologyClass G K n) :
    CohomologyClass.homAddEquiv (classPrecomp (A := A) f n x) =
      (HomotopyCategory.quotient C (.up ℤ)).map f ≫ CohomologyClass.homAddEquiv x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp only [classPrecomp_mk, CohomologyClass.homAddEquiv_apply, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_precomp, Functor.map_comp]

end ClassPrecomp

variable {S R : Type u} [CommRing S] [CommRing R]

lemma coextensionCochainEquiv_precomp (φ : S →+* R) {M M' : ModuleCat.{u} R}
    (f : M ⟶ M') (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ)
    (x : Cochain ((singleFunctor (ModuleCat S) 0).obj
      ((ModuleCat.restrictScalars φ).obj M')) K n) :
    coextensionCochainEquiv φ M K n
      ((Cochain.ofHom ((singleFunctor (ModuleCat S) 0).map
        ((ModuleCat.restrictScalars φ).map f))).comp x (zero_add n)) =
      (Cochain.ofHom ((singleFunctor (ModuleCat R) 0).map f)).comp
        (coextensionCochainEquiv φ M' K n x) (zero_add n) := by
  obtain ⟨g, rfl⟩ := Cochain.fromSingleMk_surjective x n (zero_add n)
  rw [← Cochain.fromSingleMk_precomp, coextensionCochainEquiv_fromSingleMk,
    coextensionCochainEquiv_fromSingleMk, ← Cochain.fromSingleMk_precomp]
  congr 1
  exact (ModuleCat.restrictCoextendScalarsAdj φ).homEquiv_naturality_left f g

lemma coextensionCocycleEquiv_precomp (φ : S →+* R) {M M' : ModuleCat.{u} R}
    (f : M ⟶ M') (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ)
    (x : Cocycle ((singleFunctor (ModuleCat S) 0).obj
      ((ModuleCat.restrictScalars φ).obj M')) K n) :
    coextensionCocycleEquiv φ M K n
      (x.precomp ((singleFunctor (ModuleCat S) 0).map
        ((ModuleCat.restrictScalars φ).map f))) =
      (coextensionCocycleEquiv φ M' K n x).precomp
        ((singleFunctor (ModuleCat R) 0).map f) := by
  ext : 1
  exact coextensionCochainEquiv_precomp φ f K n x.1

lemma coextensionClassEquiv_precomp (φ : S →+* R) {M M' : ModuleCat.{u} R}
    (f : M ⟶ M') (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ)
    (x : CohomologyClass ((singleFunctor (ModuleCat S) 0).obj
      ((ModuleCat.restrictScalars φ).obj M')) K n) :
    coextensionClassEquiv φ M K n
      (classPrecomp (A := S) ((singleFunctor (ModuleCat S) 0).map
        ((ModuleCat.restrictScalars φ).map f)) n x) =
      classPrecomp (A := R) ((singleFunctor (ModuleCat R) 0).map f) n
        (coextensionClassEquiv φ M' K n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk _ = CohomologyClass.mk _
  exact congrArg CohomologyClass.mk (coextensionCocycleEquiv_precomp φ f K n x)

lemma injectiveResolution_extAddEquiv_precomp {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{v} C] {A : Type*} [Ring A] [Linear A C]
    {X X' Y : C} (I : InjectiveResolution Y) (f : X ⟶ X') (n : ℕ)
    (x : Ext X' Y n) :
    I.extAddEquivCohomologyClass ((Ext.mk₀ f).comp x (zero_add n)) =
      classPrecomp (A := A) ((singleFunctor C 0).map f) n
        (I.extAddEquivCohomologyClass x) := by
  obtain ⟨g, hg, rfl⟩ := I.extMk_surjective x (n+1) rfl
  change I.extEquivCohomologyClass ((Ext.mk₀ f).comp (I.extMk g (n+1) rfl hg) (zero_add n)) =
    classPrecomp (A := A) ((singleFunctor C 0).map f) n
      (I.extEquivCohomologyClass (I.extMk g (n+1) rfl hg))
  simp only [I.mk₀_comp_extMk, I.extEquivCohomologyClass_extMk, classPrecomp_mk]
  congr 1
  rw [← Cocycle.fromSingleMk_precomp]
  simp only [Category.assoc]

lemma extCoextensionClassEquiv_precomp (φ : S →+* R) {M M' : ModuleCat.{u} R}
    (f : M ⟶ M') {N : ModuleCat.{u} S} (I : InjectiveResolution N) (n : ℕ)
    (x : Ext ((ModuleCat.restrictScalars φ).obj M') N n) :
    extCoextensionClassEquiv φ M I n
      ((Ext.mk₀ ((ModuleCat.restrictScalars φ).map f)).comp x (zero_add n)) =
      classPrecomp (A := R) ((singleFunctor (ModuleCat R) 0).map f) n
        (extCoextensionClassEquiv φ M' I n x) := by
  unfold extCoextensionClassEquiv
  simp only [AddEquiv.trans_apply]
  rw [injectiveResolution_extAddEquiv_precomp (A := S)]
  exact coextensionClassEquiv_precomp φ f I.cochainComplex n _

/-- Derived coextension is R-linear for the actual first-argument action. -/
def extCoextensionClassLinearEquiv (φ : S →+* R) (M : ModuleCat.{u} R)
    {N : ModuleCat.{u} S} (I : InjectiveResolution N) (n : ℕ) :
    FirstExt φ M N n ≃ₗ[R]
      CohomologyClass ((singleFunctor (ModuleCat R) 0).obj M) (coextensionComplex φ I) n where
  toAddEquiv := (firstExtAddEquiv φ M N n).trans (extCoextensionClassEquiv φ M I n)
  map_smul' r x := by
    change extCoextensionClassEquiv φ M I n
      ((Ext.mk₀ ((ModuleCat.restrictScalars φ).map (r • 𝟙 M))).comp x (zero_add n)) = _
    rw [extCoextensionClassEquiv_precomp]
    simp only [Functor.map_smul, CategoryTheory.Functor.map_id]
    change classPrecomp (A := R) (r • 𝟙 _) (n : ℤ)
        (extCoextensionClassEquiv φ M I n x) =
      r • extCoextensionClassEquiv φ M I n x
    exact classPrecomp_smul_id r (n : ℤ) _

lemma extCoextensionClassLinearEquiv_precomp (φ : S →+* R) {M M' : ModuleCat.{u} R}
    (f : M ⟶ M') {N : ModuleCat.{u} S} (I : InjectiveResolution N) (n : ℕ)
    (x : FirstExt φ M' N n) :
    extCoextensionClassLinearEquiv φ M I n (firstExtPullback φ f N n x) =
      classPrecomp (A := R) ((singleFunctor (ModuleCat R) 0).map f) n
        (extCoextensionClassLinearEquiv φ M' I n x) :=
  extCoextensionClassEquiv_precomp φ f I n x


variable {S R : Type u} [CommRing S] [CommRing R]

def regularCochainEquiv (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Cochain ((CochainComplex.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) K n ≃ₗ[R] K.X n :=
  (Cochain.fromSingleLinearEquiv (zero_add n)).trans
    ((ModuleCat.homLinearEquiv).trans (LinearMap.ringLmapEquivSelf R R (K.X n)))

@[simp] lemma regularCochainEquiv_fromSingleMk (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) (f : ModuleCat.of R R ⟶ K.X n) :
    regularCochainEquiv K n (Cochain.fromSingleMk f (zero_add n)) = f 1 := by
  simp [regularCochainEquiv]
  rfl

lemma regularCochainEquiv_δ (K : CochainComplex (ModuleCat.{u} R) ℤ) (n m : ℤ)
    (x : Cochain ((CochainComplex.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) K n) :
    regularCochainEquiv K m (δ n m x) = K.d n m (regularCochainEquiv K n x) := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective x n (zero_add n)
  simp only [Cochain.δ_fromSingleMk _ _ _ m (zero_add m),
    regularCochainEquiv_fromSingleMk]
  rfl

def regularHomComplexIso (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    linearHomComplex R ((CochainComplex.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) K ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (regularCochainEquiv K n).toModuleIso)
    (by intro n m h; ext x; exact (regularCochainEquiv_δ K n m x).symm)

/-- Evaluation on the regular module computes actual module homology. -/
def regularHomologyEquiv (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    K.homology n ≃ₗ[R] CohomologyClass
      ((CochainComplex.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) K n :=
  ((HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) n).mapIso
    (regularHomComplexIso K).symm).toLinearEquiv |>.trans
    (homologyLinearEquiv R _ K n)

lemma coextensionComplex_isZero_homology (φ : S →+* R) {N : ModuleCat.{u} S}
    (I : InjectiveResolution N) (c : ℕ) (h : Concentrated φ N c)
    (n : ℤ) (hn : n ≠ (c : ℤ)) :
    Limits.IsZero ((coextensionComplex φ I).homology n) := by
  by_cases hneg : n < 0
  · exact (coextensionComplex φ I).isZero_of_isGE 0 n hneg
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    have hm : m ≠ c := by omega
    have hsub := h m hm
    have hclass : Subsingleton (CohomologyClass
        ((CochainComplex.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))
          (coextensionComplex φ I) m) :=
      (extCoextensionClassEquiv φ (ModuleCat.of R R) I m).surjective.subsingleton
    exact ModuleCat.isZero_iff_subsingleton.mpr
      ((regularHomologyEquiv (coextensionComplex φ I) m).injective.subsingleton)

/-- The degree-c homology of derived coextension is the actual coefficient Ext,
with the action through the regular first argument. -/
def coextensionHomologyIso (φ : S →+* R) {N : ModuleCat.{u} S}
    (I : InjectiveResolution N) (c : ℕ) :
    (coextensionComplex φ I).homology c ≅ coefficient φ N c :=
  ((regularHomologyEquiv (coextensionComplex φ I) c).trans
    (extCoextensionClassLinearEquiv φ (ModuleCat.of R R) I c).symm).toModuleIso


variable {S R : Type u} [CommRing S] [CommRing R]

def coefficientExtLinearEquiv {Y Z : ModuleCat.{u} R} (e : Y ≅ Z)
    (M : ModuleCat.{u} R) (i : ℕ) : Ext M Y i ≃ₗ[R] Ext M Z i :=
  ((linearExtFunctorObj R M i).mapIso e).toLinearEquiv

lemma coefficientExtLinearEquiv_naturality {Y Z : ModuleCat.{u} R} (e : Y ≅ Z)
    {M M' : ModuleCat.{u} R} (f : M ⟶ M') (i : ℕ) (x : Ext M' Y i) :
    coefficientExtLinearEquiv e M i ((Ext.mk₀ f).comp x (zero_add i)) =
      (Ext.mk₀ f).comp (coefficientExtLinearEquiv e M' i x) (zero_add i) := by
  change ((Ext.mk₀ f).comp x (zero_add i)).comp (Ext.mk₀ e.hom) (add_zero i) =
    (Ext.mk₀ f).comp (x.comp (Ext.mk₀ e.hom) (add_zero i)) (zero_add i)
  exact Ext.comp_assoc _ _ _ (zero_add i) (add_zero i) (by omega)

def comparisonOfNaturalEquivs (φ : S →+* R) (N : ModuleCat.{u} S) (c i : ℕ)
    (e : ∀ M : ModuleCat.{u} R,
      Ext M (coefficient φ N c) i ≃ₗ[R] FirstExt φ M N (i+c))
    (he : ∀ {M M' : ModuleCat.{u} R} (f : M ⟶ M')
      (x : Ext M' (coefficient φ N c) i),
      e M ((Ext.mk₀ f).comp x (zero_add i)) =
        firstExtPullback φ f N (i+c) (e M' x)) :
    coefficientExtFunctor φ N c i ≅ shiftedExtFunctor φ N c i :=
  NatIso.ofComponents (fun M => (e M.unop).toModuleIso) (by
    intro M M' f
    ext x
    exact he f.unop x)

variable {R : Type u} [CommRing R]

-- Conversion from actual cohomology classes to derived morphisms.
def classHomotopyLinearEquiv (A K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    CohomologyClass A K n ≃ₗ[R]
      ((HomotopyCategory.quotient _ _).obj A ⟶
        (HomotopyCategory.quotient _ _).obj (K⟦n⟧)) where
  toAddEquiv := CohomologyClass.homAddEquiv
  map_smul' r x := by
    induction x using CohomologyClass.rec with
    | mk z =>
      change CohomologyClass.toHom (r • CohomologyClass.mk z) =
        r • CohomologyClass.toHom (CohomologyClass.mk z)
      rw [← CohomologyClass.mk_smul, CohomologyClass.toHom_mk,
        CohomologyClass.toHom_mk, Cocycle.equivHomShift_symm_smul, Functor.map_smul]

def classDerivedLinearEquiv [HasDerivedCategory (ModuleCat.{u} R)]
    (A K : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKInjective] (n : ℤ) :
    CohomologyClass A K n ≃ₗ[R]
      (DerivedCategory.Q.obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :=
  (classHomotopyLinearEquiv A K n).trans
    ((LinearEquiv.ofBijective (DerivedCategory.Qh.mapLinearMap R)
      (CochainComplex.IsKInjective.Qh_map_bijective _ _)).trans
      (Linear.homCongr R ((DerivedCategory.quotientCompQhIso _).app A)
        (((DerivedCategory.quotientCompQhIso _).app (K⟦n⟧)) ≪≫
          (DerivedCategory.Q.commShiftIso n).app K)))

lemma classDerivedLinearEquiv_mk [HasDerivedCategory (ModuleCat.{u} R)]
    (A K : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKInjective] (n : ℤ)
    (z : Cocycle A K n) :
    classDerivedLinearEquiv A K n (CohomologyClass.mk z) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app K := by
  dsimp only [classDerivedLinearEquiv, LinearEquiv.trans_apply,
    classHomotopyLinearEquiv,
    LinearEquiv.coe_mk, AddEquiv.coe_mk, Linear.homCongr_apply]
  change ((DerivedCategory.quotientCompQhIso _).inv.app A ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      (Cocycle.equivHomShift.symm z))) ≫ _ = _
  simp only [Iso.trans_hom, Category.assoc,
    ← DerivedCategory.quotientCompQhIso_inv_naturality,
    Iso.app_hom, Iso.inv_hom_id_app_assoc]


lemma classDerivedLinearEquiv_precomp [HasDerivedCategory (ModuleCat.{u} R)]
    {A B K : CochainComplex (ModuleCat.{u} R) ℤ} [K.IsKInjective]
    (f : A ⟶ B) (n : ℤ) (x : CohomologyClass B K n) :
    classDerivedLinearEquiv A K n (classPrecomp (A := R) f n x) =
      DerivedCategory.Q.map f ≫ classDerivedLinearEquiv B K n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [classPrecomp_mk, classDerivedLinearEquiv_mk,
    classDerivedLinearEquiv_mk, Cocycle.equivHomShift_symm_precomp, Functor.map_comp,
    Category.assoc]

-- The target identification is fixed independently of M.
def concentratedShiftIso [HasDerivedCategory (ModuleCat.{u} R)]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (c : ℕ)
    (e : DerivedCategory.Q.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) c).obj (K.homology c))
    (i : ℕ) :
    (DerivedCategory.Q.obj K)⟦((i+c : ℕ) : ℤ)⟧ ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (K.homology c))⟦(i:ℤ)⟧ :=
  (CategoryTheory.shiftFunctor _ ((i+c:ℕ):ℤ)).mapIso e ≪≫
    ((CategoryTheory.shiftFunctorAdd' _ (c:ℤ) (i:ℤ) ((i+c:ℕ):ℤ) (by omega)).app _ ) ≪≫
    (CategoryTheory.shiftFunctor _ (i:ℤ)).mapIso
      (((DerivedCategory.singleFunctors (ModuleCat.{u} R)).shiftIso (c:ℤ) 0 c
        (by simp)).app (K.homology c))

def concentratedExtClassLinearEquiv [HasDerivedCategory (ModuleCat.{u} R)]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKInjective] (c : ℕ)
    (e : DerivedCategory.Q.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) c).obj (K.homology c))
    (i : ℕ) (M : ModuleCat.{u} R) :
    Ext M (K.homology c) i ≃ₗ[R]
      CohomologyClass ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)
        K ((i+c:ℕ):ℤ) :=
  (Ext.homLinearEquiv (R := R)).trans
    ((Linear.homCongr R (Iso.refl _) (concentratedShiftIso K c e i).symm).trans
      (classDerivedLinearEquiv _ K ((i+c:ℕ):ℤ)).symm)

lemma classDerivedLinearEquiv_concentratedExtClassLinearEquiv
    [HasDerivedCategory (ModuleCat.{u} R)]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKInjective] (c : ℕ)
    (e : DerivedCategory.Q.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) c).obj (K.homology c))
    (i : ℕ) (M : ModuleCat.{u} R) (x : Ext M (K.homology c) i) :
    classDerivedLinearEquiv ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)
      K ((i+c:ℕ):ℤ) (concentratedExtClassLinearEquiv K c e i M x) =
        x.hom ≫ (concentratedShiftIso K c e i).inv := by
  simp only [concentratedExtClassLinearEquiv, LinearEquiv.trans_apply,
    Linear.homCongr_apply, Iso.refl_inv, Category.id_comp]
  change (classDerivedLinearEquiv
    ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj M)
    K ((i+c:ℕ):ℤ))
      ((classDerivedLinearEquiv
        ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj M)
        K ((i+c:ℕ):ℤ)).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg (fun a => a ≫ (concentratedShiftIso K c e i).inv)
    (Ext.homLinearEquiv_apply x)

lemma concentratedExtClassLinearEquiv_precomp [HasDerivedCategory (ModuleCat.{u} R)]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) [K.IsKInjective] (c : ℕ)
    (e : DerivedCategory.Q.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) c).obj (K.homology c))
    (i : ℕ) {M M' : ModuleCat.{u} R} (f : M ⟶ M')
    (x : Ext M' (K.homology c) i) :
    concentratedExtClassLinearEquiv K c e i M ((Ext.mk₀ f).comp x (zero_add i)) =
      classPrecomp (A := R) ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map f)
        ((i+c:ℕ):ℤ) (concentratedExtClassLinearEquiv K c e i M' x) := by
  apply (classDerivedLinearEquiv _ K ((i+c:ℕ):ℤ)).injective
  rw [classDerivedLinearEquiv_precomp]
  rw [classDerivedLinearEquiv_concentratedExtClassLinearEquiv,
    classDerivedLinearEquiv_concentratedExtClassLinearEquiv,
    Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp, Category.assoc]
  rfl


/-- The natural R-linear concentrated change-of-rings comparison. -/
theorem comparison : Specs.AdvCommAlg.Gorenstein.ConcentratedChangeOfRings.comparison.{u} := by
  intro S R _ _ φ N c h i
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let I := injectiveResolution N
  let J := coextensionComplex φ I
  obtain ⟨e⟩ := exists_iso_single_homology.{u, u+1} J (c : ℤ)
    (coextensionComplex_isZero_homology φ I c h)
  let a := coextensionHomologyIso φ I c
  let E (M : ModuleCat.{u} R) :=
    (coefficientExtLinearEquiv a.symm M i).trans
      ((concentratedExtClassLinearEquiv J c e i M).trans
        (extCoextensionClassLinearEquiv φ M I (i+c)).symm)
  refine ⟨comparisonOfNaturalEquivs φ N c i E ?_⟩
  intro M M' f x
  apply (extCoextensionClassLinearEquiv φ M I (i+c)).injective
  rw [extCoextensionClassLinearEquiv_precomp]
  simp only [E, LinearEquiv.trans_apply]
  rw [coefficientExtLinearEquiv_naturality, concentratedExtClassLinearEquiv_precomp]
  exact ((extCoextensionClassLinearEquiv φ M I (i+c)).apply_symm_apply _).trans
    (congrArg (classPrecomp (A := R) ((CochainComplex.singleFunctor (ModuleCat R) 0).map f)
      ((i+c : ℕ) : ℤ))
        ((extCoextensionClassLinearEquiv φ M' I (i+c)).apply_symm_apply _)).symm

/-- Vanishing below the concentration degree. -/
theorem vanishing : Specs.AdvCommAlg.Gorenstein.ConcentratedChangeOfRings.vanishing := by
  intro S R _ _ φ N c h M j hj
  induction j generalizing M with
  | zero => exact vanishing_zero φ N c h hj M
  | succ j ih =>
    let P := Projective.over M
    let π : P ⟶ M := Projective.π M
    let T := ShortComplex.mk (Limits.kernel.ι π) π (Limits.kernel.condition π)
    have hT : T.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (Limits.kernelIsKernel π) }
    have hres : (T.map (ModuleCat.restrictScalars φ)).ShortExact := hT.map _
    have hP := vanishing_projective φ N P j (h (j+1) (Nat.ne_of_lt hj))
    have hK := ih T.X₁ (Nat.lt_of_succ_lt hj)
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₃ hres N x
      (hP.elim _ _) (n₀ := j) (by omega)
    rw [hK.elim y 0] at hy
    simpa using hy.symm

end AdvCommAlg.Gorenstein.ConcentratedChangeOfRings
