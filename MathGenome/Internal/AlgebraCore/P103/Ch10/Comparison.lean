import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.Comparison
import MathGenome.Internal.AlgebraCore.P103.Ch10.HomotopyAndContraction
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.Exact

namespace P103.Ch10.Comparison
open CategoryTheory CategoryTheory.Limits
open P103.Specs.Ch10.Comparison
noncomputable section
universe u v w x y
variable {R : Type u} [Ring R]

/-- Lift through an exact pair, with no projectivity assumption on its terms. -/
theorem exists_liftExact {X : Type v} {Y : Type w} {Z : Type x} {P : Type y}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] [AddCommGroup P] [Module R P]
    [Module.Projective R P] (a : X →ₗ[R] Y) (b : Y →ₗ[R] Z)
    (he : LinearMap.range a = LinearMap.ker b) (g : P →ₗ[R] Y)
    (hg : b.comp g = 0) : ∃ f : P →ₗ[R] X, a.comp f = g := by
  let a' : X →ₗ[R] LinearMap.ker b := a.codRestrict _ (by
    intro x
    rw [← he]
    exact ⟨x, rfl⟩)
  let g' : P →ₗ[R] LinearMap.ker b := g.codRestrict _ (by
    intro p
    exact LinearMap.congr_fun hg p)
  have ha : Function.Surjective a' := by
    intro z
    obtain ⟨x, hx⟩ := (show z.val ∈ LinearMap.range a from by rw [he]; exact z.property)
    exact ⟨x, Subtype.ext hx⟩
  obtain ⟨f, hf⟩ := Module.projective_lifting_property a' g' ha
  exact ⟨f, LinearMap.ext (fun p => congrArg Subtype.val (LinearMap.congr_fun hf p))⟩

def liftExact {X : Type v} {Y : Type w} {Z : Type x} {P : Type y}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] [AddCommGroup P] [Module R P]
    [Module.Projective R P] (a : X →ₗ[R] Y) (b : Y →ₗ[R] Z)
    (he : LinearMap.range a = LinearMap.ker b) (g : P →ₗ[R] Y)
    (hg : b.comp g = 0) : P →ₗ[R] X := (exists_liftExact a b he g hg).choose

@[simp] theorem liftExact_comp {X : Type v} {Y : Type w} {Z : Type x} {P : Type y}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] [AddCommGroup P] [Module R P]
    [Module.Projective R P] (a : X →ₗ[R] Y) (b : Y →ₗ[R] Z)
    (he : LinearMap.range a = LinearMap.ker b) (g : P →ₗ[R] Y)
    (hg : b.comp g = 0) : a.comp (liftExact a b he g hg) = g :=
  (exists_liftExact a b he g hg).choose_spec

variable {A B : Type v} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- The first augmentation annihilates the first differential. -/
theorem augmentation_square (P : LeftResolution R A) :
    P.ε.comp (P.complex.d 1 0).hom = 0 := by
  ext x
  exact (show (P.complex.d 1 0).hom x ∈ LinearMap.ker P.ε from
    P.exact_zero ▸ (show (P.complex.d 1 0).hom x ∈ LinearMap.range _ from ⟨x, rfl⟩))

/-- Exactness of the adjacent positive-degree pair in the categorical API. -/
theorem chain_exact (Q : LeftResolution R B) (n : ℕ) :
    (ShortComplex.mk _ _ (Q.complex.d_comp_d (n + 2) (n + 1) n)).Exact :=
  (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr (Q.exact_succ n)

section Chain
variable (P : LeftResolution R A) (Q : LeftResolution R B) (hP : P.IsProjective)
include hP

private def chainZero (u : A →ₗ[R] B) : P.complex.X 0 →ₗ[R] Q.complex.X 0 := by
  letI := hP 0
  exact (Module.projective_lifting_property Q.ε (u.comp P.ε) Q.surjective).choose

private theorem chainZero_comp (u : A →ₗ[R] B) :
    Q.ε.comp (chainZero P Q hP u) = u.comp P.ε := by
  let := hP 0
  unfold chainZero
  exact (Module.projective_lifting_property Q.ε (u.comp P.ε) Q.surjective).choose_spec

private def chainOne (u : A →ₗ[R] B) : P.complex.X 1 →ₗ[R] Q.complex.X 1 := by
  letI := hP 1
  exact liftExact (Q.complex.d 1 0).hom Q.ε Q.exact_zero
    ((chainZero P Q hP u).comp (P.complex.d 1 0).hom) (by
      rw [← LinearMap.comp_assoc, chainZero_comp, LinearMap.comp_assoc, augmentation_square,
        LinearMap.comp_zero])

private theorem chainOne_comp (u : A →ₗ[R] B) :
    ModuleCat.ofHom (chainOne P Q hP u) ≫ Q.complex.d 1 0 =
      P.complex.d 1 0 ≫ ModuleCat.ofHom (chainZero P Q hP u) := by
  let := hP 1
  apply ModuleCat.hom_ext
  unfold chainOne
  apply liftExact_comp (Q.complex.d 1 0).hom Q.ε Q.exact_zero
  rw [← LinearMap.comp_assoc, chainZero_comp, LinearMap.comp_assoc, augmentation_square,
    LinearMap.comp_zero]

private def chainSucc (n : ℕ)
    (g : P.complex.X n ⟶ Q.complex.X n)
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 1))
    (h : g' ≫ Q.complex.d (n + 1) n = P.complex.d (n + 1) n ≫ g) :
    Σ' g'' : P.complex.X (n + 2) ⟶ Q.complex.X (n + 2),
      g'' ≫ Q.complex.d (n + 2) (n + 1) = P.complex.d (n + 2) (n + 1) ≫ g' := by
  letI := hP (n + 2)
  exact ⟨(chain_exact Q n).liftFromProjective
    (P.complex.d (n + 2) (n + 1) ≫ g') (by simp [h]),
      (chain_exact Q n).liftFromProjective_comp _ _⟩

/-- An actual comparison chain map, for an arbitrary exact target resolution. -/
def chainMap (u : A →ₗ[R] B) : P.complex ⟶ Q.complex :=
  ChainComplex.mkHom _ _ (ModuleCat.ofHom (chainZero P Q hP u))
    (ModuleCat.ofHom (chainOne P Q hP u)) (chainOne_comp P Q hP u)
    (fun n ⟨g, g', h⟩ => chainSucc P Q hP n g g' h)

theorem chainMap_lifts (u : A →ₗ[R] B) : ChainLift P Q u (chainMap P Q hP u) :=
  chainZero_comp P Q hP u

end Chain

theorem chain_exists : chain_existsType.{u,v} := by
  intro R _ A B _ _ _ _ P Q hP u
  exact ⟨chainMap P Q hP u, chainMap_lifts P Q hP u⟩

section ChainUniqueness
variable (P : LeftResolution R A) (Q : LeftResolution R B) (hP : P.IsProjective)
variable (f : P.complex ⟶ Q.complex) (hf : Q.ε.comp (f.f 0).hom = 0)

private def chainHomZero : P.complex.X 0 ⟶ Q.complex.X 1 := by
  letI := hP 0
  exact ModuleCat.ofHom (liftExact (Q.complex.d 1 0).hom Q.ε Q.exact_zero (f.f 0).hom hf)

@[simp] private theorem chainHomZero_comp :
    chainHomZero P Q hP f hf ≫ Q.complex.d 1 0 = f.f 0 := by
  let := hP 0
  apply ModuleCat.hom_ext
  unfold chainHomZero
  apply liftExact_comp (Q.complex.d 1 0).hom Q.ε Q.exact_zero
  exact hf

private def chainHomOne : P.complex.X 1 ⟶ Q.complex.X 2 := by
  letI := hP 1
  exact (chain_exact Q 0).liftFromProjective
    (f.f 1 - P.complex.d 1 0 ≫ chainHomZero P Q hP f hf) (by
      rw [Preadditive.sub_comp, Category.assoc, chainHomZero_comp,
        HomologicalComplex.Hom.comm, sub_self])

@[simp] private theorem chainHomOne_comp :
    chainHomOne P Q hP f hf ≫ Q.complex.d 2 1 =
      f.f 1 - P.complex.d 1 0 ≫ chainHomZero P Q hP f hf := by
  let := hP 1
  exact (chain_exact Q 0).liftFromProjective_comp _ _

private def chainHomSucc (n : ℕ)
    (g : P.complex.X n ⟶ Q.complex.X (n + 1))
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2))
    (h : f.f (n + 1) = P.complex.d (n + 1) n ≫ g +
      g' ≫ Q.complex.d (n + 2) (n + 1)) :
    Σ' g'' : P.complex.X (n + 2) ⟶ Q.complex.X (n + 3),
      f.f (n + 2) = P.complex.d (n + 2) (n + 1) ≫ g' +
        g'' ≫ Q.complex.d (n + 3) (n + 2) := by
  letI := hP (n + 2)
  let g'' := (chain_exact Q (n + 1)).liftFromProjective
    (f.f (n + 2) - P.complex.d (n + 2) (n + 1) ≫ g') (by simp [h])
  refine ⟨g'', ?_⟩
  dsimp [g'']
  rw [ShortComplex.Exact.liftFromProjective_comp, add_sub_cancel]

/-- Any augmented lift of zero is nullhomotopic, without projectivity of Q. -/
def chainNullHomotopy : Homotopy f 0 :=
  Homotopy.mkInductive f (chainHomZero P Q hP f hf) (by simp)
    (chainHomOne P Q hP f hf) (by simp)
    (fun n ⟨g, g', h⟩ => chainHomSucc P Q hP f n g g' h)

end ChainUniqueness

theorem chain_unique : chain_uniqueType.{u,v} := by
  intro R _ A B _ _ _ _ P Q hP u f g hf hg
  refine ⟨Homotopy.equivSubZero.invFun (chainNullHomotopy P Q hP (f - g) ?_)⟩
  change Q.ε.comp ((f.f 0).hom - (g.f 0).hom) = 0
  rw [LinearMap.comp_sub, hf, hg, sub_self]

/-- The source augmentation lifted only to put all objects in one category. -/
def coaugmentation (J : RightResolution R A) :
    ModuleCat.of R (ULift.{u} A) ⟶ J.complex.X 0 :=
  ModuleCat.ofHom (J.η.comp (ULift.moduleEquiv : ULift.{u} A ≃ₗ[R] A).toLinearMap)

theorem coaugmentation_square (J : RightResolution R A) :
    coaugmentation J ≫ J.complex.d 0 1 = 0 := by
  ext x
  exact J.exact_zero.apply_apply_eq_zero x.down

theorem cochain_exact_zero (J : RightResolution R A) :
    (ShortComplex.mk _ _ (coaugmentation_square J)).Exact := by
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  exact (ULift.moduleEquiv : ULift.{u} A ≃ₗ[R] A).surjective.comp_exact_iff_exact.mpr
    J.exact_zero

theorem cochain_exact (J : RightResolution R A) (n : ℕ) :
    (ShortComplex.mk _ _ (J.complex.d_comp_d n (n + 1) (n + 2))).Exact := by
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  exact J.exact_succ n

section Cochain
variable (J : RightResolution R A) (I : InjectiveResolution R B)

private def cochainZero (u : A →ₗ[R] B) : J.complex.X 0 →ₗ[R] I.complex.X 0 := by
  letI := I.injectiveTerm 0
  exact (Module.Injective.extension_property R (I.complex.X 0) A (J.complex.X 0)
    J.η J.injective_η (I.η.comp u)).choose

private theorem cochainZero_comp (u : A →ₗ[R] B) :
    (cochainZero J I u).comp J.η = I.η.comp u := by
  let := I.injectiveTerm 0
  exact (Module.Injective.extension_property R (I.complex.X 0) A (J.complex.X 0)
    J.η J.injective_η (I.η.comp u)).choose_spec

private def cochainOne (u : A →ₗ[R] B) : J.complex.X 1 ⟶ I.complex.X 1 := by
  letI := Module.injective_object_of_injective_module R (I.complex.X 1)
    (inj := I.injectiveTerm 1)
  exact (cochain_exact_zero J).descToInjective
    (ModuleCat.ofHom (cochainZero J I u) ≫ I.complex.d 0 1) (by
      ext x
      change (I.complex.d 0 1).hom (cochainZero J I u (J.η x.down)) = 0
      rw [show cochainZero J I u (J.η x.down) = I.η (u x.down) from
        LinearMap.congr_fun (cochainZero_comp J I u) x.down]
      exact I.exact_zero.apply_apply_eq_zero _)

private theorem cochainOne_comp (u : A →ₗ[R] B) :
    J.complex.d 0 1 ≫ cochainOne J I u =
      ModuleCat.ofHom (cochainZero J I u) ≫ I.complex.d 0 1 := by
  let := Module.injective_object_of_injective_module R (I.complex.X 1)
    (inj := I.injectiveTerm 1)
  exact (cochain_exact_zero J).comp_descToInjective _ _

private def cochainSucc (n : ℕ)
    (g : J.complex.X n ⟶ I.complex.X n)
    (g' : J.complex.X (n + 1) ⟶ I.complex.X (n + 1))
    (h : g ≫ I.complex.d n (n + 1) = J.complex.d n (n + 1) ≫ g') :
    Σ' g'' : J.complex.X (n + 2) ⟶ I.complex.X (n + 2),
      g' ≫ I.complex.d (n + 1) (n + 2) = J.complex.d (n + 1) (n + 2) ≫ g'' := by
  letI := Module.injective_object_of_injective_module R (I.complex.X (n + 2))
    (inj := I.injectiveTerm (n + 2))
  exact ⟨(cochain_exact J n).descToInjective
    (g' ≫ I.complex.d (n + 1) (n + 2)) (by rw [← Category.assoc, ← h]; simp),
    ((cochain_exact J n).comp_descToInjective _ _).symm⟩

/-- Comparison cochain map from an arbitrary exact right resolution. -/
def cochainMap (u : A →ₗ[R] B) : J.complex ⟶ I.complex :=
  CochainComplex.mkHom _ _ (ModuleCat.ofHom (cochainZero J I u))
    (cochainOne J I u) (cochainOne_comp J I u).symm
    (fun n ⟨g, g', h⟩ => cochainSucc J I n g g' h)

theorem cochainMap_lifts (u : A →ₗ[R] B) : CochainLift J I u (cochainMap J I u) :=
  cochainZero_comp J I u

end Cochain

theorem cochain_exists : cochain_existsType.{u,v} := by
  intro R _ A B _ _ _ _ J I u
  exact ⟨cochainMap J I u, cochainMap_lifts J I u⟩

section CochainUniqueness
variable (J : RightResolution R A) (I : InjectiveResolution R B)
variable (f : J.complex ⟶ I.complex) (hf : (f.f 0).hom.comp J.η = 0)

private def cochainHomZero : J.complex.X 1 ⟶ I.complex.X 0 := by
  letI := Module.injective_object_of_injective_module R (I.complex.X 0)
    (inj := I.injectiveTerm 0)
  exact (cochain_exact_zero J).descToInjective (f.f 0) (by
    ext x
    exact LinearMap.congr_fun hf x.down)

@[simp] private theorem cochainHomZero_comp :
    J.complex.d 0 1 ≫ cochainHomZero J I f hf = f.f 0 := by
  let := Module.injective_object_of_injective_module R (I.complex.X 0)
    (inj := I.injectiveTerm 0)
  exact (cochain_exact_zero J).comp_descToInjective _ _

private def cochainHomOne : J.complex.X 2 ⟶ I.complex.X 1 := by
  letI := Module.injective_object_of_injective_module R (I.complex.X 1)
    (inj := I.injectiveTerm 1)
  exact (cochain_exact J 0).descToInjective
    (f.f 1 - cochainHomZero J I f hf ≫ I.complex.d 0 1) (by
      rw [Preadditive.comp_sub, ← Category.assoc, cochainHomZero_comp,
        HomologicalComplex.Hom.comm, sub_self])

@[simp] private theorem cochainHomOne_comp :
    J.complex.d 1 2 ≫ cochainHomOne J I f hf =
      f.f 1 - cochainHomZero J I f hf ≫ I.complex.d 0 1 := by
  let := Module.injective_object_of_injective_module R (I.complex.X 1)
    (inj := I.injectiveTerm 1)
  exact (cochain_exact J 0).comp_descToInjective _ _

private def cochainHomSucc (n : ℕ)
    (g : J.complex.X (n + 1) ⟶ I.complex.X n)
    (g' : J.complex.X (n + 2) ⟶ I.complex.X (n + 1))
    (h : f.f (n + 1) = g ≫ I.complex.d n (n + 1) +
      J.complex.d (n + 1) (n + 2) ≫ g') :
    Σ' g'' : J.complex.X (n + 3) ⟶ I.complex.X (n + 2),
      f.f (n + 2) = g' ≫ I.complex.d (n + 1) (n + 2) +
        J.complex.d (n + 2) (n + 3) ≫ g'' := by
  letI := Module.injective_object_of_injective_module R (I.complex.X (n + 2))
    (inj := I.injectiveTerm (n + 2))
  have hz : J.complex.d (n + 1) (n + 2) ≫
      (f.f (n + 2) - g' ≫ I.complex.d (n + 1) (n + 2)) = 0 := by
    rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, h,
      Preadditive.add_comp, Category.assoc, Category.assoc,
      HomologicalComplex.d_comp_d, comp_zero, zero_add, sub_self]
  let g'' := (cochain_exact J (n + 1)).descToInjective
    (f.f (n + 2) - g' ≫ I.complex.d (n + 1) (n + 2)) hz
  refine ⟨g'', ?_⟩
  have he := (cochain_exact J (n + 1)).comp_descToInjective
    (f.f (n + 2) - g' ≫ I.complex.d (n + 1) (n + 2)) hz
  change J.complex.d (n + 2) (n + 3) ≫ g'' = _ at he
  rw [he, add_sub_cancel]

/-- Augmented zero maps are nullhomotopic with no injectivity of J. -/
def cochainNullHomotopy : Homotopy f 0 :=
  Homotopy.mkCoinductive f (cochainHomZero J I f hf) (by simp)
    (cochainHomOne J I f hf) (by simp)
    (fun n ⟨g, g', h⟩ => cochainHomSucc J I f n g g' h)

end CochainUniqueness

theorem cochain_unique : cochain_uniqueType.{u,v} := by
  intro R _ A B _ _ _ _ J I u f g hf hg
  refine ⟨Homotopy.equivSubZero.invFun (cochainNullHomotopy J I (f - g) ?_)⟩
  change ((f.f 0).hom - (g.f 0).hom).comp J.η = 0
  rw [LinearMap.sub_comp, hf, hg, sub_self]

variable {C : Type v} [AddCommGroup C] [Module R C]

theorem chainLift_id (P : LeftResolution R A) : ChainLift P P LinearMap.id (𝟙 P.complex) := by
  simp [ChainLift]

theorem chainLift_comp {P : LeftResolution R A} {Q : LeftResolution R B}
    {T : LeftResolution R C} {u : A →ₗ[R] B} {v : B →ₗ[R] C}
    {f : P.complex ⟶ Q.complex} {g : Q.complex ⟶ T.complex}
    (hf : ChainLift P Q u f) (hg : ChainLift Q T v g) :
    ChainLift P T (v.comp u) (f ≫ g) := by
  change T.ε.comp ((g.f 0).hom.comp (f.f 0).hom) = (v.comp u).comp P.ε
  rw [← LinearMap.comp_assoc, hg, LinearMap.comp_assoc, hf, ← LinearMap.comp_assoc]

theorem chainLift_add {P : LeftResolution R A} {Q : LeftResolution R B}
    {u v : A →ₗ[R] B} {f g : P.complex ⟶ Q.complex}
    (hf : ChainLift P Q u f) (hg : ChainLift P Q v g) : ChainLift P Q (u + v) (f + g) := by
  change Q.ε.comp ((f.f 0).hom + (g.f 0).hom) = (u + v).comp P.ε
  rw [LinearMap.comp_add, hf, hg, LinearMap.add_comp]

theorem cochainLift_id (I : InjectiveResolution R A) :
    CochainLift (ofInjective I) I LinearMap.id (𝟙 I.complex) := by
  ext x
  rfl

theorem cochainLift_comp {J : RightResolution R A} {I : InjectiveResolution R B}
    {K : InjectiveResolution R C} {u : A →ₗ[R] B} {v : B →ₗ[R] C}
    {f : J.complex ⟶ I.complex} {g : I.complex ⟶ K.complex}
    (hf : CochainLift J I u f) (hg : CochainLift (ofInjective I) K v g) :
    CochainLift J K (v.comp u) (f ≫ g) := by
  change ((g.f 0).hom.comp (f.f 0).hom).comp J.η = K.η.comp (v.comp u)
  rw [LinearMap.comp_assoc, hf, ← LinearMap.comp_assoc]
  change (g.f 0).hom.comp I.η = K.η.comp v at hg
  rw [hg, LinearMap.comp_assoc]

theorem cochainLift_add {J : RightResolution R A} {I : InjectiveResolution R B}
    {u v : A →ₗ[R] B} {f g : J.complex ⟶ I.complex}
    (hf : CochainLift J I u f) (hg : CochainLift J I v g) :
    CochainLift J I (u + v) (f + g) := by
  change ((f.f 0).hom + (g.f 0).hom).comp J.η = I.η.comp (u + v)
  rw [LinearMap.add_comp, hf, hg, LinearMap.comp_add]

theorem projective_equiv : projective_equivType.{u,v} := by
  intro R _ A _ _ P Q hP hQ
  let f := chainMap P Q hP LinearMap.id
  let g := chainMap Q P hQ LinearMap.id
  have hf := chainMap_lifts P Q hP LinearMap.id
  have hg := chainMap_lifts Q P hQ LinearMap.id
  have hfg : ChainLift P P LinearMap.id (f ≫ g) := by
    simpa using chainLift_comp hf hg
  have hgf : ChainLift Q Q LinearMap.id (g ≫ f) := by
    simpa using chainLift_comp hg hf
  exact ⟨⟨f, g,
    (chain_unique R A A P P hP LinearMap.id _ _ hfg (chainLift_id P)).some,
    (chain_unique R A A Q Q hQ LinearMap.id _ _ hgf (chainLift_id Q)).some⟩, hf, hg⟩

theorem injective_equiv : injective_equivType.{u,v} := by
  intro R _ A _ _ I J
  let f := cochainMap (ofInjective I) J LinearMap.id
  let g := cochainMap (ofInjective J) I LinearMap.id
  have hf := cochainMap_lifts (ofInjective I) J LinearMap.id
  have hg := cochainMap_lifts (ofInjective J) I LinearMap.id
  have hfg : CochainLift (ofInjective I) I LinearMap.id (f ≫ g) := by
    simpa using cochainLift_comp hf hg
  have hgf : CochainLift (ofInjective J) J LinearMap.id (g ≫ f) := by
    simpa using cochainLift_comp hg hf
  exact ⟨⟨f, g,
    (cochain_unique R A A (ofInjective I) I LinearMap.id _ _ hfg (cochainLift_id I)).some,
    (cochain_unique R A A (ofInjective J) J LinearMap.id _ _ hgf (cochainLift_id J)).some⟩, hf, hg⟩

section Coherence
universe u₁ v₁ u₂ v₂ u₃ v₃ t
variable {D : Type u₁} [Category.{v₁} D] [Preadditive D]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E]
  {W : Type u₃} [Category.{v₃} W] [Preadditive W]

/-- Descent of lift maps to any additive homotopy invariant construction.
All coherence equations follow from uniqueness for the same augmented map. -/
theorem coherentComparison_of_lifts
    (I : D → Type t) (K : ∀ A, I A → E)
    (L : ∀ {A B} (P : I A) (Q : I B), (A ⟶ B) → (K A P ⟶ K B Q) → Prop)
    (H : E ⥤ W) [H.Additive]
    (exists_lift : ∀ {A B} (P : I A) (Q : I B) (u : A ⟶ B), ∃ f, L P Q u f)
    (unique_map : ∀ {A B} (P : I A) (Q : I B) (u : A ⟶ B) (f g : K A P ⟶ K B Q),
      L P Q u f → L P Q u g → H.map f = H.map g)
    (id_lift : ∀ A (P : I A), L P P (𝟙 A) (𝟙 (K A P)))
    (comp_lift : ∀ {A B C} (P : I A) (Q : I B) (T : I C) (u : A ⟶ B) (v : B ⟶ C)
      (f : K A P ⟶ K B Q) (g : K B Q ⟶ K C T),
      L P Q u f → L Q T v g → L P T (u ≫ v) (f ≫ g))
    (add_lift : ∀ {A B} (P : I A) (Q : I B) (u v : A ⟶ B) (f g : K A P ⟶ K B Q),
      L P Q u f → L P Q v g → L P Q (u + v) (f + g)) :
    Nonempty (CoherentComparison I K L H) := by
  classical
  let l : ∀ {A B} (P : I A) (Q : I B), (A ⟶ B) → (K A P ⟶ K B Q) :=
    fun P Q u => (exists_lift P Q u).choose
  have hl : ∀ {A B} (P : I A) (Q : I B) (u : A ⟶ B), L P Q u (l P Q u) :=
    fun P Q u => (exists_lift P Q u).choose_spec
  let m : ∀ {A B} (P : I A) (Q : I B), (A ⟶ B) → (H.obj (K A P) ⟶ H.obj (K B Q)) :=
    fun P Q u => H.map (l P Q u)
  have hm : ∀ {A B} (P : I A) (Q : I B) (u : A ⟶ B) (f : K A P ⟶ K B Q),
      L P Q u f → m P Q u = H.map f := by
    intro A B P Q u f hf
    exact unique_map P Q u _ _ (hl P Q u) hf
  have hi : ∀ A (P : I A), m P P (𝟙 A) = 𝟙 _ := by
    intro A P
    rw [hm P P (𝟙 A) (𝟙 _) (id_lift A P), H.map_id]
  have hc : ∀ {A B C} (P : I A) (Q : I B) (T : I C) (u : A ⟶ B) (v : B ⟶ C),
      m P T (u ≫ v) = m P Q u ≫ m Q T v := by
    intro A B C P Q T u v
    exact (hm P T (u ≫ v) _ (comp_lift P Q T u v _ _ (hl P Q u) (hl Q T v))).trans
      (H.map_comp _ _)
  have ha : ∀ {A B} (P : I A) (Q : I B) (u v : A ⟶ B),
      m P Q (u + v) = m P Q u + m P Q v := by
    intro A B P Q u v
    exact (hm P Q (u + v) _ (add_lift P Q u v _ _ (hl P Q u) (hl P Q v))).trans
      H.map_add
  let e : ∀ {A} (P Q : I A), H.obj (K A P) ≅ H.obj (K A Q) := fun {A} P Q =>
    { hom := m P Q (𝟙 A)
      inv := m Q P (𝟙 A)
      hom_inv_id := by rw [← hc, Category.id_comp, hi]
      inv_hom_id := by rw [← hc, Category.id_comp, hi] }
  refine ⟨{
    map := m
    map_eq := hm
    map_id := hi
    map_comp := hc
    map_add := ha
    comparison := e
    comparison_hom := fun _ _ => rfl
    comparison_inv := fun _ _ => rfl
    comparison_refl := ?_
    comparison_trans := ?_
    naturality := ?_ }⟩
  · intro A P
    apply Iso.ext
    exact hi A P
  · intro A P Q T
    apply Iso.ext
    change m P Q (𝟙 A) ≫ m Q T (𝟙 A) = m P T (𝟙 A)
    rw [← hc, Category.id_comp]
  · intro A B P P' Q Q' u
    change m P Q u ≫ m Q Q' (𝟙 B) = m P P' (𝟙 A) ≫ m P' Q' u
    rw [← hc, ← hc, Category.comp_id, Category.id_comp]

end Coherence

section Invariant
universe a b c d
variable {V : Type a} [Category.{b} V] [Preadditive V]
  {W : Type c} [Category.{d} W] [Preadditive W]

/-- Additive functors followed by explicit quotient homology are invariant
under homotopy. They need not preserve kernels, cokernels or exact sequences. -/
theorem appliedHomology_invariant {S : Type w} [Ring S] {ι : Type x}
    (F : V ⥤ ModuleCat.{y} S) [F.Additive] (c : ComplexShape ι) (n : ι)
    {K T : HomologicalComplex V c} {f g : K ⟶ T} (h : Homotopy f g) :
    (F.mapHomologicalComplex c ⋙ quotientHomology c n).map f =
      (F.mapHomologicalComplex c ⋙ quotientHomology c n).map g := by
  apply ModuleCat.hom_ext
  exact P103.Ch10.HomotopyAndContraction.homotopy_homologyMap (F.mapHomotopy h) n

/-- The opposite complex exchanges the chain and cochain directions. -/
theorem appliedContravariantHomology_invariant {S : Type w} [Ring S] {ι : Type x}
    (F : Vᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive] (c : ComplexShape ι) (n : ι)
    {K T : HomologicalComplex V c} {f g : K ⟶ T} (h : Homotopy f g) :
    ((HomologicalComplex.opFunctor V c ⋙ F.mapHomologicalComplex c.symm ⋙
      quotientHomology c.symm n).rightOp).map f =
    ((HomologicalComplex.opFunctor V c ⋙ F.mapHomologicalComplex c.symm ⋙
      quotientHomology c.symm n).rightOp).map g := by
  apply Quiver.Hom.unop_inj
  exact appliedHomology_invariant F c.symm n h.op

end Invariant

section DerivedComparison
universe a b
variable {D : Type a} [Category.{b} D] [Preadditive D]

theorem projective_coherent
    (H : ChainComplex (ModuleCat.{max u v} R) ℕ ⥤ D) [H.Additive]
    (hi : ∀ {K T} {f g : K ⟶ T}, Homotopy f g → H.map f = H.map g) :
    Nonempty (CoherentComparison (fun A : ModuleCat.{v} R => ProjectiveChoice R A) (projectiveComplex R)
      projectiveOver H) := by
  apply coherentComparison_of_lifts (ProjectiveChoice R) (projectiveComplex R) projectiveOver H
  · intro A B P Q u
    exact chain_exists R A B P.val Q.val P.property u.hom
  · intro A B P Q u f g hf hg
    exact hi (chain_unique R A B P.val Q.val P.property u.hom f g hf hg).some
  · intro A P
    exact chainLift_id P.val
  · intro A B C P Q T u v f g hf hg
    exact chainLift_comp hf hg
  · intro A B P Q u v f g hf hg
    exact chainLift_add hf hg

theorem injective_coherent
    (H : CochainComplex (ModuleCat.{max u v} R) ℕ ⥤ D) [H.Additive]
    (hi : ∀ {K T} {f g : K ⟶ T}, Homotopy f g → H.map f = H.map g) :
    Nonempty (CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolution R A)
      (injectiveComplex R) injectiveOver H) := by
  apply coherentComparison_of_lifts _ (injectiveComplex R) injectiveOver H
  · intro A B I J u
    exact cochain_exists R A B (ofInjective I) J u.hom
  · intro A B I J u f g hf hg
    exact hi (cochain_unique R A B (ofInjective I) J u.hom f g hf hg).some
  · intro A I
    exact cochainLift_id I
  · intro A B C I J K u v f g hf hg
    exact cochainLift_comp hf hg
  · intro A B I J u v f g hf hg
    exact cochainLift_add hf hg

end DerivedComparison

theorem chain_homology_functorial :
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive] (n : ℕ),
    Nonempty (CoherentComparison (ProjectiveChoice R) (projectiveComplex R) projectiveOver
      (appliedHomology F (ComplexShape.down ℕ) n)) := by
  intro R _ S _ F _ n
  exact projective_coherent (appliedHomology F (ComplexShape.down ℕ) n)
    (fun h => appliedHomology_invariant F (ComplexShape.down ℕ) n h)

theorem cochain_homology_functorial :
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive] (n : ℕ),
    Nonempty (CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolution R A)
      (injectiveComplex R) injectiveOver (appliedHomology F (ComplexShape.up ℕ) n)) := by
  intro R _ S _ F _ n
  exact injective_coherent (appliedHomology F (ComplexShape.up ℕ) n)
    (fun h => appliedHomology_invariant F (ComplexShape.up ℕ) n h)

theorem chain_contravariant_functorial :
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive] (n : ℕ),
    Nonempty (CoherentComparison (ProjectiveChoice R) (projectiveComplex R) projectiveOver
      (appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp) := by
  intro R _ S _ F _ n
  exact projective_coherent (appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp
    (fun h => appliedContravariantHomology_invariant F (ComplexShape.down ℕ) n h)

theorem cochain_contravariant_functorial :
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive] (n : ℕ),
    Nonempty (CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolution R A)
      (injectiveComplex R) injectiveOver
      (appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp) := by
  intro R _ S _ F _ n
  exact injective_coherent (appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp
    (fun h => appliedContravariantHomology_invariant F (ComplexShape.up ℕ) n h)

theorem chain_ab_homology_functorial : chain_ab_homology_functorialType.{u,v,y} := by
  intro R _ F _ n
  apply projective_coherent (appliedAbHomology F (ComplexShape.down ℕ) n)
  intro K T f g h
  exact congrArg (fun k => (forget₂ (ModuleCat ℤ) AddCommGrpCat).map k)
    (appliedHomology_invariant (F ⋙ abelianGroupsToModules) (ComplexShape.down ℕ) n h)

theorem chain_ab_contravariant_functorial : chain_ab_contravariant_functorialType.{u,v,y} := by
  intro R _ F _ n
  apply projective_coherent (appliedAbContravariantHomology F (ComplexShape.down ℕ) n).rightOp
  intro K T f g h
  apply Quiver.Hom.unop_inj
  exact congrArg (fun k => (forget₂ (ModuleCat ℤ) AddCommGrpCat).map k)
    (appliedHomology_invariant (F ⋙ abelianGroupsToModules) ((ComplexShape.down ℕ).symm) n h.op)

theorem cochain_ab_homology_functorial : cochain_ab_homology_functorialType.{u,v,y} := by
  intro R _ F _ n
  apply injective_coherent (appliedAbHomology F (ComplexShape.up ℕ) n)
  intro K T f g h
  exact congrArg (fun k => (forget₂ (ModuleCat ℤ) AddCommGrpCat).map k)
    (appliedHomology_invariant (F ⋙ abelianGroupsToModules) (ComplexShape.up ℕ) n h)

theorem cochain_ab_contravariant_functorial : cochain_ab_contravariant_functorialType.{u,v,y} := by
  intro R _ F _ n
  apply injective_coherent (appliedAbContravariantHomology F (ComplexShape.up ℕ) n).rightOp
  intro K T f g h
  apply Quiver.Hom.unop_inj
  exact congrArg (fun k => (forget₂ (ModuleCat ℤ) AddCommGrpCat).map k)
    (appliedHomology_invariant (F ⋙ abelianGroupsToModules) ((ComplexShape.up ℕ).symm) n h.op)

theorem chain_homology_independent :
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
    (A B : Type v) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : LeftResolution R A) (Q : LeftResolution R B) (hP : P.IsProjective) (u : A →ₗ[R] B) (f g : P.complex ⟶ Q.complex) (n : ℕ),
    ChainLift P Q u f → ChainLift P Q u g → (appliedHomology F (ComplexShape.down ℕ) n).map f = (appliedHomology F (ComplexShape.down ℕ) n).map g := by
  intro R _ S _ F _ A B _ _ _ _ P Q hP u f g n hf hg
  exact appliedHomology_invariant F (ComplexShape.down ℕ) n
    (chain_unique R A B P Q hP u f g hf hg).some

theorem chain_contravariant_independent :
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
    (A B : Type v) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : LeftResolution R A) (Q : LeftResolution R B) (hP : P.IsProjective) (u : A →ₗ[R] B) (f g : P.complex ⟶ Q.complex) (n : ℕ),
    ChainLift P Q u f → ChainLift P Q u g → (appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map f = (appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map g := by
  intro R _ S _ F _ A B _ _ _ _ P Q hP u f g n hf hg
  exact appliedContravariantHomology_invariant F (ComplexShape.down ℕ) n
    (chain_unique R A B P Q hP u f g hf hg).some

theorem cochain_homology_independent :
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
    (A B : Type v) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : RightResolution R A) (Q : InjectiveResolution R B) (u : A →ₗ[R] B) (f g : P.complex ⟶ Q.complex) (n : ℕ),
    CochainLift P Q u f → CochainLift P Q u g → (appliedHomology F (ComplexShape.up ℕ) n).map f = (appliedHomology F (ComplexShape.up ℕ) n).map g := by
  intro R _ S _ F _ A B _ _ _ _ P Q u f g n hf hg
  exact appliedHomology_invariant F (ComplexShape.up ℕ) n
    (cochain_unique R A B P Q u f g hf hg).some

theorem cochain_contravariant_independent :
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
    (A B : Type v) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (P : RightResolution R A) (Q : InjectiveResolution R B) (u : A →ₗ[R] B) (f g : P.complex ⟶ Q.complex) (n : ℕ),
    CochainLift P Q u f → CochainLift P Q u g → (appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map f = (appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map g := by
  intro R _ S _ F _ A B _ _ _ _ P Q u f g n hf hg
  exact appliedContravariantHomology_invariant F (ComplexShape.up ℕ) n
    (cochain_unique R A B P Q u f g hf hg).some

theorem chain_ab_homology_independent : chain_ab_homology_independentType.{u,v,y} := by
  intro R _ F _ A B _ _ _ _ P Q hP u f g n hf hg
  have h := (chain_unique R A B P Q hP u f g hf hg).some
  exact congrArg (fun k => (forget₂ (ModuleCat ℤ) AddCommGrpCat).map k)
    (appliedHomology_invariant (F ⋙ abelianGroupsToModules) (ComplexShape.down ℕ) n h)

theorem chain_ab_contravariant_independent : chain_ab_contravariant_independentType.{u,v,y} := by
  intro R _ F _ A B _ _ _ _ P Q hP u f g n hf hg
  have h := (chain_unique R A B P Q hP u f g hf hg).some
  apply Quiver.Hom.unop_inj
  exact congrArg (fun k => (forget₂ (ModuleCat ℤ) AddCommGrpCat).map k)
    (appliedHomology_invariant (F ⋙ abelianGroupsToModules) ((ComplexShape.down ℕ).symm) n h.op)

theorem cochain_ab_homology_independent : cochain_ab_homology_independentType.{u,v,y} := by
  intro R _ F _ A B _ _ _ _ P Q u f g n hf hg
  have h := (cochain_unique R A B P Q u f g hf hg).some
  exact congrArg (fun k => (forget₂ (ModuleCat ℤ) AddCommGrpCat).map k)
    (appliedHomology_invariant (F ⋙ abelianGroupsToModules) (ComplexShape.up ℕ) n h)

theorem cochain_ab_contravariant_independent : cochain_ab_contravariant_independentType.{u,v,y} := by
  intro R _ F _ A B _ _ _ _ P Q u f g n hf hg
  have h := (cochain_unique R A B P Q u f g hf hg).some
  apply Quiver.Hom.unop_inj
  exact congrArg (fun k => (forget₂ (ModuleCat ℤ) AddCommGrpCat).map k)
    (appliedHomology_invariant (F ⋙ abelianGroupsToModules) ((ComplexShape.up ℕ).symm) n h.op)

end
end P103.Ch10.Comparison

/- Mathlib proof attribution
Adapted portion near line 98:
The recursive comparison maps and null-homotopy constructions for projective
and injective resolutions, adapted to the local hypotheses on the resolutions.

Upstream: Mathlib/CategoryTheory/Abelian/Projective/Resolution.lean (around line 81)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison, Jakob von Raumer, Joël Riou

Upstream: Mathlib/CategoryTheory/Abelian/Injective/Resolution.lean (around line 84)
Revision: 56a005855ea17e0b0958f73ec801ae140b0a1679
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kim Morrison

See THIRD_PARTY_NOTICES.md for source links and the Apache 2.0 license.
-/
