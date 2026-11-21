import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Homology.BarProjectionKernel
import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Homology.IntegralBar
import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Extensions.Basic

open CategoryTheory CategoryTheory.Limits Category Finsupp

universe u

namespace ALG02GroupTheory.BarProjectionKernel

open IntegralBar

set_option allowUnsafeReducibility true in
attribute [local reducible] normalizedChains kernelChains ChainComplex.of

noncomputable section

variable {N E Q N' E' Q' : Type u}
variable [Group N] [Group E] [Group Q] [Group N'] [Group E'] [Group Q']

private theorem finsuppLift_bar {G M : Type u} [Group G] [AddCommGroup M]
    [Module Integers.{u} M] {n : ℕ} (f : (Fin n → G) → M) (g : Fin n → G) :
    (Finsupp.lift M Integers.{u} _ f) (bar n g) = f g := by
  rw [← Finsupp.lift_symm_apply, AddEquiv.symm_apply_apply]

private def liftNormalized {G M : Type u} [Group G] [AddCommGroup M]
    [Module Integers.{u} M] {n : ℕ} (f : (Fin n → G) → M)
    (h : ∀ g, (∃ j, g j = 1) → f g = 0) : NormalizedModule G n →ₗ[Integers.{u}] M :=
  (degenerate G n).liftQ (Finsupp.lift M Integers.{u} _ f) (Submodule.span_le.mpr (by
    rintro _ ⟨g, hg, rfl⟩
    exact (finsuppLift_bar f g).trans (h g hg)))

@[simp]
private theorem liftNormalized_bar {G M : Type u} [Group G] [AddCommGroup M]
    [Module Integers.{u} M] {n : ℕ} (f : (Fin n → G) → M)
    (h : ∀ g, (∃ j, g j = 1) → f g = 0) (g : Fin n → G) :
    liftNormalized f h (normalizedBar n g) = f g :=
  finsuppLift_bar f g

private theorem normalizedLinear_ext {G M : Type u} [Group G] [AddCommGroup M]
    [Module Integers.{u} M] {n : ℕ}
    {f g : NormalizedModule G n →ₗ[Integers.{u}] M}
    (h : ∀ t, f (normalizedBar n t) = g (normalizedBar n t)) : f = g := by
  have hm : f.comp (degenerate G n).mkQ = g.comp (degenerate G n).mkQ := by
    apply (Finsupp.lift M Integers.{u} (Fin n → G)).symm.injective
    funext t
    rw [Finsupp.lift_symm_apply, Finsupp.lift_symm_apply]
    exact h t
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (degenerate G n).mkQ_surjective x
  exact DFunLike.congr_fun hm y

private theorem map_tuple_one (f : E →* Q) (a : E) :
    f ∘ ![a] = ![f a] := by
  funext i
  fin_cases i
  rfl

private theorem map_tuple_two (f : E →* Q) (a b : E) :
    f ∘ ![a, b] = ![f a, f b] := by
  funext i
  fin_cases i <;> rfl

private theorem tuple_one {X : Type u} (t : Fin 1 → X) : t = ![t 0] := by
  funext i
  fin_cases i
  rfl

private theorem tuple_two {X : Type u} (t : Fin 2 → X) : t = ![t 0, t 1] := by
  funext i
  fin_cases i <;> rfl

private theorem bar_one_identity : normalizedBar 1 ![(1 : E)] = 0 :=
  normalizedBar_eq_zero ⟨0, rfl⟩

theorem projection_surjective (S : GroupExtension N E Q) (n : ℕ) :
    Function.Surjective ((normalizedChainsMap S.rightHom).f n) :=
  normalizedChainsMap_f_surjective _ S.rightHom_surjective n

private def liftEmptyTuple (_S : GroupExtension N E Q) :
    NormalizedModule Q 0 →ₗ[Integers.{u}] NormalizedModule E 0 :=
  liftNormalized (fun _ => normalizedBar 0 (Fin.elim0 : Fin 0 → E))
    (fun _ ⟨j, _⟩ => Fin.elim0 j)

theorem kernel_zero (S : GroupExtension N E Q) : IsZero ((kernelChains S).X 0) := by
  have h : (liftEmptyTuple S).comp ((normalizedChainsMap S.rightHom).f 0).hom =
      LinearMap.id := by
    apply normalizedLinear_ext
    intro t
    rw [LinearMap.comp_apply]
    change liftEmptyTuple S ((normalizedChainsMap S.rightHom).f 0 (normalizedBar 0 t)) = _
    rw [normalizedChainsMap_bar]
    change liftNormalized _ _ _ = _
    rw [liftNormalized_bar]
    exact congrArg (normalizedBar 0) (Subsingleton.elim _ _)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y => ?_⟩
  have hz (z : KernelModule S 0) : z.val = 0 := by
    have he := DFunLike.congr_fun h z.val
    change liftEmptyTuple S ((normalizedChainsMap S.rightHom).f 0 z.val) = z.val at he
    rw [show (normalizedChainsMap S.rightHom).f 0 z.val = 0 from z.property, map_zero] at he
    exact he.symm
  exact Subtype.ext ((hz x).trans (hz y).symm)

theorem projection_shortExact (S : GroupExtension N E Q) : (projectionSequence S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact LinearMap.shortExact_shortComplexKer (projection_surjective S n)

private theorem kernelDOne (S : GroupExtension N E Q) : (kernelChains S).d 1 0 = 0 :=
  (kernel_zero S).eq_of_tgt _ _

/-- When the degree-one differential is zero, all degree-one chains are cycles. -/
def degreeOneCyclesIso (K : ChainComplex (ModuleCat.{u} Integers.{u}) ℕ)
    (h : K.d 1 0 = 0) : K.cycles 1 ≅ K.X 1 :=
  (K.sc 1).cyclesIsoX₂ (by
    change K.d 1 ((ComplexShape.down ℕ).next 1) = 0
    rw [(ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
    exact h)

/-- The class of a degree-one cycle, when the degree-one differential is zero. -/
def degreeOneClassMap (K : ChainComplex (ModuleCat.{u} Integers.{u}) ℕ)
    (h : K.d 1 0 = 0) : K.X 1 ⟶ K.homology 1 :=
  (degreeOneCyclesIso K h).inv ≫ K.homologyπ 1

/-- Projection of first kernel chains to their homology classes. -/
def kernelClass (S : GroupExtension N E Q) : (kernelChains S).X 1 ⟶ (kernelChains S).homology 1 :=
  degreeOneClassMap (kernelChains S) (kernelDOne S)

private theorem degreeOneCycles_inv_i (K : ChainComplex (ModuleCat.{u} Integers.{u}) ℕ)
    (h : K.d 1 0 = 0) :
    (degreeOneCyclesIso K h).inv ≫ K.iCycles 1 = 𝟙 _ :=
  (degreeOneCyclesIso K h).inv_hom_id

private theorem classMap_natural {K L : ChainComplex (ModuleCat.{u} Integers.{u}) ℕ}
    (hK : K.d 1 0 = 0) (hL : L.d 1 0 = 0) (f : K ⟶ L) :
    degreeOneClassMap K hK ≫ HomologicalComplex.homologyMap f 1 =
      f.f 1 ≫ degreeOneClassMap L hL := by
  simp only [degreeOneClassMap, Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply (cancel_mono (L.iCycles 1)).mp
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i, degreeOneCycles_inv_i,
    Category.comp_id]
  rw [← Category.assoc, degreeOneCycles_inv_i, Category.id_comp]

private theorem classMap_boundary (S : GroupExtension N E Q) (x : KernelModule S 2) :
    kernelClass S ((kernelChains S).d 2 1 x) = 0 := by
  have ha : (kernelChains S).d 2 1 ≫ kernelClass S = 0 := by
    unfold kernelClass degreeOneClassMap
    rw [← Category.assoc]
    have he : (kernelChains S).d 2 1 ≫ (degreeOneCyclesIso _ (kernelDOne S)).inv =
        (kernelChains S).toCycles 2 1 := by
      apply (cancel_mono ((kernelChains S).iCycles 1)).mp
      rw [Category.assoc, HomologicalComplex.toCycles_i, degreeOneCycles_inv_i, Category.comp_id]
    rw [he, HomologicalComplex.toCycles_comp_homologyπ]
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ha) x

private theorem kernelClass_surjective (S : GroupExtension N E Q) :
    Function.Surjective (kernelClass S) := by
  unfold kernelClass degreeOneClassMap
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

private def chosenSection (S : GroupExtension N E Q) : Extensions.NormalizedSection S :=
  Classical.choice (Extensions.normalizedSectionExists S)

private def representative (S : GroupExtension N E Q) (q : Q) : E := (chosenSection S).val q

@[simp]
private theorem representative_right (S : GroupExtension N E Q) (q : Q) :
    S.rightHom (representative S q) = q :=
  (chosenSection S).val.rightInverse_rightHom q

@[simp]
private theorem representative_one (S : GroupExtension N E Q) :
    representative S 1 = 1 :=
  (chosenSection S).property

private def coordinate (S : GroupExtension N E Q) (x : E) : N :=
  (MonoidHom.ofInjective S.inl_injective).symm
    ⟨x * (representative S (S.rightHom x))⁻¹, by
      rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
      simp⟩

@[simp]
private theorem inl_coordinate (S : GroupExtension N E Q) (x : E) :
    S.inl (coordinate S x) = x * (representative S (S.rightHom x))⁻¹ :=
  congrArg Subtype.val ((MonoidHom.ofInjective S.inl_injective).apply_symm_apply _)

@[simp]
private theorem coordinate_one (S : GroupExtension N E Q) : coordinate S 1 = 1 := by
  apply S.inl_injective
  simp

private theorem coordinate_translate (S : GroupExtension N E Q) (n : N) (x : E) :
    coordinate S (S.inl n * x) = n * coordinate S x := by
  apply S.inl_injective
  simp [mul_assoc]

private theorem translate_coordinate (S : GroupExtension N E Q) (x y : E)
    (h : S.rightHom x = S.rightHom y) :
    S.inl (coordinate S x * (coordinate S y)⁻¹) * y = x := by
  simp only [map_mul, inl_coordinate, map_inv, h]
  group

/-- The difference of two tuples lying over the same quotient tuple. -/
def fiberDifference (S : GroupExtension N E Q) {n : ℕ} (t s : Fin n → E)
    (h : S.rightHom ∘ t = S.rightHom ∘ s) : KernelModule S n :=
  ⟨normalizedBar n t - normalizedBar n s, by
    change (normalizedChainsMap S.rightHom).f n (normalizedBar n t - normalizedBar n s) = 0
    rw [map_sub, normalizedChainsMap_bar, normalizedChainsMap_bar, h, sub_self]⟩

/-- The degree-one kernel chain represented by `[i(n)x] - [x]`. -/
def translateDifference (S : GroupExtension N E Q) (n : N) (x : E) : KernelModule S 1 :=
  fiberDifference S ![S.inl n * x] ![x] (by simp [map_tuple_one])

private def linearRepresentative (S : GroupExtension N E Q) (n : ℕ) :
    NormalizedModule Q n →ₗ[Integers.{u}] NormalizedModule E n :=
  liftNormalized (fun t => normalizedBar n (representative S ∘ t))
    (fun _ ⟨j, hj⟩ => normalizedBar_eq_zero ⟨j, by simp [hj]⟩)

private def projectToKernel (S : GroupExtension N E Q) (n : ℕ) :
    NormalizedModule E n →ₗ[Integers.{u}] KernelModule S n :=
  liftNormalized (fun t =>
    fiberDifference S t (representative S ∘ S.rightHom ∘ t) (by
      funext j
      simp)) (fun _ ⟨j, hj⟩ => by
    apply Subtype.ext
    change normalizedBar n _ - normalizedBar n _ = 0
    rw [normalizedBar_eq_zero ⟨j, hj⟩,
      normalizedBar_eq_zero ⟨j, by simp [hj]⟩, sub_zero])

private theorem projectToKernel_bar (S : GroupExtension N E Q) (n : ℕ) (t : Fin n → E) :
    projectToKernel S n (normalizedBar n t) =
      fiberDifference S t (representative S ∘ S.rightHom ∘ t) (by funext j; simp) :=
  liftNormalized_bar _ _ t

private theorem projectToKernel_val (S : GroupExtension N E Q) (n : ℕ)
    (x : NormalizedModule E n) :
    (projectToKernel S n x).val =
      x - linearRepresentative S n ((normalizedChainsMap S.rightHom).f n x) := by
  have he : (KernelModule S n).subtype.comp (projectToKernel S n) =
      LinearMap.id - (linearRepresentative S n).comp ((normalizedChainsMap S.rightHom).f n).hom := by
    apply normalizedLinear_ext
    intro t
    change (projectToKernel S n (normalizedBar n t)).val =
      normalizedBar n t - linearRepresentative S n ((normalizedChainsMap S.rightHom).f n
        (normalizedBar n t))
    rw [projectToKernel_bar, normalizedChainsMap_bar]
    change _ = _ - liftNormalized _ _ _
    rw [liftNormalized_bar]
    rfl
  exact DFunLike.congr_fun he x

private theorem projectToKernel_of_mem (S : GroupExtension N E Q) (n : ℕ)
    (x : KernelModule S n) : projectToKernel S n x.val = x := by
  apply Subtype.ext
  rw [projectToKernel_val, show (normalizedChainsMap S.rightHom).f n x.val = 0 from x.property,
    map_zero, sub_zero]

private theorem kernelLinear_ext {M : Type u} [AddCommGroup M] [Module Integers.{u} M]
    (S : GroupExtension N E Q) (n : ℕ) {f g : KernelModule S n →ₗ[Integers.{u}] M}
    (h : ∀ t, f (fiberDifference S t (representative S ∘ S.rightHom ∘ t)
        (by funext j; simp)) =
      g (fiberDifference S t (representative S ∘ S.rightHom ∘ t) (by funext j; simp))) :
    f = g := by
  have he : f.comp (projectToKernel S n) = g.comp (projectToKernel S n) := by
    apply normalizedLinear_ext
    intro t
    change f (projectToKernel S n (normalizedBar n t)) =
      g (projectToKernel S n (normalizedBar n t))
    rw [projectToKernel_bar]
    exact h t
  apply LinearMap.ext
  intro x
  have hx := DFunLike.congr_fun he x.val
  change f (projectToKernel S n x.val) = g (projectToKernel S n x.val) at hx
  rwa [projectToKernel_of_mem] at hx

private theorem conjugation_product (S : GroupExtension N E Q) (n m : N) (a b : E) :
    (S.inl n * a) * (S.inl m * b) = S.inl (n * S.conjAct a m) * (a * b) := by
  rw [map_mul, S.inl_conjAct_comm]
  group

private theorem boundary_translate (S : GroupExtension N E Q) (n m : N) (a b : E) :
    (kernelChains S).d 2 1
        (fiberDifference S ![S.inl n * a, S.inl m * b] ![a, b]
          (by simp [map_tuple_two])) =
      translateDifference S m b -
        translateDifference S (n * S.conjAct a m) (a * b) + translateDifference S n a := by
  apply Subtype.ext
  rw [kernelChains_d]
  change (normalizedChains E).d 2 1
      (normalizedBar 2 ![S.inl n * a, S.inl m * b] - normalizedBar 2 ![a, b]) =
    (normalizedBar 1 ![S.inl m * b] - normalizedBar 1 ![b]) -
      (normalizedBar 1 ![S.inl (n * S.conjAct a m) * (a * b)] - normalizedBar 1 ![a * b]) +
      (normalizedBar 1 ![S.inl n * a] - normalizedBar 1 ![a])
  rw [map_sub, normalizedBar_d_two, normalizedBar_d_two, conjugation_product]
  abel

private theorem quotient_conj (S : GroupExtension N E Q) (a : E) (m : N) :
    QuotientGroup.mk (s := pulledBackCommutator S.inl) (S.conjAct a m) =
      (QuotientGroup.mk m : KernelQuotient S) := by
  have hm : (S.conjAct a m) * m⁻¹ ∈ pulledBackCommutator S.inl := by
    change S.inl (S.conjAct a m * m⁻¹) ∈ ⁅(⊤ : Subgroup E), S.inl.range⁆
    rw [map_mul, S.inl_conjAct_comm, map_inv]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) ⟨m, rfl⟩
  have he := (QuotientGroup.eq_one_iff _).mpr hm
  change QuotientGroup.mk' (pulledBackCommutator S.inl) (S.conjAct a m * m⁻¹) = 1 at he
  rw [map_mul, map_inv] at he
  exact mul_inv_eq_one.mp he

private instance quotientCommGroup (S : GroupExtension N E Q) : CommGroup (KernelQuotient S) where
  toGroup := inferInstance
  mul_comm := (kernelQuotient_commutative S.inl S.inl_injective).is_comm.comm

private def rhoOnAmbientChains (S : GroupExtension N E Q) :
    NormalizedModule E 1 →ₗ[Integers.{u}] Additive (KernelQuotient S) :=
  liftNormalized (fun t => Additive.ofMul (QuotientGroup.mk (coordinate S (t 0))))
    (fun _ ⟨j, hj⟩ => by
      rw [Subsingleton.elim j (0 : Fin 1)] at hj
      rw [hj, coordinate_one]
      exact congrArg Additive.ofMul ((QuotientGroup.mk' (pulledBackCommutator S.inl)).map_one))

private def rhoChains (S : GroupExtension N E Q) :
    KernelModule S 1 →ₗ[Integers.{u}] Additive (KernelQuotient S) :=
  (rhoOnAmbientChains S).comp (KernelModule S 1).subtype

@[simp]
private theorem rho_translate (S : GroupExtension N E Q) (n : N) (x : E) :
    rhoChains S (translateDifference S n x) =
      Additive.ofMul (QuotientGroup.mk n) := by
  change rhoOnAmbientChains S (normalizedBar 1 ![S.inl n * x] - normalizedBar 1 ![x]) = _
  unfold rhoOnAmbientChains
  rw [map_sub, liftNormalized_bar, liftNormalized_bar]
  change Additive.ofMul (QuotientGroup.mk' _ (coordinate S (S.inl n * x))) -
      Additive.ofMul (QuotientGroup.mk' _ (coordinate S x)) = _
  rw [coordinate_translate, map_mul, ofMul_mul, add_sub_cancel_right]
  rfl

private theorem fiberDifference_one (S : GroupExtension N E Q) (t s : Fin 1 → E)
    (h : S.rightHom ∘ t = S.rightHom ∘ s) :
    fiberDifference S t s h =
      translateDifference S (coordinate S (t 0) * (coordinate S (s 0))⁻¹) (s 0) := by
  have he := congrFun h 0
  change S.rightHom (t 0) = S.rightHom (s 0) at he
  apply Subtype.ext
  change normalizedBar 1 t - normalizedBar 1 s =
    normalizedBar 1 ![S.inl (coordinate S (t 0) * (coordinate S (s 0))⁻¹) * s 0] -
      normalizedBar 1 ![s 0]
  rw [translate_coordinate S _ _ he, ← tuple_one t, ← tuple_one s]

private theorem fiberDifference_two (S : GroupExtension N E Q) (t s : Fin 2 → E)
    (h : S.rightHom ∘ t = S.rightHom ∘ s) :
    ∃ (n m : N) (a b : E) (h' : S.rightHom ∘ ![S.inl n * a, S.inl m * b] =
        S.rightHom ∘ ![a, b]),
      fiberDifference S t s h = fiberDifference S ![S.inl n * a, S.inl m * b] ![a, b] h' := by
  have h0 : S.rightHom (t 0) = S.rightHom (s 0) := congrFun h 0
  have h1 : S.rightHom (t 1) = S.rightHom (s 1) := congrFun h 1
  refine ⟨coordinate S (t 0) * (coordinate S (s 0))⁻¹,
    coordinate S (t 1) * (coordinate S (s 1))⁻¹, s 0, s 1, by simp [map_tuple_two], ?_⟩
  apply Subtype.ext
  change normalizedBar 2 t - normalizedBar 2 s = normalizedBar 2 _ - normalizedBar 2 _
  rw [translate_coordinate S _ _ h0, translate_coordinate S _ _ h1,
    ← tuple_two t, ← tuple_two s]

private theorem rho_boundary (S : GroupExtension N E Q) :
    (rhoChains S).comp ((kernelChains S).d 2 1).hom = 0 := by
  apply kernelLinear_ext S 2
  intro t
  obtain ⟨n, m, a, b, _, h⟩ := fiberDifference_two S t
    (representative S ∘ S.rightHom ∘ t) (by funext j; simp)
  change rhoChains S ((kernelChains S).d 2 1 (fiberDifference S t
    (representative S ∘ S.rightHom ∘ t) (by funext j; simp))) = 0
  rw [h, boundary_translate, map_add, map_sub, rho_translate, rho_translate, rho_translate]
  let q := QuotientGroup.mk' (pulledBackCommutator S.inl)
  change Additive.ofMul (q m) - Additive.ofMul (q (n * S.conjAct a m)) +
    Additive.ofMul (q n) = (0 : Additive (KernelQuotient S))
  rw [map_mul, ofMul_mul, show q (S.conjAct a m) = q m from quotient_conj S a m]
  abel

private def rhoHomology (S : GroupExtension N E Q) :
    (kernelChains S).homology 1 ⟶ ModuleCat.of Integers.{u} (Additive (KernelQuotient S)) :=
  ((kernelChains S).homologyIsCokernel (i := 2) (j := 1) ((ComplexShape.down ℕ).prev_eq' rfl)).desc <|
    CokernelCofork.ofπ ((kernelChains S).iCycles 1 ≫ ModuleCat.ofHom (rhoChains S)) (by
      rw [← Category.assoc, HomologicalComplex.toCycles_i]
      exact ModuleCat.hom_ext (rho_boundary S))

private theorem rhoHomology_class (S : GroupExtension N E Q) (x : KernelModule S 1) :
    rhoHomology S (kernelClass S x) = rhoChains S x := by
  have h : (kernelChains S).homologyπ 1 ≫ rhoHomology S =
      (kernelChains S).iCycles 1 ≫ ModuleCat.ofHom (rhoChains S) :=
    Cofork.IsColimit.π_desc ((kernelChains S).homologyIsCokernel (i := 2) (j := 1) ((ComplexShape.down ℕ).prev_eq' rfl))
  have he : kernelClass S ≫ rhoHomology S = ModuleCat.ofHom (rhoChains S) := by
    unfold kernelClass degreeOneClassMap
    rw [Category.assoc, h, ← Category.assoc, degreeOneCycles_inv_i, Category.id_comp]
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom he) x

@[simp]
private theorem translateDifference_one_left (S : GroupExtension N E Q) (x : E) :
    translateDifference S 1 x = 0 := by
  apply Subtype.ext
  change normalizedBar 1 ![S.inl 1 * x] - normalizedBar 1 ![x] = (0 : NormalizedModule E 1)
  simp

private theorem class_translate (S : GroupExtension N E Q) (n : N) (x : E) :
    kernelClass S (translateDifference S n x) = kernelClass S (translateDifference S n 1) := by
  have h := congrArg (kernelClass S) (boundary_translate S n 1 1 x)
  rw [classMap_boundary, map_add, map_sub, translateDifference_one_left, map_zero,
    map_one (S.conjAct 1), mul_one, one_mul, zero_sub] at h
  exact neg_add_eq_zero.mp h.symm

private def kernelClassHom (S : GroupExtension N E Q) : N →* Multiplicative ((kernelChains S).homology 1) where
  toFun n := Multiplicative.ofAdd (kernelClass S (translateDifference S n 1))
  map_one' := by rw [translateDifference_one_left, map_zero]; rfl
  map_mul' n m := by
    have h := congrArg (kernelClass S) (boundary_translate S n m 1 1)
    rw [classMap_boundary, map_add, map_sub, map_one S.conjAct, MulAut.one_apply, one_mul] at h
    change kernelClass S (translateDifference S (n * m) 1) =
      kernelClass S (translateDifference S n 1) + kernelClass S (translateDifference S m 1)
    apply sub_eq_zero.mp
    calc
      _ = -(kernelClass S (translateDifference S m 1) -
          kernelClass S (translateDifference S (n * m) 1) +
          kernelClass S (translateDifference S n 1)) := by abel
      _ = 0 := by rw [← h, neg_zero]

private theorem kernelClassHom_conj (S : GroupExtension N E Q) (a : E) (n : N) :
    kernelClassHom S (S.conjAct a n) = kernelClassHom S n := by
  have h := congrArg (kernelClass S) (boundary_translate S 1 n a 1)
  rw [classMap_boundary, map_add, map_sub, translateDifference_one_left, map_zero,
    add_zero, one_mul, mul_one, class_translate S (S.conjAct a n)] at h
  exact congrArg Multiplicative.ofAdd (sub_eq_zero.mp h.symm).symm

private theorem kernelClassHom_kills (S : GroupExtension N E Q) :
    pulledBackCommutator S.inl ≤ (kernelClassHom S).ker := by
  let K := ((kernelClassHom S).ker).map S.inl
  have hk : ⁅(⊤ : Subgroup E), S.inl.range⁆ ≤ K := by
    apply Subgroup.commutator_le.mpr
    rintro a _ _ ⟨n, rfl⟩
    refine ⟨S.conjAct a n * n⁻¹, ?_, ?_⟩
    · change kernelClassHom S (S.conjAct a n * n⁻¹) = 1
      rw [map_mul, map_inv, kernelClassHom_conj, mul_inv_cancel]
    · rw [map_mul, map_inv, S.inl_conjAct_comm]
      rfl
  intro n hn
  obtain ⟨m, hm, he⟩ := hk hn
  exact (S.inl_injective he) ▸ hm

/-- Send the class of a kernel element to the class of its degree-one bar generator. -/
def classOfKernelElement (S : GroupExtension N E Q) :
    KernelQuotient S →* Multiplicative ((kernelChains S).homology 1) :=
  QuotientGroup.lift _ (kernelClassHom S) (kernelClassHom_kills S)

theorem classOfKernelElement_mk (S : GroupExtension N E Q) (n : N) (x : E) :
    classOfKernelElement S (QuotientGroup.mk n) =
      Multiplicative.ofAdd (kernelClass S (translateDifference S n x)) :=
  congrArg Multiplicative.ofAdd (class_translate S n x).symm

private def additiveToLinear {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [Module Integers.{u} A] [Module Integers.{u} B] (f : A →+ B) : A →ₗ[Integers.{u}] B where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    have hr : (r.down : Integers.{u}) = r := rfl
    rw [RingHom.id_apply, ← hr, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul]

private theorem classOfKernelElement_rho (S : GroupExtension N E Q) (x : KernelModule S 1) :
    classOfKernelElement S (rhoChains S x).toMul = Multiplicative.ofAdd (kernelClass S x) := by
  have h : (additiveToLinear (classOfKernelElement S).toAdditiveLeft).comp (rhoChains S) =
      (kernelClass S).hom := by
    apply kernelLinear_ext S 1
    intro t
    rw [fiberDifference_one]
    change ((classOfKernelElement S) (rhoChains S (translateDifference S _ _)).toMul).toAdd =
      kernelClass S (translateDifference S _ _)
    rw [rho_translate]
    exact congrArg Multiplicative.toAdd (classOfKernelElement_mk S _ _)
  exact congrArg Multiplicative.ofAdd (DFunLike.congr_fun h x)

/-- The first homology of the bar projection kernel is the conjugation coinvariant quotient. -/
def homologyEquiv (S : GroupExtension N E Q) :
    Multiplicative ((kernelChains S).homology 1) ≃* KernelQuotient S where
  toFun x := (rhoHomology S x.toAdd).toMul
  invFun := classOfKernelElement S
  left_inv x := by
    obtain ⟨y, hy⟩ := kernelClass_surjective S x.toAdd
    change classOfKernelElement S (rhoHomology S x.toAdd).toMul =
      Multiplicative.ofAdd x.toAdd
    rw [← hy, rhoHomology_class]
    exact classOfKernelElement_rho S y
  right_inv x := by
    induction x using QuotientGroup.induction_on with
    | _ n =>
      change (rhoHomology S (classOfKernelElement S (QuotientGroup.mk n)).toAdd).toMul =
        QuotientGroup.mk n
      rw [classOfKernelElement_mk S n 1]
      exact congrArg Additive.toMul ((rhoHomology_class S _).trans (rho_translate S n 1))
  map_mul' x y := map_add (rhoHomology S).hom x.toAdd y.toAdd

theorem homologyEquiv_translate (S : GroupExtension N E Q) (n : N) (x : E) :
    homologyEquiv S (Multiplicative.ofAdd (kernelClass S (translateDifference S n x))) =
      QuotientGroup.mk n :=
  congrArg Additive.toMul ((rhoHomology_class S _).trans (rho_translate S n x))

/-- The inverse identifies a kernel element with its bar class. -/
theorem homologyEquiv_symm_mk (S : GroupExtension N E Q) (n : N) (x : E) :
    (homologyEquiv S).symm (QuotientGroup.mk n) =
      Multiplicative.ofAdd (kernelClass S (translateDifference S n x)) :=
  classOfKernelElement_mk S n x

private theorem generatorClass_bar {G : Type u} [Group G] (g : G) :
    generatorClass g = degreeOneClassMap (chains G) d_one_eq_zero (bar 1 ![g]) := by
  change (chains G).homologyπ 1
    ((groupHomology.isoCycles₁ (coefficients G)).inv
      ((groupHomology.cycles₁IsoOfIsTrivial (coefficients G)).inv (single g 1))) =
    (chains G).homologyπ 1 ((degreeOneCyclesIso (chains G) d_one_eq_zero).inv (bar 1 ![g]))
  congr 1
  apply (ModuleCat.mono_iff_injective ((chains G).iCycles 1)).mp inferInstance
  rw [groupHomology.isoCycles₁_inv_comp_iCycles_apply]
  have hi := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (degreeOneCycles_inv_i (chains G) d_one_eq_zero)) (bar 1 ![g])
  change (chains G).iCycles 1 ((degreeOneCyclesIso (chains G) d_one_eq_zero).inv
    (bar 1 ![g])) = bar 1 ![g] at hi
  rw [hi]
  change (groupHomology.chainsIso₁ (coefficients G)).inv (single g 1) = bar 1 ![g]
  change (Finsupp.domLCongr (Equiv.funUnique (Fin 1) G)).symm (single g 1) = bar 1 ![g]
  rw [Finsupp.domLCongr_symm, Finsupp.domLCongr_single]
  apply congrArg (fun t : Fin 1 → G => single t (1 : Integers.{u}))
  funext i
  fin_cases i
  rfl

/-- The kernel inclusion carries the given class to the class induced by the group inclusion. -/
theorem homologyEquiv_inclusion (S : GroupExtension N E Q) (n : N) :
    HomologicalComplex.homologyMap (kernelInclusion S) 1
        ((homologyEquiv S).symm (QuotientGroup.mk n)).toAdd =
      HomologicalComplex.homologyMap (normalization E) 1
        (homologyMap S.inl 1 (generatorClass n)) := by
  rw [homologyEquiv_symm_mk S n 1, homologyMap_generatorClass, generatorClass_bar]
  have hJ := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (classMap_natural (kernelDOne S) normalized_d_one_eq_zero (kernelInclusion S)))
    (translateDifference S n 1)
  have hE := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (classMap_natural d_one_eq_zero normalized_d_one_eq_zero (normalization E)))
    (bar 1 ![S.inl n])
  change HomologicalComplex.homologyMap (kernelInclusion S) 1
    (kernelClass S (translateDifference S n 1)) =
    degreeOneClassMap (normalizedChains E) normalized_d_one_eq_zero
      (normalizedBar 1 ![S.inl n * 1] - normalizedBar 1 ![1]) at hJ
  change HomologicalComplex.homologyMap (normalization E) 1
    (degreeOneClassMap (chains E) d_one_eq_zero (bar 1 ![S.inl n])) =
    degreeOneClassMap (normalizedChains E) normalized_d_one_eq_zero
      (normalizedBar 1 ![S.inl n]) at hE
  change HomologicalComplex.homologyMap (kernelInclusion S) 1
    (kernelClass S (translateDifference S n 1)) = _
  rw [hJ, hE, mul_one, bar_one_identity, sub_zero]

/-- The map from the kernel coinvariants into standard integral first homology. -/
def integralInclusion (S : GroupExtension N E Q) :
    KernelQuotient S →* Multiplicative (homology E 1) :=
  ((HomologicalComplex.homologyMap (kernelInclusion S) 1 ≫
      (normalizationHomologyIso E 1 (by decide)).inv).hom.toAddMonoidHom.toMultiplicative).comp
    (homologyEquiv S).symm.toMonoidHom

theorem integralInclusion_mk (S : GroupExtension N E Q) (n : N) :
    integralInclusion S (QuotientGroup.mk n) =
      Multiplicative.ofAdd (homologyMap S.inl 1 (generatorClass n)) := by
  let e := normalizationHomologyIso E 1 (by decide)
  apply Multiplicative.toAdd.injective
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom e.inv_hom_id)
    (HomologicalComplex.homologyMap (kernelInclusion S) 1
      ((homologyEquiv S).symm (QuotientGroup.mk n)).toAdd)
  change e.hom (e.inv (HomologicalComplex.homologyMap (kernelInclusion S) 1
    ((homologyEquiv S).symm (QuotientGroup.mk n)).toAdd)) = _ at h
  change e.hom (e.inv (HomologicalComplex.homologyMap (kernelInclusion S) 1
    ((homologyEquiv S).symm (QuotientGroup.mk n)).toAdd)) =
    e.hom (homologyMap S.inl 1 (generatorClass n))
  rw [h]
  exact homologyEquiv_inclusion S n

/-- The chain square induced by a commuting map of extensions. -/
theorem projection_square {S : GroupExtension N E Q} {T : GroupExtension N' E' Q'}
    (f : ExtensionHom S T) :
    normalizedChainsMap f.middle ≫ normalizedChainsMap T.rightHom =
      normalizedChainsMap S.rightHom ≫ normalizedChainsMap f.quotient := by
  rw [← normalizedChainsMap_comp, ← normalizedChainsMap_comp, f.right_comm]

/-- The map of kernel complexes induced by a commuting map of extensions. -/
def kernelChainsMap {S : GroupExtension N E Q} {T : GroupExtension N' E' Q'}
    (f : ExtensionHom S T) : kernelChains S ⟶ kernelChains T :=
  restrictKernelMap (projection_square f)

private theorem restrictKernelMap_translate {S : GroupExtension N E Q}
    {T : GroupExtension N' E' Q'} (f : ExtensionHom S T)
    (h : normalizedChainsMap f.middle ≫ normalizedChainsMap T.rightHom =
      normalizedChainsMap S.rightHom ≫ normalizedChainsMap f.quotient) (n : N) (x : E) :
    (restrictKernelMap h).f 1 (translateDifference S n x) =
      translateDifference T (f.kernel n) (f.middle x) := by
  apply Subtype.ext
  change (normalizedChainsMap f.middle).f 1
    (normalizedBar 1 ![S.inl n * x] - normalizedBar 1 ![x]) =
    normalizedBar 1 ![T.inl (f.kernel n) * f.middle x] - normalizedBar 1 ![f.middle x]
  rw [map_sub, normalizedChainsMap_bar, normalizedChainsMap_bar, map_tuple_one, map_tuple_one,
    map_mul, show f.middle (S.inl n) = T.inl (f.kernel n) from DFunLike.congr_fun f.inl_comm n]

/-- The homology equivalence is natural with respect to commuting maps of extensions. -/
theorem homologyEquiv_natural {S : GroupExtension N E Q} {T : GroupExtension N' E' Q'}
    (f : ExtensionHom S T)
    (h : normalizedChainsMap f.middle ≫ normalizedChainsMap T.rightHom =
      normalizedChainsMap S.rightHom ≫ normalizedChainsMap f.quotient)
    (x : (kernelChains S).homology 1) :
    homologyEquiv T (Multiplicative.ofAdd
      (HomologicalComplex.homologyMap (restrictKernelMap h) 1 x)) =
      quotientMap f (homologyEquiv S (Multiplicative.ofAdd x)) := by
  obtain ⟨y, hy⟩ := (homologyEquiv S).symm.surjective (Multiplicative.ofAdd x)
  have hx : ((homologyEquiv S).symm y).toAdd = x := congrArg Multiplicative.toAdd hy
  rw [← hx]
  induction y using QuotientGroup.induction_on with
  | _ n =>
    rw [homologyEquiv_symm_mk S n 1]
    have he := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (classMap_natural (kernelDOne S) (kernelDOne T) (restrictKernelMap h)))
      (translateDifference S n 1)
    change HomologicalComplex.homologyMap (restrictKernelMap h) 1
      (kernelClass S (translateDifference S n 1)) =
      kernelClass T ((restrictKernelMap h).f 1 (translateDifference S n 1)) at he
    change homologyEquiv T (Multiplicative.ofAdd
        (HomologicalComplex.homologyMap (restrictKernelMap h) 1
          (kernelClass S (translateDifference S n 1)))) =
      quotientMap f (homologyEquiv S (Multiplicative.ofAdd (kernelClass S
        (translateDifference S n 1))))
    rw [he, restrictKernelMap_translate f, homologyEquiv_translate, homologyEquiv_translate]
    rfl

theorem natural_identification : Spec.NaturalIdentification.{u} := by
  refine ⟨fun S => homologyEquiv S, ?_, fun S n => homologyEquiv_inclusion S n,
    fun f h x => homologyEquiv_natural f h x⟩
  intro N E Q _ _ _ S n x
  let y := translateDifference S n x
  let z := (degreeOneCyclesIso (kernelChains S) (kernelDOne S)).inv y
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (degreeOneCycles_inv_i (kernelChains S) (kernelDOne S))) y
  refine ⟨z, congrArg Subtype.val h, homologyEquiv_translate S n x⟩

end
end ALG02GroupTheory.BarProjectionKernel

