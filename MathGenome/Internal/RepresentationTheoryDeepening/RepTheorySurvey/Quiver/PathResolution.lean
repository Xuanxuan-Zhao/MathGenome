import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.Forms
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.PathResolution
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! The standard projective resolution associated to the paths of a quiver. -/

open CategoryTheory
open scoped DirectSum TensorProduct ModuleCat ModuleCat.Algebra Classical ZeroObject

universe u v w d

namespace RepTheorySurvey.Quiver.PathResolution

noncomputable section

open RM03 PathResolutionSpec

variable {k : Type w} {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]

local notation "A" => PathAlgebra k Q

private def projectToVertex (i : Q) : A →ₗ[A] VertexProjective k i where
  toFun x := ⟨x * PathAlgebra.vertex k i, Submodule.mem_span_singleton.mpr ⟨x, rfl⟩⟩
  map_add' x y := Subtype.ext (add_mul x y _)
  map_smul' t x := Subtype.ext (mul_assoc t x _)

private theorem projectToVertex_subtype (i : Q) (p : VertexProjective k i) :
    projectToVertex i p.val = p := by
  apply Subtype.ext
  obtain ⟨x, hx⟩ := (Forms.mem_projectiveAt k i p.val).mp p.property
  change p.val * PathAlgebra.vertex k i = p.val
  rw [← hx, mul_assoc, PathAlgebra.vertex_idempotent]

theorem vertexProjective_isProjective : VertexProjectiveIsProjective.{u, v, w} := by
  intro k Q _ _ _ i
  refine Module.Projective.of_split (VertexProjective k i).subtype (projectToVertex i) ?_
  exact LinearMap.ext (projectToVertex_subtype i)

local instance (i : Q) : Module.Projective A (VertexProjective k i) :=
  vertexProjective_isProjective k i

/-- The paths starting at the chosen vertex are a basis of its left ideal. -/
def pathsBasis (i : Q) : Module.Basis (Σ j, Quiver.Path i j) k (VertexProjective k i) := by
  let g : (Σ j, Quiver.Path i j) → VertexProjective k i := fun p => pathVector p.2
  have hi : LinearIndependent k g := by
    apply LinearIndependent.of_comp ((VertexProjective k i).subtype.restrictScalars k)
    change LinearIndependent k (fun p : Σ j, Quiver.Path i j => PathAlgebra.basis k Q ⟨i, p⟩)
    exact (PathAlgebra.basis k Q).linearIndependent.comp (fun p : Σ j, Quiver.Path i j =>
        (⟨i, p⟩ : Path Q)) (fun _ _ h => @sigma_mk_injective Q (fun t => Σ j, Quiver.Path t j) i _ _ h)
  refine Module.Basis.mk hi ?_
  have hrange : LinearMap.range ((projectToVertex (k := k) i).restrictScalars k) = ⊤ :=
    LinearMap.range_eq_top.2 fun p => ⟨p.val, projectToVertex_subtype i p⟩
  rw [← hrange, ← Submodule.map_top, ← (PathAlgebra.basis k Q).span_eq, Submodule.map_span]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨_, ⟨⟨j, l, p⟩, rfl⟩, rfl⟩
  rw [PathAlgebra.basis_apply]
  by_cases hj : j = i
  · subst j
    apply Submodule.subset_span
    refine ⟨⟨l, p⟩, Subtype.ext ?_⟩
    change _ = PathAlgebra.ofPath k (Path.ofPath p) * PathAlgebra.vertex k i
    simp [g, pathVector]
  · have hz : projectToVertex (k := k) i (PathAlgebra.ofPath k (Path.ofPath p)) = 0 :=
      Subtype.ext (by
        change PathAlgebra.ofPath k (Path.ofPath p) * PathAlgebra.vertex k i = 0
        simp [hj])
    change projectToVertex i (PathAlgebra.ofPath k (Path.ofPath p)) ∈ _
    rw [hz]
    exact Submodule.zero_mem _

@[simp]
theorem pathsBasis_apply {i j : Q} (p : Quiver.Path i j) :
    pathsBasis (k := k) i ⟨j, p⟩ = pathVector p := by
  simp [pathsBasis]

variable (V : QuiverRepresentation.{u, v, w, d} k Q)

private def point (i : Q) : V.vertex i →ₗ[k] Target V :=
  (QuiverModuleEquivalence.coordinates V).symm.toLinearMap.comp (PathOperators.inclusion V i)

@[simp]
private theorem coordinates_point (i : Q) (x : V.vertex i) :
    QuiverModuleEquivalence.coordinates V (point V i x) = PathOperators.inclusion V i x :=
  (QuiverModuleEquivalence.coordinates V).apply_symm_apply _

private def augmentationBilinear (i : Q) : VertexProjective k i →ₗ[A] V.vertex i →ₗ[k] Target V where
  toFun p := (p : A) • point V i
  map_add' p q := add_smul (p : A) (q : A) _
  map_smul' a p := mul_smul a (p : A) _

/-- The augmentation is induced by the action of the left ideal on the vertex space. -/
def augmentation : DegreeZero V →ₗ[A] Target V :=
  DirectSum.toModule A Q _ fun i => TensorProduct.AlgebraTensorModule.lift (augmentationBilinear V i)

private theorem augmentation_tmul (i : Q) (p : VertexProjective k i) (x : V.vertex i) :
    augmentation V (insertZero V i (p ⊗ₜ[k] x)) = (p : A) • point V i x := by
  simp [augmentation, augmentationBilinear]

theorem augmentation_path {i j : Q} (p : Quiver.Path i j) (x : V.vertex i) :
    QuiverModuleEquivalence.coordinates V
      (augmentation V (insertZero V i (pathVector p ⊗ₜ[k] x))) =
      PathOperators.inclusion V j (V.mapPath p x) := by
  rw [augmentation_tmul]
  change QuiverModuleEquivalence.coordinates V
      (PathAlgebra.ofPath k (Path.ofPath p) • point V i x) = _
  refine (QuiverModuleEquivalence.coordinates_smul_ofPath V (Path.ofPath p) (point V i x)).trans ?_
  rw [coordinates_point]
  change PathOperators.inclusion V j
    (V.mapPath p (PathOperators.projection V i (PathOperators.inclusion V i x))) = _
  rw [PathOperators.projection_inclusion]

/-- The two terms of the differential on the summand indexed by an arrow. -/
def boundary : DegreeOne V →ₗ[A] DegreeZero V :=
  DirectSum.toModule (M := fun a : Arrow Q => VertexProjective k a.2.1 ⊗[k] V.vertex a.1)
    A (Arrow Q) (DegreeZero V) fun a =>
    let plus : VertexProjective k a.2.1 ⊗[k] V.vertex a.1 →ₗ[A] DegreeZero V :=
      (insertZero V a.1).comp (TensorProduct.AlgebraTensorModule.map
        (appendArrow a.2.2) LinearMap.id)
    let minus : VertexProjective k a.2.1 ⊗[k] V.vertex a.1 →ₗ[A] DegreeZero V :=
      (insertZero V a.2.1).comp (TensorProduct.AlgebraTensorModule.map
        LinearMap.id (V.arrow a.2.2))
    { toFun := fun z => plus z - minus z
      map_add' := fun x y => by simp only [map_add]; abel
      map_smul' := fun t z => by simp only [RingHom.id_apply, map_smul, smul_sub] }

@[simp]
theorem boundary_tmul (a : Arrow Q) (p : VertexProjective k a.2.1) (x : V.vertex a.1) :
    boundary V (insertOne V a (p ⊗ₜ[k] x)) =
      insertZero V a.1 (appendArrow a.2.2 p ⊗ₜ[k] x) -
        insertZero V a.2.1 (p ⊗ₜ[k] V.arrow a.2.2 x) := by
  simp [boundary]

private def genZero {i j : Q} (p : Quiver.Path i j) : V.vertex i →ₗ[k] DegreeZero V :=
  (insertZero V i).restrictScalars k ∘ₗ TensorProduct.mk k _ _ (pathVector p)

private def genOne {i j l : Q} (a : i ⟶ j) (p : Quiver.Path j l) :
    V.vertex i →ₗ[k] DegreeOne V :=
  (insertOne V ⟨i, j, a⟩).restrictScalars k ∘ₗ TensorProduct.mk k _ _ (pathVector p)

private theorem genZero_cons {i j l : Q} (p : Quiver.Path i j) (a : j ⟶ l) (x : V.vertex i) :
    genZero V (p.cons a) x = PathAlgebra.arrow k a • genZero V p x := by
  change insertZero V i (pathVector (p.cons a) ⊗ₜ[k] x) =
    PathAlgebra.arrow k a • insertZero V i (pathVector p ⊗ₜ[k] x)
  rw [← map_smul, TensorProduct.smul_tmul']
  congr 2
  apply Subtype.ext
  exact (PathAlgebra.ofPath_cons p a).symm

private theorem genOne_cons {i j l m : Q} (a : i ⟶ j) (p : Quiver.Path j l) (b : l ⟶ m)
    (x : V.vertex i) :
    genOne V a (p.cons b) x = PathAlgebra.arrow k b • genOne V a p x := by
  change insertOne V ⟨i, j, a⟩ (pathVector (p.cons b) ⊗ₜ[k] x) =
    PathAlgebra.arrow k b • insertOne V ⟨i, j, a⟩ (pathVector p ⊗ₜ[k] x)
  rw [← map_smul, TensorProduct.smul_tmul']
  congr 2
  apply Subtype.ext
  exact (PathAlgebra.ofPath_cons p b).symm

private theorem boundary_genOne {i j l : Q} (a : i ⟶ j) (p : Quiver.Path j l)
    (x : V.vertex i) :
    boundary V (genOne V a p x) = genZero V (a.toPath.comp p) x - genZero V p (V.arrow a x) := by
  have h : appendArrow (k := k) a (pathVector p) = pathVector (a.toPath.comp p) :=
    Subtype.ext (PathAlgebra.ofPath_mul_comp p a.toPath)
  exact (boundary_tmul V ⟨i, j, a⟩ (pathVector p) x).trans (by rw [h]; rfl)

private theorem augmentation_genZero {i j : Q} (p : Quiver.Path i j) (x : V.vertex i) :
    augmentation V (genZero V p x) = point V j (V.mapPath p x) := by
  apply (QuiverModuleEquivalence.coordinates V).injective
  rw [coordinates_point]
  exact augmentation_path V p x

/-- Sum the arrow summands met as a path acts on the initial vector. -/
private def homotopyOnPath {i : Q} : ∀ {j : Q}, Quiver.Path i j → V.vertex i →ₗ[k] DegreeOne V
  | _, .nil => 0
  | _, .cons p a => PathAlgebra.arrow k a • homotopyOnPath p +
      (genOne V a .nil).comp (V.mapPath p)

private theorem homotopyOnPath_first {i j l : Q} (a : i ⟶ j) (p : Quiver.Path j l)
    (x : V.vertex i) :
    homotopyOnPath V (a.toPath.comp p) x =
      genOne V a p x + homotopyOnPath V p (V.arrow a x) := by
  induction p with
  | nil =>
    simp [Quiver.Hom.toPath, homotopyOnPath]
  | cons p b ih =>
    simp only [Quiver.Path.comp_cons, homotopyOnPath, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, QuiverRepresentation.mapPath_comp, QuiverRepresentation.mapPath_toPath]
    rw [ih, smul_add, genOne_cons, add_assoc]

private theorem boundary_homotopyOnPath {i j : Q} (p : Quiver.Path i j) (x : V.vertex i) :
    boundary V (homotopyOnPath V p x) =
      genZero V p x - genZero V (.nil : Quiver.Path j j) (V.mapPath p x) := by
  induction p with
  | nil => simp [homotopyOnPath]
  | cons p a ih =>
    simp only [homotopyOnPath, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      map_add, map_smul, ih, boundary_genOne, Quiver.Path.comp_nil, QuiverRepresentation.mapPath_cons]
    rw [smul_sub, ← genZero_cons, ← genZero_cons]
    change _ + (genZero V ((Quiver.Path.nil : Quiver.Path _ _).cons a) _ - _) = _
    abel

private theorem tensor_ext_basis {M N L : Type*} [AddCommMonoid M] [Module k M]
    [AddCommMonoid N] [Module k N] [AddCommMonoid L] [Module k L]
    {ι : Type*} (b : Module.Basis ι k M) {f g : M ⊗[k] N →ₗ[k] L}
    (h : ∀ (i : ι) (x : N), f (b i ⊗ₜ[k] x) = g (b i ⊗ₜ[k] x)) : f = g :=
  TensorProduct.curry_injective (b.ext fun i => LinearMap.ext (h i))

private theorem degreeZero_ext {L : Type*} [AddCommMonoid L] [Module k L]
    {f g : DegreeZero V →ₗ[k] L}
    (h : ∀ {i j : Q} (p : Quiver.Path i j) (x : V.vertex i),
      f (genZero V p x) = g (genZero V p x)) : f = g := by
  apply DirectSum.linearMap_ext
  intro i
  apply tensor_ext_basis (pathsBasis (k := k) i)
  rintro ⟨j, p⟩ x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, pathsBasis_apply]
  exact h p x

private theorem degreeOne_ext {L : Type*} [AddCommMonoid L] [Module k L]
    {f g : DegreeOne V →ₗ[k] L}
    (h : ∀ {i j l : Q} (a : i ⟶ j) (p : Quiver.Path j l) (x : V.vertex i),
      f (genOne V a p x) = g (genOne V a p x)) : f = g := by
  apply DirectSum.linearMap_ext
  rintro ⟨i, j, a⟩
  apply tensor_ext_basis (pathsBasis (k := k) j)
  rintro ⟨l, p⟩ x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, pathsBasis_apply]
  exact h a p x

private def homotopy : DegreeZero V →ₗ[k] DegreeOne V :=
  DirectSum.toModule k Q _ fun i =>
    TensorProduct.lift ((pathsBasis (k := k) i).constr k fun p => homotopyOnPath V p.2)

private theorem homotopy_genZero {i j : Q} (p : Quiver.Path i j) (x : V.vertex i) :
    homotopy V (genZero V p x) = homotopyOnPath V p x := by
  change homotopy V
    (DirectSum.lof k Q (fun j => VertexProjective k j ⊗[k] V.vertex j) i
      (pathVector p ⊗ₜ[k] x)) = _
  rw [homotopy, DirectSum.toModule_lof, TensorProduct.lift.tmul, ← pathsBasis_apply p,
    Module.Basis.constr_basis]

private def sectionAugmentation : Target V →ₗ[k] DegreeZero V :=
  (DirectSum.toModule k Q _ fun i => genZero V (Quiver.Path.nil : Quiver.Path i i)).comp
    (QuiverModuleEquivalence.coordinates V).toLinearMap

private theorem section_point (i : Q) (x : V.vertex i) :
    sectionAugmentation V (point V i x) = genZero V (.nil : Quiver.Path i i) x := by
  change (DirectSum.toModule k Q _ fun i => genZero V (Quiver.Path.nil : Quiver.Path i i))
    (QuiverModuleEquivalence.coordinates V (point V i x)) = _
  rw [coordinates_point]
  dsimp [PathOperators.inclusion, PathOperatorsSpec.inclusion]
  rw [DirectSum.toModule_lof]

theorem boundary_injective : Function.Injective (boundary V) := by
  let f : DegreeOne V →ₗ[k] DegreeOne V := (homotopy V).comp ((boundary V).restrictScalars k)
  have h : f = LinearMap.id := by
    refine degreeOne_ext V (f := f) ?_
    intro i j l a p x
    change homotopy V (boundary V (genOne V a p x)) = genOne V a p x
    rw [boundary_genOne, map_sub, homotopy_genZero, homotopy_genZero, homotopyOnPath_first]
    abel
  exact Function.LeftInverse.injective
    (g := homotopy V) (fun x => LinearMap.congr_fun h x)

theorem augmentation_surjective : Function.Surjective (augmentation V) := by
  let s : PathOperators.Total V →ₗ[k] DegreeZero V :=
    DirectSum.toModule k Q _ fun i => genZero V (Quiver.Path.nil : Quiver.Path i i)
  have h : ((augmentation V).restrictScalars k).comp s =
      (QuiverModuleEquivalence.coordinates V).symm.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change augmentation V (s (PathOperators.inclusion V i x)) = point V i x
    dsimp [s, PathOperators.inclusion, PathOperatorsSpec.inclusion]
    rw [DirectSum.toModule_lof, augmentation_genZero,
      QuiverRepresentation.mapPath_nil, LinearMap.id_apply]
  intro y
  refine ⟨sectionAugmentation V y, ?_⟩
  change augmentation V (s (QuiverModuleEquivalence.coordinates V y)) = y
  exact (LinearMap.congr_fun h _).trans ((QuiverModuleEquivalence.coordinates V).symm_apply_apply y)

private theorem augmentation_boundary :
    (augmentation V).comp (boundary V) = 0 := by
  apply LinearMap.restrictScalars_injective k
  apply degreeOne_ext V
  intro i j l a p x
  change augmentation V (boundary V (genOne V a p x)) = 0
  rw [boundary_genOne, map_sub, augmentation_genZero, augmentation_genZero,
    QuiverRepresentation.mapPath_comp, QuiverRepresentation.mapPath_toPath,
    LinearMap.comp_apply, sub_self]

theorem boundary_augmentation_exact : Function.Exact (boundary V) (augmentation V) := by
  have h : ((boundary V).restrictScalars k).comp (homotopy V) +
      (sectionAugmentation V).comp ((augmentation V).restrictScalars k) =
      (LinearMap.id : DegreeZero V →ₗ[k] DegreeZero V) := by
    apply degreeZero_ext V
    intro i j p x
    change boundary V (homotopy V (genZero V p x)) +
      sectionAugmentation V (augmentation V (genZero V p x)) = genZero V p x
    rw [homotopy_genZero, boundary_homotopyOnPath, augmentation_genZero, section_point,
      sub_add_cancel]
  intro y
  constructor
  · intro hy
    refine ⟨homotopy V y, ?_⟩
    have hy' := LinearMap.congr_fun h y
    change boundary V (homotopy V y) + sectionAugmentation V (augmentation V y) = y at hy'
    rw [hy, map_zero, add_zero] at hy'
    exact hy'
  · rintro ⟨x, rfl⟩
    exact LinearMap.congr_fun (augmentation_boundary V) x

theorem tensor_left_action : TensorLeftAction.{u, v, w, d} := by
  intro k Q _ _ _ V i j r p x
  exact TensorProduct.smul_tmul' r p x

theorem degreeZero_projective : Module.Projective A (DegreeZero V) := by
  let (i : Q) : Module.Projective A (VertexProjective k i ⊗[k] V.vertex i) := inferInstance
  exact Module.Projective.directSum

theorem degreeOne_projective : Module.Projective A (DegreeOne V) := by
  let (a : Arrow Q) : Module.Projective A (VertexProjective k a.2.1 ⊗[k] V.vertex a.1) :=
    inferInstance
  exact Module.Projective.directSum

private theorem finitePaths (L : Type w) [Field L] [Finite (Arrow Q)] (h : ¬ HasOrientedCycle Q) :
    Finite (Path Q) := by
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · let : IsEmpty (Path Q) := ⟨fun p => hQ.false p.1⟩
    infer_instance
  · let : FiniteDimensional L (PathAlgebra L Q) :=
      PathAlgebra.finiteDimensional_iff_no_orientedCycle.mpr h
    exact Module.Finite.finite_basis (PathAlgebra.basis L Q)

private theorem smallTensor [Finite (Path Q)] (i : Q) (M : ModuleCat.{d} k) :
    Small.{d} (VertexProjective k i ⊗[k] M) := by
  have : Finite (Σ j, Quiver.Path i j) :=
    Finite.of_injective (fun p => (⟨i, p⟩ : Path Q))
      (fun _ _ h => @sigma_mk_injective Q (fun t => Σ j, Quiver.Path t j) i _ _ h)
  let F : Fintype (Σ j, Quiver.Path i j) := Fintype.ofFinite _
  let : Small.{d} (Σ j, Quiver.Path i j) := small_map (Fintype.equivFin _)
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := M) (pathsBasis (k := k) i)
  exact small_of_injective (f := fun z => (e z : (Σ j, Quiver.Path i j) → M))
    (fun _ _ h => e.injective (Finsupp.ext (congrFun h)))

private theorem smallDirectSum {ι : Type*} [Finite ι] (M : ι → Type*)
    [∀ i, AddCommMonoid (M i)] [∀ i, Small.{d} (M i)] : Small.{d} (⨁ i, M i) := by
  let : Fintype ι := Fintype.ofFinite _
  let : Small.{d} ι := small_map (Fintype.equivFin ι)
  exact small_of_injective (f := fun x : ⨁ i, M i => (x : ∀ i, M i))
    (fun _ _ h => DFinsupp.ext (congrFun h))

private theorem smallDegreeZero [Finite (Path Q)] : Small.{d} (DegreeZero V) := by
  let (i : Q) := smallTensor (k := k) i (V.vertex i)
  exact smallDirectSum (fun i : Q => VertexProjective k i ⊗[k] V.vertex i)

private theorem smallDegreeOne [Finite (Path Q)] [Finite (Arrow Q)] :
    Small.{d} (DegreeOne V) := by
  let (a : Arrow Q) := smallTensor (k := k) a.2.1 (V.vertex a.1)
  exact smallDirectSum (fun a : Arrow Q => VertexProjective k a.2.1 ⊗[k] V.vertex a.1)

section ShortExact

open Limits ZeroObject

variable {C : Type*} [Category C] [Abelian C] [HasZeroObject C] (S : ShortComplex C)

private def twoTermObjects : ℕ → C
  | 0 => S.X₂
  | 1 => S.X₁
  | _ + 2 => 0

private def twoTermDiff : ∀ n, twoTermObjects S (n + 1) ⟶ twoTermObjects S n
  | 0 => S.f
  | _ + 1 => 0

private def twoTermComplex : ChainComplex C ℕ :=
  ChainComplex.of (twoTermObjects S) (twoTermDiff S) fun n => by
    change (0 : twoTermObjects S (n + 2) ⟶ twoTermObjects S (n + 1)) ≫ _ = 0
    exact zero_comp

private theorem twoTermComplex_d (n : ℕ) :
    (twoTermComplex S).d (n + 1) n = twoTermDiff S n :=
  ChainComplex.of_d _ _ n

private theorem twoTermExactAt (h : S.ShortExact) (n : ℕ) :
    (twoTermComplex S).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  cases n with
  | zero =>
    refine (ShortComplex.exact_iff_mono _ (twoTermComplex_d S 1)).2 ?_
    change Mono ((twoTermComplex S).d 1 0)
    rw [twoTermComplex_d S 0]
    exact h.mono_f
  | succ n =>
    apply ShortComplex.exact_of_isZero_X₂
    change IsZero (0 : C)
    exact isZero_zero C

private def twoTermAugmentation : twoTermComplex S ⟶ (ChainComplex.single₀ C).obj S.X₃ :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨S.g, by
    rw [twoTermComplex_d S 0]
    exact S.zero⟩

private theorem twoTermAugmentation_zero : (twoTermAugmentation S).f 0 = S.g := by
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

private def twoTermResolution (h : S.ShortExact) (h₀ : Projective S.X₂)
    (h₁ : Projective S.X₁) : ProjectiveResolution S.X₃ where
  complex := twoTermComplex S
  projective n := by
    obtain (_ | _ | n) := n
    · exact h₀
    · exact h₁
    · change Projective (0 : C)
      infer_instance
  π := twoTermAugmentation S
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨h.exact, h.epi_g⟩
        refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
        · change 𝟙 _ ≫ S.f = (twoTermComplex S).d 1 0 ≫ 𝟙 _
          rw [Category.comp_id, Category.id_comp, twoTermComplex_d S 0]
          rfl
        · change 𝟙 _ ≫ S.g = (twoTermAugmentation S).f 0 ≫ 𝟙 _
          rw [Category.comp_id, Category.id_comp, twoTermAugmentation_zero]
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact twoTermExactAt S h n
      · exact ChainComplex.exactAt_succ_single_obj _ n⟩

end ShortExact

/-- The path resolution in the universe of the actual module associated to the
representation. The first two objects carry coordinates in the tensor sums. -/
def resolutionData [Fintype (Arrow Q)] (h : ¬ HasOrientedCycle Q) : Resolution V := by
  letI := finitePaths k h
  letI := smallDegreeZero V
  letI := smallDegreeOne V
  let e₀ : Shrink.{d} (DegreeZero V) ≃ₗ[A] DegreeZero V := Shrink.linearEquiv A _
  let e₁ : Shrink.{d} (DegreeOne V) ≃ₗ[A] DegreeOne V := Shrink.linearEquiv A _
  let f : Shrink.{d} (DegreeOne V) →ₗ[A] Shrink.{d} (DegreeZero V) :=
    e₀.symm.toLinearMap.comp ((boundary V).comp e₁.toLinearMap)
  let g : Shrink.{d} (DegreeZero V) →ₗ[A] Target V :=
    (augmentation V).comp e₀.toLinearMap
  have hf (x : Shrink.{d} (DegreeOne V)) : e₀ (f x) = boundary V (e₁ x) :=
    e₀.apply_symm_apply _
  have hg (y : Shrink.{d} (DegreeZero V)) : g y = augmentation V (e₀ y) := rfl
  have hzero : g.comp f = 0 := by
    apply LinearMap.ext
    intro x
    change g (f x) = 0
    rw [hg, hf]
    exact LinearMap.congr_fun (augmentation_boundary V) _
  let S : ShortComplex (ModuleCat.{d} A) :=
    ModuleCat.shortComplexOfCompEqZero (R := A) (M := Shrink.{d} (DegreeOne V))
      (N := Shrink.{d} (DegreeZero V)) (L := Target V) f g hzero
  have hS : S.ShortExact := by
    apply ModuleCat.shortComplex_shortExact S
    · intro y
      change g y = 0 ↔ y ∈ Set.range f
      rw [hg, boundary_augmentation_exact V]
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨e₁.symm x, e₀.injective ?_⟩
        rw [hf, e₁.apply_symm_apply, hx]
      · rintro ⟨x, rfl⟩
        exact ⟨e₁ x, (hf x).symm⟩
    · intro x y hxy
      change f x = f y at hxy
      apply e₁.injective
      apply boundary_injective V
      simpa only [hf] using congrArg e₀ hxy
    · intro y
      obtain ⟨x, hx⟩ := augmentation_surjective V y
      refine ⟨e₀.symm x, ?_⟩
      change g (e₀.symm x) = y
      rw [hg, e₀.apply_symm_apply, hx]
  letI := degreeZero_projective V
  letI := degreeOne_projective V
  have h₀ : Projective S.X₂ := ModuleCat.projective_of_categoryTheory_projective _
  have h₁ : Projective S.X₁ := ModuleCat.projective_of_categoryTheory_projective _
  refine
    { boundary := boundary V
      augmentation := augmentation V
      boundary_tmul := boundary_tmul V
      augmentation_path := fun p x => augmentation_path V p x
      injective_boundary := boundary_injective V
      exact := boundary_augmentation_exact V
      surjective_augmentation := augmentation_surjective V
      resolution := twoTermResolution S hS h₀ h₁
      degreeZero := e₀
      degreeOne := e₁
      differential := ?_
      augment := ?_
      higher := ?_ }
  · intro x
    change e₀ ((twoTermComplex S).d 1 0 x) = _
    rw [twoTermComplex_d S 0]
    exact hf x
  · intro x
    change (twoTermAugmentation S).f 0 x = _
    rw [twoTermAugmentation_zero]
    exact hg x
  · intro n
    change Limits.IsZero (0 : ModuleCat.{d} A)
    exact Limits.isZero_zero _

theorem exists_resolution : ResolutionExists.{u, v, w, d} := by
  intro k Q _ _ _ _ h V
  exact ⟨resolutionData V.obj h⟩

end

end RepTheorySurvey.Quiver.PathResolution
