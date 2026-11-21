import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.FreeComplexReplacement
import MathGenome.Internal.AlgebraCore.P103.Ch10.ProjectiveResolutions
import MathGenome.Internal.AlgebraCore.P103.Ch10.Complexes
import MathGenome.Internal.AlgebraCore.P103.Ch10.HomologySequence
import MathGenome.Internal.AlgebraCore.P103.Ch10.TotalComplexAssembly
import MathGenome.Internal.AlgebraCore.P103.Ch02.FlatnessTests
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

noncomputable section
universe u v
namespace P103.Ch11.FreeComplexReplacement
open CategoryTheory P103.Specs.Ch10.Complexes
open P103.Specs.Ch11.FreeComplexReplacement
variable {R : Type u} [Ring R]

/-- All elements in degree zero of a nonnegative chain complex are cycles. -/
theorem mem_cycles_zero (D : ChainComplex (ModuleCat.{v} R) ℕ) (x : D.X 0) :
    x ∈ cycles D 0 := by
  change (D.d 0 ((ComplexShape.down ℕ).next 0)).hom x = 0
  rw [ChainComplex.next_nat_zero, D.shape 0 0 (by simp)]
  rfl

/-- A single induction stage retains exactly the cycles needed for the next cover. -/
structure Stage (D : ChainComplex (ModuleCat.{max u v} R) ℕ) (n : ℕ) where
  X : ModuleCat.{max u v} R
  Z : Submodule R X
  f : X →ₗ[R] D.X n
  maps_cycles : ∀ z : Z, f z.val ∈ cycles D n
  lifts_cycles : ∀ y : cycles D n, ∃ z : Z, f z.val = y.val

variable (D : ChainComplex (ModuleCat.{max u v} R) ℕ)
open P103.Ch10.ProjectiveResolutions (cover cover_surjective)

def initial : Stage D 0 where
  X := ModuleCat.of R (D.X 0 →₀ R)
  Z := ⊤
  f := cover (D.X 0)
  maps_cycles z := mem_cycles_zero D _
  lifts_cycles y := by
    obtain ⟨x, hx⟩ := cover_surjective (D.X 0) y.val
    exact ⟨⟨x, Submodule.mem_top⟩, hx⟩

/-- The pullback of the preceding cycle module and the next differential. -/
def matching {n : ℕ} (S : Stage D n) : Submodule R (S.X × D.X (n + 1)) where
  carrier := {x | x.1 ∈ S.Z ∧ S.f x.1 = (D.d (n + 1) n).hom x.2}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨S.Z.add_mem hx hy, by change S.f (x.1 + y.1) = (D.d (n + 1) n).hom (x.2 + y.2); simp only [map_add, hx', hy']⟩
  smul_mem' := by
    rintro r x ⟨hx, hx'⟩
    exact ⟨S.Z.smul_mem r hx, by change S.f (r • x.1) = (D.d (n + 1) n).hom (r • x.2); simp only [map_smul, hx']⟩

def stageCover {n : ℕ} (S : Stage D n) : (matching D S →₀ R) →ₗ[R] matching D S :=
  cover (ModuleCat.of R (matching D S))

def stageD {n : ℕ} (S : Stage D n) : (matching D S →₀ R) →ₗ[R] S.X :=
  (LinearMap.fst R S.X (D.X (n + 1))).comp ((matching D S).subtype.comp (stageCover D S))

def stageF {n : ℕ} (S : Stage D n) : (matching D S →₀ R) →ₗ[R] D.X (n + 1) :=
  (LinearMap.snd R S.X (D.X (n + 1))).comp ((matching D S).subtype.comp (stageCover D S))

theorem stage_comm {n : ℕ} (S : Stage D n) (x : matching D S →₀ R) :
    S.f (stageD D S x) = (D.d (n + 1) n).hom (stageF D S x) :=
  (stageCover D S x).property.2

def next {n : ℕ} (S : Stage D n) : Stage D (n + 1) where
  X := ModuleCat.of R (matching D S →₀ R)
  Z := LinearMap.ker (stageD D S)
  f := stageF D S
  maps_cycles z := by
    change (D.d (n + 1) ((ComplexShape.down ℕ).next (n + 1))).hom _ = 0
    rw [ChainComplex.next_nat_succ]
    rw [← stage_comm, z.property, map_zero]
  lifts_cycles y := by
    have hy : (D.d (n + 1) n).hom y.val = 0 := by
      have h := y.property
      change (D.d (n + 1) ((ComplexShape.down ℕ).next (n + 1))).hom y.val = 0 at h
      rw [ChainComplex.next_nat_succ] at h
      exact h
    let m : matching D S := ⟨(0, y.val), by simp [matching, hy]⟩
    obtain ⟨x, hx⟩ := cover_surjective (ModuleCat.of R (matching D S)) m
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change (stageCover D S x).val.1 = 0
      exact congrArg (fun a : matching D S => a.val.1) hx
    · change (stageCover D S x).val.2 = y.val
      exact congrArg (fun a : matching D S => a.val.2) hx

def stages : (n : ℕ) → Stage D n
  | 0 => initial D
  | n + 1 => next D (stages n)

def differential (n : ℕ) : (stages D (n + 1)).X →ₗ[R] (stages D n).X :=
  stageD D (stages D n)

theorem differential_square (n : ℕ) :
    (differential D n).comp (differential D (n + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  exact (stageCover D (stages D (n + 1)) x).property.1

def replacementComplex : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n => (stages D n).X)
    (fun n => ModuleCat.ofHom (differential D n)) (by
      intro n
      apply ModuleCat.hom_ext
      exact differential_square D n)

@[simp] theorem replacementComplex_d (n : ℕ) :
    ((replacementComplex D).d (n + 1) n).hom = differential D n := by
  simp only [replacementComplex, ChainComplex.of.d, dite_eq_left rfl,
    eqToHom_refl]
  rfl

/-- The second projections form a genuine map of the constructed complexes. -/
def replacementMap : replacementComplex D ⟶ D :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (stages D n).f) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (D.d (n + 1) n).hom ((stages D (n + 1)).f x) =
      (stages D n).f (((replacementComplex D).d (n + 1) n).hom x)
    rw [replacementComplex_d]
    exact (stage_comm D (stages D n) x).symm)

theorem replacement_cycles (n : ℕ) :
    cycles (replacementComplex D) n = (stages D n).Z := by
  cases n with
  | zero =>
    apply top_unique
    intro x _
    exact mem_cycles_zero _ x
  | succ n =>
    change LinearMap.ker ((replacementComplex D).d (n + 1)
      ((ComplexShape.down ℕ).next (n + 1))).hom = _
    rw [ChainComplex.next_nat_succ, replacementComplex_d]
    rfl

/-- Every compatible cycle and next-degree element lift together. -/
theorem lift_matching (n : ℕ) (z : cycles (replacementComplex D) n)
    (y : D.X (n + 1))
    (h : ((replacementMap D).f n).hom z.val = (D.d (n + 1) n).hom y) :
    ∃ x : (replacementComplex D).X (n + 1),
      ((replacementComplex D).d (n + 1) n).hom x = z.val ∧
      ((replacementMap D).f (n + 1)).hom x = y := by
  have hz : z.val ∈ (stages D n).Z := (replacement_cycles D n) ▸ z.property
  let m : matching D (stages D n) := ⟨(z.val, y), hz, h⟩
  obtain ⟨x, hx⟩ := cover_surjective (ModuleCat.of R (matching D (stages D n))) m
  refine ⟨x, ?_, ?_⟩
  · rw [replacementComplex_d]
    exact congrArg (fun a : matching D (stages D n) => a.val.1) hx
  · exact congrArg (fun a : matching D (stages D n) => a.val.2) hx

theorem replacement_lifts_cycles (n : ℕ) (y : cycles D n) :
    ∃ z : cycles (replacementComplex D) n,
      ((replacementMap D).f n).hom z.val = y.val := by
  obtain ⟨z, hz⟩ := (stages D n).lifts_cycles y
  refine ⟨⟨z.val, ?_⟩, hz⟩
  exact (replacement_cycles D n).symm ▸ z.property

theorem replacement_surjective (n : ℕ) : Function.Surjective ((replacementMap D).f n).hom := by
  cases n with
  | zero => exact cover_surjective (D.X 0)
  | succ n =>
    intro y
    have hc : (D.d (n + 1) n).hom y ∈ cycles D n := by
      apply boundaryInclusion D n
      change ∃ x, (D.d ((ComplexShape.down ℕ).prev n) n).hom x = _
      rw [ChainComplex.prev]
      exact ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := replacement_lifts_cycles D n ⟨_, hc⟩
    obtain ⟨x, _, hx⟩ := lift_matching D n z y hz
    exact ⟨x, hx⟩

theorem replacement_free (n : ℕ) : Module.Free R ((replacementComplex D).X n) := by
  cases n with
  | zero => change Module.Free R (D.X 0 →₀ R); infer_instance
  | succ n => change Module.Free R (matching D (stages D n) →₀ R); infer_instance

theorem replacement_quasiIsomorphism : QuasiIsomorphism (replacementMap D) := by
  intro n
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro h hh
    obtain ⟨z, rfl⟩ := (cycleBoundaries (replacementComplex D) n).mkQ_surjective h
    have hh' : homologyClass D n (cyclesMap (replacementMap D) n z) = 0 := hh
    have hb := (Submodule.Quotient.mk_eq_zero (cycleBoundaries D n)).mp hh'
    change ((replacementMap D).f n).hom z.val ∈
      LinearMap.range (D.d ((ComplexShape.down ℕ).prev n) n).hom at hb
    rw [ChainComplex.prev] at hb
    obtain ⟨y, hy⟩ := hb
    obtain ⟨x, hx, _⟩ := lift_matching D n z y hy.symm
    apply (Submodule.Quotient.mk_eq_zero (cycleBoundaries (replacementComplex D) n)).mpr
    change ∃ x, ((replacementComplex D).d ((ComplexShape.down ℕ).prev n) n).hom x = z.val
    rw [ChainComplex.prev]
    exact ⟨x, hx⟩
  · intro h
    obtain ⟨y, rfl⟩ := (cycleBoundaries D n).mkQ_surjective h
    obtain ⟨z, hz⟩ := replacement_lifts_cycles D n y
    refine ⟨homologyClass (replacementComplex D) n z, ?_⟩
    change homologyClass D n (cyclesMap (replacementMap D) n z) = homologyClass D n y
    congr 1
    exact Subtype.ext hz

/-- A kernel cycle is filled by lifting the compatible pair (z,0). -/
theorem replacement_kernel_acyclic : Acyclic (kernelComplex (replacementMap D)) := by
  intro n
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro z _
  let zQ : cycles (replacementComplex D) n := ⟨z.val.val, by
    have h := congrArg Subtype.val z.property
    exact h⟩
  obtain ⟨x, hx, hf⟩ := lift_matching D n zQ 0 (by
    change ((replacementMap D).f n).hom z.val.val = (D.d (n + 1) n).hom 0
    rw [z.val.property, map_zero])
  change ∃ x : (kernelComplex (replacementMap D)).X ((ComplexShape.down ℕ).prev n),
    ((kernelComplex (replacementMap D)).d ((ComplexShape.down ℕ).prev n) n).hom x = z.val
  rw [ChainComplex.prev]
  refine ⟨⟨x, hf⟩, ?_⟩
  apply Subtype.ext
  exact hx

theorem exists_free_replacement : exists_free_replacementType.{u,v} := by
  intro R _ D
  exact ⟨replacementComplex D, replacementMap D,
    replacement_free D, replacement_surjective D,
    replacement_quasiIsomorphism D, replacement_kernel_acyclic D⟩

theorem exists_right_free_replacement : exists_right_free_replacementType.{u,v} := by
  intro R _ D
  exact exists_free_replacement Rᵐᵒᵖ D


section TotalComparison
set_option backward.isDefEq.respectTransparency false
open scoped DirectSum
open P103.Specs.Ch10.TotalComplexAssembly
open P103.Specs.Ch10.HomologySequence

/-- The total map acts on the algebraic direct sum component by component. -/
theorem total_map_coordinates {K L : ChainBicomplex.{u,v} R} (f : K ⟶ L)
    (n : ℤ) (x : (total K).X n) :
    totalTermEquiv L n (((HomologicalComplex₂.total.map f (ComplexShape.down ℤ)).f n).hom x) =
      DirectSum.lmap (fun i : {i : ℤ × ℤ // i.1 + i.2 = n} =>
        ((f.f i.val.1).f i.val.2).hom) (totalTermEquiv K n x) := by
  classical
  let a : (total K).X n ⟶ ModuleCat.of R
      (⨁ i : {i : ℤ × ℤ // i.1 + i.2 = n}, diagonalFamily L n i) :=
    (HomologicalComplex₂.total.map f (ComplexShape.down ℤ)).f n ≫
      ModuleCat.ofHom (totalTermEquiv L n).toLinearMap
  let b : (total K).X n ⟶ ModuleCat.of R
      (⨁ i : {i : ℤ × ℤ // i.1 + i.2 = n}, diagonalFamily L n i) :=
    ModuleCat.ofHom ((DirectSum.lmap (fun i : {i : ℤ × ℤ // i.1 + i.2 = n} =>
      ((f.f i.val.1).f i.val.2).hom)).comp (totalTermEquiv K n).toLinearMap)
  have hab : a = b := by
    apply P103.Ch10.TotalComplexAssembly.total_hom_ext K n
    intro p q h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have hf := congrArg (fun t => t.hom z)
      (HomologicalComplex₂.ιTotal_map K L f (ComplexShape.down ℤ) p q n h)
    change ((HomologicalComplex₂.total.map f (ComplexShape.down ℤ)).f n).hom
      ((totalInclusion K p q n h).hom z) =
        (totalInclusion L p q n h).hom (((f.f p).f q).hom z) at hf
    change totalTermEquiv L n
      (((HomologicalComplex₂.total.map f (ComplexShape.down ℤ)).f n).hom
        ((totalInclusion K p q n h).hom z)) =
      DirectSum.lmap (fun i : {i : ℤ × ℤ // i.1 + i.2 = n} =>
        ((f.f i.val.1).f i.val.2).hom)
        (totalTermEquiv K n ((totalInclusion K p q n h).hom z))
    rw [hf, P103.Ch10.TotalComplexAssembly.totalTermEquiv_inclusion,
      P103.Ch10.TotalComplexAssembly.totalTermEquiv_inclusion, DirectSum.lmap_lof]
  exact congrArg (fun t => t.hom x) hab

/-- Direct sums preserve exactness without cardinality restrictions. -/
theorem directSum_exact {ι : Type*} {A B C : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (C i)]
    [∀ i, Module R (A i)] [∀ i, Module R (B i)] [∀ i, Module R (C i)]
    (f : ∀ i, A i →ₗ[R] B i) (g : ∀ i, B i →ₗ[R] C i)
    (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (DirectSum.lmap f) (DirectSum.lmap g) := by
  rw [LinearMap.exact_iff, DirectSum.range_lmap, DirectSum.ker_lmap]
  congr 2
  funext i
  exact (LinearMap.exact_iff.mp (h i))

/-- A componentwise short exact sequence of bicomplexes stays short exact
on their canonical algebraic direct-sum totals. -/
theorem total_degreewiseExact {E K L : ChainBicomplex.{u,v} R}
    (i : E ⟶ K) (p : K ⟶ L)
    (h : ∀ a b, Function.Injective ((i.f a).f b).hom ∧
      Function.Exact ((i.f a).f b).hom ((p.f a).f b).hom ∧
      Function.Surjective ((p.f a).f b).hom) :
    DegreewiseExact (HomologicalComplex₂.total.map i (ComplexShape.down ℤ))
      (HomologicalComplex₂.total.map p (ComplexShape.down ℤ)) := by
  intro n
  let F := fun j : {j : ℤ × ℤ // j.1 + j.2 = n} => ((i.f j.val.1).f j.val.2).hom
  let G := fun j : {j : ℤ × ℤ // j.1 + j.2 = n} => ((p.f j.val.1).f j.val.2).hom
  have hi := (DirectSum.lmap_injective F).mpr (fun j => (h _ _).1)
  have he := directSum_exact F G (fun j => (h _ _).2.1)
  have hp := (DirectSum.lmap_surjective G).mpr (fun j => (h _ _).2.2)
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    apply (totalTermEquiv E n).injective
    apply hi
    simp only [F, ← total_map_coordinates, hxy]
  · intro x
    constructor
    · intro hx
      have hz : DirectSum.lmap G (totalTermEquiv K n x) = 0 := by
        dsimp only [G]
        rw [← total_map_coordinates, hx, map_zero]
      obtain ⟨y, hy⟩ := (he _).mp hz
      refine ⟨(totalTermEquiv E n).symm y, ?_⟩
      apply (totalTermEquiv K n).injective
      rw [total_map_coordinates, LinearEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨y, rfl⟩
      apply (totalTermEquiv L n).injective
      rw [total_map_coordinates, total_map_coordinates, map_zero]
      exact (he _).mpr ⟨_, rfl⟩
  · intro y
    obtain ⟨x, hx⟩ := hp (totalTermEquiv L n y)
    refine ⟨(totalTermEquiv K n).symm x, ?_⟩
    apply (totalTermEquiv L n).injective
    rw [total_map_coordinates, LinearEquiv.apply_symm_apply]
    exact hx

/-- An acyclic first term in a short exact sequence gives a quasi-isomorphism. -/
theorem quasiIsomorphism_of_acyclic_left {A B C : Chain.{u,v} R}
    (i : A ⟶ B) (p : B ⟶ C) (hs : DegreewiseExact i p) (ha : Acyclic A) :
    QuasiIsomorphism p := by
  obtain ⟨δ, hδ⟩ := P103.Ch10.HomologySequence.chainSequence i p hs
  intro n
  have h := P103.Ch10.HomologySequence.zero_endpoints i p n (n - 1) (δ n) (hδ n).2
  exact ⟨h.1 (ha n), h.2.2.1 (ha (n - 1))⟩

/-- First-quadrant assembly applied to an explicit short exact kernel model. -/
theorem total_quasiIsomorphism_of_exact {E K L : ChainBicomplex.{u,v} R}
    (i : E ⟶ K) (p : K ⟶ L)
    (h : ∀ a b, Function.Injective ((i.f a).f b).hom ∧
      Function.Exact ((i.f a).f b).hom ((p.f a).f b).hom ∧
      Function.Surjective ((p.f a).f b).hom)
    (a b : ℤ) (hs : SupportedQuadrant E a b)
    (ha : ColumnsAcyclic E ∨ RowsAcyclic E) :
    (∀ n, Function.Surjective
      ((HomologicalComplex₂.total.map p (ComplexShape.down ℤ)).f n).hom) ∧
    QuasiIsomorphism (HomologicalComplex₂.total.map p (ComplexShape.down ℤ)) := by
  have he := total_degreewiseExact i p h
  exact ⟨fun n => (he n).2.2, quasiIsomorphism_of_acyclic_left _ _ he
    (P103.Ch10.TotalComplexAssembly.chain_acyclic_of_columns_or_rows E a b hs ha)⟩
end TotalComparison


section TensorConstruction
set_option backward.isDefEq.respectTransparency false
open P103.BalancedTensor

/-- Tensoring a left complex with a fixed right module gives a complex of
abelian groups, represented as integer modules. -/
def tensorColumn (A : ModuleCat.{v} Rᵐᵒᵖ)
    (D : ChainComplex (ModuleCat.{v} R) ℤ) : ChainComplex (ModuleCat.{v} ℤ) ℤ where
  X q := ModuleCat.of ℤ (Tensor R A (D.X q))
  d q q' := ModuleCat.ofHom (map (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A)
    (D.d q q').hom).toIntLinearMap
  shape q q' h := by
    simp only [D.shape q q' h, ModuleCat.hom_zero, map_zero_right]
    rfl
  d_comp_d' q q' q'' _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply P103.BalancedTensor.hom_ext
    intro x y
    change tmul R x ((D.d q' q'').hom ((D.d q q').hom y)) = 0
    rw [P103.Ch10.HomologySequence.square_zero, tmul_zero]

def tensorHorizontal {A B : ModuleCat.{v} Rᵐᵒᵖ} (f : A ⟶ B)
    (D : ChainComplex (ModuleCat.{v} R) ℤ) : tensorColumn A D ⟶ tensorColumn B D where
  f q := ModuleCat.ofHom (map f.hom (LinearMap.id : D.X q →ₗ[R] D.X q)).toIntLinearMap
  comm' q q' _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply P103.BalancedTensor.hom_ext
    intro x y
    rfl

/-- The commuting tensor bicomplex; the upstream total inserts (-1)^p. -/
def tensorBicomplex (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{v} R) ℤ) :
    P103.Specs.Ch10.TotalComplexAssembly.ChainBicomplex.{0,v} ℤ where
  X p := tensorColumn (C.X p) D
  d p p' := tensorHorizontal (C.d p p') D
  shape p p' h := by
    apply HomologicalComplex.Hom.ext
    funext q
    simp only [tensorHorizontal, C.shape p p' h, ModuleCat.hom_zero, map_zero_left]
    rfl
  d_comp_d' p p' p'' _ _ := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply P103.BalancedTensor.hom_ext
    intro x y
    change tmul R ((C.d p' p'').hom ((C.d p p').hom x)) y = 0
    rw [P103.Ch10.HomologySequence.square_zero, zero_tmul]

/-- A concrete model of the source's balanced tensor bicomplex. -/
def tensorModel (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{v} R) ℤ) : TensorModel C D where
  complex := tensorBicomplex C D
  termEquiv _ _ := LinearEquiv.refl ℤ _
  horizontal _ _ _ _ _ := rfl
  vertical _ _ _ _ _ := rfl

/-- Maps in both variables commute with the two bicomplex differentials. -/
def tensorBicomplexMap {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {D D' : ChainComplex (ModuleCat.{v} R) ℤ} (f : C ⟶ C') (g : D ⟶ D') :
    tensorBicomplex C D ⟶ tensorBicomplex C' D' where
  f p :=
    { f q := ModuleCat.ofHom (map (f.f p).hom (g.f q).hom).toIntLinearMap
      comm' q q' _ := by
        apply ModuleCat.hom_ext
        apply LinearMap.toAddMonoidHom_injective
        apply P103.BalancedTensor.hom_ext
        intro x y
        change tmul R ((f.f p).hom x) ((D'.d q q').hom ((g.f q).hom y)) =
          tmul R ((f.f p).hom x) ((g.f q').hom ((D.d q q').hom y))
        rw [P103.Ch10.HomologySequence.comm_apply] }
  comm' p p' _ := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply P103.BalancedTensor.hom_ext
    intro x y
    change tmul R ((C'.d p p').hom ((f.f p).hom x)) ((g.f q).hom y) =
      tmul R ((f.f p').hom ((C.d p p').hom x)) ((g.f q).hom y)
    rw [P103.Ch10.HomologySequence.comm_apply]

theorem tensorBicomplexMap_formula {C C' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ}
    {D D' : ChainComplex (ModuleCat.{v} R) ℤ} (f : C ⟶ C') (g : D ⟶ D') :
    IsTensorMap (tensorModel C D) (tensorModel C' D') f g (tensorBicomplexMap f g) := by
  intro p q x y
  rfl

end TensorConstruction


section ExactnessBridges
set_option backward.isDefEq.respectTransparency false
open P103.Specs.Ch10.HomologySequence
open P103.BalancedTensor P103.Specs.Ch02.FlatnessTests

/-- Explicit quotient acyclicity agrees with categorical exactness. -/
theorem acyclic_iff_exactAt {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) :
    Acyclic C ↔ ∀ n, C.ExactAt n := by
  constructor
  · intro h n
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (C.sc n)).mpr
    apply LinearMap.exact_iff.mpr
    exact ((P103.Ch10.Complexes.acyclic_iff C).mp h n).symm
  · intro h
    apply (P103.Ch10.Complexes.acyclic_iff C).mpr
    intro n
    have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (C.sc n)).mp (h n)
    exact (LinearMap.exact_iff.mp he).symm

/-- Extension by zero preserves acyclicity, including the endpoint degree. -/
theorem extend_acyclic {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (e : c.Embedding c')
    (h : Acyclic C) : Acyclic (C.extend e) := by
  apply (acyclic_iff_exactAt _).mpr
  intro n
  by_cases hn : ∃ j, e.f j = n
  · obtain ⟨j, hj⟩ := hn
    exact (C.extend_exactAt_iff e hj).mpr ((acyclic_iff_exactAt C).mp h j)
  · exact C.extend_exactAt e n (by simpa using hn)

/-- Exactness is invariant under specified equivalences of its three terms. -/
theorem exact_iff_of_equiv {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (a : A ≃+ A') (b : B ≃+ B') (c : C ≃+ C')
    (f : A →+ B) (g : B →+ C) (f' : A' →+ B') (g' : B' →+ C')
    (hf : ∀ x, b (f x) = f' (a x)) (hg : ∀ x, c (g x) = g' (b x)) :
    Function.Exact f g ↔ Function.Exact f' g' := by
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := b.surjective y
    constructor
    · intro hx
      have hz : g x = 0 := c.injective (by rw [hg, hx, map_zero])
      obtain ⟨z, hz⟩ := (h x).mp hz
      exact ⟨a z, by rw [← hf, hz]⟩
    · rintro ⟨z, hz⟩
      obtain ⟨t, rfl⟩ := a.surjective z
      have ht : f t = x := b.injective (by rw [hf, hz])
      rw [← hg, (h x).mpr ⟨t, ht⟩, map_zero]
  · intro h x
    constructor
    · intro hx
      have hz : g' (b x) = 0 := by rw [← hg, hx, map_zero]
      obtain ⟨z, hz⟩ := (h (b x)).mp hz
      refine ⟨a.symm z, b.injective ?_⟩
      rw [hf, AddEquiv.apply_symm_apply, hz]
    · rintro ⟨z, rfl⟩
      apply c.injective
      rw [hg, hf, (h _).mpr ⟨a z, rfl⟩, map_zero]

open private oppositeFlip oppositeFlip_tmul from MathGenome.Internal.AlgebraCore.P103.Ch02.FlatnessTests

/-- The exactness theorem in the original right-left tensor orientation. -/
theorem rightFlat_preserves_exact (M : Type (max u v)) [AddCommGroup M]
    [Module Rᵐᵒᵖ M] (h : RightFlat.{u,max u v,v} R M)
    {A B C : Type (max u v)} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (he : Function.Exact f g) :
    Function.Exact (map (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) f) (map LinearMap.id g) := by
  letI := doubleOppositeModule R A
  letI := doubleOppositeModule R B
  letI := doubleOppositeModule R C
  let fop : A →ₗ[Rᵐᵒᵖᵐᵒᵖ] B :=
    { f.toAddMonoidHom with map_smul' := fun r a => f.map_smul r.unop.unop a }
  let gop : B →ₗ[Rᵐᵒᵖᵐᵒᵖ] C :=
    { g.toAddMonoidHom with map_smul' := fun r a => g.map_smul r.unop.unop a }
  have hflat := (P103.Ch02.FlatnessTests.rightFlat_iff_opposite R M).mp h
  have hop := P103.Ch02.FlatnessTests.flat_preserves_exact Rᵐᵒᵖ M hflat A B C fop gop he
    (map fop LinearMap.id) (map gop LinearMap.id) (by intros; rfl) (by intros; rfl)
  apply (exact_iff_of_equiv (oppositeFlip (R := R) (A := M) (B := A))
    (oppositeFlip (R := R) (A := M) (B := B))
    (oppositeFlip (R := R) (A := M) (B := C))
    (map LinearMap.id f) (map LinearMap.id g)
    (map fop LinearMap.id) (map gop LinearMap.id) ?_ ?_).mpr hop
  all_goals
    intro z
    induction z using induction_on with
    | h0 => simp
    | ht a b => rfl
    | ha x y hx hy => simp [hx, hy]


/-- Flatness is unchanged by an isomorphism of the fixed tensor factor. -/
theorem flat_of_equiv {M N : Type (max u v)} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N) (h : Flat.{u,max u v,v} R N) :
    Flat.{u,max u v,v} R M := by
  apply (P103.Ch02.FlatnessTests.flat_iff_finiteRelations R M).mpr
  have hn := (P103.Ch02.FlatnessTests.flat_iff_finiteRelations R N).mp h
  intro n k x r hx
  obtain ⟨l, y, s, hy, hs⟩ := hn n k (fun i => e (x i)) r (by
    intro j
    simp only [← map_smul, ← map_sum, hx, map_zero])
  refine ⟨l, fun a => e.symm (y a), s, ?_, hs⟩
  intro i
  apply e.injective
  simpa only [map_sum, map_smul, LinearEquiv.apply_symm_apply] using hy i

theorem rightFlat_of_equiv {M N : Type (max u v)} [AddCommGroup M] [AddCommGroup N]
    [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ N] (e : M ≃ₗ[Rᵐᵒᵖ] N)
    (h : RightFlat.{u,max u v,v} R N) : RightFlat.{u,max u v,v} R M := by
  apply (P103.Ch02.FlatnessTests.rightFlat_iff_opposite R M).mpr
  exact flat_of_equiv e ((P103.Ch02.FlatnessTests.rightFlat_iff_opposite R N).mp h)

/-- Nonnegative extension retains termwise flatness in the original orientation. -/
theorem extend_rightFlat (C : ChainComplex (ModuleCat.{max u v} Rᵐᵒᵖ) ℕ)
    (h : ∀ p, RightFlat.{u,max u v,v} R (C.X p)) :
    ∀ p, RightFlat.{u,max u v,v} R ((extendNonnegativeChain C).X p) := by
  intro p
  by_cases hp : 0 ≤ p
  · have he : nonnegativeChainEmbedding.f p.toNat = p := Int.toNat_of_nonneg hp
    exact rightFlat_of_equiv (C.extendXIso nonnegativeChainEmbedding he).toLinearEquiv (h _)
  · haveI := P103.Ch10.Complexes.extendNonnegativeChain_supported C p hp
    intro A B _ _ _ _ f hf F hF
    exact Function.injective_of_subsingleton F

theorem extend_flat (D : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (h : ∀ q, Flat.{u,max u v,v} R (D.X q)) :
    ∀ q, Flat.{u,max u v,v} R ((extendNonnegativeChain D).X q) := by
  intro q
  by_cases hq : 0 ≤ q
  · have he : nonnegativeChainEmbedding.f q.toNat = q := Int.toNat_of_nonneg hq
    exact flat_of_equiv (D.extendXIso nonnegativeChainEmbedding he).toLinearEquiv (h _)
  · haveI := P103.Ch10.Complexes.extendNonnegativeChain_supported D q hq
    intro A B _ _ _ _ f hf F hF
    exact Function.injective_of_subsingleton F

/-- Degreewise short exactness survives extension by zero. -/
theorem extend_degreewiseExact {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {A B C : HomologicalComplex (ModuleCat.{v} R) c} (i : A ⟶ B) (p : B ⟶ C)
    (h : DegreewiseExact i p) (e : c.Embedding c') :
    DegreewiseExact (HomologicalComplex.extendMap i e) (HomologicalComplex.extendMap p e) := by
  intro n
  by_cases hn : ∃ j, e.f j = n
  · obtain ⟨j, hj⟩ := hn
    let a := (A.extendXIso e hj).toLinearEquiv
    let b := (B.extendXIso e hj).toLinearEquiv
    let c := (C.extendXIso e hj).toLinearEquiv
    have hi (x : (A.extend e).X n) :
        b (((HomologicalComplex.extendMap i e).f n).hom x) = (i.f j).hom (a x) := by
      simp [a, b, HomologicalComplex.extendMap_f i e hj]
    have hp (x : (B.extend e).X n) :
        c (((HomologicalComplex.extendMap p e).f n).hom x) = (p.f j).hom (b x) := by
      simp [b, c, HomologicalComplex.extendMap_f p e hj]
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy
      apply a.injective
      apply (h j).1
      rw [← hi, ← hi, hxy]
    · exact (exact_iff_of_equiv a.toAddEquiv b.toAddEquiv c.toAddEquiv
        ((HomologicalComplex.extendMap i e).f n).hom.toAddMonoidHom
        ((HomologicalComplex.extendMap p e).f n).hom.toAddMonoidHom
        (i.f j).hom.toAddMonoidHom (p.f j).hom.toAddMonoidHom hi hp).mpr (h j).2.1
    · intro y
      obtain ⟨x, hx⟩ := (h j).2.2 (c y)
      refine ⟨b.symm x, c.injective ?_⟩
      rw [hp, LinearEquiv.apply_symm_apply, hx]
  · haveI := ModuleCat.subsingleton_of_isZero (A.isZero_extend_X e n (by simpa using hn))
    haveI := ModuleCat.subsingleton_of_isZero (B.isZero_extend_X e n (by simpa using hn))
    haveI := ModuleCat.subsingleton_of_isZero (C.isZero_extend_X e n (by simpa using hn))
    refine ⟨Function.injective_of_subsingleton _, ?_, Function.surjective_to_subsingleton _⟩
    intro x
    exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩

/-- The kernel used in the replacement is an actual short exact kernel model. -/
def kernelInclusion {Q D : ChainComplex (ModuleCat.{v} R) ℕ} (f : Q ⟶ D) :
    kernelComplex f ⟶ Q where
  f n := ModuleCat.ofHom (LinearMap.ker (f.f n).hom).subtype
  comm' _ _ _ := rfl

theorem kernel_degreewiseExact {Q D : ChainComplex (ModuleCat.{v} R) ℕ} (f : Q ⟶ D)
    (h : ∀ n, Function.Surjective (f.f n).hom) : DegreewiseExact (kernelInclusion f) f := by
  intro n
  refine ⟨Subtype.val_injective, ?_, h n⟩
  intro x
  exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩

/-- A flat right module carries every acyclic left complex to an acyclic
complex of abelian groups. -/
theorem tensorColumn_acyclic (A : ModuleCat.{max u v} Rᵐᵒᵖ)
    (hA : RightFlat.{u,max u v,v} R A)
    (D : ChainComplex (ModuleCat.{max u v} R) ℤ) (hD : Acyclic D) :
    Acyclic (tensorColumn A D) := by
  apply (acyclic_iff_exactAt _).mpr
  intro n
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  exact rightFlat_preserves_exact A hA (D.d _ n).hom (D.d n _).hom
    (LinearMap.exact_iff.mpr ((P103.Ch10.Complexes.acyclic_iff D).mp hD n).symm)

theorem tensorRow_acyclic
    (C : ChainComplex (ModuleCat.{max u v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{max u v} R) ℤ) (q : ℤ)
    (hD : Flat.{u,max u v,v} R (D.X q)) (hC : Acyclic C) :
    Acyclic ((tensorBicomplex C D).flip.X q) := by
  apply (acyclic_iff_exactAt _).mpr
  intro n
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  exact P103.Ch02.FlatnessTests.flat_preserves_exact R (D.X q) hD
    (C.X _) (C.X n) (C.X _) (C.d _ n).hom (C.d n _).hom
    (LinearMap.exact_iff.mpr ((P103.Ch10.Complexes.acyclic_iff C).mp hC n).symm)
    (map (C.d _ n).hom LinearMap.id) (map (C.d n _).hom LinearMap.id)
    (by intros; rfl) (by intros; rfl)

end ExactnessBridges



section TensorComparison
set_option backward.isDefEq.respectTransparency false
open P103.Specs.Ch10.TotalComplexAssembly
open P103.Specs.Ch10.HomologySequence
open P103.BalancedTensor P103.Specs.Ch02.FlatnessTests

/-- Tensor short exactness when the fixed right terms are flat. -/
theorem tensor_degreewiseExact_left
    (C : ChainComplex (ModuleCat.{max u v} Rᵐᵒᵖ) ℤ)
    {A B D : ChainComplex (ModuleCat.{max u v} R) ℤ} (i : A ⟶ B) (p : B ⟶ D)
    (h : DegreewiseExact i p) (hC : ∀ a, RightFlat.{u,max u v,v} R (C.X a)) :
    ∀ a b, Function.Injective (((tensorBicomplexMap (𝟙 C) i).f a).f b).hom ∧
      Function.Exact (((tensorBicomplexMap (𝟙 C) i).f a).f b).hom
        (((tensorBicomplexMap (𝟙 C) p).f a).f b).hom ∧
      Function.Surjective (((tensorBicomplexMap (𝟙 C) p).f a).f b).hom := by
  intro a b
  have he := P103.HomTensorExactness.tensorSecond_rightExact (A := C.X a)
    (i.f b).hom (p.f b).hom (h b).2.1 (h b).2.2
    (map LinearMap.id (i.f b).hom) (map LinearMap.id (p.f b).hom)
    (by intros; rfl) (by intros; rfl)
  exact ⟨hC a (A.X b) (B.X b) (i.f b).hom (h b).1
    (map LinearMap.id (i.f b).hom) (by intros; rfl), he⟩

/-- Tensor short exactness when the fixed left terms are flat. -/
theorem tensor_degreewiseExact_right
    {A B C : ChainComplex (ModuleCat.{max u v} Rᵐᵒᵖ) ℤ}
    (D : ChainComplex (ModuleCat.{max u v} R) ℤ) (i : A ⟶ B) (p : B ⟶ C)
    (h : DegreewiseExact i p) (hD : ∀ b, Flat.{u,max u v,v} R (D.X b)) :
    ∀ a b, Function.Injective (((tensorBicomplexMap i (𝟙 D)).f a).f b).hom ∧
      Function.Exact (((tensorBicomplexMap i (𝟙 D)).f a).f b).hom
        (((tensorBicomplexMap p (𝟙 D)).f a).f b).hom ∧
      Function.Surjective (((tensorBicomplexMap p (𝟙 D)).f a).f b).hom := by
  intro a b
  exact (P103.Ch02.FlatnessTests.flat_iff_exact R (D.X b)).mp (hD b)
    (A.X a) (B.X a) (C.X a) (i.f a).hom (p.f a).hom (h a).1 (h a).2.1 (h a).2.2
    (map (i.f a).hom LinearMap.id) (map (p.f a).hom LinearMap.id)
    (by intros; rfl) (by intros; rfl)

/-- The tensor bicomplex of nonnegative factors is supported in the first quadrant. -/
theorem tensor_supported
    (C : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (D : ChainComplex (ModuleCat.{v} R) ℤ)
    (hC : SupportedIn C (Set.Ici (0 : ℤ))) (hD : SupportedIn D (Set.Ici (0 : ℤ))) :
    SupportedQuadrant (tensorBicomplex C D) 0 0 := by
  intro p q h
  change Subsingleton (Tensor R (C.X p) (D.X q))
  rcases h with hp | hq
  · haveI := hC p (not_le.mpr hp)
    infer_instance
  · haveI := hD q (not_le.mpr hq)
    infer_instance

/-- The left-module replacement comparison uses only the flat terms C_p. -/
theorem tensor_comparison_left : tensor_comparison_leftType.{u,v} := by
  intro R _ C Q D f hC hf
  let e := nonnegativeChainEmbedding
  let i := kernelInclusion f
  let j := HomologicalComplex.extendMap i e
  let g := HomologicalComplex.extendMap f e
  let C' := extendNonnegativeChain C
  let Q' := extendNonnegativeChain Q
  let D' := extendNonnegativeChain D
  let A' := extendNonnegativeChain (kernelComplex f)
  have he : DegreewiseExact j g :=
    extend_degreewiseExact i f (kernel_degreewiseExact f hf.2.1) e
  have hA : Acyclic A' := extend_acyclic _ e hf.2.2.2
  have hc : ∀ p, RightFlat.{u,max u v,v} R (C'.X p) := extend_rightFlat C hC
  refine ⟨tensorModel C' Q', tensorModel C' D', tensorBicomplexMap (𝟙 C') g,
    tensorBicomplexMap_formula _ _, ?_⟩
  apply total_quasiIsomorphism_of_exact (tensorBicomplexMap (𝟙 C') j)
    (tensorBicomplexMap (𝟙 C') g) (tensor_degreewiseExact_left C' j g he hc) 0 0
  · exact tensor_supported C' A'
      (P103.Ch10.Complexes.extendNonnegativeChain_supported C)
      (P103.Ch10.Complexes.extendNonnegativeChain_supported (kernelComplex f))
  · exact Or.inl (fun p => tensorColumn_acyclic (C'.X p) (hc p) A' hA)

/-- The right-module replacement comparison uses only the flat terms D_q. -/
theorem tensor_comparison_right : tensor_comparison_rightType.{u,v} := by
  intro R _ Q C D f hD hf
  let e := nonnegativeChainEmbedding
  let i := kernelInclusion f
  let j := HomologicalComplex.extendMap i e
  let g := HomologicalComplex.extendMap f e
  let Q' := extendNonnegativeChain Q
  let C' := extendNonnegativeChain C
  let D' := extendNonnegativeChain D
  let A' := extendNonnegativeChain (kernelComplex f)
  have he : DegreewiseExact j g :=
    extend_degreewiseExact i f (kernel_degreewiseExact f hf.2.1) e
  have hA : Acyclic A' := extend_acyclic _ e hf.2.2.2
  have hd : ∀ q, Flat.{u,max u v,v} R (D'.X q) := extend_flat D hD
  refine ⟨tensorModel Q' D', tensorModel C' D', tensorBicomplexMap g (𝟙 D'),
    tensorBicomplexMap_formula _ _, ?_⟩
  apply total_quasiIsomorphism_of_exact (tensorBicomplexMap j (𝟙 D'))
    (tensorBicomplexMap g (𝟙 D')) (tensor_degreewiseExact_right D' j g he hd) 0 0
  · exact tensor_supported A' D'
      (P103.Ch10.Complexes.extendNonnegativeChain_supported (kernelComplex f))
      (P103.Ch10.Complexes.extendNonnegativeChain_supported D)
  · exact Or.inr (fun q => tensorRow_acyclic A' D' q (hd q) hA)

end TensorComparison

end P103.Ch11.FreeComplexReplacement
