import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CartanEilenbergExistence
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.HorizontalInvariantExactness
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Existence of Cartan–Eilenberg injective resolutions (HA-G01)

Source: notes/002/advanced-homological-algebra.tex:2391–2450.
We construct a compatible embedding into a split row using injective
presentations of boundaries and cohomology. Iterating its cokernel gives
all four induced injective resolutions, with the prescribed horizontal bound.
HA-G07 is transferred to the categorical-image boundary functor of HA-G00.
-/

universe v u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

namespace AdvancedHomologicalAlgebra.CartanEilenbergExistence

open CartanEilenbergData

variable {C : Type u} [Category.{v} C] [Abelian C]

private noncomputable def kernelToAbelianImage (K : CochainComplex C ℤ) (p : ℤ) :=
  (HorizontalInvariantExactness.boundaryImageComparison C K p).choose

private lemma kernelToAbelianImage_hom_ι (K : CochainComplex C ℤ) (p : ℤ) :
    (kernelToAbelianImage K p).hom ≫ Abelian.image.ι (K.d (p - 1) p) =
      kernel.ι (K.pOpcycles p) :=
  (HorizontalInvariantExactness.boundaryImageComparison C K p).choose_spec

/-- The two boundary representations used by HA-G07 and HA-G00 agree over Kᵖ. -/
noncomputable def boundaryKernelIso (K : CochainComplex C ℤ) (p : ℤ) :
    _root_.Specs.AdvancedHomologicalAlgebra.HorizontalInvariantExactness.boundaries K p ≅
      (boundariesFunctor p).obj K :=
  kernelToAbelianImage K p ≪≫ Abelian.imageIsoImage (K.d (p - 1) p)

@[reassoc (attr := simp)]
lemma boundaryKernelIso_hom_ι (K : CochainComplex C ℤ) (p : ℤ) :
    (boundaryKernelIso K p).hom ≫ image.ι (K.d (p - 1) p) =
      kernel.ι (K.pOpcycles p) := by
  simp only [boundaryKernelIso, Iso.trans_hom, Category.assoc,
    Abelian.imageIsoImage_hom_comp_image_ι, kernelToAbelianImage_hom_ι]

@[reassoc]
lemma boundaryKernelIso_naturality {K J : CochainComplex C ℤ} (f : K ⟶ J) (p : ℤ) :
    _root_.Specs.AdvancedHomologicalAlgebra.HorizontalInvariantExactness.boundariesMap f p ≫
        (boundaryKernelIso J p).hom =
      (boundaryKernelIso K p).hom ≫ (boundariesFunctor p).map f := by
  apply (cancel_mono (image.ι (J.d (p - 1) p))).1
  simp [boundariesFunctor,
    _root_.Specs.AdvancedHomologicalAlgebra.HorizontalInvariantExactness.boundariesMap,
    image.map_homMk'_ι]

/-- HA-G07 as a short exact sequence for the actual shared boundary functor. -/
lemma boundaries_shortExact (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (hi : ∀ p, Mono (opcyclesMap S.f p)) (p : ℤ) :
    (S.map (boundariesFunctor p)).ShortExact := by
  let e : _root_.Specs.AdvancedHomologicalAlgebra.HorizontalInvariantExactness.boundarySequence
      S p ≅ S.map (boundariesFunctor p) :=
    ShortComplex.isoMk (boundaryKernelIso S.X₁ p) (boundaryKernelIso S.X₂ p)
      (boundaryKernelIso S.X₃ p)
      (boundaryKernelIso_naturality S.f p).symm (boundaryKernelIso_naturality S.g p).symm
  exact ShortComplex.shortExact_of_iso e
    (HorizontalInvariantExactness.boundaries_shortExact S hS hi p)

/-- Cokernels preserve a specified horizontal lower support bound. -/
lemma cokernel_lowerBound {K J : CochainComplex C ℤ} (i : K ⟶ J) (L : ℤ)
    (hJ : ∀ p : ℤ, p < L → IsZero (J.X p)) :
    ∀ p : ℤ, p < L → IsZero ((cokernel i).X p) := by
  intro p hp
  exact IsZero.of_epi ((cokernel.π i).f p) (hJ p hp)

/-- Successive short exact sequences to be spliced into a resolution.
No injectivity is built into this structure. In the application C may itself
be a category of complexes, and injectivity is imposed only after taking
the four horizontal invariants. -/
structure ExactTower (C : Type u) [Category.{v} C] [Abelian C] where
  syzygy : ℕ → C
  row : ℕ → C
  inclusion : ∀ n, syzygy n ⟶ row n
  projection : ∀ n, row n ⟶ syzygy (n + 1)
  zero : ∀ n, inclusion n ≫ projection n = 0
  shortExact : ∀ n, (ShortComplex.mk (inclusion n) (projection n) (zero n)).ShortExact

namespace ExactTower

variable (T : ExactTower C)

instance inclusion_mono (n : ℕ) : Mono (T.inclusion n) := (T.shortExact n).mono_f
instance projection_epi (n : ℕ) : Epi (T.projection n) := (T.shortExact n).epi_g

@[reassoc (attr := simp)]
lemma inclusion_projection (n : ℕ) : T.inclusion n ≫ T.projection n = 0 := T.zero n

/-- Splicing uses the quotient map followed by the next inclusion. -/
def differential (n : ℕ) : T.row n ⟶ T.row (n + 1) :=
  T.projection n ≫ T.inclusion (n + 1)

@[reassoc (attr := simp)]
lemma differential_comp_differential (n : ℕ) :
    T.differential n ≫ T.differential (n + 1) = 0 := by
  simp [differential, Category.assoc]

def natComplex : CochainComplex C ℕ :=
  CochainComplex.of T.row T.differential T.differential_comp_differential

@[simp]
lemma natComplex_d (n : ℕ) :
    T.natComplex.d n (n + 1) = T.differential n :=
  CochainComplex.of_d _ _ n

/-- Exactness is unchanged by an epimorphism before the first arrow
and a monomorphism after the second arrow. -/
lemma exact_splice {S : ShortComplex C} (hS : S.Exact)
    {X Y : C} (e : X ⟶ S.X₁) (m : S.X₃ ⟶ Y) [Epi e] [Mono m] :
    (ShortComplex.mk (e ≫ S.f) (S.g ≫ m) (by simp [Category.assoc])).Exact := by
  let R := ShortComplex.mk (e ≫ S.f) S.g (by simp [Category.assoc, S.zero])
  let a : R ⟶ S := { τ₁ := e, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
  have ha : R.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono a).2 hS
  let b : R ⟶ ShortComplex.mk (e ≫ S.f) (S.g ≫ m)
      (by simp [Category.assoc]) :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := m }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono b).1 ha

lemma natComplex_exactAt_succ (n : ℕ) : T.natComplex.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  simpa [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', differential] using
    exact_splice (T.shortExact (n + 1)).exact (T.projection n) (T.inclusion (n + 2))

@[reassoc (attr := simp)]
lemma inclusion_zero_d : T.inclusion 0 ≫ T.natComplex.d 0 1 = 0 := by
  simp [differential, ← Category.assoc, T.zero]

lemma exact_zero :
    (ShortComplex.mk (T.inclusion 0) (T.natComplex.d 0 1) T.inclusion_zero_d).Exact := by
  simpa [differential] using
    exact_splice (T.shortExact 0).exact (𝟙 _) (T.inclusion 1)

/-- Extend the spliced complex by zero to negative integer degrees. -/
noncomputable def intComplex : CochainComplex C ℤ :=
  T.natComplex.extend ComplexShape.embeddingUpNat

noncomputable def xIso (n : ℕ) : T.intComplex.X (n : ℤ) ≅ T.row n :=
  T.natComplex.extendXIso ComplexShape.embeddingUpNat (i := n) rfl

lemma intComplex_d (n : ℕ) :
    T.intComplex.d (n : ℤ) ((n : ℤ) + 1) =
      (T.xIso n).hom ≫ T.differential n ≫ (T.xIso (n + 1)).inv := by
  simpa [intComplex, xIso] using
    T.natComplex.extend_d_eq ComplexShape.embeddingUpNat (i := n) (j := n + 1)
      (i' := (n : ℤ)) (j' := (n : ℤ) + 1) rfl (by simp)

lemma intComplex_zero_neg (q : ℤ) (hq : q < 0) : IsZero (T.intComplex.X q) :=
  T.natComplex.isZero_extend_X ComplexShape.embeddingUpNat q (by
    intro n hn
    change (n : ℤ) = q at hn
    omega)

noncomputable def augmentation : T.syzygy 0 ⟶ T.intComplex.X 0 :=
  T.inclusion 0 ≫ (T.xIso 0).inv

instance augmentation_mono : Mono T.augmentation := by
  dsimp [augmentation]
  infer_instance

@[reassoc (attr := simp)]
lemma augmentation_d : T.augmentation ≫ T.intComplex.d 0 1 = 0 := by
  rw [show T.intComplex.d 0 1 = _ from T.intComplex_d 0]
  simp [augmentation, differential, Category.assoc]

lemma augmentation_exact :
    (ShortComplex.mk T.augmentation (T.intComplex.d 0 1) T.augmentation_d).Exact := by
  let e : ShortComplex.mk T.augmentation (T.intComplex.d 0 1) T.augmentation_d ≅
      ShortComplex.mk (T.inclusion 0) (T.natComplex.d 0 1) T.inclusion_zero_d :=
    ShortComplex.isoMk (Iso.refl _) (T.xIso 0) (T.xIso 1)
      (by simp [augmentation])
      (by simp [show T.intComplex.d 0 1 = _ from T.intComplex_d 0])
  exact (ShortComplex.exact_iff_of_iso e).2 T.exact_zero

lemma intComplex_exact_pos (q : ℤ) (hq : 0 < q) : T.intComplex.ExactAt q := by
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hq)
  have hnpos : 0 < n := by omega
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  subst q
  exact (T.natComplex.extend_exactAt_iff ComplexShape.embeddingUpNat rfl).2
    (T.natComplex_exactAt_succ m)

/-- A spliced exact tower with injective rows is an augmented injective resolution. -/
lemma isInjectiveResolution (hJ : ∀ n, Injective (T.row n)) :
    IsInjectiveResolution (T.syzygy 0) T.intComplex T.augmentation where
  zero_neg := T.intComplex_zero_neg
  injective q hq := by
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    exact Injective.of_iso (T.xIso n).symm (hJ n)
  mono := T.augmentation_mono
  augmentation_d := T.augmentation_d
  exact_zero := T.augmentation_exact
  exact_pos := T.intComplex_exact_pos

end ExactTower

namespace ExactTower

universe v' u'
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (T : ExactTower C) (F : C ⥤ D) [F.PreservesZeroMorphisms]

def sequence (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (T.inclusion n) (T.projection n) (T.zero n)

/-- Functors need preserve only the particular short exact sequences in the
tower; global exactness of a horizontal invariant functor is not required. -/
def map (hS : ∀ n, ((T.sequence n).map F).ShortExact) : ExactTower D where
  syzygy n := F.obj (T.syzygy n)
  row n := F.obj (T.row n)
  inclusion n := F.map (T.inclusion n)
  projection n := F.map (T.projection n)
  zero n := by rw [← F.map_comp, T.zero, F.map_zero]
  shortExact n := hS n

/-- The integer extension of a tower remains an injective resolution after
a functor which makes its rows injective and preserves its short exact steps.
This applies separately to terms, boundaries, cycles and cohomology. -/
lemma map_isInjectiveResolution
    (hS : ∀ n, ((T.sequence n).map F).ShortExact)
    (hJ : ∀ n, Injective (F.obj (T.row n))) :
    IsInjectiveResolution (F.obj (T.syzygy 0))
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj T.intComplex)
      (F.map T.augmentation) := by
  let (n : ℕ) : Mono (F.map (T.inclusion n)) := (hS n).mono_f
  let (n : ℕ) : Epi (F.map (T.projection n)) := (hS n).epi_g
  have hd (n : ℕ) :
      F.map (T.intComplex.d (n : ℤ) ((n + 1 : ℕ) : ℤ)) =
        (F.mapIso (T.xIso n)).hom ≫
          (F.map (T.projection n) ≫ F.map (T.inclusion (n + 1))) ≫
          (F.mapIso (T.xIso (n + 1))).inv := by
    simpa only [Int.natCast_add, Int.natCast_one, differential, F.map_comp,
      Functor.mapIso_hom, Functor.mapIso_inv] using
      congrArg F.map (T.intComplex_d n)
  have hz : F.map T.augmentation ≫ F.map (T.intComplex.d 0 1) = 0 := by
    rw [← F.map_comp, T.augmentation_d, F.map_zero]
  refine {
    zero_neg := fun q hq => F.map_isZero (T.intComplex_zero_neg q hq)
    injective := ?_
    mono := ?_
    augmentation_d := hz
    exact_zero := ?_
    exact_pos := ?_ }
  · intro q hq
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    exact Injective.of_iso (F.mapIso (T.xIso n)).symm (hJ n)
  · dsimp [augmentation]
    rw [F.map_comp]
    infer_instance
  · let R := ShortComplex.mk (F.map (T.inclusion 0))
        (F.map (T.projection 0) ≫ F.map (T.inclusion 1)) (by
          rw [← Category.assoc, ← F.map_comp, T.zero, F.map_zero, zero_comp])
    have hex : R.Exact := by
      simpa [R, sequence] using
        exact_splice (hS 0).exact (𝟙 _) (F.map (T.inclusion 1))
    let e : ShortComplex.mk (F.map T.augmentation)
        (F.map (T.intComplex.d 0 1)) hz ≅ R :=
      ShortComplex.isoMk (Iso.refl _) (F.mapIso (T.xIso 0)) (F.mapIso (T.xIso 1))
        (by simp [R, augmentation, F.map_comp])
        (by simp [R, show F.map (T.intComplex.d 0 1) = _ from hd 0])
    exact (ShortComplex.exact_iff_of_iso e).2 hex
  · intro q hq
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hq)
    have hnpos : 0 < n := by omega
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
    subst q
    let M := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj T.intComplex
    rw [HomologicalComplex.exactAt_iff' M (m : ℤ) ((m + 1 : ℕ) : ℤ)
      ((m + 2 : ℕ) : ℤ) (by simp) (by simp; omega)]
    let R := ShortComplex.mk
      (F.map (T.projection m) ≫ F.map (T.inclusion (m + 1)))
      (F.map (T.projection (m + 1)) ≫ F.map (T.inclusion (m + 2))) (by
        simpa only [differential, F.map_comp, F.map_zero, Nat.add_assoc] using
          congrArg F.map (T.differential_comp_differential m))
    have hex : R.Exact :=
      exact_splice (hS (m + 1)).exact
        (F.map (T.projection m)) (F.map (T.inclusion (m + 2)))
    let e : M.sc' (m : ℤ) ((m + 1 : ℕ) : ℤ) ((m + 2 : ℕ) : ℤ) ≅ R :=
      ShortComplex.isoMk (F.mapIso (T.xIso m)) (F.mapIso (T.xIso (m + 1)))
        (F.mapIso (T.xIso (m + 2)))
        (by
          change (F.mapIso (T.xIso m)).hom ≫
              (F.map (T.projection m) ≫ F.map (T.inclusion (m + 1))) =
            F.map (T.intComplex.d (m : ℤ) ((m + 1 : ℕ) : ℤ)) ≫
              (F.mapIso (T.xIso (m + 1))).hom
          rw [hd m]
          simp)
        (by
          change (F.mapIso (T.xIso (m + 1))).hom ≫
              (F.map (T.projection (m + 1)) ≫ F.map (T.inclusion (m + 2))) =
            F.map (T.intComplex.d ((m + 1 : ℕ) : ℤ) ((m + 2 : ℕ) : ℤ)) ≫
              (F.mapIso (T.xIso (m + 2))).hom
          rw [hd (m + 1)]
          simp)
    exact (ShortComplex.exact_iff_of_iso e).2 hex

end ExactTower

/-- The genuinely smaller construction needed at each vertical step. It asks
for one admissible embedding into a row whose four invariants are injective,
and contains no resolution or vertical exactness assumption. -/
structure InjectiveRowPresentation (K : CochainComplex C ℤ) (L : ℤ) where
  target : CochainComplex C ℤ
  inclusion : K ⟶ target
  lowerBound : ∀ p : ℤ, p < L → IsZero (target.X p)
  mono_terms : ∀ p : ℤ, Mono (inclusion.f p)
  mono_opcycles : ∀ p : ℤ, Mono (opcyclesMap inclusion p)
  injective_terms : ∀ p : ℤ, Injective (target.X p)
  injective_boundaries : ∀ p : ℤ, Injective ((boundariesFunctor p).obj target)
  injective_cycles : ∀ p : ℤ, Injective (target.cycles p)
  injective_homology : ∀ p : ℤ, Injective (target.homology p)

/- The split horizontal row with prescribed boundaries and homology. -/
namespace SplitRow

variable (B H : ℤ → C)

noncomputable def complex : CochainComplex C ℤ :=
  CochainComplex.of (fun p => (B p ⊞ H p) ⊞ B (p + 1))
    (fun p => biprod.snd ≫ biprod.inl ≫ biprod.inl)
    (fun p => by simp)

@[simp]
lemma complex_d (p : ℤ) :
    (complex B H).d p (p + 1) =
      biprod.snd ≫ biprod.inl ≫ biprod.inl := by
  simp [complex]

noncomputable def quotient (p : ℤ) : (complex B H).X p ⟶ H p ⊞ B (p + 1) :=
  biprod.desc (biprod.snd ≫ biprod.inl) biprod.inr

@[reassoc (attr := simp)]
lemma d_quotient (a p : ℤ) : (complex B H).d a p ≫ quotient B H p = 0 := by
  by_cases h : a + 1 = p
  · subst p
    simp [quotient]
  · rw [HomologicalComplex.shape _ a p h, zero_comp]

/-- Cycles and cohomology of the row are the indicated first two and middle summands. -/
noncomputable def leftData (p : ℤ) :
    ((complex B H).sc' p (p + 1) (p + 1 + 1)).LeftHomologyData := by
  let S := (complex B H).sc' p (p + 1) (p + 1 + 1)
  have wi : (biprod.inl : B (p + 1) ⊞ H (p + 1) ⟶
      (complex B H).X (p + 1)) ≫ S.g = 0 := by simp [S]
  let hi : IsLimit (KernelFork.ofι _ wi) :=
    isKernelCompMono (biprod.isKernelSndKernelFork
      (B (p + 1) ⊞ H (p + 1)) (B (p + 1 + 1)))
      (biprod.inl ≫ biprod.inl) (by simp [S])
  have hl : hi.lift (KernelFork.ofι S.f S.zero) =
      (biprod.snd : (complex B H).X p ⟶ B (p + 1)) ≫ biprod.inl := by
    apply (cancel_mono (biprod.inl : B (p + 1) ⊞ H (p + 1) ⟶
      (complex B H).X (p + 1))).1
    simpa [S] using hi.fac (KernelFork.ofι S.f S.zero) WalkingParallelPair.zero
  have wπ : hi.lift (KernelFork.ofι S.f S.zero) ≫
      (biprod.snd : B (p + 1) ⊞ H (p + 1) ⟶ H (p + 1)) = 0 := by
    rw [hl]; simp
  exact {
    K := B (p + 1) ⊞ H (p + 1)
    H := H (p + 1)
    i := biprod.inl
    π := biprod.snd
    wi := wi
    hi := hi
    wπ := wπ
    hπ := isCokernelEpiComp (biprod.isCokernelInlCokernelFork _ _)
      (biprod.snd : (complex B H).X p ⟶ B (p + 1)) hl }

noncomputable def cyclesIso (p : ℤ) :
    (complex B H).cycles (p + 1) ≅ B (p + 1) ⊞ H (p + 1) :=
  (complex B H).cyclesIsoSc' p (p + 1) (p + 1 + 1) (by simp) (by simp) ≪≫
    (leftData B H p).cyclesIso

noncomputable def homologyIso (p : ℤ) :
    (complex B H).homology (p + 1) ≅ H (p + 1) :=
  (complex B H).homologyIsoSc' p (p + 1) (p + 1 + 1) (by simp) (by simp) ≪≫
    (leftData B H p).homologyIso

noncomputable def boundaryIso (p : ℤ) :
    B (p + 1) ≅ image ((complex B H).d p (p + 1)) :=
  image.isoStrongEpiMono (biprod.snd : (complex B H).X p ⟶ B (p + 1))
    (biprod.inl ≫ biprod.inl) (by simp)

lemma injective_terms [∀ p, Injective (B p)] [∀ p, Injective (H p)] (p : ℤ) :
    Injective ((complex B H).X p) := by
  dsimp [complex]; infer_instance

lemma injective_cycles [∀ p, Injective (B p)] [∀ p, Injective (H p)] (p : ℤ) :
    Injective ((complex B H).cycles p) := by
  have h (q : ℤ) : Injective ((complex B H).cycles (q + 1)) :=
    Injective.of_iso (cyclesIso B H q).symm inferInstance
  convert h (p - 1) using 1; simp

lemma injective_homology [∀ p, Injective (H p)] (p : ℤ) :
    Injective ((complex B H).homology p) := by
  have h (q : ℤ) : Injective ((complex B H).homology (q + 1)) :=
    Injective.of_iso (homologyIso B H q).symm inferInstance
  convert h (p - 1) using 1; simp

lemma injective_boundaries [∀ p, Injective (B p)] (p : ℤ) :
    Injective ((boundariesFunctor p).obj (complex B H)) := by
  have h (q : ℤ) : Injective ((boundariesFunctor (q + 1)).obj (complex B H)) := by
    change Injective (image ((complex B H).d (q + 1 - 1) (q + 1)))
    rw [add_sub_cancel_right]
    exact Injective.of_iso (boundaryIso B H q) inferInstance
  convert h (p - 1) using 1; simp

end SplitRow

namespace CompatibleEmbedding

variable (K : CochainComplex C ℤ)

/-- The epic part of the outgoing differential, with the boundary convention
used by the shared interface. -/
noncomputable def toNextBoundary (p : ℤ) :
    K.X p ⟶ (boundariesFunctor (p + 1)).obj K :=
  eqToHom (by simp) ≫ factorThruImage (K.d (p + 1 - 1) (p + 1))

instance (p : ℤ) : Epi (toNextBoundary K p) := by
  dsimp [toNextBoundary]; infer_instance

@[reassoc (attr := simp)]
lemma toNextBoundary_ι (p : ℤ) :
    toNextBoundary K p ≫ image.ι (K.d (p + 1 - 1) (p + 1)) =
      K.d p (p + 1) := by
  simp [toNextBoundary]

@[reassoc (attr := simp)]
lemma d_toNextBoundary (a p : ℤ) : K.d a p ≫ toNextBoundary K p = 0 := by
  apply (cancel_mono (image.ι (K.d (p + 1 - 1) (p + 1)))).1
  simp

/-- Quotienting the epic part by the preceding boundaries. -/
noncomputable def outBoundary (p : ℤ) :
    K.opcycles p ⟶ (boundariesFunctor (p + 1)).obj K :=
  K.descOpcycles (toNextBoundary K p) (p - 1) (by simp) (d_toNextBoundary K _ _)

@[reassoc (attr := simp)]
lemma p_outBoundary (p : ℤ) : K.pOpcycles p ≫ outBoundary K p = toNextBoundary K p := by
  simp [outBoundary]

@[reassoc (attr := simp)]
lemma outBoundary_ι (p : ℤ) :
    outBoundary K p ≫ image.ι (K.d (p + 1 - 1) (p + 1)) =
      K.fromOpcycles p (p + 1) := by
  apply (cancel_epi (K.pOpcycles p)).1
  simp

@[reassoc (attr := simp)]
lemma homologyι_outBoundary (p : ℤ) : K.homologyι p ≫ outBoundary K p = 0 := by
  apply (cancel_mono (image.ι (K.d (p + 1 - 1) (p + 1)))).1
  simp

noncomputable def homologySequence (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (K.homologyι p) (outBoundary K p) (homologyι_outBoundary K p)

instance homologySequence_f_mono (p : ℤ) : Mono (homologySequence K p).f := by
  dsimp [homologySequence]; infer_instance

lemma homologySequence_exact (p : ℤ) : (homologySequence K p).Exact := by
  dsimp only [homologySequence]
  apply ShortComplex.exact_of_f_is_kernel
  apply KernelFork.IsLimit.ofι'
  intro A k hk
  have hk' : k ≫ K.fromOpcycles p (p + 1) = 0 := by
    rw [← outBoundary_ι, ← Category.assoc, hk, zero_comp]
  exact ⟨(K.homologyIsKernel p (p + 1) (by simp)).lift (KernelFork.ofι k hk'),
    (K.homologyIsKernel p (p + 1) (by simp)).fac
      (KernelFork.ofι k hk') WalkingParallelPair.zero⟩

@[reassoc (attr := simp)]
lemma boundary_ι_pOpcycles (p : ℤ) :
    image.ι (K.d (p - 1) p) ≫ K.pOpcycles p = 0 := by
  apply (cancel_epi (factorThruImage (K.d (p - 1) p))).1
  simp

noncomputable def boundarySequence (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (image.ι (K.d (p - 1) p)) (K.pOpcycles p)
    (boundary_ι_pOpcycles K p)

instance boundarySequence_f_mono (p : ℤ) : Mono (boundarySequence K p).f := by
  dsimp [boundarySequence]; infer_instance

lemma boundarySequence_exact (p : ℤ) : (boundarySequence K p).Exact := by
  dsimp only [boundarySequence]
  apply ShortComplex.exact_of_f_is_kernel
  apply KernelFork.IsLimit.ofι'
  intro A k hk
  exact ⟨kernel.lift (K.pOpcycles p) k hk ≫ (boundaryKernelIso K p).hom, by simp⟩

variable [EnoughInjectives C]

noncomputable def B (p : ℤ) : C := Injective.under ((boundariesFunctor p).obj K)
noncomputable def H (p : ℤ) : C := Injective.under (K.homology p)

instance (p : ℤ) : Injective (B K p) := Injective.injective_under _
instance (p : ℤ) : Injective (H K p) := Injective.injective_under _

noncomputable def jB (p : ℤ) : (boundariesFunctor p).obj K ⟶ B K p := Injective.ι _
noncomputable def jH (p : ℤ) : K.homology p ⟶ H K p := Injective.ι _

instance (p : ℤ) : Mono (jB K p) := by
  dsimp [jB]; infer_instance
instance (p : ℤ) : Mono (jH K p) := by
  dsimp [jH]; infer_instance

noncomputable def u (p : ℤ) : K.X p ⟶ B K p :=
  Injective.factorThru (jB K p) (image.ι (K.d (p - 1) p))

noncomputable def v (p : ℤ) : K.X p ⟶ H K p :=
  Injective.factorThru (K.homologyπ p ≫ jH K p) (K.iCycles p)

noncomputable def w (p : ℤ) : K.X p ⟶ B K (p + 1) :=
  toNextBoundary K p ≫ jB K (p + 1)

@[reassoc (attr := simp)]
lemma boundary_ι_u (p : ℤ) : image.ι (K.d (p - 1) p) ≫ u K p = jB K p := by
  simp [u]

@[reassoc (attr := simp)]
lemma iCycles_v (p : ℤ) : K.iCycles p ≫ v K p = K.homologyπ p ≫ jH K p := by
  simp [v]

@[reassoc (attr := simp)]
lemma d_v (a p : ℤ) : K.d a p ≫ v K p = 0 := by
  rw [← K.toCycles_i a p, Category.assoc, iCycles_v, ← Category.assoc]
  simp

@[reassoc (attr := simp)]
lemma d_w (a p : ℤ) : K.d a p ≫ w K p = 0 := by simp [w]

@[reassoc (attr := simp)]
lemma d_u (p : ℤ) : K.d p (p + 1) ≫ u K (p + 1) = w K p := by
  rw [← toNextBoundary_ι K p, Category.assoc]
  simp only [u, Injective.comp_factorThru, w]

@[reassoc (attr := simp)]
lemma boundary_ι_v (p : ℤ) : image.ι (K.d (p - 1) p) ≫ v K p = 0 := by
  apply (cancel_epi (factorThruImage (K.d (p - 1) p))).1
  simp

@[reassoc (attr := simp)]
lemma boundary_ι_w (p : ℤ) : image.ι (K.d (p - 1) p) ≫ w K p = 0 := by
  apply (cancel_epi (factorThruImage (K.d (p - 1) p))).1
  simp

noncomputable def barV (p : ℤ) : K.opcycles p ⟶ H K p :=
  K.descOpcycles (v K p) (p - 1) (by simp) (d_v K _ _)

@[reassoc (attr := simp)]
lemma p_barV (p : ℤ) : K.pOpcycles p ≫ barV K p = v K p := by simp [barV]

@[reassoc (attr := simp)]
lemma homologyι_barV (p : ℤ) : K.homologyι p ≫ barV K p = jH K p := by
  apply (cancel_epi (K.homologyπ p)).1
  rw [← Category.assoc, K.homology_π_ι, Category.assoc, p_barV, iCycles_v]

noncomputable def barMap (p : ℤ) : K.opcycles p ⟶ H K p ⊞ B K (p + 1) :=
  biprod.lift (barV K p) (outBoundary K p ≫ jB K (p + 1))

instance barMap_mono (p : ℤ) : Mono (barMap K p) := by
  let S := ShortComplex.mk (biprod.inl : H K p ⟶ H K p ⊞ B K (p + 1))
    biprod.snd (by simp)
  let f : homologySequence K p ⟶ S := {
    τ₁ := jH K p
    τ₂ := barMap K p
    τ₃ := jB K (p + 1)
    comm₁₂ := by ext <;> simp [homologySequence, S, barMap]
    comm₂₃ := by simp [homologySequence, S, barMap] }
  exact ShortComplex.mono_τ₂_of_exact_of_mono f (homologySequence_exact K p)

/-- The same boundary injective occurs in the last summand of one degree
and the first summand of the next degree. -/
noncomputable def target : CochainComplex C ℤ := SplitRow.complex (B K) (H K)

noncomputable def inclusion : K ⟶ target K :=
  CochainComplex.ofHom
    (fun p => biprod.lift (biprod.lift (u K p) (v K p)) (w K p))
    (fun p => by
      dsimp only [target, SplitRow.complex]
      ext <;> simp)

instance inclusion_f_mono (p : ℤ) : Mono ((inclusion K).f p) := by
  let S := ShortComplex.mk
    (biprod.inl ≫ biprod.inl : B K p ⟶ (target K).X p)
    (SplitRow.quotient (B K) (H K) p) (by simp [SplitRow.quotient])
  have : Mono S.f := by dsimp [S]; infer_instance
  let f : boundarySequence K p ⟶ S := {
    τ₁ := jB K p
    τ₂ := (inclusion K).f p
    τ₃ := barMap K p
    comm₁₂ := by
      dsimp only [boundarySequence, S, target, SplitRow.complex]
      apply biprod.hom_ext
      · apply biprod.hom_ext <;> simp [inclusion]
      · simp [inclusion]
    comm₂₃ := by ext <;> simp [boundarySequence, S, inclusion, SplitRow.quotient, barMap, w] }
  exact ShortComplex.mono_τ₂_of_exact_of_mono f (boundarySequence_exact K p)

/-- The last two components give a monomorphism on quotients by boundaries. -/
instance inclusion_opcycles_mono (p : ℤ) : Mono (opcyclesMap (inclusion K) p) := by
  let r := (target K).descOpcycles (SplitRow.quotient (B K) (H K) p)
    (p - 1) (by simp) (SplitRow.d_quotient (B K) (H K) (p - 1) p)
  have h : opcyclesMap (inclusion K) p ≫ r = barMap K p := by
    apply (cancel_epi (K.pOpcycles p)).1
    rw [← Category.assoc, p_opcyclesMap, Category.assoc]
    ext <;> simp [r, inclusion, SplitRow.quotient, barMap, w]
  exact mono_of_mono_fac h

lemma target_lowerBound (L : ℤ) (hK : ∀ p : ℤ, p < L → IsZero (K.X p))
    (p : ℤ) (hp : p < L) : IsZero ((target K).X p) := by
  have hb : IsZero (B K p) := Injective.isZero_under _
    (IsZero.of_mono (image.ι (K.d (p - 1) p)) (hK p hp))
  have hh : IsZero (H K p) := Injective.isZero_under _
    (IsZero.of_epi (K.homologyπ p) (IsZero.of_mono (K.iCycles p) (hK p hp)))
  have hb' : IsZero (B K (p + 1)) := Injective.isZero_under _
    (IsZero.of_epi (toNextBoundary K p) (hK p hp))
  exact (biprod_isZero_iff _ _).2 ⟨(biprod_isZero_iff _ _).2 ⟨hb, hh⟩, hb'⟩

/-- The one-step simultaneous injective horseshoe construction. -/
noncomputable def presentation (L : ℤ) (hK : ∀ p : ℤ, p < L → IsZero (K.X p)) :
    InjectiveRowPresentation K L where
  target := target K
  inclusion := inclusion K
  lowerBound := target_lowerBound K L hK
  mono_terms := inclusion_f_mono K
  mono_opcycles := inclusion_opcycles_mono K
  injective_terms := SplitRow.injective_terms (B K) (H K)
  injective_boundaries := SplitRow.injective_boundaries (B K) (H K)
  injective_cycles := SplitRow.injective_cycles (B K) (H K)
  injective_homology := SplitRow.injective_homology (B K) (H K)

end CompatibleEmbedding

namespace FromPresentations

variable (L : ℤ)

abbrev BoundedComplex :=
  {K : CochainComplex C ℤ // ∀ p : ℤ, p < L → IsZero (K.X p)}

variable (embed : ∀ K : CochainComplex C ℤ,
  (∀ p : ℤ, p < L → IsZero (K.X p)) → Nonempty (InjectiveRowPresentation K L))

noncomputable def presentation (K : BoundedComplex (C := C) L) :
    InjectiveRowPresentation K.val L := (embed K.val K.property).some

noncomputable def next (K : BoundedComplex (C := C) L) : BoundedComplex (C := C) L :=
  ⟨cokernel (presentation L embed K).inclusion,
    cokernel_lowerBound _ L (presentation L embed K).lowerBound⟩

variable (K : CochainComplex C ℤ) (hK : ∀ p : ℤ, p < L → IsZero (K.X p))

noncomputable def syzygy : ℕ → BoundedComplex (C := C) L
  | 0 => ⟨K, hK⟩
  | n + 1 => next L embed (syzygy n)

noncomputable def rowPresentation (n : ℕ) :=
  presentation L embed (syzygy L embed K hK n)

/-- The exact tower of horizontal complexes. HA-G07 supplies invariant
exactness, not an unsupported global exactness instance for those functors. -/
noncomputable def tower : ExactTower (CochainComplex C ℤ) where
  syzygy n := (syzygy L embed K hK n).val
  row n := (rowPresentation L embed K hK n).target
  inclusion n := (rowPresentation L embed K hK n).inclusion
  projection n := cokernel.π (rowPresentation L embed K hK n).inclusion
  zero n := cokernel.condition _
  shortExact n := by
    let i := (rowPresentation L embed K hK n).inclusion
    let : Mono i := mono_of_mono_f i (rowPresentation L embed K hK n).mono_terms
    exact { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i) }

lemma tower_mono_opcycles (n : ℕ) (p : ℤ) :
    Mono (opcyclesMap ((tower L embed K hK).inclusion n) p) :=
  (rowPresentation L embed K hK n).mono_opcycles p

/-- The horizontal bound survives both the integer extension and the flip. -/
lemma tower_lowerBound (p q : ℤ) (hp : p < L) :
    IsZero ((((tower L embed K hK).intComplex).X q).X p) := by
  by_cases hq : 0 ≤ q
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    exact IsZero.of_iso ((rowPresentation L embed K hK n).lowerBound p hp)
      ((eval C (ComplexShape.up ℤ) p).mapIso ((tower L embed K hK).xIso n))
  · exact (eval C (ComplexShape.up ℤ) p).map_isZero
      ((tower L embed K hK).intComplex_zero_neg q (by omega))

/-- Iteration and splicing produce every simultaneous resolution condition
from actual one-step presentations. This is the assembly part of HA-G01. -/
noncomputable def resolution : ResolutionData K where
  bicomplex := HomologicalComplex₂.flip (tower L embed K hK).intComplex
  boundedBelow := ⟨L, fun p q hp => tower_lowerBound L embed K hK p q hp⟩
  nonnegative p q hq := (eval C (ComplexShape.up ℤ) p).map_isZero
    ((tower L embed K hK).intComplex_zero_neg q hq)
  augmentation := (tower L embed K hK).augmentation
  augmentation_d p := by
    have h := congrArg (fun f => f.f p) (tower L embed K hK).augmentation_d
    exact h
  terms p := (tower L embed K hK).map_isInjectiveResolution
    (eval C (ComplexShape.up ℤ) p)
    (fun n => ((tower L embed K hK).shortExact n).map (eval C (ComplexShape.up ℤ) p))
    (fun n => (rowPresentation L embed K hK n).injective_terms p)
  boundaries p := (tower L embed K hK).map_isInjectiveResolution (boundariesFunctor p)
    (fun n => boundaries_shortExact _ ((tower L embed K hK).shortExact n)
      (tower_mono_opcycles L embed K hK n) p)
    (fun n => (rowPresentation L embed K hK n).injective_boundaries p)
  cycles p := (tower L embed K hK).map_isInjectiveResolution
    (HomologicalComplex.cyclesFunctor C (ComplexShape.up ℤ) p)
    (fun n => HorizontalInvariantExactness.cycles_shortExact _
      ((tower L embed K hK).shortExact n) (tower_mono_opcycles L embed K hK n) p)
    (fun n => (rowPresentation L embed K hK n).injective_cycles p)
  cohomology p := (tower L embed K hK).map_isInjectiveResolution
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) p)
    (fun n => HorizontalInvariantExactness.homology_shortExact _
      ((tower L embed K hK).shortExact n) (tower_mono_opcycles L embed K hK n) p)
    (fun n => (rowPresentation L embed K hK n).injective_homology p)

lemma resolution_lowerBound (p q : ℤ) (hp : p < L) :
    IsZero ((((resolution L embed K hK).bicomplex).X p).X q) :=
  tower_lowerBound L embed K hK p q hp

end FromPresentations

/-- HA-G01 with the original prescribed horizontal bound. -/
theorem existsResolutionAtBound : Specs.ExistenceAtBound.{v, u} := by
  intro C _ _ _ K L hK
  have embed : ∀ U : CochainComplex C ℤ,
      (∀ p : ℤ, p < L → IsZero (U.X p)) → Nonempty (InjectiveRowPresentation U L) := by
    intro U hU
    exact ⟨CompatibleEmbedding.presentation U L hU⟩
  exact ⟨FromPresentations.resolution L embed K hK,
    FromPresentations.resolution_lowerBound L embed K hK⟩

/-- Bounded-below existence follows by choosing any lower bound. -/
theorem existsResolution : Specs.Existence.{v, u} := by
  intro C _ _ _ K hK
  obtain ⟨L, hL⟩ := hK
  obtain ⟨R, _⟩ := existsResolutionAtBound K L hL
  exact ⟨R⟩

end AdvancedHomologicalAlgebra.CartanEilenbergExistence
