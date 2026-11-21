import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SmallChainHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularSubdivision
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.RelativeSingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SmallChainSubdivision
import Mathlib.Tactic.Abel

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open scoped Simplicial
universe u v w
namespace P202.SmallChainHomology
open P202Specs.SingularChains P202Specs.SingularSubdivision
open P202Specs.RelativeSingularChains P202Specs.SmallChainHomology
open P202.SingularSubdivision

/-- An elementwise comparison criterion using actual categorical homology.
The two hypotheses are surjectivity on cycles modulo boundaries and
injectivity on cycles modulo boundaries, respectively. -/
theorem shortComplex_comparison {R : Type u} [CommRing R]
    {S T : ShortComplex (ModuleCat.{v} R)} (f : S ⟶ T)
    (hsurj : ∀ z : T.X₂, T.g z = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ ∃ y : T.X₁, f.τ₂ x - z = T.f y)
    (hinj : ∀ x : S.X₂, S.g x = 0 → ∀ y : T.X₁,
      T.f y = f.τ₂ x → ∃ a : S.X₁, S.f a = x) :
    IsIso (ShortComplex.homologyMap f) := by
  let γ : ShortComplex.LeftHomologyMapData f
      S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData := default
  have hK (x : S.g.hom.ker) : (γ.φK x).val = f.τ₂ x.val := by
    exact congrArg (fun g => g x) γ.commi
  have hH (x : S.g.hom.ker) :
      γ.φH (Submodule.Quotient.mk x) = Submodule.Quotient.mk (γ.φK x) := by
    exact congrArg (fun g => g x) γ.commπ
  have hbij : Function.Bijective γ.φH := by
    constructor
    · apply (injective_iff_map_eq_zero γ.φH.hom).mpr
      intro q hq
      induction q using Submodule.Quotient.induction_on with
      | _ x =>
        rw [hH] at hq
        obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
        have hy' : T.f y = f.τ₂ x.val := (congrArg Subtype.val hy).trans (hK x)
        obtain ⟨a, ha⟩ := hinj x.val x.property y hy'
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact ⟨a, Subtype.ext ha⟩
    · intro q
      induction q using Submodule.Quotient.induction_on with
      | _ z =>
        obtain ⟨x, hx, y, hy⟩ := hsurj z.val z.property
        refine ⟨Submodule.Quotient.mk (⟨x, hx⟩ : S.g.hom.ker), ?_⟩
        rw [hH]
        apply (Submodule.Quotient.eq _).mpr
        refine ⟨y, ?_⟩
        apply Subtype.ext
        change T.f y = (γ.φK ⟨x, hx⟩).val - z.val
        rw [hK]
        exact hy.symm
  have : IsIso γ.φH := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact (ShortComplex.quasiIso_iff f).mp (γ.quasiIso_iff.mpr inferInstance)

variable (R : Type u) [CommRing R] (X : TopCat.{v})

/-- The boundary with its concrete finite-chain module type exposed. -/
def chainDifferential (n : ℕ) : Chains R X (n+1) →ₗ[R] Chains R X n :=
  boundary R R X n

/-- The m-fold subdivision of a finite chain. -/
def iterateSubdivision (n m : ℕ) : Chains R X n →ₗ[R] Chains R X n :=
  (subdivision R X n)^m

/-- The telescoping homotopy from identity to m-fold subdivision. -/
def iterateHomotopy (n m : ℕ) : Chains R X n →ₗ[R] Chains R X (n+1) :=
  ∑ j ∈ Finset.range m, (homotopy R X n).comp (iterateSubdivision R X n j)

@[simp] theorem iterateSubdivision_zero (n : ℕ) (c : Chains R X n) :
    iterateSubdivision R X n 0 c = c := rfl

@[simp] theorem iterateSubdivision_succ (n m : ℕ) (c : Chains R X n) :
    iterateSubdivision R X n (m+1) c =
      subdivision R X n (iterateSubdivision R X n m c) := by
  simp [iterateSubdivision, pow_succ']

@[simp] theorem iterateHomotopy_zero (n : ℕ) (c : Chains R X n) :
    iterateHomotopy R X n 0 c = 0 := by simp [iterateHomotopy]

@[simp] theorem iterateHomotopy_succ (n m : ℕ) (c : Chains R X n) :
    iterateHomotopy R X n (m+1) c = iterateHomotopy R X n m c +
      homotopy R X n (iterateSubdivision R X n m c) := by
  simp [iterateHomotopy, Finset.sum_range_succ]

theorem iterateSubdivision_boundary (n m : ℕ) (c : Chains R X (n+1)) :
    chainDifferential R X n (iterateSubdivision R X (n+1) m c) =
      iterateSubdivision R X n m (chainDifferential R X n c) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [iterateSubdivision_succ]
    change boundary R R X n _ = _
    rw [subdivision_boundary]
    exact congrArg (subdivision R X n) ih

theorem iterateHomotopy_identity (n m : ℕ) (c : Chains R X (n+1)) :
    chainDifferential R X (n+1) (iterateHomotopy R X (n+1) m c) +
      iterateHomotopy R X n m (chainDifferential R X n c) =
        iterateSubdivision R X (n+1) m c - c := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := homotopy_identity R X n (iterateSubdivision R X (n+1) m c)
    change chainDifferential R X (n+1) _ + homotopy R X n (chainDifferential R X n _) = _ at h
    rw [iterateSubdivision_boundary] at h
    simp only [iterateHomotopy_succ, map_add, iterateSubdivision_succ]
    calc
      _ = (chainDifferential R X (n+1) (iterateHomotopy R X (n+1) m c) +
          iterateHomotopy R X n m (chainDifferential R X n c)) +
        (chainDifferential R X (n+1) (homotopy R X (n+1) (iterateSubdivision R X (n+1) m c)) +
          homotopy R X n (iterateSubdivision R X n m (chainDifferential R X n c))) := by abel
      _ = _ := by rw [ih, h]; abel

theorem iterateHomotopy_identity_zero (m : ℕ) (c : Chains R X 0) :
    chainDifferential R X 0 (iterateHomotopy R X 0 m c) =
      iterateSubdivision R X 0 m c - c := by
  have h : ∀ m, iterateSubdivision R X 0 m c = c := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp only [iterateSubdivision_succ, subdivision_zero, ih]
  simp [iterateHomotopy, homotopy_zero, h]

theorem iterateSubdivision_small {ι : Type w} (U : OpenCover X ι) (n m : ℕ)
    (c : Chains R X n) (hc : IsSmall U.sets c) :
    IsSmall U.sets (iterateSubdivision R X n m c) := by
  induction m with
  | zero => exact hc
  | succ m ih =>
    rw [iterateSubdivision_succ]
    exact (preserves_small R X U.sets n _ ih).1

theorem iterateHomotopy_small {ι : Type w} (U : OpenCover X ι) (n m : ℕ)
    (c : Chains R X n) (hc : IsSmall U.sets c) :
    IsSmall U.sets (iterateHomotopy R X n m c) := by
  change iterateHomotopy R X n m c ∈ smallModule R U (n+1)
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iterateHomotopy_succ]
    exact (smallModule R U (n+1)).add_mem ih
      ((preserves_small R X U.sets n _ (iterateSubdivision_small R X U n m c hc)).2)

/-- Once a finite chain is small, every further subdivision remains small. -/
theorem iterateSubdivision_small_of_le {ι : Type w} (U : OpenCover X ι)
    (n a b : ℕ) (hab : a ≤ b) (c : Chains R X n)
    (hc : IsSmall U.sets (iterateSubdivision R X n a c)) :
    IsSmall U.sets (iterateSubdivision R X n b c) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction k with
  | zero => simpa using hc
  | succ k ih =>
    rw [Nat.add_succ, iterateSubdivision_succ]
    exact (preserves_small R X U.sets n _ ih).1

/-- The common level is chosen for this finite chain, not uniformly for all
singular simplices. Only the unit-coefficient generators are needed. -/
theorem eventualSmall_of_generators {ι : Type w} (U : OpenCover X ι) (n : ℕ)
    (h : ∀ s : Simplex X n, ∃ m, IsSmall U.sets
      (iterateSubdivision R X n m (Finsupp.single s 1)))
    (c : Chains R X n) :
    ∃ m, IsSmall U.sets (iterateSubdivision R X n m c) := by
  induction c using Finsupp.induction_linear with
  | zero => exact ⟨0, by simp only [map_zero]; exact (smallModule R U n).zero_mem⟩
  | add c d hc hd =>
    obtain ⟨a, ha⟩ := hc
    obtain ⟨b, hb⟩ := hd
    refine ⟨max a b, ?_⟩
    rw [map_add]
    exact (smallModule R U n).add_mem
      (iterateSubdivision_small_of_le R X U n a _ (le_max_left _ _) c ha)
      (iterateSubdivision_small_of_le R X U n b _ (le_max_right _ _) d hb)
  | single s r =>
    obtain ⟨m, hm⟩ := h s
    refine ⟨m, ?_⟩
    rw [← Finsupp.smul_single_one s r, map_smul]
    exact (smallModule R U n).smul_mem r hm

/-- All outgoing differentials vanish if the differential to the designated
next degree vanishes. -/
lemma differential_vanishes {K : ChainComplex (ModuleCat.{v} R) ℕ}
    {n : ℕ} (c : K.X n) (hc : K.d n ((ComplexShape.down ℕ).next n) c = 0)
    (j : ℕ) : K.d n j c = 0 := by
  by_cases h : (ComplexShape.down ℕ).Rel n j
  · have hj := (ComplexShape.down ℕ).next_eq' h
    subst hj
    exact hc
  · rw [K.shape _ _ h]
    rfl

/-- Algebraic part of the comparison theorem. The geometric hypothesis is
stated explicitly here and is not asserted as a theorem. -/
theorem absoluteComparison_of_eventualSmall {ι : Type w} (U : OpenCover X ι)
    (hsmall : ∀ n (c : Chains R X n),
      ∃ m, IsSmall U.sets (iterateSubdivision R X n m c))
    (n : ℕ) : IsIso (homologyMap (smallInclusion R U) n) := by
  let f := smallInclusion R U
  apply (quasiIsoAt_iff_isIso_homologyMap f n).mp
  apply (quasiIsoAt_iff' f (n+1) n (n-1) (by simp) (by cases n <;> simp)).mpr
  apply (ShortComplex.quasiIso_iff _).mpr
  apply shortComplex_comparison
  · intro z hz
    change Chains R X n at z
    change (complex R R X).d n (n-1) z = 0 at hz
    obtain ⟨m, hm⟩ := hsmall n z
    refine ⟨⟨iterateSubdivision R X n m z, hm⟩, ?_, iterateHomotopy R X n m z, ?_⟩
    · change (smallComplex R U).d n (n-1) _ = 0
      cases n with
      | zero => rw [(smallComplex R U).shape _ _ (by simp)]; rfl
      | succ n =>
        change (smallComplex R U).d (n+1) n _ = 0
        simp only [smallComplex, ChainComplex.of_d]
        apply Subtype.ext
        change chainDifferential R X n (iterateSubdivision R X (n+1) m z) = 0
        rw [iterateSubdivision_boundary]
        change chainDifferential R X n z = 0 at hz
        rw [hz, map_zero]
    · change iterateSubdivision R X n m z - z = chainDifferential R X n _
      symm
      cases n with
      | zero => exact iterateHomotopy_identity_zero R X m z
      | succ n =>
        have h := iterateHomotopy_identity R X n m z
        change chainDifferential R X n z = 0 at hz
        simpa only [hz, map_zero, add_zero] using h
  · intro x hx c hc
    change ↥(smallModule R U n) at x
    change Chains R X (n+1) at c
    change (smallComplex R U).d n (n-1) x = 0 at hx
    change chainDifferential R X n c = x.val at hc
    obtain ⟨m, hm⟩ := hsmall (n+1) c
    let b := iterateSubdivision R X (n+1) m c - iterateHomotopy R X n m x.val
    have hb : b ∈ smallModule R U (n+1) :=
      (smallModule R U (n+1)).sub_mem hm
        (iterateHomotopy_small R X U n m x.val x.property)
    refine ⟨⟨b, hb⟩, ?_⟩
    change (smallComplex R U).d (n+1) n ⟨b, hb⟩ = x
    simp only [smallComplex, ChainComplex.of_d]
    apply Subtype.ext
    change chainDifferential R X n b = x.val
    dsimp only [b]
    rw [map_sub, iterateSubdivision_boundary, hc]
    have hi : chainDifferential R X n (iterateHomotopy R X n m x.val) =
        iterateSubdivision R X n m x.val - x.val := by
      cases n with
      | zero => exact iterateHomotopy_identity_zero R X m x.val
      | succ n =>
        change (smallComplex R U).d (n+1) n x = 0 at hx
        simp only [smallComplex, ChainComplex.of_d] at hx
        have hz : chainDifferential R X n x.val = 0 := congrArg Subtype.val hx
        simpa only [hz, map_zero, add_zero] using iterateHomotopy_identity R X n m x.val
    rw [hi]
    abel

/-- Inclusion of restricted-cover small chains in X is degreewise injective. -/
theorem smallSubspaceInclusion_injective {ι : Type w} (U : OpenCover X ι)
    (A : Set X) (n : ℕ) :
    Function.Injective ((smallSubspaceInclusion R U A).f n) := by
  intro c d h
  apply Subtype.ext
  apply P202.RelativeSingularChains.inclusion_injective R R ⟨X, A⟩ n
  exact congrArg Subtype.val h

instance smallSubspaceInclusion_mono {ι : Type w} (U : OpenCover X ι)
    (A : Set X) : Mono (smallSubspaceInclusion R U A) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  exact (ModuleCat.mono_iff_injective _).mpr
    (smallSubspaceInclusion_injective R X U A n)

/-- The relative small quotient sits in the genuine short exact sequence. -/
theorem smallSequence_shortExact {ι : Type w} (U : OpenCover X ι) (A : Set X) :
    (ShortComplex.cokernelSequence (smallSubspaceInclusion R U A)).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by change Mono (smallSubspaceInclusion R U A); infer_instance
  epi_g := inferInstance

/-- The comparison morphism of the small and ordinary pair sequences. -/
def relativeSequenceMap {ι : Type w} (U : OpenCover X ι) (A : Set X) :
    ShortComplex.cokernelSequence (smallSubspaceInclusion R U A) ⟶
      sequence (chainFunctor R R) ⟨X, A⟩ :=
  ShortComplex.Hom.mk (smallInclusion R (restrictedCover U A))
    (smallInclusion R U) (smallRelativeInclusion R U A)
      (smallSubspace_square R U A).symm (cokernel.π_desc _ _ _).symm

/-- The relative comparison follows from the absolute comparison for X and A.
No openness or nonemptiness of A is needed. -/
theorem relativeComparison_of_absolute {ι : Type w} (U : OpenCover X ι) (A : Set X)
    (hX : ∀ n, IsIso (homologyMap (smallInclusion R U) n))
    (hA : ∀ n, IsIso (homologyMap (smallInclusion R (restrictedCover U A)) n))
    (n : ℕ) : IsIso (homologyMap (smallRelativeInclusion R U A) n) := by
  have h₁ : QuasiIso (smallInclusion R (restrictedCover U A)) := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_isIso_homologyMap _ n).mpr (hA n)
  have h₂ : QuasiIso (smallInclusion R U) := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_isIso_homologyMap _ n).mpr (hX n)
  have hlarge : (sequence (chainFunctor R R) ⟨X, A⟩).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _
      (P202.RelativeSingularChains.sequence_shortExact (chainFunctor R R) ⟨X, A⟩)
  have h : QuasiIso (smallRelativeInclusion R U A) :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ (relativeSequenceMap R X U A)
      (smallSequence_shortExact R X U A) hlarge h₁ h₂
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp (h.quasiIsoAt n)

/-- Explicit identification with the span of the selected simplex basis. -/
theorem smallModule_eq_span {ι : Type w} (U : OpenCover X ι) (n : ℕ) :
    smallModule R U n = Submodule.span R
      ((fun s : Simplex X n => Finsupp.single s 1) ''
        {s | ∃ i, Set.range (simplexEquiv X n s) ⊆ U.sets i}) :=
  Finsupp.supported_eq_span_single R _

/-- Assembly of the absolute and relative comparisons from generator smallness.
The finite-chain reduction chooses a level separately for each input chain. -/
theorem comparison_from_generators : comparison_from_generators_type.{u,v,w} := by
  intro hg
  have habs : absoluteComparison_type.{u,v,w} := by
    intro R _ X ι U n
    apply absoluteComparison_of_eventualSmall R X U
    intro k c
    apply eventualSmall_of_generators R X U k
      (fun s => hg R X ι U.sets U.isOpen U.covers k s) c
  refine ⟨habs, ?_⟩
  intro R _ X ι U A n
  exact relativeComparison_of_absolute R X U A (habs R X ι U)
    (habs R (TopCat.of A) _ (restrictedCover U A)) n

/-- The inclusion of small chains induces an isomorphism in every nonnegative
degree, for every open cover and every commutative coefficient ring. -/
theorem absoluteComparison : absoluteComparison_type.{u,v,w} :=
  (comparison_from_generators P202.Topology.smallChainEventualSubdivision).1

/-- The relative small-chain inclusion induces an isomorphism for every
subspace, using its restricted cover with empty intersections discarded. -/
theorem relativeComparison : relativeComparison_type.{u,v,w} :=
  (comparison_from_generators P202.Topology.smallChainEventualSubdivision).2

end P202.SmallChainHomology
