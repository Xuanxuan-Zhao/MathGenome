import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.FiniteProperEmbedding
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.GoodProjections
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.SmoothExhaustion
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.ProperEmbedding
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

namespace SmoothManifolds.FiniteProperEmbedding
open ModelData AtlasData MapData FiniteRegularityData GoodProjectionData
  MapClassData PartitionData Set Filter
open scoped Topology BigOperators
universe u
variable {n q : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]

/-- Finite-dimensional smoothness is componentwise for the shared local
ambient-extension definition. Finiteness provides one common neighborhood. -/
theorem smoothEuclidean_iff_scalar (S : SmoothManifold n a M)
    (f : M → Euclidean q) :
    IsSmoothEuclidean S f ↔ ∀ i, ScalarSmooth S.smoothStructure.val (fun p => f p i) := by
  constructor
  · intro hf i p
    apply (scalarContDiffAt_iff _ _ _ _).mpr
    refine ⟨(continuous_apply i).continuousAt.comp (hf p).1, ?_⟩
    intro c hc hp
    obtain ⟨U, hU, hpU, F, hF, heq⟩ := (hf p).2 c hc hp
    exact ⟨U, hU, hpU, fun x => F x i, (contDiffOn_pi.mp hF) i,
      heq.mono (fun _ h => congrFun h i)⟩
  · intro hf p
    have hcomp := fun i => (scalarContDiffAt_iff _ _ _ _).mp (hf i p)
    refine ⟨continuousAt_pi.mpr (fun i => (hcomp i).1), ?_⟩
    intro c hc hp
    choose U hU hpU F hF heq using (fun i => (hcomp i).2 c hc hp)
    refine ⟨⋂ i, U i, isOpen_iInter_of_finite hU, mem_iInter.mpr hpU,
      fun x i => F i x, contDiffOn_pi.mpr (fun i => (hF i).mono (iInter_subset U i)), ?_⟩
    exact (eventually_all.mpr heq).mono (fun _ h => funext h)

/-- A continuous map with a proper exhaustion among its continuous coordinate
observables has compact inverse images. No regularity of level sets is used. -/
theorem proper_of_exhaustion_observable {X : Type u} [TopologicalSpace X]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (e : X → Y) (he : Continuous e) (ρ : X → ℝ) (t : Y → ℝ)
    (ht : Continuous t) (hρ : ∀ c : ℝ, IsCompact {x | ρ x ≤ c})
    (hcoord : ∀ x, t (e x) = ρ x) : IsProper e := by
  intro K hK
  obtain ⟨c, hc⟩ := (hK.image ht).bddAbove
  apply (hρ c).of_isClosed_subset (hK.isClosed.preimage he)
  intro x hx
  change ρ x ≤ c
  rw [← hcoord x]
  exact hc (mem_image_of_mem t hx)

/-- Properness gives the homeomorphism onto precisely the subspace image. -/
theorem homeomorph_of_proper_injective (S : SmoothManifold n a M)
    (e : M → Euclidean q) (he : IsSmoothEuclidean S e)
    (hi : Function.Injective e) (hp : IsProper e) :
    ∃ h : M ≃ₜ Set.range e, ∀ x, (h x).val = e x := by
  have hc : Continuous e := continuous_iff_continuousAt.mpr (fun x => (he x).1)
  have hproper : IsProperMap e :=
    isProperMap_iff_isCompact_preimage.mpr ⟨hc, fun {K} hK => hp K hK⟩
  have hemb : Topology.IsClosedEmbedding e :=
    .of_continuous_injective_isClosedMap hc hi hproper.isClosedMap
  exact ⟨hemb.isEmbedding.toHomeomorph, fun _ => rfl⟩

/-- Closed exhaustion bands; they are sets and are never treated as manifolds. -/
def band (ρ : M → ℝ) (j : ℕ) : Set M := ρ ⁻¹' Icc (j : ℝ) (j + 1)

/-- Slightly enlarged open bands, disjoint within each parity class. -/
def bandNeighborhood (ρ : M → ℝ) (j : ℕ) : Set M :=
  ρ ⁻¹' Ioo ((j : ℝ) - 1 / 4) (j + 5 / 4)

theorem band_subset_neighborhood (ρ : M → ℝ) (j : ℕ) :
    band ρ j ⊆ bandNeighborhood ρ j := by
  intro x hx
  change (j : ℝ) ≤ ρ x ∧ ρ x ≤ j + 1 at hx
  change (j : ℝ) - 1 / 4 < ρ x ∧ ρ x < j + 5 / 4
  constructor <;> linarith [hx.1, hx.2]

theorem isCompact_band (ρ : M → ℝ) (hc : Continuous ρ)
    (hp : ∀ c : ℝ, IsCompact {x | ρ x ≤ c}) (j : ℕ) : IsCompact (band ρ j) := by
  apply (hp (j + 1)).of_isClosed_subset (isClosed_Icc.preimage hc)
  exact fun x hx => hx.2

theorem isCompact_closure_bandNeighborhood
    (ρ : M → ℝ) (hc : Continuous ρ)
    (hp : ∀ c : ℝ, IsCompact {x | ρ x ≤ c}) (j : ℕ) :
    IsCompact (closure (bandNeighborhood ρ j)) := by
  apply (hp (j + 5 / 4)).of_isClosed_subset isClosed_closure
  apply closure_minimal
  · exact fun x hx => le_of_lt hx.2
  · exact isClosed_le hc continuous_const

theorem mem_some_band (ρ : M → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (x : M) :
    ∃ j : ℕ, x ∈ band ρ j := by
  refine ⟨⌊ρ x⌋₊, Nat.floor_le (hρ x), ?_⟩
  exact le_of_lt (Nat.lt_floor_add_one (ρ x))

theorem disjoint_bandNeighborhood_of_parity (ρ : M → ℝ) {i j : ℕ}
    (hne : i ≠ j) (hpar : i % 2 = j % 2) :
    Disjoint (bandNeighborhood ρ i) (bandNeighborhood ρ j) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hgap : i + 2 ≤ j ∨ j + 2 ≤ i := by omega
  change (i : ℝ) - 1 / 4 < ρ x ∧ ρ x < i + 5 / 4 at hxi
  change (j : ℝ) - 1 / 4 < ρ x ∧ ρ x < j + 5 / 4 at hxj
  rcases hgap with hgap | hgap
  · have : (i : ℝ) + 2 ≤ j := by exact_mod_cast hgap
    linarith [hxi.2, hxj.1]
  · have : (j : ℝ) + 2 ≤ i := by exact_mod_cast hgap
    linarith [hxj.2, hxi.1]

theorem locallyFinite_bandNeighborhood (ρ : M → ℝ) (hc : Continuous ρ) :
    LocallyFinite (bandNeighborhood ρ) := by
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt (ρ x + 2)
  refine ⟨ρ ⁻¹' Iio (ρ x + 1), (isOpen_Iio.preimage hc).mem_nhds (by simp),
    (Set.finite_lt_nat N).subset ?_⟩
  rintro j ⟨y, hy, hyx⟩
  change (j : ℝ) - 1 / 4 < ρ y ∧ ρ y < j + 5 / 4 at hy
  change ρ y < ρ x + 1 at hyx
  have hreal : (j : ℝ) < N := by linarith [hy.1]
  exact_mod_cast hreal

/-- Equality of germs preserves the full ambient derivative, including at a face. -/
theorem coordinateDerivative_congr (c : ModelChart n a M) (f g : M → Euclidean q)
    (p : M) (hp : p ∈ c.source)
    (hf : LocalCoordinateExtension (⊤ : ℕ∞) (fun x => (c x).val) f p)
    (heq : f =ᶠ[𝓝 p] g) : coordinateDerivative c f p = coordinateDerivative c g p := by
  obtain ⟨U, hU, hpU, F, hF, hEq⟩ := hf
  have hD := ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt
  exact (FiniteRegularity.coordinateDerivative_eq c f p hp _ ⟨F, hD, hEq⟩).trans
    (FiniteRegularity.coordinateDerivative_eq c g p hp _ ⟨F, hD, hEq.trans heq⟩).symm

/-- A fixed finite number of local coordinates suffices near each compact set.
This is an explicit hypothesis only for the assembly lemma below, not a field
of a manifold and not a hypothesis of the required existence theorem. -/
def CompactUniformImmersions (S : SmoothManifold n a M) (q : ℕ) : Prop :=
  ∀ K : Set M, IsCompact K →
    ∃ (V : Set M) (e : M → Euclidean q), IsOpen V ∧ K ⊆ V ∧
      IsSmoothEuclidean S e ∧ InjOn e V ∧
        ∀ c ∈ S.smoothStructure.val, ∀ p ∈ c.source, p ∈ V →
          Function.Injective (coordinateDerivative c e p)

def parity (j : ℕ) : Fin 2 := ⟨j % 2, Nat.mod_lt _ (by decide)⟩

/-- Only finitely many summands are nonzero near any point. -/
noncomputable def parityBlock (χ : ℕ → M → ℝ) (e : ℕ → M → Euclidean q)
    (b : Fin 2) (p : M) : Euclidean q :=
  fun i => ∑ᶠ j, if parity j = b then χ j p * e j p i else 0

theorem parityBlock_eq (ρ : M → ℝ) (χ : ℕ → M → ℝ)
    (e : ℕ → M → Euclidean q)
    (hsupp : ∀ j, sectionSupport (χ j) ⊆ bandNeighborhood ρ j)
    {j : ℕ} {p : M} (hp : p ∈ bandNeighborhood ρ j) (hχ : χ j p = 1) :
    parityBlock χ e (parity j) p = e j p := by
  classical
  ext i
  rw [parityBlock, finsum_eq_single _ j]
  · simp [hχ]
  · intro k hkj
    by_cases hk : parity k = parity j
    · have hdis := disjoint_bandNeighborhood_of_parity ρ hkj (congrArg Fin.val hk)
      have hzero : χ k p = 0 := by
        apply Function.notMem_support.mp
        intro hne
        exact Set.disjoint_left.mp hdis (hsupp k (subset_closure hne)) hp
      simp [hk, hzero]
    · simp [hk]

/-- Smoothness of each scalar component of a parity block. Its closed support
is controlled by the cutoff support, irrespective of the local map's size. -/
theorem parityBlock_smooth (S : SmoothManifold n a M) (ρ : M → ℝ)
    (hρ : Continuous ρ) (χ : ℕ → M → ℝ) (e : ℕ → M → Euclidean q)
    (hχ : ∀ j, ScalarSmooth S.smoothStructure.val (χ j))
    (he : ∀ j, IsSmoothEuclidean S (e j))
    (hsupp : ∀ j, sectionSupport (χ j) ⊆ bandNeighborhood ρ j)
    (b : Fin 2) : IsSmoothEuclidean S (parityBlock χ e b) := by
  apply (smoothEuclidean_iff_scalar S _).mpr
  intro i
  apply scalarContDiff_finsum
  · intro j
    by_cases hj : parity j = b
    · simpa only [hj, ite_true] using
        scalarContDiff_mul (hχ j) ((smoothEuclidean_iff_scalar S _).mp (he j) i)
    · simpa only [hj, ite_false] using scalarContDiff_const (⊤ : ℕ∞) S.smoothStructure.val 0
  · apply (locallyFinite_bandNeighborhood ρ hρ).subset
    intro j
    apply subset_trans _ (hsupp j)
    apply closure_mono
    intro x hx
    by_contra hzero
    have hz : χ j x = 0 := not_not.mp hzero
    exact hx (by simp [hz])

/-- A finite coordinate set for two q-dimensional blocks and the exhaustion. -/
abbrev BlockIndex (q : ℕ) := Option (Fin 2 × Fin q)

noncomputable def blockIndex (b : Fin 2) (i : Fin q) : Fin (Fintype.card (BlockIndex q)) :=
  Fintype.equivFin (BlockIndex q) (some (b, i))

noncomputable def exhaustionIndex (q : ℕ) : Fin (Fintype.card (BlockIndex q)) :=
  Fintype.equivFin (BlockIndex q) none

noncomputable def assembledMap (ρ : M → ℝ) (χ : ℕ → M → ℝ)
    (e : ℕ → M → Euclidean q) (p : M) : Euclidean (Fintype.card (BlockIndex q)) :=
  fun k => match (Fintype.equivFin (BlockIndex q)).symm k with
    | none => ρ p
    | some (b, i) => parityBlock χ e b p i

@[simp] theorem assembledMap_block (ρ : M → ℝ) (χ : ℕ → M → ℝ)
    (e : ℕ → M → Euclidean q) (p : M) (b : Fin 2) (i : Fin q) :
    assembledMap ρ χ e p (blockIndex b i) = parityBlock χ e b p i := by
  simp [assembledMap, blockIndex]

@[simp] theorem assembledMap_exhaustion (ρ : M → ℝ) (χ : ℕ → M → ℝ)
    (e : ℕ → M → Euclidean q) (p : M) :
    assembledMap ρ χ e p (exhaustionIndex q) = ρ p := by
  simp [assembledMap, exhaustionIndex]

noncomputable def blockProjection (b : Fin 2) :
    Euclidean (Fintype.card (BlockIndex q)) →L[ℝ] Euclidean q :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (blockIndex b i))

@[simp] theorem blockProjection_assembledMap (ρ : M → ℝ) (χ : ℕ → M → ℝ)
    (e : ℕ → M → Euclidean q) (p : M) (b : Fin 2) :
    blockProjection b (assembledMap ρ χ e p) = parityBlock χ e b p := by
  ext i
  exact assembledMap_block ρ χ e p b i

theorem assembledMap_smooth (S : SmoothManifold n a M) (ρ : M → ℝ)
    (hρ : ScalarSmooth S.smoothStructure.val ρ) (χ : ℕ → M → ℝ)
    (e : ℕ → M → Euclidean q)
    (hχ : ∀ j, ScalarSmooth S.smoothStructure.val (χ j))
    (he : ∀ j, IsSmoothEuclidean S (e j))
    (hsupp : ∀ j, sectionSupport (χ j) ⊆ bandNeighborhood ρ j) :
    IsSmoothEuclidean S (assembledMap ρ χ e) := by
  have hcont : Continuous ρ := continuous_iff_continuousAt.mpr
    (fun p => ((scalarContDiffAt_iff _ _ _ _).mp (hρ p)).1)
  apply (smoothEuclidean_iff_scalar S _).mpr
  intro k
  cases hk : (Fintype.equivFin (BlockIndex q)).symm k with
  | none => simpa only [assembledMap, hk] using hρ
  | some bi =>
    simpa only [assembledMap, hk] using
      (smoothEuclidean_iff_scalar S _).mp
        (parityBlock_smooth S ρ hcont χ e hχ he hsupp bi.1) bi.2

/-- Assembly from compact-neighborhood immersions of one fixed finite target
dimension. The exhaustion coordinate ensures properness, even when the local
immersions are unbounded. No exhaustion band is given a manifold structure. -/
theorem exists_finite_proper_embedding_of_compact_uniform
    (S : SmoothManifold n a M) (hloc : CompactUniformImmersions S q) :
    ∃ (r : ℕ) (E : M → Euclidean r),
      IsEuclideanImmersion S E ∧ Function.Injective E ∧ IsProper E ∧
        ∃ h : M ≃ₜ Set.range E, ∀ p, (h p).val = E p := by
  classical
  let : T2Space M := S.topologicalManifold.hausdorff
  obtain ⟨ρ, hρ, hρnonneg, hρproper⟩ := exists_smooth_exhaustion S
  have hρcont : Continuous ρ := continuous_iff_continuousAt.mpr
    (fun p => ((scalarContDiffAt_iff _ _ _ _).mp (hρ p)).1)
  have hlocal (j : ℕ) := hloc (closure (bandNeighborhood ρ j))
    (isCompact_closure_bandNeighborhood ρ hρcont hρproper j)
  choose V e hV hsub he hi hd using hlocal
  have hcut (j : ℕ) : ∃ χ : M → ℝ, IsCutoff S (band ρ j) (bandNeighborhood ρ j) χ :=
    exists_smooth_cutoff S (band ρ j) (bandNeighborhood ρ j)
      (isCompact_band ρ hρcont hρproper j).isClosed
      (isOpen_Ioo.preimage hρcont) (band_subset_neighborhood ρ j)
  choose χ hχ using hcut
  have hsupp (j : ℕ) : sectionSupport (χ j) ⊆ bandNeighborhood ρ j := (hχ j).2.2.2
  let E := assembledMap ρ χ e
  have hEs : IsSmoothEuclidean S E :=
    assembledMap_smooth S ρ hρ χ e (fun j => (hχ j).1) he hsupp
  have hpoint (j : ℕ) {p : M} (hp : p ∈ band ρ j) :
      parityBlock χ e (parity j) p = e j p := by
    obtain ⟨W, _, hKW, hχW⟩ := (hχ j).2.2.1
    exact parityBlock_eq ρ χ e hsupp (band_subset_neighborhood ρ j hp) (hχW (hKW hp))
  have hgerm (j : ℕ) {p : M} (hp : p ∈ band ρ j) :
      (fun x => blockProjection (parity j) (E x)) =ᶠ[𝓝 p] e j := by
    obtain ⟨W, hW, hKW, hχW⟩ := (hχ j).2.2.1
    filter_upwards [hW.mem_nhds (hKW hp),
      (isOpen_Ioo.preimage hρcont).mem_nhds (band_subset_neighborhood ρ j hp)] with x hxW hxU
    change blockProjection (parity j) (assembledMap ρ χ e x) = e j x
    rw [blockProjection_assembledMap]
    exact parityBlock_eq ρ χ e hsupp hxU (hχW hxW)
  have hEp : IsProper E := proper_of_exhaustion_observable E
    (continuous_iff_continuousAt.mpr (fun p => (hEs p).1)) ρ
    (fun z => z (exhaustionIndex q)) (continuous_apply _) hρproper
    (assembledMap_exhaustion ρ χ e)
  have hEi : Function.Injective E := by
    intro p p' hpp'
    have hlevel : ρ p = ρ p' := by
      simpa only [E, assembledMap_exhaustion] using
        congrFun hpp' (exhaustionIndex q)
    obtain ⟨j, hpj⟩ := mem_some_band ρ hρnonneg p
    have hpj' : p' ∈ band ρ j := by
      change ρ p' ∈ Icc _ _
      rw [← hlevel]
      exact hpj
    apply hi j
      (hsub j (subset_closure (band_subset_neighborhood ρ j hpj)))
      (hsub j (subset_closure (band_subset_neighborhood ρ j hpj')))
    calc
      e j p = blockProjection (parity j) (E p) := by
        change e j p = blockProjection (parity j) (assembledMap ρ χ e p)
        rw [blockProjection_assembledMap, hpoint j hpj]
      _ = blockProjection (parity j) (E p') := congrArg _ hpp'
      _ = e j p' := by
        change blockProjection (parity j) (assembledMap ρ χ e p') = e j p'
        rw [blockProjection_assembledMap, hpoint j hpj']
  have hEim : IsEuclideanImmersion S E := by
    refine ⟨hEs, ?_⟩
    intro c hc p hpc
    obtain ⟨j, hpj⟩ := mem_some_band ρ hρnonneg p
    have hder := coordinateDerivative_congr c
      (fun x => blockProjection (parity j) (E x)) (e j) p hpc
      ((GoodProjections.smoothEuclidean_postcomp S E hEs (blockProjection (parity j)) p).2
        c hc hpc) (hgerm j hpj)
    rw [GoodProjections.coordinateDerivative_postcomp c E p hpc ((hEs p).2 c hc hpc)] at hder
    intro v w hvw
    apply hd j c hc p hpc
      (hsub j (subset_closure (band_subset_neighborhood ρ j hpj)))
    rw [← hder]
    exact congrArg (blockProjection (parity j)) hvw
  exact ⟨_, E, hEim, hEi, hEp, homeomorph_of_proper_injective S E hEs hEi hEp⟩

/-- A chart coordinate multiplied by a cutoff whose closed support is in the
chart is globally smooth, even though the total chart map is arbitrary outside
its source. -/
theorem cutoff_chart_coordinate_smooth (S : SmoothManifold n a M)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (b : M → ℝ)
    (hb : ScalarSmooth S.smoothStructure.val b) (hsupp : sectionSupport b ⊆ c.source)
    (i : Fin n) : ScalarSmooth S.smoothStructure.val (fun x => b x * (c x).val i) := by
  intro p
  by_cases hp : p ∈ c.source
  · apply ScalarContDiffAt.mul (hb p)
    apply scalarContDiffAt_of_chart S.smoothStructure.property.1 hc hp
    exact ⟨univ, isOpen_univ, mem_univ _, fun z => z i,
      (contDiff_apply ℝ (fun _ : Fin n => ℝ) i).contDiffOn, Eventually.of_forall (fun _ => rfl)⟩
  · have hp' : p ∉ sectionSupport b := fun h => hp (hsupp h)
    apply ScalarContDiffAt.congr (ScalarContDiffAt.const _ _ 0 p)
    filter_upwards [isClosed_closure.compl_mem_nhds hp'] with x hx
    have hz : b x = 0 := Function.notMem_support.mp (fun h => hx (subset_closure h))
    simp [hz]

/-- The first local construction in the source: finitely many chart-cutoff
blocks give an injective full immersion near an arbitrary compact subset.
The finite dimension here may depend on the compact set. -/
theorem exists_compact_neighborhood_immersion (S : SmoothManifold n a M)
    (K : Set M) (hK : IsCompact K) :
    ∃ (q : ℕ) (V : Set M) (e : M → Euclidean q), IsOpen V ∧ K ⊆ V ∧
      IsSmoothEuclidean S e ∧ InjOn e V ∧
        ∀ c ∈ S.smoothStructure.val, ∀ p ∈ c.source, p ∈ V →
          Function.Injective (coordinateDerivative c e p) := by
  classical
  have hloc (p : M) : ∃ c : ModelChart n a M, c ∈ S.smoothStructure.val ∧
      ∃ b : M → ℝ, ScalarSmooth S.smoothStructure.val b ∧ sectionSupport b ⊆ c.source ∧
      ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ W ⊆ c.source ∧ EqOn b (fun _ => 1) W := by
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
    obtain ⟨b, hb, _, hb1, hsupp, _⟩ := exists_local_bump S p c.source c.open_source hp
    obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hb1
    exact ⟨c, hc, b, hb, hsupp, W ∩ c.source, hW.inter c.open_source,
      ⟨hpW, hp⟩, inter_subset_right, fun x hx => hWsub hx.1⟩
  choose c hc b hb hsupp W hW hpW hWs hbW using hloc
  obtain ⟨J, hJ⟩ := hK.elim_finite_subcover W hW (fun x _ => mem_iUnion.mpr ⟨x, hpW x⟩)
  let I := {p // p ∈ J}
  let ξ := I × Option (Fin n)
  let q := Fintype.card ξ
  let index : ξ → Fin q := Fintype.equivFin ξ
  let e : M → Euclidean q := fun x k =>
    match (Fintype.equivFin ξ).symm k with
      | (i, none) => b i.val x
      | (i, some j) => b i.val x * (c i.val x).val j
  have hescalar (x : M) (i : I) : e x (index (i, none)) = b i.val x := by
    simp [e, index]
  have hecoord (x : M) (i : I) (j : Fin n) :
      e x (index (i, some j)) = b i.val x * (c i.val x).val j := by simp [e, index]
  have he : IsSmoothEuclidean S e := by
    apply (smoothEuclidean_iff_scalar S _).mpr
    intro k
    rcases hk : (Fintype.equivFin ξ).symm k with ⟨i, j⟩
    cases j with
    | none => simpa only [e, hk] using hb i.val
    | some j =>
      simpa only [e, hk] using (cutoff_chart_coordinate_smooth S (c i.val) (hc i.val)
        (b i.val) (hb i.val) (hsupp i.val) j)
  let V := ⋃ i ∈ J, W i
  have hVi {p : M} (hp : p ∈ V) : ∃ i : I, p ∈ W i.val := by
    obtain ⟨i, hpi⟩ := mem_iUnion.mp hp
    obtain ⟨hi, hpi⟩ := mem_iUnion.mp hpi
    exact ⟨⟨i, hi⟩, hpi⟩
  refine ⟨q, V, e, isOpen_biUnion (fun i _ => hW i), hJ, he, ?_, ?_⟩
  · intro p hp p' _ hpp'
    obtain ⟨i, hpi⟩ := hVi hp
    have hbip : b i.val p = 1 := hbW i.val hpi
    have hbip' : b i.val p' = 1 := by
      have hh := congrFun hpp' (index (i, none))
      rwa [hescalar, hescalar, hbip, eq_comm] at hh
    have hpc : p ∈ (c i.val).source := hWs i.val hpi
    have hp'c : p' ∈ (c i.val).source := hsupp i.val (subset_closure (by change b i.val p' ≠ 0; rw [hbip']; norm_num))
    have hchart : c i.val p = c i.val p' := by
      apply Subtype.ext
      funext j
      have hh := congrFun hpp' (index (i, some j))
      simpa only [hecoord, hbip, hbip', one_mul] using hh
    exact (c i.val).injOn hpc hp'c hchart
  · intro d hd p hpd hpV
    obtain ⟨i, hpi⟩ := hVi hpV
    let P : Euclidean q →L[ℝ] Euclidean n :=
      ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (index (i, some j)))
    have hgerm : (fun x => P (e x)) =ᶠ[𝓝 p] (fun x => (c i.val x).val) := by
      filter_upwards [(hW i.val).mem_nhds hpi] with x hx
      ext j
      change e x (index (i, some j)) = (c i.val x).val j
      rw [hecoord, hbW i.val hx, one_mul]
    have hder := coordinateDerivative_congr d (fun x => P (e x))
      (fun x => (c i.val x).val) p hpd
      ((GoodProjections.smoothEuclidean_postcomp S e he P p).2 d hd hpd) hgerm
    rw [GoodProjections.coordinateDerivative_postcomp d e p hpd ((he p).2 d hd hpd)] at hder
    have hpc : p ∈ (c i.val).source := hWs i.val hpi
    have hchain := FiniteRegularity.derivative_cocycle (⊤ : ℕ∞) (by simp)
      S.smoothStructure.val S.smoothStructure.property.1 d (c i.val) d hd (hc i.val) hd
      p hpd hpc hpd
    rw [FiniteRegularity.chartDerivative_id d p hpd] at hchain
    intro v w hvw
    have hh : chartDerivative d (c i.val) id p v = chartDerivative d (c i.val) id p w := by
      change coordinateDerivative d (fun x => (c i.val x).val) p v =
        coordinateDerivative d (fun x => (c i.val x).val) p w
      rw [← hder]
      exact congrArg P hvw
    have h := congrArg (chartDerivative (c i.val) d id p) hh
    change ((chartDerivative (c i.val) d id p).comp (chartDerivative d (c i.val) id p)) v =
      ((chartDerivative (c i.val) d id p).comp (chartDerivative d (c i.val) id p)) w at h
    rwa [← hchain] at h

/-- Restrict an atlas to an open subspace, before taking its maximal extension. -/
theorem openSubsetAtlas_isContDiffAtlas (S : SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) :
    IsContDiffAtlas (⊤ : ℕ∞) (openSubsetAtlas S.smoothStructure.val U hU) := by
  have hA := S.smoothStructure.property.1
  constructor
  · intro x
    obtain ⟨c, hc, hxc⟩ := hA.1 x.val
    refine ⟨c.subtypeRestr (s := ⟨U, hU⟩) ⟨x⟩, ⟨⟨x⟩, c, hc, rfl⟩, ?_⟩
    simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxc
  · rintro _ ⟨hne, c, hc, rfl⟩ _ ⟨hne', d, hd, rfl⟩
    apply contDiffCompatible_of_germs
    · intro x hxc hxd
      have hxc0 : x.val ∈ c.source := by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxc
      have hxd0 : x.val ∈ d.source := by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxd
      exact LocalCoordinateExtension.precomp
        (chartContDiffAt_of_compatible (hA.2 c hc d hd) hxc0 hxd0)
        continuousAt_subtype_val rfl
    · intro x hxd hxc
      have hxc0 : x.val ∈ c.source := by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxc
      have hxd0 : x.val ∈ d.source := by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxd
      exact LocalCoordinateExtension.precomp
        (chartContDiffAt_of_compatible (hA.2 d hd c hc) hxd0 hxc0)
        continuousAt_subtype_val rfl

/-- The canonical induced smooth structure on an open subspace. Empty open
subspaces require no chosen points and are included. -/
noncomputable def openSubmanifold (S : SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) : SmoothManifold n a U := by
  let : T2Space M := S.topologicalManifold.hausdorff
  let : SecondCountableTopology M := S.topologicalManifold.secondCountable
  let A := openSubsetAtlas S.smoothStructure.val U hU
  have hA := openSubsetAtlas_isContDiffAtlas S U hU
  exact {
    topologicalManifold := ⟨inferInstance, inferInstance, A, hA.1⟩
    smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) A, maximalExtension_isMaximal hA⟩ }

/-- The same extension gives the same full derivative on an open subspace. -/
theorem coordinateDerivative_open_restriction (c : ModelChart n a M)
    (f : M → Euclidean q) (U : Set M) (hU : IsOpen U) (x : U)
    (hne : Nonempty U) (hxc : x.val ∈ c.source)
    (hf : LocalCoordinateExtension (⊤ : ℕ∞) (fun y => (c y).val) f x.val) :
    coordinateDerivative (c.subtypeRestr (s := ⟨U, hU⟩) hne) (fun y : U => f y.val) x =
      coordinateDerivative c f x.val := by
  obtain ⟨W, hW, hxW, F, hF, heq⟩ := hf
  have hD := ((hF.contDiffAt (hW.mem_nhds hxW)).differentiableAt (by simp)).hasFDerivAt
  rw [FiniteRegularity.coordinateDerivative_eq c f x.val hxc _ ⟨F, hD, heq⟩]
  apply FiniteRegularity.coordinateDerivative_eq _ _ x
    (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxc)
  exact ⟨F, hD, heq.comp_tendsto continuousAt_subtype_val⟩

theorem smoothEuclidean_open_restriction (S : SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) (f : M → Euclidean q) (hf : IsSmoothEuclidean S f) :
    IsSmoothEuclidean (openSubmanifold S U hU) (fun x : U => f x.val) := by
  intro x
  refine ⟨(hf x.val).1.comp continuousAt_subtype_val, ?_⟩
  intro d hd hxd
  obtain ⟨c, hc, hxc⟩ := S.smoothStructure.property.1.1 x.val
  let c' := c.subtypeRestr (s := ⟨U, hU⟩) ⟨x⟩
  have hc' : c' ∈ openSubsetAtlas S.smoothStructure.val U hU := ⟨⟨x⟩, c, hc, rfl⟩
  have hxc' : x ∈ c'.source := by
    simpa only [c', OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxc
  have hbase : LocalCoordinateExtension (⊤ : ℕ∞) (fun y : U => (c' y).val)
      (fun y : U => f y.val) x :=
    LocalCoordinateExtension.precomp ((hf x.val).2 c hc hxc) continuousAt_subtype_val rfl
  exact LocalCoordinateExtension.comp hbase
    (chartContDiffAt_of_compatible (hd c' hc') hxd hxc')

/-- Chart transitions have injective full derivatives even along the boundary. -/
theorem chartDerivative_injective (S : SmoothManifold n a M)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : M) (hpc : p ∈ c.source) (hpd : p ∈ d.source) :
    Function.Injective (chartDerivative c d id p) := by
  have hchain := FiniteRegularity.derivative_cocycle (⊤ : ℕ∞) (by simp)
    S.smoothStructure.val S.smoothStructure.property.1 c d c hc hd hc p hpc hpd hpc
  rw [FiniteRegularity.chartDerivative_id c p hpc] at hchain
  intro v w hvw
  have h := congrArg (chartDerivative d c id p) hvw
  change ((chartDerivative d c id p).comp (chartDerivative c d id p)) v =
    ((chartDerivative d c id p).comp (chartDerivative c d id p)) w at h
  rwa [← hchain] at h

/-- One full-rank chart at each point suffices, once smoothness is known. -/
theorem immersion_of_one_chart (S : SmoothManifold n a M) (f : M → Euclidean q)
    (hf : IsSmoothEuclidean S f)
    (h : ∀ p, ∃ c ∈ S.smoothStructure.val, p ∈ c.source ∧
      Function.Injective (coordinateDerivative c f p)) : IsEuclideanImmersion S f := by
  refine ⟨hf, ?_⟩
  intro d hd p hpd
  obtain ⟨c, hc, hpc, hinj⟩ := h p
  rw [GoodProjections.coordinateDerivative_change_source S f hf c d hc hd p hpc hpd]
  exact hinj.comp (chartDerivative_injective S d c hd hc p hpd hpc)

theorem immersion_open_restriction (S : SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) (f : M → Euclidean q) (hf : IsSmoothEuclidean S f)
    (hd : ∀ c ∈ S.smoothStructure.val, ∀ p ∈ c.source, p ∈ U →
      Function.Injective (coordinateDerivative c f p)) :
    IsEuclideanImmersion (openSubmanifold S U hU) (fun x : U => f x.val) := by
  apply immersion_of_one_chart _ _ (smoothEuclidean_open_restriction S U hU f hf)
  intro x
  obtain ⟨c, hc, hxc⟩ := S.smoothStructure.property.1.1 x.val
  let c' := c.subtypeRestr (s := ⟨U, hU⟩) ⟨x⟩
  refine ⟨c', subset_maximalExtension (openSubsetAtlas_isContDiffAtlas S U hU)
    ⟨⟨x⟩, c, hc, rfl⟩, ?_, ?_⟩
  · simpa only [c', OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hxc
  · rw [coordinateDerivative_open_restriction c f U hU x ⟨x⟩ hxc ((hf x.val).2 c hc hxc)]
    exact hd c hc x.val hxc x.property

/-- Reflecting injectivity of a derivative from an open submanifold uses the
actual same extension germ, so it retains the normal vectors at a face. -/
theorem immersion_open_reflection (S : SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) (f : M → Euclidean q) (hf : IsSmoothEuclidean S f)
    (him : IsEuclideanImmersion (openSubmanifold S U hU) (fun x : U => f x.val)) :
    ∀ c ∈ S.smoothStructure.val, ∀ p ∈ c.source, p ∈ U →
      Function.Injective (coordinateDerivative c f p) := by
  intro c hc p hpc hpU
  let x : U := ⟨p, hpU⟩
  let c' := c.subtypeRestr (s := ⟨U, hU⟩) ⟨x⟩
  have hc' : c' ∈ (openSubmanifold S U hU).smoothStructure.val :=
    subset_maximalExtension (openSubsetAtlas_isContDiffAtlas S U hU) ⟨⟨x⟩, c, hc, rfl⟩
  have hpc' : x ∈ c'.source := by
    simpa only [c', OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hpc
  have h := him.2 c' hc' x hpc'
  rwa [coordinateDerivative_open_restriction c f U hU x ⟨x⟩ hpc ((hf p).2 c hc hpc)] at h

/-- Padding a finite coordinate tuple with zeros is an injective continuous
linear map, including the unique map out of the zero-dimensional space. -/
theorem exists_padding {q r : ℕ} (hqr : q ≤ r) :
    ∃ P : Euclidean q →L[ℝ] Euclidean r, Function.Injective P := by
  classical
  let P : Euclidean q →L[ℝ] Euclidean r :=
    ContinuousLinearMap.pi (fun j => if h : j.val < q then
      ContinuousLinearMap.proj (⟨j.val, h⟩ : Fin q) else 0)
  refine ⟨P, ?_⟩
  intro v w hvw
  funext i
  have h := congrFun hvw (⟨i.val, lt_of_lt_of_le i.isLt hqr⟩ : Fin r)
  simpa [P, i.isLt] using h

/-- Good projections reduce the dimension of an injective immersion on an
open neighborhood. The maps remain globally smooth because every step is a
linear postcomposition of the original globally defined map. -/
theorem reduce_immersion_on_open (S : SmoothManifold n a M) (U : Set M) (hU : IsOpen U) :
    ∀ (q : ℕ) (e : M → Euclidean q), IsSmoothEuclidean S e → InjOn e U →
      (∀ c ∈ S.smoothStructure.val, ∀ p ∈ c.source, p ∈ U →
        Function.Injective (coordinateDerivative c e p)) →
      ∃ g : M → Euclidean (2 * n + 1), IsSmoothEuclidean S g ∧ InjOn g U ∧
        ∀ c ∈ S.smoothStructure.val, ∀ p ∈ c.source, p ∈ U →
          Function.Injective (coordinateDerivative c g p) := by
  classical
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro e he hi hd
    by_cases hq : q ≤ 2 * n + 1
    · obtain ⟨P, hP⟩ := exists_padding hq
      refine ⟨fun x => P (e x), GoodProjections.smoothEuclidean_postcomp S e he P,
        fun x hx y hy hxy => hi hx hy (hP hxy), ?_⟩
      intro c hc p hpc hpU
      rw [GoodProjections.coordinateDerivative_postcomp c e p hpc ((he p).2 c hc hpc)]
      exact hP.comp (hd c hc p hpc hpU)
    · have hqpos : 0 < q := by omega
      obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hqpos)
      let T := openSubmanifold S U hU
      let er : U → Euclidean (d + 1) := fun x => e x.val
      have her : IsEuclideanImmersion T er := immersion_open_restriction S U hU e he hd
      have hir : Function.Injective er := by
        intro x y hxy
        exact Subtype.ext (hi x.property y.property hxy)
      let : Nonempty (ProjectiveData.RealProjectiveSpace d) :=
        ⟨ProjectiveData.projectiveProjection (SphereTorus.sphereBase d)⟩
      have hdim : 2 * n + 1 < d + 1 := by omega
      have hdense := GoodProjections.injective_immersion_directions_dense T er her hir hdim
        (⊥ : Submodule ℝ (Euclidean (d + 1))) bot_ne_top
      obtain ⟨L, _, hLi, hLim⟩ := hdense.nonempty
      let A : ProjectionSpace L ≃L[ℝ] Euclidean d :=
        ContinuousLinearEquiv.ofFinrankEq (by
          rw [GoodProjections.projectionSpace_finrank]
          simp [Euclidean, ModelData.Euclidean])
      let R : Euclidean (d + 1) →L[ℝ] ProjectionSpace L :=
        (projectionLinear L).rangeRestrict.toContinuousLinearMap
      let P : Euclidean (d + 1) →L[ℝ] Euclidean d := A.toContinuousLinearMap.comp R
      have hP (v w : Euclidean (d + 1)) (hvw : P v = P w) :
          projection L v = projection L w := by
        have hh : R v = R w := A.injective hvw
        exact congrArg Subtype.val hh
      let f : M → Euclidean d := fun x => P (e x)
      have hf : IsSmoothEuclidean S f := GoodProjections.smoothEuclidean_postcomp S e he P
      have hfi : InjOn f U := by
        intro x hx y hy hxy
        have hproj : projectedMap L er ⟨x, hx⟩ = projectedMap L er ⟨y, hy⟩ :=
          Subtype.ext (hP (e x) (e y) hxy)
        exact congrArg Subtype.val (hLi hproj)
      have hpr : IsSmoothEuclidean S (fun x => projection L (e x)) :=
        GoodProjections.smoothEuclidean_postcomp S e he (projection L)
      have hprd := immersion_open_reflection S U hU (fun x => projection L (e x)) hpr hLim
      have hfd : ∀ c ∈ S.smoothStructure.val, ∀ p ∈ c.source, p ∈ U →
          Function.Injective (coordinateDerivative c f p) := by
        intro c hc p hpc hpU
        have hdi := hprd c hc p hpc hpU
        rw [GoodProjections.coordinateDerivative_postcomp c e p hpc ((he p).2 c hc hpc)] at hdi
        rw [GoodProjections.coordinateDerivative_postcomp c e p hpc ((he p).2 c hc hpc)]
        intro v w hvw
        apply hdi
        exact hP _ _ hvw
      exact ih d (by omega) f hf hfi hfd

/-- The uniform finite bound needed for the two parity blocks follows from
finite chart blocks and projection on their open neighborhood. -/
theorem compactUniformImmersions (S : SmoothManifold n a M) :
    CompactUniformImmersions S (2 * n + 1) := by
  intro K hK
  obtain ⟨q, V, e, hV, hKV, he, hi, hd⟩ := exists_compact_neighborhood_immersion S K hK
  obtain ⟨g, hg, hgi, hgd⟩ := reduce_immersion_on_open S V hV q e he hi hd
  exact ⟨V, g, hV, hKV, hg, hgi, hgd⟩

/-- The finite-dimensional existence stage of proper weak Whitney embedding.
The target is not assumed to have the final sharp dimension. -/
theorem exists_finite_proper_embedding :
    Specs.SmoothManifolds.Ch04.FiniteProperEmbedding.exists_finite_proper_embeddingType.{u} := by
  intro n a M _ S
  exact exists_finite_proper_embedding_of_compact_uniform S (compactUniformImmersions S)

end SmoothManifolds.FiniteProperEmbedding
