import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.AbstractTubular
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.MetricSplittings
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.BundleOperations
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.TubularLocalGeometry
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.BundleTubularGlobalization

/-! M05.08 on the actual quotient normal fibers. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace SmoothManifolds.AbstractTubular
open ModelData AtlasData MapData BundleData BundleOperationsData TangentData
  QuotientData ConstantRankData AbstractTubularData Bundle Set Filter
open scoped Topology
universe u

/-- A smooth quotient by the image of an injective bundle morphism has
an actual smooth right inverse. Keeping the fiber modules abstract also avoids
unfolding the internal representation of derivation tangent spaces. -/
theorem quotient_rightInverse
    {d l r : ℕ} {a : ModelKind} {X : Type u} [TopologicalSpace X]
    {T : SmoothManifold d a X} {ι κ : Type u} {V E : X → Type u}
    [∀ p, AddCommGroup (V p)] [∀ p, Module ℝ (V p)]
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean l) V)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (A : SmoothVectorBundle T l ι V) (B : SmoothVectorBundle T r κ E)
    (D : SmoothBundleMorphism A B) (hD : ∀ p, Function.Injective (D.linearMap p))
    (Q : SmoothQuotient.{u,u,u,u,u} B (fun p => (D.linearMap p).range) l) :
    letI := Q.topology
    ∃ t : SmoothBundleMorphism Q.bundle B,
      ∀ p v, QuotientData.quotientProjection (fun p => (D.linearMap p).range) p (t.linearMap p v) = v := by
  letI := Q.topology
  let K : (p : X) → Submodule ℝ (E p) := fun p => (D.linearMap p).range
  let q : SmoothBundleMorphism B Q.bundle :=
    ⟨QuotientData.quotientProjection (E := E) K, Q.projection_smooth⟩
  obtain ⟨t, ht, _⟩ := MetricSplittings.shortExact_splitting A B Q.bundle D q hD
    (fun p => (K p).mkQ_surjective) (fun p => (Submodule.ker_mkQ (K p)).symm)
  exact ⟨t, fun p v => LinearMap.congr_fun (ht p) v⟩

/-- Smooth linear lift on the actual quotient normal bundle. -/
theorem normalLift_exists :
    Specs.SmoothManifolds.Ch05.AbstractTubular.normalLift_existsType.{u} := by
  intro m n P M _ _ T S i N
  letI := N.ambientRealization.space.topology
  letI := N.sourceRealization.space.topology
  letI := N.pullback.space.topology
  letI := N.quotient.topology
  let d : SmoothBundleMorphism N.sourceRealization.space.bundle N.pullback.space.bundle :=
    ⟨N.differential, N.differential_smooth⟩
  obtain ⟨t, ht⟩ := quotient_rightInverse N.sourceRealization.space.bundle
    N.pullback.space.bundle d N.injective N.quotient
  exact ⟨⟨t.linearMap, ht, t.smooth⟩⟩

/-- A family of quotient right inverses supplies the complementary linear
summands, including fibers of dimension zero. -/
theorem quotient_sum_bijective {X : Type u} {V E : X → Type u}
    [∀ p, AddCommGroup (V p)] [∀ p, Module ℝ (V p)]
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    (d : (p : X) → V p →ₗ[ℝ] E p) (hd : ∀ p, Function.Injective (d p))
    (t : (p : X) → QuotientFiber (E := E) (fun p => (d p).range) p →ₗ[ℝ] E p)
    (ht : ∀ p v, QuotientData.quotientProjection (E := E) (fun p => (d p).range) p (t p v) = v) :
    ∀ p, Function.Bijective ((d p).coprod (t p)) := by
  intro p
  apply MetricSplittings.split_coprod_bijective (d p) (d p).range.mkQ (t p)
    (hd p) (Submodule.ker_mkQ _).symm
  apply LinearMap.ext
  exact ht p

/-- Compact-parameter radial shrinking, independent of any choice of metric
or uniform radius. This applies to a bundle scaling action once its continuity
has been established. -/
theorem radial_shrinking {X : Type u} [TopologicalSpace X]
    (scale : ℝ → X → X)
    (hscale : Continuous (fun z : ℝ × X => scale z.1 z.2))
    (hone : ∀ z, scale 1 z = z)
    (hmul : ∀ s t z, scale s (scale t z) = scale (s*t) z)
    (Z V : Set X) (hV : IsOpen V) (hZV : Z ⊆ V)
    (hfix : ∀ z ∈ Z, ∀ t : ℝ, scale t z = z) :
    ∃ U : Set X, IsOpen U ∧ U ⊆ V ∧ Z ⊆ U ∧
      ∀ z ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, scale t z ∈ U := by
  let U : Set X := {z | ∀ t ∈ Icc (0 : ℝ) 1, scale t z ∈ V}
  let f : Icc (0 : ℝ) 1 × X → X := fun z => scale z.1.val z.2
  have hf : Continuous f := hscale.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hbad : IsClosed (Prod.snd '' (f ⁻¹' Vᶜ)) :=
    isClosedMap_snd_of_compactSpace _ (hV.isClosed_compl.preimage hf)
  have hU : IsOpen U := by
    have heq : U = (Prod.snd '' (f ⁻¹' Vᶜ))ᶜ := by
      ext z
      constructor
      · intro hz hb
        obtain ⟨⟨t, y⟩, hy, hyz⟩ := hb
        change y = z at hyz
        subst y
        exact hy (hz t.val t.property)
      · intro hz t ht
        by_contra hv
        exact hz ⟨(⟨t, ht⟩, z), hv, rfl⟩
    rw [heq]
    exact hbad.isOpen_compl
  refine ⟨U, hU, ?_, ?_, ?_⟩
  · intro z hz
    simpa only [hone] using hz 1 ⟨zero_le_one, le_rfl⟩
  · intro z hz t ht
    rw [hfix z hz t]
    exact hZV hz
  · intro z hz t ht s hs
    rw [hmul]
    exact hz (s*t) ⟨mul_nonneg hs.1 ht.1,
      (mul_le_mul_of_nonneg_right hs.2 ht.1).trans (by simpa using ht.2)⟩

/-- Joint continuity of scalar multiplication follows from the specified
smooth bundle parametrizations, rather than from a separately assumed topology
on the fibers. -/
theorem bundle_scale_continuous
    {d r : ℕ} {a : ModelKind} {X : Type u} [TopologicalSpace X]
    {T : SmoothManifold d a X} {ι : Type u} {E : X → Type u}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle T r ι E) :
    Continuous (fun z : ℝ × Bundle.TotalSpace (Euclidean r) E =>
      (⟨z.2.proj, z.1 • z.2.snd⟩ : Bundle.TotalSpace (Euclidean r) E)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨i, hi⟩ := B.covers z.2.proj
  let e := B.trivialization i
  have hi' : z.2.proj ∈ e.baseSet := (B.trivialization_baseSet i).symm ▸ hi
  have hp : Continuous (Bundle.TotalSpace.proj : Bundle.TotalSpace (Euclidean r) E → X) :=
    continuous_iff_continuousAt.mpr (fun y => (B.projection_smooth y).1)
  let g : ℝ × Bundle.TotalSpace (Euclidean r) E → X × (ℝ × Euclidean r) :=
    fun y => (y.2.proj, y.1, (e y.2).2)
  have hg : ContinuousAt g z :=
    (hp.continuousAt.comp continuousAt_snd).prodMk
      (continuousAt_fst.prodMk
        ((e.toOpenPartialHomeomorph.continuousAt (e.mem_source.mpr hi')).snd.comp continuousAt_snd))
  have hcont := ((B.smul_smooth i (g z) hi).1).comp hg
  apply hcont.congr_of_eventuallyEq
  have hbase : ∀ᶠ y : ℝ × Bundle.TotalSpace (Euclidean r) E in 𝓝 z,
      y.2.proj ∈ e.baseSet :=
    (hp.comp continuous_snd).continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hi')
  filter_upwards [hbase] with y hy
  change (⟨y.2.proj, y.1 • y.2.snd⟩ :
    Bundle.TotalSpace (Euclidean r) E) = ⟨y.2.proj, y.1 • e.symm y.2.proj (e y.2).2⟩
  rw [e.symm_apply_apply_mk hy]

attribute [local instance] normalTopology

/-- Every open neighborhood of the quotient zero section contains an open
fiberwise star-shaped neighborhood. -/
theorem normal_radial_shrinking
    {m n : ℕ} {P M : Type u} [TopologicalSpace P] [TopologicalSpace M]
    {T : SmoothManifold m .euclidean P} {S : SmoothManifold n .euclidean M}
    {i : P → M} (N : NormalBundle T S i)
    (V : Set (NormalTotal N)) (hV : IsOpen V)
    (hzero : ∀ p, normalZero N p ∈ V) :
    ∃ U : Set (NormalTotal N), IsOpen U ∧ U ⊆ V ∧
      (∀ p, normalZero N p ∈ U) ∧
      ∀ z ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, normalScale N t z ∈ U := by
  obtain ⟨U, hU, hUV, hZU, hstar⟩ := radial_shrinking (normalScale N)
    (bundle_scale_continuous (normalBundle N))
    (by intro z; simp [normalScale])
    (by intro s t z; change (⟨z.proj, s • (t • z.snd)⟩ : NormalTotal N) = ⟨z.proj, (s*t) • z.snd⟩; rw [mul_smul])
    (range (normalZero N)) V hV (by rintro _ ⟨p, rfl⟩; exact hzero p)
    (by rintro _ ⟨p, rfl⟩ t; change (⟨p, t • (0 : NormalFiber N p)⟩ : NormalTotal N) = ⟨p,0⟩; rw [smul_zero])
  exact ⟨U, hU, hUV, fun p => hZU ⟨p, rfl⟩, hstar⟩

/-- The local quotient-normal construction globalizes to a tubular
diffeomorphism, with a fiberwise star-shaped domain. No closed-image or
compactness hypothesis is needed. -/
theorem abstract_tubular :
    Specs.SmoothManifolds.Ch05.AbstractTubular.abstract_tubularType.{u} := by
  intro m n P M _ _ T S i hi
  obtain ⟨N⟩ := BundleOperations.exists_normal T S i hi
  letI := N.ambientRealization.space.topology
  letI := N.pullback.space.topology
  letI := N.quotient.topology
  obtain ⟨O, F, hO, hzO, hzero, hF, hlocal⟩ :=
    TubularLocalGeometry.tubular_local_geometry T S i hi N
  have hemb : Topology.IsEmbedding i := by
    obtain ⟨h, hh⟩ := hi.2.2.2
    have heq : i = (Subtype.val : range i → M) ∘ h := by
      funext p
      exact (hh p).symm
    rw [heq]
    exact Topology.IsEmbedding.subtypeVal.comp h.isEmbedding
  obtain ⟨V, W, hV, hW, h, _, hzV, hiW, hval, hs, hinv, hstar⟩ :=
    BundleTubularGlobalization.bundle_tubular_globalization T S N.quotient.bundle
      i O F hemb hO hzO hzero hF hlocal
  refine ⟨N, ⟨{
    domain := V
    target := W
    isOpen_domain := hV
    isOpen_target := hW
    zero_mem := hzV
    star := hstar
    inclusion_mem := hiW
    homeomorph := h
    zero_eq := ?_
    smooth := hs
    inverse_smooth := hinv }⟩⟩
  intro p
  exact (hval ⟨normalZero N p, hzV p⟩).trans (hzero p)

end SmoothManifolds.AbstractTubular
