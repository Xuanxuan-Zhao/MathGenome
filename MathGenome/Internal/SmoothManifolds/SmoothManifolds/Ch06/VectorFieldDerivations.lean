import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.VectorFieldDerivations
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Bundle
namespace SmoothManifolds.VectorFields
open ModelData AtlasData MapData PartitionData TangentData DifferentialData
  TangentBundleData VectorFieldData Set Filter
open scoped Topology
universe u

open private scalar_comp_at from MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential

section Algebra
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M)

/-- Evaluation of an algebraic derivation at a point is a point derivation. -/
def evaluate (D : RealDerivation S) (p : M) : GlobalPointDerivation S p :=
  ⟨{ toFun := fun f => (D f).val p
     map_add' := by intro f g; exact congrArg (fun h : GlobalSmooth S => h.val p) (map_add D f g)
     map_smul' := by intro c f; exact congrArg (fun h : GlobalSmooth S => h.val p) (D.map_smul c f) }, by
    intro f g
    exact congrArg (fun h : GlobalSmooth S => h.val p) (D.leibniz f g)⟩

/-- Locality follows from the proved global point-derivation comparison. -/
theorem derivation_locality (D : RealDerivation S) (p : M)
    (f g : GlobalSmooth S) (hfg : f.val =ᶠ[𝓝 p] g.val) :
    (D f).val p = (D g).val p := by
  have hz : (f - g).val =ᶠ[𝓝 p] (fun _ => 0) := by
    filter_upwards [hfg] with x hx
    exact sub_eq_zero.mpr hx
  have h := global_derivation_locality S p (evaluate S D p) (f - g) hz
  change (D (f - g)).val p = 0 at h
  rw [map_sub] at h
  exact sub_eq_zero.mp h

theorem derivation_local_action (D : RealDerivation S) (p : M) (r : M → ℝ)
    (hr : ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val r p) :
    ∃! t : ℝ, ∀ f : GlobalSmooth S, f.val =ᶠ[𝓝 p] r → (D f).val p = t := by
  obtain ⟨g, hg, hgr⟩ := exists_global_representative S p r hr
  let g' : GlobalSmooth S := ⟨g, (mem_globalSmoothAlgebra_iff S g).mpr hg⟩
  refine ⟨(D g').val p, ?_, ?_⟩
  · intro f hf
    exact derivation_locality S D p f g' (hf.trans hgr.symm)
  · intro t ht
    exact (ht g' hgr).symm

/-- The underlying section attached to a derivation, before its smoothness proof. -/
noncomputable def sectionOfDerivation (D : RealDerivation S) : Section S :=
  fun p => (germGlobalDerivationEquiv S p).symm (evaluate S D p)

theorem sectionOfDerivation_apply (D : RealDerivation S) (p : M)
    (f : GlobalSmooth S) (g : SmoothGerm S p) (hfg : Germ.ofFun f.val = g.val) :
    (sectionOfDerivation S D p).val g = (D f).val p := by
  have he : (germGlobalDerivationEquiv S p (sectionOfDerivation S D p)).val f =
      (D f).val p := by
    rw [sectionOfDerivation, LinearEquiv.apply_symm_apply]
    rfl
  change (sectionOfDerivation S D p).val (globalToGerm S p f) = _ at he
  have hg : globalToGerm S p f = g := Subtype.ext hfg
  rwa [hg] at he

/-- Equality on global functions detects equality in the original tangent fiber. -/
theorem tangent_ext_global (p : M) (v z : TangentSpace S p)
    (h : ∀ f : GlobalSmooth S, v.val (globalToGerm S p f) =
      z.val (globalToGerm S p f)) : v = z := by
  apply Subtype.ext
  ext g
  obtain ⟨f, rfl⟩ := globalToGerm_surjective S p g
  exact h f

/-- A global derivation determines its representing section uniquely. -/
theorem represents_unique {B : TangentBundleStructure S} (X Y : SmoothField B)
    (D : RealDerivation S) (hX : Represents X D) (hY : Represents Y D) : X = Y := by
  have hv : X.val = Y.val := by
    funext p
    apply tangent_ext_global S p
    intro f
    exact (hX p f (globalToGerm S p f) rfl).symm.trans
      (hY p f (globalToGerm S p f) rfl)
  cases X
  cases Y
  cases hv
  rfl

/-- A section also determines its representing derivation uniquely. -/
theorem representing_derivation_unique {B : TangentBundleStructure S} (X : SmoothField B)
    (D E : RealDerivation S) (hD : Represents X D) (hE : Represents X E) : D = E := by
  apply Derivation.ext
  intro f
  apply Subtype.ext
  funext p
  exact (hD p f (globalToGerm S p f) rfl).trans
    (hE p f (globalToGerm S p f) rfl).symm

/-- All coordinates extend globally on one common neighborhood. -/
theorem chart_global_extensions (e : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ⊆ e.source ∧
      ∃ g : Fin n → GlobalSmooth S,
        ∀ i, EqOn (g i).val (fun y => (e y).val i) U := by
  classical
  have hex (i : Fin n) : ∃ g : GlobalSmooth S,
      g.val =ᶠ[𝓝 p] (fun y => (e y).val i) := by
    have hr : ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val
        (fun y => (e y).val i) p := by
      exact scalarContDiffAt_of_chart S.smoothStructure.property.1 he hp
        ⟨univ, isOpen_univ, mem_univ _, (fun z => z i),
          (contDiff_apply ℝ (fun _ : Fin n => ℝ) i).contDiffOn,
          Eventually.of_forall (fun _ => rfl)⟩
    obtain ⟨g, hg, heq⟩ := exists_global_representative S p _ hr
    exact ⟨⟨g, (mem_globalSmoothAlgebra_iff S g).mpr hg⟩, heq⟩
  choose g hg using hex
  have hnear : ∀ᶠ y in 𝓝 p, y ∈ e.source ∧ ∀ i, (g i).val y = (e y).val i :=
    Filter.Eventually.and (e.open_source.mem_nhds hp) (Filter.eventually_all.mpr hg)
  obtain ⟨U, hU, hUo, hpU⟩ := eventually_nhds_iff.mp hnear
  exact ⟨U, hUo, hpU, (fun _ h => (hU _ h).1), g, fun i y hy => (hU y hy).2 i⟩

theorem coefficients_of_represents (B : TangentBundleStructure S)
    (X : SmoothField B) (D : RealDerivation S) (hXD : Represents X D)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ hUs : U ⊆ e.source,
      ∃ g : Fin n → GlobalSmooth S,
        (∀ i, EqOn (g i).val (fun y => (e y).val i) U) ∧
        ∀ (q : M) (hq : q ∈ U) (i : Fin n),
          B.fiberCoordinates.equiv e he q (hUs hq) (X.val q) i = (D (g i)).val q := by
  obtain ⟨U, hU, hpU, hUs, g, hg⟩ := chart_global_extensions S e he p hp
  refine ⟨U, hU, hpU, hUs, g, hg, ?_⟩
  intro q hq i
  obtain ⟨coords, hc, hv⟩ := B.fiberCoordinates.isCoordinates e he q (hUs hq)
  rw [hv]
  apply (hXD q (g i) (coords i) _).symm
  rw [hc]
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.mono (hU.mem_nhds hq) (fun y hy => hg i hy)
end Algebra

section Related
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  (S : SmoothManifold n a M) (T : SmoothManifold m b N)

/-- Actual smooth composition, needed to interpret the function identity. -/
def composeGlobal (f : M → N) (hf : IsSmoothMap S T f) (g : GlobalSmooth T) :
    GlobalSmooth S :=
  ⟨g.val ∘ f, (mem_globalSmoothAlgebra_iff S _).mpr (fun p =>
    scalar_comp_at (hf p) ((mem_globalSmoothAlgebra_iff T _).mp g.property (f p)))⟩

theorem related_functions_iff (B : TangentBundleStructure S) (C : TangentBundleStructure T)
    (f : M → N) (hf : IsSmoothMap S T f)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p))
    (X : SmoothField B) (Y : SmoothField C) (D : RealDerivation S) (E : RealDerivation T)
    (hX : Represents X D) (hY : Represents Y E) :
    (∀ p, L p (X.val p) = Y.val (f p)) ↔ FunctionsRelated f D E := by
  constructor
  · intro h u
    refine ⟨composeGlobal S T f hf u, rfl, ?_⟩
    funext p
    change (D (composeGlobal S T f hf u)).val p = (E u).val (f p)
    rw [hX p _ (globalToGerm S p (composeGlobal S T f hf u)) rfl,
      hY (f p) u (globalToGerm T (f p) u) rfl]
    exact ((hL p) (X.val p) (globalToGerm T (f p) u)
      (globalToGerm S p (composeGlobal S T f hf u)) u.val rfl rfl).symm.trans
        (congrArg (fun z : TangentSpace T (f p) => z.val (globalToGerm T (f p) u)) (h p))
  · intro h p
    apply tangent_ext_global T (f p)
    intro u
    obtain ⟨v, hv, hDv⟩ := h u
    calc
      (L p (X.val p)).val (globalToGerm T (f p) u) =
          (X.val p).val (globalToGerm S p v) :=
        (hL p) _ _ _ u.val rfl (by change Germ.ofFun (u.val ∘ f) = Germ.ofFun v.val; rw [hv])
      _ = (D v).val p := (hX p v _ rfl).symm
      _ = (E u).val (f p) := congrFun hDv p
      _ = (Y.val (f p)).val (globalToGerm T (f p) u) := hY (f p) u _ rfl
end Related

section Pushforward
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  (S : SmoothManifold n a M) (T : SmoothManifold m b N)

/-- Transport only the base equality; the tangent vector itself is unchanged. -/
def rebase (z : TotalSpace T) (q : N) (h : z.1 = q) : TangentSpace T q := h ▸ z.2

theorem rebase_sigma (z : TotalSpace T) (q : N) (h : z.1 = q) :
    (⟨q, rebase T z q h⟩ : TotalSpace T) = z := by
  cases h
  rfl

theorem field_ext {C : TangentBundleStructure T} (Y Z : SmoothField C)
    (h : ∀ q, (⟨q, Y.val q⟩ : TotalSpace T) = ⟨q, Z.val q⟩) : Y = Z := by
  have hv : Y.val = Z.val := by
    funext q
    exact eq_of_heq (Sigma.mk.inj (h q)).2
  cases Y
  cases Z
  cases hv
  rfl

theorem pushforward_exists
    (hmap : Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_totalMap_smoothType.{u})
    (B : TangentBundleStructure S) (C : TangentBundleStructure T)
    (h : Diffeomorph S.smoothStructure.val T.smoothStructure.val)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (h.toEquiv p))
    (hL : ∀ p, IsDifferential S T h.toEquiv p (L p)) (X : SmoothField B) :
    ∃! Y : SmoothField C, ∀ q : N,
      (⟨q, Y.val q⟩ : TotalSpace T) =
        totalMap S T h.toEquiv L ⟨h.toEquiv.symm q, X.val (h.toEquiv.symm q)⟩ := by
  letI := B.topology
  letI := C.topology
  let z : N → TotalSpace T := fun q =>
    totalMap S T h.toEquiv L ⟨h.toEquiv.symm q, X.val (h.toEquiv.symm q)⟩
  have hz (q : N) : (z q).1 = q := h.toEquiv.apply_symm_apply q
  let Yval : Section T := fun q => rebase T (z q) q (hz q)
  have hY (q : N) : (⟨q, Yval q⟩ : TotalSpace T) = z q := rebase_sigma T _ _ _
  have hXinv := manifoldContDiff_comp (⊤ : ℕ∞)
    T.smoothStructure.val S.smoothStructure.val B.manifold.smoothStructure.val
    S.smoothStructure.property.1.1 h.toEquiv.symm (fun p => ⟨p, X.val p⟩)
    h.contDiff_invFun X.smooth
  have hzSmooth := manifoldContDiff_comp (⊤ : ℕ∞)
    T.smoothStructure.val B.manifold.smoothStructure.val C.manifold.smoothStructure.val
    B.manifold.smoothStructure.property.1.1 _ (totalMap S T h.toEquiv L)
    hXinv (hmap S T B C h.toEquiv h.contDiff_toFun L hL)
  have hYs : IsSmoothMap T C.manifold (fun q => ⟨q, Yval q⟩) := by
    change ManifoldSmooth _ _ _
    convert hzSmooth using 1
    funext q
    exact hY q
  refine ⟨⟨Yval, hYs⟩, hY, ?_⟩
  intro Z hZ
  exact field_ext T Z ⟨Yval, hYs⟩ (fun q => (hZ q).trans (hY q).symm)

/-- Smoothness of the ordinary inclusion of an open submanifold. -/
theorem open_inclusion_smooth (U : Set M) (hU : IsOpen U) :
    ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      S.smoothStructure.val (Subtype.val : U → M) :=
  (manifoldContDiff_restrict_open (⊤ : ℕ∞) S.smoothStructure.val S.smoothStructure.val
    id U hU).mp (fun p _ => manifoldContDiff_id _ _ S.smoothStructure.property.1 p)

/-- Every inverse branch gives a field over its own target open set. -/
theorem local_pushforward_exists
    (hmap : Specs.SmoothManifolds.Tangent.Bundle.tangentBundle_totalMap_smoothType.{u})
    (B : TangentBundleStructure S) (C : TangentBundleStructure T)
    (f : M → N) (hf : IsLocalDiffeomorphism S T f)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p)) (X : SmoothField B) (p : M) :
    ∃ (U : Set M) (V : Set N) (hU : IsOpen U) (hV : IsOpen V),
      p ∈ U ∧ f p ∈ V ∧
      ∃ h : Diffeomorph (openSubsetAtlas S.smoothStructure.val U hU)
          (openSubsetAtlas T.smoothStructure.val V hV),
        (∀ x : U, (h.toEquiv x).val = f x.val) ∧
        ∃ Y : (q : V) → TangentSpace T q.val,
          (letI := C.topology
           ManifoldSmooth (openSubsetAtlas T.smoothStructure.val V hV)
             C.manifold.smoothStructure.val (fun q : V => ⟨q.val, Y q⟩)) ∧
          ∀ q : V, (⟨q.val, Y q⟩ : TotalSpace T) =
            totalMap S T f L ⟨(h.toEquiv.symm q).val, X.val (h.toEquiv.symm q).val⟩ := by
  obtain ⟨U, V, hU, hV, hpU, hfpV, h, hh⟩ := hf.2 p
  refine ⟨U, V, hU, hV, hpU, hfpV, h, hh, ?_⟩
  letI := B.topology
  letI := C.topology
  let z : V → TotalSpace T := fun q =>
    totalMap S T f L ⟨(h.toEquiv.symm q).val, X.val (h.toEquiv.symm q).val⟩
  have hz (q : V) : (z q).1 = q.val := by
    change f (h.toEquiv.symm q).val = q.val
    rw [← hh (h.toEquiv.symm q), h.toEquiv.apply_symm_apply]
  let Y : (q : V) → TangentSpace T q.val := fun q => rebase T (z q) q.val (hz q)
  have hY (q : V) : (⟨q.val, Y q⟩ : TotalSpace T) = z q := rebase_sigma T _ _ _
  have hInv := manifoldContDiff_comp (⊤ : ℕ∞)
    (openSubsetAtlas T.smoothStructure.val V hV)
    (openSubsetAtlas S.smoothStructure.val U hU) S.smoothStructure.val
    (by
      intro x
      obtain ⟨e, he, hx⟩ := S.smoothStructure.property.1.1 x.val
      exact ⟨e.subtypeRestr (s := ⟨U, hU⟩) ⟨x⟩, ⟨⟨x⟩, e, he, rfl⟩, by
        simpa only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hx⟩)
    h.toEquiv.symm Subtype.val h.contDiff_invFun (open_inclusion_smooth S U hU)
  have hXinv := manifoldContDiff_comp (⊤ : ℕ∞)
    (openSubsetAtlas T.smoothStructure.val V hV)
    S.smoothStructure.val B.manifold.smoothStructure.val
    S.smoothStructure.property.1.1 _ (fun p => ⟨p, X.val p⟩) hInv X.smooth
  have hzSmooth := manifoldContDiff_comp (⊤ : ℕ∞)
    (openSubsetAtlas T.smoothStructure.val V hV)
    B.manifold.smoothStructure.val C.manifold.smoothStructure.val
    B.manifold.smoothStructure.property.1.1 _ (totalMap S T f L)
    hXinv (hmap S T B C f hf.1 L hL)
  refine ⟨Y, ?_, hY⟩
  convert hzSmooth using 1
  funext q
  exact hY q
end Pushforward

section SectionSmoothness
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M) (B : TangentBundleStructure S)

/-- The specified tangent charts belong to the maximal tangent atlas. -/
theorem bundleChart_mem (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) :
    letI := B.topology
    B.chart e he ∈ B.manifold.smoothStructure.val := by
  letI := B.topology
  let A := B.manifold.smoothStructure.val
  have hA := B.manifold.smoothStructure.property.1
  have hmax : maximalExtension (⊤ : ℕ∞) A = A :=
    B.manifold.smoothStructure.property.2 _ (maximalExtension_isContDiffAtlas hA)
      (subset_maximalExtension hA)
  change B.chart e he ∈ A
  rw [← hmax]
  intro d hd
  have hd' : d ∈ maximalExtension (⊤ : ℕ∞) {t | ∃ e he, t = B.chart e he} := by
    change d ∈ AtlasData.maximalExtension (⊤ : ℕ∞) {t | ∃ e he, t = B.chart e he}
    rw [← B.maximalAtlas]
    exact hd
  exact contDiffCompatible_symm (hd' (B.chart e he) ⟨e, he, rfl⟩)

/-- A local smooth coordinate representative is sufficient for a section to be
smooth at a point, in the actual bundle topology. -/
theorem section_smoothAt_of_coordinates (X : Section S)
    (p : M) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (hp : p ∈ e.source) (V : Set M) (hV : IsOpen V) (hpV : p ∈ V)
    (hVs : V ⊆ e.source) (w : M → Euclidean n)
    (hw : ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val w p)
    (heq : ∀ q (hq : q ∈ V), w q = B.fiberCoordinates.equiv e he q (hVs hq) (X q)) :
    letI := B.topology
    ManifoldSmoothAt S.smoothStructure.val B.manifold.smoothStructure.val
      (fun q => ⟨q, X q⟩) p := by
  letI := B.topology
  let t := B.chart e he
  let F : M → TotalSpace S := fun q => ⟨q, X q⟩
  have htp : F p ∈ t.source := by
    rw [B.chart_source]
    exact hp
  have htnear : F ⁻¹' t.source ∈ 𝓝 p := by
    apply Filter.mem_of_superset (e.open_source.mem_nhds hp)
    intro q hq
    change (⟨q, X q⟩ : TotalSpace S) ∈ (B.chart e he).source
    rw [B.chart_source]
    exact hq
  have hval : (fun q => (t (F q)).val) =ᶠ[𝓝 p]
      (fun q => B.productCoordinates.linearEquiv ((e q).val, w q)) := by
    filter_upwards [hV.mem_nhds hpV] with q hq
    rw [B.chart_apply e he (F q) (hVs hq), heq q hq]
  have hc : ContinuousAt (fun q => (t (F q)).val) p :=
    ((B.productCoordinates.linearEquiv.continuous).continuousAt.comp
      ((continuous_subtype_val.continuousAt.comp (e.continuousAt hp)).prodMk hw.1)).congr hval.symm
  have hcont : ContinuousAt F p :=
    (t.continuousAt_iff_continuousAt_comp_left htnear).mpr
      (Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hc)
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    S.smoothStructure.property.1 B.manifold.smoothStructure.property.1 F p).mpr
  refine ⟨hcont, e, he, t, bundleChart_mem S B e he, hp, htp, ?_⟩
  obtain ⟨U, hU, hepU, W, hW, hWw⟩ := hw.2 e he hp
  refine ⟨U, hU, hepU, (fun z => B.productCoordinates.linearEquiv (z, W z)),
    ?_, ?_⟩
  · exact B.productCoordinates.linearEquiv.contDiff.contDiffOn.comp
      (contDiffOn_id.prodMk hW) (mapsTo_univ _ _)
  · filter_upwards [hWw, hval] with q hq htq
    rw [htq, hq]
end SectionSmoothness

section Correspondence
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M) (B : TangentBundleStructure S)

/-- Finite scalar component tests give exactly the ambient vector test. -/
theorem vectorSmoothAt_of_components {k : ℕ} (w : M → Euclidean k) (p : M)
    (hw : ∀ i, ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val (fun q => w q i) p) :
    ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val w p := by
  classical
  have hwi i := (scalarContDiffAt_iff _ _ _ _).mp (hw i)
  refine ⟨continuousAt_pi.mpr (fun i => (hwi i).1), ?_⟩
  intro e he hp
  choose U hU hpU F hF heq using (fun i => (hwi i).2 e he hp)
  refine ⟨⋂ i, U i, isOpen_iInter_of_finite hU, mem_iInter.mpr hpU,
    (fun z i => F i z), contDiffOn_pi.mpr (fun i => (hF i).mono (iInter_subset U i)), ?_⟩
  exact (Filter.eventually_all.mpr heq).mono (fun q hq => funext hq)

/-- The reconstructed section has smooth coordinate functions D applied to
cutoff extensions, so it is smooth in the specified tangent atlas. -/
theorem sectionOfDerivation_smooth (D : RealDerivation S) :
    letI := B.topology
    IsSmoothMap S B.manifold (fun p => ⟨p, sectionOfDerivation S D p⟩) := by
  letI := B.topology
  intro p
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨U, hU, hpU, hUs, g, hg⟩ := chart_global_extensions S e he p hp
  let w : M → Euclidean n := fun q i => (D (g i)).val q
  apply section_smoothAt_of_coordinates S B (sectionOfDerivation S D) p e he hp
    U hU hpU hUs w
  · exact vectorSmoothAt_of_components S w p (fun i =>
      (mem_globalSmoothAlgebra_iff S _).mp (D (g i)).property p)
  · intro q hq
    obtain ⟨coords, hc, hv⟩ := B.fiberCoordinates.isCoordinates e he q (hUs hq)
    funext i
    rw [hv]
    exact (sectionOfDerivation_apply S D q (g i) (coords i) (by
      rw [hc]
      exact Germ.coe_eq.mpr (Filter.Eventually.mono (hU.mem_nhds hq) (fun y hy => hg i hy)))).symm

noncomputable def fieldOfDerivation (D : RealDerivation S) : SmoothField B :=
  ⟨sectionOfDerivation S D, sectionOfDerivation_smooth S B D⟩

theorem fieldOfDerivation_represents (D : RealDerivation S) :
    Represents (fieldOfDerivation S B D) D := by
  intro p f g hfg
  exact (sectionOfDerivation_apply S D p f g hfg).symm

/-- In one base chart, a smooth field has one ambient smooth representative for
its fiber coordinates. The proof uses the actual tangent chart map. -/
theorem field_local_coordinates (X : SmoothField B) (p : M)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) :
    ∃ (U : Set (Euclidean n)), IsOpen U ∧ (e p).val ∈ U ∧
      ∃ W : Euclidean n → Euclidean n, ContDiffOn ℝ (⊤ : ℕ∞) W U ∧
        ∀ᶠ q in 𝓝 p, ∃ hq : q ∈ e.source,
          W (e q).val = B.fiberCoordinates.equiv e he q hq (X.val q) := by
  letI := B.topology
  have htp : (⟨p, X.val p⟩ : TotalSpace S) ∈ (B.chart e he).source := by
    rw [B.chart_source]
    exact hp
  obtain ⟨U, hU, hpU, F, hF, heq⟩ :=
    (X.smooth p).2 e he (B.chart e he) (bundleChart_mem S B e he) hp htp
  let W : Euclidean n → Euclidean n := fun z => (B.productCoordinates.linearEquiv.symm (F z)).2
  refine ⟨U, hU, hpU, W, ?_, ?_⟩
  · exact contDiff_snd.contDiffOn.comp
      (B.productCoordinates.linearEquiv.symm.contDiff.contDiffOn.comp hF (mapsTo_univ _ _))
      (mapsTo_univ _ _)
  · filter_upwards [heq, e.open_source.mem_nhds hp] with q hq hqs
    refine ⟨hqs, ?_⟩
    change (B.productCoordinates.linearEquiv.symm (F (e q).val)).2 = _
    rw [hq, B.chart_apply e he _ hqs, B.productCoordinates.linearEquiv.symm_apply_apply]
end Correspondence

section FieldAction
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n a M) (B : TangentBundleStructure S)

/-- The derivation action in any intrinsic coordinates is evaluation of the
ambient differential on the coordinate vector. -/
theorem tangent_action_coordinates (K : FiberCoordinates S)
    (p : M) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (v : TangentSpace S p) (g : SmoothGerm S p) (F : Euclidean n → ℝ)
    (hF : GermChartExtension S p e g F) :
    v.val g = fderiv ℝ F (e p).val (K.equiv e he p hp v) := by
  classical
  obtain ⟨coords, hc, hv⟩ := K.isCoordinates e he p hp
  have hcoords (i : Fin n) : coordinateGerm S p e he hp i = coords i :=
    Subtype.ext (hc i).symm
  rw [derivation_coordinate_formula S p e he hp v g F hF]
  simp_rw [hcoords, ← hv]
  have hexp : K.equiv e he p hp v =
      ∑ i : Fin n, (K.equiv e he p hp v) i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hexp, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- Applying a smooth section to a global smooth function gives a global smooth
function. Local extensions provide smooth derivatives also at the boundary. -/
theorem field_action_smooth (X : SmoothField B) (f : GlobalSmooth S) :
    ScalarSmooth S.smoothStructure.val
      (fun p => (X.val p).val (globalToGerm S p f)) := by
  intro p
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨U, hU, hpU, F, hF, hFf⟩ :=
    ((scalarContDiffAt_iff _ _ _ _).mp
      ((mem_globalSmoothAlgebra_iff S _).mp f.property p)).2 e he hp
  obtain ⟨V, hV, hpV, W, hW, hWv⟩ := field_local_coordinates S B X p e he hp
  have hDer : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hU (by simp)
  apply scalarContDiffAt_of_chart S.smoothStructure.property.1 he hp
  refine ⟨U ∩ V, hU.inter hV, ⟨hpU, hpV⟩,
    (fun z => fderiv ℝ F z (W z)),
    (hDer.mono inter_subset_left).clm_apply (hW.mono inter_subset_right), ?_⟩
  have hFnear : ∀ᶠ q in 𝓝 p,
      (e q).val ∈ U ∧ (fun y => F (e y).val) =ᶠ[𝓝 q] f.val := by
    have hcp : ContinuousAt (fun q => (e q).val) p :=
      continuous_subtype_val.continuousAt.comp (e.continuousAt hp)
    exact Filter.Eventually.and (hcp.preimage_mem_nhds (hU.mem_nhds hpU)) hFf.eventually_nhds
  filter_upwards [hWv, hFnear] with q hq hFq
  obtain ⟨hqs, hWq⟩ := hq
  rw [hWq]
  apply (tangent_action_coordinates S B.fiberCoordinates q e he hqs (X.val q)
    (globalToGerm S q f) F ⟨⟨U, hU, hFq.1, hF⟩, Germ.coe_eq.mpr hFq.2⟩).symm

/-- The derivation associated to a field has values in the original algebra
C∞(M), rather than in the algebra of all set-theoretic functions. -/
def derivationOfField (X : SmoothField B) : RealDerivation S where
  toFun f := ⟨(fun p => (X.val p).val (globalToGerm S p f)),
    (mem_globalSmoothAlgebra_iff S _).mpr (field_action_smooth S B X f)⟩
  map_add' f g := by
    apply Subtype.ext
    funext p
    change (X.val p).val (globalToGerm S p (f + g)) = _
    rw [map_add, map_add]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext p
    change (X.val p).val (globalToGerm S p (c • f)) = _
    rw [map_smul, map_smul]
    rfl
  map_one_eq_zero' := by
    apply Subtype.ext
    funext p
    change (X.val p).val (globalToGerm S p 1) = 0
    rw [map_one]
    exact derivation_kills_constants (germEvaluation S p) (X.val p) 1
  leibniz' f g := by
    apply Subtype.ext
    funext p
    change (X.val p).val (globalToGerm S p (f * g)) =
      f.val p * (X.val p).val (globalToGerm S p g) +
        g.val p * (X.val p).val (globalToGerm S p f)
    rw [map_mul, (X.val p).property]
    rfl

theorem derivationOfField_represents (X : SmoothField B) :
    Represents X (derivationOfField S B X) := by
  intro p f g hfg
  change (X.val p).val (globalToGerm S p f) = _
  exact congrArg (X.val p).val (Subtype.ext hfg)

/-- The two constructions give the full original bijection. -/
noncomputable def fieldDerivationEquiv : SmoothField B ≃ RealDerivation S where
  toFun := derivationOfField S B
  invFun := fieldOfDerivation S B
  left_inv X := represents_unique S _ X (derivationOfField S B X)
    (fieldOfDerivation_represents S B _) (derivationOfField_represents S B X)
  right_inv D := representing_derivation_unique S (fieldOfDerivation S B D) _ D
    (derivationOfField_represents S B _) (fieldOfDerivation_represents S B D)
end FieldAction

/-- Smooth fields and algebraic derivations correspond by their action on germs. -/
theorem correspondence :
    Specs.SmoothManifolds.Ch06.VectorFieldDerivations.correspondenceType.{u} := by
  intro n a M _ S B
  exact ⟨fieldDerivationEquiv S B, derivationOfField_represents S B⟩

theorem locality :
    Specs.SmoothManifolds.Ch06.VectorFieldDerivations.localityType.{u} := by
  intro n a M _ S D p f g hfg
  exact derivation_locality S D p f g hfg

theorem local_action :
    Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_actionType.{u} := by
  intro n a M _ S D p r hr
  exact derivation_local_action S D p r hr

theorem chart_coefficients :
    Specs.SmoothManifolds.Ch06.VectorFieldDerivations.chart_coefficientsType.{u} := by
  intro n a M _ S B X D hXD e he p hp
  exact coefficients_of_represents S B X D hXD e he p hp

theorem related_iff :
    Specs.SmoothManifolds.Ch06.VectorFieldDerivations.related_iffType.{u} := by
  intro n m a b M N _ _ S T B C f hf L hL X Y D E hX hY
  exact related_functions_iff S T B C f hf L hL X Y D E hX hY

theorem pushforward :
    Specs.SmoothManifolds.Ch06.VectorFieldDerivations.pushforwardType.{u} := by
  intro n m a b M N _ _ S T B C h L hL X
  exact pushforward_exists S T TangentBundle.map_smooth B C h L hL X

theorem local_pushforward :
    Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_pushforwardType.{u} := by
  intro n m a b M N _ _ S T B C f hf L hL X p
  exact local_pushforward_exists S T TangentBundle.map_smooth B C f hf L hL X p

end SmoothManifolds.VectorFields
