import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.InteriorInverse
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.MapClasses
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace SmoothManifolds.InteriorInverse
open ModelData AtlasData MapData BoundaryData FiniteRegularityData Set Filter
open scoped Topology ContDiff
universe u v

/-- Inclusion of the interior of a model, with an arbitrary total inverse
outside the model. Only the open interior is used as source and target. -/
noncomputable def modelInteriorChart (n : ℕ) (a : ModelKind) :
    OpenPartialHomeomorph (ModelSpace n a) (Euclidean n) := by
  classical
  let z : ModelSpace n a := ⟨0, by cases a <;> cases n <;> simp [ModelData.modelSet, ModelData.halfSpaceSet]⟩
  let g : Euclidean n → ModelSpace n a := fun x =>
    if h : x ∈ modelSet n a then ⟨x, h⟩ else z
  have hg (x : Euclidean n) (hx : x ∈ interior (modelSet n a)) :
      (g x).val = x := by simp [g, interior_subset hx]
  exact {
    toFun := Subtype.val
    invFun := g
    source := Subtype.val ⁻¹' interior (modelSet n a)
    target := interior (modelSet n a)
    map_source' := fun _ hx => hx
    map_target' := fun x hx => by change (g x).val ∈ interior (modelSet n a); rwa [hg x hx]
    left_inv' := fun x hx => Subtype.ext (hg x.val hx)
    right_inv' := hg
    open_source := isOpen_interior.preimage continuous_subtype_val
    open_target := isOpen_interior
    continuousOn_toFun := continuous_subtype_val.continuousOn
    continuousOn_invFun := Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      (continuousOn_id.congr hg) }

/-- A model chart restricted to its ambient interior is an ordinary Euclidean
open chart. This includes dimension zero for both permitted models. -/
noncomputable def ambientChart {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (e : ModelChart n a M) :
    OpenPartialHomeomorph M (Euclidean n) := e.trans (modelInteriorChart n a)

@[simp] theorem ambientChart_apply {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (e : ModelChart n a M) (x : M) :
    ambientChart e x = (e x).val := rfl

@[simp] theorem ambientChart_source {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (e : ModelChart n a M) :
    (ambientChart e).source = e.source ∩ (fun x => (e x).val) ⁻¹' interior (modelSet n a) := rfl

/-- A Euclidean C^r map with bijective derivative has a local inverse which
is C^r throughout its open target. Restricting to the open set where the
Jacobian is invertible handles smooth regularity without assuming that
smoothness at a single point holds on one fixed neighborhood. -/
theorem euclidean_inverse {m n : ℕ} (r : ℕ∞) (hr : 1 ≤ r)
    (f : Euclidean m → Euclidean n) (U : Set (Euclidean m)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ r f U) (x : Euclidean m) (hx : x ∈ U)
    (L : Euclidean m →L[ℝ] Euclidean n) (hL : HasFDerivAt f L x)
    (hbij : Function.Bijective L) :
    ∃ j : OpenPartialHomeomorph (Euclidean m) (Euclidean n),
      x ∈ j.source ∧ (j : Euclidean m → Euclidean n) = f ∧
      ContDiffOn ℝ r j.symm j.target := by
  let E : Euclidean m ≃L[ℝ] Euclidean n :=
    (LinearEquiv.ofBijective L.toLinearMap hbij).toContinuousLinearEquiv
  have hE : (E : Euclidean m →L[ℝ] Euclidean n) = L := by ext y i; rfl
  have hr0 : (r : ℕ∞ω) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ∞) < 1) hr))
  have hfx := hf.contDiffAt (hU.mem_nhds hx)
  have hd : HasFDerivAt f (E : Euclidean m →L[ℝ] Euclidean n) x := hE ▸ hL
  let j₀ := hfx.toOpenPartialHomeomorph f hd hr0
  let W := U ∩ (fderiv ℝ f) ⁻¹' range
    (fun e : Euclidean m ≃L[ℝ] Euclidean n => (e : Euclidean m →L[ℝ] Euclidean n))
  have hW : IsOpen W :=
    (hf.continuousOn_fderiv_of_isOpen hU (by exact_mod_cast hr)).isOpen_inter_preimage
      hU ContinuousLinearEquiv.isOpen
  have hxW : x ∈ W := ⟨hx, E, by simpa only [hE] using hL.fderiv.symm⟩
  let j := j₀.restrOpen W hW
  refine ⟨j, ⟨hfx.mem_toOpenPartialHomeomorph_source hd hr0, hxW⟩, rfl, ?_⟩
  intro y hy
  have hsy := j.map_target hy
  obtain ⟨D, hD⟩ := hsy.2.2
  have hdf : HasFDerivAt f (D : Euclidean m →L[ℝ] Euclidean n) (j.symm y) := by
    change (D : Euclidean m →L[ℝ] Euclidean n) = _ at hD
    rw [hD]
    exact ((hf.contDiffAt (hU.mem_nhds hsy.2.1)).differentiableAt hr0).hasFDerivAt
  exact (j.contDiffAt_symm hy hdf
    (hf.contDiffAt (hU.mem_nhds hsy.2.1))).contDiffWithinAt

/-- Smooth chart transitions have every finite order and smooth order. -/
theorem smoothAtlas_contDiff {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (r : ℕ∞) :
    IsContDiffAtlas r S.smoothStructure.val := by
  refine ⟨S.smoothStructure.property.1.1, ?_⟩
  intro e he d hd
  have lower : ∀ (g : ModelSpace n a → ModelSpace n a) (s : Set (ModelSpace n a)),
      ContDiffOnModel (⊤ : ℕ∞) g s → ContDiffOnModel r g s := by
    intro g s hg x hx
    obtain ⟨U, hU, hxU, F, hF, heF⟩ := hg x hx
    exact ⟨U, hU, hxU, F, hF.of_le (by exact_mod_cast (le_top : r ≤ (⊤ : ℕ∞))), heF⟩
  have h := S.smoothStructure.property.1.2 e he d hd
  exact ⟨lower _ _ h.1, lower _ _ h.2⟩

/-- The inverse function theorem in interior charts, for all positive finite
regularities and for smooth maps, on manifolds allowed to have boundary. -/
theorem interior_inverse :
    Specs.SmoothManifolds.Ch03.InteriorInverse.interior_inverseType.{u,v} := by
  intro m n a b M N _ _ r hr S T f hf p hpi hfpi F G
  letI := F.group; letI := F.module; letI := G.group; letI := G.module
  intro L hL hbij
  obtain ⟨e, he, hp, hpei⟩ := hpi
  obtain ⟨d, hd, hfp, hfpei⟩ := hfpi
  let E := ambientChart e
  let D := ambientChart d
  have hpE : p ∈ E.source := ⟨hp, hpei⟩
  have hfpD : f p ∈ D.source := ⟨hfp, hfpei⟩
  obtain ⟨U, hU, hepU, g, hg, heq⟩ := (hf p).2 e he d hd hp hfp
  have hr0 : (r : ℕ∞ω) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ∞) < 1) hr))
  have hdg := ((hg.contDiffAt (hU.mem_nhds hepU)).differentiableAt hr0).hasFDerivAt
  have hderiv : chartDerivative e d f p = fderiv ℝ g (e p).val :=
    FiniteRegularity.coordinateDerivative_eq e _ p hp _ ⟨g, hdg, heq⟩
  have hlin := MapClasses.differential_chart_invariants S T f p F G
    e d he hd hp hfp L hL
  have hgBij : Function.Bijective (fderiv ℝ g (e p).val) := by
    rw [← hderiv]
    exact ⟨hlin.2.1.mp hbij.1, hlin.2.2.mp hbij.2⟩
  obtain ⟨j, hpj, hj, hji⟩ := euclidean_inverse r hr g U hU hg (e p).val hepU
    (fderiv ℝ g (e p).val) hdg hgBij
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp
    (heq.and ((hf p).1.preimage_mem_nhds (D.open_source.mem_nhds hfpD)))
  let h₀ := (E.trans j).trans D.symm
  let h := h₀.restrOpen V hV
  have hjp : j (E p) = D (f p) := by
    change j (e p).val = (d (f p)).val
    rw [hj]
    exact heq.eq_of_nhds
  have hph₀ : p ∈ h₀.source := by
    refine ⟨⟨hpE, hpj⟩, ?_⟩
    change j (E p) ∈ D.target
    rw [hjp]
    exact D.map_source hfpD
  have hsource (x : M) (hx : x ∈ h.source) : x ∈ manifoldInterior S :=
    ⟨e, he, hx.1.1.1.1, hx.1.1.1.2⟩
  have htarget (y : N) (hy : y ∈ h.target) : y ∈ manifoldInterior T :=
    ⟨d, hd, hy.1.1.1, hy.1.1.2⟩
  have hforward : EqOn h f h.source := by
    intro x hx
    have hxV := hVsub hx.2
    change D.symm (j (E x)) = f x
    have hgx : j (E x) = D (f x) := by
      change j (e x).val = (d (f x)).val
      rw [hj]
      exact hxV.1
    rw [hgx, D.left_inv hxV.2]
  have hinv_coords (y : N) (hy : y ∈ h.target) :
      (e (h.symm y)).val = j.symm (d y).val := by
    have hyE : j.symm (D y) ∈ E.target := hy.1.2.2
    change E (E.symm (j.symm (D y))) = j.symm (D y)
    exact E.right_inv hyE
  refine ⟨h, ⟨hph₀, hpV⟩, hsource, htarget, hforward,
    (fun x _ => hf x), ?_⟩
  intro y hy
  apply (manifoldContDiffAt_iff_oneChart r _ _
    (smoothAtlas_contDiff T r) (smoothAtlas_contDiff S r) h.symm y).mpr
  have hsy := h.map_target hy
  refine ⟨h.symm.continuousAt hy, d, hd, e, he, hy.1.1.1, hsy.1.1.1.1, ?_⟩
  refine ⟨j.target, j.open_target, hy.1.2.1, j.symm, hji, ?_⟩
  filter_upwards [h.open_target.mem_nhds hy] with z hz
  exact (hinv_coords z hz).symm

end SmoothManifolds.InteriorInverse
