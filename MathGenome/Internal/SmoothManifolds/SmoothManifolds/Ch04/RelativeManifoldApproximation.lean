import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.RelativeManifoldApproximation
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.EuclideanTubular
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.ProperWhitney
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.RelativeEuclideanApproximation
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.EmbeddedComparison
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.FiniteProperEmbedding
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Tactic.Linarith

namespace SmoothManifolds.RelativeManifoldApproximation
open ModelData AtlasData Set Filter
open RelativeManifoldApproximationData
open scoped Topology
universe u v w

/-- A graph neighborhood has a positive continuous fiber radius. This uses
paracompactness of the source, not compactness or a chosen metric on it. -/
theorem exists_graph_tolerance {X : Type u} [TopologicalSpace X]
    [NormalSpace X] [ParacompactSpace X]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : X → E) (hf : Continuous f) (Q : Set (X × E))
    (hQ : IsOpen Q) (hgraph : ∀ x, (x, f x) ∈ Q) :
    ∃ ε : X → ℝ, Continuous ε ∧ (∀ x, 0 < ε x) ∧
      ∀ x y, ‖y - f x‖ < ε x → (x, y) ∈ Q := by
  let R : X → Set ℝ := fun x =>
    {r | 0 < r ∧ ∀ y, ‖y - f x‖ < r → (x, y) ∈ Q}
  have hconv (x : X) : Convex ℝ (R x) := by
    apply OrdConnected.convex
    constructor
    intro r hr s hs t ht
    exact ⟨lt_of_lt_of_le hr.1 ht.1, fun y hy => hs.2 y (lt_of_lt_of_le hy ht.2)⟩
  have hlocal (x : X) : ∃ r : ℝ, ∀ᶠ z in 𝓝 x, r ∈ R z := by
    obtain ⟨U, V, hU, hV, hxU, hxV, hUV⟩ :=
      isOpen_prod_iff.mp hQ x (f x) (hgraph x)
    obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV (f x) hxV
    refine ⟨r / 2, ?_⟩
    filter_upwards [hU.mem_nhds hxU,
      hf.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (f x) (half_pos hr))]
      with z hzU hz
    refine ⟨half_pos hr, ?_⟩
    intro y hy
    apply hUV
    refine ⟨hzU, hrV ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have hz' : ‖f z - f x‖ < r / 2 := by
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using hz
    calc
      ‖y - f x‖ ≤ ‖y - f z‖ + ‖f z - f x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < r := by linarith
  obtain ⟨ε, hε⟩ := exists_continuous_forall_mem_convex_of_local_const hconv hlocal
  exact ⟨ε, ε.continuous, fun x => (hε x).1, fun x => (hε x).2⟩

/-- Compose a manifold-valued smooth germ with a Euclidean-valued one. -/
theorem smoothEuclideanAt_comp {n m q : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    {f : M → N} {g : N → Euclidean q} {x : M}
    (hf : ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val f x)
    (hg : ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) T.smoothStructure.val g (f x)) :
    ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val (g ∘ f) x := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  intro e he hxe
  obtain ⟨d, hd, hfd⟩ := T.smoothStructure.property.1.1 (f x)
  exact LocalCoordinateExtension.comp
    (LocalCoordinateExtension.precomp (hg.2 d hd hfd) hf.1 rfl)
    (hf.2 e he d hd hxe hfd)

/-- Smooth local extensions on the closed subset remain smooth after an
arbitrary smooth Euclidean-valued map of the target. -/
theorem locallySmooth_comp_euclidean {n m q : ℕ} {a : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m .euclidean N)
    (A : Set M) (F : M → N) (j : N → Euclidean q)
    (hj : ∀ y, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) T.smoothStructure.val j y)
    (hF : LocallySmoothOnSubsetToManifold S.smoothStructure.val T.smoothStructure.val
      A (fun x => F x.val)) :
    LocallySmoothOnSubset S.smoothStructure.val A (fun x => j (F x.val)) := by
  intro x
  obtain ⟨U, hU, hxU, f, hf, heq⟩ := hF x
  exact ⟨U, hU, hxU, j ∘ f,
    fun y hy => smoothEuclideanAt_comp S T (hf y hy) (hj (f y)),
    fun y hy => congrArg j (heq y hy)⟩

/-- The Euclidean `L²` norm dominates the shared coordinate-space sup norm,
including in dimension zero. -/
theorem norm_le_euclideanNorm {q : ℕ} (v : Euclidean q) :
    ‖v‖ ≤ ‖WithLp.toLp 2 v‖ := by
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    (fun i => PiLp.norm_apply_le (WithLp.toLp 2 v) i)

/-- Every point of the straight homotopy lies within the endpoint error. -/
theorem straight_error_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E) (t : Time) :
    ‖((1 - t.val) • f + t.val • g) - f‖ ≤ ‖g - f‖ := by
  have heq : ((1 - t.val) • f + t.val • g) - f = t.val • (g - f) := by
    rw [sub_smul, one_smul, smul_sub]
    abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
  exact mul_le_of_le_one_left (norm_nonneg _) t.property.2

/-- Given a continuous neighborhood retraction, sufficiently close Euclidean
endpoints yield a continuous relative homotopy in any graph neighborhood.
The approximation theorem will subsequently supply the smooth endpoint. -/
theorem retracted_straight_homotopy {n m q : ℕ} {a : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (_T : SmoothManifold m .euclidean N)
    (j : N → Euclidean q) (hj : Continuous j)
    (W : Set (Euclidean q)) (hW : IsOpen W) (hjW : ∀ y, j y ∈ W)
    (r : W → N) (hr : Continuous r) (hrj : ∀ y, r ⟨j y, hjW y⟩ = y)
    (A : Set M) (F : M → N) (hF : Continuous F)
    (O : Set (M × N)) (hO : IsOpen O) (hgraph : ∀ x, (x, F x) ∈ O) :
    ∃ ε : M → ℝ, Continuous ε ∧ (∀ x, 0 < ε x) ∧
      ∀ (g : M → Euclidean q), Continuous g → EqOn g (j ∘ F) A →
        (∀ x, ‖WithLp.toLp 2 (g x - j (F x))‖ < ε x) →
        ∃ (L : Time × M → W) (H : Time × M → N),
          Continuous L ∧ Continuous H ∧ H = r ∘ L ∧
          (∀ z, (L z).val = (1 - z.1.val) • j (F z.2) + z.1.val • g z.2) ∧
          (∀ x, H (⟨0, by simp⟩, x) = F x) ∧
          (∀ x, H (⟨1, by simp⟩, x) = r (L (⟨1, by simp⟩, x))) ∧
          (∀ t x, x ∈ A → H (t, x) = F x) ∧
          ∀ t x, (x, H (t, x)) ∈ O := by
  let := S.topologicalManifold.hausdorff
  let := _root_.SmoothManifolds.TopologicalManifold.regularSpace S.topologicalManifold
  let := _root_.SmoothManifolds.TopologicalManifold.paracompactSpace S.topologicalManifold
  let : NormalSpace M := inferInstance
  let P : Set (M × W) := (fun z : M × W => (z.1, r z.2)) ⁻¹' O
  let Q : Set (M × Euclidean q) := (Prod.map id Subtype.val) '' P
  have hP : IsOpen P := hO.preimage (continuous_fst.prodMk (hr.comp continuous_snd))
  have hQ : IsOpen Q := (IsOpenMap.prodMap IsOpenMap.id hW.isOpenEmbedding_subtypeVal.isOpenMap) P hP
  have hQgraph (x : M) : (x, j (F x)) ∈ Q := by
    refine ⟨(x, ⟨j (F x), hjW (F x)⟩), ?_, rfl⟩
    change (x, r ⟨j (F x), hjW (F x)⟩) ∈ O
    rw [hrj]
    exact hgraph x
  obtain ⟨ε, hε, hεpos, hεQ⟩ := exists_graph_tolerance (j ∘ F) (hj.comp hF) Q hQ hQgraph
  refine ⟨ε, hε, hεpos, ?_⟩
  intro g hg heq herr
  let l : Time × M → Euclidean q :=
    fun z => (1 - z.1.val) • j (F z.2) + z.1.val • g z.2
  have hl : Continuous l :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      ((hj.comp hF).comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul (hg.comp continuous_snd))
  have hlQ (z : Time × M) : (z.2, l z) ∈ Q := by
    apply hεQ
    exact lt_of_le_of_lt (straight_error_le (j (F z.2)) (g z.2) z.1)
      (lt_of_le_of_lt (norm_le_euclideanNorm _) (herr z.2))
  have hlW (z : Time × M) : l z ∈ W := by
    obtain ⟨w, _, hw⟩ := hlQ z
    have hh := congrArg Prod.snd hw
    change w.2.val = l z at hh
    rw [← hh]
    exact w.2.property
  let L : Time × M → W := fun z => ⟨l z, hlW z⟩
  let H : Time × M → N := r ∘ L
  have hL : Continuous L := hl.subtype_mk _
  have hzero (x : M) : L (⟨0, by simp⟩, x) = ⟨j (F x), hjW (F x)⟩ := by
    apply Subtype.ext
    simp [L, l]
  refine ⟨L, H, hL, hr.comp hL, rfl, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro x
    change r (L _) = F x
    rw [hzero, hrj]
  · intro x
    rfl
  · intro t x hx
    have hh : L (t, x) = ⟨j (F x), hjW (F x)⟩ := by
      apply Subtype.ext
      change (1 - t.val) • j (F x) + t.val • g x = j (F x)
      rw [heq hx]
      simp only [Function.comp_apply, ← add_smul, sub_add_cancel, one_smul]
    change r (L _) = F x
    rw [hh, hrj]
  · intro t x
    obtain ⟨w, hw, he⟩ := hlQ (t, x)
    have hx : w.1 = x := congrArg Prod.fst he
    have hy : w.2 = L (t, x) := Subtype.ext (congrArg Prod.snd he)
    change (w.1, r w.2) ∈ O at hw
    simpa only [hx, hy, H, Function.comp_apply] using hw

/-- The straight interpolation of two locally smooth Euclidean maps has
an ambient extension jointly in time and source coordinates. -/
theorem straight_localCoordinateExtension {n q : ℕ} {X : Type u} [TopologicalSpace X]
    {ι : X → Euclidean n} {f g : X → Euclidean q} {x : X}
    (hf : LocalCoordinateExtension (⊤ : ℕ∞) ι f x)
    (hg : LocalCoordinateExtension (⊤ : ℕ∞) ι g x) (t : Time) :
    LocalCoordinateExtension (⊤ : ℕ∞)
      (fun z : Time × X => Fin.cons z.1.val (ι z.2))
      (fun z => (1 - z.1.val) • f z.2 + z.1.val • g z.2) (t, x) := by
  obtain ⟨U, hU, hxU, f', hf', hef⟩ := hf
  obtain ⟨V, hV, hxV, g', hg', heg⟩ := hg
  have htail : ContDiff ℝ (⊤ : ℕ∞) (fun y : Euclidean (n + 1) => Fin.tail y) :=
    contDiff_pi.mpr (fun i => contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) i.succ)
  let D : Set (Euclidean (n + 1)) := Fin.tail ⁻¹' (U ∩ V)
  have hD : IsOpen D := (hU.inter hV).preimage htail.continuous
  have hft : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Euclidean (n + 1) => f' (Fin.tail y)) D :=
    hf'.comp htail.contDiffOn (fun _ hy => hy.1)
  have hgt : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Euclidean (n + 1) => g' (Fin.tail y)) D :=
    hg'.comp htail.contDiffOn (fun _ hy => hy.2)
  refine ⟨D, hD, ?_,
    fun y => (1 - y 0) • f' (Fin.tail y) + y 0 • g' (Fin.tail y),
    ((contDiffOn_const.sub (contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) 0).contDiffOn).smul hft).add
      ((contDiff_apply ℝ (fun _ : Fin (n + 1) => ℝ) 0).contDiffOn.smul hgt), ?_⟩
  · change Fin.tail (Fin.cons t.val (ι x) : Euclidean (n + 1)) ∈ U ∩ V
    simpa using And.intro hxU hxV
  · filter_upwards [hef.comp_tendsto (continuous_snd.continuousAt (x := (t, x))),
      heg.comp_tendsto (continuous_snd.continuousAt (x := (t, x)))] with z hzf hzg
    simpa only [Function.comp_apply, Fin.cons_zero, Fin.tail_cons] using congrArg₂ (fun a b => (1 - z.1.val) • a + z.1.val • b) hzf hzg

/-- Smoothness of a map into an open Euclidean neighborhood can be composed
with a retraction expressed by its genuine ambient coordinate germs. -/
theorem retraction_comp_smoothAt {n m q : ℕ} {a : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m .euclidean N)
    (W : Set (Euclidean q)) (r : W → N) (hr : Continuous r)
    (hrext : ∀ y : W, ∀ d ∈ T.smoothStructure.val, r y ∈ d.source →
      LocalCoordinateExtension (⊤ : ℕ∞) Subtype.val (fun z => (d (r z)).val) y)
    (g : M → W) (x : M)
    (hg : ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val
      (fun p => (g p).val) x) :
    ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val (r ∘ g) x := by
  have hgc : ContinuousAt g x := tendsto_subtype_rng.mpr hg.1
  refine ⟨hr.continuousAt.comp hgc, ?_⟩
  intro e he d hd hxe hgd
  exact LocalCoordinateExtension.comp
    (LocalCoordinateExtension.precomp (ι := fun y : W => y.val)
      (f := fun z : W => (d (r z)).val) (h := g) (hrext (g x) d hd hgd) hgc rfl)
    (hg.2 e he hxe)

/-- Joint smoothness survives retraction, at time endpoints and source faces. -/
theorem retraction_straight_cylinderSmoothAt {n m q : ℕ} {a : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m .euclidean N)
    (W : Set (Euclidean q)) (r : W → N) (hr : Continuous r)
    (hrext : ∀ y : W, ∀ d ∈ T.smoothStructure.val, r y ∈ d.source →
      LocalCoordinateExtension (⊤ : ℕ∞) Subtype.val (fun z => (d (r z)).val) y)
    (f g : M → Euclidean q) (L : Time × M → W) (hL : Continuous L)
    (hformula : ∀ z, (L z).val = (1 - z.1.val) • f z.2 + z.1.val • g z.2)
    (z : Time × M)
    (hf : ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val f z.2)
    (hg : ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val g z.2) :
    CylinderSmoothAt S T (r ∘ L) z := by
  refine ⟨(hr.comp hL).continuousAt, ?_⟩
  intro e he d hd hze hzd
  have hstraight := straight_localCoordinateExtension (hf.2 e he hze) (hg.2 e he hze) z.1
  have hext : LocalCoordinateExtension (⊤ : ℕ∞)
      (fun w : Time × M => Fin.cons w.1.val (e w.2).val)
      (fun w => (L w).val) z :=
    hstraight.congr (Eventually.of_forall fun w => (hformula w).symm)
  exact LocalCoordinateExtension.comp
    (LocalCoordinateExtension.precomp (ι := fun y : W => y.val)
      (f := fun y : W => (d (r y)).val) (h := L)
      (hrext (L z) d hd hzd) hL.continuousAt rfl) hext

/-- The complete approximation argument once a smooth Euclidean neighborhood
retraction of the target is available. All graph and cylinder conclusions are
retained; the hypotheses here are to be constructed from Whitney and tubular
neighborhoods, not added to the original theorem. -/
theorem approximation_of_retraction {n m q : ℕ} {a : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m .euclidean N)
    (j : N → Euclidean q)
    (hj : ∀ y, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) T.smoothStructure.val j y)
    (W : Set (Euclidean q)) (hW : IsOpen W) (hjW : ∀ y, j y ∈ W)
    (r : W → N) (hr : Continuous r) (hrj : ∀ y, r ⟨j y, hjW y⟩ = y)
    (hrext : ∀ y : W, ∀ d ∈ T.smoothStructure.val, r y ∈ d.source →
      LocalCoordinateExtension (⊤ : ℕ∞) Subtype.val (fun z => (d (r z)).val) y)
    (A : Set M) (F : M → N) (O : Set (M × N))
    (hA : IsClosed A) (hF : Continuous F)
    (hlocal : LocallySmoothOnSubsetToManifold S.smoothStructure.val T.smoothStructure.val
      A (fun x => F x.val))
    (hO : IsOpen O) (hgraph : ∀ x, (x, F x) ∈ O) :
    ∃ G : M → N, IsSmoothMap S T G ∧ EqOn G F A ∧
      ∃ H : Time × M → N, Continuous H ∧
        (∀ x, H (⟨0, by simp⟩, x) = F x) ∧
        (∀ x, H (⟨1, by simp⟩, x) = G x) ∧
        (∀ t x, x ∈ A → H (t, x) = F x) ∧
        (∀ t x, (x, H (t, x)) ∈ O) ∧
        ((∃ U : Set M, IsOpen U ∧ A ⊆ U ∧
          ManifoldSmoothOn S.smoothStructure.val T.smoothStructure.val F U) →
          HomotopySmoothNear S T A H) := by
  have hjc : Continuous j := continuous_iff_continuousAt.mpr fun y => (hj y).1
  obtain ⟨ε, hε, hεpos, hεgood⟩ := retracted_straight_homotopy S T j hjc
    W hW hjW r hr hrj A F hF O hO hgraph
  obtain ⟨g, hg, heq, herr⟩ := exists_relative_euclidean_approximation S A (j ∘ F) ε
    hA (hjc.comp hF) hε hεpos (locallySmooth_comp_euclidean S T A F j hj hlocal)
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).1
  obtain ⟨L, H, hL, hH, hHrL, hformula, hzero, hone, hfix, hcontrol⟩ :=
    hεgood g hgc heq herr
  subst H
  let gW : M → W := fun x => L (⟨1, by simp⟩, x)
  have hgWval : (fun x => (gW x).val) = g := by
    funext x
    simpa [gW] using hformula (⟨1, by simp⟩, x)
  let G : M → N := r ∘ gW
  have hGsmooth : IsSmoothMap S T G := by
    intro x
    apply retraction_comp_smoothAt S T W r hr hrext gW x
    simpa only [hgWval] using hg x
  refine ⟨G, hGsmooth, ?_, r ∘ L, hH, hzero, ?_, hfix, hcontrol, ?_⟩
  · intro x hx
    exact hfix ⟨1, by simp⟩ x hx
  · intro x
    rfl
  · rintro ⟨U, hU, hAU, hFU⟩
    refine ⟨U, hU, hAU, ?_⟩
    intro z hz
    exact retraction_straight_cylinderSmoothAt S T W r hr hrext (j ∘ F) g L hL hformula z
      (smoothEuclideanAt_comp S T (hFU z.2 hz) (hj (F z.2))) (hg z.2)

/-- Actual neighborhood retraction with ambient local smooth coordinate
extensions. This is auxiliary data, to be produced by the tubular theorem. -/
structure EuclideanNeighborhoodRetraction {m q : ℕ} {N : Type v} [TopologicalSpace N]
    (T : SmoothManifold m .euclidean N) (j : N → Euclidean q) where
  domain : Set (Euclidean q)
  open_domain : IsOpen domain
  image_mem : ∀ y, j y ∈ domain
  retract : domain → N
  continuous_retract : Continuous retract
  retracts : ∀ y, retract ⟨j y, image_mem y⟩ = y
  smooth_germs : ∀ y : domain, ∀ d ∈ T.smoothStructure.val, retract y ∈ d.source →
    LocalCoordinateExtension (⊤ : ℕ∞) Subtype.val (fun z => (d (retract z)).val) y

/-- The Euclidean-valued smoothness test agrees with manifold smoothness for
any standard Euclidean structure containing its global identity chart. -/
theorem smoothEuclidean_isSmoothMap {m q : ℕ} {b : ModelKind}
    {N : Type v} [TopologicalSpace N] (T : SmoothManifold m b N)
    (E : SmoothManifold q .euclidean (Euclidean q))
    (hE : euclideanChart q ∈ E.smoothStructure.val) (j : N → Euclidean q)
    (hj : ∀ y, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) T.smoothStructure.val j y) :
    IsSmoothMap T E j := by
  intro y
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    T.smoothStructure.property.1 E.smoothStructure.property.1 j y).mpr
  obtain ⟨d, hd, hyd⟩ := T.smoothStructure.property.1.1 y
  exact ⟨(hj y).1, d, hd, euclideanChart q, hE, hyd, mem_univ _, (hj y).2 d hd hyd⟩

/-- Convert the full Euclidean immersion interface into the shared embedding
interface. Injectivity and the subspace homeomorphism are explicit inputs. -/
theorem euclideanImmersion_isSmoothEmbedding {m q : ℕ} {b : ModelKind}
    {N : Type v} [TopologicalSpace N] (T : SmoothManifold m b N)
    (E : SmoothManifold q .euclidean (Euclidean q))
    (hE : euclideanChart q ∈ E.smoothStructure.val) (j : N → Euclidean q)
    (hj : GoodProjectionData.IsEuclideanImmersion T j) (hi : Function.Injective j)
    (hh : ∃ h : N ≃ₜ range j, ∀ y, (h y).val = j y) :
    MapClassData.IsSmoothEmbedding T E j := by
  have hjs := smoothEuclidean_isSmoothMap T E hE j hj.1
  have hj1 := manifoldContDiff_of_le (⊤ : ℕ∞) 1
    T.smoothStructure.val E.smoothStructure.val j (by simp) hjs
  refine ⟨hjs, hi, ?_, hh⟩
  intro y
  obtain ⟨d, hd, hyd⟩ := T.smoothStructure.property.1.1 y
  exact (MapClasses.chart_invariants T E j hj1 y d (euclideanChart q)
    hd hE hyd (mem_univ _)).2.1.mpr (hj.2 d hd y hyd)

/-- Extract the smooth neighborhood retraction from the
small-universe tubular theorem. No closedness of the embedded image is used. -/
theorem retraction_of_tubular
    (ht : Specs.SmoothManifolds.Ch04.EuclideanTubular.euclidean_tubularType)
    {m q : ℕ} {N : Type} [TopologicalSpace N]
    (T : SmoothManifold m .euclidean N) (j : N → Euclidean q)
    (hj : GoodProjectionData.IsEuclideanImmersion T j) (hi : Function.Injective j)
    (hh : ∃ h : N ≃ₜ range j, ∀ y, (h y).val = j y) :
    Nonempty (EuclideanNeighborhoodRetraction T j) := by
  obtain ⟨E, hE⟩ := standardEuclidean_exists q
  obtain ⟨B, _, V, W, hV, hW, h, hTub⟩ := ht T E hE j
    (euclideanImmersion_isSmoothEmbedding T E hE j hj hi hh)
  obtain ⟨_, _, _, hjW, _, _, r, _, hrs, _, hrj, _⟩ := hTub
  refine ⟨⟨W, hW, fun y => hjW (mem_range_self y), r,
    continuous_iff_continuousAt.mpr (fun y => (hrs y).1),
    fun y => hrj y _, ?_⟩⟩
  intro y d hd hyd
  let e : ModelChart q .euclidean W :=
    (euclideanChart q).subtypeRestr (s := ⟨W, hW⟩) ⟨y⟩
  have he : e ∈ openSubsetAtlas E.smoothStructure.val W hW :=
    ⟨⟨y⟩, euclideanChart q, hE, rfl⟩
  have hye : y ∈ e.source := by
    simp [e, OpenPartialHomeomorph.subtypeRestr_source, euclideanChart_source]
  exact (hrs y).2 e he d hd hye hyd

/-- Transport a manifold to a homeomorphic space, keeping the actual charts
and then taking their maximal extension. -/
noncomputable def transportedManifold {m : ℕ} {b : ModelKind}
    {N : Type v} {P : Type w} [TopologicalSpace N] [TopologicalSpace P]
    [T2Space P] [SecondCountableTopology P]
    (T : SmoothManifold m b N) (h : N ≃ₜ P) : SmoothManifold m b P := by
  let B := transportAtlas h T.smoothStructure.val
  have hB := transportAtlas_isContDiffAtlas (⊤ : ℕ∞) T.smoothStructure.val h
    T.smoothStructure.property.1
  exact ⟨⟨inferInstance, inferInstance, B, hB.1⟩,
    ⟨maximalExtension (⊤ : ℕ∞) B, maximalExtension_isMaximal hB⟩⟩

/-- Chart transport is a smooth equivalence, at the level of maximal atlases. -/
theorem transportedManifold_maps {m : ℕ} {b : ModelKind}
    {N : Type v} {P : Type w} [TopologicalSpace N] [TopologicalSpace P]
    [T2Space P] [SecondCountableTopology P]
    (T : SmoothManifold m b N) (h : N ≃ₜ P) :
    IsSmoothMap T (transportedManifold T h) h ∧
      IsSmoothMap (transportedManifold T h) T h.symm := by
  let A := T.smoothStructure.val
  let B := transportAtlas h A
  have hA := T.smoothStructure.property.1
  have hB := transportAtlas_isContDiffAtlas (⊤ : ℕ∞) A h hA
  have hmax : maximalExtension (⊤ : ℕ∞) A = A :=
    T.smoothStructure.property.2 _ (maximalExtension_isContDiffAtlas hA) (subset_maximalExtension hA)
  obtain ⟨hf, hg⟩ := transportAtlas_maps (⊤ : ℕ∞) A h hA
  constructor
  · have hh := (manifoldContDiff_maximalExtension_iff (⊤ : ℕ∞) A B hA hB h).mpr hf
    rw [hmax] at hh
    exact hh
  · have hh := (manifoldContDiff_maximalExtension_iff (⊤ : ℕ∞) B A hB hA h.symm).mpr hg
    rw [hmax] at hh
    exact hh

/-- Euclidean immersions survive genuine change of their underlying space.
In the transported source chart the same ambient extension has exactly the
same derivative, so no tangent direction is discarded. -/
theorem euclideanImmersion_transport {m q : ℕ} {b : ModelKind}
    {N : Type v} {P : Type w} [TopologicalSpace N] [TopologicalSpace P]
    [T2Space P] [SecondCountableTopology P]
    (T : SmoothManifold m b N) (h : N ≃ₜ P) (j : N → Euclidean q)
    (hj : GoodProjectionData.IsEuclideanImmersion T j) :
    GoodProjectionData.IsEuclideanImmersion (transportedManifold T h) (j ∘ h.symm) := by
  have hmaps := transportedManifold_maps T h
  have hs : GoodProjectionData.IsSmoothEuclidean (transportedManifold T h) (j ∘ h.symm) :=
    fun p => smoothEuclideanAt_comp (transportedManifold T h) T (hmaps.2 p) (hj.1 (h.symm p))
  apply FiniteProperEmbedding.immersion_of_one_chart (transportedManifold T h) (j ∘ h.symm) hs
  intro p
  obtain ⟨e, he, hpe⟩ := T.smoothStructure.property.1.1 (h.symm p)
  let d := h.symm.toOpenPartialHomeomorph.trans e
  have hB := transportAtlas_isContDiffAtlas (⊤ : ℕ∞) T.smoothStructure.val h
    T.smoothStructure.property.1
  have hd : d ∈ (transportedManifold T h).smoothStructure.val :=
    subset_maximalExtension hB ⟨e, he, rfl⟩
  have hpd : p ∈ d.source := by
    change p ∈ univ ∩ h.symm ⁻¹' e.source
    exact ⟨mem_univ _, hpe⟩
  let L := FiniteRegularityData.coordinateDerivative e j (h.symm p)
  have hL : FiniteRegularityData.HasCoordinateDerivative e j (h.symm p) L :=
    FiniteRegularity.chartDerivative_exists (⊤ : ℕ∞) (by simp) e (euclideanChart q) j
      (h.symm p) ((hj.1 (h.symm p)).2 e he hpe)
  obtain ⟨F, hF, heq⟩ := hL
  have hdL : FiniteRegularityData.coordinateDerivative d (j ∘ h.symm) p = L := by
    apply FiniteRegularity.coordinateDerivative_eq d (j ∘ h.symm) p hpd L
    exact ⟨F, hF, heq.comp_tendsto h.symm.continuous.continuousAt⟩
  refine ⟨d, hd, hpd, ?_⟩
  rw [hdL]
  exact hj.2 e he (h.symm p) hpe

/-- Pull a smooth neighborhood retraction back from a transported copy of a
manifold. This is the universe bridge for the tubular interface. -/
theorem retraction_transport_back {m q : ℕ}
    {N : Type v} {P : Type w} [TopologicalSpace N] [TopologicalSpace P]
    [T2Space P] [SecondCountableTopology P]
    (T : SmoothManifold m .euclidean N) (h : N ≃ₜ P) (j : N → Euclidean q)
    (R : EuclideanNeighborhoodRetraction (transportedManifold T h) (j ∘ h.symm)) :
    Nonempty (EuclideanNeighborhoodRetraction T j) := by
  have hmaps := transportedManifold_maps T h
  have hmem (y : N) : j y ∈ R.domain := by
    simpa only [Function.comp_apply, h.symm_apply_apply] using R.image_mem (h y)
  let r : R.domain → N := h.symm ∘ R.retract
  have hrc : Continuous r := h.symm.continuous.comp R.continuous_retract
  refine ⟨⟨R.domain, R.open_domain, hmem, r, hrc, ?_, ?_⟩⟩
  · intro y
    have hh := R.retracts (h y)
    have harg : (⟨(j ∘ h.symm) (h y), R.image_mem (h y)⟩ : R.domain) = ⟨j y, hmem y⟩ := by
      apply Subtype.ext
      simp only [Function.comp_apply, h.symm_apply_apply]
    rw [harg] at hh
    change h.symm (R.retract _) = y
    rw [hh, h.symm_apply_apply]
  · intro y d hd hyd
    obtain ⟨e, he, hye⟩ := (transportedManifold T h).smoothStructure.property.1.1 (R.retract y)
    have hout := (hmaps.2 (R.retract y)).2 e he d hd hye hyd
    have hpull := LocalCoordinateExtension.precomp
      (ι := fun z : P => (e z).val) (f := fun z : P => (d (h.symm z)).val)
      (h := R.retract) hout R.continuous_retract.continuousAt rfl
    exact LocalCoordinateExtension.comp hpull (R.smooth_germs y e he hye)

/-- Relative Whitney approximation into a boundaryless manifold. The homotopy
is fixed on the closed set, stays in the prescribed graph neighborhood, and
has ambient smooth extensions near the closed set whenever the original map
does. The source may have ordinary boundary. -/
theorem relative_manifold_approximation :
    Specs.SmoothManifolds.Ch04.RelativeManifoldApproximation.relative_manifold_approximationType.{u,v} := by
  intro n m a N M _ _ S T A F O hA hF hlocal hO hgraph
  obtain ⟨j, hj, hi, _, hhome⟩ := ProperWhitney.exists_proper_embedding T
  obtain ⟨h, hh⟩ := hhome
  let P := range j
  let T' := transportedManifold T h
  let j' : P → Euclidean (2 * m + 1) := j ∘ h.symm
  have hj' : GoodProjectionData.IsEuclideanImmersion T' j' :=
    euclideanImmersion_transport T h j hj
  have hj'val : j' = (Subtype.val : P → Euclidean (2 * m + 1)) := by
    funext y
    have hy := hh (h.symm y)
    simpa only [j', Function.comp_apply, h.apply_symm_apply] using hy.symm
  have hEmb : Topology.IsEmbedding j' := by
    rw [hj'val]
    exact Topology.IsEmbedding.subtypeVal
  obtain ⟨R'⟩ := retraction_of_tubular EuclideanTubular.euclidean_tubular T' j' hj'
    (hi.comp h.symm.injective) ⟨hEmb.toHomeomorph, fun _ => rfl⟩
  obtain ⟨R⟩ := retraction_transport_back T h j R'
  exact approximation_of_retraction S T j hj.1 R.domain R.open_domain R.image_mem
    R.retract R.continuous_retract R.retracts R.smooth_germs A F O hA hF hlocal hO hgraph

end SmoothManifolds.RelativeManifoldApproximation
