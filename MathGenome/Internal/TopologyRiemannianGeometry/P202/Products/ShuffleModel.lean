import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.ShuffleModel
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.AlexanderWhitney

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial TensorProduct ContDiff
namespace P202.ShuffleModel
open P202Specs.SingularChains P202Specs.AlexanderWhitney P202Specs.ShuffleModel
universe u w
variable (R : Type u) [CommRing R]

def shuffleComponent (X Y : TopCat.{w}) (p q : ℕ) :
    Summand R X Y p q →ₗ[R] Chains R (productSpace X Y) (p+q) :=
  P202Specs.ShuffleModel.shuffleComponent R X Y p q

def shuffle (X Y : TopCat.{w}) (n : ℕ) :
    Total R X Y n →ₗ[R] Chains R (productSpace X Y) n :=
  P202Specs.ShuffleModel.shuffle R X Y n

lemma permutation_sign {p q : ℕ} (s : LatticePath p q) :
    (∀ k, s.permutation k = s.stepLabel k) ∧
      s.sign = ((Equiv.Perm.sign s.permutation : ℤˣ) : ℤ) := ⟨fun _ => rfl, rfl⟩

lemma path_initial {p q : ℕ} (s : LatticePath p q) :
    s.horizontal 0 = 0 ∧ s.vertical 0 = 0 := by
  have h := s.rank 0
  simp only [Fin.val_zero] at h
  constructor <;> apply Fin.ext <;> simp only [Fin.val_zero] <;> omega

lemma path_terminal {p q : ℕ} (s : LatticePath p q) :
    s.horizontal (Fin.last (p+q)) = Fin.last p ∧
      s.vertical (Fin.last (p+q)) = Fin.last q := by
  have h := s.rank (Fin.last (p+q))
  have hx := (s.horizontal (Fin.last (p+q))).isLt
  have hy := (s.vertical (Fin.last (p+q))).isLt
  simp only [Fin.val_last] at h
  exact ⟨Fin.ext (by simp only [Fin.val_last]; omega),
    Fin.ext (by simp only [Fin.val_last]; omega)⟩

lemma path_step {p q : ℕ} (s : LatticePath p q) (k : Fin (p+q)) :
    ((s.horizontal k.succ).val = (s.horizontal k.castSucc).val + 1 ∧
      s.vertical k.succ = s.vertical k.castSucc) ∨
    (s.horizontal k.succ = s.horizontal k.castSucc ∧
      (s.vertical k.succ).val = (s.vertical k.castSucc).val + 1) := s.step k

lemma parametrization_vertex {p q : ℕ} (s : LatticePath p q) (k : Fin (p+q+1)) :
    parametrization s (Convexity.StdSimplex.single k) =
      (Convexity.StdSimplex.single (s.horizontal k),
        Convexity.StdSimplex.single (s.vertical k)) := by
  simp [parametrization]

lemma parametrization_weights {p q : ℕ} (s : LatticePath p q) (z : StdSimplex (p+q)) :
    (parametrization s z).1.weights = z.weights.mapDomain s.horizontal ∧
      (parametrization s z).2.weights = z.weights.mapDomain s.vertical := ⟨rfl, rfl⟩

lemma simplex_formula {X Y : TopCat.{w}} {p q : ℕ} (s : LatticePath p q)
    (σ : Simplex X p) (τ : Simplex Y q) (z : StdSimplex (p+q)) :
    simplexEquiv (productSpace X Y) (p+q) (shuffleSimplex s σ τ) z =
      (simplexEquiv X p σ (z.map s.horizontal),
        simplexEquiv Y q τ (z.map s.vertical)) := by
  simp [shuffleSimplex, parametrization]

@[simp] lemma component_basis (X Y : TopCat.{w}) (p q : ℕ)
    (σ : Simplex X p) (τ : Simplex Y q) :
    shuffleComponent R X Y p q (Finsupp.single σ (1 : R) ⊗ₜ[R] Finsupp.single τ (1 : R)) =
      shuffleGenerator R σ τ := by
  let b : Module.Basis (Simplex X p) R (Chains R X p) := Finsupp.basisSingleOne
  let c : Module.Basis (Simplex Y q) R (Chains R Y q) := Finsupp.basisSingleOne
  simpa only [shuffleComponent, P202Specs.ShuffleModel.shuffleComponent,
    b, c, Module.Basis.tensorProduct_apply, Finsupp.coe_basisSingleOne] using
    ((b.tensorProduct c).constr_basis R (fun st => shuffleGenerator R st.1 st.2) (σ,τ))

lemma component_formula (X Y : TopCat.{w}) (p q : ℕ)
    (σ : Simplex X p) (τ : Simplex Y q) (r t : R) :
    shuffleComponent R X Y p q (Finsupp.single σ r ⊗ₜ[R] Finsupp.single τ t) =
      (r*t) • ∑ s : LatticePath p q, s.sign • Finsupp.single (shuffleSimplex s σ τ) 1 := by
  have hr : Finsupp.single σ r = r • Finsupp.single σ (1 : R) := by simp
  have ht : Finsupp.single τ t = t • Finsupp.single τ (1 : R) := by simp
  rw [hr, ht, TensorProduct.smul_tmul_smul, map_smul, component_basis]
  rfl

lemma simplex_natural {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    {p q : ℕ} (s : LatticePath p q) (σ : Simplex X p) (τ : Simplex Y q) :
    postSimplex (productMap f g) (p+q) (shuffleSimplex s σ τ) =
      shuffleSimplex s (postSimplex f p σ) (postSimplex g q τ) := by
  apply (simplexEquiv (productSpace X' Y') (p+q)).injective
  ext z
  simp only [postSimplex, P202.SingularChains.simplexEquiv_postcomp,
    ContinuousMap.comp_apply, simplex_formula]
  rfl

lemma generator_natural {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q) :
    ((chainMap R R (productMap f g)).f (p+q)).hom (shuffleGenerator R σ τ) =
      shuffleGenerator R (postSimplex f p σ) (postSimplex g q τ) := by
  simp only [shuffleGenerator, map_sum, map_zsmul,
    P202.SingularChains.chainMap_single]
  apply Finset.sum_congr rfl
  intro s _
  change s.sign • Finsupp.single
    (postSimplex (productMap f g) (p+q) (shuffleSimplex s σ τ)) 1 = _
  rw [simplex_natural]

lemma component_natural {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    (p q : ℕ) :
    (((chainMap R R (productMap f g)).f (p+q)).hom).comp
      (shuffleComponent R X Y p q) =
    (shuffleComponent R X' Y' p q).comp
      (TensorProduct.map ((chainMap R R f).f p).hom ((chainMap R R g).f q).hom) := by
  apply ((Finsupp.basisSingleOne : Module.Basis (Simplex X p) R (Chains R X p)).tensorProduct
    (Finsupp.basisSingleOne : Module.Basis (Simplex Y q) R (Chains R Y q))).ext
  intro ⟨σ,τ⟩
  simp only [Module.Basis.tensorProduct_apply, Finsupp.coe_basisSingleOne]
  change Finsupp.lmapDomain R R (postSimplex (productMap f g) (p+q))
    (shuffleComponent R X Y p q (Finsupp.single σ (1:R) ⊗ₜ[R] Finsupp.single τ (1:R))) =
    shuffleComponent R X' Y' p q (TensorProduct.map
      (Finsupp.lmapDomain R R (postSimplex f p))
      (Finsupp.lmapDomain R R (postSimplex g q))
      (Finsupp.single σ (1:R) ⊗ₜ[R] Finsupp.single τ (1:R)))
  rw [component_basis, TensorProduct.map_tmul]
  simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [component_basis]
  exact generator_natural R f g σ τ

lemma castChains_natural {X Y : TopCat.{w}} (f : X ⟶ Y) {n m : ℕ} (h : n=m)
    (c : Chains R X n) :
    ((chainMap R R f).f m).hom (castChains R h c) =
      castChains R h (((chainMap R R f).f n).hom c) := by
  subst m
  rfl

lemma total_formula (X Y : TopCat.{w}) (n : ℕ) (z : Total R X Y n) :
    shuffle R X Y n z = ∑ i : Diagonal n, castChains R i.property
      (shuffleComponent R X Y i.val.1 i.val.2 (z i)) := by
  simp only [shuffle, P202Specs.ShuffleModel.shuffle, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
  rfl

lemma naturality {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    (((chainMap R R (productMap f g)).f n).hom).comp (shuffle R X Y n) =
      (shuffle R X' Y' n).comp (totalMap R f g n) := by
  apply LinearMap.ext
  intro z
  change Finsupp.lmapDomain R R (postSimplex (productMap f g) n) (shuffle R X Y n z) =
    shuffle R X' Y' n (totalMap R f g n z)
  rw [total_formula, total_formula, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ((chainMap R R (productMap f g)).f n).hom
    (castChains R i.property (shuffleComponent R X Y i.val.1 i.val.2 (z i))) = _
  rw [castChains_natural]
  apply congrArg (castChains R i.property)
  exact LinearMap.congr_fun (component_natural R f g i.val.1 i.val.2) (z i)

lemma zeroLeft_unique (q : ℕ) (s : LatticePath 0 q) : s = zeroLeft q := by
  apply Subtype.ext
  apply Prod.ext
  · apply DFunLike.ext
    intro k
    apply Fin.ext
    change (s.horizontal k).val = 0
    have hx := (s.horizontal k).isLt
    change (s.horizontal k).val < 1 at hx
    omega
  · apply DFunLike.ext
    intro k
    apply Fin.ext
    change (s.vertical k).val = k.val
    have h := s.rank k
    have hx := (s.horizontal k).isLt
    change (s.horizontal k).val < 1 at hx
    omega

lemma zeroRight_unique (p : ℕ) (s : LatticePath p 0) : s = zeroRight p := by
  apply Subtype.ext
  apply Prod.ext
  · apply DFunLike.ext
    intro k
    apply Fin.ext
    change (s.horizontal k).val = k.val
    have h := s.rank k
    have hy := (s.vertical k).isLt
    change (s.vertical k).val < 1 at hy
    omega
  · apply DFunLike.ext
    intro k
    apply Fin.ext
    change (s.vertical k).val = 0
    have hy := (s.vertical k).isLt
    change (s.vertical k).val < 1 at hy
    omega

lemma zeroLeft_sign (q : ℕ) : (zeroLeft q).sign = 1 := by
  have h : (zeroLeft q).permutation = Equiv.refl _ := by
    apply Equiv.ext
    intro k
    apply Fin.ext
    change ((zeroLeft q).stepLabel k).val = k.val
    simp [LatticePath.stepLabel, LatticePath.horizontal, LatticePath.vertical, zeroLeft]
  simp [LatticePath.sign, h]

lemma zeroRight_sign (p : ℕ) : (zeroRight p).sign = 1 := by
  have h : (zeroRight p).permutation = Equiv.refl _ := by
    apply Equiv.ext
    intro k
    apply Fin.ext
    change ((zeroRight p).stepLabel k).val = k.val
    simp [LatticePath.stepLabel, LatticePath.horizontal, LatticePath.vertical, zeroRight]
  simp [LatticePath.sign, h]

lemma component_zero_left (X Y : TopCat.{w}) (q : ℕ)
    (σ : Simplex X 0) (τ : Simplex Y q) :
    shuffleComponent R X Y 0 q (Finsupp.single σ (1:R) ⊗ₜ[R] Finsupp.single τ (1:R)) =
      Finsupp.single (shuffleSimplex (zeroLeft q) σ τ) 1 := by
  rw [component_basis, shuffleGenerator, Finset.sum_eq_single (zeroLeft q)]
  · rw [zeroLeft_sign, one_smul]
  · intro s _ hs
    exact (hs (zeroLeft_unique q s)).elim
  · simp

lemma component_zero_right (X Y : TopCat.{w}) (p : ℕ)
    (σ : Simplex X p) (τ : Simplex Y 0) :
    shuffleComponent R X Y p 0 (Finsupp.single σ (1:R) ⊗ₜ[R] Finsupp.single τ (1:R)) =
      Finsupp.single (shuffleSimplex (zeroRight p) σ τ) 1 := by
  rw [component_basis, shuffleGenerator, Finset.sum_eq_single (zeroRight p)]
  · rw [zeroRight_sign, one_smul]
  · intro s _ hs
    exact (hs (zeroRight_unique p s)).elim
  · simp

lemma ambientMap_smooth {m n : ℕ} (f : Fin (m+1) → Fin (n+1)) :
    ContDiff ℝ ∞ (ambientMap f) := by
  apply contDiff_pi.mpr
  intro i
  exact ContDiff.sum (fun k _ => contDiff_apply ℝ _ k)

lemma ambientParametrization_smooth {p q : ℕ} (s : LatticePath p q) :
    ContDiff ℝ ∞ (ambientParametrization s) :=
  (ambientMap_smooth s.horizontal).prodMk (ambientMap_smooth s.vertical)

lemma ambientMap_weights {m n : ℕ} (f : Fin (m+1) → Fin (n+1)) (z : StdSimplex m) :
    ambientMap f (weights z) = weights (z.map f) := by
  classical
  ext i
  simp only [ambientMap, weights, Convexity.StdSimplex.weights_map,
    Finsupp.mapDomain_fintype, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.single_apply, Finset.sum_filter]

lemma ambientParametrization_weights {p q : ℕ} (s : LatticePath p q)
    (z : StdSimplex (p+q)) :
    ambientParametrization s (weights z) =
      (weights (parametrization s z).1, weights (parametrization s z).2) := by
  exact Prod.ext (ambientMap_weights s.horizontal z) (ambientMap_weights s.vertical z)

/-- Affine pullback preserves local smooth extensions even at simplex corners. -/
lemma smooth_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : ℕ} (f : StdSimplex n → E) (hf : SmoothAtCorners f)
    (θ : Fin (m+1) → Fin (n+1)) :
    SmoothAtCorners (fun z : StdSimplex m => f (z.map θ)) := by
  intro z
  obtain ⟨U,hU,hz,F,hF,hEq⟩ := hf (z.map θ)
  refine ⟨ambientMap θ ⁻¹' U, hU.preimage (ambientMap_smooth θ).continuous,
    ?_, fun a => F (ambientMap θ a), ?_, ?_⟩
  · change ambientMap θ (weights z) ∈ U
    rwa [ambientMap_weights]
  · exact hF.comp (ambientMap_smooth θ).contDiffOn (fun a ha => ha)
  · intro x hx
    change F (ambientMap θ (weights x)) = f (x.map θ)
    rw [ambientMap_weights]
    apply hEq
    rwa [← ambientMap_weights]

lemma smooth_pair {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    (f : StdSimplex n → E) (g : StdSimplex n → F)
    (hf : SmoothAtCorners f) (hg : SmoothAtCorners g) :
    SmoothAtCorners (fun z => (f z, g z)) := by
  intro z
  obtain ⟨U,hU,hzU,f',hf',hfEq⟩ := hf z
  obtain ⟨V,hV,hzV,g',hg',hgEq⟩ := hg z
  refine ⟨U ∩ V, hU.inter hV, ⟨hzU,hzV⟩, fun a => (f' a, g' a),
    (hf'.mono Set.inter_subset_left).prodMk (hg'.mono Set.inter_subset_right), ?_⟩
  intro x hx
  exact Prod.ext (hfEq x hx.1) (hgEq x hx.2)

/-- The chartwise smooth shuffle restriction. The hypothesis requires local
ambient extensions at every simplex point, not just its relative interior. -/
lemma smooth_shuffle {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p q : ℕ}
    (f : StdSimplex p → E) (g : StdSimplex q → F)
    (hf : SmoothAtCorners f) (hg : SmoothAtCorners g) (s : LatticePath p q) :
    SmoothAtCorners (fun z : StdSimplex (p+q) =>
      (f (parametrization s z).1, g (parametrization s z).2)) :=
  smooth_pair _ _ (smooth_pullback f hf s.horizontal) (smooth_pullback g hg s.vertical)

/-- The accepted ordered face has the same global linear extension. -/
lemma face_ambient_extension {n : ℕ} (i : Fin (n+2)) :
    ContDiff ℝ ∞ (ambientMap i.succAbove) ∧
      ∀ z : StdSimplex n, ambientMap i.succAbove (weights z) = weights (faceInclusion i z) := by
  refine ⟨ambientMap_smooth _, ?_⟩
  intro z
  rw [ambientMap_weights]
  rfl

section Charts
variable {E F H K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]

lemma charts_pullback {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (I : H → E) {m n : ℕ} (f : StdSimplex n → M) (hf : SmoothInCharts I f)
    (θ : Fin (m+1) → Fin (n+1)) :
    SmoothInCharts I (fun z : StdSimplex m => f (z.map θ)) := by
  refine ⟨hf.1.comp (Convexity.StdSimplex.continuous_map ℝ θ), ?_⟩
  intro z c hc hcz
  obtain ⟨U, hU, hz, F, hF, hEq⟩ := hf.2 (z.map θ) c hc hcz
  refine ⟨ambientMap θ ⁻¹' U, hU.preimage (ambientMap_smooth θ).continuous,
    ?_, fun a => F (ambientMap θ a), ?_, ?_⟩
  · change ambientMap θ (weights z) ∈ U
    rwa [ambientMap_weights]
  · exact hF.comp (ambientMap_smooth θ).contDiffOn (fun a ha => ha)
  · intro x hx
    change f (x.map θ) ∈ c.source ∧
      F (ambientMap θ (weights x)) = I (c (f (x.map θ)))
    rw [ambientMap_weights]
    apply hEq
    rwa [← ambientMap_weights]

lemma charts_pair {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N] (I : H → E) (J : K → F) {n : ℕ}
    (f : StdSimplex n → M) (g : StdSimplex n → N)
    (hf : SmoothInCharts I f) (hg : SmoothInCharts J g) :
    SmoothInCharts (H := ModelProd H K) (fun h => (I h.1, J h.2)) (fun z => (f z, g z)) := by
  refine ⟨hf.1.prodMk hg.1, ?_⟩
  intro z c hc hcz
  change c ∈ Set.image2 OpenPartialHomeomorph.prod (atlas H M) (atlas K N) at hc
  obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := hc
  obtain ⟨U, hU, hzU, f', hf', hfEq⟩ := hf.2 z c₁ hc₁ hcz.1
  obtain ⟨V, hV, hzV, g', hg', hgEq⟩ := hg.2 z c₂ hc₂ hcz.2
  refine ⟨U ∩ V, hU.inter hV, ⟨hzU, hzV⟩, fun a => (f' a, g' a),
    (hf'.mono Set.inter_subset_left).prodMk (hg'.mono Set.inter_subset_right), ?_⟩
  intro x hx
  obtain ⟨hfx, hfEqx⟩ := hfEq x hx.1
  obtain ⟨hgx, hgEqx⟩ := hgEq x hx.2
  exact ⟨⟨hfx, hgx⟩, Prod.ext hfEqx hgEqx⟩

/-- Every product target chart is a product of factor charts. The extension
is constructed near each point and in each such chart independently. -/
lemma charts_shuffle {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N] (I : H → E) (J : K → F) {p q : ℕ}
    (f : StdSimplex p → M) (g : StdSimplex q → N)
    (hf : SmoothInCharts I f) (hg : SmoothInCharts J g) (s : LatticePath p q) :
    SmoothInCharts (H := ModelProd H K) (fun h => (I h.1, J h.2))
      (fun z : StdSimplex (p+q) => (f (parametrization s z).1, g (parametrization s z).2)) :=
  charts_pair I J _ _ (charts_pullback I f hf s.horizontal)
    (charts_pullback J g hg s.vertical)

lemma smooth_face (I : H → E) (X : TopCat.{w}) [ChartedSpace H X]
    {n : ℕ} (σ : Simplex X (n+1)) (hσ : SmoothSimplex I X σ) (i : Fin (n+2)) :
    SmoothSimplex I X (face i σ) := by
  unfold SmoothSimplex at *
  rw [P202.SingularChains.simplexEquiv_face]
  exact charts_pullback I _ hσ i.succAbove

lemma smooth_simplex (I : H → E) (J : K → F)
    (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y]
    {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q)
    (hσ : SmoothSimplex I X σ) (hτ : SmoothSimplex J Y τ) (s : LatticePath p q) :
    SmoothSimplex (H := ModelProd H K) (fun h => (I h.1, J h.2))
      (productSpace X Y) (shuffleSimplex s σ τ) := by
  unfold SmoothSimplex
  have he : (simplexEquiv (productSpace X Y) (p+q) (shuffleSimplex s σ τ) :
      StdSimplex (p+q) → X × Y) =
      fun z => (simplexEquiv X p σ (parametrization s z).1,
        simplexEquiv Y q τ (parametrization s z).2) := by
    funext z
    exact simplex_formula s σ τ z
  rw [he]
  exact charts_shuffle I J _ _ hσ hτ s

/-- Extending a generator calculation to all finite smooth chains. -/
lemma map_smoothChains {V : Type*} [AddCommGroup V] [Module R V]
    (I : H → E) (X : TopCat.{w}) [ChartedSpace H X] {n : ℕ}
    (L : Chains R X n →ₗ[R] V) (S : Submodule R V)
    (hL : ∀ σ, SmoothSimplex I X σ → L (Finsupp.single σ 1) ∈ S)
    (c : Chains R X n) (hc : c ∈ smoothChains R I X n) : L c ∈ S := by
  have hle : smoothChains R I X n ≤ S.comap L := by
    unfold smoothChains
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨σ, hσ, rfl⟩
    exact hL σ hσ
  exact hle hc

/-- Thus the corner-smooth finite chains are closed under the ordinary
boundary. The degree-zero boundary in the shared ordinary complex is zero. -/
lemma smooth_boundary (I : H → E) (X : TopCat.{w}) [ChartedSpace H X] (n : ℕ)
    (c : Chains R X (n+1)) (hc : c ∈ smoothChains R I X (n+1)) :
    boundary R R X n c ∈ smoothChains R I X n := by
  apply map_smoothChains R I X _ _ ?_ c hc
  intro σ hσ
  have hs : (∑ i : Fin (n+2), (-1 : ℤ)^i.val • Finsupp.single (face i σ) (1:R)) ∈
      smoothChains R I X n := by
    apply Submodule.sum_mem
    intro i _
    exact (smoothChains R I X n).toAddSubgroup.zsmul_mem
      (Finsupp.single_mem_supported R 1 (smooth_face I X σ hσ i)) _
  exact (P202.SingularChains.boundary_single R R X n σ (1:R)).symm ▸ hs

lemma smooth_generator (I : H → E) (J : K → F)
    (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y]
    {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q)
    (hσ : SmoothSimplex I X σ) (hτ : SmoothSimplex J Y τ) :
    shuffleGenerator R σ τ ∈
      smoothChains R (H := ModelProd H K) (fun h => (I h.1, J h.2)) (productSpace X Y) (p+q) := by
  unfold shuffleGenerator
  apply Submodule.sum_mem
  intro s _
  exact (smoothChains R (H := ModelProd H K) (fun h => (I h.1, J h.2))
    (productSpace X Y) (p+q)).toAddSubgroup.zsmul_mem
    (Finsupp.single_mem_supported R 1 (smooth_simplex I J X Y σ τ hσ hτ s)) _

lemma smooth_component (I : H → E) (J : K → F)
    (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y]
    (p q : ℕ) (a : smoothChains R I X p) (b : smoothChains R J Y q) :
    shuffleComponent R X Y p q (a.val ⊗ₜ[R] b.val) ∈
      smoothChains R (H := ModelProd H K) (fun h => (I h.1, J h.2)) (productSpace X Y) (p+q) := by
  let S := smoothChains R (H := ModelProd H K) (fun h => (I h.1, J h.2))
    (productSpace X Y) (p+q)
  apply map_smoothChains R I X
    ((shuffleComponent R X Y p q).comp ((TensorProduct.mk R _ _).flip b.val)) S ?_ a.val a.property
  intro σ hσ
  apply map_smoothChains R J Y
    ((shuffleComponent R X Y p q).comp ((TensorProduct.mk R _ _) (Finsupp.single σ 1))) S ?_ b.val b.property
  intro τ hτ
  change shuffleComponent R X Y p q (Finsupp.single σ 1 ⊗ₜ[R] Finsupp.single τ 1) ∈ S
  rw [component_basis]
  exact smooth_generator R I J X Y σ τ hσ hτ

lemma smooth_tensor (I : H → E) (J : K → F)
    (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y] (p q : ℕ)
    (z : smoothChains R I X p ⊗[R] smoothChains R J Y q) :
    shuffleComponent R X Y p q
      (TensorProduct.map (smoothChains R I X p).subtype (smoothChains R J Y q).subtype z) ∈
      smoothChains R (H := ModelProd H K) (fun h => (I h.1, J h.2)) (productSpace X Y) (p+q) := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | tmul a b => exact smooth_component R I J X Y p q a b

lemma smooth_restriction (I : H → E) (J : K → F)
    (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y] (p q : ℕ) :
    ∃ L : (smoothChains R I X p ⊗[R] smoothChains R J Y q) →ₗ[R]
        smoothChains R (H := ModelProd H K) (fun h => (I h.1, J h.2)) (productSpace X Y) (p+q),
      (smoothChains R (H := ModelProd H K) (fun h => (I h.1, J h.2))
        (productSpace X Y) (p+q)).subtype.comp L =
      (P202Specs.ShuffleModel.shuffleComponent R X Y p q).comp
        (TensorProduct.map (smoothChains R I X p).subtype (smoothChains R J Y q).subtype) := by
  let L := (P202Specs.ShuffleModel.shuffleComponent R X Y p q).comp
    (TensorProduct.map (smoothChains R I X p).subtype (smoothChains R J Y q).subtype)
  exact ⟨L.codRestrict _ (smooth_tensor R I J X Y p q), rfl⟩

lemma smooth_castChains (I : H → E) (X : TopCat.{w}) [ChartedSpace H X]
    {n m : ℕ} (h : n=m) (c : Chains R X n) (hc : c ∈ smoothChains R I X n) :
    castChains R h c ∈ smoothChains R I X m := by
  subst m
  exact hc

lemma smooth_total_restriction (I : H → E) (J : K → F)
    (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y] (n : ℕ) :
    ∃ L : SmoothTotal R I J X Y n →ₗ[R]
        smoothChains R (H := ModelProd H K) (fun h => (I h.1, J h.2)) (productSpace X Y) n,
      (smoothChains R (H := ModelProd H K) (fun h => (I h.1, J h.2))
        (productSpace X Y) n).subtype.comp L =
      (P202Specs.ShuffleModel.shuffle R X Y n).comp (smoothTotalInclusion R I J X Y n) := by
  let L := (P202Specs.ShuffleModel.shuffle R X Y n).comp (smoothTotalInclusion R I J X Y n)
  have hL : ∀ z, L z ∈ smoothChains R (H := ModelProd H K)
      (fun h => (I h.1, J h.2)) (productSpace X Y) n := by
    intro z
    change shuffle R X Y n (smoothTotalInclusion R I J X Y n z) ∈ _
    rw [total_formula]
    apply Submodule.sum_mem
    intro i _
    apply smooth_castChains R _ _ i.property
    exact smooth_tensor R I J X Y i.val.1 i.val.2 (z i)
  exact ⟨L.codRestrict _ hL, rfl⟩
end Charts

end P202.ShuffleModel
