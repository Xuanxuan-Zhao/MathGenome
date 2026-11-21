import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.EilenbergZilber
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.AlexanderWhitney
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.ShuffleChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.EZProductHomotopy
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.EZTensorHomotopy

/-! Eilenberg–Zilber for the specified Alexander–Whitney and oriented shuffle
maps, with natural homotopies, smooth restrictions and relative compatibility. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory HomologicalComplex
open scoped TensorProduct
namespace P202.EilenbergZilber
open P202Specs.SingularChains P202Specs.AlexanderWhitney
open P202Specs.ShuffleModel P202Specs.EilenbergZilber
universe u w
variable (R : Type u) [CommRing R]

/-- Exactly the specified AW and oriented shuffle, with their proved chain
identities. This packages existing results and assumes no inverse property. -/
def comparison (X Y : TopCat.{w}) : Comparison R X Y where
  toTensor := P202.AlexanderWhitney.awChainMap R X Y
  fromTensor := ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (shuffle R X Y n)) (by
      intro n
      simp only [P202Specs.AlexanderWhitney.tensorComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      exact P202.ShuffleChains.chain_identity R X Y n)
  toTensor_f _ := rfl
  fromTensor_f _ := rfl

theorem comparison_exists : P202Specs.EilenbergZilber.comparison_type.{u,w} := by
  intro R _ X Y
  exact ⟨comparison R X Y⟩

/-- Naturality of the forward map as an equality of chain maps. -/
theorem comparison_toTensor_natural {X X' Y Y' : TopCat.{w}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    chainMap R R (productMap f g) ≫ (comparison R X' Y').toTensor =
      (comparison R X Y).toTensor ≫ P202.AlexanderWhitney.tensorChainMap R f g :=
  P202.AlexanderWhitney.awChainMap_natural R f g

/-- Naturality of the inverse candidate, before any homotopy assertion. -/
theorem comparison_fromTensor_natural {X X' Y Y' : TopCat.{w}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    P202.AlexanderWhitney.tensorChainMap R f g ≫ (comparison R X' Y').fromTensor =
      (comparison R X Y).fromTensor ≫ chainMap R R (productMap f g) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact (P202.ShuffleChains.naturality R f g n).symm

theorem naturalComparison : P202Specs.EilenbergZilber.naturalComparison_type.{u,w} := by
  intro R _
  refine ⟨comparison R, ?_, ?_⟩
  · intro X X' Y Y' f g n
    exact P202.AlexanderWhitney.naturality R f g n
  · intro X X' Y Y' f g n
    exact P202.ShuffleChains.naturality R f g n

/-- The nonnegative homology in the cycle formula is naturally the paper's
ordinary homology in every degree n ≥ 0. -/
theorem ordinaryHomologyIso_natural {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    (homologyFunctor R R (n : ℤ)).map f ≫ (ordinaryHomologyIso R Y n).hom =
      (ordinaryHomologyIso R X n).hom ≫ homologyMap (chainMap R R f) n := by
  exact HomologicalComplex.extendHomologyIso_hom_naturality (chainMap R R f)
    (degreeEmbedding 0) (by change (0 : ℤ) + (n : ℤ) = n; omega)

/-- Convert degree-raising components and the ordinary endpoint equations into
Mathlib's chain homotopy, without any nonnegative-degree truncation ambiguity. -/
def homotopyOfComponents {C D : ChainComplex (ModuleCat.{max u w} R) ℕ}
    (f g : C ⟶ D) (h : ∀ n, C.X n ⟶ D.X (n+1))
    (hz : f.f 0 = h 0 ≫ D.d 1 0 + g.f 0)
    (hs : ∀ n, f.f (n+1) = C.d (n+1) n ≫ h n +
      h (n+1) ≫ D.d (n+2) (n+1) + g.f (n+1)) : Homotopy f g where
  hom i j := if e : i+1 = j then h i ≫ eqToHom (congrArg D.X e) else 0
  zero i j hij := by
    change ¬(i+1 = j) at hij
    simp [hij]
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simpa using hz
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simpa using hs n

/-- Realize a natural product-side family as a chain homotopy. -/
def productHomotopy (h : ProductHomotopy.{u,w} R) (X Y : TopCat.{w}) :
    Homotopy ((comparison R X Y).toTensor ≫ (comparison R X Y).fromTensor)
      (𝟙 (complex R R (productSpace X Y))) :=
  homotopyOfComponents R _ _ (fun n => ModuleCat.ofHom (h.hom X Y n))
    (by
      apply ModuleCat.hom_ext
      change (shuffle R X Y 0).comp (aw R X Y 0) =
        (differential R (productSpace X Y) 0).comp (h.hom X Y 0) + LinearMap.id
      exact sub_eq_iff_eq_add.mp (h.zero X Y))
    (by
      intro n
      apply ModuleCat.hom_ext
      change (shuffle R X Y (n+1)).comp (aw R X Y (n+1)) =
        (h.hom X Y n).comp (differential R (productSpace X Y) n) +
        (differential R (productSpace X Y) (n+1)).comp (h.hom X Y (n+1)) + LinearMap.id
      rw [add_comm ((h.hom X Y n).comp _)]
      exact sub_eq_iff_eq_add.mp (h.succ X Y n))

/-- The corresponding assembly for the tensor-side homotopy. -/
def tensorHomotopy (h : TensorHomotopy.{u,w} R) (X Y : TopCat.{w}) :
    Homotopy ((comparison R X Y).fromTensor ≫ (comparison R X Y).toTensor)
      (𝟙 (tensorComplex R X Y)) :=
  homotopyOfComponents R _ _ (fun n => ModuleCat.ofHom (h.hom X Y n))
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      let c : Total R X Y 0 := z
      have hh := LinearMap.congr_fun (h.zero X Y) c
      change aw R X Y 0 (shuffle R X Y 0 c) - c =
        totalBoundary R X Y 0 (h.hom X Y 0 c) at hh
      change aw R X Y 0 (shuffle R X Y 0 c) =
        totalBoundary R X Y 0 (h.hom X Y 0 c) + c
      exact sub_eq_iff_eq_add.mp hh)
    (by
      intro n
      simp only [P202Specs.AlexanderWhitney.tensorComplex, ChainComplex.of.d,
        dite_true, eqToHom_refl, Category.id_comp]
      rw [dite_eq_left (show n+2 = n+1+1 from rfl)]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      let c : Total R X Y (n+1) := z
      have hh := LinearMap.congr_fun (h.succ X Y n) c
      change aw R X Y (n+1) (shuffle R X Y (n+1) c) - c =
        totalBoundary R X Y (n+1) (h.hom X Y (n+1) c) +
        h.hom X Y n (totalBoundary R X Y n c) at hh
      change aw R X Y (n+1) (shuffle R X Y (n+1) c) =
        h.hom X Y n (totalBoundary R X Y n c) +
        totalBoundary R X Y (n+1) (h.hom X Y (n+1) c) + c
      rw [add_comm (h.hom X Y n _)]
      exact sub_eq_iff_eq_add.mp hh)

/-- Assemble the two homotopies with exactly the prescribed comparison maps. -/
def equivalenceOfHomotopies (h : ProductHomotopy.{u,w} R) (k : TensorHomotopy.{u,w} R)
    (X Y : TopCat.{w}) :
    HomotopyEquiv (complex R R (productSpace X Y)) (tensorComplex R X Y) where
  hom := (comparison R X Y).toTensor
  inv := (comparison R X Y).fromTensor
  homotopyHomInvId := productHomotopy R h X Y
  homotopyInvHomId := tensorHomotopy R k X Y

theorem equivalence_of_naturalHomotopies
    (h : P202Specs.EilenbergZilber.naturalHomotopies_type.{u,w}) :
    P202Specs.EilenbergZilber.equivalence_type.{u,w} := by
  intro R _ X Y
  obtain ⟨h,k,_,_⟩ := h R
  exact ⟨equivalenceOfHomotopies R h k X Y, fun _ => rfl, fun _ => rfl⟩

/-- Both affine constructions provide the natural homotopies of the comparison. -/
theorem naturalHomotopies : P202Specs.EilenbergZilber.naturalHomotopies_type.{u,w} := by
  intro R _
  obtain ⟨h, hs⟩ := P202.EZProductHomotopy.naturalHomotopy.{u,w} R
  obtain ⟨k, ks⟩ := P202.EZTensorHomotopy.naturalHomotopy.{u,w,w,w,w,w} R
  exact ⟨h, k, hs, ks⟩

/-- The specified AW and oriented shuffle maps are chain homotopy inverses. -/
theorem equivalence : P202Specs.EilenbergZilber.equivalence_type.{u,w} :=
  equivalence_of_naturalHomotopies naturalHomotopies

section Subspaces
variable {A₁ A₂ B C D₁ D₂ : Type*}
  [AddCommGroup A₁] [Module R A₁] [AddCommGroup A₂] [Module R A₂]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  [AddCommGroup D₁] [Module R D₁] [AddCommGroup D₂] [Module R D₂]

private lemma map_sup_ranges_le
    {i₁ : A₁ →ₗ[R] B} {i₂ : A₂ →ₗ[R] B}
    {j₁ : D₁ →ₗ[R] C} {j₂ : D₂ →ₗ[R] C} {f : B →ₗ[R] C}
    (g₁ : A₁ →ₗ[R] D₁) (g₂ : A₂ →ₗ[R] D₂)
    (h₁ : f.comp i₁ = j₁.comp g₁) (h₂ : f.comp i₂ = j₂.comp g₂) :
    (LinearMap.range i₁ ⊔ LinearMap.range i₂).map f ≤
      LinearMap.range j₁ ⊔ LinearMap.range j₂ := by
  rw [Submodule.map_sup, ← LinearMap.range_comp, ← LinearMap.range_comp, h₁, h₂]
  exact sup_le_sup (LinearMap.range_comp_le_range _ _) (LinearMap.range_comp_le_range _ _)
end Subspaces

/-- Both maps and any natural choices of the stipulated homotopies preserve
C(A×Y)+C(X×B) and its total-tensor counterpart, for arbitrary subspaces. -/
theorem relativeCompatibility : P202Specs.EilenbergZilber.relativeCompatibility_type.{u,w} := by
  intro R _ h k X Y A B n
  unfold productPair tensorPair
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact map_sup_ranges_le R _ _
      (P202.AlexanderWhitney.naturality R (subspaceInclusion X A) (𝟙 Y) n).symm
      (P202.AlexanderWhitney.naturality R (𝟙 X) (subspaceInclusion Y B) n).symm
  · exact map_sup_ranges_le R _ _
      (P202.ShuffleChains.naturality R (subspaceInclusion X A) (𝟙 Y) n).symm
      (P202.ShuffleChains.naturality R (𝟙 X) (subspaceInclusion Y B) n).symm
  · exact map_sup_ranges_le R _ _
      (h.naturality (subspaceInclusion X A) (𝟙 Y) n).symm
      (h.naturality (𝟙 X) (subspaceInclusion Y B) n).symm
  · exact map_sup_ranges_le R _ _
      (k.naturality (subspaceInclusion X A) (𝟙 Y) n).symm
      (k.naturality (𝟙 X) (subspaceInclusion Y B) n).symm

section Smooth
variable {E F H K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]

/-- Taking a factor projection preserves the chart-local extension criterion. -/
lemma charts_fst {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N] (I : H → E) (J : K → F) {n : ℕ}
    (f : StdSimplex n → M × N)
    (hf : SmoothInCharts (H := ModelProd H K) (fun z => (I z.1, J z.2)) f) :
    SmoothInCharts I (fun z => (f z).1) := by
  refine ⟨continuous_fst.comp hf.1, ?_⟩
  intro z c hc hcz
  let d := chartAt K (f z).2
  have hcd : c.prod d ∈ atlas (ModelProd H K) (M × N) :=
    Set.mem_image2_of_mem hc (chart_mem_atlas K (f z).2)
  obtain ⟨U, hU, hz, G, hG, heq⟩ := hf.2 z (c.prod d) hcd
    ⟨hcz, mem_chart_source K (f z).2⟩
  refine ⟨U, hU, hz, fun a => (G a).1, hG.fst, ?_⟩
  intro x hx
  obtain ⟨hfx, hEq⟩ := heq x hx
  exact ⟨hfx.1, congrArg Prod.fst hEq⟩

lemma charts_snd {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N] (I : H → E) (J : K → F) {n : ℕ}
    (f : StdSimplex n → M × N)
    (hf : SmoothInCharts (H := ModelProd H K) (fun z => (I z.1, J z.2)) f) :
    SmoothInCharts J (fun z => (f z).2) := by
  refine ⟨continuous_snd.comp hf.1, ?_⟩
  intro z d hd hdz
  let c := chartAt H (f z).1
  have hcd : c.prod d ∈ atlas (ModelProd H K) (M × N) :=
    Set.mem_image2_of_mem (chart_mem_atlas H (f z).1) hd
  obtain ⟨U, hU, hz, G, hG, heq⟩ := hf.2 z (c.prod d) hcd
    ⟨mem_chart_source H (f z).1, hdz⟩
  refine ⟨U, hU, hz, fun a => (G a).2, hG.snd, ?_⟩
  intro x hx
  obtain ⟨hfx, hEq⟩ := heq x hx
  exact ⟨hfx.2, congrArg Prod.snd hEq⟩

lemma smooth_aw_faces (I : H → E) (J : K → F)
    (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y]
    {n : ℕ} (σ : Simplex (productSpace X Y) n)
    (hσ : SmoothSimplex (H := ModelProd H K) (fun z => (I z.1, J z.2))
      (productSpace X Y) σ) (i : Diagonal n) :
    SmoothSimplex I X
      (interval (postSimplex (firstProjection X Y) n σ) 0 i.val.1 (by have := i.property; omega)) ∧
    SmoothSimplex J Y
      (interval (postSimplex (secondProjection X Y) n σ) i.val.1 i.val.2
        (by have := i.property; omega)) := by
  constructor
  · unfold SmoothSimplex
    rw [P202.AlexanderWhitney.interval_continuous]
    change SmoothInCharts I (fun z =>
      (simplexEquiv (productSpace X Y) n σ (z.map
        (intervalInclusion 0 i.val.1 n (by have := i.property; omega)).toOrderHom)).1)
    exact P202.ShuffleModel.charts_pullback I _
      (charts_fst I J _ hσ) _
  · unfold SmoothSimplex
    rw [P202.AlexanderWhitney.interval_continuous]
    change SmoothInCharts J (fun z =>
      (simplexEquiv (productSpace X Y) n σ (z.map
        (intervalInclusion i.val.1 i.val.2 n (by have := i.property; omega)).toOrderHom)).2)
    exact P202.ShuffleModel.charts_pullback J _
      (charts_snd I J _ hσ) _

/-- Retraction onto the finite total tensor of the two supported submodules.
It is used only to construct the restriction; no injectivity of tensoring a
submodule is assumed. -/
def smoothTotalProjection (I : H → E) (J : K → F)
    (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y] (n : ℕ) :
    Total R X Y n →ₗ[R] SmoothTotal R I J X Y n := by
  classical
  exact
    { toFun := fun z i => TensorProduct.map
        (Finsupp.restrictDom R R {σ | SmoothSimplex I X σ})
        (Finsupp.restrictDom R R {τ | SmoothSimplex J Y τ}) (z i)
      map_add' := by intros; ext i; apply map_add
      map_smul' := by
        intro r z
        ext i
        change TensorProduct.map _ _ (r • z i) = r • _
        exact map_smul _ _ _ }

lemma smoothTotalProjection_inclusion (I : H → E) (J : K → F)
    (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y] (n : ℕ) :
    (smoothTotalProjection R I J X Y n).comp (smoothTotalInclusion R I J X Y n) =
      LinearMap.id := by
  classical
  apply LinearMap.ext
  intro z
  funext i
  change TensorProduct.map _ _ (TensorProduct.map _ _ (z i)) = z i
  simp only [TensorProduct.map_map, smoothChains, Finsupp.restrictDom_comp_subtype,
    TensorProduct.map_id, LinearMap.id_apply]

end Smooth

/-- The exact prescribed AW formula restricts to the tensor of the smooth
chain submodules, using affine interval faces and local extensions at corners. -/
theorem smoothAW : P202Specs.EilenbergZilber.smoothAW_type.{u,w} := by
  intro R _ E F H K _ _ _ _ _ _ I J X Y _ _ n
  classical
  let S := smoothChains R (H := ModelProd H K) (fun z => (I z.1, J z.2))
    (productSpace X Y) n
  let P := smoothTotalProjection R I J X Y n
  let L := (P.comp (aw R X Y n)).comp S.subtype
  refine ⟨L, ?_⟩
  apply LinearMap.ext
  intro c
  have hc : ((smoothTotalInclusion R I J X Y n).comp
      (P.comp (aw R X Y n)) - aw R X Y n) c.val = 0 := by
    apply P202.ShuffleModel.map_smoothChains R
      (H := ModelProd H K) (fun z => (I z.1, J z.2)) (productSpace X Y)
      ((smoothTotalInclusion R I J X Y n).comp
        (P.comp (aw R X Y n)) - aw R X Y n) (⊥ : Submodule R (Total R X Y n))
      ?_ c.val c.property
    intro σ hσ
    change ((smoothTotalInclusion R I J X Y n).comp
      (P.comp (aw R X Y n)) - aw R X Y n) (Finsupp.single σ 1) = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    funext i
    obtain ⟨hx,hy⟩ := smooth_aw_faces I J X Y σ hσ i
    simp only [LinearMap.comp_apply, smoothTotalInclusion, smoothTotalProjection,
      LinearMap.coe_mk, AddHom.coe_mk, P, P202.AlexanderWhitney.formula,
      one_smul, awComponent, TensorProduct.map_tmul]
    simp [Finsupp.restrictDom_apply, hx, hy]
  change smoothTotalInclusion R I J X Y n (P (aw R X Y n c.val)) = aw R X Y n c.val
  exact sub_eq_zero.mp hc

/-! The shuffle product of cycles and its behavior on boundaries, with the
ordinary degree-zero endpoints treated explicitly. -/

lemma boundary_shuffle_positive (X Y : TopCat.{w}) (p q : ℕ)
    (a : Chains R X (p+1)) (b : Chains R Y (q+1)) :
    boundary R R (productSpace X Y) (p+q+1)
      (castChains R (by omega : (p+1)+(q+1)=(p+q+1)+1)
        (shuffleComponent R X Y (p+1) (q+1) (a ⊗ₜ[R] b))) =
      castChains R (by omega : p+(q+1)=p+q+1)
        (shuffleComponent R X Y p (q+1) (boundary R R X p a ⊗ₜ[R] b)) +
      (-1 : ℤ)^(p+1) • castChains R (by omega : (p+1)+q=p+q+1)
        (shuffleComponent R X Y (p+1) q (a ⊗ₜ[R] boundary R R Y q b)) := by
  have h := LinearMap.congr_fun (P202.ShuffleChains.chain_identity R X Y (p+q+1))
    (Pi.single (⟨(p+1,q+1), by omega⟩ : Diagonal (p+q+1+1)) (a ⊗ₜ[R] b))
  change boundary R R (productSpace X Y) _
    (shuffle R X Y _ _) = shuffle R X Y _ (totalBoundary R X Y _ _) at h
  rw [P202.ShuffleBoundary.shuffle_single,
    P202.ShuffleBoundary.totalBoundary_single_positive,
    map_add, map_zsmul, P202.ShuffleBoundary.shuffle_single,
    P202.ShuffleBoundary.shuffle_single] at h
  exact h

lemma boundary_shuffle_zero_right (X Y : TopCat.{w}) (p : ℕ)
    (a : Chains R X (p+1)) (b : Chains R Y 0) :
    boundary R R (productSpace X Y) p
      (shuffleComponent R X Y (p+1) 0 (a ⊗ₜ[R] b)) =
    shuffleComponent R X Y p 0 (boundary R R X p a ⊗ₜ[R] b) := by
  have h := LinearMap.congr_fun (P202.ShuffleChains.chain_identity R X Y p)
    (Pi.single (⟨(p+1,0), rfl⟩ : Diagonal (p+1)) (a ⊗ₜ[R] b))
  change boundary R R (productSpace X Y) _
    (shuffle R X Y _ _) = shuffle R X Y _ (totalBoundary R X Y _ _) at h
  rw [P202.ShuffleBoundary.shuffle_single,
    P202.ShuffleBoundary.totalBoundary_single_zero_right,
    P202.ShuffleBoundary.shuffle_single] at h
  exact h

lemma boundary_shuffle_zero_left (X Y : TopCat.{w}) (q : ℕ)
    (a : Chains R X 0) (b : Chains R Y (q+1)) :
    boundary R R (productSpace X Y) q
      (castChains R (Nat.zero_add (q+1))
        (shuffleComponent R X Y 0 (q+1) (a ⊗ₜ[R] b))) =
    castChains R (Nat.zero_add q)
      (shuffleComponent R X Y 0 q (a ⊗ₜ[R] boundary R R Y q b)) := by
  have h := LinearMap.congr_fun (P202.ShuffleChains.chain_identity R X Y q)
    (Pi.single (⟨(0,q+1), by omega⟩ : Diagonal (q+1)) (a ⊗ₜ[R] b))
  change boundary R R (productSpace X Y) _
    (shuffle R X Y _ _) = shuffle R X Y _ (totalBoundary R X Y _ _) at h
  rw [P202.ShuffleBoundary.shuffle_single,
    P202.ShuffleBoundary.totalBoundary_single_zero_left,
    P202.ShuffleBoundary.shuffle_single] at h
  exact h

lemma cycle_cast_iff (X : TopCat.{w}) {n m : ℕ} (h : n=m)
    (c : Chains R X n) :
    ((complex R R X).d m (m-1) (castChains R h c) = 0) ↔
      (complex R R X).d n (n-1) c = 0 := by
  subst m
  rfl

lemma shuffle_cycles (X Y : TopCat.{w}) (p q : ℕ)
    (a : Chains R X p) (b : Chains R Y q)
    (ha : (complex R R X).d p (p-1) a = 0)
    (hb : (complex R R Y).d q (q-1) b = 0) :
    (complex R R (productSpace X Y)).d (p+q) (p+q-1)
      (shuffleComponent R X Y p q (a ⊗ₜ[R] b)) = 0 := by
  cases p with
  | zero =>
    cases q with
    | zero =>
      have h : (complex R R (productSpace X Y)).d 0 0 = 0 :=
        HomologicalComplex.shape _ _ _ (by simp [ComplexShape.down_Rel])
      rw [h]
      change (0 : Chains R (productSpace X Y) 0 →ₗ[R] _) _ = 0
      rfl
    | succ q =>
      have h := boundary_shuffle_zero_left R X Y q a b
      change boundary R R Y q b = 0 at hb
      apply (cycle_cast_iff R (productSpace X Y) (Nat.zero_add (q+1)) _).mp
      change boundary R R (productSpace X Y) q _ = 0
      simpa only [hb, TensorProduct.tmul_zero, map_zero] using h
  | succ p =>
    cases q with
    | zero =>
      change boundary R R X p a = 0 at ha
      have h := boundary_shuffle_zero_right R X Y p a b
      change boundary R R (productSpace X Y) p _ = 0
      simpa only [ha, TensorProduct.zero_tmul, map_zero] using h
    | succ q =>
      change boundary R R X p a = 0 at ha
      change boundary R R Y q b = 0 at hb
      have h := boundary_shuffle_positive R X Y p q a b
      apply (cycle_cast_iff R (productSpace X Y)
        (by omega : (p+1)+(q+1)=(p+q+1)+1) _).mp
      change boundary R R (productSpace X Y) (p+q+1) _ = 0
      simpa only [ha, hb, TensorProduct.tmul_zero, TensorProduct.zero_tmul, map_zero, smul_zero, zero_add] using h

lemma boundary_exists_cast_iff (X : TopCat.{w}) {n m : ℕ} (h : n=m)
    (c : Chains R X n) :
    (∃ z : Chains R X (m+1), boundary R R X m z = castChains R h c) ↔
      ∃ z : Chains R X (n+1), boundary R R X n z = c := by
  subst m
  rfl

lemma shuffle_boundary_left (X Y : TopCat.{w}) (p q : ℕ)
    (a : Chains R X (p+1)) (b : Chains R Y q)
    (hb : (complex R R Y).d q (q-1) b = 0) :
    ∃ z : Chains R (productSpace X Y) ((p+q)+1),
      boundary R R (productSpace X Y) (p+q) z =
        shuffleComponent R X Y p q (boundary R R X p a ⊗ₜ[R] b) := by
  cases q with
  | zero =>
    exact ⟨shuffleComponent R X Y (p+1) 0 (a ⊗ₜ[R] b),
      boundary_shuffle_zero_right R X Y p a b⟩
  | succ q =>
    change boundary R R Y q b = 0 at hb
    apply (boundary_exists_cast_iff R (productSpace X Y)
      (by omega : p+(q+1)=p+q+1) _).mp
    refine ⟨castChains R (by omega : (p+1)+(q+1)=(p+q+1)+1)
      (shuffleComponent R X Y (p+1) (q+1) (a ⊗ₜ[R] b)), ?_⟩
    have h := boundary_shuffle_positive R X Y p q a b
    simpa only [hb, TensorProduct.tmul_zero, map_zero, smul_zero, add_zero] using h

lemma shuffle_boundary_right (X Y : TopCat.{w}) (p q : ℕ)
    (a : Chains R X p) (b : Chains R Y (q+1))
    (ha : (complex R R X).d p (p-1) a = 0) :
    ∃ z : Chains R (productSpace X Y) ((p+q)+1),
      boundary R R (productSpace X Y) (p+q) z =
        shuffleComponent R X Y p q (a ⊗ₜ[R] boundary R R Y q b) := by
  cases p with
  | zero =>
    apply (boundary_exists_cast_iff R (productSpace X Y) (Nat.zero_add q) _).mp
    exact ⟨castChains R (Nat.zero_add (q+1))
      (shuffleComponent R X Y 0 (q+1) (a ⊗ₜ[R] b)),
        boundary_shuffle_zero_left R X Y q a b⟩
  | succ p =>
    change boundary R R X p a = 0 at ha
    apply (boundary_exists_cast_iff R (productSpace X Y)
      (by omega : (p+1)+q=p+q+1) _).mp
    refine ⟨(-1 : ℤ)^(p+1) • castChains R
      (by omega : (p+1)+(q+1)=(p+q+1)+1)
      (shuffleComponent R X Y (p+1) (q+1) (a ⊗ₜ[R] b)), ?_⟩
    have h := boundary_shuffle_positive R X Y p q a b
    simp only [ha, TensorProduct.zero_tmul, map_zero, zero_add] at h
    have hs : (-1 : ℤ)^(p+1) * (-1 : ℤ)^(p+1) = 1 := by
      rw [← mul_pow]
      simp
    rw [map_zsmul, h, smul_smul, hs, one_smul]

/-! Descent of the shuffle pairing through both homology quotients. -/
section HomologicalProduct
universe v
variable {R}

private def descCycles (S : ChainComplex (ModuleCat.{max u v} R) ℕ) (p : ℕ)
    {N : Type (max u v)} [AddCommGroup N] [Module R N]
    (F : S.cycles p →ₗ[R] N) (hF : ∀ x, F (S.toCycles (p+1) p x) = 0) :
    S.homology p →ₗ[R] N :=
  ((S.homologyIsCokernel (p+1) p (by simp)).desc
    (CategoryTheory.Limits.CokernelCofork.ofπ (ModuleCat.ofHom F)
      (by ext x; exact hF x))).hom

private lemma descCycles_π (S : ChainComplex (ModuleCat.{max u v} R) ℕ) (p : ℕ)
    {N : Type (max u v)} [AddCommGroup N] [Module R N]
    (F : S.cycles p →ₗ[R] N) (hF : ∀ x, F (S.toCycles (p+1) p x) = 0)
    (x : S.cycles p) : descCycles S p F hF (S.homologyπ p x) = F x := by
  exact CategoryTheory.congr_fun
    (CategoryTheory.Limits.Cofork.IsColimit.π_desc
      (S.homologyIsCokernel (p+1) p (by simp))
      (t := CategoryTheory.Limits.CokernelCofork.ofπ (ModuleCat.ofHom F)
        (by ext x; exact hF x))) x

private def descBilinearHomology (S T : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (p q : ℕ) {N : Type (max u v)} [AddCommGroup N] [Module R N]
    (F : S.cycles p →ₗ[R] T.cycles q →ₗ[R] N)
    (hF : ∀ x, F (S.toCycles (p+1) p x) = 0)
    (hF' : ∀ y, F.flip (T.toCycles (q+1) q y) = 0) :
    S.homology p →ₗ[R] T.homology q →ₗ[R] N := by
  let G := descCycles S p F hF
  have hG : ∀ y, G.flip (T.toCycles (q+1) q y) = 0 := by
    intro y
    ext a
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective (S.homologyπ p)).mp inferInstance a
    change G (S.homologyπ p x) (T.toCycles (q+1) q y) = 0
    rw [descCycles_π]
    exact LinearMap.congr_fun (hF' y) x
  exact (descCycles T q G.flip hG).flip

private lemma descBilinearHomology_π (S T : ChainComplex (ModuleCat.{max u v} R) ℕ)
    (p q : ℕ) {N : Type (max u v)} [AddCommGroup N] [Module R N]
    (F : S.cycles p →ₗ[R] T.cycles q →ₗ[R] N)
    (hF : ∀ x, F (S.toCycles (p+1) p x) = 0)
    (hF' : ∀ y, F.flip (T.toCycles (q+1) q y) = 0)
    (a : S.cycles p) (b : T.cycles q) :
    descBilinearHomology S T p q F hF hF' (S.homologyπ p a) (T.homologyπ q b) = F a b := by
  simp only [descBilinearHomology, LinearMap.flip_apply, descCycles_π]


variable (R)

private def cycleShuffle (X Y : TopCat.{w}) (p q : ℕ)
    (hc : ∀ (a : (complex R R X).cycles p) (b : (complex R R Y).cycles q),
      ((complex R R (productSpace X Y)).sc (p+q)).g
        (shuffleComponent R X Y p q
          ((complex R R X).iCycles p a ⊗ₜ[R] (complex R R Y).iCycles q b)) = 0) :
    (complex R R X).cycles p ⊗[R] (complex R R Y).cycles q →ₗ[R]
      (complex R R (productSpace X Y)).cycles (p+q) := by
  let raw := (shuffleComponent R X Y p q).comp (TensorProduct.map
    ((complex R R X).iCycles p).hom ((complex R R Y).iCycles q).hom)
  refine (((complex R R (productSpace X Y)).sc (p+q)).liftCycles
    (ModuleCat.ofHom raw) ?_).hom
  apply ModuleCat.hom_ext
  ext a b
  exact hc a b

private lemma cycleShuffle_i (X Y : TopCat.{w}) (p q : ℕ)
    (hc : ∀ (a : (complex R R X).cycles p) (b : (complex R R Y).cycles q),
      ((complex R R (productSpace X Y)).sc (p+q)).g
        (shuffleComponent R X Y p q
          ((complex R R X).iCycles p a ⊗ₜ[R] (complex R R Y).iCycles q b)) = 0)
    (a : (complex R R X).cycles p) (b : (complex R R Y).cycles q) :
    (complex R R (productSpace X Y)).iCycles (p+q)
      (cycleShuffle R X Y p q hc (a ⊗ₜ[R] b)) =
        shuffleComponent R X Y p q
          ((complex R R X).iCycles p a ⊗ₜ[R] (complex R R Y).iCycles q b) := by
  let raw := (shuffleComponent R X Y p q).comp (TensorProduct.map
    ((complex R R X).iCycles p).hom ((complex R R Y).iCycles q).hom)
  have heq : ModuleCat.ofHom (cycleShuffle R X Y p q hc) ≫
      (complex R R (productSpace X Y)).iCycles (p+q) = ModuleCat.ofHom raw := by
    exact ((complex R R (productSpace X Y)).sc (p+q)).liftCycles_i _ _
  exact CategoryTheory.congr_fun heq (a ⊗ₜ[R] b)


private lemma homologyπ_map_apply
    {K L : ChainComplex (ModuleCat.{max u v} R) ℕ} (f : K ⟶ L) (n : ℕ)
    (a : K.cycles n) :
    homologyMap f n (K.homologyπ n a) = L.homologyπ n (cyclesMap f n a) :=
  CategoryTheory.congr_fun (homologyπ_naturality f n) a

private lemma cyclesMap_i_apply
    {K L : ChainComplex (ModuleCat.{max u v} R) ℕ} (f : K ⟶ L) (n : ℕ)
    (a : K.cycles n) :
    L.iCycles n (cyclesMap f n a) = f.f n (K.iCycles n a) :=
  CategoryTheory.congr_fun (cyclesMap_i f n) a

private lemma toCycles_i_apply
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (i j : ℕ) (x : K.X i) :
    K.iCycles j (K.toCycles i j x) = K.d i j x :=
  CategoryTheory.congr_fun (K.toCycles_i i j) x

private lemma homologyπ_eq_zero_of_boundary
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (n : ℕ)
    (z : K.cycles n) (x : K.X (n+1))
    (h : K.iCycles n z = K.d (n+1) n x) : K.homologyπ n z = 0 := by
  have hz : z = K.toCycles (n+1) n x := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    rw [h]
    exact (CategoryTheory.congr_fun (K.toCycles_i (n+1) n) x).symm
  rw [hz]
  exact CategoryTheory.congr_fun (K.toCycles_comp_homologyπ (n+1) n) x

private lemma cycle_all_of_cycle
    (K : ChainComplex (ModuleCat.{max u v} R) ℕ) (n : ℕ) (a : K.X n)
    (ha : K.d n (n-1) a = 0) (j : ℕ) : K.d n j a = 0 := by
  by_cases h : j+1=n
  · have hj : j=n-1 := by omega
    rw [hj]
    exact ha
  · rw [K.shape n j (by simpa only [ComplexShape.down_Rel] using h)]
    rfl

private def shuffleCyclePairing (X Y : TopCat.{w}) (p q : ℕ) :
    (complex R R X).cycles p ⊗[R] (complex R R Y).cycles q →ₗ[R]
      (complex R R (productSpace X Y)).cycles (p+q) :=
  cycleShuffle R X Y p q (by
    intro a b
    apply cycle_all_of_cycle R (complex R R (productSpace X Y)) (p+q) _
    exact shuffle_cycles R X Y p q _ _
      (CategoryTheory.congr_fun ((complex R R X).iCycles_d p (p-1)) a)
      (CategoryTheory.congr_fun ((complex R R Y).iCycles_d q (q-1)) b))

private lemma shuffleCyclePairing_i (X Y : TopCat.{w}) (p q : ℕ)
    (a : (complex R R X).cycles p) (b : (complex R R Y).cycles q) :
    (complex R R (productSpace X Y)).iCycles (p+q)
      (shuffleCyclePairing R X Y p q (a ⊗ₜ[R] b)) =
        shuffleComponent R X Y p q
          ((complex R R X).iCycles p a ⊗ₜ[R] (complex R R Y).iCycles q b) :=
  cycleShuffle_i R X Y p q _ a b

private lemma shuffleCyclePairing_left (X Y : TopCat.{w}) (p q : ℕ)
    (x : (complex R R X).X (p+1)) (b : (complex R R Y).cycles q) :
    (complex R R (productSpace X Y)).homologyπ (p+q)
      (shuffleCyclePairing R X Y p q ((complex R R X).toCycles (p+1) p x ⊗ₜ[R] b)) = 0 := by
  obtain ⟨z, hz⟩ := shuffle_boundary_left R X Y p q x ((complex R R Y).iCycles q b)
    (CategoryTheory.congr_fun ((complex R R Y).iCycles_d q (q-1)) b)
  apply homologyπ_eq_zero_of_boundary R _ (p+q) _ z
  rw [shuffleCyclePairing_i,
    toCycles_i_apply R (complex R R X) (p+1) p x]
  exact hz.symm

private lemma shuffleCyclePairing_right (X Y : TopCat.{w}) (p q : ℕ)
    (a : (complex R R X).cycles p) (y : (complex R R Y).X (q+1)) :
    (complex R R (productSpace X Y)).homologyπ (p+q)
      (shuffleCyclePairing R X Y p q (a ⊗ₜ[R] (complex R R Y).toCycles (q+1) q y)) = 0 := by
  obtain ⟨z, hz⟩ := shuffle_boundary_right R X Y p q ((complex R R X).iCycles p a) y
    (CategoryTheory.congr_fun ((complex R R X).iCycles_d p (p-1)) a)
  apply homologyπ_eq_zero_of_boundary R _ (p+q) _ z
  rw [shuffleCyclePairing_i,
    toCycles_i_apply R (complex R R Y) (q+1) q y]
  exact hz.symm

private def homologyProductOfPairing
    (S : ∀ (X Y : TopCat.{w}) (p q : ℕ),
      (complex R R X).cycles p ⊗[R] (complex R R Y).cycles q →ₗ[R]
        (complex R R (productSpace X Y)).cycles (p+q))
    (hL : ∀ (X Y : TopCat.{w}) (p q : ℕ)
      (x : (complex R R X).X (p+1)) (b : (complex R R Y).cycles q),
      (complex R R (productSpace X Y)).homologyπ (p+q)
        (S X Y p q ((complex R R X).toCycles (p+1) p x ⊗ₜ[R] b)) = 0)
    (hR : ∀ (X Y : TopCat.{w}) (p q : ℕ)
      (a : (complex R R X).cycles p) (y : (complex R R Y).X (q+1)),
      (complex R R (productSpace X Y)).homologyπ (p+q)
        (S X Y p q (a ⊗ₜ[R] (complex R R Y).toCycles (q+1) q y)) = 0)
    (X Y : TopCat.{w}) (p q : ℕ) :
    (complex R R X).homology p ⊗[R] (complex R R Y).homology q →ₗ[R]
      (complex R R (productSpace X Y)).homology (p+q) := by
  let F := TensorProduct.curry (((complex R R (productSpace X Y)).homologyπ (p+q)).hom.comp
    (S X Y p q))
  exact TensorProduct.lift (descBilinearHomology (complex R R X)
    (complex R R Y) p q F
    (by intro x; apply LinearMap.ext; intro b; exact hL X Y p q x b)
    (by intro y; apply LinearMap.ext; intro a; exact hR X Y p q a y))

private lemma homologyProductOfPairing_π
    (S : ∀ (X Y : TopCat.{w}) (p q : ℕ),
      (complex R R X).cycles p ⊗[R] (complex R R Y).cycles q →ₗ[R]
        (complex R R (productSpace X Y)).cycles (p+q))
    (hL : ∀ (X Y : TopCat.{w}) (p q : ℕ)
      (x : (complex R R X).X (p+1)) (b : (complex R R Y).cycles q),
      (complex R R (productSpace X Y)).homologyπ (p+q)
        (S X Y p q ((complex R R X).toCycles (p+1) p x ⊗ₜ[R] b)) = 0)
    (hR : ∀ (X Y : TopCat.{w}) (p q : ℕ)
      (a : (complex R R X).cycles p) (y : (complex R R Y).X (q+1)),
      (complex R R (productSpace X Y)).homologyπ (p+q)
        (S X Y p q (a ⊗ₜ[R] (complex R R Y).toCycles (q+1) q y)) = 0)
    (X Y : TopCat.{w}) (p q : ℕ)
    (a : (complex R R X).cycles p) (b : (complex R R Y).cycles q) :
    homologyProductOfPairing R S hL hR X Y p q
      ((complex R R X).homologyπ p a ⊗ₜ[R] (complex R R Y).homologyπ q b) =
      (complex R R (productSpace X Y)).homologyπ (p+q) (S X Y p q (a ⊗ₜ[R] b)) := by
  simp only [homologyProductOfPairing, TensorProduct.lift.tmul]
  rw [descBilinearHomology_π]
  rfl


private def externalMap (X Y : TopCat.{w}) (p q : ℕ) :
    (complex R R X).homology p ⊗[R] (complex R R Y).homology q →ₗ[R]
      (complex R R (productSpace X Y)).homology (p+q) :=
  homologyProductOfPairing R (shuffleCyclePairing R)
    (shuffleCyclePairing_left R) (shuffleCyclePairing_right R) X Y p q

private lemma externalMap_π (X Y : TopCat.{w}) (p q : ℕ)
    (a : (complex R R X).cycles p) (b : (complex R R Y).cycles q) :
    externalMap R X Y p q
      ((complex R R X).homologyπ p a ⊗ₜ[R] (complex R R Y).homologyπ q b) =
      (complex R R (productSpace X Y)).homologyπ (p+q)
        (shuffleCyclePairing R X Y p q (a ⊗ₜ[R] b)) :=
  homologyProductOfPairing_π R (shuffleCyclePairing R)
    (shuffleCyclePairing_left R) (shuffleCyclePairing_right R) X Y p q a b

private lemma shuffleCyclePairing_natural
    {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (p q : ℕ)
    (a : (complex R R X).cycles p) (b : (complex R R Y).cycles q) :
    cyclesMap (chainMap R R (productMap f g)) (p+q)
      (shuffleCyclePairing R X Y p q (a ⊗ₜ[R] b)) =
      shuffleCyclePairing R X' Y' p q
        (cyclesMap (chainMap R R f) p a ⊗ₜ[R] cyclesMap (chainMap R R g) q b) := by
  apply (ModuleCat.mono_iff_injective
    ((complex R R (productSpace X' Y')).iCycles (p+q))).mp inferInstance
  rw [cyclesMap_i_apply, shuffleCyclePairing_i, shuffleCyclePairing_i,
    cyclesMap_i_apply, cyclesMap_i_apply]
  exact LinearMap.congr_fun (P202.ShuffleChains.component_natural R f g p q)
    ((complex R R X).iCycles p a ⊗ₜ[R] (complex R R Y).iCycles q b)

/-- The homological product determined by the specified shuffle on every cycle representative. -/
def externalProductData : P202Specs.EilenbergZilber.ExternalProduct.{u,w} R where
  map := externalMap R
  represents X Y p q a b :=
    ⟨shuffleCyclePairing R X Y p q (a ⊗ₜ[R] b),
      shuffleCyclePairing_i R X Y p q a b, externalMap_π R X Y p q a b⟩
  naturality {X X' Y Y'} f g p q := by
    ext a b
    change homologyMap (chainMap R R (productMap f g)) (p+q)
      (externalMap R X Y p q (a ⊗ₜ[R] b)) =
        externalMap R X' Y' p q
          (TensorProduct.map (homologyMap (chainMap R R f) p).hom
            (homologyMap (chainMap R R g) q).hom (a ⊗ₜ[R] b))
    obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective ((complex R R X).homologyπ p)).mp
      inferInstance a
    obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective ((complex R R Y).homologyπ q)).mp
      inferInstance b
    rw [TensorProduct.map_tmul, externalMap_π]
    have hf : (homologyMap (chainMap R R f) p).hom ((complex R R X).homologyπ p a) =
        (complex R R X').homologyπ p (cyclesMap (chainMap R R f) p a) :=
      homologyπ_map_apply R (chainMap R R f) p a
    have hg : (homologyMap (chainMap R R g) q).hom ((complex R R Y).homologyπ q b) =
        (complex R R Y').homologyπ q (cyclesMap (chainMap R R g) q b) :=
      homologyπ_map_apply R (chainMap R R g) q b
    rw [hf, hg, externalMap_π,
      homologyπ_map_apply R (chainMap R R (productMap f g)) (p+q),
      shuffleCyclePairing_natural]

theorem externalProduct : P202Specs.EilenbergZilber.externalProduct_type.{u,w} := by
  intro R _
  exact ⟨externalProductData R⟩


end HomologicalProduct

end P202.EilenbergZilber
