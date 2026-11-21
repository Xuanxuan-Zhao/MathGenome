import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.BoundaryRegularLevels
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.RegularLevels
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.BoundaryInverse
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.BoundaryCones
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! Boundary regular levels: full and boundary tangent formulas, dimension
bounds, natural boundary structures, and the necessity counterexample.
The fiber structure uses normal-coordinate-preserving local charts on its
actual subspace, including positive-codimension boundary fibers. -/
set_option autoImplicit false
set_option linter.unusedVariables false
open Set Filter
open scoped Topology ContDiff
namespace SmoothManifolds.BoundaryConstruction
open ModelData AtlasData MapData BoundaryData FiniteRegularityData

/-- Complete a surjective map by coordinates on its kernel. -/
theorem exists_linear_complement {m n : ℕ} (L : Euclidean m →L[ℝ] Euclidean n)
    (hL : Function.Surjective L) :
    ∃ K : Euclidean m →L[ℝ] Euclidean (m-n), Function.Bijective (K.prod L) := by
  classical
  obtain ⟨R, hR⟩ := L.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hL)
  have hR' (w : Euclidean n) : L (R w) = w := LinearMap.congr_fun hR w
  have hdim : Module.finrank ℝ L.ker = m - n := by
    have h := LinearMap.finrank_range_add_finrank_ker L.toLinearMap
    rw [LinearMap.range_eq_top.mpr hL, finrank_top,
      Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    omega
  let E : L.ker ≃L[ℝ] Euclidean (m-n) :=
    ContinuousLinearEquiv.ofFinrankEq (hdim.trans (Module.finrank_fin_fun ℝ).symm)
  let P : Euclidean m →ₗ[ℝ] L.ker := {
    toFun := fun z => ⟨z - R (L z), by simp [hR']⟩
    map_add' := by intro x y; apply Subtype.ext; simp; abel
    map_smul' := by intro a x; apply Subtype.ext; simp [smul_sub] }
  let K : Euclidean m →L[ℝ] Euclidean (m-n) := E.toContinuousLinearMap.comp P.toContinuousLinearMap
  refine ⟨K, ?_, ?_⟩
  · intro x y hxy
    have hK : P x = P y := E.injective (congrArg Prod.fst hxy)
    have hP := congrArg Subtype.val hK
    have hLxy : L x = L y := congrArg Prod.snd hxy
    change x - R (L x) = y - R (L y) at hP
    rw [hLxy] at hP
    exact sub_left_inj.mp hP
  · rintro ⟨u,w⟩
    refine ⟨(E.symm u).val + R w, ?_⟩
    have hz : L (E.symm u).val = 0 := (E.symm u).property
    apply Prod.ext
    · change E (P ((E.symm u).val + R w)) = u
      apply E.symm.injective
      rw [E.symm_apply_apply]
      apply Subtype.ext
      change (E.symm u).val + R w - R (L ((E.symm u).val + R w)) = (E.symm u).val
      simp only [map_add, hz, hR', zero_add]
      abel
    · change L ((E.symm u).val + R w) = w
      simp only [map_add, hz, hR', zero_add]



/-- Append coordinate blocks, as a continuous linear equivalence. -/
noncomputable def appendEquiv (n k : ℕ) :
    (Euclidean n × Euclidean k) ≃L[ℝ] Euclidean (n+k) :=
  ({ toFun := fun z => Fin.append z.1 z.2
     invFun := fun z => (fun i => z (Fin.castAdd k i), fun i => z (Fin.natAdd n i))
     left_inv := by intro z; apply Prod.ext <;> funext i <;> simp
     right_inv := by
       intro z; funext i
       refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
     map_add' := by
       intro x y; funext i
       refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
     map_smul' := by
       intro a x; funext i
       refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp } :
    (Euclidean n × Euclidean k) ≃ₗ[ℝ] Euclidean (n+k)).toContinuousLinearEquiv

@[simp] theorem appendEquiv_apply (n k : ℕ) (z : Euclidean n × Euclidean k) :
    appendEquiv n k z = Fin.append z.1 z.2 := rfl

/-- Split off the final real coordinate. -/
noncomputable def snocEquiv (m : ℕ) :
    (Euclidean m × ℝ) ≃L[ℝ] Euclidean (m+1) :=
  ({ toFun := fun z => Fin.snoc z.1 z.2
     invFun := fun z => (Fin.init z, z (Fin.last m))
     left_inv := by intro z; apply Prod.ext <;> simp
     right_inv := by intro z; exact Fin.snoc_init_self z
     map_add' := by
       intro x y; funext i
       refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
     map_smul' := by
       intro a x; funext i
       refine Fin.lastCases ?_ (fun j => ?_) i <;> simp } :
    (Euclidean m × ℝ) ≃ₗ[ℝ] Euclidean (m+1)).toContinuousLinearEquiv

@[simp] theorem snocEquiv_apply (m : ℕ) (z : Euclidean m × ℝ) :
    snocEquiv m z = Fin.snoc z.1 z.2 := rfl


/-- Coordinate change with unchanged final coordinate. -/
def boundaryChange {n k : ℕ}
    (g : Euclidean ((n+k)+1) → Euclidean n)
    (K : Euclidean (n+k) →L[ℝ] Euclidean k) (z : Euclidean ((n+k)+1)) :
    Euclidean ((n+k)+1) :=
  Fin.snoc (Fin.append (g z) (K (Fin.init z))) (z (Fin.last (n+k)))

/-- The derivative coordinate change. -/
noncomputable def boundaryLinear {n k : ℕ}
    (L : Euclidean ((n+k)+1) →L[ℝ] Euclidean n)
    (K : Euclidean (n+k) →L[ℝ] Euclidean k) :
    Euclidean ((n+k)+1) →L[ℝ] Euclidean ((n+k)+1) :=
  let drop : Euclidean ((n+k)+1) →L[ℝ] Euclidean (n+k) :=
    (ContinuousLinearMap.fst ℝ (Euclidean (n+k)) ℝ).comp (snocEquiv (n+k)).symm.toContinuousLinearMap
  let normal : Euclidean ((n+k)+1) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (Euclidean (n+k)) ℝ).comp (snocEquiv (n+k)).symm.toContinuousLinearMap
  (snocEquiv (n+k)).toContinuousLinearMap.comp
    (((appendEquiv n k).toContinuousLinearMap.comp (L.prod (K.comp drop))).prod normal)

@[simp] theorem boundaryLinear_apply {n k : ℕ}
    (L : Euclidean ((n+k)+1) →L[ℝ] Euclidean n)
    (K : Euclidean (n+k) →L[ℝ] Euclidean k) (z : Euclidean ((n+k)+1)) :
    boundaryLinear L K z = boundaryChange L K z := rfl

lemma snoc_init_zero_eq {m : ℕ} (x : Euclidean (m+1)) :
    Fin.snoc (Fin.init x) 0 = x - x (Fin.last m) • Fin.snoc (0 : Euclidean m) 1 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Fin.init]

lemma snoc_eq_add {m : ℕ} (x : Euclidean m) (t : ℝ) :
    (Fin.snoc x t : Euclidean (m+1)) = Fin.snoc x 0 + Fin.snoc (0 : Euclidean m) t := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- Tangential row rank suffices to complete the derivative without moving s. -/
theorem exists_boundary_linear {n k : ℕ}
    (L : Euclidean ((n+k)+1) →L[ℝ] Euclidean n)
    (hs : Function.Surjective (fun x : Euclidean (n+k) => L (Fin.snoc x 0))) :
    ∃ K : Euclidean (n+k) →L[ℝ] Euclidean k,
      Function.Bijective (boundaryLinear L K) := by
  let I : Euclidean (n+k) →L[ℝ] Euclidean ((n+k)+1) :=
    (snocEquiv (n+k)).toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ (Euclidean (n+k)) ℝ)
  let L₀ := L.comp I
  have hs₀ : Function.Surjective L₀ := hs
  obtain ⟨K, hK⟩ : ∃ K : Euclidean (n+k) →L[ℝ] Euclidean k,
      Function.Bijective (K.prod L₀) := by
    have heq : n+k-n = k := by omega
    have h := exists_linear_complement (m:=n+k) (n:=n) L₀ hs₀
    rw [heq] at h
    exact h
  refine ⟨K, ?_, ?_⟩
  · intro x y hxy
    have hpair : (L x, K (Fin.init x)) = (L y, K (Fin.init y)) := by
      apply (appendEquiv n k).injective
      simpa only [appendEquiv_apply, boundaryLinear_apply, boundaryChange, Fin.init_snoc] using
        congrArg (fun z : Euclidean ((n+k)+1) => Fin.init z) hxy
    have ht : x (Fin.last (n+k)) = y (Fin.last (n+k)) := by
      simpa only [boundaryLinear_apply, boundaryChange, Fin.snoc_last] using
        congrArg (fun z : Euclidean ((n+k)+1) => z (Fin.last (n+k))) hxy
    have h0 : L₀ (Fin.init x) = L₀ (Fin.init y) := by
      change L (Fin.snoc (Fin.init x) 0) = L (Fin.snoc (Fin.init y) 0)
      have hLxy : L x = L y := congrArg Prod.fst hpair
      rw [snoc_init_zero_eq, snoc_init_zero_eq, map_sub, map_sub, map_smul, map_smul,
        hLxy, ht]
    have hi : Fin.init x = Fin.init y := hK.1 (Prod.ext (congrArg Prod.snd hpair) h0)
    rw [← Fin.snoc_init_self x, ← Fin.snoc_init_self y, hi, ht]
  · intro z
    let w : Euclidean n := fun i => z (Fin.castSucc (Fin.castAdd k i))
    let v : Euclidean k := fun i => z (Fin.castSucc (Fin.natAdd n i))
    let t : ℝ := z (Fin.last (n+k))
    obtain ⟨x, hx⟩ := hK.2 (v, w - L (Fin.snoc (0 : Euclidean (n+k)) t))
    have hKx : K x = v := congrArg Prod.fst hx
    have hLx : L₀ x = w - L (Fin.snoc (0 : Euclidean (n+k)) t) := congrArg Prod.snd hx
    refine ⟨Fin.snoc x t, ?_⟩
    have hLxt : L (Fin.snoc x t) = w := by
      rw [snoc_eq_add, map_add]
      change L₀ x + L (Fin.snoc (0 : Euclidean (n+k)) t) = w
      rw [hLx, sub_add_cancel]
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [boundaryLinear_apply, boundaryChange, Fin.snoc_last, t]
    · simp only [boundaryLinear_apply, boundaryChange, Fin.snoc_castSucc]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · rw [Fin.append_left, hLxt]
      · rw [Fin.append_right, Fin.init_snoc, hKx]



/-- Boundary submersion coordinates with the last coordinate unchanged. -/
theorem euclidean_boundary_coordinates {n k : ℕ}
    (g : Euclidean ((n+k)+1) → Euclidean n)
    (U : Set (Euclidean ((n+k)+1))) (hU : IsOpen U)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (p : Euclidean ((n+k)+1)) (hp : p ∈ U)
    (L : Euclidean ((n+k)+1) →L[ℝ] Euclidean n) (hL : HasFDerivAt g L p)
    (hs : Function.Surjective (fun x : Euclidean (n+k) => L (Fin.snoc x 0))) :
    ∃ j : OpenPartialHomeomorph (Euclidean ((n+k)+1)) (Euclidean ((n+k)+1)),
      p ∈ j.source ∧ j.source ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) j j.source ∧ ContDiffOn ℝ (⊤ : ℕ∞) j.symm j.target ∧
      (∀ z, j z (Fin.last (n+k)) = z (Fin.last (n+k))) ∧
      ∀ z (i : Fin n), j z (Fin.castSucc (Fin.castAdd k i)) = (g z - g p) i := by
  obtain ⟨K, hK⟩ := exists_boundary_linear L hs
  let D : Euclidean ((n+k)+1) →L[ℝ] Euclidean (n+k) :=
    (ContinuousLinearMap.fst ℝ (Euclidean (n+k)) ℝ).comp (snocEquiv (n+k)).symm.toContinuousLinearMap
  let N : Euclidean ((n+k)+1) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (Euclidean (n+k)) ℝ).comp (snocEquiv (n+k)).symm.toContinuousLinearMap
  let H := boundaryChange (fun z => g z - g p) K
  have hHs : ContDiffOn ℝ (⊤ : ℕ∞) H U :=
    (snocEquiv (n+k)).contDiff.comp_contDiffOn
      (((appendEquiv n k).contDiff.comp_contDiffOn
        ((hg.sub contDiffOn_const).prodMk (K.contDiff.comp D.contDiff).contDiffOn)).prodMk N.contDiff.contDiffOn)
  have hHD : HasFDerivAt H (boundaryLinear L K) p :=
    (snocEquiv (n+k)).hasFDerivAt.comp p
      (((appendEquiv n k).hasFDerivAt.comp p
        ((hL.sub_const (g p)).prodMk (K.hasFDerivAt.comp p D.hasFDerivAt))).prodMk N.hasFDerivAt)
  obtain ⟨j₀, hpj₀, hj₀, hji₀⟩ :=
    InteriorInverse.euclidean_inverse ⊤ le_top H U hU hHs p hp (boundaryLinear L K) hHD hK
  let j := j₀.restrOpen U hU
  refine ⟨j, ⟨hpj₀,hp⟩, fun _ hz => hz.2, ?_, ?_, ?_, ?_⟩
  · exact (hj₀ ▸ hHs).mono inter_subset_right
  · exact hji₀.mono inter_subset_left
  · intro z
    change j₀ z (Fin.last (n+k)) = z (Fin.last (n+k))
    rw [hj₀]
    exact Fin.snoc_last _ _
  · intro z i
    change j₀ z (Fin.castSucc (Fin.castAdd k i)) = (g z - g p) i
    rw [hj₀]
    exact (Fin.snoc_castSucc _ _ _).trans (Fin.append_left _ _ _)

end SmoothManifolds.BoundaryConstruction

namespace SmoothManifolds.BoundaryRegularLevels
open ModelData AtlasData MapData BoundaryData MapClassData FiniteRegularityData
  TangentData DifferentialData BoundaryRegularLevelData InteriorRankData
  RegularLevelData SliceData Set Filter
open scoped Topology
universe u v

/-- A boundary atlas always exists, even when the source dimension is zero. -/
theorem natural_boundary_exists_proof :
    Specs.SmoothManifolds.Ch03.BoundaryRegularLevels.natural_boundary_existsType.{u} := by
  intro m a M _ S
  cases m with
  | zero =>
    letI := S.topologicalManifold.hausdorff
    letI := S.topologicalManifold.secondCountable
    have he (p : intrinsicBoundary S) : False := by
      exact (Set.ext_iff.mp (intrinsicBoundary_zero S) p.val).mp p.property
    have hA : IsContDiffAtlas (⊤ : ℕ∞)
        (∅ : Set (ModelChart 0 .euclidean (intrinsicBoundary S))) := by
      refine ⟨?_, ?_⟩
      · intro p; exact (he p).elim
      · intro c hc; exact hc.elim
    let B : SmoothManifold 0 .euclidean (intrinsicBoundary S) := {
      topologicalManifold := ⟨inferInstance, inferInstance, ∅, hA.1⟩
      smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) ∅, maximalExtension_isMaximal hA⟩ }
    exact ⟨B, (fun p => (he p).elim), trivial⟩
  | succ r =>
    obtain ⟨B, hB, hface⟩ := exists_boundary_smoothManifold S
    exact ⟨B, hB, hface⟩

/-- Surjectivity of the full differential bounds dimensions in either model,
including at a boundary point. No interior hypothesis is used. -/
theorem submersionAt_dimension_le {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N) (p : M)
    (h : IsSubmersionAt S T f p) : n ≤ m := by
  obtain ⟨hf, F, G, hh⟩ := h
  letI := F.group; letI := F.module; letI := G.group; letI := G.module
  obtain ⟨L, hL, hs⟩ := hh
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p)
  have hsur := (MapClasses.differential_chart_invariants S T f p F G e d
    he hd hp hfp L hL).2.2.mp hs
  simpa using LinearMap.finrank_le_finrank_of_surjective
    (f := (chartDerivative e d f p).toLinearMap) hsur

/-- The differential of a constant map is zero directly on smooth germs. -/
theorem constant_differential {m n : ℕ} {a b : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N) (p : M)
    (hconst : ∀ x, f x = f p) : IsDifferential S T f p 0 := by
  intro w h k r hr hk
  have he : k = algebraMap ℝ (SmoothGerm S p) (r (f p)) := by
    apply Subtype.ext
    rw [← hk]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (fun x => congrArg r (hconst x))
  change 0 = w.val k
  rw [he, derivation_kills_constants]

/-- Inclusion of any smooth fiber annihilates the ambient differential.
This works at faces and retains the full germ-derivation tangent spaces. -/
theorem fiber_range_le_kernel {m n k : ℕ} {a b c : ModelKind}
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (y : N) (R : SmoothManifold k c (f ⁻¹' {y}))
    (hi : IsSmoothMap R S Subtype.val) (p : f ⁻¹' {y})
    (L : TangentSpace S p.val →ₗ[ℝ] TangentSpace T (f p.val))
    (K : TangentSpace R p →ₗ[ℝ] TangentSpace S p.val)
    (hL : IsDifferential S T f p.val L) (hK : IsDifferential R S Subtype.val p K) :
    LinearMap.range K ≤ LinearMap.ker L := by
  have hc := differential_comp R S T Subtype.val f hi hf p K L hK hL
  have hz : IsDifferential R T (f ∘ Subtype.val) p 0 :=
    constant_differential R T (f ∘ Subtype.val) p
      (fun x => (mem_singleton_iff.mp x.property).trans
        (mem_singleton_iff.mp p.property).symm)
  have hsmooth := manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ S.smoothStructure.property.1.1 Subtype.val f hi hf
  have heq : L.comp K = 0 := (differential_exists R T _ hsmooth p).unique hc hz
  rintro z ⟨w, rfl⟩
  change L (K w) = 0
  exact congrArg (fun A : TangentSpace R p →ₗ[ℝ] TangentSpace T (f p.val) => A w) heq

/-- Rank-nullity finishes the full tangent equality after construction of an
embedding of the expected dimension. Boundary regularity is not needed here. -/
theorem regular_fiber_tangent_proof :
    Specs.SmoothManifolds.Ch03.BoundaryRegularLevels.regular_fiber_tangentType.{u} := by
  intro m n a b c M N _ _ S T f hf y hy R hR p L K hL hK
  have hi : Function.Injective K :=
    (MapClasses.smooth_tangent_invariants R S Subtype.val hR.1 p K hK).2.1.mp
      (hR.2.2.1 p)
  have hs : Function.Surjective L :=
    (MapClasses.smooth_tangent_invariants S T f hf p.val L hL).2.2.mp
      (hy p.val (mem_singleton_iff.mp p.property))
  letI : AddCommGroup (TangentSpace R p) := Module.addCommMonoidToAddCommGroup ℝ
  letI : AddCommGroup (TangentSpace S p.val) := Module.addCommMonoidToAddCommGroup ℝ
  letI : AddCommGroup (TangentSpace T (f p.val)) := Module.addCommMonoidToAddCommGroup ℝ
  have hRdim := tangent_dimension R p
  have hSdim := tangent_dimension S p.val
  have hTdim := tangent_dimension T (f p.val)
  letI := hRdim.1; letI := hSdim.1; letI := hTdim.1
  have hle : LinearMap.range K ≤ LinearMap.ker L :=
    fiber_range_le_kernel S T f hf y R hR.1 p L K hL hK
  have hdim := L.finrank_range_add_finrank_ker
  have htop : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hs
  rw [htop, finrank_top, hSdim.2, hTdim.2] at hdim
  have heq : Module.finrank ℝ (LinearMap.range K) = Module.finrank ℝ (LinearMap.ker L) := by
    rw [LinearMap.finrank_range_of_inj hi, hRdim.2]
    omega
  exact ⟨hi, Submodule.eq_of_le_of_finrank_eq hle heq⟩


/-- The dimension and emptiness alternatives use the actual full tangent ranks. -/
theorem regular_fiber_dimension_proof :
    Specs.SmoothManifolds.Ch03.BoundaryRegularLevels.regular_fiber_dimensionType.{u,v} := by
  intro m n a b M N _ _ S T f B hB hT hf y hy hyB
  have hdim : (f ⁻¹' {y}).Nonempty → n ≤ m := by
    rintro ⟨p, hp⟩
    exact submersionAt_dimension_le S T f p (hy p (mem_singleton_iff.mp hp))
  refine ⟨hdim, ?_, ?_⟩
  · intro hlt
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact (Nat.not_le_of_gt hlt) (hdim ⟨p, hp⟩)
  · rintro ⟨p, hp, hpb⟩
    have hm : 0 < m := by
      by_contra hn
      have hm0 : m = 0 := by omega
      subst m
      have hh := (Set.ext_iff.mp (intrinsicBoundary_zero S) p).mp hpb
      exact hh
    exact ⟨hm, submersionAt_dimension_le B T (fun q => f q.val) ⟨p, hpb⟩
      (hyB ⟨p, hpb⟩ (mem_singleton_iff.mp hp))⟩

/-- The zero fiber in the necessity example is exactly one point. -/
theorem parabola_zero_fiber : parabolaMap ⁻¹' {0} = {origin} := by
  ext p
  change parabolaMap p = 0 ↔ p = origin
  constructor
  · intro h
    have hs : 0 ≤ p.val 1 := p.property
    have hx : p.val 0 = 0 := by
      have hsq := sq_nonneg (p.val 0)
      dsimp [parabolaMap] at h
      have hsqzero : p.val 0 ^ 2 = 0 := by linarith
      exact sq_eq_zero_iff.mp hsqzero
    have hs0 : p.val 1 = 0 := by simpa [parabolaMap, hx] using h
    apply Subtype.ext
    ext i
    fin_cases i <;> simp_all [origin]
  · rintro rfl
    norm_num [parabolaMap, origin]

/-- Even an arbitrary relatively open subset of H¹ has no isolated point. -/
theorem halfSpace_one_not_open_singleton (x : HalfSpace 1) :
    ¬ IsOpen ({x} : Set (HalfSpace 1)) := by
  intro h
  let line : ℝ → HalfSpace 1 := fun t => ⟨fun i => x.val i + t ^ 2, by
    change 0 ≤ x.val 0 + t ^ 2
    exact add_nonneg x.property (sq_nonneg t)⟩
  have hc : Continuous line := by
    apply Continuous.subtype_mk
    fun_prop
  have hl0 : line 0 = x := by ext i; simp [line]
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ), line t = x := by
    have hh := hc.continuousAt.preimage_mem_nhds (show {x} ∈ 𝓝 (line 0) by
      rw [hl0]; exact h.mem_nhds (mem_singleton x))
    change ∀ᶠ t : ℝ in 𝓝 0, line t ∈ ({x} : Set (HalfSpace 1)) at hh
    exact Filter.Eventually.mono hh (fun t ht => mem_singleton_iff.mp ht)
  have hright : ∀ᶠ t in 𝓝[Ioi (0 : ℝ)] 0, line t = x :=
    hevent.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, hpos⟩ := (hright.and self_mem_nhdsWithin).exists
  have hh := congrArg (fun z : HalfSpace 1 => z.val 0) ht
  change x.val 0 + t ^ 2 = x.val 0 at hh
  nlinarith [sq_pos_of_pos hpos]

/-- A singleton zero fiber cannot even carry one nonempty H¹ chart. -/
theorem parabola_no_halfSpace_chart (p : parabolaMap ⁻¹' {0}) :
    ¬ ∃ c : ModelChart 1 .halfSpace (parabolaMap ⁻¹' {0}), p ∈ c.source := by
  have he (q : parabolaMap ⁻¹' {0}) : q.val = origin :=
    mem_singleton_iff.mp ((Set.ext_iff.mp parabola_zero_fiber q.val).mp q.property)
  have hsub (q r : parabolaMap ⁻¹' {0}) : q = r := Subtype.ext ((he q).trans (he r).symm)
  rintro ⟨c, hp⟩
  have htarget : c.target = {c p} := by
    ext z
    constructor
    · intro hz
      have hh := c.right_inv hz
      rw [hsub (c.symm z) p] at hh
      exact hh.symm
    · rintro rfl
      exact c.map_source hp
  apply halfSpace_one_not_open_singleton (c p)
  exact htarget ▸ c.open_target

/-- Ambient polynomial representative in the standard charts. -/
def parabolaExtension (z : Euclidean 2) : Euclidean 1 :=
  fun _ => z 1 + (z 0) ^ 2

noncomputable def parabolaJacobian (z : Euclidean 2) : Euclidean 2 →L[ℝ] Euclidean 1 :=
  ContinuousLinearMap.pi fun _ =>
    ContinuousLinearMap.proj (1 : Fin 2) + (2 * z 0) • ContinuousLinearMap.proj (0 : Fin 2)

theorem parabolaExtension_hasFDerivAt (z : Euclidean 2) :
    HasFDerivAt parabolaExtension (parabolaJacobian z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  convert (ContinuousLinearMap.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).hasFDerivAt.add
      ((ContinuousLinearMap.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).hasFDerivAt.pow 2) using 1 <;>
    ext x <;> simp [parabolaExtension, parabolaJacobian]

theorem parabola_standard_smooth_and_derivative
    (S : SmoothManifold 2 .halfSpace (HalfSpace 2))
    (T : SmoothManifold 1 .euclidean ℝ)
    (hS : OpenPartialHomeomorph.refl (HalfSpace 2) ∈ S.smoothStructure.val)
    (hT : realChart ∈ T.smoothStructure.val) :
    IsSmoothMap S T parabolaMap ∧
    ∀ p : HalfSpace 2,
      chartDerivative (a := .halfSpace) (b := .euclidean)
        (OpenPartialHomeomorph.refl (HalfSpace 2)) realChart parabolaMap p =
      parabolaJacobian p.val := by
  constructor
  · intro p
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      S.smoothStructure.property.1 T.smoothStructure.property.1 parabolaMap p).mpr
    refine ⟨?_, _, hS, _, hT, mem_univ _, mem_univ _,
      univ, isOpen_univ, mem_univ _, parabolaExtension, ?_, ?_⟩
    · change ContinuousAt (fun q : HalfSpace 2 => q.val 1 + (q.val 0) ^ 2) p
      exact (((continuous_apply (1 : Fin 2)).comp continuous_subtype_val).continuousAt).add
        ((((continuous_apply (0 : Fin 2)).comp continuous_subtype_val).continuousAt).pow 2)
    · apply ContDiff.contDiffOn
      change ContDiff ℝ (⊤ : ℕ∞) (fun z : Euclidean 2 => fun _ : Fin 1 => z 1 + (z 0) ^ 2)
      fun_prop
    · exact Eventually.of_forall (fun _ => rfl)
  · intro p
    exact FiniteRegularity.coordinateDerivative_eq _ _ p (mem_univ _) _
      ⟨parabolaExtension, parabolaExtension_hasFDerivAt p.val,
        Eventually.of_forall (fun _ => rfl)⟩

/-- The full derivative is surjective; the witness uses the normal direction. -/
theorem parabola_isRegularValue
    (S : SmoothManifold 2 .halfSpace (HalfSpace 2))
    (T : SmoothManifold 1 .euclidean ℝ)
    (hS : OpenPartialHomeomorph.refl (HalfSpace 2) ∈ S.smoothStructure.val)
    (hT : realChart ∈ T.smoothStructure.val) : IsRegularValue S T parabolaMap 0 := by
  have hf := parabola_standard_smooth_and_derivative S T hS hT
  have hf1 := manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ _ (by simp) hf.1
  intro p hp
  apply (MapClasses.chart_invariants S T parabolaMap hf1 p _ _ hS hT
    (mem_univ _) (mem_univ _)).2.2.mpr
  rw [hf.2 p]
  intro w
  refine ⟨Pi.single (1 : Fin 2) (w 0), ?_⟩
  ext i
  fin_cases i
  simp [parabolaJacobian]

/-- The boundary restriction has zero differential at the origin. -/
theorem parabola_boundary_not_regular
    (S : SmoothManifold 2 .halfSpace (HalfSpace 2))
    (T : SmoothManifold 1 .euclidean ℝ)
    (hS : OpenPartialHomeomorph.refl (HalfSpace 2) ∈ S.smoothStructure.val)
    (hT : realChart ∈ T.smoothStructure.val)
    (B : SmoothManifold 1 .euclidean (intrinsicBoundary S))
    (hB : IsNaturalBoundaryStructure S B) :
    ¬ IsRegularValue B T (fun p => parabolaMap p.val) 0 := by
  let e : ModelChart 2 .halfSpace (HalfSpace 2) := OpenPartialHomeomorph.refl _
  have hpbd : origin ∈ intrinsicBoundary S :=
    (intrinsicBoundary_iff_chart S e hS origin (mem_univ _)).mpr rfl
  let p : intrinsicBoundary S := ⟨origin, hpbd⟩
  obtain ⟨b, hb, hface⟩ := hB.2 e hS ⟨⟨p, mem_univ _⟩⟩
  have hpb : p ∈ b.source := by rw [hface.1]; exact mem_univ _
  have hcoords (q : intrinsicBoundary S) (hq : q ∈ b.source) :
      (b q).val 0 = q.val.val 0 := hface.2.2 q hq 0
  have hb0 : (b p).val 0 = 0 := (hcoords p hpb).trans rfl
  let F : Euclidean 1 → Euclidean 1 := fun z _ => (z 0) ^ 2
  have hdF : HasFDerivAt F (0 : Euclidean 1 →L[ℝ] Euclidean 1) (b p).val := by
    have hpow := ((ContinuousLinearMap.proj (0 : Fin 1) : Euclidean 1 →L[ℝ] ℝ).hasFDerivAt (x := (b p).val)).pow 2
    have hpi := hasFDerivAt_pi.mpr (fun _ : Fin 1 => hpow)
    convert hpi using 1 <;> ext x <;> simp [F, hb0]
  have hrep : (fun q => F (b q).val) =ᶠ[𝓝 p]
      (fun q : intrinsicBoundary S => (realChart (parabolaMap q.val)).val) := by
    filter_upwards [b.open_source.mem_nhds hpb] with q hq
    have hs : q.val.val 1 = 0 :=
      (intrinsicBoundary_iff_chart S e hS q.val (mem_univ _)).mp q.property
    ext i
    change (b q).val 0 ^ 2 = q.val.val 1 + q.val.val 0 ^ 2
    rw [hcoords q hq, hs, zero_add]
  have hder : chartDerivative b realChart (fun q => parabolaMap q.val) p = 0 :=
    FiniteRegularity.coordinateDerivative_eq b _ p hpb 0 ⟨F, hdF, hrep⟩
  intro hreg
  have hsub := hreg p (by norm_num [p, parabolaMap, origin])
  obtain ⟨hf, C, D, hh⟩ := hsub
  letI := C.group; letI := C.module; letI := D.group; letI := D.module
  obtain ⟨L, hL, hsur⟩ := hh
  have hsur' := (MapClasses.differential_chart_invariants B T (fun q => parabolaMap q.val) p C D b realChart
    hb hT hpb (mem_univ _) L hL).2.2.mp hsur
  rw [hder] at hsur'
  obtain ⟨z, hz⟩ := hsur' (fun _ => 1)
  have hh := congrFun hz 0
  norm_num at hh

/-- All parts of the necessity example use the standard structures and function. -/
theorem boundary_regularity_counterexample_proof :
    Specs.SmoothManifolds.Ch03.BoundaryRegularLevels.boundary_regularity_counterexampleType := by
  obtain ⟨S, hS⟩ := BoundaryInverse.smoothManifold_of_globalChart
    (n := 2) (a := .halfSpace) (OpenPartialHomeomorph.refl (HalfSpace 2)) rfl
  obtain ⟨T, hT⟩ := BoundaryInverse.smoothManifold_of_globalChart (n := 1) (a := .euclidean) realChart rfl
  obtain ⟨B, hB⟩ := natural_boundary_exists_proof S
  exact ⟨S, T, hS, hT, (parabola_standard_smooth_and_derivative S T hS hT).1,
    parabola_isRegularValue S T hS hT,
    ⟨B, hB, parabola_boundary_not_regular S T hS hT B hB⟩,
    parabola_zero_fiber, parabola_no_halfSpace_chart⟩

/-- Rank-nullity inside an injectively realized subspace. -/
theorem kernel_intersection_dimension {U V W : Type*}
    [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ U]
    (I : U →ₗ[ℝ] V) (L : V →ₗ[ℝ] W)
    (hi : Function.Injective I) (hs : Function.Surjective (L.comp I)) :
    Module.finrank ℝ ↥(LinearMap.ker L ⊓ LinearMap.range I) +
      Module.finrank ℝ W = Module.finrank ℝ U := by
  let A := LinearMap.ker (L.comp I)
  let j : A →ₗ[ℝ] V := I.comp A.subtype
  have hj : Function.Injective j := hi.comp Subtype.val_injective
  have hrange : LinearMap.range j = LinearMap.ker L ⊓ LinearMap.range I := by
    ext v
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.property, ⟨z.val, rfl⟩⟩
    · rintro ⟨hv, z, rfl⟩
      exact ⟨⟨z, hv⟩, rfl⟩
  have hdim := (L.comp I).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hdim
  have hjdim := LinearMap.finrank_range_of_inj hj
  rw [hrange] at hjdim
  dsimp [A] at hjdim
  omega

/-- Natural face inclusions have injective full tangent differential in all
allowed dimensions/models. Empty boundary cases are vacuous. -/
theorem natural_boundary_inclusion_injective {m : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold m a M)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S))
    (hB : IsNaturalBoundaryStructure S B) (p : intrinsicBoundary S)
    (I : TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hI : IsDifferential B S Subtype.val p I) : Function.Injective I := by
  cases m with
  | zero => exact ((Set.ext_iff.mp (intrinsicBoundary_zero S) p.val).mp p.property).elim
  | succ r =>
    cases a with
    | euclidean =>
      exact ((Set.ext_iff.mp (intrinsicBoundary_euclidean S) p.val).mp p.property).elim
    | halfSpace =>
      obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p.val
      let E := coordinateDerivationEquiv S p.val e he hp
      exact (boundary_inclusion_image S B hB p e he hp I hI E
        (coordinateDerivationEquiv_isChartCoordinates S p.val e he hp)).1

/-- A smooth map whose image lies in the intrinsic boundary has tangent image
inside the tangent image of the natural boundary inclusion. -/
theorem range_le_boundary_tangent {m k : ℕ} {a c : ModelKind}
    {M P : Type u} [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold m a M)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S))
    (hB : IsNaturalBoundaryStructure S B) (C : SmoothManifold k c P)
    (g : P → M) (hg : IsSmoothMap C S g) (hface : ∀ z, g z ∈ intrinsicBoundary S)
    (p : P) (I : TangentSpace B ⟨g p, hface p⟩ →ₗ[ℝ] TangentSpace S (g p))
    (J : TangentSpace C p →ₗ[ℝ] TangentSpace S (g p))
    (hI : IsDifferential B S Subtype.val ⟨g p, hface p⟩ I)
    (hJ : IsDifferential C S g p J) : LinearMap.range J ≤ LinearMap.range I := by
  cases m with
  | zero => exact ((Set.ext_iff.mp (intrinsicBoundary_zero S) (g p)).mp (hface p)).elim
  | succ r =>
    cases a with
    | euclidean =>
      exact ((Set.ext_iff.mp (intrinsicBoundary_euclidean S) (g p)).mp (hface p)).elim
    | halfSpace =>
      obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (g p)
      let E := coordinateDerivationEquiv S (g p) e he hp
      have hIm := boundary_inclusion_image S B hB ⟨g p, hface p⟩ e he hp I hI E
        (coordinateDerivationEquiv_isChartCoordinates S (g p) e he hp)
      rintro v ⟨w, rfl⟩
      apply (hIm.2 (J w)).mpr
      change (J w).val (coordinateGerm S (g p) e he hp (Fin.last r)) = 0
      have hzero : Germ.ofFun ((fun z => (e z).val (Fin.last r)) ∘ g) =
          (0 : SmoothGerm C p).val := by
        apply Germ.coe_eq.mpr
        filter_upwards [(hg p).1.preimage_mem_nhds (e.open_source.mem_nhds hp)] with z hz
        exact (intrinsicBoundary_iff_chart S e he (g z) hz).mp (hface z)
      rw [hJ w _ 0 _ rfl hzero, map_zero]

/-- Functoriality and the constant-map differential give kernel containment. -/
theorem range_le_kernel_of_constant_comp {k m n : ℕ} {c a b : ModelKind}
    {P M N : Type u} [TopologicalSpace P] [TopologicalSpace M] [TopologicalSpace N]
    (C : SmoothManifold k c P) (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (g : P → M) (f : M → N) (hg : IsSmoothMap C S g) (hf : IsSmoothMap S T f)
    (p : P) (hc : ∀ z, f (g z) = f (g p))
    (J : TangentSpace C p →ₗ[ℝ] TangentSpace S (g p))
    (L : TangentSpace S (g p) →ₗ[ℝ] TangentSpace T (f (g p)))
    (hJ : IsDifferential C S g p J) (hL : IsDifferential S T f (g p) L) :
    LinearMap.range J ≤ LinearMap.ker L := by
  have hcomp := differential_comp C S T g f hg hf p J L hJ hL
  have hz : IsDifferential C T (f ∘ g) p 0 := constant_differential C T _ p hc
  have hs := manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ S.smoothStructure.property.1.1 g f hg hf
  have heq : L.comp J = 0 := (differential_exists C T _ hs p).unique hcomp hz
  rintro v ⟨w, rfl⟩
  exact congrArg (fun A : TangentSpace C p →ₗ[ℝ] TangentSpace T (f (g p)) => A w) heq

/-- The boundary tangent formula follows from natural face inclusions, their
functorial differentials, and rank-nullity for the boundary restriction. -/
theorem boundary_fiber_tangent_proof :
    Specs.SmoothManifolds.Ch03.BoundaryRegularLevels.boundary_fiber_tangentType.{u} := by
  intro m n a b M N _ _ S T f B hB hT hf y hy hyB R hR hboundary C hC p
  dsimp only
  intro L I J hL hI hJ
  let g : intrinsicBoundary R → M := fun z => z.val.val
  have hface : ∀ z : intrinsicBoundary R, g z ∈ intrinsicBoundary S :=
    fun z => (Set.ext_iff.mp hboundary z.val).mp z.property
  let q : intrinsicBoundary S := ⟨p.val.val, hface p⟩
  have hg : IsSmoothMap C S g :=
    manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ R.smoothStructure.property.1.1
      Subtype.val Subtype.val hC.1 hR.1
  have hiI : Function.Injective I := natural_boundary_inclusion_injective S B hB q I hI
  obtain ⟨H, hH, _⟩ := differential_exists C R Subtype.val hC.1 p
  obtain ⟨K, hK, _⟩ := differential_exists R S Subtype.val hR.1 p.val
  have hiH : Function.Injective H := natural_boundary_inclusion_injective R C hC p H hH
  have hiK : Function.Injective K :=
    (MapClasses.smooth_tangent_invariants R S Subtype.val hR.1 p.val K hK).2.1.mp
      (hR.2.2.1 p.val)
  have hcomp : IsDifferential C S g p (K.comp H) :=
    differential_comp C R S Subtype.val Subtype.val hC.1 hR.1 p H K hH hK
  have heqJ : J = K.comp H := (differential_exists C S g hg p).unique hJ hcomp
  have hiJ : Function.Injective J := by rw [heqJ]; exact hiK.comp hiH
  have hker : LinearMap.range J ≤ LinearMap.ker L :=
    range_le_kernel_of_constant_comp C S T g f hg hf p
      (fun z => (mem_singleton_iff.mp z.val.property).trans
        (mem_singleton_iff.mp p.val.property).symm) J L hJ hL
  have hbound : LinearMap.range J ≤ LinearMap.range I :=
    range_le_boundary_tangent S B hB C g hg hface p I J hI hJ
  have hBf : IsSmoothMap B T (fun z => f z.val) :=
    manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ S.smoothStructure.property.1.1
      Subtype.val f hB.1 hf
  have hLI : IsDifferential B T (fun z => f z.val) q (L.comp I) :=
    differential_comp B S T Subtype.val f hB.1 hf q I L hI hL
  have hsur : Function.Surjective (L.comp I) :=
    (MapClasses.smooth_tangent_invariants B T (fun z => f z.val) hBf q (L.comp I) hLI).2.2.mp
      (hyB q (mem_singleton_iff.mp p.val.property))
  letI : AddCommGroup (TangentSpace B q) := Module.addCommMonoidToAddCommGroup ℝ
  letI : AddCommGroup (TangentSpace S p.val.val) := Module.addCommMonoidToAddCommGroup ℝ
  letI : AddCommGroup (TangentSpace T (f p.val.val)) := Module.addCommMonoidToAddCommGroup ℝ
  letI : AddCommGroup (TangentSpace C p) := Module.addCommMonoidToAddCommGroup ℝ
  have hBdim := tangent_dimension B q
  have hSdim := tangent_dimension S p.val.val
  have hTdim := tangent_dimension T (f p.val.val)
  have hCdim := tangent_dimension C p
  letI := hBdim.1; letI := hSdim.1; letI := hTdim.1; letI := hCdim.1
  have hdim := kernel_intersection_dimension I L hiI hsur
  rw [hBdim.2, hTdim.2] at hdim
  have hJdim := LinearMap.finrank_range_of_inj hiJ
  rw [hCdim.2] at hJdim
  have hle : LinearMap.range J ≤ LinearMap.ker L ⊓ LinearMap.range I := le_inf hker hbound
  have hdimEq : Module.finrank ℝ (LinearMap.range J) =
      Module.finrank ℝ ↥(LinearMap.ker L ⊓ LinearMap.range I) := by omega
  exact ⟨hiJ, Submodule.eq_of_le_of_finrank_eq hle hdimEq⟩

/-- An open subspace inherits an embedding and exactly the inherited intrinsic
boundary, including the empty open subspace and dimension zero. -/
theorem open_subset_embedding_boundary {m : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold m a M)
    (U : Set M) (hU : IsOpen U) :
    ∃ R : SmoothManifold m a U,
      IsSmoothEmbedding R S Subtype.val ∧
      intrinsicBoundary R = Subtype.val ⁻¹' intrinsicBoundary S := by
  obtain ⟨R, htop, hatlas, hsmooth⟩ := exists_openSubset_smoothManifold S U hU
  have hA := openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _ S.smoothStructure.property.1 U hU
  have hchart (p : U) (e : ModelChart m a M) (he : e ∈ S.smoothStructure.val) :
      e.subtypeRestr (s := ⟨U, hU⟩) ⟨p⟩ ∈ R.smoothStructure.val := by
    rw [hatlas]
    exact subset_maximalExtension hA ⟨⟨p⟩, e, he, rfl⟩
  refine ⟨R, ⟨hsmooth, Subtype.val_injective, ?_,
    ⟨Topology.IsEmbedding.subtypeVal.toHomeomorph, fun _ => rfl⟩⟩, ?_⟩
  · intro p
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p.val
    let c := e.subtypeRestr (s := ⟨U, hU⟩) ⟨p⟩
    have hc := hchart p e he
    have hpc : p ∈ c.source := by simpa [c] using hp
    have hder : chartDerivative c e Subtype.val p = ContinuousLinearMap.id ℝ (Euclidean m) :=
      FiniteRegularity.coordinateDerivative_eq c _ p hpc _
        ⟨id, hasFDerivAt_id _, Eventually.of_forall (fun _ => rfl)⟩
    apply (MapClasses.chart_invariants R S Subtype.val
      (manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ _ le_top hsmooth) p c e hc he hpc hp).2.1.mpr
    intro x z hxz
    have hx := congrArg (fun A : Euclidean m →L[ℝ] Euclidean m => A x) hder
    have hz := congrArg (fun A : Euclidean m →L[ℝ] Euclidean m => A z) hder
    exact hx.symm.trans (hxz.trans hz)
  · ext p
    obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p.val
    let c := e.subtypeRestr (s := ⟨U, hU⟩) ⟨p⟩
    have hc := hchart p e he
    have hpc : p ∈ c.source := by simpa [c] using hp
    exact (intrinsicBoundary_iff_chart R c hc p hpc).trans
      (intrinsicBoundary_iff_chart S e he p.val hp).symm

/-- The expected dimension can be chosen arbitrarily on an empty fiber. -/
theorem empty_fiber_structure {m k : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold m a M)
    (s : Set M) (hs : s = ∅) :
    ∃ R : SmoothManifold k a s,
      IsSmoothEmbedding R S Subtype.val ∧
      intrinsicBoundary R = Subtype.val ⁻¹' intrinsicBoundary S := by
  letI := S.topologicalManifold.hausdorff
  letI := S.topologicalManifold.secondCountable
  have he (p : s) : False := (Set.ext_iff.mp hs p.val).mp p.property
  have hA : IsContDiffAtlas (⊤ : ℕ∞) (∅ : Set (ModelChart k a s)) := by
    refine ⟨?_, ?_⟩
    · intro p; exact (he p).elim
    · intro c hc; exact hc.elim
  let R : SmoothManifold k a s := {
    topologicalManifold := ⟨inferInstance, inferInstance, ∅, hA.1⟩
    smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) ∅, maximalExtension_isMaximal hA⟩ }
  refine ⟨R, ⟨(fun p => (he p).elim), (fun p => (he p).elim),
    (fun p => (he p).elim),
    ⟨Topology.IsEmbedding.subtypeVal.toHomeomorph, fun _ => rfl⟩⟩, ?_⟩
  ext p
  exact (he p).elim


/-- The entire structure conclusion for codimension zero, including inherited
boundary, follows from the open-subspace construction. -/

theorem zero_target_structure
    : ∀ {m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
      [TopologicalSpace M] [TopologicalSpace N]
      (S : SmoothManifold m a M) (T : SmoothManifold 0 b N) (f : M → N),
      IsSmoothMap S T f → ∀ y,
      ∃ R : SmoothManifold (m - 0) a (f ⁻¹' {y}),
        IsSmoothEmbedding R S Subtype.val ∧
        intrinsicBoundary R = Subtype.val ⁻¹' intrinsicBoundary S ∧
        ((f ⁻¹' {y}).Nonempty → (m - 0) + 0 = m) := by
  intro m a b M N _ _ S T f hf y
  obtain ⟨R, hR, hboundary⟩ := open_subset_embedding_boundary S _ (RegularLevels.zero_target_clopen S T f hf y).1
  exact ⟨R, hR, hboundary, fun _ => rfl⟩

/-- The Euclidean-global-model source case is a genuine application of the
boundary-free structure theorem. -/

theorem euclidean_source_structure
    : ∀ {m n : ℕ} {b : ModelKind} {M : Type u} {N : Type v}
      [TopologicalSpace M] [TopologicalSpace N]
      (S : SmoothManifold m .euclidean M) (T : SmoothManifold n b N) (f : M → N),
      intrinsicBoundary T = ∅ → IsSmoothMap S T f →
      ∀ y, IsRegularValue S T f y →
      ∃ R : SmoothManifold (m - n) .euclidean (f ⁻¹' {y}),
        IsSmoothEmbedding R S Subtype.val ∧
        intrinsicBoundary R = Subtype.val ⁻¹' intrinsicBoundary S ∧
        ((f ⁻¹' {y}).Nonempty → (m - n) + n = m) := by
  intro m n b M N _ _ S T f hT hf y hy
  obtain ⟨R, hR, hboundary, hdim, _⟩ :=
    RegularLevels.regular_fiber_structure S T f (intrinsicBoundary_euclidean S) hT hf y hy
  refine ⟨R, hR, ?_, hdim⟩
  exact hboundary.trans (by
    ext p
    constructor
    · intro hp; exact hp.elim
    · intro hp
      exact (Set.ext_iff.mp (intrinsicBoundary_euclidean S) p.val).mp hp)

/-- A chart on a subspace whose inclusion and coordinate retraction both extend
smoothly in some ambient chart at every point of its source. -/
def HasAmbientCoordinateRetraction {k m : ℕ} {a b : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold m b M)
    (s : Set M) (c : ModelChart k a s) : Prop :=
  ∀ p ∈ c.source, ∃ d ∈ S.smoothStructure.val, p.val ∈ d.source ∧
    ChartContDiffAt ⊤ c d Subtype.val p ∧
    LocalCoordinateExtension ⊤ (fun y : s => (d y.val).val) (fun y => (c y).val) p

/-- Ambient atlas compatibility changes the selected ambient chart in the
coordinate inclusion and retraction germs. -/
theorem ambientCoordinateRetraction_change {k m : ℕ} {a b : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold m b M)
    (s : Set M) (c : ModelChart k a s)
    (hc : HasAmbientCoordinateRetraction S s c) (p : s) (hp : p ∈ c.source)
    (e : ModelChart m b M) (he : e ∈ S.smoothStructure.val)
    (hpe : p.val ∈ e.source) :
    ChartContDiffAt ⊤ c e Subtype.val p ∧
    LocalCoordinateExtension ⊤ (fun y : s => (e y.val).val) (fun y => (c y).val) p := by
  obtain ⟨d, hd, hpd, hcd, hdc⟩ := hc p hp
  have hde := S.smoothStructure.property.1.2 d hd e he
  have hf : LocalCoordinateExtension ⊤ (fun y : s => (d y.val).val)
      (fun y => (e y.val).val) p :=
    LocalCoordinateExtension.precomp
      (chartContDiffAt_of_compatible hde hpd hpe) continuousAt_subtype_val rfl
  have hg : LocalCoordinateExtension ⊤ (fun y : s => (e y.val).val)
      (fun y => (d y.val).val) p :=
    LocalCoordinateExtension.precomp
      (chartContDiffAt_of_compatible (contDiffCompatible_symm hde) hpe hpd)
      continuousAt_subtype_val rfl
  exact ⟨LocalCoordinateExtension.comp hf hcd, LocalCoordinateExtension.comp hdc hg⟩

/-- The ambient inclusion and retraction germs prove all transition germs. -/
theorem coordinateRetractionAtlas_smooth {k m : ℕ} {a b : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold m b M)
    (s : Set M) (A : Set (ModelChart k a s)) (hA : IsAtlas A)
    (hret : ∀ c ∈ A, HasAmbientCoordinateRetraction S s c) :
    IsContDiffAtlas ⊤ A := by
  have hchange : ∀ c ∈ A, ∀ d ∈ A, ∀ p ∈ c.source,
      p ∈ d.source → ChartContDiffAt ⊤ c d id p := by
    intro c hc d hd p hp hpd
    obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p.val
    exact LocalCoordinateExtension.comp
      (ambientCoordinateRetraction_change S s d (hret d hd) p hpd e he hpe).2
      (ambientCoordinateRetraction_change S s c (hret c hc) p hp e he hpe).1
  refine ⟨hA, ?_⟩
  intro c hc d hd
  exact contDiffCompatible_of_germs (hchange c hc d hd) (hchange d hd c hc)

/-- Gluing actual subtype charts by coordinate retractions constructs an
embedded manifold, with the intrinsic boundary read from their model faces. -/
theorem manifold_of_coordinate_retractions {k m : ℕ} {a b : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold m b M)
    (s : Set M) (A : Set (ModelChart k a s)) (hA : IsAtlas A)
    (hret : ∀ c ∈ A, HasAmbientCoordinateRetraction S s c)
    (hface : ∀ c ∈ A, ∀ p ∈ c.source,
      (c p).val ∈ modelFace k a ↔ p.val ∈ intrinsicBoundary S) :
    ∃ R : SmoothManifold k a s,
      IsSmoothEmbedding R S Subtype.val ∧
      intrinsicBoundary R = Subtype.val ⁻¹' intrinsicBoundary S ∧
      R.smoothStructure.val = maximalExtension ⊤ A := by
  let : T2Space M := S.topologicalManifold.hausdorff
  let : SecondCountableTopology M := S.topologicalManifold.secondCountable
  have hAs := coordinateRetractionAtlas_smooth S s A hA hret
  let R : SmoothManifold k a s := {
    topologicalManifold := ⟨inferInstance, inferInstance, A, hA⟩
    smoothStructure := ⟨_, maximalExtension_isMaximal hAs⟩ }
  have hf : IsSmoothMap R S Subtype.val := by
    intro p
    obtain ⟨c, hc, hp⟩ := hA p
    obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p.val
    apply (manifoldContDiffAt_iff_oneChart ⊤ _ _ R.smoothStructure.property.1
      S.smoothStructure.property.1 Subtype.val p).mpr
    exact ⟨continuousAt_subtype_val, c, subset_maximalExtension hAs hc,
      e, he, hp, hpe,
      (ambientCoordinateRetraction_change S s c (hret c hc) p hp e he hpe).1⟩
  refine ⟨R, ⟨hf, Subtype.val_injective, ?_, ?_⟩, ?_, rfl⟩
  · intro p
    obtain ⟨c, hc, hp⟩ := hA p
    obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p.val
    exact SliceStructures.immersion_of_coordinate_retraction R S Subtype.val hf p c e
      (subset_maximalExtension hAs hc) he hp hpe
      (ambientCoordinateRetraction_change S s c (hret c hc) p hp e he hpe).2
  · exact ⟨Topology.IsEmbedding.subtypeVal.toHomeomorph, fun _ => rfl⟩
  · ext p
    obtain ⟨c, hc, hp⟩ := hA p
    exact (intrinsicBoundary_iff_chart R c (subset_maximalExtension hAs hc) p hp).trans
      (hface c hc p hp)

/-- Coordinate retractions and face matching pass to smooth chart refinements,
including refinements from a Euclidean chart to a half-space chart. -/
theorem ambientCoordinateRetraction_refines {k m : ℕ} {a q b : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold m b M)
    (s : Set M) (c : ModelChart k a s) (d : ModelChart k q s)
    (hd : HasAmbientCoordinateRetraction S s d) (href : SliceStructures.RefinesChart c d) :
    HasAmbientCoordinateRetraction S s c := by
  intro p hp
  obtain ⟨hpd, hcd, hdc⟩ := href p hp
  obtain ⟨e, he, hpe, hde, hed⟩ := hd p hpd
  exact ⟨e, he, hpe, LocalCoordinateExtension.comp hde hcd,
    LocalCoordinateExtension.comp hdc hed⟩

theorem faceMatch_refines {k m : ℕ} {a q b : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold m b M)
    (s : Set M) (c : ModelChart k a s) (d : ModelChart k q s)
    (hface : ∀ p ∈ d.source, (d p).val ∈ modelFace k q ↔ p.val ∈ intrinsicBoundary S)
    (href : SliceStructures.RefinesChart c d) :
    ∀ p ∈ c.source, (c p).val ∈ modelFace k a ↔ p.val ∈ intrinsicBoundary S := by
  intro p hp
  obtain ⟨hpd, hcd, hdc⟩ := href p hp
  exact (modelFace_chart_independent c d p hp hpd hcd hdc).trans (hface p hpd)

/-- Local charts may use either the Euclidean or the fixed global model.
Refinement puts all of them in that global model before the gluing theorem. -/
theorem manifold_of_local_coordinate_retractions {k m : ℕ} {a b : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold m b M)
    (s : Set M)
    (hlocal : ∀ p : s, ∃ (q : ModelKind), (q = .euclidean ∨ q = a) ∧
      ∃ c : ModelChart k q s, p ∈ c.source ∧
        HasAmbientCoordinateRetraction S s c ∧
        ∀ y ∈ c.source, (c y).val ∈ modelFace k q ↔ y.val ∈ intrinsicBoundary S) :
    ∃ R : SmoothManifold k a s,
      IsSmoothEmbedding R S Subtype.val ∧
      intrinsicBoundary R = Subtype.val ⁻¹' intrinsicBoundary S := by
  let A : Set (ModelChart k a s) := {c | HasAmbientCoordinateRetraction S s c ∧
    ∀ p ∈ c.source, (c p).val ∈ modelFace k a ↔ p.val ∈ intrinsicBoundary S}
  have hA : IsAtlas A := by
    intro p
    obtain ⟨q, hq, c, hp, hret, hface⟩ := hlocal p
    obtain ⟨d, hpd, href⟩ := SliceStructures.model_refinement c hq p hp
    exact ⟨d, ⟨ambientCoordinateRetraction_refines S s d c hret href,
      faceMatch_refines S s d c hface href⟩, hpd⟩
  obtain ⟨R, hR, hb, _⟩ := manifold_of_coordinate_retractions S s A hA
    (fun c hc => hc.1) (fun c hc => hc.2)
  exact ⟨R, hR, hb⟩

/-- Ordinary compatible coordinates on a boundary-model manifold lie in its
intrinsic interior. -/
theorem interior_of_compatible_euclidean_chart {m : ℕ} {a : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold m a M)
    (d : ModelChart m .euclidean M) (hd : CompatibleChart S d)
    (p : M) (hp : p ∈ d.source) : p ∈ manifoldInterior S := by
  rw [← compl_intrinsicBoundary]
  intro hb
  obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
  have hface := (intrinsicBoundary_iff_chart S e he p hpe).mp hb
  exact ((modelFace_chart_independent d e p hp hpe
    (hd e he p hp hpe).1 (hd e he p hp hpe).2).mpr hface).elim

/-- The interior normal form supplies an ordinary slice, even if the global
source uses half-space coordinates. -/
theorem interior_regular_fiber_slice {n k : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold (n + k) a M) (T : SmoothManifold n b N) (f : M → N)
    (hT : intrinsicBoundary T = ∅) (hf : IsSmoothMap S T f)
    (y : N) (hy : IsRegularValue S T f y) (p : f ⁻¹' {y})
    (hp : p.val ∈ manifoldInterior S) :
    ∃ d : ModelChart (n + k) .euclidean M,
      CompatibleChart S d ∧ p.val ∈ d.source ∧
        IsSliceChart (f ⁻¹' {y}) k .euclidean d := by
  have hpEq : f p.val = y := p.property
  have hn := InteriorConstantRank.interior_submersion ⊤ (by simp) S T f hf p.val hp
    (RegularLevels.mem_manifoldInterior_of_boundary_empty T hT (f p.val))
    (hy p.val p.property)
  obtain ⟨c, d, hc, hd, hpc, hcp, hfpd, hdfp, hmap, hform⟩ := hn.2.1
  let B : E (n + k) ≃L[ℝ] Euclidean (n + k) :=
    (InteriorConstantRank.toL2 (n + k)).symm.trans (RegularLevels.blockLinear n k)
  let C := RegularLevels.chartOfCoordinates c B
  have hslice (x : M) (hx : x ∈ c.source) :
      f x = y ↔ (C x).val ∈ coordinateSlice k (n + k) .euclidean := by
    have hn := hform (c x) (c.map_source hx)
    rw [c.left_inv hx] at hn
    change f x = y ↔ RegularLevels.blockLinear n k
      ((InteriorConstantRank.toL2 (n + k)).symm (c x)) ∈ _
    rw [RegularLevels.blockLinear_slice_iff, ← hn]
    constructor
    · intro h
      simpa only [h, ← hpEq] using hdfp
    · intro h
      apply d.injOn (hmap hx) (hpEq ▸ hfpd)
      exact h.trans (by simpa only [hpEq] using hdfp.symm)
  refine ⟨C, RegularLevels.compatible_chartOfCoordinates S c B hc, hpc,
    by omega, ?_, ?_⟩
  · intro h; cases h
  · ext z
    constructor
    · rintro ⟨x, ⟨hx, hxc⟩, rfl⟩
      exact ⟨C.map_source hxc, (hslice x hxc).mp hx⟩
    · intro hz
      refine ⟨C.symm z, ⟨?_, C.map_target hz.1⟩, C.right_inv hz.1⟩
      apply (hslice (C.symm z) (C.map_target hz.1)).mpr
      rw [congrArg Subtype.val (C.right_inv hz.1)]
      exact hz.2

/-- Actual fiber coordinates at an interior point, in the inherited global
model. They provide smooth inclusion, a smooth coordinate retraction, and
the correct face test on their entire source. -/
theorem interior_regular_fiber_chart {n k : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold (n + k) a M) (T : SmoothManifold n b N) (f : M → N)
    (hT : intrinsicBoundary T = ∅) (hf : IsSmoothMap S T f)
    (y : N) (hy : IsRegularValue S T f y) (p : f ⁻¹' {y})
    (hp : p.val ∈ manifoldInterior S) :
    ∃ c : ModelChart k a (f ⁻¹' {y}), p ∈ c.source ∧
      (∀ z ∈ c.source, ∀ e ∈ S.smoothStructure.val, z.val ∈ e.source →
        ChartContDiffAt ⊤ c e Subtype.val z ∧
        LocalCoordinateExtension ⊤ (fun w : f ⁻¹' {y} => (e w.val).val)
          (fun w => (c w).val) z) ∧
      (∀ z ∈ c.source,
        ((c z).val ∈ modelFace k a ↔ z.val ∈ intrinsicBoundary S)) := by
  obtain ⟨d, hd, hpd, hs⟩ := interior_regular_fiber_slice S T f hT hf y hy p hp
  let hne : Nonempty {z : f ⁻¹' {y} // z.val ∈ d.source} := ⟨⟨p, hpd⟩⟩
  let C := SliceStructures.restrictedSliceChart d hs hne
  obtain ⟨c, hpc, hr⟩ := SliceStructures.model_refinement (a := a) C (Or.inl rfl) p hpd
  refine ⟨c, hpc, ?_, ?_⟩
  · intro z hz e he hze
    have hrc := hr z hz
    have hde : LocalCoordinateExtension ⊤ (fun w : f ⁻¹' {y} => (d w.val).val)
        (fun w => (e w.val).val) z :=
      LocalCoordinateExtension.precomp (hd e he z.val hrc.1 hze).1
        continuousAt_subtype_val rfl
    have hed : LocalCoordinateExtension ⊤ (fun w : f ⁻¹' {y} => (e w.val).val)
        (fun w => (d w.val).val) z :=
      LocalCoordinateExtension.precomp (hd e he z.val hrc.1 hze).2
        continuousAt_subtype_val rfl
    exact ⟨LocalCoordinateExtension.comp hde (LocalCoordinateExtension.comp
        (SliceStructures.restrictedSliceChart_inclusion d hs hne z hrc.1) hrc.2.1),
      LocalCoordinateExtension.comp hrc.2.2 (LocalCoordinateExtension.comp
          (SliceStructures.restrictedSliceChart_projection d hs hne z hrc.1) hed)⟩
  · intro z hz
    have hrc := hr z hz
    have hnoC : (c z).val ∉ modelFace k a := by
      intro hface
      exact ((modelFace_chart_independent c C z hz hrc.1 hrc.2.1 hrc.2.2).mp hface).elim
    have hnoS : z.val ∉ intrinsicBoundary S := by
      have hi := interior_of_compatible_euclidean_chart S d hd z.val hrc.1
      rw [← compl_intrinsicBoundary] at hi
      exact hi
    exact iff_of_false hnoC hnoS

/-- Every regular fiber avoiding the ambient intrinsic boundary has the full
expected structure, even when the ambient manifold has boundary elsewhere. -/
theorem boundary_disjoint_fiber_structure {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N)
    (hT : intrinsicBoundary T = ∅) (hf : IsSmoothMap S T f)
    (y : N) (hy : IsRegularValue S T f y)
    (havoid : f ⁻¹' {y} ∩ intrinsicBoundary S = ∅) :
    ∃ R : SmoothManifold (m - n) a (f ⁻¹' {y}),
      IsSmoothEmbedding R S Subtype.val ∧
      intrinsicBoundary R = Subtype.val ⁻¹' intrinsicBoundary S ∧
      ((f ⁻¹' {y}).Nonempty → (m - n) + n = m) := by
  by_cases hne : (f ⁻¹' {y}).Nonempty
  · obtain ⟨p, hp⟩ := hne
    have hnm := submersionAt_dimension_le S T f p (hy p hp)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hlocal (p : f ⁻¹' {y}) : p.val ∈ manifoldInterior S := by
      rw [← compl_intrinsicBoundary]
      intro hb
      exact (Set.ext_iff.mp havoid p.val).mp ⟨p.property, hb⟩
    obtain ⟨R, hR, hb⟩ := manifold_of_local_coordinate_retractions (a := a) S (f ⁻¹' {y}) (by
      intro z
      obtain ⟨c, hc, hret, hface⟩ := interior_regular_fiber_chart S T f hT hf y hy z (hlocal z)
      refine ⟨a, Or.inr rfl, c, hc, ?_, hface⟩
      intro w hw
      obtain ⟨e, he, hwe⟩ := S.smoothStructure.property.1.1 w.val
      exact ⟨e, he, hwe, hret w hw e he hwe⟩)
    have hdim : n + k - n = k := by omega
    rw [hdim]
    exact ⟨R, hR, hb, by omega⟩
  · obtain ⟨R, hR, hb⟩ := empty_fiber_structure S _ (not_nonempty_iff_eq_empty.mp hne)
    exact ⟨R, hR, hb, fun h => (hne h).elim⟩

/-- Equal-dimensional regular fibers cannot meet the boundary under boundary
regularity, and consequently inherit zero-dimensional embedded structures. -/
theorem equal_dimension_fiber_structure {m : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold m b N) (f : M → N)
    (B : SmoothManifold (m - 1) .euclidean (intrinsicBoundary S))
    (hB : IsNaturalBoundaryStructure S B) (hT : intrinsicBoundary T = ∅)
    (hf : IsSmoothMap S T f) (y : N) (hy : IsRegularValue S T f y)
    (hyB : IsRegularValue B T (fun p => f p.val) y) :
    ∃ R : SmoothManifold (m - m) a (f ⁻¹' {y}),
      IsSmoothEmbedding R S Subtype.val ∧
      intrinsicBoundary R = Subtype.val ⁻¹' intrinsicBoundary S ∧
      ((f ⁻¹' {y}).Nonempty → (m - m) + m = m) := by
  apply boundary_disjoint_fiber_structure S T f hT hf y hy
  apply not_nonempty_iff_eq_empty.mp
  intro hne
  have hd := (regular_fiber_dimension_proof S T f B hB hT hf y hy hyB).2.2 hne
  omega

noncomputable def snocZero (m : ℕ) : Euclidean m →L[ℝ] Euclidean (m + 1) :=
  ContinuousLinearMap.pi (fun i => Fin.lastCases 0 (fun j => ContinuousLinearMap.proj j) i)

@[simp] theorem snocZero_apply (m : ℕ) (x : Euclidean m) :
    snocZero m x = Fin.snoc x 0 := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [snocZero]

/-- The Jacobian of the natural face inclusion in its restricted chart inserts
one final zero coordinate. -/
theorem boundary_chartDerivative_inclusion {m : ℕ} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold (m + 1) .halfSpace M)
    (B : SmoothManifold m .euclidean (intrinsicBoundary S))
    (c : ModelChart (m + 1) .halfSpace M)
    (b : ModelChart m .euclidean (intrinsicBoundary S))
    (hface : IsFaceRestriction S c b) (p : intrinsicBoundary S)
    (hc : c ∈ S.smoothStructure.val) (hpc : p.val ∈ c.source) :
    chartDerivative b c Subtype.val p = snocZero m := by
  have hpb : p ∈ b.source := by rw [hface.1]; exact hpc
  apply FiniteRegularity.coordinateDerivative_eq b _ p hpb
  refine ⟨snocZero m, (snocZero m).hasFDerivAt, ?_⟩
  filter_upwards [b.open_source.mem_nhds hpb] with q hq
  rw [snocZero_apply]
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    exact ((intrinsicBoundary_iff_chart S c hc q.val
      (by rw [hface.1] at hq; exact hq)).mp q.property).symm
  · simp only [Fin.snoc_castSucc]
    exact hface.2.2 q hq j

/-- Boundary regularity gives surjectivity of the ambient Jacobian restricted
to tangential coordinates, without any choice of a preferred ambient chart. -/
theorem boundary_chartDerivative_surjective {m n : ℕ} {a : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold (m + 1) .halfSpace M) (T : SmoothManifold n a N)
    (B : SmoothManifold m .euclidean (intrinsicBoundary S))
    (hB : IsNaturalBoundaryStructure S B) (f : M → N) (hf : IsSmoothMap S T f)
    (p : intrinsicBoundary S)
    (hreg : IsSubmersionAt B T (fun q => f q.val) p)
    (c : ModelChart (m + 1) .halfSpace M) (d : ModelChart n a N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hpc : p.val ∈ c.source) (hpd : f p.val ∈ d.source) :
    Function.Surjective (fun x : Euclidean m =>
      chartDerivative c d f p.val (Fin.snoc x 0)) := by
  obtain ⟨b, hb, hface⟩ := hB.2 c hc ⟨⟨p, hpc⟩⟩
  have hpb : p ∈ b.source := by rw [hface.1]; exact hpc
  have hBf : IsSmoothMap B T (fun q => f q.val) :=
    manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ S.smoothStructure.property.1.1
      Subtype.val f hB.1 hf
  have hs : Function.Surjective (chartDerivative b d (fun q => f q.val) p) :=
    (MapClasses.chart_invariants B T (fun q => f q.val)
      (manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ _ le_top hBf)
      p b d hb hd hpb hpd).2.2.mp hreg
  have hchain := FiniteRegularity.chartDerivative_comp (⊤ : ℕ∞) (by simp)
    b c d Subtype.val f p hpb (hB.1 p).1
    ((hB.1 p).2 b hb c hc hpb hpc) ((hf p.val).2 c hc d hd hpc hpd)
  rw [boundary_chartDerivative_inclusion S B c b hface p hc hpc] at hchain
  intro w
  obtain ⟨x, hx⟩ := hs w
  refine ⟨x, ?_⟩
  change chartDerivative b d (f ∘ Subtype.val) p x = w at hx
  rw [hchain] at hx
  simpa only [ContinuousLinearMap.comp_apply, snocZero_apply] using hx

/-- Insert zero normal coordinates before the free coordinates. -/
def tailEmbedding (n k : ℕ) (x : Euclidean k) : Euclidean (n + k) :=
  Fin.append 0 x

/-- Drop the first normal coordinates. -/
def tailProjection (n k : ℕ) (x : Euclidean (n + k)) : Euclidean k :=
  fun i => x (Fin.natAdd n i)

theorem tailProjection_embedding (n k : ℕ) (x : Euclidean k) :
    tailProjection n k (tailEmbedding n k x) = x := by
  funext i
  exact Fin.append_right 0 x i

theorem tailEmbedding_projection (n k : ℕ) (x : Euclidean (n + k))
    (hx : ∀ i : Fin n, x (Fin.castAdd k i) = 0) :
    tailEmbedding n k (tailProjection n k x) = x := by
  funext i
  induction i using Fin.addCases with
  | left i => simpa [tailEmbedding] using (hx i).symm
  | right i => exact Fin.append_right 0 (tailProjection n k x) i

theorem contDiff_tailEmbedding (n k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (tailEmbedding n k) := by
  apply contDiff_pi.mpr
  intro i
  induction i using Fin.addCases with
  | left i => simpa [tailEmbedding] using
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Euclidean k => (0 : ℝ)))
  | right i => simpa [tailEmbedding] using
      (contDiff_apply ℝ (fun _ : Fin k => ℝ) i)

theorem contDiff_tailProjection (n k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (tailProjection n k) :=
  contDiff_pi.mpr (fun i => contDiff_apply ℝ (fun _ : Fin (n + k) => ℝ) (Fin.natAdd n i))

def tailModelInsertion (n k : ℕ) (z : ModelSpace (k + 1) .halfSpace) :
    ModelSpace (n + (k + 1)) .halfSpace :=
  ⟨tailEmbedding n (k + 1) z.val, by
    change 0 ≤ tailEmbedding n (k + 1) z.val (Fin.last (n + k))
    rw [← Fin.natAdd_last]
    simpa only [tailEmbedding, Fin.append_right] using
      (show 0 ≤ z.val (Fin.last k) from z.property)⟩

def tailModelProjection (n k : ℕ) (z : ModelSpace (n + (k + 1)) .halfSpace) :
    ModelSpace (k + 1) .halfSpace :=
  ⟨tailProjection n (k + 1) z.val, by
    change 0 ≤ z.val (Fin.natAdd n (Fin.last k))
    rw [Fin.natAdd_last]
    exact z.property⟩

theorem tailModelProjection_insertion (n k : ℕ) (z : ModelSpace (k + 1) .halfSpace) :
    tailModelProjection n k (tailModelInsertion n k z) = z := by
  apply Subtype.ext
  exact tailProjection_embedding n (k + 1) z.val

theorem continuous_tailModelInsertion (n k : ℕ) : Continuous (tailModelInsertion n k) :=
  ((contDiff_tailEmbedding n (k + 1)).continuous.comp continuous_subtype_val).subtype_mk _

theorem continuous_tailModelProjection (n k : ℕ) : Continuous (tailModelProjection n k) :=
  ((contDiff_tailProjection n (k + 1)).continuous.comp continuous_subtype_val).subtype_mk _

section Restriction
variable {n k : ℕ} {M : Type u} [TopologicalSpace M] {s : Set M}
  (d : ModelChart (n + (k + 1)) .halfSpace M)
  (hs : ∀ x ∈ d.source, x ∈ s ↔ ∀ i : Fin n, (d x).val (Fin.castAdd (k + 1) i) = 0)
include hs

theorem tailSlice_inverse_mem (z : ModelSpace (k + 1) .halfSpace)
    (hz : tailModelInsertion n k z ∈ d.target) : d.symm (tailModelInsertion n k z) ∈ s := by
  apply (hs _ (d.symm.map_source hz)).mpr
  intro i
  rw [d.right_inv hz]
  exact Fin.append_left 0 z.val i

theorem insertion_tailSlicePoint (p : s) (hp : p.val ∈ d.source) :
    tailModelInsertion n k (tailModelProjection n k (d p.val)) = d p.val := by
  apply Subtype.ext
  exact tailEmbedding_projection n (k + 1) (d p.val).val ((hs _ hp).mp p.property)

/-- Project a straightened half-space fiber to its free tail coordinates.
The chart uses exactly the inherited subspace topology. -/
noncomputable def restrictedHalfSpaceSliceChart
    (hne : Nonempty {p : s // p.val ∈ d.source}) : ModelChart (k + 1) .halfSpace s := by
  classical
  exact {
    toFun p := tailModelProjection n k (d p.val)
    invFun z := if hz : tailModelInsertion n k z ∈ d.target then
      ⟨d.symm (tailModelInsertion n k z), tailSlice_inverse_mem d hs z hz⟩
      else (Classical.choice hne).val
    source := Subtype.val ⁻¹' d.source
    target := tailModelInsertion n k ⁻¹' d.target
    map_source' p hp := by
      change tailModelInsertion n k (tailModelProjection n k (d p.val)) ∈ d.target
      rw [insertion_tailSlicePoint d hs p hp]
      exact d.map_source hp
    map_target' z hz := by
      change tailModelInsertion n k z ∈ d.target at hz
      simp only [dite_eq_left hz]
      exact d.symm.map_source hz
    left_inv' p hp := by
      have hi := insertion_tailSlicePoint d hs p hp
      have hz : tailModelInsertion n k (tailModelProjection n k (d p.val)) ∈ d.target := by
        rw [hi]; exact d.map_source hp
      simp only [dite_eq_left hz]
      apply Subtype.ext
      change d.symm (tailModelInsertion n k (tailModelProjection n k (d p.val))) = p.val
      rw [hi, d.left_inv hp]
    right_inv' z hz := by
      change tailModelInsertion n k z ∈ d.target at hz
      simp only [dite_eq_left hz]
      change tailModelProjection n k (d (d.symm (tailModelInsertion n k z))) = z
      rw [d.right_inv hz, tailModelProjection_insertion]
    open_source := d.open_source.preimage continuous_subtype_val
    open_target := d.open_target.preimage (continuous_tailModelInsertion n k)
    continuousOn_toFun :=
      (continuous_tailModelProjection n k).comp_continuousOn
        (d.continuousOn.comp continuous_subtype_val.continuousOn (fun _ h => h))
    continuousOn_invFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      apply (d.symm.continuousOn.comp (continuous_tailModelInsertion n k).continuousOn
        (fun _ h => h)).congr
      intro z hz
      change tailModelInsertion n k z ∈ d.target at hz
      simp only [Function.comp_apply, dite_eq_left hz]
  }

theorem restrictedHalfSpaceSliceChart_source
    (hne : Nonempty {p : s // p.val ∈ d.source}) :
    (restrictedHalfSpaceSliceChart d hs hne).source = Subtype.val ⁻¹' d.source := rfl

theorem restrictedHalfSpaceSliceChart_val
    (hne : Nonempty {p : s // p.val ∈ d.source}) (p : s) :
    ((restrictedHalfSpaceSliceChart d hs hne) p).val =
      tailProjection n (k + 1) (d p.val).val := rfl

theorem restrictedHalfSpaceSliceChart_inclusion
    (hne : Nonempty {p : s // p.val ∈ d.source})
    (p : s) (hp : p.val ∈ d.source) :
    ChartContDiffAt ⊤ (restrictedHalfSpaceSliceChart d hs hne) d Subtype.val p := by
  refine ⟨univ, isOpen_univ, mem_univ _, tailEmbedding n (k + 1),
    (contDiff_tailEmbedding n (k + 1)).contDiffOn, ?_⟩
  filter_upwards [d.open_source.preimage continuous_subtype_val |>.mem_nhds hp] with q hq
  exact tailEmbedding_projection n (k + 1) (d q.val).val ((hs _ hq).mp q.property)

theorem restrictedHalfSpaceSliceChart_projection
    (hne : Nonempty {p : s // p.val ∈ d.source}) (p : s) :
    LocalCoordinateExtension ⊤ (fun q : s => (d q.val).val)
      (fun q => ((restrictedHalfSpaceSliceChart d hs hne) q).val) p :=
  ⟨univ, isOpen_univ, mem_univ _, tailProjection n (k + 1),
    (contDiff_tailProjection n (k + 1)).contDiffOn, Filter.Eventually.of_forall (fun _ => rfl)⟩

theorem restrictedHalfSpaceSliceChart_face
    (hne : Nonempty {p : s // p.val ∈ d.source}) (p : s) :
    ((restrictedHalfSpaceSliceChart d hs hne) p).val ∈ modelFace (k + 1) .halfSpace ↔
      (d p.val).val ∈ modelFace (n + (k + 1)) .halfSpace := by
  change (d p.val).val (Fin.natAdd n (Fin.last k)) = 0 ↔
    (d p.val).val (Fin.last (n + k)) = 0
  rw [Fin.natAdd_last]

end Restriction
/-- Compatible charts of either permitted model read the intrinsic boundary. -/
theorem compatibleChart_boundary_iff {m : ℕ} {a q : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold m a M)
    (d : ModelChart m q M) (hd : CompatibleChart S d) (p : M) (hp : p ∈ d.source) :
    (d p).val ∈ modelFace m q ↔ p ∈ intrinsicBoundary S := by
  obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p
  exact (modelFace_chart_independent d e p hp hpe
    (hd e he p hp hpe).1 (hd e he p hp hpe).2).trans
    (intrinsicBoundary_iff_chart S e he p hpe).symm

/-- A straightened half-space fiber chart supplies all local data needed by
`manifold_of_local_coordinate_retractions`. -/
theorem halfSpaceSlice_local_data {n k : ℕ} {b : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold (n + (k + 1)) b M)
    (s : Set M) (d : ModelChart (n + (k + 1)) .halfSpace M)
    (hd : CompatibleChart S d)
    (hs : ∀ x ∈ d.source, x ∈ s ↔ ∀ i : Fin n, (d x).val (Fin.castAdd (k + 1) i) = 0)
    (p : s) (hp : p.val ∈ d.source) :
    ∃ c : ModelChart (k + 1) .halfSpace s, p ∈ c.source ∧
      HasAmbientCoordinateRetraction S s c ∧
      ∀ y ∈ c.source, (c y).val ∈ modelFace (k + 1) .halfSpace ↔
        y.val ∈ intrinsicBoundary S := by
  let hne : Nonempty {p : s // p.val ∈ d.source} := ⟨⟨p, hp⟩⟩
  let c := restrictedHalfSpaceSliceChart d hs hne
  refine ⟨c, hp, ?_, ?_⟩
  · intro y hy
    obtain ⟨e, he, hye⟩ := S.smoothStructure.property.1.1 y.val
    have hde : LocalCoordinateExtension ⊤ (fun z : s => (d z.val).val)
        (fun z => (e z.val).val) y :=
      LocalCoordinateExtension.precomp (hd e he y.val hy hye).1 continuousAt_subtype_val rfl
    have hed : LocalCoordinateExtension ⊤ (fun z : s => (e z.val).val)
        (fun z => (d z.val).val) y :=
      LocalCoordinateExtension.precomp (hd e he y.val hy hye).2 continuousAt_subtype_val rfl
    exact ⟨e, he, hye,
      LocalCoordinateExtension.comp hde
        (restrictedHalfSpaceSliceChart_inclusion d hs hne y hy),
      LocalCoordinateExtension.comp
        (restrictedHalfSpaceSliceChart_projection d hs hne y) hed⟩
  · intro y hy
    exact (restrictedHalfSpaceSliceChart_face d hs hne y).trans
      (compatibleChart_boundary_iff S d hd y.val hy)

/-- An ambient smooth coordinate change gives a compatible chart for either
allowed source and target model. -/
theorem compatibleChart_of_model_change {m : ℕ} {a q : ModelKind}
    {M : Type u} [TopologicalSpace M] (S : SmoothManifold m a M)
    (e : ModelChart m a M) (he : e ∈ S.smoothStructure.val)
    (c : ModelChart m q M)
    (j : OpenPartialHomeomorph (Euclidean m) (Euclidean m))
    (hj : ContDiffOn ℝ (⊤ : ℕ∞) j j.source)
    (hji : ContDiffOn ℝ (⊤ : ℕ∞) j.symm j.target)
    (hsub : c.source ⊆ e.source)
    (hform : ∀ x ∈ c.source, (e x).val ∈ j.source ∧ (c x).val = j (e x).val) :
    CompatibleChart S c := by
  intro d hd p hp hpd
  have hpe := hsub hp
  have hec : ChartContDiffAt ⊤ e c id p := by
    refine ⟨j.source, j.open_source, (hform p hp).1, j, hj, ?_⟩
    filter_upwards [c.open_source.mem_nhds hp] with x hx
    exact (hform x hx).2.symm
  have hce : ChartContDiffAt ⊤ c e id p := by
    have hct : (c p).val ∈ j.target := by
      rw [(hform p hp).2]
      exact j.map_source (hform p hp).1
    refine ⟨j.target, j.open_target, hct, j.symm, hji, ?_⟩
    filter_upwards [c.open_source.mem_nhds hp] with x hx
    rw [(hform x hx).2, j.left_inv (hform x hx).1]
    rfl
  exact ⟨LocalCoordinateExtension.comp
      (chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 e he d hd) hpe hpd) hce,
    LocalCoordinateExtension.comp hec
      (chartContDiffAt_of_compatible (S.smoothStructure.property.1.2 d hd e he) hpd hpe)⟩

/-- The full proposition proved by the Euclidean normal-coordinate construction. -/
def EuclideanBoundaryCoordinates (n k : ℕ) : Prop :=
  ∀ (g : Euclidean ((n + k) + 1) → Euclidean n)
    (U : Set (Euclidean ((n + k) + 1))),
    IsOpen U → ContDiffOn ℝ (⊤ : ℕ∞) g U →
    ∀ p ∈ U, ∀ L : Euclidean ((n + k) + 1) →L[ℝ] Euclidean n,
    HasFDerivAt g L p →
    Function.Surjective (fun x : Euclidean (n + k) => L (Fin.snoc x 0)) →
    ∃ j : OpenPartialHomeomorph (Euclidean ((n + k) + 1)) (Euclidean ((n + k) + 1)),
      p ∈ j.source ∧ j.source ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) j j.source ∧
      ContDiffOn ℝ (⊤ : ℕ∞) j.symm j.target ∧
      (∀ z, j z (Fin.last (n + k)) = z (Fin.last (n + k))) ∧
      (∀ z (i : Fin n), j z (Fin.castSucc (Fin.castAdd k i)) = (g z - g p) i)

/-- At a regular boundary fiber point, a compatible ambient half-space chart
makes the fiber the vanishing of the first n coordinates and preserves its
actual boundary face. -/
theorem boundary_ambient_chart {n k : ℕ} {a : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold ((n + k) + 1) .halfSpace M)
    (T : SmoothManifold n a N)
    (B : SmoothManifold (n + k) .euclidean (intrinsicBoundary S))
    (hB : IsNaturalBoundaryStructure S B) (f : M → N) (hf : IsSmoothMap S T f)
    (y : N) (p : intrinsicBoundary S) (hpy : f p.val = y)
    (hreg : IsSubmersionAt B T (fun q => f q.val) p) :
    ∃ c : ModelChart ((n + k) + 1) .halfSpace M,
      CompatibleChart S c ∧ p.val ∈ c.source ∧
      (∀ x ∈ c.source, f x = y ↔
        ∀ i : Fin n, (c x).val (Fin.castSucc (Fin.castAdd k i)) = 0) ∧
      (∀ x ∈ c.source, (c x).val ∈ halfSpaceFace ((n + k) + 1) ↔
        x ∈ intrinsicBoundary S) := by
  have hnormal : EuclideanBoundaryCoordinates n k :=
    BoundaryConstruction.euclidean_boundary_coordinates
  obtain ⟨e, he, hpe⟩ := S.smoothStructure.property.1.1 p.val
  obtain ⟨d, hd, hpd⟩ := T.smoothStructure.property.1.1 (f p.val)
  obtain ⟨U, hU, hepU, G, hG, heq⟩ := (hf p.val).2 e he d hd hpe hpd
  have hDG : HasFDerivAt G (fderiv ℝ G (e p.val).val) (e p.val).val :=
    ((hG.contDiffAt (hU.mem_nhds hepU)).differentiableAt (by simp)).hasFDerivAt
  have hder : chartDerivative e d f p.val = fderiv ℝ G (e p.val).val :=
    FiniteRegularity.coordinateDerivative_eq e _ p.val hpe _ ⟨G, hDG, heq⟩
  have hsur : Function.Surjective (fun x : Euclidean (n + k) =>
      fderiv ℝ G (e p.val).val (Fin.snoc x 0)) := by
    rw [← hder]
    exact boundary_chartDerivative_surjective S T B hB f hf p hreg e d he hd hpe hpd
  obtain ⟨j, hpj, hjU, hj, hji, hjlast, hjfirst⟩ :=
    hnormal G U hU hG (e p.val).val hepU _ hDG hsur
  have hsame : j.IsImage (halfSpaceSet ((n + k) + 1))
      (halfSpaceSet ((n + k) + 1)) := by
    intro z hz
    change 0 ≤ j z (Fin.last (n + k)) ↔ 0 ≤ z (Fin.last (n + k))
    rw [hjlast]
  let r := BoundaryInverse.restrictInvariant j (halfSpaceSet ((n + k) + 1)) hsame (e p.val)
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp
    (heq.and ((hf p.val).1.preimage_mem_nhds (d.open_source.mem_nhds hpd)))
  let c : ModelChart ((n + k) + 1) .halfSpace M := (e.restrOpen V hV).trans r
  have hpc : p.val ∈ c.source := ⟨⟨hpe, hpV⟩, hpj⟩
  have hcsub : c.source ⊆ e.source := fun x hx => hx.1.1
  have hcform (x : M) (hx : x ∈ c.source) :
      (e x).val ∈ j.source ∧ (c x).val = j (e x).val := by
    refine ⟨hx.2, ?_⟩
    exact BoundaryInverse.restrictInvariant_val j _ hsame (e p.val) (e x) hx.2
  have hccompat : CompatibleChart S c :=
    compatibleChart_of_model_change S e he c j hj hji hcsub hcform
  have hdY : y ∈ d.source := hpy ▸ hpd
  have hGp : G (e p.val).val = (d y).val := by
    rw [heq.eq_of_nhds, hpy]
  have hfirst (x : M) (hx : x ∈ c.source) (i : Fin n) :
      (c x).val (Fin.castSucc (Fin.castAdd k i)) = ((d (f x)).val - (d y).val) i := by
    have hGx : G (e x).val = (d (f x)).val := (hVsub hx.1.2).1
    rw [(hcform x hx).2, hjfirst, hGx, hGp]
  refine ⟨c, hccompat, hpc, ?_, ?_⟩
  · intro x hx
    constructor
    · intro hxy i
      rw [hfirst x hx i, hxy]
      simp
    · intro hz
      apply d.injOn (hVsub hx.1.2).2 hdY
      apply Subtype.ext
      funext i
      have hi := hz i
      rw [hfirst x hx i] at hi
      exact sub_eq_zero.mp hi
  · intro x hx
    change (c x).val (Fin.last (n + k)) = 0 ↔ x ∈ intrinsicBoundary S
    rw [(hcform x hx).2, hjlast]
    exact (intrinsicBoundary_iff_chart S e he x (hcsub hx)).symm

/-- Interior and half-space fiber charts glue to the full regular-level
conclusion, including empty fibers and the inherited intrinsic boundary. -/
theorem regular_fiber_structure :
    Specs.SmoothManifolds.Ch03.BoundaryRegularLevels.regular_fiber_structureType.{u,v} := by
  intro m n a b M N _ _ S T f B hB hT hf y hy hyB
  by_cases hn0 : n = 0
  · subst n
    exact zero_target_structure S T f hf y
  cases a with
  | euclidean => exact euclidean_source_structure S T f hT hf y hy
  | halfSpace =>
    by_cases hne : (f ⁻¹' {y}).Nonempty
    · by_cases hboundary : (f ⁻¹' {y} ∩ intrinsicBoundary S).Nonempty
      · have hd := (regular_fiber_dimension_proof S T f B hB hT hf y hy hyB).2.2 hboundary
        obtain ⟨k, hm⟩ : ∃ k, m = (n + k) + 1 := ⟨m - 1 - n, by omega⟩
        subst m
        obtain ⟨R, hR, hRb⟩ := manifold_of_local_coordinate_retractions
          (k := k + 1) (a := .halfSpace) S (f ⁻¹' {y}) (by
          intro p
          by_cases hpBoundary : p.val ∈ intrinsicBoundary S
          · let q : intrinsicBoundary S := ⟨p.val, hpBoundary⟩
            obtain ⟨d, hd, hpd, hzero, hface⟩ :=
              boundary_ambient_chart S T B hB f hf y q p.property (hyB q p.property)
            obtain ⟨c, hpc, hret, hcf⟩ :=
              halfSpaceSlice_local_data (n := n) (k := k) S (f ⁻¹' {y}) d hd hzero p hpd
            exact ⟨.halfSpace, Or.inr rfl, c, hpc, hret, hcf⟩
          · have hpInterior : p.val ∈ manifoldInterior S := by
              rw [← compl_intrinsicBoundary]
              exact hpBoundary
            obtain ⟨c, hpc, hret, hface⟩ :=
              interior_regular_fiber_chart (k := k + 1) S T f hT hf y hy p hpInterior
            refine ⟨.halfSpace, Or.inr rfl, c, hpc, ?_, hface⟩
            intro z hz
            obtain ⟨e, he, hze⟩ := S.smoothStructure.property.1.1 z.val
            exact ⟨e, he, hze, hret z hz e he hze⟩)
        have hdim : (n + k + 1) - n = k + 1 := by omega
        rw [hdim]
        exact ⟨R, hR, hRb, fun _ => by omega⟩
      · exact boundary_disjoint_fiber_structure S T f hT hf y hy
          (not_nonempty_iff_eq_empty.mp hboundary)
    · obtain ⟨R, hR, hRb⟩ := empty_fiber_structure S (f ⁻¹' {y})
        (not_nonempty_iff_eq_empty.mp hne)
      exact ⟨R, hR, hRb, fun h => (hne h).elim⟩

/-- Boundary surjectivity makes (dF, ds) surjective. -/
theorem boundary_augmented_surjective {m n : ℕ}
    (L : Euclidean (m + 1) →L[ℝ] Euclidean n)
    (hs : Function.Surjective (fun x : Euclidean m => L (Fin.snoc x 0))) :
    Function.Surjective (fun z : Euclidean (m + 1) => (L z, z (Fin.last m))) := by
  rintro ⟨w, t⟩
  let normal : Euclidean (m + 1) := Pi.single (Fin.last m) t
  obtain ⟨x, hx⟩ := hs (w - L normal)
  refine ⟨Fin.snoc x 0 + normal, ?_⟩
  apply Prod.ext
  · simp only [map_add, hx, sub_add_cancel]
  · simp [normal]

/-- The intrinsic boundary has its natural face atlas, including dimension zero. -/
theorem natural_boundary_exists :
    Specs.SmoothManifolds.Ch03.BoundaryRegularLevels.natural_boundary_existsType.{u} :=
  natural_boundary_exists_proof

/-- Smooth maps have closed fibers, with no boundary or regularity restriction. -/
theorem fiber_closed :
    Specs.SmoothManifolds.Ch03.BoundaryRegularLevels.fiber_closedType.{u,v} :=
  RegularLevels.fiber_closed

/-- Regularity bounds dimensions only on nonempty fibers. -/
theorem regular_fiber_dimension :
    Specs.SmoothManifolds.Ch03.BoundaryRegularLevels.regular_fiber_dimensionType.{u,v} :=
  regular_fiber_dimension_proof

/-- The full tangent image is the differential kernel, including at the face. -/
theorem regular_fiber_tangent :
    Specs.SmoothManifolds.Ch03.BoundaryRegularLevels.regular_fiber_tangentType.{u} :=
  regular_fiber_tangent_proof

/-- The boundary tangent image is the intersection with the ambient boundary tangent. -/
theorem boundary_fiber_tangent :
    Specs.SmoothManifolds.Ch03.BoundaryRegularLevels.boundary_fiber_tangentType.{u} :=
  boundary_fiber_tangent_proof

/-- A zero-dimensional target has open and closed fibers. -/
theorem zero_target_clopen :
    Specs.SmoothManifolds.Ch03.BoundaryRegularLevels.zero_target_clopenType.{u,v} :=
  RegularLevels.zero_target_clopen

/-- The parabola example shows why boundary regularity is required. -/
theorem boundary_regularity_counterexample :
    Specs.SmoothManifolds.Ch03.BoundaryRegularLevels.boundary_regularity_counterexampleType :=
  boundary_regularity_counterexample_proof

end SmoothManifolds.BoundaryRegularLevels
