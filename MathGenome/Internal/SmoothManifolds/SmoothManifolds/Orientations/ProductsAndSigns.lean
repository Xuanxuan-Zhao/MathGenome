import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.ProductsAndSigns
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Bundle
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.TensorProduct.Finite
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.Equivalences
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical TensorProduct Topology

namespace SmoothManifolds.OrientationProducts
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  ProductData BoundaryData OrientationData OrientationProductData Set Filter Module
universe u v w

@[simp] theorem determinantMap_trans {V : Type u} {W : Type v} {X : Type w}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup X] [Module ℝ X] (n : ℕ) (E : V ≃ₗ[ℝ] W) (F : W ≃ₗ[ℝ] X) :
    determinantMap n (E.trans F) = (determinantMap n E).trans (determinantMap n F) := by
  apply LinearEquiv.toLinearMap_injective
  exact exteriorPower.map_comp E.toLinearMap F.toLinearMap

@[simp] theorem rayMap_trans {V : Type u} {W : Type v} {X : Type w}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup X] [Module ℝ X] (E : V ≃ₗ[ℝ] W) (F : W ≃ₗ[ℝ] X)
    (r : Module.Ray ℝ V) :
    Module.Ray.map (E.trans F) r = Module.Ray.map F (Module.Ray.map E r) := by
  induction r using Module.Ray.ind with | h v hv => simp

/-- The exterior product of an ordered basis is nonzero, including the empty
basis. This follows by evaluating its determinant, whose value is one. -/
theorem basisWedge_ne_zero {V : Type u} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (b : Basis (Fin n) ℝ V) : exteriorPower.ιMulti ℝ n b ≠ 0 := by
  intro h
  have hx := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) h
  simpa only [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero,
    Basis.det_self, one_ne_zero] using hx

/-- The algebraic convention really concatenates the first basis before the
second, without a hidden permutation from boundary coordinate rearrangements. -/
theorem orderedWedge_basis {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {m n : ℕ}
    (v : Fin m → V) (w : Fin n → W) :
    orderedWedge m n V W (exteriorPower.ιMulti ℝ m v) (exteriorPower.ιMulti ℝ n w) =
      exteriorPower.ιMulti ℝ (m+n)
        (Fin.append (fun i => (v i, 0)) (fun j => (0, w j))) := by
  simp only [orderedWedge, LinearMap.compl₁₂_apply, exteriorPower.map_apply_ιMulti]
  apply Subtype.ext
  exact ExteriorAlgebra.ιMulti_mul_ιMulti _ _

theorem orderedWedge_nonzero {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {m n : ℕ}
    (b : Basis (Fin m) ℝ V) (c : Basis (Fin n) ℝ W) :
    orderedWedge m n V W (exteriorPower.ιMulti ℝ m b)
      (exteriorPower.ιMulti ℝ n c) ≠ 0 := by
  rw [orderedWedge_basis]
  convert basisWedge_ne_zero ((b.prod c).reindex (finSumFinEquiv)) using 1
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [Basis.reindex_apply, Basis.prod_apply]
  · intro j
    simp [Basis.reindex_apply, Basis.prod_apply]

/-- Direct sum determinant lines are genuinely isomorphic. -/
theorem determinantSumMap_bijective (m n : ℕ) (V W : Type u)
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (hm : finrank ℝ V = m) (hn : finrank ℝ W = n) :
    Function.Bijective (determinantSumMap m n V W) := by
  let b := Module.finBasisOfFinrankEq ℝ V hm
  let c := Module.finBasisOfFinrankEq ℝ W hn
  have hne : determinantSumMap m n V W ≠ 0 := by
    intro h
    have hv := congrArg (fun L => L ((exteriorPower.ιMulti ℝ m b) ⊗ₜ[ℝ]
      (exteriorPower.ιMulti ℝ n c))) h
    exact orderedWedge_nonzero b c (by simpa [determinantSumMap] using hv)
  have hdim : finrank ℝ (⋀[ℝ]^(m+n) (V × W)) = 1 := by
    simp [exteriorPower.finrank_eq, Module.finrank_prod, hm, hn]
  have hs : Function.Surjective (determinantSumMap m n V W) := by
    apply surjective_of_nonzero_of_finrank_eq_one (K := ℝ) (A := ℝ)
      (V := (⋀[ℝ]^m V) ⊗[ℝ] (⋀[ℝ]^n W))
      (W := ⋀[ℝ]^(m+n) (V × W)) hdim
    exact hne
  refine ⟨?_, hs⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (V := (⋀[ℝ]^m V) ⊗[ℝ] (⋀[ℝ]^n W))
    (V₂ := ⋀[ℝ]^(m+n) (V × W)) (by
    simp [Module.finrank_tensorProduct, exteriorPower.finrank_eq, hm, hn, hdim])).mpr hs

/-- Positive changes of generators multiply the ordered wedge by a positive
scalar. This is the pointwise independence argument, in every dimension. -/
theorem orderedWedge_pos_rescale {V W : Type u}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (m n : ℕ) (v : ⋀[ℝ]^m V) (w : ⋀[ℝ]^n W) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    0 < a * b ∧ orderedWedge m n V W (a • v) (b • w) =
      (a*b) • orderedWedge m n V W v w := by
  exact ⟨mul_pos ha hb, by simp [smul_smul, mul_comm a b]⟩

/-- No nonzero determinant generator is lost by concatenation. -/
theorem orderedWedge_ne_zero {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    {m n : ℕ} (hm : finrank ℝ V = m) (hn : finrank ℝ W = n)
    {v : ⋀[ℝ]^m V} {w : ⋀[ℝ]^n W} (hv : v ≠ 0) (hw : w ≠ 0) :
    orderedWedge m n V W v w ≠ 0 := by
  let b := Module.finBasisOfFinrankEq ℝ V hm
  let c := Module.finBasisOfFinrankEq ℝ W hn
  have hdV : finrank ℝ (⋀[ℝ]^m V) = 1 := by simp [exteriorPower.finrank_eq, hm]
  have hdW : finrank ℝ (⋀[ℝ]^n W) = 1 := by simp [exteriorPower.finrank_eq, hn]
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hdV (basisWedge_ne_zero b) v
  obtain ⟨d, hd⟩ := exists_smul_eq_of_finrank_eq_one hdW (basisWedge_ne_zero c) w
  have ha0 : a ≠ 0 := by intro h; apply hv; rw [← ha, h, zero_smul]
  have hd0 : d ≠ 0 := by intro h; apply hw; rw [← hd, h, zero_smul]
  rw [← ha, ← hd]
  have heq : orderedWedge m n V W (a • exteriorPower.ιMulti ℝ m b)
      (d • exteriorPower.ιMulti ℝ n c) =
      (a*d) • orderedWedge m n V W (exteriorPower.ιMulti ℝ m b)
        (exteriorPower.ιMulti ℝ n c) := by simp [smul_smul, mul_comm a d]
  rw [heq]
  exact smul_ne_zero (mul_ne_zero ha0 hd0) (orderedWedge_nonzero b c)

/-- The product of two determinant rays, before checking variation in the base. -/
def orderedProductRay {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    {m n : ℕ} (hm : finrank ℝ V = m) (hn : finrank ℝ W = n)
    (r : Module.Ray ℝ (⋀[ℝ]^m V)) (s : Module.Ray ℝ (⋀[ℝ]^n W)) :
    Module.Ray ℝ (⋀[ℝ]^(m+n) (V × W)) :=
  rayOfNeZero ℝ (orderedWedge m n V W r.someVector s.someVector)
    (orderedWedge_ne_zero hm hn r.someVector_ne_zero s.someVector_ne_zero)

/-- The resulting ray is independent of both chosen positive generators. -/
theorem orderedProductRay_positive {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    {m n : ℕ} (hm : finrank ℝ V = m) (hn : finrank ℝ W = n)
    (r : Module.Ray ℝ (⋀[ℝ]^m V)) (s : Module.Ray ℝ (⋀[ℝ]^n W))
    {v : ⋀[ℝ]^m V} {w : ⋀[ℝ]^n W} (hv : IsPositive r v) (hw : IsPositive s w) :
    IsPositive (orderedProductRay hm hn r s) (orderedWedge m n V W v w) := by
  obtain ⟨hv0, hv⟩ := hv
  obtain ⟨hw0, hw⟩ := hw
  have hrv : SameRay ℝ r.someVector v :=
    (ray_eq_iff r.someVector_ne_zero hv0).mp (r.someVector_ray.trans hv.symm)
  have hsw : SameRay ℝ s.someVector w :=
    (ray_eq_iff s.someVector_ne_zero hw0).mp (s.someVector_ray.trans hw.symm)
  obtain ⟨a, ha, hav⟩ := hrv.exists_pos_left r.someVector_ne_zero hv0
  obtain ⟨b, hb, hbw⟩ := hsw.exists_pos_left s.someVector_ne_zero hw0
  refine ⟨orderedWedge_ne_zero hm hn hv0 hw0, ?_⟩
  unfold orderedProductRay
  apply (ray_eq_iff _ _).mpr
  rw [← hav, ← hbw, (orderedWedge_pos_rescale m n _ _ a b ha hb).2]
  exact (SameRay.refl (R := ℝ) _).pos_smul_left (mul_pos ha hb)

/-- Two rays in a real line are equal or opposite. -/
theorem rays_eq_or_neg {V : Type u} [AddCommGroup V] [Module ℝ V]
    (hd : finrank ℝ V = 1) (r s : Module.Ray ℝ V) : r = s ∨ r = -s := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hd s.someVector_ne_zero r.someVector
  have hc0 : c ≠ 0 := by
    intro h
    have : r.someVector = 0 := by simpa [h] using hc.symm
    exact r.someVector_ne_zero this
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · right
    have hv : (-c) • (-s.someVector) = r.someVector := by simpa using hc
    rw [← r.someVector_ray, ← s.someVector_ray, neg_rayOfNeZero]
    rw [ray_eq_iff]
    rw [← hv]
    exact (SameRay.refl (R := ℝ) _).pos_smul_left (neg_pos.mpr hneg)
  · left
    rw [← r.someVector_ray, ← s.someVector_ray, ray_eq_iff, ← hc]
    exact (SameRay.refl (R := ℝ) _).pos_smul_left hpos

theorem determinantLine_finrank {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (p : M) :
    finrank ℝ (DeterminantLine S p) = 1 := by
  obtain ⟨hfinite, hdim⟩ := tangent_dimension S p
  letI : FiniteDimensional ℝ (TangentData.TangentSpace S p) := hfinite
  letI : Module.Free ℝ (TangentData.TangentSpace S p) := Module.Free.of_divisionRing ℝ (TangentData.TangentSpace S p)
  rw [exteriorPower.finrank_eq, hdim, Nat.choose_self]

/-- Pointwise meaning of the sign, prior to its local-constancy theorem. -/
theorem orientationSign_rays {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold n b N} {f : M → N}
    (o : Orientation S) (q : Orientation T)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p)) (p : M) :
    Module.Ray.map (determinantMap n (E p)) (o.val p) =
      if orientationSign o q E p then q.val (f p) else -q.val (f p) := by
  by_cases h : Module.Ray.map (determinantMap n (E p)) (o.val p) = q.val (f p)
  · simpa [orientationSign, h] using h
  · simpa [orientationSign, h] using
      (rays_eq_or_neg (determinantLine_finrank T (f p)) _ _).resolve_left h

/-- Local diffeomorphisms are globally smooth in the specified structures. -/
theorem IsLocalDiffeomorphism.smooth {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold n b N} {f : M → N}
    (hf : IsLocalDiffeomorphism S T f) : IsSmoothMap S T f := by
  intro p
  obtain ⟨e, hp, he, hs, _⟩ := hf p
  apply manifoldContDiffAt_congr (hs p hp)
  filter_upwards [e.open_source.mem_nhds hp] with x hx
  exact he hx

/-- The chain rule determines the composite differential, independent of every
choice of local inverse used to obtain the linear equivalences. -/
theorem differential_equiv_comp {n : ℕ} {a b c : ModelKind} {M N Q : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Q]
    {S : SmoothManifold n a M} {T : SmoothManifold n b N}
    {R : SmoothManifold n c Q} {f : M → N} {g : N → Q}
    (hf : IsSmoothMap S T f) (hg : IsSmoothMap T R g)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p))
    (F : ∀ p, TangentSpace T p ≃ₗ[ℝ] TangentSpace R (g p))
    (H : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace R ((g ∘ f) p))
    (hE : ∀ p, IsDifferential S T f p (E p).toLinearMap)
    (hF : ∀ p, IsDifferential T R g p (F p).toLinearMap)
    (hH : ∀ p, IsDifferential S R (g ∘ f) p (H p).toLinearMap) (p : M) :
    H p = (E p).trans (F (f p)) := by
  apply LinearEquiv.toLinearMap_injective
  exact (differential_exists S R (g ∘ f)
    (manifoldContDiff_comp _ _ _ _ T.smoothStructure.property.1.1 f g hf hg) p).unique
      (hH p) (differential_comp S T R f g hf hg p _ _ (hE p) (hF (f p)))

open private scalar_comp_at from MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential

/-- A smooth local inverse gives enough scalar germs to detect every source
derivation, hence forces dF to be injective. No global inverse is used. -/
theorem local_differential_injective {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold n b N} {f : M → N}
    (hf : IsLocalDiffeomorphism S T f) (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : IsDifferential S T f p L) : Function.Injective L := by
  obtain ⟨e, hp, he, _, hinv⟩ := hf p
  have hfp : f p ∈ e.target := by rw [← he hp]; exact e.map_source hp
  have hleft : e.symm (f p) = p := by rw [← he hp]; exact e.left_inv hp
  intro v w hvw
  apply Subtype.ext
  apply LinearMap.ext
  intro k
  obtain ⟨r, hr, hrk⟩ := (mem_smoothGermAlgebra_iff S p k.val).mp k.property
  have hr' : PartitionData.ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val r
      (e.symm (f p)) := hleft.symm ▸ hr
  let j : SmoothGerm T (f p) := ⟨Germ.ofFun (r ∘ e.symm),
    Algebra.subset_adjoin ⟨r ∘ e.symm, scalar_comp_at (hinv (f p) hfp) hr', rfl⟩⟩
  have hcomp : Germ.ofFun ((r ∘ e.symm) ∘ f) = k.val := by
    rw [hrk]
    apply Quotient.sound
    filter_upwards [e.open_source.mem_nhds hp] with x hx
    change r (e.symm (f x)) = r x
    rw [← he hx, e.left_inv hx]
  exact (hL v j k (r ∘ e.symm) rfl hcomp).symm.trans
    ((congrArg (fun z : TangentSpace T (f p) => z.val j) hvw).trans
      (hL w j k (r ∘ e.symm) rfl hcomp))

/-- The intrinsic differential of a local diffeomorphism is a uniquely
specified family of linear equivalences. -/
theorem local_differential_exists :
    Specs.SmoothManifolds.Orientations.ProductsAndSigns.local_differentialType.{u} := by
  intro n a b M N _ _ S T f hf
  have hs := IsLocalDiffeomorphism.smooth hf
  have hex (p : M) : ∃ E : TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p),
      IsDifferential S T f p E.toLinearMap := by
    obtain ⟨L, hL, _⟩ := differential_exists S T f hs p
    obtain ⟨hfiniteS, hdimS⟩ := tangent_dimension S p
    obtain ⟨hfiniteT, hdimT⟩ := tangent_dimension T (f p)
    letI := hfiniteS
    letI := hfiniteT
    have hi := local_differential_injective hf p L hL
    have hb : Function.Bijective L := ⟨hi,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (V := TangentSpace S p) (V₂ := TangentSpace T (f p))
        (hdimS.trans hdimT.symm) (f := L)).mp hi⟩
    exact ⟨LinearEquiv.ofBijective L hb, hL⟩
  choose E hE using hex
  refine ⟨E, hE, ?_⟩
  intro F hF
  funext p
  apply LinearEquiv.toLinearMap_injective
  exact (differential_exists S T f hs p).unique (hF p) (hE p)

/-- Multiplicativity is a consequence of the chain rule on actual exterior
powers and the two possible rays in a real line. -/
theorem orientationSign_comp :
    Specs.SmoothManifolds.Orientations.ProductsAndSigns.sign_compType.{u} := by
  intro n a b c M N Q _ _ _ S T R f g hf hg o q r E F H hE hF hH p
  have htrans := differential_equiv_comp (IsLocalDiffeomorphism.smooth hf)
    (IsLocalDiffeomorphism.smooth hg) E F H hE hF hH p
  have h1 := orientationSign_rays o q E p
  have h2 := orientationSign_rays q r F (f p)
  have hmap : Module.Ray.map (determinantMap n (H p)) (o.val p) =
      Module.Ray.map (determinantMap (V := TangentSpace T (f p))
        (W := TangentSpace R (g (f p))) n (F (f p)))
        (if orientationSign o q E p then q.val (f p) else -q.val (f p)) := by
    rw [htrans, determinantMap_trans (V := TangentSpace S p)
      (W := TangentSpace T (f p)) (X := TangentSpace R (g (f p))) n (E p) (F (f p))]
    rw [rayMap_trans (V := DeterminantLine S p) (W := DeterminantLine T (f p))
      (X := DeterminantLine R (g (f p))), h1]
  cases hs : orientationSign o q E p
  all_goals cases ht : orientationSign q r F (f p)
  all_goals simp only [hs, ht, Bool.false_eq_true, ite_false, ite_true,
    Module.Ray.map_neg, h2, neg_neg] at hmap
  · have hp : Module.Ray.map (determinantMap n (H p)) (o.val p) = r.val (g (f p)) :=
      hmap.trans (neg_neg (r.val (g (f p))))
    have hsign : orientationSign o r H p = true := if_pos hp
    rw [hsign]
    norm_num [signValue]
  · have hne : Module.Ray.map (determinantMap n (H p)) (o.val p) ≠ r.val (g (f p)) := by
      rw [hmap]
      exact (Module.Ray.ne_neg_self (r.val (g (f p)))).symm
    have hsign : orientationSign o r H p = false := if_neg hne
    rw [hsign]
    norm_num [signValue]
  · have hne : Module.Ray.map (determinantMap n (H p)) (o.val p) ≠ r.val (g (f p)) := by
      rw [hmap]
      exact (Module.Ray.ne_neg_self (r.val (g (f p)))).symm
    have hsign : orientationSign o r H p = false := if_neg hne
    rw [hsign]
    norm_num [signValue]
  · have hsign : orientationSign o r H p = true := if_pos hmap
    rw [hsign]
    norm_num [signValue]

/-- Exterior multiplication respects the two ordered factor maps. -/
theorem orderedWedge_natural {V W : Type u} {V' W' : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']
    (m n : ℕ) (A : V ≃ₗ[ℝ] V') (B : W ≃ₗ[ℝ] W')
    (v : ⋀[ℝ]^m V) (w : ⋀[ℝ]^n W) :
    determinantMap (m+n) (A.prodCongr B) (orderedWedge m n V W v w) =
      orderedWedge m n V' W' (determinantMap m A v) (determinantMap n B w) := by
  have h : (orderedWedge m n V W).compr₂
      (determinantMap (m+n) (A.prodCongr B)).toLinearMap =
      (orderedWedge m n V' W').compl₁₂ (determinantMap m A).toLinearMap
        (determinantMap n B).toLinearMap := by
    apply exteriorPower.linearMap_ext (M := V) (N := (⋀[ℝ]^n W) →ₗ[ℝ] (⋀[ℝ]^(m+n) (V' × W')))
    apply AlternatingMap.ext
    intro v
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.compr₂_apply,
      LinearMap.compl₁₂_apply, orderedWedge_basis]
    change exteriorPower.map (m+n) (A.prodCongr B).toLinearMap
        (exteriorPower.ιMulti ℝ (m+n) _) =
        orderedWedge m n V' W' (exteriorPower.map m A.toLinearMap (exteriorPower.ιMulti ℝ m v))
          (exteriorPower.map n B.toLinearMap (exteriorPower.ιMulti ℝ n w))
    simp only [exteriorPower.map_apply_ιMulti]
    rw [orderedWedge_basis]
    congr 1
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Function.comp_def]
    · intro j
      simp [Function.comp_def]
  exact congrArg (fun L => L v w) h

/-- Positivity is preserved by an actual linear isomorphism. -/
theorem isPositive_map {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (A : V ≃ₗ[ℝ] W) {r : Module.Ray ℝ V} {v : V} (h : IsPositive r v) :
    IsPositive (Module.Ray.map A r) (A v) := by
  rcases h with ⟨hv, rfl⟩
  refine ⟨fun h => hv (A.injective (h.trans A.map_zero.symm)), ?_⟩
  exact (Module.Ray.map_apply A v hv).symm


@[simp] theorem determinantMap_apply_symm_apply {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (n : ℕ) (E : V ≃ₗ[ℝ] W) (v : ⋀[ℝ]^n W) :
    determinantMap n E (determinantMap n E.symm v) = v := by
  change (exteriorPower.map n E.toLinearMap) ((exteriorPower.map n E.symm.toLinearMap) v) = v
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  have h : E.toLinearMap.comp E.symm.toLinearMap = LinearMap.id := by ext; simp
  rw [h, exteriorPower.map_id]
  rfl

@[simp] theorem determinantMap_symm_apply_apply {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (n : ℕ) (E : V ≃ₗ[ℝ] W) (v : ⋀[ℝ]^n V) :
    determinantMap n E.symm (determinantMap n E v) = v := by
  exact determinantMap_apply_symm_apply n E.symm v

theorem determinantMap_orderedWedge_change {V W V' W' X : Type u}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']
    [AddCommGroup X] [Module ℝ X]
    (m n : ℕ) (L : X ≃ₗ[ℝ] (V × W))
    (A : V ≃ₗ[ℝ] V') (B : W ≃ₗ[ℝ] W') (v : ⋀[ℝ]^m V) (w : ⋀[ℝ]^n W) :
    determinantMap (m+n) (L.trans (A.prodCongr B)).symm
      (orderedWedge m n V' W' (determinantMap m A v) (determinantMap n B w)) =
      determinantMap (m+n) L.symm (orderedWedge m n V W v w) := by
  apply (determinantMap (m+n) (L.trans (A.prodCongr B))).injective
  rw [determinantMap_apply_symm_apply, determinantMap_trans]
  change _ = determinantMap (m+n) (A.prodCongr B)
    (determinantMap (m+n) L (determinantMap (m+n) L.symm _))
  rw [determinantMap_apply_symm_apply, orderedWedge_natural]

theorem productVector_change {m n : ℕ} {a b a' b' k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold m a M} {T : SmoothManifold n b N}
    {S' : SmoothManifold m a' M} {T' : SmoothManifold n b' N}
    {P : SmoothManifold (m+n) k (M × N)} {p : M × N}
    (L : TangentSpace P p ≃ₗ[ℝ] (TangentSpace S p.1 × TangentSpace T p.2))
    (A : TangentSpace S p.1 ≃ₗ[ℝ] TangentSpace S' p.1)
    (B : TangentSpace T p.2 ≃ₗ[ℝ] TangentSpace T' p.2)
    (v : DeterminantLine S p.1) (w : DeterminantLine T p.2) :
    productVector (S := S') (T := T') (P := P) (p := p)
      (L.trans (A.prodCongr B)) (determinantMap m A v) (determinantMap n B w) =
      productVector (S := S) (T := T) (P := P) (p := p) L v w := by
  simpa only [productVector, determinantMap] using
    (determinantMap_orderedWedge_change (V := TangentSpace S p.1)
    (W := TangentSpace T p.2) (V' := TangentSpace S' p.1)
    (W' := TangentSpace T' p.2) (X := TangentSpace P p) m n L A B v w)

open private smoothGermPullback smoothGermPullback_rep from MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential

theorem identity_differential_equiv {n : ℕ} {a b : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (T : SmoothManifold n b M)
    (hf : IsSmoothMap S T id) (hg : IsSmoothMap T S id) :
    ∃ E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T p,
      (∀ p, IsDifferential S T id p (E p).toLinearMap) ∧
      (∀ p, IsDifferential T S id p (E p).symm.toLinearMap) := by
  let D : Diffeomorph S.smoothStructure.val T.smoothStructure.val :=
    ⟨Equiv.refl M, hf, hg⟩
  have hex (p : M) : ∃ E : TangentSpace S p ≃ₗ[ℝ] TangentSpace T p,
      IsDifferential S T id p E.toLinearMap := differential_diffeomorph S T D p
  choose E hE using hex
  refine ⟨E, hE, ?_⟩
  intro p
  let K := differential T S id hg p
  have hK : IsDifferential T S id p K := differential_spec T S id hg p
  have hid : IsSmoothMap S S id :=
    manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val S.smoothStructure.property.1
  have hKE : K.comp (E p).toLinearMap = LinearMap.id :=
    (differential_exists S S id hid p).unique
      (differential_comp S T S id id hf hg p (E p).toLinearMap K (hE p) hK)
      (differential_id S p)
  have hEq : K = (E p).symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    have hh := congrArg (fun L : TangentSpace S p →ₗ[ℝ] TangentSpace S p => L ((E p).symm v)) hKE
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      LinearMap.id_apply] using hh
  rw [← hEq]
  exact hK

/-- Chain rule needs only smoothness of the postcomposed map when an actual
first differential is already provided; this follows directly on germs. -/
theorem differential_comp_of_target_smooth
    {l n m : ℕ} {c a b : ModelKind} {X M N : Type u}
    [TopologicalSpace X] [TopologicalSpace M] [TopologicalSpace N]
    (P : SmoothManifold l c X) (S : SmoothManifold n a M)
    (T : SmoothManifold m b N) (f : X → M) (g : M → N)
    (hg : IsSmoothMap S T g) (p : X)
    (L : TangentSpace P p →ₗ[ℝ] TangentSpace S (f p))
    (A : TangentSpace S (f p) →ₗ[ℝ] TangentSpace T (g (f p)))
    (hL : IsDifferential P S f p L) (hA : IsDifferential S T g (f p) A) :
    IsDifferential P T (g ∘ f) p (A.comp L) := by
  intro v h k r hr hk
  let j := smoothGermPullback (@mem_smoothGermAlgebra_iff.{u}) S T g hg (f p) h
  have hj := (smoothGermPullback_rep (@mem_smoothGermAlgebra_iff.{u}) S T g hg (f p) h r hr).symm
  exact (hA (L v) h j r hr hj).trans
    (hL v j k (r ∘ g) hj (by simpa only [Function.comp_assoc] using hk))

theorem product_differential_change
    {m n : ℕ} {a a' b b' k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (S' : SmoothManifold m a' M)
    (T : SmoothManifold n b N) (T' : SmoothManifold n b' N)
    (P : SmoothManifold (m+n) k (M × N))
    (hf : IsSmoothMap S S' id) (hg : IsSmoothMap T T' id)
    (p : M × N)
    (L : TangentSpace P p ≃ₗ[ℝ] (TangentSpace S p.1 × TangentSpace T p.2))
    (hL : IsProductDifferential S T P p L)
    (A : TangentSpace S p.1 ≃ₗ[ℝ] TangentSpace S' p.1)
    (B : TangentSpace T p.2 ≃ₗ[ℝ] TangentSpace T' p.2)
    (hA : IsDifferential S S' id p.1 A.toLinearMap)
    (hB : IsDifferential T T' id p.2 B.toLinearMap) :
    IsProductDifferential S' T' P p (L.trans (A.prodCongr B)) := by
  constructor
  · exact differential_comp_of_target_smooth P S S' Prod.fst id hf p
      ((LinearMap.fst ℝ _ _).comp L.toLinearMap) A.toLinearMap hL.1 hA
  · exact differential_comp_of_target_smooth P T T' Prod.snd id hg p
      ((LinearMap.snd ℝ _ _).comp L.toLinearMap) B.toLinearMap hL.2 hB

theorem ordinary_product_representations
    {m n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (h : intrinsicBoundary S = ∅ ∨ intrinsicBoundary T = ∅) :
    ∃ a' b' k, ∃ S' : SmoothManifold m a' M, ∃ T' : SmoothManifold n b' N,
    ∃ C : ProductCoordinates m a' n b' k,
    ∃ P : SmoothManifold (m+n) k (M × N),
      IsSmoothMap S S' id ∧ IsSmoothMap S' S id ∧
      IsSmoothMap T T' id ∧ IsSmoothMap T' T id ∧
      P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (productAtlas C S'.smoothStructure.val T'.smoothStructure.val) := by
  rcases h with hS | hT
  · obtain ⟨S', hSS', hS'S, C, P, _, hP⟩ := exists_product_leftBoundaryless S T hS
    have hTT : IsSmoothMap T T id :=
      manifoldContDiff_id (⊤ : ℕ∞) T.smoothStructure.val T.smoothStructure.property.1
    exact ⟨.euclidean, b, _, S', T, C, P, hSS', hS'S, hTT, hTT, hP⟩
  · obtain ⟨T', hTT', hT'T, C, P, _, hP⟩ := exists_product_rightBoundaryless S T hT
    have hSS : IsSmoothMap S S id :=
      manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val S.smoothStructure.property.1
    exact ⟨a, .euclidean, _, S, T', C, P, hSS, hSS, hTT', hT'T, hP⟩

/-- The ordinary product has the smooth universal property in the original
factor structures, with intrinsic tangent splitting for these same factors. -/
theorem ordinary_product_geometry
    {m n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (h : intrinsicBoundary S = ∅ ∨ intrinsicBoundary T = ∅) :
    ∃ a' b' k, ∃ S' : SmoothManifold m a' M, ∃ T' : SmoothManifold n b' N,
    ∃ C : ProductCoordinates m a' n b' k,
    ∃ P : SmoothManifold (m+n) k (M × N),
      IsSmoothMap S S' id ∧ IsSmoothMap S' S id ∧
      IsSmoothMap T T' id ∧ IsSmoothMap T' T id ∧
      P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (productAtlas C S'.smoothStructure.val T'.smoothStructure.val) ∧
      IsSmoothMap P S Prod.fst ∧ IsSmoothMap P T Prod.snd ∧
      (∀ {l : ℕ} {c : ModelKind} {Q : Type u} [TopologicalSpace Q]
        (R : SmoothManifold l c Q) (f : Q → M) (g : Q → N),
        IsSmoothMap R S f → IsSmoothMap R T g →
          IsSmoothMap R P (fun x => (f x, g x))) ∧
      (∀ p, ∃ E, IsProductDifferential S T P p E) := by
  obtain ⟨a', b', k, S', T', C, P, hSS', hS'S, hTT', hT'T, hP⟩ :=
    ordinary_product_representations S T h
  obtain ⟨hfst', hsnd', hsplit'⟩ := differential_product S' T' C P hP
  have hfst : IsSmoothMap P S Prod.fst :=
    manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ S'.smoothStructure.property.1.1
      Prod.fst id hfst' hS'S
  have hsnd : IsSmoothMap P T Prod.snd :=
    manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ T'.smoothStructure.property.1.1
      Prod.snd id hsnd' hT'T
  refine ⟨a', b', k, S', T', C, P, hSS', hS'S, hTT', hT'T, hP, hfst, hsnd, ?_, ?_⟩
  · intro l c Q _ R f g hf hg
    have hf' : IsSmoothMap R S' f :=
      manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ S.smoothStructure.property.1.1 f id hf hSS'
    have hg' : IsSmoothMap R T' g :=
      manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ T.smoothStructure.property.1.1 g id hg hTT'
    exact (differential_pair S' T' R C P hP f g hf' hg').1
  · obtain ⟨A, _, hAinv⟩ := identity_differential_equiv S S' hSS' hS'S
    obtain ⟨B, _, hBinv⟩ := identity_differential_equiv T T' hTT' hT'T
    intro p
    obtain ⟨L, hL⟩ := hsplit' p
    refine ⟨L.trans ((A p.1).symm.prodCongr (B p.2).symm), ?_⟩
    exact product_differential_change S' S T' T P hS'S hT'T p L hL
      (A p.1).symm (B p.2).symm (hAinv p.1) (hBinv p.2)


theorem determinantMap_isPositive {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (n : ℕ) (A : V ≃ₗ[ℝ] W) {r : Module.Ray ℝ (⋀[ℝ]^n V)} {v : ⋀[ℝ]^n V}
    (hv : IsPositive r v) :
    IsPositive (Module.Ray.map (determinantMap n A) r) (determinantMap n A v) := by
  exact isPositive_map (determinantMap n A) hv

theorem product_positivity_transport {V W V' W' X : Type u}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']
    [AddCommGroup X] [Module ℝ X]
    (m n : ℕ) (L : X ≃ₗ[ℝ] (V × W))
    (A : V ≃ₗ[ℝ] V') (B : W ≃ₗ[ℝ] W')
    (o : Module.Ray ℝ (⋀[ℝ]^m V)) (o' : Module.Ray ℝ (⋀[ℝ]^m V'))
    (q : Module.Ray ℝ (⋀[ℝ]^n W)) (q' : Module.Ray ℝ (⋀[ℝ]^n W'))
    (r : Module.Ray ℝ (⋀[ℝ]^(m+n) X))
    (ho : Module.Ray.map (determinantMap m A) o = o')
    (hq : Module.Ray.map (determinantMap n B) q = q')
    (hp : ∀ v' w', IsPositive o' v' → IsPositive q' w' →
      IsPositive r (determinantMap (m+n) (L.trans (A.prodCongr B)).symm
        (orderedWedge m n V' W' v' w')))
    (v : ⋀[ℝ]^m V) (w : ⋀[ℝ]^n W) (hv : IsPositive o v) (hw : IsPositive q w) :
    IsPositive r (determinantMap (m+n) L.symm (orderedWedge m n V W v w)) := by
  have hv' : IsPositive o' (determinantMap m A v) := by
    rw [← ho]
    exact determinantMap_isPositive m A hv
  have hw' : IsPositive q' (determinantMap n B w) := by
    rw [← hq]
    exact determinantMap_isPositive n B hw
  have hx := hp _ _ hv' hw'
  have heq := determinantMap_orderedWedge_change m n L A B v w
  exact heq ▸ hx

/-- Product positivity is invariant under smooth re-presentations of the factors
whose identity differential transports their orientations. -/
theorem productOrientation_factorChange
    {m n : ℕ} {a a' b b' k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (S' : SmoothManifold m a' M)
    (T : SmoothManifold n b N) (T' : SmoothManifold n b' N)
    (P : SmoothManifold (m+n) k (M × N))
    (hf : IsSmoothMap S S' id) (hg : IsSmoothMap T T' id)
    (A : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace S' p)
    (B : ∀ p, TangentSpace T p ≃ₗ[ℝ] TangentSpace T' p)
    (hA : ∀ p, IsDifferential S S' id p (A p).toLinearMap)
    (hB : ∀ p, IsDifferential T T' id p (B p).toLinearMap)
    (o : Orientation S) (o' : Orientation S')
    (q : Orientation T) (q' : Orientation T') (r : Orientation P)
    (ho : ∀ p, Module.Ray.map (determinantMap (V := TangentSpace S p)
      (W := TangentSpace S' p) m (A p)) (o.val p) = o'.val p)
    (hq : ∀ p, Module.Ray.map (determinantMap (V := TangentSpace T p)
      (W := TangentSpace T' p) n (B p)) (q.val p) = q'.val p)
    (hr : IsProductOrientation (S := S') (T := T') (P := P) o' q' r) :
    IsProductOrientation (S := S) (T := T) (P := P) o q r := by
  intro p L hL v w hv hw
  have H : ∀ v' w', IsPositive (o'.val p.1) v' → IsPositive (q'.val p.2) w' →
      IsPositive (r.val p) (determinantMap
        (V := TangentSpace S' p.1 × TangentSpace T' p.2)
        (W := TangentSpace P p) (m+n)
        (L.trans ((A p.1).prodCongr (B p.2))).symm
          (orderedWedge m n (TangentSpace S' p.1) (TangentSpace T' p.2) v' w')) := by
    intro v' w' hv' hw'
    simpa only [productVector, determinantMap] using
      (hr p (L.trans ((A p.1).prodCongr (B p.2)))
        (product_differential_change S S' T T' P hf hg p L hL
          (A p.1) (B p.2) (hA p.1) (hB p.2)) v' w' hv' hw')
  have F := product_positivity_transport (V := TangentSpace S p.1) (W := TangentSpace T p.2)
      (V' := TangentSpace S' p.1) (W' := TangentSpace T' p.2) (X := TangentSpace P p)
      m n L (A p.1) (B p.2) (o.val p.1) (o'.val p.1) (q.val p.2) (q'.val p.2)
      (r.val p)
  have G := F (ho p.1) (hq p.2) H
  have HH := G v w hv hw
  simpa only [productVector, determinantMap] using HH


@[simp] theorem determinantMap_symm {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (n : ℕ) (E : V ≃ₗ[ℝ] W) :
    determinantMap n E.symm = (determinantMap n E).symm := by
  apply LinearEquiv.ext
  intro v
  apply (determinantMap n E).injective
  rw [determinantMap_apply_symm_apply, LinearEquiv.apply_symm_apply]

@[simp] theorem rayMap_determinant_symm_apply_apply {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (n : ℕ) (E : V ≃ₗ[ℝ] W) (r : Module.Ray ℝ (⋀[ℝ]^n V)) :
    Module.Ray.map (determinantMap n E.symm)
      (Module.Ray.map (determinantMap n E) r) = r := by
  rw [determinantMap_symm, ← Module.Ray.map_symm]
  exact Equiv.symm_apply_apply _ r

/-- The top exterior power of an endomorphism is multiplication by its
ordinary determinant, including the zeroth power. -/
theorem topExterior_map_eq_smul {n : ℕ} (A : Euclidean n →ₗ[ℝ] Euclidean n)
    (v : ⋀[ℝ]^n (Euclidean n)) :
    exteriorPower.map n A v = A.det • v := by
  let b := Pi.basisFun ℝ (Fin n)
  let t := exteriorPower.ιMulti ℝ n b
  let d : (⋀[ℝ]^n (Euclidean n)) →ₗ[ℝ] ℝ :=
    exteriorPower.alternatingMapLinearEquiv b.det
  have hdim : finrank ℝ (⋀[ℝ]^n (Euclidean n)) = 1 := by
    simp [exteriorPower.finrank_eq, Module.finrank_pi]
  have hdt : d t = 1 := by
    simpa only [d, t, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti] using b.det_self
  have hi : Function.Injective d := by
    intro x y hxy
    obtain ⟨r, hr⟩ := exists_smul_eq_of_finrank_eq_one hdim (basisWedge_ne_zero b) x
    obtain ⟨s, hs⟩ := exists_smul_eq_of_finrank_eq_one hdim (basisWedge_ne_zero b) y
    have hrs : r = s := by
      have := hxy
      rw [← hr, ← hs, map_smul, map_smul, hdt] at this
      simpa using this
    rw [← hr, ← hs, hrs]
  obtain ⟨r, hr⟩ := exists_smul_eq_of_finrank_eq_one hdim (basisWedge_ne_zero b) v
  rw [← hr]
  simp only [map_smul]
  rw [← smul_comm r A.det]
  congr 1
  apply hi
  simp only [t, exteriorPower.map_apply_ιMulti, d,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_smul]
  simpa only [Basis.det_self, mul_one, smul_eq_mul] using b.det_comp A b

/-- The action on either determinant ray depends only on the sign of the
ordinary determinant. -/
theorem topExterior_ray_map {n : ℕ} (A : Euclidean n ≃ₗ[ℝ] Euclidean n)
    (r : Module.Ray ℝ (⋀[ℝ]^n (Euclidean n))) :
    Module.Ray.map (determinantMap n A) r =
      if 0 < A.toLinearMap.det then r else -r := by
  induction r using Module.Ray.ind with | h v hv =>
    rw [Module.Ray.map_apply]
    change rayOfNeZero ℝ (exteriorPower.map n A.toLinearMap v) _ = _
    by_cases h : 0 < A.toLinearMap.det
    · rw [if_pos h]
      apply (ray_eq_iff _ _).mpr
      rw [topExterior_map_eq_smul]
      exact SameRay.sameRay_pos_smul_left v h
    · rw [if_neg h, neg_rayOfNeZero]
      apply (ray_eq_iff _ _).mpr
      rw [topExterior_map_eq_smul]
      have hd : A.toLinearMap.det < 0 :=
        lt_of_le_of_ne (le_of_not_gt h) (by simpa only [LinearEquiv.coe_det] using A.det.ne_zero)
      have heq : A.toLinearMap.det • v = (-A.toLinearMap.det) • (-v) := by simp
      rw [heq]
      exact SameRay.sameRay_pos_smul_left (-v) (neg_pos.mpr hd)

/-- Coordinate transport commutes with the actual exterior differential. -/
theorem determinantRay_conjugate {V W : Type u}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {n : ℕ} (U : V ≃ₗ[ℝ] Euclidean n) (Z : W ≃ₗ[ℝ] Euclidean n)
    (E : V ≃ₗ[ℝ] W) (r : Module.Ray ℝ (⋀[ℝ]^n V)) :
    Module.Ray.map (determinantMap n Z) (Module.Ray.map (determinantMap n E) r) =
      Module.Ray.map (determinantMap n (U.symm.trans (E.trans Z)))
        (Module.Ray.map (determinantMap n U) r) := by
  rw [← rayMap_trans, ← determinantMap_trans, ← rayMap_trans, ← determinantMap_trans]
  have he : U.trans (U.symm.trans (E.trans Z)) = E.trans Z := by
    ext v
    simp
  rw [he]

/-- A continuous family of invertible coordinate matrices transports locally
constant rays to locally constant rays. No topology on chosen representatives
of a ray is used. -/
theorem coordinateRayTransport_locallyConstant {X : Type u} [TopologicalSpace X]
    {n : ℕ} (A : X → Euclidean n ≃ₗ[ℝ] Euclidean n)
    (hA : Continuous (fun x => (A x).toLinearMap.det))
    (r : X → Module.Ray ℝ (⋀[ℝ]^n (Euclidean n))) (hr : IsLocallyConstant r) :
    IsLocallyConstant (fun x => Module.Ray.map (determinantMap n (A x)) (r x)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hd : ∀ᶠ y in 𝓝 x, (0 < (A y).toLinearMap.det ↔ 0 < (A x).toLinearMap.det) := by
    by_cases hx : 0 < (A x).toLinearMap.det
    · filter_upwards [hA.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hx)] with y hy
      exact iff_of_true hy hx
    · have hx' : (A x).toLinearMap.det < 0 := lt_of_le_of_ne (le_of_not_gt hx)
        (by simpa only [LinearEquiv.coe_det] using (A x).det.ne_zero)
      filter_upwards [hA.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hx')] with y hy
      exact iff_of_false (not_lt_of_ge hy.le) hx
  filter_upwards [hr.eventually_eq x, hd] with y hyr hyd
  simp only [topExterior_ray_map, hyr, hyd]

theorem determinantRay_eq_iff {V W : Type u}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {n : ℕ} (U : V ≃ₗ[ℝ] Euclidean n) (Z : W ≃ₗ[ℝ] Euclidean n)
    (E : V ≃ₗ[ℝ] W) (r : Module.Ray ℝ (⋀[ℝ]^n V))
    (s : Module.Ray ℝ (⋀[ℝ]^n W)) :
    Module.Ray.map (determinantMap n E) r = s ↔
      Module.Ray.map (determinantMap n (U.symm.trans (E.trans Z)))
          (Module.Ray.map (determinantMap n U) r) =
        Module.Ray.map (determinantMap n Z) s := by
  rw [← determinantRay_conjugate U Z E r]
  exact (Module.Ray.map (determinantMap n Z)).injective.eq_iff.symm


/-- In local source and target charts, the coordinate differential has a
continuous determinant on a neighborhood. -/
theorem local_sign_locallyConstant :
    ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N),
    IsLocalDiffeomorphism S T f → ∀ (o : Orientation S) (q : Orientation T)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p)),
    (∀ p, IsDifferential S T f p (E p).toLinearMap) →
    IsLocallyConstant (orientationSign o q E) := by
  intro n a b M N _ _ S T f hf o q E hE
  have hf' := IsLocalDiffeomorphism.smooth hf
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun p => (hf' p).1)
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  obtain ⟨L⟩ := TangentBundle.fiberCoordinates_exists T
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p)
  obtain ⟨U, hU, hpU, F, hF, hFeq⟩ := (hf' p).2 c hc d hd hp hfp
  obtain ⟨V, hVeq, hV, hpV⟩ := mem_nhds_iff.mp hFeq
  let O : Set M := c.source ∩ f ⁻¹' d.source ∩ V ∩ (fun x => (c x).val) ⁻¹' U
  have hO : IsOpen O := by
    have hcu : IsOpen (c.source ∩ (fun x => (c x).val) ⁻¹' U) :=
      (continuous_subtype_val.comp_continuousOn c.continuousOn).isOpen_inter_preimage c.open_source hU
    convert (hcu.inter (d.open_source.preimage hfc)).inter hV using 1
    ext x
    simp only [O, mem_inter_iff, mem_preimage]
    tauto
  have hpO : p ∈ O := ⟨⟨⟨hp, hfp⟩, hpV⟩, hpU⟩
  let u (x : O) := K.equiv c hc x.val x.property.1.1.1
  let z (x : O) := L.equiv d hd (f x.val) x.property.1.1.2
  let A (x : O) : Euclidean n ≃ₗ[ℝ] Euclidean n :=
    (u x).symm.trans ((E x.val).trans (z x))
  have hjac (x : O) : (A x).toLinearMap = (fderiv ℝ F (c x.val).val).toLinearMap := by
    apply LinearMap.ext
    intro v
    have hrep : (fun y => F (c y).val) =ᶠ[𝓝 x.val] (fun y => (d (f y)).val) :=
      Filter.mem_of_superset (hV.mem_nhds x.property.1.2) hVeq
    exact (differential_jacobian S T f hf' x.val (E x.val).toLinearMap (hE x.val)
      c d hc hd x.property.1.1.1 x.property.1.1.2 (u x) (z x)
      (K.isCoordinates c hc _ _) (L.isCoordinates d hd _ _)
      U F hU x.property.2 hF hrep ((u x).symm v)).trans
        (by rw [LinearEquiv.apply_symm_apply]; rfl)
  have hcc : Continuous (fun x : O => (c x.val).val) :=
    continuous_subtype_val.comp
      (c.continuousOn.comp_continuous continuous_subtype_val (fun x => x.property.1.1.1))
  have hderF : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hU (by simp)
  have hder : Continuous (fun x : O => fderiv ℝ F (c x.val).val) :=
    hderF.continuousOn.comp_continuous hcc (fun x => x.property.2)
  have hdet : Continuous (fun x : O => (A x).toLinearMap.det) := by
    simp_rw [hjac]
    exact ContinuousLinearMap.continuous_det.comp hder
  let ro (x : O) : Module.Ray ℝ (⋀[ℝ]^n (Euclidean n)) := Module.Ray.map (determinantMap n (u x)) (o.val x.val)
  let rq (x : O) : Module.Ray ℝ (⋀[ℝ]^n (Euclidean n)) := Module.Ray.map (determinantMap n (z x)) (q.val (f x.val))
  have hro : IsLocallyConstant ro :=
    (o.property K c hc).comp_continuous
      (f := fun x : O => (⟨x.val, x.property.1.1.1⟩ : c.source))
      (continuous_subtype_val.subtype_mk _)
  have hrq : IsLocallyConstant rq :=
    (q.property L d hd).comp_continuous
      (f := fun x : O => (⟨f x.val, x.property.1.1.2⟩ : d.source))
      ((hfc.comp continuous_subtype_val).subtype_mk _)
  have hs := (coordinateRayTransport_locallyConstant A hdet ro hro).comp₂ hrq
    (fun r s => if r = s then true else false)
  have heq (x : O) : orientationSign o q E x.val =
      (if Module.Ray.map (determinantMap n (A x)) (ro x) = rq x then true else false) := by
    have hiff := determinantRay_eq_iff (u x) (z x) (E x.val) (o.val x.val) (q.val (f x.val))
    simp only [orientationSign, hiff]
    rfl
  have hs' : IsLocallyConstant (fun x : O => orientationSign o q E x.val) := by
    simpa only [← heq] using hs
  have hn := hs'.eventually_eq ⟨p, hpO⟩
  have hn' : ∀ᶠ x in 𝓝[O] p, orientationSign o q E x = orientationSign o q E p := by
    rwa [← map_nhds_subtype_val ⟨p, hpO⟩]
  rwa [hO.nhdsWithin_eq hpO] at hn'



/-- Pulling back an orientation by an everywhere invertible actual differential
preserves continuity of determinant rays. -/
theorem pullbackRayField_continuous {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (q : Orientation T)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p))
    (hE : ∀ p, IsDifferential S T f p (E p).toLinearMap) :
    IsContinuousRayField (fun p =>
      Module.Ray.map (determinantMap n (E p).symm) (q.val (f p))) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun p => (hf p).1)
  obtain ⟨L⟩ := TangentBundle.fiberCoordinates_exists T
  intro K c hc
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro p
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p.val)
  obtain ⟨U, hU, hpU, F, hF, hFeq⟩ := (hf p.val).2 c hc d hd p.property hfp
  obtain ⟨V, hVeq, hV, hpV⟩ := mem_nhds_iff.mp hFeq
  let O : Set c.source := (fun x => f x.val) ⁻¹' d.source ∩
    Subtype.val ⁻¹' V ∩ (fun x => (c x.val).val) ⁻¹' U
  have hcc0 : Continuous (fun x : c.source => (c x.val).val) :=
    continuous_subtype_val.comp
      (c.continuousOn.comp_continuous continuous_subtype_val (fun x => x.property))
  have hO : IsOpen O :=
    ((d.open_source.preimage (hfc.comp continuous_subtype_val)).inter
      (hV.preimage continuous_subtype_val)).inter (hU.preimage hcc0)
  have hpO : p ∈ O := ⟨⟨hfp, hpV⟩, hpU⟩
  let u (x : O) := K.equiv c hc x.val.val x.val.property
  let z (x : O) := L.equiv d hd (f x.val.val) x.property.1.1
  let A (x : O) : Euclidean n ≃ₗ[ℝ] Euclidean n :=
    (u x).symm.trans ((E x.val.val).trans (z x))
  have hjac (x : O) : (A x).toLinearMap =
      (fderiv ℝ F (c x.val.val).val).toLinearMap := by
    apply LinearMap.ext
    intro v
    have hrep : (fun y => F (c y).val) =ᶠ[𝓝 x.val.val]
        (fun y => (d (f y)).val) :=
      Filter.mem_of_superset (hV.mem_nhds x.property.1.2) hVeq
    exact (differential_jacobian S T f hf x.val.val (E x.val.val).toLinearMap
      (hE x.val.val) c d hc hd x.val.property x.property.1.1 (u x) (z x)
      (K.isCoordinates c hc _ _) (L.isCoordinates d hd _ _)
      U F hU x.property.2 hF hrep ((u x).symm v)).trans
        (by rw [LinearEquiv.apply_symm_apply]; rfl)
  have hcc : Continuous (fun x : O => (c x.val.val).val) :=
    hcc0.comp continuous_subtype_val
  have hderF : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hU (by simp)
  have hder : Continuous (fun x : O => fderiv ℝ F (c x.val.val).val) :=
    hderF.continuousOn.comp_continuous hcc (fun x => x.property.2)
  have hdet : Continuous (fun x : O => (A x).toLinearMap.det) := by
    simp_rw [hjac]
    exact ContinuousLinearMap.continuous_det.comp hder
  have hdetInv : Continuous (fun x : O => ((A x).symm).toLinearMap.det) := by
    have heq (x : O) : ((A x).symm).toLinearMap.det = ((A x).toLinearMap.det)⁻¹ := by
      rw [← LinearEquiv.coe_inv_det, Units.val_inv_eq_inv_val, LinearEquiv.coe_det]
    simp_rw [heq]
    exact hdet.inv₀ (fun x => by simpa only [LinearEquiv.coe_det] using (A x).det.ne_zero)
  let rq (x : O) : Module.Ray ℝ (⋀[ℝ]^n (Euclidean n)) :=
    Module.Ray.map (determinantMap n (z x)) (q.val (f x.val.val))
  have hrq : IsLocallyConstant rq :=
    (q.property L d hd).comp_continuous
      (f := fun x : O => (⟨f x.val.val, x.property.1.1⟩ : d.source))
      ((hfc.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)
  have hs := coordinateRayTransport_locallyConstant (fun x => (A x).symm) hdetInv rq hrq
  have heq (x : O) :
      Module.Ray.map (determinantCoordinates K c hc x.val)
          (Module.Ray.map (determinantMap n (E x.val.val).symm) (q.val (f x.val.val))) =
        Module.Ray.map (determinantMap n (A x).symm) (rq x) := by
    have hsymm : (z x).symm.trans ((E x.val.val).symm.trans (u x)) = (A x).symm := by
      ext v
      rfl
    simpa only [determinantCoordinates, determinantMap, u, rq, hsymm] using
      (determinantRay_conjugate (V := TangentSpace T (f x.val.val))
        (W := TangentSpace S x.val.val) (z x) (u x) (E x.val.val).symm
        (q.val (f x.val.val)))
  have hs' : IsLocallyConstant (fun x : O =>
      Module.Ray.map (determinantCoordinates K c hc x.val)
        (Module.Ray.map (determinantMap n (E x.val.val).symm) (q.val (f x.val.val)))) := by
    simpa only [heq] using hs
  have hn := hs'.eventually_eq ⟨p, hpO⟩
  have hn' : ∀ᶠ x in 𝓝[O] p,
      Module.Ray.map (determinantCoordinates K c hc x)
          (Module.Ray.map (determinantMap n (E x.val).symm) (q.val (f x.val))) =
        Module.Ray.map (determinantCoordinates K c hc p)
          (Module.Ray.map (determinantMap n (E p.val).symm) (q.val (f p.val))) := by
    rwa [← map_nhds_subtype_val ⟨p, hpO⟩]
  rwa [hO.nhdsWithin_eq hpO] at hn'

set_option linter.unusedVariables false in
theorem local_sign_conditional
    (h_comparison : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h_connected_two : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h_empty : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h_generators_orientation : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h_positive_multiple : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h_positive_top_form : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h_signed_charts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h_signed_orientation : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h_smooth_generators : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h_top_form_quotient : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h_transition_jacobian : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h_zero_dimension : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u})
    : Specs.SmoothManifolds.Orientations.ProductsAndSigns.local_signType.{u} := by
  intro n a b M N _ _ S T f hf o q E hE
  exact ⟨local_sign_locallyConstant S T f hf o q E hE,
    fun p => orientationSign_rays o q E p⟩


lemma determinantRay_coordinate_change {V : Type u}
    [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (E F : V ≃ₗ[ℝ] Euclidean n) (r : Module.Ray ℝ (⋀[ℝ]^n V)) :
    Module.Ray.map (determinantMap n (E.symm.trans F))
        (Module.Ray.map (determinantMap n E) r) =
      Module.Ray.map (determinantMap n F) r := by
  rw [← rayMap_trans, ← determinantMap_trans]
  have hEF : E.trans (E.symm.trans F) = F := by
    ext v
    simp
  rw [hEF]

/-- Local constancy in a generating chart cover is intrinsic. -/
lemma isContinuousRayField_of_cover {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (A : Set (ModelChart n a M)) (hAS : A ⊆ S.smoothStructure.val)
    (hcover : ∀ p, ∃ e ∈ A, p ∈ e.source) (r : RayField S)
    (hr : ∀ (K : FiberCoordinates S) e (he : e ∈ A),
      IsLocallyConstant (fun x : e.source =>
        Module.Ray.map (determinantCoordinates K e (hAS he) x) (r x.val))) :
    IsContinuousRayField r := by
  intro K c hc
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro p
  obtain ⟨e, he, hpe⟩ := hcover p.val
  obtain ⟨U, hU, hpU, B, hB, hBeq⟩ := TangentBundle.transition_smooth S K e c
    (hAS he) hc p.val hpe p.property
  let O : Set c.source := {x | x.val ∈ e.source ∧ (e x.val).val ∈ U}
  have hO : IsOpen O := by
    have hu : IsOpen (e.source ∩ (fun x => (e x).val) ⁻¹' U) :=
      (continuous_subtype_val.comp_continuousOn e.continuousOn).isOpen_inter_preimage e.open_source hU
    exact hu.preimage continuous_subtype_val
  have hpO : p ∈ O := ⟨hpe, hpU⟩
  let E (x : O) := K.equiv e (hAS he) x.val.val x.property.1
  let F (x : O) := K.equiv c hc x.val.val x.val.property
  let L (x : O) : Euclidean n ≃ₗ[ℝ] Euclidean n := (E x).symm.trans (F x)
  have hjac (x : O) : (L x).toLinearMap = (B (e x.val.val).val).toLinearMap := by
    apply LinearMap.ext
    intro v
    exact (hBeq x.val.val x.property.1 x.val.property x.property.2 v).symm
  have hec : Continuous (fun x : O => (e x.val.val).val) :=
    continuous_subtype_val.comp
      (e.continuousOn.comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.property.1))
  have hdet : Continuous (fun x : O => (L x).toLinearMap.det) := by
    simp_rw [hjac]
    exact ContinuousLinearMap.continuous_det.comp
      (hB.continuousOn.comp_continuous hec (fun x => x.property.2))
  let rE (x : O) := Module.Ray.map (determinantMap n (E x)) (r x.val.val)
  have hrE : IsLocallyConstant rE := (hr K e he).comp_continuous
    (f := fun x : O => (⟨x.val.val, x.property.1⟩ : e.source))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
  have hl := coordinateRayTransport_locallyConstant L hdet rE hrE
  have heq (x : O) : Module.Ray.map (determinantMap n (L x)) (rE x) =
      Module.Ray.map (determinantCoordinates K c hc x.val) (r x.val.val) := by
    simpa only [L, rE, E, F, determinantCoordinates, determinantMap] using
      (determinantRay_coordinate_change (E x) (F x) (r x.val.val))
  have hl' : IsLocallyConstant (fun x : O =>
      Module.Ray.map (determinantCoordinates K c hc x.val) (r x.val.val)) := by
    simpa only [heq] using hl
  have hn := hl'.eventually_eq ⟨p, hpO⟩
  have hn' : ∀ᶠ x in 𝓝[O] p,
      Module.Ray.map (determinantCoordinates K c hc x) (r x.val) =
        Module.Ray.map (determinantCoordinates K c hc p) (r p.val) := by
    rwa [← map_nhds_subtype_val ⟨p, hpO⟩]
  rwa [hO.nhdsWithin_eq hpO] at hn'

lemma positive_map {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {r : Module.Ray ℝ V} {v : V} (h : IsPositive r v) (E : V ≃ₗ[ℝ] W) :
    IsPositive (Module.Ray.map E r) (E v) := by
  obtain ⟨hv, hr⟩ := h
  refine ⟨E.map_ne_zero_iff.mpr hv, ?_⟩
  rw [← hr, Module.Ray.map_apply]

lemma positive_ray_eq {V : Type u} [AddCommGroup V] [Module ℝ V]
    {r s : Module.Ray ℝ V} {v : V} (hr : IsPositive r v) (hs : IsPositive s v) : r = s :=
  hr.2.symm.trans hs.2

lemma orderedProductRay_natural {V W : Type u} {V' W' : Type v}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup V'] [Module ℝ V'] [AddCommGroup W'] [Module ℝ W']
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    [FiniteDimensional ℝ V'] [FiniteDimensional ℝ W']
    {m n : ℕ} (hm : finrank ℝ V = m) (hn : finrank ℝ W = n)
    (hm' : finrank ℝ V' = m) (hn' : finrank ℝ W' = n)
    (E : V ≃ₗ[ℝ] V') (F : W ≃ₗ[ℝ] W')
    (r : Module.Ray ℝ (⋀[ℝ]^m V)) (s : Module.Ray ℝ (⋀[ℝ]^n W)) :
    Module.Ray.map (determinantMap (m+n) (E.prodCongr F)) (orderedProductRay hm hn r s) =
      orderedProductRay hm' hn' (Module.Ray.map (determinantMap m E) r)
        (Module.Ray.map (determinantMap n F) s) := by
  have hp := positive_map (orderedProductRay_positive hm hn r s
    ⟨r.someVector_ne_zero, r.someVector_ray⟩ ⟨s.someVector_ne_zero, s.someVector_ray⟩)
    (determinantMap (m+n) (E.prodCongr F))
  rw [orderedWedge_natural] at hp
  exact positive_ray_eq hp (orderedProductRay_positive hm' hn' _ _
    (positive_map (show IsPositive r r.someVector from ⟨r.someVector_ne_zero, r.someVector_ray⟩)
      (determinantMap m E))
    (positive_map (show IsPositive s s.someVector from ⟨s.someVector_ne_zero, s.someVector_ray⟩)
      (determinantMap n F)))

lemma productDifferential_unique {m n : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold m a M} {T : SmoothManifold n b N}
    {P : SmoothManifold (m+n) k (M × N)}
    (hf : IsSmoothMap P S Prod.fst) (hg : IsSmoothMap P T Prod.snd)
    (p : M × N) (E F : TangentSpace P p ≃ₗ[ℝ] (TangentSpace S p.1 × TangentSpace T p.2))
    (hE : IsProductDifferential S T P p E) (hF : IsProductDifferential S T P p F) : E = F := by
  apply LinearEquiv.ext
  intro v
  exact Prod.ext
    (congrArg (fun L => L v) ((differential_exists P S Prod.fst hf p).unique hE.1 hF.1))
    (congrArg (fun L => L v) ((differential_exists P T Prod.snd hg p).unique hE.2 hF.2))

def productRayField {m n : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold m a M} {T : SmoothManifold n b N}
    {P : SmoothManifold (m+n) k (M × N)}
    (E : ∀ p, TangentSpace P p ≃ₗ[ℝ] (TangentSpace S p.1 × TangentSpace T p.2))
    (o : Orientation S) (q : Orientation T) : RayField P := fun p =>
  letI := (tangent_dimension S p.1).1
  letI := (tangent_dimension T p.2).1
  Module.Ray.map (determinantMap (m+n) (E p).symm)
    (orderedProductRay (tangent_dimension S p.1).2 (tangent_dimension T p.2).2
      (o.val p.1) (q.val p.2))

lemma productRayField_positive {m n : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold m a M} {T : SmoothManifold n b N}
    {P : SmoothManifold (m+n) k (M × N)}
    (E : ∀ p, TangentSpace P p ≃ₗ[ℝ] (TangentSpace S p.1 × TangentSpace T p.2))
    (o : Orientation S) (q : Orientation T) (p : M × N)
    (v : DeterminantLine S p.1) (w : DeterminantLine T p.2)
    (hv : IsPositive (o.val p.1) v) (hw : IsPositive (q.val p.2) w) :
    IsPositive (productRayField (S := S) (T := T) (P := P) E o q p) (productVector (S := S) (T := T) (P := P) (p := p) (E p) v w) := by
  letI := (tangent_dimension S p.1).1
  letI := (tangent_dimension T p.2).1
  exact positive_map (V := ⋀[ℝ]^(m+n) (TangentData.TangentSpace S p.1 × TangentData.TangentSpace T p.2))
    (W := DeterminantLine P p)
    (orderedProductRay_positive (V := TangentData.TangentSpace S p.1)
    (W := TangentData.TangentSpace T p.2) (tangent_dimension S p.1).2
    (tangent_dimension T p.2).2 (o.val p.1) (q.val p.2) hv hw)
    (determinantMap (m+n) (E p).symm)

lemma productOrientation_unique {m n : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold m a M} {T : SmoothManifold n b N}
    {P : SmoothManifold (m+n) k (M × N)}
    (E : ∀ p, TangentSpace P p ≃ₗ[ℝ] (TangentSpace S p.1 × TangentSpace T p.2))
    (hE : ∀ p, IsProductDifferential S T P p (E p))
    (o : Orientation S) (q : Orientation T) (r : Orientation P)
    (hr : IsProductOrientation o q r) : r.val = productRayField (S := S) (T := T) (P := P) E o q := by
  funext p
  exact positive_ray_eq (hr p (E p) (hE p) (o.val p.1).someVector (q.val p.2).someVector
    ⟨(o.val p.1).someVector_ne_zero, (o.val p.1).someVector_ray⟩
    ⟨(q.val p.2).someVector_ne_zero, (q.val p.2).someVector_ray⟩)
      (productRayField_positive (S := S) (T := T) (P := P) E o q p _ _
        ⟨(o.val p.1).someVector_ne_zero, (o.val p.1).someVector_ray⟩
        ⟨(q.val p.2).someVector_ne_zero, (q.val p.2).someVector_ray⟩)




open private product_chart_mem from MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential

lemma productDifferential_coordinates {m n : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (C : ProductCoordinates m a n b k) (P : SmoothManifold (m+n) k (M × N))
    (hP : P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C S.smoothStructure.val T.smoothStructure.val))
    (K : FiberCoordinates S) (L : FiberCoordinates T) (H : FiberCoordinates P)
    (c : ModelChart m a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (p : M × N) (hp : p ∈ (productChart C c d).source)
    (E : TangentSpace P p ≃ₗ[ℝ] (TangentSpace S p.1 × TangentSpace T p.2))
    (hE : IsProductDifferential S T P p E) :
    E.symm.trans (H.equiv (productChart C c d) (product_chart_mem S T C P hP c d hc hd) p hp) =
      ((K.equiv c hc p.1 ((show p.1 ∈ c.source ∧ p.2 ∈ d.source from by simpa only [productChart_source, Set.mem_prod] using hp).1)).prodCongr
        (L.equiv d hd p.2 ((show p.1 ∈ c.source ∧ p.2 ∈ d.source from by simpa only [productChart_source, Set.mem_prod] using hp).2))).trans
          C.linearEquiv.toLinearEquiv := by
  have hpc : p.1 ∈ c.source := (show p.1 ∈ c.source ∧ p.2 ∈ d.source from by
    simpa only [productChart_source, Set.mem_prod] using hp).1
  have hpd : p.2 ∈ d.source := (show p.1 ∈ c.source ∧ p.2 ∈ d.source from by
    simpa only [productChart_source, Set.mem_prod] using hp).2
  let ES := K.equiv c hc p.1 hpc
  let ET := L.equiv d hd p.2 hpd
  let EP := H.equiv (productChart C c d) (product_chart_mem S T C P hP c d hc hd) p hp
  obtain ⟨hf, hg, _⟩ := differential_product S T C P hP
  let A : Euclidean (m+n) →L[ℝ] Euclidean m :=
    (ContinuousLinearMap.fst ℝ (Euclidean m) (Euclidean n)).comp C.linearEquiv.symm.toContinuousLinearMap
  let B : Euclidean (m+n) →L[ℝ] Euclidean n :=
    (ContinuousLinearMap.snd ℝ (Euclidean m) (Euclidean n)).comp C.linearEquiv.symm.toContinuousLinearMap
  have hA (v) : ES (E v).1 = A (EP v) := by
    have hx := differential_jacobian P S Prod.fst hf p _ hE.1
      (productChart C c d) c (product_chart_mem S T C P hP c d hc hd) hc hp hpc EP ES
      (H.isCoordinates _ _ p hp) (K.isCoordinates c hc p.1 hpc)
      univ A isOpen_univ (mem_univ _) A.contDiff.contDiffOn
      (Eventually.of_forall (fun q => by simp [A, productChart_val])) v
    rw [A.fderiv] at hx
    exact hx
  have hB (v) : ET (E v).2 = B (EP v) := by
    have hx := differential_jacobian P T Prod.snd hg p _ hE.2
      (productChart C c d) d (product_chart_mem S T C P hP c d hc hd) hd hp hpd EP ET
      (H.isCoordinates _ _ p hp) (L.isCoordinates d hd p.2 hpd)
      univ B isOpen_univ (mem_univ _) B.contDiff.contDiffOn
      (Eventually.of_forall (fun q => by simp [B, productChart_val])) v
    rw [B.fderiv] at hx
    exact hx
  apply LinearEquiv.ext
  intro z
  apply C.linearEquiv.symm.injective
  change C.linearEquiv.symm (EP (E.symm z)) = C.linearEquiv.symm (C.linearEquiv (ES z.1, ET z.2))
  rw [C.linearEquiv.symm_apply_apply]
  apply Prod.ext
  · exact (hA (E.symm z)).symm.trans (by rw [E.apply_symm_apply])
  · exact (hB (E.symm z)).symm.trans (by rw [E.apply_symm_apply])



lemma orderedProductRay_transport {V W X : Type u}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup X] [Module ℝ X]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    {m n : ℕ} (hm : finrank ℝ V = m) (hn : finrank ℝ W = n)
    (E : X ≃ₗ[ℝ] V × W) (H : X ≃ₗ[ℝ] Euclidean (m+n))
    (K : V ≃ₗ[ℝ] Euclidean m) (L : W ≃ₗ[ℝ] Euclidean n)
    (C : (Euclidean m × Euclidean n) ≃ₗ[ℝ] Euclidean (m+n))
    (hH : E.symm.trans H = (K.prodCongr L).trans C)
    (r : Module.Ray ℝ (⋀[ℝ]^m V)) (s : Module.Ray ℝ (⋀[ℝ]^n W)) :
    Module.Ray.map (determinantMap (m+n) H)
        (Module.Ray.map (determinantMap (m+n) E.symm) (orderedProductRay hm hn r s)) =
      Module.Ray.map (determinantMap (m+n) C)
        (orderedProductRay (by simp) (by simp)
          (Module.Ray.map (determinantMap m K) r)
          (Module.Ray.map (determinantMap n L) s)) := by
  rw [← rayMap_trans, ← determinantMap_trans, hH,
    determinantMap_trans, rayMap_trans]
  exact congrArg (Module.Ray.map (determinantMap (m+n) C))
    (orderedProductRay_natural (V := V) (W := W) (V' := Euclidean m) (W' := Euclidean n)
      hm hn (by simp) (by simp) K L r s)


lemma productRayField_coordinates {m n : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (C : ProductCoordinates m a n b k) (P : SmoothManifold (m+n) k (M × N))
    (hP : P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C S.smoothStructure.val T.smoothStructure.val))
    (K : FiberCoordinates S) (L : FiberCoordinates T) (H : FiberCoordinates P)
    (c : ModelChart m a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (E : ∀ p, TangentSpace P p ≃ₗ[ℝ] (TangentSpace S p.1 × TangentSpace T p.2))
    (hE : ∀ p, IsProductDifferential S T P p (E p))
    (o : Orientation S) (q : Orientation T) (p : (productChart C c d).source) :
    Module.Ray.map (determinantCoordinates H (productChart C c d)
        (product_chart_mem S T C P hP c d hc hd) p) (productRayField (S := S) (T := T) (P := P) E o q p.val) =
      Module.Ray.map (determinantMap (m+n) C.linearEquiv.toLinearEquiv)
        (orderedProductRay (by simp) (by simp)
          (Module.Ray.map (determinantCoordinates K c hc
            ⟨p.val.1, (show p.val.1 ∈ c.source ∧ p.val.2 ∈ d.source from by
              simpa only [productChart_source, Set.mem_prod] using p.property).1⟩) (o.val p.val.1))
          (Module.Ray.map (determinantCoordinates L d hd
            ⟨p.val.2, (show p.val.1 ∈ c.source ∧ p.val.2 ∈ d.source from by
              simpa only [productChart_source, Set.mem_prod] using p.property).2⟩) (q.val p.val.2))) := by
  letI := (tangent_dimension S p.val.1).1
  letI := (tangent_dimension T p.val.2).1
  simpa only [productRayField, determinantCoordinates, determinantMap] using
    (orderedProductRay_transport
      (V := TangentData.TangentSpace S p.val.1)
      (W := TangentData.TangentSpace T p.val.2)
      (X := TangentData.TangentSpace P p.val)
      (tangent_dimension S p.val.1).2 (tangent_dimension T p.val.2).2
      (E p.val)
      (H.equiv (productChart C c d) (product_chart_mem S T C P hP c d hc hd) p.val p.property)
      (K.equiv c hc p.val.1 (by
        have hp : p.val.1 ∈ c.source ∧ p.val.2 ∈ d.source := by
          simpa only [productChart_source, Set.mem_prod] using p.property
        exact hp.1))
      (L.equiv d hd p.val.2 (by
        have hp : p.val.1 ∈ c.source ∧ p.val.2 ∈ d.source := by
          simpa only [productChart_source, Set.mem_prod] using p.property
        exact hp.2))
      C.linearEquiv.toLinearEquiv
      (productDifferential_coordinates S T C P hP K L H c d hc hd p.val p.property (E p.val) (hE p.val))
      (o.val p.val.1) (q.val p.val.2))


lemma productRayField_continuous {m n : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (C : ProductCoordinates m a n b k) (P : SmoothManifold (m+n) k (M × N))
    (hP : P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C S.smoothStructure.val T.smoothStructure.val))
    (E : ∀ p, TangentSpace P p ≃ₗ[ℝ] (TangentSpace S p.1 × TangentSpace T p.2))
    (hE : ∀ p, IsProductDifferential S T P p (E p))
    (o : Orientation S) (q : Orientation T) :
    IsContinuousRayField (productRayField (S := S) (T := T) (P := P) E o q) := by
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  obtain ⟨L⟩ := TangentBundle.fiberCoordinates_exists T
  have hAS : productAtlas C S.smoothStructure.val T.smoothStructure.val ⊆ P.smoothStructure.val := by
    rintro e ⟨c, hc, d, hd, rfl⟩
    exact product_chart_mem S T C P hP c d hc hd
  apply isContinuousRayField_of_cover _ hAS
  · intro p
    obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p.1
    obtain ⟨d, hd, hpd⟩ := T.smoothStructure.property.1.1 p.2
    exact ⟨productChart C c d, ⟨c, hc, d, hd, rfl⟩, by
      simpa only [productChart_source, Set.mem_prod] using And.intro hpc hpd⟩
  intro H e he
  rcases he with ⟨c, hc, d, hd, rfl⟩
  let f (p : (productChart C c d).source) : c.source :=
    ⟨p.val.1, (show p.val.1 ∈ c.source ∧ p.val.2 ∈ d.source from by
      simpa only [productChart_source, Set.mem_prod] using p.property).1⟩
  let g (p : (productChart C c d).source) : d.source :=
    ⟨p.val.2, (show p.val.1 ∈ c.source ∧ p.val.2 ∈ d.source from by
      simpa only [productChart_source, Set.mem_prod] using p.property).2⟩
  have hfc : Continuous f := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hgc : Continuous g := (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have ho := (o.property K c hc).comp_continuous (f := f) hfc
  have hq := (q.property L d hd).comp_continuous (f := g) hgc
  have hl := ho.comp₂ hq (fun r s => Module.Ray.map
    (determinantMap (m+n) C.linearEquiv.toLinearEquiv)
    (orderedProductRay (by simp) (by simp) r s))
  have heq (p : (productChart C c d).source) :=
    productRayField_coordinates S T C P hP K L H c d hc hd E hE o q p
  simpa only [heq, f, g, Function.comp_apply] using hl

lemma productOrientation_of_continuous {m n : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold m a M} {T : SmoothManifold n b N}
    {P : SmoothManifold (m+n) k (M × N)}
    (hf : IsSmoothMap P S Prod.fst) (hg : IsSmoothMap P T Prod.snd)
    (E : ∀ p, TangentSpace P p ≃ₗ[ℝ] (TangentSpace S p.1 × TangentSpace T p.2))
    (hE : ∀ p, IsProductDifferential S T P p (E p))
    (o : Orientation S) (q : Orientation T)
    (hcont : IsContinuousRayField (productRayField (S := S) (T := T) (P := P) E o q)) :
    ∃! r : Orientation P, IsProductOrientation o q r := by
  refine ⟨⟨productRayField (S := S) (T := T) (P := P) E o q, hcont⟩, ?_, ?_⟩
  · intro p F hF v w hv hw
    have hFE := productDifferential_unique hf hg p F (E p) hF (hE p)
    subst F
    exact productRayField_positive (S := S) (T := T) (P := P) E o q p v w hv hw
  · intro r hr
    apply Subtype.ext
    exact productOrientation_unique E hE o q r hr

lemma product_orientation_exists :
    Specs.SmoothManifolds.Orientations.ProductsAndSigns.product_orientationType.{u} := by
  intro m n a b k M N _ _ S T C P hP o q
  obtain ⟨hf, hg, hsplit⟩ := differential_product S T C P hP
  choose E hE using hsplit
  exact productOrientation_of_continuous hf hg E hE o q
    (productRayField_continuous S T C P hP E hE o q)


/-- The intrinsic boundaryless product construction carries the original factor
orientations, independently of their chosen smooth model presentations. -/
theorem ordinaryProduct_orientation_of
    (h_product : Specs.SmoothManifolds.Orientations.ProductsAndSigns.product_orientationType.{u}) :
    Specs.SmoothManifolds.Orientations.ProductsAndSigns.ordinary_productType.{u} := by
  intro m n a b M N _ _ S T o q h
  obtain ⟨a', b', k, S', T', C, P, hSS', hS'S, hTT', hT'T, hP,
    hfst, hsnd, hpair, hsplit⟩ := ordinary_product_geometry S T h
  obtain ⟨A, hA, hAinv⟩ := identity_differential_equiv S S' hSS' hS'S
  obtain ⟨B, hB, hBinv⟩ := identity_differential_equiv T T' hTT' hT'T
  let o' : Orientation S' := ⟨fun p =>
    Module.Ray.map (determinantMap m (A p)) (o.val p), by
      simpa only [LinearEquiv.symm_symm, id_eq] using
        (pullbackRayField_continuous S' S id hS'S o (fun p => (A p).symm) hAinv)⟩
  let q' : Orientation T' := ⟨fun p =>
    Module.Ray.map (determinantMap n (B p)) (q.val p), by
      simpa only [LinearEquiv.symm_symm, id_eq] using
        (pullbackRayField_continuous T' T id hT'T q (fun p => (B p).symm) hBinv)⟩
  obtain ⟨r, hr, hrunique⟩ := h_product S' T' C P hP o' q'
  have hr0 := productOrientation_factorChange S S' T T' P hSS' hTT'
    A B hA hB o o' q q' r (fun _ => rfl) (fun _ => rfl) hr
  refine ⟨k, P, hfst, hsnd, hpair, hsplit, r, hr0, ?_⟩
  intro r' hr'
  apply hrunique r'
  apply productOrientation_factorChange S' S T' T P hS'S hT'T
    (fun p => (A p).symm) (fun p => (B p).symm) hAinv hBinv o' o q' q r' ?_ ?_ hr'
  · intro p
    simpa only [o', determinantMap] using
      (rayMap_determinant_symm_apply_apply (V := TangentSpace S p)
        (W := TangentSpace S' p) m (A p) (o.val p))
  · intro p
    simpa only [q', determinantMap] using
      (rayMap_determinant_symm_apply_apply (V := TangentSpace T p)
        (W := TangentSpace T' p) n (B p) (q.val p))

/-! Conditional draft entry points. All twelve frozen premises are explicit, in
the contract order, even when a particular algebraic proof does not need them.
The original closed target names are intentionally not defined here. -/

set_option linter.unusedVariables false in
theorem determinant_directSum_conditional
    (h_comparison : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h_connected_two : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h_empty : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h_generators_orientation : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h_positive_multiple : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h_positive_top_form : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h_signed_charts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h_signed_orientation : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h_smooth_generators : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h_top_form_quotient : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h_transition_jacobian : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h_zero_dimension : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u})
    : Specs.SmoothManifolds.Orientations.ProductsAndSigns.determinant_directSumType.{u} := by
  intro m n V W _ _ _ _ _ _ hm hn
  exact determinantSumMap_bijective m n V W hm hn

set_option linter.unusedVariables false in
theorem local_differential_conditional
    (h_comparison : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h_connected_two : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h_empty : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h_generators_orientation : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h_positive_multiple : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h_positive_top_form : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h_signed_charts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h_signed_orientation : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h_smooth_generators : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h_top_form_quotient : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h_transition_jacobian : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h_zero_dimension : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u})
    : Specs.SmoothManifolds.Orientations.ProductsAndSigns.local_differentialType.{u} := by
  exact local_differential_exists

set_option linter.unusedVariables false in
theorem sign_comp_conditional
    (h_comparison : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h_connected_two : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h_empty : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h_generators_orientation : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h_positive_multiple : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h_positive_top_form : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h_signed_charts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h_signed_orientation : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h_smooth_generators : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h_top_form_quotient : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h_transition_jacobian : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h_zero_dimension : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u})
    : Specs.SmoothManifolds.Orientations.ProductsAndSigns.sign_compType.{u} := by
  exact orientationSign_comp

set_option linter.unusedVariables false in
theorem product_orientation_conditional
    (h_comparison : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h_connected_two : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h_empty : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h_generators_orientation : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h_positive_multiple : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h_positive_top_form : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h_signed_charts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h_signed_orientation : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h_smooth_generators : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h_top_form_quotient : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h_transition_jacobian : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h_zero_dimension : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u})
    : Specs.SmoothManifolds.Orientations.ProductsAndSigns.product_orientationType.{u} := by
  exact product_orientation_exists

set_option linter.unusedVariables false in
theorem ordinary_product_conditional
    (h_comparison : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u})
    (h_connected_two : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u})
    (h_empty : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u})
    (h_generators_orientation : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u})
    (h_positive_multiple : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u})
    (h_positive_top_form : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u})
    (h_signed_charts : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u})
    (h_signed_orientation : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u})
    (h_smooth_generators : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u})
    (h_top_form_quotient : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u})
    (h_transition_jacobian : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u})
    (h_zero_dimension : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u})
    : Specs.SmoothManifolds.Orientations.ProductsAndSigns.ordinary_productType.{u} := by
  exact ordinaryProduct_orientation_of product_orientation_exists


end SmoothManifolds.OrientationProducts

universe v8_closure_97fa3db65f5bc694_u0
theorem _root_.«SmoothManifolds».«OrientationProducts».«determinant_directSum» : _root_.«Specs».«SmoothManifolds».«Orientations».«ProductsAndSigns».«determinant_directSumType».{v8_closure_97fa3db65f5bc694_u0} :=
  @_root_.«SmoothManifolds».«OrientationProducts».«determinant_directSum_conditional».{v8_closure_97fa3db65f5bc694_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_97fa3db65f5bc694_u0})
theorem _root_.«SmoothManifolds».«OrientationProducts».«local_differential» : _root_.«Specs».«SmoothManifolds».«Orientations».«ProductsAndSigns».«local_differentialType».{v8_closure_97fa3db65f5bc694_u0} :=
  @_root_.«SmoothManifolds».«OrientationProducts».«local_differential_conditional».{v8_closure_97fa3db65f5bc694_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_97fa3db65f5bc694_u0})
theorem _root_.«SmoothManifolds».«OrientationProducts».«local_sign» : _root_.«Specs».«SmoothManifolds».«Orientations».«ProductsAndSigns».«local_signType».{v8_closure_97fa3db65f5bc694_u0} :=
  @_root_.«SmoothManifolds».«OrientationProducts».«local_sign_conditional».{v8_closure_97fa3db65f5bc694_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_97fa3db65f5bc694_u0})
theorem _root_.«SmoothManifolds».«OrientationProducts».«ordinary_product» : _root_.«Specs».«SmoothManifolds».«Orientations».«ProductsAndSigns».«ordinary_productType».{v8_closure_97fa3db65f5bc694_u0} :=
  @_root_.«SmoothManifolds».«OrientationProducts».«ordinary_product_conditional».{v8_closure_97fa3db65f5bc694_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_97fa3db65f5bc694_u0})
theorem _root_.«SmoothManifolds».«OrientationProducts».«product_orientation» : _root_.«Specs».«SmoothManifolds».«Orientations».«ProductsAndSigns».«product_orientationType».{v8_closure_97fa3db65f5bc694_u0} :=
  @_root_.«SmoothManifolds».«OrientationProducts».«product_orientation_conditional».{v8_closure_97fa3db65f5bc694_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_97fa3db65f5bc694_u0})
theorem _root_.«SmoothManifolds».«OrientationProducts».«sign_comp» : _root_.«Specs».«SmoothManifolds».«Orientations».«ProductsAndSigns».«sign_compType».{v8_closure_97fa3db65f5bc694_u0} :=
  @_root_.«SmoothManifolds».«OrientationProducts».«sign_comp_conditional».{v8_closure_97fa3db65f5bc694_u0} (@_root_.«SmoothManifolds».«OrientationResults».«comparison».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«connected_two».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«empty».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«generators_orientation».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_multiple».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«positive_top_form».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_charts».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«signed_orientation».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«smooth_generators».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«top_form_quotient».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«transition_jacobian».{v8_closure_97fa3db65f5bc694_u0}) (@_root_.«SmoothManifolds».«OrientationResults».«zero_dimension».{v8_closure_97fa3db65f5bc694_u0})
