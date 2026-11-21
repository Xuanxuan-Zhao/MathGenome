import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.Spheres
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Algebra
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.SpheresAndTori
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.MayerVietoris
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.HomotopyInvariance
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SmoothManifolds.SphereCohomology
open ModelData AtlasData SphereTorusData BundleOperationsData CovectorData ExteriorData DeRhamData
open scoped BigOperators

/-- The shared sphere uses coordinate tuples with the sup norm. Passing to
EuclideanSpace changes the norm, and the square-sum equation becomes exactly
the metric unit sphere equation. -/
def metricSphereHomeomorph (n : ℕ) :
    Sphere n ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 where
  toFun x := ⟨WithLp.toLp 2 x.val, by
    rw [Metric.mem_sphere, dist_zero_right]
    have h : ‖WithLp.toLp 2 x.val‖ ^ 2 = (1 : ℝ) ^ 2 := by
      simpa [EuclideanSpace.real_norm_sq_eq, squareSum] using x.property
    exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp h⟩
  invFun x := ⟨WithLp.ofLp x.val, by
    have hx : ‖x.val‖ = 1 := by simpa using x.property
    simpa [squareSum, ← EuclideanSpace.real_norm_sq_eq, hx]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (PiLp.continuous_toLp 2 _).comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun := (PiLp.continuous_ofLp 2 _).comp continuous_subtype_val |>.subtype_mk _

/-- Positive dimensional spheres are connected in their actual subspace topology. -/
theorem sphere_connected (n : ℕ) (hn : 0 < n) : ConnectedSpace (Sphere n) := by
  have hd : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n+1))) := by
    rw [← Module.finrank_eq_rank]
    simp only [finrank_euclideanSpace_fin]
    exact_mod_cast (show 1 < n+1 by omega)
  have hc := isConnected_sphere hd (0 : EuclideanSpace ℝ (Fin (n+1)))
    (show (0 : ℝ) ≤ 1 by norm_num)
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :=
    Subtype.connectedSpace hc
  exact (metricSphereHomeomorph n).symm.surjective.connectedSpace
    (metricSphereHomeomorph n).symm.continuous

/-- The two points of S⁰, in the original sum-of-squares coordinates. -/
def zeroSphereEquiv : Sphere 0 ≃ Bool where
  toFun x := decide (0 < x.val 0)
  invFun b := ⟨fun _ => if b then 1 else -1, by cases b <;> norm_num [squareSum]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := by omega
    subst i
    have hx : x.val 0 ^ 2 = 1 := by simpa [squareSum] using x.property
    rcases (sq_eq_one_iff).mp hx with hp | hm
    · simp [hp]
    · simp [hm]
  right_inv b := by cases b <;> norm_num

/-- On the finite Hausdorff space S⁰ every function is locally constant. -/
def zeroLocallyConstantEquiv : LocallyConstant (Sphere 0) ℝ ≃ₗ[ℝ] (ℝ × ℝ) := by
  letI : Finite (Sphere 0) := Finite.of_equiv Bool zeroSphereEquiv.symm
  exact {
    toFun := fun f => (f (zeroSphereEquiv.symm false), f (zeroSphereEquiv.symm true))
    invFun := fun r => ⟨fun x => if zeroSphereEquiv x then r.2 else r.1,
      IsLocallyConstant.of_discrete _⟩
    left_inv := by
      intro f
      apply LocallyConstant.ext
      intro x
      change (if zeroSphereEquiv x then f (zeroSphereEquiv.symm true)
        else f (zeroSphereEquiv.symm false)) = f x
      have hx := zeroSphereEquiv.symm_apply_apply x
      cases h : zeroSphereEquiv x <;> simp only [h, Bool.false_eq_true, reduceIte] at hx ⊢
      · exact congrArg f hx
      · exact congrArg f hx
    right_inv := by intro r; simp
    map_add' := by intro f g; rfl
    map_smul' := by intro r f; rfl }

theorem zero_sphere : Specs.SmoothManifolds.DeRham.Spheres.zero_sphereType := by
  intro S C B K
  obtain ⟨e, _⟩ := DeRhamResults.h0_locally_constant K
  exact ⟨⟨e.trans zeroLocallyConstantEquiv⟩, fun k hk =>
    DeRhamResults.above_dimension K k hk⟩

theorem h0_positive : Specs.SmoothManifolds.DeRham.Spheres.h0_positiveType := by
  intro n hn S C B K
  letI := sphere_connected n hn
  exact DeRhamResults.h0_connected K

theorem above_dimension : Specs.SmoothManifolds.DeRham.Spheres.above_dimensionType := by
  intro n S C B K k hk
  exact DeRhamResults.above_dimension K k hk

theorem negative_degrees : Specs.SmoothManifolds.DeRham.Spheres.negative_degreesType := by
  intro n S C B K j
  exact (DeRhamResults.negative_degrees K j).2

universe u v w t
/-- An exact segment with vanishing neighboring groups identifies its two
central groups. This is the higher-degree Mayer–Vietoris step. -/
def linearEquivOfExactVanish
    {W : Type u} {X : Type v} {Y : Type w} {Z : Type t}
    [AddCommGroup W] [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module ℝ W] [Module ℝ X] [Module ℝ Y] [Module ℝ Z]
    (q : W →ₗ[ℝ] X) (d : X →ₗ[ℝ] Y) (r : Y →ₗ[ℝ] Z)
    (hd : ∀ x, d x = 0 ↔ ∃ w, q w = x)
    (hr : ∀ y, r y = 0 ↔ ∃ x, d x = y)
    (hW : Subsingleton W) (hZ : Subsingleton Z) : X ≃ₗ[ℝ] Y :=
  LinearEquiv.ofBijective d ⟨by
    intro x y hxy
    have hz : d (x-y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨w, hw⟩ := (hd (x-y)).mp hz
    have hw0 : w = 0 := hW.elim _ _
    rw [hw0, map_zero] at hw
    exact sub_eq_zero.mp hw.symm,
    fun y => (hr y).mp (hZ.elim _ _)⟩

/-- A surjection from ℝ² with exactly the diagonal as its kernel has
one-dimensional target. In the circle cover this is the connecting map. -/
def diagonalCokernelEquiv {X : Type u} [AddCommGroup X] [Module ℝ X]
    (d : (ℝ × ℝ) →ₗ[ℝ] X) (hsurj : Function.Surjective d)
    (hker : ∀ z, d z = 0 ↔ z.1 = z.2) : X ≃ₗ[ℝ] ℝ := by
  let f : ℝ →ₗ[ℝ] X := d.comp (LinearMap.inr ℝ ℝ ℝ)
  have hrel (z : ℝ × ℝ) : d z = d (0, z.2 - z.1) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (hker _).mpr
    change z.1 - 0 = z.2 - (z.2 - z.1)
    abel
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have hz : d ((0,a)-(0,b)) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.mpr hab
      have ha := (hker _).mp hz
      exact sub_eq_zero.mp (by simpa using ha.symm)
    · intro x
      obtain ⟨z, rfl⟩ := hsurj x
      exact ⟨z.2-z.1, (hrel z).symm⟩
  exact (LinearEquiv.ofBijective f hf).symm
/-- Exactness with a surjective preceding map kills the next group if the
following group vanishes. This treats H¹(Sⁿ) for n>1. -/
theorem subsingletonOfExactSurjective
    {W : Type u} {X : Type v} {Y : Type w} {Z : Type t}
    [AddCommGroup W] [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module ℝ W] [Module ℝ X] [Module ℝ Y] [Module ℝ Z]
    (q : W →ₗ[ℝ] X) (d : X →ₗ[ℝ] Y) (r : Y →ₗ[ℝ] Z)
    (hd : ∀ x, d x = 0 ↔ ∃ w, q w = x)
    (hr : ∀ y, r y = 0 ↔ ∃ x, d x = y)
    (hq : Function.Surjective q) (hZ : Subsingleton Z) : Subsingleton Y := by
  have hy (y : Y) : y = 0 := by
    obtain ⟨x, rfl⟩ := (hr y).mp (hZ.elim _ _)
    obtain ⟨w, rfl⟩ := hq x
    exact (hd (q w)).mpr ⟨w, rfl⟩
  exact ⟨fun x y => (hy x).trans (hy y).symm⟩

/-- The final dimension induction is independent of choices of complexes and
connecting maps. Its hypotheses are supplied by the actual two-pole cover. -/
theorem classifyBySuspension
    (H : ℕ → ℕ → Type u) [∀ n k, AddCommGroup (H n k)] [∀ n k, Module ℝ (H n k)]
    (h0 : ∀ n, 0 < n → Nonempty (H n 0 ≃ₗ[ℝ] ℝ))
    (hcircle : Nonempty (H 1 1 ≃ₗ[ℝ] ℝ))
    (habove : ∀ n k, n < k → Subsingleton (H n k))
    (hfirst : ∀ n, 0 < n → Subsingleton (H (n+1) 1))
    (hsusp : ∀ n, 0 < n → ∀ k, Nonempty (H (n+1) (k+2) ≃ₗ[ℝ] H n (k+1))) :
    ∀ n, 0 < n → Nonempty (H n 0 ≃ₗ[ℝ] ℝ) ∧ Nonempty (H n n ≃ₗ[ℝ] ℝ) ∧
      ∀ k, k ≠ 0 → k ≠ n → Subsingleton (H n k) := by
  suffices h : ∀ n, Nonempty (H (n+1) 0 ≃ₗ[ℝ] ℝ) ∧
      Nonempty (H (n+1) (n+1) ≃ₗ[ℝ] ℝ) ∧
      ∀ k, k ≠ 0 → k ≠ n+1 → Subsingleton (H (n+1) k) by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact h m
  intro n
  induction n with
  | zero =>
    exact ⟨h0 1 (by omega), hcircle, fun k hk0 hk1 => habove 1 k (by omega)⟩
  | succ n ih =>
    refine ⟨h0 (n+2) (by omega), ?_, ?_⟩
    · obtain ⟨e⟩ := hsusp (n+1) (by omega) n
      obtain ⟨f⟩ := ih.2.1
      exact ⟨e.trans f⟩
    · intro k hk0 hkn
      cases k with
      | zero => exact (hk0 rfl).elim
      | succ k =>
        cases k with
        | zero => exact hfirst (n+1) (by omega)
        | succ k =>
          obtain ⟨e⟩ := hsusp (n+1) (by omega) k
          have hv := ih.2.2 (k+1) (by omega) (by omega)
          exact ⟨fun x y => e.injective (hv.elim _ _)⟩


/-- Evaluation identifies locally constant functions on a nonempty connected
space with their single constant value. -/
def locallyConstantConnectedEquiv (X : Type*) [TopologicalSpace X]
    [PreconnectedSpace X] (p : X) : LocallyConstant X ℝ ≃ₗ[ℝ] ℝ where
  toFun f := f p
  invFun r := LocallyConstant.const X r
  left_inv f := (f.eq_const p).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A connected real factor does not change locally constant functions. -/
def locallyConstantRealProdEquiv (X : Type*) [TopologicalSpace X] :
    LocallyConstant (X × ℝ) ℝ ≃ₗ[ℝ] LocallyConstant X ℝ where
  toFun f := f.comap ⟨fun x => (x, 0), continuous_id.prodMk continuous_const⟩
  invFun f := f.comap ⟨Prod.fst, continuous_fst⟩
  left_inv f := by
    apply LocallyConstant.ext
    rintro ⟨x,t⟩
    let g : LocallyConstant ℝ ℝ :=
      f.comap ⟨fun t => (x,t), continuous_const.prodMk continuous_id⟩
    exact g.isLocallyConstant.apply_eq_of_preconnectedSpace 0 t
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


namespace CoverAlgebra
open MayerVietorisData

/-- A vanishing pair of open-set cohomology groups kills the product group. -/
theorem product_cohomology_subsingleton (U V : Cochain.{u}) (k : ℕ)
    (hU : Subsingleton (U.H k)) (hV : Subsingleton (V.H k)) :
    Subsingleton ((U.prod V).H k) := by
  let e := U.productHEquiv V k
  exact ⟨fun x y => e.injective (Prod.ext (hU.elim _ _) (hV.elim _ _))⟩

/-- The higher-degree suspension step of the actual cover sequence. -/
def higherCoverEquiv (A U V W : Cochain.{u})
    (E : ShortExact A (U.prod V) W)
    (hU : ∀ k, 0 < k → Subsingleton (U.H k))
    (hV : ∀ k, 0 < k → Subsingleton (V.H k)) (k : ℕ) :
    A.H (k+2) ≃ₗ[ℝ] W.H (k+1) :=
  (linearEquivOfExactVanish (E.q.onH (k+1)) (E.delta (k+1)) (E.r.onH (k+2))
    (E.exact_at_right (k+1)) (E.exact_at_left (k+1))
    (product_cohomology_subsingleton U V (k+1) (hU _ (by omega)) (hV _ (by omega)))
    (product_cohomology_subsingleton U V (k+2) (hU _ (by omega)) (hV _ (by omega)))).symm

/-- A surjective degree-zero difference kills H¹ in dimensions above one. -/
theorem firstCoverVanishes (A U V W : Cochain.{u})
    (E : ShortExact A (U.prod V) W)
    (hU : Subsingleton (U.H 1)) (hV : Subsingleton (V.H 1))
    (hq : Function.Surjective (E.q.onH 0)) : Subsingleton (A.H 1) :=
  subsingletonOfExactSurjective (E.q.onH 0) (E.delta 0) (E.r.onH 1)
    (E.exact_at_right 0) (E.exact_at_left 0) hq
    (product_cohomology_subsingleton U V 1 hU hV)

/-- A two-component overlap with diagonal difference image gives H¹=ℝ.
The diagonal hypothesis concerns the actual induced q in the given sequence. -/
def circleCoverEquiv (A U V W : Cochain.{u})
    (E : ShortExact A (U.prod V) W)
    (hU : Subsingleton (U.H 1)) (hV : Subsingleton (V.H 1))
    (e : W.H 0 ≃ₗ[ℝ] (ℝ × ℝ))
    (hq : ∀ z : ℝ × ℝ,
      (∃ x, e (E.q.onH 0 x) = z) ↔ z.1 = z.2) : A.H 1 ≃ₗ[ℝ] ℝ := by
  let d : (ℝ × ℝ) →ₗ[ℝ] A.H 1 := (E.delta 0).comp e.symm.toLinearMap
  have hsurj : Function.Surjective d := by
    intro x
    have hz := product_cohomology_subsingleton U V 1 hU hV
    obtain ⟨z, he⟩ := (E.exact_at_left 0 x).mp (hz.elim _ _)
    exact ⟨e z, by simpa [d] using he⟩
  have hker (z : ℝ × ℝ) : d z = 0 ↔ z.1 = z.2 := by
    change E.delta 0 (e.symm z) = 0 ↔ _
    rw [E.exact_at_right 0]
    constructor
    · rintro ⟨x, hx⟩
      apply (hq z).mp
      exact ⟨x, by rw [hx, e.apply_symm_apply]⟩
    · intro hz
      obtain ⟨x, hx⟩ := (hq z).mpr hz
      exact ⟨x, e.injective (by simpa using hx)⟩
  exact diagonalCokernelEquiv d hsurj hker

end CoverAlgebra

section HomotopyEquivalences
open ModelData AtlasData MapData InteriorHomotopyData
open scoped ContinuousMap

/-- Smooth representatives of any topological homotopy equivalence, with
continuous homotopies from the two composites to the corresponding identities. -/
theorem smoothMapsOfHomotopyEquiv
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N) (e : M ≃ₕ N) :
    ∃ (f : M → N) (g : N → M), IsSmoothMap S T f ∧ IsSmoothMap T S g ∧
      (∃ H : HomotopyTime × M → M, Continuous H ∧
        (∀ p, H (timeZero, p) = g (f p)) ∧ (∀ p, H (timeOne, p) = p)) ∧
      (∃ H : HomotopyTime × N → N, Continuous H ∧
        (∀ p, H (timeZero, p) = f (g p)) ∧ (∀ p, H (timeOne, p) = p)) := by
  obtain ⟨f, hf, Hf, hHf, hHf0, hHf1⟩ := SmoothingHomotopies.continuous_map_homotopic_smooth S T e e.continuous
  obtain ⟨g, hg, Hg, hHg, hHg0, hHg1⟩ := SmoothingHomotopies.continuous_map_homotopic_smooth T S e.symm e.symm.continuous
  let fC : C(M, N) := ⟨f, continuous_iff_continuousAt.mpr (fun x => (hf x).1)⟩
  let gC : C(N, M) := ⟨g, continuous_iff_continuousAt.mpr (fun x => (hg x).1)⟩
  let F : ContinuousMap.Homotopy e.toFun fC := {
    toFun := Hf
    continuous_toFun := hHf
    map_zero_left := hHf0
    map_one_left := hHf1 }
  let G : ContinuousMap.Homotopy e.invFun gC := {
    toFun := Hg
    continuous_toFun := hHg
    map_zero_left := hHg0
    map_one_left := hHg1 }
  obtain ⟨L⟩ := e.left_inv
  obtain ⟨R⟩ := e.right_inv
  let HL := (G.symm.comp F.symm).trans L
  let HR := (F.symm.comp G.symm).trans R
  exact ⟨f, g, hf, hg,
    ⟨HL, HL.continuous_toFun, HL.map_zero_left, HL.map_one_left⟩,
    ⟨HR, HR.continuous_toFun, HR.map_zero_left, HR.map_one_left⟩⟩

/-- Projection across a real factor is a homotopy equivalence. -/
def prodRealHomotopyEquiv (X : Type u) [TopologicalSpace X] : (X × ℝ) ≃ₕ X :=
  ((ContinuousMap.HomotopyEquiv.refl X).prodCongr
    (Classical.choice (ContractibleSpace.hequiv_unit ℝ))).trans
      (Homeomorph.prodUnique X Unit).toHomotopyEquiv


open ModelData AtlasData MapData TangentData DifferentialData BundleOperationsData
  CovectorData ExteriorData DeRhamData InteriorHomotopyData

/-- Smooth homotopy inverse maps induce inverse real linear maps on ordinary
intrinsic de Rham cohomology. The homotopies need only be continuous. -/
theorem cohomologyEquivOfSmoothHomotopyInverse
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (A : CotangentBundle T) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (f : M → N) (g : N → M)
    (hf : IsSmoothMap S T f) (hg : IsSmoothMap T S g)
    (hgf : ∃ H : HomotopyTime × M → M, Continuous H ∧
      (∀ p, H (timeZero, p) = g (f p)) ∧ (∀ p, H (timeOne, p) = p))
    (hfg : ∃ H : HomotopyTime × N → N, Continuous H ∧
      (∀ p, H (timeZero, p) = f (g p)) ∧ (∀ p, H (timeOne, p) = p))
    (k : ℕ) : Nonempty (K.Cohomology k ≃ₗ[ℝ] J.Cohomology k) := by
  let L := differential S T f hf
  let R := differential T S g hg
  have hL : ∀ p, IsDifferential S T f p (L p) := differential_spec S T f hf
  have hR : ∀ p, IsDifferential T S g p (R p) := differential_spec T S g hg
  have hcompM : IsSmoothMap S S (g ∘ f) :=
    manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ T.smoothStructure.property.1.1 f g hf hg
  have hcompN : IsSmoothMap T T (f ∘ g) :=
    manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ S.smoothStructure.property.1.1 g f hg hf
  let LM := differential S S (g ∘ f) hcompM
  let LN := differential T T (f ∘ g) hcompN
  have hLM : ∀ p, IsDifferential S S (g ∘ f) p (LM p) :=
    differential_spec S S (g ∘ f) hcompM
  have hLN : ∀ p, IsDifferential T T (f ∘ g) p (LN p) :=
    differential_spec T T (f ∘ g) hcompN
  obtain ⟨F,hF⟩ := DeRhamResults.pullback_exists S T C A B E K J f hf L hL
  obtain ⟨G,hG⟩ := DeRhamResults.pullback_exists T S A C E B J K g hg R hR
  obtain ⟨QM,hQM⟩ := DeRhamResults.pullback_exists S S C C B B K K (g ∘ f) hcompM LM hLM
  obtain ⟨QN,hQN⟩ := DeRhamResults.pullback_exists T T A A E E J J (f ∘ g) hcompN LN hLN
  have hIdK : IsCohomologyPullback C B K K id (fun p => LinearMap.id)
      (fun _ => LinearMap.id) := by
    intro j ω
    exact ⟨ω, (FormPullbackResults.pullback_id S _ (differential_id S) j ω.val.val).symm, rfl⟩
  have hIdJ : IsCohomologyPullback A E J J id (fun p => LinearMap.id)
      (fun _ => LinearMap.id) := by
    intro j ω
    exact ⟨ω, (FormPullbackResults.pullback_id T _ (differential_id T) j ω.val.val).symm, rfl⟩
  have hQMId := HomotopyResults.homotopy_invariance S S C B C B K K
    (g ∘ f) id hcompM (manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1)
    hgf LM (fun p => LinearMap.id) hLM (differential_id S) QM
    (fun _ => LinearMap.id) hQM hIdK
  have hQNId := HomotopyResults.homotopy_invariance T T A E A E J J
    (f ∘ g) id hcompN (manifoldContDiff_id (⊤ : ℕ∞) _ T.smoothStructure.property.1)
    hfg LN (fun p => LinearMap.id) hLN (differential_id T) QN
    (fun _ => LinearMap.id) hQN hIdJ
  have hFG := DeRhamResults.pullback_comp S T S C A C B E B K J K f g hf hg
    L R LM hL hR hLM F G QM hF hG hQM
  have hGF := DeRhamResults.pullback_comp T S T A C A E B E J K J g f hg hf
    R L LN hR hL hLN G F QN hG hF hQN
  exact ⟨{
    toLinearMap := G k
    invFun := F k
    left_inv := fun x => (hFG k x).symm.trans (congrArg (fun q => q x) (hQMId k))
    right_inv := fun x => (hGF k x).symm.trans (congrArg (fun q => q x) (hQNId k)) }⟩



/-- Ordinary real de Rham cohomology is invariant under a topological homotopy
 equivalence between the underlying smooth manifolds. -/
theorem cohomologyEquivOfHomotopyEquiv
    {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (A : CotangentBundle T) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (e : ContinuousMap.HomotopyEquiv M N) (k : ℕ) :
    Nonempty (K.Cohomology k ≃ₗ[ℝ] J.Cohomology k) := by
  obtain ⟨f, g, hf, hg, hgf, hfg⟩ := smoothMapsOfHomotopyEquiv S T e
  exact cohomologyEquivOfSmoothHomotopyInverse S T C B A E K J f g hf hg hgf hfg k

end HomotopyEquivalences

namespace PoleTopology

/-- The north pole in the manuscript's original coordinates. -/
def north (n : ℕ) : Sphere n :=
  ⟨fun i => if i = 0 then 1 else 0, by simp [squareSum, ite_pow]⟩

/-- Antipodal reflection, preserving the sum-of-squares sphere. -/
def antipodal (n : ℕ) : Sphere n ≃ₜ Sphere n where
  toFun x := ⟨-x.val, by simpa [squareSum] using x.property⟩
  invFun x := ⟨-x.val, by simpa [squareSum] using x.property⟩
  left_inv x := Subtype.ext (neg_neg x.val)
  right_inv x := Subtype.ext (neg_neg x.val)
  continuous_toFun := continuous_subtype_val.neg.subtype_mk _
  continuous_invFun := continuous_subtype_val.neg.subtype_mk _

/-- The other pole is the antipode of the first. -/
def south (n : ℕ) : Sphere n := antipodal n (north n)

theorem north_ne_south (n : ℕ) : north n ≠ south n := by
  intro h
  have := congrArg (fun x : Sphere n => x.val 0) h
  norm_num [north, south, antipodal] at this

/-- The literal two-pole cover, including dimension zero. -/
def cover (n : ℕ) : MayerVietorisData.OpenCover (Sphere n) where
  U := ⟨{north n}ᶜ, isOpen_compl_singleton⟩
  V := ⟨{south n}ᶜ, isOpen_compl_singleton⟩
  cover x := by
    by_cases h : x = north n
    · exact Or.inr (by simpa [h] using north_ne_south n)
    · exact Or.inl h

/-- Removing any one point gives Euclidean n-space. This is a topological
statement; smooth compatibility with the shared hemisphere atlas is separate. -/
def puncturedHomeomorph (n : ℕ) (p : Sphere n) :
    {x : Sphere n // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin n) := by
  let h := metricSphereHomeomorph n
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let e := stereographic' n (h p)
  let f : {x : Sphere n // x ≠ p} ≃ₜ e.source :=
    h.subtype (fun x => by simp [e, h.injective.eq_iff])
  exact f.trans (e.toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr (stereographic'_target (h p))).trans
      (Homeomorph.Set.univ _)))

/-- Both members of the actual pole cover are contractible. -/
theorem complements_contractible (n : ℕ) :
    ContractibleSpace (cover n).U ∧ ContractibleSpace (cover n).V :=
  ⟨(puncturedHomeomorph n (north n)).contractibleSpace,
   (puncturedHomeomorph n (south n)).contractibleSpace⟩

/-- Stereographic projection sends the antipodal pole to zero. -/
theorem punctured_south (n : ℕ) :
    puncturedHomeomorph n (north n) ⟨south n, (north_ne_south n).symm⟩ = 0 := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) :=
    ⟨finrank_euclideanSpace_fin⟩
  change stereographic' n (metricSphereHomeomorph n (north n))
    (metricSphereHomeomorph n (south n)) = 0
  have hn : metricSphereHomeomorph n (south n) =
      -(metricSphereHomeomorph n (north n)) := rfl
  rw [hn]
  simp [stereographic', stereographic_apply_neg]

/-- The overlap is punctured Euclidean space under stereographic projection. -/
def overlapPuncturedHomeomorph (n : ℕ) :
    ↥((cover n).U ⊓ (cover n).V) ≃ₜ
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
  let e := puncturedHomeomorph n (north n)
  let f : ↥((cover n).U ⊓ (cover n).V) ≃ₜ
      {x : {x : Sphere n // x ≠ north n} // x.val ≠ south n} := {
    toFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
    invFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun :=
      (continuous_subtype_val.subtype_mk _).subtype_mk _
    continuous_invFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  refine f.trans (e.subtype (fun x => ?_))
  change x.val ≠ south n ↔ e x ≠ 0
  rw [← punctured_south n, e.injective.ne_iff]
  exact not_congr ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- The logarithm identifies the positive radial coordinate with the real line. -/
def positiveRadialHomeomorph : Set.Ioi (0 : ℝ) ≃ₜ ℝ :=
  Real.expOrderIso.symm.toHomeomorph

/-- The actual intersection of the pole complements is S^r × ℝ, also for r=0.
This uses stereographic coordinates followed by polar coordinates and log radius. -/
def overlapHomeomorph (r : ℕ) :
    ↥((cover (r+1)).U ⊓ (cover (r+1)).V) ≃ₜ (Sphere r × ℝ) :=
  (overlapPuncturedHomeomorph (r+1)).trans
    ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin (r+1)))).trans
      ((metricSphereHomeomorph r).symm.prodCongr positiveRadialHomeomorph))

/-- The overlap has the homotopy type of the preceding sphere, including S⁰. -/
def overlapHomotopyEquiv (r : ℕ) :
    ContinuousMap.HomotopyEquiv ↥((cover (r+1)).U ⊓ (cover (r+1)).V) (Sphere r) :=
  (overlapHomeomorph r).toHomotopyEquiv.trans (prodRealHomotopyEquiv (Sphere r))

/-- The overlap is connected precisely in the higher-dimensional induction step. -/
theorem overlap_connected (r : ℕ) (hr : 0 < r) :
    ConnectedSpace ↥((cover (r+1)).U ⊓ (cover (r+1)).V) := by
  letI := sphere_connected r hr
  exact (overlapHomeomorph r).symm.surjective.connectedSpace
    (overlapHomeomorph r).symm.continuous

/-- Locally constant functions on the overlap are those on the preceding sphere. -/
def overlapLocallyConstantEquiv (r : ℕ) :
    LocallyConstant ↥((cover (r+1)).U ⊓ (cover (r+1)).V) ℝ ≃ₗ[ℝ]
      LocallyConstant (Sphere r) ℝ :=
  (LocallyConstant.congrLeftₗ ℝ (overlapHomeomorph r)).trans
    (locallyConstantRealProdEquiv (Sphere r))

/-- The circle overlap retains its two independently chosen constants. -/
def circleOverlapLocallyConstantEquiv :
    LocallyConstant ↥((cover 1).U ⊓ (cover 1).V) ℝ ≃ₗ[ℝ] (ℝ × ℝ) :=
  (overlapLocallyConstantEquiv 0).trans zeroLocallyConstantEquiv

/-- The actual difference of restrictions in degree zero, with the source sign b-a. -/
def locallyConstantDifference (n : ℕ) :
    (LocallyConstant (cover n).U ℝ × LocallyConstant (cover n).V ℝ) →ₗ[ℝ]
      LocallyConstant ↥((cover n).U ⊓ (cover n).V) ℝ where
  toFun f :=
    f.2.comap ⟨fun p => ⟨p.val, p.property.2⟩, continuous_subtype_val.subtype_mk _⟩ -
    f.1.comap ⟨fun p => ⟨p.val, p.property.1⟩, continuous_subtype_val.subtype_mk _⟩
  map_add' f g := by
    apply LocallyConstant.ext
    intro p
    change (f.2 _ + g.2 _) - (f.1 _ + g.1 _) =
      (f.2 _ - f.1 _) + (g.2 _ - g.1 _)
    abel
  map_smul' r f := by
    apply LocallyConstant.ext
    intro p
    change r • (f.2 _) - r • (f.1 _) = r • (f.2 _ - f.1 _)
    exact (smul_sub r _ _).symm

/-- Both cover members are connected; their restrictions differ by a constant. -/
theorem difference_is_constant (n : ℕ)
    (f : LocallyConstant (cover n).U ℝ × LocallyConstant (cover n).V ℝ) :
    ∃ r : ℝ, locallyConstantDifference n f =
      LocallyConstant.const ↥((cover n).U ⊓ (cover n).V) r := by
  letI := (complements_contractible n).1
  letI := (complements_contractible n).2
  let p : (cover n).U := ⟨south n, (north_ne_south n).symm⟩
  let q : (cover n).V := ⟨north n, north_ne_south n⟩
  refine ⟨f.2 q - f.1 p, ?_⟩
  apply LocallyConstant.ext
  intro x
  change f.2 ⟨x.val,x.property.2⟩ - f.1 ⟨x.val,x.property.1⟩ = f.2 q - f.1 p
  exact congrArg₂ (fun a b : ℝ => a-b)
    (f.2.isLocallyConstant.apply_eq_of_preconnectedSpace _ q)
    (f.1.isLocallyConstant.apply_eq_of_preconnectedSpace _ p)

/-- On the circle overlap the range of b-a is exactly the diagonal, not all ℝ². -/
theorem circle_difference_range (z : ℝ × ℝ) :
    (∃ f, circleOverlapLocallyConstantEquiv (locallyConstantDifference 1 f) = z) ↔
      z.1 = z.2 := by
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨r, hr⟩ := difference_is_constant 1 f
    rw [hr]
    rfl
  · intro hz
    refine ⟨(LocallyConstant.const _ 0, LocallyConstant.const _ z.1), ?_⟩
    have h : locallyConstantDifference 1
        (LocallyConstant.const _ 0, LocallyConstant.const _ z.1) =
        LocallyConstant.const _ z.1 := by
      apply LocallyConstant.ext
      intro p
      change z.1 - 0 = z.1
      exact sub_zero _
    rw [h]
    change (z.1, z.1) = z
    exact Prod.ext rfl hz

/-- In dimensions greater than one the overlap is connected and b-a is onto. -/
theorem difference_surjective (r : ℕ) (hr : 0 < r) :
    Function.Surjective (locallyConstantDifference (r+1)) := by
  letI := overlap_connected r hr
  intro f
  obtain ⟨c, hc⟩ := f.exists_eq_const
  refine ⟨(LocallyConstant.const _ 0, LocallyConstant.const _ c), ?_⟩
  rw [hc]
  apply LocallyConstant.ext
  intro p
  change c - 0 = c
  exact sub_zero _

/-- Any intrinsic calculus on either pole complement has no positive cohomology.
The identification with an OpenCalculus is a separate comparison. -/
theorem complements_positive_vanishing (n : ℕ) :
    (∀ (S : SmoothManifold n .euclidean (cover n).U)
      (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B) (k : ℕ),
        0 < k → Subsingleton (K.Cohomology k)) ∧
    (∀ (S : SmoothManifold n .euclidean (cover n).V)
      (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B) (k : ℕ),
        0 < k → Subsingleton (K.Cohomology k)) := by
  letI := (complements_contractible n).1
  letI := (complements_contractible n).2
  exact ⟨fun S C B K k hk => HomotopyResults.contractible_vanishing S C B K k hk,
    fun S C B K k hk => HomotopyResults.contractible_vanishing S C B K k hk⟩

/-- Intrinsic cohomology on the overlap agrees with that of the preceding sphere.
This statement is independent of the choices of smooth structures and calculus. -/
theorem overlap_cohomology (r : ℕ)
    (S : SmoothManifold (r+1) .euclidean ↥((cover (r+1)).U ⊓ (cover (r+1)).V))
    (T : SmoothManifold r .euclidean (Sphere r))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (A : CotangentBundle T) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E) (k : ℕ) :
    Nonempty (K.Cohomology k ≃ₗ[ℝ] J.Cohomology k) :=
  cohomologyEquivOfHomotopyEquiv S T C B A E K J (overlapHomotopyEquiv r) k

end PoleTopology


section OpenDegreeZero
set_option backward.isDefEq.respectTransparency.types false
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData MapData Set Filter
open scoped Topology
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
open private zeroCoefficient zeroCoefficient_smooth scalarField_const_smooth scalar_lc_smooth
  dFunction_lc_zero from MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Algebra
private theorem scalar_eventually_constant_of_dFunction_eventually_zero
    (C : CotangentBundle S) (f : M → ℝ)
    (hf : PartitionData.ScalarSmooth S.smoothStructure.val f)
    (p : M) (hdf : ∀ᶠ q in nhds p, dFunction S f hf q = 0) :
    ∀ᶠ q in nhds p, f q = f p := by
  classical
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨F, ⟨U, hU, hpU, hF⟩, hFf⟩ :=
    exists_germChartExtension S p c hc hp (functionGerm S f hf p)
  have heq : (fun y => F (c y).val) =ᶠ[𝓝 p] f := Filter.Germ.coe_eq.mp hFf
  obtain ⟨V, hVe, hV, hpV⟩ := mem_nhds_iff.mp (heq.and hdf)
  let W : Set (ModelSpace n a) := c.target ∩ c.symm ⁻¹' V
  have hW : IsOpen W := c.isOpen_inter_preimage_symm hV
  have hpW : c p ∈ W := ⟨c.map_source hp, by simpa only [mem_preimage, c.left_inv hp] using hpV⟩
  obtain ⟨W0, hW0, eW0⟩ := (isOpen_induced_iff (f := (Subtype.val : ModelSpace n a → Euclidean n))).mp hW
  have hpW0 : (c p).val ∈ W0 := by
    have : c p ∈ Subtype.val ⁻¹' W0 := by rw [eW0]; exact hpW
    exact this
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp (hU.inter hW0) (c p).val ⟨hpU, hpW0⟩
  let Q : Set (Euclidean n) := Metric.ball (c p).val r ∩ modelSet n a
  have hQ : Convex ℝ Q := (convex_ball _ _).inter (convex_modelSet n a)
  have hD (z : Euclidean n) (hz : z ∈ Q) : fderiv ℝ F z = 0 := by
    have hzU : z ∈ U := (hrsub hz.1).1
    let z' : ModelSpace n a := ⟨z, hz.2⟩
    have hzW : z' ∈ W := by
      rw [← eW0]
      exact (hrsub hz.1).2
    have hzT : z' ∈ c.target := hzW.1
    have hzV : c.symm z' ∈ V := hzW.2
    have hcp : c (c.symm z') = z' := c.right_inv hzT
    have hcg : TangentData.GermChartExtension S (c.symm z') c
        (functionGerm S f hf (c.symm z')) F := by
      refine ⟨⟨U, hU, ?_, hF⟩, Filter.Germ.coe_eq.mpr ?_⟩
      · simpa only [hcp] using hzU
      · filter_upwards [hV.mem_nhds hzV] with y hy
        exact (hVe hy).1
    have hcoord := (Covectors.differential_coordinates S C f hf c hc
      (c.symm z') (c.map_target hzT) F hcg).1
    apply ContinuousLinearMap.coe_injective
    have hhmap : (fderiv ℝ F z).toLinearMap = 0 := by
      apply (Pi.basisFun ℝ (Fin n)).ext
      intro j
      have hh := hcoord j
      rw [(hVe hzV).2] at hh
      simpa only [LinearMap.zero_apply, hcp, Pi.basisFun_apply,
        ContinuousLinearMap.coe_coe, ContinuousLinearMap.toLinearMap_zero, Pi.zero_apply] using hh.symm
    exact hhmap
  have hFD (z : Euclidean n) (hz : z ∈ Q) :
      HasFDerivWithinAt F (0 : Euclidean n →L[ℝ] ℝ) Q z := by
    have hzU := (hrsub hz.1).1
    have hdiff : DifferentiableAt ℝ F z :=
      (hF.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)
    simpa only [hD z hz] using hdiff.hasFDerivAt.hasFDerivWithinAt (s := Q)
  have hpQ : (c p).val ∈ Q := ⟨Metric.mem_ball_self hr, (c p).property⟩
  have hconst (z : Euclidean n) (hz : z ∈ Q) : F z = F (c p).val := by
    have hh := hQ.norm_image_sub_le_of_norm_hasFDerivWithin_le hFD
      (C := 0) (by intro z hz; simp) hpQ hz
    have hh' : ‖F z - F (c p).val‖ = 0 := le_antisymm (by simpa using hh) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hh')
  have hball : ∀ᶠ y in 𝓝 p, (c y).val ∈ Metric.ball (c p).val r :=
    ((continuous_subtype_val.continuousAt.comp (c.continuousAt hp)).preimage_mem_nhds
      (Metric.ball_mem_nhds _ hr))
  filter_upwards [heq, hball] with y hy hyball
  rw [← hy]
  rw [hconst (c y).val ⟨hyball, (c y).property⟩]
  exact heq.self_of_nhds


private def openZeroCoefficient (U : TopologicalSpace.Opens M)
    (ω : RestrictedField S U 0) (p : U) : ℝ :=
  exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p.val)) (ω p)

private theorem openClosed_zeroCoefficient_lc (K : Calculus C B)
    (U : TopologicalSpace.Opens M) (X : OpenCalculus C B U) (ω : X.complex.closed 0) :
    IsLocallyConstant (openZeroCoefficient U (X.field 0 ω.val)) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro p
  have hω : IsRestrictedForm (B 0) U (X.field 0 ω.val) :=
    (X.range_smooth 0 _).mpr ⟨ω.val, rfl⟩
  obtain ⟨α, hα, hgerm⟩ := OpenForms.exists_global_germ (B 0) U _ hω p
  have hKD : ∀ᶠ q in nhds p.val, K.D 0 α q = 0 := by
    filter_upwards [hgerm.eventually_nhds, U.isOpen.mem_nhds p.property] with q hq hqu
    rw [← OpenForms.restricted_derivative_eq_global K U _ _
      (X.coordinates 0 ω.val) α hα ⟨q,hqu⟩ hq]
    have hd : X.complex.d 0 ω.val = 0 := ω.property
    simp only [hd, map_zero, Pi.zero_apply]
  have hs : PartitionData.ScalarSmooth S.smoothStructure.val (zeroCoefficient α) :=
    zeroCoefficient_smooth α hα
  have hdf : ∀ᶠ q in nhds p.val, dFunction S (zeroCoefficient α) hs q = 0 := by
    filter_upwards [hKD] with q hq
    have heq : FormPullbackData.scalarField S (zeroCoefficient α) = α := by
      funext r
      exact (exteriorPower.zeroEquiv ℝ _).symm_apply_apply _
    have h := K.axioms.function_rule (zeroCoefficient α) hs q
    rw [heq, hq] at h
    have h' := congrArg (exteriorPower.oneEquiv ℝ
      (Module.Dual ℝ (TangentSpace S q))) h
    simpa only [map_zero, LinearEquiv.apply_symm_apply] using h'.symm
  have hfc := scalar_eventually_constant_of_dFunction_eventually_zero C
    (zeroCoefficient α) hs p.val hdf
  have hpα : zeroCoefficient α p.val = openZeroCoefficient U (X.field 0 ω.val) p := by
    have hh := hgerm.self_of_nhds
    simp only [zeroExtend, dite_eq_left p.property] at hh
    exact congrArg (exteriorPower.zeroEquiv ℝ _) hh
  filter_upwards [continuous_subtype_val.continuousAt.eventually hgerm,
    continuous_subtype_val.continuousAt.eventually hfc] with q hq hqc
  simp only [zeroExtend, dite_eq_left q.property] at hq
  have hqα : zeroCoefficient α q.val = openZeroCoefficient U (X.field 0 ω.val) q :=
    congrArg (exteriorPower.zeroEquiv ℝ _) hq
  exact hqα.symm.trans (hqc.trans hpα)

private def openScalarField (U : TopologicalSpace.Opens M) (f : U → ℝ) :
    RestrictedField S U 0 := fun p =>
  (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p.val))).symm (f p)

private theorem openScalarField_germ (U : TopologicalSpace.Opens M)
    (f : LocallyConstant U ℝ) (p : U) :
    ∀ᶠ q in nhds p.val, FormPullbackData.scalarField S (fun _ => f p) q =
      zeroExtend (openScalarField U f) q := by
  classical
  have he := f.isLocallyConstant.eventually_eq p
  obtain ⟨V,hV,hsub⟩ := (mem_nhds_subtype (U : Set M) p {q : U | f q = f p}).mp he
  filter_upwards [hV, U.isOpen.mem_nhds p.property] with q hq hqu
  have hqu' : q ∈ U := hqu
  have hfq : f ⟨q,hqu'⟩ = f p := hsub hq
  simp [zeroExtend, hqu', openScalarField, FormPullbackData.scalarField, hfq]

private theorem openScalarField_smooth (U : TopologicalSpace.Opens M)
    (f : LocallyConstant U ℝ) : IsRestrictedForm (B 0) U (openScalarField U f) := by
  apply OpenForms.restricted_smooth_of_global_germs
  intro p
  exact ⟨FormPullbackData.scalarField S (fun _ => f p),
    scalarField_const_smooth (f p), openScalarField_germ U f p⟩

private def openClosedOfLocallyConstant (K : Calculus C B)
    (U : TopologicalSpace.Opens M) (X : OpenCalculus C B U)
    (f : LocallyConstant U ℝ) : X.complex.closed 0 := by
  let x := ((X.range_smooth 0 _).mp (openScalarField_smooth U f)).choose
  have hx : X.field 0 x = openScalarField U f :=
    ((X.range_smooth 0 _).mp (openScalarField_smooth U f)).choose_spec
  refine ⟨x, ?_⟩
  apply X.injective 1
  rw [map_zero]
  funext p
  change X.field 1 (X.complex.d 0 x) p = 0
  have hder := X.coordinates 0 x
  rw [hx] at hder
  rw [OpenForms.restricted_derivative_eq_global K U _ _ hder
    (FormPullbackData.scalarField S (fun _ => f p))
    (scalarField_const_smooth (f p)) p (openScalarField_germ U f p)]
  let cf : M → ℝ := fun _ => f p
  have hcf : IsLocallyConstant cf := IsLocallyConstant.const _
  rw [K.axioms.function_rule cf (scalar_lc_smooth cf hcf),
    dFunction_lc_zero cf hcf]
  exact map_zero _

private def openClosedZeroCoefficients (K : Calculus C B)
    (U : TopologicalSpace.Opens M) (X : OpenCalculus C B U) :
    X.complex.closed 0 →ₗ[ℝ] LocallyConstant U ℝ where
  toFun ω := ⟨openZeroCoefficient U (X.field 0 ω.val), openClosed_zeroCoefficient_lc K U X ω⟩
  map_add' ω η := by
    apply LocallyConstant.ext
    intro p
    change exteriorPower.zeroEquiv ℝ _ (X.field 0 (ω.val+η.val) p) = _
    rw [map_add, Pi.add_apply, map_add]
    rfl
  map_smul' r ω := by
    apply LocallyConstant.ext
    intro p
    change exteriorPower.zeroEquiv ℝ _ (X.field 0 (r • ω.val) p) = _
    rw [map_smul, Pi.smul_apply, map_smul]
    rfl

private def openClosedZeroEquiv (K : Calculus C B)
    (U : TopologicalSpace.Opens M) (X : OpenCalculus C B U) :
    X.complex.closed 0 ≃ₗ[ℝ] LocallyConstant U ℝ :=
  LinearEquiv.ofBijective (openClosedZeroCoefficients K U X) ⟨by
    intro ω η h
    apply Subtype.ext
    apply X.injective 0
    funext p
    apply (exteriorPower.zeroEquiv ℝ _).injective
    exact congrArg (fun f : LocallyConstant U ℝ => f p) h,
    by
      intro f
      refine ⟨openClosedOfLocallyConstant K U X f, ?_⟩
      apply LocallyConstant.ext
      intro p
      change exteriorPower.zeroEquiv ℝ _ (X.field 0 _ p) = f p
      rw [show X.field 0 (openClosedOfLocallyConstant K U X f).val = openScalarField U f from
        ((X.range_smooth 0 _).mp (openScalarField_smooth U f)).choose_spec]
      exact (exteriorPower.zeroEquiv ℝ _).apply_symm_apply _⟩

private def openClassZeroEquiv (A : Cochain.{u}) : A.closed 0 ≃ₗ[ℝ] A.H 0 :=
  LinearEquiv.ofBijective (A.classOf 0) ⟨by
    intro ω η h
    have hz : (ω - η).val = 0 := (Submodule.Quotient.eq (A.boundaries 0)).mp h
    apply Subtype.ext
    exact sub_eq_zero.mp hz,
    (A.boundaries 0).mkQ_surjective⟩

private theorem open_h0_locally_constant (K : Calculus C B)
    (U : TopologicalSpace.Opens M) (X : OpenCalculus C B U) :
    ∃ e : X.complex.H 0 ≃ₗ[ℝ] LocallyConstant U ℝ,
      ∀ (ω : X.complex.closed 0) (p : U), e (X.complex.classOf 0 ω) p =
        exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p.val)) (X.field 0 ω.val p) := by
  let e := (openClassZeroEquiv X.complex).symm.trans (openClosedZeroEquiv K U X)
  refine ⟨e, ?_⟩
  intro ω p
  change openClosedZeroEquiv K U X ((openClassZeroEquiv X.complex).symm
    (openClassZeroEquiv X.complex ω)) p = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

private theorem open_h0_difference (K : Calculus C B) (O : OpenCover M)
    (D : CoverComplex K O)
    (eU : D.onU.complex.H 0 ≃ₗ[ℝ] LocallyConstant O.U ℝ)
    (eV : D.onV.complex.H 0 ≃ₗ[ℝ] LocallyConstant O.V ℝ)
    (eW : D.onOverlap.complex.H 0 ≃ₗ[ℝ] LocallyConstant ↥(O.U ⊓ O.V) ℝ)
    (hU : ∀ (ω : D.onU.complex.closed 0) (p : O.U),
      eU (D.onU.complex.classOf 0 ω) p = exteriorPower.zeroEquiv ℝ
        (Module.Dual ℝ (TangentSpace S p.val)) (D.onU.field 0 ω.val p))
    (hV : ∀ (ω : D.onV.complex.closed 0) (p : O.V),
      eV (D.onV.complex.classOf 0 ω) p = exteriorPower.zeroEquiv ℝ
        (Module.Dual ℝ (TangentSpace S p.val)) (D.onV.field 0 ω.val p))
    (hW : ∀ (ω : D.onOverlap.complex.closed 0) (p : ↥(O.U ⊓ O.V)),
      eW (D.onOverlap.complex.classOf 0 ω) p = exteriorPower.zeroEquiv ℝ
        (Module.Dual ℝ (TangentSpace S p.val)) (D.onOverlap.field 0 ω.val p))
    (z : (D.onU.complex.prod D.onV.complex).H 0) (p : ↥(O.U ⊓ O.V)) :
    eW (D.sequence.q.onH 0 z) p =
      eV ((D.onU.complex.productHEquiv D.onV.complex 0 z).2) ⟨p.val,p.property.2⟩ -
      eU ((D.onU.complex.productHEquiv D.onV.complex 0 z).1) ⟨p.val,p.property.1⟩ := by
  obtain ⟨ω,rfl⟩ := (D.onU.complex.prod D.onV.complex).class_surjective 0 z
  rw [ChainMap.onH_class, hW]
  change exteriorPower.zeroEquiv ℝ _ (D.onOverlap.field 0 (D.sequence.q.map 0 ω.val) p) =
    eV (D.onV.complex.classOf 0 ((ChainMap.snd D.onU.complex D.onV.complex).onClosed 0 ω))
      ⟨p.val,p.property.2⟩ -
    eU (D.onU.complex.classOf 0 ((ChainMap.fst D.onU.complex D.onV.complex).onClosed 0 ω))
      ⟨p.val,p.property.1⟩
  rw [hV, hU, D.difference, map_sub]
  rfl

private theorem open_h0_difference_equivs (K : Calculus C B) (O : OpenCover M)
    (D : CoverComplex K O)
    (d : (LocallyConstant O.U ℝ × LocallyConstant O.V ℝ) →ₗ[ℝ]
      LocallyConstant ↥(O.U ⊓ O.V) ℝ)
    (hd : ∀ f (p : ↥(O.U ⊓ O.V)), d f p =
      f.2 ⟨p.val,p.property.2⟩ - f.1 ⟨p.val,p.property.1⟩) :
    ∃ eP : (D.onU.complex.prod D.onV.complex).H 0 ≃ₗ[ℝ]
      (LocallyConstant O.U ℝ × LocallyConstant O.V ℝ),
    ∃ eW : D.onOverlap.complex.H 0 ≃ₗ[ℝ] LocallyConstant ↥(O.U ⊓ O.V) ℝ,
      ∀ z, eW (D.sequence.q.onH 0 z) = d (eP z) := by
  obtain ⟨eU,hU⟩ := open_h0_locally_constant K O.U D.onU
  obtain ⟨eV,hV⟩ := open_h0_locally_constant K O.V D.onV
  obtain ⟨eW,hW⟩ := open_h0_locally_constant K (O.U ⊓ O.V) D.onOverlap
  let eP := (D.onU.complex.productHEquiv D.onV.complex 0).trans (eU.prodCongr eV)
  refine ⟨eP,eW,?_⟩
  intro z
  apply LocallyConstant.ext
  intro p
  rw [open_h0_difference K O D eU eV eW hU hV hW, hd]
  rfl

private theorem range_iff_of_conjugate
    {A₀ B₀ C₀ D₀ E₀ : Type*}
    [AddCommGroup A₀] [AddCommGroup B₀] [AddCommGroup C₀] [AddCommGroup D₀]
    [Module ℝ A₀] [Module ℝ B₀] [Module ℝ C₀] [Module ℝ D₀]
    (q : A₀ →ₗ[ℝ] C₀) (d : B₀ →ₗ[ℝ] D₀)
    (eP : A₀ ≃ₗ[ℝ] B₀) (eW : C₀ ≃ₗ[ℝ] D₀)
    (h : ∀ x, eW (q x) = d (eP x)) (s : D₀ → E₀) (z : E₀) :
    (∃ x, s (eW (q x)) = z) ↔ ∃ f, s (d f) = z := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨eP x, by rw [← h x]; exact hx⟩
  · rintro ⟨f,hf⟩
    refine ⟨eP.symm f, ?_⟩
    rw [h, eP.apply_symm_apply]
    exact hf

private theorem surjective_of_conjugate
    {A₀ B₀ C₀ D₀ : Type*}
    [AddCommGroup A₀] [AddCommGroup B₀] [AddCommGroup C₀] [AddCommGroup D₀]
    [Module ℝ A₀] [Module ℝ B₀] [Module ℝ C₀] [Module ℝ D₀]
    (q : A₀ →ₗ[ℝ] C₀) (d : B₀ →ₗ[ℝ] D₀)
    (eP : A₀ ≃ₗ[ℝ] B₀) (eW : C₀ ≃ₗ[ℝ] D₀)
    (h : ∀ x, eW (q x) = d (eP x)) (hd : Function.Surjective d) :
    Function.Surjective q := by
  intro y
  obtain ⟨f,hf⟩ := hd (eW y)
  refine ⟨eP.symm f, eW.injective ?_⟩
  rw [h, eP.apply_symm_apply, hf]


end OpenDegreeZero

namespace PoleTopology
open MayerVietorisData

private theorem circle_open_difference_range
    (S : SmoothManifold 1 .euclidean (Sphere 1))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
    (D : CoverComplex K (cover 1)) :
    ∃ e : D.onOverlap.complex.H 0 ≃ₗ[ℝ] (ℝ × ℝ),
      ∀ z : ℝ × ℝ, (∃ x, e (D.sequence.q.onH 0 x) = z) ↔ z.1 = z.2 := by
  obtain ⟨eP,eW,hq⟩ := open_h0_difference_equivs K (cover 1) D
    (locallyConstantDifference 1) (by intro f p; rfl)
  refine ⟨eW.trans circleOverlapLocallyConstantEquiv, ?_⟩
  intro z
  exact (range_iff_of_conjugate (D.sequence.q.onH 0) (locallyConstantDifference 1)
    eP eW hq circleOverlapLocallyConstantEquiv z).trans (circle_difference_range z)

private theorem higher_open_difference_surjective
    (r : ℕ) (hr : 0 < r)
    (S : SmoothManifold (r+1) .euclidean (Sphere (r+1)))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
    (D : CoverComplex K (cover (r+1))) : Function.Surjective (D.sequence.q.onH 0) := by
  obtain ⟨eP,eW,hq⟩ := open_h0_difference_equivs K (cover (r+1)) D
    (locallyConstantDifference (r+1)) (by intro f p; rfl)
  exact surjective_of_conjugate (D.sequence.q.onH 0) (locallyConstantDifference (r+1))
    eP eW hq (difference_surjective r hr)

end PoleTopology

section OpenComparisonConstruction
attribute [local irreducible] TangentData.smoothGermAlgebra TangentData.pointDerivations
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
open Set Filter

/-- The differential of an open-submanifold inclusion identifies the genuine
intrinsic tangent space with its ambient tangent space. -/
theorem openInclusionDifferential_bijective
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M)
    (R : SmoothManifold n a U)
    (hRsub : openSubsetAtlas S.smoothStructure.val U U.isOpen ⊆ R.smoothStructure.val)
    (hinc : IsSmoothMap R S Subtype.val) (p : U)
    (L : TangentSpace R p →ₗ[ℝ] TangentSpace S p.val)
    (hL : IsDifferential R S Subtype.val p L) : Function.Bijective L := by
  obtain ⟨c,hc,hp⟩ := S.smoothStructure.property.1.1 p.val
  let e := c.subtypeRestr (s := U) ⟨p⟩
  have he : e ∈ R.smoothStructure.val := by
    exact hRsub ⟨⟨p⟩,c,hc,rfl⟩
  have hpe : p ∈ e.source := by simpa [e] using hp
  obtain ⟨ER⟩ := TangentBundle.fiberCoordinates_exists R
  obtain ⟨ES⟩ := TangentBundle.fiberCoordinates_exists S
  let E := ER.equiv e he p hpe
  let F := ES.equiv c hc p.val hp
  have hEF (v : TangentSpace R p) : F (L v) = E v := by
    have h := differential_jacobian R S Subtype.val hinc p L hL e c he hc hpe hp
      E F (ER.isCoordinates e he p hpe) (ES.isCoordinates c hc p.val hp)
      Set.univ id isOpen_univ (mem_univ _) contDiff_id.contDiffOn
      (Eventually.of_forall (fun _ => rfl)) v
    simpa only [fderiv_id, ContinuousLinearMap.id_apply] using h
  have hLE : L = (E.trans F.symm).toLinearMap := by
    apply LinearMap.ext
    intro v
    apply F.injective
    simpa only [LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply] using hEF v
  rw [hLE]
  exact (E.trans F.symm).bijective


open ModelData AtlasData MapData TangentData TangentBundleData DifferentialData
  BundleData BundleOperationsData FrameData CovectorData ExteriorData FormPullbackData
  MayerVietorisData Set Filter Module
open scoped Topology

/-- Intrinsic smooth forms on an open submanifold give smooth restricted forms
with the ambient tangent fibers, by the inverse inclusion differential. -/
theorem openInverseField_smooth
    {n k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M)
    (R : SmoothManifold n a U)
    (hRsub : openSubsetAtlas S.smoothStructure.val U U.isOpen ⊆ R.smoothStructure.val)
    (hinc : IsSmoothMap R S Subtype.val)
    (CS : CotangentBundle S) (CR : CotangentBundle R)
    (BS : FormBundle CS k) (BR : FormBundle CR k)
    (E : ∀ p : U, TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
    (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)
    (α : Field R k) (hα : IsForm BR α) :
    IsRestrictedForm BS U
      (fun p => fiberPullback (V := TangentSpace S p.val) (W := TangentSpace R p) k (E p).symm.toLinearMap (α p)) := by
  classical
  letI := (cotangentSpace CS).topology
  letI := (cotangentSpace CR).topology
  letI := BS.space.topology
  letI := BR.space.topology
  let A := openSubsetAtlas S.smoothStructure.val U U.isOpen
  have hA : IsContDiffAtlas (⊤ : ℕ∞) A :=
    openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _ S.smoothStructure.property.1 U U.isOpen
  have hincA : ManifoldSmooth A S.smoothStructure.val (Subtype.val : U → M) := by
    intro p
    exact ⟨(hinc p).1, fun c hc d hd hpc hpd =>
      (hinc p).2 c (hRsub hc) d hd hpc hpd⟩
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
  let d := c.subtypeRestr (s := U) ⟨p⟩
  have hd : d ∈ R.smoothStructure.val := hRsub ⟨⟨p⟩, c, hc, rfl⟩
  have hpd : p ∈ d.source := by
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hp
  let z : U → Euclidean (n.choose k) := fun q =>
    ((BR.space.bundle.trivialization ⟨d, hd⟩) ⟨q, α q⟩).2
  have hzR : VectorSmoothAt R.smoothStructure.val z p := by
    apply (Frames.trivializationCoordinates_smoothAt BR.space.bundle ⟨d, hd⟩
      ⟨p, α p⟩ (by rw [BR.baseSet, Covectors.cotangent_baseSet]; exact hpd)).comp
      (g := fun q => (⟨q, α q⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
        (fun q => Fiber (TangentSpace R q) k)))
      BR.space.bundle.totalManifold.smoothStructure.property.1.1 (hα p)
  have hz : VectorSmoothAt A z p :=
    ⟨hzR.1, fun e he hpe => hzR.2 e (hRsub he) hpe⟩
  let Q : Euclidean (n.choose k) →L[ℝ] Euclidean (n.choose k) :=
    (BS.modelEquiv.toLinearMap.comp BR.modelEquiv.symm.toLinearMap).toContinuousLinearMap
  apply Frames.smoothAt_from_trivialization BS.space.bundle hA ⟨c, hc⟩
    (by rw [BS.baseSet, Covectors.cotangent_baseSet]; exact hp)
    (hincA p) (hz.postcomp Q.contDiff) (fun _ => rfl)
  filter_upwards [(continuous_subtype_val.continuousAt.preimage_mem_nhds
    (c.open_source.mem_nhds hp))] with q hq
  change q.val ∈ c.source at hq
  have hqd : q ∈ d.source := by
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hq
  let F : TangentSpace S q.val ≃ₗ[ℝ] Euclidean n := CS.tangent.fiberCoordinates.equiv c hc q.val hq
  let G : TangentSpace R q ≃ₗ[ℝ] Euclidean n := CR.tangent.fiberCoordinates.equiv d hd q hqd
  have heq (v : TangentSpace R q) : F (E q v) = G v := by
    have hj := differential_jacobian R S Subtype.val hinc q (E q).toLinearMap (hE q)
      d c hd hc hqd hq G F
      (CR.tangent.fiberCoordinates.isCoordinates d hd q hqd)
      (CS.tangent.fiberCoordinates.isCoordinates c hc q.val hq)
      univ id isOpen_univ (mem_univ _) contDiff_id.contDiffOn
      (Filter.Eventually.of_forall (fun _ => rfl)) v
    simpa only [fderiv_id, ContinuousLinearMap.id_apply, LinearEquiv.coe_coe] using hj
  have hvector (j : Fin n) :
      (E q).symm (coordinateVector CS.tangent.fiberCoordinates c hc q.val hq j) =
      coordinateVector CR.tangent.fiberCoordinates d hd q hqd j := by
    apply (E q).injective
    apply F.injective
    rw [LinearEquiv.apply_symm_apply, heq]
    simp [coordinateVector, F, G]
  let eS := (cotangentSpace CS).bundle.fiberCoordinates ⟨c, hc⟩ q.val
    (by rw [Covectors.cotangent_baseSet]; exact hq)
  let eR := (cotangentSpace CR).bundle.fiberCoordinates ⟨d, hd⟩ q
    (by rw [Covectors.cotangent_baseSet]; exact hqd)
  have heLin : eS.toLinearMap.comp (E q).symm.toLinearMap.dualMap = eR.toLinearMap := by
    ext lam j
    change eS (lam.comp (E q).symm.toLinearMap) j = eR lam j
    rw [show eS (lam.comp (E q).symm.toLinearMap) j =
      (lam.comp (E q).symm.toLinearMap)
        (coordinateVector CS.tangent.fiberCoordinates c hc q.val hq j) from
      Covectors.cotangent_coordinates CS c hc q.val hq _ j]
    rw [show eR lam j = lam
      (coordinateVector CR.tangent.fiberCoordinates d hd q hqd j) from
      Covectors.cotangent_coordinates CR d hd q hqd _ j]
    exact congrArg lam (hvector j)
  change ((BS.space.bundle.trivialization ⟨c, hc⟩)
    ⟨q.val, fiberPullback (V := TangentSpace S q.val) (W := TangentSpace R q) k (E q).symm.toLinearMap (α q)⟩).2 = Q (z q)
  rw [FormPullbackResults.form_coordinates CS k BS c hc q.val hq]
  have hzq : z q = BR.modelEquiv (exteriorPower.map k eR.toLinearMap (α q)) :=
    FormPullbackResults.form_coordinates CR k BR d hd q hqd (α q)
  rw [hzq]
  change BS.modelEquiv
    (exteriorPower.map k eS.toLinearMap
      (exteriorPower.map k (E q).symm.toLinearMap.dualMap (α q))) =
    BS.modelEquiv (BR.modelEquiv.symm
      (BR.modelEquiv (exteriorPower.map k eR.toLinearMap (α q))))
  rw [LinearEquiv.symm_apply_apply]
  apply congrArg BS.modelEquiv
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, heLin]


open ModelData AtlasData MapData TangentData DifferentialData BundleOperationsData
  CovectorData ExteriorData ExteriorDerivativeData DeRhamData MayerVietorisData
open Set Filter
open scoped Topology
section OpenComparison
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M)
    (R : SmoothManifold n a U)
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {A : CotangentBundle R} {E : ∀ k, FormBundle A k}
    (hinc : IsSmoothMap R S Subtype.val)
    (L : (p : U) → TangentSpace R p →ₗ[ℝ] TangentSpace S p.val)
    (hL : ∀ p, IsDifferential R S Subtype.val p (L p))

/-- Pull a restricted ambient section back to the intrinsic open manifold. -/
def inclusionPullField (k : ℕ) : RestrictedField S U k →ₗ[ℝ] Field R k where
  toFun ω p := FormPullbackData.fiberPullback (V := TangentSpace R p) (W := TangentSpace S p.val) k (L p) (ω p)
  map_add' ω η := by
    funext p
    exact map_add (FormPullbackData.fiberPullback (V := TangentSpace R p) (W := TangentSpace S p.val) k (L p)) _ _
  map_smul' r ω := by
    funext p
    exact map_smul (FormPullbackData.fiberPullback (V := TangentSpace R p) (W := TangentSpace S p.val) k (L p)) r _

include hinc hL in
/-- The pullback on an open subset uses actual smooth germs of ambient sections. -/
theorem inclusionPullField_smooth (k : ℕ) (ω : RestrictedField S U k)
    (hω : IsRestrictedForm (B k) U ω) :
    IsForm (E k) (inclusionPullField S U R L k ω) := by
  letI := (cotangentSpace A).topology
  letI := (E k).space.topology
  intro p
  obtain ⟨α,hα,he⟩ := OpenForms.exists_global_germ (B k) U ω hω p
  have hpull := FormPullbackResults.pullback_smooth R S A C Subtype.val hinc L hL k
    (E k) (B k) α hα
  apply manifoldContDiffAt_congr (hpull p)
  filter_upwards [continuous_subtype_val.continuousAt.eventually he] with q hq
  apply congrArg (fun v => (⟨q,v⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
    (fun r => Fiber (TangentSpace R r) k)))
  change FormPullbackData.fiberPullback (V := TangentSpace R q) (W := TangentSpace S q.val) k (L q) (α q.val) =
    FormPullbackData.fiberPullback (V := TangentSpace R q) (W := TangentSpace S q.val) k (L q) (ω q)
  apply congrArg (FormPullbackData.fiberPullback (V := TangentSpace R q) (W := TangentSpace S q.val) k (L q))
  simpa only [zeroExtend, dif_pos q.property] using hq

def inclusionPullLinear (J : Calculus A E) (D : OpenCalculus C B U) (k : ℕ) :
    D.complex.Obj k →ₗ[ℝ] J.forms k :=
  LinearMap.codRestrict (J.forms k) ((inclusionPullField S U R L k).comp (D.field k))
    (fun ω => (J.mem_forms k _).mpr (inclusionPullField_smooth S U R hinc L hL k _
      ((D.range_smooth k _).mpr ⟨ω,rfl⟩)))

@[simp] theorem inclusionPullLinear_field (J : Calculus A E) (D : OpenCalculus C B U)
    (k : ℕ) (ω : D.complex.Obj k) :
    (inclusionPullLinear S U R hinc L hL J D k ω).val =
      inclusionPullField S U R L k (D.field k ω) := rfl

/-- Inclusion pullback commutes with the genuine local exterior derivative. -/
def inclusionPullChain (K : Calculus C B) (J : Calculus A E)
    (D : OpenCalculus C B U) : ChainMap D.complex (globalComplex J) where
  map := inclusionPullLinear S U R hinc L hL J D
  comm k ω := by
    apply Subtype.ext
    funext p
    obtain ⟨α,hα,he⟩ := OpenForms.exists_global_germ (B k) U (D.field k ω)
      ((D.range_smooth k _).mpr ⟨ω,rfl⟩) p
    have hpull := FormPullbackResults.pullback_smooth R S A C Subtype.val hinc L hL k
      (E k) (B k) α hα
    have hτ : IsForm (E k) (inclusionPullField S U R L k (D.field k ω)) :=
      inclusionPullField_smooth S U R hinc L hL k _
        ((D.range_smooth k _).mpr ⟨ω,rfl⟩)
    have he' : ∀ᶠ q in 𝓝 p, inclusionPullField S U R L k (D.field k ω) q =
        FormPullbackData.pullbackField R S Subtype.val L α q := by
      filter_upwards [continuous_subtype_val.continuousAt.eventually he] with q hq
      change FormPullbackData.fiberPullback (V := TangentSpace R q) (W := TangentSpace S q.val) k (L q) (D.field k ω q) =
        FormPullbackData.fiberPullback (V := TangentSpace R q) (W := TangentSpace S q.val) k (L q) (α q.val)
      apply congrArg (FormPullbackData.fiberPullback (V := TangentSpace R q) (W := TangentSpace S q.val) k (L q))
      have hq' : α q.val = D.field k ω q := by
        simpa only [zeroExtend, dif_pos q.property] using hq
      exact hq'.symm
    have hloc := ExteriorDerivativeResults.axioms_locality A E J.D J.axioms k
      (inclusionPullField S U R L k (D.field k ω))
      (FormPullbackData.pullbackField R S Subtype.val L α) hτ hpull p he'
    change J.D k (inclusionPullField S U R L k (D.field k ω)) p =
      FormPullbackData.fiberPullback (V := TangentSpace R p) (W := TangentSpace S p.val) (k+1) (L p) (D.field (k+1) (D.complex.d k ω) p)
    rw [hloc, OpenForms.restricted_derivative_eq_global K U (D.field k ω)
      (D.field (k+1) (D.complex.d k ω)) (D.coordinates k ω) α hα p he]
    exact congrFun (ExteriorDerivativeResults.smooth_naturality R S A C E B J.D K.D
      J.axioms K.axioms Subtype.val hinc L hL k α hα).symm p

end OpenComparison

open MayerVietorisData

/-- A degreewise bijective chain map induces an isomorphism on cohomology. -/
def cohomologyEquivOfDegreewiseBijective {A B : Cochain.{u}} (f : ChainMap A B)
    (h : ∀ k, Function.Bijective (f.map k)) (k : ℕ) : A.H k ≃ₗ[ℝ] B.H k := by
  let e (j : ℕ) : A.Obj j ≃ₗ[ℝ] B.Obj j := LinearEquiv.ofBijective (f.map j) (h j)
  let g : ChainMap B A := {
    map j := (e j).symm.toLinearMap
    comm j x := by
      apply (h (j+1)).1
      rw [← f.comm]
      change B.d j (e j ((e j).symm x)) = e (j+1) ((e (j+1)).symm (B.d j x))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] }
  exact {
    toLinearMap := f.onH k
    invFun := g.onH k
    left_inv := by
      intro x
      refine Submodule.Quotient.induction_on _ x ?_
      intro a
      change g.onH k (f.onH k (A.classOf k a)) = A.classOf k a
      rw [f.onH_induced k a, g.onH_induced k (f.onClosed k a)]
      apply congrArg (A.classOf k)
      apply Subtype.ext
      exact (e k).symm_apply_apply a.val
    right_inv := by
      intro x
      refine Submodule.Quotient.induction_on _ x ?_
      intro b
      change f.onH k (g.onH k (B.classOf k b)) = B.classOf k b
      rw [g.onH_induced k b, f.onH_induced k (g.onClosed k b)]
      apply congrArg (B.classOf k)
      apply Subtype.ext
      exact (e k).apply_symm_apply b.val }


open ExteriorData FormPullbackData
theorem fiberPullback_symm_right {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (k : ℕ) (E : V ≃ₗ[ℝ] W) (α : Fiber V k) :
    fiberPullback (V := V) (W := W) k E.toLinearMap
      (fiberPullback (V := W) (W := V) k E.symm.toLinearMap α) = α := by
  unfold fiberPullback
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp,
    LinearMap.dualMap_comp_dualMap, LinearEquiv.symm_comp,
    LinearMap.dualMap_id, exteriorPower.map_id, LinearMap.id_apply]

open ModelData AtlasData MapData TangentData DifferentialData BundleOperationsData
  CovectorData ExteriorData DeRhamData MayerVietorisData

/-- Restricted ambient forms and the intrinsic de Rham complex of the
canonical open submanifold have canonically isomorphic cohomology. -/
theorem openCohomologyEquiv
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M)
    (R : SmoothManifold n a U)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U U.isOpen))
    (hinc : IsSmoothMap R S Subtype.val)
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {A : CotangentBundle R} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E) (D : OpenCalculus C B U)
    (k : ℕ) : Nonempty (D.complex.H k ≃ₗ[ℝ] J.Cohomology k) := by
  have hRsub : openSubsetAtlas S.smoothStructure.val U U.isOpen ⊆ R.smoothStructure.val := by
    rw [hR]
    exact subset_maximalExtension
      (openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _ S.smoothStructure.property.1 U U.isOpen)
  let L := differential R S Subtype.val hinc
  let F (p : U) : TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val :=
    LinearEquiv.ofBijective (L p)
      (openInclusionDifferential_bijective S U R hRsub hinc p (L p)
        (differential_spec R S Subtype.val hinc p))
  have hF : ∀ p, IsDifferential R S Subtype.val p (F p).toLinearMap :=
    differential_spec R S Subtype.val hinc
  let P := inclusionPullChain S U R hinc (fun p => (F p).toLinearMap) hF K J D
  have hP : ∀ j, Function.Bijective (P.map j) := by
    intro j
    constructor
    · intro ω η h
      apply D.injective j
      funext p
      have hp := congrArg (fun β : J.forms j => β.val p) h
      change FormPullbackData.fiberPullback (V := TangentSpace R p)
          (W := TangentSpace S p.val) j (F p).toLinearMap (D.field j ω p) =
        FormPullbackData.fiberPullback (V := TangentSpace R p)
          (W := TangentSpace S p.val) j (F p).toLinearMap (D.field j η p) at hp
      have hinj : Function.Injective (FormPullbackData.fiberPullback
          (V := TangentSpace R p) (W := TangentSpace S p.val) j (F p).toLinearMap) :=
        exteriorPower.map_injective_field (n := j)
          (LinearMap.dualMap_injective_of_surjective (F p).surjective)
      exact hinj hp
    · intro α
      let ω : RestrictedField S U j := fun p =>
        FormPullbackData.fiberPullback (V := TangentSpace S p.val)
          (W := TangentSpace R p) j (F p).symm.toLinearMap (α.val p)
      have hω : IsRestrictedForm (B j) U ω :=
        openInverseField_smooth S U R hRsub hinc C A (B j) (E j) F hF α.val
          ((J.mem_forms j _).mp α.property)
      obtain ⟨η,hη⟩ := (D.range_smooth j ω).mp hω
      refine ⟨η, ?_⟩
      apply Subtype.ext
      funext p
      change FormPullbackData.fiberPullback (V := TangentSpace R p)
        (W := TangentSpace S p.val) j (F p).toLinearMap (D.field j η p) = α.val p
      rw [congrFun hη p]
      change FormPullbackData.fiberPullback (V := TangentSpace R p)
          (W := TangentSpace S p.val) j (F p).toLinearMap
        (FormPullbackData.fiberPullback (V := TangentSpace S p.val)
          (W := TangentSpace R p) j (F p).symm.toLinearMap (α.val p)) = α.val p
      exact @fiberPullback_symm_right (TangentSpace R p) (TangentSpace S p.val)
        (inferInstance : AddCommGroup (TangentSpace R p))
        (inferInstance : Module ℝ (TangentSpace R p))
        (inferInstance : AddCommGroup (TangentSpace S p.val))
        (inferInstance : Module ℝ (TangentSpace S p.val)) j (F p) (α.val p)
  exact ⟨cohomologyEquivOfDegreewiseBijective P hP k⟩


end OpenComparisonConstruction

namespace Computation
open MayerVietorisData MapData

private def sphere (n : ℕ) : SmoothManifold n .euclidean (Sphere n) :=
  (SphereTorus.sphereManifold n).2.2.choose

private def cotangent {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) : CotangentBundle S :=
  Classical.choice (BundleOperations.exists_cotangent S)

private def bundles {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (k : ℕ) : FormBundle (cotangent S) k :=
  Classical.choice (ExteriorAlgebraResults.exists_formBundle (cotangent S) k)

private def calculus {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) : Calculus (cotangent S) (bundles S) :=
  Classical.choice (DeRhamResults.complex_exists (cotangent S) (bundles S))

private def restricted {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M) : SmoothManifold n a U :=
  (SmoothManifolds.exists_openSubset_smoothManifold S U U.isOpen).choose

private theorem restricted_atlas {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M) :
    (restricted S U).smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U U.isOpen) :=
  (SmoothManifolds.exists_openSubset_smoothManifold S U U.isOpen).choose_spec.2.1

private theorem restricted_inclusion {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M) :
    IsSmoothMap (restricted S U) S Subtype.val :=
  (SmoothManifolds.exists_openSubset_smoothManifold S U U.isOpen).choose_spec.2.2

private abbrev H (n k : ℕ) := (calculus (sphere n)).Cohomology k

/-- The full smooth restricted complex on each chosen open subspace. -/
private def openCalculus {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M) :
    OpenCalculus (cotangent S) (bundles S) U :=
  Classical.choice (OpenForms.openCalculus_exists (calculus S) U)

private def poleCover (n : ℕ) :
    CoverComplex (calculus (sphere n)) (PoleTopology.cover n) :=
  OpenForms.assembledCover (calculus (sphere n)) (PoleTopology.cover n)
    (openCalculus (sphere n) (PoleTopology.cover n).U)
    (openCalculus (sphere n) (PoleTopology.cover n).V)
    (openCalculus (sphere n) ((PoleTopology.cover n).U ⊓ (PoleTopology.cover n).V))

private theorem openComparison {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} (K : Calculus C B)
    {U : TopologicalSpace.Opens M} (D : OpenCalculus C B U) (k : ℕ) :
    Nonempty (D.complex.H k ≃ₗ[ℝ] (calculus (restricted S U)).Cohomology k) := by
  exact openCohomologyEquiv S U (restricted S U) (restricted_atlas S U)
    (restricted_inclusion S U) K (calculus (restricted S U)) D k

private theorem positiveU (n k : ℕ) (hk : 0 < k) :
    Subsingleton ((poleCover n).onU.complex.H k) := by
  obtain ⟨e⟩ := openComparison (calculus (sphere n)) (poleCover n).onU k
  let R := restricted (sphere n) (PoleTopology.cover n).U
  have hz : Subsingleton ((calculus R).Cohomology k) :=
    (PoleTopology.complements_positive_vanishing n).1
      R (cotangent R) (bundles R) (calculus R) k hk
  exact ⟨fun x y => e.injective (hz.elim _ _)⟩

private theorem positiveV (n k : ℕ) (hk : 0 < k) :
    Subsingleton ((poleCover n).onV.complex.H k) := by
  obtain ⟨e⟩ := openComparison (calculus (sphere n)) (poleCover n).onV k
  let R := restricted (sphere n) (PoleTopology.cover n).V
  have hz : Subsingleton ((calculus R).Cohomology k) :=
    (PoleTopology.complements_positive_vanishing n).2
      R (cotangent R) (bundles R) (calculus R) k hk
  exact ⟨fun x y => e.injective (hz.elim _ _)⟩

private theorem overlap (r k : ℕ) :
    Nonempty ((poleCover (r+1)).onOverlap.complex.H k ≃ₗ[ℝ] H r k) := by
  obtain ⟨e⟩ := openComparison (calculus (sphere (r+1))) (poleCover (r+1)).onOverlap k
  let R := restricted (sphere (r+1))
    ((PoleTopology.cover (r+1)).U ⊓ (PoleTopology.cover (r+1)).V)
  obtain ⟨f⟩ := PoleTopology.overlap_cohomology r R (sphere r)
    (cotangent R) (bundles R) (cotangent (sphere r)) (bundles (sphere r))
    (calculus R) (calculus (sphere r)) k
  exact ⟨e.trans f⟩

private theorem higher (n : ℕ) (_hn : 0 < n) (k : ℕ) :
    Nonempty (H (n+1) (k+2) ≃ₗ[ℝ] H n (k+1)) := by
  obtain ⟨e⟩ := overlap n (k+1)
  let d := CoverAlgebra.higherCoverEquiv (globalComplex (calculus (sphere (n+1))))
    (poleCover (n+1)).onU.complex (poleCover (n+1)).onV.complex
    (poleCover (n+1)).onOverlap.complex (poleCover (n+1)).sequence
    (positiveU (n+1)) (positiveV (n+1)) k
  exact ⟨d.trans e⟩

private theorem first (n : ℕ) (hn : 0 < n) : Subsingleton (H (n+1) 1) := by
  exact CoverAlgebra.firstCoverVanishes (globalComplex (calculus (sphere (n+1))))
    (poleCover (n+1)).onU.complex (poleCover (n+1)).onV.complex
    (poleCover (n+1)).onOverlap.complex (poleCover (n+1)).sequence
    (positiveU (n+1) 1 (by omega)) (positiveV (n+1) 1 (by omega))
    (PoleTopology.higher_open_difference_surjective n hn (sphere (n+1))
      (cotangent (sphere (n+1))) (bundles (sphere (n+1)))
      (calculus (sphere (n+1))) (poleCover (n+1)))

private theorem circle : Nonempty (H 1 1 ≃ₗ[ℝ] ℝ) := by
  obtain ⟨e, he⟩ := PoleTopology.circle_open_difference_range (sphere 1) (cotangent (sphere 1))
    (bundles (sphere 1)) (calculus (sphere 1)) (poleCover 1)
  exact ⟨CoverAlgebra.circleCoverEquiv (globalComplex (calculus (sphere 1)))
    (poleCover 1).onU.complex (poleCover 1).onV.complex
    (poleCover 1).onOverlap.complex (poleCover 1).sequence
    (positiveU 1 1 (by omega)) (positiveV 1 1 (by omega)) e he⟩

private theorem classification :
    ∀ n, 0 < n → Nonempty (H n 0 ≃ₗ[ℝ] ℝ) ∧ Nonempty (H n n ≃ₗ[ℝ] ℝ) ∧
      ∀ k, k ≠ 0 → k ≠ n → Subsingleton (H n k) := by
  apply classifyBySuspension H
  · intro n hn
    exact h0_positive n hn (sphere n) (cotangent (sphere n))
      (bundles (sphere n)) (calculus (sphere n))
  · exact circle
  · intro n k hk
    exact DeRhamResults.above_dimension (calculus (sphere n)) k hk
  · exact first
  · exact higher

end Computation

/-- Full real de Rham degree classification for every standard smooth sphere. -/
theorem sphere_cohomology : Specs.SmoothManifolds.DeRham.Spheres.sphere_cohomologyType := by
  intro n hn S _hstandard C B K
  obtain ⟨hzero, htop, hother⟩ := Computation.classification n hn
  have he (k : ℕ) : Nonempty (K.Cohomology k ≃ₗ[ℝ] Computation.H n k) :=
    cohomologyEquivOfHomotopyEquiv S (Computation.sphere n) C B
      (Computation.cotangent (Computation.sphere n))
      (Computation.bundles (Computation.sphere n)) K
      (Computation.calculus (Computation.sphere n))
      (ContinuousMap.HomotopyEquiv.refl (Sphere n)) k
  obtain ⟨e0⟩ := he 0
  obtain ⟨en⟩ := he n
  obtain ⟨f0⟩ := hzero
  obtain ⟨fn⟩ := htop
  refine ⟨⟨e0.trans f0⟩, ⟨en.trans fn⟩, ?_⟩
  intro k hk0 hkn
  obtain ⟨e⟩ := he k
  have hz := hother k hk0 hkn
  exact ⟨fun x y => e.injective (hz.elim _ _)⟩


end SmoothManifolds.SphereCohomology
