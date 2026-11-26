import Specs.LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
import Specs.LinearAlgebraicGroups.Arithmetic.LocalRescaling
import LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import LinearAlgebraicGroups.Affine.FaithfulLinearization
import LinearAlgebraicGroups.Arithmetic.IsotropicOuterTypeA
import LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
import LinearAlgebraicGroups.Arithmetic.LocalBruhatTorusCommutator
import LinearAlgebraicGroups.Arithmetic.LocalMinimalParabolicDynamics
import LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo
import LinearAlgebraicGroups.Arithmetic.QuaternionSpinOddCharacteristic
import LinearAlgebraicGroups.Arithmetic.QuasiSplitRadicalGeneration
import LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
import LinearAlgebraicGroups.Relative.RationalFlagLifting
import LinearAlgebraicGroups.Relative.RelativeBruhat
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.Algebra.Polynomial
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRadicalGeneration
import LinearAlgebraicGroups.Arithmetic.LocalRescaling
open AlgebraicGeometry CategoryTheory Filter Opposite Topology
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Topology commutatorElement

universe u

set_option linter.style.haveILetI false

namespace LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure

open LocalQuotientTransport (closedNormalClosure)
open LocalAlgebraicTransport
  (RationalPoints pointTopology rationalPointTopologicalGroup)
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme SubgroupSections)
open Specs.ExceptionalMarkedRootDescent (coordinatePointEquiv)
open Specs.ExceptionalIwahoriCongruence (affinePointTopology)
open Specs.ExceptionalLocalRadicalGeneration (localPointTopology)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.Arithmetic.LocalQuotientMixing
  (HasDenseRadicals IsIsotropicSpecialUnitary IsIsotropicQuadraticSpin
   IsIsotropicQuaternionicSpin MixingCases)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Specs.GeometricBorelConjugacy (IsQuasiSplit)
open Specs.GeometricRadicals (IsSplitReductive)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.IntegralModels (MatrixRealization)
open AdelicGroups (PointsIn asMatrix)
open Specs.QuasiSplitOrbitAmbientWords (groundPointIso)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.BorelProper (IsParabolic)
open Specs.Relative.Parabolics (CocharacterLeviDecomposition)
open Specs.CharacterDescent (Cocharacter)
open CocharacterDynamics (HasLimit cocharacterPoint polynomialAlgebra polynomialEvaluate
  polynomialToLaurent mapPoints_comp HasExtension LimitDecomposition oppositeCocharacter
  existsLimitDecomposition oppositeLimit_intersection_onPoints)
open private evalLaurent orbit_eval unitPointHom opposite_point centralizes_hasLimit centralizes_onAlgebras from
  LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private centralizes_opposite_iff from LinearAlgebraicGroups.RootData.RankOneFlag
open private terminalPointHom terminalSubgroup_map from
  LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration
open private reductive_of_semisimple from
  LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private exists_regular_cocharacter from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private matrixPresentation continuous_glEvaluation from
  LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private glEvaluation from LinearAlgebraicGroups.Affine.StandardGroups
open private coordinateMap coordinateMap_spec from LinearAlgebraicGroups.Arithmetic.IntegralModels
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private cocharacterPoint_postcompose from LinearAlgebraicGroups.RootData.OrderedRootProducts
open Specs.Arithmetic.LocalProjectedClosure (LocalNormalClosure FiniteCovolumeSubgroup)

section CosetAction

variable {G : Type*} [Group G]

/-- If a maximal proper subgroup has central core, the central quotient's
coset action is faithful and primitive. -/
theorem faithful_preprimitive_central_quotient {P : Subgroup G}
    (hP : IsCoatom P) (hcore : P.normalCore = Subgroup.center G) :
    let Q := G ⧸ Subgroup.center G
    let P' := P.map (QuotientGroup.mk' (Subgroup.center G))
    FaithfulSMul Q (Q ⧸ P') ∧ MulAction.IsPreprimitive Q (Q ⧸ P') := by
  let Q := G ⧸ Subgroup.center G
  let q : G →* Q := QuotientGroup.mk' (Subgroup.center G)
  let P' := P.map q
  have hker : q.ker ≤ P := by
    rw [show q.ker = Subgroup.center G from QuotientGroup.ker_mk' _]
    exact hcore ▸ P.normalCore_le
  have hcomap : P'.comap q = P := Subgroup.comap_map_eq_self hker
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hproper : P' ≠ ⊤ := fun h => hP.ne_top (by rw [← hcomap, h, Subgroup.comap_top])
  have hmax : IsCoatom P' := by
    refine SetLike.isCoatom_iff.mpr ⟨hproper, fun K k hK hkP hkK => ?_⟩
    obtain ⟨g, rfl⟩ := hsurj k
    have h : K.comap q = ⊤ := (SetLike.isCoatom_iff.mp hP).2 (K.comap q) g
      (by rw [← hcomap]; exact Subgroup.comap_mono hK)
      (fun hg => hkP (Subgroup.mem_map_of_mem q hg)) hkK
    rw [← Subgroup.map_comap_eq_self_of_surjective hsurj K, h, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr hsurj]
  change FaithfulSMul Q (Q ⧸ P') ∧ MulAction.IsPreprimitive Q (Q ⧸ P')
  constructor
  · rw [faithfulSMul_iff]
    intro x hx
    obtain ⟨g, rfl⟩ := hsurj x
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [← hcore]
    intro y
    have hy := hx (QuotientGroup.mk (q y⁻¹) : Q ⧸ P')
    change QuotientGroup.mk (q g * q y⁻¹) = QuotientGroup.mk (q y⁻¹) at hy
    have hmem : (q y⁻¹)⁻¹ * (q g * q y⁻¹) ∈ P' := QuotientGroup.eq.mp hy.symm
    rw [← map_inv, inv_inv] at hmem
    rw [← hcomap]
    change q (y * g * y⁻¹) ∈ P'
    simpa only [map_mul, mul_assoc] using hmem
  · let _ : Nontrivial (Q ⧸ P') := QuotientGroup.nontrivial_iff.mpr hproper
    rw [← MulAction.isCoatom_stabilizer_iff_preprimitive Q ((1 : Q) : Q ⧸ P'),
      MulAction.stabilizer_quotient]
    exact hmax

end CosetAction

section TopologicalGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- When the conjugating element belongs to a closed normal subgroup, so do
all points contracted by its nonnegative powers. -/
theorem mem_of_conj_pow_tendsto_one {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) {a g : G} (ha : a ∈ N)
    (hg : Tendsto (fun n : ℕ => a ^ n * g * (a ^ n)⁻¹) atTop (𝓝 1)) :
    g ∈ N := by
  let q := QuotientGroup.mk' N
  have hlim : Tendsto (fun n : ℕ => a ^ n * g * (a ^ n)⁻¹ * g⁻¹)
      atTop (𝓝 g⁻¹) := by
    simpa only [one_mul] using hg.mul (tendsto_const_nhds (x := g⁻¹))
  have hmem (n : ℕ) : a ^ n * g * (a ^ n)⁻¹ * g⁻¹ ∈ N := by
    have hq : q (a ^ n) = 1 := (QuotientGroup.eq_one_iff _).mpr (N.pow_mem ha n)
    apply (QuotientGroup.eq_one_iff _).mp
    change q (a ^ n * g * (a ^ n)⁻¹ * g⁻¹) = 1
    simp only [map_mul, map_inv, hq, one_mul, inv_one, mul_one, mul_inv_cancel]
  simpa only [inv_inv] using N.inv_mem (hN.mem_of_tendsto hlim (.of_forall hmem))

/-- A normal subgroup commuting with an element whose two contraction
groups generate densely lies in the center. -/
theorem le_center_of_commute_and_dense_contractions [T2Space G]
    {N U V : Subgroup G} [N.Normal] {a : G}
    (hN : ∀ n ∈ N, Commute a n)
    (hU : ∀ u ∈ U, Tendsto (fun n : ℕ => a ^ n * u * (a ^ n)⁻¹) atTop (𝓝 1))
    (hV : ∀ v ∈ V, Tendsto (fun n : ℕ => a⁻¹ ^ n * v * (a⁻¹ ^ n)⁻¹) atTop (𝓝 1))
    (hgen : Dense ((U ⊔ V : Subgroup G) : Set G)) :
    N ≤ Subgroup.center G := by
  let C := Subgroup.centralizer (N : Set G)
  letI : C.Normal := Subgroup.normal_centralizer
  have hC : IsClosed (C : Set G) := Set.isClosed_centralizer (N : Set G)
  have ha : a ∈ C := Subgroup.mem_centralizer_iff.mpr fun n hn => (hN n hn).symm.eq
  have hUV : U ⊔ V ≤ C := sup_le
    (fun u hu => mem_of_conj_pow_tendsto_one hC ha (hU u hu))
    (fun v hv => mem_of_conj_pow_tendsto_one hC (C.inv_mem ha) (hV v hv))
  apply Subgroup.centralizer_eq_top_iff_subset.mp
  exact eq_top_iff.mpr fun g _ => closure_minimal hUV hC (hgen g)

/-- If two representatives agree modulo a closed normal subgroup, their
commutators agree there. A commuting commutator can then be recovered as the
limit obtained by contracting the other representative. -/
theorem commutator_mem_of_conj_pow_tendsto {N : Subgroup G} [N.Normal]
    (hN : IsClosed (N : Set G)) {a t b p z : G}
    (hb : QuotientGroup.mk' N b = QuotientGroup.mk' N p)
    (hat : Commute a t) (htz : Commute t z) (hab : Commute a ⁅t, b⁆)
    (hp : Tendsto (fun n : ℕ => a ^ n * p * (a ^ n)⁻¹) atTop (𝓝 z)) :
    ⁅t, b⁆ ∈ N := by
  let q := QuotientGroup.mk' N
  have hcomm : Tendsto (fun n : ℕ => ⁅t, a ^ n * p * (a ^ n)⁻¹⁆)
      atTop (𝓝 1) := by
    have h1 : ⁅t, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr htz.eq
    rw [← h1, commutatorElement_def]
    exact (((tendsto_const_nhds (x := t)).mul hp).mul
      (tendsto_const_nhds (x := t⁻¹))).mul hp.inv
  have hlim : Tendsto (fun n : ℕ => ⁅t, b⁆ * ⁅t, a ^ n * p * (a ^ n)⁻¹⁆⁻¹)
      atTop (𝓝 ⁅t, b⁆) := by
    simpa only [inv_one, mul_one] using (tendsto_const_nhds (x := ⁅t, b⁆)).mul hcomm.inv
  apply hN.mem_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro n
  apply (QuotientGroup.eq_one_iff _).mp
  let a' := a ^ n
  have hqa : Commute (q a') (q t) := (hat.pow_left n).map q
  have hqb : Commute (q a') (q ⁅t, b⁆) := (hab.pow_left n).map q
  have h : q ⁅t, a' * p * a'⁻¹⁆ = q ⁅t, b⁆ := by
    rw [map_commutatorElement, map_mul, map_mul, map_inv, ← hb]
    calc
      _ = q a' * q ⁅t, b⁆ * (q a')⁻¹ := by
        rw [map_commutatorElement, conjugate_commutatorElement, hqa.mul_inv_cancel]
      _ = q ⁅t, b⁆ := hqb.mul_inv_cancel
  change q (⁅t, b⁆ * ⁅t, a' * p * a'⁻¹⁆⁻¹) = 1
  rw [map_mul, map_inv, h, mul_inv_cancel]

/-- A point contracted to the identity by conjugations lies in the closure
of the commutator subgroup. -/
theorem mem_closedCommutator_of_contraction {g : G} (a : ℕ → G)
    (h : Tendsto (fun n => a n * g * (a n)⁻¹) atTop (𝓝 1)) :
    g ∈ (commutator G).topologicalClosure := by
  have hlim : Tendsto (fun n => a n * g * (a n)⁻¹ * g⁻¹) atTop (𝓝 g⁻¹) := by
    simpa only [one_mul] using h.mul (tendsto_const_nhds (x := g⁻¹))
  have hmem : ∀ n, a n * g * (a n)⁻¹ * g⁻¹ ∈ commutator G := fun n =>
    show ⁅a n, g⁆ ∈ commutator G by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (by simp) (by simp)
  have hinv : g⁻¹ ∈ (commutator G).topologicalClosure :=
    mem_closure_of_tendsto hlim (.of_forall hmem)
  simpa only [inv_inv] using (commutator G).topologicalClosure.inv_mem hinv

/-- Dense normal generation by contracted points gives topological perfection. -/
theorem closedCommutator_eq_top_of_contractions {s : Set G} (hs : closedNormalClosure s = ⊤)
    (h : ∀ g ∈ s, ∃ a : ℕ → G, Tendsto (fun n => a n * g * (a n)⁻¹) atTop (𝓝 1)) :
    (commutator G).topologicalClosure = ⊤ := by
  let _ := Subgroup.is_normal_topologicalClosure (commutator G)
  rw [eq_top_iff, ← hs]
  apply Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_topologicalClosure _)
  apply Subgroup.normalClosure_le_normal
  intro g hg
  obtain ⟨a, ha⟩ := h g hg
  exact mem_closedCommutator_of_contraction a ha

/-- The closed-subgroup form of the Iwasawa argument. The core of the coset
stabilizer lies in the center, and conjugates of its abelian subgroup
topologically generate the group. -/
theorem eq_top_of_isCoatom_of_dense_abelian_conjugates
    {P A N : Subgroup G} [IsMulCommutative A] [N.Normal]
    (hP : IsCoatom P) (hcore : P.normalCore ≤ Subgroup.center G)
    (hA : ∀ p ∈ P, ∀ a ∈ A, p * a * p⁻¹ ∈ A)
    (hgen : closedNormalClosure (A : Set G) = ⊤)
    (hperfect : (commutator G).topologicalClosure = ⊤)
    (hclosed : IsClosed (N : Set G)) (hn : ¬ N ≤ Subgroup.center G) :
    N = ⊤ := by
  have hnP : ¬ N ≤ P := fun h => hn ((Subgroup.normal_le_normalCore.mpr h).trans hcore)
  obtain ⟨n, hnN, hnP⟩ := IsConcreteLE.not_le_iff_exists.mp hnP
  have hNP : N ⊔ P = ⊤ :=
    (SetLike.isCoatom_iff.mp hP).2 _ n le_sup_right hnP (Subgroup.mem_sup_left hnN)
  have hnormal : Subgroup.normalClosure (A : Set G) ≤ N ⊔ A := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro b hb
    obtain ⟨a, ha, hab⟩ := Group.mem_conjugatesOfSet_iff.mp hb
    obtain ⟨k, rfl⟩ := isConj_iff.mp hab
    have hk : k ∈ N ⊔ P := by rw [hNP]; trivial
    obtain ⟨m, hm, p, hp, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hk
    have hm' : m ∈ N ⊔ A := Subgroup.mem_sup_left hm
    have ha' : p * a * p⁻¹ ∈ N ⊔ A := Subgroup.mem_sup_right (hA p hp a ha)
    change (m * p) * a * (m * p)⁻¹ ∈ N ⊔ A
    simpa only [mul_inv_rev, mul_assoc] using
      (N ⊔ A).mul_mem hm' ((N ⊔ A).mul_mem ha' ((N ⊔ A).inv_mem hm'))
  let B := (N ⊔ A).topologicalClosure
  have hB : B = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact Subgroup.topologicalClosure_mono hnormal
  have hcentral : commutator G ≤ N := by
    -- Use density to extend the pairwise commutator relation from `N ⊔ A`.
    have hpair : ⁅N ⊔ A, N ⊔ A⁆ ≤ N := by
      let q := QuotientGroup.mk' N
      suffices h : Subgroup.map q ⁅N ⊔ A, N ⊔ A⁆ = ⊥ by
        simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp h
      dsimp only [q]
      rw [Subgroup.map_commutator, Subgroup.map_sup, QuotientGroup.map_mk'_self,
        bot_sup_eq, Subgroup.commutator_self_eq_bot_iff]
      infer_instance
    have hdense : Dense ((N ⊔ A : Subgroup G) : Set G) := by
      rw [dense_iff_closure_eq]
      exact congrArg (fun H : Subgroup G => (H : Set G)) hB
    have hclosedPair : IsClosed {p : G × G | ⁅p.1, p.2⁆ ∈ N} := by
      change IsClosed ((fun p : G × G => p.1 * p.2 * p.1⁻¹ * p.2⁻¹) ⁻¹' (N : Set G))
      exact hclosed.preimage (by fun_prop)
    have hall := closure_minimal
      (show ((N ⊔ A : Subgroup G) : Set G) ×ˢ ((N ⊔ A : Subgroup G) : Set G) ⊆
          {p : G × G | ⁅p.1, p.2⁆ ∈ N} from fun _ hp => hpair (Subgroup.commutator_mem_commutator hp.1 hp.2))
      hclosedPair
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hall (hdense.prod hdense (x, y))
  rw [eq_top_iff, ← hperfect]
  exact Subgroup.topologicalClosure_minimal _ hcentral hclosed

/-- The closed normal subgroup generated by a point outside the center is
the whole group under the topological Iwasawa hypotheses. -/
theorem normalClosure_eq_univ_of_isCoatom
    {P A : Subgroup G} [IsMulCommutative A]
    (hP : IsCoatom P) (hcore : P.normalCore ≤ Subgroup.center G)
    (hA : ∀ p ∈ P, ∀ a ∈ A, p * a * p⁻¹ ∈ A)
    (hgen : closedNormalClosure (A : Set G) = ⊤)
    (hperfect : (commutator G).topologicalClosure = ⊤)
    {g : G} (hg : g ∉ Subgroup.center G) :
    closure (Subgroup.normalClosure ({g} : Set G) : Set G) = Set.univ := by
  let N := closedNormalClosure ({g} : Set G)
  let _ : N.Normal := Subgroup.is_normal_topologicalClosure _
  have hgN : g ∈ N :=
    Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (Set.mem_singleton g))
  have hN : N = ⊤ :=
    eq_top_of_isCoatom_of_dense_abelian_conjugates hP hcore hA hgen hperfect
      (Subgroup.isClosed_topologicalClosure _) (fun h => hg (h hgN))
  exact congrArg (fun H : Subgroup G => (H : Set G)) hN

/-- A closed subgroup containing a conjugate of the whole conjugacy class
of a topological normal generator is the whole group. -/
theorem eq_top_of_conjugated_class {H : Subgroup G} (hH : IsClosed (H : Set G))
    {x g : G} (hgen : closure (Subgroup.normalClosure ({g} : Set G) : Set G) = Set.univ)
    (hclass : ∀ y : G, x * (y * g * y⁻¹) * x⁻¹ ∈ H) :
    H = ⊤ := by
  let K := H.comap (MulAut.conj x).toMonoidHom
  have hK : IsClosed (K : Set G) :=
    hH.preimage (IsTopologicalGroup.continuous_conj x)
  have hle : Subgroup.normalClosure ({g} : Set G) ≤ K := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro b hb
    obtain ⟨a, ha, h⟩ := Group.mem_conjugatesOfSet_iff.mp hb
    obtain rfl : a = g := ha
    obtain ⟨y, rfl⟩ := isConj_iff.mp h
    exact hclass y
  have htop : K = ⊤ := by
    rw [eq_top_iff]
    have h := closure_minimal hle hK
    rw [hgen] at h
    exact h
  rw [eq_top_iff]
  intro z _
  obtain ⟨y, rfl⟩ := (MulAut.conj x).surjective z
  have hy : y ∈ K := by rw [htop]; trivial
  exact hy

end TopologicalGroup

section CocharacterContraction

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

set_option backward.isDefEq.respectTransparency false in
private theorem continuous_polynomial_point {X : SchemeOver F}
    (f : Points X (polynomialAlgebra (CommAlgCat.of F F))) :
    letI := pointTopology X
    Continuous (fun t : F => mapPoints (polynomialEvaluate (CommAlgCat.of F F) t) f) := by
  let R := CommAlgCat.of F F
  letI := pointTopology X
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  let p : Polynomial F :=
    (f.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (Polynomial F))).hom).hom a
  have h (t : F) : LocalAlgebraicTransport.evaluation (mapPoints (polynomialEvaluate R t) f) a = p.eval t := by
    change ((Spec.map (CommRingCat.ofHom (polynomialEvaluate R t).hom.toRingHom) ≫
      f.left).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom a = _
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
    rfl
  change Continuous (fun t : F => LocalAlgebraicTransport.evaluation (mapPoints (polynomialEvaluate R t) f) a)
  simpa only [h] using p.continuous

set_option backward.isDefEq.respectTransparency false in
/-- An algebraically extended conjugation orbit converges at zero in the
coordinate topology of the original group scheme. -/
theorem tendsto_conjugation_of_hasLimit {G : GroupScheme F} (c : Cocharacter G)
    {g z : RationalPoints G.X} (h : HasLimit c g z)
    (π : ℕ → Fˣ) (hπ : Tendsto (fun n => (π n : F)) atTop (𝓝 0)) :
    letI := pointTopology G.X
    Tendsto (fun n =>
      let a : RationalPoints G.X := cocharacterPoint c (CommAlgCat.of F F) (π n)
      a * g * a⁻¹) atTop (𝓝 z) := by
  let R := CommAlgCat.of F F
  letI := pointTopology G.X
  obtain ⟨f, hf, hz⟩ := h
  have heval (s : Fˣ) :
      polynomialToLaurent R ≫ evalLaurent (𝟙 R) s = polynomialEvaluate R s := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro p
    change LaurentPolynomial.eval₂ (RingHom.id F) s p.toLaurent =
      (Polynomial.aevalTower (AlgHom.id F F) (s : F)) p
    rw [LaurentPolynomial.eval₂_toLaurent]
    rfl
  have happ (s : Fˣ) :
      let a : RationalPoints G.X := cocharacterPoint c R s
      mapPoints (polynomialEvaluate R s) f = a * g * a⁻¹ := by
    have h := congrArg (mapPoints (X := G.X) (evalLaurent (𝟙 R) s)) hf
    rw [← mapPoints_comp, heval, orbit_eval] at h
    have hg : mapPoints (𝟙 R) g = g := by simp [mapPoints]
    rwa [hg] at h
  have hcont := (continuous_polynomial_point f).continuousAt (x := (0 : F))
  have hlim : Tendsto (fun n => mapPoints (polynomialEvaluate R (π n)) f) atTop (𝓝 z) := by
    simpa only [Function.comp_def, hz] using hcont.tendsto.comp hπ
  simpa only [happ] using hlim

end CocharacterContraction

section RationalPoints

variable {F : Type u} [Field F]

private noncomputable def rationalSectionEquiv (J : AffineAlgebraicGroup F) :
    (𝟙_ (SchemeOver F) ⟶ J.val.X) ≃* RationalPoints J.val.X where
  toFun p := (groundPointIso F).inv ≫ p
  invFun p := (groundPointIso F).hom ≫ p
  left_inv p := (groundPointIso F).hom_inv_id_assoc p
  right_inv p := (groundPointIso F).inv_hom_id_assoc p
  map_mul' _x _y := MonObj.comp_mul _ _ _

set_option backward.isDefEq.respectTransparency false in
private noncomputable def coordinateEquiv (J : AffineAlgebraicGroup F) :
    Γ(J.val.X.left, ⊤) ≃+* Specs.AdjointCocharacters.coordinateHopf J :=
  ((Scheme.Γ.mapIso ((Grp.forget (SchemeOver F) ⋙ Over.forget _).mapIso
      (Specs.AdjointCocharacters.coordinateHopfIso J)).op).trans (Scheme.ΓSpecIso _)).commRingCatIsoToRingEquiv

set_option maxHeartbeats 700000 in
set_option backward.isDefEq.respectTransparency false in
private theorem evaluation_coordinateEquiv (J : AffineAlgebraicGroup F)
    (p : RationalPoints J.val.X) (a : Γ(J.val.X.left, ⊤)) :
    LocalAlgebraicTransport.evaluation p a =
      ((coordinatePointEquiv J (CommAlgCat.of F F)).symm p).ofConv (coordinateEquiv J a) := by
  let b := coordinatePointEquiv J (CommAlgCat.of F F)
  obtain ⟨x, rfl⟩ := b.surjective p
  rw [MulEquiv.symm_apply_apply]
  change ((Spec.map (CommRingCat.ofHom x.ofConv.toRingHom) ≫
      (Specs.AdjointCocharacters.coordinateHopfIso J).hom.hom.hom.left).appTop ≫ (Scheme.ΓSpecIso _).hom).hom a = _
  rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
  rfl

theorem rationalPoints_t2Space [TopologicalSpace F] [T2Space F] (J : AffineAlgebraicGroup F) :
    letI := pointTopology J.val.X
    T2Space (RationalPoints J.val.X) := by
  letI := pointTopology J.val.X
  let ev (p : RationalPoints J.val.X) (a : Γ(J.val.X.left, ⊤)) :=
    LocalAlgebraicTransport.evaluation p a
  have hinj : Function.Injective ev := by
    intro p q hpq
    apply (coordinatePointEquiv J (CommAlgCat.of F F)).symm.injective
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro a
    obtain ⟨b, rfl⟩ := (coordinateEquiv J).surjective a
    have h := congrFun hpq b
    change LocalAlgebraicTransport.evaluation p b = LocalAlgebraicTransport.evaluation q b at h
    rwa [evaluation_coordinateEquiv, evaluation_coordinateEquiv] at h
  exact (show IsEmbedding ev from ⟨⟨rfl⟩, hinj⟩).t2Space

set_option backward.isDefEq.respectTransparency false in
private theorem section_point_topology [TopologicalSpace F] (J : AffineAlgebraicGroup F) :
    localPointTopology J = TopologicalSpace.induced (rationalSectionEquiv J) (pointTopology J.val.X) := by
  apply le_antisymm
  · apply continuous_iff_le_induced.mp
    letI := localPointTopology J
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro a
    change Continuous (fun p => LocalAlgebraicTransport.evaluation (rationalSectionEquiv J p) a)
    simp only [evaluation_coordinateEquiv]
    letI := affinePointTopology F (Specs.AdjointCocharacters.coordinateHopf J) F
    have h₁ : Continuous (fun b : Specs.AdjointCocharacters.coordinateHopf J →ₐ[F] F => (b : Specs.AdjointCocharacters.coordinateHopf J → F)) :=
      continuous_induced_dom
    have h₂ : Continuous (fun p : 𝟙_ (SchemeOver F) ⟶ J.val.X =>
        ((coordinatePointEquiv J (CommAlgCat.of F F)).symm (rationalSectionEquiv J p)).ofConv) :=
      continuous_induced_dom
    exact (continuous_apply (coordinateEquiv J a)).comp (h₁.comp h₂)
  · letI : TopologicalSpace (𝟙_ (SchemeOver F) ⟶ J.val.X) :=
      TopologicalSpace.induced (rationalSectionEquiv J) (pointTopology J.val.X)
    letI := pointTopology J.val.X
    apply continuous_iff_le_induced.mp
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro a
    change Continuous
      (fun p => ((coordinatePointEquiv J (CommAlgCat.of F F)).symm (rationalSectionEquiv J p)).ofConv a)
    have hc : Continuous (fun p => LocalAlgebraicTransport.evaluation (rationalSectionEquiv J p) ((coordinateEquiv J).symm a)) :=
      ((continuous_apply _).comp (continuous_induced_dom : @Continuous _ _
        (pointTopology J.val.X) _ (fun p a => LocalAlgebraicTransport.evaluation p a))).comp continuous_induced_dom
    simpa only [evaluation_coordinateEquiv, RingEquiv.apply_symm_apply] using hc

theorem hasDenseRadicals_of_dense_sections [TopologicalSpace F] (J : AffineAlgebraicGroup F)
    (h : @Dense _ (localPointTopology J)
      (unipotentGenerated J : Set (𝟙_ (SchemeOver F) ⟶ J.val.X))) :
    HasDenseRadicals J := by
  letI := pointTopology J.val.X
  letI : TopologicalSpace (𝟙_ (SchemeOver F) ⟶ J.val.X) :=
    TopologicalSpace.induced (rationalSectionEquiv J) inferInstance
  rw [section_point_topology J] at h
  have hi : IsInducing (rationalSectionEquiv J) := ⟨rfl⟩
  have hd : DenseRange (rationalSectionEquiv J) := (rationalSectionEquiv J).surjective.denseRange
  have h' := hd.dense_image hi.continuous h
  refine h'.mono ?_
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨p, hp, ?_⟩
  change toUnit _ ≫ p = (groundPointIso F).inv ≫ p
  congr 1
  exact (isTerminalTensorUnit (C := SchemeOver F)).hom_ext _ _

theorem hasDenseRadicals_of_unipotentGenerated_eq_top [TopologicalSpace F]
    (J : AffineAlgebraicGroup F) (h : unipotentGenerated J = ⊤) :
    HasDenseRadicals J := by
  letI := localPointTopology J
  apply hasDenseRadicals_of_dense_sections
  rw [h, Subgroup.coe_top]
  exact dense_univ

private theorem eq_top_of_dense_radicals [TopologicalSpace F]
    (J : AffineAlgebraicGroup F) (hdense : HasDenseRadicals J)
    (K : Subgroup (RationalPoints J.val.X)) :
    letI := pointTopology J.val.X
    IsClosed (K : Set (RationalPoints J.val.X)) →
    unipotentGenerated J ≤ K.comap (rationalSectionEquiv J).toMonoidHom → K = ⊤ := by
  letI := pointTopology J.val.X
  intro hclosed hgen
  change Dense {g : RationalPoints J.val.X |
    ∃ x ∈ unipotentGenerated J, toUnit _ ≫ x = g} at hdense
  have hle : {g : RationalPoints J.val.X |
    ∃ x ∈ unipotentGenerated J, toUnit _ ≫ x = g} ⊆ (K : Set _) := by
    rintro g ⟨x, hx, rfl⟩
    have heq : toUnit ((testSpec F).obj (.op (CommAlgCat.of F F))) =
        (groundPointIso F).inv := (isTerminalTensorUnit (C := SchemeOver F)).hom_ext _ _
    rw [heq]
    exact hgen hx
  exact eq_top_iff.mpr fun g _ => closure_minimal hle hclosed (hdense g)

open ValuativeRel in
theorem exists_unit_powers_tendsto_zero [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    ∃ π : Fˣ, Tendsto (fun n : ℕ => (π : F) ^ n) atTop (𝓝 0) := by
  obtain ⟨x, hx, hv⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  refine ⟨Units.mk0 x hx, ?_⟩
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  have := (ValuativeRel.isRankLeOne_iff_mulArchimedean (R := F)).mp inferInstance
  apply Valued.tendsto_zero_pow_of_v_lt_one (Γ₀ := ValueGroupWithZero F)
  rwa [IsValuativeTopology.v_eq_valuation]

/-- The exceptional generation premise supplies density in the common local
rational-point topology for each of the exceptional cases. -/
theorem hasDenseRadicals_of_exceptional_case
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (hGeneration : Specs.ExceptionalLocalRadicalGeneration.LocalRadicalGeneration.{u})
    (J : AffineAlgebraicGroup F)
    (hJ : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple J)
    (hsc : Specs.SimplyConnectedLattice.GeometricallySimplyConnected J)
    (hcase : Specs.Arithmetic.LocalQuotientMixing.IsExceptionalCase J) :
    HasDenseRadicals J := by
  have ht : Specs.ExceptionalLocalRadicalGeneration.HasAbsoluteTypeE J 6 ∨
      Specs.ExceptionalLocalRadicalGeneration.HasAbsoluteTypeE J 7 ∨
      Specs.ExceptionalLocalRadicalGeneration.HasAbsoluteTypeE J 8 := by
    rcases hcase with h | h | h
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h.1)
    · exact Or.inl h.1
  exact hasDenseRadicals_of_dense_sections J (hGeneration F J hJ hsc ht).2

set_option backward.isDefEq.respectTransparency false in
private theorem radical_hasLimit (hLevi : CocharacterLeviDecomposition.{u})
    {F : Type u} [Field F] (J : AffineAlgebraicGroup F)
    {P : ClosedSubgroup J.val} (hP : IsParabolic J P) {U : ClosedSubgroup P.group}
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U)
    (p : RationalPoints U.group.X) :
    ∃ c : Cocharacter J.val,
      HasLimit c (p ≫ U.inclusion.hom.hom ≫ P.inclusion.hom.hom) 1 := by
  obtain ⟨c, D, e, U', i, L, j, he, hi, _, _, _, _, _, hU', _⟩ := hLevi J P hP
  obtain ⟨k, hk⟩ := hU'.2.2 U hU.1 hU.2.1
  have eq : (k ≫ i.hom) ≫ D.contracting.inclusion = U.inclusion ≫ P.inclusion := by
    rw [Category.assoc, ← D.contracting_in_G, ← Category.assoc i.hom, hi,
      Category.assoc U'.inclusion, he, ← Category.assoc, hk]
  refine ⟨c, (D.contracting_points _ _).mpr ⟨p ≫ (k ≫ i.hom).hom.hom, ?_⟩⟩
  change (p ≫ (k ≫ i.hom).hom.hom) ≫ D.contracting.inclusion.hom.hom = _
  have eq' := congrArg (fun v : U.group ⟶ J.val => v.hom.hom) eq
  change (k ≫ i.hom).hom.hom ≫ D.contracting.inclusion.hom.hom =
    U.inclusion.hom.hom ≫ P.inclusion.hom.hom at eq'
  rw [Category.assoc, eq']

set_option maxHeartbeats 120000 in
private theorem radicalPoint_mem_closedCommutator
    (hLevi : CocharacterLeviDecomposition.{u})
    [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (J : AffineAlgebraicGroup F)
    {P : ClosedSubgroup J.val} (hP : IsParabolic J P)
    {U : ClosedSubgroup P.group}
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U)
    (p : RationalPoints U.group.X) :
    letI := pointTopology J.val.X
    letI := rationalPointTopologicalGroup J
    (p ≫ U.inclusion.hom.hom ≫ P.inclusion.hom.hom : RationalPoints J.val.X) ∈
      (commutator (RationalPoints J.val.X)).topologicalClosure := by
  letI := pointTopology J.val.X
  letI := rationalPointTopologicalGroup J
  obtain ⟨π, hπ⟩ := exists_unit_powers_tendsto_zero (F := F)
  obtain ⟨c, hc⟩ := radical_hasLimit hLevi J hP hU p
  let g : RationalPoints J.val.X := p ≫ U.inclusion.hom.hom ≫ P.inclusion.hom.hom
  let a (n : ℕ) : RationalPoints J.val.X := cocharacterPoint c (CommAlgCat.of F F) (π ^ n)
  have hlim : Tendsto (fun n => a n * g * (a n)⁻¹) atTop (𝓝 1) :=
    tendsto_conjugation_of_hasLimit c hc (fun n => π ^ n)
      (by simpa only [Units.val_pow_eq_pow_val] using hπ)
  exact mem_closedCommutator_of_contraction (g := g) a hlim

end RationalPoints

section CocharacterPowers

variable {F : Type u} [Field F]

private theorem cocharacterPoint_pow {G : GroupScheme F} (c : Cocharacter G)
    (π : Fˣ) (n : ℕ) :
    (cocharacterPoint c (CommAlgCat.of F F) (π ^ n) : RationalPoints G.X) =
      (cocharacterPoint c (CommAlgCat.of F F) π : RationalPoints G.X) ^ n := by
  let R := CommAlgCat.of F F
  let f := (((groupPointsFunctor F).map c).app R).hom.comp (unitPointHom R)
  change f (π ^ n) = f π ^ n
  exact map_pow f π n

private theorem opposite_point_inv {G : GroupScheme F} (c : Cocharacter G)
    (π : Fˣ) :
    (cocharacterPoint (oppositeCocharacter c) (CommAlgCat.of F F) π : RationalPoints G.X) =
      (cocharacterPoint c (CommAlgCat.of F F) π : RationalPoints G.X)⁻¹ := by
  let R := CommAlgCat.of F F
  rw [opposite_point c R π]
  let f := (((groupPointsFunctor F).map c).app R).hom.comp (unitPointHom R)
  change f π⁻¹ = (f π)⁻¹
  exact map_inv f π

/-- Powers of a cocharacter value realize the limit along powers of a small unit. -/
theorem tendsto_conj_pow_of_hasLimit [TopologicalSpace F] [IsTopologicalRing F]
    {G : GroupScheme F} (c : Cocharacter G)
    {g z : RationalPoints G.X} (h : HasLimit c g z)
    (π : Fˣ) (hπ : Tendsto (fun n : ℕ => (π : F) ^ n) atTop (𝓝 0)) :
    letI := pointTopology G.X
    let a : RationalPoints G.X := cocharacterPoint c (CommAlgCat.of F F) π
    Tendsto (fun n : ℕ => a ^ n * g * (a ^ n)⁻¹) atTop (𝓝 z) := by
  letI := pointTopology G.X
  have hlim := tendsto_conjugation_of_hasLimit c h (fun n : ℕ => π ^ n)
    (by simpa only [Units.val_pow_eq_pow_val] using hπ)
  refine hlim.congr ?_
  intro n
  exact congrArg (fun x : RationalPoints G.X => x * g * x⁻¹) (cocharacterPoint_pow c π n)

/-- A point of both opposite limit parabolics commutes with the cocharacter. -/
theorem centralizes_of_opposite_extensions {J : AffineAlgebraicGroup F}
    (c : Cocharacter J.val) (E : LimitDecomposition (oppositeCocharacter c))
    {g : RationalPoints J.val.X} (h : HasExtension c g)
    (hneg : HasExtension (oppositeCocharacter c) g) : Centralizes c g := by
  let R := CommAlgCat.of F F
  obtain ⟨p, hp⟩ := (E.parabolic_points R g).mp hneg
  let z : RationalPoints J.val.X := p ≫ E.limit.hom.hom ≫ E.centralizer.inclusion.hom.hom
  have hzc' : Centralizes (oppositeCocharacter c) z :=
    (E.centralizer_points _ z).mpr ⟨p ≫ E.limit.hom.hom, Category.assoc _ _ _⟩
  have hzc : Centralizes c z := (centralizes_opposite_iff c z).mp hzc'
  have hlim : HasLimit (oppositeCocharacter c) g z := by
    have hh := E.limit_points R p
    change HasLimit (oppositeCocharacter c) _ z at hh
    rwa [hp] at hh
  obtain ⟨z₀, hz₀⟩ := h
  have hplus := hz₀.mul (centralizes_hasLimit c hzc).inv
  have hminus : HasLimit (oppositeCocharacter c) (g * z⁻¹) (1 : RationalPoints J.val.X) :=
    (mul_inv_cancel z) ▸ (hlim.mul (centralizes_hasLimit (oppositeCocharacter c) hzc').inv)
  have he := oppositeLimit_intersection_onPoints J.property.1 c (g * z⁻¹)
    ⟨_, hplus⟩ hminus
  have hg : g = z := mul_inv_eq_one.mp he
  simpa only [hg] using hzc

end CocharacterPowers

section OppositeRadicals

variable {F : Type u} [Field F]

private noncomputable abbrev rationalSubgroup {G : GroupScheme F} (P : ClosedSubgroup G) :
    Subgroup (RationalPoints G.X) :=
  (((groupPointsFunctor F).map P.inclusion).app (CommAlgCat.of F F)).hom.range

set_option backward.isDefEq.respectTransparency false in
private theorem rationalSubgroup_map (J : AffineAlgebraicGroup F) (P : ClosedSubgroup J.val) :
    (SubgroupSections P (𝟙_ (SchemeOver F))).map (rationalSectionEquiv J).toMonoidHom =
      rationalSubgroup P :=
  terminalSubgroup_map P

private theorem contract_radical [TopologicalSpace F] [IsTopologicalRing F]
    {J : AffineAlgebraicGroup F} {c : Cocharacter J.val} (D : LimitDecomposition c)
    (π : Fˣ) (hπ : Tendsto (fun n : ℕ => (π : F) ^ n) atTop (𝓝 0))
    {g : RationalPoints J.val.X} (hg : g ∈ rationalSubgroup D.contracting) :
    letI := pointTopology J.val.X
    let a : RationalPoints J.val.X := cocharacterPoint c (CommAlgCat.of F F) π
    Tendsto (fun n : ℕ => a ^ n * g * (a ^ n)⁻¹) atTop (𝓝 1) :=
  tendsto_conj_pow_of_hasLimit c ((D.contracting_points _ _).mpr hg) π hπ

/-- A closed normal subgroup containing the value at a small unit of a
noncentral cocharacter contains both of its contracting radicals. -/
theorem eq_top_of_cocharacterPoint_mem
    [TopologicalSpace F] [IsTopologicalRing F] [Infinite F]
    (J : AffineAlgebraicGroup F) (hJ : IsAbsolutelyAlmostSimple J) (hdense : HasDenseRadicals J)
    (c : Cocharacter J.val) (hc : IsNoncentral c)
    (π : Fˣ) (hπ : Tendsto (fun n : ℕ => (π : F) ^ n) atTop (𝓝 0))
    (N : Subgroup (RationalPoints J.val.X)) [N.Normal] :
    letI := pointTopology J.val.X
    IsClosed (N : Set (RationalPoints J.val.X)) →
    cocharacterPoint c (CommAlgCat.of F F) π ∈ N → N = ⊤ := by
  letI := pointTopology J.val.X
  letI := rationalPointTopologicalGroup J
  intro hN ha
  obtain ⟨D⟩ := existsLimitDecomposition J c
  obtain ⟨E⟩ := existsLimitDecomposition J (oppositeCocharacter c)
  have hpos : rationalSubgroup D.contracting ≤ N :=
    fun _g hg => mem_of_conj_pow_tendsto_one hN ha (contract_radical D π hπ hg)
  have hb : cocharacterPoint (oppositeCocharacter c) (CommAlgCat.of F F) π ∈ N := by
    rw [opposite_point_inv]
    exact N.inv_mem ha
  have hneg : rationalSubgroup E.contracting ≤ N :=
    fun _g hg => mem_of_conj_pow_tendsto_one hN hb (contract_radical E π hπ hg)
  apply eq_top_of_dense_radicals J hdense N hN
  rw [← RelativeRayGeneration.twoRadicalsGenerate J hJ c hc D E]
  apply Subgroup.map_le_iff_le_comap.mp
  rw [Subgroup.map_sup, rationalSubgroup_map, rationalSubgroup_map]
  exact sup_le hpos hneg

end OppositeRadicals

section Density

variable {F : Type u} [Field F]

private theorem localField_of_nonarchimedean
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    Specs.QuasiSplitLocalGeneration.IsLocalField F :=
  Or.inl ⟨inferInstance, inferInstance, inferInstance⟩

private theorem infinite_of_nonarchimedean
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] : Infinite F :=
  QuasiSplitLocalGeneration.infiniteOfIsLocalField F localField_of_nonarchimedean

theorem hasDenseRadicals_of_quasiSplit
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (J : AffineAlgebraicGroup F) (hJ : IsAbsolutelyAlmostSimple J)
    (hsc : GeometricallySimplyConnected J) (h : IsQuasiSplit J) :
    HasDenseRadicals J :=
  hasDenseRadicals_of_unipotentGenerated_eq_top J
    (QuasiSplitRadicalGeneration.quasiSplitRadicalGeneration
      localField_of_nonarchimedean J hJ.1 hsc h)

theorem hasDenseRadicals_of_split
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (J : AffineAlgebraicGroup F) (hJ : IsAbsolutelyAlmostSimple J)
    (hsc : GeometricallySimplyConnected J) (h : IsSplitReductive J) :
    HasDenseRadicals J := by
  obtain ⟨hred, T, hs, hm⟩ := h
  obtain ⟨c, hc⟩ := exists_regular_cocharacter J T hs
  obtain ⟨D⟩ := existsLimitDecomposition J (c ≫ T.inclusion)
  have hb := (RootData.BorelsAndChambers.regularCocharacterBorel J hred T hs hm c hc D).2.1
  exact hasDenseRadicals_of_quasiSplit J hJ hsc ⟨hred, D.parabolic, hb⟩

theorem hasDenseRadicals_of_isotropicSpecialUnitary
    [TopologicalSpace F] [Infinite F]
    (J : AffineAlgebraicGroup F) (h : IsIsotropicSpecialUnitary J) :
    HasDenseRadicals J := by
  obtain ⟨E, hField, hAlg, hQuad, hSep, n, H, hH, hIso, hRep⟩ := h
  letI := hField
  letI := hAlg
  letI := hQuad
  letI := hSep
  exact hasDenseRadicals_of_unipotentGenerated_eq_top J
    (IsotropicOuterTypeA.hermitianLocalGeneration H hH hIso J hRep)

set_option backward.isDefEq.respectTransparency false in
theorem hasDenseRadicals_of_isotropicQuadraticSpin
    [TopologicalSpace F] [Infinite F]
    (J : AffineAlgebraicGroup F) (hJ : IsAbsolutelyAlmostSimple J)
    (h : IsIsotropicQuadraticSpin J) : HasDenseRadicals J := by
  obtain ⟨V, hAdd, hModule, hDim, q, ρ, _, hReg, hIso, hRep⟩ := h
  letI := hAdd
  letI := hModule
  letI := hDim
  obtain ⟨x, hx, hqx⟩ := hIso
  obtain ⟨p, _⟩ := IsotropicSpinGeneration.hyperbolicPairExistence q hReg x hx hqx
  let b := (Module.finBasis F V).reindex
    (Equiv.ulift.symm : Fin (Module.finrank F V) ≃ ULift.{u} (Fin (Module.finrank F V)))
  obtain ⟨c, _, _, _, hGen⟩ := IsotropicSpinGeneration.localSpinGeneration q b J ρ hRep hReg hJ p
  obtain ⟨D⟩ := existsLimitDecomposition J c
  obtain ⟨E⟩ := existsLimitDecomposition J (oppositeCocharacter c)
  have hle := RelativeRayGeneration.twoRadicals_le_unipotentGenerated
    (reductive_of_semisimple J hJ.1) D E
  rw [(hGen D E).2.2] at hle
  exact hasDenseRadicals_of_unipotentGenerated_eq_top J (top_le_iff.mp hle)


end Density

section QuaternionicDensity

set_option backward.isDefEq.respectTransparency false

section MatrixPoints

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable (J : AffineAlgebraicGroup F)

set_option maxHeartbeats 300000 in
private theorem continuous_from_matrixPoints (i : MatrixRealization J) :
    letI := pointTopology J.val.X
    Continuous (fun p : PointsIn i F => (show RationalPoints J.val.X from p)) := by
  letI := pointTopology J.val.X
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr J.prop.1
  obtain ⟨a, ha, hm⟩ := matrixPresentation A.unop e i
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro b
  let b₀ : A.unop := (e.hom.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A.unop)).hom).hom b
  obtain ⟨x, hx⟩ := ha b₀
  have he (p : PointsIn i F) :
      LocalAlgebraicTransport.evaluation (show RationalPoints J.val.X from p) b =
        glEvaluation (asMatrix i F p) x := by
    let q := coordinateMap ((show RationalPoints J.val.X from p) ≫ e.inv)
    have hp : (testSpec F).map q.op ≫ e.hom = (show RationalPoints J.val.X from p) := by
      rw [coordinateMap_spec, Category.assoc, e.inv_hom_id, Category.comp_id]
    have hEval : LocalAlgebraicTransport.evaluation (show RationalPoints J.val.X from p) b =
        q.hom b₀ := by
      rw [← hp]
      change (((Spec.map (CommRingCat.ofHom q.hom.toRingHom) ≫ e.hom.left).appTop) ≫
        (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom b = _
      rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
      rfl
    have h := DFunLike.congr_fun (hm F p) x
    change glEvaluation (asMatrix i F p) x = q.hom (a.hom x) at h
    rw [hx] at h
    exact hEval.trans h.symm
  change Continuous (fun p : PointsIn i F =>
    LocalAlgebraicTransport.evaluation (show RationalPoints J.val.X from p) b)
  simp only [he]
  exact (continuous_glEvaluation x).comp continuous_induced_dom

private theorem hasDenseRadicals_of_matrix_dense (i : MatrixRealization J)
    (H : Subgroup (RationalPoints J.val.X))
    (hle : H ≤ (unipotentGenerated J).map (terminalPointHom J.val))
    (hd : Dense {g : PointsIn i F | (show RationalPoints J.val.X from g) ∈ H}) :
    HasDenseRadicals J := by
  letI := pointTopology J.val.X
  let f : PointsIn i F → RationalPoints J.val.X := fun p => p
  have hf : Function.Surjective f := fun p => ⟨p, rfl⟩
  have h := hf.denseRange.dense_image (continuous_from_matrixPoints J i) hd
  refine h.mono ?_
  rintro p ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hxy⟩ := hle hy
  refine ⟨x, hx, ?_⟩
  have heq : toUnit ((testSpec F).obj (.op (CommAlgCat.of F F))) =
      (groundPointIso F).inv := (isTerminalTensorUnit (C := SchemeOver F)).hom_ext _ _
  rw [heq]
  exact hxy

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem contractingPoints_sup_le (hJ : IsAbsolutelyAlmostSimple J)
    {c : Cocharacter J.val} (U : LimitDecomposition c) (V : LimitDecomposition (oppositeCocharacter c)) :
    SubgroupSections U.contracting ((testSpec F).obj (.op (CommAlgCat.of F F))) ⊔
      SubgroupSections V.contracting ((testSpec F).obj (.op (CommAlgCat.of F F))) ≤
      (unipotentGenerated J).map (terminalPointHom J.val) := by
  have hle := Subgroup.map_mono (f := terminalPointHom J.val)
    (RelativeRayGeneration.twoRadicals_le_unipotentGenerated
      (reductive_of_semisimple J hJ.1) U V)
  rw [Subgroup.map_sup, terminalSubgroup_map, terminalSubgroup_map] at hle
  exact hle

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem oppositeWords_le (hJ : IsAbsolutelyAlmostSimple J) (c : Cocharacter J.val) :
    Specs.Arithmetic.QuaternionSpinCharacteristicTwo.oppositeWords c ≤
      (unipotentGenerated J).map (terminalPointHom J.val) := by
  obtain ⟨U⟩ := existsLimitDecomposition J c
  obtain ⟨V⟩ := existsLimitDecomposition J (oppositeCocharacter c)
  rw [Specs.Arithmetic.QuaternionSpinCharacteristicTwo.oppositeWords, Subgroup.closure_le]
  intro g hg
  apply contractingPoints_sup_le J hJ U V
  rcases hg with h | h
  · exact Subgroup.mem_sup_left ((U.contracting_points _ _).mp h)
  · exact Subgroup.mem_sup_right ((V.contracting_points _ _).mp h)

end MatrixPoints

set_option maxHeartbeats 400000 in
theorem hasDenseRadicals_of_isotropicQuaternionicSpin
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (J : AffineAlgebraicGroup F) (hJ : IsAbsolutelyAlmostSimple J)
    (h : IsIsotropicQuaternionicSpin J) : HasDenseRadicals J := by
  obtain ⟨K, I, B, hK, hAlg, hFin, hGal, hI, hDec, hDiv, hBA, ρ, D, hB, d,
    hcard, hdeg, hd, ⟨M⟩, ⟨Q⟩⟩ := h
  letI := hK
  letI := hAlg
  letI := hFin
  letI := hGal
  letI := hI
  letI := hDec
  letI := hDiv
  letI := hBA
  obtain ⟨n, L, ⟨e⟩, f, hf⟩ := LinearAlgebraicGroups.faithfulLinearization F J
  let i : MatrixRealization J := ⟨n, L, e, f, hf⟩
  by_cases h2 : (2 : F) = 0
  · have hchar : ringChar F = 2 :=
      ((Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd (show ((2 : ℕ) : F) = 0 from h2))).resolve_left
        CharP.ringChar_ne_one
    letI : CharP F 2 := ringChar.of_eq hchar
    obtain ⟨W, c, _, _, _, _, _, _, hD⟩ :=
      QuaternionSpinCharacteristicTwo.quaternionLocalGeneration M hcard hB hdeg Q i
    exact hasDenseRadicals_of_matrix_dense J i _ (oppositeWords_le J hJ c) (dense_iff_closure_eq.mpr hD)
  · obtain ⟨c, lifts, _, _, _, _, ⟨⟨U⟩, ⟨V⟩⟩, h⟩ :=
      QuaternionSpinOddCharacteristic.localGeneration.1 M hJ hcard h2 hB hdeg d (hd h2) Q
    exact hasDenseRadicals_of_matrix_dense J i _ (contractingPoints_sup_le J hJ U V)
      (h U V i).2.2

end QuaternionicDensity

/-- Each of the original local cases has dense parabolic radical generation. -/
theorem hasDenseRadicals_of_mixingCases
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (hGeneration : Specs.ExceptionalLocalRadicalGeneration.LocalRadicalGeneration.{u})
    (J : AffineAlgebraicGroup F) (hJ : IsAbsolutelyAlmostSimple J)
    (h : MixingCases J) : HasDenseRadicals J := by
  letI : Infinite F := infinite_of_nonarchimedean
  rcases h with hsplit | hunit | hspin | hquat | ⟨hsc, hcase⟩
  · exact hasDenseRadicals_of_split J hJ hsplit.2 hsplit.1
  · exact hasDenseRadicals_of_isotropicSpecialUnitary J hunit
  · exact hasDenseRadicals_of_isotropicQuadraticSpin J hJ hspin
  · exact hasDenseRadicals_of_isotropicQuaternionicSpin J hJ hquat
  · rcases hcase with hexc | htrial | hextra
    · exact hasDenseRadicals_of_exceptional_case hGeneration J hJ hsc hexc
    · exact hasDenseRadicals_of_quasiSplit J hJ hsc htrial.2
    · exact hextra.1

set_option backward.isDefEq.respectTransparency false in
private theorem eq_top_of_closed_normal_not_le_center
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (J : AffineAlgebraicGroup F) (hJ : IsAbsolutelyAlmostSimple J) (hdense : HasDenseRadicals J)
    (N : Subgroup (RationalPoints J.val.X)) [N.Normal] :
    letI := pointTopology J.val.X
    IsClosed (N : Set (RationalPoints J.val.X)) → ¬ N ≤ Subgroup.center (RationalPoints J.val.X) →
      N = ⊤ := by
  letI := pointTopology J.val.X
  letI := rationalPointTopologicalGroup J
  letI := rationalPoints_t2Space J
  letI : Infinite F := infinite_of_nonarchimedean
  intro hN hnoncentral
  obtain ⟨g, _, hg⟩ := IsConcreteLE.not_le_iff_exists.mp hnoncentral
  have hg₁ : g ≠ 1 := fun h => hg (h.symm ▸ (Subgroup.center _).one_mem)
  have hred := reductive_of_semisimple J hJ.1
  obtain ⟨S, c, D, hS, hc, hmin, hproper, hnc⟩ :=
    LocalMinimalParabolicDynamics.existsProperMinimalParabolic F J hred ⟨g, hg₁⟩ hdense
  obtain ⟨π, hπ⟩ := exists_unit_powers_tendsto_zero (F := F)
  let R := CommAlgCat.of F F
  let B : Subgroup (RationalPoints J.val.X) := SubgroupSections D.parabolic ((testSpec F).obj (op R))
  let a : RationalPoints J.val.X := cocharacterPoint (c ≫ S.inclusion) R π
  by_cases hNB : N ≤ B
  · let C := Subgroup.centralizer (N : Set (RationalPoints J.val.X))
    letI : C.Normal := Subgroup.normal_centralizer
    have hC : IsClosed (C : Set (RationalPoints J.val.X)) := Set.isClosed_centralizer _
    have ha : a ∈ C := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro x hx
      have h := LocalMinimalParabolicDynamics.normalSubgroupCentralizesCocharacter
        J hred S c D hS hc hmin hproper hnc N hNB x hx
      have hx' := (centralizes_onAlgebras (c ≫ S.inclusion) (R := R) x).mp h R (𝟙 R) π
      have hxid : mapPoints (𝟙 R) x = x := by simp [mapPoints]
      rw [hxid] at hx'
      exact hx'.eq
    have htop := eq_top_of_cocharacterPoint_mem J hJ hdense (c ≫ S.inclusion) hnc π hπ C hC ha
    exact (hnoncentral (Subgroup.centralizer_eq_top_iff_subset.mp htop)).elim
  · obtain ⟨b, p, z, d, hq, _, hlim, hz, hd, hcomm, htorus⟩ :=
      LocalBruhatTorusCommutator.bruhatTorusCommutator F J hred S hS c hc D N
        (IsConcreteLE.not_le_iff_exists.mp hNB)
    have hza : Commute z a := by
      have h := (centralizes_iff S.inclusion z).mp hz _ (𝟙 _) (cocharacterPoint c R π)
      change Commute z (cocharacterPoint (c ≫ S.inclusion) R π)
      rw [cocharacterPoint_postcompose]
      simpa only [Category.id_comp] using h
    have heq : ⁅a, b⁆ = (cocharacterPoint (d ≫ S.inclusion) R π : RationalPoints J.val.X) := hcomm π
    have hab : Commute a ⁅a, b⁆ := heq.symm ▸ htorus π π
    have hmem : ⁅a, b⁆ ∈ N :=
      commutator_mem_of_conj_pow_tendsto hN hq (Commute.refl a) hza.symm hab
        (tendsto_conj_pow_of_hasLimit (c ≫ S.inclusion) hlim π hπ)
    exact eq_top_of_cocharacterPoint_mem J hJ hdense (d ≫ S.inclusion) hd π hπ N hN (heq ▸ hmem)

/-- The closed normal closure of a noncentral point in the specified local groups. -/
theorem localNormalClosure_conditional
    (_hRootSystems : Specs.ExceptionalLocalRadicalGeneration.ExceptionalRootSystemsAndLevis.{u})
    (hGeneration : Specs.ExceptionalLocalRadicalGeneration.LocalRadicalGeneration.{u})
    (_hRescale : Specs.Arithmetic.LocalRescaling.Statement.{u}) :
    LocalNormalClosure.{u} := by
  intro F _ _ _ _ J hJ hCases
  letI := pointTopology J.val.X
  letI := rationalPointTopologicalGroup J
  intro g hg
  let N := closedNormalClosure ({g} : Set (RationalPoints J.val.X))
  letI : N.Normal := Subgroup.is_normal_topologicalClosure _
  have hgN : g ∈ N :=
    Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (Set.mem_singleton g))
  have htop : N = ⊤ :=
    eq_top_of_closed_normal_not_le_center J hJ (hasDenseRadicals_of_mixingCases hGeneration J hJ hCases)
      N (Subgroup.isClosed_topologicalClosure _) (fun h => hg (h hgN))
  exact congrArg (fun H : Subgroup (RationalPoints J.val.X) => (H : Set (RationalPoints J.val.X))) htop

/-- The rescaling theorem reduces the finite-covolume assertion to normal
generation by noncentral elements, with the original topology and measure. -/
theorem finiteCovolumeSubgroup_of_normalClosure
    (hNormal : LocalNormalClosure.{u})
    (hRescale : Specs.Arithmetic.LocalRescaling.Statement.{u}) :
    FiniteCovolumeSubgroup.{u} := by
  intro F _ _ _ _ J hJ hCases
  letI := pointTopology J.val.X
  intro H hH hnondiscrete ν _ hν₀ hν
  letI := rationalPointTopologicalGroup J
  obtain ⟨x, g, hg, hclass⟩ :=
    hRescale F J hJ hCases H hH hnondiscrete ν hν₀ hν
  exact eq_top_of_conjugated_class hH (hNormal F J hJ hCases g hg) hclass

/-- The original finite-covolume conclusion follows by rescaling and normal generation. -/
theorem localProjectedClosure_conditional
    (hRootSystems : Specs.ExceptionalLocalRadicalGeneration.ExceptionalRootSystemsAndLevis.{u})
    (hGeneration : Specs.ExceptionalLocalRadicalGeneration.LocalRadicalGeneration.{u})
    (hRescale : Specs.Arithmetic.LocalRescaling.Statement.{u}) :
    FiniteCovolumeSubgroup.{u} :=
  finiteCovolumeSubgroup_of_normalClosure
    (localNormalClosure_conditional hRootSystems hGeneration hRescale) hRescale

end LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure

universe v8_closure_e0f615ab7920c4e6_u0
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«LocalProjectedClosure».«localNormalClosure» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«LocalProjectedClosure».«LocalNormalClosure».{v8_closure_e0f615ab7920c4e6_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalProjectedClosure».«localNormalClosure_conditional».{v8_closure_e0f615ab7920c4e6_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalLocalRadicalGeneration».«exceptionalRootSystemsAndLevis».{v8_closure_e0f615ab7920c4e6_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalLocalRadicalGeneration».«localRadicalGeneration».{v8_closure_e0f615ab7920c4e6_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalRescaling».«localRescaling».{v8_closure_e0f615ab7920c4e6_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«LocalProjectedClosure».«localProjectedClosure» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«LocalProjectedClosure».«FiniteCovolumeSubgroup».{v8_closure_e0f615ab7920c4e6_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalProjectedClosure».«localProjectedClosure_conditional».{v8_closure_e0f615ab7920c4e6_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalLocalRadicalGeneration».«exceptionalRootSystemsAndLevis».{v8_closure_e0f615ab7920c4e6_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalLocalRadicalGeneration».«localRadicalGeneration».{v8_closure_e0f615ab7920c4e6_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalRescaling».«localRescaling».{v8_closure_e0f615ab7920c4e6_u0})

namespace LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure

section MaximalParabolics

open CategoryTheory.Limits
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme SubgroupSections)
open Specs.BorelProper (IsParabolic)
open Specs.Relative.MaximalSplitTori (IsMinimalParabolic)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.SimpleParabolicProduct (doubleCoset)
open Specs.Arithmetic.LocalProjectedClosure (MaximalParabolicCosetAction)
open LocalAlgebraicTransport (RationalPoints evaluation pointTopology)
open CocharacterDynamics (existsLimitDecomposition oppositeCocharacter multiplyFactors)

open private rationalSource dense_rationalSectionValues exists_rationalPointClosure
  factors_through_closed_of_range from LinearAlgebraicGroups.Relative.RationalDensity
open private parabolicCellOpen factorThroughOpen from
  LinearAlgebraicGroups.Relative.RationalFlagLifting
open private group_geometricallyIrreducible from
  LinearAlgebraicGroups.Reductive.CocharacterOpenCell
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private range_doubleOrbit comp_doubleOrbitMap from LinearAlgebraicGroups.Relative.RelativeBruhat
open private leftTranslation from LinearAlgebraicGroups.Flag.OpenCell
open private isIso_of_section from LinearAlgebraicGroups.Relative.RelativeChambers
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private extendSubgroup from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private normalizes_iff_sections from LinearAlgebraicGroups.RootData.BorelNormalizer
open private continuous_evaluation from LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport

private theorem faithful_primitive_action_on_cosets {G : Type*} [Group G] (P : Subgroup G)
    (hP : IsCoatom P) (hcore : P.normalCore = Subgroup.center G) :
    let Z := Subgroup.center G
    ∃ action : MulAction (G ⧸ Z) (G ⧸ P),
      letI := action
      (∀ (g : G) (x : G ⧸ P), (QuotientGroup.mk g : G ⧸ Z) • x = g • x) ∧
      FaithfulSMul (G ⧸ Z) (G ⧸ P) ∧ MulAction.IsPreprimitive (G ⧸ Z) (G ⧸ P) := by
  let Z := Subgroup.center G
  let X := G ⧸ P
  let q := QuotientGroup.mk' Z
  let ρ := MulAction.toPermHom G X
  have hker : Z = ρ.ker := hcore.symm.trans P.normalCore_eq_ker
  let σ := QuotientGroup.lift Z ρ hker.le
  let action : MulAction (G ⧸ Z) X := MulAction.compHom X σ
  letI := action
  have hsmul (g : G) (x : X) : q g • x = g • x := rfl
  refine ⟨action, hsmul, ?_, ?_⟩
  · have hinj := (QuotientGroup.injective_lift_iff Z ρ hker.le).mpr hker
    refine ⟨fun {a b} hab => hinj (Equiv.ext fun x => ?_)⟩
    exact hab x
  · letI : Nontrivial X := QuotientGroup.nontrivial_iff.mpr hP.ne_top
    haveI : MulAction.IsPreprimitive G X := by
      rw [← MulAction.isCoatom_stabilizer_iff_preprimitive G ((1 : G) : X),
        MulAction.stabilizer_quotient]
      exact hP
    let f : X →ₑ[q] X := ⟨id, fun g x => (hsmul g x).symm⟩
    exact MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id

noncomputable section

variable {F : Type u} [Field F]

private abbrev sectionValue {X : SchemeOver F}
    (p : rationalSource F ⟶ X) : X.left :=
  p.left (IsLocalRing.closedPoint F)

private theorem sectionValue_comp {X Y : SchemeOver F}
    (p : rationalSource F ⟶ X) (f : X ⟶ Y) :
    sectionValue (p ≫ f) = f.left (sectionValue p) := rfl

private theorem dense_sections_of_open_immersion {X Y : SchemeOver F}
    (f : X ⟶ Y) [IsOpenImmersion f.left]
    (hY : DenseRange (sectionValue (X := Y))) :
    DenseRange (sectionValue (X := X)) := by
  apply dense_iff_inter_open.mpr
  intro V hV hVne
  let E := f.left.isOpenEmbedding
  obtain ⟨p, ⟨x, hx, hxp⟩⟩ := hY.exists_mem_open (E.isOpenMap V hV) (hVne.image f.left)
  obtain ⟨y, hy⟩ := factorThroughOpen f p ⟨x, hxp⟩
  have hxy : sectionValue y = x := E.injective
    ((sectionValue_comp y f).symm.trans ((congrArg sectionValue hy).trans hxp.symm))
  exact ⟨x, hx, y, hxy⟩

/-- Projection from the open parabolic cell gives Zariski density of the rational points. -/
private theorem parabolic_sections_dense [Infinite F] (J : AffineAlgebraicGroup F)
    (P : ClosedSubgroup J.val) (hP : IsParabolic J P) :
    DenseRange (sectionValue (X := P.group.X)) := by
  letI : Smooth J.val.X.hom := hP.1.1
  obtain ⟨c, D, hPD, _, _⟩ := Relative.RationalCocharacter.rationalParabolic J P hP
  obtain ⟨E⟩ := existsLimitDecomposition J (oppositeCocharacter c)
  let V := E.contracting.group.X
  let m := multiplyFactors E.contracting.inclusion P.inclusion
  letI : IsOpenImmersion m.left := parabolicCellOpen J P D E hPD
  have hd := dense_rationalSectionValues (X := J.val.X) id
    (Relative.RationalDensity.reductiveRationalPointsDense F J hP.1)
  have hcell := dense_sections_of_open_immersion m hd
  let pr := snd V P.group.X
  have hpr : Function.Surjective pr.left := by
    intro y
    let s := lift (1 : P.group.X ⟶ V) (𝟙 P.group.X)
    exact ⟨s.left y, congrArg (fun f : P.group.X ⟶ P.group.X => f.left y)
      (lift_snd _ _)⟩
  refine (hpr.denseRange.dense_image pr.left.continuous hcell).mono ?_
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨x ≫ pr, sectionValue_comp x pr⟩

private theorem subgroup_inclusion_of_dense_sections {G H : GroupScheme F}
    (f : G ⟶ H) (C : ClosedSubgroup H) [IsReduced G.X.left]
    (hd : DenseRange (sectionValue (X := G.X)))
    (h : ∀ p : rationalSource F ⟶ G.X,
      p ≫ f.hom.hom ∈ SubgroupSections C (rationalSource F)) :
    ∃ i : G ⟶ C.group, i ≫ C.inclusion = f := by
  apply factors_through_closed_of_range f C
  letI := C.isClosedImmersion
  have hClosed := C.isClosedImmersion.isClosedEmbedding.isClosed_range.preimage
    f.hom.hom.left.continuous
  have hsubset : Set.range (sectionValue (X := G.X)) ⊆
      f.hom.hom.left ⁻¹' Set.range C.inclusion.hom.hom.left := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : rationalSource F ⟶ C.group.X,
        c ≫ C.inclusion.hom.hom = p ≫ f.hom.hom := h p
    change f.hom.hom.left (sectionValue p) ∈ Set.range C.inclusion.hom.hom.left
    exact ⟨sectionValue c, (sectionValue_comp c _).symm.trans
      ((congrArg sectionValue hc).trans (sectionValue_comp p _))⟩
  rintro _ ⟨x, rfl⟩
  exact closure_minimal hsubset hClosed (hd x)

private theorem exists_dense_cell {X I : Type*} [TopologicalSpace X] [IrreducibleSpace X]
    [Finite I] (A : I → Set X) (hA : Dense (⋃ i, A i)) :
    ∃ i, Dense (A i) := by
  classical
  letI := Fintype.ofFinite I
  let S := Finset.univ.image (fun i => closure (A i))
  have hclosed : ∀ s ∈ S, IsClosed s := by
    intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact isClosed_closure
  have hcover : (Set.univ : Set X) ⊆ ⋃₀ ↑S := by
    intro x _
    have hx : x ∈ ⋃ i, closure (A i) := by
      rw [← closure_iUnion_of_finite]
      exact hA x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_sUnion.mpr ⟨closure (A i),
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩
  obtain ⟨s, hs, huniv⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (IrreducibleSpace.isIrreducible_univ X) S hclosed hcover
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
  exact ⟨i, fun x => huniv (Set.mem_univ x)⟩

/-- A dense subgroup containing the minimal parabolic points contains an open Bruhat cell
on rational points, which suffices to recover every rational point by translation. -/
private theorem eq_top_of_dense_sections_and_minimal_parabolic (J : AffineAlgebraicGroup F)
    (B : ClosedSubgroup J.val) (hB : IsMinimalParabolic J B)
    (K : Subgroup (𝟙_ (SchemeOver F) ⟶ J.val.X))
    (hBK : SubgroupSections B (𝟙_ (SchemeOver F)) ≤ K)
    (hd : DenseRange (fun x : K => sectionValue x.val)) : K = ⊤ := by
  classical
  letI : GeometricallyConnected J.val.X.hom := hB.1.1.2.1
  letI : ConnectedSpace J.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := J.val.X.hom)
  letI : GeometricallyIrreducible J.val.X.hom := group_geometricallyIrreducible J
  letI : IrreducibleSpace J.val.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton J.val.X.hom
  obtain ⟨S, hS, hSB, _⟩ := Relative.RelativeWeylScheme.commonMaximalSplitTorus J hB.1.1 B B hB hB
  obtain ⟨D, _, _, _, hr, h⟩ := Relative.RelativeBruhat.relativeBruhat J hB.1.1 S B hS hB hSB
  choose n hn using hr
  obtain ⟨hall, _, O, hdisjoint⟩ := h n hn
  let W := D.splitImage.labels
  letI : Finite W := D.splitImage.finite
  let g (w : W) := n w ≫ D.normalizer.inclusion.hom.hom
  let cell (w : W) := Set.range (O w).inclusion.left
  have factor {w : W} {p : 𝟙_ (SchemeOver F) ⟶ J.val.X}
      (hp : p ∈ doubleCoset B (𝟙_ (SchemeOver F)) (g w)) :
      ∃ a b : 𝟙_ (SchemeOver F) ⟶ B.group.X,
        p = (a ≫ B.inclusion.hom.hom) * g w * (b ≫ B.inclusion.hom.hom) := by
    obtain ⟨_, hab, _, ⟨b, rfl⟩, rfl⟩ := Set.mem_mul.mp hp
    obtain ⟨_, ⟨a, rfl⟩, z, hz, rfl⟩ := Set.mem_mul.mp hab
    have he : z = g w := by
      have ht : toUnit (𝟙_ (SchemeOver F)) = 𝟙 _ := Subsingleton.elim _ _
      simpa only [Set.mem_singleton_iff, ht, Category.id_comp] using hz
    refine ⟨a, b, ?_⟩
    change (a ≫ B.inclusion.hom.hom) * z * (b ≫ B.inclusion.hom.hom) = _
    rw [he]
  have section_cell {w : W} {p : 𝟙_ (SchemeOver F) ⟶ J.val.X}
      (hp : p ∈ doubleCoset B (𝟙_ (SchemeOver F)) (g w)) : sectionValue p ∈ cell w := by
    obtain ⟨a, b, rfl⟩ := factor hp
    change _ ∈ Set.range (O w).inclusion.left
    rw [range_doubleOrbit]
    refine ⟨sectionValue (lift a b), ?_⟩
    have hf := comp_doubleOrbitMap B (g w) (lift a b)
    rw [lift_fst_assoc, lift_snd_assoc] at hf
    exact congrArg sectionValue hf
  have cell_cover (p : 𝟙_ (SchemeOver F) ⟶ J.val.X) :
      ∃ w : W, p ∈ doubleCoset B (𝟙_ (SchemeOver F)) (g w) :=
    Set.mem_iUnion.mp (hall.symm ▸ Set.mem_univ p)
  have selected {p : 𝟙_ (SchemeOver F) ⟶ J.val.X} {w : W}
      (hp : p ∈ K) (hcell : p ∈ doubleCoset B (𝟙_ (SchemeOver F)) (g w)) : g w ∈ K := by
    obtain ⟨a, b, rfl⟩ := factor hcell
    have ha : a ≫ B.inclusion.hom.hom ∈ K := hBK ⟨a, rfl⟩
    have hb : b ≫ B.inclusion.hom.hom ∈ K := hBK ⟨b, rfl⟩
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using
      K.mul_mem (K.inv_mem ha) (K.mul_mem hp (K.inv_mem hb))
  have hd' : Dense (⋃ w : {w : W // g w ∈ K}, cell w.val) := hd.mono (by
    rintro _ ⟨p, rfl⟩
    obtain ⟨w, hp⟩ := cell_cover p.val
    exact Set.mem_iUnion.mpr ⟨⟨w, selected p.property hp⟩, section_cell hp⟩)
  obtain ⟨⟨w, hw⟩, hdw⟩ := exists_dense_cell (fun w : {w : W // g w ∈ K} => cell w.val) hd'
  have hopen : IsOpen (cell w) := by
    letI : IsImmersion (O w).inclusion.left := (O w).immersion
    have ho := (O w).inclusion.left.isLocallyClosed_range.isOpen_coborder
    change IsOpen (coborder (cell w)) at ho
    have hs : Set.univ \ cell w = (cell w)ᶜ := by ext x; simp
    simpa only [coborder, hdw.closure_eq, hs, compl_compl] using ho
  have hmem {p : 𝟙_ (SchemeOver F) ⟶ J.val.X} (hp : sectionValue p ∈ cell w) : p ∈ K := by
    obtain ⟨v, hv⟩ := cell_cover p
    have hvw : v = w := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisjoint hne) (section_cell hv) hp
    subst v
    obtain ⟨a, b, rfl⟩ := factor hv
    exact K.mul_mem (K.mul_mem (hBK ⟨a, rfl⟩) hw) (hBK ⟨b, rfl⟩)
  refine eq_top_iff.mpr fun x _ => ?_
  let t := leftTranslation x
  have ht : Function.Surjective t.hom.left :=
    ((Over.forget _).mapIso t).schemeIsoToHomeo.surjective
  have hne : (t.hom.left ⁻¹' cell w).Nonempty :=
    hdw.nonempty.preimage ht
  obtain ⟨p, hp⟩ := hd.exists_mem_open (hopen.preimage t.hom.left.continuous) hne
  have hxp : p.val ≫ t.hom = x * p.val := by
    have he : toUnit (𝟙_ (SchemeOver F)) = 𝟙 _ := Subsingleton.elim _ _
    simp only [t, leftTranslation, MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id, he,
      Category.id_comp]
  have hprod : x * p.val ∈ K := by
    rw [← hxp]
    exact hmem hp
  simpa only [mul_inv_cancel_right] using K.mul_mem hprod (K.inv_mem p.property)

private theorem parabolic_of_contains_parabolic {J : AffineAlgebraicGroup F}
    {P C : ClosedSubgroup J.val} (hP : IsParabolic J P) (hC : Smooth C.group.X.hom)
    (hPC : IsSubgroupOf P C) : IsParabolic J C := by
  obtain ⟨hp, B, hB, hBP⟩ := hP.2.2
  let L := AlgebraicClosure F
  let C' := extendSubgroup L C
  have hPC' : IsSubgroupOf (Specs.GeometricRadicals.baseChangedSubgroup L P hp) C' := by
    obtain ⟨i, hi⟩ := hPC
    refine ⟨(groupBaseChange F L).map i, ?_⟩
    change (groupBaseChange F L).map i ≫ (groupBaseChange F L).map C.inclusion =
      (groupBaseChange F L).map P.inclusion
    rw [← Functor.map_comp, hi]
  exact ⟨hP.1, hC, C'.isClosedImmersion, B, hB, subgroupOf_trans hBP hPC'⟩

private theorem isCoatom_of_maximal_parabolic_sections [Infinite F] (J : AffineAlgebraicGroup F)
    (B P : ClosedSubgroup J.val) (hB : IsMinimalParabolic J B) (hP : IsParabolic J P)
    (hBP : IsSubgroupOf B P) (hproper : ¬ IsIso P.inclusion)
    (hmax : ∀ C : ClosedSubgroup J.val, IsParabolic J C → IsSubgroupOf P C →
      IsSubgroupOf C P ∨ IsIso C.inclusion) :
    IsCoatom (SubgroupSections P (rationalSource F)) := by
  have hdJ : DenseRange (sectionValue (X := J.val.X)) :=
    dense_rationalSectionValues id (Relative.RationalDensity.reductiveRationalPointsDense F J hP.1)
  letI : Smooth J.val.X.hom := hP.1.1
  letI : IsReduced J.val.X.left := isReduced_of_smooth_over_field J.val.X.hom
  refine SetLike.isCoatom_iff.mpr ⟨?_, fun K x hKP hxP hxK => ?_⟩
  · intro h
    obtain ⟨i, hi⟩ := subgroup_inclusion_of_dense_sections (𝟙 J.val) P hdJ (by simp [h])
    exact hproper (isIso_of_section P i hi)
  · obtain ⟨C, hC, _, p, hmem, hlift, hdC⟩ := exists_rationalPointClosure J K
    letI : Smooth P.group.X.hom := hP.2.1
    letI : IsReduced P.group.X.left := isReduced_of_smooth_over_field P.group.X.hom
    have hPC : IsSubgroupOf P C := by
      apply subgroup_inclusion_of_dense_sections P.inclusion C (parabolic_sections_dense J P hP)
      intro a
      have ha : a ≫ P.inclusion.hom.hom ∈ K := hKP ⟨a, rfl⟩
      obtain ⟨i, hi⟩ := hlift ⟨_, ha⟩
      exact ⟨p i, hi⟩
    rcases hmax C (parabolic_of_contains_parabolic hP hC hPC) hPC with hCP | hiso
    · obtain ⟨i, hi⟩ := hCP
      obtain ⟨a, ha⟩ := hlift ⟨x, hxK⟩
      exfalso
      apply hxP
      refine ⟨p a ≫ i.hom.hom, ?_⟩
      have hi' : i.hom.hom ≫ P.inclusion.hom.hom = C.inclusion.hom.hom :=
        congrArg (fun f : C.group ⟶ J.val => f.hom.hom) hi
      exact (Category.assoc ..).trans ((congrArg (p a ≫ ·) hi').trans ha)
    · letI : IsIso C.inclusion := hiso
      let e := ((Grp.forget (SchemeOver F)) ⋙ Over.forget _).mapIso (asIso C.inclusion)
      have hs : Function.Surjective C.inclusion.hom.hom.left := e.schemeIsoToHomeo.surjective
      have hdK : DenseRange (fun a : K => sectionValue a.val) := by
        refine (hs.denseRange.dense_image C.inclusion.hom.hom.left.continuous
          (dense_rationalSectionValues p hdC)).mono ?_
        rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨⟨p a ≫ C.inclusion.hom.hom, hmem a⟩, sectionValue_comp _ _⟩
      obtain ⟨i, hi⟩ := hBP
      apply eq_top_of_dense_sections_and_minimal_parabolic J B hB K _ hdK
      intro x hx
      obtain ⟨b, rfl⟩ :
          ∃ b : rationalSource F ⟶ B.group.X, b ≫ B.inclusion.hom.hom = x := hx
      have hi' : i.hom.hom ≫ P.inclusion.hom.hom = B.inclusion.hom.hom :=
        congrArg (fun f : B.group ⟶ J.val => f.hom.hom) hi
      exact hKP ⟨b ≫ i.hom.hom, (Category.assoc ..).trans (congrArg (b ≫ ·) hi')⟩

/-- Density extends commutation with rational points to the scheme, so the normalizer
identity puts the rational center in the parabolic. -/
private theorem center_le_parabolic_sections [Infinite F] (J : AffineAlgebraicGroup F)
    (P : ClosedSubgroup J.val) (hP : IsParabolic J P) :
    Subgroup.center (𝟙_ (SchemeOver F) ⟶ J.val.X) ≤ SubgroupSections P (𝟙_ (SchemeOver F)) := by
  intro z hz
  let X := J.val.X
  let a : X ⟶ X := toUnit X ≫ z
  let f := a * 𝟙 X
  let g := 𝟙 X * a
  have hz' (p : 𝟙_ (SchemeOver F) ⟶ X) : p ≫ f = p ≫ g := by
    have he : toUnit (𝟙_ (SchemeOver F)) = 𝟙 _ := Subsingleton.elim _ _
    simpa only [f, g, a, MonObj.comp_mul, comp_toUnit_assoc, he, Category.id_comp,
      Category.comp_id] using (Subgroup.mem_center_iff.mp hz p).symm
  letI : IsAffine X.left := J.property.1
  letI : Smooth X.hom := hP.1.1
  letI : IsReduced X.left := isReduced_of_smooth_over_field X.hom
  let j := equalizer.ι f g
  have hclosed : IsClosed (Set.range j.left) := j.left.isClosedEmbedding.isClosed_range
  have hX : DenseRange (sectionValue (X := X)) :=
    dense_rationalSectionValues id (Relative.RationalDensity.reductiveRationalPointsDense F J hP.1)
  have hj : DenseRange j.left := hX.mono (by
    rintro _ ⟨p, rfl⟩
    refine ⟨sectionValue (equalizer.lift p (hz' p)), ?_⟩
    exact congrArg sectionValue (equalizer.lift_ι p (hz' p)))
  letI : Surjective j.left := ⟨Set.range_eq_univ.mp (hclosed.closure_eq.symm.trans hj.closure_eq)⟩
  letI : IsIso j.left := isIso_of_isClosedImmersion_of_surjective j.left
  have hfg : f = g := by
    apply Over.OverMorphism.ext
    exact (cancel_epi j.left).mp (congrArg Over.Hom.left (equalizer.condition f g))
  apply (Flag.StandardParabolics.groundFieldParabolicNormalizer J P hP _ z).mp
  rw [normalizes_iff_sections]
  intro Y t p
  let b := p ≫ P.inclusion.hom.hom
  have hba : b ≫ a = t ≫ z := by
    change b ≫ toUnit X ≫ z = t ≫ z
    rw [← Category.assoc, show b ≫ toUnit X = t from isTerminalTensorUnit.hom_ext _ _]
  have hb : Commute (t ≫ z) b := by
    have he := congrArg (fun v : X ⟶ X => b ≫ v) hfg
    have hbid : b ≫ 𝟙 X = b := Category.comp_id b
    change (t ≫ z) * b = b * (t ≫ z)
    simpa only [f, g, MonObj.comp_mul, hba, hbid] using he
  refine ⟨⟨p, ?_⟩, ⟨p, ?_⟩⟩
  · change b = (t ≫ z) * b * (t ≫ z)⁻¹
    rw [hb.eq, mul_inv_cancel_right]
  · change b = (t ≫ z)⁻¹ * b * (t ≫ z)
    rw [hb.inv_left.eq, inv_mul_cancel_right]

private theorem isClosed_rational_subgroup [TopologicalSpace F] [T1Space F]
    (J : AffineAlgebraicGroup F) (P : ClosedSubgroup J.val) :
    letI := pointTopology J.val.X
    IsClosed (rationalSubgroup P : Set (RationalPoints J.val.X)) := by
  letI := pointTopology J.val.X
  letI : IsAffine J.val.X.left := J.property.1
  let j := P.inclusion.hom.hom
  letI : IsClosedImmersion j.left := P.isClosedImmersion
  let I := RingHom.ker j.left.appTop.hom
  letI : IsAffine ((testSpec F).obj (op (CommAlgCat.of F F))).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of F)))
  have hiff (p : RationalPoints J.val.X) : p ∈ rationalSubgroup P ↔
      ∀ a : I, evaluation p a.val = 0 := by
    have heval (a : Γ(J.val.X.left, ⊤)) : evaluation p a = 0 ↔ p.left.appTop.hom a = 0 :=
      map_eq_zero_iff ((Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).hom).1
    have hker : j.left.ker ≤ p.left.ker ↔ I ≤ RingHom.ker p.left.appTop.hom := by
      letI : IsAffineHom p.left := inferInstance
      let U : J.val.X.left.affineOpens := ⟨⊤, isAffineOpen_top _⟩
      change j.left.ker ≤ p.left.ker ↔ RingHom.ker (j.left.app U.1).hom ≤
        RingHom.ker (p.left.app U.1).hom
      rw [← j.left.ker_apply U, ← p.left.ker_apply U]
      exact ⟨fun h => h U, Scheme.IdealSheafData.le_of_isAffine⟩
    change (∃ q : RationalPoints P.group.X, q ≫ j = p) ↔ _
    constructor
    · rintro ⟨q, hq⟩ a
      have hq' : q.left ≫ j.left = p.left := congrArg Over.Hom.left hq
      have hk : j.left.ker ≤ p.left.ker := hq' ▸ (q.left.le_ker_comp j.left)
      exact (heval a).mpr (hker.mp hk a.property)
    · intro h
      have hk : j.left.ker ≤ p.left.ker := hker.mpr (fun a ha => (heval a).mp (h ⟨a, ha⟩))
      let q := IsClosedImmersion.lift j.left p.left hk
      have hq : q ≫ j.left = p.left := IsClosedImmersion.lift_fac _ _ _
      let q' : RationalPoints P.group.X := Over.homMk q (by
        rw [← Over.w j, ← Category.assoc, hq, Over.w p])
      exact ⟨q', Over.OverMorphism.ext hq⟩
  have heq : (rationalSubgroup P : Set (RationalPoints J.val.X)) =
      ⋂ a : I, (fun p : RationalPoints J.val.X => evaluation p a.val) ⁻¹' ({0} : Set F) := by
    ext p
    simpa only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] using hiff p
  rw [heq]
  exact isClosed_iInter fun a => isClosed_singleton.preimage (continuous_evaluation J.val.X a)

end

/-- On cosets of a maximal proper standard rational parabolic, the central quotient
acts faithfully and primitively. -/
theorem maximalParabolicCosetAction : MaximalParabolicCosetAction.{u} := by
  intro F _ _ _ _ J hJ hCase B P hB hP hBP hproper hmax
  letI : Infinite F := infinite_of_nonarchimedean
  letI := pointTopology J.val.X
  let P_F := rationalSubgroup P
  have hP_F : IsCoatom P_F := by
    change IsCoatom (rationalSubgroup P)
    rw [← rationalSubgroup_map J P]
    exact (OrderIso.isCoatom_iff (rationalSectionEquiv J).mapSubgroup
      (SubgroupSections P (𝟙_ (SchemeOver F)))).mpr
      (isCoatom_of_maximal_parabolic_sections J B P hB hP hBP hproper hmax)
  have hcent : Subgroup.center (RationalPoints J.val.X) ≤ P_F := by
    change Subgroup.center (RationalPoints J.val.X) ≤ rationalSubgroup P
    rw [← rationalSubgroup_map J P, ← Subgroup.map_center_eq (rationalSectionEquiv J)]
    exact Subgroup.map_mono (center_le_parabolic_sections J P hP)
  have hcore : P_F.normalCore = Subgroup.center (RationalPoints J.val.X) := by
    refine le_antisymm ?_ (Subgroup.normal_le_normalCore.mpr hcent)
    intro g hg
    by_contra h
    have hgen := localNormalClosure F J hJ hCase g h
    have hle : Subgroup.normalClosure ({g} : Set (RationalPoints J.val.X)) ≤ P_F.normalCore :=
      Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hg)
    have hclosed : IsClosed (P_F : Set (RationalPoints J.val.X)) := isClosed_rational_subgroup J P
    have hall := closure_minimal (hle.trans P_F.normalCore_le) hclosed
    rw [hgen] at hall
    exact hP_F.ne_top (eq_top_iff.mpr fun x _ => hall (Set.mem_univ x))
  exact ⟨hP_F, hcore, faithful_primitive_action_on_cosets P_F hP_F hcore⟩

end MaximalParabolics

end LinearAlgebraicGroups.Arithmetic.LocalProjectedClosure
