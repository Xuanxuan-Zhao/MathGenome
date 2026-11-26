import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterWallGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalFoldedWeyl
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactRankOneLifts
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactWeylLabels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterFoldedWallTransport
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterTorus
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Module
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalOuterWallGroups

open AlgebraicGeometry CategoryTheory Topology
open scoped CategoryTheory.MonObj
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterPairing (characterValue)
open Specs.ExceptionalCompactInner (fixedSubgroup)
open Specs.ExceptionalFoldedWeyl
open Specs.ExceptionalOuterCompactRankOneLifts (MarkedTorus)
open Specs.ExceptionalOuterWallGroups (OuterWallCalculation)
open Specs.ExceptionalOuterTorus (MarkedPair complexTest fixedCompact identityComponent
  OuterInvolutions OuterTorusComparison IsMaximalCompactTorus)
open Specs.RootGroups (AdditiveLine rootPoint)

open private rootPoint_injective_of_mono from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private exp_add exp_sub exp_mem exists_exp torus_commutes fixed_torus_kernel
  mem_component_map conj_intertwine torus_subset_compact markedPointMap markedPointMap_apply
  simple_evaluation torus_conj_on_self
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactRankOneLifts
open private normalizes_compact_torus vectors_eq_of_exp_smul_eq weyl_smul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactWeylLabels

private theorem diagram_involutive : Function.Involutive e6Diagram := by
  intro v
  funext j
  change v (Specs.AbsoluteDynkinTypes.E6Reflection
    (Specs.AbsoluteDynkinTypes.E6Reflection j)) = v j
  have h : ∀ j : Fin 6, Specs.AbsoluteDynkinTypes.E6Reflection
      (Specs.AbsoluteDynkinTypes.E6Reflection j) = j := by decide
  rw [h]

private theorem diagram_sub (v w : E6Space) :
    e6Diagram (v - w) = e6Diagram v - e6Diagram w := rfl

private theorem diagram_smul (r : ℝ) (v : E6Space) :
    e6Diagram (r • v) = r • e6Diagram v := rfl

private theorem project_sub (v w : E6Space) : project (v - w) = project v - project w := by
  unfold project
  rw [diagram_sub]
  module

private theorem project_anti (v : E6Space) : project (v - e6Diagram v) = 0 := by
  unfold project
  rw [diagram_sub, diagram_involutive v]
  module

private theorem project_eq_zero_lift {v : E6Space} (h : project v = 0) :
    ∃ b : E6Space, v = b - e6Diagram b := by
  refine ⟨(1 / 2 : ℝ) • v, ?_⟩
  rw [diagram_smul]
  have h' : v + e6Diagram v = 0 := by
    change (1 / 2 : ℝ) • (v + e6Diagram v) = 0 at h
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  rw [eq_neg_of_add_eq_zero_right h']
  module

variable {G : Specs.AffineAlgebraicGroup ℝ} {i : Specs.IntegralModels.MatrixRealization G}
  {ω θ : MulAut (AdelicGroups.PointsIn i ℂ)} {S : Subgroup (AdelicGroups.PointsIn i ℂ)}
  (D : MarkedTorus ω θ S)

private theorem exp_eq_iff (y z : E6Space) :
    D.exp y = D.exp z ↔ y - z ∈ e6Lattice := by
  have h : D.exp (y - z) = 1 ↔ y - z ∈ e6Lattice := D.expKernel _
  rw [← h, exp_sub, mul_inv_eq_one]

/-- Every class in the quotient by the image of the diagram difference is
represented by a logarithm in the fixed space. -/
theorem projected_quotient_representative (projection : ProjectionCalculation) (t : D.T) :
    ∃ y ∈ foldedSpace, ∃ b : D.T, D.exp y = t.val * (b.val * (D.δ b.val)⁻¹) := by
  obtain ⟨v, hv⟩ := exists_exp D t.property
  let a := (1 / 4 : ℝ) • (e6Diagram v - v)
  refine ⟨project v, projection.1 v, ⟨D.exp a, exp_mem D a⟩, ?_⟩
  change D.exp (project v) = t.val * (D.exp a * (D.δ (D.exp a))⁻¹)
  rw [← hv, D.diagramExp, ← exp_sub, ← exp_add]
  apply congrArg D.exp
  dsimp only [a, project]
  rw [diagram_smul, diagram_sub, diagram_involutive]
  module

/-- Removing the anti-invariant part of the logarithm by torus conjugation. -/
theorem normalize_twist (projection : ProjectionCalculation) :
    ∃ (t₀ a : D.T) (x : E6Space), x ∈ foldedSpace ∧
      θ = MulAut.conj t₀.val * D.δ ∧
      D.exp x = a.val * t₀.val * (D.δ a.val)⁻¹ := by
  obtain ⟨t₀, hθ⟩ := D.twist
  obtain ⟨x, hx, a, ha⟩ := projected_quotient_representative D projection t₀
  rw [← mul_assoc, (torus_commutes D t₀.property a.property).eq] at ha
  exact ⟨t₀, a, x, hx, hθ, ha⟩

/-- The kernel lattice for the quotient by the image of the diagram difference. -/
theorem projected_quotient_iff (projection : ProjectionCalculation)
    {y z : E6Space} (hy : y ∈ foldedSpace) (hz : z ∈ foldedSpace) :
    (∃ b : D.T, D.exp y = D.exp z * (b.val * (D.δ b.val)⁻¹)) ↔
      y - z ∈ projectedLattice := by
  have hfixed : project (y - z) = y - z := by
    rw [project_sub, projection.2.1 y hy, projection.2.1 z hz]
  have hcriterion (v : E6Space) :
      D.exp y = D.exp z * (D.exp v * (D.δ (D.exp v))⁻¹) ↔
        (y - z) - (v - e6Diagram v) ∈ e6Lattice := by
    rw [D.diagramExp, ← exp_sub, ← exp_add, exp_eq_iff]
    have h : y - (z + (v - e6Diagram v)) = (y - z) - (v - e6Diagram v) := by
      module
    rw [h]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨v, hv⟩ := exists_exp D b.property
    rw [← hv] at hb
    refine ⟨(y - z) - (v - e6Diagram v), (hcriterion v).mp hb, ?_⟩
    rw [project_sub, hfixed, project_anti, sub_zero]
  · rintro ⟨l, hl, hp⟩
    obtain ⟨v, hv⟩ := project_eq_zero_lift (v := (y - z) - l) (by
      rw [project_sub, hfixed, hp, sub_self])
    refine ⟨⟨D.exp v, exp_mem D v⟩, (hcriterion v).mpr ?_⟩
    rwa [← hv, sub_sub_cancel]

/-- Package the point-group data supplied by the frozen compact torus comparison. -/
theorem exists_markedTorus (comparison : OuterTorusComparison)
    (hG : Specs.AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G)
    (hsc : Specs.SimplyConnectedLattice.GeometricallySimplyConnected G)
    (htype : Specs.ExceptionalCompactInner.HasExceptionalType G)
    (hωθ : OuterInvolutions (i := i) ω θ)
    (hS : IsMaximalCompactTorus (identityComponent (fixedCompact ω θ)) S) :
    Nonempty (MarkedTorus ω θ S) := by
  obtain ⟨T, A, M, d, δ, hcomponent, hcentral, hmax, hpoints, hstable, hpin, hcartan,
    hbasis, hroots, hvalue, hregular, hcontinuous, hadd, hrange, hkernel, hδpin, hδcoroot,
    hδaction, hδinv, hδcontinuous, hδcomm, hδexp, htwist, hfixed, hfixedExp⟩ :=
    comparison G i hG hsc htype ω θ hωθ S hS
  exact ⟨{
    T := T
    A := A
    M := M
    d := d
    δ := δ
    centralizer := hcentral
    centralizerComponent := hcomponent
    maximal := hmax
    stablePair := hstable
    compactPinning := hpin
    tori := hpoints
    cartan := hcartan
    corootBasis := hbasis
    rootCoordinates := hroots
    rootEvaluation := hvalue
    regularChamber := hregular
    continuousExp := hcontinuous
    expAdd := hadd
    expRange := hrange
    expKernel := hkernel
    diagramPin := hδpin
    diagramCoroot := hδcoroot
    diagramAction := hδaction
    diagramInvolutive := hδinv
    continuousDiagram := hδcontinuous
    diagramCommutes := hδcomm
    diagramExp := hδexp
    twist := htwist
    fixedTorus := hfixed
    fixedExp := hfixedExp
  }⟩

private theorem mem_identityComponent {H : Type*} [Group H] [TopologicalSpace H]
    (J : Subgroup H) {g : H} (hg : g ∈ identityComponent J) : g ∈ J := by
  obtain ⟨g', -, rfl⟩ := hg
  exact g'.property

private theorem mem_identityComponent_iff {H : Type*} [Group H] [TopologicalSpace H]
    (J : Subgroup H) (g : J) :
    g.val ∈ identityComponent J ↔ g ∈ connectedComponent (1 : J) := by
  constructor
  · rintro ⟨g', hg', heq⟩
    exact Subtype.ext heq ▸ hg'
  · exact fun hg => ⟨g, hg, rfl⟩

private theorem connected_identityComponent {H : Type*} [Group H] [TopologicalSpace H]
    (J : Subgroup H) (h : ∀ g ∈ J, g ∈ identityComponent J) : ConnectedSpace J := by
  refine connectedSpace_iff_connectedComponent.mpr ⟨1, Set.eq_univ_of_forall ?_⟩
  exact fun g => (mem_identityComponent_iff J g).mp (h _ g.property)

theorem normalize_intertwines {t₀ a : D.T} {x : E6Space}
    (hθ : θ = MulAut.conj t₀.val * D.δ)
    (hx : D.exp x = a.val * t₀.val * (D.δ a.val)⁻¹) :
    D.twisted x * MulAut.conj a.val = MulAut.conj a.val * θ := by
  calc
    D.twisted x * MulAut.conj a.val =
        MulAut.conj a.val * (MulAut.conj t₀.val * D.δ) := by
      rw [MarkedTorus.twisted, hx, mul_assoc, conj_intertwine, ← mul_assoc,
        ← map_mul, inv_mul_cancel_right, map_mul, mul_assoc]
    _ = MulAut.conj a.val * θ := congrArg (MulAut.conj a.val * ·) hθ.symm

private theorem fixedCompact_conj_iff {H : Type*} [Group H] {ω θ τ : MulAut H} {a : H}
    (ha : a ∈ fixedSubgroup ω)
    (ht : τ * MulAut.conj a = MulAut.conj a * θ) (g : H) :
    MulAut.conj a g ∈ fixedCompact ω τ ↔ g ∈ fixedCompact ω θ := by
  have hω : ω (MulAut.conj a g) = MulAut.conj a (ω g) := by
    have hh : ω * MulAut.conj a = MulAut.conj a * ω :=
      (conj_intertwine ω a).trans (congrArg (fun v => MulAut.conj v * ω) ha)
    exact DFunLike.congr_fun hh g
  have hθ : τ (MulAut.conj a g) = MulAut.conj a (θ g) := DFunLike.congr_fun ht g
  change (ω (MulAut.conj a g) = MulAut.conj a g ∧
    τ (MulAut.conj a g) = MulAut.conj a g) ↔ (ω g = g ∧ θ g = g)
  rw [hω, hθ, (MulAut.conj a).injective.eq_iff, (MulAut.conj a).injective.eq_iff]

private theorem fixedTorus_le : S ≤ D.T :=
  fun _ hg => (show _ ∈ D.T ⊓ fixedSubgroup D.δ from D.fixedTorus ▸ hg).1

private theorem torus_normalizes_fixedTorus {a : AdelicGroups.PointsIn i ℂ} (ha : a ∈ D.T) :
    a ∈ Subgroup.normalizer (S : Set _) := by
  apply Subgroup.centralizer_le_normalizer
  exact (show a ∈ fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set _) from
    D.centralizer ▸ ha).2

/-- The Weyl action on the marked compact torus has kernel exactly the fixed torus. -/
theorem represents_one_iff {x : E6Space} {n : AdelicGroups.PointsIn i ℂ}
    (hn : n ∈ D.fixedAt x) : D.RepresentsWeyl n 1 ↔ n ∈ S := by
  constructor
  · intro h
    have hT : n ∈ D.T := by
      rw [D.centralizer]
      refine ⟨hn.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro s hs
      obtain ⟨y, rfl⟩ := exists_exp D (fixedTorus_le D hs)
      exact ((mul_inv_eq_iff_eq_mul.mp (h y))).symm
    have hb : n ∈ D.T ⊓ D.fixedAt x := ⟨hT, hn⟩
    exact fixed_torus_kernel D x ▸ hb
  · intro h y
    change n * D.exp y * n⁻¹ = D.exp y
    rw [(torus_commutes D (fixedTorus_le D h) (exp_mem D y)).eq, mul_inv_cancel_right]

private theorem weyl_label_unique {n : AdelicGroups.PointsIn i ℂ} {w v : Function.End E6Space}
    (hw : w ∈ e6Weyl) (hv : v ∈ e6Weyl)
    (hnw : D.RepresentsWeyl n w) (hnv : D.RepresentsWeyl n v) : w = v := by
  funext y
  apply vectors_eq_of_exp_smul_eq D.exp D.expAdd D.expKernel
  intro r
  simpa only [weyl_smul hw, weyl_smul hv] using (hnw (r • y)).symm.trans (hnv (r • y))

/-- Conjugation in the marked torus transports the fixed-component representatives. -/
theorem normalized_component_representatives {t₀ a : D.T} {x : E6Space}
    (hθ : θ = MulAut.conj t₀.val * D.δ)
    (hx : D.exp x = a.val * t₀.val * (D.δ a.val)⁻¹)
    (representatives : ∀ g ∈ fixedCompact ω θ, ∃ n ∈ fixedCompact ω θ,
      n ∈ Subgroup.normalizer (S : Set _) ∧ g * n⁻¹ ∈ identityComponent (fixedCompact ω θ)) :
    ∀ g ∈ D.fixedAt x, ∃ n ∈ D.fixedAt x,
      n ∈ Subgroup.normalizer (S : Set _) ∧ g * n⁻¹ ∈ identityComponent (D.fixedAt x) := by
  let c := MulAut.conj a.val
  have hc (g) : c g ∈ D.fixedAt x ↔ g ∈ fixedCompact ω θ :=
    fixedCompact_conj_iff (torus_subset_compact D a.property) (normalize_intertwines D hθ hx) g
  intro g hg
  have hm : c.symm g ∈ fixedCompact ω θ := (hc _).1 (by simpa only [c.apply_symm_apply])
  obtain ⟨n, hn, hnS, hn0⟩ := representatives _ hm
  have haS := torus_normalizes_fixedTorus D a.property
  refine ⟨c n, (hc _).2 hn, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ haS hnS) (Subgroup.inv_mem _ haS)
  · have hp := mem_component_map c.toMonoidHom
      (IsTopologicalGroup.continuous_conj a.val) (fun u hu => (hc u).2 hu) hn0
    change c (c.symm g * n⁻¹) ∈ identityComponent (D.fixedAt x) at hp
    simpa only [map_mul, map_inv, c.apply_symm_apply] using hp

/-- Connectedness transfers back along the same torus conjugation. -/
theorem connected_original_of_normalized {t₀ a : D.T} {x : E6Space}
    (hθ : θ = MulAut.conj t₀.val * D.δ)
    (hx : D.exp x = a.val * t₀.val * (D.δ a.val)⁻¹)
    (h : ConnectedSpace (D.fixedAt x)) : ConnectedSpace (fixedCompact ω θ) := by
  let := h
  let c := MulAut.conj a.val
  have hc (g) : c g ∈ D.fixedAt x ↔ g ∈ fixedCompact ω θ :=
    fixedCompact_conj_iff (torus_subset_compact D a.property) (normalize_intertwines D hθ hx) g
  apply connected_identityComponent
  intro g hg
  have h0 : c g ∈ identityComponent (D.fixedAt x) := by
    refine ⟨⟨c g, (hc g).2 hg⟩, ?_, rfl⟩
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    trivial
  have hm (u) (hu : u ∈ D.fixedAt x) : c.symm u ∈ fixedCompact ω θ :=
    (hc _).1 (by simpa only [c.apply_symm_apply])
  have hcont : Continuous c.symm := by
    change Continuous (fun g => a.val⁻¹ * g * a.val)
    exact (continuous_const.mul continuous_id).mul continuous_const
  have hp := mem_component_map c.symm.toMonoidHom hcont hm h0
  change c.symm (c g) ∈ identityComponent (fixedCompact ω θ) at hp
  simpa only [c.symm_apply_apply] using hp

private theorem diagram_exp_fixed {x : E6Space} (hx : x ∈ foldedSpace) :
    D.δ (D.exp x) = D.exp x := D.diagramExp x |>.trans (congrArg D.exp hx)

theorem normalized_involutive {t₀ a : D.T} {x : E6Space}
    (hθ : θ = MulAut.conj t₀.val * D.δ)
    (hx : D.exp x = a.val * t₀.val * (D.δ a.val)⁻¹) (hinv : Function.Involutive θ) :
    Function.Involutive (D.twisted x) := by
  let c := MulAut.conj a.val
  have hh (g) : D.twisted x (c g) = c (θ g) :=
    DFunLike.congr_fun (normalize_intertwines D hθ hx) g
  intro g
  obtain ⟨u, rfl⟩ := c.surjective g
  rw [hh, hh, hinv]

private theorem involutive_twist_conj_eq_one {x : E6Space} (hx : x ∈ foldedSpace)
    (h : Function.Involutive (D.twisted x)) :
    MulAut.conj (D.exp ((2 : ℝ) • x)) = 1 := by
  have ht := diagram_exp_fixed D hx
  have hδ : D.δ * D.δ = 1 := by
    ext g
    exact D.diagramInvolutive g
  have hτ : D.twisted x * D.twisted x = 1 := by
    ext g
    exact h g
  calc
    MulAut.conj (D.exp ((2 : ℝ) • x)) = D.twisted x * D.twisted x := by
      rw [two_smul, exp_add, map_mul]
      symm
      unfold MarkedTorus.twisted
      rw [mul_assoc, ← mul_assoc D.δ, conj_intertwine, ht,
        mul_assoc (MulAut.conj (D.exp x)) D.δ D.δ, hδ, mul_one]
    _ = 1 := hτ

private theorem markedPointMap_injective {A : AdditiveLine ℂ} (M : MarkedPair G A) :
    Function.Injective (markedPointMap (i := i) M (𝟙 _)) := by
  intro p q hp
  have heq := (baseChangePointGroupEquiv ℂ G.val complexTest).injective hp
  change p ≫ (𝟙 _ ≫ M.comparison.hom).hom.hom =
    q ≫ (𝟙 _ ≫ M.comparison.hom).hom.hom at heq
  rw [Category.id_comp] at heq
  let : IsIso M.comparison.hom.hom.hom := inferInstance
  exact (cancel_mono M.comparison.hom.hom.hom).mp heq

private theorem simpleRootPoint_injective (j : Fin 6) :
    Function.Injective (rootPoint (D.M.simpleCoordinate j) complexTest) := by
  let U := (D.M.P.roots (D.M.simple j).val).val
  let e := (D.M.P.pin (D.M.simple j)).val
  have : IsClosedImmersion U.inclusion.hom.hom.left := U.isClosedImmersion
  have : Mono U.inclusion.hom.hom := Over.mono_of_mono_left _
  have : Mono (D.M.simpleCoordinate j).hom.hom := by
    change Mono (e.hom.hom.hom ≫ U.inclusion.hom.hom)
    infer_instance
  exact rootPoint_injective_of_mono _ complexTest

private theorem simple_character_one_of_conj_eq_one {y : E6Space}
    (h : MulAut.conj (D.exp y) = 1) (j : Fin 6) :
    characterValue (D.M.simple j).val.val complexTest (D.M.torusPoint y) = 1 := by
  let Q := D.M.P.pair.G.val
  let F := markedPointMap (i := i) D.M (𝟙 Q)
  let p := rootPoint (D.M.simpleCoordinate j) complexTest 1
  let t : GroupPoints Q complexTest := D.M.torusPoint y ≫ D.M.P.pair.T.inclusion.hom.hom
  have ht : F t = D.exp y := by
    change markedPointMap (i := i) D.M (𝟙 Q) t = D.exp y
    rw [markedPointMap_apply]
    unfold MarkedPair.onPoints
    rw [Category.id_comp]
    rfl
  have hs := (D.M.P.pin (D.M.simple j)).property complexTest (D.M.torusPoint y) 1
  change t * p * t⁻¹ =
    rootPoint (D.M.simpleCoordinate j) complexTest
      (characterValue (D.M.simple j).val.val complexTest (D.M.torusPoint y) * 1) at hs
  rw [mul_one] at hs
  apply simpleRootPoint_injective D j
  rw [← hs]
  apply markedPointMap_injective (i := i) D.M
  change F (t * p * t⁻¹) = F p
  rw [map_mul, map_mul, map_inv, ht]
  exact DFunLike.congr_fun h (F p)

/-- The normalized logarithm lies in the range of the frozen affine calculation. -/
theorem normalized_involution_range (range : InvolutionRange)
    {x : E6Space} (hx : x ∈ foldedSpace) (h : Function.Involutive (D.twisted x)) :
    (2 : ℝ) • x ∈ e6Lattice := by
  apply (range x hx).2
  intro j
  have h1 := simple_character_one_of_conj_eq_one D (involutive_twist_conj_eq_one D hx h) j
  rw [D.rootEvaluation, simple_evaluation] at h1
  have h2 : Circle.exp (2 * Real.pi * e6Inner (Pi.single j 1) ((2 : ℝ) • x)) = 1 :=
    Circle.coe_injective (by simpa only [Circle.coe_one])
  obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp h2
  have hπ : (2 * Real.pi) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  exact ⟨m, mul_left_cancel₀ hπ (hm.trans (mul_comm _ _))⟩

private theorem conj_mem_centralizer_of_eq_on_fixed
    {n m : AdelicGroups.PointsIn i ℂ}
    (h : ∀ y ∈ foldedSpace, MulAut.conj n (D.exp y) = MulAut.conj m (D.exp y)) :
    m⁻¹ * n ∈ Subgroup.centralizer (S : Set _) := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro s hs
  obtain ⟨y, hy, rfl⟩ := show s ∈ D.exp '' foldedSpace by
    rw [← D.fixedExp]
    exact hs
  have hh := congrArg (MulAut.conj m).symm (h y hy)
  have he : MulAut.conj (m⁻¹ * n) (D.exp y) = D.exp y := by
    rw [map_mul, map_inv]
    exact hh.trans ((MulAut.conj m).symm_apply_apply _)
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private theorem identityComponent_mul {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {J : Subgroup H} {g h : H} (hg : g ∈ identityComponent J) (hh : h ∈ identityComponent J) :
    g * h ∈ identityComponent J := by
  obtain ⟨u, hu, rfl⟩ := hg
  obtain ⟨v, hv, rfl⟩ := hh
  exact ⟨u * v, mul_mem_connectedComponent_one hu hv, rfl⟩

private theorem component_wall_words (x : E6Space)
    (hfolded : ∀ β ∈ foldedRoots, Set.MapsTo (reflection β) foldedSpace foldedSpace)
    (hwalls : ∀ β ∈ foldedRoots, OnWall β x → D.RealizesFoldedRoot x β) :
    ∀ r ∈ wallReflections x, ∃ m ∈ identityComponent (D.fixedAt x),
      ∀ y ∈ foldedSpace, MulAut.conj m (D.exp y) = D.exp (r y) := by
  intro r hr
  have h : Set.MapsTo r foldedSpace foldedSpace ∧
      ∃ m ∈ identityComponent (D.fixedAt x),
        ∀ y ∈ foldedSpace, MulAut.conj m (D.exp y) = D.exp (r y) := by
    induction hr using Submonoid.closure_induction with
    | mem f hf =>
      obtain ⟨β, ⟨hβ, hwall⟩, rfl⟩ := hf
      obtain ⟨s, _, hs, _, u, _, _, hu⟩ := hwalls β hβ hwall
      exact ⟨hfolded β hβ, s u, hs ⟨u, rfl⟩, hu⟩
    | one =>
      exact ⟨fun _ hy => hy, 1, ⟨1, mem_connectedComponent, rfl⟩, by intro y _; simp; rfl⟩
    | mul f g _ _ hf hg =>
      obtain ⟨hf, m, hm, hmact⟩ := hf
      obtain ⟨hg, n, hn, hnact⟩ := hg
      refine ⟨hf.comp hg, m * n, identityComponent_mul hm hn, ?_⟩
      intro y hy
      rw [map_mul]
      change MulAut.conj m (MulAut.conj n (D.exp y)) = D.exp (f (g y))
      rw [hnact _ hy, hmact _ (hg hy)]
  exact h.2

/-- Once the wall groups are realized, their Weyl actions reduce all components to the fixed torus. -/
theorem connected_normalized_of_wall_groups (x : E6Space)
    (hS : (S : Set _) ⊆ identityComponent (D.fixedAt x))
    (hreps : ∀ g ∈ D.fixedAt x, ∃ n ∈ D.fixedAt x,
      n ∈ Subgroup.normalizer (S : Set _) ∧ g * n⁻¹ ∈ identityComponent (D.fixedAt x))
    (hlabels : ∀ n ∈ D.fixedAt x, n ∈ Subgroup.normalizer (S : Set _) →
      ∃ w ∈ diagramCentralizingWeyl, D.RepresentsWeyl n w)
    (hstab : ∀ n ∈ D.fixedAt x, n ∈ Subgroup.normalizer (S : Set _) →
      ∀ w ∈ diagramCentralizingWeyl, D.RepresentsWeyl n w →
        ∃ r ∈ wallReflections x, Set.EqOn w r foldedSpace)
    (hfolded : ∀ β ∈ foldedRoots, Set.MapsTo (reflection β) foldedSpace foldedSpace)
    (hwalls : ∀ β ∈ foldedRoots, OnWall β x → D.RealizesFoldedRoot x β) :
    ConnectedSpace (D.fixedAt x) := by
  apply connected_identityComponent
  intro g hg
  obtain ⟨n, hn, hnS, hgn⟩ := hreps g hg
  obtain ⟨w, hw, hrepresent⟩ := hlabels n hn hnS
  obtain ⟨r, hr, hwr⟩ := hstab n hn hnS w hw hrepresent
  obtain ⟨m, hm, hmact⟩ := component_wall_words D x hfolded hwalls r hr
  have hcent := conj_mem_centralizer_of_eq_on_fixed D (n := n) (m := m)
    (fun y hy => (hrepresent y).trans ((congrArg D.exp (hwr hy)).trans (hmact y hy).symm))
  have hmn : m⁻¹ * n ∈ D.fixedAt x :=
    (D.fixedAt x).mul_mem ((D.fixedAt x).inv_mem (mem_identityComponent _ hm)) hn
  have hT : m⁻¹ * n ∈ D.T := by
    rw [D.centralizer]
    exact ⟨hmn.1, hcent⟩
  have hmnS : m⁻¹ * n ∈ S := fixed_torus_kernel D x ▸
    (show m⁻¹ * n ∈ D.T ⊓ D.fixedAt x from ⟨hT, hmn⟩)
  have hn0 := identityComponent_mul hm (hS hmnS)
  rw [mul_inv_cancel_left] at hn0
  have hg0 := identityComponent_mul hgn hn0
  rwa [inv_mul_cancel_right] at hg0

private theorem compact_rep_in_torus {n m : AdelicGroups.PointsIn i ℂ}
    (hn : n ∈ fixedSubgroup ω) (hm : m ∈ fixedSubgroup ω) {w : Function.End E6Space}
    (hnw : D.RepresentsWeyl n w) (hmw : D.RepresentsWeyl m w) : m⁻¹ * n ∈ D.T := by
  rw [D.centralizer]
  exact ⟨(fixedSubgroup ω).mul_mem ((fixedSubgroup ω).inv_mem hm) hn,
    conj_mem_centralizer_of_eq_on_fixed D (fun y _ => (hnw y).trans (hmw y).symm)⟩

private theorem twisted_fixed_equation {x : E6Space} {n b : AdelicGroups.PointsIn i ℂ}
    (hn : n ∈ fixedSubgroup D.δ) (hb : b ∈ D.T) {w : Function.End E6Space}
    (hw : D.RepresentsWeyl n w) :
    D.twisted x (b * n) = b * n ↔
      D.exp x = D.exp (w x) * (b * (D.δ b)⁻¹) := by
  let t := D.exp x
  let u := D.exp (w x)
  have hδb : D.δ b ∈ D.T := by
    obtain ⟨v, rfl⟩ := exists_exp D hb
    rw [D.diagramExp]
    exact exp_mem D _
  have hnt : n * t⁻¹ = u⁻¹ * n := by
    have hnt' : MulAut.conj n t = u := hw x
    calc
      n * t⁻¹ = MulAut.conj n (t⁻¹) * n := by simp [MulAut.conj_apply, mul_assoc]
      _ = u⁻¹ * n := by rw [map_inv, hnt']
  have hstep : D.twisted x (b * n) = t * D.δ b * u⁻¹ * n := by
    change t * D.δ (b * n) * t⁻¹ = _
    rw [map_mul, show D.δ n = n from hn, mul_assoc (t * D.δ b), ← mul_assoc t (D.δ b),
      mul_assoc (t * D.δ b), hnt, ← mul_assoc]
  rw [hstep, mul_left_inj, mul_inv_eq_iff_eq_mul]
  change (t * D.δ b = b * u) ↔ t = u * (b * (D.δ b)⁻¹)
  rw [← eq_mul_inv_iff_mul_eq, (torus_commutes D hb (exp_mem D (w x))).eq, mul_assoc]

/-- The Weyl stabilizer criterion from diagram-fixed compact representatives of the labels. -/
theorem normalizer_criterion_of_diagram_lift (rootCalc : FoldedRootCalculation)
    (projection : ProjectionCalculation) (weyl : FoldedWeylCalculation) {x : E6Space}
    (hx : x ∈ foldedSpace) {w : Function.End E6Space} (hw : w ∈ diagramCentralizingWeyl)
    {n₀ : AdelicGroups.PointsIn i ℂ} (hn₀ : n₀ ∈ fixedCompact ω D.δ)
    (hn₀S : n₀ ∈ Subgroup.normalizer (S : Set _)) (hrep : D.RepresentsWeyl n₀ w) :
    (∃ n ∈ D.fixedAt x, n ∈ Subgroup.normalizer (S : Set _) ∧ D.RepresentsWeyl n w) ↔
      w x - x ∈ projectedLattice := by
  have hfixed := weyl.2.2.1 w hw hx
  have hs : x - w x ∈ projectedLattice ↔ w x - x ∈ projectedLattice := by
    rw [rootCalc.2.2.1, ← neg_sub (w x) x]
    exact (AddSubgroup.closure foldedRoots).neg_mem_iff
  rw [← hs, ← projected_quotient_iff D projection hx hfixed]
  constructor
  · rintro ⟨n, hn, _, hnw⟩
    let b := n * n₀⁻¹
    have hb : b ∈ D.T := by
      have hcentral : n₀⁻¹ * n ∈ fixedSubgroup ω ⊓ Subgroup.centralizer (S : Set _) :=
        D.centralizer ▸ compact_rep_in_torus D hn.1 hn₀.1 hnw hrep
      have h : MulAut.conj n₀ (n₀⁻¹ * n) ∈ D.T :=
        D.centralizer.symm ▸ normalizes_compact_torus hn₀.1 hn₀S hcentral
      simpa only [MulAut.conj_apply, mul_inv_cancel_left] using h
    refine ⟨⟨b, hb⟩, (twisted_fixed_equation D hn₀.2 hb hrep).1 ?_⟩
    simpa only [b, inv_mul_cancel_right] using (show D.twisted x n = n from hn.2)
  · rintro ⟨b, hb⟩
    refine ⟨b.val * n₀, ⟨(fixedSubgroup ω).mul_mem (torus_subset_compact D b.property) hn₀.1,
      (twisted_fixed_equation D hn₀.2 b.property hrep).2 hb⟩,
      ?_, ?_⟩
    · let N : Subgroup (AdelicGroups.PointsIn i ℂ) := Subgroup.normalizer (S : Set _)
      exact N.mul_mem (torus_normalizes_fixedTorus D b.property) hn₀S
    · intro y
      change MulAut.conj (b.val * n₀) (D.exp y) = _
      rw [map_mul]
      change MulAut.conj b.val (MulAut.conj n₀ (D.exp y)) = _
      rw [show MulAut.conj n₀ (D.exp y) = _ from hrep y]
      exact torus_conj_on_self D b.property (exp_mem D _)

private theorem fixedTorus_subset_normalized_component {t₀ a : D.T} {x : E6Space}
    (hθ : θ = MulAut.conj t₀.val * D.δ)
    (hx : D.exp x = a.val * t₀.val * (D.δ a.val)⁻¹)
    (hS : (S : Set _) ⊆ identityComponent (fixedCompact ω θ)) :
    (S : Set _) ⊆ identityComponent (D.fixedAt x) := by
  intro s hs
  let c := MulAut.conj a.val
  have hc (g) : c g ∈ D.fixedAt x ↔ g ∈ fixedCompact ω θ :=
    fixedCompact_conj_iff (torus_subset_compact D a.property) (normalize_intertwines D hθ hx) g
  have h := mem_component_map c.toMonoidHom (IsTopologicalGroup.continuous_conj a.val)
    (fun u hu => (hc u).2 hu) (hS hs)
  change c s ∈ identityComponent (D.fixedAt x) at h
  rwa [show c s = s from torus_conj_on_self D a.property (fixedTorus_le D hs)] at h

private theorem folded_reflection_mapsTo (weyl : FoldedWeylCalculation) {β : E6Space}
    (hβ : β ∈ foldedRoots) : Set.MapsTo (reflection β) foldedSpace foldedSpace := by
  obtain ⟨w, hw, hwr⟩ := weyl.2.2.2.2.2 (reflection β) (Submonoid.subset_closure ⟨β, hβ, rfl⟩)
  intro y hy
  rw [← hwr hy]
  exact weyl.2.2.1 w hw hy

/-- The fixed compact group in the outer case is connected, with its normalizer
and compact root maps given by the same marked torus and wall arrangement. -/
theorem outerWallCalculation : OuterWallCalculation := by
  intro G i hG hsc htype ω θ hωθ S hS
  obtain ⟨D⟩ := exists_markedTorus ExceptionalOuterTorus.outerTorusComparison
    hG hsc htype hωθ hS
  have projection := ExceptionalFoldedWeyl.projectionCalculation
  have rootCalc := ExceptionalFoldedWeyl.foldedRootCalculation
  have weyl := ExceptionalFoldedWeyl.foldedWeylCalculation
  obtain ⟨t₀, a, x, hx, hθ, htwist⟩ := normalize_twist D projection
  have hinv := normalized_involutive D hθ htwist hωθ.outer_involutive
  have hrange := normalized_involution_range D ExceptionalFoldedWeyl.involutionRange hx hinv
  have hreps := normalized_component_representatives D hθ htwist
    (ExceptionalOuterTorus.fixedNormalizerRepresentatives G i hG hsc htype ω θ hωθ S hS)
  have hlabels (n : AdelicGroups.PointsIn i ℂ) (hn : n ∈ D.fixedAt x)
      (hnS : n ∈ Subgroup.normalizer (S : Set _)) :
      ∃ w ∈ diagramCentralizingWeyl, D.RepresentsWeyl n w := by
    obtain ⟨w, _, hrep, hfixed⟩ :=
      ExceptionalOuterCompactWeylLabels.compactWeylLabels G i hG hsc htype ω θ hωθ S hS
        D.T D.A D.M D.δ D.centralizer D.tori D.cartan D.corootBasis
        D.expAdd D.expRange D.expKernel D.diagramExp n hn.1 hnS
    exact ⟨w, hfixed x hx hinv hn, hrep⟩
  have hnormalizers (w : Function.End E6Space) (hw : w ∈ diagramCentralizingWeyl) :
      (∃ n ∈ D.fixedAt x, n ∈ Subgroup.normalizer (S : Set _) ∧ D.RepresentsWeyl n w) ↔
        w x - x ∈ projectedLattice := by
    obtain ⟨n, hn, hnS, hrep⟩ :=
      ExceptionalOuterCompactRankOneLifts.diagramFixedNormalizerLifts
        G i hG hsc htype ω θ hωθ S hS D w hw
    exact normalizer_criterion_of_diagram_lift D rootCalc projection weyl hx hw hn hnS hrep
  have hstab := ExceptionalFoldedWeyl.wallStabilizer x hx hrange
  have hwalls := ExceptionalOuterCompactRankOneLifts.compactRankOneWallLifts
    G i hG hsc htype ω θ hωθ S hS D x hx hinv
  have hconnected : ConnectedSpace (D.fixedAt x) :=
    connected_normalized_of_wall_groups D x
      (fixedTorus_subset_normalized_component D hθ htwist hS.2.1) hreps hlabels
      (fun n hn hnS w hw hrep => (hstab w hw).mp ((hnormalizers w hw).mp ⟨n, hn, hnS, hrep⟩))
      (fun _ hβ => folded_reflection_mapsTo weyl hβ) hwalls
  have hunique (n : AdelicGroups.PointsIn i ℂ) (hn : n ∈ D.fixedAt x)
      (hnS : n ∈ Subgroup.normalizer (S : Set _)) :
      ∃! w, w ∈ diagramCentralizingWeyl ∧ D.RepresentsWeyl n w := by
    obtain ⟨w, hw, hrep⟩ := hlabels n hn hnS
    exact ⟨w, ⟨hw, hrep⟩, fun v hv => weyl_label_unique D hv.1.1 hw.1 hv.2 hrep⟩
  refine ⟨connected_original_of_normalized D hθ htwist hconnected,
    D, t₀, a, x, hx, hrange, hθ, htwist, normalize_intertwines D hθ htwist,
    projected_quotient_representative D projection,
    (fun _ hy _ hz => projected_quotient_iff D projection hy hz), fixed_torus_kernel D x,
    (fun _ hn => represents_one_iff D hn), hreps, hunique, hnormalizers, hstab, ?_⟩
  intro β hβ
  refine ⟨hwalls β hβ, ?_⟩
  rintro ⟨f, _, himage, _, u, _, huS, huact⟩
  have hn : f u ∈ D.fixedAt x := mem_identityComponent _ (himage ⟨u, rfl⟩)
  obtain ⟨w, hw, hrep⟩ := hlabels (f u) hn huS
  have hshift := (hnormalizers w hw).mp ⟨f u, hn, huS, hrep⟩
  obtain ⟨b, hb⟩ := (projected_quotient_iff D projection (weyl.2.2.1 w hw hx) hx).mpr hshift
  have heq : D.exp (reflection β x) = D.exp (w x) := (huact x hx).symm.trans (hrep x)
  exact (ExceptionalOuterFoldedWallTransport.reflectionShiftCriterion β hβ x).mp
    ((projected_quotient_iff D projection (folded_reflection_mapsTo weyl hβ hx) hx).mp
      ⟨b, heq.trans hb⟩)

end LinearAlgebraicGroups.Arithmetic.ExceptionalOuterWallGroups
