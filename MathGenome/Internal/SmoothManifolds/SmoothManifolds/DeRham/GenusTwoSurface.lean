import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.GenusTwoSurface
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.Tori
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.GenusTwoAtlas
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.GenusTwoOrientation
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Algebra
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.MayerVietoris
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.HomotopyInvariance
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.PathIntegration
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.Stokes
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Algebra.Group.Quotient

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Tori
/-! Work on the cohomology of the constructed reflected connected sum.
Only the torus algebra statement is a conditional premise; no original target
is declared before dependency closure. The actual cover geometry, punctured-side
computations, and both restriction maps are established below. All four original conclusions are derived as
conditional helpers, without defining the original closed target wrappers.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SmoothManifolds.GenusTwoDeRhamResults

/-- Connectedness of the actual quotient gives its degree-zero group. -/
theorem degree_zero_conditional
    (_htorus : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType) :
    Specs.SmoothManifolds.DeRham.GenusTwoSurface.degree_zeroType := by
  intro S _ C B K
  letI : ConnectedSpace GenusTwoData.Surface := GenusTwoAtlas.connected
  exact DeRhamResults.h0_connected K

/-- The manifold has dimension two, and negative degrees use the zero complex. -/
theorem other_degrees_conditional
    (_htorus : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType) :
    Specs.SmoothManifolds.DeRham.GenusTwoSurface.other_degreesType := by
  intro S _ C B K
  exact ⟨fun k hk => DeRhamResults.above_dimension K k hk,
    fun j => (DeRhamResults.negative_degrees K j).2⟩

end SmoothManifolds.GenusTwoDeRhamResults

namespace SmoothManifolds.GenusTwoMayerVietoris
open MayerVietorisData
universe u
variable {A B C : Cochain.{u}} (E : ShortExact A B C)

/-- A surjection onto overlap cohomology kills the next connecting map. -/
theorem delta_eq_zero_of_surjective (k : ℕ)
    (hQ : Function.Surjective (E.q.onH k)) : E.delta k = 0 := by
  apply LinearMap.ext
  intro z
  exact (E.exact_at_right k z).mpr (hQ z)

/-- An injective connecting map forces the preceding difference to vanish. -/
theorem difference_eq_zero_of_injective_delta (k : ℕ)
    (hδ : Function.Injective (E.delta k)) : E.q.onH k = 0 := by
  apply LinearMap.ext
  intro y
  apply hδ
  exact (E.exact_at_right k (E.q.onH k y)).mpr ⟨y, rfl⟩ |>.trans (map_zero _).symm

/-- Once the preceding difference is onto, the next restriction is injective. -/
theorem restriction_injective (k : ℕ)
    (hQ : Function.Surjective (E.q.onH k)) :
    Function.Injective (E.r.onH (k+1)) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨z, hz⟩ := (E.exact_at_left k x).mp hx
  rw [delta_eq_zero_of_surjective E k hQ] at hz
  exact hz.symm

/-- A zero difference gives a surjective restriction by exactness. -/
theorem restriction_surjective (k : ℕ) (hQ : E.q.onH k = 0) :
    Function.Surjective (E.r.onH k) := by
  intro y
  apply (E.exact_at_middle k y).mp
  rw [hQ]
  rfl

/-- The algebraic step that identifies the two degree-one summands of the
connected sum, after the geometric restriction maps have been computed. -/
def restrictionEquiv (k : ℕ)
    (hprev : Function.Surjective (E.q.onH k))
    (hnext : E.q.onH (k+1) = 0) : A.H (k+1) ≃ₗ[ℝ] B.H (k+1) :=
  LinearEquiv.ofBijective (E.r.onH (k+1))
    ⟨restriction_injective E k hprev, restriction_surjective E (k+1) hnext⟩

/-- If the middle group in the following degree vanishes and the current
difference is zero, the connecting map is an isomorphism. -/
def connectingEquiv (k : ℕ) (hQ : E.q.onH k = 0)
    [Subsingleton (B.H (k+1))] : C.H k ≃ₗ[ℝ] A.H (k+1) := by
  apply LinearEquiv.ofBijective (E.delta k)
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro z hz
    obtain ⟨y, hy⟩ := (E.exact_at_right k z).mp hz
    rw [hQ] at hy
    exact hy.symm
  · intro x
    exact (E.exact_at_left k x).mp (Subsingleton.elim _ _)

/-- A surjective connecting map together with vanishing overlap in the
following degree forces the middle cohomology in that degree to vanish.
Applied to the torus/disk cover this proves vanishing on the punctured torus,
once the annulus connecting map has actually been evaluated. -/
theorem middle_subsingleton (k : ℕ)
    (hδ : Function.Surjective (E.delta k)) [Subsingleton (C.H (k+1))] :
    Subsingleton (B.H (k+1)) := by
  have hzero (y : B.H (k+1)) : y = 0 := by
    obtain ⟨x, hx⟩ := (E.exact_at_middle (k+1) y).mp (Subsingleton.elim _ _)
    obtain ⟨z, rfl⟩ := hδ x
    have hz := (E.exact_at_left k (E.delta k z)).mpr ⟨z, rfl⟩
    exact hx.symm.trans hz
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

end SmoothManifolds.GenusTwoMayerVietoris

namespace SmoothManifolds.GenusTwoDeRhamGeometry
open ModelData GenusTwoData GenusTwoAtlas MayerVietorisData Set

/-- The actual open collar of width 1/32 in the signed radial seam charts. -/
def collarRegion : Set Surface :=
  seamPoint '' {x : Euclidean 2 | |x 1| < (1/32 : ℝ)}

/-- The interior of either punctured torus inside the quotient. -/
def bulkRegion (side : Bool) : Set Surface :=
  sideInclusion side '' {p : PuncturedTorus | p.val ∉ boundaryCircle}

lemma collarRegion_open : IsOpen collarRegion :=
  isOpen_image_seamPoint
    (isOpen_lt (continuous_apply 1).abs continuous_const)
    (fun _ hx => lt_trans hx (by norm_num))

lemma bulkRegion_open (side : Bool) : IsOpen (bulkRegion side) :=
  isOpen_sideImage (isClosed_frontier.isOpen_compl.preimage continuous_subtype_val)
    (fun _ hp => hp) side

lemma bulkRegions_disjoint : Disjoint (bulkRegion false) (bulkRegion true) := by
  apply Set.disjoint_left.mpr
  intro z hzU hzV
  obtain ⟨p, hp, rfl⟩ := hzU
  obtain ⟨q, hq, he⟩ := hzV
  have hg := (projection_eq_iff (true, q) (false, p)).mp he
  rcases hg with h | h
  · have hf : true = false := congrArg Prod.fst h
    cases hf
  · exact hq h.2.1

lemma seam_subset_collar (side : Bool) (p : PuncturedTorus)
    (hp : p.val ∈ boundaryCircle) : sideInclusion side p ∈ collarRegion := by
  obtain ⟨s, hs⟩ := seam_covers_boundary side p hp
  exact ⟨![s, 0], by norm_num, hs⟩

/-- Each side is extended by the SAME open signed collar. -/
def extendedSide (side : Bool) : TopologicalSpace.Opens Surface :=
  ⟨bulkRegion side ∪ collarRegion, (bulkRegion_open side).union collarRegion_open⟩

/-- A concrete open cover on the specified quotient topology. -/
def surfaceCover : OpenCover Surface where
  U := extendedSide false
  V := extendedSide true
  cover z := by
    obtain ⟨⟨side, p⟩, rfl⟩ := projection_surjective z
    by_cases hp : p.val ∈ boundaryCircle
    · exact Or.inl (Or.inr (seam_subset_collar side p hp))
    · cases side
      · exact Or.inl (Or.inl ⟨p, hp, rfl⟩)
      · exact Or.inr (Or.inl ⟨p, hp, rfl⟩)

/-- No extraneous overlap is introduced by extending both bulks. -/
lemma surfaceCover_overlap :
    ((surfaceCover.U ⊓ surfaceCover.V : TopologicalSpace.Opens Surface) : Set Surface) =
      collarRegion := by
  ext z
  change (z ∈ bulkRegion false ∪ collarRegion ∧
    z ∈ bulkRegion true ∪ collarRegion) ↔ z ∈ collarRegion
  constructor
  · rintro ⟨hU, hV⟩
    rcases hU with hU | hU
    · rcases hV with hV | hV
      · exact (Set.disjoint_left.mp bulkRegions_disjoint hU hV).elim
      · exact hV
    · exact hU
  · intro h
    exact ⟨Or.inr h, Or.inr h⟩

/-- The overlap contains every seam point and is nonempty. -/
lemma collarRegion_nonempty : collarRegion.Nonempty :=
  ⟨seamPoint ![0, 0], ⟨![0, 0], by norm_num, rfl⟩⟩

/-- The overlap is connected: it is the continuous image of a real line
of angles times the signed radial interval. No cohomology is assumed here. -/
lemma collarRegion_connected : IsConnected collarRegion := by
  let J := Set.Ioo (-(1/32 : ℝ)) (1/32 : ℝ)
  letI : ConnectedSpace J := isConnected_iff_connectedSpace.mp
    (isConnected_Ioo (by norm_num))
  let f : ℝ × J → Euclidean 2 := fun z => ![z.1, z.2.val]
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_subtype_val.comp continuous_snd
  have hstrip (z : ℝ × J) : |f z 1| < 1/16 := by
    have h : |z.2.val| < (1/32 : ℝ) := abs_lt.mpr z.2.property
    exact h.trans (by norm_num)
  have hcont : Continuous (seamPoint ∘ f) :=
    continuousOn_seamPoint.comp_continuous hf hstrip
  have hrange : Set.range (seamPoint ∘ f) = collarRegion := by
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨f q, abs_lt.mpr q.2.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(x 0, ⟨x 1, abs_lt.mp hx⟩), ?_⟩
      congr 1
  rw [← hrange]
  exact isConnected_range hcont

end SmoothManifolds.GenusTwoDeRhamGeometry

namespace SmoothManifolds.GenusTwoMayerVietoris
open MayerVietorisData ModelData AtlasData BundleOperationsData CovectorData
  ExteriorData DeRhamData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  {K : Calculus C B} {O : OpenCover M}

/-- The cohomological difference of a realized cover is the difference of
its actual two open restrictions. This holds for every realization. -/
theorem difference_onH (D : CoverComplex K O) (k : ℕ)
    (x : (D.onU.complex.prod D.onV.complex).H k) :
    D.sequence.q.onH k x =
      (OpenForms.openRestriction O.V (O.U ⊓ O.V) inf_le_right
        D.onV D.onOverlap).onH k ((ChainMap.snd _ _).onH k x) -
      (OpenForms.openRestriction O.U (O.U ⊓ O.V) inf_le_left
        D.onU D.onOverlap).onH k ((ChainMap.fst _ _).onH k x) := by
  obtain ⟨ω, rfl⟩ := (D.onU.complex.prod D.onV.complex).class_surjective k x
  simp only [ChainMap.onH_class]
  rw [← map_sub]
  congr 1
  apply Subtype.ext
  apply D.onOverlap.injective k
  funext p
  change D.onOverlap.field k (D.sequence.q.map k ω.val) p =
    D.onOverlap.field k
      ((OpenForms.openRestriction O.V (O.U ⊓ O.V) inf_le_right
          D.onV D.onOverlap).map k ω.val.2 -
        (OpenForms.openRestriction O.U (O.U ⊓ O.V) inf_le_left
          D.onU D.onOverlap).map k ω.val.1) p
  simpa only [map_sub, Pi.sub_apply, OpenForms.openRestriction_field] using
    D.difference k ω.val p

/-- Vanishing of BOTH geometric restrictions makes the difference zero. -/
theorem difference_zero (D : CoverComplex K O) (k : ℕ)
    (hU : (OpenForms.openRestriction O.U (O.U ⊓ O.V) inf_le_left
      D.onU D.onOverlap).onH k = 0)
    (hV : (OpenForms.openRestriction O.V (O.U ⊓ O.V) inf_le_right
      D.onV D.onOverlap).onH k = 0) : D.sequence.q.onH k = 0 := by
  apply LinearMap.ext
  intro x
  rw [difference_onH D k x, hU, hV]
  exact sub_self 0

/-- Restriction gives the direct sum after the preceding difference is onto
and the two current restrictions to the overlap have been shown to vanish. -/
def coverRestrictionEquiv (D : CoverComplex K O) (k : ℕ)
    (hprev : Function.Surjective (D.sequence.q.onH k))
    (hU : (OpenForms.openRestriction O.U (O.U ⊓ O.V) inf_le_left
      D.onU D.onOverlap).onH (k+1) = 0)
    (hV : (OpenForms.openRestriction O.V (O.U ⊓ O.V) inf_le_right
      D.onV D.onOverlap).onH (k+1) = 0) :
    K.Cohomology (k+1) ≃ₗ[ℝ]
      (D.onU.complex.H (k+1) × D.onV.complex.H (k+1)) :=
  (restrictionEquiv D.sequence k hprev (difference_zero D (k+1) hU hV)).trans
    (D.onU.complex.productHEquiv D.onV.complex (k+1))

/-- The annulus connecting map identifies the next global group once the two
restrictions vanish and both side groups in the next degree are zero. -/
def coverConnectingEquiv (D : CoverComplex K O) (k : ℕ)
    (hU : (OpenForms.openRestriction O.U (O.U ⊓ O.V) inf_le_left
      D.onU D.onOverlap).onH k = 0)
    (hV : (OpenForms.openRestriction O.V (O.U ⊓ O.V) inf_le_right
      D.onV D.onOverlap).onH k = 0)
    [Subsingleton (D.onU.complex.H (k+1))]
    [Subsingleton (D.onV.complex.H (k+1))] :
    K.Cohomology (k+1) ≃ₗ[ℝ] D.onOverlap.complex.H k := by
  let e := D.onU.complex.productHEquiv D.onV.complex (k+1)
  letI : Subsingleton ((D.onU.complex.prod D.onV.complex).H (k+1)) :=
    e.injective.subsingleton
  exact (connectingEquiv D.sequence k (difference_zero D k hU hV)).symm

end SmoothManifolds.GenusTwoMayerVietoris

namespace SmoothManifolds.GenusTwoDeRhamResults
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
  GenusTwoData MayerVietorisData GenusTwoMayerVietoris

/-- Concatenating the two pairs of handle coordinates gives four coordinates. -/
def twoHandleCoordinates :
    ((Fin 2 → ℝ) × (Fin 2 → ℝ)) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 2) ℝ ℝ).symm.trans
    (LinearEquiv.piCongrLeft ℝ (fun _ : Fin 4 => ℝ) finSumFinEquiv)

/-- Algebraic reduction for a genuine open cover of the constructed surface.
Its geometric inputs are explicit arguments and are established below
for the actual surface cover. -/
theorem degree_one_of_cover
    {S : SmoothManifold 2 .euclidean Surface} {C : CotangentBundle S}
    {B : ∀ k, FormBundle C k} {K : Calculus C B} {O : OpenCover Surface}
    (D : CoverComplex K O)
    (hprev : Function.Surjective (D.sequence.q.onH 0))
    (hU : (OpenForms.openRestriction O.U (O.U ⊓ O.V) inf_le_left
      D.onU D.onOverlap).onH 1 = 0)
    (hV : (OpenForms.openRestriction O.V (O.U ⊓ O.V) inf_le_right
      D.onV D.onOverlap).onH 1 = 0)
    (eU : D.onU.complex.H 1 ≃ₗ[ℝ] (Fin 2 → ℝ))
    (eV : D.onV.complex.H 1 ≃ₗ[ℝ] (Fin 2 → ℝ)) :
    Nonempty (K.Cohomology 1 ≃ₗ[ℝ] (Fin 4 → ℝ)) :=
  ⟨((coverRestrictionEquiv D 0 hprev hU hV).trans (eU.prodCongr eV)).trans
    twoHandleCoordinates⟩

/-- The degree-two reduction uses the ACTUAL overlap group and restrictions.
The annulus identification and punctured-side vanishing are proved below. -/
theorem degree_two_of_cover
    {S : SmoothManifold 2 .euclidean Surface} {C : CotangentBundle S}
    {B : ∀ k, FormBundle C k} {K : Calculus C B} {O : OpenCover Surface}
    (D : CoverComplex K O)
    (hU : (OpenForms.openRestriction O.U (O.U ⊓ O.V) inf_le_left
      D.onU D.onOverlap).onH 1 = 0)
    (hV : (OpenForms.openRestriction O.V (O.U ⊓ O.V) inf_le_right
      D.onV D.onOverlap).onH 1 = 0)
    [Subsingleton (D.onU.complex.H 2)] [Subsingleton (D.onV.complex.H 2)]
    (eOverlap : D.onOverlap.complex.H 1 ≃ₗ[ℝ] ℝ) :
    Nonempty (K.Cohomology 2 ≃ₗ[ℝ] ℝ) :=
  ⟨(coverConnectingEquiv D 1 hU hV).trans eOverlap⟩

end SmoothManifolds.GenusTwoDeRhamResults

namespace SmoothManifolds.GenusTwoMayerVietoris
open MayerVietorisData
universe u
variable {A B C : Cochain.{u}} (E : ShortExact A B C)

/-- A zero preceding difference makes the connecting map injective. -/
theorem connecting_injective (k : ℕ) (hQ : E.q.onH k = 0) :
    Function.Injective (E.delta k) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro z hz
  obtain ⟨y, hy⟩ := (E.exact_at_right k z).mp hz
  rw [hQ] at hy
  exact hy.symm

/-- In the punctured-torus sequence the annulus and torus groups are both R.
Hence a zero restriction makes their connecting map bijective. This uses
one-dimensionality only AFTER the geometric zero restriction is known. -/
theorem connecting_bijective_of_lines (k : ℕ)
    (hQ : E.q.onH k = 0)
    (eC : C.H k ≃ₗ[ℝ] ℝ) (eA : A.H (k+1) ≃ₗ[ℝ] ℝ) :
    Function.Bijective (E.delta k) := by
  have hinj := connecting_injective E k hQ
  let f : ℝ →ₗ[ℝ] ℝ := eA.toLinearMap.comp ((E.delta k).comp eC.symm.toLinearMap)
  have hf : Function.Injective f := eA.injective.comp (hinj.comp eC.symm.injective)
  have hs := LinearMap.surjective_of_injective hf
  refine ⟨hinj, ?_⟩
  intro x
  obtain ⟨t, ht⟩ := hs (eA x)
  exact ⟨eC.symm t, eA.injective ht⟩

/-- The punctured-torus Mayer–Vietoris calculation, stated for actual exact
sequence maps. The zero restriction is a geometric input, not a consequence
of the dimensions of the torus alone. -/
theorem punctured_torus_algebra
    (hQ0 : Function.Surjective (E.q.onH 0)) (hQ1 : E.q.onH 1 = 0)
    (eC : C.H 1 ≃ₗ[ℝ] ℝ) (eA : A.H 2 ≃ₗ[ℝ] ℝ)
    [Subsingleton (C.H 2)] :
    Nonempty (A.H 1 ≃ₗ[ℝ] B.H 1) ∧ Subsingleton (B.H 2) := by
  exact ⟨⟨restrictionEquiv E 0 hQ0 hQ1⟩,
    middle_subsingleton E 1 (connecting_bijective_of_lines E 1 hQ1 eC eA).2⟩

end SmoothManifolds.GenusTwoMayerVietoris

namespace SmoothManifolds.GenusTwoDeRhamResults
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
  SphereTorusData TorusDeRhamData

/-- Extract the degree-one torus group from the entire conditional algebra
statement, without replacing that premise by a special case. -/
theorem torus_degree_one
    (htorus : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType)
    (r : ℕ) (S : SmoothManifold r .euclidean (FlatTorus r))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B) :
    Nonempty (K.Cohomology 1 ≃ₗ[ℝ] (Fin r → ℝ)) := by
  obtain ⟨P, hP⟩ := DeRhamResults.product_exists K
  obtain ⟨F⟩ := htorus r S hS C B K P hP
  exact ⟨(F.equiv 1).symm.trans (exteriorPower.oneEquiv ℝ (Euclidean r))⟩

/-- Extract the two-dimensional torus top group from its actual exterior
presentation. The top exterior power of R² has dimension one. -/
theorem torus_degree_two
    (htorus : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType)
    (S : SmoothManifold 2 .euclidean (FlatTorus 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B) :
    Nonempty (K.Cohomology 2 ≃ₗ[ℝ] ℝ) := by
  obtain ⟨P, hP⟩ := DeRhamResults.product_exists K
  obtain ⟨F⟩ := htorus 2 S hS C B K P hP
  let e : ExteriorModel 2 2 ≃ₗ[ℝ] ℝ :=
    LinearEquiv.ofFinrankEq _ _ (by simp [ExteriorModel, exteriorPower.finrank_eq])
  exact ⟨(F.equiv 2).symm.trans e⟩

end SmoothManifolds.GenusTwoDeRhamResults

namespace SmoothManifolds.GenusTwoDeRhamGeometry
open ModelData SphereTorusData GenusTwoData GenusTwoAtlas Set Topology

abbrev CollarInterval := Set.Ioo (-(1/32 : ℝ)) (1/32 : ℝ)
abbrev AngleStrip := ℝ × CollarInterval

/-- Coordinates on the open strip before imposing periodicity of angle. -/
def stripCoordinates (z : AngleStrip) : Euclidean 2 := ![z.1, z.2.val]

lemma stripCoordinates_bound (z : AngleStrip) :
    |stripCoordinates z 1| < (1/32 : ℝ) := abs_lt.mpr z.2.property

/-- The real strip in the upstream coordinate representation. -/
def stripCoordinatesHomeomorph :
    AngleStrip ≃ₜ {x : Euclidean 2 | |x 1| < (1/32 : ℝ)} where
  toFun z := ⟨stripCoordinates z, stripCoordinates_bound z⟩
  invFun x := (x.val 0, ⟨x.val 1, abs_lt.mp x.property⟩)
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_subtype_val.comp continuous_snd
  continuous_invFun :=
    ((continuous_apply 0).comp continuous_subtype_val).prodMk
      (((continuous_apply 1).comp continuous_subtype_val).subtype_mk _)

lemma stripCoordinates_continuous : Continuous stripCoordinates :=
  continuous_subtype_val.comp stripCoordinatesHomeomorph.continuous

/-- The actual signed seam parametrization into its open image. -/
def stripMap : C(AngleStrip, collarRegion) where
  toFun z := ⟨seamPoint (stripCoordinates z),
    ⟨stripCoordinates z, stripCoordinates_bound z, rfl⟩⟩
  continuous_toFun :=
    (continuousOn_seamPoint.comp_continuous stripCoordinates_continuous
      (fun z => (stripCoordinates_bound z).trans (by norm_num))).subtype_mk _

lemma stripMap_surjective : Function.Surjective stripMap := by
  rintro ⟨p, x, hx, rfl⟩
  refine ⟨(x 0, ⟨x 1, abs_lt.mp hx⟩), ?_⟩
  apply Subtype.ext
  congr 1

lemma stripMap_open : IsOpenMap stripMap := by
  have hraw : IsOpenMap (fun z : AngleStrip => seamPoint (stripCoordinates z)) := by
    intro U hU
    have hcoord : IsOpen (stripCoordinates '' U) :=
      ((isOpen_lt (continuous_apply 1).abs continuous_const).isOpenMap_subtype_val.comp
        stripCoordinatesHomeomorph.isOpenMap) U hU
    have he : (fun z : AngleStrip => seamPoint (stripCoordinates z)) '' U =
        seamPoint '' (stripCoordinates '' U) :=
      Set.image_comp seamPoint stripCoordinates U
    rw [he]
    apply isOpen_image_seamPoint hcoord
    rintro x ⟨z, _, rfl⟩
    exact (stripCoordinates_bound z).trans (by norm_num)
  exact hraw.codRestrict _

lemma stripMap_quotient : IsQuotientMap stripMap :=
  stripMap_open.isQuotientMap stripMap.continuous stripMap_surjective

/-- Periodic angle and signed radius in the standard open cylinder. -/
def cylinderProjection : C(AngleStrip, AddCircle (1 : ℝ) × CollarInterval) where
  toFun z := ((z.1 : AddCircle (1 : ℝ)), z.2)
  continuous_toFun :=
    ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_fst).prodMk continuous_snd

lemma cylinderProjection_quotient : IsQuotientMap cylinderProjection :=
  (QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).isQuotientMap

lemma anglePoint_eq_of_circle_eq {s s' : ℝ}
    (h : (s : AddCircle (1 : ℝ)) = (s' : AddCircle (1 : ℝ))) :
    anglePoint s = anglePoint s' := by
  have hp : quotientProjection 1 (fun _ => s) = quotientProjection 1 (fun _ => s') :=
    funext (fun _ => h)
  have he := congrArg
    (fun q : FlatTorus 1 => SphereTorus.periodicAngleHomeomorph 1 q 0) hp
  simpa only [SphereTorus.periodicAngleHomeomorph_apply, SphereTorusData.angleMap] using he

/-- The only identifications in the collar are whole turns in the angle. -/
lemma stripMap_fibers (x y : AngleStrip) :
    stripMap x = stripMap y ↔ cylinderProjection x = cylinderProjection y := by
  constructor
  · intro h
    have he : seamPoint (stripCoordinates x) = seamPoint (stripCoordinates y) :=
      congrArg Subtype.val h
    obtain ⟨ht, k, hk⟩ := seamPoint_fiber
      ((stripCoordinates_bound x).trans (by norm_num))
      ((stripCoordinates_bound y).trans (by norm_num)) he
    apply Prod.ext
    · apply QuotientAddGroup.eq_iff_sub_mem.mpr
      refine ⟨k, ?_⟩
      change k • (1 : ℝ) = x.1 - y.1
      rw [zsmul_eq_mul]
      change x.1 = y.1 + k at hk
      rw [hk]
      ring
    · exact Subtype.ext ht
  · intro h
    have ha : (x.1 : AddCircle (1 : ℝ)) = (y.1 : AddCircle (1 : ℝ)) :=
      congrArg Prod.fst h
    have ht : x.2 = y.2 :=
      congrArg (fun z : AddCircle (1 : ℝ) × CollarInterval => z.2) h
    have hang := anglePoint_eq_of_circle_eq ha
    apply Subtype.ext
    change seamPoint (stripCoordinates x) = seamPoint (stripCoordinates y)
    rw [seamPoint_eq _ ((stripCoordinates_bound x).trans (by norm_num)),
      seamPoint_eq _ ((stripCoordinates_bound y).trans (by norm_num))]
    have htime : stripCoordinates x 1 = stripCoordinates y 1 := congrArg Subtype.val ht
    have hrad : radialCoordinates (stripCoordinates x 0) (stripCoordinates x 1) =
        radialCoordinates (stripCoordinates y 0) (stripCoordinates y 1) := by
      unfold radialCoordinates
      rw [htime]
      change (fun j => (1/8 + |stripCoordinates y 1|) * (anglePoint x.1).val j) = _
      rw [hang]
      rfl
    have htor : signedRadialTorus (stripCoordinates x 0) (stripCoordinates x 1) =
        signedRadialTorus (stripCoordinates y 0) (stripCoordinates y 1) := by
      unfold signedRadialTorus
      rw [hrad, htime]
    simp only [htime]
    congr 1
    apply Subtype.ext
    simpa only [htime] using htor

/-- The actual collar in the quotient topology is the standard open annulus.
This is a topological identification; no smoothness or cohomology bridge is
asserted by this declaration. -/
def collarHomeomorph : collarRegion ≃ₜ AddCircle (1 : ℝ) × CollarInterval :=
  stripMap_quotient.homeomorph.symm.trans
    ((Homeomorph.Quotient.congrRight stripMap_fibers).trans
      cylinderProjection_quotient.homeomorph)

end SmoothManifolds.GenusTwoDeRhamGeometry

namespace SmoothManifolds.GenusTwoDeRhamGeometry
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
  GenusTwoData MayerVietorisData

/-- The concrete cover has its genuine short exact de Rham sequence, for
every supplied realization of the global smooth de Rham complex. The full
restricted form spaces and partition lifts come from the proved MV theorem. -/
theorem surface_cover_complex
    {S : SmoothManifold 2 .euclidean Surface} {C : CotangentBundle S}
    {B : ∀ k, FormBundle C k} (K : Calculus C B) :
    ∃ D : CoverComplex K surfaceCover, HasPartitionLift D := by
  obtain ⟨DU⟩ := OpenForms.openCalculus_exists K surfaceCover.U
  obtain ⟨DV⟩ := OpenForms.openCalculus_exists K surfaceCover.V
  obtain ⟨DW⟩ := OpenForms.openCalculus_exists K (surfaceCover.U ⊓ surfaceCover.V)
  exact ⟨OpenForms.assembledCover K surfaceCover DU DV DW,
    OpenForms.assembledCover_partition K surfaceCover DU DV DW⟩

end SmoothManifolds.GenusTwoDeRhamGeometry

namespace SmoothManifolds.GenusTwoOpenCohomology
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
  {B : ∀ k, FormBundle C k}

/-- A smooth function whose intrinsic differential vanishes near p is constant
near p. The Euclidean model is sufficient for the present surface calculation. -/
theorem scalar_constant_near (C : CotangentBundle S) (f : M → ℝ)
    (hf : PartitionData.ScalarSmooth S.smoothStructure.val f) (p : M)
    (hd : ∀ᶠ q in 𝓝 p, dFunction S f hf q = 0) :
    ∀ᶠ q in 𝓝 p, f q = f p := by
  classical
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨F, ⟨A, hA, hpA, hF⟩, hFg⟩ :=
    exists_germChartExtension S p c hc hp (functionGerm S f hf p)
  have he : (fun q => F (c q).val) =ᶠ[𝓝 p] f := Germ.coe_eq.mp hFg
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp (he.and hd)
  let W := c.target ∩ c.symm ⁻¹' V
  have hW : IsOpen W := c.isOpen_inter_preimage_symm hV
  have hpW : c p ∈ W := ⟨c.map_source hp, by
    simpa only [mem_preimage, c.left_inv hp] using hpV⟩
  have hval : IsOpenMap (Subtype.val : ModelSpace n .euclidean → Euclidean n) :=
    (show IsOpen (modelSet n .euclidean) from isOpen_univ).isOpenMap_subtype_val
  have hdomain : IsOpen (A ∩ (Subtype.val '' W)) := hA.inter (hval W hW)
  have hpdomain : (c p).val ∈ A ∩ (Subtype.val '' W) := ⟨hpA, ⟨c p, hpW, rfl⟩⟩
  have hdiff : DifferentiableOn ℝ F (A ∩ (Subtype.val '' W)) :=
    hF.differentiableOn (by simp) |>.mono inter_subset_left
  have hzero : (A ∩ (Subtype.val '' W)).EqOn (fderiv ℝ F) 0 := by
    rintro z ⟨hzA, y, hy, rfl⟩
    have hcy : c (c.symm y) = y := c.right_inv hy.1
    have hcg : GermChartExtension S (c.symm y) c
        (functionGerm S f hf (c.symm y)) F := by
      refine ⟨⟨A, hA, by simpa only [hcy] using hzA, hF⟩, Germ.coe_eq.mpr ?_⟩
      filter_upwards [hV.mem_nhds hy.2] with q hq
      exact (hVsub hq).1
    have hcoords := (Covectors.differential_coordinates S C f hf c hc
      (c.symm y) (c.map_target hy.1) F hcg).1
    apply ContinuousLinearMap.coe_injective
    apply (Pi.basisFun ℝ (Fin n)).ext
    intro i
    have hi := hcoords i
    rw [(hVsub hy.2).2] at hi
    simpa only [hcy, LinearMap.zero_apply, Pi.basisFun_apply,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.toLinearMap_zero,
      Pi.zero_apply] using hi.symm
  have hopen := hdomain.isOpen_inter_preimage_of_fderiv_eq_zero hdiff hzero {F (c p).val}
  have hn : A ∩ (Subtype.val '' W) ∩ F ⁻¹' {F (c p).val} ∈ 𝓝 (c p).val :=
    hopen.mem_nhds ⟨hpdomain, rfl⟩
  have hccont : ContinuousAt (fun q => (c q).val) p :=
    continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
  filter_upwards [he, hccont.preimage_mem_nhds hn] with q hq hqW
  exact hq.symm.trans (hqW.2.trans he.self_of_nhds)

/-- Scalar coefficient of an actual degree-zero restricted form. -/
def zeroCoefficient {U : TopologicalSpace.Opens M} (ω : RestrictedField S U 0)
    (p : U) : ℝ :=
  exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p.val)) (ω p)

end SmoothManifolds.GenusTwoOpenCohomology

namespace SmoothManifolds.GenusTwoDeRhamGeometry
open ModelData SphereTorusData GenusTwoData GenusTwoAtlas Set

lemma sideImage_subset_extendedSide (side : Bool) :
    Set.range (sideInclusion side) ⊆ (extendedSide side : Set Surface) := by
  rintro z ⟨p, rfl⟩
  by_cases hp : p.val ∈ boundaryCircle
  · exact Or.inr (seam_subset_collar side p hp)
  · exact Or.inl ⟨p, hp, rfl⟩

lemma extendedSide_eq_sideImage_union_collar (side : Bool) :
    (extendedSide side : Set Surface) = Set.range (sideInclusion side) ∪ collarRegion := by
  apply Set.Subset.antisymm
  · rintro z (hz | hz)
    · obtain ⟨p, _, rfl⟩ := hz
      exact Or.inl ⟨p, rfl⟩
    · exact Or.inr hz
  · rintro z (hz | hz)
    · exact sideImage_subset_extendedSide side hz
    · exact Or.inr hz

lemma extendedSide_connected (side : Bool) :
    IsConnected (extendedSide side : Set Surface) := by
  rw [extendedSide_eq_sideImage_union_collar]
  have hs : (Set.range (sideInclusion side) ∩ collarRegion).Nonempty := by
    let p : PuncturedTorus :=
      ⟨signedRadialTorus 0 0, signedRadialTorus_notMem_removedDisk 0 0 (by norm_num)⟩
    have hp : p.val ∈ boundaryCircle :=
      (signedRadialTorus_mem_boundaryCircle_iff 0 0 (by norm_num)).mpr rfl
    exact ⟨sideInclusion side p, ⟨p, rfl⟩, seam_subset_collar side p hp⟩
  exact (isConnected_range (continuous_sideInclusion side)).union hs collarRegion_connected


/-- The bulk really is the torus with the closed coordinate disk removed. -/
def puncturedInteriorHomeomorph :
    {p : PuncturedTorus | p.val ∉ boundaryCircle} ≃ₜ
      ↥((closure removedDisk)ᶜ) where
  toFun p := ⟨p.val.val, by
    intro hp
    apply p.property
    change p.val.val ∈ frontier removedDisk
    rw [frontier, isOpen_removedDisk.interior_eq]
    exact ⟨hp, p.val.property⟩⟩
  invFun p := ⟨⟨p.val, fun hp => p.property (subset_closure hp)⟩,
    fun hp => p.property (frontier_subset_closure hp)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val

/-- Exact topological identification of each actual quotient bulk. -/
def bulkHomeomorph (side : Bool) :
    bulkRegion side ≃ₜ ↥((closure removedDisk)ᶜ) :=
  ((isClosedEmbedding_sideInclusion side).isEmbedding.homeomorphImage
    {p : PuncturedTorus | p.val ∉ boundaryCircle}).symm.trans
      puncturedInteriorHomeomorph

end SmoothManifolds.GenusTwoDeRhamGeometry

namespace SmoothManifolds.GenusTwoOpenCohomology
open ModelData AtlasData MapData TangentData DifferentialData Set Filter
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]

theorem open_inclusion_differential_equiv
    (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M)
    (R : SmoothManifold n a U)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U U.isOpen))
    (hinc : IsSmoothMap R S Subtype.val) (p : U) :
    ∃ E : TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val,
      IsDifferential R S Subtype.val p E.toLinearMap := by
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
  let cr : ModelChart n a U := c.subtypeRestr (s := U) ⟨p⟩
  have hcr : cr ∈ R.smoothStructure.val := by
    rw [hR]
    exact subset_maximalExtension
      (openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _ S.smoothStructure.property.1 U U.isOpen)
      ⟨⟨p⟩, c, hc, rfl⟩
  have hpr : p ∈ cr.source := by simpa [cr] using hp
  obtain ⟨xs, bs, ER, hxs, hER, _, _⟩ := coordinate_tangent_model R p cr hcr hpr
  obtain ⟨ys, bt, ES, hys, hES, _, _⟩ := coordinate_tangent_model S p.val c hc hp
  let L := differential R S Subtype.val hinc p
  have hL : IsDifferential R S Subtype.val p L :=
    differential_spec R S Subtype.val hinc p
  have heq (v : TangentSpace R p) : ES (L v) = ER v := by
    have hj := differential_jacobian R S Subtype.val hinc p L hL cr c hcr hc hpr hp
      ER ES ⟨xs, hxs, hER⟩ ⟨ys, hys, hES⟩ univ id isOpen_univ (mem_univ _)
      contDiffOn_id (Filter.Eventually.of_forall (fun _ => rfl)) v
    simpa using hj
  let E : TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val := ER.trans ES.symm
  refine ⟨E, ?_⟩
  have he : E.toLinearMap = L := by
    apply LinearMap.ext
    intro v
    apply ES.injective
    simpa [E] using (heq v).symm
  rw [he]
  exact hL

/-- The induced open manifold comes with the genuine invertible tangent inclusion. -/
theorem open_manifold_tangent_equiv
    (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M) :
    ∃ R : SmoothManifold n a U,
      R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (openSubsetAtlas S.smoothStructure.val U U.isOpen) ∧
      IsSmoothMap R S Subtype.val ∧
      ∀ p : U, ∃ E : TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val,
        IsDifferential R S Subtype.val p E.toLinearMap := by
  obtain ⟨R, _, hR, hinc⟩ := exists_openSubset_smoothManifold S U U.isOpen
  exact ⟨R, hR, hinc, open_inclusion_differential_equiv S U R hR hinc⟩
end SmoothManifolds.GenusTwoOpenCohomology

namespace SmoothManifolds.MayerVietorisData.OpenForms
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}

/-- The identity change of realization preserves the underlying smooth field. -/
@[simp] theorem realizationChange_field (U : TopologicalSpace.Opens M)
    (D E : OpenCalculus C B U) (k : ℕ) (ω : D.complex.Obj k) :
    E.field k ((openRestriction U U le_rfl D E).map k ω) = D.field k ω := by
  simpa only using openRestriction_field U U le_rfl D E k ω

/-- Changing full realizations and changing back fixes every cochain. -/
@[simp] theorem realizationChange_inverse (U : TopologicalSpace.Opens M)
    (D E : OpenCalculus C B U) (k : ℕ) (ω : D.complex.Obj k) :
    (openRestriction U U le_rfl E D).map k
      ((openRestriction U U le_rfl D E).map k ω) = ω := by
  apply D.injective k
  simp only [realizationChange_field]

/-- The unique field-preserving equivalence between full realizations. -/
def realizationEquiv (U : TopologicalSpace.Opens M)
    (D E : OpenCalculus C B U) (k : ℕ) :
    D.complex.Obj k ≃ₗ[ℝ] E.complex.Obj k where
  toLinearMap := (openRestriction U U le_rfl D E).map k
  invFun := (openRestriction U U le_rfl E D).map k
  left_inv := realizationChange_inverse U D E k
  right_inv := realizationChange_inverse U E D k

@[simp] theorem realizationEquiv_comm (U : TopologicalSpace.Opens M)
    (D E : OpenCalculus C B U) (k : ℕ) (ω : D.complex.Obj k) :
    E.complex.d k (realizationEquiv U D E k ω) =
      realizationEquiv U D E (k+1) (D.complex.d k ω) :=
  (openRestriction U U le_rfl D E).comm k ω

/-- Restriction is independent of the chosen full realization of each domain. -/
theorem realizationEquiv_restriction
    (U W : TopologicalSpace.Opens M) (hWU : W ≤ U)
    (D E : OpenCalculus C B U) (F G : OpenCalculus C B W)
    (k : ℕ) (ω : D.complex.Obj k) :
    realizationEquiv W F G k ((openRestriction U W hWU D F).map k ω) =
      (openRestriction U W hWU E G).map k (realizationEquiv U D E k ω) := by
  apply G.injective k
  simp only [realizationEquiv, LinearEquiv.coe_mk,
    realizationChange_field, openRestriction_field]

/-- The canonical isomorphism on cohomology induced by unchanged fields. -/
def realizationHEquiv (U : TopologicalSpace.Opens M)
    (D E : OpenCalculus C B U) (k : ℕ) :
    D.complex.H k ≃ₗ[ℝ] E.complex.H k where
  toLinearMap := (openRestriction U U le_rfl D E).onH k
  invFun := (openRestriction U U le_rfl E D).onH k
  left_inv := by
    intro x
    obtain ⟨ω, rfl⟩ := D.complex.class_surjective k x
    change (openRestriction U U le_rfl E D).onH k
      ((openRestriction U U le_rfl D E).onH k (D.complex.classOf k ω)) =
        D.complex.classOf k ω
    simp only [ChainMap.onH_class]
    apply congrArg (D.complex.classOf k)
    apply Subtype.ext
    exact realizationChange_inverse U D E k ω.val
  right_inv := by
    intro x
    obtain ⟨ω, rfl⟩ := E.complex.class_surjective k x
    change (openRestriction U U le_rfl D E).onH k
      ((openRestriction U U le_rfl E D).onH k (E.complex.classOf k ω)) =
        E.complex.classOf k ω
    simp only [ChainMap.onH_class]
    apply congrArg (E.complex.classOf k)
    apply Subtype.ext
    exact realizationChange_inverse U E D k ω.val

/-- The cohomological restriction square commutes for arbitrary realizations. -/
theorem realizationHEquiv_restriction
    (U W : TopologicalSpace.Opens M) (hWU : W ≤ U)
    (D E : OpenCalculus C B U) (F G : OpenCalculus C B W)
    (k : ℕ) (x : D.complex.H k) :
    realizationHEquiv W F G k ((openRestriction U W hWU D F).onH k x) =
      (openRestriction U W hWU E G).onH k (realizationHEquiv U D E k x) := by
  obtain ⟨ω, rfl⟩ := D.complex.class_surjective k x
  simp only [realizationHEquiv, LinearEquiv.coe_mk,
    ChainMap.onH_class]
  congr 1
  apply Subtype.ext
  exact realizationEquiv_restriction U W hWU D E F G k ω.val

end SmoothManifolds.MayerVietorisData.OpenForms

namespace SmoothManifolds.GenusTwoMayerVietoris
open MayerVietorisData
universe u
variable {A B C : Cochain.{u}} (E : ShortExact A B C)

/-- A single nonzero connecting value suffices when source and target are lines.
This does not assume that the preceding restriction has already vanished. -/
theorem connecting_bijective_of_nonzero (k : ℕ)
    (eC : C.H k ≃ₗ[ℝ] ℝ) (eA : A.H (k+1) ≃ₗ[ℝ] ℝ)
    (z : C.H k) (hz : E.delta k z ≠ 0) : Function.Bijective (E.delta k) := by
  let f : ℝ →ₗ[ℝ] ℝ := eA.toLinearMap.comp ((E.delta k).comp eC.symm.toLinearMap)
  have hm (t : ℝ) : f t = t * f 1 := by
    simpa only [smul_eq_mul, mul_one] using f.map_smul t 1
  have hv : f (eC z) ≠ 0 := by
    change eA (E.delta k (eC.symm (eC z))) ≠ 0
    rw [LinearEquiv.symm_apply_apply]
    exact fun h => hz (eA.injective (h.trans (map_zero eA).symm))
  have h1 : f 1 ≠ 0 := by
    intro h
    apply hv
    rw [hm, h, mul_zero]
  have hinj : Function.Injective f := by
    intro s t hst
    exact mul_right_cancel₀ h1 ((hm s).symm.trans (hst.trans (hm t)))
  have hsurj := LinearMap.surjective_of_injective hinj
  constructor
  · intro x y hxy
    apply eC.injective
    apply hinj
    change eA (E.delta k (eC.symm (eC x))) = eA (E.delta k (eC.symm (eC y)))
    simpa only [LinearEquiv.symm_apply_apply] using congrArg eA hxy
  · intro x
    obtain ⟨t, ht⟩ := hsurj (eA x)
    exact ⟨eC.symm t, eA.injective ht⟩

/-- A nonzero global class killed by the next restriction provides the
nonzero connecting value required by the preceding lemma. -/
theorem connecting_bijective_of_kernel_class (k : ℕ)
    (eC : C.H k ≃ₗ[ℝ] ℝ) (eA : A.H (k+1) ≃ₗ[ℝ] ℝ)
    (x : A.H (k+1)) (hx : x ≠ 0) (hr : E.r.onH (k+1) x = 0) :
    Function.Bijective (E.delta k) := by
  obtain ⟨z, hz⟩ := (E.exact_at_left k x).mp hr
  apply connecting_bijective_of_nonzero E k eC eA z
  rw [hz]
  exact hx

end SmoothManifolds.GenusTwoMayerVietoris

open private zeroCoefficient_smooth closedOfLocallyConstant
  from MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Algebra

namespace SmoothManifolds.GenusTwoOpenCohomology
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MayerVietorisData Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M} {C : CotangentBundle S}
  {B : ∀ k, FormBundle C k} {U : TopologicalSpace.Opens M}

theorem closed_zeroCoefficient_lc (K : Calculus C B) (D : OpenCalculus C B U)
    (ω : D.complex.closed 0) : IsLocallyConstant (zeroCoefficient (D.field 0 ω.val)) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro p
  obtain ⟨α, hα, he⟩ := OpenForms.exists_global_germ (B 0) U
    (D.field 0 ω.val) (OpenForms.field_smooth D 0 ω.val) p
  let f : M → ℝ := fun q => exteriorPower.zeroEquiv ℝ
    (Module.Dual ℝ (TangentSpace S q)) (α q)
  have hs : PartitionData.ScalarSmooth S.smoothStructure.val f :=
    zeroCoefficient_smooth α hα
  have hscalar : FormPullbackData.scalarField S f = α := by
    funext q
    exact (exteriorPower.zeroEquiv ℝ _).symm_apply_apply _
  have hd : ∀ᶠ q in 𝓝 p.val, dFunction S f hs q = 0 := by
    filter_upwards [he.eventually_nhds, U.isOpen.mem_nhds p.property] with q hq hqu
    have hD := OpenForms.restricted_derivative_eq_global K U
      (D.field 0 ω.val) (D.field 1 (D.complex.d 0 ω.val))
      (D.coordinates 0 ω.val) α hα ⟨q, hqu⟩ hq
    rw [show D.complex.d 0 ω.val = 0 from ω.property, map_zero] at hD
    have hz : K.D 0 α q = 0 := hD.symm
    have h := K.axioms.function_rule f hs q
    rw [hscalar, hz] at h
    have h' := congrArg (exteriorPower.oneEquiv ℝ
      (Module.Dual ℝ (TangentSpace S q))) h
    simpa only [map_zero, LinearEquiv.apply_symm_apply] using h'.symm
  have hc := scalar_constant_near C f hs p.val hd
  have hcoeff : ∀ᶠ q in 𝓝 p, f q.val = zeroCoefficient (D.field 0 ω.val) q := by
    filter_upwards [continuous_subtype_val.continuousAt.eventually he] with q hq
    change exteriorPower.zeroEquiv ℝ _ (α q.val) = _
    rw [hq]
    simp only [zeroExtend, dite_eq_left q.property]
    rfl
  filter_upwards [hcoeff, continuous_subtype_val.continuousAt.eventually hc] with q hq hqc
  exact hq.symm.trans (hqc.trans hcoeff.self_of_nhds)

/-- The actual constant restricted zero-form, obtained by restricting the
closed global constant. -/
def closedConstant (K : Calculus C B) (D : OpenCalculus C B U) (r : ℝ) :
    D.complex.closed 0 :=
  (OpenForms.globalRestriction K U D).onClosed 0
    (closedOfLocallyConstant K (LocallyConstant.const M r))

@[simp] theorem closedConstant_field (K : Calculus C B) (D : OpenCalculus C B U)
    (r : ℝ) (p : U) :
    D.field 0 (closedConstant K D r).val p =
      FormPullbackData.scalarField S (fun _ => r) p.val := by
  change D.field 0 ((OpenForms.globalRestriction K U D).map 0 _) p = _
  rw [OpenForms.globalRestriction_field]
  rfl

/-- Evaluation of the scalar coefficient of a closed restricted zero-form. -/
def closedZeroEvaluation (D : OpenCalculus C B U) (p : U) :
    D.complex.closed 0 →ₗ[ℝ] ℝ where
  toFun ω := zeroCoefficient (D.field 0 ω.val) p
  map_add' ω η := by
    simp only [zeroCoefficient, Submodule.coe_add, map_add, Pi.add_apply]
  map_smul' r ω := by
    simp only [zeroCoefficient, Submodule.coe_smul, map_smul, Pi.smul_apply,
      RingHom.id_apply]

/-- On a connected open domain, every closed zero-form is its one constant
coefficient. This uses the actual restricted derivative, not a model complex. -/
def closedZeroEvaluationEquiv (K : Calculus C B) (D : OpenCalculus C B U)
    [PreconnectedSpace U] (p : U) : D.complex.closed 0 ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective (closedZeroEvaluation D p) ⟨by
    intro ω η h
    apply Subtype.ext
    apply D.injective 0
    funext q
    apply (exteriorPower.zeroEquiv ℝ _).injective
    exact ((closed_zeroCoefficient_lc K D ω).apply_eq_of_preconnectedSpace q p).trans
      (h.trans ((closed_zeroCoefficient_lc K D η).apply_eq_of_preconnectedSpace p q)),
    by
      intro r
      refine ⟨closedConstant K D r, ?_⟩
      change exteriorPower.zeroEquiv ℝ _ (D.field 0 (closedConstant K D r).val p) = r
      rw [closedConstant_field]
      exact (exteriorPower.zeroEquiv ℝ _).apply_symm_apply r⟩

/-- There are no boundaries in degree zero of the nonnegative complex. -/
def classZeroEquiv (A : Cochain.{u}) : A.closed 0 ≃ₗ[ℝ] A.H 0 :=
  LinearEquiv.ofBijective (A.classOf 0) ⟨by
    intro ω η h
    have hz : (ω - η).val = 0 := (Submodule.Quotient.eq (A.boundaries 0)).mp h
    apply Subtype.ext
    exact sub_eq_zero.mp hz,
    A.class_surjective 0⟩

/-- The zeroth cohomology of any nonempty connected open domain is R,
with its map given by evaluation of the actual coefficient. -/
def h0ConnectedEquiv (K : Calculus C B) (D : OpenCalculus C B U)
    [PreconnectedSpace U] (p : U) : D.complex.H 0 ≃ₗ[ℝ] ℝ :=
  (classZeroEquiv D.complex).symm.trans (closedZeroEvaluationEquiv K D p)

@[simp] theorem h0ConnectedEquiv_class (K : Calculus C B)
    (D : OpenCalculus C B U) [PreconnectedSpace U] (p : U)
    (ω : D.complex.closed 0) :
    h0ConnectedEquiv K D p (D.complex.classOf 0 ω) =
      zeroCoefficient (D.field 0 ω.val) p := by
  change closedZeroEvaluationEquiv K D p
    ((classZeroEquiv D.complex).symm ((classZeroEquiv D.complex) ω)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

set_option maxHeartbeats 2500000 in
/-- Every overlap degree-zero class is the difference of actual side
constants when the overlap is connected and nonempty. -/
theorem degree_zero_difference_surjective (K : Calculus C B)
    {O : OpenCover M} (D : CoverComplex K O)
    [ConnectedSpace ↥(O.U ⊓ O.V)] :
    Function.Surjective (D.sequence.q.onH 0) := by
  intro x
  obtain ⟨ω, rfl⟩ := D.onOverlap.complex.class_surjective 0 x
  let p : ↥(O.U ⊓ O.V) := Classical.arbitrary _
  let r := zeroCoefficient (D.onOverlap.field 0 ω.val) p
  let β := closedConstant K D.onV r
  let b : (D.onU.complex.prod D.onV.complex).closed 0 :=
    ⟨(0, β.val), by
      change (D.onU.complex.d 0 0, D.onV.complex.d 0 β.val) = 0
      exact Prod.ext (map_zero _) β.property⟩
  refine ⟨(D.onU.complex.prod D.onV.complex).classOf 0 b, ?_⟩
  rw [ChainMap.onH_class]
  apply congrArg (D.onOverlap.complex.classOf 0)
  apply Subtype.ext
  apply D.onOverlap.injective 0
  funext q
  change D.onOverlap.field 0 (D.sequence.q.map 0 b.val) q = _
  rw [D.difference]
  change D.onV.field 0 β.val ⟨q.val, q.property.2⟩ -
    D.onU.field 0 0 ⟨q.val, q.property.1⟩ = _
  rw [closedConstant_field, map_zero, Pi.zero_apply, sub_zero]
  apply (exteriorPower.zeroEquiv ℝ _).injective
  simp only [FormPullbackData.scalarField, LinearEquiv.apply_symm_apply]
  change r = zeroCoefficient (D.onOverlap.field 0 ω.val) q
  exact (closed_zeroCoefficient_lc K D.onOverlap ω).apply_eq_of_preconnectedSpace p q

end SmoothManifolds.GenusTwoOpenCohomology

namespace SmoothManifolds.GenusTwoDeRhamGeometry
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
  GenusTwoData MayerVietorisData GenusTwoOpenCohomology

/-- The actual overlap, with its quotient-induced topology, is connected. -/
theorem surfaceOverlap_connectedSpace : ConnectedSpace ↥(surfaceCover.U ⊓ surfaceCover.V) := by
  apply isConnected_iff_connectedSpace.mp
  change IsConnected (((surfaceCover.U ⊓ surfaceCover.V : TopologicalSpace.Opens Surface) :
    Set Surface))
  rw [surfaceCover_overlap]
  exact collarRegion_connected

variable {S : SmoothManifold 2 .euclidean Surface} {C : CotangentBundle S}
  {B : ∀ k, FormBundle C k}

/-- All three degree-zero groups in the concrete surface cover are lines.
These are groups of the actual restricted smooth-form complexes. -/
theorem surface_cover_h0 (K : Calculus C B) (D : CoverComplex K surfaceCover) :
    Nonempty (D.onU.complex.H 0 ≃ₗ[ℝ] ℝ) ∧
    Nonempty (D.onV.complex.H 0 ≃ₗ[ℝ] ℝ) ∧
    Nonempty (D.onOverlap.complex.H 0 ≃ₗ[ℝ] ℝ) := by
  letI : ConnectedSpace ↥surfaceCover.U :=
    isConnected_iff_connectedSpace.mp (extendedSide_connected false)
  letI : ConnectedSpace ↥surfaceCover.V :=
    isConnected_iff_connectedSpace.mp (extendedSide_connected true)
  letI : ConnectedSpace ↥(surfaceCover.U ⊓ surfaceCover.V) := surfaceOverlap_connectedSpace
  exact ⟨⟨h0ConnectedEquiv K D.onU (Classical.arbitrary _)⟩,
    ⟨h0ConnectedEquiv K D.onV (Classical.arbitrary _)⟩,
    ⟨h0ConnectedEquiv K D.onOverlap (Classical.arbitrary _)⟩⟩

/-- The degree-zero difference is onto for every realization of the concrete
cover. In particular no extra surjectivity premise is needed in degree one. -/
theorem surface_difference_zero_surjective (K : Calculus C B)
    (D : CoverComplex K surfaceCover) :
    Function.Surjective (D.sequence.q.onH 0) := by
  letI : ConnectedSpace ↥(surfaceCover.U ⊓ surfaceCover.V) := surfaceOverlap_connectedSpace
  exact degree_zero_difference_surjective K D

/-- Restriction to the two actual extended sides is injective in degree one. -/
theorem surface_restriction_one_injective (K : Calculus C B)
    (D : CoverComplex K surfaceCover) :
    Function.Injective (D.sequence.r.onH 1) :=
  GenusTwoMayerVietoris.restriction_injective D.sequence 0
    (surface_difference_zero_surjective K D)

end SmoothManifolds.GenusTwoDeRhamGeometry

namespace SmoothManifolds.GenusTwoPeriods
open ModelData AtlasData TangentData DifferentialData BundleOperationsData CovectorData
  ExteriorData ExteriorDerivativeData DeRhamData FormPullbackData PathIntegrationData
  LocalIntegrationData GlobalIntegrationData OrientationData BoundaryData BoundaryOrientationData Set
universe u

def oneCovector {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (ω : Field S 1) : CovectorField S :=
  fun p => exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p)) (ω p)

/-- Exact intrinsic exterior one-forms have zero period on every closed path. -/
theorem exact_period_zero
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (ω : K.closed 1) (hω : K.classOf 1 ω = 0)
    (γ : ℝ → M) (s t : ℝ) (hγ : PiecewiseSmoothOn S γ s t) (hloop : γ s = γ t) :
    pathIntegral S (oneCovector ω.val.val) γ s t = 0 := by
  obtain ⟨φ, hφ⟩ := (DeRhamResults.class_zero_iff_exact K 1 ω).mp hω
  let f : M → ℝ := fun p => exteriorPower.zeroEquiv ℝ
    (Module.Dual ℝ (TangentSpace S p)) (φ.val p)
  have hf : PartitionData.ScalarSmooth S.smoothStructure.val f :=
    zeroCoefficient_smooth (C := C) (B := B) φ.val ((K.mem_forms _ _).mp φ.property)
  have hscalar : scalarField S f = φ.val := by
    funext p
    exact (exteriorPower.zeroEquiv ℝ _).symm_apply_apply _
  have hD : K.D 0 φ.val = ω.val.val := congrArg Subtype.val hφ
  have heq : oneCovector ω.val.val = dFunction S f hf := by
    funext p
    have h := K.axioms.function_rule f hf p
    rw [hscalar, hD] at h
    simpa only [oneCovector, LinearEquiv.apply_symm_apply] using
      congrArg (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))) h
  rw [heq, PathIntegration.integral_dFunction S f hf γ s t hγ, hloop, sub_self]

/-- Stokes gives zero integral for the actual restriction of any closed C¹ form.
No special support assumption is needed on a compact manifold. -/
theorem closed_boundary_integral_zero
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold (n+1) a M) (C : CotangentBundle S)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)) (A : CotangentBundle B)
    (hB : IsNaturalBoundary S B) (o : Orientation S) (q : Orientation B)
    (hq : IsInducedOrientation o q)
    (L : (p : intrinsicBoundary S) → TangentSpace B p →ₗ[ℝ] TangentSpace S p.val)
    (hL : ∀ p, IsDifferential B S Subtype.val p (L p))
    (I : CompactTopForm S → ℝ) (J : CompactTopForm B → ℝ)
    (hI : IsIntegral o I) (hJ : IsIntegral q J)
    (ω : Field S n) (hω : IsRegularField C 1 n ω)
    (hdω : HasExteriorDerivative C ω 0) :
    ∃ β : CompactTopForm B,
      β.field = pullbackField B S Subtype.val L ω ∧ J β = 0 := by
  obtain ⟨η, β, hη, _, hβ, he⟩ :=
    StokesResults.stokes S C B A hB o q hq L hL I J hI hJ ω hω
      (StokesResults.compact_support S n ω)
  refine ⟨β, hβ, ?_⟩
  rw [← he]
  exact StokesResults.integral_zero_field o I hI η
    (ExteriorDerivativeResults.derivative_unique C n ω η.field 0 hη hdω)

/-- A nonzero top-form integral detects a nonzero ordinary de Rham class
on a compact manifold with empty intrinsic boundary. -/
theorem integral_ne_zero_class_ne_zero
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold (n+1) a M) (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (K : Calculus C B)
    (o : Orientation S) (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (hempty : intrinsicBoundary S = ∅)
    (ω : K.closed (n+1)) (η : CompactTopForm S)
    (hη : η.field = ω.val.val) (hne : I η ≠ 0) : K.classOf (n+1) ω ≠ 0 := by
  intro hz
  obtain ⟨φ, hφ⟩ := (DeRhamResults.class_zero_iff_exact K (n+1) ω).mp hz
  have hsmooth : IsForm (B n) φ.val := (K.mem_forms _ _).mp φ.property
  have hreg := ExteriorDerivativeResults.smooth_regular C n (B n) φ.val 1 hsmooth
  have hD : K.D n φ.val = ω.val.val := congrArg Subtype.val hφ
  have hdη : HasExteriorDerivative C φ.val η.field := by
    rw [hη, ← hD]
    exact K.coordinates n φ.val hsmooth
  obtain ⟨⟨T, hT⟩, hq⟩ := BoundaryOrientations.boundary_orientation S o
  obtain ⟨q, ⟨hq, _⟩, _⟩ := hq T hT
  obtain ⟨A⟩ := BundleOperations.exists_cotangent T
  let L := differential T S Subtype.val hT.1
  have hL := differential_spec T S Subtype.val hT.1
  obtain ⟨J, hJ, _⟩ := GlobalIntegrationResults.exists_integral T q
  obtain ⟨σ, β, hσ, _, _, he⟩ := StokesResults.stokes S C T A hT o q hq L hL
    I J hI hJ φ.val hreg (StokesResults.compact_support S n φ.val)
  have hση : σ.field = η.field :=
    ExteriorDerivativeResults.derivative_unique C n φ.val σ.field η.field hσ hdη
  have hIση : I σ = I η := by
    simpa only [one_smul, one_mul] using hI.2.1 1 η σ (by simpa using hση)
  apply hne
  exact hIση.symm.trans (he.trans (StokesResults.empty_boundary_integral S T q J hJ hempty β))

end SmoothManifolds.GenusTwoPeriods

namespace SmoothManifolds.GenusTwoDeRhamGeometry
open ModelData SphereTorusData Set

/-- Projection of the actual collar to the one-dimensional standard flat torus. -/
def collarCircleProjection : C(collarRegion, FlatTorus 1) where
  toFun p _ := (collarHomeomorph p).1
  continuous_toFun := continuous_pi (fun _ => collarHomeomorph.continuous.fst)

/-- The middle circle of the actual signed collar. -/
def collarCircleSection : C(FlatTorus 1, collarRegion) where
  toFun z := collarHomeomorph.symm (z 0, ⟨0, by norm_num⟩)
  continuous_toFun := collarHomeomorph.symm.continuous.comp
    ((continuous_apply 0).prodMk continuous_const)

@[simp] theorem collarCircleProjection_section (z : FlatTorus 1) :
    collarCircleProjection (collarCircleSection z) = z := by
  funext i
  fin_cases i
  change (collarHomeomorph (collarHomeomorph.symm _)).1 = z 0
  rw [Homeomorph.apply_symm_apply]

/-- Multiplying the signed radius by a time in [0,1] stays inside the collar. -/
def collarContractInterval (t : unitInterval) (y : CollarInterval) : CollarInterval :=
  ⟨t.val * y.val, abs_lt.mp (by
    rw [abs_mul, abs_of_nonneg t.property.1]
    exact (mul_le_mul_of_nonneg_right t.property.2 (abs_nonneg y.val)).trans_lt
      (by simpa only [one_mul] using abs_lt.mpr y.property))⟩

/-- The actual collar retracts continuously onto its middle circle. -/
def collarCircleContraction : ContinuousMap.Homotopy
    (collarCircleSection.comp collarCircleProjection) (ContinuousMap.id collarRegion) where
  toFun z := collarHomeomorph.symm
    ((collarHomeomorph z.2).1, collarContractInterval z.1 (collarHomeomorph z.2).2)
  continuous_toFun := by
    apply collarHomeomorph.symm.continuous.comp
    apply Continuous.prodMk
    · exact collarHomeomorph.continuous.fst.comp continuous_snd
    · apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp (collarHomeomorph.continuous.snd.comp continuous_snd))
  map_zero_left p := by
    change collarHomeomorph.symm _ = collarHomeomorph.symm _
    congr 1
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact zero_mul _
  map_one_left p := by
    change collarHomeomorph.symm _ = p
    apply collarHomeomorph.injective
    rw [Homeomorph.apply_symm_apply]
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact one_mul _

/-- The two maps are homotopy inverses, with exactly the original collar topology. -/
theorem collarCircle_homotopyEquivalence :
    ContinuousMap.Homotopic (collarCircleSection.comp collarCircleProjection)
      (ContinuousMap.id collarRegion) ∧
    ContinuousMap.Homotopic (collarCircleProjection.comp collarCircleSection)
      (ContinuousMap.id (FlatTorus 1)) := by
  refine ⟨⟨collarCircleContraction⟩, ?_⟩
  have he : collarCircleProjection.comp collarCircleSection = ContinuousMap.id (FlatTorus 1) := by
    ext z i
    exact congrFun (collarCircleProjection_section z) i
  simpa only [he] using (ContinuousMap.Homotopic.refl (ContinuousMap.id (FlatTorus 1)))
end SmoothManifolds.GenusTwoDeRhamGeometry


namespace SmoothManifolds.GenusTwoMayerVietoris
open MayerVietorisData
universe u
variable {A B C : Cochain.{u}} (E : ShortExact A B C)

/-- A nonzero top class supported away from the punctured part can replace
an explicit calculation of the annulus connecting form. Exactness and the two
line identifications then prove the needed zero difference as a conclusion. -/
theorem punctured_torus_of_kernel_class
    (hQ0 : Function.Surjective (E.q.onH 0))
    (eC : C.H 1 ≃ₗ[ℝ] ℝ) (eA : A.H 2 ≃ₗ[ℝ] ℝ)
    [Subsingleton (C.H 2)]
    (x : A.H 2) (hx : x ≠ 0) (hr : E.r.onH 2 x = 0) :
    Nonempty (A.H 1 ≃ₗ[ℝ] B.H 1) ∧ Subsingleton (B.H 2) ∧ E.q.onH 1 = 0 := by
  have hδ := connecting_bijective_of_kernel_class E 1 eC eA x hx hr
  have hq := difference_eq_zero_of_injective_delta E 1 hδ.1
  exact ⟨⟨restrictionEquiv E 0 hQ0 hq⟩, middle_subsingleton E 1 hδ.2, hq⟩

end SmoothManifolds.GenusTwoMayerVietoris

namespace SmoothManifolds.GenusTwoOpenCohomology
open ModelData AtlasData MapData TangentData DifferentialData BundleOperationsData
  CovectorData ExteriorData ExteriorDerivativeData DeRhamData MayerVietorisData Set Filter
open scoped Topology
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {U : TopologicalSpace.Opens M}
  {R : SmoothManifold n a U}

/-- The actual pullback along the inclusion, with ambient restricted fibers. -/
def intrinsicRestrictedPullback
    (L : (p : U) → TangentSpace R p →ₗ[ℝ] TangentSpace S p.val) (k : ℕ) :
    RestrictedField S U k →ₗ[ℝ] Field R k where
  toFun ω p := FormPullbackData.fiberPullback
    (V := TangentSpace R p) (W := TangentSpace S p.val) k (L p) (ω p)
  map_add' ω η := by
    funext p
    exact map_add (FormPullbackData.fiberPullback
      (V := TangentSpace R p) (W := TangentSpace S p.val) k (L p)) (ω p) (η p)
  map_smul' r ω := by
    funext p
    exact map_smul (FormPullbackData.fiberPullback
      (V := TangentSpace R p) (W := TangentSpace S p.val) k (L p)) r (ω p)

theorem intrinsicRestrictedPullback_zeroExtend
    (L : (p : U) → TangentSpace R p →ₗ[ℝ] TangentSpace S p.val) (k : ℕ)
    (ω : RestrictedField S U k) :
    intrinsicRestrictedPullback L k ω =
      FormPullbackData.pullbackField R S Subtype.val L (zeroExtend ω) := by
  funext p
  simp [intrinsicRestrictedPullback, FormPullbackData.pullbackField, zeroExtend, p.property]

/-- Genuine ambient restricted forms pull back to all-point smooth intrinsic forms. -/
theorem intrinsicRestrictedPullback_smooth
    (C : CotangentBundle S) (A : CotangentBundle R) (k : ℕ)
    (B : FormBundle C k) (E : FormBundle A k)
    (hinc : IsSmoothMap R S Subtype.val)
    (L : (p : U) → TangentSpace R p →ₗ[ℝ] TangentSpace S p.val)
    (hL : ∀ p, IsDifferential R S Subtype.val p (L p))
    (ω : RestrictedField S U k) (hω : IsRestrictedForm B U ω) :
    IsForm E (intrinsicRestrictedPullback L k ω) := by
  let := (cotangentSpace A).topology
  let := E.space.topology
  intro p
  obtain ⟨α, hα, hg⟩ := OpenForms.exists_global_germ B U ω hω p
  have hβ := FormPullbackResults.pullback_smooth R S A C Subtype.val hinc L hL k E B α hα
  apply manifoldContDiffAt_congr (hβ p)
  have he : ∀ᶠ q : U in 𝓝 p, α q.val = zeroExtend ω q.val :=
    (show Tendsto (Subtype.val : U → M) (𝓝 p) (𝓝 p.val) from
      continuous_subtype_val.continuousAt).eventually hg
  filter_upwards [he] with q hq
  apply congrArg (fun v => (⟨q, v⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
    (fun z => Fiber (TangentSpace R z) k)))
  change FormPullbackData.fiberPullback (V := TangentSpace R q)
    (W := TangentSpace S q.val) k (L q) (α q.val) =
    FormPullbackData.fiberPullback (V := TangentSpace R q)
      (W := TangentSpace S q.val) k (L q) (ω q)
  rw [hq]
  simp [zeroExtend, q.property]

/-- In the restricted ambient chart the inclusion Jacobian is literally identity,
so every increasing coefficient is preserved, in every degree. -/
theorem intrinsicRestrictedPullback_coefficients
    (C : CotangentBundle S) (A : CotangentBundle R)
    (hinc : IsSmoothMap R S Subtype.val)
    (L : (p : U) → TangentSpace R p →ₗ[ℝ] TangentSpace S p.val)
    (hL : ∀ p, IsDifferential R S Subtype.val p (L p))
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hne : Nonempty U)
    (hcr : c.subtypeRestr (s := U) hne ∈ R.smoothStructure.val)
    (k : ℕ) (ω : RestrictedField S U k) (p : U)
    (hp : p.val ∈ c.source) (I : Index n k) :
    coefficients A k (c.subtypeRestr (s := U) hne) hcr
        (intrinsicRestrictedPullback L k ω) ⟨p, by simpa using hp⟩ I =
      coefficients C k c hc (zeroExtend ω) ⟨p.val, hp⟩ I := by
  let cr : ModelChart n a U := c.subtypeRestr (s := U) hne
  have hpr : p ∈ cr.source := by simpa [cr] using hp
  have hK (v : TangentSpace R p) :
      C.tangent.fiberCoordinates.equiv c hc p.val hp (L p v) =
        ContinuousLinearMap.id ℝ (Euclidean n)
          (A.tangent.fiberCoordinates.equiv cr hcr p hpr v) := by
    have hj := differential_jacobian R S Subtype.val hinc p (L p) (hL p)
      cr c hcr hc hpr hp
      (A.tangent.fiberCoordinates.equiv cr hcr p hpr)
      (C.tangent.fiberCoordinates.equiv c hc p.val hp)
      (A.tangent.fiberCoordinates.isCoordinates cr hcr p hpr)
      (C.tangent.fiberCoordinates.isCoordinates c hc p.val hp)
      univ id isOpen_univ (mem_univ _) contDiffOn_id
      (Filter.Eventually.of_forall (fun _ => rfl)) v
    simpa using hj
  have he := ExteriorDerivativeResults.coefficient_pullback_of_jacobian R S A C
    Subtype.val L cr hcr c hc p hpr hp (ContinuousLinearMap.id ℝ (Euclidean n))
    hK k (zeroExtend ω)
  rw [← intrinsicRestrictedPullback_zeroExtend] at he
  have he' :
      (fun J => coefficients A k cr hcr (intrinsicRestrictedPullback L k ω) ⟨p,hpr⟩ J) =
        (fun J => coefficients C k c hc (zeroExtend ω) ⟨p.val,hp⟩ J) := by
    apply (ExteriorDerivativeResults.Euclidean.coefficientAlternatingEquiv n k).injective
    exact he.trans (by ext v; rfl)
  exact congrFun he' I

/-- Smoothness is reflected as well as preserved by the genuine inclusion
pullback on its induced open manifold. -/
theorem intrinsicRestrictedPullback_smooth_iff
    (C : CotangentBundle S) (A : CotangentBundle R) (k : ℕ)
    (B : FormBundle C k) (E : FormBundle A k)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U U.isOpen))
    (hinc : IsSmoothMap R S Subtype.val)
    (L : (p : U) → TangentSpace R p →ₗ[ℝ] TangentSpace S p.val)
    (hL : ∀ p, IsDifferential R S Subtype.val p (L p))
    (ω : RestrictedField S U k) :
    IsForm E (intrinsicRestrictedPullback L k ω) ↔ IsRestrictedForm B U ω := by
  refine ⟨?_, intrinsicRestrictedPullback_smooth C A k B E hinc L hL ω⟩
  intro hβ
  let := (cotangentSpace C).topology
  let := B.space.topology
  let := (cotangentSpace A).topology
  let := E.space.topology
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
  let cr : ModelChart n a U := c.subtypeRestr (s := U) ⟨p⟩
  have hsub : openSubsetAtlas S.smoothStructure.val U U.isOpen ⊆ R.smoothStructure.val := by
    rw [hR]
    exact subset_maximalExtension
      (openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _ S.smoothStructure.property.1 U U.isOpen)
  have hcr : cr ∈ R.smoothStructure.val := hsub ⟨⟨p⟩, c, hc, rfl⟩
  have hpcr : p ∈ cr.source := by simpa [cr] using hp
  let β := intrinsicRestrictedPullback L k ω
  let coordsR : U → Euclidean (n.choose k) := fun q =>
    ((E.space.bundle.trivialization ⟨cr,hcr⟩)
      (⟨q, β q⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
        (fun q => Fiber (TangentSpace R q) k))).2
  have hpB : p.val ∈ B.space.bundle.baseSet ⟨c,hc⟩ := by
    rw [B.baseSet, Covectors.cotangent_baseSet]
    exact hp
  have hpE : p ∈ E.space.bundle.baseSet ⟨cr,hcr⟩ := by
    rw [E.baseSet, Covectors.cotangent_baseSet]
    exact hpcr
  have hsR : FrameData.VectorSmoothAt R.smoothStructure.val coordsR p := by
    apply FrameData.VectorSmoothAt.comp
      (f := fun z : Bundle.TotalSpace (Euclidean (n.choose k))
        (fun q => Fiber (TangentSpace R q) k) =>
          ((E.space.bundle.trivialization ⟨cr,hcr⟩) z).2)
      (g := fun q : U => (⟨q, β q⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
        (fun q => Fiber (TangentSpace R q) k)))
      E.space.bundle.totalManifold.smoothStructure.property.1.1
    · exact Frames.trivializationCoordinates_smoothAt E.space.bundle ⟨cr,hcr⟩
        ⟨p,β p⟩ hpE
    · exact hβ p
  let eA : Euclidean (n.choose k) ≃ₗ[ℝ] (Index n k → ℝ) :=
    E.modelEquiv.symm.trans ((Pi.basisFun ℝ (Fin n)).exteriorPower k).equivFun
  let eC : Euclidean (n.choose k) ≃ₗ[ℝ] (Index n k → ℝ) :=
    B.modelEquiv.symm.trans ((Pi.basisFun ℝ (Fin n)).exteriorPower k).equivFun
  have hsA : FrameData.VectorSmoothAt R.smoothStructure.val (fun q => eA (coordsR q)) p :=
    (ExteriorAlgebraResults.vectorSmoothAt_equiv_iff _ eA coordsR p).mpr hsR
  have hsOpen : FrameData.VectorSmoothAt
      (openSubsetAtlas S.smoothStructure.val U U.isOpen) (fun q => eA (coordsR q)) p :=
    ⟨hsA.1, fun d hd => hsA.2 d (hsub hd)⟩
  apply Frames.smoothAt_of_sectionCoordinates B.space.bundle U U.isOpen ⟨c,hc⟩ ω p hpB
  apply (ExteriorAlgebraResults.vectorSmoothAt_equiv_iff _ eC _ p).mp
  apply hsOpen.congr
  have hn : ∀ᶠ q : U in 𝓝 p, q.val ∈ c.source :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hp)
  filter_upwards [hn] with q hq
  have hqr : q ∈ cr.source := by simpa [cr] using hq
  have hr := ExteriorAlgebraResults.coefficients_coordinates A E cr hcr β ⟨q,hqr⟩
  have hs := ExteriorAlgebraResults.coefficients_coordinates C B c hc (zeroExtend ω) ⟨q.val,hq⟩
  change eA (coordsR q) = eC (Frames.sectionCoordinates B.space.bundle U ⟨c,hc⟩ ω q)
  have hr' : (fun I => coefficients A k cr hcr β ⟨q,hqr⟩ I) = eA (coordsR q) := hr
  have hs' : (fun I => coefficients C k c hc (zeroExtend ω) ⟨q.val,hq⟩ I) =
      eC (Frames.sectionCoordinates B.space.bundle U ⟨c,hc⟩ ω q) := by
    simpa [eC, LinearEquiv.trans_apply, Frames.sectionCoordinates,
      zeroExtend, q.property] using hs
  rw [← hr', ← hs']
  funext I
  exact intrinsicRestrictedPullback_coefficients C A hinc L hL c hc ⟨p⟩ hcr k ω q hq I

/-- The intrinsic derivative of a pulled restricted form is the pullback of its
actual restricted derivative. All comparisons use genuine smooth local germs. -/
theorem intrinsicRestrictedPullback_derivative
    {C : CotangentBundle S} {A : CotangentBundle R}
    {B : ∀ k, FormBundle C k} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E)
    (hinc : IsSmoothMap R S Subtype.val)
    (L : (p : U) → TangentSpace R p →ₗ[ℝ] TangentSpace S p.val)
    (hL : ∀ p, IsDifferential R S Subtype.val p (L p))
    (k : ℕ) (ω : RestrictedField S U k) (η : RestrictedField S U (k+1))
    (hω : IsRestrictedForm (B k) U ω) (hη : HasRestrictedDerivative C U ω η) :
    J.D k (intrinsicRestrictedPullback L k ω) =
      intrinsicRestrictedPullback L (k+1) η := by
  funext p
  obtain ⟨α,hα,hg⟩ := OpenForms.exists_global_germ (B k) U ω hω p
  have hβ := FormPullbackResults.pullback_smooth R S A C Subtype.val hinc L hL
    k (E k) (B k) α hα
  have hω' := intrinsicRestrictedPullback_smooth C A k (B k) (E k) hinc L hL ω hω
  have he : ∀ᶠ q : U in 𝓝 p,
      intrinsicRestrictedPullback L k ω q =
        FormPullbackData.pullbackField R S Subtype.val L α q := by
    have hh : ∀ᶠ q : U in 𝓝 p, α q.val = zeroExtend ω q.val :=
      (show Tendsto (Subtype.val : U → M) (𝓝 p) (𝓝 p.val) from
        continuous_subtype_val.continuousAt).eventually hg
    filter_upwards [hh] with q hq
    change FormPullbackData.fiberPullback (V := TangentSpace R q)
      (W := TangentSpace S q.val) k (L q) (ω q) =
      FormPullbackData.fiberPullback (V := TangentSpace R q)
        (W := TangentSpace S q.val) k (L q) (α q.val)
    rw [hq]
    simp [zeroExtend, q.property]
  rw [ExteriorDerivativeResults.axioms_locality A E J.D J.axioms k _ _ hω' hβ p he]
  rw [← ExteriorDerivativeResults.smooth_naturality R S A C E B J.D K.D
    J.axioms K.axioms Subtype.val hinc L hL k α hα]
  change FormPullbackData.fiberPullback (V := TangentSpace R p)
      (W := TangentSpace S p.val) (k+1) (L p) (K.D k α p.val) =
    FormPullbackData.fiberPullback (V := TangentSpace R p)
      (W := TangentSpace S p.val) (k+1) (L p) (η p)
  rw [OpenForms.restricted_derivative_eq_global K U ω η hη α hα p hg]

/-- Fiberwise pullback along genuine tangent equivalences is a linear
isomorphism on all fields, prior to imposing smoothness. -/
def intrinsicRestrictedFieldEquiv
    (F : (p : U) → TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val) (k : ℕ) :
    RestrictedField S U k ≃ₗ[ℝ] Field R k :=
  LinearEquiv.piCongrRight (fun p => BundleOperations.exteriorEquiv k (F p).dualMap)

@[simp] theorem intrinsicRestrictedFieldEquiv_apply
    (F : (p : U) → TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val) (k : ℕ)
    (ω : RestrictedField S U k) :
    intrinsicRestrictedFieldEquiv F k ω =
      intrinsicRestrictedPullback (fun p => (F p).toLinearMap) k ω := rfl

/-- The intrinsic open manifold complex receives the actual inclusion pullback. -/
def intrinsicOpenPullChain
    {C : CotangentBundle S} {A : CotangentBundle R}
    {B : ∀ k, FormBundle C k} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E)
    (hinc : IsSmoothMap R S Subtype.val)
    (L : (p : U) → TangentSpace R p →ₗ[ℝ] TangentSpace S p.val)
    (hL : ∀ p, IsDifferential R S Subtype.val p (L p))
    (D : OpenCalculus C B U) : ChainMap D.complex (globalComplex J) where
  map k := {
    toFun ω := ⟨intrinsicRestrictedPullback L k (D.field k ω),
      (J.mem_forms k _).mpr (intrinsicRestrictedPullback_smooth C A k (B k) (E k)
        hinc L hL (D.field k ω) (OpenForms.field_smooth D k ω))⟩
    map_add' x y := by
      apply Subtype.ext
      change intrinsicRestrictedPullback L k (D.field k (x+y)) =
        intrinsicRestrictedPullback L k (D.field k x) + intrinsicRestrictedPullback L k (D.field k y)
      simp only [map_add]
    map_smul' r x := by
      apply Subtype.ext
      change intrinsicRestrictedPullback L k (D.field k (r • x)) =
        r • intrinsicRestrictedPullback L k (D.field k x)
      simp only [map_smul] }
  comm k ω := by
    apply Subtype.ext
    exact intrinsicRestrictedPullback_derivative K J hinc L hL k _ _
      (OpenForms.field_smooth D k ω) (D.coordinates k ω)

/-- Every full restricted realization is degreewise canonically isomorphic to
the genuine intrinsic open-manifold complex. -/
def intrinsicOpenEquiv
    {C : CotangentBundle S} {A : CotangentBundle R}
    {B : ∀ k, FormBundle C k} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U U.isOpen))
    (hinc : IsSmoothMap R S Subtype.val)
    (F : (p : U) → TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
    (hF : ∀ p, IsDifferential R S Subtype.val p (F p).toLinearMap)
    (D : OpenCalculus C B U) (k : ℕ) : D.complex.Obj k ≃ₗ[ℝ] J.forms k := by
  let f := (intrinsicOpenPullChain K J hinc (fun p => (F p).toLinearMap) hF D).map k
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply D.injective k
    apply (intrinsicRestrictedFieldEquiv F k).injective
    exact congrArg Subtype.val hxy
  · intro β
    let ω := (intrinsicRestrictedFieldEquiv F k).symm β.val
    have hω : IsRestrictedForm (B k) U ω := by
      apply (intrinsicRestrictedPullback_smooth_iff C A k (B k) (E k) hR hinc
        (fun p => (F p).toLinearMap) hF ω).mp
      have he : intrinsicRestrictedPullback (fun p => (F p).toLinearMap) k ω = β.val :=
        (intrinsicRestrictedFieldEquiv F k).apply_symm_apply β.val
      rw [he]
      exact (J.mem_forms k β.val).mp β.property
    obtain ⟨x,hx⟩ := (D.range_smooth k ω).mp hω
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change intrinsicRestrictedPullback (fun p => (F p).toLinearMap) k (D.field k x) = β.val
    rw [hx]
    exact (intrinsicRestrictedFieldEquiv F k).apply_symm_apply β.val


/-- A degreewise invertible chain map has the actual inverse chain map. -/
def inverseChainOfBijective {X Y : Cochain.{u}} (f : ChainMap X Y)
    (hf : ∀ k, Function.Bijective (f.map k)) : ChainMap Y X where
  map k := (LinearEquiv.ofBijective (f.map k) (hf k)).symm.toLinearMap
  comm k y := by
    let e := fun j => LinearEquiv.ofBijective (f.map j) (hf j)
    apply (e (k+1)).injective
    change f.map (k+1) (X.d k ((e k).symm y)) = e (k+1) ((e (k+1)).symm (Y.d k y))
    rw [← f.comm, LinearEquiv.apply_symm_apply]
    change Y.d k (e k ((e k).symm y)) = Y.d k y
    rw [LinearEquiv.apply_symm_apply]

/-- A degreewise cochain isomorphism induces the quotient isomorphism in every degree. -/
def cohomologyEquivOfBijective {X Y : Cochain.{u}} (f : ChainMap X Y)
    (hf : ∀ k, Function.Bijective (f.map k)) (k : ℕ) : X.H k ≃ₗ[ℝ] Y.H k where
  toLinearMap := f.onH k
  invFun := (inverseChainOfBijective f hf).onH k
  left_inv := by
    intro x
    obtain ⟨ω,rfl⟩ := X.class_surjective k x
    change (inverseChainOfBijective f hf).onH k (f.onH k (X.classOf k ω)) = X.classOf k ω
    simp only [ChainMap.onH_class]
    apply congrArg (X.classOf k)
    apply Subtype.ext
    exact (LinearEquiv.ofBijective (f.map k) (hf k)).symm_apply_apply ω.val
  right_inv := by
    intro y
    obtain ⟨ω,rfl⟩ := Y.class_surjective k y
    change f.onH k ((inverseChainOfBijective f hf).onH k (Y.classOf k ω)) = Y.classOf k ω
    simp only [ChainMap.onH_class]
    apply congrArg (Y.classOf k)
    apply Subtype.ext
    exact (LinearEquiv.ofBijective (f.map k) (hf k)).apply_symm_apply ω.val

/-- The full open cohomology equals the intrinsic cohomology of the induced
open submanifold, through the actual tangent inclusion. -/
def intrinsicOpenHEquiv
    {C : CotangentBundle S} {A : CotangentBundle R}
    {B : ∀ k, FormBundle C k} {E : ∀ k, FormBundle A k}
    (K : Calculus C B) (J : Calculus A E)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U U.isOpen))
    (hinc : IsSmoothMap R S Subtype.val)
    (F : (p : U) → TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
    (hF : ∀ p, IsDifferential R S Subtype.val p (F p).toLinearMap)
    (D : OpenCalculus C B U) (k : ℕ) : D.complex.H k ≃ₗ[ℝ] J.Cohomology k :=
  cohomologyEquivOfBijective
    (intrinsicOpenPullChain K J hinc (fun p => (F p).toLinearMap) hF D)
    (fun j => (intrinsicOpenEquiv K J hR hinc F hF D j).bijective) k

end SmoothManifolds.GenusTwoOpenCohomology





section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SmoothManifolds.GenusTwoMayerVietoris
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
  MayerVietorisData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  {K : Calculus C B} {O : OpenCover M}

/-- The cohomology restriction is exactly the pair of genuine open restrictions,
for every full realization of the cover sequence. -/
theorem restriction_onH (D : CoverComplex K O) (k : ℕ) (x : K.Cohomology k) :
    D.onU.complex.productHEquiv D.onV.complex k (D.sequence.r.onH k x) =
      ((OpenForms.globalRestriction K O.U D.onU).onH k x,
        (OpenForms.globalRestriction K O.V D.onV).onH k x) := by
  obtain ⟨ω, rfl⟩ := (globalComplex K).class_surjective k x
  apply Prod.ext
  · change (ChainMap.fst _ _).onH k (D.sequence.r.onH k _) = _
    simp only [ChainMap.onH_class]
    apply congrArg (D.onU.complex.classOf k)
    apply Subtype.ext
    apply D.onU.injective k
    funext p
    change D.onU.field k (D.sequence.r.map k ω.val).1 p = _
    change D.onU.field k (D.sequence.r.map k ω.val).1 p =
      D.onU.field k ((OpenForms.globalRestriction K O.U D.onU).map k ω.val) p
    exact (D.restriction_U k ω.val p).trans
      (congrFun (OpenForms.globalRestriction_field K O.U D.onU k ω.val) p).symm
  · change (ChainMap.snd _ _).onH k (D.sequence.r.onH k _) = _
    simp only [ChainMap.onH_class]
    apply congrArg (D.onV.complex.classOf k)
    apply Subtype.ext
    apply D.onV.injective k
    funext p
    change D.onV.field k (D.sequence.r.map k ω.val).2 p = _
    change D.onV.field k (D.sequence.r.map k ω.val).2 p =
      D.onV.field k ((OpenForms.globalRestriction K O.V D.onV).map k ω.val) p
    exact (D.restriction_V k ω.val p).trans
      (congrFun (OpenForms.globalRestriction_field K O.V D.onV k ω.val) p).symm

/-- A class represented by a form vanishing on U restricts to zero there.
No condition on a chosen model of the form complex is imposed. -/
theorem globalRestriction_class_eq_zero
    (U : TopologicalSpace.Opens M) (D : OpenCalculus C B U) (k : ℕ) (ω : K.closed k)
    (hω : ∀ p : U, ω.val.val p.val = 0) :
    (OpenForms.globalRestriction K U D).onH k (K.classOf k ω) = 0 := by
  change (OpenForms.globalRestriction K U D).onH k ((globalComplex K).classOf k ω) = 0
  rw [ChainMap.onH_class]
  have hz : (OpenForms.globalRestriction K U D).onClosed k ω = 0 := by
    apply Subtype.ext
    apply D.injective k
    funext p
    change D.field k ((OpenForms.globalRestriction K U D).map k ω.val) p = D.field k 0 p
    rw [map_zero, Pi.zero_apply, OpenForms.globalRestriction_field]
    exact hω p
  rw [hz, map_zero]

/-- A disk-supported class is in the global restriction kernel as soon as
its other cover side has zero cohomology in that degree. -/
theorem cover_class_in_kernel (D : CoverComplex K O) (k : ℕ)
    [Subsingleton (D.onV.complex.H k)] (ω : K.closed k)
    (hω : ∀ p : O.U, ω.val.val p.val = 0) :
    D.sequence.r.onH k (K.classOf k ω) = 0 := by
  apply (D.onU.complex.productHEquiv D.onV.complex k).injective
  rw [restriction_onH, map_zero]
  apply Prod.ext
  · exact globalRestriction_class_eq_zero O.U D.onU k ω hω
  · exact Subsingleton.elim _ _
end SmoothManifolds.GenusTwoMayerVietoris

end

namespace SmoothManifolds.GenusTwoHomotopyCohomology
open ModelData AtlasData MapData TangentData DifferentialData BundleOperationsData
  CovectorData ExteriorData DeRhamData InteriorHomotopyData
universe u
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  (S : SmoothManifold n a M) (T : SmoothManifold m b N)
  (C : CotangentBundle S) (A : CotangentBundle T)
  (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
  (K : Calculus C B) (J : Calculus A E)

/-- Smooth maps inverse up to continuous homotopy induce inverse de Rham maps. -/
theorem smooth_homotopy_equivalence
    (f : M → N) (g : N → M) (hf : IsSmoothMap S T f) (hg : IsSmoothMap T S g)
    (hgf : ∃ H : HomotopyTime × M → M, Continuous H ∧
      (∀ x, H (timeZero, x) = g (f x)) ∧ (∀ x, H (timeOne, x) = x))
    (hfg : ∃ H : HomotopyTime × N → N, Continuous H ∧
      (∀ x, H (timeZero, x) = f (g x)) ∧ (∀ x, H (timeOne, x) = x))
    (k : ℕ) : Nonempty (K.Cohomology k ≃ₗ[ℝ] J.Cohomology k) := by
  let Lf := differential S T f hf
  let Lg := differential T S g hg
  have hLf := differential_spec S T f hf
  have hLg := differential_spec T S g hg
  have hcompM : IsSmoothMap S S (g ∘ f) :=
    manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ T.smoothStructure.property.1.1 f g hf hg
  have hcompN : IsSmoothMap T T (f ∘ g) :=
    manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ S.smoothStructure.property.1.1 g f hg hf
  let LM := differential S S (g ∘ f) hcompM
  let LN := differential T T (f ∘ g) hcompN
  have hLM := differential_spec S S (g ∘ f) hcompM
  have hLN := differential_spec T T (f ∘ g) hcompN
  obtain ⟨F, hF⟩ := DeRhamResults.pullback_exists S T C A B E K J f hf Lf hLf
  obtain ⟨G, hG⟩ := DeRhamResults.pullback_exists T S A C E B J K g hg Lg hLg
  obtain ⟨PM, hPM⟩ := DeRhamResults.pullback_exists S S C C B B K K
    (g ∘ f) hcompM LM hLM
  obtain ⟨PN, hPN⟩ := DeRhamResults.pullback_exists T T A A E E J J
    (f ∘ g) hcompN LN hLN
  have hIdM : IsSmoothMap S S id :=
    manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1
  have hIdN : IsSmoothMap T T id :=
    manifoldContDiff_id (⊤ : ℕ∞) _ T.smoothStructure.property.1
  obtain ⟨IM, hIM⟩ := DeRhamResults.pullback_exists S S C C B B K K
    id hIdM (fun _ => LinearMap.id) (differential_id S)
  obtain ⟨IN, hIN⟩ := DeRhamResults.pullback_exists T T A A E E J J
    id hIdN (fun _ => LinearMap.id) (differential_id T)
  have hM := HomotopyResults.homotopy_invariance S S C B C B K K
    (g ∘ f) id hcompM hIdM hgf LM (fun _ => LinearMap.id)
    hLM (differential_id S) PM IM hPM hIM
  have hN := HomotopyResults.homotopy_invariance T T A E A E J J
    (f ∘ g) id hcompN hIdN hfg LN (fun _ => LinearMap.id)
    hLN (differential_id T) PN IN hPN hIN
  have hFG (x : K.Cohomology k) : F k (G k x) = x := by
    rw [← DeRhamResults.pullback_comp S T S C A C B E B K J K
      f g hf hg Lf Lg LM hLf hLg hLM F G PM hF hG hPM k x, hM k]
    exact DeRhamResults.pullback_id S C B K (fun _ => LinearMap.id)
      (differential_id S) IM hIM k x
  have hGF (x : J.Cohomology k) : G k (F k x) = x := by
    rw [← DeRhamResults.pullback_comp T S T A C A E B E J K J
      g f hg hf Lg Lf LN hLg hLf hLN G F PN hG hF hPN k x, hN k]
    exact DeRhamResults.pullback_id T A E J (fun _ => LinearMap.id)
      (differential_id T) IN hIN k x
  exact ⟨{ toLinearMap := G k, invFun := F k, left_inv := hFG, right_inv := hGF }⟩

/-- Ordinary continuous homotopy equivalences preserve the full intrinsic
real de Rham cohomology, for any supplied realizations of the calculi. -/
theorem continuous_homotopy_equivalence
    (f : C(M, N)) (g : C(N, M))
    (hgf : (g.comp f).Homotopic (ContinuousMap.id M))
    (hfg : (f.comp g).Homotopic (ContinuousMap.id N))
    (k : ℕ) : Nonempty (K.Cohomology k ≃ₗ[ℝ] J.Cohomology k) := by
  obtain ⟨f', hf', Hf, hHf, hHf0, hHf1⟩ :=
    SmoothingHomotopies.continuous_map_homotopic_smooth S T f f.continuous
  obtain ⟨g', hg', Hg, hHg, hHg0, hHg1⟩ :=
    SmoothingHomotopies.continuous_map_homotopic_smooth T S g g.continuous
  let F : C(M, N) := ⟨f', continuous_iff_continuousAt.mpr (fun x => (hf' x).1)⟩
  let G : C(N, M) := ⟨g', continuous_iff_continuousAt.mpr (fun x => (hg' x).1)⟩
  have hfhom : f.Homotopic F :=
    ⟨{ toFun := Hf, continuous_toFun := hHf, map_zero_left := hHf0, map_one_left := hHf1 }⟩
  have hghom : g.Homotopic G :=
    ⟨{ toFun := Hg, continuous_toFun := hHg, map_zero_left := hHg0, map_one_left := hHg1 }⟩
  obtain ⟨HM⟩ := (hghom.comp hfhom).symm.trans hgf
  obtain ⟨HN⟩ := (hfhom.comp hghom).symm.trans hfg
  exact smooth_homotopy_equivalence S T C A B E K J f' g' hf' hg'
    ⟨HM, HM.continuous_toFun, HM.map_zero_left, HM.map_one_left⟩
    ⟨HN, HN.continuous_toFun, HN.map_zero_left, HN.map_one_left⟩ k


/-- Version with explicit continuous homotopies in the shared time interval. -/
theorem continuous_homotopy_equivalence_of_homotopies
    (f : M → N) (g : N → M) (hf : Continuous f) (hg : Continuous g)
    (hgf : ∃ H : HomotopyTime × M → M, Continuous H ∧
      (∀ x, H (timeZero, x) = g (f x)) ∧ (∀ x, H (timeOne, x) = x))
    (hfg : ∃ H : HomotopyTime × N → N, Continuous H ∧
      (∀ x, H (timeZero, x) = f (g x)) ∧ (∀ x, H (timeOne, x) = x))
    (k : ℕ) : Nonempty (K.Cohomology k ≃ₗ[ℝ] J.Cohomology k) := by
  obtain ⟨HM, hHM, hHM0, hHM1⟩ := hgf
  obtain ⟨HN, hHN, hHN0, hHN1⟩ := hfg
  apply continuous_homotopy_equivalence S T C A B E K J ⟨f, hf⟩ ⟨g, hg⟩
  · exact ⟨{ toFun := HM, continuous_toFun := hHM, map_zero_left := hHM0, map_one_left := hHM1 }⟩
  · exact ⟨{ toFun := HN, continuous_toFun := hHN, map_zero_left := hHN0, map_one_left := hHN1 }⟩

/-- In particular, every actual homeomorphism of realized manifolds preserves
ordinary intrinsic de Rham cohomology. -/
theorem homeomorphism_equivalence (h : M ≃ₜ N) (k : ℕ) :
    Nonempty (K.Cohomology k ≃ₗ[ℝ] J.Cohomology k) := by
  apply continuous_homotopy_equivalence S T C A B E K J
    (h : C(M, N)) (h.symm : C(N, M))
  · have he : (h.symm : C(N, M)).comp (h : C(M, N)) = ContinuousMap.id M := by
      ext x
      exact h.symm_apply_apply x
    rw [he]
  · have he : (h : C(M, N)).comp (h.symm : C(N, M)) = ContinuousMap.id N := by
      ext x
      exact h.apply_symm_apply x
    rw [he]

end SmoothManifolds.GenusTwoHomotopyCohomology

namespace SmoothManifolds.GenusTwoOpenCohomology
open ModelData AtlasData MapData TangentData DifferentialData BundleOperationsData
  CovectorData ExteriorData DeRhamData MayerVietorisData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {U : TopologicalSpace.Opens M}

/-- Every actual open de Rham realization has an intrinsic induced-open
calculus with canonically isomorphic cohomology, without extra hypotheses. -/
theorem open_intrinsic_cohomology_exists
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (D : OpenCalculus C B U) :
    ∃ (R : SmoothManifold n a U) (A : CotangentBundle R)
      (E : ∀ k, FormBundle A k) (J : Calculus A E),
      R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (openSubsetAtlas S.smoothStructure.val U U.isOpen) ∧
      IsSmoothMap R S Subtype.val ∧
      ∀ k, Nonempty (D.complex.H k ≃ₗ[ℝ] J.Cohomology k) := by
  classical
  obtain ⟨R,hR,hinc,hT⟩ := open_manifold_tangent_equiv S U
  choose F hF using hT
  obtain ⟨A⟩ := BundleOperations.exists_cotangent R
  let E : ∀ k, FormBundle A k := fun k =>
    Classical.choice (ExteriorAlgebraResults.exists_formBundle A k)
  obtain ⟨J⟩ := DeRhamResults.complex_exists A E
  exact ⟨R,A,E,J,hR,hinc,fun k => ⟨intrinsicOpenHEquiv K J hR hinc F hF D k⟩⟩
end SmoothManifolds.GenusTwoOpenCohomology

namespace SmoothManifolds.GenusTwoDeRhamGeometry
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
  GenusTwoData SphereTorusData MayerVietorisData GenusTwoOpenCohomology
  GenusTwoHomotopyCohomology InteriorHomotopyData

/-- The actual annulus overlap has one degree-one class and no higher classes.
The only conditional input is the entire frozen standard torus algebra. -/
theorem surface_overlap_cohomology
    (htorus : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType)
    {S : SmoothManifold 2 .euclidean Surface} {C : CotangentBundle S}
    {B : ∀ k, FormBundle C k} (K : Calculus C B)
    (D : CoverComplex K surfaceCover) :
    Nonempty (D.onOverlap.complex.H 1 ≃ₗ[ℝ] ℝ) ∧
      ∀ k : ℕ, 1 < k → Subsingleton (D.onOverlap.complex.H k) := by
  classical
  obtain ⟨R, A, E, J, _, _, hJ⟩ := open_intrinsic_cohomology_exists K D.onOverlap
  obtain ⟨T, _, hT⟩ := (SphereTorus.angleManifold 1).2.2
  obtain ⟨A₁⟩ := BundleOperations.exists_cotangent T
  let E₁ : ∀ k, FormBundle A₁ k := fun k =>
    Classical.choice (ExteriorAlgebraResults.exists_formBundle A₁ k)
  obtain ⟨J₁⟩ := DeRhamResults.complex_exists A₁ E₁
  let e : ↥(surfaceCover.U ⊓ surfaceCover.V) ≃ₜ collarRegion :=
    Homeomorph.setCongr surfaceCover_overlap
  let f : ↥(surfaceCover.U ⊓ surfaceCover.V) → FlatTorus 1 :=
    fun p => collarCircleProjection (e p)
  let g : FlatTorus 1 → ↥(surfaceCover.U ⊓ surfaceCover.V) :=
    fun z => e.symm (collarCircleSection z)
  have hf : Continuous f := collarCircleProjection.continuous.comp e.continuous
  have hg : Continuous g := e.symm.continuous.comp collarCircleSection.continuous
  have hgf : ∃ H : HomotopyTime × ↥(surfaceCover.U ⊓ surfaceCover.V) →
      ↥(surfaceCover.U ⊓ surfaceCover.V), Continuous H ∧
      (∀ p, H (timeZero, p) = g (f p)) ∧ (∀ p, H (timeOne, p) = p) := by
    refine ⟨fun z => e.symm (collarCircleContraction (z.1, e z.2)), ?_, ?_, ?_⟩
    · exact e.symm.continuous.comp (collarCircleContraction.continuous_toFun.comp
        (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
    · intro p
      exact congrArg e.symm (collarCircleContraction.map_zero_left (e p))
    · intro p
      exact (congrArg e.symm (collarCircleContraction.map_one_left (e p))).trans
        (e.symm_apply_apply p)
  have hfg : ∃ H : HomotopyTime × FlatTorus 1 → FlatTorus 1, Continuous H ∧
      (∀ z, H (timeZero, z) = f (g z)) ∧ (∀ z, H (timeOne, z) = z) := by
    refine ⟨fun z => z.2, continuous_snd, ?_, fun _ => rfl⟩
    intro z
    change z = collarCircleProjection (e (e.symm (collarCircleSection z)))
    rw [Homeomorph.apply_symm_apply, collarCircleProjection_section]
  have hEq (k : ℕ) : Nonempty (J.Cohomology k ≃ₗ[ℝ] J₁.Cohomology k) :=
    continuous_homotopy_equivalence_of_homotopies R T A A₁ E E₁ J J₁ f g hf hg hgf hfg k
  constructor
  · obtain ⟨eO⟩ := hJ 1
    obtain ⟨eH⟩ := hEq 1
    obtain ⟨eT⟩ := GenusTwoDeRhamResults.torus_degree_one htorus 1 T hT A₁ E₁ J₁
    exact ⟨((eO.trans eH).trans eT).trans (LinearEquiv.funUnique (Fin 1) ℝ ℝ)⟩
  · intro k hk
    obtain ⟨eO⟩ := hJ k
    obtain ⟨eH⟩ := hEq k
    letI : Subsingleton (J₁.Cohomology k) := DeRhamResults.above_dimension J₁ k hk
    exact (eO.trans eH).injective.subsingleton

end SmoothManifolds.GenusTwoDeRhamGeometry

namespace SmoothManifolds.GenusTwoOpenCohomology
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
  MayerVietorisData
universe u

/-- Continuous contractibility kills positive cohomology of every full open
realization, through its genuine intrinsic open manifold. -/
theorem open_contractible_vanishing
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {U : TopologicalSpace.Opens M} [Nonempty U] [ContractibleSpace U]
    (K : Calculus C B) (D : OpenCalculus C B U) (k : ℕ) (hk : 0 < k) :
    Subsingleton (D.complex.H k) := by
  obtain ⟨R,A,E,J,_,_,hE⟩ := open_intrinsic_cohomology_exists K D
  obtain ⟨e⟩ := hE k
  letI : Subsingleton (J.Cohomology k) :=
    HomotopyResults.contractible_vanishing R A E J k hk
  exact e.injective.subsingleton
end SmoothManifolds.GenusTwoOpenCohomology

namespace SmoothManifolds.GenusTwoMayerVietoris
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
  MayerVietorisData
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  {K : Calculus C B} {O : OpenCover M}

/-- Zero cohomological difference means each actual restriction vanishes,
since the two summands can be tested independently. -/
theorem restrictions_zero_of_difference_zero (D : CoverComplex K O) (k : ℕ)
    (hQ : D.sequence.q.onH k = 0) :
    (OpenForms.openRestriction O.U (O.U ⊓ O.V) inf_le_left
      D.onU D.onOverlap).onH k = 0 ∧
    (OpenForms.openRestriction O.V (O.U ⊓ O.V) inf_le_right
      D.onV D.onOverlap).onH k = 0 := by
  let e := D.onU.complex.productHEquiv D.onV.complex k
  have hpair (u : D.onU.complex.H k) (v : D.onV.complex.H k) :
      ((ChainMap.fst _ _).onH k (e.symm (u,v)),
        (ChainMap.snd _ _).onH k (e.symm (u,v))) = (u,v) :=
    e.apply_symm_apply (u,v)
  simp only [Prod.mk.injEq] at hpair
  constructor
  · apply LinearMap.ext
    intro u
    have h := congrArg (fun F => F (e.symm (u,0))) hQ
    rw [difference_onH] at h
    rw [(hpair u 0).1, (hpair u 0).2] at h
    simpa only [map_zero, zero_sub, LinearMap.zero_apply, neg_eq_zero] using h
  · apply LinearMap.ext
    intro v
    have h := congrArg (fun F => F (e.symm (0,v))) hQ
    rw [difference_onH] at h
    rw [(hpair 0 v).1, (hpair 0 v).2] at h
    simpa only [map_zero, sub_zero, LinearMap.zero_apply] using h
end SmoothManifolds.GenusTwoMayerVietoris

namespace SmoothManifolds.GenusTwoMayerVietoris
open MayerVietorisData
universe u
variable {A B C : Cochain.{u}} (E : ShortExact A B C)

/-- If the following middle group vanishes, a nonzero global class forces a
surjective connecting map from a line to be injective as well. -/
theorem connecting_bijective_of_nontrivial
    (k : ℕ) (eC : C.H k ≃ₗ[ℝ] ℝ) [Subsingleton (B.H (k+1))]
    (x : A.H (k+1)) (hx : x ≠ 0) : Function.Bijective (E.delta k) := by
  have hsurj : Function.Surjective (E.delta k) := by
    intro y
    exact (E.exact_at_left k y).mp (Subsingleton.elim _ _)
  obtain ⟨z, hz⟩ := hsurj x
  let f : ℝ →ₗ[ℝ] A.H (k+1) := (E.delta k).comp eC.symm.toLinearMap
  have hm (r : ℝ) : f r = r • f 1 := by
    simpa only [smul_eq_mul, mul_one] using f.map_smul r 1
  have hfz : f (eC z) = x := by
    change E.delta k (eC.symm (eC z)) = x
    rw [LinearEquiv.symm_apply_apply]
    exact hz
  have h1 : f 1 ≠ 0 := by
    intro h
    apply hx
    rw [← hfz, hm, h, smul_zero]
  have hfinj : Function.Injective f := by
    intro s t hst
    have hs : (s-t) • f 1 = 0 := by
      rw [← hm, map_sub, hst, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right h1)
  refine ⟨?_, hsurj⟩
  intro u v huv
  apply eC.injective
  apply hfinj
  change E.delta k (eC.symm (eC u)) = E.delta k (eC.symm (eC v))
  simpa only [LinearEquiv.symm_apply_apply] using huv
end SmoothManifolds.GenusTwoMayerVietoris

section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SmoothManifolds.GenusTwoBump
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData
  ExteriorData ExteriorDerivativeData DeRhamData FormPullbackData PathIntegrationData
  LocalIntegrationData GlobalIntegrationData OrientationData BoundaryData BoundaryOrientationData
  FrameData PartitionData OrientationResults Set MeasureTheory Module
universe u

lemma topCoefficient_coordinateTopForm
    {n : ℕ} {M : Type u} [TopologicalSpace M] {S : SmoothManifold n .euclidean M}
    (K : FiberCoordinates S) (c : ModelChart n .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) :
    evaluate (TangentSpace S p.val) n (coordinateTopForm K c hc p)
      (CovectorData.coordinateVector K c hc p.val p.property) = 1 := by
  change exteriorPower.alternatingMapLinearEquiv.symm
    (exteriorPower.pairingDual ℝ (TangentSpace S p.val) n (coordinateTopForm K c hc p))
      (CovectorData.coordinateVector K c hc p.val p.property) = 1
  rw [exteriorPower.alternatingMapLinearEquiv_symm_apply]
  change exteriorPower.pairingDual ℝ (TangentSpace S p.val) n
    (coordinateTopForm K c hc p) (exteriorPower.ιMulti ℝ n
      (CovectorData.coordinateVector K c hc p.val p.property)) = 1
  have hv : CovectorData.coordinateVector K c hc p.val p.property =
      fun j => (K.equiv c hc p.val p.property).symm (Pi.single j 1) := rfl
  rw [hv]
  simpa only [pairing, OrientationData.coordinateVector, Pi.basisFun_apply] using
    pairing_coordinateTopForm_self K c hc p

/-- Every nonempty open set contains a smooth compact top form with positive
integral for the given actual intrinsic orientation and integral. -/
theorem supported_positive_top_form
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : CotangentBundle S) (B : FormBundle C n)
    (o : Orientation S) (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (U : Set M) (hU : IsOpen U) (x : M) (hx : x ∈ U) :
    ∃ η : CompactTopForm S, IsForm B η.field ∧
      sectionSupport η.field ⊆ U ∧ 0 < I η := by
  classical
  obtain ⟨c, hc, hxc⟩ := S.smoothStructure.property.1.1 x
  obtain ⟨s, hs, _⟩ := LocalIntegrationResults.orientation_signs S o
  obtain ⟨ρ, hρ, hρ01, hρ1, hρs, hρcp⟩ :=
    exists_local_bump S x (U ∩ c.source) (hU.inter c.open_source) ⟨hx, hxc⟩
  let W : Field S n := fun p => ρ p • localTopField C.tangent.fiberCoordinates s c hc p
  have hsρ : sectionSupport ρ ⊆ c.source := fun p hp => (hρs hp).2
  have hW : IsForm B W :=
    supported_local_form_smooth ExteriorAlgebraResults.smooth_iff_coefficients C B
      c.source c.open_source (localTopField C.tangent.fiberCoordinates s c hc)
      (smooth_localTopField_coefficients S C s c hc) ρ
      ((vectorSmooth_scalar_iff _ _).mpr hρ) hsρ
  have hWs : sectionSupport W ⊆ sectionSupport ρ := fun p hp =>
    (GlobalIntegrationResults.weight_support S n
      (localTopField C.tangent.fiberCoordinates s c hc) ρ hp).1
  let η : CompactTopForm S :=
    ⟨W, StokesResults.continuous_top_of_coefficients C W
      (ExteriorDerivativeResults.regular_continuous C n 1 W
        (ExteriorDerivativeResults.smooth_regular C n B W 1 hW)),
      hρcp.of_isClosed_subset isClosed_closure hWs⟩
  have hηc : sectionSupport η.field ⊆ c.source := hWs.trans hsρ
  let f : Euclidean n → ℝ := signedCoordinateCoefficient s C.tangent.fiberCoordinates c hc η.field
  have hfc : Continuous f := by
    have h := (LocalIntegrationResults.modelSignedCoefficient_continuous s
      C.tangent.fiberCoordinates c hc η hηc).comp
      (show Continuous (fun z : Euclidean n => (⟨z, mem_univ z⟩ : ModelSpace n .euclidean)) from
        continuous_id.subtype_mk _)
    convert h using 1
    funext z
    simp only [f, signedCoordinateCoefficient, extendModel]
    rw [dite_eq_left (show z ∈ ModelData.modelSet n .euclidean from mem_univ z)]
    rfl
  have hfi : Integrable f := LocalIntegrationResults.integrable S s
    C.tangent.fiberCoordinates c hc η hηc
  have hfchart (p : c.source) : f (c p.val).val = ρ p.val := by
    change signedCoordinateCoefficient s C.tangent.fiberCoordinates c hc η.field (c p.val).val = _
    rw [LocalIntegrationResults.signedCoefficient_at]
    change signValue (s.sign c hc p) *
      evaluate (TangentSpace S p.val) n (W p.val)
        (CovectorData.coordinateVector C.tangent.fiberCoordinates c hc p.val p.property) = _
    simp only [W, localTopField, dite_eq_left p.property, signedCoordinateTopForm,
      map_smul, LinearMap.smul_apply, AlternatingMap.smul_apply, smul_eq_mul,
      topCoefficient_coordinateTopForm]
    change signValue (s.sign c hc p) *
      (ρ p.val * (signValue (s.sign c hc p) * 1)) = ρ p.val
    rw [mul_one, mul_left_comm, signValue_mul_self, mul_one]
  have hfn : 0 ≤ f := by
    intro z
    by_cases hz : z ∈ modelSet n .euclidean
    · by_cases hzt : (⟨z,hz⟩ : ModelSpace n .euclidean) ∈ c.target
      · let p : c.source := ⟨c.symm ⟨z,hz⟩, c.map_target hzt⟩
        have hpz : (c p.val).val = z := congrArg Subtype.val (c.right_inv hzt)
        rw [← hpz, hfchart]
        exact (hρ01 _).1
      · simp [f, signedCoordinateCoefficient, extendModel, hz, modelSignedCoefficient, hzt]
    · simp [f, signedCoordinateCoefficient, extendModel, hz]
  have hfx : f (c x).val ≠ 0 := by
    rw [hfchart ⟨x,hxc⟩, hρ1.self_of_nhds]
    exact one_ne_zero
  have hpos : 0 < ∫ z, f z := integral_pos_of_integrable_nonneg_nonzero hfc hfi hfn hfx
  refine ⟨η, hW, hWs.trans (fun p hp => (hρs hp).1), ?_⟩
  rw [hI.2.2 s hs C.tangent.fiberCoordinates c hc η hηc]
  exact hpos

end SmoothManifolds.GenusTwoBump

namespace SmoothManifolds.GenusTwoBump
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData CovectorData
  ExteriorData ExteriorDerivativeData DeRhamData FormPullbackData LocalIntegrationData
  GlobalIntegrationData OrientationData OrientationResults SphereTorusData TorusDeRhamData Set Module
universe u

lemma coordinateCovector_dualBasis
    {n : ℕ} {M : Type u} [TopologicalSpace M] {S : SmoothManifold n .euclidean M}
    (K : FiberCoordinates S) (c : ModelChart n .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (i : Fin n) :
    coordinateCovector K c hc p.val p.property i =
      (((Pi.basisFun ℝ (Fin n)).map (K.equiv c hc p.val p.property).symm).dualBasis i) := by
  let b := (Pi.basisFun ℝ (Fin n)).map (K.equiv c hc p.val p.property).symm
  apply b.ext
  intro j
  change coordinateCovector K c hc p.val p.property i (b j) = b.dualBasis i (b j)
  rw [Basis.dualBasis_apply_self]
  change coordinateCovector K c hc p.val p.property i (b j) = if j = i then 1 else 0
  simpa only [b, Basis.map_apply, Pi.basisFun_apply, CovectorData.coordinateVector, eq_comm] using
    Covectors.coordinateCovector_apply K c hc p.val p.property i j

lemma coordinate_wedge_eq_top
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}
    (K : FiberCoordinates S) (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) :
    wedge (V := TangentSpace S p.val) (k := 1) (l := 1)
      ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p.val))).symm
        (coordinateCovector K c hc p.val p.property 0))
      ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p.val))).symm
        (coordinateCovector K c hc p.val p.property 1)) = coordinateTopForm K c hc p := by
  let b := (Pi.basisFun ℝ (Fin 2)).map (K.equiv c hc p.val p.property).symm
  have h (i : Fin 2) :
      (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p.val))).symm
        (coordinateCovector K c hc p.val p.property i) =
      exteriorPower.ιMulti ℝ 1 (fun _ => b.dualBasis i) := by
    apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p.val))).injective
    rw [LinearEquiv.apply_symm_apply, exteriorPower.oneEquiv_ιMulti]
    exact coordinateCovector_dualBasis K c hc p i
  have he : Fin.append (fun _ : Fin 1 => b.dualBasis 0)
      (fun _ : Fin 1 => b.dualBasis 1) = b.dualBasis := by
    funext i
    fin_cases i <;> rfl
  calc
    _ = wedge (V := TangentSpace S p.val) (k := 1) (l := 1)
        (exteriorPower.ιMulti ℝ 1 (fun _ => b.dualBasis 0))
        (exteriorPower.ιMulti ℝ 1 (fun _ => b.dualBasis 1)) :=
      congrArg₂ (fun α β : Fiber (TangentSpace S p.val) 1 =>
        wedge (V := TangentSpace S p.val) (k := 1) (l := 1) α β) (h 0) (h 1)
    _ = exteriorPower.ιMulti ℝ 2
        (Fin.append (fun _ : Fin 1 => b.dualBasis 0) (fun _ : Fin 1 => b.dualBasis 1)) :=
      ExteriorAlgebraResults.wedge_decomposable (TangentSpace S p.val) 1 1 _ _
    _ = _ := congrArg (exteriorPower.ιMulti ℝ 2) he

/-- The full torus presentation supplies a genuine orientation, through its
nowhere-zero smooth coordinate two-form. -/
theorem torus_orientation
    (htorus : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType)
    (S : SmoothManifold 2 .euclidean (FlatTorus 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B) :
    Nonempty (Orientation S) := by
  obtain ⟨P,hP⟩ := DeRhamResults.product_exists K
  obtain ⟨F⟩ := htorus 2 S hS C B K P hP
  let Ω : Field S 2 := fieldWedge (F.theta 0).val.val (F.theta 1).val.val
  have hΩ : IsForm (B 2) Ω := ExteriorAlgebraResults.wedge_smooth C 1 1 (B 1) (B 1) (B 2)
    (F.theta 0).val.val (F.theta 1).val.val
    ((K.mem_forms _ _).mp (F.theta 0).val.property)
    ((K.mem_forms _ _).mp (F.theta 1).val.property)
  have hΩnz (p : FlatTorus 2) : Ω p ≠ 0 := by
    obtain ⟨c, hca, hpc⟩ := (SphereTorus.angleAtlas_isContDiffAtlas 2).1 p
    have hc : c ∈ S.smoothStructure.val := by
      rw [hS]
      exact subset_maximalExtension (SphereTorus.angleAtlas_isContDiffAtlas 2) hca
    obtain ⟨z,ε,hε0,hε,hangle⟩ := hca
    have htheta (i : Fin 2) : (F.theta i).val.val p =
        (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
          (coordinateCovector C.tangent.fiberCoordinates c hc p hpc i) := by
      apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
      rw [LinearEquiv.apply_symm_apply]
      exact F.coordinate i c hc z ε hε0 hε hangle p hpc
    have he : Ω p = coordinateTopForm C.tangent.fiberCoordinates c hc ⟨p,hpc⟩ := by
      change wedge (V := TangentSpace S p) (k := 1) (l := 1) ((F.theta 0).val.val p) ((F.theta 1).val.val p) = _
      exact (congrArg₂ (fun α β : Fiber (TangentSpace S p) 1 =>
        wedge (V := TangentSpace S p) (k := 1) (l := 1) α β)
        (htheta 0) (htheta 1)).trans
        (coordinate_wedge_eq_top C.tangent.fiberCoordinates c hc ⟨p,hpc⟩)
    intro hz
    have hn := topCoefficient_coordinateTopForm C.tangent.fiberCoordinates c hc ⟨p,hpc⟩
    have hzero : coordinateTopForm C.tangent.fiberCoordinates c hc ⟨p,hpc⟩ = 0 :=
      he.symm.trans hz
    have hh := congrArg (fun α : Fiber (TangentSpace S p) 2 =>
      evaluate (TangentSpace S p) 2 α
        (CovectorData.coordinateVector C.tangent.fiberCoordinates c hc p hpc)) hzero
    rw [hn, map_zero] at hh
    exact one_ne_zero hh
  let ω : NonvanishingTopForm (B 2) := ⟨⟨Ω,hΩ⟩,hΩnz⟩
  obtain ⟨o,_,_⟩ := form_orientation_exists_unique ExteriorAlgebraResults.alternating_interpretation
    ExteriorAlgebraResults.smooth_iff_coefficients S C (B 2) ω
  exact ⟨o⟩

end SmoothManifolds.GenusTwoBump
end



namespace SmoothManifolds.GenusTwoDeRhamGeometry
open ModelData SphereTorusData GenusTwoData GenusTwoAtlas Set Topology

lemma collarHomeomorph_stripMap (x : AngleStrip) :
    collarHomeomorph (stripMap x) = cylinderProjection x := by
  change cylinderProjection_quotient.homeomorph
    ((Homeomorph.Quotient.congrRight stripMap_fibers)
      (stripMap_quotient.homeomorph.symm (stripMap x))) = cylinderProjection x
  have he : stripMap_quotient.homeomorph (Quotient.mk (Setoid.ker stripMap) x) = stripMap x := rfl
  rw [← he, Homeomorph.symm_apply_apply]
  rfl

lemma halfTorus_mem_boundaryCircle_iff (side : Bool) (x : Euclidean 2)
    (hx : |x 1| < (1/16 : ℝ)) :
    halfTorus side x ∈ boundaryCircle ↔ x 1 = 0 := by
  rw [halfTorus, projection_mem_boundaryCircle_iff (halfCoordinates_small side x hx),
    halfCoordinates_squareSum]
  have ht := abs_lt.mp hx
  cases side <;> dsimp <;> constructor <;> intro h <;> nlinarith

lemma seamPoint_mem_bulkRegion (side : Bool) (x : Euclidean 2)
    (hx : |x 1| < (1/16 : ℝ)) :
    seamPoint x ∈ bulkRegion side ↔ (if side then x 1 < 0 else 0 < x 1) := by
  constructor
  · rintro ⟨p, hp, he⟩
    have hval := seamPoint_fiber_half side p x hx he.symm
    have hn : halfTorus side x ∉ removedDisk := by rw [← hval]; exact p.property
    have hsign := (halfTorus_notMem_removedDisk_iff side x hx).mp hn
    have hne : x 1 ≠ 0 := by
      intro h
      apply hp
      rw [hval]
      exact (halfTorus_mem_boundaryCircle_iff side x hx).mpr h
    cases side <;> dsimp at * <;> apply lt_of_le_of_ne hsign <;> first | exact hne | exact Ne.symm hne
  · intro hsign
    have hn : halfTorus side x ∉ removedDisk :=
      (halfTorus_notMem_removedDisk_iff side x hx).mpr (by
        cases side <;> dsimp at * <;> exact le_of_lt hsign)
    let p : PuncturedTorus := ⟨halfTorus side x, hn⟩
    refine ⟨p, ?_, (seamPoint_eq_side side p x hx rfl).symm⟩
    change halfTorus side x ∉ boundaryCircle
    rw [halfTorus_mem_boundaryCircle_iff side x hx]
    cases side <;> dsimp at hsign <;> intro h <;> linarith

/-- Signed radial distance into the specified side. -/
def orientedRadius (side : Bool) (t : ℝ) : ℝ := if side then -t else t

lemma orientedRadius_involutive (side : Bool) (t : ℝ) :
    orientedRadius side (orientedRadius side t) = t := by cases side <;> simp [orientedRadius]

lemma orientedRadius_abs (side : Bool) (t : ℝ) : |orientedRadius side t| = |t| := by
  cases side <;> simp [orientedRadius]

lemma collar_mem_bulkRegion (side : Bool) (p : collarRegion) :
    p.val ∈ bulkRegion side ↔ 0 < orientedRadius side (collarHomeomorph p).2.val := by
  obtain ⟨x, rfl⟩ := stripMap_surjective p
  rw [collarHomeomorph_stripMap]
  change seamPoint (stripCoordinates x) ∈ bulkRegion side ↔ _
  rw [seamPoint_mem_bulkRegion side (stripCoordinates x)
    ((stripCoordinates_bound x).trans (by norm_num))]
  change (if side then x.2.val < 0 else 0 < x.2.val) ↔
    0 < orientedRadius side x.2.val
  cases side <;> simp [orientedRadius]


lemma continuous_orientedRadius (side : Bool) : Continuous (orientedRadius side) := by
  cases side
  · exact continuous_id
  · exact continuous_neg

abbrev CapInterval := Set.Icc (0 : ℝ) (1/64 : ℝ)

def capInterval (side : Bool) (t : CapInterval) : CollarInterval :=
  ⟨orientedRadius side t.val, abs_lt.mp (by
    rw [orientedRadius_abs, abs_of_nonneg t.property.1]
    exact t.property.2.trans_lt (by norm_num))⟩

/-- A compact collar cap on the specified side, including its seam. -/
def sideCapMap (side : Bool) : C(AddCircle (1 : ℝ) × CapInterval, Surface) where
  toFun z := (collarHomeomorph.symm (z.1, capInterval side z.2)).val
  continuous_toFun := continuous_subtype_val.comp (collarHomeomorph.symm.continuous.comp
    (continuous_fst.prodMk (((continuous_orientedRadius side).comp
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _)))

def sideCap (side : Bool) : Set Surface := range (sideCapMap side)

lemma sideCap_closed (side : Bool) : IsClosed (sideCap side) :=
  (isCompact_range (sideCapMap side).continuous).isClosed

lemma sideCap_subset_collar (side : Bool) : sideCap side ⊆ collarRegion := by
  rintro z ⟨p, rfl⟩
  exact (collarHomeomorph.symm (p.1, capInterval side p.2)).property

lemma mem_sideCap (side : Bool) (p : collarRegion) :
    p.val ∈ sideCap side ↔ orientedRadius side (collarHomeomorph p).2.val ∈ CapInterval := by
  constructor
  · rintro ⟨⟨a, t⟩, he⟩
    have hp : collarHomeomorph.symm (a, capInterval side t) = p := Subtype.ext he
    rw [← hp, Homeomorph.apply_symm_apply]
    change orientedRadius side (orientedRadius side t.val) ∈ CapInterval
    rw [orientedRadius_involutive]
    exact t.property
  · intro ht
    let t : CapInterval := ⟨orientedRadius side (collarHomeomorph p).2.val, ht⟩
    refine ⟨((collarHomeomorph p).1, t), ?_⟩
    change (collarHomeomorph.symm ((collarHomeomorph p).1, capInterval side t)).val = p.val
    apply congrArg Subtype.val
    apply collarHomeomorph.injective
    rw [Homeomorph.apply_symm_apply]
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact orientedRadius_involutive side (collarHomeomorph p).2.val

/-- Outside this compact cap, the interior side is open and the collar push
will be the identity. -/
def outerSide (side : Bool) : Set Surface := bulkRegion side \ sideCap side

lemma outerSide_open (side : Bool) : IsOpen (outerSide side) :=
  (bulkRegion_open side).inter (sideCap_closed side).isOpen_compl

lemma extendedSide_collar_or_outer (side : Bool) (p : extendedSide side) :
    p.val ∈ collarRegion ∨ p.val ∈ outerSide side := by
  rcases p.property with hp | hp
  · by_cases hcap : p.val ∈ sideCap side
    · exact Or.inl (sideCap_subset_collar side hcap)
    · exact Or.inr ⟨hp, hcap⟩
  · exact Or.inl hp

lemma collar_outer_radius (side : Bool) (p : collarRegion)
    (hp : p.val ∈ outerSide side) :
    (1/64 : ℝ) < orientedRadius side (collarHomeomorph p).2.val := by
  have hpos := (collar_mem_bulkRegion side p).mp hp.1
  have hnot := (mem_sideCap side p).not.mp hp.2
  exact lt_of_not_ge (fun h => hnot ⟨le_of_lt hpos, h⟩)

/-- Continuous inward push in an oriented collar coordinate. -/
def pushInward (s : unitInterval) (r : ℝ) : ℝ :=
  (1-s.val)*r+s.val*max r (1/64 : ℝ)

lemma le_pushInward (s : unitInterval) (r : ℝ) : r ≤ pushInward s r := by
  have h := mul_nonneg s.property.1 (sub_nonneg.mpr (le_max_left r (1/64 : ℝ)))
  unfold pushInward
  nlinarith

lemma pushInward_le (s : unitInterval) (r : ℝ) :
    pushInward s r ≤ max r (1/64 : ℝ) := by
  have h := mul_nonneg (sub_nonneg.mpr s.property.2)
    (sub_nonneg.mpr (le_max_left r (1/64 : ℝ)))
  unfold pushInward
  nlinarith

def pushCollarInterval (side : Bool) (s : unitInterval) (t : CollarInterval) : CollarInterval :=
  ⟨orientedRadius side (pushInward s (orientedRadius side t.val)), abs_lt.mp (by
    rw [orientedRadius_abs]
    have ht : |orientedRadius side t.val| < (1/32 : ℝ) := by
      rw [orientedRadius_abs]
      exact abs_lt.mpr t.property
    apply abs_lt.mpr
    exact ⟨lt_of_lt_of_le (abs_lt.mp ht).1 (le_pushInward s _),
      lt_of_le_of_lt (pushInward_le s _) (max_lt (abs_lt.mp ht).2 (by norm_num))⟩)⟩

def collarPush (side : Bool) : C(unitInterval × collarRegion, collarRegion) where
  toFun z := collarHomeomorph.symm
    ((collarHomeomorph z.2).1, pushCollarInterval side z.1 (collarHomeomorph z.2).2)
  continuous_toFun := by
    apply collarHomeomorph.symm.continuous.comp
    apply Continuous.prodMk
    · exact collarHomeomorph.continuous.fst.comp continuous_snd
    · apply Continuous.subtype_mk
      unfold orientedRadius pushInward
      cases side <;> dsimp <;> fun_prop

lemma collarPush_zero (side : Bool) (p : collarRegion) : collarPush side (0, p) = p := by
  apply collarHomeomorph.injective
  change collarHomeomorph (collarHomeomorph.symm _) = _
  rw [Homeomorph.apply_symm_apply]
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change orientedRadius side (pushInward 0 (orientedRadius side _)) = _
    simp only [pushInward, Set.Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
    exact orientedRadius_involutive side _

lemma collarPush_one_bulk (side : Bool) (p : collarRegion) :
    (collarPush side (1, p)).val ∈ bulkRegion side := by
  apply (collar_mem_bulkRegion side _).mpr
  change 0 < orientedRadius side
    (collarHomeomorph (collarHomeomorph.symm _)).2.val
  rw [Homeomorph.apply_symm_apply]
  change 0 < orientedRadius side (orientedRadius side _)
  rw [orientedRadius_involutive]
  simp only [pushInward, Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/64) (le_max_right _ _)

lemma collarPush_preserves_bulk (side : Bool) (s : unitInterval) (p : collarRegion)
    (hp : p.val ∈ bulkRegion side) : (collarPush side (s, p)).val ∈ bulkRegion side := by
  apply (collar_mem_bulkRegion side _).mpr
  change 0 < orientedRadius side
    (collarHomeomorph (collarHomeomorph.symm _)).2.val
  rw [Homeomorph.apply_symm_apply]
  change 0 < orientedRadius side (orientedRadius side _)
  rw [orientedRadius_involutive]
  exact lt_of_lt_of_le ((collar_mem_bulkRegion side p).mp hp) (le_pushInward s _)

lemma collarPush_eq_self (side : Bool) (s : unitInterval) (p : collarRegion)
    (hp : p.val ∈ outerSide side) : collarPush side (s, p) = p := by
  apply collarHomeomorph.injective
  change collarHomeomorph (collarHomeomorph.symm _) = _
  rw [Homeomorph.apply_symm_apply]
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change orientedRadius side (pushInward s (orientedRadius side _)) = _
    unfold pushInward
    rw [max_eq_left (le_of_lt (collar_outer_radius side p hp))]
    have he (r : ℝ) : (1-s.val)*r+s.val*r = r := by ring
    rw [he]
    exact orientedRadius_involutive side _


/-- The collar push is the identity on the complementary outer open set. -/
def rawSidePush (side : Bool) (z : unitInterval × extendedSide side) : Surface := by
  classical
  exact if hp : z.2.val ∈ collarRegion then
    (collarPush side (z.1, ⟨z.2.val, hp⟩)).val else z.2.val

lemma rawSidePush_outer (side : Bool) (z : unitInterval × extendedSide side)
    (hz : z.2.val ∈ outerSide side) : rawSidePush side z = z.2.val := by
  classical
  unfold rawSidePush
  split_ifs with hp
  · exact congrArg Subtype.val (collarPush_eq_self side z.1 ⟨z.2.val, hp⟩ hz)
  · rfl

lemma rawSidePush_continuous (side : Bool) : Continuous (rawSidePush side) := by
  classical
  let A : Set (unitInterval × extendedSide side) := {z | z.2.val ∈ collarRegion}
  let B : Set (unitInterval × extendedSide side) := {z | z.2.val ∈ outerSide side}
  have hA : IsOpen A := collarRegion_open.preimage (continuous_subtype_val.comp continuous_snd)
  have hB : IsOpen B := (outerSide_open side).preimage
    (continuous_subtype_val.comp continuous_snd)
  have hcA : ContinuousOn (rawSidePush side) A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hlocal : Continuous (fun z : A =>
        (collarPush side (z.val.1, ⟨z.val.2.val, z.property⟩)).val) := by
      apply continuous_subtype_val.comp
      apply (collarPush side).continuous.comp
      apply Continuous.prodMk
      · exact continuous_fst.comp continuous_subtype_val
      · apply Continuous.subtype_mk
        exact continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
    apply hlocal.congr
    intro z
    change (collarPush side (z.val.1, ⟨z.val.2.val, z.property⟩)).val =
      rawSidePush side z.val
    unfold rawSidePush
    split_ifs with hz
    · rfl
    · exact (hz z.property).elim
  have hcB : ContinuousOn (rawSidePush side) B :=
    (continuous_subtype_val.comp continuous_snd).continuousOn.congr
      (fun z hz => rawSidePush_outer side z hz)
  apply continuous_iff_continuousAt.mpr
  intro z
  rcases extendedSide_collar_or_outer side z.2 with hz | hz
  · exact hcA.continuousAt (hA.mem_nhds hz)
  · exact hcB.continuousAt (hB.mem_nhds hz)

lemma rawSidePush_mem (side : Bool) (z : unitInterval × extendedSide side) :
    rawSidePush side z ∈ (extendedSide side : Set Surface) := by
  classical
  unfold rawSidePush
  split_ifs with hp
  · exact Or.inr (collarPush side (z.1, ⟨z.2.val, hp⟩)).property
  · exact z.2.property

/-- A genuine continuous homotopy pushing an extended side into its own bulk. -/
def extendedSidePush (side : Bool) :
    C(unitInterval × extendedSide side, extendedSide side) where
  toFun z := ⟨rawSidePush side z, rawSidePush_mem side z⟩
  continuous_toFun := (rawSidePush_continuous side).subtype_mk _

lemma extendedSidePush_zero (side : Bool) (p : extendedSide side) :
    extendedSidePush side (0, p) = p := by
  classical
  apply Subtype.ext
  change rawSidePush side (0, p) = p.val
  unfold rawSidePush
  split_ifs with hp
  · exact congrArg Subtype.val (collarPush_zero side ⟨p.val, hp⟩)
  · rfl

lemma extendedSidePush_one_bulk (side : Bool) (p : extendedSide side) :
    (extendedSidePush side (1, p)).val ∈ bulkRegion side := by
  classical
  change rawSidePush side (1, p) ∈ bulkRegion side
  unfold rawSidePush
  split_ifs with hp
  · exact collarPush_one_bulk side ⟨p.val, hp⟩
  · exact p.property.resolve_right hp

lemma extendedSidePush_preserves_bulk (side : Bool) (s : unitInterval)
    (p : extendedSide side) (hp : p.val ∈ bulkRegion side) :
    (extendedSidePush side (s, p)).val ∈ bulkRegion side := by
  classical
  change rawSidePush side (s, p) ∈ bulkRegion side
  unfold rawSidePush
  split_ifs with hc
  · exact collarPush_preserves_bulk side s ⟨p.val, hc⟩ hp
  · exact hp

/-- The literal inclusion of the actual bulk into the extended quotient side. -/
def bulkToExtended (side : Bool) : C(bulkRegion side, extendedSide side) where
  toFun p := ⟨p.val, Or.inl p.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The final pushed map has image in the actual bulk. -/
def extendedToBulk (side : Bool) : C(extendedSide side, bulkRegion side) where
  toFun p := ⟨(extendedSidePush side (1, p)).val, extendedSidePush_one_bulk side p⟩
  continuous_toFun := (continuous_subtype_val.comp
    ((extendedSidePush side).continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk _

def extendedSideToBulkHomotopy (side : Bool) : ContinuousMap.Homotopy
    (ContinuousMap.id (extendedSide side)) ((bulkToExtended side).comp (extendedToBulk side)) where
  toContinuousMap := extendedSidePush side
  map_zero_left := extendedSidePush_zero side
  map_one_left _ := rfl

def bulkToExtendedHomotopy (side : Bool) : ContinuousMap.Homotopy
    (ContinuousMap.id (bulkRegion side)) ((extendedToBulk side).comp (bulkToExtended side)) where
  toFun z := ⟨(extendedSidePush side (z.1, bulkToExtended side z.2)).val,
    extendedSidePush_preserves_bulk side z.1 (bulkToExtended side z.2) z.2.property⟩
  continuous_toFun := (continuous_subtype_val.comp
    ((extendedSidePush side).continuous.comp
      (continuous_fst.prodMk ((bulkToExtended side).continuous.comp continuous_snd)))).subtype_mk _
  map_zero_left p := by
    apply Subtype.ext
    change (extendedSidePush side (0, bulkToExtended side p)).val = p.val
    exact congrArg (fun q : extendedSide side => q.val)
      (extendedSidePush_zero side (bulkToExtended side p))
  map_one_left _ := rfl

/-- Each actual extended side is continuously homotopy equivalent to its
bulk, and hence to the torus with its closed coordinate disk removed. -/
theorem extendedSide_bulk_homotopyEquivalence (side : Bool) :
    ((bulkToExtended side).comp (extendedToBulk side)).Homotopic
      (ContinuousMap.id (extendedSide side)) ∧
    ((extendedToBulk side).comp (bulkToExtended side)).Homotopic
      (ContinuousMap.id (bulkRegion side)) :=
  ⟨⟨(extendedSideToBulkHomotopy side).symm⟩, ⟨(bulkToExtendedHomotopy side).symm⟩⟩


/-- Map from the actual extended quotient side to the source's punctured
open torus U, using the genuine bulk homeomorphism. -/
def extendedToTorusBulk (side : Bool) :
    C(extendedSide side, ↥((closure removedDisk)ᶜ)) :=
  (bulkHomeomorph side : C(bulkRegion side, ↥((closure removedDisk)ᶜ))).comp
    (extendedToBulk side)

def torusBulkToExtended (side : Bool) :
    C(↥((closure removedDisk)ᶜ), extendedSide side) :=
  (bulkToExtended side).comp
    ((bulkHomeomorph side).symm : C(↥((closure removedDisk)ᶜ), bulkRegion side))

/-- The actual extended side and the source's torus complement have mutually
inverse continuous maps up to continuous homotopy. -/
theorem extendedSide_torusBulk_homotopyEquivalence (side : Bool) :
    ((torusBulkToExtended side).comp (extendedToTorusBulk side)).Homotopic
      (ContinuousMap.id (extendedSide side)) ∧
    ((extendedToTorusBulk side).comp (torusBulkToExtended side)).Homotopic
      (ContinuousMap.id ↥((closure removedDisk)ᶜ)) := by
  constructor
  · convert (extendedSide_bulk_homotopyEquivalence side).1 using 1
    apply ContinuousMap.ext
    intro p
    change bulkToExtended side
      ((bulkHomeomorph side).symm ((bulkHomeomorph side) (extendedToBulk side p))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  · have hh := (ContinuousMap.Homotopic.refl
        (bulkHomeomorph side : C(bulkRegion side, ↥((closure removedDisk)ᶜ)))).comp
      ((extendedSide_bulk_homotopyEquivalence side).2.comp
        (ContinuousMap.Homotopic.refl
          ((bulkHomeomorph side).symm : C(↥((closure removedDisk)ᶜ), bulkRegion side))))
    convert hh using 1
    · apply ContinuousMap.ext
      intro p
      rfl
    · apply ContinuousMap.ext
      intro p
      change p = (bulkHomeomorph side) ((bulkHomeomorph side).symm p)
      exact ((bulkHomeomorph side).apply_symm_apply p).symm

end SmoothManifolds.GenusTwoDeRhamGeometry

namespace SmoothManifolds.GenusTwoTorusGeometry
open ModelData SphereTorusData SphereTorus GenusTwoData GenusTwoAtlas
  MayerVietorisData Set TopologicalSpace
open scoped Topology

/-- The larger actual coordinate disk has radius 3/16. -/
def coordinateLargeDisk : Set (Euclidean 2) :=
  {x | squareSum x < (3/16 : ℝ)^2}

/-- The actual coordinate annulus between radii 1/8 and 3/16. -/
def coordinateAnnulus : Set (Euclidean 2) :=
  {x | (1/8 : ℝ)^2 < squareSum x ∧ squareSum x < (3/16 : ℝ)^2}

lemma coordinates_small_of_squareSum {x : Euclidean 2} {r : ℝ}
    (hr : 0 ≤ r) (hx : squareSum x < r^2) (j : Fin 2) : |x j| < r := by
  have hs : (x 0)^2 + (x 1)^2 < r^2 := by
    simpa [squareSum, Fin.sum_univ_two] using hx
  apply abs_lt_of_sq_lt_sq _ hr
  fin_cases j <;> dsimp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

lemma coordinateLargeDisk_open : IsOpen coordinateLargeDisk :=
  isOpen_lt (continuous_squareSum 2) continuous_const

lemma coordinateAnnulus_open : IsOpen coordinateAnnulus :=
  (isOpen_lt continuous_const (continuous_squareSum 2)).inter coordinateLargeDisk_open

lemma coordinateLargeDisk_small : coordinateLargeDisk ⊆ angleBox 0 (1/3) := by
  intro x hx j
  simpa only [Pi.zero_apply, sub_zero] using
    (coordinates_small_of_squareSum (by norm_num : (0:ℝ) ≤ 3/16) hx j).trans
      (by norm_num : (3:ℝ)/16 < 1/3)

lemma projection_mem_closure_removedDisk_iff {x : Euclidean 2}
    (hx : x ∈ angleBox 0 (1/3)) :
    quotientProjection 2 x ∈ closure removedDisk ↔ squareSum x ≤ (1/8 : ℝ)^2 := by
  rw [closure_removedDisk]
  constructor
  · rintro ⟨y,hy,he⟩
    change squareSum y ≤ (1/8 : ℝ)^2 at hy
    have hyb : y ∈ angleBox 0 (1/3) := by
      intro j
      simpa only [Pi.zero_apply, sub_zero] using
        (coordinates_le hy j).trans_lt (by norm_num : (1:ℝ)/8 < 1/3)
    have hxy := quotientProjection_injOn_box (0 : Euclidean 2)
      (by norm_num : (1:ℝ)/3 < 1/2) hyb hx he
    simpa only [hxy] using hy
  · intro h
    exact ⟨x,h,rfl⟩

/-- The actual open punctured torus, with boundary circle removed as well. -/
def torusExterior : Opens (FlatTorus 2) :=
  ⟨(closure removedDisk)ᶜ, isClosed_closure.isOpen_compl⟩

/-- The larger actual disk supplies the other open set of the torus cover. -/
def torusDisk : Opens (FlatTorus 2) :=
  ⟨quotientProjection 2 '' coordinateLargeDisk,
    (quotientProjection_isOpenQuotientMap 2).isOpenMap _ coordinateLargeDisk_open⟩

def torusCover : OpenCover (FlatTorus 2) where
  U := torusExterior
  V := torusDisk
  cover p := by
    by_cases hp : p ∈ closure removedDisk
    · right
      obtain ⟨x,hx,rfl⟩ := (closure_removedDisk ▸ hp)
      change squareSum x ≤ (1/8 : ℝ)^2 at hx
      exact ⟨x,lt_of_le_of_lt hx (by norm_num : (1/8 : ℝ)^2 < (3/16 : ℝ)^2),rfl⟩
    · exact Or.inl hp

lemma torusCover_overlap :
    ((torusCover.U ⊓ torusCover.V : Opens (FlatTorus 2)) : Set (FlatTorus 2)) =
      quotientProjection 2 '' coordinateAnnulus := by
  ext p
  constructor
  · rintro ⟨hp, x,hx,rfl⟩
    refine ⟨x,⟨?_,hx⟩,rfl⟩
    exact lt_of_not_ge (fun h => hp ((projection_mem_closure_removedDisk_iff
      (coordinateLargeDisk_small hx)).mpr h))
  · rintro ⟨x,⟨hx0,hx1⟩,rfl⟩
    exact ⟨fun h => (not_le_of_gt hx0)
      ((projection_mem_closure_removedDisk_iff (coordinateLargeDisk_small hx1)).mp h),
      x,hx1,rfl⟩

/-- Quotient projection is a genuine homeomorphism on any sufficiently small
open coordinate region; this retains the actual quotient topology. -/
def coordinateRegionHomeomorph (D : Set (Euclidean 2)) (hD : IsOpen D)
    (hsmall : D ⊆ angleBox 0 (1/3)) : D ≃ₜ (quotientProjection 2 '' D) := by
  let f : D → (quotientProjection 2 '' D) := fun x =>
    ⟨quotientProjection 2 x.val,⟨x.val,x.property,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact quotientProjection_injOn_box (0 : Euclidean 2)
        (by norm_num : (1:ℝ)/3 < 1/2) (hsmall x.property) (hsmall y.property)
        (congrArg Subtype.val hxy)
    · rintro ⟨p,x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  have hc : Continuous f :=
    ((quotientProjection_isOpenQuotientMap 2).continuous.comp continuous_subtype_val).subtype_mk _
  have ho : IsOpenMap f :=
    ((quotientProjection_isOpenQuotientMap 2).isOpenMap.comp hD.isOpenMap_subtype_val).codRestrict _
  exact (Equiv.ofBijective f hf).toHomeomorphOfContinuousOpen hc ho

/-- The disk in the torus has exactly the ordinary open disk topology. -/
def torusDiskHomeomorph : torusDisk ≃ₜ coordinateLargeDisk :=
  (coordinateRegionHomeomorph coordinateLargeDisk coordinateLargeDisk_open
    coordinateLargeDisk_small).symm

/-- The overlap in the actual torus cover has exactly the ordinary annulus topology. -/
def torusOverlapHomeomorph : (torusCover.U ⊓ torusCover.V : Opens (FlatTorus 2)) ≃ₜ coordinateAnnulus :=
  (Homeomorph.setCongr torusCover_overlap).trans
    (coordinateRegionHomeomorph coordinateAnnulus coordinateAnnulus_open
      (fun _ h => coordinateLargeDisk_small h.2)).symm

/-- The coordinate disk is the ordinary Euclidean L2 ball, not the sup-norm ball. -/
def coordinateDiskBallHomeomorph : coordinateLargeDisk ≃ₜ
    Metric.ball (0 : WithLp 2 (Euclidean 2)) (3/16 : ℝ) :=
  (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).symm.subtype (fun x => by
    change squareSum x < (3/16 : ℝ)^2 ↔
      (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).symm x ∈
        Metric.ball (0 : WithLp 2 (Euclidean 2)) (3/16 : ℝ)
    rw [Metric.mem_ball, dist_zero_right, squareSum_eq_norm_sq]
    exact sq_lt_sq₀ (norm_nonneg _) (by norm_num))

/-- The larger actual disk in the torus is contractible. -/
theorem torusDisk_contractible : ContractibleSpace torusDisk := by
  have hb : ContractibleSpace (Metric.ball (0 : WithLp 2 (Euclidean 2)) (3/16 : ℝ)) :=
    (convex_ball (0 : WithLp 2 (Euclidean 2)) (3/16 : ℝ)).contractibleSpace
      ⟨0,by norm_num⟩
  exact (torusDiskHomeomorph.trans coordinateDiskBallHomeomorph).contractibleSpace_iff.mpr hb

abbrev AnnulusRadius := Set.Ioo (1/8 : ℝ) (3/16 : ℝ)

def annulusRadius (x : coordinateAnnulus) : ℝ := Real.sqrt (squareSum x.val)

lemma annulusRadius_mem (x : coordinateAnnulus) : annulusRadius x ∈ AnnulusRadius := by
  have hs : 0 ≤ squareSum x.val := by
    unfold squareSum
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsq := Real.sq_sqrt hs
  have hn := Real.sqrt_nonneg (squareSum x.val)
  have h0 := x.property.1
  have h1 := x.property.2
  constructor <;> dsimp [annulusRadius] <;> nlinarith

lemma annulusRadius_pos (x : coordinateAnnulus) : 0 < annulusRadius x :=
  lt_trans (by norm_num) (annulusRadius_mem x).1

lemma normalized_annulus_sphere (x : coordinateAnnulus) :
    squareSum ((annulusRadius x)⁻¹ • x.val) = 1 := by
  have hs : 0 ≤ squareSum x.val := by
    unfold squareSum
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : (annulusRadius x)^2 = squareSum x.val := Real.sq_sqrt hs
  rw [squareSum_smul, ← he]
  field_simp [ne_of_gt (annulusRadius_pos x)]

/-- The annulus is genuinely the sphere of directions times its open radius interval. -/
def coordinateAnnulusSphereHomeomorph : coordinateAnnulus ≃ₜ Sphere 1 × AnnulusRadius where
  toFun x := (⟨(annulusRadius x)⁻¹ • x.val,normalized_annulus_sphere x⟩,
    ⟨annulusRadius x,annulusRadius_mem x⟩)
  invFun z := ⟨z.2.val • z.1.val, by
    change (1/8 : ℝ)^2 < squareSum (z.2.val • z.1.val) ∧
      squareSum (z.2.val • z.1.val) < (3/16 : ℝ)^2
    rw [show squareSum (z.2.val • z.1.val) = z.2.val^2 from by
      rw [squareSum_smul,z.1.property,mul_one]]
    constructor <;> nlinarith [z.2.property.1,z.2.property.2]⟩
  left_inv x := by
    apply Subtype.ext
    change annulusRadius x • ((annulusRadius x)⁻¹ • x.val) = x.val
    rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (annulusRadius_pos x)),one_smul]
  right_inv z := by
    have hz : 0 < z.2.val := lt_trans (by norm_num) z.2.property.1
    have hr : Real.sqrt (squareSum (z.2.val • z.1.val)) = z.2.val := by
      rw [squareSum_smul,z.1.property,mul_one,Real.sqrt_sq_eq_abs,abs_of_pos hz]
    apply Prod.ext
    · apply Subtype.ext
      change (Real.sqrt (squareSum (z.2.val • z.1.val)))⁻¹ • (z.2.val • z.1.val) = z.1.val
      rw [hr,smul_smul,inv_mul_cancel₀ (ne_of_gt hz),one_smul]
    · exact Subtype.ext hr
  continuous_toFun := by
    have hr : Continuous annulusRadius :=
      Real.continuous_sqrt.comp ((continuous_squareSum 2).comp continuous_subtype_val)
    exact ((hr.inv₀ (fun x => ne_of_gt (annulusRadius_pos x))).smul
      continuous_subtype_val).subtype_mk _ |>.prodMk (hr.subtype_mk _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)

/-- The source's actual S¹ and the period-one flat circle have their standard
quotient/product topology identification. -/
def sphereFlatCircleHomeomorph : Sphere 1 ≃ₜ FlatTorus 1 :=
  ((periodicAngleHomeomorph 1).trans (Homeomorph.funUnique (Fin 1) (Sphere 1))).symm

/-- The actual overlap is a cylinder over the specified standard flat circle. -/
def torusOverlapCylinderHomeomorph :
    (torusCover.U ⊓ torusCover.V : Opens (FlatTorus 2)) ≃ₜ FlatTorus 1 × AnnulusRadius :=
  torusOverlapHomeomorph.trans (coordinateAnnulusSphereHomeomorph.trans
    (sphereFlatCircleHomeomorph.prodCongr (Homeomorph.refl _)))

/-- Translating radius by its midpoint produces exactly the existing signed
collar interval of width 1/32. -/
def annulusRadiusCollarHomeomorph :
    AnnulusRadius ≃ₜ GenusTwoDeRhamGeometry.CollarInterval where
  toFun r := ⟨r.val - 5/32, by constructor <;> linarith [r.property.1,r.property.2]⟩
  invFun t := ⟨t.val + 5/32, by constructor <;> linarith [t.property.1,t.property.2]⟩
  left_inv r := Subtype.ext (sub_add_cancel r.val (5/32))
  right_inv t := Subtype.ext (add_sub_cancel_right t.val (5/32))
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.sub continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.add continuous_const

/-- The torus-cover overlap and constructed surface collar are homeomorphic,
so the already constructed collar retraction can be transported exactly. -/
def torusOverlapCollarHomeomorph :
    (torusCover.U ⊓ torusCover.V : Opens (FlatTorus 2)) ≃ₜ
      GenusTwoDeRhamGeometry.collarRegion :=
  torusOverlapCylinderHomeomorph.trans
    (((Homeomorph.funUnique (Fin 1) (AddCircle (1 : ℝ))).prodCongr
      annulusRadiusCollarHomeomorph).trans GenusTwoDeRhamGeometry.collarHomeomorph.symm)

open GenusTwoDeRhamGeometry

/-- The circle projection of the actual torus-cover annulus. -/
def torusOverlapCircleProjection : C((torusCover.U ⊓ torusCover.V : Opens (FlatTorus 2)), FlatTorus 1) where
  toFun p := collarCircleProjection (torusOverlapCollarHomeomorph p)
  continuous_toFun := collarCircleProjection.continuous.comp torusOverlapCollarHomeomorph.continuous

/-- A genuine middle circle inside the torus-cover annulus. -/
def torusOverlapCircleSection : C(FlatTorus 1, (torusCover.U ⊓ torusCover.V : Opens (FlatTorus 2))) where
  toFun z := torusOverlapCollarHomeomorph.symm (collarCircleSection z)
  continuous_toFun := torusOverlapCollarHomeomorph.symm.continuous.comp collarCircleSection.continuous

@[simp] theorem torusOverlapCircleProjection_section (z : FlatTorus 1) :
    torusOverlapCircleProjection (torusOverlapCircleSection z) = z := by
  change collarCircleProjection
    (torusOverlapCollarHomeomorph (torusOverlapCollarHomeomorph.symm (collarCircleSection z))) = z
  rw [Homeomorph.apply_symm_apply,collarCircleProjection_section]

/-- Transporting the already proved signed-collar contraction gives an actual
continuous annulus contraction through the stated quotient topology. -/
def torusOverlapCircleContraction : ContinuousMap.Homotopy
    (torusOverlapCircleSection.comp torusOverlapCircleProjection)
    (ContinuousMap.id (torusCover.U ⊓ torusCover.V : Opens (FlatTorus 2))) where
  toFun z := torusOverlapCollarHomeomorph.symm
    (collarCircleContraction (z.1,torusOverlapCollarHomeomorph z.2))
  continuous_toFun := torusOverlapCollarHomeomorph.symm.continuous.comp
    (collarCircleContraction.continuous.comp
      (continuous_fst.prodMk (torusOverlapCollarHomeomorph.continuous.comp continuous_snd)))
  map_zero_left p := by
    exact congrArg torusOverlapCollarHomeomorph.symm
      (collarCircleContraction.map_zero_left (torusOverlapCollarHomeomorph p))
  map_one_left p := by
    exact (congrArg torusOverlapCollarHomeomorph.symm
      (collarCircleContraction.map_one_left (torusOverlapCollarHomeomorph p))).trans
        (Homeomorph.symm_apply_apply _ _)

/-- The actual annulus and actual period-one standard circle are homotopy equivalent. -/
theorem torusOverlapCircle_homotopyEquivalence :
    ContinuousMap.Homotopic (torusOverlapCircleSection.comp torusOverlapCircleProjection)
      (ContinuousMap.id (torusCover.U ⊓ torusCover.V : Opens (FlatTorus 2))) ∧
    ContinuousMap.Homotopic (torusOverlapCircleProjection.comp torusOverlapCircleSection)
      (ContinuousMap.id (FlatTorus 1)) := by
  refine ⟨⟨torusOverlapCircleContraction⟩, ?_⟩
  have he : torusOverlapCircleProjection.comp torusOverlapCircleSection =
      ContinuousMap.id (FlatTorus 1) := by
    ext z i
    exact congrFun (torusOverlapCircleProjection_section z) i
  simpa only [he] using
    (ContinuousMap.Homotopic.refl (ContinuousMap.id (FlatTorus 1)))

/-- The genuine disk is nonempty, including the coordinate origin. -/
theorem torusDisk_nonempty : Nonempty torusDisk := by
  refine ⟨⟨quotientProjection 2 0,0,?_,rfl⟩⟩
  change squareSum (0 : Euclidean 2) < (3/16 : ℝ)^2
  norm_num [squareSum]

/-- The actual overlap is connected in its subspace topology. -/
theorem torusOverlap_connected :
    ConnectedSpace (torusCover.U ⊓ torusCover.V : Opens (FlatTorus 2)) := by
  letI : ConnectedSpace collarRegion :=
    isConnected_iff_connectedSpace.mp collarRegion_connected
  exact torusOverlapCollarHomeomorph.symm.surjective.connectedSpace
    torusOverlapCollarHomeomorph.symm.continuous
end SmoothManifolds.GenusTwoTorusGeometry








namespace SmoothManifolds.GenusTwoTorusGeometry
open ModelData AtlasData MapData BundleOperationsData CovectorData ExteriorData DeRhamData
  SphereTorusData MayerVietorisData GenusTwoOpenCohomology GenusTwoHomotopyCohomology

/-- The actual torus-cover overlap has the ordinary circle cohomology. -/
theorem torus_overlap_cohomology
    (htorus : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType)
    {S : SmoothManifold 2 .euclidean (FlatTorus 2)} {C : CotangentBundle S}
    {B : ∀ k, FormBundle C k} (K : Calculus C B)
    (D : CoverComplex K torusCover) :
    Nonempty (D.onOverlap.complex.H 1 ≃ₗ[ℝ] ℝ) ∧
      ∀ k : ℕ, 1 < k → Subsingleton (D.onOverlap.complex.H k) := by
  classical
  obtain ⟨R,A,E,J,_,_,hJ⟩ := open_intrinsic_cohomology_exists K D.onOverlap
  obtain ⟨T,_,hT⟩ := (SphereTorus.angleManifold 1).2.2
  obtain ⟨A₁⟩ := BundleOperations.exists_cotangent T
  let E₁ : ∀ k, FormBundle A₁ k := fun k =>
    Classical.choice (ExteriorAlgebraResults.exists_formBundle A₁ k)
  obtain ⟨J₁⟩ := DeRhamResults.complex_exists A₁ E₁
  have hEq (k : ℕ) : Nonempty (J.Cohomology k ≃ₗ[ℝ] J₁.Cohomology k) :=
    continuous_homotopy_equivalence R T A A₁ E E₁ J J₁
      torusOverlapCircleProjection torusOverlapCircleSection
      torusOverlapCircle_homotopyEquivalence.1 torusOverlapCircle_homotopyEquivalence.2 k
  constructor
  · obtain ⟨eO⟩ := hJ 1
    obtain ⟨eH⟩ := hEq 1
    obtain ⟨eT⟩ := GenusTwoDeRhamResults.torus_degree_one htorus 1 T hT A₁ E₁ J₁
    exact ⟨((eO.trans eH).trans eT).trans (LinearEquiv.funUnique (Fin 1) ℝ ℝ)⟩
  · intro k hk
    obtain ⟨eO⟩ := hJ k
    obtain ⟨eH⟩ := hEq k
    letI : Subsingleton (J₁.Cohomology k) := DeRhamResults.above_dimension J₁ k hk
    exact (eO.trans eH).injective.subsingleton

/-- The disk side of the actual torus cover has zero positive cohomology. -/
theorem torus_disk_positive_vanishing
    {S : SmoothManifold 2 .euclidean (FlatTorus 2)} {C : CotangentBundle S}
    {B : ∀ k, FormBundle C k} (K : Calculus C B)
    (D : CoverComplex K torusCover) (k : ℕ) (hk : 0 < k) :
    Subsingleton (D.onV.complex.H k) := by
  letI : Nonempty ↥torusCover.V := torusDisk_nonempty
  letI : ContractibleSpace ↥torusCover.V := torusDisk_contractible
  exact open_contractible_vanishing K D.onV k hk

/-- Actual overlap connectedness supplies degree-zero difference surjectivity. -/
theorem torus_difference_zero_surjective
    {S : SmoothManifold 2 .euclidean (FlatTorus 2)} {C : CotangentBundle S}
    {B : ∀ k, FormBundle C k} (K : Calculus C B)
    (D : CoverComplex K torusCover) : Function.Surjective (D.sequence.q.onH 0) := by
  letI : ConnectedSpace ↥(torusCover.U ⊓ torusCover.V) := torusOverlap_connected
  exact degree_zero_difference_surjective K D
end SmoothManifolds.GenusTwoTorusGeometry


namespace SmoothManifolds.GenusTwoTorusGeometry
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
  SphereTorusData GenusTwoData MayerVietorisData GenusTwoMayerVietoris

/-- The punctured-torus computation from a genuine nonzero top class supported
inside the removed disk. The final theorem constructs this class below. -/
theorem torus_exterior_cohomology_of_supported_class
    (htorus : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType)
    (S : SmoothManifold 2 .euclidean (FlatTorus 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
    (D : CoverComplex K torusCover) (ω : K.closed 2)
    (hsupp : sectionSupport ω.val.val ⊆ removedDisk) (hn : K.classOf 2 ω ≠ 0) :
    Nonempty (D.onU.complex.H 1 ≃ₗ[ℝ] (Fin 2 → ℝ)) ∧
      Subsingleton (D.onU.complex.H 2) ∧
      D.sequence.q.onH 1 = 0 := by
  obtain ⟨hOverlap,hOverlapHigh⟩ := torus_overlap_cohomology htorus K D
  obtain ⟨eOverlap⟩ := hOverlap
  obtain ⟨eT2⟩ := GenusTwoDeRhamResults.torus_degree_two htorus S hS C B K
  letI : Subsingleton (D.onOverlap.complex.H 2) := hOverlapHigh 2 (by decide)
  letI : Subsingleton (D.onV.complex.H 1) := torus_disk_positive_vanishing K D 1 (by decide)
  letI : Subsingleton (D.onV.complex.H 2) := torus_disk_positive_vanishing K D 2 (by decide)
  have hωU (p : torusCover.U) : ω.val.val p.val = 0 := by
    by_contra hp
    have hmem : p.val ∈ sectionSupport ω.val.val := subset_closure hp
    exact p.property (subset_closure (hsupp hmem))
  have hr := cover_class_in_kernel D 2 ω hωU
  obtain ⟨hRes,hMiddle,hQ1⟩ := punctured_torus_of_kernel_class D.sequence
    (torus_difference_zero_surjective K D) eOverlap eT2 (K.classOf 2 ω) hn hr
  obtain ⟨eRes⟩ := hRes
  obtain ⟨eT1⟩ := GenusTwoDeRhamResults.torus_degree_one htorus 2 S hS C B K
  let eDrop : (D.onU.complex.H 1 × D.onV.complex.H 1) ≃ₗ[ℝ] D.onU.complex.H 1 :=
    LinearEquiv.ofBijective (LinearMap.fst ℝ _ _) ⟨by
      intro x y hxy
      exact Prod.ext hxy (Subsingleton.elim _ _), by
      intro x
      exact ⟨(x,0),rfl⟩⟩
  let eU : D.onU.complex.H 1 ≃ₗ[ℝ] (Fin 2 → ℝ) :=
    (eRes.trans ((D.onU.complex.productHEquiv D.onV.complex 1).trans eDrop)).symm.trans eT1
  have hU2 : Subsingleton (D.onU.complex.H 2) := by
    letI : Subsingleton ((D.onU.complex.prod D.onV.complex).H 2) := hMiddle
    have hp : Subsingleton (D.onU.complex.H 2 × D.onV.complex.H 2) :=
      (D.onU.complex.productHEquiv D.onV.complex 2).symm.injective.subsingleton
    exact ⟨fun x y => congrArg Prod.fst (@Subsingleton.elim _ hp (x,0) (y,0))⟩
  exact ⟨⟨eU⟩,hU2,hQ1⟩
end SmoothManifolds.GenusTwoTorusGeometry

namespace SmoothManifolds.GenusTwoDeRhamGeometry
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
  GenusTwoData SphereTorusData MayerVietorisData GenusTwoOpenCohomology
  GenusTwoHomotopyCohomology GenusTwoTorusGeometry

/-- The actual side cohomology transports from any genuine intrinsic model
of the torus exterior, using the constructed continuous collar push. -/
theorem surface_side_cohomology_of_exterior_model
    {S : SmoothManifold 2 .euclidean Surface} {C : CotangentBundle S}
    {B : ∀ k, FormBundle C k} (K : Calculus C B) (side : Bool)
    (D : OpenCalculus C B (extendedSide side))
    (R : SmoothManifold 2 .euclidean torusExterior) (A : CotangentBundle R)
    (E : ∀ k, FormBundle A k) (J : Calculus A E)
    (h1 : Nonempty (J.Cohomology 1 ≃ₗ[ℝ] (Fin 2 → ℝ)))
    (h2 : Subsingleton (J.Cohomology 2)) :
    Nonempty (D.complex.H 1 ≃ₗ[ℝ] (Fin 2 → ℝ)) ∧
      Subsingleton (D.complex.H 2) := by
  classical
  obtain ⟨P, CP, BP, KP, _, _, hD⟩ := open_intrinsic_cohomology_exists K D
  have htop := extendedSide_torusBulk_homotopyEquivalence side
  have hEq (k : ℕ) : Nonempty (KP.Cohomology k ≃ₗ[ℝ] J.Cohomology k) :=
    continuous_homotopy_equivalence P R CP A BP E KP J
      (extendedToTorusBulk side) (torusBulkToExtended side) htop.1 htop.2 k
  constructor
  · obtain ⟨eD⟩ := hD 1
    obtain ⟨eH⟩ := hEq 1
    obtain ⟨eT⟩ := h1
    exact ⟨(eD.trans eH).trans eT⟩
  · obtain ⟨eD⟩ := hD 2
    obtain ⟨eH⟩ := hEq 2
    letI : Subsingleton (J.Cohomology 2) := h2
    exact (eD.trans eH).injective.subsingleton

end SmoothManifolds.GenusTwoDeRhamGeometry

section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SmoothManifolds.GenusTwoBump
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData LocalIntegrationData GlobalIntegrationData OrientationData
  BoundaryData SphereTorusData TorusDeRhamData GenusTwoData Set
/-- An oriented compact boundaryless manifold has a nonzero ordinary top
class supported in every nonempty open set. -/
theorem supported_nonzero_top_class
    {n : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold (n+1) .euclidean M) (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (K : Calculus C B)
    (o : Orientation S) (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (U : Set M) (hU : IsOpen U) (x : M) (hx : x ∈ U) :
    ∃ ω : K.closed (n+1), sectionSupport ω.val.val ⊆ U ∧
      K.classOf (n+1) ω ≠ 0 := by
  classical
  obtain ⟨η,hη,hηsupp,hηpos⟩ := supported_positive_top_form S C (B (n+1)) o I hI U hU x hx
  let ω : K.closed (n+1) := ⟨⟨η.field,(K.mem_forms (n+1) η.field).mpr hη⟩, by
    apply Subtype.ext
    funext p
    change K.D (n+1) η.field p = 0
    exact ExteriorAlgebraResults.fields_above_dimension (S := S) C ((n+1)+1)
      (by omega) (K.D (n+1) η.field) p⟩
  have hn : K.classOf (n+1) ω ≠ 0 := GenusTwoPeriods.integral_ne_zero_class_ne_zero
    S C B K o I hI (intrinsicBoundary_euclidean S) ω η rfl (ne_of_gt hηpos)
  exact ⟨ω,hηsupp,hn⟩


end SmoothManifolds.GenusTwoBump

end

namespace SmoothManifolds.GenusTwoBump
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData LocalIntegrationData GlobalIntegrationData OrientationData
  BoundaryData SphereTorusData TorusDeRhamData GenusTwoData Set

/-- An orientation supplies the integral needed for a supported nonzero class,
with all integration data constructed on an arbitrary compact manifold. -/
theorem oriented_supported_nonzero_top_class
    {n : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M]
    (S : SmoothManifold (n+1) .euclidean M) (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (K : Calculus C B) (o : Orientation S)
    (U : Set M) (hU : IsOpen U) (x : M) (hx : x ∈ U) :
    ∃ ω : K.closed (n+1), sectionSupport ω.val.val ⊆ U ∧
      K.classOf (n+1) ω ≠ 0 := by
  obtain ⟨I,hI,_⟩ := GlobalIntegrationResults.exists_integral S o
  exact supported_nonzero_top_class S C B K o I hI U hU x hx

/-- A nonzero ordinary top class on the standard torus supported in its removed disk. -/
theorem torus_disk_supported_class
    (htorus : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType)
    (S : SmoothManifold 2 .euclidean (FlatTorus 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B) :
    ∃ ω : K.closed 2, sectionSupport ω.val.val ⊆ removedDisk ∧ K.classOf 2 ω ≠ 0 := by
  classical
  let o : Orientation S := Classical.choice (torus_orientation htorus S hS C B K)
  have hx : quotientProjection 2 0 ∈ removedDisk := by
    refine ⟨0, ?_, rfl⟩
    norm_num [squareSum]
  exact oriented_supported_nonzero_top_class (n := 1) S C B K o removedDisk
    GenusTwoAtlas.isOpen_removedDisk (quotientProjection 2 0) hx
end SmoothManifolds.GenusTwoBump

namespace SmoothManifolds.GenusTwoTorusGeometry
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
  SphereTorusData MayerVietorisData

/-- Full degree-one and degree-two cohomology of the actual punctured torus.
The nonzero disk-supported top class is constructed by integration and Stokes. -/
theorem torus_exterior_groups
    (htorus : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType)
    (S : SmoothManifold 2 .euclidean (FlatTorus 2))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas 2))
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
    (D : CoverComplex K torusCover) :
    Nonempty (D.onU.complex.H 1 ≃ₗ[ℝ] (Fin 2 → ℝ)) ∧
      Subsingleton (D.onU.complex.H 2) := by
  obtain ⟨ω,hsupp,hn⟩ :=
    GenusTwoBump.torus_disk_supported_class htorus S hS C B K
  obtain ⟨h1,h2,_⟩ := torus_exterior_cohomology_of_supported_class htorus S hS C B K D ω hsupp hn
  exact ⟨h1,h2⟩

/-- One genuine intrinsic calculus on the actual open punctured torus, with
its complete positive-degree cohomology calculation through dimension two. -/
theorem torus_exterior_intrinsic_model
    (htorus : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType) :
    ∃ (R : SmoothManifold 2 .euclidean torusExterior) (A : CotangentBundle R)
      (E : ∀ k, FormBundle A k) (J : Calculus A E),
      Nonempty (J.Cohomology 1 ≃ₗ[ℝ] (Fin 2 → ℝ)) ∧
        Subsingleton (J.Cohomology 2) := by
  classical
  obtain ⟨S,_,hS⟩ := (SphereTorus.angleManifold 2).2.2
  obtain ⟨C⟩ := BundleOperations.exists_cotangent S
  let B : ∀ k, FormBundle C k := fun k =>
    Classical.choice (ExteriorAlgebraResults.exists_formBundle C k)
  obtain ⟨K,D,_⟩ := MayerVietorisResults.cover_sequence_exists S C B torusCover
  obtain ⟨h1,h2⟩ := torus_exterior_groups htorus S hS C B K D
  obtain ⟨R,A,E,J,_,_,hEq⟩ :=
    GenusTwoOpenCohomology.open_intrinsic_cohomology_exists K D.onU
  obtain ⟨e1⟩ := hEq 1
  obtain ⟨e2⟩ := hEq 2
  obtain ⟨eU1⟩ := h1
  letI : Subsingleton (D.onU.complex.H 2) := h2
  exact ⟨R,A,E,J,⟨e1.symm.trans eU1⟩,e2.symm.injective.subsingleton⟩
end SmoothManifolds.GenusTwoTorusGeometry


namespace SmoothManifolds.GenusTwoBump
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
  LocalIntegrationData GlobalIntegrationData OrientationData Set

set_option maxHeartbeats 2000000 in
/-- Every nonempty compact oriented boundaryless manifold has a nonzero
ordinary top class. All point choices and existence eliminations are made
at the generic manifold type. -/
theorem oriented_top_class_nonzero
    {n : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M] [Nonempty M]
    (S : SmoothManifold (n+1) .euclidean M) (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (K : Calculus C B) (o : Orientation S) :
    ∃ ω : K.closed (n+1), K.classOf (n+1) ω ≠ 0 := by
  classical
  obtain ⟨ω,_,hn⟩ := oriented_supported_nonzero_top_class S C B K o
    Set.univ isOpen_univ (Classical.arbitrary M) (Set.mem_univ _)
  exact ⟨ω,hn⟩

end SmoothManifolds.GenusTwoBump

namespace SmoothManifolds.GenusTwoDeRhamResults
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData GenusTwoData

/-- Nonzero top cohomology of the actual oriented genus-two quotient. -/
theorem surface_top_class_nonzero
    (S : SmoothManifold 2 .euclidean Surface)
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) constructionAtlas)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B) :
    ∃ ω : K.closed 2, K.classOf 2 ω ≠ 0 := by
  exact GenusTwoBump.oriented_top_class_nonzero (n := 1) (M := Surface) S C B K
    (GenusTwoOrientation.orientation_exists S hS).choose

end SmoothManifolds.GenusTwoDeRhamResults

namespace SmoothManifolds.GenusTwoDeRhamResults
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
  GenusTwoData MayerVietorisData GenusTwoMayerVietoris GenusTwoDeRhamGeometry

/-- The side-group computation suffices for both original positive
cohomology groups. Nonzero top integration forces BOTH restrictions to vanish. -/
theorem surface_cohomology_from_sides
    (htorus : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType)
    (S : SmoothManifold 2 .euclidean Surface)
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) constructionAtlas)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
    (D : CoverComplex K surfaceCover)
    (eU : D.onU.complex.H 1 ≃ₗ[ℝ] (Fin 2 → ℝ))
    (eV : D.onV.complex.H 1 ≃ₗ[ℝ] (Fin 2 → ℝ))
    [Subsingleton (D.onU.complex.H 2)] [Subsingleton (D.onV.complex.H 2)] :
    Nonempty (K.Cohomology 1 ≃ₗ[ℝ] (Fin 4 → ℝ)) ∧
      Nonempty (K.Cohomology 2 ≃ₗ[ℝ] ℝ) := by
  obtain ⟨eO⟩ := (surface_overlap_cohomology htorus K D).1
  let eB := D.onU.complex.productHEquiv D.onV.complex 2
  letI : Subsingleton ((D.onU.complex.prod D.onV.complex).H 2) := eB.injective.subsingleton
  obtain ⟨ω,hω⟩ := surface_top_class_nonzero S hS C B K
  have hδ := connecting_bijective_of_nontrivial D.sequence 1 eO (K.classOf 2 ω) hω
  have hQ := difference_eq_zero_of_injective_delta D.sequence 1 hδ.1
  obtain ⟨hU,hV⟩ := restrictions_zero_of_difference_zero D 1 hQ
  exact ⟨degree_one_of_cover D (surface_difference_zero_surjective K D) hU hV eU eV,
    degree_two_of_cover D hU hV eO⟩
end SmoothManifolds.GenusTwoDeRhamResults

namespace SmoothManifolds.GenusTwoDeRhamGeometry
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
  GenusTwoData MayerVietorisData
/-- Both low positive cohomology groups of each actual extended side.
Only the complete frozen torus algebra is a conditional premise. -/
theorem surface_side_cohomology
    (htorus : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType)
    {S : SmoothManifold 2 .euclidean Surface} {C : CotangentBundle S}
    {B : ∀ k, FormBundle C k} (K : Calculus C B) (side : Bool)
    (D : OpenCalculus C B (extendedSide side)) :
    Nonempty (D.complex.H 1 ≃ₗ[ℝ] (Fin 2 → ℝ)) ∧
      Subsingleton (D.complex.H 2) := by
  obtain ⟨R,A,E,J,h1,h2⟩ := GenusTwoTorusGeometry.torus_exterior_intrinsic_model htorus
  exact surface_side_cohomology_of_exterior_model K side D R A E J h1 h2

end SmoothManifolds.GenusTwoDeRhamGeometry

namespace SmoothManifolds.GenusTwoDeRhamResults
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData DeRhamData
  GenusTwoData MayerVietorisData GenusTwoDeRhamGeometry

/-- Both positive-degree computations for the actual constructed surface,
using its genuine cover and the full conditional torus algebra premise. -/
theorem surface_positive_cohomology
    (htorus : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType)
    (S : SmoothManifold 2 .euclidean Surface)
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) constructionAtlas)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B) :
    Nonempty (K.Cohomology 1 ≃ₗ[ℝ] (Fin 4 → ℝ)) ∧
      Nonempty (K.Cohomology 2 ≃ₗ[ℝ] ℝ) := by
  obtain ⟨D,_⟩ := surface_cover_complex K
  obtain ⟨⟨eU⟩,hU2⟩ := surface_side_cohomology htorus K false D.onU
  obtain ⟨⟨eV⟩,hV2⟩ := surface_side_cohomology htorus K true D.onV
  letI : Subsingleton (D.onU.complex.H 2) := hU2
  letI : Subsingleton (D.onV.complex.H 2) := hV2
  exact surface_cohomology_from_sides htorus S hS C B K D eU eV

/-- Exact conditional form of the original degree-one conclusion. -/
theorem degree_one_conditional
    (htorus : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType) :
    Specs.SmoothManifolds.DeRham.GenusTwoSurface.degree_oneType := by
  intro S hS C B K
  exact (surface_positive_cohomology htorus S hS C B K).1

/-- Exact conditional form of the original degree-two conclusion. -/
theorem degree_two_conditional
    (htorus : Specs.SmoothManifolds.DeRham.Tori.torus_algebraType) :
    Specs.SmoothManifolds.DeRham.GenusTwoSurface.degree_twoType := by
  intro S hS C B K
  exact (surface_positive_cohomology htorus S hS C B K).2

end SmoothManifolds.GenusTwoDeRhamResults

theorem _root_.«SmoothManifolds».«GenusTwoDeRhamResults».«degree_one» : _root_.«Specs».«SmoothManifolds».«DeRham».«GenusTwoSurface».«degree_oneType» :=
  @_root_.«SmoothManifolds».«GenusTwoDeRhamResults».«degree_one_conditional» (@_root_.«SmoothManifolds».«TorusDeRhamResults».«torus_algebra»)
theorem _root_.«SmoothManifolds».«GenusTwoDeRhamResults».«degree_two» : _root_.«Specs».«SmoothManifolds».«DeRham».«GenusTwoSurface».«degree_twoType» :=
  @_root_.«SmoothManifolds».«GenusTwoDeRhamResults».«degree_two_conditional» (@_root_.«SmoothManifolds».«TorusDeRhamResults».«torus_algebra»)
theorem _root_.«SmoothManifolds».«GenusTwoDeRhamResults».«degree_zero» : _root_.«Specs».«SmoothManifolds».«DeRham».«GenusTwoSurface».«degree_zeroType» :=
  @_root_.«SmoothManifolds».«GenusTwoDeRhamResults».«degree_zero_conditional» (@_root_.«SmoothManifolds».«TorusDeRhamResults».«torus_algebra»)
theorem _root_.«SmoothManifolds».«GenusTwoDeRhamResults».«other_degrees» : _root_.«Specs».«SmoothManifolds».«DeRham».«GenusTwoSurface».«other_degreesType» :=
  @_root_.«SmoothManifolds».«GenusTwoDeRhamResults».«other_degrees_conditional» (@_root_.«SmoothManifolds».«TorusDeRhamResults».«torus_algebra»)
