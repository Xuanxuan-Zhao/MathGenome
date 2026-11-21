import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.TopDegree
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.DoubleCover
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.CompactSupport
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.Global
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.SmoothDescent
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Tensors
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.Maps.Proper.Basic

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.NoncompactTopDegree
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.OrientedTopDegree
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
noncomputable section
open scoped Classical Topology

namespace SmoothManifolds.TopDegreeResults
open ModelData AtlasData MapData TangentData DifferentialData
  BundleOperationsData CovectorData ExteriorData DeRhamData MayerVietorisData
  CompactSupportData OrientationData OrientationCoverData CoveringData
  BoundaryData Set Filter
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- Every point has both determinant rays, including in dimension zero. -/
theorem projection_surjective (S : SmoothManifold n a M) :
    Function.Surjective (projection S) := by
  intro p
  let z := (OrientationCover.fiberEquiv S p).symm false
  exact ⟨z.val, z.property⟩

/-- Saturation of a set under the two-sheet projection is its union with its
translate by the actual deck involution. -/
theorem projection_saturation (S : SmoothManifold n a M) (F : Set (Space S)) :
    projection S ⁻¹' (projection S '' F) = F ∪ deck S ⁻¹' F := by
  ext z
  constructor
  · rintro ⟨w, hw, h⟩
    rcases OrientationCover.fiber_eq_or_deck w z h with he | he
    · exact Or.inl (he ▸ hw)
    · exact Or.inr (show deck S z ∈ F from he ▸ hw)
  · rintro (hz | hz)
    · exact ⟨z, hz, rfl⟩
    · exact ⟨deck S z, hz, rfl⟩

/-- The quotient by the two sheet exchange is closed. This avoids adding any
properness certificate to the covering construction. -/
theorem projection_closed (S : SmoothManifold n a M) :
    IsClosedMap (projection S) := by
  have hq := (OrientationCover.isCovering_projection (S := S)).isOpenMap.isQuotientMap
    OrientationCover.continuous_projection (projection_surjective S)
  intro F hF
  apply hq.isCoinducing.isClosed_preimage.mp
  rw [projection_saturation]
  exact hF.union (hF.preimage OrientationCover.continuous_deck)

/-- The actual orientation double cover is proper: it is closed and each
fiber has exactly two points. No compactness of the base is used. -/
theorem projection_proper (S : SmoothManifold n a M) :
    IsProperMap (projection S) := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨OrientationCover.continuous_projection, projection_closed S, ?_⟩
  intro p
  haveI : Finite ↥(projection S ⁻¹' {p}) :=
    Finite.of_equiv Bool (OrientationCover.fiberEquiv S p).symm
  exact (Set.toFinite _).isCompact

/-- A compact total space would have compact image equal to the whole base. -/
theorem cover_noncompact (S : SmoothManifold n a M)
    (hM : ¬ IsCompact (Set.univ : Set M)) :
    ¬ IsCompact (Set.univ : Set (Space S)) := by
  intro hE
  apply hM
  simpa only [Set.image_univ, (projection_surjective S).range_eq] using
    hE.image (OrientationCover.continuous_projection (S := S))


open FormPullbackData OrientationProductData TangentBundleData FrameData

/-- Pullback along an invertible fiber map has the contravariant inverse. -/
theorem fiberPullback_inverse {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (k : ℕ) (E : V ≃ₗ[ℝ] W)
    (ω : Fiber V k) :
    fiberPullback k E.toLinearMap (fiberPullback k E.symm.toLinearMap ω) = ω := by
  change ((exteriorPower.map k E.toLinearMap.dualMap).comp
    (exteriorPower.map k E.symm.toLinearMap.dualMap)) ω = ω
  rw [← exteriorPower.map_comp, LinearMap.dualMap_comp_dualMap]
  simp

theorem fiberPullback_injective {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (k : ℕ) (E : V ≃ₗ[ℝ] W) :
    Function.Injective (fiberPullback k E.toLinearMap) := by
  apply Function.LeftInverse.injective (g := fiberPullback k E.symm.toLinearMap)
  intro ω
  exact fiberPullback_inverse (V := W) (W := V) k E.symm ω

/-- Contravariant composition on the actual exterior fibers. -/
theorem fiberPullback_comp {V W U : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [AddCommGroup U] [Module ℝ U]
    (k : ℕ) (L : V →ₗ[ℝ] W) (R : W →ₗ[ℝ] U) (ω : Fiber U k) :
    fiberPullback k L (fiberPullback k R ω) = fiberPullback k (R.comp L) ω := by
  change ((exteriorPower.map k L.dualMap).comp (exteriorPower.map k R.dualMap)) ω = _
  rw [← exteriorPower.map_comp, LinearMap.dualMap_comp_dualMap]
  rfl

/-- The chosen ray is only for specifying a field; smoothness is proved by
local sheets, never by assuming a smooth global choice of ray. -/
def chosenRay (S : SmoothManifold n a M) (p : M) : DeterminantRay S p :=
  (Classical.choose (OrientationCover.local_exists (S := S) p)).ray
    ⟨p, Classical.choose_spec (OrientationCover.local_exists (S := S) p)⟩

def chosenLift (S : SmoothManifold n a M) (p : M) : Space S := ⟨p, chosenRay S p⟩

/-- Pullback by the orientation projection is injective on all fields. -/
theorem projection_pullback_injective
    (T : SmoothManifold n a (Space S))
    (E : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace S z.1) (k : ℕ) :
    Function.Injective (pullbackField T S (projection S)
      (fun z => (E z).toLinearMap) (k := k)) := by
  intro α β h
  have hp : ∀ z : Space S, α z.1 = β z.1 := by
    intro z
    have hz := congrFun h z
    change fiberPullback (V := TangentSpace T z) (W := TangentSpace S z.1)
      k (E z).toLinearMap (α z.1) =
      fiberPullback (V := TangentSpace T z) (W := TangentSpace S z.1)
      k (E z).toLinearMap (β z.1) at hz
    exact @fiberPullback_injective (TangentSpace T z) (TangentSpace S z.1)
      (inferInstance : AddCommGroup (TangentSpace T z))
      (inferInstance : Module ℝ (TangentSpace T z))
      (inferInstance : AddCommGroup (TangentSpace S z.1))
      (inferInstance : Module ℝ (TangentSpace S z.1))
      k (E z) (α z.1) (β z.1) hz
  funext p
  exact hp (chosenLift S p)

/-- Transport a cover field back along the actual dπ, pointwise. -/
def pushField (T : SmoothManifold n a (Space S))
    (E : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace S z.1)
    (k : ℕ) (β : Field T k) (z : Space S) : Fiber (TangentSpace S z.1) k :=
  fiberPullback (V := TangentSpace S z.1) (W := TangentSpace T z)
    k (E z).symm.toLinearMap (β z)

/-- A deck-invariant field gives the same pushed value on both sheets. -/
theorem pushField_deck
    (T : SmoothManifold n a (Space S)) (hT : IsSmoothCovering T S (projection S))
    (E : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace S z.1)
    (hE : ∀ z, IsDifferential T S (projection S) z (E z).toLinearMap)
    (F : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace T (deck S z))
    (hF : ∀ z, IsDifferential T T (deck S) z (F z).toLinearMap)
    (k : ℕ) (β : Field T k)
    (hβ : pullbackField T T (deck S) (fun z => (F z).toLinearMap) β = β)
    (z : Space S) : pushField T E k β (deck S z) = pushField T E k β z := by
  have heq : (E (deck S z)).toLinearMap.comp (F z).toLinearMap = (E z).toLinearMap := by
    exact (differential_exists T S (projection S) hT.2.1 z).unique
      (differential_comp T T S (deck S) (projection S)
        (OrientationCover.smooth_deck T hT) hT.2.1 z _ _ (hF z) (hE (deck S z))) (hE z)
  have hinv : (F z).toLinearMap.comp (E z).symm.toLinearMap =
      (E (deck S z)).symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    apply (E (deck S z)).injective
    calc
      (E (deck S z)) ((F z) ((E z).symm v)) = (E z) ((E z).symm v) :=
        congrArg (fun L => L ((E z).symm v)) heq
      _ = v := (E z).apply_symm_apply v
      _ = (E (deck S z)) ((E (deck S z)).symm v) :=
        ((E (deck S z)).apply_symm_apply v).symm
  have hi := congrFun hβ z
  change fiberPullback (V := TangentSpace T z) (W := TangentSpace T (deck S z))
    k (F z).toLinearMap (β (deck S z)) = β z at hi
  unfold pushField
  rw [← hi]
  rw [fiberPullback_comp (V := TangentSpace S z.1) (W := TangentSpace T z)
    (U := TangentSpace T (deck S z)) k (E z).symm.toLinearMap (F z).toLinearMap,
    hinv]


def descendField (T : SmoothManifold n a (Space S))
    (E : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace S z.1)
    (k : ℕ) (β : Field T k) : Field S k :=
  fun p => pushField T E k β (chosenLift S p)

/-- The local-sheet gluing equation: the choice of lift drops out because
there are exactly two rays and the pushed field agrees under their exchange. -/
theorem descendField_value
    (T : SmoothManifold n a (Space S))
    (E : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace S z.1)
    (k : ℕ) (β : Field T k)
    (hβ : ∀ z, pushField T E k β (deck S z) = pushField T E k β z)
    (z : Space S) : descendField T E k β z.1 = pushField T E k β z := by
  rcases z with ⟨p, r⟩
  rcases OrientationResults.determinant_ray_eq_or_neg S p r (chosenRay S p) with hr | hr
  · subst r
    rfl
  · subst r
    exact (hβ (chosenLift S p)).symm

/-- Pullback of the descended field is the original invariant field. -/
theorem pullback_descendField
    (T : SmoothManifold n a (Space S))
    (E : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace S z.1)
    (k : ℕ) (β : Field T k)
    (hβ : ∀ z, pushField T E k β (deck S z) = pushField T E k β z) :
    pullbackField T S (projection S) (fun z => (E z).toLinearMap)
      (descendField T E k β) = β := by
  funext z
  change fiberPullback (V := TangentSpace T z) (W := TangentSpace S z.1)
    k (E z).toLinearMap (descendField T E k β z.1) = β z
  have hv := descendField_value T E k β hβ z
  calc
    fiberPullback (V := TangentSpace T z) (W := TangentSpace S z.1)
        k (E z).toLinearMap (descendField T E k β z.1) =
      fiberPullback (V := TangentSpace T z) (W := TangentSpace S z.1)
        k (E z).toLinearMap (pushField T E k β z) := congrArg _ hv
    _ = β z := by
      change ((exteriorPower.map k (E z).toLinearMap.dualMap).comp
        (exteriorPower.map k (E z).symm.toLinearMap.dualMap)) (β z) = β z
      rw [← exteriorPower.map_comp, LinearMap.dualMap_comp_dualMap]
      simp only [LinearEquiv.symm_comp, LinearMap.dualMap_id,
        exteriorPower.map_id, LinearMap.id_apply]

/-- Descent preserves compact support. The support is contained in the compact
projection of the support upstairs, using closedness of the projection. -/
theorem descendField_compact_support
    (T : SmoothManifold n a (Space S))
    (E : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace S z.1)
    (k : ℕ) (β : Field T k) (hc : IsCompact (sectionSupport β)) :
    IsCompact (sectionSupport (descendField T E k β)) := by
  apply (hc.image (OrientationCover.continuous_projection (S := S))).of_isClosed_subset
    isClosed_closure
  apply closure_minimal
  · intro p hp
    refine ⟨chosenLift S p, ?_, rfl⟩
    apply subset_closure
    intro hz
    apply hp
    change fiberPullback (V := TangentSpace S p)
      (W := TangentSpace T (chosenLift S p)) k (E (chosenLift S p)).symm.toLinearMap
      (β (chosenLift S p)) = 0
    rw [hz, map_zero]
  · exact projection_closed S _ isClosed_closure

/-- The deck map, with its actual inverse and smoothness on the cover atlas. -/
def deckDiffeomorph (T : SmoothManifold n a (Space S))
    (hT : IsSmoothCovering T S (projection S)) :
    Diffeomorph T.smoothStructure.val T.smoothStructure.val where
  toEquiv := (OrientationCover.deckHomeomorph (S := S)).toEquiv
  contDiff_toFun := OrientationCover.smooth_deck T hT
  contDiff_invFun := OrientationCover.smooth_deck T hT

/-- An invariant compact top form on the canonically oriented cover has zero
integral. The sign comes from the actual differential of the sheet exchange. -/
theorem invariant_cover_integral_zero
    (T : SmoothManifold n a (Space S))
    (hT : IsSmoothCovering T S (projection S))
    (o : Orientation T) (ho : IsTautologicalOrientation T o)
    (F : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace T (deck S z))
    (hF : ∀ z, IsDifferential T T (deck S) z (F z).toLinearMap)
    (I : LocalIntegrationData.CompactTopForm T → ℝ)
    (hI : GlobalIntegrationData.IsIntegral o I)
    (η : LocalIntegrationData.CompactTopForm T)
    (hη : FormPullbackData.pullbackField T T (deck S)
      (fun z => (F z).toLinearMap) η.field = η.field) : I η = 0 := by
  have hrev := (OrientationCover.deck S T hT).2.2.2.2 o ho F hF
  have hsign : ∀ z, OrientationProductData.orientationSign o o F z = false := by
    intro z
    apply if_neg
    rw [hrev z]
    exact fun h => Module.Ray.ne_neg_self (o.val (deck S z)) h.symm
  have heq := GlobalIntegrationResults.constant_sign_substitution T T
    (deckDiffeomorph T hT) o o F hF false hsign I I hI hI η η hη.symm
  norm_num [OrientationData.signValue] at heq
  linarith

/-- Vanishing of all representatives implies vanishing of the actual quotient. -/
theorem cochain_cohomology_subsingleton (A : Cochain.{u}) (k : ℕ)
    (h : ∀ x : A.Obj k, x ∈ A.exact k) : Subsingleton (A.H k) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := A.class_surjective k x
  obtain ⟨y, rfl⟩ := A.class_surjective k y
  exact ((A.class_zero_iff k x).mpr (h x.val)).trans
    ((A.class_zero_iff k y).mpr (h y.val)).symm

/-- On a compact manifold every ordinary representative lies in the image of
the full compact complex, so compact exactness gives ordinary exactness. -/
theorem ordinary_exact_of_compact [CompactSpace M]
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} (K : Calculus C B)
    (D : CompactCalculus K ⊤) (k : ℕ)
    (h : ∀ x : D.complex.Obj k, x ∈ D.complex.exact k) :
    ∀ ω : K.forms k, ω ∈ K.exact k := by
  intro ω
  obtain ⟨x, hx⟩ := (D.range k ω).mp
    ⟨isClosed_closure.isCompact, Set.subset_univ _⟩
  have he := D.inclusion.maps_exact k x (h x)
  rw [hx] at he
  cases k <;> exact he

/-- The remaining compact ordinary clause follows from the nonorientable
compact-support clause, using actual full range of the compact complex. -/
theorem compact_nonorientable_of_compact_support
    (h : Specs.SmoothManifolds.DeRham.TopDegree.nonorientable_compact_supportType.{u}) :
    Specs.SmoothManifolds.DeRham.TopDegree.compact_nonorientableType.{u} := by
  intro n a M _ _ _ S hb hn C B K
  let D := CompactSupportResults.supportedCalculus K ⊤
  have he := ordinary_exact_of_compact K D n (h S hb hn C B K D).1
  refine ⟨he, ?_⟩
  exact cochain_cohomology_subsingleton (globalComplex K) n (by
    intro ω
    cases n <;> exact he ω)

/-- Average a primitive in a real complex with its translate by an involutive
chain map. Invariance of its derivative is exactly what is needed. -/
theorem average_primitive (A : Cochain.{u}) (f : ChainMap A A)
    (hf : ∀ k, Function.Involutive (f.map k)) (k : ℕ) (β : A.Obj k)
    (hβ : f.map (k+1) (A.d k β) = A.d k β) :
    let γ := (2 : ℝ)⁻¹ • (β + f.map k β)
    A.d k γ = A.d k β ∧ f.map k γ = γ := by
  dsimp only
  constructor
  · rw [map_smul, map_add, f.comm, hβ, ← two_smul ℝ (A.d k β), smul_smul]
    norm_num
  · rw [map_smul, map_add, hf k β, add_comm (f.map k β) β]


/-- Independence of the chosen representative of the differential, including
when the smooth map is rewritten by a function equality. -/
theorem pullback_map_congr
    {m : ℕ} {b : ModelKind} {N : Type u} [TopologicalSpace N]
    (T : SmoothManifold m b N) (f g : M → N)
    (hf : IsSmoothMap S T f) (hg : IsSmoothMap S T g)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (R : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (g p))
    (hL : ∀ p, IsDifferential S T f p (L p))
    (hR : ∀ p, IsDifferential S T g p (R p)) (heq : f = g)
    (k : ℕ) (ω : Field T k) : pullbackField S T f L ω = pullbackField S T g R ω := by
  subst g
  have hLR : L = R := by
    funext p
    exact (differential_exists S T f hf p).unique (hL p) (hR p)
  rw [hLR]

/-- The actual deck pullback is an involution on fields in every degree. -/
theorem deck_pullback_involutive
    (T : SmoothManifold n a (Space S)) (hT : IsSmoothCovering T S (projection S))
    (F : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace T (deck S z))
    (hF : ∀ z, IsDifferential T T (deck S) z (F z).toLinearMap) (k : ℕ) :
    Function.Involutive (pullbackField T T (deck S) (fun z => (F z).toLinearMap) (k := k)) := by
  intro ω
  have hs := OrientationCover.smooth_deck T hT
  have hh : IsSmoothMap T T (deck S ∘ deck S) :=
    manifoldContDiff_comp _ _ _ _ T.smoothStructure.property.1.1 _ _ hs hs
  let H := differential T T (deck S ∘ deck S) hh
  have hH := differential_spec T T (deck S ∘ deck S) hh
  have hid : IsSmoothMap T T id := manifoldContDiff_id _ _ T.smoothStructure.property.1
  have heq : deck S ∘ deck S = id := funext OrientationCover.deck_involutive
  have hcomp := FormPullbackResults.pullback_comp T T T (deck S) (deck S)
    hs hs (fun z => (F z).toLinearMap) (fun z => (F z).toLinearMap) H hF hF hH k ω
  rw [← hcomp]
  rw [pullback_map_congr T (deck S ∘ deck S) id hh hid H (fun _ => LinearMap.id)
    hH (differential_id T) heq k ω]
  exact FormPullbackResults.pullback_id T (fun _ => LinearMap.id) (differential_id T) k ω

/-- Every pulled-back base field is deck-invariant, by π ∘ τ = π. -/
theorem projection_pullback_invariant
    (T : SmoothManifold n a (Space S)) (hT : IsSmoothCovering T S (projection S))
    (E : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace S z.1)
    (hE : ∀ z, IsDifferential T S (projection S) z (E z).toLinearMap)
    (F : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace T (deck S z))
    (hF : ∀ z, IsDifferential T T (deck S) z (F z).toLinearMap)
    (k : ℕ) (ω : Field S k) :
    pullbackField T T (deck S) (fun z => (F z).toLinearMap)
      (pullbackField T S (projection S) (fun z => (E z).toLinearMap) ω) =
      pullbackField T S (projection S) (fun z => (E z).toLinearMap) ω := by
  exact (FormPullbackResults.pullback_comp T T S (deck S) (projection S)
    (OrientationCover.smooth_deck T hT) hT.2.1 (fun z => (F z).toLinearMap)
    (fun z => (E z).toLinearMap) (fun z => (E z).toLinearMap) hF hE hE k ω).symm

/-- Smooth local inverse germs for the actual orientation projection. -/
theorem projection_inverse_germs
    (T : SmoothManifold n a (Space S)) (hT : IsSmoothCovering T S (projection S)) :
    TensorData.IsLocalDiffeomorphism T S (projection S) := by
  refine ⟨hT.2.1, ?_⟩
  intro z
  obtain ⟨e, hz, he, _, hinv⟩ :=
    OrientationCover.smoothCovering_localDiffeomorphism T hT z
  have hp : projection S z ∈ e.target := by
    rw [← he hz]
    exact e.map_source hz
  refine ⟨e.symm, hinv _ hp, ?_, ?_, ?_⟩
  · rw [← he hz]
    exact e.left_inv hz
  · filter_upwards [e.open_source.mem_nhds hz] with w hw
    change e.symm (projection S w) = w
    rw [← he hw]
    exact e.left_inv hw
  · filter_upwards [e.open_target.mem_nhds hp] with p hp
    change projection S (e.symm p) = p
    rw [← he (e.map_target hp)]
    exact e.right_inv hp

/-- Pointwise inverse transport of a smooth cover form is a smooth map into
the base exterior bundle. Its coordinate matrix is the transpose of the
inverse Jacobian of π; no global smooth choice of sheet occurs here. -/
theorem pushField_section_smooth
    (T : SmoothManifold n a (Space S)) (hT : IsSmoothCovering T S (projection S))
    (C : CotangentBundle S) (D : CotangentBundle T) (k : ℕ)
    (A : FormBundle C k) (B : FormBundle D k)
    (E : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace S z.1)
    (hE : ∀ z, IsDifferential T S (projection S) z (E z).toLinearMap)
    (β : Field T k) (hβ : IsForm B β) :
    letI := (cotangentSpace C).topology
    letI := A.space.topology
    IsSmoothMap T A.space.bundle.totalManifold
      (fun z => (⟨z.1, pushField T E k β z⟩ : Bundle.TotalSpace
        (Euclidean (n.choose k)) (fun p => Fiber (TangentSpace S p) k))) := by
  classical
  letI := (cotangentSpace C).topology
  letI := A.space.topology
  letI := (cotangentSpace D).topology
  letI := B.space.topology
  intro p
  obtain ⟨e, he, hp⟩ := T.smoothStructure.property.1.1 p
  obtain ⟨c, hc, hfp⟩ := S.smoothStructure.property.1.1 p.1
  let Jinv (z : Space S) :=
    ContinuousLinearMap.inverse (FiniteRegularityData.chartDerivative e c (projection S) z)
  have hJinv : VectorSmoothAt T.smoothStructure.val Jinv p :=
    Tensors.inverse_chartDerivative_smoothAt T S (projection S)
      (projection_inverse_germs T hT) e c he hc p hp hfp
  let J : Space S → Euclidean n →L[ℝ] Euclidean n := fun z =>
    QuotientBundles.columnOperator (fun j i => Jinv z (Pi.single i 1) j)
  have hJ : VectorSmoothAt T.smoothStructure.val J p := by
    apply BundleOperations.columnOperator_smooth
    intro j
    apply VectorSmoothAt.pi
    intro i
    exact (hJinv.clm_apply (VectorSmoothAt.const _ (Pi.single i 1) p)).postcomp
      (ContinuousLinearMap.proj j).contDiff
  let v : Space S → Euclidean (n.choose k) := fun z =>
    ((B.space.bundle.trivialization ⟨e, he⟩) ⟨z, β z⟩).2
  have hv : VectorSmoothAt T.smoothStructure.val v p := by
    apply (Frames.trivializationCoordinates_smoothAt B.space.bundle ⟨e, he⟩
      ⟨p, β p⟩ (by rw [B.baseSet, Covectors.cotangent_baseSet]; exact hp)).comp
      (g := fun z => (⟨z, β z⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
        (fun z => Fiber (TangentSpace T z) k)))
      B.space.bundle.totalManifold.smoothStructure.property.1.1 (hβ p)
  have hout := FormPullbackResults.exterior_image_smooth B.modelEquiv A.modelEquiv hJ hv
  apply Frames.smoothAt_from_trivialization A.space.bundle T.smoothStructure.property.1
    ⟨c, hc⟩ (by rw [A.baseSet, Covectors.cotangent_baseSet]; exact hfp)
    (hT.2.1 p) hout (fun _ => rfl)
  filter_upwards [e.open_source.mem_nhds hp,
    (hT.2.1 p).1.preimage_mem_nhds (c.open_source.mem_nhds hfp)] with z hze hzc
  change z.1 ∈ c.source at hzc
  have hzC : z.1 ∈ (cotangentSpace C).bundle.baseSet ⟨c, hc⟩ := by
    rw [Covectors.cotangent_baseSet]; exact hzc
  have hzD : z ∈ (cotangentSpace D).bundle.baseSet ⟨e, he⟩ := by
    rw [Covectors.cotangent_baseSet]; exact hze
  let eC := (cotangentSpace C).bundle.fiberCoordinates ⟨c, hc⟩ z.1 hzC
  let eD := (cotangentSpace D).bundle.fiberCoordinates ⟨e, he⟩ z hzD
  have hinv (i : Fin n) : D.tangent.fiberCoordinates.equiv e he z hze
      ((E z).symm (coordinateVector C.tangent.fiberCoordinates c hc z.1 hzc i)) =
      Jinv z (Pi.single i 1) := by
    have h := Tensors.inverse_differential_coordinates S T (projection S)
      (projection_inverse_germs T hT) E hE C.tangent.fiberCoordinates
      D.tangent.fiberCoordinates c e hc he z hze hzc
      (coordinateVector C.tangent.fiberCoordinates c hc z.1 hzc i)
    simpa only [CovectorData.coordinateVector, LinearEquiv.apply_symm_apply,
      Jinv, OrientationCoverData.projection] using h.symm
  have heJ (lam : CotangentFiber T z) :
      J z (eD lam) = eC (lam.comp (E z).symm.toLinearMap) := by
    ext i
    have heval := congrArg (fun α : CotangentFiber T z =>
        α ((E z).symm (coordinateVector C.tangent.fiberCoordinates c hc z.1 hzc i)))
      (Covectors.covector_expansion D.tangent.fiberCoordinates e he z hze lam)
    simpa [J, QuotientBundles.columnOperator_apply, eC, eD,
      BundleData.SmoothVectorBundle.fiberCoordinates_apply,
      Covectors.cotangent_coordinates C c hc z.1 hzc,
      Covectors.cotangent_coordinates D e he z hze,
      CovectorData.coordinateCovector, hinv i] using heval.symm
  have heLin : eC.toLinearMap.comp (E z).symm.toLinearMap.dualMap =
      (J z).toLinearMap.comp eD.toLinearMap := by
    ext lam i
    exact congrFun (heJ lam).symm i
  have heMap := congrArg (fun F => exteriorPower.map k F (β z)) heLin
  simp only [exteriorPower.map_comp, LinearMap.comp_apply] at heMap
  change ((A.space.bundle.trivialization ⟨c, hc⟩)
      ⟨z.1, fiberPullback (V := TangentSpace S z.1) (W := TangentSpace T z)
        k (E z).symm.toLinearMap (β z)⟩).2 =
    A.modelEquiv (exteriorPower.map k (J z).toLinearMap (B.modelEquiv.symm (v z)))
  rw [FormPullbackResults.form_coordinates C k A c hc z.1 hzc]
  have hvval : v z = B.modelEquiv (exteriorPower.map k eD.toLinearMap (β z)) :=
    FormPullbackResults.form_coordinates D k B e he z hze (β z)
  rw [hvval, LinearEquiv.symm_apply_apply]
  exact congrArg A.modelEquiv heMap

/-- Every point of the base has an actual smooth inverse branch on an open
neighborhood, constructed from an evenly covered sheet. -/
theorem projection_has_local_sections
    (T : SmoothManifold n a (Space S)) (hT : IsSmoothCovering T S (projection S)) :
    SmoothDescentData.HasSmoothLocalSections T S (projection S) := by
  intro p
  let z := chosenLift S p
  obtain ⟨e, hz, he, _, hinv⟩ :=
    OrientationCover.smoothCovering_localDiffeomorphism T hT z
  have hp : p ∈ e.target := by
    change projection S z ∈ e.target
    rw [← he hz]
    exact e.map_source hz
  refine ⟨e.target, e.open_target, hp, (fun y => e.symm y.val), ?_, ?_⟩
  · exact (manifoldContDiff_restrict_open (⊤ : ℕ∞) S.smoothStructure.val
      T.smoothStructure.val e.symm e.target e.open_target).mp hinv
  · intro y
    rw [← he (e.map_target y.property)]
    exact e.right_inv y.property

/-- A smooth invariant cover form descends smoothly. Equality on the two sheets
was proved in `descendField_value`; the local sections verify smooth gluing. -/
theorem descendField_smooth
    (T : SmoothManifold n a (Space S)) (hT : IsSmoothCovering T S (projection S))
    (C : CotangentBundle S) (D : CotangentBundle T) (k : ℕ)
    (A : FormBundle C k) (B : FormBundle D k)
    (E : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace S z.1)
    (hE : ∀ z, IsDifferential T S (projection S) z (E z).toLinearMap)
    (β : Field T k) (hs : IsForm B β)
    (hi : ∀ z, pushField T E k β (deck S z) = pushField T E k β z) :
    IsForm A (descendField T E k β) := by
  letI := (cotangentSpace C).topology
  letI := A.space.topology
  apply SmoothDescent.smooth_of_comp T S A.space.bundle.totalManifold (projection S) _
    (projection_has_local_sections T hT)
  convert pushField_section_smooth T hT C D k A B E hE β hs using 1
  funext z
  exact congrArg (fun w => (⟨z.1, w⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
      (fun p => Fiber (TangentSpace S p) k))) (descendField_value T E k β hi z)

/-- Naturality and injectivity of pullback turn a descended primitive into a
primitive downstairs, retaining compact support whenever it was present. -/
theorem descend_primitive
    (T : SmoothManifold n a (Space S)) (hT : IsSmoothCovering T S (projection S))
    (C : CotangentBundle S) (D : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (A : ∀ k, FormBundle D k)
    (K : Calculus C B) (J : Calculus D A)
    (E : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace S z.1)
    (hE : ∀ z, IsDifferential T S (projection S) z (E z).toLinearMap)
    (F : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace T (deck S z))
    (hF : ∀ z, IsDifferential T T (deck S) z (F z).toLinearMap)
    (k : ℕ) (β : J.forms k) (ω : K.forms (k+1))
    (hi : pullbackField T T (deck S) (fun z => (F z).toLinearMap) β.val = β.val)
    (hd : J.D k β.val =
      pullbackField T S (projection S) (fun z => (E z).toLinearMap) ω.val) :
    ∃ γ : K.forms k, K.d k γ = ω ∧
      (IsCompact (sectionSupport β.val) → IsCompact (sectionSupport γ.val)) := by
  have hpush := pushField_deck T hT E hE F hF k β.val hi
  have hs := descendField_smooth T hT C D k (B k) (A k) E hE β.val
    ((J.mem_forms k _).mp β.property) hpush
  let γ : K.forms k := ⟨descendField T E k β.val, (K.mem_forms k _).mpr hs⟩
  refine ⟨γ, ?_, fun hc => descendField_compact_support T E k β.val hc⟩
  apply Subtype.ext
  apply projection_pullback_injective T E (k+1)
  have hn := ExteriorDerivativeResults.smooth_naturality T S D C A B J.D K.D
    J.axioms K.axioms (projection S) hT.2.1 (fun z => (E z).toLinearMap) hE
    k γ.val hs
  change pullbackField T S (projection S) (fun z => (E z).toLinearMap)
    (K.D k γ.val) = _
  rw [hn, pullback_descendField T E k β.val hpush]
  exact hd


open private smoothPull smoothPull_chain from MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Algebra

/-- The ordinary intrinsic pullback as a chain map, reusing the original
smooth pullback and its proved naturality. -/
def ordinaryPullback
    {m : ℕ} {b : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m b N} {C : CotangentBundle S} {D : CotangentBundle T}
    {B : ∀ k, FormBundle C k} {A : ∀ k, FormBundle D k}
    (K : Calculus C B) (J : Calculus D A) (f : M → N)
    (hf : IsSmoothMap S T f)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p)) :
    ChainMap (globalComplex J) (globalComplex K) where
  map := smoothPull K J f hf L hL
  comm k ω := (smoothPull_chain K J f hf L hL
    (@ExteriorDerivativeResults.smooth_naturality.{u}) k ω).symm

/-- A chain map representing the deck pullback is involutive, because its
field realization is injective and the actual deck field pullback squares to id. -/
theorem chain_involutive_of_field
    (T : SmoothManifold n a (Space S)) (hT : IsSmoothCovering T S (projection S))
    (F : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace T (deck S z))
    (hF : ∀ z, IsDifferential T T (deck S) z (F z).toLinearMap)
    (A : Cochain.{u}) (r : ∀ k, A.Obj k → Field T k)
    (hr : ∀ k, Function.Injective (r k)) (f : ChainMap A A)
    (hfield : ∀ k x, r k (f.map k x) =
      pullbackField T T (deck S) (fun z => (F z).toLinearMap) (r k x)) :
    ∀ k, Function.Involutive (f.map k) := by
  intro k x
  apply hr k
  rw [hfield, hfield]
  exact deck_pullback_involutive T hT F hF k (r k x)

/-- A zero-dimensional manifold always admits the constant positive orientation. -/
theorem zero_dim_orientable {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) : Nonempty (Orientation S) := by
  obtain ⟨e, _⟩ := OrientationResults.zero_dimension S
  exact ⟨e.symm (fun _ => true)⟩

/-- All cover geometry here is derived from the actual canonical ray cover. -/
theorem nonorientable_cover_geometry [ConnectedSpace M]
    (hb : intrinsicBoundary S = ∅) (hn : ¬ Nonempty (Orientation S)) :
    ∃ T : SmoothManifold n a (Space S),
      IsSmoothCovering T S (projection S) ∧ intrinsicBoundary T = ∅ ∧
      ConnectedSpace (Space S) ∧
      ∃ o : Orientation T, IsTautologicalOrientation T o ∧
      ∃ E : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace S z.1,
        (∀ z, IsDifferential T S (projection S) z (E z).toLinearMap) ∧
      ∃ F : ∀ z, TangentSpace T z ≃ₗ[ℝ] TangentSpace T (deck S z),
        ∀ z, IsDifferential T T (deck S) z (F z).toLinearMap := by
  obtain ⟨_, _, T, _, hT, hloc, hbd, _⟩ := OrientationCover.construction S
  obtain ⟨o, ho, _⟩ := OrientationCover.canonical_orientation S T hT
  obtain ⟨E, hE, _⟩ := OrientationProducts.local_differential T S (projection S) hloc
  obtain ⟨F, hF, _⟩ := GlobalIntegrationResults.diffeomorphism_differential T T
    (deckDiffeomorph T hT)
  refine ⟨T, hT, ?_, (OrientationCover.connected_classification S).2.mpr hn,
    o, ho, E, hE, F, hF⟩
  change BoundaryData.intrinsicBoundary T = ∅
  change BoundaryData.intrinsicBoundary S = ∅ at hb
  rw [hbd, hb]
  rfl


/-- Nonorientable compact-support vanishing derived from the full oriented
zero-integral exactness premise on the canonical connected cover. -/
private theorem nonorientable_compact_support_proof
    (hexact : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u}) :
    Specs.SmoothManifolds.DeRham.TopDegree.nonorientable_compact_supportType.{u} := by
  intro n a M _ _ S hb hn C B K D
  cases n with
  | zero => exact (hn (zero_dim_orientable S)).elim
  | succ k =>
    obtain ⟨T, hT, hbT, hconn, o, ho, E, hE, F, hF⟩ :=
      nonorientable_cover_geometry (S := S) hb hn
    letI := hconn
    obtain ⟨Ct⟩ := BundleOperations.exists_cotangent T
    let A : ∀ j, FormBundle Ct j := fun j =>
      Classical.choice (ExteriorAlgebraResults.exists_formBundle Ct j)
    obtain ⟨J⟩ := DeRhamResults.complex_exists Ct A
    let G := CompactSupportResults.supportedCalculus J ⊤
    obtain ⟨P⟩ := CompactSupportResults.proper_pullback T S Ct C A B J K G D
      (projection S) hT.2.1 (projection_proper S) (fun z => (E z).toLinearMap) hE
    obtain ⟨Q⟩ := CompactSupportResults.proper_pullback T T Ct Ct A A J J G G
      (deck S) (OrientationCover.smooth_deck T hT)
      (OrientationCover.deckHomeomorph (S := S)).isProperMap
      (fun z => (F z).toLinearMap) hF
    have hr : ∀ j, Function.Injective
        (fun x : G.complex.Obj j => (G.inclusion.map j x).val) := by
      intro j x y h
      exact G.injective j (Subtype.ext h)
    have hf := chain_involutive_of_field T hT F hF G.complex
      (fun j x => (G.inclusion.map j x).val) hr Q.chain Q.field
    obtain ⟨I, hI, _⟩ := GlobalIntegrationResults.exists_integral T o
    have hevery : ∀ ω : D.complex.Obj (k+1), ω ∈ D.complex.exact (k+1) := by
      intro ω
      let x := P.chain.map (k+1) ω
      have hxfield : (G.inclusion.map (k+1) x).val =
          pullbackField T S (projection S) (fun z => (E z).toLinearMap)
            (D.inclusion.map (k+1) ω).val := P.field (k+1) ω
      obtain ⟨η, hη, heq⟩ := hexact T hbT o Ct A J G I hI x
      have hinv : pullbackField T T (deck S) (fun z => (F z).toLinearMap) η.field =
          η.field := by
        rw [hη, hxfield]
        exact projection_pullback_invariant T hT E hE F hF (k+1) _
      have hxexact := heq.mpr (invariant_cover_integral_zero T hT o ho F hF I hI η hinv)
      obtain ⟨b, hb⟩ := hxexact
      have hxInv : Q.chain.map (k+1) x = x := by
        apply hr (k+1)
        exact (Q.field (k+1) x).trans
          ((congrArg (FormPullbackData.pullbackField T T (deck S)
              (fun z => (F z).toLinearMap) (k := k+1)) hxfield).trans
            ((projection_pullback_invariant T hT E hE F hF (k+1)
              (D.inclusion.map (k+1) ω).val).trans hxfield.symm))
      have hbInv : Q.chain.map (k+1) (G.complex.d k b) = G.complex.d k b := by
        rw [hb, hxInv]
      let bavg : G.complex.Obj k := (2 : ℝ)⁻¹ • (b + Q.chain.map k b)
      have havg := average_primitive G.complex Q.chain hf k b hbInv
      have hdavg : G.complex.d k bavg = x := havg.1.trans hb
      have hiavg : Q.chain.map k bavg = bavg := havg.2
      let bform : J.forms k := G.inclusion.map k bavg
      have hiField : pullbackField T T (deck S) (fun z => (F z).toLinearMap) bform.val =
          bform.val :=
        (Q.field k bavg).symm.trans
          (congrArg (fun y => (G.inclusion.map k y).val) hiavg)
      have hdField : J.D k bform.val =
          pullbackField T S (projection S) (fun z => (E z).toLinearMap)
            (D.inclusion.map (k+1) ω).val := by
        have heq : J.d k bform = G.inclusion.map (k+1) x :=
          (G.inclusion.comm k bavg).trans (congrArg (G.inclusion.map (k+1)) hdavg)
        exact (congrArg Subtype.val heq).trans hxfield
      obtain ⟨γ, hγ, hcγ⟩ := descend_primitive T hT C Ct B A K J E hE F hF k
        bform (D.inclusion.map (k+1) ω) hiField hdField
      have hcompact := hcγ (CompactSupportResults.inclusion_support G k bavg).1
      obtain ⟨c, hc⟩ := (D.range k γ).mp ⟨hcompact, Set.subset_univ _⟩
      refine ⟨c, ?_⟩
      apply D.injective (k+1)
      calc
        D.inclusion.map (k+1) (D.complex.d k c) = K.d k (D.inclusion.map k c) :=
          (D.inclusion.comm k c).symm
        _ = K.d k γ := congrArg (K.d k) hc
        _ = D.inclusion.map (k+1) ω := hγ
    exact ⟨hevery, cochain_cohomology_subsingleton D.complex (k+1) hevery⟩

/-- Ordinary vanishing without orientability, using unrestricted primitives
on the noncompact orientation cover and the proved smooth descent. -/
private theorem noncompact_proof
    (hNC : Specs.SmoothManifolds.DeRham.NoncompactTopDegree.top_degreeType.{u}) :
    Specs.SmoothManifolds.DeRham.TopDegree.noncompactType.{u} := by
  intro n a M _ _ S hb hnc C B K
  by_cases hor : Nonempty (Orientation S)
  · obtain ⟨o⟩ := hor
    exact hNC S hb o hnc C B K
  · cases n with
    | zero => exact (hor (zero_dim_orientable S)).elim
    | succ k =>
      obtain ⟨T, hT, hbT, hconn, o, ho, E, hE, F, hF⟩ :=
        nonorientable_cover_geometry (S := S) hb hor
      letI := hconn
      obtain ⟨Ct⟩ := BundleOperations.exists_cotangent T
      let A : ∀ j, FormBundle Ct j := fun j =>
        Classical.choice (ExteriorAlgebraResults.exists_formBundle Ct j)
      obtain ⟨J⟩ := DeRhamResults.complex_exists Ct A
      let P := ordinaryPullback J K (projection S) hT.2.1
        (fun z => (E z).toLinearMap) hE
      let Q := ordinaryPullback J J (deck S) (OrientationCover.smooth_deck T hT)
        (fun z => (F z).toLinearMap) hF
      have hP : ∀ j x, (P.map j x).val =
          pullbackField T S (projection S) (fun z => (E z).toLinearMap) x.val :=
        fun _ _ => rfl
      have hQ : ∀ j x, (Q.map j x).val =
          pullbackField T T (deck S) (fun z => (F z).toLinearMap) x.val :=
        fun _ _ => rfl
      have hf := chain_involutive_of_field T hT F hF (globalComplex J)
        (fun _ x => x.val) (fun _ => Subtype.val_injective) Q hQ
      have hUp := (hNC T hbT o (cover_noncompact S hnc) Ct A J).1
      have hevery : ∀ ω : K.forms (k+1), ω ∈ K.exact (k+1) := by
        intro ω
        let x := P.map (k+1) ω
        obtain ⟨b, hb⟩ := hUp x
        have hxInv : Q.map (k+1) x = x := by
          apply Subtype.ext
          exact (hQ (k+1) x).trans
            ((congrArg (FormPullbackData.pullbackField T T (deck S)
              (fun z => (F z).toLinearMap) (k := k+1))
                (hP (k+1) ω)).trans
              ((projection_pullback_invariant T hT E hE F hF (k+1) ω.val).trans
                (hP (k+1) ω).symm))
        have hbInv : Q.map (k+1) (J.d k b) = J.d k b := by rw [hb, hxInv]
        let bavg : J.forms k :=
          (2 : ℝ)⁻¹ • (b + (show J.forms k from Q.map k b))
        have havg := average_primitive (globalComplex J) Q hf k b hbInv
        have hdavg : J.d k bavg = x := havg.1.trans hb
        have hiavg : Q.map k bavg = bavg := havg.2
        have hiField : pullbackField T T (deck S) (fun z => (F z).toLinearMap) bavg.val =
            bavg.val := (hQ k bavg).symm.trans (congrArg Subtype.val hiavg)
        have hdField : J.D k bavg.val =
            pullbackField T S (projection S) (fun z => (E z).toLinearMap) ω.val :=
          (congrArg Subtype.val hdavg).trans (hP (k+1) ω)
        obtain ⟨γ, hγ, _⟩ := descend_primitive T hT C Ct B A K J E hE F hF k
          bavg ω hiField hdField
        exact ⟨γ, hγ⟩
      refine ⟨hevery, ?_⟩
      exact cochain_cohomology_subsingleton (globalComplex K) (k+1) hevery

/-- Conditional derivation using exactly the ordered frozen upstream premises. -/
theorem nonorientable_compact_support_conditional
    (hNC : Specs.SmoothManifolds.DeRham.NoncompactTopDegree.top_degreeType.{u})
    (hComparison : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_comparisonType.{u})
    (hCompact : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u})
    (hExact : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    (hOriented : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u})
    (hZero : Specs.SmoothManifolds.DeRham.OrientedTopDegree.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.DeRham.TopDegree.nonorientable_compact_supportType.{u} := by
  exact nonorientable_compact_support_proof hExact

/-- Conditional derivation using exactly the ordered frozen upstream premises. -/
theorem noncompact_conditional
    (hNC : Specs.SmoothManifolds.DeRham.NoncompactTopDegree.top_degreeType.{u})
    (hComparison : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_comparisonType.{u})
    (hCompact : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u})
    (hExact : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    (hOriented : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u})
    (hZero : Specs.SmoothManifolds.DeRham.OrientedTopDegree.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.DeRham.TopDegree.noncompactType.{u} := by
  exact noncompact_proof hNC

/-- Conditional derivation using exactly the ordered frozen upstream premises. -/
theorem compact_nonorientable_conditional
    (hNC : Specs.SmoothManifolds.DeRham.NoncompactTopDegree.top_degreeType.{u})
    (hComparison : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_comparisonType.{u})
    (hCompact : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u})
    (hExact : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    (hOriented : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u})
    (hZero : Specs.SmoothManifolds.DeRham.OrientedTopDegree.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.DeRham.TopDegree.compact_nonorientableType.{u} := by
  exact compact_nonorientable_of_compact_support (nonorientable_compact_support_proof hExact)

/-- Conditional derivation using exactly the ordered frozen upstream premises. -/
theorem full_top_degree_conditional
    (hNC : Specs.SmoothManifolds.DeRham.NoncompactTopDegree.top_degreeType.{u})
    (hComparison : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_comparisonType.{u})
    (hCompact : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u})
    (hExact : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    (hOriented : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u})
    (hZero : Specs.SmoothManifolds.DeRham.OrientedTopDegree.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.DeRham.TopDegree.full_top_degreeType.{u} := by
  exact ⟨hOriented, hExact, hComparison, hCompact, hZero, noncompact_proof hNC,
    nonorientable_compact_support_proof hExact,
    compact_nonorientable_of_compact_support (nonorientable_compact_support_proof hExact)⟩

end SmoothManifolds.TopDegreeResults

universe v8_closure_0123e74d99211b73_u0
theorem _root_.«SmoothManifolds».«TopDegreeResults».«compact_nonorientable» : _root_.«Specs».«SmoothManifolds».«DeRham».«TopDegree».«compact_nonorientableType».{v8_closure_0123e74d99211b73_u0} :=
  @_root_.«SmoothManifolds».«TopDegreeResults».«compact_nonorientable_conditional».{v8_closure_0123e74d99211b73_u0} (@_root_.«SmoothManifolds».«NoncompactTopDegreeResults».«top_degree».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_comparison».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_top_degree».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«exact_iff_integral_zero».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«top_degree».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«zero_dimension».{v8_closure_0123e74d99211b73_u0})
theorem _root_.«SmoothManifolds».«TopDegreeResults».«full_top_degree» : _root_.«Specs».«SmoothManifolds».«DeRham».«TopDegree».«full_top_degreeType».{v8_closure_0123e74d99211b73_u0} :=
  @_root_.«SmoothManifolds».«TopDegreeResults».«full_top_degree_conditional».{v8_closure_0123e74d99211b73_u0} (@_root_.«SmoothManifolds».«NoncompactTopDegreeResults».«top_degree».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_comparison».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_top_degree».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«exact_iff_integral_zero».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«top_degree».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«zero_dimension».{v8_closure_0123e74d99211b73_u0})
theorem _root_.«SmoothManifolds».«TopDegreeResults».«noncompact» : _root_.«Specs».«SmoothManifolds».«DeRham».«TopDegree».«noncompactType».{v8_closure_0123e74d99211b73_u0} :=
  @_root_.«SmoothManifolds».«TopDegreeResults».«noncompact_conditional».{v8_closure_0123e74d99211b73_u0} (@_root_.«SmoothManifolds».«NoncompactTopDegreeResults».«top_degree».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_comparison».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_top_degree».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«exact_iff_integral_zero».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«top_degree».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«zero_dimension».{v8_closure_0123e74d99211b73_u0})
theorem _root_.«SmoothManifolds».«TopDegreeResults».«nonorientable_compact_support» : _root_.«Specs».«SmoothManifolds».«DeRham».«TopDegree».«nonorientable_compact_supportType».{v8_closure_0123e74d99211b73_u0} :=
  @_root_.«SmoothManifolds».«TopDegreeResults».«nonorientable_compact_support_conditional».{v8_closure_0123e74d99211b73_u0} (@_root_.«SmoothManifolds».«NoncompactTopDegreeResults».«top_degree».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_comparison».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_top_degree».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«exact_iff_integral_zero».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«top_degree».{v8_closure_0123e74d99211b73_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«zero_dimension».{v8_closure_0123e74d99211b73_u0})
