import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Independent domain-aware formulation of paper.tex, d13:01:coordinates.
A change of coordinates is given by ambient representatives, used only on
its specified open source and target. No global extension is required. -/
noncomputable section
open Set

namespace D13Unified

/-- A C¹ diffeomorphism between open subsets of real normed spaces. -/
structure C1Change (E G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] where
  source : Set E
  target : Set G
  open_source : IsOpen source
  open_target : IsOpen target
  forward : E → G
  inverse : G → E
  map_source : MapsTo forward source target
  map_target : MapsTo inverse target source
  left_inv : ∀ x ∈ source, inverse (forward x) = x
  right_inv : ∀ z ∈ target, forward (inverse z) = z
  forward_c1 : ContDiffOn ℝ 1 forward source
  inverse_c1 : ContDiffOn ℝ 1 inverse target

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The domain is Ω̃ intersected with the inverse image of the original
 time-state domain; the field is DH(H⁻¹z) f(t,H⁻¹z). -/
def ODE.inCoordinates (F : ODE E) (H : C1Change E G) : ODE G where
  domain := {p | p.2 ∈ H.target ∧ (p.1, H.inverse p.2) ∈ F.domain}
  isOpen_domain := by
    have hc : ContinuousOn (fun p : ℝ × G => (p.1, H.inverse p.2))
        (Prod.snd ⁻¹' H.target) :=
      continuousOn_fst.prodMk (H.inverse_c1.continuousOn.comp continuousOn_snd
        (fun _ hp => hp))
    exact hc.isOpen_inter_preimage (H.open_target.preimage continuous_snd) F.isOpen_domain
  field := fun p => fderiv ℝ H.forward (H.inverse p.val.2)
    (F.field ⟨(p.val.1, H.inverse p.val.2), p.property.2⟩)
  continuous_field := by
    have hi : Continuous (fun p : {p : ℝ × G |
        p.2 ∈ H.target ∧ (p.1, H.inverse p.2) ∈ F.domain} => H.inverse p.val.2) :=
      H.inverse_c1.continuousOn.comp_continuous
        (continuous_snd.comp continuous_subtype_val) (fun p => p.property.1)
    have hd := (H.forward_c1.continuousOn_fderiv_of_isOpen H.open_source le_rfl).comp_continuous
      hi (fun p => H.map_target p.property.1)
    exact hd.clm_apply (F.continuous_field.comp
      (((continuous_fst.comp continuous_subtype_val).prodMk hi).subtype_mk _))

/-- Pull back time and its domain. The velocity is θ′(r) f(θ(r),x). -/
def ODE.inTime (F : ODE E) (θ : C1Change ℝ ℝ) : ODE E where
  domain := {p | p.1 ∈ θ.source ∧ (θ.forward p.1, p.2) ∈ F.domain}
  isOpen_domain := by
    have hc : ContinuousOn (fun p : ℝ × E => (θ.forward p.1, p.2))
        (Prod.fst ⁻¹' θ.source) :=
      (θ.forward_c1.continuousOn.comp continuousOn_fst (fun _ hp => hp)).prodMk
        continuousOn_snd
    exact hc.isOpen_inter_preimage (θ.open_source.preimage continuous_fst) F.isOpen_domain
  field := fun p => deriv θ.forward p.val.1 •
    F.field ⟨(θ.forward p.val.1, p.val.2), p.property.2⟩
  continuous_field := by
    have ht : Continuous (fun p : {p : ℝ × E |
        p.1 ∈ θ.source ∧ (θ.forward p.1, p.2) ∈ F.domain} => θ.forward p.val.1) :=
      θ.forward_c1.continuousOn.comp_continuous
        (continuous_fst.comp continuous_subtype_val) (fun p => p.property.1)
    have hd : Continuous (fun p : {p : ℝ × E |
        p.1 ∈ θ.source ∧ (θ.forward p.1, p.2) ∈ F.domain} => deriv θ.forward p.val.1) :=
      (θ.forward_c1.continuousOn_deriv_of_isOpen θ.open_source le_rfl).comp_continuous
        (continuous_fst.comp continuous_subtype_val) (fun p => p.property.1)
    exact hd.smul (F.continuous_field.comp
      ((ht.prodMk (continuous_snd.comp continuous_subtype_val)).subtype_mk _))

/-- Actual-domain solution values. Existence of an ambient representative
is precisely the shared solution convention; off-interval values are ignored. -/
def SolutionValues (F : ODE E) (I : OpenTimeInterval) : Set (I.carrier → E) :=
  {v | ∃ x : ℝ → E,
    Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue F I x ∧
    ∀ t : I.carrier, x t = v t}

/-- Reflection of the actual time interval about zero. -/
def OpenTimeInterval.reflected (I : OpenTimeInterval) : OpenTimeInterval where
  carrier := (fun r : ℝ => -r) ⁻¹' I.carrier
  nonempty := by
    obtain ⟨t, ht⟩ := I.nonempty
    exact ⟨-t, by simpa using ht⟩
  ordConnected := I.ordConnected.preimage_anti (fun _ _ h => neg_le_neg h)
  isOpen := I.isOpen.preimage continuous_neg

/-- Negation as a diffeomorphism of bounded or unbounded open intervals. -/
def timeReflection (I : OpenTimeInterval) : C1Change ℝ ℝ where
  source := I.reflected.carrier
  target := I.carrier
  open_source := I.reflected.isOpen
  open_target := I.isOpen
  forward := fun r => -r
  inverse := fun t => -t
  map_source := fun _ h => h
  map_target := fun _ h => by simpa [OpenTimeInterval.reflected] using h
  left_inv := fun _ _ => neg_neg _
  right_inv := fun _ _ => neg_neg _
  forward_c1 := contDiff_id.neg.contDiffOn
  inverse_c1 := contDiff_id.neg.contDiffOn

/-- An intrinsic C¹ diffeomorphism of intervals of arbitrary endpoint type.
The displayed velocities are continuous within derivatives, so included
endpoints use their one-sided derivatives. No extension past an endpoint
or inverse-derivative identity is assumed. -/
structure IntervalClock (J I : TimeInterval) where
  forward : ℝ → ℝ
  inverse : ℝ → ℝ
  velocity : ℝ → ℝ
  inverseVelocity : ℝ → ℝ
  map_source : MapsTo forward J.carrier I.carrier
  map_target : MapsTo inverse I.carrier J.carrier
  left_inv : ∀ r ∈ J.carrier, inverse (forward r) = r
  right_inv : ∀ t ∈ I.carrier, forward (inverse t) = t
  continuous_forward : ContinuousOn forward J.carrier
  continuous_inverse : ContinuousOn inverse I.carrier
  continuous_velocity : ContinuousOn velocity J.carrier
  continuous_inverseVelocity : ContinuousOn inverseVelocity I.carrier
  hasDeriv_forward : ∀ r ∈ J.carrier, HasDerivWithinAt forward (velocity r) J.carrier r
  hasDeriv_inverse : ∀ t ∈ I.carrier, HasDerivWithinAt inverse (inverseVelocity t) I.carrier t

/-- Restrict an ambient clock to matching intervals, retaining its
ordinary derivatives as the within derivatives at any included endpoints. -/
def IntervalClock.restrictChange (θ : C1Change ℝ ℝ) (J I : TimeInterval)
    (hJ : J.carrier ⊆ θ.source) (hI : I.carrier ⊆ θ.target)
    (hf : MapsTo θ.forward J.carrier I.carrier)
    (hi : MapsTo θ.inverse I.carrier J.carrier) : IntervalClock J I where
  forward := θ.forward
  inverse := θ.inverse
  velocity := deriv θ.forward
  inverseVelocity := deriv θ.inverse
  map_source := hf
  map_target := hi
  left_inv := fun r hr => θ.left_inv r (hJ hr)
  right_inv := fun t ht => θ.right_inv t (hI ht)
  continuous_forward := θ.forward_c1.continuousOn.mono hJ
  continuous_inverse := θ.inverse_c1.continuousOn.mono hI
  continuous_velocity :=
    (θ.forward_c1.continuousOn_deriv_of_isOpen θ.open_source le_rfl).mono hJ
  continuous_inverseVelocity :=
    (θ.inverse_c1.continuousOn_deriv_of_isOpen θ.open_target le_rfl).mono hI
  hasDeriv_forward := fun _r hr =>
    (θ.forward_c1.differentiableOn_one.differentiableAt
      (θ.open_source.mem_nhds (hJ hr))).hasDerivAt.hasDerivWithinAt
  hasDeriv_inverse := fun _t ht =>
    (θ.inverse_c1.differentiableOn_one.differentiableAt
      (θ.open_target.mem_nhds (hI ht))).hasDerivAt.hasDerivWithinAt

/-- The transported equation on the actual interval J. This formulation also
applies when J includes an endpoint and the clock has no specified extension
past it; it retains the original ODE's graph condition after pullback. -/
def IsTimeChangedSolutionOn (F : ODE E) {J I : TimeInterval}
    (θ : IntervalClock J I) (y : ℝ → E) : Prop :=
  ContinuousOn y J.carrier ∧
  (∀ r ∈ J.carrier, (θ.forward r, y r) ∈ F.domain) ∧
  ∀ r ∈ J.carrier,
    HasDerivWithinAt y (θ.velocity r • F.eval (θ.forward r) (y r)) J.carrier r

/-- Actual-domain values for the shared endpoint-aware solution predicate. -/
def IntervalSolutionValues (F : ODE E) (I : TimeInterval) : Set (I.carrier → E) :=
  {v | ∃ x : ℝ → E,
    Specs.D13Unified.Ch01.SolutionConcepts.solutionOnValue F I x ∧
    ∀ t : I.carrier, x t = v t}

/-- Actual-domain values for the pulled-back equation. -/
def TimeChangedSolutionValues (F : ODE E) {J I : TimeInterval}
    (θ : IntervalClock J I) : Set (J.carrier → E) :=
  {v | ∃ y : ℝ → E, IsTimeChangedSolutionOn F θ y ∧ ∀ r : J.carrier, y r = v r}

end D13Unified

namespace Specs.D13Unified.Ch01.CoordinateTimeChanges
open _root_.D13Unified
open Specs.D13Unified.Ch01.SolutionConcepts

universe u v

/-- Both directions, actual-domain bijectivity, and transported initial data. -/
def coordinateChangeExpected : Prop :=
  ∀ {E : Type u} {G : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : ODE E) (H : C1Change E G) (I : OpenTimeInterval),
    (∀ x : ℝ → E, classicalSolutionOnValue F I x → MapsTo x I.carrier H.source →
      classicalSolutionOnValue (F.inCoordinates H) I (H.forward ∘ x)) ∧
    (∀ z : ℝ → G, classicalSolutionOnValue (F.inCoordinates H) I z →
      classicalSolutionOnValue F I (H.inverse ∘ z) ∧
      MapsTo (H.inverse ∘ z) I.carrier H.source ∧
      EqOn (H.forward ∘ H.inverse ∘ z) z I.carrier) ∧
    BijOn (fun v : I.carrier → E => H.forward ∘ v)
      {v | v ∈ SolutionValues F I ∧ ∀ t, v t ∈ H.source}
      (SolutionValues (F.inCoordinates H) I) ∧
    (∀ (x : ℝ → E) (s : ℝ) (ξ : E),
      MapsTo x I.carrier H.source → ξ ∈ H.source →
      (classicalIVPOnValue (F.inCoordinates H) I (H.forward ∘ x) s (H.forward ξ) ↔
        classicalIVPOnValue F I x s ξ))

/-- Forward and inverse time correspondence on exactly J and I, including
initial data. Nonvanishing θ′ is included as a derived conclusion of C¹
invertibility rather than as an assumed inverse-derivative certificate. -/
def timeChangeExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ODE E) (θ : C1Change ℝ ℝ) (J I : OpenTimeInterval)
    (hJ : θ.source = J.carrier) (hI : θ.target = I.carrier),
    (∀ r ∈ J.carrier, deriv θ.forward r ≠ 0) ∧
    (∀ x : ℝ → E, classicalSolutionOnValue F I x →
      classicalSolutionOnValue (F.inTime θ) J (x ∘ θ.forward)) ∧
    (∀ y : ℝ → E, classicalSolutionOnValue (F.inTime θ) J y →
      classicalSolutionOnValue F I (y ∘ θ.inverse) ∧
      EqOn (y ∘ θ.inverse ∘ θ.forward) y J.carrier) ∧
    BijOn (fun v : I.carrier → E => fun r : J.carrier =>
      v ⟨θ.forward r, by
        rw [← hI]
        exact θ.map_source (by simpa only [hJ] using r.property)⟩)
      (SolutionValues F I) (SolutionValues (F.inTime θ) J) ∧
    (∀ (x : ℝ → E) (r : ℝ) (ξ : E), r ∈ J.carrier →
      (classicalIVPOnValue (F.inTime θ) J (x ∘ θ.forward) r ξ ↔
        classicalIVPOnValue F I x (θ.forward r) ξ))

/-- Reflection about zero has exactly the sign and time argument stated
in the source. Reflection back gives the inverse correspondence above. -/
def timeReversalExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ODE E) (I : OpenTimeInterval),
    (∀ (r : ℝ) (x : E),
      ((r, x) ∈ (F.inTime (timeReflection I)).domain ↔
        -r ∈ I.carrier ∧ (-r, x) ∈ F.domain)) ∧
    (∀ (r : ℝ) (x : E), (r, x) ∈ (F.inTime (timeReflection I)).domain →
      (F.inTime (timeReflection I)).eval r x = -F.eval (-r) x) ∧
    (∀ x : ℝ → E,
      classicalSolutionOnValue (F.inTime (timeReflection I)) I.reflected
        (fun r => x (-r)) ↔ classicalSolutionOnValue F I x) ∧
    (∀ (x : ℝ → E) (s : ℝ) (ξ : E),
      classicalIVPOnValue (F.inTime (timeReflection I)) I.reflected
        (fun r => x (-r)) (-s) ξ ↔ classicalIVPOnValue F I x s ξ)

/-- The same coordinate correspondence retains one-sided derivatives on all
interval endpoint types, including a singleton interval. -/
def intervalCoordinateChangeExpected : Prop :=
  ∀ {E : Type u} {G : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : ODE E) (H : C1Change E G) (I : TimeInterval),
    (∀ x : ℝ → E, MapsTo x I.carrier H.source →
      (solutionOnValue (F.inCoordinates H) I (H.forward ∘ x) ↔ solutionOnValue F I x)) ∧
    (∀ z : ℝ → G, solutionOnValue (F.inCoordinates H) I z →
      solutionOnValue F I (H.inverse ∘ z) ∧
      MapsTo (H.inverse ∘ z) I.carrier H.source ∧
      EqOn (H.forward ∘ H.inverse ∘ z) z I.carrier) ∧
    (∀ (x : ℝ → E) (s : ℝ) (ξ : E),
      MapsTo x I.carrier H.source → ξ ∈ H.source →
      (ivpOnValue (F.inCoordinates H) I (H.forward ∘ x) s (H.forward ξ) ↔
        ivpOnValue F I x s ξ))

/-- Restrict a clock diffeomorphism to matching intervals of any endpoint
type. The two subset and map conditions specify the restrictions' domains;
no derivative is discarded at an included endpoint. -/
def intervalTimeChangeExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ODE E) (θ : C1Change ℝ ℝ) (J I : TimeInterval),
    J.carrier ⊆ θ.source → I.carrier ⊆ θ.target →
    MapsTo θ.forward J.carrier I.carrier → MapsTo θ.inverse I.carrier J.carrier →
    (∀ x : ℝ → E,
      solutionOnValue (F.inTime θ) J (x ∘ θ.forward) ↔ solutionOnValue F I x) ∧
    (∀ y : ℝ → E, solutionOnValue (F.inTime θ) J y →
      solutionOnValue F I (y ∘ θ.inverse) ∧
      EqOn (y ∘ θ.inverse ∘ θ.forward) y J.carrier) ∧
    (∀ (x : ℝ → E) (r : ℝ) (ξ : E), r ∈ J.carrier →
      (ivpOnValue (F.inTime θ) J (x ∘ θ.forward) r ξ ↔
        ivpOnValue F I x (θ.forward r) ξ))

/-- Full intrinsic interval statement, including clocks given only up to
included endpoints. Ordinary open-interval C¹ clocks are special cases;
no hypothesis about an extension outside J or I is added. -/
def intrinsicTimeChangeExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ODE E) (J I : TimeInterval) (θ : IntervalClock J I),
    (∀ x : ℝ → E,
      IsTimeChangedSolutionOn F θ (x ∘ θ.forward) ↔ solutionOnValue F I x) ∧
    (∀ y : ℝ → E, IsTimeChangedSolutionOn F θ y →
      solutionOnValue F I (y ∘ θ.inverse) ∧
      EqOn (y ∘ θ.inverse ∘ θ.forward) y J.carrier) ∧
    BijOn (fun v : I.carrier → E => fun r : J.carrier =>
      v ⟨θ.forward r, θ.map_source r.property⟩)
      (IntervalSolutionValues F I) (TimeChangedSolutionValues F θ) ∧
    (∀ (x : ℝ → E) (r : ℝ) (ξ : E), r ∈ J.carrier →
      ((IsTimeChangedSolutionOn F θ (x ∘ θ.forward) ∧ x (θ.forward r) = ξ) ↔
        ivpOnValue F I x (θ.forward r) ξ))

/-- The intrinsic interval formulation is precisely the shared ODE
predicate whenever the clock is given on open neighborhoods. -/
def intervalTimeCompatibilityExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ODE E) (θ : C1Change ℝ ℝ) (J I : TimeInterval)
    (hJ : J.carrier ⊆ θ.source) (hI : I.carrier ⊆ θ.target)
    (hf : MapsTo θ.forward J.carrier I.carrier)
    (hi : MapsTo θ.inverse I.carrier J.carrier) (y : ℝ → E),
    IsTimeChangedSolutionOn F (IntervalClock.restrictChange θ J I hJ hI hf hi) y ↔
      solutionOnValue (F.inTime θ) J y

end Specs.D13Unified.Ch01.CoordinateTimeChanges
