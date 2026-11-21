import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.LieBracket
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Bundle
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.FiniteRegularity
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Analysis.Matrix.Normed

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch06.VectorFieldDerivations
/-! Lie brackets of intrinsic smooth sections, including finite regularity,
left-invariant fields, and the open matrix group. The final declarations apply
the proved vector-field/derivation correspondence to the intermediate helpers. -/
namespace SmoothManifolds.LieBrackets
open ModelData AtlasData MapData PartitionData TangentData DifferentialData
  TangentBundleData VectorFieldData FiniteRegularityData LieBracketData Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
universe u

variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {B : TangentBundleStructure S}

@[ext] theorem field_ext {X Y : SmoothField B} (h : X.val = Y.val) : X = Y := by
  cases X
  cases Y
  cases h
  rfl

/-- Global functions separate the intrinsic germ derivations, by cutoff
extension of every smooth germ. -/
theorem tangent_ext_global (p : M) {v w : TangentSpace S p}
    (h : ∀ f : GlobalSmooth S,
      v.val (globalToGerm S p f) = w.val (globalToGerm S p f)) : v = w := by
  apply Subtype.ext
  apply LinearMap.ext
  intro g
  obtain ⟨f, rfl⟩ := globalToGerm_surjective S p g
  exact h f

theorem represents_eval {X : SmoothField B} {D : RealDerivation S}
    (h : Represents X D) (p : M) (f : GlobalSmooth S) :
    (X.val p).val (globalToGerm S p f) = (D f).val p :=
  (h p f (globalToGerm S p f) rfl).symm

theorem represents_unique {X : SmoothField B} {D E : RealDerivation S}
    (hD : Represents X D) (hE : Represents X E) : D = E := by
  apply Derivation.ext
  intro f
  apply Subtype.ext
  funext p
  exact (represents_eval hD p f).symm.trans (represents_eval hE p f)

theorem field_unique {X Y : SmoothField B} {D : RealDerivation S}
    (hX : Represents X D) (hY : Represents Y D) : X = Y := by
  apply field_ext
  funext p
  apply tangent_ext_global p
  intro f
  rw [represents_eval hX, represents_eval hY]

theorem field_has_representative
    (hc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.correspondenceType.{u})
    (X : SmoothField B) : ∃ D : RealDerivation S, Represents X D := by
  obtain ⟨e, he⟩ := hc S B
  exact ⟨e X, he X⟩

theorem represents_add {X Y W : SmoothField B} {D E : RealDerivation S}
    (hX : Represents X D) (hY : Represents Y E)
    (hW : ∀ p, W.val p = X.val p + Y.val p) : Represents W (D + E) := by
  intro p f g hg
  change (D f).val p + (E f).val p = (W.val p).val g
  rw [hW p]
  exact congrArg₂ (· + ·) (hX p f g hg) (hY p f g hg)

theorem represents_smul {X W : SmoothField B} {D : RealDerivation S}
    (hX : Represents X D) (r : ℝ)
    (hW : ∀ p, W.val p = r • X.val p) : Represents W (r • D) := by
  intro p f g hg
  change r * (D f).val p = (W.val p).val g
  rw [hW p]
  change r * (D f).val p = r * (X.val p).val g
  rw [hX p f g hg]

theorem represents_mul {X W : SmoothField B} {D : RealDerivation S}
    (hX : Represents X D) (h : GlobalSmooth S)
    (hW : ∀ p, W.val p = h.val p • X.val p) : Represents W (h • D) := by
  intro p f g hg
  change h.val p * (D f).val p = (W.val p).val g
  rw [hW p]
  change h.val p * (D f).val p = h.val p * (X.val p).val g
  rw [hX p f g hg]

theorem smooth_field_add (X Y : SmoothField B) :
    ∃ W : SmoothField B, ∀ p, W.val p = X.val p + Y.val p := by
  refine ⟨⟨fun p => X.val p + Y.val p, ?_⟩, fun _ => rfl⟩
  exact (TangentBundle.operations_smooth S B S id X.val Y.val (fun _ => 0)).1
    X.smooth Y.smooth

theorem smooth_field_mul (h : GlobalSmooth S) (X : SmoothField B) :
    ∃ W : SmoothField B, ∀ p, W.val p = h.val p • X.val p := by
  refine ⟨⟨fun p => h.val p • X.val p, ?_⟩, fun _ => rfl⟩
  exact (TangentBundle.operations_smooth S B S id X.val X.val h.val).2
    X.smooth ((mem_globalSmoothAlgebra_iff S h.val).mp h.property)

/-- This local helper uses exactly the correspondence interface needed for
construction. The exported conditional target below retains every premise. -/
theorem bracket_exists_of_correspondence
    (hc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.correspondenceType.{u}) :
    Specs.SmoothManifolds.Ch06.LieBracket.bracket_existsType.{u} := by
  intro n a M _ S B
  classical
  obtain ⟨e, he⟩ := hc S B
  let b : SmoothField B → SmoothField B → SmoothField B :=
    fun X Y => e.symm ⁅e X, e Y⁆
  have hb : BracketOperation b := by
    intro X Y D E hX hY
    have hD : e X = D := represents_unique (he X) hX
    have hE : e Y = E := represents_unique (he Y) hY
    simpa only [b, Equiv.apply_symm_apply, hD, hE] using he (b X Y)
  refine ⟨b, hb, ?_⟩
  intro c hc
  funext X Y
  exact field_unique (hc X Y (e X) (e Y) (he X) (he Y))
    (hb X Y (e X) (e Y) (he X) (he Y))

theorem bracket_exists_conditional
    (_hcoeff : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.chart_coefficientsType.{u})
    (hc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.correspondenceType.{u})
    (_hact : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_actionType.{u})
    (_hlpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_pushforwardType.{u})
    (_hloc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.localityType.{u})
    (_hpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.pushforwardType.{u})
    (_hrel : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.related_iffType.{u}) :
    Specs.SmoothManifolds.Ch06.LieBracket.bracket_existsType.{u} :=
  bracket_exists_of_correspondence hc

/-- Evaluation of section identities reduces to identities of derivations.
In particular this does not transport a bracket to a different tangent model. -/
theorem bracket_algebra_of_correspondence
    (hc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.correspondenceType.{u}) :
    Specs.SmoothManifolds.Ch06.LieBracket.bracket_algebraType.{u} := by
  intro n a M _ S B
  refine ⟨smooth_field_add, smooth_field_mul, ?_⟩
  intro b hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y p
    obtain ⟨D, hD⟩ := field_has_representative hc X
    obtain ⟨E, hE⟩ := field_has_representative hc Y
    apply tangent_ext_global p
    intro f
    change ((b X Y).val p).val (globalToGerm S p f) =
      -((b Y X).val p).val (globalToGerm S p f)
    rw [represents_eval (hb X Y D E hD hE), represents_eval (hb Y X E D hE hD)]
    simp only [Derivation.commutator_apply]
    change (D (E f)).val p - (E (D f)).val p =
      -((E (D f)).val p - (D (E f)).val p)
    ring
  · intro X Y Z p
    obtain ⟨D, hD⟩ := field_has_representative hc X
    obtain ⟨E, hE⟩ := field_has_representative hc Y
    obtain ⟨F, hF⟩ := field_has_representative hc Z
    apply tangent_ext_global p
    intro f
    change ((b X (b Y Z)).val p).val (globalToGerm S p f) +
      ((b Y (b Z X)).val p).val (globalToGerm S p f) +
      ((b Z (b X Y)).val p).val (globalToGerm S p f) = 0
    rw [represents_eval (hb X (b Y Z) D ⁅E, F⁆ hD (hb Y Z E F hE hF)),
      represents_eval (hb Y (b Z X) E ⁅F, D⁆ hE (hb Z X F D hF hD)),
      represents_eval (hb Z (b X Y) F ⁅D, E⁆ hF (hb X Y D E hD hE))]
    have hj := congrArg (fun H : RealDerivation S => (H f).val p) (lie_jacobi D E F)
    exact hj
  · intro X Y Z W hW p
    obtain ⟨D, hD⟩ := field_has_representative hc X
    obtain ⟨E, hE⟩ := field_has_representative hc Y
    obtain ⟨F, hF⟩ := field_has_representative hc Z
    apply tangent_ext_global p
    intro f
    change ((b W Z).val p).val (globalToGerm S p f) =
      ((b X Z).val p).val (globalToGerm S p f) +
        ((b Y Z).val p).val (globalToGerm S p f)
    rw [represents_eval (hb W Z (D + E) F (represents_add hD hE hW) hF),
      represents_eval (hb X Z D F hD hF), represents_eval (hb Y Z E F hE hF), (add_lie D E F)]
    rfl
  · intro X Y Z W hW p
    obtain ⟨D, hD⟩ := field_has_representative hc X
    obtain ⟨E, hE⟩ := field_has_representative hc Y
    obtain ⟨F, hF⟩ := field_has_representative hc Z
    apply tangent_ext_global p
    intro f
    change ((b X W).val p).val (globalToGerm S p f) =
      ((b X Y).val p).val (globalToGerm S p f) +
        ((b X Z).val p).val (globalToGerm S p f)
    rw [represents_eval (hb X W D (E + F) hD (represents_add hE hF hW)),
      represents_eval (hb X Y D E hD hE), represents_eval (hb X Z D F hD hF), (lie_add D E F)]
    rfl
  · intro r X Y W hW p
    obtain ⟨D, hD⟩ := field_has_representative hc X
    obtain ⟨E, hE⟩ := field_has_representative hc Y
    apply tangent_ext_global p
    intro f
    change ((b W Y).val p).val (globalToGerm S p f) =
      r * ((b X Y).val p).val (globalToGerm S p f)
    rw [represents_eval (hb W Y (r • D) E (represents_smul hD r hW) hE),
      represents_eval (hb X Y D E hD hE), (smul_lie r D E)]
    rfl
  · intro r X Y W hW p
    obtain ⟨D, hD⟩ := field_has_representative hc X
    obtain ⟨E, hE⟩ := field_has_representative hc Y
    apply tangent_ext_global p
    intro f
    change ((b X W).val p).val (globalToGerm S p f) =
      r * ((b X Y).val p).val (globalToGerm S p f)
    rw [represents_eval (hb X W D (r • E) hD (represents_smul hE r hW)),
      represents_eval (hb X Y D E hD hE), (lie_smul r D E)]
    rfl
  · intro h X Y W D hD hW p
    obtain ⟨E, hE⟩ := field_has_representative hc Y
    apply tangent_ext_global p
    intro f
    change ((b X W).val p).val (globalToGerm S p f) =
      h.val p * ((b X Y).val p).val (globalToGerm S p f) +
        (D h).val p * (Y.val p).val (globalToGerm S p f)
    rw [represents_eval (hb X W D (h • E) hD (represents_mul hE h hW)),
      represents_eval (hb X Y D E hD hE), represents_eval hE]
    simp only [Derivation.commutator_apply, Derivation.smul_apply, smul_eq_mul,
      Derivation.leibniz]
    change (h.val p * (D (E f)).val p + (E f).val p * (D h).val p) -
      h.val p * (E (D f)).val p =
      h.val p * ((D (E f)).val p - (E (D f)).val p) + (D h).val p * (E f).val p
    ring

theorem bracket_algebra_conditional
    (_hcoeff : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.chart_coefficientsType.{u})
    (hc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.correspondenceType.{u})
    (_hact : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_actionType.{u})
    (_hlpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_pushforwardType.{u})
    (_hloc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.localityType.{u})
    (_hpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.pushforwardType.{u})
    (_hrel : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.related_iffType.{u}) :
    Specs.SmoothManifolds.Ch06.LieBracket.bracket_algebraType.{u} :=
  bracket_algebra_of_correspondence hc

/-- Compatibility with a pullback of functions is closed under commutators.
Existence of composites is retained throughout, as in FunctionsRelated. -/
theorem functionsRelated_commutator
    {m : ℕ} {c : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m c N} {f : M → N}
    {D E : RealDerivation S} {D' E' : RealDerivation T}
    (hD : FunctionsRelated f D D') (hE : FunctionsRelated f E E') :
    FunctionsRelated f ⁅D, E⁆ ⁅D', E'⁆ := by
  intro g
  obtain ⟨v, hv, hDv⟩ := hD g
  obtain ⟨w, hw, hEw⟩ := hE g
  have hwv : w = v := Subtype.ext (hw.trans hv.symm)
  subst w
  obtain ⟨vE, hvE, hDvE⟩ := hD (E' g)
  obtain ⟨vD, hvD, hEvD⟩ := hE (D' g)
  have hEv : E v = vE := Subtype.ext (hEw.trans hvE.symm)
  have hDv' : D v = vD := Subtype.ext (hDv.trans hvD.symm)
  refine ⟨v, hv, ?_⟩
  funext p
  change (D (E v)).val p - (E (D v)).val p =
    (D' (E' g)).val (f p) - (E' (D' g)).val (f p)
  rw [hEv, hDv']
  exact congrArg₂ (· - ·) (congrFun hDvE p) (congrFun hEvD p)

theorem bracket_related_conditional
    (_hcoeff : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.chart_coefficientsType.{u})
    (hc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.correspondenceType.{u})
    (_hact : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_actionType.{u})
    (_hlpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_pushforwardType.{u})
    (_hloc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.localityType.{u})
    (_hpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.pushforwardType.{u})
    (hr : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.related_iffType.{u}) :
    Specs.SmoothManifolds.Ch06.LieBracket.bracket_relatedType.{u} := by
  intro n m a c M N _ _ S T B C b d hb hd f hf L hL X Y X' Y' hX hY
  obtain ⟨D, hD⟩ := field_has_representative hc X
  obtain ⟨E, hE⟩ := field_has_representative hc Y
  obtain ⟨D', hD'⟩ := field_has_representative hc X'
  obtain ⟨E', hE'⟩ := field_has_representative hc Y'
  have hDr := (hr S T B C f hf L hL X X' D D' hD hD').mp hX
  have hEr := (hr S T B C f hf L hL Y Y' E E' hE hE').mp hY
  exact (hr S T B C f hf L hL (b X Y) (d X' Y') ⁅D, E⁆ ⁅D', E'⁆
    (hb X Y D E hD hE) (hd X' Y' D' E' hD' hE')).mpr
      (functionsRelated_commutator hDr hEr)

@[simp] theorem coefficients_eq (X : Section S) (e : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) :
    coefficients B X e he p = B.fiberCoordinates.equiv e he p hp (X p) := by
  classical
  exact dite_eq_left hp

theorem coordinates_eval (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (v : TangentSpace S p) (i : Fin n) :
    B.fiberCoordinates.equiv e he p hp v i = v.val (coordinateGerm S p e he hp i) := by
  obtain ⟨g, hg, hval⟩ := B.fiberCoordinates.isCoordinates e he p hp
  rw [hval]
  congr 1
  exact Subtype.ext (hg i)

theorem represents_coordinate_value {X : SmoothField B} {D : RealDerivation S}
    (hX : Represents X D) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (f : GlobalSmooth S) (i : Fin n)
    (hf : f.val =ᶠ[𝓝 p] (fun y => (e y).val i)) :
    coefficients B X.val e he p i = (D f).val p := by
  rw [coefficients_eq X.val e he p hp, coordinates_eval]
  exact (hX p f (coordinateGerm S p e he hp i) (Germ.coe_eq.mpr hf)).symm

theorem smooth_field_regular (X : SmoothField B) : FieldRegular B ⊤ X.val := by
  intro e he p hp
  have h := (TangentBundle.chartFiber_smoothAt S B S (fun y => ⟨y, X.val y⟩)
    p e he hp (X.smooth p)).2 e he hp
  apply SmoothManifolds.LocalCoordinateExtension.congr h
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  rw [TangentBundle.chartFiber_eq S B e he ⟨q, X.val q⟩ hq,
    coefficients_eq X.val e he q hq]

theorem coordinate_derivative_exists (X : SmoothField B) (e : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) :
    ∃ L, HasCoordinateDerivative e (coefficients B X.val e he) p L := by
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := smooth_field_regular X e he p hp
  exact ⟨fderiv ℝ F (e p).val, F,
    ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt, heF⟩

theorem action_coordinate_formula {X : SmoothField B} {D : RealDerivation S}
    (hX : Represents X D) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (f : GlobalSmooth S)
    (F : Euclidean n → ℝ) (hF : GermChartExtension S p e (globalToGerm S p f) F) :
    (D f).val p = ∑ i, coefficients B X.val e he p i *
      fderiv ℝ F (e p).val (Pi.single i 1) := by
  rw [← represents_eval hX p f,
    derivation_coordinate_formula S p e he hp (X.val p) (globalToGerm S p f) F hF]
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficients_eq X.val e he p hp, coordinates_eval]

theorem bracket_coordinates_conditional
    (hcoeff : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.chart_coefficientsType.{u})
    (hc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.correspondenceType.{u})
    (_hact : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_actionType.{u})
    (_hlpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_pushforwardType.{u})
    (_hloc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.localityType.{u})
    (_hpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.pushforwardType.{u})
    (_hr : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.related_iffType.{u}) :
    Specs.SmoothManifolds.Ch06.LieBracket.bracket_coordinatesType.{u} := by
  intro n a M _ S B b hb X Y
  constructor
  · intro e he p hp
    obtain ⟨L, hL⟩ := coordinate_derivative_exists X e he p hp
    obtain ⟨K, hK⟩ := coordinate_derivative_exists Y e he p hp
    exact ⟨L, K, hL, hK⟩
  · intro e he p hp L K hL hK j
    obtain ⟨D, hD⟩ := field_has_representative hc X
    obtain ⟨E, hE⟩ := field_has_representative hc Y
    have hZ := hb X Y D E hD hE
    obtain ⟨U, hU, hpU, hUs, g, hg, hZg⟩ := hcoeff S B (b X Y) ⁅D, E⁆ hZ e he p hp
    obtain ⟨V, hV, hpV, F, hF, heF⟩ := smooth_field_regular X e he p hp
    obtain ⟨W, hW, hpW, G, hG, heG⟩ := smooth_field_regular Y e he p hp
    have hFd : DifferentiableAt ℝ F (e p).val :=
      (hF.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)
    have hGd : DifferentiableAt ℝ G (e p).val :=
      (hG.contDiffAt (hW.mem_nhds hpW)).differentiableAt (by simp)
    have hLf : L = fderiv ℝ F (e p).val :=
      FiniteRegularity.extension_independence e _ p hp L _ hL ⟨F, hFd.hasFDerivAt, heF⟩
    have hKg : K = fderiv ℝ G (e p).val :=
      FiniteRegularity.extension_independence e _ p hp K _ hK ⟨G, hGd.hasFDerivAt, heG⟩
    have hDg : (D (g j)).val =ᶠ[𝓝 p] (fun q => coefficients B X.val e he q j) := by
      filter_upwards [hU.mem_nhds hpU] with q hq
      symm
      apply represents_coordinate_value hD e he q (hUs hq) (g j) j
      filter_upwards [hU.mem_nhds hq] with y hy
      exact hg j hy
    have hEg : (E (g j)).val =ᶠ[𝓝 p] (fun q => coefficients B Y.val e he q j) := by
      filter_upwards [hU.mem_nhds hpU] with q hq
      symm
      apply represents_coordinate_value hE e he q (hUs hq) (g j) j
      filter_upwards [hU.mem_nhds hq] with y hy
      exact hg j hy
    have hFj : GermChartExtension S p e (globalToGerm S p (D (g j))) (fun z => F z j) := by
      refine ⟨⟨V, hV, hpV, (contDiffOn_pi.mp hF) j⟩, ?_⟩
      exact Germ.coe_eq.mpr ((heF.fun_comp (fun z => z j)).trans hDg.symm)
    have hGj : GermChartExtension S p e (globalToGerm S p (E (g j))) (fun z => G z j) := by
      refine ⟨⟨W, hW, hpW, (contDiffOn_pi.mp hG) j⟩, ?_⟩
      exact Germ.coe_eq.mpr ((heG.fun_comp (fun z => z j)).trans hEg.symm)
    rw [coefficients_eq (b X Y).val e he p hp, hZg p hpU j]
    change (D (E (g j))).val p - (E (D (g j))).val p = _
    rw [action_coordinate_formula hD e he p hp (E (g j)) (fun z => G z j) hGj,
      action_coordinate_formula hE e he p hp (D (g j)) (fun z => F z j) hFj,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hLf, hKg, fderiv_apply hFd j, fderiv_apply hGd j]
    rfl

theorem constant_smooth {m : ℕ} {c : ModelKind} {N : Type u} [TopologicalSpace N]
    (R : SmoothManifold m c N) (q : M) : IsSmoothMap R S (fun _ => q) := by
  intro p
  refine ⟨continuousAt_const, ?_⟩
  intro e he d hd hp hq
  exact ⟨univ, isOpen_univ, mem_univ _, fun _ => (d q).val,
    contDiffOn_const, Eventually.of_forall (fun _ => rfl)⟩

theorem left_translation_smooth {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    {S : SmoothManifold n .euclidean G} (A : LieGroupStructure S) (g : G) :
    IsSmoothMap S S (fun p => g * p) := by
  have hpair := (differential_pair S S S A.productCoordinates A.productManifold
    A.productAtlas (fun _ => g) id (constant_smooth S g)
    (manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val S.smoothStructure.property.1)).1
  exact manifoldContDiff_comp (⊤ : ℕ∞) S.smoothStructure.val
    A.productManifold.smoothStructure.val S.smoothStructure.val
    A.productManifold.smoothStructure.property.1.1 (fun p => (g, p))
    (fun z => z.1 * z.2) hpair A.multiplication_smooth

/-- Evaluation at the identity is injective on left-invariant fields. This
uses only smoothness of multiplication, not the still separate existence of
an invariant field with prescribed identity value. -/
theorem leftInvariant_eval_injective {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    {S : SmoothManifold n .euclidean G} {B : TangentBundleStructure S}
    (A : LieGroupStructure S) :
    Function.Injective (fun X : LeftInvariantField B => X.val.val 1) := by
  intro X Y h
  apply Subtype.ext
  apply field_ext
  funext g
  obtain ⟨L, hL, _⟩ := differential_exists S S (fun p => g * p)
    (left_translation_smooth A g) 1
  have hX := X.property g 1 L hL
  have hY := Y.property g 1 L hL
  have hh := hX.symm.trans ((congrArg L h).trans hY)
  exact Eq.mp (congrArg (fun q => X.val.val q = Y.val.val q) (mul_one g)) hh

theorem leftInvariant_bracket_conditional
    (hcoeff : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.chart_coefficientsType.{u})
    (hc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.correspondenceType.{u})
    (hact : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_actionType.{u})
    (hlpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_pushforwardType.{u})
    (hloc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.localityType.{u})
    (hpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.pushforwardType.{u})
    (hr : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.related_iffType.{u}) :
    Specs.SmoothManifolds.Ch06.LieBracket.leftInvariant_bracketType.{u} := by
  intro n G _ _ S B A b hb
  have hclosed (X Y : LeftInvariantField B) : IsLeftInvariant (b X.val Y.val) := by
    intro g p L hL
    have hf := left_translation_smooth A g
    classical
    let K (q : G) : TangentSpace S q →ₗ[ℝ] TangentSpace S (g * q) :=
      if h : q = p then h.symm ▸ L else
        Classical.choose (differential_exists S S (fun q => g * q) hf q)
    have hK (q : G) : IsDifferential S S (fun q => g * q) q (K q) := by
      by_cases h : q = p
      · subst q
        simpa only [K, dite_eq_left rfl] using hL
      · simpa only [K, dite_eq_right h] using
          (Classical.choose_spec (differential_exists S S (fun q => g * q) hf q)).1
    have h := bracket_related_conditional hcoeff hc hact hlpush hloc hpush hr
      S S B B b b hb hb (fun q => g * q) hf K hK X.val Y.val X.val Y.val
      (fun q => X.property g q (K q) (hK q))
      (fun q => Y.property g q (K q) (hK q)) p
    simpa only [K, dite_eq_left rfl] using h
  refine ⟨hclosed, ?_⟩
  intro e he
  let β (v w : TangentSpace S (1 : G)) := (b (e v).val (e w).val).val 1
  refine ⟨β, ?_⟩
  intro v w
  refine ⟨rfl, ?_⟩
  let Z : LeftInvariantField B := ⟨b (e v).val (e w).val, hclosed (e v) (e w)⟩
  have h : e.symm Z = β v w := he.1 Z
  have hz : e (β v w) = Z := by rw [← h, Equiv.apply_symm_apply]
  exact congrArg Subtype.val hz

/-- The loss of one derivative in an ambient chart. Open-domain hypotheses
are essential here; boundary fields are handled by their ambient extensions. -/
theorem ambient_bracket_regular {n : ℕ} (r : ℕ) (hr : 1 ≤ r)
    (U : Set (Euclidean n)) (F G : Euclidean n → Euclidean n)
    (hU : IsOpen U) (hF : ContDiffOn ℝ r F U) (hG : ContDiffOn ℝ r G U) :
    ContDiffOn ℝ (r - 1 : ℕ) (VectorField.lieBracket ℝ F G) U := by
  have horder : ((r - 1 : ℕ) : ℕ∞ω) + 1 ≤ (r : ℕ∞ω) := by
    exact_mod_cast (Nat.sub_add_cancel hr).le
  have hle : ((r - 1 : ℕ) : ℕ∞ω) ≤ (r : ℕ∞ω) := by
    exact_mod_cast Nat.sub_le r 1
  exact ((hG.fderiv_of_isOpen hU horder).clm_apply (hF.of_le hle)).sub
    ((hF.fderiv_of_isOpen hU horder).clm_apply (hG.of_le hle))

/-- Expanding a linear map on the coordinate basis identifies the derivative
formula with precisely the sum printed in M06.02. -/
theorem coordinate_commutator_sum {n : ℕ}
    (L K : Euclidean n →L[ℝ] Euclidean n) (x y : Euclidean n) (j : Fin n) :
    (K x - L y) j = ∑ i, (x i * K (Pi.single i 1) j - y i * L (Pi.single i 1) j) := by
  classical
  have hexp (z : Euclidean n) : z = ∑ i, z i • Pi.single i 1 := by
    funext k
    simp [Pi.single_apply]
  conv_lhs => rw [hexp x, hexp y]
  simp only [map_sum, map_smul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_sub_distrib]

/-- Local C^(r-1) coefficient functions from C^r sections. This is the local
analytic stage of finite-regularity gluing, including the actual derivative
formula at every point in a neighborhood of a boundary point. -/
theorem finite_bracket_local (r : ℕ) (hr : 1 ≤ r) (X Y : Section S)
    (hX : FieldRegular B r X) (hY : FieldRegular B r Y)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) :
    ∃ (U : Set (Euclidean n)) (F G H : Euclidean n → Euclidean n),
      IsOpen U ∧ (e p).val ∈ U ∧ ContDiffOn ℝ r F U ∧ ContDiffOn ℝ r G U ∧
      ContDiffOn ℝ (r - 1 : ℕ) H U ∧
      (fun q => F (e q).val) =ᶠ[𝓝 p] coefficients B X e he ∧
      (fun q => G (e q).val) =ᶠ[𝓝 p] coefficients B Y e he ∧
      ∀ᶠ q in 𝓝 p, ∀ L K : Euclidean n →L[ℝ] Euclidean n,
        HasCoordinateDerivative e (coefficients B X e he) q L →
        HasCoordinateDerivative e (coefficients B Y e he) q K →
        ∀ j, H (e q).val j = ∑ i,
          (coefficients B X e he q i * K (Pi.single i 1) j -
            coefficients B Y e he q i * L (Pi.single i 1) j) := by
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := hX e he p hp
  obtain ⟨V, hV, hpV, G, hG, heG⟩ := hY e he p hp
  have hFu := hF.mono (inter_subset_left : U ∩ V ⊆ U)
  have hGu := hG.mono (inter_subset_right : U ∩ V ⊆ V)
  refine ⟨U ∩ V, F, G, VectorField.lieBracket ℝ F G, hU.inter hV, ⟨hpU, hpV⟩,
    hFu, hGu, ambient_bracket_regular r hr (U ∩ V) F G (hU.inter hV) hFu hGu,
    heF, heG, ?_⟩
  have hc : ContinuousAt (fun q => (e q).val) p :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt hp)
  filter_upwards [e.open_source.mem_nhds hp,
    hc.preimage_mem_nhds ((hU.inter hV).mem_nhds ⟨hpU, hpV⟩),
    eventually_eventually_nhds.mpr heF, eventually_eventually_nhds.mpr heG] with q hq hqU hqF hqG
  intro L K hL hK j
  have hne : (r : ℕ∞ω) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hr))
  have hFd := (hFu.contDiffAt ((hU.inter hV).mem_nhds hqU)).differentiableAt hne
  have hGd := (hGu.contDiffAt ((hU.inter hV).mem_nhds hqU)).differentiableAt hne
  have hLf : L = fderiv ℝ F (e q).val :=
    FiniteRegularity.extension_independence e _ q hq L _ hL ⟨F, hFd.hasFDerivAt, hqF⟩
  have hKg : K = fderiv ℝ G (e q).val :=
    FiniteRegularity.extension_independence e _ q hq K _ hK ⟨G, hGd.hasFDerivAt, hqG⟩
  have hFq : F (e q).val = coefficients B X e he q :=
    (show (fun x => F (e x).val) =ᶠ[𝓝 q] coefficients B X e he from hqF).eq_of_nhds
  have hGq : G (e q).val = coefficients B Y e he q :=
    (show (fun x => G (e x).val) =ᶠ[𝓝 q] coefficients B Y e he from hqG).eq_of_nhds
  rw [hLf, hKg, ← hFq, ← hGq]
  exact coordinate_commutator_sum _ _ _ _ j

/-- The total coordinate expression for a commutator. Its use below is
restricted to charts containing the base point, where derivatives exist. -/
noncomputable def coordinateBracket (B : TangentBundleStructure S)
    (X Y : Section S) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) : Euclidean n :=
  coordinateDerivative e (coefficients B Y e he) p (coefficients B X e he p) -
    coordinateDerivative e (coefficients B X e he) p (coefficients B Y e he p)

/-- Positive finite regularity supplies an actual ambient derivative. -/
theorem regular_coordinate_derivative_exists (r : ℕ) (hr : 1 ≤ r)
    (X : Section S) (hX : FieldRegular B r X)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) :
    HasCoordinateDerivative e (coefficients B X e he) p
      (coordinateDerivative e (coefficients B X e he) p) := by
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := hX e he p hp
  have hne : (r : ℕ∞ω) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hr))
  have hFd := (hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt hne
  have h := FiniteRegularity.coordinateDerivative_eq e _ p hp
    (fderiv ℝ F (e p).val) ⟨F, hFd.hasFDerivAt, heF⟩
  rw [h]
  exact ⟨F, hFd.hasFDerivAt, heF⟩

/-- Any valid coordinate derivatives give the same commutator expression. -/
theorem coordinateBracket_eq (X Y : Section S)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (L K : Euclidean n →L[ℝ] Euclidean n)
    (hL : HasCoordinateDerivative e (coefficients B X e he) p L)
    (hK : HasCoordinateDerivative e (coefficients B Y e he) p K) :
    coordinateBracket B X Y e he p =
      K (coefficients B X e he p) - L (coefficients B Y e he p) := by
  unfold coordinateBracket
  rw [FiniteRegularity.coordinateDerivative_eq e _ p hp L hL,
    FiniteRegularity.coordinateDerivative_eq e _ p hp K hK]

/-- Uniqueness of the finite-regularity section follows from one chart at
 each point. Derivative existence is essential to avoid a vacuous condition. -/
theorem finite_bracket_unique (r : ℕ) (hr : 1 ≤ r) (X Y Z W : Section S)
    (hX : FieldRegular B r X) (hY : FieldRegular B r Y)
    (hZ : HasBracketCoefficients B X Y Z) (hW : HasBracketCoefficients B X Y W) : Z = W := by
  funext p
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  apply (B.fiberCoordinates.equiv e he p hp).injective
  have hL := regular_coordinate_derivative_exists r hr X hX e he p hp
  have hK := regular_coordinate_derivative_exists r hr Y hY e he p hp
  rw [← coefficients_eq Z e he p hp, ← coefficients_eq W e he p hp]
  funext j
  exact (hZ e he p hp _ _ hL hK j).trans (hW e he p hp _ _ hL hK j).symm

/-- Ambient coordinate transformations respect the commutator of one-jets. -/
theorem bracket_change_of_derivatives (X Y : Section S)
    (e d : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) (hpd : p ∈ d.source)
    (L K Ld Kd : Euclidean n →L[ℝ] Euclidean n)
    (hL : HasCoordinateDerivative e (coefficients B X e he) p L)
    (hK : HasCoordinateDerivative e (coefficients B Y e he) p K)
    (hLd : HasCoordinateDerivative d (coefficients B X d hd) p Ld)
    (hKd : HasCoordinateDerivative d (coefficients B Y d hd) p Kd) :
    B.fiberCoordinates.equiv d hd p hpd
        ((B.fiberCoordinates.equiv e he p hp).symm
          (K (coefficients B X e he p) - L (coefficients B Y e he p))) =
      Kd (coefficients B X d hd p) - Ld (coefficients B Y d hd p) := by
  have hc := S.smoothStructure.property.1.2 e he d hd
  have hpt : e p ∈ (e.symm.trans d).source := by
    simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
    exact ⟨e.map_source hp, by simpa only [e.left_inv hp] using hpd⟩
  obtain ⟨U, hU, hpU, T, hT, heq⟩ := hc.1 (e p) hpt
  have hrep (q : M) (hq : q ∈ e.source) (hqd : q ∈ d.source) (hqU : (e q).val ∈ U) :
      (fun y => T (e y).val) =ᶠ[𝓝 q] (fun y => (d y).val) := by
    filter_upwards [e.open_source.mem_nhds hq, d.open_source.mem_nhds hqd,
      (continuous_subtype_val.continuousAt.comp (e.continuousAt hq)).preimage_mem_nhds
        (hU.mem_nhds hqU)] with y hye hyd hyU
    have hyt : e y ∈ (e.symm.trans d).source := by
      simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
      exact ⟨e.map_source hye, by simpa only [e.left_inv hye] using hyd⟩
    simpa only [OpenPartialHomeomorph.trans_apply, e.left_inv hye] using heq (e y) hyt hyU
  have hbase : T (e p).val = (d p).val := (hrep p hp hpd hpU).eq_of_nhds
  have hTpt := hT.contDiffAt (hU.mem_nhds hpU)
  have hTdiff := hTpt.differentiableAt (by simp)
  have hDT : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ T) U :=
    hT.fderiv_of_isOpen hU (by simp)
  have hDTdiff : DifferentiableAt ℝ (fderiv ℝ T) (e p).val :=
    (hDT.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have hjac (V : Section S) (q : M) (hq : q ∈ e.source) (hqd : q ∈ d.source)
      (hqU : (e q).val ∈ U) :
      fderiv ℝ T (e q).val (coefficients B V e he q) = coefficients B V d hd q := by
    rw [coefficients_eq V e he q hq, coefficients_eq V d hd q hqd]
    exact (TangentBundle.transition_jacobian S B.fiberCoordinates e d he hd q hq hqd
      U T hU hqU hT (hrep q hq hqd hqU) (V q)).symm
  have hnear : ∀ᶠ q in 𝓝 p, q ∈ e.source ∧ q ∈ d.source ∧ (e q).val ∈ U := by
    filter_upwards [e.open_source.mem_nhds hp, d.open_source.mem_nhds hpd,
      (continuous_subtype_val.continuousAt.comp (e.continuousAt hp)).preimage_mem_nhds
        (hU.mem_nhds hpU)] with q hqe hqd hqu
    exact ⟨hqe, hqd, hqu⟩
  obtain ⟨F, hF, heF⟩ := hL
  obtain ⟨G, hG, heG⟩ := hK
  have hpointF : F (e p).val = coefficients B X e he p := heF.eq_of_nhds
  have hpointG : G (e p).val = coefficients B Y e he p := heG.eq_of_nhds
  have htransform (V : Section S) (H : Euclidean n → Euclidean n)
      (hH : DifferentiableAt ℝ H (e p).val)
      (heH : (fun q => H (e q).val) =ᶠ[𝓝 p] coefficients B V e he)
      (J : Euclidean n →L[ℝ] Euclidean n)
      (hJ : HasCoordinateDerivative d (coefficients B V d hd) p J) :
      fderiv ℝ (fun z => fderiv ℝ T z (H z)) (e p).val =
        J.comp (fderiv ℝ T (e p).val) := by
    apply FiniteRegularity.extension_independence e (coefficients B V d hd) p hp
    · refine ⟨fun z => fderiv ℝ T z (H z), (hDTdiff.clm_apply hH).hasFDerivAt, ?_⟩
      filter_upwards [hnear, heH] with q hq hqH
      rw [hqH]
      exact hjac V q hq.1 hq.2.1 hq.2.2
    · obtain ⟨Q, hQ, heQ⟩ := hJ
      refine ⟨Q ∘ T, ?_, ?_⟩
      · exact (hbase ▸ hQ).comp (e p).val hTdiff.hasFDerivAt
      · exact ((hrep p hp hpd hpU).fun_comp Q).trans heQ
  have hDF := htransform X F hF.differentiableAt heF Ld hLd
  have hDG := htransform Y G hG.differentiableAt heG Kd hKd
  have hcomm := VectorField.fderiv_apply_lieBracket hTpt (by simp)
    hG.differentiableAt hF.differentiableAt
  have hjacV := TangentBundle.transition_jacobian S B.fiberCoordinates e d he hd p hp hpd
    U T hU hpU hT (hrep p hp hpd hpU)
    ((B.fiberCoordinates.equiv e he p hp).symm
      (K (coefficients B X e he p) - L (coefficients B Y e he p)))
  rw [LinearEquiv.apply_symm_apply] at hjacV
  rw [hjacV]
  simpa only [VectorField.lieBracket, hF.fderiv, hG.fderiv, hpointF, hpointG,
    hDF, hDG, ContinuousLinearMap.comp_apply, hjac X p hp hpd hpU,
    hjac Y p hp hpd hpU] using hcomm

/-- Pointwise covariance suffices to glue the local commutators. The analytic
regularity and the uniqueness assertion are proved independently here. -/
theorem finite_bracket_of_coordinate_change (r : ℕ) (hr : 1 ≤ r)
    (X Y : Section S) (hX : FieldRegular B r X) (hY : FieldRegular B r Y)
    (hchange : ∀ (e d : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
      (hd : d ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) (hpd : p ∈ d.source),
      B.fiberCoordinates.equiv d hd p hpd
        ((B.fiberCoordinates.equiv e he p hp).symm (coordinateBracket B X Y e he p)) =
          coordinateBracket B X Y d hd p) :
    ∃! Z : Section S, FieldRegular B (r - 1 : ℕ) Z ∧ HasBracketCoefficients B X Y Z := by
  classical
  have hcover := S.smoothStructure.property.1.1
  let e (p : M) := Classical.choose (hcover p)
  have he (p : M) : e p ∈ S.smoothStructure.val := (Classical.choose_spec (hcover p)).1
  have hp (p : M) : p ∈ (e p).source := (Classical.choose_spec (hcover p)).2
  let Z : Section S := fun p =>
    (B.fiberCoordinates.equiv (e p) (he p) p (hp p)).symm
      (coordinateBracket B X Y (e p) (he p) p)
  have hZ (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val)
      (p : M) (hpd : p ∈ d.source) :
      coefficients B Z d hd p = coordinateBracket B X Y d hd p := by
    rw [coefficients_eq Z d hd p hpd]
    exact hchange (e p) d (he p) hd p (hp p) hpd
  have hZcoeff : HasBracketCoefficients B X Y Z := by
    intro d hd p hpd L K hL hK j
    rw [hZ d hd p hpd, coordinateBracket_eq X Y d hd p hpd L K hL hK]
    exact coordinate_commutator_sum L K _ _ j
  refine ⟨Z, ⟨?_, hZcoeff⟩, ?_⟩
  · intro d hd p hpd
    obtain ⟨U, F, G, H, hU, hpU, hF, hG, hH, heF, heG, heH⟩ :=
      finite_bracket_local r hr X Y hX hY d hd p hpd
    refine ⟨U, hU, hpU, H, hH, ?_⟩
    filter_upwards [d.open_source.mem_nhds hpd, heH] with q hq hformula
    have hL := regular_coordinate_derivative_exists r hr X hX d hd q hq
    have hK := regular_coordinate_derivative_exists r hr Y hY d hd q hq
    funext j
    exact (hformula _ _ hL hK j).trans (hZcoeff d hd q hq _ _ hL hK j).symm
  · intro W hW
    exact finite_bracket_unique r hr X Y W Z hX hY hW.2 hZcoeff

/-- Changes of charts transform the coordinate commutator as an intrinsic
vector; the symmetric second derivative of the transition cancels. -/
theorem finite_bracket_coordinate_change (r : ℕ) (hr : 1 ≤ r)
    (X Y : Section S) (hX : FieldRegular B r X) (hY : FieldRegular B r Y)
    (e d : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : M) (hp : p ∈ e.source) (hpd : p ∈ d.source) :
    B.fiberCoordinates.equiv d hd p hpd
      ((B.fiberCoordinates.equiv e he p hp).symm (coordinateBracket B X Y e he p)) =
        coordinateBracket B X Y d hd p := by
  exact bracket_change_of_derivatives X Y e d he hd p hp hpd _ _ _ _
    (regular_coordinate_derivative_exists r hr X hX e he p hp)
    (regular_coordinate_derivative_exists r hr Y hY e he p hp)
    (regular_coordinate_derivative_exists r hr X hX d hd p hpd)
    (regular_coordinate_derivative_exists r hr Y hY d hd p hpd)

theorem bracket_finiteRegularity_conditional
    (_hcoeff : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.chart_coefficientsType.{u})
    (_hc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.correspondenceType.{u})
    (_hact : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_actionType.{u})
    (_hlpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_pushforwardType.{u})
    (_hloc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.localityType.{u})
    (_hpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.pushforwardType.{u})
    (_hr : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.related_iffType.{u}) :
    Specs.SmoothManifolds.Ch06.LieBracket.bracket_finiteRegularityType.{u} := by
  intro n a M _ S B r hr X Y hX hY
  exact finite_bracket_of_coordinate_change r hr X Y hX hY
    (finite_bracket_coordinate_change r hr X Y hX hY)

/-- Ambient calculation behind the GL_n example. Restriction to the open
invertible-matrix locus and identification with intrinsic tangent fibers are
separate geometric obligations. -/
theorem matrix_ambient_commutator (d : ℕ) (v w g : Matrix (Fin d) (Fin d) ℝ) :
    (fderiv ℝ (fun x : Matrix (Fin d) (Fin d) ℝ => x * w) g) (g * v) -
      (fderiv ℝ (fun x : Matrix (Fin d) (Fin d) ℝ => x * v) g) (g * w) =
        g * (v * w - w * v) := by
  let V := (LinearMap.mulRight ℝ v).toContinuousLinearMap
  let W := (LinearMap.mulRight ℝ w).toContinuousLinearMap
  have hVder : fderiv ℝ (fun x : Matrix (Fin d) (Fin d) ℝ => x * v) g = V := V.fderiv
  have hWder : fderiv ℝ (fun x : Matrix (Fin d) (Fin d) ℝ => x * w) g = W := W.fderiv
  rw [hVder, hWder]
  change g * v * w - g * w * v = g * (v * w - w * v)
  rw [mul_sub, mul_assoc, mul_assoc]

/-- A full base chart turns any ambient smooth coefficient function into one
actual smooth section, with uniqueness in the intrinsic fibers. -/
theorem field_of_full_chart (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val)
    (hfull : e.source = univ) (F : Euclidean n → Euclidean n) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∃! X : SmoothField B, ∀ p, coefficients B X.val e he p = F (e p).val := by
  have hp (p : M) : p ∈ e.source := hfull.symm ▸ mem_univ p
  let v (p : M) := (B.fiberCoordinates.equiv e he p (hp p)).symm (F (e p).val)
  have hs : letI := B.topology
      IsSmoothMap S B.manifold (fun p => ⟨p, v p⟩) := by
    intro p
    apply TangentBundle.lift_smoothAt_of_coeff S B S (fun p => ⟨p, v p⟩) p e he
      (hp p) (fun q => F (e q).val)
      (manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val S.smoothStructure.property.1 p)
    · exact TangentBundle.euclidean_smoothAt_of_chart S _ p e he (hp p)
        ⟨univ, isOpen_univ, mem_univ _, F, hF.contDiffOn, Eventually.of_forall (fun _ => rfl)⟩
    · exact Eventually.of_forall (fun q => ⟨hp q, by simp only [v, LinearEquiv.apply_symm_apply]⟩)
  let X : SmoothField B := ⟨v, hs⟩
  have hX (p : M) : coefficients B X.val e he p = F (e p).val := by
    simp only [coefficients_eq X.val e he p (hp p), X, v, LinearEquiv.apply_symm_apply]
  refine ⟨X, hX, ?_⟩
  intro Y hY
  apply field_ext
  funext p
  apply (B.fiberCoordinates.equiv e he p (hp p)).injective
  exact (coefficients_eq Y.val e he p (hp p)).symm.trans
    ((hY p).trans ((hX p).symm.trans (coefficients_eq X.val e he p (hp p))))

theorem smooth_of_full_charts {m : ℕ} {c : ModelKind} {N : Type u} [TopologicalSpace N]
    (T : SmoothManifold m c N) (e : ModelChart n a M) (d : ModelChart m c N)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hefull : e.source = univ) (hdfull : d.source = univ)
    (f : M → N) (F : Euclidean n → Euclidean m) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hcoord : ∀ x, (d (f x)).val = F (e x).val) : IsSmoothMap S T f := by
  have hep (p : M) : p ∈ e.source := hefull.symm ▸ mem_univ p
  have hdp (p : N) : p ∈ d.source := hdfull.symm ▸ mem_univ p
  intro p
  have hcf : ContinuousAt (fun x => (d (f x)).val) p :=
    (TangentBundle.euclidean_smoothAt_of_chart S (fun x => (d (f x)).val) p e he (hep p)
      ⟨univ, isOpen_univ, mem_univ _, F, hF.contDiffOn,
        Eventually.of_forall (fun x => (hcoord x).symm)⟩).1
  have hcd : ContinuousAt (fun x => d (f x)) p := hcf.codRestrict _
  have hcont : ContinuousAt f p :=
    ((d.symm.continuousAt (d.map_source (hdp (f p)))).comp (f := fun x => d (f x)) hcd).congr
      (Eventually.of_forall (fun x => d.left_inv (hdp (f x))))
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _ S.smoothStructure.property.1
    T.smoothStructure.property.1 f p).mpr
  exact ⟨hcont, e, he, d, hd, hep p, hdp (f p), univ, isOpen_univ, mem_univ _,
    F, hF.contDiffOn, Eventually.of_forall (fun x => (hcoord x).symm)⟩

noncomputable def matrixRightMap {d : ℕ} {P : Type u} [TopologicalSpace P] (A : MatrixGroupModel d P)
    (v : Matrix (Fin d) (Fin d) ℝ) : Euclidean (d * d) →L[ℝ] Euclidean (d * d) :=
  A.coordinates.toContinuousLinearMap.comp
    ((LinearMap.mulRight ℝ v).toContinuousLinearMap.comp A.coordinates.symm.toContinuousLinearMap)

noncomputable def matrixLeftMap {d : ℕ} {P : Type u} [TopologicalSpace P] (A : MatrixGroupModel d P)
    (v : Matrix (Fin d) (Fin d) ℝ) : Euclidean (d * d) →L[ℝ] Euclidean (d * d) :=
  A.coordinates.toContinuousLinearMap.comp
    ((LinearMap.mulLeft ℝ v).toContinuousLinearMap.comp A.coordinates.symm.toContinuousLinearMap)

@[simp] theorem matrixRightMap_apply {d : ℕ} {P : Type u} [TopologicalSpace P] (A : MatrixGroupModel d P)
    (v : Matrix (Fin d) (Fin d) ℝ) (z : Euclidean (d * d)) :
    matrixRightMap A v z = A.coordinates (A.coordinates.symm z * v) := rfl

@[simp] theorem matrixLeftMap_apply {d : ℕ} {P : Type u} [TopologicalSpace P] (A : MatrixGroupModel d P)
    (v : Matrix (Fin d) (Fin d) ℝ) (z : Euclidean (d * d)) :
    matrixLeftMap A v z = A.coordinates (v * A.coordinates.symm z) := rfl

theorem matrix_field_exists {d : ℕ} {P : Type u} [TopologicalSpace P] (A : MatrixGroupModel d P) (v : Matrix (Fin d) (Fin d) ℝ) :
    ∃! X : SmoothField A.bundle, MatrixField A v X := by
  have heq (g : P) :
      matrixRightMap A v (A.chart g).val = A.coordinates ((A.points g).val * v) := by
    simp only [matrixRightMap_apply, A.chart_apply, ContinuousLinearEquiv.symm_apply_apply]
  simpa only [MatrixField, heq] using (field_of_full_chart (B := A.bundle) A.chart A.chart_mem
    A.full_source (matrixRightMap A v) (matrixRightMap A v).contDiff)

theorem matrix_left_smooth {d : ℕ} {P : Type u} [TopologicalSpace P] (A : MatrixGroupModel d P) (g : P) :
    IsSmoothMap A.manifold A.manifold (matrixLeftOn A g) := by
  apply smooth_of_full_charts A.manifold A.chart A.chart A.chart_mem A.chart_mem
    A.full_source A.full_source (matrixLeftOn A g) (matrixLeftMap A (A.points g).val) (matrixLeftMap A (A.points g).val).contDiff
  intro p
  simp only [A.chart_apply, matrixLeft, matrixLeftMap_apply, ContinuousLinearEquiv.symm_apply_apply, matrixLeftOn, Homeomorph.apply_symm_apply]

theorem matrix_field_derivative {d : ℕ} {P : Type u} [TopologicalSpace P] (A : MatrixGroupModel d P)
    (v : Matrix (Fin d) (Fin d) ℝ) (X : SmoothField A.bundle) (hX : MatrixField A v X)
    (p : P) :
    HasCoordinateDerivative A.chart (coefficients A.bundle X.val A.chart A.chart_mem) p
      (matrixRightMap A v) := by
  refine ⟨matrixRightMap A v, (matrixRightMap A v).hasFDerivAt, ?_⟩
  apply Eventually.of_forall
  intro q
  change matrixRightMap A v (A.chart q).val = _
  rw [hX q, matrixRightMap_apply, A.chart_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem matrix_field_invariant {d : ℕ} {P : Type u} [TopologicalSpace P] (A : MatrixGroupModel d P)
    (v : Matrix (Fin d) (Fin d) ℝ) (X : SmoothField A.bundle) (hX : MatrixField A v X)
    (g p : P)
    (L : TangentSpace A.manifold p →ₗ[ℝ] TangentSpace A.manifold (matrixLeftOn A g p))
    (hL : IsDifferential A.manifold A.manifold (matrixLeftOn A g) p L) :
    L (X.val p) = X.val (matrixLeftOn A g p) := by
  have hp (q : P) : q ∈ A.chart.source := A.full_source.symm ▸ mem_univ q
  let K := A.bundle.fiberCoordinates
  have hjac := differential_jacobian A.manifold A.manifold (matrixLeftOn A g)
    (matrix_left_smooth A g) p L hL A.chart A.chart A.chart_mem A.chart_mem
    (hp p) (hp (matrixLeftOn A g p)) (K.equiv A.chart A.chart_mem p (hp p))
    (K.equiv A.chart A.chart_mem (matrixLeftOn A g p) (hp (matrixLeftOn A g p)))
    (K.isCoordinates A.chart A.chart_mem p (hp p))
    (K.isCoordinates A.chart A.chart_mem (matrixLeftOn A g p) (hp (matrixLeftOn A g p)))
    univ (matrixLeftMap A (A.points g).val) isOpen_univ (mem_univ _)
    (matrixLeftMap A (A.points g).val).contDiff.contDiffOn
    (Eventually.of_forall (fun q => by
      simp only [matrixLeftMap_apply, A.chart_apply, ContinuousLinearEquiv.symm_apply_apply, matrixLeftOn, Homeomorph.apply_symm_apply, matrixLeft]))
    (X.val p)
  apply (K.equiv A.chart A.chart_mem (matrixLeftOn A g p) (hp (matrixLeftOn A g p))).injective
  rw [hjac, (matrixLeftMap A (A.points g).val).fderiv]
  rw [← coefficients_eq X.val A.chart A.chart_mem p (hp p),
    ← coefficients_eq X.val A.chart A.chart_mem (matrixLeftOn A g p) (hp (matrixLeftOn A g p))]
  change matrixLeftMap A (A.points g).val (coefficients A.bundle X.val A.chart A.chart_mem p) =
    coefficients A.bundle X.val A.chart A.chart_mem (matrixLeftOn A g p)
  rw [hX p, hX (matrixLeftOn A g p), matrixLeftMap_apply, ContinuousLinearEquiv.symm_apply_apply]
  simp only [matrixLeftOn, Homeomorph.apply_symm_apply, matrixLeft]
  change A.coordinates ((A.points g).val * ((A.points p).val * v)) = A.coordinates (((A.points g).val * (A.points p).val) * v)
  rw [mul_assoc]

theorem matrix_fields_conditional
    (hcoeff : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.chart_coefficientsType.{u})
    (hc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.correspondenceType.{u})
    (hact : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_actionType.{u})
    (hlpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_pushforwardType.{u})
    (hloc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.localityType.{u})
    (hpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.pushforwardType.{u})
    (hr : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.related_iffType.{u}) :
    Specs.SmoothManifolds.Ch06.LieBracket.matrix_fieldsType.{u} := by
  intro P _ d A b hb
  refine ⟨matrix_field_exists A, matrix_field_invariant A, ?_⟩
  intro v w X Y hX hY g
  have hp : g ∈ A.chart.source := A.full_source.symm ▸ mem_univ g
  have hcoord := (bracket_coordinates_conditional hcoeff hc hact hlpush hloc hpush hr
    A.manifold A.bundle b hb X Y).2 A.chart A.chart_mem g hp
    (matrixRightMap A v) (matrixRightMap A w)
    (matrix_field_derivative A v X hX g) (matrix_field_derivative A w Y hY g)
  calc
    coefficients A.bundle (b X Y).val A.chart A.chart_mem g =
        matrixRightMap A w (coefficients A.bundle X.val A.chart A.chart_mem g) -
          matrixRightMap A v (coefficients A.bundle Y.val A.chart A.chart_mem g) := by
      funext j
      exact (hcoord j).trans (coordinate_commutator_sum _ _ _ _ j).symm
    _ = A.coordinates ((A.points g).val * (v * w - w * v)) := by
      rw [hX g, hY g, matrixRightMap_apply, matrixRightMap_apply,
        ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply,
        ← map_sub, mul_sub, mul_assoc, mul_assoc]

noncomputable def matrixCoordinates (d : ℕ) :
    Matrix (Fin d) (Fin d) ℝ ≃L[ℝ] Euclidean (d * d) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [Module.finrank_matrix, Module.finrank_pi]
    simp)

theorem matrixInvertible_isOpen (d : ℕ) : IsOpen {g : Matrix (Fin d) (Fin d) ℝ | IsUnit g} := by
  simpa only [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, id_eq] using
    (isOpen_ne_fun (continuous_id.matrix_det : Continuous (fun g : Matrix (Fin d) (Fin d) ℝ => g.det)) continuous_const)

noncomputable def matrixChart (d : ℕ) : ModelChart (d * d) .euclidean (OpenMatrixGroup d) := by
  let C := matrixCoordinates d
  let H : Euclidean (d*d) ≃ₜ ModelSpace (d*d) .euclidean :=
    (Homeomorph.Set.univ (Euclidean (d*d))).symm
  let f : OpenMatrixGroup d → ModelSpace (d*d) .euclidean := fun g => H (C g.val)
  have hf : Topology.IsOpenEmbedding f :=
    H.isOpenEmbedding.comp (C.toHomeomorph.isOpenEmbedding.comp
      (matrixInvertible_isOpen d).isOpenEmbedding_subtypeVal)
  letI : Nonempty (OpenMatrixGroup d) := ⟨⟨1, isUnit_one⟩⟩
  exact hf.toOpenPartialHomeomorph f

@[simp] theorem matrixChart_source (d : ℕ) : (matrixChart d).source = univ := by
  simp [matrixChart]

@[simp] theorem matrixChart_val (d : ℕ) (g : OpenMatrixGroup d) :
    ((matrixChart d) g).val = matrixCoordinates d g.val := by
  rfl

theorem fullChart_compatible_self {n : ℕ} {M : Type u} [TopologicalSpace M]
    (c : ModelChart n .euclidean M) : ContDiffCompatible (⊤ : ℕ∞) c c := by
  have h : ContDiffOnModel (⊤ : ℕ∞) (c.symm.trans c) (c.symm.trans c).source := by
    intro x hx
    refine ⟨univ, isOpen_univ, mem_univ _, id, contDiffOn_id, ?_⟩
    intro y hy _
    have hyc : y ∈ c.target := hy.1
    exact congrArg Subtype.val (c.right_inv hyc).symm
  refine ⟨h, ?_⟩
  intro x hx
  refine ⟨univ, isOpen_univ, mem_univ _, id, contDiffOn_id, ?_⟩
  intro y hy _
  have hyc : y ∈ c.target := by
    exact hy.1
  change y.val = (c (c.symm y)).val
  exact congrArg Subtype.val (c.right_inv hyc).symm

theorem matrix_model_construct (d : ℕ) : Nonempty (MatrixGroupModel d (OpenMatrixGroup d)) := by
  let c := matrixChart d
  let A : Set (ModelChart (d*d) .euclidean (OpenMatrixGroup d)) := {c}
  have hA : IsContDiffAtlas (⊤ : ℕ∞) A := by
    constructor
    · intro p
      exact ⟨c, mem_singleton _, by simp [c]⟩
    · intro e he f hf
      rcases (mem_singleton_iff.mp he) with rfl
      rcases (mem_singleton_iff.mp hf) with rfl
      exact fullChart_compatible_self c
  letI : SecondCountableTopology (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  letI : SecondCountableTopology (OpenMatrixGroup d) := by
    unfold OpenMatrixGroup
    exact TopologicalSpace.Subtype.secondCountableTopology _
  let S : SmoothManifold (d*d) .euclidean (OpenMatrixGroup d) := {
    topologicalManifold := {
      hausdorff := inferInstance
      secondCountable := inferInstance
      atlas := A
      covers := hA.1 }
    smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) A, maximalExtension_isMaximal hA⟩ }
  obtain ⟨B⟩ := TangentBundle.exists_bundle S
  exact ⟨{
    points := Homeomorph.refl _
    coordinates := matrixCoordinates d
    manifold := S
    bundle := B
    chart := c
    chart_mem := subset_maximalExtension hA (mem_singleton _)
    full_source := matrixChart_source d
    chart_apply := matrixChart_val d }⟩

theorem matrix_model_exists_conditional
    (_hcoeff : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.chart_coefficientsType.{u})
    (_hc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.correspondenceType.{u})
    (_hact : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_actionType.{u})
    (_hlpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_pushforwardType.{u})
    (_hloc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.localityType.{u})
    (_hpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.pushforwardType.{u})
    (_hr : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.related_iffType.{u}) :
    Specs.SmoothManifolds.Ch06.LieBracket.matrix_model_existsType :=
  matrix_model_construct


end SmoothManifolds.LieBrackets

namespace SmoothManifolds.LieBrackets
open ModelData AtlasData MapData PartitionData TangentData DifferentialData
  TangentBundleData VectorFieldData FiniteRegularityData LieBracketData ProductData Set Filter
open scoped Topology ContDiff
universe u
noncomputable def leftDifferential {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    {S : SmoothManifold n .euclidean G} (A : LieGroupStructure S) (g : G) :
    TangentData.TangentSpace S 1 →ₗ[ℝ] TangentData.TangentSpace S g := by
  have L := Classical.choose (differential_exists S S (fun p => g * p)
    (left_translation_smooth A g) 1)
  exact (mul_one g) ▸ L

theorem leftDifferential_spec {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    {S : SmoothManifold n .euclidean G} (A : LieGroupStructure S) (g : G) :
    IsDifferential S S (fun p => g * p) 1
      ((mul_one g).symm ▸ leftDifferential A g) := by
  have hcancel {x y : G} (h : x = y)
      (L : TangentData.TangentSpace S 1 →ₗ[ℝ] TangentData.TangentSpace S x) :
      (h.symm ▸ (h ▸ L)) = L := by cases h; rfl
  change IsDifferential S S (fun p => g * p) 1
    ((mul_one g).symm ▸ ((mul_one g) ▸ _))
  rw [hcancel]
  exact (Classical.choose_spec (differential_exists S S (fun p => g * p)
      (left_translation_smooth A g) 1)).1

end SmoothManifolds.LieBrackets
namespace SmoothManifolds.LieBrackets
open ModelData AtlasData MapData PartitionData TangentData DifferentialData
  TangentBundleData VectorFieldData FiniteRegularityData LieBracketData ProductData Set Filter
open scoped Topology ContDiff
universe u

theorem leftDifferential_sigma {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    {S : SmoothManifold n .euclidean G} (A : LieGroupStructure S)
    (v : TangentData.TangentSpace S 1) (g : G) :
    (⟨g, leftDifferential A g v⟩ : TotalSpace S) =
      ⟨g * 1, Classical.choose (differential_exists S S (fun p => g * p)
        (left_translation_smooth A g) 1) v⟩ := by
  have htransport {x y : G} (h : x = y)
      (L : TangentData.TangentSpace S 1 →ₗ[ℝ] TangentData.TangentSpace S x) :
      (⟨y, (h ▸ L) v⟩ : TotalSpace S) = ⟨x, L v⟩ := by cases h; rfl
  exact htransport (mul_one g) _


theorem leftDifferential_smooth {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    {S : SmoothManifold n .euclidean G} (A : LieGroupStructure S)
    (B : TangentBundleStructure S) (v : TangentData.TangentSpace S 1) :
    letI := B.topology
    IsSmoothMap S B.manifold (fun g => ⟨g, leftDifferential A g v⟩) := by
  letI := B.topology
  intro g0
  obtain ⟨e, he, heg⟩ := S.smoothStructure.property.1.1 g0
  obtain ⟨d, hd, hd1⟩ := S.smoothStructure.property.1.1 (1 : G)
  have hprod : productChart A.productCoordinates e d ∈ A.productManifold.smoothStructure.val := by
    rw [A.productAtlas]
    exact subset_maximalExtension (productAtlas_isContDiffAtlas A.productCoordinates _ _ _
      S.smoothStructure.property.1 S.smoothStructure.property.1) ⟨e, he, d, hd, rfl⟩
  have hpg : (g0, (1 : G)) ∈ (productChart A.productCoordinates e d).source := by
    simpa only [productChart_source, Set.mem_prod] using And.intro heg hd1
  have hegg : g0 * (1 : G) ∈ e.source := by simpa using heg
  obtain ⟨U, hU, hpU, F, hF, hrep⟩ :=
    (A.multiplication_smooth (g0, 1)).2 _ hprod e he hpg hegg
  change A.productCoordinates.linearEquiv ((e g0).val, (d 1).val) ∈ U at hpU
  let C := A.productCoordinates.linearEquiv
  let Ev := B.fiberCoordinates.equiv d hd 1 hd1 v
  let I : Euclidean n →L[ℝ] Euclidean (n+n) := C.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ (Euclidean n) (Euclidean n))
  let embed : Euclidean n → Euclidean (n+n) := fun z => C (z, (d 1).val)
  have hembed : ContDiff ℝ (⊤ : ℕ∞) embed :=
    C.contDiff.comp (contDiff_id.prodMk contDiff_const)
  let W := embed ⁻¹' U
  have hW : IsOpen W := hU.preimage hembed.continuous
  have hgW : (e g0).val ∈ W := hpU
  let H : Euclidean n → Euclidean n := fun z => fderiv ℝ F (embed z) (I Ev)
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H W := by
    exact ((hF.fderiv_of_isOpen hU (by simp)).comp hembed.contDiffOn
      (fun _ hz => hz)).clm_apply contDiffOn_const
  apply TangentBundle.lift_smoothAt_of_coeff S B S
    (fun g => ⟨g, leftDifferential A g v⟩) g0 e he heg
    (fun g => H (e g).val)
    (manifoldContDiff_id (⊤ : ℕ∞) S.smoothStructure.val S.smoothStructure.property.1 g0)
  · exact TangentBundle.euclidean_smoothAt_of_chart S _ g0 e he heg
      ⟨W, hW, hgW, H, hH, Eventually.of_forall (fun _ => rfl)⟩
  have hdg : ContinuousAt (fun g : G => (g, (1 : G))) g0 :=
    continuousAt_id.prodMk continuousAt_const
  have hcoord : ContinuousAt (fun g => (e g).val) g0 :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt heg)
  filter_upwards [e.open_source.mem_nhds heg,
    hcoord.preimage_mem_nhds (hW.mem_nhds hgW),
    hdg.preimage_mem_nhds (eventually_eventually_nhds.mpr hrep)] with g hg hgU hgrep
  refine ⟨hg, ?_⟩
  let E := B.fiberCoordinates.equiv
  let L := Classical.choose (differential_exists S S (fun q => g * q)
    (left_translation_smooth A g) 1)
  have hL := (Classical.choose_spec (differential_exists S S (fun q => g * q)
    (left_translation_smooth A g) 1)).1
  have hg1 : g * (1 : G) ∈ e.source := by simpa using hg
  let embedg : Euclidean n → Euclidean (n+n) := fun z => C ((e g).val, z)
  have hegsm : ContDiff ℝ (⊤ : ℕ∞) embedg :=
    C.contDiff.comp (contDiff_const.prodMk contDiff_id)
  let V := embedg ⁻¹' U
  have hV : IsOpen V := hU.preimage hegsm.continuous
  have h1V : (d 1).val ∈ V := hgU
  have hfg : ContDiffOn ℝ (⊤ : ℕ∞) (F ∘ embedg) V :=
    hF.comp hegsm.contDiffOn (fun _ hz => hz)
  have hrg : (fun q => (F ∘ embedg) (d q).val) =ᶠ[𝓝 (1 : G)]
      (fun q => (e (g * q)).val) := by
    have hc : ContinuousAt (fun q : G => (g, q)) 1 :=
      continuousAt_const.prodMk continuousAt_id
    have hgrep' : (fun z : G × G => F (productChart A.productCoordinates e d z).val)
        =ᶠ[𝓝 (g, 1)] (fun z => (e (z.1 * z.2)).val) := hgrep
    filter_upwards [hgrep'.comp_tendsto hc] with q hq
    exact hq
  have hj := differential_jacobian S S (fun q => g * q) (left_translation_smooth A g) 1
    L hL d e hd he hd1 hg1 (E d hd 1 hd1) (E e he (g*1) hg1)
    (B.fiberCoordinates.isCoordinates d hd 1 hd1)
    (B.fiberCoordinates.isCoordinates e he (g*1) hg1)
    V (F ∘ embedg) hV h1V hfg hrg v
  have hFg : DifferentiableAt ℝ F (embedg (d 1).val) :=
    (hF.contDiffAt (hU.mem_nhds h1V)).differentiableAt (by simp)
  have hegder : HasFDerivAt embedg I (d 1).val := by
    convert C.hasFDerivAt.comp (d 1).val
      (hasFDerivAt_const (e g).val (d 1).val |>.prodMk (hasFDerivAt_id (d 1).val)) using 1
    all_goals rfl
  have hder := (hFg.hasFDerivAt.comp (d 1).val hegder).fderiv
  rw [hder] at hj
  have hs := congrArg (TangentBundle.chartFiber B e he) (leftDifferential_sigma A v g)
  rw [TangentBundle.chartFiber_eq S B e he _ hg,
    TangentBundle.chartFiber_eq S B e he _ hg1] at hs
  exact (hj.trans (by rfl)).symm.trans hs.symm

/-- The normalized identity-to-g differential is independent of its representative. -/
theorem leftDifferential_sigma_of_eq {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    {S : SmoothManifold n .euclidean G} (A : LieGroupStructure S)
    (v : TangentSpace S 1) (g : G) (f : G → G) (hf : f = fun q => g * q)
    (L : TangentSpace S 1 →ₗ[ℝ] TangentSpace S (f 1))
    (hL : IsDifferential S S f 1 L) :
    (⟨g, leftDifferential A g v⟩ : TotalSpace S) = ⟨f 1, L v⟩ := by
  subst f
  have huniq := (Classical.choose_spec (differential_exists S S (fun p => g * p)
    (left_translation_smooth A g) 1)).2 L hL
  exact (leftDifferential_sigma A v g).trans (by rw [huniq])

theorem leftDifferential_one {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    {S : SmoothManifold n .euclidean G} (A : LieGroupStructure S)
    (v : TangentSpace S 1) : leftDifferential A 1 v = v := by
  have h := leftDifferential_sigma_of_eq A v 1 id (by funext q; exact (one_mul q).symm)
    LinearMap.id (differential_id S 1)
  exact eq_of_heq (Sigma.mk.inj h).2

theorem leftDifferential_invariant {n : ℕ} {G : Type u} [TopologicalSpace G] [Group G]
    {S : SmoothManifold n .euclidean G} (A : LieGroupStructure S)
    (v : TangentSpace S 1) (g p : G)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace S (g * p))
    (hL : IsDifferential S S (fun q => g * q) p L) :
    L (leftDifferential A p v) = leftDifferential A (g * p) v := by
  classical
  let K (q : G) : TangentSpace S q →ₗ[ℝ] TangentSpace S (g * q) :=
    Classical.choose (differential_exists S S (fun q => g * q) (left_translation_smooth A g) q)
  have hK (q : G) : IsDifferential S S (fun q => g * q) q (K q) :=
    (Classical.choose_spec (differential_exists S S (fun q => g * q)
      (left_translation_smooth A g) q)).1
  let P : TangentSpace S 1 →ₗ[ℝ] TangentSpace S (p * 1) :=
    Classical.choose (differential_exists S S (fun q => p * q) (left_translation_smooth A p) 1)
  have hP : IsDifferential S S (fun q => p * q) 1 P :=
    (Classical.choose_spec (differential_exists S S (fun q => p * q)
      (left_translation_smooth A p) 1)).1
  have hcomp := differential_comp S S S (fun q => p * q) (fun q => g * q)
    (left_translation_smooth A p) (left_translation_smooth A g) 1 P (K (p * 1)) hP (hK (p * 1))
  have hfirst := congrArg (totalMap S S (fun q => g * q) K)
    (leftDifferential_sigma_of_eq A v p (fun q => p * q) rfl P hP)
  have hsecond := leftDifferential_sigma_of_eq A v (g * p)
    ((fun q => g * q) ∘ (fun q => p * q))
    (by funext q; exact (mul_assoc g p q).symm)
    ((K (p * 1)).comp P) hcomp
  have hs : (⟨g * p, K p (leftDifferential A p v)⟩ : TotalSpace S) =
      ⟨g * p, leftDifferential A (g * p) v⟩ := hfirst.trans hsecond.symm
  have hKL : L = K p :=
    (Classical.choose_spec (differential_exists S S (fun q => g * q)
      (left_translation_smooth A g) p)).2 L hL
  rw [hKL]
  exact eq_of_heq (Sigma.mk.inj hs).2

theorem leftInvariant_correspondence_conditional
    (hcoeff : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.chart_coefficientsType.{u})
    (hc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.correspondenceType.{u})
    (hact : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_actionType.{u})
    (hlpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.local_pushforwardType.{u})
    (hloc : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.localityType.{u})
    (hpush : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.pushforwardType.{u})
    (hr : Specs.SmoothManifolds.Ch06.VectorFieldDerivations.related_iffType.{u}) :
    Specs.SmoothManifolds.Ch06.LieBracket.leftInvariant_correspondenceType.{u} := by
  intro n G _ _ S B A
  let make (v : TangentSpace S 1) : LeftInvariantField B :=
    ⟨⟨fun g => leftDifferential A g v, leftDifferential_smooth A B v⟩,
      leftDifferential_invariant A v⟩
  let e : TangentSpace S 1 ≃ LeftInvariantField B :=
    { toFun := make
      invFun := fun X => X.val.val 1
      left_inv := leftDifferential_one A
      right_inv := fun X => leftInvariant_eval_injective A (leftDifferential_one A _) }
  refine ⟨e, fun _ => rfl, ?_⟩
  intro v g L hL
  exact leftDifferential_sigma_of_eq A v g (fun q => g * q) rfl L hL

end SmoothManifolds.LieBrackets

universe v8_closure_a710d91318ac1890_u0
theorem _root_.«SmoothManifolds».«LieBrackets».«bracket_algebra» : _root_.«Specs».«SmoothManifolds».«Ch06».«LieBracket».«bracket_algebraType».{v8_closure_a710d91318ac1890_u0} :=
  @_root_.«SmoothManifolds».«LieBrackets».«bracket_algebra_conditional».{v8_closure_a710d91318ac1890_u0} (@_root_.«SmoothManifolds».«VectorFields».«chart_coefficients».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«correspondence».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_action».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_pushforward».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«locality».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«pushforward».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«related_iff».{v8_closure_a710d91318ac1890_u0})
theorem _root_.«SmoothManifolds».«LieBrackets».«bracket_coordinates» : _root_.«Specs».«SmoothManifolds».«Ch06».«LieBracket».«bracket_coordinatesType».{v8_closure_a710d91318ac1890_u0} :=
  @_root_.«SmoothManifolds».«LieBrackets».«bracket_coordinates_conditional».{v8_closure_a710d91318ac1890_u0} (@_root_.«SmoothManifolds».«VectorFields».«chart_coefficients».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«correspondence».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_action».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_pushforward».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«locality».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«pushforward».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«related_iff».{v8_closure_a710d91318ac1890_u0})
theorem _root_.«SmoothManifolds».«LieBrackets».«bracket_exists» : _root_.«Specs».«SmoothManifolds».«Ch06».«LieBracket».«bracket_existsType».{v8_closure_a710d91318ac1890_u0} :=
  @_root_.«SmoothManifolds».«LieBrackets».«bracket_exists_conditional».{v8_closure_a710d91318ac1890_u0} (@_root_.«SmoothManifolds».«VectorFields».«chart_coefficients».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«correspondence».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_action».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_pushforward».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«locality».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«pushforward».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«related_iff».{v8_closure_a710d91318ac1890_u0})
theorem _root_.«SmoothManifolds».«LieBrackets».«bracket_finiteRegularity» : _root_.«Specs».«SmoothManifolds».«Ch06».«LieBracket».«bracket_finiteRegularityType».{v8_closure_a710d91318ac1890_u0} :=
  @_root_.«SmoothManifolds».«LieBrackets».«bracket_finiteRegularity_conditional».{v8_closure_a710d91318ac1890_u0} (@_root_.«SmoothManifolds».«VectorFields».«chart_coefficients».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«correspondence».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_action».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_pushforward».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«locality».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«pushforward».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«related_iff».{v8_closure_a710d91318ac1890_u0})
theorem _root_.«SmoothManifolds».«LieBrackets».«bracket_related» : _root_.«Specs».«SmoothManifolds».«Ch06».«LieBracket».«bracket_relatedType».{v8_closure_a710d91318ac1890_u0} :=
  @_root_.«SmoothManifolds».«LieBrackets».«bracket_related_conditional».{v8_closure_a710d91318ac1890_u0} (@_root_.«SmoothManifolds».«VectorFields».«chart_coefficients».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«correspondence».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_action».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_pushforward».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«locality».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«pushforward».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«related_iff».{v8_closure_a710d91318ac1890_u0})
theorem _root_.«SmoothManifolds».«LieBrackets».«leftInvariant_bracket» : _root_.«Specs».«SmoothManifolds».«Ch06».«LieBracket».«leftInvariant_bracketType».{v8_closure_a710d91318ac1890_u0} :=
  @_root_.«SmoothManifolds».«LieBrackets».«leftInvariant_bracket_conditional».{v8_closure_a710d91318ac1890_u0} (@_root_.«SmoothManifolds».«VectorFields».«chart_coefficients».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«correspondence».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_action».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_pushforward».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«locality».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«pushforward».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«related_iff».{v8_closure_a710d91318ac1890_u0})
theorem _root_.«SmoothManifolds».«LieBrackets».«leftInvariant_correspondence» : _root_.«Specs».«SmoothManifolds».«Ch06».«LieBracket».«leftInvariant_correspondenceType».{v8_closure_a710d91318ac1890_u0} :=
  @_root_.«SmoothManifolds».«LieBrackets».«leftInvariant_correspondence_conditional».{v8_closure_a710d91318ac1890_u0} (@_root_.«SmoothManifolds».«VectorFields».«chart_coefficients».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«correspondence».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_action».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_pushforward».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«locality».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«pushforward».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«related_iff».{v8_closure_a710d91318ac1890_u0})
theorem _root_.«SmoothManifolds».«LieBrackets».«matrix_fields» : _root_.«Specs».«SmoothManifolds».«Ch06».«LieBracket».«matrix_fieldsType».{v8_closure_a710d91318ac1890_u0} :=
  @_root_.«SmoothManifolds».«LieBrackets».«matrix_fields_conditional».{v8_closure_a710d91318ac1890_u0} (@_root_.«SmoothManifolds».«VectorFields».«chart_coefficients».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«correspondence».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_action».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«local_pushforward».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«locality».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«pushforward».{v8_closure_a710d91318ac1890_u0}) (@_root_.«SmoothManifolds».«VectorFields».«related_iff».{v8_closure_a710d91318ac1890_u0})
theorem _root_.«SmoothManifolds».«LieBrackets».«matrix_model_exists» : _root_.«Specs».«SmoothManifolds».«Ch06».«LieBracket».«matrix_model_existsType» :=
  SmoothManifolds.LieBrackets.matrix_model_construct
