import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction
import MathGenome.Internal.RealAnalysis.D11.Ch10.LpDefinition
import Mathlib.Analysis.Normed.Module.TransferInstance

/-! The ordinary measurable raw quotient is linearly isometric to native Lp.
The map is built from representatives, and its inverse uses the strongly
measurable representative supplied by native Lp. Both directions work on
incomplete, non-sigma-finite spaces, including zero measures and empty spaces.
The transferred operations are proved to be the quotient pointwise operations.
-/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch10.QuotientConstruction

open Specs.D11.Ch10.QuotientConstruction

variable {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- The ordinary measurable raw-function quotient, with its canonical Spec carrier. -/
def quotientLp (μ : Measure X) (p : ℝ≥0∞) : Type u := QuotientLp (𝕜 := 𝕜) μ p

theorem raw_finite : Specs.D11.Ch10.QuotientConstruction.raw_finite := by
  intro X 𝕜 _ _ _ _ μ p hp f
  exact (LpDefinition.rawLp_iff_memLp μ p f hp).symm

theorem raw_top : Specs.D11.Ch10.QuotientConstruction.raw_top := by
  intro X 𝕜 _ _ _ _ μ f
  exact (LpDefinition.rawLInfinity_iff_memLp μ f).symm

/-- Literal null failure sets and native a.e. equality agree. -/
theorem nullRelation_iff_native (μ : Measure X) (p : ℝ≥0∞)
    (f g : Raw (𝕜 := 𝕜) μ p) : nullRelation μ p f g ↔ f.val =ᵐ[μ] g.val := by
  change _ ↔ ∀ᵐ x ∂μ, f.val x = g.val x
  rw [ae_iff]
  rfl

theorem sourceNorm_bridge : Specs.D11.Ch10.QuotientConstruction.sourceNorm_bridge := by
  intro X 𝕜 _ _ _ _ μ p hp f
  unfold sourceNorm
  split_ifs with h
  · subst p
    exact LpDefinition.essentialSupNorm_eq_eLpNorm μ f.val f.property.1
  · have hr : 1 ≤ p.toReal := by
      exact_mod_cast (ENNReal.toReal_le_toReal ENNReal.one_ne_top h).mpr hp
    have heq := LpDefinition.powerNorm_eq_eLpNorm μ p.toReal f.val hr f.property.1
    simpa only [ENNReal.ofReal_toReal h] using heq

theorem measurable_exception : Specs.D11.Ch10.QuotientConstruction.measurable_exception := by
  intro X 𝕜 _ _ _ _ μ p f g
  exact (measurableSet_eq_fun f.property.1 g.property.1).compl

theorem ordinary_relation : Specs.D11.Ch10.QuotientConstruction.ordinary_relation := by
  intro X 𝕜 _ _ _ _ μ p f g
  exact (nullRelation_iff_native μ p f g).trans
    (D11.Ch04.AeCommonException.aeEq_iff_native μ f.val g.val).symm

theorem relation_equivalence : Specs.D11.Ch10.QuotientConstruction.relation_equivalence := by
  intro X 𝕜 _ _ _ _ μ p
  exact (rawSetoid (𝕜 := 𝕜) μ p).iseqv

theorem operations_compatible : Specs.D11.Ch10.QuotientConstruction.operations_compatible := by
  intro X 𝕜 _ _ _ _ μ p f f' g g' hf hg
  have hf' := (nullRelation_iff_native μ p f f').mp hf
  have hg' := (nullRelation_iff_native μ p g g').mp hg
  exact ⟨(nullRelation_iff_native μ p (f + g) (f' + g')).mpr (hf'.add hg'),
    fun c => (nullRelation_iff_native μ p (c • f) (c • f')).mpr (hf'.const_smul c)⟩

theorem norm_congr : Specs.D11.Ch10.QuotientConstruction.norm_congr := by
  intro X 𝕜 _ _ _ _ μ p hp f g h
  rw [sourceNorm_bridge μ p hp f, sourceNorm_bridge μ p hp g]
  exact eLpNorm_congr_ae ((nullRelation_iff_native μ p f g).mp h)

/-- Representative map into native Lp; its domain requires actual measurability. -/
def toNative (μ : Measure X) (p : ℝ≥0∞) : QuotientLp (𝕜 := 𝕜) μ p → Lp 𝕜 p μ :=
  Quotient.lift (fun f : Raw (𝕜 := 𝕜) μ p => f.property.2.toLp f.val)
    (fun f g h => MemLp.toLp_congr f.property.2 g.property.2
      ((nullRelation_iff_native μ p f g).mp h))

@[simp] theorem toNative_classOf (μ : Measure X) (p : ℝ≥0∞)
    (f : Raw (𝕜 := 𝕜) μ p) : toNative μ p (classOf f) = f.property.2.toLp f.val := rfl

/-- Native Lp has an ordinary strongly measurable representative even when the
ambient measure is incomplete. No arbitrary a.e. modification is used. -/
def nativeRepresentative (μ : Measure X) (p : ℝ≥0∞) (f : Lp 𝕜 p μ) :
    Raw (𝕜 := 𝕜) μ p :=
  ⟨f, (Lp.stronglyMeasurable f).measurable, Lp.memLp f⟩

def nativeEquiv (μ : Measure X) (p : ℝ≥0∞) : QuotientLp (𝕜 := 𝕜) μ p ≃ Lp 𝕜 p μ where
  toFun := toNative μ p
  invFun := fun f => classOf (nativeRepresentative μ p f)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ f =>
      apply Quotient.sound
      apply (nullRelation_iff_native μ p _ _).mpr
      exact MemLp.coeFn_toLp f.property.2
  right_inv := by
    intro f
    exact Lp.toLp_coeFn f (Lp.memLp f)

instance quotientNormedAddCommGroup (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    NormedAddCommGroup (QuotientLp (𝕜 := 𝕜) μ p) := (nativeEquiv μ p).normedAddCommGroup

/-- The additive equivalence for the transported group structure. -/
def nativeAddEquiv (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    QuotientLp (𝕜 := 𝕜) μ p ≃+ Lp 𝕜 p μ := (nativeEquiv μ p).addEquiv

instance quotientNormedSpace (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    NormedSpace 𝕜 (QuotientLp (𝕜 := 𝕜) μ p) := (nativeAddEquiv μ p).normedSpace 𝕜

set_option maxHeartbeats 1200000 in
def nativeLinearIsometryEquiv (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    QuotientLp (𝕜 := 𝕜) μ p ≃ₗᵢ[𝕜] Lp 𝕜 p μ :=
  { (nativeAddEquiv μ p).linearEquiv 𝕜 with norm_map' := fun _ => rfl }

@[simp] theorem nativeLinearIsometryEquiv_classOf (μ : Measure X) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (f : Raw (𝕜 := 𝕜) μ p) :
    nativeLinearIsometryEquiv μ p (classOf f) = f.property.2.toLp f.val := rfl

theorem classOf_add (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f g : Raw (𝕜 := 𝕜) μ p) : classOf (f + g) = classOf f + classOf g := by
  apply (nativeLinearIsometryEquiv μ p).injective
  rw [map_add]
  exact MemLp.toLp_add f.property.2 g.property.2

theorem classOf_smul (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (c : 𝕜) (f : Raw (𝕜 := 𝕜) μ p) : classOf (c • f) = c • classOf f := by
  apply (nativeLinearIsometryEquiv μ p).injective
  rw [map_smul]
  exact MemLp.toLp_const_smul c f.property.2

theorem classOf_zero (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    classOf (0 : Raw (𝕜 := 𝕜) μ p) = 0 := by
  apply (nativeLinearIsometryEquiv μ p).injective
  rw [map_zero]
  rfl

theorem norm_classOf (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Raw (𝕜 := 𝕜) μ p) : ‖classOf f‖ = (sourceNorm μ p f.val).toReal := by
  rw [← (nativeLinearIsometryEquiv μ p).norm_map (classOf f),
    nativeLinearIsometryEquiv_classOf, Lp.norm_toLp, sourceNorm_bridge μ p Fact.out f]

theorem classOf_eq_iff (μ : Measure X) (p : ℝ≥0∞)
    (f g : Raw (𝕜 := 𝕜) μ p) : classOf f = classOf g ↔ nullRelation μ p f g :=
  Quotient.eq

theorem quotient_construction : Specs.D11.Ch10.QuotientConstruction.quotient_construction := by
  intro X 𝕜 _ _ _ _ μ p _
  exact ⟨quotientNormedAddCommGroup μ p, quotientNormedSpace μ p,
    nativeLinearIsometryEquiv μ p, nativeLinearIsometryEquiv_classOf μ p,
    classOf_add μ p, classOf_smul μ p, classOf_zero μ p, norm_classOf μ p,
    classOf_eq_iff μ p⟩

end D11.Ch10.QuotientConstruction
