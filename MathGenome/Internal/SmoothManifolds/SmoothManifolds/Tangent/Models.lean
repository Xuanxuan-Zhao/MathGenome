import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.Models
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.Partitions
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.HadamardLocal
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.CoordinateCurves
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace SmoothManifolds
open ModelData AtlasData PartitionData TangentData Set Filter
open scoped Topology
universe u v

abbrev smoothGermAlgebra := @TangentData.smoothGermAlgebra
abbrev SmoothGerm := @TangentData.SmoothGerm
abbrev globalSmoothAlgebra := @TangentData.globalSmoothAlgebra
abbrev GlobalSmooth := @TangentData.GlobalSmooth
abbrev germEvaluation := @TangentData.germEvaluation
abbrev globalEvaluation := @TangentData.globalEvaluation
abbrev pointDerivations := @TangentData.pointDerivations
abbrev PointDerivation := @TangentData.PointDerivation
abbrev TangentSpace := @TangentData.TangentSpace
abbrev GlobalPointDerivation := @TangentData.GlobalPointDerivation
abbrev vanishingIdeal := @TangentData.vanishingIdeal
abbrev squareInIdeal := @TangentData.squareInIdeal
abbrev CotangentQuotient := @TangentData.CotangentQuotient
abbrev cotangentClass := @TangentData.cotangentClass
abbrev GermChartExtension := @TangentData.GermChartExtension
abbrev CurveSide := @TangentData.CurveSide
abbrev curveParameterSet := @TangentData.curveParameterSet
abbrev CurveSmoothAt := @TangentData.CurveSmoothAt
abbrev CurveRepresentsDerivation := @TangentData.CurveRepresentsDerivation

variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]

theorem mem_smoothGermAlgebra_iff (S : SmoothManifold n a M) (p : M)
    (g : Germ (𝓝 p) ℝ) :
    g ∈ smoothGermAlgebra S p ↔ ∃ f : M → ℝ,
      ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val f p ∧ g = Germ.ofFun f := by
  constructor
  · intro h
    induction h using Algebra.adjoin_induction with
    | mem g hg => exact hg
    | algebraMap c => exact ⟨fun _ => c, ScalarContDiffAt.const _ _ _ _, rfl⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨f, hf, rfl⟩ := ihx
      obtain ⟨g, hg, rfl⟩ := ihy
      exact ⟨fun z => f z + g z, hf.add hg, rfl⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨f, hf, rfl⟩ := ihx
      obtain ⟨g, hg, rfl⟩ := ihy
      exact ⟨fun z => f z * g z, hf.mul hg, rfl⟩
  · intro h
    exact Algebra.subset_adjoin h

theorem mem_globalSmoothAlgebra_iff (S : SmoothManifold n a M) (f : M → ℝ) :
    f ∈ globalSmoothAlgebra S ↔ ScalarSmooth S.smoothStructure.val f := by
  constructor
  · intro h
    induction h using Algebra.adjoin_induction with
    | mem f hf => exact hf
    | algebraMap c => exact scalarContDiff_const _ _ _
    | add f g hf hg ihf ihg => exact scalarContDiff_add ihf ihg
    | mul f g hf hg ihf ihg => exact scalarContDiff_mul ihf ihg
  · intro h
    exact Algebra.subset_adjoin h

section AugmentedAlgebra
variable {B : Type v} [CommRing B] [Algebra ℝ B]

theorem derivation_kills_constants (ε : B →ₐ[ℝ] ℝ)
    (D : pointDerivations ε) (c : ℝ) : D.val (algebraMap ℝ B c) = 0 := by
  have h1 := D.property (1 : B) 1
  simp only [one_mul, map_one, one_mul] at h1
  have hzero : D.val 1 = 0 := by linarith
  rw [Algebra.algebraMap_eq_smul_one, map_smul, hzero, smul_zero]

theorem derivation_kills_square (ε : B →ₐ[ℝ] ℝ)
    (D : pointDerivations ε) (f : B) (hf : f ∈ vanishingIdeal ε ^ 2) : D.val f = 0 := by
  rw [pow_two] at hf
  refine Submodule.mul_induction_on (R := B) (M := vanishingIdeal ε)
    (N := vanishingIdeal ε) (C := fun x => D.val x = 0) hf ?_ ?_
  · intro x hx y hy
    have hx0 : ε x = 0 := hx
    have hy0 : ε y = 0 := hy
    rw [D.property, hx0, hy0, zero_mul, zero_mul, zero_add]
  · intro x y ihx ihy
    rw [map_add, ihx, ihy, add_zero]

/-- Subtracting the value gives a linear map to the vanishing ideal. -/
def centeredGerm (ε : B →ₐ[ℝ] ℝ) : B →ₗ[ℝ] vanishingIdeal ε where
  toFun f := ⟨f - algebraMap ℝ B (ε f), by
    simp [TangentData.vanishingIdeal, RingHom.mem_ker]⟩
  map_add' f g := by
    apply Subtype.ext
    simp only [map_add, Submodule.coe_add]
    abel
  map_smul' c f := by
    apply Subtype.ext
    simp [Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul]

/-- The class of f-f(p) in m/m². -/
def cotangentDifferential (ε : B →ₐ[ℝ] ℝ) : B →ₗ[ℝ] CotangentQuotient ε :=
  (cotangentClass ε).comp (centeredGerm ε)

/-- Restriction of a derivation descends through m². -/
def derivationToCotangent (ε : B →ₐ[ℝ] ℝ) :
    pointDerivations ε →ₗ[ℝ] Module.Dual ℝ (CotangentQuotient ε) where
  toFun D := (squareInIdeal ε).liftQ
    (D.val.comp ((vanishingIdeal ε).subtype.restrictScalars ℝ))
    (fun f hf => derivation_kills_square ε D f hf)
  map_add' D E := by
    apply Submodule.quot_hom_ext
    intro f
    rfl
  map_smul' c D := by
    apply Submodule.quot_hom_ext
    intro f
    rfl

theorem cotangentDifferential_mul (ε : B →ₐ[ℝ] ℝ) (f g : B) :
    cotangentDifferential ε (f * g) =
      ε f • cotangentDifferential ε g + ε g • cotangentDifferential ε f := by
  change cotangentClass ε (centeredGerm ε (f * g)) =
    ε f • cotangentClass ε (centeredGerm ε g) +
      ε g • cotangentClass ε (centeredGerm ε f)
  rw [← (cotangentClass ε).map_smul (ε f) (centeredGerm ε g),
    ← (cotangentClass ε).map_smul (ε g) (centeredGerm ε f), ← map_add]
  apply (Submodule.Quotient.eq _).mpr
  change (f * g - algebraMap ℝ B (ε (f * g))) -
    (ε f • (g - algebraMap ℝ B (ε g)) +
      ε g • (f - algebraMap ℝ B (ε f))) ∈ vanishingIdeal ε ^ 2
  rw [pow_two]
  convert Ideal.mul_mem_mul (centeredGerm ε f).property (centeredGerm ε g).property using 1
  simp only [map_mul, Algebra.smul_def, centeredGerm, LinearMap.coe_mk,
    AddHom.coe_mk]
  ring

def cotangentToDerivation (ε : B →ₐ[ℝ] ℝ) :
    Module.Dual ℝ (CotangentQuotient ε) →ₗ[ℝ] pointDerivations ε where
  toFun φ := ⟨φ.comp (cotangentDifferential ε), by
    intro f g
    simp only [LinearMap.comp_apply, cotangentDifferential_mul, map_add, map_smul,
      smul_eq_mul]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical duality with m/m², with no finite-dimensionality assumption. -/
def derivationCotangentEquiv (ε : B →ₐ[ℝ] ℝ) :
    pointDerivations ε ≃ₗ[ℝ] Module.Dual ℝ (CotangentQuotient ε) where
  toLinearMap := derivationToCotangent ε
  invFun := cotangentToDerivation ε
  left_inv D := by
    apply Subtype.ext
    ext f
    change D.val (f - algebraMap ℝ B (ε f)) = D.val f
    rw [map_sub, derivation_kills_constants, sub_zero]
  right_inv φ := by
    apply Submodule.quot_hom_ext
    intro f
    change φ (cotangentClass ε (centeredGerm ε f.val)) = φ (cotangentClass ε f)
    congr 2
    apply Subtype.ext
    have hf : ε f.val = 0 := f.property
    simp [centeredGerm, hf]

theorem exists_derivationCotangentEquiv (ε : B →ₐ[ℝ] ℝ) :
    ∃ e : pointDerivations ε ≃ₗ[ℝ] Module.Dual ℝ (CotangentQuotient ε),
      ∀ (D : pointDerivations ε) (f : vanishingIdeal ε),
        e D (cotangentClass ε f) = D.val f :=
  ⟨derivationCotangentEquiv ε, fun _ _ => rfl⟩

end AugmentedAlgebra

/-- Every locally smooth scalar germ has a global smooth representative.
The cutoff is applied to an actual ambient extension in a chart. -/
theorem exists_global_representative (S : SmoothManifold n a M) (p : M)
    (f : M → ℝ) (hf : ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val f p) :
    ∃ g : M → ℝ, ScalarSmooth S.smoothStructure.val g ∧ g =ᶠ[𝓝 p] f := by
  let A := S.smoothStructure.val
  have hA : IsContDiffAtlas (⊤ : ℕ∞) A := S.smoothStructure.property.1
  obtain ⟨e, he, hp⟩ := hA.1 p
  obtain ⟨U, hU, hpU, F, hF, hFf⟩ := (scalarContDiffAt_iff _ A f p).mp hf |>.2 e he hp
  let V := e.source ∩ (fun y => (e y).val) ⁻¹' U
  have hV : IsOpen V :=
    (continuous_subtype_val.comp_continuousOn e.continuousOn).isOpen_inter_preimage
      e.open_source hU
  obtain ⟨χ, hχ, h01, hχ1, hsupp, hcompact⟩ := exists_local_bump S p V hV ⟨hp, hpU⟩
  refine ⟨fun y => χ y * F (e y).val, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ sectionSupport χ
    · have hxV := hsupp hx
      apply ScalarContDiffAt.mul (hχ x)
      exact scalarContDiffAt_of_chart hA he hxV.1
        ⟨U, hU, hxV.2, F, hF, Eventually.of_forall (fun _ => rfl)⟩
    · apply (ScalarContDiffAt.const (⊤ : ℕ∞) A 0 x).congr
      have hevent : ∀ᶠ y in 𝓝 x, y ∉ sectionSupport χ :=
        isClosed_closure.isOpen_compl.mem_nhds hx
      filter_upwards [hevent] with y hy
      have hy0 : χ y = 0 := by
        by_contra h
        exact hy (subset_closure h)
      simp [hy0]
  · filter_upwards [hχ1, hFf] with y hy hfy
    simp [hy, hfy]

def globalToGerm (S : SmoothManifold n a M) (p : M) :
    GlobalSmooth S →ₐ[ℝ] SmoothGerm S p where
  toFun f := ⟨Germ.ofFun f.val,
    (mem_smoothGermAlgebra_iff S p _).mpr
      ⟨f.val, (mem_globalSmoothAlgebra_iff S _).mp f.property p, rfl⟩⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

theorem globalToGerm_surjective (S : SmoothManifold n a M) (p : M) :
    Function.Surjective (globalToGerm S p) := by
  intro f
  obtain ⟨g, hg, hfg⟩ := (mem_smoothGermAlgebra_iff S p f.val).mp f.property
  obtain ⟨h, hh, heq⟩ := exists_global_representative S p g hg
  refine ⟨⟨h, (mem_globalSmoothAlgebra_iff S h).mpr hh⟩, ?_⟩
  apply Subtype.ext
  change Germ.ofFun h = f.val
  rw [hfg]
  exact Germ.coe_eq.mpr heq

/-- Locality is a consequence of Leibniz and a cutoff, not part of the
definition of a global point derivation. -/
theorem global_derivation_locality (S : SmoothManifold n a M) (p : M)
    (D : GlobalPointDerivation S p) (f : GlobalSmooth S)
    (hf : f.val =ᶠ[𝓝 p] (fun _ => 0)) : D.val f = 0 := by
  obtain ⟨U, hUf, hU, hpU⟩ := eventually_nhds_iff.mp hf
  obtain ⟨χ, hχ, h01, hχ1, hsupp, hcompact⟩ := exists_local_bump S p U hU hpU
  let χ' : GlobalSmooth S := ⟨χ, (mem_globalSmoothAlgebra_iff S χ).mpr hχ⟩
  have hprod : f * χ' = 0 := by
    apply Subtype.ext
    funext x
    change f.val x * χ x = 0
    by_cases hx : χ x = 0
    · simp [hx]
    · rw [hUf x (hsupp (subset_closure hx)), zero_mul]
  have h := D.property f χ'
  have hfp : globalEvaluation S p f = 0 := hf.eq_of_nhds
  have hχp : globalEvaluation S p χ' = 1 := hχ1.eq_of_nhds
  rw [hprod, map_zero, hfp, hχp, zero_mul, one_mul, zero_add] at h
  exact h.symm

def restrictGermDerivation (S : SmoothManifold n a M) (p : M) :
    PointDerivation S p →ₗ[ℝ] GlobalPointDerivation S p where
  toFun D := ⟨D.val.comp (globalToGerm S p).toLinearMap, by
    intro f g
    change D.val (globalToGerm S p (f * g)) = _
    rw [map_mul, D.property]
    rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrictGermDerivation_bijective (S : SmoothManifold n a M) (p : M) :
    Function.Bijective (restrictGermDerivation S p) := by
  let q := globalToGerm S p
  have hq := globalToGerm_surjective S p
  constructor
  · intro D E h
    apply Subtype.ext
    ext f
    obtain ⟨g, rfl⟩ := hq f
    exact congrArg (fun d : GlobalPointDerivation S p => d.val g) h
  · intro D
    have hker : LinearMap.ker q.toLinearMap ≤ LinearMap.ker D.val := by
      intro f hf
      apply global_derivation_locality S p D f
      apply Germ.coe_eq.mp
      exact congrArg Subtype.val hf
    let ℓ := q.toLinearMap.liftOfSurjective hq ⟨D.val, hker⟩
    have hℓ (f : GlobalSmooth S) : ℓ (q f) = D.val f :=
      LinearMap.equivOfSurjective_apply hq hker
    have hder : ℓ ∈ pointDerivations (germEvaluation S p) := by
      intro f g
      obtain ⟨f', rfl⟩ := hq f
      obtain ⟨g', rfl⟩ := hq g
      rw [← map_mul, hℓ, hℓ, hℓ]
      exact D.property f' g'
    refine ⟨⟨ℓ, hder⟩, ?_⟩
    apply Subtype.ext
    ext f
    exact hℓ f

noncomputable def germGlobalDerivationEquiv (S : SmoothManifold n a M) (p : M) :
    PointDerivation S p ≃ₗ[ℝ] GlobalPointDerivation S p :=
  LinearEquiv.ofBijective (restrictGermDerivation S p) (restrictGermDerivation_bijective S p)

theorem exists_germGlobalDerivationEquiv (S : SmoothManifold n a M) (p : M) :
    ∃ e : PointDerivation S p ≃ₗ[ℝ] GlobalPointDerivation S p,
      ∀ (D : PointDerivation S p) (f : GlobalSmooth S) (g : SmoothGerm S p),
        Germ.ofFun f.val = g.val → (e D).val f = D.val g := by
  refine ⟨germGlobalDerivationEquiv S p, ?_⟩
  intro D f g h
  change D.val (globalToGerm S p f) = D.val g
  exact congrArg D.val (Subtype.ext h)

theorem germ_eq_constant_zero_dimension (S : SmoothManifold 0 a M) (p : M)
    (g : SmoothGerm S p) :
    g = algebraMap ℝ (SmoothGerm S p) (germEvaluation S p g) := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨f, hf, heq⟩ := (mem_smoothGermAlgebra_iff S p g.val).mp g.property
  apply Subtype.ext
  change g.val = Germ.ofFun (fun _ => g.val.value)
  rw [heq]
  apply Germ.coe_eq.mpr
  filter_upwards [e.open_source.mem_nhds hp] with y hy
  have hyp : y = p := e.injOn hy hp (Subsingleton.elim _ _)
  subst y
  rfl

theorem tangent_zero (S : SmoothManifold 0 a M) (p : M) :
    Subsingleton (PointDerivation S p) := by
  constructor
  intro D E
  apply Subtype.ext
  ext g
  rw [germ_eq_constant_zero_dimension S p g, derivation_kills_constants,
    derivation_kills_constants]

/-- Every smooth germ admits an ambient representative in each chart at p. -/
theorem exists_germChartExtension (S : SmoothManifold n a M) (p : M)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (g : SmoothGerm S p) : ∃ F, GermChartExtension S p e g F := by
  obtain ⟨f, hf, hfg⟩ := (mem_smoothGermAlgebra_iff S p g.val).mp g.property
  obtain ⟨U, hU, hpU, F, hF, hFf⟩ :=
    ((scalarContDiffAt_iff _ _ _ _).mp hf).2 e he hp
  exact ⟨F, ⟨U, hU, hpU, hF⟩, (Germ.coe_eq.mpr hFf).trans hfg.symm⟩

/-- Pulling back an ambient smooth function defines a smooth germ. -/
def germOfChart (S : SmoothManifold n a M) (p : M)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (F : Euclidean n → ℝ)
    (hF : ∃ U, IsOpen U ∧ (e p).val ∈ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) F U) :
    SmoothGerm S p :=
  ⟨Germ.ofFun (fun y => F (e y).val), (mem_smoothGermAlgebra_iff S p _).mpr
    ⟨_, scalarContDiffAt_of_chart S.smoothStructure.property.1 he hp
      (by obtain ⟨U, hU, hpU, hF⟩ := hF
          exact ⟨U, hU, hpU, F, hF, Eventually.of_forall (fun _ => rfl)⟩), rfl⟩⟩

def coordinateGerm (S : SmoothManifold n a M) (p : M)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (i : Fin n) : SmoothGerm S p :=
  germOfChart S p e he hp (fun x => x i)
    ⟨univ, isOpen_univ, mem_univ _, (contDiff_apply ℝ (fun _ : Fin n => ℝ) i).contDiffOn⟩

theorem curveDomain_cases (side : CurveSide) :
    curveParameterSet side = univ ∨ curveParameterSet side = Ici 0 ∨
      curveParameterSet side = Iic 0 := by
  cases side <;> simp [curveParameterSet, TangentData.curveParameterSet]

theorem uniqueDiff_curveDomain (side : CurveSide) :
    UniqueDiffWithinAt ℝ (curveParameterSet side) 0 :=
  uniqueDiffCurveDomain _ (curveDomain_cases side)

/-- A chart derivative gives a unique derivative for every representative of a germ. -/
theorem exists_derivative_on_germ (S : SmoothManifold n a M) (p : M)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (side : CurveSide) (c : ℝ → M) (hc : c 0 = p)
    (hcont : ContinuousWithinAt c (curveParameterSet side) 0)
    (v : Euclidean n)
    (hv : HasDerivWithinAt (fun t => (e (c t)).val) v (curveParameterSet side) 0)
    (g : SmoothGerm S p) :
    ∃ r : ℝ, ∀ f : M → ℝ, Germ.ofFun f = g.val →
      HasDerivWithinAt (f ∘ c) r (curveParameterSet side) 0 := by
  obtain ⟨F, ⟨U, hU, hpU, hF⟩, heq⟩ := exists_germChartExtension S p e he hp g
  refine ⟨fderiv ℝ F (e p).val v, ?_⟩
  intro f hf
  exact scalarDerivativeAlongCurve p e _ (curveDomain_cases side) c hc hcont v hv
    F U hU hpU hF f (Germ.coe_eq.mp (hf.trans heq.symm))

/-- Construct the derivation by differentiating representatives. No locality
assumption on a linear functional is used. -/
theorem exists_curve_derivation_of_chart (S : SmoothManifold n a M) (p : M)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (side : CurveSide) (c : ℝ → M) (hs : CurveSmoothAt S p side c)
    (v : Euclidean n)
    (hv : HasDerivWithinAt (fun t => (e (c t)).val) v (curveParameterSet side) 0) :
    ∃! D : PointDerivation S p, CurveRepresentsDerivation S p side c D := by
  classical
  choose d hd using exists_derivative_on_germ S p e he hp side c hs.1 hs.2.1 v hv
  have hu := uniqueDiff_curveDomain side
  have rep (g : SmoothGerm S p) : ∃ f : M → ℝ, Germ.ofFun f = g.val := by
    obtain ⟨f, _, hf⟩ := (mem_smoothGermAlgebra_iff S p _).mp g.property
    exact ⟨f, hf.symm⟩
  let L : SmoothGerm S p →ₗ[ℝ] ℝ :=
    { toFun := d
      map_add' := by
        intro g h
        obtain ⟨f, hf⟩ := rep g
        obtain ⟨k, hk⟩ := rep h
        have hsum : Germ.ofFun (fun y => f y + k y) = (g + h).val := by
          change Germ.ofFun f + Germ.ofFun k = g.val + h.val
          rw [hf, hk]
        exact UniqueDiffWithinAt.eq_deriv _ hu (hd (g+h) _ hsum) ((hd g f hf).add (hd h k hk))
      map_smul' := by
        intro r g
        obtain ⟨f, hf⟩ := rep g
        have hsmul : Germ.ofFun (fun y => r * f y) = (r • g).val := by
          change r • Germ.ofFun f = r • g.val
          rw [hf]
        exact UniqueDiffWithinAt.eq_deriv _ hu (hd (r • g) _ hsmul) ((hd g f hf).const_mul r) }
  have hder : L ∈ pointDerivations (germEvaluation S p) := by
    intro g h
    obtain ⟨f, hf⟩ := rep g
    obtain ⟨k, hk⟩ := rep h
    have hprod : Germ.ofFun (fun y => f y * k y) = (g*h).val := by
      change Germ.ofFun f * Germ.ofFun k = g.val * h.val
      rw [hf, hk]
    have hfp : f p = germEvaluation S p g := congrArg Germ.value hf
    have hkp : k p = germEvaluation S p h := congrArg Germ.value hk
    have hh := UniqueDiffWithinAt.eq_deriv _ hu (hd (g*h) _ hprod) ((hd g f hf).mul (hd h k hk))
    change d (g*h) = _
    change d (g*h) = d g * k (c 0) + f (c 0) * d h at hh
    rw [hs.1, hfp, hkp] at hh
    change d (g*h) = germEvaluation S p g * d h + germEvaluation S p h * d g
    exact hh.trans (by ring)
  refine ⟨⟨L, hder⟩, ⟨hs, hd⟩, ?_⟩
  intro E hE
  apply Subtype.ext
  ext g
  obtain ⟨f, hf⟩ := rep g
  exact UniqueDiffWithinAt.eq_deriv _ hu (hE.2 g f hf) (hd g f hf)

theorem curve_chart_hasDeriv (S : SmoothManifold n a M) (p : M)
    (side : CurveSide) (c : ℝ → M) (hs : CurveSmoothAt S p side c)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) :
    ∃ v, HasDerivWithinAt (fun t => (e (c t)).val) v (curveParameterSet side) 0 := by
  obtain ⟨U, hU, h0U, F, hF, heq⟩ := hs.2.2 e he hp
  have hd := ((hF.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)).hasDerivAt
  have h0 : 0 ∈ curveParameterSet side := by
    cases side <;> simp [curveParameterSet, TangentData.curveParameterSet]
  exact ⟨_, hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem heq h0⟩

theorem smooth_curve_defines_derivation (S : SmoothManifold n a M) (p : M)
    (side : CurveSide) (c : ℝ → M) (hs : CurveSmoothAt S p side c) :
    ∃! D : PointDerivation S p, CurveRepresentsDerivation S p side c D := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨v, hv⟩ := curve_chart_hasDeriv S p side c hs e he hp
  exact exists_curve_derivation_of_chart S p e he hp side c hs v hv

/-- Hadamard factorization reduces every derivation to its coordinate values. -/
theorem derivation_coordinate_formula (S : SmoothManifold n a M) (p : M)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (D : PointDerivation S p) (g : SmoothGerm S p) (F : Euclidean n → ℝ)
    (hF : GermChartExtension S p e g F) :
    D.val g = ∑ i, D.val (coordinateGerm S p e he hp i) *
      fderiv ℝ F (e p).val (Pi.single i 1) := by
  classical
  obtain ⟨⟨U, hU, hpU, hFU⟩, hFg⟩ := hF
  obtain ⟨V, hV, hpV, hVU, k, hk, hfactor, hvalue⟩ :=
    smooth_hadamard_local n U (e p).val F hU hpU hFU
  let x := coordinateGerm S p e he hp
  let K (i : Fin n) : SmoothGerm S p :=
    germOfChart S p e he hp (k i) ⟨V, hV, hpV, hk i⟩
  have hfactorGerm : g - algebraMap ℝ (SmoothGerm S p) (F (e p).val) =
      ∑ i, (x i - algebraMap ℝ (SmoothGerm S p) ((e p).val i)) * K i := by
    apply Subtype.ext
    change g.val - Germ.ofFun (fun _ : M => F (e p).val) = _
    rw [← hFg]
    have hevent : (fun y => F (e y).val - F (e p).val) =ᶠ[𝓝 p]
        (fun y => ∑ i, ((e y).val i - (e p).val i) * k i (e y).val) := by
      have hcoord : ContinuousAt (fun y => (e y).val) p :=
        continuous_subtype_val.continuousAt.comp (e.continuousAt hp)
      filter_upwards [hcoord.preimage_mem_nhds (hV.mem_nhds hpV)] with y hy
      exact hfactor _ hy
    convert Germ.coe_eq.mpr hevent using 1
    · rfl
    · change (smoothGermAlgebra S p).val (∑ i,
          (x i - algebraMap ℝ (SmoothGerm S p) ((e p).val i)) * K i) = _
      rw [map_sum]
      simp only [map_mul, map_sub]
      change (∑ i, (Germ.coeRingHom (𝓝 p))
        (fun y => ((e y).val i - (e p).val i) * k i (e y).val)) = _
      rw [← map_sum]
      change Germ.ofFun (∑ i, fun y => ((e y).val i - (e p).val i) * k i (e y).val) =
        Germ.ofFun (fun y => ∑ i, ((e y).val i - (e p).val i) * k i (e y).val)
      apply congrArg Germ.ofFun
      funext y
      simp only [Finset.sum_apply]
  have hKvalue (i : Fin n) : germEvaluation S p (K i) =
      fderiv ℝ F (e p).val (Pi.single i 1) := hvalue i
  have hxvalue (i : Fin n) : germEvaluation S p (x i) = (e p).val i := rfl
  have h := congrArg D.val hfactorGerm
  rw [map_sub, derivation_kills_constants, sub_zero, map_sum] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  rw [D.property, map_sub, hxvalue, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self, zero_mul,
    zero_add, map_sub, derivation_kills_constants, sub_zero, hKvalue]
  exact mul_comm _ _

/-- The coordinate velocity of a representing curve is precisely D(x^i). -/
theorem curve_coordinate_values (S : SmoothManifold n a M) (p : M)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (side : CurveSide) (c : ℝ → M) (D : PointDerivation S p)
    (hD : CurveRepresentsDerivation S p side c D) (v : Euclidean n)
    (hv : HasDerivWithinAt (fun t => (e (c t)).val) v (curveParameterSet side) 0)
    (i : Fin n) : D.val (coordinateGerm S p e he hp i) = v i := by
  exact UniqueDiffWithinAt.eq_deriv _ (uniqueDiff_curveDomain side)
    (hD.2 (coordinateGerm S p e he hp i) (fun y => (e y).val i) rfl)
    (hasDerivWithinAt_pi.mp hv i)

/-- A curve with any prescribed coordinate derivative, expressed with CurveSide. -/
theorem exists_curve_with_coordinate_velocity (S : SmoothManifold n a M) (p : M)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (v : Euclidean n) :
    ∃ (side : CurveSide) (c : ℝ → M), CurveSmoothAt S p side c ∧
      HasDerivWithinAt (fun t => (e (c t)).val) v (curveParameterSet side) 0 := by
  obtain ⟨J, hJ, c, hc, hcont, hv, hs⟩ := existsCoordinateCurve S p e he hp v
  rcases hJ with rfl | rfl | rfl
  · exact ⟨.twoSided, c, ⟨hc, hcont, hs⟩, hv⟩
  · exact ⟨.forward, c, ⟨hc, hcont, hs⟩, hv⟩
  · exact ⟨.backward, c, ⟨hc, hcont, hs⟩, hv⟩

/-- All derivations are determined by their values on the coordinates. -/
theorem derivation_ext_coordinates (S : SmoothManifold n a M) (p : M)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (D E : PointDerivation S p)
    (h : ∀ i, D.val (coordinateGerm S p e he hp i) =
      E.val (coordinateGerm S p e he hp i)) : D = E := by
  apply Subtype.ext
  ext g
  obtain ⟨F, hF⟩ := exists_germChartExtension S p e he hp g
  rw [derivation_coordinate_formula S p e he hp D g F hF,
    derivation_coordinate_formula S p e he hp E g F hF]
  simp only [h]

/-- Evaluation on coordinates is an isomorphism onto the shared coordinate space. -/
def coordinateDerivationMap (S : SmoothManifold n a M) (p : M)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) :
    PointDerivation S p →ₗ[ℝ] Euclidean n where
  toFun D i := D.val (coordinateGerm S p e he hp i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinateDerivationMap_bijective (S : SmoothManifold n a M) (p : M)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) :
    Function.Bijective (coordinateDerivationMap S p e he hp) := by
  constructor
  · intro D E h
    exact derivation_ext_coordinates S p e he hp D E (congrFun h)
  · intro v
    obtain ⟨side, c, hs, hv⟩ := exists_curve_with_coordinate_velocity S p e he hp v
    obtain ⟨D, hD, _⟩ := exists_curve_derivation_of_chart S p e he hp side c hs v hv
    exact ⟨D, funext (curve_coordinate_values S p e he hp side c D hD v hv)⟩

noncomputable def coordinateDerivationEquiv (S : SmoothManifold n a M) (p : M)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) :
    PointDerivation S p ≃ₗ[ℝ] Euclidean n :=
  LinearEquiv.ofBijective (coordinateDerivationMap S p e he hp)
    (coordinateDerivationMap_bijective S p e he hp)

theorem coordinate_tangent_model (S : SmoothManifold n a M) (p : M)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) :
    ∃ (coords : Fin n → SmoothGerm S p)
      (b : Module.Basis (Fin n) ℝ (PointDerivation S p))
      (E : PointDerivation S p ≃ₗ[ℝ] Euclidean n),
      (∀ i, (coords i).val = Germ.ofFun (fun y => (e y).val i)) ∧
      (∀ D i, E D i = D.val (coords i)) ∧
      (∀ i, E (b i) = Pi.single i 1) ∧
      ∀ (D : PointDerivation S p) (g : SmoothGerm S p) (F : Euclidean n → ℝ),
        GermChartExtension S p e g F →
        D.val g = ∑ i, D.val (coords i) * fderiv ℝ F (e p).val (Pi.single i 1) := by
  classical
  let E := coordinateDerivationEquiv S p e he hp
  refine ⟨coordinateGerm S p e he hp, (Pi.basisFun ℝ (Fin n)).map E.symm,
    E, fun _ => rfl, fun _ _ => rfl, ?_, ?_⟩
  · intro i
    simp only [Module.Basis.map_apply, E.apply_symm_apply, Pi.basisFun_apply]
  · exact derivation_coordinate_formula S p e he hp

theorem tangent_dimension (S : SmoothManifold n a M) (p : M) :
    FiniteDimensional ℝ (PointDerivation S p) ∧
      Module.finrank ℝ (PointDerivation S p) = n := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let E := coordinateDerivationEquiv S p e he hp
  have hfin : FiniteDimensional ℝ (PointDerivation S p) :=
    FiniteDimensional.of_injective E.toLinearMap E.injective
  exact ⟨hfin, by simpa using E.finrank_eq⟩

theorem every_derivation_is_curve_velocity (S : SmoothManifold n a M) (p : M)
    (D : PointDerivation S p) :
    ∃ (side : CurveSide) (c : ℝ → M), CurveRepresentsDerivation S p side c D := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let v := coordinateDerivationMap S p e he hp D
  obtain ⟨side, c, hs, hv⟩ := exists_curve_with_coordinate_velocity S p e he hp v
  obtain ⟨E, hE, _⟩ := exists_curve_derivation_of_chart S p e he hp side c hs v hv
  have hED : E = D := derivation_ext_coordinates S p e he hp E D
    (curve_coordinate_values S p e he hp side c E hE v hv)
  exact ⟨side, c, hED ▸ hE⟩

theorem curve_velocity_chart_independent (S : SmoothManifold n a M) (p : M)
    (s t : CurveSide) (c d : ℝ → M) (D E : PointDerivation S p)
    (hD : CurveRepresentsDerivation S p s c D)
    (hE : CurveRepresentsDerivation S p t d E)
    (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source)
    (v w : Euclidean n)
    (hv : HasDerivWithinAt (fun z => (e (c z)).val) v (curveParameterSet s) 0)
    (hw : HasDerivWithinAt (fun z => (e (d z)).val) w (curveParameterSet t) 0) :
    v = w ↔ D = E := by
  have hDv := curve_coordinate_values S p e he hp s c D hD v hv
  have hEw := curve_coordinate_values S p e he hp t d E hE w hw
  constructor
  · intro h
    exact derivation_ext_coordinates S p e he hp D E
      (fun i => (hDv i).trans ((congrFun h i).trans (hEw i).symm))
  · intro h
    funext i
    exact (hDv i).symm.trans ((congrArg (fun A : PointDerivation S p =>
      A.val (coordinateGerm S p e he hp i)) h).trans (hEw i))

end SmoothManifolds
