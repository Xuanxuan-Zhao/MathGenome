import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAdjointPolarPaths
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.Star.Unitary

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAdjointPolarPaths

open Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAdjointPolarPaths
open Specs.LieAlgebrasAndRepresentations.PolarRealStructures
open LieAlgebrasAndRepresentations.RealForms
open LieAlgebrasAndRepresentations.PolarRealStructures

open private hermitianCore hermitian_positive from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures

universe u v

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

private abbrev linear (g : LieAut L) : L →ₗ[ℂ] L := g.val.toLinearMap

private theorem aut_ext {g h : LieAut L} (he : ∀ x, g.val x = h.val x) : g = h :=
  Subtype.ext (LinearEquiv.ext he)

@[simp] private theorem compactAction_apply (ω : Conjugation L) (g : LieAut L) (x : L) :
    (compactAction ω g).val x = ω.map (g.val (ω.map x)) := rfl

@[simp] private theorem holomorphicAction_apply (θ g : LieAut L) (x : L) :
    (holomorphicAction θ g).val x = θ.val (g.val (θ.val.symm x)) := rfl

private theorem compactAction_involutive (ω : Conjugation L) :
    Function.Involutive (compactAction ω) := by
  intro g
  apply aut_ext
  intro x
  simp only [compactAction_apply]
  rw [ω.involutive, ω.involutive]

variable [FiniteDimensional ℂ L]

private theorem adjoint_form (ω : Conjugation L) (g : LieAut L) (x y : L) :
    hermitian ω (g.val x) y = hermitian ω x ((adjoint ω g).val y) :=
  adjoint_identity ω (toLieEquiv g) x y

private theorem existsUnique_power (ω : Conjugation L) (hc : IsCompact ω) (g : LieAut L) (t : ℝ) :
    ∃! p, IsAdjointPower ω g t p := by
  obtain ⟨p, hp, hu⟩ := adjoint_product_power ω hc (toLieEquiv g) t
  refine ⟨ofLieEquiv p, hp, fun q hq => ?_⟩
  exact congrArg ofLieEquiv (hu (toLieEquiv q) hq)

private noncomputable def power (ω : Conjugation L) (hc : IsCompact ω) (g : LieAut L) (t : ℝ) :
    LieAut L := Classical.choose (existsUnique_power ω hc g t)

private theorem power_spec (ω : Conjugation L) (hc : IsCompact ω) (g : LieAut L) (t : ℝ) :
    IsAdjointPower ω g t (power ω hc g t) := (Classical.choose_spec (existsUnique_power ω hc g t)).1

private theorem power_unique (ω : Conjugation L) (hc : IsCompact ω) {g : LieAut L} {t : ℝ}
    {p : LieAut L} (hp : IsAdjointPower ω g t p) : p = power ω hc g t :=
  (Classical.choose_spec (existsUnique_power ω hc g t)).2 p hp

private theorem power_zero (ω : Conjugation L) (hc : IsCompact ω) (g : LieAut L) :
    power ω hc g 0 = 1 := by
  symm
  apply power_unique
  intro r x _
  simp

omit [FiniteDimensional ℂ L] in
private theorem product_eq_one_iff (ω : Conjugation L) (g : LieAut L) :
    adjoint ω g * g = 1 ↔ compactAction ω g = g := by
  rw [adjoint, compactAction_inv, inv_mul_eq_one]

private theorem unitary_iff_product_eq_one (ω : Conjugation L) (hc : IsCompact ω) (g : LieAut L) :
    IsUnitary ω g ↔ adjoint ω g * g = 1 := by
  let c := hermitianCore ω hc
  let : NormedAddCommGroup L := c.toNormedAddCommGroup
  let : InnerProductSpace ℂ L := InnerProductSpace.ofCore c.toCore
  constructor
  · intro h
    apply aut_ext
    intro y
    apply ext_inner_left ℂ
    intro x
    change hermitian ω x ((adjoint ω g).val (g.val y)) = hermitian ω x y
    rw [← adjoint_form]
    exact h x y
  · intro h x y
    rw [adjoint_form]
    exact congrArg (hermitian ω x) (congrArg (fun k : LieAut L => k.val y) h)

private theorem power_of_fixed (ω : Conjugation L) (hc : IsCompact ω) {g : LieAut L}
    (hg : compactAction ω g = g) (t : ℝ) : power ω hc g t = 1 := by
  symm
  apply power_unique
  have he := (product_eq_one_iff ω g).2 hg
  intro r x hx
  rw [he] at hx
  change x = (r : ℂ) • x at hx
  by_cases hzero : x = 0
  · simp [hzero]
  have hr : (r : ℂ) = 1 := (smul_left_injective ℂ hzero) (hx.symm.trans (one_smul ℂ x).symm)
  have hr' : r = 1 := Complex.ofReal_injective (by simpa using hr)
  simp [hr']

section Operators

open Polynomial Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

private noncomputable def asRealEnd : (E →L[ℂ] E) →ₐ[ℝ] Module.End ℝ E where
  toFun T := T.toLinearMap.restrictScalars ℝ
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

private theorem finite_real_spectrum (T : E →L[ℂ] E) : (spectrum ℝ T).Finite := by
  have hs : (spectrum ℂ T).Finite := by
    rw [← AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap E).symm T]
    exact Module.End.finite_spectrum _
  refine (hs.preimage Complex.ofReal_injective.injOn).subset ?_
  intro r hr
  change (r : ℂ) ∈ spectrum ℂ T
  rw [spectrum.mem_iff] at hr ⊢
  rw [Algebra.algebraMap_eq_smul_one] at hr ⊢
  exact hr

/-- Evaluating real functional calculus on an eigenvector reduces to scalar evaluation.
A Lagrange polynomial agrees with the function on the finite real spectrum. -/
private theorem cfc_apply_eigenvector (f : ℝ → ℝ) (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (r : ℝ) (x : E) (hx : T x = r • x) :
    (cfc f T) x = f r • x := by
  classical
  by_cases hz : x = 0
  · simp [hz]
  have hr : r ∈ spectrum ℝ T := by
    apply AlgHom.spectrum_apply_subset asRealEnd T
    apply Module.End.HasEigenvalue.mem_spectrum
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (⟨Module.End.mem_eigenspace_iff.mpr hx, hz⟩ : (asRealEnd T).HasEigenvector r x)
  let s := (finite_real_spectrum T).toFinset
  let p := Lagrange.interpolate s id f
  have he (y : ℝ) (hy : y ∈ spectrum ℝ T) : p.eval y = f y :=
    Lagrange.eval_interpolate_at_node f (fun _ _ _ _ heq => heq) (by simpa [s] using hy)
  rw [cfc_congr (fun y hy => (he y hy).symm), cfc_polynomial p T hT]
  change (asRealEnd (aeval T p)) x = f r • x
  rw [← Polynomial.aeval_algHom_apply]
  have hx' : asRealEnd T x = r • x := hx
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul hx', he r hr]

private noncomputable def spectralPower (t : ℝ) (T : E →L[ℂ] E) : E →L[ℂ] E :=
  cfc Real.exp (t • CFC.log T)

private theorem spectralPower_eq_cfc (t : ℝ) (T : E →L[ℂ] E) (hT : IsStrictlyPositive T) :
    spectralPower t T = cfc (fun r : ℝ => r ^ t) T := by
  have hlog : ContinuousOn Real.log (spectrum ℝ T) :=
    Real.continuousOn_log.mono fun r hr => (hT.spectrum_pos hr).ne'
  unfold spectralPower CFC.log
  rw [← cfc_const_mul t Real.log T hlog]
  rw [← cfc_comp' Real.exp (fun r => t * Real.log r) T
    Real.continuous_exp.continuousOn (continuousOn_const.mul hlog) hT.isSelfAdjoint]
  apply cfc_congr
  intro r hr
  change Real.exp (t * Real.log r) = r ^ t
  rw [Real.rpow_def_of_pos (hT.spectrum_pos hr), mul_comm]

private theorem continuous_spectralPower {X : Type*} [TopologicalSpace X]
    {t : X → ℝ} {T : X → (E →L[ℂ] E)} (ht : Continuous t) (hT : Continuous T)
    (h : ∀ x, IsStrictlyPositive (T x)) :
    Continuous (fun x => spectralPower (t x) (T x)) := by
  refine Continuous.cfc_of_mem_nhdsSet (s := Set.univ) Real.exp (by simp) ?_ ?_
    Real.continuous_exp.continuousOn
  · exact ht.smul (CFC.continuousOn_log.comp_continuous hT
      (fun x => ⟨(h x).isSelfAdjoint, (h x).isUnit⟩))
  · intro x
    exact (IsSelfAdjoint.all (t x)).smul (cfc_predicate Real.log (T x))

private theorem unitary_polar (G : E →L[ℂ] E) (hG : IsUnit G) :
    star (G * spectralPower (-(1 : ℝ) / 2) (star G * G)) *
      (G * spectralPower (-(1 : ℝ) / 2) (star G * G)) = 1 := by
  let P := star G * G
  have hP : IsStrictlyPositive P := ⟨star_mul_self_nonneg G, hG.star.mul hG⟩
  let f (r : ℝ) := r ^ (-(1 : ℝ) / 2)
  have hf : ContinuousOn f (spectrum ℝ P) :=
    fun r hr => (Real.continuousAt_rpow_const _ _ (Or.inl (hP.spectrum_pos hr).ne')).continuousWithinAt
  change star (G * spectralPower _ P) * (G * spectralPower _ P) = 1
  rw [spectralPower_eq_cfc _ P hP, star_mul]
  change (star (cfc f P) * star G) * (G * cfc f P) = 1
  have hs : IsSelfAdjoint (cfc f P) := cfc_predicate f P
  rw [hs.star_eq]
  calc
    (cfc f P * star G) * (G * cfc f P) = cfc f P * P * cfc f P := by simp [P, mul_assoc]
    _ = cfc (fun r => (f r * r) * f r) P := by
      nth_rw 2 [← cfc_id ℝ P hP.isSelfAdjoint]
      rw [← cfc_mul f id P hf continuousOn_id,
        ← cfc_mul (fun r => f r * id r) f P (hf.mul continuousOn_id) hf]
      rfl
    _ = 1 := by
      rw [← cfc_const_one ℝ P]
      apply cfc_congr
      intro r hr
      have hp := hP.spectrum_pos (𝕜 := ℝ) hr
      calc
        (f r * r) * f r = (r ^ (-(1 : ℝ) / 2 + -(1 : ℝ) / 2)) * r := by
          rw [Real.rpow_add hp]
          simp only [f]
          ac_rfl
        _ = 1 := by
          rw [show -(1 : ℝ) / 2 + -(1 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one,
            inv_mul_cancel₀ hp.ne']

end Operators

private def compactMulAut (ω : Conjugation L) : MulAut (LieAut L) where
  toFun := compactAction ω
  invFun := compactAction ω
  left_inv := compactAction_involutive ω
  right_inv := compactAction_involutive ω
  map_mul' := compactAction_mul ω

private theorem equivariant_power (ω : Conjugation L) (hc : IsCompact ω)
    (φ : MulAut (LieAut L)) (k : L → L) (hk : Function.Bijective k)
    (hscalar : ∀ (r : ℝ) (x : L), k ((r : ℂ) • x) = (r : ℂ) • k x)
    (haction : ∀ a x, (φ a).val (k x) = k (a.val x))
    (hadj : ∀ a, φ (adjoint ω a) = adjoint ω (φ a))
    (g : LieAut L) (t : ℝ) :
    φ (power ω hc g t) = power ω hc (φ g) t := by
  apply power_unique
  intro r z hz
  obtain ⟨x, rfl⟩ := hk.surjective z
  have hP : φ (adjoint ω g * g) = adjoint ω (φ g) * φ g := by rw [map_mul, hadj]
  have hx : (adjoint ω g * g).val x = (r : ℂ) • x := by
    apply hk.injective
    rw [← haction, hP, hz, hscalar]
  rw [haction, power_spec ω hc g t r x hx, hscalar]

private theorem compact_equivariant_power (ω : Conjugation L) (hc : IsCompact ω)
    (g : LieAut L) (t : ℝ) :
    compactAction ω (power ω hc g t) = power ω hc (compactAction ω g) t := by
  apply equivariant_power ω hc (compactMulAut ω) ω.map ω.involutive.bijective
  · intro r x
    rw [ω.antilinear]
    exact congrArg (fun z : ℂ => z • ω.map x) (Complex.conj_ofReal r)
  · intro a x
    change ω.map (a.val (ω.map (ω.map x))) = ω.map (a.val x)
    rw [ω.involutive]
  · intro a
    change compactAction ω (compactAction ω a⁻¹) = compactAction ω (compactAction ω a)⁻¹
    rw [← compactAction_inv ω a, compactAction_involutive ω]

private theorem holomorphic_equivariant_power (ω : Conjugation L) (hc : IsCompact ω)
    (θ : LieAut L) (hθ : ∀ x, θ.val (ω.map x) = ω.map (θ.val x))
    (g : LieAut L) (t : ℝ) :
    holomorphicAction θ (power ω hc g t) = power ω hc (holomorphicAction θ g) t := by
  have hfix : compactAction ω θ = θ := by
    apply aut_ext
    intro x
    rw [compactAction_apply, hθ, ω.involutive]
  apply equivariant_power ω hc (MulAut.conj θ) θ.val θ.val.bijective
  · exact fun r x => map_smul θ.val (r : ℂ) x
  · intro a x
    change θ.val (a.val (θ.val.symm (θ.val x))) = θ.val (a.val x)
    rw [θ.val.symm_apply_apply]
  · intro a
    change θ * adjoint ω a * θ⁻¹ = compactAction ω (θ * a * θ⁻¹)⁻¹
    rw [mul_inv_rev, mul_inv_rev, inv_inv, compactAction_mul, compactAction_mul,
      compactAction_inv ω θ, hfix, adjoint, mul_assoc]

/-- The Lie algebra equipped with the metric from its compact conjugation. -/
private def HermitianSpace (ω : Conjugation L) (_ : IsCompact ω) := L

private noncomputable instance (ω : Conjugation L) (hc : IsCompact ω) :
    NormedAddCommGroup (HermitianSpace ω hc) :=
  (hermitianCore ω hc).toNormedAddCommGroup

private noncomputable instance (ω : Conjugation L) (hc : IsCompact ω) :
    InnerProductSpace ℂ (HermitianSpace ω hc) :=
  InnerProductSpace.ofCore (hermitianCore ω hc).toCore

private instance (ω : Conjugation L) (hc : IsCompact ω) :
    FiniteDimensional ℂ (HermitianSpace ω hc) :=
  ‹FiniteDimensional ℂ L›

section LieOperators

open Topology

variable (ω : Conjugation L) (hc : IsCompact ω)
local notation "V" => HermitianSpace ω hc
local notation "Op" => (V →L[ℂ] V)

private noncomputable def asOperator : LieAut L →* Op where
  toFun g := LinearMap.toContinuousLinearMap (show V →ₗ[ℂ] V from linear (L := L) g)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] private theorem asOperator_apply (g : LieAut L) (x : V) :
    asOperator ω hc g x = g.val x := rfl

private theorem asOperator_injective : Function.Injective (asOperator ω hc) := by
  intro g h he
  exact aut_ext fun x => congrArg (fun f : Op => f x) he

private theorem asOperator_isEmbedding (b : Module.Basis ι ℂ L) :
    letI := matrixTopology b
    IsEmbedding (asOperator ω hc) := by
  let := matrixTopology b
  let bv : Module.Basis ι ℂ V := b
  let e : Matrix ι ι ℂ ≃L[ℂ] Op :=
    ((LinearMap.toMatrix bv bv).symm.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv
  have hmat : IsEmbedding (matrixOf b) :=
    ⟨⟨rfl⟩, fun g h he => aut_ext fun x =>
      LinearMap.congr_fun ((LinearMap.toMatrix b b).injective he) x⟩
  have he : IsEmbedding (e ∘ matrixOf b) := e.toHomeomorph.isEmbedding.comp hmat
  have eq : e ∘ matrixOf b = asOperator ω hc := by
    funext g
    change LinearMap.toContinuousLinearMap
      ((LinearMap.toMatrix bv bv).symm (LinearMap.toMatrix bv bv
        (show V →ₗ[ℂ] V from linear (L := L) g))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  rwa [eq] at he

private theorem asOperator_isUnit (g : LieAut L) :
    IsUnit (asOperator ω hc g) :=
  ContinuousLinearMap.isUnit_iff_bijective.mpr g.val.bijective

private theorem asOperator_adjoint (g : LieAut L) :
    asOperator ω hc (adjoint ω g) = star (asOperator ω hc g) := by
  change asOperator ω hc (adjoint ω g) = (asOperator ω hc g).adjoint
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (adjoint_form ω g x y).symm

private theorem asOperator_power (g : LieAut L) (t : ℝ) :
    asOperator ω hc (power ω hc g t) =
      spectralPower t (star (asOperator ω hc g) * asOperator ω hc g) := by
  let P := adjoint ω g * g
  let G := asOperator ω hc g
  have hG := asOperator_isUnit ω hc g
  have hP : asOperator ω hc P = star G * G := by rw [map_mul, asOperator_adjoint]
  have hpos : IsStrictlyPositive (star G * G) := ⟨star_mul_self_nonneg G, hG.star.mul hG⟩
  have hsym : (show V →ₗ[ℂ] V from linear (L := L) P).IsSymmetric := by
    intro x y
    change inner ℂ (asOperator ω hc P x) y = inner ℂ x (asOperator ω hc P y)
    rw [hP, ← ContinuousLinearMap.adjoint_inner_right (star G * G)]
    change inner ℂ x (star (star G * G) y) = _
    rw [star_mul, star_star]
  let b := (hsym.eigenvectorBasis rfl).toBasis
  suffices h : (asOperator ω hc (power ω hc g t)).toLinearMap =
      (spectralPower t (star G * G)).toLinearMap by
    exact ContinuousLinearMap.ext fun x => LinearMap.congr_fun h x
  apply b.ext
  intro i
  let r := hsym.eigenvalues rfl i
  have hx : P.val (b i) = (r : ℂ) • b i := hsym.apply_eigenvectorBasis rfl i
  have hx' : (star G * G) (b i) = r • b i := by rw [← hP, asOperator_apply]; exact hx
  change (power ω hc g t).val (b i) = spectralPower t (star G * G) (b i)
  rw [power_spec ω hc g t r (b i) hx, spectralPower_eq_cfc _ _ hpos,
    cfc_apply_eigenvector _ _ hpos.isSelfAdjoint _ _ hx']
  rfl

private theorem continuous_power (b : Module.Basis ι ℂ L) :
    letI := matrixTopology b
    Continuous (fun tg : ℝ × LieAut L => power ω hc tg.2 tg.1) := by
  let := matrixTopology b
  have he := asOperator_isEmbedding ω hc b
  apply he.isInducing.continuous_iff.mpr
  simp only [Function.comp_def, asOperator_power]
  have hG : Continuous (fun tg : ℝ × LieAut L => asOperator ω hc tg.2) :=
    he.continuous.comp continuous_snd
  exact continuous_spectralPower continuous_fst (hG.star.mul hG) (fun tg =>
    ⟨star_mul_self_nonneg _, (asOperator_isUnit ω hc tg.2).star.mul
      (asOperator_isUnit ω hc tg.2)⟩)

private theorem polar_endpoint (g : LieAut L) :
    compactAction ω (g * power ω hc g (-(1 : ℝ) / 2)) = g * power ω hc g (-(1 : ℝ) / 2) := by
  let k := g * power ω hc g (-(1 : ℝ) / 2)
  show compactAction ω k = k
  apply (product_eq_one_iff ω k).mp
  apply asOperator_injective ω hc
  rw [map_one, map_mul, asOperator_adjoint]
  have hk : asOperator ω hc k = asOperator ω hc g *
      spectralPower (-(1 : ℝ) / 2) (star (asOperator ω hc g) * asOperator ω hc g) := by
    dsimp only [k]
    rw [map_mul, asOperator_power]
  rw [hk]
  exact unitary_polar _ (asOperator_isUnit ω hc g)

private def bracketInMetric (x y : V) : V :=
  (show L from ⁅(show L from x), (show L from y)⁆)

include hc in
private theorem compact_unitary_automorphisms (b : Module.Basis ι ℂ L) :
    letI := matrixTopology b
    IsCompact {g : LieAut L | compactAction ω g = g} := by
  let := matrixTopology b
  let preserves : Set Op :=
    {T | ∀ x y : V, T (bracketInMetric ω hc x y) =
      bracketInMetric ω hc (T x) (T y)}
  let K : Set Op := (unitary Op : Set Op) ∩ preserves
  let : LieRing (Module.End ℂ L) := LieRing.ofAssociativeRing
  let ad : V →L[ℂ] Op := LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      (show V →ₗ[ℂ] V →ₗ[ℂ] V from (LieAlgebra.ad ℂ L).toLinearMap))
  have hbracket : Continuous (fun z : V × V => bracketInMetric ω hc z.1 z.2) :=
    (ad.continuous.comp continuous_fst).clm_apply continuous_snd
  have hpres : IsClosed preserves := by
    have heq (x y : V) :
        IsClosed {T : Op | T (bracketInMetric ω hc x y) = bracketInMetric ω hc (T x) (T y)} :=
      isClosed_eq (continuous_id.clm_apply continuous_const)
        (hbracket.comp ((continuous_id.clm_apply (continuous_const (y := x))).prodMk
          (continuous_id.clm_apply (continuous_const (y := y)))))
    simpa only [preserves, Set.ofPred_forall] using isClosed_iInter (fun x => isClosed_iInter (heq x))
  have hK : IsCompact K := by
    have hball := isCompact_closedBall (0 : Op) 1
    apply hball.of_isClosed_subset (isClosed_unitary.inter hpres)
    intro T hT
    obtain hnt | hnt := subsingleton_or_nontrivial Op
    · simpa only [Subsingleton.elim T (0 : Op), Metric.mem_closedBall, dist_self] using (zero_le_one : (0 : ℝ) ≤ 1)
    · have := hnt
      simpa only [Metric.mem_closedBall, dist_zero_right, CStarRing.norm_of_mem_unitary hT.1]
        using (le_rfl : (1 : ℝ) ≤ 1)
  have hsub : K ⊆ Set.range (asOperator ω hc) := by
    intro T hT
    have hunit : IsUnit T := Unitary.isUnit_coe (U := ⟨T, hT.1⟩)
    have hbij := ContinuousLinearMap.isUnit_iff_bijective.mp hunit
    let hlinear : L →ₗ[ℂ] L := T.toLinearMap
    have hLie (x y : L) : hlinear ⁅x, y⁆ = ⁅hlinear x, hlinear y⁆ := by
      exact hT.2 x y
    let f : L →ₗ⁅ℂ⁆ L := { hlinear with map_lie' := hLie _ _ }
    have hfbij : Function.Bijective f := by
      change Function.Bijective (fun x : V => T x)
      exact hbij
    refine ⟨ofLieEquiv (LieEquiv.ofBijective f hfbij), ?_⟩
    ext x
    rfl
  have hpre : (asOperator ω hc) ⁻¹' K = {g : LieAut L | compactAction ω g = g} := by
    ext g
    have hbr : asOperator ω hc g ∈ preserves := g.property
    simp only [K, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, hbr, and_true]
    change asOperator ω hc g ∈ unitary Op ↔ _
    rw [(asOperator_isUnit ω hc g).mem_unitary_iff_star_mul_self,
      ← asOperator_adjoint ω hc, ← map_mul, ← map_one (asOperator ω hc),
      (asOperator_injective ω hc).eq_iff, product_eq_one_iff]
  rw [← hpre]
  exact (asOperator_isEmbedding ω hc b).isInducing.isCompact_preimage' hK hsub

private theorem power_mem_component (b : Module.Basis ι ℂ L) (g : LieAut L) (t : ℝ) :
    letI := matrixTopology b
    power ω hc g t ∈ connectedComponent (1 : LieAut L) := by
  let := matrixTopology b
  let path (s : ℝ) := power ω hc g s
  have hparam : Continuous (fun s : ℝ => (s, g)) :=
    continuous_id.prodMk (continuous_const (y := g))
  have hp := (continuous_power ω hc b).comp' hparam
  change Continuous path at hp
  have hone : (1 : LieAut L) ∈ Set.range path := ⟨0, power_zero ω hc g⟩
  exact (isPreconnected_range hp).subset_connectedComponent hone ⟨t, rfl⟩

private theorem continuous_polar (b : Module.Basis ι ℂ L) :
    letI := matrixTopology b
    Continuous (fun sg : ℝ × LieAut L => sg.2 * power ω hc sg.2 (-sg.1 / 2)) := by
  let := matrixTopology b
  have he := asOperator_isEmbedding ω hc b
  apply he.isInducing.continuous_iff.mpr
  have hG : Continuous (fun sg : ℝ × LieAut L => asOperator ω hc sg.2) :=
    he.continuous.comp continuous_snd
  have hparam : Continuous (fun sg : ℝ × LieAut L => (-sg.1 / 2, sg.2)) :=
    (continuous_fst.neg.div_const 2).prodMk continuous_snd
  have hP : Continuous (fun sg : ℝ × LieAut L => asOperator ω hc (power ω hc sg.2 (-sg.1 / 2))) :=
    he.continuous.comp ((continuous_power ω hc b).comp hparam)
  simp only [Function.comp_def, map_mul]
  exact continuous_mul.comp₂ hG hP

end LieOperators

open Topology

/-- The polar strong deformation retraction in the topology of the given matrix coordinates. -/
theorem polarDeformation : polarDeformationStatement.{u, v} := by
  intro L _ _ _ ι _ _ b _ ω hc θ _ hθ A hclosed hcomponent hωA hθA
  let := matrixTopology b
  let F (s : ℝ) (g : LieAut L) := g * power ω hc g (-(s : ℝ) / 2)
  have hmem (s : ℝ) (g : A) : F s g.val ∈ A :=
    A.mul_mem g.property (hcomponent (power_mem_component ω hc b g.val (-s / 2)))
  have htime : Continuous (fun s : unitInterval => s.val) := continuous_subtype_val
  have hgroup : Continuous (fun g : A => g.val) := continuous_subtype_val
  have hparam : Continuous (fun sg : unitInterval × A => (sg.1.val, sg.2.val)) :=
    (htime.comp' continuous_fst).prodMk (hgroup.comp' continuous_snd)
  have hF := (continuous_polar ω hc b).comp' hparam
  change Continuous (fun sg : unitInterval × A => F sg.1 sg.2.val) at hF
  let H : C(unitInterval × A, A) :=
    ⟨fun sg => ⟨F sg.1 sg.2.val, hmem sg.1 sg.2⟩, hF.subtype_mk _⟩
  have hstationary (s : unitInterval) (g : A) (hg : g ∈ compactFixed ω A) :
      H (s, g) = g := by
    apply Subtype.ext
    change F s g.val = g.val
    dsimp only [F]
    rw [power_of_fixed ω hc hg, mul_one]
  have hend (g : A) : H (1, g) ∈ compactFixed ω A := polar_endpoint ω hc g.val
  have hHerm (x y : L) : star (hermitian ω y x) = hermitian ω x y :=
    (hermitianCore ω hc).conj_inner_symm x y
  have hpos (x : L) (hx : x ≠ 0) : 0 < (hermitian ω x x).re :=
    hermitian_positive ω hc hx
  refine ⟨H, hHerm, hpos, adjoint_form ω, ?_, ?_, hend, hstationary, ?_, ?_, ?_, ?_, ?_⟩
  · intro s g
    refine ⟨power ω hc g.val (-(s : ℝ) / 2), ⟨power_spec ω hc g.val (-(s : ℝ) / 2), rfl⟩, ?_⟩
    exact fun p hp => power_unique ω hc hp.1
  · intro g
    apply Subtype.ext
    change g.val * power ω hc g.val (-(0 : ℝ) / 2) = g.val
    simp [power_zero]
  · intro s g k hk
    change F s k.val = compactAction ω (F s g.val)
    dsimp only [F]
    rw [hk, compactAction_mul, compact_equivariant_power]
  · intro s g k hk
    change F s k.val = holomorphicAction θ (F s g.val)
    dsimp only [F]
    rw [hk, ← holomorphic_equivariant_power ω hc θ hθ]
    exact ((MulAut.conj θ).map_mul _ _).symm
  · apply Set.Subset.antisymm
    · rintro _ ⟨g, rfl⟩
      exact hend g
    · exact fun g hg => ⟨g, hstationary 1 g hg⟩
  · intro g
    exact ((unitary_iff_product_eq_one ω hc g.val).trans (product_eq_one_iff ω g.val)).symm
  · apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    have heq : ((↑) : A → LieAut L) '' (compactFixed ω A : Set A) =
        {g : LieAut L | compactAction ω g = g} ∩ (A : Set (LieAut L)) := by
      ext g
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨ha, a.property⟩
      · rintro ⟨hfix, hg⟩
        exact ⟨⟨g, hg⟩, hfix, rfl⟩
    rw [heq]
    exact (compact_unitary_automorphisms ω hc b).inter_right hclosed

end LinearAlgebraicGroups.Arithmetic.ExceptionalAdjointPolarPaths
