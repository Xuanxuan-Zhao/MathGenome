import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanConjugacy
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.DominantFundamentalDomain
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Reconstruction
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightClassification
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.SpecialFunctions.Complex.Log

noncomputable section

namespace LieAlgebrasAndRepresentations.AutomorphismDecomposition

open Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient (Normalized)
open Specs.LieAlgebrasAndRepresentations.RealRootSpace
open Specs.LieAlgebrasAndRepresentations.CartanConjugacy (exponentialOperator)
open Module
open scoped Classical

universe u
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable {H : LieSubalgebra ℂ L} {φ : Direction H}

theorem existsPinning : existsPinningType.{u} := by
  intro L _ _ _ hss
  obtain ⟨H, hH⟩ := exists_maximal_toral L hss
  obtain ⟨x, hx⟩ := RegularSemisimple.rootRegular_nonempty H hH.1
  let ψ : ℂ →ₗ[ℝ] ℝ := Complex.reLm
  let ev : Module.Dual ℂ H →ₗ[ℂ] ℂ := Module.Dual.eval ℂ H x
  letI : Finite (rootSet H) := (rootSet_finite H hH.1).to_subtype
  have hn (α : rootSet H) : ∃ q : ℂ, (ψ (q * ev α.val)) ≠ 0 := by
    refine ⟨(ev α.val)⁻¹, ?_⟩
    have hz : ev α.val ≠ 0 := hx _ α.property
    rw [inv_mul_cancel₀ hz]
    simp [ψ]
  let w (α : rootSet H) : ℂ →ₗ[ℝ] ℝ := ψ.comp
    ((LinearMap.mulRight ℂ (ev α.val)).restrictScalars ℝ)
  obtain ⟨q, hq⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists w hn
  let φ : Direction H := ψ.comp ((Module.Dual.eval ℂ H (q • x)).restrictScalars ℝ)
  have hφ : Regular H φ := by
    intro α hα
    simpa [φ, w, ev, smul_eq_mul] using hq ⟨α, hα⟩
  have ht (i : simple H φ) := exists_root_triple hss H hH i.val i.property.1.1
  choose e f he hf hne hnf hef _ _ using ht
  exact ⟨H, hH, φ, hφ, e, f, fun i => ⟨he i, hf i, hne i, hnf i, hef i⟩⟩



private def toAut (g : L ≃ₗ⁅ℂ⁆ L) : Aut L :=
  ⟨g.toLinearEquiv, g.map_lie⟩

private def asLieEquiv (g : Aut L) : L ≃ₗ⁅ℂ⁆ L :=
  { g.val with map_lie' := fun {x y} => g.property x y }

open private direction_vector simple_equiv vector_regular reflection_extension
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence
open private cartan_lattice_comparison_of_realization
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightData

private theorem basedRootSystem (d : Realization H) (hφ : Regular H φ) :
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    ∃ (v : E H) (_ : RootRegular (realRoots H) v)
      (b : Basis (simple H φ) ℝ (E H)) (c : Basis (simple H φ) ℂ H)
      (a : Basis (simple H φ) ℂ (Dual ℂ H)),
      IsSimpleBasis (realRoots H) v b ∧
      (∀ i, d.j (b i) = i.val ∧ c i = killingCoroot H i.val ∧ a i = i.val) ∧
      (∀ i j, j.val (killingCoroot H i.val) = (cartanMatrix b i j : ℂ)) := by
  letI : Fact (Realization H) := ⟨d⟩
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  obtain ⟨v, hv⟩ := direction_vector d φ
  have hvr := vector_regular d φ hv hφ
  obtain ⟨s, hs⟩ := simple_equiv d φ hv
  obtain ⟨b, c, a, hb, hc, hp, _⟩ :=
    cartan_lattice_comparison_of_realization d v hvr s
  refine ⟨v, hvr, b, c, a, hb, ?_, ?_⟩
  · intro i
    obtain ⟨hbi, hai, hci, _, _⟩ := hc i
    change a i = d.j (s i : E H) at hai
    change c i = killingCoroot H (d.j (s i : E H)) at hci
    rw [hs i] at hai hci
    exact ⟨by rw [hbi, hs], hci, hai⟩
  · intro i j
    have hpair := hp (s j : E H) i
    change d.j (s j : E H) (killingCoroot H (d.j (s i : E H))) = _ at hpair
    rw [hs i, hs j, ← (hc j).1, inner_coroot] at hpair
    exact hpair

theorem diagramEncoding : diagramEncodingType.{u} := by
  intro L _ _ _ hss H hH φ hφ
  classical
  let d := RealRootSpace.realization_of_maximalToral hss H hH
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  obtain ⟨v, hv, b, _, _, hb, hroots, hpair⟩ := basedRootSystem d hφ
  refine ⟨d, v, hv, b, hb, fun i => (hroots i).1, ?_⟩
  intro D p
  change (∀ i j, (p j).val (killingCoroot H (p i).val) = j.val (killingCoroot H i.val)) ↔
    (∀ i j, D.edges (p i) (p j) = D.edges i j) ∧
    (∀ i j, D.arrow (p i) (p j) ↔ D.arrow i j)
  have hR := d.root_system
  constructor
  · intro hp
    have hmat (i j) : cartanMatrix b (p i) (p j) = cartanMatrix b i j :=
      Complex.ofReal_injective ((hpair (p i) (p j)).symm.trans ((hp i j).trans (hpair i j)))
    constructor
    · intro i j
      by_cases hij : i = j
      · subst j
        simp [D, dynkinDiagram]
      · apply Nat.cast_injective (R := ℝ)
        change ((dynkinDiagram b).edges (p i) (p j) : ℝ) = _
        rw [dynkin_edges_cast hR hv hb (p.injective.ne hij), dynkin_edges_cast hR hv hb hij, hmat, hmat]
    · intro i j
      by_cases hij : i = j
      · subst j
        simp [D, dynkinDiagram]
      · change (dynkinDiagram b).arrow (p i) (p j) ↔ (dynkinDiagram b).arrow i j
        rw [dynkin_arrow_iff_cartan_lt hR hv hb (p.injective.ne hij),
          dynkin_arrow_iff_cartan_lt hR hv hb hij, hmat, hmat]
  · rintro ⟨hedge, harrow⟩
    let c := b.reindex p.symm
    have hc (i) : c i = b (p i) := by simp [c, Basis.reindex_apply]
    have hDf : (c : simple H φ → E H) = b ∘ p := funext hc
    have hcs : IsSimpleBasis (realRoots H) v c := by
      change Set.range (c : simple H φ → E H) = _
      rw [hDf, p.surjective.range_comp]
      exact hb
    have hcart := cartan_eq_of_diagram_eq hR hR hv hv hb hcs
      (fun i j => by
        rw [hDf]
        by_cases hij : i = j
        · subst j
          simp [dynkinDiagram]
        · simpa [D, dynkinDiagram, cartanMatrix, hij, p.injective.ne hij] using (hedge i j).symm)
      (fun i j => by
        rw [hDf]
        simpa [D, dynkinDiagram, p.injective.eq_iff] using (harrow i j).symm)
    intro i j
    rw [hpair, hpair]
    apply congrArg Complex.ofReal
    have h := congrFun (congrFun hcart i) j
    change cartanMatrix b i j = cartanMatrix c i j at h
    simpa only [hDf, cartanMatrix, Function.comp_apply] using h.symm

/-- The reconstruction isomorphism for the chosen simple generators, with
the simple-root and coroot bases and the off-diagonal signs used below. -/
private theorem serrePresentation (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hφ : Regular H φ) (e f : simple H φ → L) (hn : Normalized H φ e f) :
    ∃ (c : Basis (simple H φ) ℂ H) (a : Basis (simple H φ) ℂ (Dual ℂ H))
      (A : Matrix (simple H φ) (simple H φ) ℤ),
      (∀ i, c i = killingCoroot H i.val ∧ a i = i.val) ∧
      (∀ i j, (A i j : ℂ) = j.val (c i)) ∧
      (∀ i j, i ≠ j → A i j ≤ 0) ∧
      ∃ T : Serre.Algebra A ≃ₗ⁅ℂ⁆ L,
        (∀ i, T (Serre.e A i) = e i) ∧ (∀ i, T (Serre.f A i) = f i) ∧
        (∀ i, T (Serre.h A i) = (c i : L)) := by
  classical
  let d := RealRootSpace.realization_of_maximalToral hss H hH
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  obtain ⟨v, hv, b, c, a, hb, hroots, hpair⟩ := basedRootSystem d hφ
  obtain ⟨A, T, hA, hT, _⟩ := serre_reconstruction hss H hH φ hφ e f hn
  have hca (i : simple H φ) := (hroots i).2
  have hA' (i j) : (A i j : ℂ) = j.val (c i) := by
    rw [(hca i).1, hA]
  have hoff (i j) (hij : i ≠ j) : A i j ≤ 0 := by
    have hreal : (A i j : ℝ) = cartanMatrix b i j := by
      apply Complex.ofReal_injective
      rw [Complex.ofReal_intCast, ← hA i j, hpair i j]
    exact Int.cast_nonpos.mp (hreal.trans_le
      ((cartan_offDiagonal (realRoots H) d.root_system v hv b hb).2 i j hij))
  exact ⟨c, a, A, hca, hA', hoff, T, fun i => (hT i).1, fun i => (hT i).2.1,
    fun i => (hT i).2.2.trans (congrArg Subtype.val (hca i).1.symm)⟩

private theorem serrePermutation_relations {ι : Type*} [DecidableEq ι]
    {A : Matrix ι ι ℤ} (ha : ∀ i j, i ≠ j → A i j ≤ 0)
    (p : Equiv.Perm ι) (hp : ∀ i j, A (p i) (p j) = A i j) :
    Serre.RelationsHold A (Serre.e A ∘ p) (Serre.f A ∘ p) (Serre.h A ∘ p) := by
  obtain ⟨hh, he, hf, hef, hs, ht⟩ := Serre.relations_spec A ha
  refine ⟨fun i j => hh (p i) (p j), ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa only [Function.comp_apply, hp] using he (p i) (p j)
  · intro i j
    simpa only [Function.comp_apply, hp] using hf (p i) (p j)
  · intro i j
    simpa only [Function.comp_apply, p.injective.eq_iff] using hef (p i) (p j)
  · intro i j hij
    simpa only [Function.comp_apply, hp] using hs (p i) (p j) (p.injective.ne hij)
  · intro i j hij
    simpa only [Function.comp_apply, hp] using ht (p i) (p j) (p.injective.ne hij)

private def serrePermutation {ι : Type*} [DecidableEq ι]
    {A : Matrix ι ι ℤ} (ha : ∀ i j, i ≠ j → A i j ≤ 0)
    (p : Equiv.Perm ι) (hp : ∀ i j, A (p i) (p j) = A i j) :
    Serre.Algebra A ≃ₗ⁅ℂ⁆ Serre.Algebra A := by
  let f (q : Equiv.Perm ι) (hq : ∀ i j, A (q i) (q j) = A i j) :=
    Serre.lift A ha _ _ _ (serrePermutation_relations ha q hq)
  have hp' (i j) : A (p.symm i) (p.symm j) = A i j := by
    simpa using (hp (p.symm i) (p.symm j)).symm
  let g := f p.symm hp'
  have hk : ∀ (q r : Equiv.Perm ι) (hq : ∀ i j, A (q i) (q j) = A i j)
      (hr : ∀ i j, A (r i) (r j) = A i j), (∀ i, q (r i) = i) →
      (f q hq).comp (f r hr) = LieHom.id := by
    intro q r hq hr hqr
    apply Serre.hom_ext A <;> intro i <;>
      simp [f, Function.comp_apply, hqr]
  have hl : Function.LeftInverse g (f p hp) :=
    fun x => LieHom.congr_fun (hk p.symm p hp' hp p.symm_apply_apply) x
  have hr : Function.RightInverse g (f p hp) :=
    fun x => LieHom.congr_fun (hk p p.symm hp hp' p.apply_symm_apply) x
  exact { f p hp with invFun := g, left_inv := hl, right_inv := hr }

@[simp] private theorem serrePermutation_e {ι : Type*} [DecidableEq ι]
    {A : Matrix ι ι ℤ} (ha : ∀ i j, i ≠ j → A i j ≤ 0)
    (p : Equiv.Perm ι) (hp : ∀ i j, A (p i) (p j) = A i j) (i : ι) :
    serrePermutation ha p hp (Serre.e A i) = Serre.e A (p i) :=
  Serre.lift_e A ha _ _ _ (serrePermutation_relations ha p hp) i

@[simp] private theorem serrePermutation_f {ι : Type*} [DecidableEq ι]
    {A : Matrix ι ι ℤ} (ha : ∀ i j, i ≠ j → A i j ≤ 0)
    (p : Equiv.Perm ι) (hp : ∀ i j, A (p i) (p j) = A i j) (i : ι) :
    serrePermutation ha p hp (Serre.f A i) = Serre.f A (p i) :=
  Serre.lift_f A ha _ _ _ (serrePermutation_relations ha p hp) i

@[simp] private theorem serrePermutation_h {ι : Type*} [DecidableEq ι]
    {A : Matrix ι ι ℤ} (ha : ∀ i j, i ≠ j → A i j ≤ 0)
    (p : Equiv.Perm ι) (hp : ∀ i j, A (p i) (p j) = A i j) (i : ι) :
    serrePermutation ha p hp (Serre.h A i) = Serre.h A (p i) :=
  Serre.lift_h A ha _ _ _ (serrePermutation_relations ha p hp) i

@[simp] private theorem asLieEquiv_apply (g : Aut L) (x : L) :
    asLieEquiv g x = g.val x := rfl

private theorem existsDiagramSection (e f : simple H φ → L)
    (c : Basis (simple H φ) ℂ H) (A : Matrix (simple H φ) (simple H φ) ℤ)
    (hc : ∀ i, c i = killingCoroot H i.val)
    (hA : ∀ i j, (A i j : ℂ) = j.val (c i))
    (ha : ∀ i j, i ≠ j → A i j ≤ 0)
    (T : Serre.Algebra A ≃ₗ⁅ℂ⁆ L)
    (he : ∀ i, T (Serre.e A i) = e i) (hf : ∀ i, T (Serre.f A i) = f i)
    (hh : ∀ i, T (Serre.h A i) = (c i : L)) :
    ∃ s : diagramAutomorphisms H φ →* Aut L,
      ∀ p i, (s p).val (e i) = e (p.val i) ∧ (s p).val (f i) = f (p.val i) ∧
        (s p).val (c i : L) = (c (p.val i) : L) := by
  classical
  have hpres (p : diagramAutomorphisms H φ) (i j) : A (p.val i) (p.val j) = A i j := by
    apply Int.cast_injective (α := ℂ)
    rw [hA, hA, hc, hc]
    exact p.property i j
  let g (p : diagramAutomorphisms H φ) :=
    (T.symm.trans (serrePermutation ha p.val (hpres p))).trans T
  have hg (p : diagramAutomorphisms H φ) (i) :
      g p (e i) = e (p.val i) ∧ g p (f i) = f (p.val i) ∧
        g p (c i : L) = (c (p.val i) : L) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← he i, ← he (p.val i)]
      simp [g]
    · rw [← hf i, ← hf (p.val i)]
      simp [g]
    · rw [← hh i, ← hh (p.val i)]
      simp [g]
  have extAut {x y : Aut L} (he' : ∀ i, x.val (e i) = y.val (e i))
      (hf' : ∀ i, x.val (f i) = y.val (f i)) (hh' : ∀ i, x.val (c i : L) = y.val (c i : L)) :
      x = y := by
    have hk : (asLieEquiv x).toLieHom.comp T.toLieHom =
        (asLieEquiv y).toLieHom.comp T.toLieHom := by
      apply Serre.hom_ext A
      · intro i; simpa only [LieHom.comp_apply, LieEquiv.coe_coe, asLieEquiv_apply, he] using he' i
      · intro i; simpa only [LieHom.comp_apply, LieEquiv.coe_coe, asLieEquiv_apply, hf] using hf' i
      · intro i; simpa only [LieHom.comp_apply, LieEquiv.coe_coe, asLieEquiv_apply, hh] using hh' i
    apply Subtype.ext
    ext y'
    obtain ⟨x', rfl⟩ := T.surjective y'
    exact LieHom.congr_fun hk x'
  refine ⟨{ toFun := fun p => toAut (g p), map_one' := ?_, map_mul' := ?_ }, hg⟩
  · apply extAut
    · exact fun i => (hg 1 i).1
    · exact fun i => (hg 1 i).2.1
    · exact fun i => (hg 1 i).2.2
  · intro p q
    apply extAut
    · intro i
      change g (p * q) (e i) = g p (g q (e i))
      rw [(hg (p * q) i).1, (hg q i).1, (hg p (q.val i)).1]
      rfl
    · intro i
      change g (p * q) (f i) = g p (g q (f i))
      rw [(hg (p * q) i).2.1, (hg q i).2.1, (hg p (q.val i)).2.1]
      rfl
    · intro i
      change g (p * q) (c i : L) = g p (g q (c i : L))
      rw [(hg (p * q) i).2.2, (hg q i).2.2, (hg p (q.val i)).2.2]
      rfl



section Exponentials

open NormedSpace
open Specs.LieAlgebrasAndRepresentations.RegularSemisimple (algebraNorm)
open RegularSemisimple (expAdEquiv)

private theorem exp_intertwine {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (D : X →L[ℂ] X) (E : Y →L[ℂ] Y) (f : X →L[ℂ] Y)
    (hf : ∀ x, f (D x) = E (f x)) (x : X) :
    f (exp D x) = exp E (f x) := by
  have hp (n : ℕ) (y : X) : f ((D ^ n) y) = (E ^ n) (f y) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [pow_succ', mul_apply_eq_comp, hf, ih]
  have hD := (exp_series_hasSum_exp' (𝕂 := ℂ) D).mapL
    (f.comp (ContinuousLinearMap.apply ℂ X x))
  have hE := (exp_series_hasSum_exp' (𝕂 := ℂ) E).mapL
    (ContinuousLinearMap.apply ℂ Y (f x))
  have hterm (n : ℕ) :
      f.comp (ContinuousLinearMap.apply ℂ X x) ((n.factorial⁻¹ : ℂ) • D ^ n) =
      ContinuousLinearMap.apply ℂ Y (f x) ((n.factorial⁻¹ : ℂ) • E ^ n) := by
    simp only [ContinuousLinearMap.comp_apply, map_smul, ContinuousLinearMap.apply_apply, hp]
  rw [funext hterm] at hD
  exact hD.unique hE

private theorem exponential_eigenvector (h x : L) (lam : ℂ)
    (hx : ⁅h, x⁆ = lam • x) :
    expAdEquiv h x = Complex.exp lam • x := by
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L := NormedSpace.induced ℂ L
    (Fin (finrank ℂ L) → ℂ) (finBasis ℂ L).equivFun
  let D := LinearMap.toContinuousLinearMap (LieAlgebra.ad ℂ L h)
  let E : ℂ →L[ℂ] ℂ := algebraMap ℂ _ lam
  let j : ℂ →L[ℂ] L := LinearMap.toContinuousLinearMap ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight x)
  have hj (t : ℂ) : j (E t) = D (j t) := by
    change (lam * t) • x = ⁅h, t • x⁆
    rw [lie_smul, hx, smul_smul, mul_comm]
  have ht := exp_intertwine E D j hj 1
  have hj1 : j 1 = x := by change (1 : ℂ) • x = x; simp
  rw [hj1] at ht
  change exp D x = _
  rw [← ht, ← algebraMap_exp_comm (𝕂 := ℂ) (𝔸 := ℂ →L[ℂ] ℂ) lam,
    ← Complex.exp_eq_exp_ℂ]
  change ((Complex.exp lam) * 1) • x = _
  rw [mul_one]

private theorem expAd_conjugate (g : L ≃ₗ⁅ℂ⁆ L) (h x : L) :
    g (expAdEquiv h x) = expAdEquiv (g h) (g x) := by
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L := NormedSpace.induced ℂ L
    (Fin (finrank ℂ L) → ℂ) (finBasis ℂ L).equivFun
  exact exp_intertwine (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℂ L h))
    (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℂ L (g h)))
    (LinearMap.toContinuousLinearMap g.toLinearMap) (g.map_lie h) x

theorem innerGenerated : innerGeneratedType.{u} := by
  intro L _ _ _
  let i : Aut L →* (L ≃ₗ[ℂ] L) := (lieAutomorphisms L).subtype
  let S : Set (Aut L) := {g | ∃ x : L, g.val.toLinearMap = exponentialOperator x}
  let T : Set (L ≃ₗ[ℂ] L) := {g | ∃ x : L, g.toLinearMap = exponentialOperator x}
  have h : i '' S = T := by
    ext g
    constructor
    · rintro ⟨a, ⟨x, hx⟩, rfl⟩
      exact ⟨x, hx⟩
    · rintro ⟨x, hx⟩
      refine ⟨toAut (expAdEquiv x), ⟨x, rfl⟩, ?_⟩
      ext y
      exact (LinearMap.congr_fun hx y).symm
  change (Subgroup.closure T).comap i = Subgroup.closure S
  rw [← h, ← MonoidHom.map_closure, Subgroup.comap_map_eq_self_of_injective
    (lieAutomorphisms L).subtype_injective]

private theorem inner_normal : (inner L).Normal := by
  constructor
  intro s hs g
  let k : (L ≃ₗ[ℂ] L) →* (L ≃ₗ[ℂ] L) :=
    (MulAut.conj g.val).toMonoidHom
  have hk : Specs.LieAlgebrasAndRepresentations.CartanConjugacy.innerAutomorphisms_value L ≤
      (Specs.LieAlgebrasAndRepresentations.CartanConjugacy.innerAutomorphisms_value L).comap k := by
    apply (Subgroup.closure_le _).mpr
    rintro a ⟨x, hx⟩
    apply Subgroup.subset_closure
    refine ⟨g.val x, ?_⟩
    ext y
    change g.val (a (g.val.symm y)) = expAdEquiv (g.val x) y
    rw [show a (g.val.symm y) = expAdEquiv x (g.val.symm y) from
      LinearMap.congr_fun hx _]
    simpa only [asLieEquiv_apply, LinearEquiv.apply_symm_apply] using
      expAd_conjugate (asLieEquiv g) x (g.val.symm y)
  exact hk hs

private theorem expAd_nilpotent (x : L) (hx : IsNilpotent (LieAlgebra.ad ℂ L x)) :
    (expAdEquiv x).toLinearMap =
      (letI := Module.restrictScalars ℚ ℂ L
       IsNilpotent.exp (LieAlgebra.ad ℂ L x)) := by
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L := NormedSpace.induced ℂ L
    (Fin (finrank ℂ L) → ℂ) (finBasis ℂ L).equivFun
  letI : Algebra ℚ (L →L[ℂ] L) := RestrictScalars.algebra ℚ ℂ _
  letI : NormedAlgebra ℚ (L →L[ℂ] L) := NormedAlgebra.restrictScalars ℚ ℂ _
  letI := Module.restrictScalars ℚ ℂ L
  letI := IsScalarTower.restrictScalars ℚ ℂ L
  let D := LinearMap.toContinuousLinearMap (LieAlgebra.ad ℂ L x)
  obtain ⟨k, hk⟩ := hx
  have hk' : D ^ k = 0 := by
    change (Module.End.toContinuousLinearMap L (LieAlgebra.ad ℂ L x)) ^ k = 0
    rw [← map_pow, hk, map_zero]
  have he : exp D = IsNilpotent.exp D := by
    rw [IsNilpotent.exp_eq_sum hk', NormedSpace.exp_eq_tsum_rat]
    apply tsum_eq_sum
    intro n hn
    rw [pow_eq_zero_of_le (by simpa only [Finset.mem_range, not_lt] using hn) hk', smul_zero]
  change (exp D).toLinearMap = _
  rw [he, IsNilpotent.exp_eq_sum hk, IsNilpotent.exp_eq_sum hk']
  ext y
  simp only [ContinuousLinearMap.coe_coe, sum_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  change ((n.factorial⁻¹ : ℚ) • ((Module.End.toContinuousLinearMap L
    (LieAlgebra.ad ℂ L x)) ^ n)) y = _
  rw [← map_pow]
  rfl

private theorem reflection_inner (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {α : Dual ℂ H} (hα : α ∈ rootSet H) :
    ∃ n : L ≃ₗ⁅ℂ⁆ L, CartanConjugacy.IsInner n ∧ H.map n.toLieHom = H ∧
      ∀ β : Dual ℂ H,
        (rootSpace H β).map n.toLinearMap = rootSpace H (RootStrings.rootReflection H α β) := by
  obtain ⟨e, f, he, hf, _, _, hef, _, _⟩ := exists_root_triple hss H hH α hα
  obtain ⟨heN, hfN, n, hn, hcart, hroot⟩ :=
    RootStrings.reflection_lift hss H hH α hα e f he hf hef
  have hfN' : IsNilpotent (LieAlgebra.ad ℂ L (-f)) := by simpa using hfN.neg
  have hn' : n = ((expAdEquiv e).trans (expAdEquiv (-f))).trans (expAdEquiv e) := by
    apply LieEquiv.ext
    intro x
    change n.toLinearMap x = _
    rw [hn]
    change _ = (expAdEquiv e).toLinearMap
      ((expAdEquiv (-f)).toLinearMap ((expAdEquiv e).toLinearMap x))
    rw [expAd_nilpotent e heN, expAd_nilpotent (-f) hfN']
    simp only [RootStrings.reflectionLiftLinear,
      Specs.LieAlgebrasAndRepresentations.RootStrings.reflectionLiftLinear_value, map_neg,
      Module.End.mul_apply]
  have hsub : H.map n.toLieHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    change n (⟨x, hx⟩ : H) ∈ H
    rw [hcart]
    exact H.sub_mem hx (H.smul_mem _ (killingCoroot H α).property)
  have hmap : H.map n.toLieHom = H := by
    apply LieSubalgebra.toSubmodule_injective
    apply Submodule.eq_of_le_of_finrank_le hsub
    exact (n.lieSubalgebraMap H).toLinearEquiv.finrank_eq.le
  refine ⟨n, ?_, hmap, hroot⟩
  rw [hn']
  exact CartanConjugacy.inner_trans
    (CartanConjugacy.inner_trans (CartanConjugacy.inner_exp e) (CartanConjugacy.inner_exp (-f)))
    (CartanConjugacy.inner_exp e)

end Exponentials


section Chambers

private def rootTransport (g : L ≃ₗ⁅ℂ⁆ L) (hg : H.map g.toLieHom = H) :
    Dual ℂ H ≃ₗ[ℂ] Dual ℂ H :=
  (g.ofSubalgebras H H hg).toLinearEquiv.symm.dualMap

private theorem rootTransport_apply (g : L ≃ₗ⁅ℂ⁆ L) (hg : H.map g.toLieHom = H)
    (α : Dual ℂ H) (h : H) :
    rootTransport g hg α ((g.ofSubalgebras H H hg).toLinearEquiv h) = α h := by
  change α ((g.ofSubalgebras H H hg).toLinearEquiv.symm
    ((g.ofSubalgebras H H hg).toLinearEquiv h)) = _
  rw [LinearEquiv.symm_apply_apply]

private theorem rootSpace_map_transport (g : L ≃ₗ⁅ℂ⁆ L) (hg : H.map g.toLieHom = H)
    (α : Dual ℂ H) :
    (rootSpace H α).map g.toLinearMap = rootSpace H (rootTransport g hg α) := by
  let k := (g.ofSubalgebras H H hg).toLinearEquiv
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (mem_rootSpace H _ _).mpr
    intro h
    obtain ⟨z, rfl⟩ := k.surjective h
    change ⁅g (z : L), g x⁆ = rootTransport g hg α (k z) • g x
    rw [rootTransport_apply, ← g.map_lie, (mem_rootSpace H _ _).mp hx, map_smul]
  · intro hy
    refine ⟨g.symm y, (mem_rootSpace H _ _).mpr ?_, g.apply_symm_apply y⟩
    intro h
    apply g.injective
    change g ⁅(h : L), g.symm y⁆ = g (α h • g.symm y)
    rw [g.map_lie, g.apply_symm_apply, map_smul, g.apply_symm_apply]
    have ht := (mem_rootSpace H _ _).mp hy (k h)
    change ⁅g (h : L), y⁆ = rootTransport g hg α ((g.ofSubalgebras H H hg).toLinearEquiv h) • y at ht
    rwa [rootTransport_apply] at ht

private theorem rootTransport_mem (g : L ≃ₗ⁅ℂ⁆ L) (hg : H.map g.toLieHom = H)
    (α : Dual ℂ H) : rootTransport g hg α ∈ rootSet H ↔ α ∈ rootSet H := by
  change (_ ≠ 0 ∧ rootSpace H _ ≠ ⊥) ↔ (α ≠ 0 ∧ rootSpace H α ≠ ⊥)
  rw [← rootSpace_map_transport]
  change (_ ≠ 0 ∧ (rootSpace H α).map g.toLinearEquiv.toLinearMap ≠ ⊥) ↔ _
  exact and_congr ((rootTransport g hg).map_ne_zero_iff)
    (Submodule.map_ne_bot_iff (e := g.toLinearEquiv))

private theorem rootTransport_trans (g k : L ≃ₗ⁅ℂ⁆ L)
    (hg : H.map g.toLieHom = H) (hk : H.map k.toLieHom = H)
    (h : H.map (g.trans k).toLieHom = H) (α : Dual ℂ H) :
    rootTransport (g.trans k) h α = rootTransport k hk (rootTransport g hg α) := by
  ext x
  obtain ⟨z, rfl⟩ := (k.ofSubalgebras H H hk).toLinearEquiv.surjective x
  obtain ⟨y, rfl⟩ := (g.ofSubalgebras H H hg).toLinearEquiv.surjective z
  have he (z : H) :
      ((g.trans k).ofSubalgebras H H h).toLinearEquiv z =
        (k.ofSubalgebras H H hk).toLinearEquiv ((g.ofSubalgebras H H hg).toLinearEquiv z) :=
    Subtype.ext rfl
  conv_lhs => rw [← he, rootTransport_apply]
  rw [rootTransport_apply, rootTransport_apply]

private theorem rootSpace_eq_weight {α β : Dual ℂ H} (hα : α ∈ rootSet H)
    (h : rootSpace H α = rootSpace H β) : α = β := by
  obtain ⟨x, hx, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hα.2
  have hy := (mem_rootSpace H β x).mp (h ▸ hx)
  ext z
  exact (smul_left_injective ℂ hn) (((mem_rootSpace H α x).mp hx z).symm.trans (hy z))

private theorem reflection_rootTransport (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    {α : Dual ℂ H} (hα : α ∈ rootSet H) :
    ∃ (n : L ≃ₗ⁅ℂ⁆ L) (hn : H.map n.toLieHom = H), CartanConjugacy.IsInner n ∧
      ∀ β ∈ rootSet H, rootTransport n hn β = RootStrings.rootReflection H α β := by
  obtain ⟨n, hi, hn, hr⟩ := reflection_inner hss hH hα
  exact ⟨n, hn, hi, fun β hb => rootSpace_eq_weight ((rootTransport_mem n hn β).2 hb)
    ((rootSpace_map_transport n hn β).symm.trans (hr β))⟩

private theorem weyl_rootTransport (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (d : Realization H) :
    letI := d.normedAddCommGroup
    letI := d.innerProductSpace
    ∀ {v : E H}, RootRegular (realRoots H) v → ∀ w : rootWeylGroup (realRoots H),
    ∃ (n : L ≃ₗ⁅ℂ⁆ L) (hn : H.map n.toLieHom = H), CartanConjugacy.IsInner n ∧
      ∀ x ∈ realRoots H, rootTransport n hn (d.j x) = d.j (w.val x) := by
  letI : Fact (Realization H) := ⟨d⟩
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  intro v hv w
  have hj (x : E H) (hx : x ∈ realRoots H) : d.j x ∈ rootSet H := by
    obtain ⟨α, hα, rfl⟩ := hx
    rw [d.extension_root α hα]
    exact hα
  obtain ⟨l, hl⟩ := exists_weylWord d.root_system hv w
  rw [← hl]
  clear w hl
  induction l with
  | nil =>
    refine ⟨LieEquiv.refl, CartanConjugacy.map_refl H, CartanConjugacy.inner_one, ?_⟩
    intro x _
    ext z
    rfl
  | cons a l ih =>
    obtain ⟨q, hq, hqi, hqj⟩ := ih
    obtain ⟨n, hn, hi, hr⟩ := reflection_rootTransport hss hH (hj a a.property.1.1)
    have he : H.map (q.trans n).toLieHom = H := by
      rw [CartanConjugacy.map_trans, hq, hn]
    refine ⟨q.trans n, he, CartanConjugacy.inner_trans hqi hi, ?_⟩
    intro x hx
    have hx' : weylWordProduct l x ∈ realRoots H :=
      (rootWeylGroup_mem_iff d.root_system.toRootAxioms (weylWordProduct_mem l) _).1 hx
    rw [rootTransport_trans q n hq hn, hqj x hx, hr _ (hj _ hx'),
      weylWordProduct_cons]
    exact (reflection_extension d a.property _).symm

open Specs.LieAlgebrasAndRepresentations.SerreRelations (positive)

private theorem correctPositiveRoots (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hφ : Regular H φ) (g : L ≃ₗ⁅ℂ⁆ L) (hg : H.map g.toLieHom = H) :
    ∃ (n : L ≃ₗ⁅ℂ⁆ L) (hn : H.map (g.trans n).toLieHom = H), CartanConjugacy.IsInner n ∧
      ∀ α : Dual ℂ H, α ∈ positive H φ ↔ rootTransport (g.trans n) hn α ∈ positive H φ := by
  let d := RealRootSpace.realization_of_maximalToral hss H hH
  letI : Fact (Realization H) := ⟨d⟩
  letI := d.normedAddCommGroup
  letI := d.innerProductSpace
  let t := rootTransport g hg
  let φ' : Direction H := φ.comp (t.symm.toLinearMap.restrictScalars ℝ)
  have hφ' : Regular H φ' := by
    intro α ha
    exact hφ _ ((rootTransport_mem g hg _).mp (by simpa [t] using ha))
  obtain ⟨v, hv⟩ := direction_vector d φ
  obtain ⟨v', hv'⟩ := direction_vector d φ'
  have hr := vector_regular d φ hv hφ
  have hr' := vector_regular d φ' hv' hφ'
  obtain ⟨w, hw⟩ := exists_weyl_into_closedSimpleChamber d.root_system v v'
  have hreg := rootWeylGroup_regular d.root_system.toRootAxioms w hr'
  have hw' : w.val v' ∈ simpleChamber (realRoots H) v :=
    fun a ha => lt_of_le_of_ne (hw a ha) (Ne.symm (hreg a ha.1.1))
  have hsign (x : E H) (hx : x ∈ realRoots H) :
      0 < inner ℝ (w.val v') x ↔ 0 < inner ℝ v x := by
    constructor
    · intro hp
      rcases positive_or_neg_positive d.root_system.toRootAxioms hr hx with h | h
      · exact h.2
      · have hn := simpleChamber_pairing_positive d.root_system.toRootAxioms hw' h
        rw [inner_neg_right] at hn
        exact False.elim (not_lt_of_ge (neg_pos.mp hn).le hp)
    · intro hp
      exact simpleChamber_pairing_positive d.root_system.toRootAxioms hw' ⟨hx, hp⟩
  obtain ⟨n, hn, hi, hj⟩ := weyl_rootTransport hss hH d hr w
  have hgn : H.map (g.trans n).toLieHom = H := by
    rw [CartanConjugacy.map_trans, hg, hn]
  refine ⟨n, hgn, hi, fun α => ?_⟩
  have hmem := rootTransport_mem (g.trans n) hgn α
  by_cases ha : α ∈ rootSet H
  · let x := rootRestriction H (t α)
    have hx : x ∈ realRoots H := ⟨t α, (rootTransport_mem g hg α).2 ha, rfl⟩
    have htx : d.j x = t α := d.extension_root _ ((rootTransport_mem g hg α).2 ha)
    have hwx := (rootWeylGroup_mem_iff d.root_system.toRootAxioms w.property _).1 hx
    have ht : rootTransport (g.trans n) hgn α = d.j (w.val x) := by
      rw [rootTransport_trans g n hg hn, ← show d.j x = rootTransport g hg α from htx, hj x hx]
    have hdir : φ' (d.j x) = φ α := by
      rw [htx]
      change φ (t.symm (t α)) = _
      simp
    change (α ∈ rootSet H ∧ 0 < φ α) ↔
      (rootTransport (g.trans n) hgn α ∈ rootSet H ∧ 0 < φ (rootTransport (g.trans n) hgn α))
    rw [hmem, and_iff_right ha, and_iff_right ha, ht, hv, ← hsign _ hwx,
      rootWeylGroup_inner w.property, ← hv', hdir]
  · exact iff_of_false (fun h => ha h.1) (fun h => ha (hmem.mp h.1))

end Chambers

section Generation

open Specs.LieAlgebrasAndRepresentations.SerreRelations (positive)

private theorem cartan_map (C : LieSubalgebra ℂ L)
    (hC : Specs.LieAlgebrasAndRepresentations.CartanEqualsToral.IsCartan_value C)
    (g : L ≃ₗ⁅ℂ⁆ L) :
    Specs.LieAlgebrasAndRepresentations.CartanEqualsToral.IsCartan_value (C.map g.toLieHom) := by
  letI : LieRing.IsNilpotent C := hC.1
  refine ⟨(g.lieSubalgebraMap C).surjective.lieAlgebra_isNilpotent, ?_⟩
  apply le_antisymm _ (LieSubalgebra.le_normalizer _)
  intro x hx
  have hy : g.symm x ∈ C.normalizer := by
    rw [LieSubalgebra.mem_normalizer_iff] at hx ⊢
    intro y hy
    have h := hx (g y) ⟨y, hy, rfl⟩
    rw [← g.apply_symm_apply x, ← g.map_lie] at h
    obtain ⟨z, hz, he⟩ := h
    exact (g.injective he) ▸ hz
  rw [hC.2] at hy
  exact ⟨g.symm x, hy, g.apply_symm_apply x⟩

private theorem coroot_transport (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (g : L ≃ₗ⁅ℂ⁆ L) (hg : H.map g.toLieHom = H) (α : Dual ℂ H) :
    (g.ofSubalgebras H H hg) (killingCoroot H α) = killingCoroot H (rootTransport g hg α) := by
  let k := g.ofSubalgebras H H hg
  have ht : k (tAlpha H α) = tAlpha H (rootTransport g hg α) := by
    apply tAlpha_unique hss H hH
    intro x
    obtain ⟨y, rfl⟩ := k.toLinearEquiv.surjective x
    change _root_.killingForm ℂ L (g (tAlpha H α : L)) (g (y : L)) = _
    rw [rootTransport_apply]
    exact (LieAlgebra.killingForm_of_equiv_apply g _ _).trans (tAlpha_pairing hss H hH α y)
  have hB : rootForm H (rootTransport g hg α) (rootTransport g hg α) = rootForm H α α := by
    rw [rootForm_apply, ← ht, rootForm_apply]
    exact LieAlgebra.killingForm_of_equiv_apply g _ _
  simp only [killingCoroot_eq, hB, map_smul, ← ht]
  rfl

private def simplePermutation (g : L ≃ₗ⁅ℂ⁆ L) (hg : H.map g.toLieHom = H)
    (hp : ∀ α : Dual ℂ H, α ∈ positive H φ ↔ rootTransport g hg α ∈ positive H φ) :
    Equiv.Perm (simple H φ) :=
  (rootTransport g hg).toEquiv.subtypeEquiv (by
    intro α
    refine and_congr (hp α) ?_
    constructor
    · intro h β hb γ hc he
      let t := rootTransport g hg
      obtain ⟨β', rfl⟩ := t.surjective β
      obtain ⟨γ', rfl⟩ := t.surjective γ
      exact h β' ((hp β').mpr hb) γ' ((hp γ').mpr hc) (t.injective (he.trans (map_add t _ _).symm))
    · intro h β hb γ hc he
      have ht : rootTransport g hg α = rootTransport g hg (β + γ) := congrArg _ he
      rw [map_add] at ht
      exact h _ ((hp β).mp hb) _ ((hp γ).mp hc) ht)

private theorem generators_ext (e f : simple H φ → L) (c : Basis (simple H φ) ℂ H)
    (A : Matrix (simple H φ) (simple H φ) ℤ)
    (T : Serre.Algebra A ≃ₗ⁅ℂ⁆ L)
    (he : ∀ i, T (Serre.e A i) = e i) (hf : ∀ i, T (Serre.f A i) = f i)
    (hh : ∀ i, T (Serre.h A i) = (c i : L))
    {x y : L ≃ₗ⁅ℂ⁆ L} (he' : ∀ i, x (e i) = y (e i))
    (hf' : ∀ i, x (f i) = y (f i)) (hh' : ∀ i, x (c i : L) = y (c i : L)) :
    x = y := by
  have hk : x.toLieHom.comp T.toLieHom = y.toLieHom.comp T.toLieHom := by
    apply Serre.hom_ext A
    · simpa only [LieHom.comp_apply, LieEquiv.coe_coe, asLieEquiv_apply, he] using he'
    · simpa only [LieHom.comp_apply, LieEquiv.coe_coe, asLieEquiv_apply, hf] using hf'
    · simpa only [LieHom.comp_apply, LieEquiv.coe_coe, asLieEquiv_apply, hh] using hh'
  apply LieEquiv.ext
  intro z
  obtain ⟨z, rfl⟩ := T.surjective z
  exact LieHom.congr_fun hk z

private theorem factorization_surjective (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hφ : Regular H φ) (e f : simple H φ → L) (hn : Normalized H φ e f)
    (c : Basis (simple H φ) ℂ H) (a : Basis (simple H φ) ℂ (Dual ℂ H))
    (hc : ∀ i, c i = killingCoroot H i.val) (ha : ∀ i, a i = i.val)
    (A : Matrix (simple H φ) (simple H φ) ℤ)
    (T : Serre.Algebra A ≃ₗ⁅ℂ⁆ L)
    (he : ∀ i, T (Serre.e A i) = e i) (hf : ∀ i, T (Serre.f A i) = f i)
    (hh : ∀ i, T (Serre.h A i) = (c i : L))
    (s : diagramAutomorphisms H φ →* Aut L)
    (hs : ∀ p i, (s p).val (e i) = e (p.val i) ∧ (s p).val (f i) = f (p.val i) ∧
      (s p).val (c i : L) = (c (p.val i) : L)) :
    Function.Surjective (fun q : inner L × diagramAutomorphisms H φ => q.1.val * s q.2) := by
  classical
  intro G
  let g := asLieEquiv G
  have hcart := (isCartan_iff_maximal_toral hss H).mpr hH
  obtain ⟨k, hk, hkH⟩ := cartan_conjugacy L hss (H.map g.toLieHom) H (cartan_map H hcart g) hcart
  have hk' : CartanConjugacy.IsInner k := hk
  have hm : H.map (g.trans k).toLieHom = H := (CartanConjugacy.map_trans _ _ _).trans hkH
  obtain ⟨n, hnH, hni, hp⟩ := correctPositiveRoots hss hH hφ (g.trans k) hm
  let v := (g.trans k).trans n
  let q := simplePermutation v hnH hp
  have hq (i : simple H φ) : (q i).val = rootTransport v hnH i.val := rfl
  have hcor (i : simple H φ) : v (c i : L) = (c (q i) : L) := by
    rw [hc, hc, hq]
    exact congrArg Subtype.val (coroot_transport hss hH v hnH i.val)
  have hmat (i j : simple H φ) :
      (q j).val (killingCoroot H (q i).val) = j.val (killingCoroot H i.val) := by
    rw [hq i, hq j, ← coroot_transport hss hH v hnH]
    exact rootTransport_apply v hnH _ _
  let p : diagramAutomorphisms H φ := ⟨q, hmat⟩
  have hline {α : Dual ℂ H} (hα : α ∈ rootSet H) {x y : L}
      (hx : x ∈ rootSpace H α) (hnx : x ≠ 0) (hy : y ∈ rootSpace H α) :
      ∃ t : ℂ, y = t • x := by
    rw [eq_span_singleton_of_mem_of_finrank_eq_one
      (finrank_rootSpace_eq_one hss H hH α hα) hx hnx] at hy
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨t, ht.symm⟩
  have he' (i : simple H φ) : ∃ t : ℂ, v (e i) = t • e (q i) := by
    apply hline (q i).property.1.1 (hn (q i)).1 (hn (q i)).2.2.1
    rw [hq, ← rootSpace_map_transport]
    exact ⟨e i, (hn i).1, rfl⟩
  have hf' (i : simple H φ) : ∃ t : ℂ, v (f i) = t • f (q i) := by
    have hfmem := (hn (q i)).2.1
    have hfne := (hn (q i)).2.2.2.1
    have hroot : -(q i).val ∈ rootSet H :=
      ⟨neg_ne_zero.mpr (q i).property.1.1.1,
        fun hbot => hfne ((Submodule.mem_bot ℂ).mp (hbot ▸ hfmem))⟩
    apply hline hroot hfmem hfne
    rw [hq, ← map_neg, ← rootSpace_map_transport]
    exact ⟨f i, (hn i).2.1, rfl⟩
  choose r hr using he'
  choose t ht using hf'
  have hr0 (i : simple H φ) : r i ≠ 0 := by
    intro hz
    exact (hn i).2.2.1 (v.injective (by simp [hr i, hz]))
  have hrr (i : simple H φ) : t i = (r i)⁻¹ := by
    have hbr (j : simple H φ) : ⁅e j, f j⁆ = (c j : L) :=
      (hn j).2.2.2.2.trans (congrArg Subtype.val (hc j).symm)
    have hb := v.map_lie (e i) (f i)
    rw [hbr, hcor, hr, ht, smul_lie, lie_smul, hbr, smul_smul] at hb
    have hmul := smul_left_injective ℂ
      (show (c (q i) : L) ≠ 0 from fun h => c.ne_zero _ (Subtype.ext h))
      ((one_smul ℂ (c (q i) : L)).trans hb)
    apply mul_left_cancel₀ (hr0 i)
    rw [← hmul, mul_inv_cancel₀ (hr0 i)]
  letI : Fintype (simple H φ) := FiniteDimensional.fintypeBasisIndex a
  let z : H := (Module.evalEquiv ℂ H).symm
    (a.dualBasis.equivFun.symm (fun i => Complex.log (r (q.symm i))))
  have hz (i : simple H φ) : (q i).val z = Complex.log (r i) := by
    rw [← ha (q i)]
    change (a (q i)) ((Module.evalEquiv ℂ H).symm _) = _
    rw [Module.apply_evalEquiv_symm_apply, ← Basis.dualBasis_equivFun, LinearEquiv.apply_symm_apply]
    simp
  let expo : L ≃ₗ⁅ℂ⁆ L := RegularSemisimple.expAdEquiv (z : L)
  have heE (i : simple H φ) : expo (e (q i)) = r i • e (q i) := by
    rw [exponential_eigenvector _ _ _ ((mem_rootSpace H _ _).mp (hn (q i)).1 z),
      hz, Complex.exp_log (hr0 i)]
  have hfE (i : simple H φ) : expo (f (q i)) = t i • f (q i) := by
    rw [exponential_eigenvector _ _ _ ((mem_rootSpace H _ _).mp (hn (q i)).2.1 z),
      LinearMap.neg_apply, Complex.exp_neg, hz, Complex.exp_log (hr0 i), hrr]
  have hhE (i : simple H φ) : expo (c i : L) = (c i : L) := by
    letI : IsLieAbelian H := hH.1.1
    have hzc : ⁅(z : L), (c i : L)⁆ = (0 : ℂ) • (c i : L) := by
      simpa using congrArg Subtype.val (trivial_lie_zero H H z (c i))
    rw [exponential_eigenvector _ _ _ hzc, Complex.exp_zero, one_smul]
  have hv : v = (asLieEquiv (s p)).trans expo := by
    apply generators_ext e f c A T he hf hh
    · intro i
      change v (e i) = expo ((s p).val (e i))
      rw [(hs p i).1, heE, hr]
    · intro i
      change v (f i) = expo ((s p).val (f i))
      rw [(hs p i).2.1, hfE, ht]
    · intro i
      change v (c i : L) = expo ((s p).val (c i : L))
      rw [(hs p i).2.2, hhE, hcor]
  let i := (expo.trans n.symm).trans k.symm
  have hi := CartanConjugacy.inner_trans
    (CartanConjugacy.inner_trans (CartanConjugacy.inner_exp (z : L)) (CartanConjugacy.inner_symm hni))
    (CartanConjugacy.inner_symm hk')
  refine ⟨(⟨toAut i, hi⟩, p), ?_⟩
  apply Subtype.ext
  ext x
  change k.symm (n.symm (expo ((s p).val x))) = g x
  have h := congrArg (fun a : L ≃ₗ⁅ℂ⁆ L => k.symm (n.symm (a x))) hv.symm
  simpa [v] using h

end Generation

section Intersection

attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

open NormedSpace
open Specs.LieAlgebrasAndRepresentations.RegularSemisimple (algebraNorm)
open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal

local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ
local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient (IsDominant coroots)

private theorem inner_module_intertwiner {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    (g : L ≃ₗ[ℂ] L) (hg : g ∈ innerAutomorphisms L) :
    ∃ U : V ≃ₗ[ℂ] V, ∀ x m, U ⁅x, m⁆ = ⁅g x, U m⁆ := by
  let K : Subgroup (L ≃ₗ[ℂ] L) :=
    { carrier := {g | ∃ U : V ≃ₗ[ℂ] V, ∀ x m, U ⁅x, m⁆ = ⁅g x, U m⁆}
      one_mem' := ⟨1, fun _ _ => rfl⟩
      mul_mem' := by
        rintro g h ⟨U, hU⟩ ⟨W, hW⟩
        refine ⟨U * W, fun x m => ?_⟩
        change U (W ⁅x, m⁆) = ⁅g (h x), U (W m)⁆
        rw [hW, hU]
      inv_mem' := by
        rintro g ⟨U, hU⟩
        refine ⟨U.symm, fun x m => U.injective ?_⟩
        simpa using (hU (g.symm x) (U.symm m)).symm }
  apply show innerAutomorphisms L ≤ K from (Subgroup.closure_le _).mpr ?_
  · exact hg
  rintro q ⟨x, hq⟩
  letI : NormedAddCommGroup L := algebraNorm
  letI : NormedSpace ℂ L := NormedSpace.induced ℂ L
    (Fin (finrank ℂ L) → ℂ) (finBasis ℂ L).equivFun
  letI : NormedAddCommGroup V := NormedAddCommGroup.induced V (Fin (finrank ℂ V) → ℂ)
    (finBasis ℂ V).equivFun (finBasis ℂ V).equivFun.injective
  letI : NormedSpace ℂ V := NormedSpace.induced ℂ V
    (Fin (finrank ℂ V) → ℂ) (finBasis ℂ V).equivFun
  letI : Algebra ℚ (L →L[ℂ] L) := RestrictScalars.algebra ℚ ℂ _
  letI : NormedAlgebra ℚ (L →L[ℂ] L) := NormedAlgebra.restrictScalars ℚ ℂ _
  letI : Algebra ℚ (V →L[ℂ] V) := RestrictScalars.algebra ℚ ℂ _
  letI : NormedAlgebra ℚ (V →L[ℂ] V) := NormedAlgebra.restrictScalars ℚ ℂ _
  let D := LinearMap.toContinuousLinearMap (LieAlgebra.ad ℂ L x)
  let ρ : L →L[ℂ] (V →L[ℂ] V) := LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (LieModule.toEnd ℂ L V).toLinearMap)
  let B := ρ x
  let U : ℂ → V →L[ℂ] V := fun t => exp (t • B)
  let W : ℂ → V →L[ℂ] V := fun t => exp (t • (-B))
  have hcomm (y : L) : ρ (D y) = B * ρ y - ρ y * B := by
    ext m
    change ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆
    rw [leibniz_lie, add_sub_cancel_right]
  have hLeft : exp (-B) * exp B = 1 := by
    simpa using (exp_add_of_commute (Commute.refl B).neg_left).symm
  have hRight : exp B * exp (-B) = 1 := by
    simpa using (exp_add_of_commute (Commute.refl B).neg_right).symm
  have he (y : L) : ρ (q y) * exp B = exp B * ρ y := by
    let E (t : ℂ) := exp (t • D)
    have hE (t : ℂ) : HasDerivAt E (D * E t) t := hasDerivAt_exp_smul_const' D t
    have hU (t : ℂ) : HasDerivAt U (B * U t) t := hasDerivAt_exp_smul_const' B t
    have hW (t : ℂ) : HasDerivAt W (W t * (-B)) t := hasDerivAt_exp_smul_const (-B) t
    let J (t : ℂ) := W t * ρ (E t y) * U t
    have hJ (t : ℂ) : HasDerivAt J 0 t := by
      have hEy : HasDerivAt (fun s => E s y) (D (E t y)) t := by
        simpa only [mul_apply_eq_comp, zero_add, map_zero, add_zero] using
          (hE t).clm_apply (hasDerivAt_const t y)
      have hR := ρ.hasFDerivAt.comp_hasDerivAt t hEy
      have hd := ((hW t).mul hR).mul (hU t)
      rw [hcomm] at hd
      have hz :
          (W t * (-B) * ρ (E t y) + W t * (B * ρ (E t y) - ρ (E t y) * B)) * U t +
            (W t * ρ (E t y)) * (B * U t) = 0 := by
        noncomm_ring
      change HasDerivAt J _ t at hd
      rw [← hz]
      exact hd
    have hc := is_const_of_deriv_eq_zero
      (fun t => (hJ t).differentiableAt) (fun t => (hJ t).deriv) 1 0
    have hc' : exp (-B) * ρ (q y) * exp B = ρ y := by
      have hy : (exp D) y = q y := (LinearMap.congr_fun hq y).symm
      simpa [J, W, U, E, hy] using hc
    replace hc' := congrArg (fun b => exp B * b) hc'
    simpa only [← mul_assoc, hRight, one_mul] using hc'
  let T : V ≃ₗ[ℂ] V :=
    { (exp B).toLinearMap with
      invFun := fun m => (exp (-B) : V →L[ℂ] V) m
      left_inv := fun m => congrArg (fun a : V →L[ℂ] V => a m) hLeft
      right_inv := fun m => congrArg (fun a : V →L[ℂ] V => a m) hRight }
  exact ⟨T, fun y m => (congrArg (fun a : V →L[ℂ] V => a m) (he y)).symm⟩

private theorem diagram_inner_eq_one (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hφ : Regular H φ) (e f : simple H φ → L) (hn : Normalized H φ e f)
    (c : Basis (simple H φ) ℂ H) (hc : ∀ i, c i = killingCoroot H i.val)
    (s : diagramAutomorphisms H φ →* Aut L)
    (hs : ∀ p i, (s p).val (e i) = e (p.val i) ∧
      (s p).val (f i) = f (p.val i) ∧ (s p).val (c i : L) = (c (p.val i) : L))
    (p : diagramAutomorphisms H φ) (hi : s p ∈ inner L) : p = 1 := by
  classical
  letI : H.IsCartanSubalgebra := (isCartan_iff_isCartanSubalgebra H).mp
    ((isCartan_iff_maximal_toral hss H).mpr hH)
  letI : Fintype (simple H φ) := FiniteDimensional.fintypeBasisIndex c
  have hraise : RaisingVectors H φ e := fun i => ⟨(hn i).1, (hn i).2.2.1⟩
  apply Subtype.ext
  apply Equiv.ext
  intro i
  change p.val i = i
  let lam : Dual ℂ H := c.dualBasis i
  let mu : Dual ℂ H := c.dualBasis (p.val i)
  have hdom : IsDominant H φ lam := by
    intro j
    change ∃ n : ℕ, lam (coroots H φ j) = (n : ℂ)
    rw [← show c j = coroots H φ j from hc j]
    by_cases h : j = i
    · exact ⟨1, by simp [lam, h]⟩
    · exact ⟨0, by simp [lam, Ne.symm h]⟩
  obtain ⟨χ, hχ, hfin, hsimple⟩ :=
    HighestWeightClassification.dominant_has_simple_quotient hss H φ hφ lam hdom
  set V := simpleQuotient_value H φ χ
  letI : LieRingModule L V := inferInstanceAs (LieRingModule L (simpleQuotient_value H φ χ))
  letI : LieModule ℂ L V := inferInstanceAs (LieModule ℂ L (simpleQuotient_value H φ χ))
  letI : FiniteDimensional ℂ V := hfin
  letI : IsSimpleOrder (LieSubmodule ℂ L V) := hsimple
  let x : V := quotientHighestVector H φ χ
  have hx : IsHighestWeight e lam x :=
    (SimpleHighestWeightQuotient.simple_quotient hss H φ hφ lam χ hχ e hraise).2
  obtain ⟨U, hU⟩ := inner_module_intertwiner (V := V) (s p).val hi
  let y := U x
  have hy0 : y ≠ 0 := fun he => hx.1 (U.injective (he.trans (map_zero U).symm))
  have hyh (h : H) : ⁅(h : L), y⁆ = mu h • y := by
    let act : H →ₗ[ℂ] V := (LinearMap.applyₗ (R := ℂ) y).comp
      ((LieModule.toEnd ℂ L V).toLinearMap.comp H.incl.toLinearMap)
    change act h = (mu.smulRight y) h
    suffices ha' : act = mu.smulRight y from LinearMap.congr_fun ha' h
    apply c.ext
    intro i'
    change ⁅(c i' : L), y⁆ = mu (c i') • y
    let j := p.val.symm i'
    have hj : p.val j = i' := p.val.apply_symm_apply i'
    have ht := hU (c j : L) x
    rw [hx.2.1, map_smul, (hs p j).2.2, hj] at ht
    have hcoord : lam (c j) = mu (c i') := by
      simp only [lam, mu, Basis.dualBasis_apply_self, ← hj, p.val.injective.eq_iff]
    rw [← ht, hcoord]
  have hye (j : simple H φ) : ⁅e j, y⁆ = 0 := by
    have h := hU (e (p.val.symm j)) x
    rw [hx.2.2.1, map_zero, (hs p (p.val.symm j)).1, Equiv.apply_symm_apply] at h
    exact h.symm
  have hyg : LieSubmodule.lieSpan ℂ L ({y} : Set V) = ⊤ := by
    rcases (IsSimpleOrder.eq_bot_or_eq_top (LieSubmodule.lieSpan ℂ L ({y} : Set V))) with h | h
    · have hy := LieSubmodule.subset_lieSpan (R := ℂ) (L := L) (s := ({y} : Set V)) (by simp : y ∈ ({y} : Set V))
      change y ∈ LieSubmodule.lieSpan ℂ L ({y} : Set V) at hy
      rw [h, LieSubmodule.mem_bot] at hy
      exact (hy0 hy).elim
    · exact h
  have hweight := SimpleHighestWeightQuotient.highest_weight_eq_of_equiv
    hss H φ hφ e hraise V V lam mu x y hx ⟨hy0, hyh, hye, hyg⟩ LieModuleEquiv.refl
  exact (c.dualBasis.injective hweight).symm

end Intersection

theorem decomposition : decompositionType.{u} := by
  intro L _ _ _ hss H hH φ hφ e f hn
  classical
  obtain ⟨c, a, A, hca, hA, ha, T, he, hf, hh⟩ := serrePresentation hss hH hφ e f hn
  have hc (i : simple H φ) := (hca i).1
  obtain ⟨s, hs⟩ := existsDiagramSection e f c A hc hA ha T he hf hh
  have hintersection (p : diagramAutomorphisms H φ) : s p ∈ inner L ↔ p = 1 := by
    constructor
    · exact diagram_inner_eq_one hss hH hφ e f hn c hc s hs p
    · rintro rfl
      rw [map_one]
      exact (inner L).one_mem
  refine ⟨inner_normal, s, ?_, hintersection, ⟨?_, ?_⟩⟩
  · simpa only [hc] using hs
  · rintro ⟨x, p⟩ ⟨y, q⟩ (heq : x.val * s p = y.val * s q)
    have hk : s (p * q⁻¹) = x.val⁻¹ * y.val := by
      rw [map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, heq, mul_inv_cancel_right]
    have hmem : s (p * q⁻¹) ∈ inner L := hk ▸ (inner L).mul_mem ((inner L).inv_mem x.property) y.property
    have hp := (hintersection (p * q⁻¹)).mp hmem
    have hpq : p = q := mul_inv_eq_one.mp hp
    subst q
    exact Prod.ext (Subtype.ext (mul_right_cancel heq)) rfl
  · exact factorization_surjective hss hH hφ e f hn c a hc (fun i => (hca i).2) A T he hf hh s hs

theorem semidirectProduct : semidirectProductType.{u} := by
  intro L _ _ _ hss H hH φ hφ e f hn
  obtain ⟨hN, s, hs, hintersection, hb⟩ := decomposition hss H hH φ hφ e f hn
  let m := SemidirectProduct.lift (φ := diagramAction hN s) (inner L).subtype s
    (fun g => by
      ext n
      rfl)
  refine ⟨hN, s, hs, hintersection, MulEquiv.ofBijective m ?_, fun _ => rfl⟩
  exact (SemidirectProduct.equivProd.bijective_comp _).mpr hb

end LieAlgebrasAndRepresentations.AutomorphismDecomposition
