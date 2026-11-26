import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalFormsOverUnramifiedFields
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalSteinbergSection
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedTorusTorsors
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.RationalStronglyRegularElements
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.StronglyRegularSeparableTransporter
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalTwistedTraceComparison
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Group

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj BigOperators

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalFormsOverUnramifiedFields

open _root_.LinearAlgebraicGroups.Specs
open Specs.ExceptionalFormsOverUnramifiedFields
open Specs.AutomorphismSequence (AdjointQuotient automorphisms groupSections relativePoints)
open Specs.RelativeFormComparison (fieldTest fieldMap transportedAut automorphismAction)
open Specs.QuasiSplitInnerForms (AreInnerForms relativeAutTopology relativeAutDiscrete
  basedAutTopology fieldGalTopology)
attribute [local instance] relativeAutTopology relativeAutDiscrete basedAutTopology fieldGalTopology
open Specs.SteinbergPinnedDescent
  (ExceptionalDiagram HighestWeightModules OppositeBorel traceValue diagramPermutation
    permuteParameters comparisonOnPoints pinnedAction coefficientAction)
open Specs.ExceptionalSteinbergSection (IsGeometricImage GeometricTraceFibre)
open Specs.GeometricRadicals (GeometricGroup)
open Specs.AdjointRepresentation (GroupPoints)
open LinearAlgebraicGroups.Descent.NonabelianCohomology
open Arithmetic.MaximalUnramifiedBrauer (maximalUnramified)

open private modelOfRelativeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms

/-- The maximal unramified field contains its infinite local base field. -/
theorem maximal_unramified_infinite (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    Infinite (maximalUnramified F) := by
  obtain ⟨v, hv, hv'⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := F)
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective v
  have hpow : Function.Injective (fun n : ℕ ↦ x ^ n) := by
    intro n m hnm
    apply (pow_right_strictAnti₀ hv hv').injective
    simpa only [map_pow, hx] using congrArg (ValuativeRel.valuation F) hnm
  exact Infinite.of_injective _ ((algebraMap F (maximalUnramified F)).injective.comp hpow)


/-- Number of Dynkin graph walks of the given length beginning at a vertex. -/
private def dynkinWalks (n : ℕ) : ℕ → Fin n → ℕ
  | 0, _ => 1
  | r + 1, i => ∑ j : Fin n, if CartanMatrix.E n i j = -1 then dynkinWalks n r j else 0

private theorem dynkinWalks_invariant {n : ℕ} (p : Equiv.Perm (Fin n))
    (hp : ∀ i j, CartanMatrix.E n (p i) (p j) = CartanMatrix.E n i j) (r : ℕ) :
    ∀ i, dynkinWalks n r (p i) = dynkinWalks n r i := by
  induction r with
  | zero => intro i; rfl
  | succ r ih =>
    intro i
    simp only [dynkinWalks]
    apply Fintype.sum_equiv p.symm
    intro j
    have hcartan : CartanMatrix.E n (p i) j = CartanMatrix.E n i (p.symm j) := by
      simpa only [p.apply_symm_apply] using hp i (p.symm j)
    have hwalk : dynkinWalks n r j = dynkinWalks n r (p.symm j) := by
      simpa only [p.apply_symm_apply] using ih (p.symm j)
    rw [hcartan, hwalk]

private theorem e7e8DiagramTrivial {n : ℕ} (hn : n = 7 ∨ n = 8)
    (p : Equiv.Perm (Fin n))
    (hp : ∀ i j, CartanMatrix.E n (p i) (p j) = CartanMatrix.E n i j) :
    p = 1 := by
  have hinj : Function.Injective (fun i ↦ (dynkinWalks n 2 i, dynkinWalks n 3 i)) := by
    rcases hn with rfl | rfl
    · decide
    · decide
  apply Equiv.ext
  intro i
  change p i = i
  exact hinj (Prod.ext (dynkinWalks_invariant p hp 2 i) (dynkinWalks_invariant p hp 3 i))

private theorem diagramTrivial_of_typeE
    {k : Type u} [Field k] {A : RootGroups.AdditiveLine k} {P : Pinning.PinnedGroup A}
    {D : Pinning.AttachedDatum P.pair} {n : ℕ} (hn : n = 7 ∨ n = 8) (ht : HasTypeE D n)
    (d : Aut D.toBased) : diagramPermutation D d = 1 := by
  obtain ⟨e, he⟩ := ht
  let := D.comm
  let p := diagramPermutation D d
  let q : Equiv.Perm (Fin n) := (e.trans p).trans e.symm
  have hp (i j : Pinning.SimpleRoot P.pair) :
      D.datum.rootDatum.pairing (p i).val (p j).val =
        D.datum.rootDatum.pairing i.val j.val := by
    let v : D.datum.rootDatum.Equiv D.datum.rootDatum := d.asIso.hom.val
    exact v.toHom.pairing
  have heq (i : Fin n) : e (q i) = p (e i) := e.apply_symm_apply _
  have hq : q = 1 := e7e8DiagramTrivial hn q (fun i j ↦ by rw [← he, heq, heq, hp, he])
  apply Equiv.ext
  intro i
  obtain ⟨j, rfl⟩ := e.surjective i
  change p (e j) = e j
  rw [← heq, hq]
  rfl

private theorem sectionDiagram
    {k S : Type u} [Field k] [Field S] [Algebra k S]
    {A : RootGroups.AdditiveLine k} {P : Pinning.PinnedGroup A} {D : Pinning.AttachedDatum P.pair}
    (outer : Gal(S/k) → Aut D.toBased) (h : IsExceptionalReference D) :
    ExceptionalDiagram D outer := by
  rcases h.2.2 with h₆ | h₇ | h₈
  · exact Or.inr h₆
  · exact Or.inl (fun galois ↦ diagramTrivial_of_typeE (Or.inl rfl) h₇ (outer galois))
  · exact Or.inl (fun galois ↦ diagramTrivial_of_typeE (Or.inr rfl) h₈ (outer galois))

/-- The compatible trace tuple of a separable-closure point is represented
by a ground-field point, with the geometric fibre comparison supplied by
the very same highest-weight modules. -/
theorem matching_reference_point
    {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {A : RootGroups.AdditiveLine k} {P : Pinning.PinnedGroup A} {D : Pinning.AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    {E : AutomorphismSequence.SplitSequence P D l Q}
    {ω : Cocycle (QuasiSplitInnerForms.trivialOuterAction (k := k) (S := S) D.toBased)}
    (V : QuasiSplitInnerForms.PinnedRepresentative (S := S) E ω)
    (hV : IsExceptionalReference D)
    (y : GroupPoints P.pair.G.val (CommAlgCat.of k S)) :
    ∃ (N : OppositeBorel P.pair) (U : ClosedSubgroup P.pair.B.group)
      (M : HighestWeightModules N U),
      (∀ (galois : Gal(S/k)) (z : GroupPoints P.pair.G.val (CommAlgCat.of k S)),
        (fun i ↦ traceValue (M.representation i) _ (pinnedAction S (l (ω galois)).asIso.hom galois z)) =
          permuteParameters (diagramPermutation D (ω galois)) (fun c : S ↦ galois c)
            (fun i ↦ traceValue (M.representation i) _ z)) ∧
      ((∀ galois, permuteParameters (diagramPermutation D (ω galois)) (fun c : S ↦ galois c)
        (fun i ↦ traceValue (M.representation i) (CommAlgCat.of k S) y) =
          fun i ↦ traceValue (M.representation i) (CommAlgCat.of k S) y) →
      ∃ (x : LinearAlgebraicGroups.Affine.RationalPoints V.model.val.val)
        (g : GroupPoints P.pair.G.val (CommAlgCat.of k S)),
        mapPoints (CommAlgCat.ofHom (Algebra.ofId k S)) x =
          comparisonOnPoints V.trivialization g ∧
        ∀ f : S →ₐ[k] AlgebraicClosure k,
          ∃ x' y' : LinearAlgebraicGroups.Affine.RationalPoints (GeometricGroup P.pair.G).val,
            IsGeometricImage f g x' ∧ IsGeometricImage f y y' ∧
            GeometricTraceFibre (GeometricGroup P.pair.G) x' y') := by
  obtain ⟨N, U, _, M, _, hsection⟩ :=
    Arithmetic.ExceptionalSteinbergSection.referenceSection V hV.1 hV.2.1 (sectionDiagram (fun galois ↦ ω galois) hV)
  obtain ⟨n, blocks, _, _, _, _, _, _, _, _, hfibre, _, _, _, hequiv, hmatching⟩ := hsection
  refine ⟨N, U, M, hequiv, fun hy ↦ ?_⟩
  obtain ⟨t, x, ht, _, hx⟩ := hmatching (fun i ↦ traceValue (M.representation i) _ y) (Or.inl hy)
  exact ⟨x, _, hx, fun f ↦ hfibre f _ y (fun i ↦ congrFun ht i)⟩

/-- An arbitrary relative trivialization transports the usual coefficient action
to its own descent action. Evaluation uses the identity object in the field slice. -/
theorem comparison_transports_coefficient_action
    {k S : Type u} [Field k] [Field S] [Algebra k S] {G H : GroupScheme k}
    (e : relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S))
    (galois : Gal(S/k)) (y : GroupPoints G (CommAlgCat.of k S)) :
    let U := Over.mk (𝟙 (fieldTest k S))
    comparisonOnPoints e
      (((transportedAut k S e galois).asIso.hom.app (op U)).hom (coefficientAction S G galois y)) =
      coefficientAction S H galois (comparisonOnPoints e y) := by
  dsimp only
  let U := Over.mk (𝟙 (fieldTest k S))
  let W := Over.mk (fieldMap k S galois)
  let v : W ⟶ U := Over.homMk (fieldMap k S galois) (Category.comp_id _)
  have hn :
      coefficientAction S H galois (comparisonOnPoints e y) =
        (e.hom.app (op W)).hom (coefficientAction S G galois y) :=
    (ConcreteCategory.congr_hom (e.hom.naturality v.op) y).symm
  rw [hn]
  change comparisonOnPoints e
    ((e.inv.app (op U)).hom ((e.hom.app (op W)).hom (coefficientAction S G galois y))) = _
  exact (comparisonOnPoints e).apply_symm_apply _

open LinearAlgebraicGroups.Affine (RationalPoints IsRationalJordanDecomposition)
open Specs.GeometricRadicals (IsTorus)
open Specs.SteinbergGeometricFibres (IsPointCentralizer)
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

/-- The matching geometric point is conjugate to the semisimple target
when the target's full scheme centralizer is a torus. -/
theorem geometric_conjugacy_of_matching
    {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (x y : RationalPoints G.val) (h : GeometricTraceFibre G x y)
    (hy : IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ y y 1)
    (C : ClosedSubgroup G.val) (y₀ : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (hT : IsTorus C.group) (hC : IsPointCentralizer C y₀)
    (hy₀ : y = (toUnit ((testSpec k).obj (op (CommAlgCat.of k k))) ≫ y₀ :
      RationalPoints G.val)) :
    ∃ g : RationalPoints G.val, g * x * g⁻¹ = y := by
  obtain ⟨⟨s, v⟩, hj, _⟩ := LinearAlgebraicGroups.Affine.rationalJordanDecomposition G x
  obtain ⟨g, _, hg⟩ := h hj hy
  exact ⟨g, hg C y₀ hT hC hy₀ rfl⟩

section Cohomology

variable {Γ M N : Type*} [Group Γ] [TopologicalSpace Γ]
  [Group M] [TopologicalSpace M] [Group N] [TopologicalSpace N]
  {ρ : Γ →* MulAut M} {σ : Γ →* MulAut N}

/-- A cocycle which can be changed into the image of a torus cocycle is
neutral whenever that torus cocycle is neutral. -/
theorem neutral_of_reduction (p : N →* M)
    (hequiv : ∀ galois n, p (σ galois n) = ρ galois (p n))
    (a : Cocycle ρ) (c : Cocycle σ) (b : M)
    (h : ∀ galois, p (c galois) = b⁻¹ * a galois * ρ galois b)
    (hc : classOf c = basepoint σ) : classOf a = basepoint ρ := by
  obtain ⟨d, hd⟩ := classOf_eq_iff.mp hc
  apply classOf_eq_iff.mpr
  refine ⟨b * p d, fun galois ↦ ?_⟩
  change 1 = (b * p d)⁻¹ * a galois * ρ galois (b * p d)
  have hd₁ : 1 = d⁻¹ * c galois * σ galois d := hd galois
  have hd₂ : 1 = p d⁻¹ * p (c galois) * ρ galois (p d) := by
    simpa only [map_one, map_mul, hequiv] using congrArg p hd₁
  rw [h galois, map_inv] at hd₂
  simpa only [mul_inv_rev, map_mul, mul_assoc] using hd₂

/-- If a continuous cocycle is conjugated into an equivariantly embedded subgroup,
the induced subgroup cocycle is continuous and has the same class after inclusion. -/
theorem cocycle_into_subgroup [DiscreteTopology M]
    (hact : Continuous (fun q : Γ × M ↦ ρ q.1 q.2))
    (p : N →* M) (hp : Function.Injective p)
    (hequiv : ∀ galois n, p (σ galois n) = ρ galois (p n))
    (a : Cocycle ρ) (b : M)
    (h : ∀ galois, b⁻¹ * a galois * ρ galois b ∈ p.range) :
    ∃ c : Cocycle σ, ∀ galois, p (c galois) = b⁻¹ * a galois * ρ galois b := by
  choose c hc using h
  have ha : Continuous (fun galois ↦ b⁻¹ * a galois * ρ galois b) :=
    (continuous_const.mul a.property.1).mul (hact.comp (continuous_id.prodMk continuous_const))
  obtain ⟨f, hf⟩ := hp.hasLeftInverse
  have hcont : Continuous c := by
    have he : c = fun galois ↦ f (b⁻¹ * a galois * ρ galois b) := by
      funext galois
      rw [← hc, hf]
    rw [he]
    exact continuous_of_discreteTopology.comp ha
  refine ⟨⟨c, hcont, fun galois tau ↦ hp ?_⟩, hc⟩
  rw [map_mul, hequiv, hc, hc, hc, a.property.2, map_mul, MulAut.mul_apply,
    map_mul, map_mul, map_inv]
  group

/-- The change of cocycle by a point transporting a rational element to a
twisted fixed element takes values in the stabilizer of the rational element. -/
theorem changed_cocycle_fixes
    {X : Type*} [Group X] (action : M →* MulAut X) (s : Γ →* MulAut X)
    (hequiv : ∀ galois m x, action (ρ galois m) (s galois x) =
      s galois (action m x))
    (a : Cocycle ρ) (b : M) (x y : X)
    (hx : ∀ galois, s galois x = x)
    (hy : ∀ galois, action (a galois) (s galois y) = y)
    (hb : action b x = y) (galois : Γ) :
    action (b⁻¹ * a galois * ρ galois b) x = x := by
  simp only [map_mul, MulAut.mul_apply]
  have hby : action (ρ galois b) x = s galois y := by
    rw [← hx galois, hequiv, hb]
  rw [hby, hy, ← hb, map_inv]
  exact (action b).symm_apply_apply x

end Cohomology

/-- Descent of an inner form follows from neutral cohomology for its actual
adjoint quotient. -/
theorem inner_form_iso_of_adjoint_vanishing
    {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (G H : AffineAlgebraicGroup k)
    (vanish : ∀ (Q : AdjointQuotient G) (x : groupH1 k Q.quotient.val.X S),
      x = groupBasepoint k Q.quotient.val.X S)
    (h : AreInnerForms (S := S) G H) :
    Nonempty (G.val ≅ H.val) := by
  obtain ⟨Q, inn, _, hinj, i, hi⟩ := h
  let : TopologicalSpace (Descent.NonabelianCohomology.Points k S Q.quotient.val.X) := ⊥
  obtain ⟨C⟩ := LinearAlgebraicGroups.Descent.RelativeFormComparison.relativeFormClassification
    (S := S) G
  obtain ⟨a, ha, hclass⟩ := C.computes (modelOfRelativeIso G H i) i
  obtain ⟨d, hd, _⟩ := LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.liftInnerCocycle
    G.val Q.quotient.val inn (hinj _) a (fun galois ↦ ha galois ▸ hi galois)
  have hneutral : classOf d = basepoint _ :=
    vanish Q (classOf d)
  obtain ⟨b, hb⟩ := classOf_eq_iff.mp hneutral
  let p : Descent.NonabelianCohomology.Points k S Q.quotient.val.X →* AutomorphismSequence.RelativeAut G.val (fieldTest k S) :=
    (inn.app (op (fieldTest k S))).hom.comp
      { toFun := ULift.up, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hequiv (galois : Gal(S/k)) (x : Descent.NonabelianCohomology.Points k S Q.quotient.val.X) :
      p (pointAction k S Q.quotient.val.X galois x) = automorphismAction k S G.val galois (p x) :=
    ConcreteCategory.congr_hom (inn.naturality (fieldMap k S galois).op)
      (ULift.up x : (groupSections Q.quotient.val).obj (op (fieldTest k S)))
  let c := p b
  have hc : ChangesBy a (trivial _) c := by
    intro galois
    have hp (galois : Gal(S/k)) : p (d galois) = a galois := hd galois
    change 1 = c⁻¹ * a galois * automorphismAction k S G.val galois c
    have hd₁ : 1 = b⁻¹ * d galois * pointAction k S Q.quotient.val.X galois b := hb galois
    simpa only [map_one, map_mul, map_inv, hequiv, hp, c] using congrArg p hd₁
  have heq := classOf_eq_iff.mpr ⟨c, hc⟩
  exact Quotient.exact (C.equiv.injective ((hclass.trans heq).trans C.pointed.symm)).symm

theorem inner_forms_are_reference_of_adjoint_vanishing
    (h : AdjointVanishing.{u}) : InnerFormsAreReference.{u} := by
  intro F _ _ _ _ K S _ _ _ A P D l Q E ω V hV H hH
  exact inner_form_iso_of_adjoint_vanishing V.model.val H (h F S V hV) hH

/-- Cohomology of a group over the maximal unramified field vanishes if
each cocycle reduces to the point group of a scheme torus. -/
theorem vanishing_of_torus_reduction
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : Type u} [Field S] [Algebra (maximalUnramified F) S]
    [IsSepClosure (maximalUnramified F) S]
    (G : AffineAlgebraicGroup (maximalUnramified F)) :
    let K := maximalUnramified F
    let : TopologicalSpace (Descent.NonabelianCohomology.Points K S G.val.X) := ⊥
    let ρ := pointAction K S G.val.X
    (∀ a : Cocycle ρ, ∃ (B : HopfAlgebraCategory K) (_ : CharacterDescent.IsTorus B),
      let : TopologicalSpace (Descent.NonabelianCohomology.Points K S (specGroup B).X) := ⊥
      let σ := pointAction K S (specGroup B).X
      ∃ (p : Descent.NonabelianCohomology.Points K S (specGroup B).X →* Descent.NonabelianCohomology.Points K S G.val.X),
        (∀ galois n, p (σ galois n) = ρ galois (p n)) ∧
          ∃ (c : Cocycle σ) (b : Descent.NonabelianCohomology.Points K S G.val.X),
            ∀ galois, p (c galois) = b⁻¹ * a galois * ρ galois b) →
    ∀ x : groupH1 K G.val.X S, x = groupBasepoint K G.val.X S := by
  intro K _ ρ h x
  refine Quotient.inductionOn x fun a ↦ ?_
  obtain ⟨B, hB, p, hp, c, b, hb⟩ := h a
  let : TopologicalSpace (Descent.NonabelianCohomology.Points K S (specGroup B).X) := ⊥
  have hc := MaximalUnramifiedTorusTorsors.torus_vanishing F S B hB (classOf c)
  exact neutral_of_reduction p hp a c b hb hc

set_option maxHeartbeats 1000000 in
/-- For a finite-type affine group the separating torus can be specified by
an equivariant injection on points and a range condition. -/
theorem vanishing_of_torus_subgroups
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : Type u} [Field S] [Algebra (maximalUnramified F) S]
    [IsSepClosure (maximalUnramified F) S]
    (G : AffineAlgebraicGroup (maximalUnramified F)) :
    let K := maximalUnramified F
    let : TopologicalSpace (Descent.NonabelianCohomology.Points K S G.val.X) := ⊥
    let ρ := pointAction K S G.val.X
    (∀ a : Cocycle ρ, ∃ (B : HopfAlgebraCategory K) (_ : CharacterDescent.IsTorus B),
      let σ := pointAction K S (specGroup B).X
      ∃ (p : Descent.NonabelianCohomology.Points K S (specGroup B).X →*
            Descent.NonabelianCohomology.Points K S G.val.X),
        Function.Injective p ∧ (∀ galois n, p (σ galois n) = ρ galois (p n)) ∧
          ∃ b : Descent.NonabelianCohomology.Points K S G.val.X,
            ∀ galois, b⁻¹ * a galois * ρ galois b ∈ p.range) →
    ∀ x : groupH1 K G.val.X S, x = groupBasepoint K G.val.X S := by
  intro K _ ρ h
  apply vanishing_of_torus_reduction F G
  intro a
  let : DiscreteTopology (Descent.NonabelianCohomology.Points K S G.val.X) := ⟨rfl⟩
  let : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  have hact : Continuous (fun q : Gal(S/K) × Descent.NonabelianCohomology.Points K S G.val.X ↦
      ρ q.1 q.2) := by
    apply (continuousAction_iff_finiteLevel (ρ := ρ)).mpr
    intro m
    obtain ⟨L, hL⟩ := point_defined_at_finite_level m
    exact ⟨L, (finitePoints_iff_fixed L m).mp hL⟩
  obtain ⟨B, hB, p, hp, hequiv, b, hb⟩ := h a
  let : TopologicalSpace (Descent.NonabelianCohomology.Points K S (specGroup B).X) := ⊥
  obtain ⟨c, hc⟩ := cocycle_into_subgroup hact p hp hequiv a b hb
  exact ⟨B, hB, p, hequiv, c, b, hc⟩


section Transport

open CategoryTheory.Limits
open Specs.ExceptionalTwistedTraceComparison (Twist PointCocycle InnerMap adjointAction extendPoint
  projectionOnPoints)
open Specs.StronglyRegularSeparableTransporter (extendedPoint Fixes)
open Specs.ExceptionalSteinbergSection (geometricTestMap)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.SteinbergGeometricFibres (pointHom)
open Specs.RelativeFormComparison (IsInduced)
open private transportSubgroup isTorus_iff_coordinates
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private pointExtension pointExtension_eq pointExtension_constant
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.StronglyRegularSeparableTransporter
open private extendedGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

variable {k S : Type u} [Field k] [Field S] [Algebra k S]

private theorem split_torus_over_separably_closed [IsSepClosed S]
    (T : AffineAlgebraicGroup k) (hT : IsTorus T.val) :
    IsSplitTorus ((groupBaseChange k S).obj T.val) := by
  obtain ⟨A, ⟨e⟩, E, _, _, _, r, ⟨t⟩⟩ := (isTorus_iff_coordinates T).mp hT
  let a : E →ₐ[k] S := IsSepClosed.lift
  let : Algebra E S := a.toAlgebra
  let : IsScalarTower k E S := IsScalarTower.of_algebraMap_eq fun x ↦ (a.commutes x).symm
  let t' : DiagonalizableGroups.groupAlgebra S (Specs.CharacterDescent.StandardLattice.{u} r) ≅ extendedHopf S A :=
    (CommHopfAlgCat.isoMk (LinearAlgebraicGroups.CharacterDescent.groupAlgebraBaseChange E S _)).symm ≪≫
      (LinearAlgebraicGroups.CharacterDescent.extendedHopfFunctor S).mapIso t ≪≫
      LinearAlgebraicGroups.CharacterDescent.extendedHopfTower (K := E) S A
  obtain ⟨j⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := S) r
  exact ⟨r, ⟨(groupBaseChange k S).mapIso e.symm ≪≫
    (extendedGroupIso S A).symm ≪≫ (hopfSpec (CommRingCat.of S)).mapIso t'.op ≪≫ j⟩⟩

private theorem centralizer_transport {G H : GroupScheme k} (e : G ≅ H)
    {C : ClosedSubgroup G} {y : 𝟙_ (SchemeOver k) ⟶ G.X} (hc : IsPointCentralizer C y) :
    IsPointCentralizer (transportSubgroup e C) (y ≫ e.hom.hom.hom) := by
  intro Y g
  let m : (Y ⟶ G.X) →* (Y ⟶ H.X) := IsMonHom.monoidHom e.hom.hom.hom Y
  let n : (Y ⟶ H.X) →* (Y ⟶ G.X) := IsMonHom.monoidHom e.inv.hom.hom Y
  have hmn (g : Y ⟶ H.X) : m (n g) = g := by
    change (g ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = g
    rw [Category.assoc]
    exact congrArg (g ≫ ·) ((Grp.forget (SchemeOver k)).congr_map e.inv_hom_id) |>.trans
      (Category.comp_id g)
  have hm : Function.Injective m := by
    let F := Grp.forget (SchemeOver k)
    let : IsIso e.hom.hom.hom := F.map_isIso e.hom
    intro x z h
    exact (cancel_mono e.hom.hom.hom).mp h
  have hcomm : Commute g (toUnit Y ≫ (y ≫ e.hom.hom.hom)) ↔
      Commute (n g) (toUnit Y ≫ y) := by
    have hh : Commute (m (n g)) (m (toUnit Y ≫ y)) ↔ Commute (n g) (toUnit Y ≫ y) := by
      simp only [Commute, SemiconjBy, ← map_mul, hm.eq_iff]
    rw [hmn] at hh
    exact (show Commute g ((toUnit Y ≫ y) ≫ e.hom.hom.hom) ↔ _ from hh)
      |> fun h ↦ by simpa only [Category.assoc] using h
  change Commute g (toUnit Y ≫ (y ≫ e.hom.hom.hom)) ↔ _
  rw [hcomm]
  have h := hc Y (n g)
  change Commute (n g) (toUnit Y ≫ y) ↔ _ at h
  rw [h]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change s ≫ C.inclusion.hom.hom ≫ e.hom.hom.hom = g
    rw [← Category.assoc, hs]
    exact hmn g
  · rintro ⟨s, hs⟩
    refine ⟨s, hm ?_⟩
    rw [hmn]
    exact Category.assoc _ _ _ |>.trans hs

private theorem extended_point_first {G : GroupScheme k}
    (x : GroupPoints G (CommAlgCat.of k S)) :
    (extendedPoint x).left ≫ pullback.fst G.X.hom (fieldSpecMap k S) = x.left := by
  let F := Over.map (fieldSpecMap k S)
  let U := 𝟙_ (SchemeOver S)
  let W := fieldTest k S
  let j : F.obj U ⟶ W := Over.homMk (𝟙 _) (by
    simp only [F, U, Over.map_obj_hom, Over.tensorUnit_hom, Category.id_comp]
    rfl)
  let e := (Over.mapPullbackAdj (fieldSpecMap k S)).homEquiv U G.X
  have h := congrArg Over.Hom.left (e.symm_apply_apply (j ≫ x))
  change (extendedPoint x).left ≫ pullback.fst G.X.hom (fieldSpecMap k S) = (j ≫ x).left at h
  exact h.trans (Category.id_comp _)

private theorem extended_point_comparison {G H : GroupScheme k}
    {e : relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S)}
    {i : (groupBaseChange k S).obj G ≅ (groupBaseChange k S).obj H}
    (hi : IsInduced k S i e) (x : GroupPoints G (CommAlgCat.of k S)) :
    extendedPoint (comparisonOnPoints e x) = extendedPoint x ≫ i.hom.hom.hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [extended_point_first, Over.comp_left, Category.assoc]
    have hl : (extendedPoint x).left =
        pullback.lift x.left (𝟙 _) (by exact Over.w x) := by
      apply pullback.hom_ext
      · rw [extended_point_first, pullback.lift_fst]
      · exact (Over.w (extendedPoint x)).trans (pullback.lift_snd ..).symm
    rw [hl]
    exact hi (Over.mk (𝟙 (fieldTest k S))) x
  · exact (Over.w (extendedPoint (comparisonOnPoints e x))).trans
      (Over.w (extendedPoint x ≫ i.hom.hom.hom)).symm

private theorem extend_rational_point {G : GroupScheme k}
    (x : 𝟙_ (SchemeOver k) ⟶ G.X) :
    extendPoint (S := S) (toUnit (fieldTest k k) ≫ x : RationalPoints G) =
      (toUnit (fieldTest k S) ≫ x : GroupPoints G (CommAlgCat.of k S)) := by
  change (testSpec k).map (CommAlgCat.ofHom (Algebra.ofId k S)).op ≫ toUnit _ ≫ x = _
  rw [← Category.assoc, comp_toUnit]

private theorem extended_rational_point {G : GroupScheme k}
    (x : 𝟙_ (SchemeOver k) ⟶ G.X) :
    extendedPoint (extendPoint (S := S) (toUnit (fieldTest k k) ≫ x : RationalPoints G)) =
      scalarExtendedRationalPoint S x := by
  rw [extend_rational_point, ← pointExtension_eq]
  exact pointExtension_constant G x

private theorem fieldTest_ground_hom (k : Type u) [Field k] :
    (fieldTest k k).hom = 𝟙 (Spec (CommRingCat.of k)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
  rw [Algebra.algebraMap_self]
  exact Spec.map_id _

private theorem geometric_image_rational_point {G : GroupScheme k}
    (f : S →ₐ[k] AlgebraicClosure k) (x : 𝟙_ (SchemeOver k) ⟶ G.X) :
    IsGeometricImage f (extendPoint (S := S) (toUnit (fieldTest k k) ≫ x : RationalPoints G))
      (toUnit _ ≫ scalarExtendedRationalPoint (AlgebraicClosure k) x) := by
  apply Over.OverMorphism.ext
  rw [show scalarExtendedRationalPoint (AlgebraicClosure k) x =
      extendedPoint (extendPoint (S := AlgebraicClosure k)
        (toUnit (fieldTest k k) ≫ x : RationalPoints G)) from
        (extended_rational_point x).symm]
  let U := fieldTest (AlgebraicClosure k) (AlgebraicClosure k)
  change ((toUnit U).left ≫ (extendedPoint _).left) ≫ _ = _
  rw [Category.assoc, extended_point_first]
  rw [extend_rational_point, extend_rational_point]
  have hU : (toUnit U).left = 𝟙 _ := (Over.w (toUnit U)).trans (by
    exact fieldTest_ground_hom (AlgebraicClosure k))
  rw [hU, Category.id_comp]
  let R := (restrictTestAlgebra k (AlgebraicClosure k)).obj
    (CommAlgCat.of (AlgebraicClosure k) (AlgebraicClosure k))
  let W := (testSpec k).obj (op R)
  let a : W ⟶ fieldTest k S := (testSpec k).map (geometricTestMap f).op
  have h : (toUnit W ≫ x) = a ≫ (toUnit (fieldTest k S) ≫ x) := by
    rw [← Category.assoc, comp_toUnit]
  exact congrArg Over.Hom.left h

open private groundIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.TorusSections

private def rationalSection {X : SchemeOver k} (x : Points X (CommAlgCat.of k k)) :
    𝟙_ (SchemeOver k) ⟶ X :=
  (groundIso (k := k)).inv ≫ x

private theorem toUnit_rationalSection {X : SchemeOver k}
    (x : Points X (CommAlgCat.of k k)) :
    toUnit (fieldTest k k) ≫ rationalSection x = x := by
  have h : toUnit (fieldTest k k) = (groundIso (k := k)).hom := toUnit_unique _ _
  rw [rationalSection, h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

private theorem geometric_image_injective {G : GroupScheme k}
    (f : S →ₐ[k] AlgebraicClosure k) {v : GroupPoints G (CommAlgCat.of k S)}
    {x y : RationalPoints ((groupBaseChange k (AlgebraicClosure k)).obj G)}
    (hx : IsGeometricImage f v x) (hy : IsGeometricImage f v y) : x = y :=
  (baseChangePointGroupEquiv (AlgebraicClosure k) G _).injective (hx.trans hy.symm)

private theorem geometric_image_value {G : GroupScheme k}
    (f : S →ₐ[k] AlgebraicClosure k) {v : GroupPoints G (CommAlgCat.of k S)}
    {x : RationalPoints ((groupBaseChange k (AlgebraicClosure k)).obj G)}
    (hx : IsGeometricImage f v x) :
    baseChangePointGroupEquiv (AlgebraicClosure k) G (CommAlgCat.of _ _) x =
      pointMap k S G.X f v := by
  apply Over.OverMorphism.ext
  exact congrArg Over.Hom.left hx

private theorem conjugacy_in_split_model
    {G H : AffineAlgebraicGroup k} (f : S →ₐ[k] AlgebraicClosure k)
    (e : relativePoints G.val (fieldTest k S) ≅ relativePoints H.val (fieldTest k S))
    (y : 𝟙_ (SchemeOver k) ⟶ H.val.X)
    (C : ClosedSubgroup (GeometricGroup H).val)
    (hC : IsPointCentralizer C (scalarExtendedRationalPoint (AlgebraicClosure k) y))
    (hT : IsTorus C.group)
    (hJ : let ybar : RationalPoints (GeometricGroup H).val :=
        toUnit _ ≫ scalarExtendedRationalPoint (AlgebraicClosure k) y
      IsRationalJordanDecomposition ⟨(GeometricGroup H).val, (GeometricGroup H).property.1⟩
        ybar ybar 1)
    (v : GroupPoints G.val (CommAlgCat.of k S))
    (hv : comparisonOnPoints e v =
      extendPoint (S := S) (toUnit (fieldTest k k) ≫ y : RationalPoints H.val))
    (x' y' : RationalPoints (GeometricGroup G).val)
    (hy' : IsGeometricImage f v y') (hxy : GeometricTraceFibre (GeometricGroup G) x' y') :
    ∃ g : RationalPoints (GeometricGroup G).val, g * x' * g⁻¹ = y' := by
  let L := AlgebraicClosure k
  let ybar : RationalPoints (GeometricGroup H).val :=
    toUnit _ ≫ scalarExtendedRationalPoint L y
  obtain ⟨_, j, _, _, _, hj⟩ := ExceptionalTwistedTraceComparison.geometricComparison f e
  let y₀ := scalarExtendedRationalPoint L y ≫ j.inv.hom.hom
  let p := pointHom j.hom
  let q := pointHom j.inv
  have hpy : p y' = ybar :=
    geometric_image_injective f (hj v y' hy') (hv ▸ geometric_image_rational_point f y)
  have hqp (z : RationalPoints (GeometricGroup G).val) : q (p z) = z := by
    change (z ≫ j.hom.hom.hom) ≫ j.inv.hom.hom = z
    rw [Category.assoc]
    exact congrArg (z ≫ ·) ((Grp.forget (SchemeOver L)).congr_map j.hom_inv_id) |>.trans
      (Category.comp_id z)
  have hy : y' = q ybar := (hqp y').symm.trans (congrArg q hpy)
  have hy₀ : y' = (toUnit _ ≫ y₀ : RationalPoints (GeometricGroup G).val) :=
    hy.trans (show (toUnit (fieldTest L L) ≫ scalarExtendedRationalPoint L y) ≫
      j.inv.hom.hom = _ from Category.assoc _ _ _)
  have hJ' := LinearAlgebraicGroups.Affine.rationalJordanDecompositionFunctorial
    (GeometricGroup H) (GeometricGroup G) j.inv hJ
  change IsRationalJordanDecomposition ⟨(GeometricGroup G).val, (GeometricGroup G).property.1⟩
    (q ybar) (q ybar) (q 1) at hJ'
  rw [← hy, map_one] at hJ'
  exact geometric_conjugacy_of_matching _ x' y' hxy hJ' (transportSubgroup j.symm C)
    y₀ hT (centralizer_transport j.symm hC) hy₀

private theorem conjugacy_in_reference
    {G H : GroupScheme k} (f : S →ₐ[k] AlgebraicClosure k)
    (e : relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S))
    {v w : GroupPoints G (CommAlgCat.of k S)}
    {x' y' : RationalPoints ((groupBaseChange k (AlgebraicClosure k)).obj G)}
    (hx' : IsGeometricImage f v x') (hy' : IsGeometricImage f w y')
    (g : RationalPoints ((groupBaseChange k (AlgebraicClosure k)).obj G))
    (hg : g * x' * g⁻¹ = y') :
    ∃ a : Descent.NonabelianCohomology.Points k (AlgebraicClosure k) H.X,
      a * pointMap k S H.X f (comparisonOnPoints e v) * a⁻¹ =
        pointMap k S H.X f (comparisonOnPoints e w) := by
  obtain ⟨_, j, _, _, _, hj⟩ := ExceptionalTwistedTraceComparison.geometricComparison f e
  let p := (baseChangePointGroupEquiv (AlgebraicClosure k) H (CommAlgCat.of _ _)).toMonoidHom.comp
    (pointHom j.hom)
  have hpv := geometric_image_value f (hj _ _ hx')
  have hpw := geometric_image_value f (hj _ _ hy')
  change p x' = _ at hpv
  change p y' = _ at hpw
  exact ⟨p g, by simpa only [map_mul, map_inv, hpv, hpw] using congrArg p hg⟩

open Specs.Pinning (PinnedGroup AttachedDatum)
open Specs.RootGroups (AdditiveLine)
open Specs.QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction)
open Specs.AutomorphismSequence (SplitSequence)

private theorem matching_twisted_point [Infinite k] [IsSepClosure k S]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    {E : SplitSequence P D l Q}
    {ω : Cocycle (trivialOuterAction (k := k) (S := S) D.toBased)}
    (V : PinnedRepresentative (S := S) E ω) (hV : IsExceptionalReference D)
    {Q₀ : AdjointQuotient V.model.val} {a : PointCocycle (S := S) Q₀.quotient.val}
    (T : Twist a) :
    ∃ (x : 𝟙_ (SchemeOver k) ⟶ V.model.val.val.X)
      (y : RationalPoints T.group.val) (b : Descent.NonabelianCohomology.Points k S V.model.val.val.X)
      (C : ClosedSubgroup V.model.val.val),
      IsTorus C.group ∧ IsPointCentralizer C x ∧
        b * (toUnit (fieldTest k S) ≫ x) * b⁻¹ =
          (comparisonOnPoints T.trivialization).symm (extendPoint (S := S) y) := by
  let G := V.model.val
  let H := T.group
  let L := AlgebraicClosure k
  let f : S →ₐ[k] L := IsAlgClosed.lift
  let : IsSepClosed S := IsSepClosure.sep_closed k
  obtain ⟨D₀, hD, ⟨_, hmax⟩, t, y, _, _, hcent, hJ⟩ :=
    RationalStronglyRegularElements.existsRationalStronglyRegularElement k H T.reductive
  let p : RationalPoints H.val := toUnit (fieldTest k k) ≫ y
  let z := (comparisonOnPoints T.trivialization).symm (extendPoint (S := S) p)
  let v := (comparisonOnPoints V.trivialization).symm z
  obtain ⟨_, _, M, hequiv, hmatch⟩ := matching_reference_point V hV v
  have htrace := ExceptionalTwistedTraceComparison.fixedTraceTuple V T p
    M.index M.representation hequiv
  obtain ⟨x, w, hx, hfib⟩ := hmatch htrace
  obtain ⟨x', y', hx', hy', hxy⟩ := hfib f
  let e := V.trivialization ≪≫ T.trivialization
  have hv : comparisonOnPoints e v = extendPoint (S := S) p := by
    change comparisonOnPoints T.trivialization (comparisonOnPoints V.trivialization v) = _
    rw [MulEquiv.apply_symm_apply]
    exact (comparisonOnPoints T.trivialization).apply_symm_apply _
  obtain ⟨hL, hCL⟩ := hcent L
  obtain ⟨g, hg⟩ := conjugacy_in_split_model f e y (scalarExtendedSubgroup L D₀ hL) hCL
    hmax.1 hJ v hv x' y' hy' hxy
  obtain ⟨g₀, hg₀⟩ := conjugacy_in_reference f V.trivialization hx' hy' g hg
  let x₀ := rationalSection x
  have hx₀ : extendPoint (S := S) x = (toUnit (fieldTest k S) ≫ x₀ :
      GroupPoints G.val (CommAlgCat.of k S)) := by
    rw [← extend_rational_point, toUnit_rationalSection]
  have hfconst : pointMap k S G.val.X f (toUnit (fieldTest k S) ≫ x₀) =
      toUnit (fieldTest k L) ≫ x₀ := by
    change (testSpec k).map (CommAlgCat.ofHom f).op ≫ toUnit (fieldTest k S) ≫ x₀ = _
    rw [← Category.assoc, comp_toUnit]
  have hg₁ : g₀ * (toUnit (fieldTest k L) ≫ x₀ : Descent.NonabelianCohomology.Points k L G.val.X) *
      g₀⁻¹ = pointMap k S G.val.X f z := by
    change extendPoint (S := S) x = _ at hx
    rw [← hx, hx₀, hfconst] at hg₀
    simpa only [v, MulEquiv.apply_symm_apply] using hg₀
  obtain ⟨i, _, hi, _, _, _⟩ :=
    ExceptionalTwistedTraceComparison.geometricComparison f T.trivialization
  obtain ⟨hS, hCS⟩ := hcent S
  let CS := scalarExtendedSubgroup S D₀ hS
  have htz : scalarExtendedRationalPoint S y = extendedPoint z ≫ i.hom.hom.hom := by
    rw [← extended_rational_point (S := S) y, ← extended_point_comparison hi]
    exact congrArg extendedPoint ((comparisonOnPoints T.trivialization).apply_symm_apply _).symm
  have hcz := centralizer_transport i.symm hCS
  have heq : scalarExtendedRationalPoint S y ≫ i.inv.hom.hom = extendedPoint z := by
    rw [htz, Category.assoc]
    exact congrArg (extendedPoint z ≫ ·) ((Grp.forget (SchemeOver S)).congr_map i.hom_inv_id)
      |>.trans (Category.comp_id _)
  rw [show i.symm.hom.hom.hom = i.inv.hom.hom from rfl, heq] at hcz
  have hs : IsSplitTorus (transportSubgroup i.symm CS).group :=
    split_torus_over_separably_closed (closedSubgroupAlgebraicGroup D₀) hD
  obtain ⟨⟨b, hb⟩, C₀, hC₀, hc⟩ := StronglyRegularSeparableTransporter.separableTransporter
    G V.reductive f x₀ z (transportSubgroup i.symm CS) hs hcz ⟨g₀, hg₁⟩
  exact ⟨x₀, p, b, C₀, hC₀, hc, hb⟩

end
end Transport

section Vanishing

open CategoryTheory.Limits
open Specs.ExceptionalTwistedTraceComparison (PointCocycle InnerMap Twist adjointAction
  projectionOnPoints)
open Specs.StronglyRegularSeparableTransporter (Fixes)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private isTorus_iff_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

variable {k S : Type u} [Field k] [Field S] [Algebra k S]

private def sectionHom {G H : GroupScheme k} (f : G ⟶ H) :
    Descent.NonabelianCohomology.Points k S G.X →*
      Descent.NonabelianCohomology.Points k S H.X :=
  IsMonHom.monoidHom f.hom.hom (fieldTest k S)

private theorem sectionHom_equivariant {G H : GroupScheme k} (f : G ⟶ H)
    (σ : Gal(S/k)) (z : Descent.NonabelianCohomology.Points k S G.X) :
    sectionHom f (pointAction k S G.X σ z) =
      pointAction k S H.X σ (sectionHom f z) := by
  change (fieldMap k S σ ≫ z) ≫ f.hom.hom = fieldMap k S σ ≫ z ≫ f.hom.hom
  exact Category.assoc _ _ _

private theorem constant_fixed {G : GroupScheme k} (x : 𝟙_ (SchemeOver k) ⟶ G.X)
    (σ : Gal(S/k)) :
    pointAction k S G.X σ (toUnit (fieldTest k S) ≫ x) = toUnit (fieldTest k S) ≫ x := by
  change fieldMap k S σ ≫ toUnit (fieldTest k S) ≫ x = _
  rw [← Category.assoc, comp_toUnit]

private theorem torus_embedding (G : AffineAlgebraicGroup k) (C : ClosedSubgroup G.val)
    (hC : IsTorus C.group)
    (p : Descent.NonabelianCohomology.Points k S C.group.X →*
      Descent.NonabelianCohomology.Points k S G.val.X)
    (hp : Function.Injective p)
    (heq : ∀ σ z, p (pointAction k S C.group.X σ z) = pointAction k S G.val.X σ (p z)) :
    ∃ (B : HopfAlgebraCategory k) (_ : CharacterDescent.IsTorus B)
      (q : Descent.NonabelianCohomology.Points k S (specGroup B).X →*
        Descent.NonabelianCohomology.Points k S G.val.X),
      Function.Injective q ∧
      (∀ σ z, q (pointAction k S (specGroup B).X σ z) = pointAction k S G.val.X σ (q z)) ∧
      q.range = p.range := by
  obtain ⟨B, ⟨e⟩, hB⟩ := (isTorus_iff_coordinates (closedSubgroupAlgebraicGroup (G := G) C)).mp hC
  change specGroup B ≅ C.group at e
  let φ : Descent.NonabelianCohomology.Points k S (specGroup B).X ≃*
      Descent.NonabelianCohomology.Points k S C.group.X :=
    (((yonedaGrp.mapIso e).app (op (fieldTest k S)))).groupIsoToMulEquiv
  let q := p.comp (sectionHom e.hom)
  have hφ (z : Descent.NonabelianCohomology.Points k S (specGroup B).X) :
      sectionHom e.hom z = φ z := rfl
  refine ⟨B, hB, q, hp.comp (show Function.Injective (sectionHom e.hom) from φ.injective),
    ?_, ?_⟩
  · intro σ z
    change p (sectionHom e.hom (pointAction k S (specGroup B).X σ z)) =
      pointAction k S G.val.X σ (p (sectionHom e.hom z))
    rw [sectionHom_equivariant, heq]
  · ext z
    change (∃ t, p (sectionHom e.hom t) = z) ↔ ∃ t, p t = z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨t, rfl⟩
      obtain ⟨s, hs⟩ := φ.surjective t
      exact ⟨s, congrArg p ((hφ s).trans hs)⟩

private def adjointActionHom {G : AffineAlgebraicGroup k} {Q : AdjointQuotient G} (inn : InnerMap Q) :
    Descent.NonabelianCohomology.Points k S Q.quotient.val.X →*
      MulAut (Descent.NonabelianCohomology.Points k S G.val.X) where
  toFun := adjointAction inn
  map_one' := by
    unfold adjointAction
    rw [show (⟨(1 : GroupPoints Q.quotient.val (CommAlgCat.of k S))⟩ :
        (groupSections Q.quotient.val).obj (op (fieldTest k S))) = 1 from rfl, map_one]
    ext z
    rfl
  map_mul' q r := by
    unfold adjointAction
    rw [show (⟨q * r⟩ : (groupSections Q.quotient.val).obj (op (fieldTest k S))) =
        ⟨q⟩ * ⟨r⟩ from rfl, map_mul]
    ext z
    rfl

open private adjoint_action_extends_points inner_conjugation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalTwistedTraceComparison

private theorem adjointAction_equivariant {G : AffineAlgebraicGroup k} {Q : AdjointQuotient G}
    (inn : InnerMap Q) (σ : Gal(S/k)) (q : GroupPoints Q.quotient.val (CommAlgCat.of k S))
    (z : GroupPoints G.val (CommAlgCat.of k S)) :
    adjointActionHom inn (pointAction k S Q.quotient.val.X σ q) (pointAction k S G.val.X σ z) =
      pointAction k S G.val.X σ (adjointActionHom inn q z) :=
  (adjoint_action_extends_points inn (CommAlgCat.ofHom σ.toAlgHom) q z).symm

/-- Every cocycle of the simply connected quasi-split reference is neutral. -/
theorem simply_connected_vanishing : SimplyConnectedVanishing.{u} := by
  intro F _ _ _ _ K S _ _ _ A P D l Q E ω V hV
  let G := V.model.val
  let : Infinite K := maximal_unramified_infinite F
  apply vanishing_of_torus_subgroups F G
  intro a
  obtain ⟨Q₀⟩ := Descent.AutomorphismSequence.adjointQuotient_exists G
  obtain ⟨d, H, _, hfix⟩ := ExceptionalTwistedTraceComparison.simplyConnectedTwisting
    G V.reductive Q₀ a
  obtain ⟨x, y, b, C, hC, hCx, hb⟩ := matching_twisted_point V hV H
  let p := sectionHom (S := S) C.inclusion
  have hp : Function.Injective p := by
    let : IsClosedImmersion C.inclusion.hom.hom.left := C.isClosedImmersion
    let : Mono C.inclusion.hom.hom := Over.mono_of_mono_left _
    intro z w h
    exact (cancel_mono C.inclusion.hom.hom).mp h
  obtain ⟨B, hB, q, hq, hσ, hrange⟩ := torus_embedding G C hC p hp
    (sectionHom_equivariant C.inclusion)
  refine ⟨B, hB, q, hq, hσ, b, fun σ ↦ ?_⟩
  let r := pointAction K S G.val.X
  let : TopologicalSpace (Descent.NonabelianCohomology.Points K S G.val.X) := ⊥
  change Cocycle r at a
  let xS : Descent.NonabelianCohomology.Points K S G.val.X := toUnit (fieldTest K S) ≫ x
  let z : Descent.NonabelianCohomology.Points K S G.val.X :=
    (comparisonOnPoints H.trivialization).symm
      (Specs.ExceptionalTwistedTraceComparison.extendPoint (S := S) y)
  have ha := changed_cocycle_fixes (ρ := r) MulAut.conj r
    (fun τ m v ↦ by simp only [MulAut.conj_apply, map_mul, map_inv])
    a b xS z (constant_fixed x)
    (fun τ ↦ hfix y τ) hb σ
  change b⁻¹ * a σ * r σ b * xS * (b⁻¹ * a σ * r σ b)⁻¹ = xS at ha
  rw [mul_inv_eq_iff_eq_mul] at ha
  change b⁻¹ * a σ * r σ b ∈ q.range
  rw [hrange]
  exact (hCx (fieldTest K S) _).mp ha

private theorem adjoint_cocycle_fixes
    {G : AffineAlgebraicGroup k} {Q : AdjointQuotient G}
    {a : PointCocycle (S := S) Q.quotient.val} (H : Twist a)
    (x : 𝟙_ (SchemeOver k) ⟶ G.val.X) (y : RationalPoints H.group.val)
    (b : Descent.NonabelianCohomology.Points k S G.val.X)
    (hb : b * (toUnit (fieldTest k S) ≫ x) * b⁻¹ =
      (comparisonOnPoints H.trivialization).symm
        (Specs.ExceptionalTwistedTraceComparison.extendPoint (S := S) y))
    (σ : Gal(S/k)) :
    let c : Descent.NonabelianCohomology.Points k S Q.quotient.val.X := projectionOnPoints Q b
    let d : Descent.NonabelianCohomology.Points k S Q.quotient.val.X := a.val σ
    Fixes H.inner x (c⁻¹ * d * pointAction k S Q.quotient.val.X σ c) := by
  dsimp only
  let : TopologicalSpace (Gal(S/k)) := krullTopology k S
  let : TopologicalSpace (Descent.NonabelianCohomology.Points k S Q.quotient.val.X) := ⊥
  let r := pointAction k S Q.quotient.val.X
  let s := pointAction k S G.val.X
  let c : Descent.NonabelianCohomology.Points k S Q.quotient.val.X := projectionOnPoints Q b
  let xS : Descent.NonabelianCohomology.Points k S G.val.X := toUnit (fieldTest k S) ≫ x
  let z : Descent.NonabelianCohomology.Points k S G.val.X := (comparisonOnPoints H.trivialization).symm
    (Specs.ExceptionalTwistedTraceComparison.extendPoint (S := S) y)
  have hc : adjointActionHom H.inner c xS = z := (inner_conjugation H.onLift b xS).trans hb
  have hfix := changed_cocycle_fixes (ρ := r) (adjointActionHom H.inner) s
    (adjointAction_equivariant H.inner) a c xS z (constant_fixed x)
    (fun τ ↦ H.fixed y τ) hc σ
  exact hfix

set_option maxHeartbeats 1200000 in
/-- Every cocycle of the full adjoint quotient reduces to the torus
stabilizer of a strongly regular element. -/
theorem adjoint_vanishing : AdjointVanishing.{u} := by
  intro F _ _ _ _ K S _ _ _ A P D l Q E ω V hV Q₀
  let G := V.model.val
  let : Infinite K := maximal_unramified_infinite F
  apply vanishing_of_torus_subgroups F (S := S) Q₀.quotient
  intro a
  obtain ⟨H⟩ := ExceptionalTwistedTraceComparison.adjointTwisting G V.reductive Q₀ a
  obtain ⟨x, y, b, C, hC, hCx, hb⟩ := matching_twisted_point V hV H
  obtain ⟨U, hU, _, p, _, hp, hσ, hpfix⟩ :=
    StronglyRegularSeparableTransporter.adjointTorusStabilizer
      (S := S) G V.reductive x C hC hCx Q₀ H.inner H.onLift
  obtain ⟨B, hB, q, hq, hqσ, hrange⟩ := torus_embedding Q₀.quotient U hU p hp hσ
  refine ⟨B, hB, q, hq, hqσ, projectionOnPoints Q₀ b, fun σ ↦ ?_⟩
  rw [hrange, hpfix]
  exact adjoint_cocycle_fixes H x y b hb σ

theorem inner_forms_are_reference : InnerFormsAreReference.{u} :=
  inner_forms_are_reference_of_adjoint_vanishing adjoint_vanishing

end
end Vanishing

end LinearAlgebraicGroups.Arithmetic.ExceptionalFormsOverUnramifiedFields
