import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SteinbergGeometricFibres
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.CharacterRing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalJordanFactors
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.TorusSections
import Mathlib.RingTheory.Filtration
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.CartesianMonoidalCategory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u v w

namespace LinearAlgebraicGroups.Arithmetic.SteinbergGeometricFibres

open _root_.LinearAlgebraicGroups.Specs
open Specs.SteinbergGeometricFibres
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (characterValue)
open Specs.RootWeightAction (Representation weightSpace mem_weightSpace)
open Specs.FormalCharacters (formalCharacter)
open Specs.CharacterRing (invariantRing)
open _root_.LinearAlgebraicGroups.Affine (RationalPoints)
open Module

noncomputable section

open private internalWeights characterOfBasis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FormalCharacters

theorem torusTrace : TorusTrace.{u} := by
  classical
  intro k I _ _ _ G T hs _ ρ t z hz
  let A := fun χ => weightSpace ρ T χ
  let h := internalWeights T hs ρ
  let b := h.collectedBasis (fun χ => Module.finBasis k (A χ))
  let := FiniteDimensional.fintypeBasisIndex b
  have hb (j : Σ χ, Fin (Module.finrank k (A χ))) : b j ∈ A j.1 :=
    h.collectedBasis_mem _ j
  rw [characterOfBasis T hs ρ b Sigma.fst hb, map_sum]
  let K := CommAlgCat.of k k
  let M : Matrix I I k := (ρ.app K (t ≫ T.inclusion.hom.hom)).val
  change M.trace = _
  rw [← LinearMap.toMatrix'_toLin' M, ← LinearMap.toMatrix_eq_toMatrix',
    ← LinearMap.trace_eq_matrix_trace, LinearMap.trace_eq_matrix_trace k b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hev := (mem_weightSpace.mp (hb j)) K t
  have hv (v : I → k) : Specs.RootWeightAction.extendVector K v = v := by
    ext i
    exact Algebra.algebraMap_self_apply (v i)
  rw [hv] at hev
  change M.mulVec (b j) = _ at hev
  rw [Matrix.toLin'_apply, hev, map_smul, Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one,
    integralEvaluation, MonoidAlgebra.liftNCRingHom_single]
  simpa using (hz j.1).symm

theorem jordanTrace : JordanTrace.{u} := by
  classical
  intro k I _ _ _ G ρ g s v h
  let H := StandardGroups.generalLinearGroup k I
  let L := H.val
  let l : (groupPointsFunctor k).obj L ≅ Specs.StandardGroups.generalLinearPoints k I :=
    StandardGroups.generalLinearGroupPointsIso k I
  let f : G.val ⟶ L := (AffineAlgebraicGroup.groupHomEquiv G H).symm (ρ ≫ l.inv)
  have hf : (groupPointsFunctor k).map f ≫ l.hom = ρ := by
    rw [show (groupPointsFunctor k).map f = ρ ≫ l.inv from
      (AffineAlgebraicGroup.groupHomEquiv G H).apply_symm_apply _]
    simp
  let b := Pi.basisFun k I
  have ha (x : RationalPoints G.val) :
      Affine.rationalRepresentationAction (G := ⟨G.val, G.property.1⟩) b l f x =
        Matrix.toLin' (ρ.app (CommAlgCat.of k k) x).val := by
    unfold Affine.rationalRepresentationAction
    rw [Matrix.toLin_eq_toLin']
    exact congrArg (fun φ : Representation G.val I =>
      Matrix.toLin' (φ.app (CommAlgCat.of k k) x).val) hf
  have hj := h.2.2 b L l f
  have ht (x : RationalPoints G.val) : pointTrace ρ x =
      LinearMap.trace k (I → k) (Affine.rationalRepresentationAction (G := ⟨G.val, G.property.1⟩) b l f x) := by
    rw [ha, LinearMap.trace_eq_matrix_trace k b]
    change _ = Matrix.trace (LinearMap.toMatrix' (Matrix.toLin' _))
    rw [LinearMap.toMatrix'_toLin']
    rfl
  rw [ht, ht, hj.eq_mul]
  rw [Module.End.mul_eq_comp]
  simpa using LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent 1 hj.commute
    (by simpa using hj.unipotent)

theorem integralEvaluationAgreement : IntegralEvaluationAgreement := by
  intro k X W J _ _ _ a character z z' hgen heq f hf
  have hle : Subring.closure (Set.range character) ≤
      (integralEvaluation z).eqLocus (integralEvaluation z') := by
    rw [Subring.closure_le]
    rintro _ ⟨j, rfl⟩
    exact heq j
  exact hle (hgen ▸ hf)

open private orbitCoordinates triangular_bijective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.CharacterRing

section HighestTerm

variable {X : Type*} [CommGroup X] (degree : X →* Multiplicative ℤ)

private theorem highestTerm_one : HasHighestTerm degree (1 : MonoidAlgebra ℤ X) 1 := by
  classical
  refine ⟨MonoidAlgebra.coeff_one_one, ?_⟩
  intro y hy hn
  exact (hn (by simp [MonoidAlgebra.one_def, Ne.symm hy])).elim

private theorem highestTerm_mul {p q : MonoidAlgebra ℤ X} {x y : X}
    (hp : HasHighestTerm degree p x) (hq : HasHighestTerm degree q y) :
    HasHighestTerm degree (p * q) (x * y) := by
  classical
  have bound {f : MonoidAlgebra ℤ X} {a b : X} (ha : HasHighestTerm degree f a)
      (hb : f.coeff b ≠ 0) : (degree b).toAdd ≤ (degree a).toAdd := by
    by_cases he : b = a
    · simp [he]
    · exact (ha.2 b he hb).le
  have addDegree (a b : X) :
      (degree (a * b)).toAdd = (degree a).toAdd + (degree b).toAdd := by
    rw [map_mul]
    rfl
  have hx : x ∈ p.coeff.support := Finsupp.mem_support_iff.mpr (by simp [hp.1])
  constructor
  · rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum,
      Finset.sum_eq_single_of_mem x hx]
    · simp [hp.1, hq.1]
    · intro a ha hax
      have ha' := hp.2 a hax (Finsupp.mem_support_iff.mp ha)
      suffices hz : q.coeff (a⁻¹ * (x * y)) = 0 by simp [hz]
      by_contra hne
      have hy := bound hq hne
      have hsum := addDegree a (a⁻¹ * (x * y))
      rw [mul_inv_cancel_left, addDegree] at hsum
      omega
  · intro b hne hn
    rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum] at hn
    obtain ⟨a, ha, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    have hp' := Finsupp.mem_support_iff.mp ha
    have hq' : q.coeff (a⁻¹ * b) ≠ 0 := fun h => hv (by simp [h])
    have hsum := addDegree a (a⁻¹ * b)
    rw [mul_inv_cancel_left] at hsum
    rw [addDegree]
    have ha' := bound hp hp'
    have hb' := bound hq hq'
    by_cases he : a = x
    · have hc : a⁻¹ * b ≠ y := by
        intro hh
        apply hne
        rw [← he, ← hh, mul_inv_cancel_left]
      have := hq.2 _ hc hq'
      omega
    · have := hp.2 _ he hp'
      omega

private theorem highestTerm_pow {p : MonoidAlgebra ℤ X} {x : X}
    (hp : HasHighestTerm degree p x) (n : ℕ) :
    HasHighestTerm degree (p ^ n) (x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using highestTerm_one degree
  | succ n ih => simpa only [pow_succ] using highestTerm_mul degree ih hp

private theorem highestTerm_prod {J : Type*}
    {p : J → MonoidAlgebra ℤ X} {x : J → X} (s : Finset J)
    (h : ∀ j ∈ s, HasHighestTerm degree (p j) (x j)) :
    HasHighestTerm degree (∏ j ∈ s, p j) (∏ j ∈ s, x j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using highestTerm_one degree
  | @insert j s hj ih =>
    simpa only [Finset.prod_insert hj] using
      highestTerm_mul degree (h j (Finset.mem_insert_self j s))
        (ih (fun l hl => h l (Finset.mem_insert_of_mem hl)))

end HighestTerm

theorem integralGeneration : IntegralGeneration := by
  classical
  intro X W A J _ _ _ _ a i degree weight character hex huniq hnonneg
    hweights hchar htop
  let C := Subring.closure (Set.range character)
  have hC : C ≤ invariantRing a :=
    Subring.closure_le.mpr (by rintro _ ⟨j, rfl⟩; exact hchar j)
  choose m hm using hweights
  let F (j : A) : MonoidAlgebra ℤ X := ∏ r, character r ^ m j r
  have hF (j : A) : F j ∈ C :=
    C.prod_mem (fun r _ => C.pow_mem (Subring.subset_closure ⟨r, rfl⟩) _)
  let f (j : A) : invariantRing a := ⟨F j, hC (hF j)⟩
  have htopF (j : A) : HasHighestTerm degree (F j) (i j) := by
    rw [hm j]
    exact highestTerm_prod degree Finset.univ (fun r _ =>
      highestTerm_pow degree (htop r) (m j r))
  let o := orbitCoordinates a i hex huniq
  let row (j : A) := o (f j)
  have he (j l : A) : row j l = (F j).coeff (i l) := rfl
  let height (j : A) := (degree (i j)).toAdd.toNat
  have hb := (triangular_bijective height row (fun j => (he j j).trans (htopF j).1)
    (fun j l hne hz => by
      have hh := (htopF j).2 (i l) (fun h => hne (i.injective h).symm) ((he j l) ▸ hz)
      exact (Int.toNat_lt_toNat ((hnonneg l).trans_lt hh)).mpr hh)).2
  apply le_antisymm hC
  intro p hp
  obtain ⟨v, hv⟩ := hb (o ⟨p, hp⟩)
  have hv' : Finsupp.linearCombination ℤ f v = ⟨p, hp⟩ := by
    apply o.injective
    rw [← hv]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, row]
  have hsum : (∑ j ∈ v.support, v j • F j) = p := by
    let coe := (invariantRing a).subtype.toAddMonoidHom.toIntLinearMap
    have h := congrArg coe hv'
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum] at h
    simp only [map_smul] at h
    change (∑ j ∈ v.support, v j • F j) = p at h
    exact h
  rw [← hsum]
  exact C.sum_mem (fun j _ => C.zsmul_mem (hF j) (v j))

theorem traceConjugation : TraceConjugation.{u} := by
  intro k I _ _ _ G ρ h g
  let φ : RationalPoints G →* (Matrix I I k)ˣ := (ρ.app (CommAlgCat.of k k)).hom
  change (φ (h * g * h⁻¹)).val.trace = (φ g).val.trace
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
  exact Matrix.trace_units_conj _ _

section FundamentalCharacters

open Specs.AbstractPairing (Datum Root)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.CharacterRing (dominantWeights weylAction)
open Specs.DominantOrder (twoRhoCoroot IsBaseFor)
open Specs.FlagLineBundle (OppositeBorelPair)
open Specs.RootWeightAction (SimpleRoot)
open Specs.SimpleClassification (SocleModel)
open Specs.SimpleRoots (evaluate)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private dominant_base_iff dominant_orbits restrictedCharacter
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.CharacterRing
open private baseSimpleRoot from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.ParabolicLineWeights
open private coefficientFormula from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FormalCharacters
open private generates_of_simple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.PrimitiveLine
open private coordinateIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SimpleClassification
open private pointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.InducedSocle

private theorem fundamentalCoordinateEquiv {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing I ℤ X Y) (b : P.Base)
    (hspan : Submodule.span ℤ (Set.range P.coroot) = ⊤) :
    ∃ e : X ≃ₗ[ℤ] (b.support → ℤ), ∀ x i, e x i = P.toLinearMap x (P.coroot i.val) := by
  classical
  let corootBasis : Module.Basis b.support ℤ Y :=
    Module.Basis.mk b.linearIndepOn_coroot (ge_of_eq (by
      rw [← Set.image_eq_range, b.span_int_coroot_support, hspan]))
  refine ⟨P.toLinearMap.toPerfPair.trans corootBasis.dualBasis.equivFun, ?_⟩
  intro x i
  change corootBasis.dualBasis.equivFun (P.toLinearMap x) i = _
  rw [Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr]
  congr 1
  exact Module.Basis.mk_apply _ _ _

theorem fundamentalGeneration : FundamentalGeneration.{u} := by
  classical
  intro k _ G P hG hsc
  obtain ⟨comm, D, ⟨e⟩, order⟩ := Representation.DominantOrder.dominantOrder
    G P.reductive P.torus P.split P.maximal
  let := comm
  let := D.finiteRoots
  let := D.freeCharacters
  let := D.finiteCharacters
  let := D.reduced
  let := e.image.finite
  let _ : Finite D.rootDatum.weylGroup := Finite.of_injective e.labelEquiv e.labelEquiv.injective
  obtain ⟨_, _, _, borels, _, _, radicals⟩ :=
    RootData.BorelPositivity.borelPositivity G P.reductive P.torus P.split P.maximal
  obtain ⟨U, _, _, hU, _⟩ := radicals P.positive P.positiveBorel P.inPositive
  obtain ⟨c, _, hc, _, hp⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT
      G P.reductive P.torus P.split P.maximal).1 P.positive P.positiveBorel P.inPositive
  have hreg (α : Root P.torus) : evaluate D c (D.rootDatum.root α) ≠ 0 := by
    change D.rootDatum.toLinearMap (D.rootDatum.root α) (Additive.ofMul c) ≠ 0
    rw [D.root_eq, D.pairing_eq]
    exact hc α
  obtain ⟨b, hb⟩ := RootData.SimpleRoots.baseFor D.rootDatum (evaluate D c) hreg
  let positives := subgroupRoots P.torus P.positive
  have hb' : IsBaseFor D.rootDatum positives b := by
    intro α
    change b.IsPos α ↔ α ∈ subgroupRoots P.torus P.positive
    rw [hb.positive_iff, hp]
    change 0 < D.rootDatum.toLinearMap (D.rootDatum.root α) (Additive.ofMul c) ↔ _
    rw [D.root_eq, D.pairing_eq]
    rfl
  have laws := (order positives (borels.1 P.positive P.positiveBorel P.inPositive)).2 b hb'
  have simple (α : Root P.torus) : α ∈ b.support ↔
      ∃ x : SimpleRoot P.torus P.positive, x.val = α := baseSimpleRoot hp.symm hb α
  have hdom := dominant_base_iff P D b simple
  obtain ⟨hex, hu⟩ := dominant_orbits P e b hdom laws.orbitRepresentative
  have hspan := (Classification.SimplyConnectedLattice.latticeCriterion
    G hG P.torus P.split P.maximal D).mp hsc
  obtain ⟨coords, hcoords⟩ := fundamentalCoordinateEquiv D.rootDatum b hspan
  let ω (i : b.support) : Character P.torus.group :=
    Additive.toMul (coords.symm (Pi.single i 1))
  have hw (i j : b.support) : D.rootDatum.toLinearMap (Additive.ofMul (ω i))
      (D.rootDatum.coroot j.val) = if i = j then 1 else 0 := by
    rw [← hcoords]
    simp [ω, Pi.single_apply, eq_comm]
  have hd (i : b.support) : InducedNonvanishing.Dominant P (ω i) := by
    apply (hdom _).mpr
    intro j hj
    have := hw i ⟨j, hj⟩
    exact this ▸ (by split <;> decide)
  obtain ⟨_, _, models⟩ := Representation.SimpleClassification.classification G P U hU
  choose S _ using fun j => models (ω j) (hd j)
  refine ⟨comm, D, e, b, U, hb', hU, ω, S, hw, hex, hu, ?_⟩
  let i : dominantWeights P ↪ Character P.torus.group := ⟨Subtype.val, Subtype.val_injective⟩
  let height : Additive (Character P.torus.group) →ₗ[ℤ] ℤ :=
    D.rootDatum.toLinearMap.flip (twoRhoCoroot D.rootDatum positives)
  let degree : Character P.torus.group →* Multiplicative ℤ :=
    height.toAddMonoidHom.toMultiplicative
  let χ (j : b.support) := formalCharacter P.torus (S j).socleAction
  apply integralGeneration (weylAction e) i degree ω χ hex hu
  · intro j
    exact laws.nonnegative _ ((hdom _).mp j.property)
  · intro j
    let m (r : b.support) := (coords (Additive.ofMul j.val) r).toNat
    refine ⟨m, Additive.ofMul.injective (coords.injective ?_)⟩
    ext r
    have hn : 0 ≤ coords (Additive.ofMul j.val) r := by
      rw [hcoords]
      exact (hdom _).mp j.property r.val r.property
    have he (s : b.support) : coords (Additive.ofMul (ω s)) r = if s = r then 1 else 0 :=
      (hcoords _ _).trans (hw s r)
    rw [ofMul_prod]
    simp only [ofMul_pow, map_sum, map_nsmul, Finset.sum_apply, Pi.smul_apply, he]
    simp [m, i, max_eq_left hn]
  · intro j
    exact (restrictedCharacter P.split e (Specs.CharacterRing.simpleRep (S j))).property
  · intro j
    have coeff := (coefficientFormula P.torus P.split (S j).socleAction).2
    refine ⟨?_, ?_⟩
    · rw [show (χ j).coeff (ω j) = _ from coeff (ω j),
        Specs.FormalCharacters.multiplicity, (S j).highestLine,
        finrank_span_singleton (S j).primitive.1]
      rfl
    · intro wt hne hn
      obtain ⟨comm', D', hhigh⟩ := Representation.CyclicHighestWeight.cyclicHighestWeight.2
        G P.reductive P.torus P.positive P.split P.maximal P.positiveBorel P.inPositive
      let V := S j
      have hgen := generates_of_simple Representation.CyclicHighestWeight.cyclicHighestWeight.1
        V.socleAction _ (pointIso (coordinateIso G)) V.simple V.primitive.1
      have htop := ((hhigh U hU V.socleAction (ω j) _ V.primitive).2 hgen).2.1
      have hweight : weightSpace V.socleAction P.torus wt ≠ ⊥ := by
        intro hz
        exact hn (by rw [coeff, Specs.FormalCharacters.multiplicity, hz, finrank_bot]; rfl)
      obtain ⟨d, hd⟩ := htop wt hne hweight
      have hsupport : d.support.Nonempty := by
        apply Finsupp.support_nonempty_iff.mpr
        intro hz
        subst d
        apply hne
        change Additive.ofMul (ω j / wt) = 0 at hd
        exact (div_eq_one.mp (congrArg Additive.toMul hd)).symm
      change Additive.ofMul (ω j) - Additive.ofMul wt = _ at hd
      have hei := congrArg height hd
      have hs (α : SimpleRoot P.torus P.positive) :
          height (Additive.ofMul α.val.val) = 2 := by
        change D.rootDatum.toLinearMap (Additive.ofMul α.val.val) _ = 2
        rw [← D.root_eq]
        exact laws.simplePairing α.val ((simple α.val).mpr ⟨α, rfl⟩)
      simp only [map_sub, Finsupp.sum, map_sum, map_nsmul, hs] at hei
      have hpos : 0 < ∑ r ∈ d.support, d r • (2 : ℤ) :=
        Finset.sum_pos (fun r hr => by
          have h := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hr)
          rw [nsmul_eq_mul]
          positivity) hsupport
      change height (Additive.ofMul wt) < height (Additive.ofMul (ω j))
      omega

end FundamentalCharacters

section CoefficientChange

open Specs.CharacterRing (orbitSum)
open private invariantOrbitSum coeff_orbitSum from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.CharacterRing

private theorem eval_coefficientCast {k X : Type*} [Field k] [CommGroup X] (z : X →* kˣ) :
    (fieldEvaluation z).comp (MonoidAlgebra.mapRingHom X (Int.castRingHom k)) =
      integralEvaluation z := by
  apply MonoidAlgebra.ringHom_ext
  · intro n
    simp [fieldEvaluation, integralEvaluation, MonoidAlgebra.liftNCRingHom_single]
  · intro x
    simp [fieldEvaluation, integralEvaluation, MonoidAlgebra.liftNCRingHom_single]

theorem integralOrbitSeparation : IntegralOrbitSeparation.{u,v,w} := by
  classical
  intro separate k X W A _ _ _ _ a i z z' hex hu agree
  let := Fintype.ofFinite W
  by_contra! hn
  obtain ⟨f, hf, hz, hz'⟩ := separate a z z' hn
  let cast : MonoidAlgebra ℤ X →+* MonoidAlgebra k X :=
    MonoidAlgebra.mapRingHom X (Int.castRingHom k)
  let orbit (j : A) : MonoidAlgebra k X := cast (orbitSum a (i j))
  have he (j : A) : fieldEvaluation z (orbit j) = fieldEvaluation z' (orbit j) := by
    have hh := agree (orbitSum a (i j)) (invariantOrbitSum a (i j)).property
    change ((fieldEvaluation z).comp cast) (orbitSum a (i j)) =
      ((fieldEvaluation z').comp cast) (orbitSum a (i j))
    simpa only [cast, eval_coefficientCast] using hh
  let c : A →₀ k := Finsupp.lcomapDomain (R := k) i i.injective f.coeff
  have expansion : f = ∑ j ∈ c.support, MonoidAlgebra.single 1 (c j) * orbit j := by
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro x
    obtain ⟨j, w, hw⟩ := hex x
    have hc : c j = f.coeff x := by
      change f.coeff (i j) = f.coeff x
      have h := congrArg (fun g : MonoidAlgebra k X => g.coeff (i j)) (hf w)
      simpa [← hw, Finsupp.equivMapDomain_apply] using h.symm
    have horb (l : A) : (orbit l).coeff x = if l = j then 1 else 0 := by
      have ht : (∃ v, a v (i l) = x) ↔ l = j := by
        rw [← hu l j, ← hw]
        constructor
        · rintro ⟨v, hv⟩
          exact ⟨w * v, by simp [hv]⟩
        · rintro ⟨v, hv⟩
          refine ⟨w⁻¹ * v, ?_⟩
          rw [map_mul]
          change a w⁻¹ (a v (i l)) = x
          rw [hv, map_inv]
          exact (a w).symm_apply_apply x
      change (cast (orbitSum a (i l))).coeff x = _
      rw [MonoidAlgebra.coeff_mapRingHom, coeff_orbitSum, ht]
      split <;> simp
    simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      MonoidAlgebra.coeff_single_mul_apply, inv_one, one_mul, horb]
    rw [Finset.sum_eq_single j]
    · simpa using hc.symm
    · intro l _ hlj
      simp [hlj]
    · intro hj
      have hzero : c j = 0 := Finsupp.notMem_support_iff.mp hj
      simp [hzero]
  have eq : fieldEvaluation z f = fieldEvaluation z' f := by
    rw [expansion]
    simp [fieldEvaluation, MonoidAlgebra.liftNCRingHom_single,
      show ∀ j, (MonoidAlgebra.liftNCRingHom (RingHom.id k) ((Units.coeHom k).comp z)
        (fun _ _ => Commute.all _ _)) (orbit j) =
        (MonoidAlgebra.liftNCRingHom (RingHom.id k) ((Units.coeHom k).comp z')
          (fun _ _ => Commute.all _ _)) (orbit j) from he]
  rw [hz, hz'] at eq
  exact zero_ne_one eq

end CoefficientChange

section TorusPoints

open Specs.CharacterRing (weylAction)
open Specs.DiagonalizableGroups (groupAlgebra)
open private splitPresentation charactersOfIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private splitCharacterValue splitPointPresentation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FormalCharacters
open private fibreTorsor splitFibrePoint from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
open private comp_conjugateFamily from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

theorem torusPointCoordinates : TorusPointCoordinates.{u} := by
  intro k _ T hT
  classical
  let K := CommAlgCat.of k k
  obtain ⟨r, ⟨s⟩⟩ := splitPresentation hT
  let M := CharacterDescent.StandardLattice.{u} r
  obtain ⟨χ, _, hχ, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing
    (k := k) r
  let e := χ.trans (charactersOfIso s)
  choose f hf using fun t : RationalPoints T => splitPointPresentation s K t
  let z (t : RationalPoints T) : Character T →* kˣ :=
    (((f t).toMonoidHom.comp (MonoidAlgebra.of k M)).toHomUnits).comp e.symm.toMonoidHom
  have hz (t : RationalPoints T) (c : Character T) :
      (z t c : k) = characterValue c K t := by
    change (f t) (MonoidAlgebra.of k M (e.symm c)) = _
    have h := splitCharacterValue s χ hχ (e.symm c) K (f t)
    rw [show (χ.trans (charactersOfIso s)) (e.symm c) = c from e.apply_symm_apply c, hf t] at h
    exact h.symm
  refine ⟨z, ?_, hz⟩
  intro t t' ht
  have he : f t = f t' := by
    apply MonoidAlgebra.algHom_ext
    · intro m
      have h := congrArg (fun ψ : Character T →* kˣ => (ψ (e m) : k)) ht
      change (f t) (MonoidAlgebra.single m 1) = (f t') (MonoidAlgebra.single m 1)
      change (f t) (MonoidAlgebra.of k M (e.symm (e m))) =
        (f t') (MonoidAlgebra.of k M (e.symm (e m))) at h
      rw [e.symm_apply_apply] at h
      exact h
    · ext
  rw [← hf t, ← hf t', he]

theorem torusWeylConjugation : TorusWeylConjugation.{u} := by
  intro k _ G T hT _ D e w t t' ht
  let K := CommAlgCat.of k k
  let a := e.image.conjugation (e.labelEquiv w)
  let t'' : RationalPoints T.group := t ≫ a.inv.hom.hom
  have hval (c : Character T.group) :
      characterValue c K t'' = characterValue (weylAction e w c) K t := by
    have hact : weylAction e w c = a.inv ≫ c := e.image.characterAction _ _
    have eq : t'' ≫ c.hom.hom = t ≫ (a.inv ≫ c).hom.hom :=
      Category.assoc t a.inv.hom.hom c.hom.hom
    unfold characterValue
    rw [hact, eq]
  obtain ⟨z, hz, he⟩ := torusPointCoordinates hT
  have ht' : t' = t'' := by
    apply hz
    ext c
    exact (he t' c).trans ((ht c).trans ((hval c).symm.trans ((he t'' c).symm)))
  let T₀ : ClosedSubgroup e.normalizer.group := ⟨T.group, e.torusInclusion, e.torusClosed⟩
  let p := e.image.constantGroup.sectionPoint (e.labelEquiv w)
  have htor := fibreTorsor (G := Specs.Unipotent.closedSubgroupAlgebraicGroup e.normalizer)
    (W := e.scheme) T₀ e.quotient e.isQuotient p
  obtain ⟨n, hn⟩ := splitFibrePoint
    (G := Specs.Unipotent.closedSubgroupAlgebraicGroup e.normalizer) (W := e.scheme)
    T₀ hT e.quotient p htor
  let Y := (testSpec k).obj (Opposite.op K)
  let n' : RationalPoints e.normalizer.group := toUnit Y ≫ n
  have hlift : n' ≫ e.quotient.hom.hom = toUnit Y ≫ p := by
    exact (Category.assoc (toUnit Y) n e.quotient.hom.hom).trans
      (congrArg (fun a => toUnit Y ≫ a) hn)
  let g : RationalPoints G.val := n' ≫ e.normalizer.inclusion.hom.hom
  have h := congrArg (fun z => lift t' (𝟙 Y) ≫ z)
    (e.image.conjugates Y n' (e.labelEquiv w) hlift)
  change lift t' (𝟙 Y) ≫ conjugateFamily T.inclusion g = _ at h
  have hright : lift t' (𝟙 Y) ≫ fst T.group.X Y ≫ (a.hom ≫ T.inclusion).hom.hom =
        t' ≫ (a.hom ≫ T.inclusion).hom.hom := lift_fst_assoc _ _ _
  erw [comp_conjugateFamily, lift_fst_assoc, lift_snd_assoc, Category.id_comp, hright] at h
  have hback : t' ≫ (a.hom ≫ T.inclusion).hom.hom = t ≫ T.inclusion.hom.hom := by
    rw [ht']
    change (t ≫ a.inv.hom.hom) ≫ a.hom.hom.hom ≫ T.inclusion.hom.hom = _
    have hassoc := Category.assoc (t : Y ⟶ T.group.X) a.inv.hom.hom
      (a.hom.hom.hom ≫ T.inclusion.hom.hom)
    erw [hassoc]
    have hh : a.inv.hom.hom ≫ a.hom.hom.hom = 𝟙 _ :=
      (Grp.forget _).congr_map a.inv_hom_id
    rw [← Category.assoc (f := a.inv.hom.hom), hh, Category.id_comp]
  rw [hback] at h
  refine ⟨g⁻¹, ?_⟩
  change g * pointHom T.inclusion t' * g⁻¹ = pointHom T.inclusion t at h
  rw [← h, inv_inv]
  group

end TorusPoints

open private isSemisimple_of_eigenbasis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LinearJordanFactors

theorem splitTorusJordan : SplitTorusJordan.{u} := by
  classical
  intro k _ _ T hs t
  refine ⟨(mul_one t).symm, Commute.one_right _, ?_⟩
  intro V I _ _ _ _ b L l f
  let ρ : Representation T.val I := (groupPointsFunctor k).map f ≫ l.hom
  let K := CommAlgCat.of k k
  let S : ClosedSubgroup T.val := ⟨T.val, 𝟙 _, by
    change IsClosedImmersion (𝟙 T.val.X.left)
    infer_instance⟩
  let A := fun χ => weightSpace ρ S χ
  let h := internalWeights S hs ρ
  let c := h.collectedBasis (fun χ => Module.finBasis k (A χ))
  let c' := c.map b.equivFun.symm
  let F := Affine.rationalRepresentationAction
    (G := ⟨T.val, T.property.1⟩) b l f
  have act (x : RationalPoints T.val) : F x = Matrix.toLin b b (ρ.app K x).val := rfl
  have unit (x : RationalPoints T.val) : IsUnit (F x) :=
    (ρ.app K x).isUnit.map (Matrix.toLinAlgEquiv b)
  have hF : (F t).IsSemisimple := by
    let : FiniteDimensional k V := b.finiteDimensional_of_finite
    apply isSemisimple_of_eigenbasis c' (fun j => characterValue j.1 K t)
    intro j
    have hm : c j ∈ A j.1 := h.collectedBasis_mem _ j
    have eq := (mem_weightSpace.mp hm) K t
    have he (x : I → k) : Specs.RootWeightAction.extendVector K x = x := by
      ext i
      exact Algebra.algebraMap_self_apply (x i)
    rw [he, show t ≫ S.inclusion.hom.hom = t from Category.comp_id t] at eq
    change (ρ.app K t).val.mulVec (c j) = _ at eq
    rw [act]
    change Matrix.toLin b b (ρ.app K t).val (b.equivFun.symm (c j)) =
      characterValue j.1 K t • b.equivFun.symm (c j)
    have hmat (M : Matrix I I k) (v : I → k) :
        Matrix.toLin b b M (b.equivFun.symm v) = b.equivFun.symm (M.mulVec v) := by
      change b.equivFun.symm (Matrix.toLin' M (b.equivFun (b.equivFun.symm v))) = _
      rw [LinearEquiv.apply_symm_apply, Matrix.toLin'_apply]
    rw [hmat, eq, map_smul]
  have hone : F 1 = 1 := by
    let φ : RationalPoints T.val →* (Matrix I I k)ˣ := (ρ.app K).hom
    change Matrix.toLin b b (φ 1).val = 1
    rw [map_one, Units.val_one, Matrix.toLin_one]
    rfl
  change Affine.IsMultiplicativeJordanDecomposition (F t) (F t) (F 1)
  rw [hone]
  refine ⟨(mul_one _).symm, Commute.one_right _, hF, ?_, unit t, isUnit_one⟩
  rw [sub_self]
  exact IsNilpotent.zero

theorem torusRepresentativeFibres : TorusRepresentativeFibres.{u} := by
  intro sep k J A _ G T hs _ D e i hex hu V hgen x y s r v u' hx hy t t' h h' ht ht' trace
  let := e.image.finite
  let _ : Finite D.rootDatum.weylGroup := Finite.of_injective e.labelEquiv e.labelEquiv.injective
  obtain ⟨z, _, hz⟩ := torusPointCoordinates hs
  have htr (j : J) :
      integralEvaluation (z t) (formalCharacter T (V j).action) =
        integralEvaluation (z t') (formalCharacter T (V j).action) := by
    rw [← torusTrace T hs _ t (z t) (hz t), ← torusTrace T hs _ t' (z t') (hz t')]
    change pointTrace (V j).action (pointHom T.inclusion t) =
      pointTrace (V j).action (pointHom T.inclusion t')
    rw [← ht, ← ht', traceConjugation, traceConjugation,
      ← jordanTrace G _ hx, ← jordanTrace G _ hy, trace]
  have hagree := integralEvaluationAgreement (Specs.CharacterRing.weylAction e)
    (fun j => formalCharacter T (V j).action) (z t) (z t') hgen htr
  obtain ⟨w, hw⟩ := integralOrbitSeparation sep _ i (z t) (z t') hex hu hagree
  obtain ⟨g, hg⟩ := torusWeylConjugation hs e w t t' (fun c => by
    rw [← hz, ← hz]
    exact (congrArg (fun f : Character T.group →* kˣ => (f c : k)) hw).symm)
  refine ⟨h'⁻¹ * g * h, ?_⟩
  rw [← ht, ← ht'] at hg
  rw [show (h'⁻¹ * g * h) * s * (h'⁻¹ * g * h)⁻¹ =
    h'⁻¹ * (g * (h * s * h⁻¹) * g⁻¹) * h' by group, hg]
  group

section Centralizers

open _root_.LinearAlgebraicGroups.Affine (IsRationalJordanDecomposition rationalRepresentationAction
  rationalJordanDecomposition rationalJordanDecompositionFunctorial)
open private conjugation conjugation_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private isSplitTorus_of_isAlgClosed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NontrivialRationalTorus

private theorem rationalPointFromUnit {k : Type u} [Field k] {G : GroupScheme k}
    (h : RationalPoints G) :
    ∃ q : 𝟙_ (SchemeOver k) ⟶ G.X,
      toUnit ((testSpec k).obj (Opposite.op (CommAlgCat.of k k))) ≫ q = h := by
  let Y := (testSpec k).obj (Opposite.op (CommAlgCat.of k k))
  have hy : Y.hom = 𝟙 (Spec (CommRingCat.of k)) := by
    change Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  let j : Over.mk (𝟙 (Spec (CommRingCat.of k))) ≅ Y :=
    Over.isoMk (Iso.refl _) (by change 𝟙 _ ≫ Y.hom = _; exact (Category.id_comp _).trans hy)
  let t : IsTerminal Y := Over.mkIdTerminal.ofIso j
  let a := t.uniqueUpToIso (isTerminalTensorUnit (C := SchemeOver k))
  refine ⟨a.inv ≫ h, ?_⟩
  have ha : a.hom = toUnit Y := Subsingleton.elim _ _
  change toUnit Y ≫ a.inv ≫ h = h
  exact congrArg (fun g : Y ⟶ 𝟙_ (SchemeOver k) => g ≫ a.inv ≫ h) ha.symm |>.trans
    (a.hom_inv_id_assoc (h : Y ⟶ G.X))

private theorem unipotentFactorJordan {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {x s v : RationalPoints G.val}
    (h : IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ x s v) :
    IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ v 1 v := by
  refine ⟨(one_mul v).symm, Commute.one_left _, ?_⟩
  intro V I _ _ _ _ b L l f
  let ρ : Representation G.val I := (groupPointsFunctor k).map f ≫ l.hom
  let φ : RationalPoints G.val →* (Matrix I I k)ˣ := (ρ.app (CommAlgCat.of k k)).hom
  let F := rationalRepresentationAction (G := ⟨G.val, G.property.1⟩) b l f
  have hone : F 1 = 1 := by
    change Matrix.toLin b b (φ 1).val = 1
    rw [map_one, Units.val_one, Matrix.toLin_one]
    rfl
  have hj := h.2.2 b L l f
  change Affine.IsMultiplicativeJordanDecomposition (F v) (F 1) (F v)
  rw [hone]
  exact ⟨(one_mul _).symm, Commute.one_left _, Module.End.isSemisimple_id,
    hj.unipotent, isUnit_one, hj.isUnit_unipotent⟩

set_option maxHeartbeats 500000 in
private theorem torusCentralizerJordan {k : Type u} [Field k] [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (C : ClosedSubgroup G.val)
    (y : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (htor : GeometricRadicals.IsTorus C.group) (hC : IsPointCentralizer C y)
    (x s v : RationalPoints G.val)
    (hs : s = toUnit ((testSpec k).obj (Opposite.op (CommAlgCat.of k k))) ≫ y)
    (hJ : IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ x s v) : x = s := by
  let Y := (testSpec k).obj (Opposite.op (CommAlgCat.of k k))
  have hv : Commute (v : Y ⟶ G.val.X) (toUnit Y ≫ y) := by
    rw [← hs]
    exact hJ.2.1.symm
  obtain ⟨c₀, hc₀⟩ := (hC Y v).mp hv
  let c : RationalPoints C.group := c₀
  let C' := Specs.Unipotent.closedSubgroupAlgebraicGroup C
  have hct : IsRationalJordanDecomposition ⟨C'.val, C'.property.1⟩ c c 1 :=
    splitTorusJordan C' (isSplitTorus_of_isAlgClosed C htor) c
  let i := pointHom C.inclusion
  have hc : i c = v := hc₀
  have hcJ : IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ (i c) (i c) (i 1) :=
    rationalJordanDecompositionFunctorial C' G C.inclusion hct
  rw [hc, map_one] at hcJ
  have hvJ : IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ v 1 v :=
    unipotentFactorJordan hJ
  have eq : (v, (1 : RationalPoints G.val)) = (1, v) :=
    ExistsUnique.unique
      (p := fun q : RationalPoints G.val × RationalPoints G.val =>
        IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ v q.1 q.2)
      (y₁ := (v, 1)) (y₂ := (1, v)) (rationalJordanDecomposition G v) hcJ hvJ
  have hv₁ : v = 1 := congrArg Prod.fst eq
  exact hJ.1.trans (by rw [hv₁, mul_one])

set_option maxHeartbeats 500000 in
theorem torusCentralizerCollapse : TorusCentralizerCollapse.{u} := by
  intro k _ _ G C y htor hC x s v hJ h hh
  obtain ⟨q, hq⟩ := rationalPointFromUnit h
  let f := conjugation q
  let φ := pointHom f
  have hφ (a : RationalPoints G.val) : φ a = h * a * h⁻¹ := by
    change a ≫ f.hom.hom = _
    erw [conjugation_apply q a, hq]
    rfl
  have hJ' : IsRationalJordanDecomposition ⟨G.val, G.property.1⟩ (φ x) (φ s) (φ v) :=
    rationalJordanDecompositionFunctorial G G f hJ
  have hs : φ s = toUnit ((testSpec k).obj (Opposite.op (CommAlgCat.of k k))) ≫ y :=
    (hφ s).trans hh
  have hx := torusCentralizerJordan G C y htor hC (φ x) (φ s) (φ v) hs hJ'
  exact (hφ x).symm.trans (hx.trans hs)

end Centralizers

open private groupBaseChangePointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations

theorem representationExtension : RepresentationExtension.{u} := by
  intro k K I _ _ _ _ _ G ρ
  let c := groupBaseChangePointIso K G
  let σ : Representation ((groupBaseChange k K).obj G) I :=
    { app := fun R => GrpCat.ofHom ((ρ.app ((restrictTestAlgebra k K).obj R)).hom.comp (c.hom.app R).hom)
      naturality := by
        intro R S f
        apply GrpCat.ext
        intro g
        have hc := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (c.hom.naturality f)) g
        have hρ := DFunLike.congr_fun
          (congrArg GrpCat.Hom.hom (ρ.naturality ((restrictTestAlgebra k K).map f)))
          (c.hom.app R g)
        change ρ.app _ (c.hom.app S (((groupPointsFunctor K).obj
          ((groupBaseChange k K).obj G)).map f g)) = _
        rw [show c.hom.app S (((groupPointsFunctor K).obj
          ((groupBaseChange k K).obj G)).map f g) =
          ((groupPointsFunctor k).obj G).map ((restrictTestAlgebra k K).map f) (c.hom.app R g)
          from hc]
        exact hρ }
  exact ⟨σ, fun _ _ => rfl⟩

section ExtendedSocle

open LinearAlgebraicGroups.RationalRepresentations (scalarExtension IsScalarExtension
  scalarExtensionCoaction coefficients coefficients_coactionOfMatrix restrictCoordinatePoint
  fieldExtensionPoints pointsCoactionEquiv matrixPointHom)
open private scalarExtensionCoaction_isScalarExtension from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.BaseChange
open private realizes_unique from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.SimpleClassification
open private pointIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.InducedSocle
open private fromCoaction from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.PrimitiveLine
open WithConv

theorem socleRepresentationExtension : SocleRepresentationExtension.{u} := by
  intro k K _ _ _ G P U hU χ S
  obtain ⟨C, E, eU, eT, qU, qT, φ, hqU, hqT, hφ, habs⟩ :=
    Representation.SimpleClassification.absoluteSimplicity G P U hU χ S
  obtain ⟨δ, hδ, hnontriv, hsimple, hv, hlines⟩ := habs K
  obtain ⟨σ, hσ⟩ := representationExtension (K := K) S.socleAction
  obtain ⟨e, he, _⟩ := fieldExtensionPoints (K := K) S.A ⟨G.val, G.property.1⟩ S.groupIso
  refine ⟨σ, δ, e, hδ, hnontriv, hsimple, hσ, ?_,
    C, E, eU, eT, qU, qT, φ, hqU, hqT, hφ, hv, hlines⟩
  intro R g
  let A := S.A
  let b := S.socleBasis
  let B := scalarExtension A K
  let a := _root_.LinearAlgebraicGroups.RationalRepresentations.restrictCoordinatePoint A K R g
  let e₀ := pointIso S.groupIso
  have hp : baseChangePoint k K G.val.X R (e.hom.app R (toConv g)) =
      e₀.hom.app ((restrictTestAlgebra k K).obj R) (toConv a) := by
    apply Over.OverMorphism.ext
    exact he R (toConv g)
  have hscalar : δ.coaction = (scalarExtensionCoaction A b K S.socleCoaction).coaction :=
    hδ.trans (scalarExtensionCoaction_isScalarExtension A b S.socleCoaction).symm
  have hcoeff : coefficients B (b.baseChange K) δ =
      fun i j => (1 : K) ⊗ₜ[k] coefficients A b S.socleCoaction i j := by
    unfold coefficients at ⊢
    simp only [hscalar]
    exact coefficients_coactionOfMatrix B _ _ _
  rw [hσ, hp, realizes_unique S.groupIso b S.socleCoaction S.socleAction S.socleAction_spec]
  have happ := e₀.hom_inv_id_app ((restrictTestAlgebra k K).obj R)
  have hpoint := DFunLike.congr_fun (congrArg GrpCat.Hom.hom happ) (toConv a)
  change (((pointsCoactionEquiv A b).symm S.socleCoaction).app _
    (e₀.inv.app _ (e₀.hom.app _ (toConv a)))).val = _
  change e₀.inv.app _ (e₀.hom.app _ (toConv a)) = toConv a at hpoint
  rw [hpoint, hcoeff]
  rfl

end ExtendedSocle

section AffineDominance

variable {k A B : Type*} [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

private abbrev augmentation (e : A →ₐ[k] k) : Ideal A := RingHom.ker e.toRingHom

private def centered (e : A →ₐ[k] k) (a : A) : augmentation e :=
  ⟨a - algebraMap k A (e a), by simp [augmentation]⟩

private theorem centered_add (e : A →ₐ[k] k) (a b : A) :
    centered e (a + b) = centered e a + centered e b := by
  apply Subtype.ext
  simp only [centered, Submodule.coe_add, map_add]
  ring

private theorem centered_mul (e : A →ₐ[k] k) (a b : A) :
    (augmentation e).toCotangent (centered e (a * b)) =
      e a • (augmentation e).toCotangent (centered e b) +
        e b • (augmentation e).toCotangent (centered e a) := by
  rw [← LinearMap.map_smul_of_tower, ← LinearMap.map_smul_of_tower, ← map_add,
    Ideal.toCotangent_eq, pow_two]
  have h : ((centered e (a * b) - (e a • centered e b + e b • centered e a) :
      augmentation e) : A) = (centered e a : A) * centered e b := by
    simp only [centered, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul_of_tower,
      Algebra.smul_def, map_mul]
    ring
  rw [← Submodule.coe_sub, h]
  exact Ideal.mul_mem_mul (centered e a).property (centered e b).property

/-- A retraction on cotangent spaces gives a section into the quotient by the
square of the maximal ideal of the rational point. -/
private theorem firstOrderSection (f : A →ₐ[k] B) (e : B →ₐ[k] k)
    (h : Function.Injective (Ideal.mapCotangent (augmentation (e.comp f))
      (augmentation e) f (fun _ ha => ha))) :
    ∃ g : B →ₐ[k] A ⧸ augmentation (e.comp f) ^ 2,
      g.comp f = Ideal.Quotient.mkₐ k _ := by
  let eA := e.comp f
  let I := augmentation eA
  let J := augmentation e
  let c : I.Cotangent →ₗ[k] J.Cotangent := Ideal.mapCotangent I J f (fun _ ha => ha)
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective c (LinearMap.ker_eq_bot.mpr h)
  let q := Ideal.Quotient.mkₐ k (I ^ 2)
  let l : J.Cotangent →ₗ[k] A ⧸ I ^ 2 :=
    (I.cotangentToQuotientSquare.restrictScalars k).comp r
  let d (b : B) := l (J.toCotangent (centered e b))
  have hd (b : B) : d b ∈ I.cotangentIdeal := by
    change I.cotangentToQuotientSquare (r _) ∈ I.cotangentIdeal.restrictScalars A
    rw [← Ideal.range_cotangentToQuotientSquare]
    exact LinearMap.mem_range_self _ _
  have hadd (a b : B) : d (a + b) = d a + d b := by
    simp only [d, centered_add, map_add]
  have hmul (a b : B) : d (a * b) = e a • d b + e b • d a := by
    have he := centered_mul e a b
    change J.toCotangent (centered e (a * b)) = _ at he
    change l (J.toCotangent (centered e (a * b))) = _
    rw [he, map_add, map_smul, map_smul]
  have hz (x : k) : d (algebraMap k B x) = 0 := by
    have h0 : centered e (algebraMap k B x) = 0 := by
      apply Subtype.ext
      simp [centered]
    simp [d, h0]
  let g : B →ₐ[k] A ⧸ I ^ 2 :=
    { toFun := fun b => algebraMap k _ (e b) + d b
      map_one' := by simpa using hz 1
      map_zero' := by simpa using hz 0
      map_add' := fun a b => by simp only [map_add, hadd]; ac_rfl
      map_mul' := fun a b => by
        have h0 : d a * d b = 0 := by
          have hm := Ideal.mul_mem_mul (hd a) (hd b)
          rwa [← pow_two, Ideal.cotangentIdeal_square, Submodule.mem_bot] at hm
        simp only [map_mul, hmul, Algebra.smul_def]
        linear_combination -h0
      commutes' := fun x => by simp [hz] }
  refine ⟨g, ?_⟩
  ext a
  change algebraMap k (A ⧸ I ^ 2) (eA a) + d (f a) = q a
  have hc : c (I.toCotangent (centered eA a)) = J.toCotangent (centered e (f a)) := by
    change J.toCotangent ⟨f (centered eA a : A), _⟩ = J.toCotangent (centered e (f a))
    congr 1
    apply Subtype.ext
    simp [centered, eA]
  rw [show d (f a) = q (a - algebraMap k A (eA a)) from by
    change I.cotangentToQuotientSquare (r _) = _
    rw [← hc, show r (c (I.toCotangent (centered eA a))) = _ from LinearMap.congr_fun hr _, LinearMap.id_apply,
      Ideal.toCotangent_to_quotient_square]
    rfl]
  rw [map_sub, AlgHom.commutes]
  ring

/-- Lift the section to each finite-order neighbourhood by formal smoothness.
The lifts agree with the quotient map on each successive graded piece,
so the kernel is contained in all powers of the augmentation ideal. -/
private theorem injective_of_firstOrderSection [IsNoetherianRing A] [IsDomain A]
    [Algebra.FormallySmooth k B] (f : A →ₐ[k] B) (e : B →ₐ[k] k)
    (g : B →ₐ[k] A ⧸ augmentation (e.comp f) ^ 2)
    (hg : g.comp f = Ideal.Quotient.mkₐ k _) :
    Function.Injective f := by
  let I := augmentation (e.comp f)
  have hI : I ≠ ⊤ := RingHom.ker_ne_top _
  have hker : ∀ a, f a = 0 → a = 0 := by
    intro a ha
    have ha₂ : a ∈ I ^ 2 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change Ideal.Quotient.mkₐ k (I ^ 2) a = 0
      rw [← hg, AlgHom.comp_apply, ha, map_zero]
    have hind (n : ℕ) (hn : 2 ≤ n) (hx : a ∈ I ^ n) : a ∈ I ^ (n + 1) := by
      let C := A ⧸ I ^ (n + 1)
      let q := Ideal.Quotient.mkₐ k (I ^ (n + 1))
      let p : C →ₐ[k] A ⧸ I ^ 2 := Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (by omega))
      have hp : Function.Surjective p := by
        intro z
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
        exact ⟨q y, rfl⟩
      let J := I.map q.toRingHom
      have hJker : RingHom.ker p.toRingHom = J ^ 2 := by
        rw [← Ideal.map_pow]
        ext z
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
        change p (q x) = 0 ↔ q x ∈ (I ^ 2).map q.toRingHom
        rw [show p (q x) = Ideal.Quotient.mk (I ^ 2) x from rfl,
          Ideal.Quotient.eq_zero_iff_mem]
        change x ∈ I ^ 2 ↔ Ideal.Quotient.mk (I ^ (n + 1)) x ∈
          (I ^ 2).map (Ideal.Quotient.mk (I ^ (n + 1)))
        rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
        refine ⟨fun hx => ⟨x, hx, rfl⟩, ?_⟩
        rintro ⟨y, hy, hyx⟩
        have hxy : x - y ∈ I ^ (n + 1) := (Ideal.Quotient.eq.mp hyx.symm)
        simpa using (I ^ 2).add_mem (Ideal.pow_le_pow_right (by omega) hxy) hy
      have hJn : J ^ (n + 1) = ⊥ := by
        rw [← Ideal.map_pow]
        exact Ideal.map_quotient_self _
      have hnil : IsNilpotent (RingHom.ker p.toRingHom) := by
        refine ⟨n + 1, ?_⟩
        change (RingHom.ker p.toRingHom) ^ (n + 1) = (⊥ : Ideal C)
        rw [hJker, ← pow_mul]
        exact eq_bot_mono (Ideal.pow_le_pow_right (by omega)) hJn
      let l := Algebra.FormallySmooth.liftOfSurjective g p hp hnil
      let h := l.comp f
      have hd (x : A) : h x - q x ∈ J ^ 2 := by
        rw [← hJker, RingHom.mem_ker]
        change p (h x - q x) = 0
        rw [map_sub, show p (h x) = g (f x) from
          Algebra.FormallySmooth.liftOfSurjective_apply g p hp hnil _, ← AlgHom.comp_apply,
          hg]
        exact sub_self _
      have hpow (m : ℕ) (x : A) (hx : x ∈ I ^ m) : h x - q x ∈ J ^ (m + 1) := by
        refine Submodule.pow_induction_on_left' I
          (C := fun m x _ => h x - q x ∈ J ^ (m + 1)) ?_ ?_ ?_ hx
        · intro t
          change h t - q t ∈ J ^ (0 + 1)
          exact Ideal.pow_le_pow_right (by omega) (hd t)
        · intro x y i hx hy hx' hy'
          rw [map_add, map_add, add_sub_add_comm]
          exact add_mem hx' hy'
        · intro y hy i x hx hx'
          have hqY : q y ∈ J := Ideal.mem_map_of_mem _ hy
          have hhY : h y ∈ J := by
            have hm : h y - q y ∈ J := Ideal.pow_le_self two_ne_zero (hd y)
            simpa using add_mem hm hqY
          have hqX : q x ∈ J ^ i := by
            rw [← Ideal.map_pow]
            exact Ideal.mem_map_of_mem _ hx
          rw [map_mul, map_mul, show h y * h x - q y * q x =
            h y * (h x - q x) + (h y - q y) * q x by ring]
          apply add_mem
          · rw [pow_succ' _ (i + 1)]
            exact Ideal.mul_mem_mul hhY hx'
          · have hm := Ideal.mul_mem_mul (hd y) hqX
            rw [← pow_add] at hm
            have he : i.succ + 1 = 2 + i := by omega
            change _ ∈ J ^ (i.succ + 1)
            simpa only [he] using hm
      have he := hpow n a hx
      have hzero : h a = 0 := by change l (f a) = 0; rw [ha, map_zero]
      rw [hJn, Submodule.mem_bot, hzero, zero_sub, neg_eq_zero] at he
      exact (Ideal.Quotient.eq_zero_iff_mem (a := a)).mp he
    have hbig (n : ℕ) : a ∈ I ^ (n + 2) := by
      induction n with
      | zero => exact ha₂
      | succ n ih =>
        simpa only [Nat.succ_eq_add_one, Nat.add_right_comm n 1 2] using
          (hind (n + 2) (by omega) ih)
    have hall (n : ℕ) : a ∈ I ^ n :=
      Ideal.pow_le_pow_right (by omega) (hbig n)
    -- Use the separated ideal-adic filtration of the noetherian domain.
    have hmem : a ∈ ⨅ n : ℕ, I ^ n := Ideal.mem_iInf.mpr hall
    rwa [Ideal.iInf_pow_eq_bot_of_isDomain I hI, Submodule.mem_bot] at hmem
  rw [injective_iff_map_eq_zero]
  exact hker

end AffineDominance

section FixedFlags

open private exists_rational_point from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit

theorem properFixedIncidence : ProperFixedIncidence.{u} := by
  intro k _ _ G X a hX hd g
  let Z := equalizer a.smul (snd G.X X)
  let j : Z ⟶ G.X ⊗ X := equalizer.ι a.smul (snd G.X X)
  let p : Z ⟶ G.X := j ≫ fst _ _
  let : IsProper X.hom := hX
  have : IsClosedImmersion j.left := isClosedImmersion_equalizer_ι_left _ _
  have : IsProper (fst G.X X).left := by
    let h := tensorProductIsBinaryProduct G.X X
    let h' := prodIsProd G.X X
    let e := h.conePointUniqueUpToIso h'
    have he : e.hom ≫ prod.fst = fst G.X X :=
      h.conePointUniqueUpToIso_hom_comp h' ⟨WalkingPair.left⟩
    have he' : e.hom.left ≫ (prod.fst : G.X ⨯ X ⟶ G.X).left = (fst G.X X).left :=
      congrArg Over.Hom.left he
    have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    rw [← he', ← Over.prodLeftIsoPullback_hom_fst]
    infer_instance
  have : IsProper p.left := by
    change IsProper (j.left ≫ (fst G.X X).left)
    infer_instance
  have hrange : IsClosed (Set.range p.left) := p.left.isClosedMap.isClosed_range
  have hin : {z : G.X.left | ∃ (g : 𝟙_ (SchemeOver k) ⟶ G.X) (x : 𝟙_ (SchemeOver k) ⟶ X),
      g.left (IsLocalRing.closedPoint k) = z ∧ lift g x ≫ a.smul = x} ⊆ Set.range p.left := by
    rintro _ ⟨g', x, rfl, hx⟩
    let q : (𝟙_ (SchemeOver k)) ⟶ Z := equalizer.lift (lift g' x) (hx.trans (lift_snd _ _).symm)
    have hq : q ≫ p = g' := by
      change q ≫ j ≫ fst _ _ = _
      rw [← Category.assoc, equalizer.lift_ι, lift_fst]
    let w : (𝟙_ (SchemeOver k)).left := IsLocalRing.closedPoint k
    refine ⟨q.left w, ?_⟩
    exact (Scheme.Hom.comp_apply q.left p.left w).symm.trans
      (congrArg (fun u : (𝟙_ (SchemeOver k)) ⟶ G.X => u.left w) hq)
  have hfull : Set.range p.left = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hd.closure_eq]
    exact closure_minimal hin hrange
  obtain ⟨z, hz⟩ := (Set.range_eq_univ.mp hfull) (g.left (IsLocalRing.closedPoint k))
  let F := pullback p g
  let f : F ⟶ 𝟙_ (SchemeOver k) := pullback.snd p g
  have hf := (IsPullback.of_hasPullback p g).map (Over.forget _)
  obtain ⟨s, -, -⟩ := Scheme.exists_preimage_of_isPullback hf z (IsLocalRing.closedPoint k) hz
  let : Nonempty F.left := ⟨s⟩
  have : LocallyOfFiniteType f.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hf
      (show LocallyOfFiniteType p.left from inferInstance)
  have : LocallyOfFiniteType (𝟙_ (SchemeOver k)).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k))))
  have : LocallyOfFiniteType F.hom := by rw [← Over.w f]; infer_instance
  obtain ⟨t⟩ := exists_rational_point F
  let q : (𝟙_ (SchemeOver k)) ⟶ Z := t ≫ pullback.fst p g
  have hq : q ≫ p = g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      toUnit_unique (t ≫ f) (𝟙 _), Category.id_comp]
  let x := q ≫ j ≫ snd G.X X
  have hcomp : lift g x = q ≫ j := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, Category.assoc]
      exact hq.symm
    · exact lift_snd _ _
  refine ⟨x, ?_⟩
  rw [hcomp, Category.assoc]
  exact congrArg (q ≫ ·) (equalizer.condition a.smul (snd G.X X))

end FixedFlags

section RegularTorusGeometry

open Opposite
open Specs.FlagLineBundle (OppositeBorelPair BorelProjection)
open Specs.CharacterDescent (Character StandardLattice)
open Specs.CharacterPairing (characterValue adjointWeightVectors adjointWeightSpace absoluteRoots)
open Specs.AdjointRepresentation (GroupPoints constants scale dualMap)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.EquivariantUnipotentSeries (onPoints)
open _root_.LinearAlgebraicGroups.Affine (RationalPoints)
open _root_.Specs.AdvCommAlg.Differentials.Tangent (PointLifts)
open Specs.DiagonalizableGroups (groupAlgebra)
open Module

variable {k : Type u} [Field k]

private abbrev groundTest (k : Type u) [Field k] := CommAlgCat.of k k
private abbrev dualTest (k : Type u) [Field k] := CommAlgCat.of k (DualNumber k)

open private affinePointEquiv_postcomp affinePointEquiv_lifts pullbackLifts torusWeightBasis
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private affinePointEquiv affinePointEquiv_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterSmoothAndUnipotent
open private splitPresentation charactersOfIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private splitCharacterValue
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FormalCharacters
open private exists_rational_point isPullback_tensor_structure
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit
open private smooth_spec_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
open private affine_tensor from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private ext_lift from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent

/-- A smooth affine source and a surjective tangent map at a rational point
give a dense morphism into an integral affine scheme of finite type. -/
private theorem denseRange_of_tangentLifts {X Y : SchemeOver k}
    (f : X ⟶ Y) [IsAffine X.left] [IsAffine Y.left] [IsIntegral Y.left]
    [LocallyOfFiniteType Y.hom] [Smooth X.hom]
    (x : Points X (groundTest k))
    (h : ∀ y : Points Y (dualTest k), mapPoints (dualReduction k) y = x ≫ f →
      ∃ z : Points X (dualTest k), mapPoints (dualReduction k) z = x ∧ z ≫ f = y) :
    DenseRange f.left := by
  obtain ⟨Aop, ⟨eY⟩⟩ := essImage_algSpec.mpr (inferInstance : IsAffine Y.left)
  obtain ⟨Bop, ⟨eX⟩⟩ := essImage_algSpec.mpr (inferInstance : IsAffine X.left)
  let A := Aop.unop
  let B := Bop.unop
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let m := (F.preimage (eX.hom ≫ f ≫ eY.inv)).unop
  let φ := m.hom
  have hm : (testSpec k).map m.op ≫ eY.hom = eX.hom ≫ f := by
    change (testSpec k).map (F.preimage (eX.hom ≫ f ≫ eY.inv)) ≫ eY.hom = _
    rw [F.map_preimage]
    simp
  have hc {R : TestAlgebra k} (z : B →ₐ[k] R) :
      affinePointEquiv eX R z ≫ f = affinePointEquiv eY R (z.comp φ) :=
    affinePointEquiv_postcomp eX eY f φ hm z
  let ε := (affinePointEquiv eX (groundTest k)).symm x
  have heX : affinePointEquiv eX _ ε = x := (affinePointEquiv eX _).apply_symm_apply _
  have heY : affinePointEquiv eY _ (ε.comp φ) = x ≫ f := (hc ε).symm.trans (by rw [heX])
  let u := affinePointEquiv_lifts eX heX
  let v := affinePointEquiv_lifts eY heY
  have hlift : Function.Surjective (pullbackLifts φ ε) := by
    intro a
    obtain ⟨z, hz, hzf⟩ := h (v a).val (v a).property
    refine ⟨u.symm ⟨z, hz⟩, v.injective (Subtype.ext ?_)⟩
    have hu := congrArg Subtype.val (u.apply_symm_apply ⟨z, hz⟩)
    change affinePointEquiv eX (dualTest k) (u.symm ⟨z,hz⟩).val = z at hu
    change affinePointEquiv eY (dualTest k) ((u.symm ⟨z,hz⟩).val.comp φ) = (v a).val
    rw [← hc, hu, hzf]
  obtain ⟨tA, hA, _⟩ := LinearAlgebraicGroups.pointTangentLifts k A (ε.comp φ)
  obtain ⟨tB, hB, _⟩ := LinearAlgebraicGroups.pointTangentLifts k B ε
  let c : (RingHom.ker (ε.comp φ).toRingHom).Cotangent →ₗ[k]
      (RingHom.ker ε.toRingHom).Cotangent := Ideal.mapCotangent _ _ φ (fun _ h => h)
  have hdual (L : PointTangent ε) : pullbackLifts φ ε (tB L) = tA (c.dualMap L) := by
    apply ext_lift
    intro a
    change ((tB L).val (φ a.val)).snd = ((tA (c.dualMap L)).val a).snd
    rw [hA]
    exact hB L ⟨φ a.val, a.property⟩
  have hcinj : Function.Injective c := by
    apply LinearMap.dualMap_surjective_iff.mp
    intro a
    obtain ⟨b, hb⟩ := hlift (tA a)
    obtain ⟨l, rfl⟩ := tB.surjective b
    exact ⟨l, tA.injective ((hdual l).symm.trans hb)⟩
  obtain ⟨g, hg⟩ := firstOrderSection φ ε hcinj
  let e : Spec (CommRingCat.of A) ≅ Y.left := (Over.forget (Spec (CommRingCat.of k))).mapIso eY
  let : IsIntegral (Spec (CommRingCat.of A)) := IsIntegral.of_isIso e.inv
  let : IsDomain A := (affine_isIntegral_iff (CommRingCat.of A)).mp inferInstance
  have hft : LocallyOfFiniteType ((testSpec k).obj Aop).hom := by
    rw [← Over.w eY.hom]
    infer_instance
  let : Algebra.FiniteType k A := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) at hft
    exact RingHom.finiteType_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft)
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hs : Smooth ((testSpec k).obj Bop).hom := by
    rw [← Over.w eX.hom]
    infer_instance
  let : Algebra.Smooth k B := smooth_spec_iff.mp hs
  have hinj := injective_of_firstOrderSection φ ε g hg
  have hd : DenseRange ((testSpec k).map m.op).left := by
    change DenseRange (PrimeSpectrum.comap φ.toRingHom)
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    rw [(RingHom.injective_iff_ker_eq_bot φ.toRingHom).mp hinj]
    exact bot_le
  have hcomm : eX.hom.left ≫ f.left = ((testSpec k).map m.op).left ≫ eY.hom.left :=
    congrArg Over.Hom.left hm.symm
  have hden : DenseRange (eX.hom.left ≫ f.left) := by
    rw [hcomm]
    exact eY.hom.left.homeomorph.surjective.denseRange.comp hd eY.hom.left.continuous
  exact hden.mono (Set.range_comp_subset_range _ _)

private theorem regularTorusPoint [IsAlgClosed k] {G : AffineAlgebraicGroup k}
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group) :
    ∃ t : RationalPoints T.group, ∀ α ∈ absoluteRoots T, characterValue α (groundTest k) t ≠ 1 := by
  classical
  obtain ⟨r, ⟨s⟩⟩ := splitPresentation hT
  let M := StandardLattice.{u} r
  let A := groupAlgebra k M
  obtain ⟨χ, _, hχ, _, _⟩ :=
    LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := k) r
  let e := χ.trans (charactersOfIso s)
  let R := CommAlgCat.of k A
  let X := (testSpec k).obj (op R)
  let hl := RootData.CharacterPairing.finiteAbsoluteRoots G T hT
  let l := hl.toFinset
  let f : A := ∏ α ∈ l, (MonoidAlgebra.of k M (e.symm α) - 1)
  let : UniqueProds Specs.DiagonalizableGroups.IntegerCharacters.{u} :=
    MulEquiv.ulift.uniqueProds_iff.mpr (inferInstance : UniqueProds (Multiplicative ℤ))
  let : IsDomain A := inferInstanceAs (IsDomain (MonoidAlgebra k M))
  have hf : f ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro α hα
    have hm : e.symm α ≠ 1 := fun h => (hl.mem_toFinset.mp hα).1
      (e.symm.injective (h.trans (e.symm.map_one).symm))
    intro hz
    have he := congrArg (fun f : MonoidAlgebra k M => f.coeff (e.symm α))
      (sub_eq_zero.mp hz)
    change (MonoidAlgebra.single (R := k) (e.symm α) 1).coeff (e.symm α) =
      (MonoidAlgebra.single 1 1).coeff (e.symm α) at he
    have h0 : (1 : k) = 0 := by
      simpa [MonoidAlgebra.coeff_single, Finsupp.single_apply, hm, Ne.symm hm] using he
    exact one_ne_zero h0
  let V : X.left.Opens := PrimeSpectrum.basicOpen f
  let D : SchemeOver k := Over.mk (V.ι ≫ X.hom)
  have hp : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  have : Nonempty D.left := ⟨⟨⟨⊥, hp⟩, hf⟩⟩
  let j : X ≅ T.group.X := (Grp.forget (SchemeOver k)).mapIso s
  let : LocallyOfFiniteType T.group.X.hom :=
    (Specs.Unipotent.closedSubgroupAlgebraicGroup T).property.2.1
  let : LocallyOfFiniteType X.hom := by rw [← Over.w j.hom]; infer_instance
  let : LocallyOfFiniteType D.hom := inferInstanceAs (LocallyOfFiniteType (V.ι ≫ X.hom))
  obtain ⟨d⟩ := exists_rational_point D
  let q : Points X (groundTest k) := toUnit _ ≫ d ≫ Over.homMk V.ι
  let a := ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage q).unop.hom
  have ha : (testSpec k).map (CommAlgCat.ofHom a).op = q := algSpec.fullyFaithful.map_preimage _
  have han : a f ≠ 0 := by
    have ht : q.left (IsLocalRing.closedPoint k) ∈ V := by
      show (toUnit _ ≫ d ≫ Over.homMk V.ι : _ ⟶ X).left _ ∈ V
      exact (((toUnit ((testSpec k).obj (op (groundTest k))) ≫ d).left
        (IsLocalRing.closedPoint k)) : V).property
    rw [← ha] at ht
    change a f ∉ (IsLocalRing.closedPoint k).asIdeal at ht
    exact fun h => ht (h.symm ▸ zero_mem _)
  let t : RationalPoints T.group := q ≫ j.hom
  refine ⟨t, ?_⟩
  intro α hα
  have hval := splitCharacterValue s χ hχ (e.symm α) (groundTest k) a
  change characterValue (e (e.symm α)) (groundTest k)
    ((testSpec k).map (CommAlgCat.ofHom a).op ≫ j.hom) =
      a (MonoidAlgebra.of k M (e.symm α)) at hval
  rw [e.apply_symm_apply] at hval
  rw [ha] at hval
  change characterValue α (groundTest k) t = _ at hval
  rw [hval, ← sub_ne_zero, ← map_one a, ← map_sub]
  apply Finset.prod_ne_zero_iff.mp ?_ α (hl.mem_toFinset.mpr hα)
  simpa only [f, map_prod] using han

private def torusConjugation {G : GroupScheme k} (T : ClosedSubgroup G) :
    G.X ⊗ T.group.X ⟶ G.X :=
  fst _ _ * (snd _ _ ≫ T.inclusion.hom.hom) * (fst _ _)⁻¹

private theorem torusConjugation_eval {G : GroupScheme k} (T : ClosedSubgroup G)
    {X : SchemeOver k} (g : X ⟶ G.X) (t : X ⟶ T.group.X) :
    lift g t ≫ torusConjugation T = g * (t ≫ T.inclusion.hom.hom) * g⁻¹ := by
  simp only [torusConjugation, MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd_assoc]

open private scale_at_base constants_scale from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.AdjointRepresentation

private theorem constant_reduction {H : GroupScheme k} (x : RationalPoints H) :
    reduceTangentPoints H
      ((((groupPointsFunctor k).obj H).map (constants (groundTest k))).hom x) = x := by
  have hc : constants (groundTest k) ≫ dualReduction k = 𝟙 _ := by
    ext
  change (((groupPointsFunctor k).obj H).map (dualReduction k))
    ((((groupPointsFunctor k).obj H).map (constants (groundTest k))) x) = x
  have he := ((groupPointsFunctor k).obj H).map_id (groundTest k)
  rw [← GrpCat.comp_apply, ← Functor.map_comp, hc, he]
  rfl

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- The differential of conjugation in the group variable is the identity
minus the adjoint action. The torus variable supplies the zero weight. -/
private theorem conjugation_lifts (G : AffineAlgebraicGroup k)
    (T : ClosedSubgroup G.val) (hG : GeometricRadicals.IsReductive G)
    (hT : IsSplitTorus T.group) (hmax : RankOneFlag.IsGeometricallyMaximal T)
    (t : RationalPoints T.group)
    (ht : ∀ α ∈ absoluteRoots T, characterValue α (groundTest k) t ≠ 1)
    (z : GroupPoints G.val (dualTest k))
    (hz : reduceTangentPoints G.val z = pointHom T.inclusion t) :
    ∃ p : Points (G.val.X ⊗ T.group.X) (dualTest k),
      mapPoints (dualReduction k) p = lift (1 : RationalPoints G.val) t ∧
      p ≫ torusConjugation T = z := by
  classical
  let s := LinearAlgebraicGroups.identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  let K := groundTest k
  let D := dualTest k
  let V := Lie k G.val
  let tc : GroupPoints T.group D := (((groupPointsFunctor k).obj T.group).map (constants K)).hom t
  let tg := onPoints T.inclusion D tc
  have htgBase : tg = (((groupPointsFunctor k).obj G.val).map (constants K)).hom
      (pointHom T.inclusion t) :=
    DFunLike.congr_fun (congrArg GrpCat.Hom.hom
      (((groupPointsFunctor k).map T.inclusion).naturality (constants K))) t
  have hr : reduceTangentPoints G.val tg = pointHom T.inclusion t :=
    htgBase ▸ constant_reduction _
  let w : V := Additive.ofMul ⟨z * tg⁻¹,
    by change reduceTangentPoints G.val (z * tg⁻¹) = 1; rw [map_mul, map_inv, hz, hr, mul_inv_cancel]⟩
  let conj : V →ₗ[k] V :=
    { toFun := fun v => Additive.ofMul ⟨tg * v.toMul.val * tg⁻¹, by
        change reduceTangentPoints G.val (tg * v.toMul.val * tg⁻¹) = 1
        rw [map_mul, map_mul, map_inv, show reduceTangentPoints G.val v.toMul.val = 1 from
          v.toMul.property, mul_one, mul_inv_cancel]⟩
      map_add' := fun v v' => by
        apply Subtype.ext
        change tg * (v.toMul.val * v'.toMul.val) * tg⁻¹ =
          (tg * v.toMul.val * tg⁻¹) * (tg * v'.toMul.val * tg⁻¹)
        group
      map_smul' := fun a v => by
        apply Subtype.ext
        let A := (((groupPointsFunctor k).obj G.val).map (scale K a)).hom
        have htg : A tg = tg := by
          have h := congrArg (fun (m : K ⟶ D) =>
            (((groupPointsFunctor k).obj G.val).map m).hom (pointHom T.inclusion t))
            (constants_scale (R := K) a)
          rw [Functor.map_comp, GrpCat.hom_comp, MonoidHom.comp_apply] at h
          rw [htgBase]
          exact h
        let B := (((groupPointsFunctor k).obj G.val).map
          (CommAlgCat.ofHom (dualNumberScale a))).hom
        have hAB : B = A := by dsimp only [A, B]; rw [scale_at_base]
        change tg * B v.toMul.val * tg⁻¹ = B (tg * v.toMul.val * tg⁻¹)
        rw [hAB]
        rw [map_mul, map_mul, map_inv, htg] }
  obtain ⟨I, hI, b, χ, hb, _⟩ := torusWeightBasis G T hT s
  letI := hI
  let a (i : I) := characterValue (χ i) K t
  have heig (i : I) : conj (b i) = a i • b i := by
    have h := hb i K t
    have hd : dualMap (CommAlgCat.ofHom (Algebra.ofId k K)) = 𝟙 D := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro v
      exact TrivSqZeroExt.ext (Algebra.algebraMap_self_apply v.fst) (Algebra.algebraMap_self_apply v.snd)
    dsimp only at h
    rw [hd] at h
    have hi (x : Points G.val.X D) : mapPoints (𝟙 D) x = x := by
      change (testSpec k).map (𝟙 (op D)) ≫ x = x
      simp
    erw [hi] at h
    apply Subtype.ext
    change tg * (b i).toMul.val * tg⁻¹ =
      mapPoints (CommAlgCat.ofHom (dualNumberScale (a i))) (b i).toMul.val
    rw [← scale_at_base]
    exact h
  let x₀ (i : I) := if χ i = 1 then 0 else b.equivFun w i / (1 - a i)
  let y₀ (i : I) := if χ i = 1 then b.equivFun w i else 0
  let x : V := ∑ i, x₀ i • b i
  let y : V := ∑ i, y₀ i • b i
  have hy : y ∈ adjointWeightVectors T 1 := by
    rw [← RootData.CharacterPairing.adjointWeightSpaceVectors G T s 1]
    apply Submodule.sum_mem
    intro i _
    by_cases h : χ i = 1
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (h ▸ hb i))
    · rw [show y₀ i = 0 from ite_eq_right h, zero_smul]
      exact Submodule.zero_mem _
  obtain ⟨v, hv⟩ := ((RootData.RootGroups.rootSubgroups G hG T hT hmax).1.2 ▸ hy :
    y ∈ Set.range (mapPointKernel T.inclusion))
  have he : x + y - conj x = w := by
    calc
      x + y - conj x = ∑ i, (x₀ i • b i + y₀ i • b i - conj (x₀ i • b i)) := by
        simp only [x, y, map_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = ∑ i, b.equivFun w i • b i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul, heig, smul_smul, ← add_smul, ← sub_smul]
        congr 1
        by_cases h : χ i = 1
        · simp [x₀, y₀, h]
        · have ha : a i ≠ 1 := ht (χ i) ⟨h, b i, hb i, b.ne_zero i⟩
          simp only [x₀, y₀, h, ite_false, add_zero]
          field_simp [sub_ne_zero.mpr (Ne.symm ha)]
          <;> ring
      _ = w := b.sum_equivFun w
  rw [← hv] at he
  have he' := congrArg (fun v : V => v.toMul.val) he
  change x.toMul.val * (mapPointKernel T.inclusion v).toMul.val *
      (tg * x.toMul.val * tg⁻¹)⁻¹ = z * tg⁻¹ at he'
  let tz : GroupPoints T.group D := v.toMul.val * tc
  refine ⟨lift x.toMul.val tz, ?_, ?_⟩
  · change (testSpec k).map (dualReduction k).op ≫ lift x.toMul.val tz = _
    rw [comp_lift]
    change lift (reduceTangentPoints G.val x.toMul.val) (reduceTangentPoints T.group tz) = _
    rw [show reduceTangentPoints G.val x.toMul.val = 1 from x.toMul.property,
      map_mul, show reduceTangentPoints T.group v.toMul.val = 1 from v.toMul.property,
      one_mul, constant_reduction]
  · rw [torusConjugation_eval]
    change x.toMul.val * onPoints T.inclusion D (v.toMul.val * tc) * x.toMul.val⁻¹ = z
    rw [map_mul]
    let w := onPoints T.inclusion D v.toMul.val
    change x.toMul.val * (w * tg) * x.toMul.val⁻¹ = z
    change x.toMul.val * w * (tg * x.toMul.val * tg⁻¹)⁻¹ = z * tg⁻¹ at he'
    calc
      _ = (x.toMul.val * w * (tg * x.toMul.val * tg⁻¹)⁻¹) * tg := by group
      _ = (z * tg⁻¹) * tg := congrArg (· * tg) he'
      _ = z := inv_mul_cancel_right _ _

private theorem torusConjugation_dense [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (P : OppositeBorelPair G) : DenseRange (torusConjugation P.torus).left := by
  let T := P.torus
  let X := G.val.X ⊗ T.group.X
  let : Smooth G.val.X.hom := P.reductive.1
  let : GeometricallyConnected G.val.X.hom := P.reductive.2.1
  let : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  let : IsIntegral G.val.X.left := WordDomainGeometry.smoothConnectedGroupIntegral G inferInstance inferInstance
  let : IsAffine G.val.X.left := G.property.1
  let : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  let : IsAffine T.group.X.left := (Specs.Unipotent.closedSubgroupAlgebraicGroup T).property.1
  let : IsAffine X.left := affine_tensor (A := G.val.X) (B := T.group.X)
  letI : Smooth T.group.X.hom := (EquivariantUnipotentSeries.split_torus_smooth_connected
    (Specs.Unipotent.closedSubgroupAlgebraicGroup T) P.split).1
  let h := isPullback_tensor_structure G.val.X T.group.X
  letI : Smooth (snd G.val.X T.group.X).left :=
    MorphismProperty.of_isPullback (P := @Smooth) h inferInstance
  let : Smooth X.hom := by
    rw [← Over.w (snd G.val.X T.group.X)]
    infer_instance
  obtain ⟨t, ht⟩ := regularTorusPoint T P.split
  apply denseRange_of_tangentLifts (torusConjugation T) (lift (1 : RationalPoints G.val) t)
  intro z hz
  apply conjugation_lifts G T P.reductive P.split P.maximal t ht z
  have h₁ := torusConjugation_eval T (1 : (testSpec k).obj (op (groundTest k)) ⟶ G.val.X) t
  erw [h₁, one_mul, inv_one, mul_one] at hz
  exact hz

open private rationalLift quotientAct_projection from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private quotientAction quotientAction_eval from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open private projection_eq_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding

/-- The image of the proper fixed-flag incidence contains the dense
conjugates of the torus. A lift of the fixed flag is the Borel conjugator. -/
private theorem conjugate_into_borel [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (P : OppositeBorelPair G) (s : RationalPoints G.val) :
    ∃ (g : RationalPoints G.val) (b : RationalPoints P.negative.group),
      g * s * g⁻¹ = pointHom P.negative.inclusion b := by
  obtain ⟨_, ⟨Q⟩, hQ⟩ := LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G P
  have hproper := (hQ Q).2.1
  let a := quotientAction Q
  let T := P.torus
  let Y := G.val.X ⊗ T.group.X
  let f := torusConjugation T
  let : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  let : LocallyOfFiniteType T.group.X.hom :=
    (Specs.Unipotent.closedSubgroupAlgebraicGroup T).property.2.1
  let : LocallyOfFiniteType (snd G.val.X T.group.X).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (isPullback_tensor_structure G.val.X T.group.X) inferInstance
  let : LocallyOfFiniteType Y.hom := by
    rw [← Over.w (snd G.val.X T.group.X)]
    infer_instance
  let : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hd : Dense (closedPoints Y.left) := dense_iff_closure_eq.mpr closure_closedPoints
  obtain ⟨i, hi⟩ := P.inNegative
  have hset : Dense {z : G.val.X.left |
      ∃ (p : 𝟙_ (SchemeOver k) ⟶ G.val.X) (q : 𝟙_ (SchemeOver k) ⟶ Q.scheme),
        p.left (IsLocalRing.closedPoint k) = z ∧ lift p q ≫ a.smul = q} := by
    apply ((torusConjugation_dense G P).dense_image f.left.continuous hd).mono
    rintro _ ⟨z, hz, rfl⟩
    change IsClosed {z} at hz
    let p : 𝟙_ (SchemeOver k) ⟶ Y :=
      Over.homMk (pointOfClosedPoint Y.hom z hz) (pointOfClosedPoint_comp Y.hom z hz)
    let g := p ≫ fst G.val.X T.group.X
    let t := p ≫ snd G.val.X T.group.X
    have hp : p = lift g t := by
      apply CartesianMonoidalCategory.hom_ext
      · exact (lift_fst g t).symm
      · exact (lift_snd g t).symm
    have he : p ≫ f = g * (t ≫ T.inclusion.hom.hom) * g⁻¹ :=
      (congrArg (· ≫ f) hp).trans (torusConjugation_eval T g t)
    refine ⟨p ≫ f, g ≫ Q.projection, ?_, ?_⟩
    · exact congrArg f.left (pointOfClosedPoint_apply Y.hom z hz _)
    · change lift (p ≫ f) (g ≫ Q.projection) ≫ (quotientAction Q).smul = _
      rw [quotientAction_eval, quotientAct_projection, he]
      symm
      apply (projection_eq_iff Q g _).mpr
      refine ⟨t ≫ i.hom.hom, ?_⟩
      change (t ≫ i.hom.hom) ≫ P.negative.inclusion.hom.hom = _
      rw [Category.assoc, ← show (i ≫ P.negative.inclusion).hom.hom =
        i.hom.hom ≫ P.negative.inclusion.hom.hom from rfl, hi]
      group
      rfl
  obtain ⟨p, hp⟩ := rationalPointFromUnit s
  obtain ⟨x, hx⟩ := properFixedIncidence a hproper hset p
  let : LocallyOfFinitePresentation Q.projection.left := Q.finitePresentation
  obtain ⟨g, rfl⟩ := rationalLift Q.projection Q.surjective inferInstance x
  change lift p (g ≫ Q.projection) ≫ (quotientAction Q).smul = _ at hx
  rw [quotientAction_eval, quotientAct_projection] at hx
  obtain ⟨b, hb⟩ := (projection_eq_iff Q g (p * g)).mp hx.symm
  let S := (testSpec k).obj (op (groundTest k))
  let g' : RationalPoints G.val := toUnit S ≫ g
  let b' : RationalPoints P.negative.group := toUnit S ≫ b
  refine ⟨g'⁻¹, b', ?_⟩
  rw [inv_inv]
  have he := congrArg (fun h : 𝟙_ (SchemeOver k) ⟶ G.val.X => toUnit S ≫ h) hb
  change pointHom P.negative.inclusion b' = toUnit S ≫ (g⁻¹ * (p * g)) at he
  erw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.comp_mul, hp] at he
  exact (mul_assoc _ _ _).trans he.symm

end RegularTorusGeometry

section SolvableConjugacy

open _root_.LinearAlgebraicGroups.Affine
  (RationalPoints IsRationalJordanDecomposition IsMultiplicativeJordanDecomposition
    rationalJordanDecomposition rationalJordanDecompositionFunctorial rationalRepresentationAction)
open Specs.Unipotent (IsUnipotent IsFppfGroupQuotient closedSubgroupAlgebraicGroup)
open Module

variable {k : Type u} [Field k]

private abbrev Jordan (G : AffineAlgebraicGroup k) :=
  IsRationalJordanDecomposition (⟨G.val, G.property.1⟩ : AffineGroupCategory k)

private abbrev SemisimplePoint (G : AffineAlgebraicGroup k) (x : RationalPoints G.val) :=
  Jordan G x x 1

open private conjugation conjugation_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private rationalLift from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private multiplicative_factors_eq isNilpotent_sub_one_iff_charpoly
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.LinearJordanFactors
open private Unipotent.onPoints_injective Unipotent.kernel_points
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries

private theorem pointHom_comp {G H J : GroupScheme k} (f : G ⟶ H) (g : H ⟶ J)
    (x : RationalPoints G) : pointHom (f ≫ g) x = pointHom g (pointHom f x) :=
  (Category.assoc x f.hom.hom g.hom.hom).symm

private theorem pointHom_surjective [IsAlgClosed k] {G H : GroupScheme k} (f : G ⟶ H)
    (hs : Surjective f.hom.hom.left) (hft : LocallyOfFiniteType f.hom.hom.left) :
    Function.Surjective (pointHom f) := by
  intro x
  obtain ⟨y, hy⟩ := rationalPointFromUnit x
  obtain ⟨z, hz⟩ := rationalLift f.hom.hom hs hft y
  refine ⟨toUnit _ ≫ z, ?_⟩
  change (toUnit _ ≫ z) ≫ f.hom.hom = x
  rw [Category.assoc, hz]
  exact hy

private theorem jordan_unique [PerfectField k] (G : AffineAlgebraicGroup k)
    {x s u' t v : RationalPoints G.val} (h : Jordan G x s u') (h' : Jordan G x t v) :
    s = t ∧ u' = v := by
  have hpair : (s, u') = (t, v) := (rationalJordanDecomposition G x).unique h h'
  exact Prod.mk.inj hpair

private theorem jordan_map [PerfectField k] (G H : AffineAlgebraicGroup k) (f : G.val ⟶ H.val)
    {x s u' : RationalPoints G.val} (h : Jordan G x s u') :
    Jordan H (pointHom f x) (pointHom f s) (pointHom f u') :=
  rationalJordanDecompositionFunctorial G H f h

private theorem semisimple_map [PerfectField k] (G H : AffineAlgebraicGroup k)
    (f : G.val ⟶ H.val) {x : RationalPoints G.val} (h : SemisimplePoint G x) :
    SemisimplePoint H (pointHom f x) := by
  simpa only [map_one] using jordan_map G H f h

private theorem semisimple_of_map [PerfectField k] (G H : AffineAlgebraicGroup k)
    (f : G.val ⟶ H.val) (hi : Function.Injective (pointHom f))
    {x : RationalPoints G.val} (h : SemisimplePoint H (pointHom f x)) :
    SemisimplePoint G x := by
  obtain ⟨⟨s, u'⟩, hu, _⟩ := rationalJordanDecomposition G x
  obtain ⟨hs, hu₁⟩ := jordan_unique H (jordan_map G H f hu) h
  have hx : s = x := hi hs
  have h₁ : u' = 1 := hi (hu₁.trans (map_one _).symm)
  subst s
  subst u'
  exact hu

private theorem semisimple_conjugate [PerfectField k] (G : AffineAlgebraicGroup k)
    {x : RationalPoints G.val} (h : SemisimplePoint G x) (g : RationalPoints G.val) :
    SemisimplePoint G (g * x * g⁻¹) := by
  obtain ⟨q, hq⟩ := rationalPointFromUnit g
  have he : pointHom (conjugation q) x = g * x * g⁻¹ := by
    change x ≫ (conjugation q).hom.hom = _
    erw [conjugation_apply q x, hq]
    rfl
  exact he ▸ semisimple_map G G (conjugation q) h

private theorem semisimple_factor (G : AffineAlgebraicGroup k)
    {x s u' : RationalPoints G.val} (h : Jordan G x s u') : SemisimplePoint G s := by
  refine ⟨(mul_one s).symm, Commute.one_right _, ?_⟩
  intro V I _ _ _ _ b L l f
  let φ : RationalPoints G.val →* (Matrix I I k)ˣ :=
    ((((groupPointsFunctor k).map f ≫ l.hom).app (groundTest k))).hom
  let F := rationalRepresentationAction (G := ⟨G.val, G.property.1⟩) b l f
  have hone : F 1 = 1 := by
    change Matrix.toLin b b (φ 1).val = 1
    rw [map_one, Units.val_one, Matrix.toLin_one]
    rfl
  let j := h.2.2 b L l f
  change IsMultiplicativeJordanDecomposition (F s) (F s) (F 1)
  rw [hone]
  refine ⟨(mul_one _).symm, Commute.one_right _, j.semisimple, ?_, j.isUnit_semisimple, isUnit_one⟩
  simp

/-- Two commuting points carrying the pure Jordan decompositions give
the Jordan decomposition of their product. -/
private theorem jordan_mul (G : AffineAlgebraicGroup k) {s u' : RationalPoints G.val}
    (hs : SemisimplePoint G s) (hu : Jordan G u' 1 u') (h : Commute s u') :
    Jordan G (s * u') s u' := by
  refine ⟨rfl, h, ?_⟩
  intro V I _ _ _ _ b L l f
  let φ : RationalPoints G.val →* (Matrix I I k)ˣ :=
    ((((groupPointsFunctor k).map f ≫ l.hom).app (groundTest k))).hom
  let F : RationalPoints G.val →* End k V :=
    (LinearMap.toMatrixAlgEquiv b).symm.toMonoidHom.comp ((Units.coeHom _).comp φ)
  have hj := hs.2.2 b L l f
  have hj' := hu.2.2 b L l f
  change IsMultiplicativeJordanDecomposition (F (s * u')) (F s) (F u')
  exact ⟨map_mul F s u', h.map F, hj.semisimple, hj'.unipotent,
    hj.isUnit_semisimple, hj'.isUnit_unipotent⟩

private theorem unipotent_point [PerfectField k] (U : AffineAlgebraicGroup k)
    (hU : IsUnipotent U) (x : RationalPoints U.val) : Jordan U x 1 x := by
  classical
  obtain ⟨A, ⟨e⟩, hu⟩ := hU
  have hcrit := Unipotent.unipotenceCriteria U A e
  obtain ⟨n, N, ⟨eN⟩, j, hj⟩ := hcrit.2.2.1.mp (hcrit.2.1.mp hu)
  let I := Specs.Unipotent.Index.{u} n
  let L := StandardGroups.generalLinearGroup k I
  let l := StandardGroups.generalLinearGroupPointsIso k I
  let incl : Specs.Unipotent.unitriangularPoints k n ⟶ Specs.StandardGroups.generalLinearPoints k I :=
    { app R := GrpCat.ofHom (Specs.Unipotent.upperUnitriangular I R).subtype
      naturality R S a := by ext x; rfl }
  let ρ := (groupPointsFunctor k).map j ≫ eN.hom ≫ incl
  let f : U.val ⟶ L.val := (AffineAlgebraicGroup.groupHomEquiv U L).symm (ρ ≫ l.inv)
  have hf : (groupPointsFunctor k).map f ≫ l.hom = ρ := by
    rw [show (groupPointsFunctor k).map f = ρ ≫ l.inv from
      (AffineAlgebraicGroup.groupHomEquiv U L).apply_symm_apply _, Category.assoc,
      l.inv_hom_id, Category.comp_id]
  obtain ⟨⟨s, v⟩, hJ, _⟩ := rationalJordanDecomposition U x
  let b := Pi.basisFun k I
  let F := rationalRepresentationAction (G := ⟨U.val, U.property.1⟩) b l f
  let R := groundTest k
  have hF (y : RationalPoints U.val) : F y = Matrix.toLin b b
      (eN.hom.app R (pointHom j y)).val.val := by
    have ht := congrArg (fun e => (e.app R) y) hf
    exact congrArg (fun (g : Matrix.GeneralLinearGroup I k) => Matrix.toLin b b g.val) ht
  have hone : F 1 = 1 := by
    rw [hF, map_one, map_one]
    change Matrix.toLin b b (1 : Matrix I I k) = 1
    rw [Matrix.toLin_one]
    rfl
  have hF_inj : Function.Injective F := by
    intro y y' hy
    apply Unipotent.onPoints_injective j hj R
    apply (eN.app R).groupIsoToMulEquiv.injective
    apply Subtype.ext
    apply Units.ext
    rw [hF, hF] at hy
    exact (Matrix.toLin b b).injective hy
  have hnil : IsNilpotent (F s - 1) := by
    rw [isNilpotent_sub_one_iff_charpoly, hF, Matrix.charpoly_toLin]
    let M := eN.hom.app R (pointHom j s)
    change M.val.val.charpoly = (Polynomial.X - 1) ^ finrank k (I → k)
    rw [Matrix.charpoly_of_isUpperTriangular _ M.property.1, Module.finrank_pi]
    simp only [M.property.2, map_one, Finset.prod_const, Finset.card_univ]
    rfl
  have he₁ := (semisimple_factor U hJ).2.2 b L.val l f
  change IsMultiplicativeJordanDecomposition (F s) (F s) (F 1) at he₁
  rw [hone] at he₁
  have he₂ : IsMultiplicativeJordanDecomposition (F s) 1 (F s) :=
    ⟨(one_mul _).symm, Commute.one_left _, Module.End.isSemisimple_id, hnil,
      isUnit_one, he₁.isUnit_semisimple⟩
  have hs : s = 1 := hF_inj ((multiplicative_factors_eq he₁ he₂).1.trans hone.symm)
  have hv : v = x := by simpa only [hs, one_mul] using hJ.1.symm
  exact hs ▸ hv ▸ hJ

/-- Lift the conjugacy through a one-dimensional additive kernel. When
its character has value one, a commuting unipotent discrepancy is trivial. -/
private theorem conjugate_over_additive_kernel [IsAlgClosed k] (E Y : AffineAlgebraicGroup k)
    (p : E.val ⟶ Y.val) (a : Multiplicative k →* RationalPoints E.val)
    (ha : ∀ x, pointHom p x = 1 ↔ ∃ r, a (Multiplicative.ofAdd r) = x)
    (hu : ∀ r, Jordan E (a (Multiplicative.ofAdd r)) 1 (a (Multiplicative.ofAdd r)))
    {x t : RationalPoints E.val} (hx : SemisimplePoint E x) (ht : SemisimplePoint E t)
    (hp : pointHom p x = pointHom p t) (c : k)
    (hc : ∀ r, t * a (Multiplicative.ofAdd r) * t⁻¹ = a (Multiplicative.ofAdd (c * r))) :
    ∃ g : RationalPoints E.val, g * x * g⁻¹ = t := by
  obtain ⟨r, hr⟩ := (ha (x * t⁻¹)).mp (by rw [map_mul, map_inv, hp, mul_inv_cancel])
  have hx' : x = a (Multiplicative.ofAdd r) * t := by rw [hr, inv_mul_cancel_right]
  by_cases h : c = 1
  · have hcomm : Commute t (a (Multiplicative.ofAdd r)) := by
      change t * a (Multiplicative.ofAdd r) = a (Multiplicative.ofAdd r) * t
      have h' := hc r
      rw [h, one_mul] at h'
      have he := congrArg (· * t) h'
      simpa only [inv_mul_cancel_right] using he
    have hJ := jordan_mul E ht (hu r) hcomm
    rw [hcomm.eq, ← hx'] at hJ
    have hxt := (jordan_unique E hx hJ).1
    exact ⟨1, by simpa using hxt⟩
  · let v := -r / (1 - c)
    refine ⟨a (Multiplicative.ofAdd v), ?_⟩
    have hv : v + r + c * (-v) = 0 := by
      dsimp only [v]
      field_simp [sub_ne_zero.mpr (Ne.symm h)]
      ring
    have eq : a (Multiplicative.ofAdd v) * x * (a (Multiplicative.ofAdd v))⁻¹ =
        (a (Multiplicative.ofAdd v) * a (Multiplicative.ofAdd r) *
          (t * a (Multiplicative.ofAdd (-v)) * t⁻¹)) * t := by
      rw [hx', show a (Multiplicative.ofAdd (-v)) = (a (Multiplicative.ofAdd v))⁻¹ from
        map_inv a (Multiplicative.ofAdd v)]
      group
    rw [eq, hc, ← map_mul, ← map_mul]
    change a (Multiplicative.ofAdd (v + r + c * (-v))) * t = t
    rw [hv, show Multiplicative.ofAdd (0 : k) = 1 from rfl, map_one, one_mul]

open Specs.EquivariantUnipotentSeries (IsSplitTorus)
open private Unipotent.closedSeries_inclusion_closed Unipotent.represented_quotient_of_kernel
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private Unipotent.scheme_kernel_of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries
open private liftGroupHomOfQuotient from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries
open private transitionKernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.TorusSections

/-- A semisimple point of a split extension by a smooth connected unipotent
radical is conjugate to the image under the section of its torus projection. -/
private theorem conjugate_into_split_factor [IsAlgClosed k]
    (B T : AffineAlgebraicGroup k) (U : ClosedSubgroup B.val)
    (p : B.val ⟶ T.val) (hp : IsFppfGroupQuotient U p)
    (hT : IsSplitTorus T.val) (hs : Smooth U.group.X.hom)
    (hconn : ConnectedSpace U.group.X.left) (hunip : IsUnipotent (closedSubgroupAlgebraicGroup U))
    {x t : RationalPoints B.val} (hx : SemisimplePoint B x) (ht : SemisimplePoint B t)
    (htx : pointHom p x = pointHom p t) :
    ∃ g : RationalPoints B.val, g * x * g⁻¹ = t := by
  obtain ⟨n, S, _, _, hN, hF⟩ :=
    EquivariantUnipotentSeries.stableSeriesForTorusExtension B T U p hp hT hs hconn hunip
  let j (i : ℕ) := S.inclusion i ≫ U.inclusion
  have hj (i : ℕ) : IsClosedImmersion (j i).hom.hom.left := by
    exact @IsClosedImmersion.comp _ _ _ _ _ (Unipotent.closedSeries_inclusion_closed S i) U.isClosedImmersion
  let N (i : ℕ) : ClosedSubgroup B.val := ⟨_, j i, hj i⟩
  have jnext (i : ℕ) : j (i + 1) = S.step i ≫ j i := Category.assoc ..
  have stage (i : ℕ) (hi : i ≤ n) :
      ∃ (Y : AffineAlgebraicGroup k) (q : B.val ⟶ Y.val),
        IsFppfGroupQuotient (N i) q ∧ ∃ g : RationalPoints B.val,
          pointHom q (g * x * g⁻¹) = pointHom q t := by
    induction i with
    | zero =>
      have hk : IsSchemeKernel p (N 0) :=
        Unipotent.scheme_kernel_of_iso p (j 0) (hj 0) U hp.1 S.top rfl
      refine ⟨T, p, Unipotent.represented_quotient_of_kernel p _ hk hp.2.1 hp.2.2.1 hp.2.2.2.1,
        1, ?_⟩
      simpa using htx
    | succ i ih =>
      obtain ⟨Y, q₀, hq₀, g, hg⟩ := ih (by omega)
      obtain ⟨_, _, E, q, _, _, hqk, hqf, _, hqe⟩ :=
        normalAffineQuotient B (N (i + 1)) (hN (i + 1) hi)
      have hq : IsFppfGroupQuotient (N (i + 1)) q :=
        ⟨hqk, hqf.2.1, hqf.2.2.1, hqf.2.2.2.1, hqe⟩
      have hkill : (N (i + 1)).inclusion.hom.hom ≫ q₀.hom.hom = 1 := by
        change (j (i + 1)).hom.hom ≫ q₀.hom.hom = 1
        rw [jnext]
        change ((S.step i).hom.hom ≫ (j i).hom.hom) ≫ q₀.hom.hom = 1
        rw [Category.assoc, show (j i).hom.hom ≫ q₀.hom.hom = 1 from hq₀.1.w, MonObj.comp_one]
      obtain ⟨π, hπ⟩ := liftGroupHomOfQuotient q hq q₀ hkill
      obtain ⟨Q, f, eQ, M, eM, χ, hf, hact⟩ := hF i (by omega)
      have hclose : IsClosedImmersion (S.step i ≫ j i).hom.hom.left := by
        rw [← jnext]
        exact hj (i + 1)
      have hqq : IsFppfGroupQuotient ⟨_, S.step i ≫ j i, hclose⟩ q := by
        have he : (⟨(S.term (i + 1)).val, S.step i ≫ j i, hclose⟩ : ClosedSubgroup B.val) =
            N (i + 1) := by
          change _ = (⟨(S.term (i + 1)).val, j (i + 1), hj (i + 1)⟩ : ClosedSubgroup B.val)
          revert hclose
          rw [← jnext]
          intro hclose
          rfl
        rw [he]
        exact hq
      obtain ⟨K, v, e, hK, hvf, hvs, hv, he⟩ :=
        transitionKernel (j i) (hj i) (S.step i) (S.closed i) hclose q₀ q π hπ hq₀.1 hqq f hf
      let R := groundTest k
      let eK := (groupPointsFunctor k).mapIso e.symm ≪≫ eQ
      let κ : RationalPoints K.group ≃* Multiplicative k := (eK.app R).groupIsoToMulEquiv
      let a : Multiplicative k →* RationalPoints E.val :=
        (pointHom K.inclusion).comp κ.symm.toMonoidHom
      have hker (z : RationalPoints E.val) :
          pointHom π z = 1 ↔ ∃ r, a (Multiplicative.ofAdd r) = z := by
        have hm : pointHom π z = 1 ↔ ∃ b, pointHom K.inclusion b = z :=
          Unipotent.kernel_points π K hK R z
        rw [hm]
        constructor
        · rintro ⟨y, rfl⟩
          exact ⟨(κ y).toAdd, congrArg (pointHom K.inclusion) (κ.symm_apply_apply y)⟩
        · rintro ⟨r, rfl⟩
          exact ⟨κ.symm (Multiplicative.ofAdd r), rfl⟩
      have hvlift : Function.Surjective (pointHom v) := by
        let : LocallyOfFiniteType (S.term i).val.X.hom := (S.term i).property.2.1
        let : LocallyOfFiniteType K.group.X.hom := (closedSubgroupAlgebraicGroup K).property.2.1
        let : LocallyOfFiniteType (v.hom.hom.left ≫ K.group.X.hom) := by
          rw [Over.w v.hom.hom]
          infer_instance
        have ht₁ := locallyOfFiniteType_of_comp v.hom.hom.left K.group.X.hom
        exact pointHom_surjective v hvs ht₁
      have hcoord (w : RationalPoints (S.term i).val) :
          κ (pointHom v w) = eQ.hom.app R (pointHom f w) := by
        change eQ.hom.app R (pointHom e.inv (pointHom v w)) = _
        rw [← pointHom_comp, ← he, Category.assoc, e.hom_inv_id, Category.comp_id]
      have hinc (w : RationalPoints (S.term i).val) :
          pointHom K.inclusion (pointHom v w) = pointHom q (pointHom (j i) w) := by
        rw [← pointHom_comp, hv, pointHom_comp]
      have hu' : IsUnipotent (S.term i) :=
        Unipotent.closedSubgroupsUnipotent (closedSubgroupAlgebraicGroup U)
          ⟨(S.term i).val, S.inclusion i, Unipotent.closedSeries_inclusion_closed S i⟩ hunip
      have ha (r : k) : Jordan E (a (Multiplicative.ofAdd r)) 1 (a (Multiplicative.ofAdd r)) := by
        obtain ⟨w, hw⟩ := hvlift (κ.symm (Multiplicative.ofAdd r))
        have hwa : a (Multiplicative.ofAdd r) = pointHom (j i ≫ q) w := by
          change pointHom K.inclusion (κ.symm _) = _
          rw [← hw, hinc, pointHom_comp]
        have hj := jordan_map (S.term i) E (j i ≫ q) (unipotent_point (S.term i) hu' w)
        simpa only [← hwa, map_one] using hj
      let c : k := (show kˣ from eM.hom.app R (pointHom χ (pointHom p t))).val
      have hc (r : k) : pointHom q t * a (Multiplicative.ofAdd r) * (pointHom q t)⁻¹ =
          a (Multiplicative.ofAdd (c * r)) := by
        obtain ⟨w, hw⟩ := hvlift (κ.symm (Multiplicative.ofAdd r))
        obtain ⟨z₀, hz⟩ := normalSubgroup_conjugate_sections (hN i (by omega)) t w
        let z : RationalPoints (S.term i).val := z₀
        have hz' : pointHom (j i) z = t * pointHom (j i) w * t⁻¹ := hz
        have hscalar := hact R t w z hz
        have hkz : (κ (pointHom v z)).toAdd = c * (κ (pointHom v w)).toAdd := by
          rw [hcoord z, hcoord w]
          exact hscalar
        rw [hw, κ.apply_symm_apply] at hkz
        have hzc : pointHom v z = κ.symm (Multiplicative.ofAdd (c * r)) :=
          κ.injective (by rw [κ.apply_symm_apply]; exact hkz)
        change pointHom q t * pointHom K.inclusion (κ.symm (Multiplicative.ofAdd r)) *
          (pointHom q t)⁻¹ = pointHom K.inclusion (κ.symm (Multiplicative.ofAdd (c * r)))
        rw [← hw, hinc w, ← hzc, hinc z, hz', map_mul, map_mul, map_inv]
      have hxt : pointHom π (pointHom q (g * x * g⁻¹)) = pointHom π (pointHom q t) := by
        rw [← pointHom_comp, ← pointHom_comp, hπ]
        exact hg
      obtain ⟨z, hz⟩ := conjugate_over_additive_kernel E Y π a hker ha
        (semisimple_map B E q (semisimple_conjugate B hx g)) (semisimple_map B E q ht)
        hxt c hc
      let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.2.1
      obtain ⟨w, hw⟩ := pointHom_surjective q hq.2.2.1 inferInstance z
      refine ⟨E, q, hq, w * g, ?_⟩
      rw [show (w * g) * x * (w * g)⁻¹ = w * (g * x * g⁻¹) * w⁻¹ by group,
        map_mul, map_mul, map_inv, hw, hz]
  obtain ⟨Y, q, hq, g, hg⟩ := stage n le_rfl
  have htriv (v : RationalPoints (S.term n).val) : v = 1 := by
    apply (((groupPointsFunctor k).mapIso S.bottom).app (groundTest k)).groupIsoToMulEquiv.injective
    exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  have hk (z : RationalPoints B.val) (hz : pointHom q z = 1) : z = 1 := by
    obtain ⟨v, hv⟩ := (Unipotent.kernel_points q (N n) hq.1 (groundTest k) z).mp hz
    have hv' : pointHom (j n) v = z := hv
    rw [htriv v, map_one] at hv'
    exact hv'.symm
  refine ⟨g, mul_inv_eq_one.mp (hk ((g * x * g⁻¹) * t⁻¹) ?_)⟩
  rw [map_mul, map_inv, hg, mul_inv_cancel]

end SolvableConjugacy

theorem geometricFibresFromTorusRepresentatives : GeometricFibresFromTorusRepresentatives.{u} := by
  intro torality sep k _ _ G P hG hsc
  obtain ⟨comm, D, e, b, U, hb, hU, ω, S, hw, hex, hu, hgen⟩ :=
    fundamentalGeneration G P hG hsc
  let := comm
  refine ⟨comm, D, e, b, U, hb, hU, ω, S, hw, hgen, ?_⟩
  intro x y s r v u' hx hy ht
  let i : Specs.CharacterRing.dominantWeights P ↪ Character P.torus.group :=
    ⟨Subtype.val, Subtype.val_injective⟩
  obtain ⟨h, t, hxt⟩ := torality G P hx
  obtain ⟨h', t', hyt⟩ := torality G P hy
  obtain ⟨g, hg⟩ := torusRepresentativeFibres sep G P.torus P.split e i hex hu
    (fun j => Specs.CharacterRing.simpleRep (S j)) hgen hx hy t t' h h' hxt hyt ht
  refine ⟨g, hg, ?_⟩
  intro C y₀ htor hC hy₀ hr
  exact (torusCentralizerCollapse G C y₀ htor hC hx g ((hg.trans hr).trans hy₀)).trans hy₀.symm

section GeometricConjugacy

variable {k : Type u} [Field k] [IsAlgClosed k]

open LinearAlgebraicGroups.CocharacterDynamics (multiplyFactors)
open Specs.Unipotent (IsFppfGroupQuotient closedSubgroupAlgebraicGroup)
open Specs.GeometricRadicals (IsUnipotentRadical IsSplitTorus)
open Specs.FlagLineBundle (OppositeBorelPair)
open private isPullback_tensor_structure from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit
open private Unipotent.represented_quotient_of_kernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private Unipotent.onPoints_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.CentralSeries

/-- In the split Borel decomposition the quotient is the projection of the
product with its smooth unipotent factor. -/
private theorem borelProjectionQuotient {G : AffineAlgebraicGroup k} {T B : ClosedSubgroup G.val}
    (U : ClosedSubgroup B.group) (i : T.group ⟶ B.group) (q : B.group ⟶ T.group)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U)
    (hq : i ≫ q = 𝟙 _) (hk : IsSchemeKernel q U) (hm : IsIso (multiplyFactors i U.inclusion)) :
    IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup B)
      (Q := closedSubgroupAlgebraicGroup T) U q := by
  let m := multiplyFactors i U.inclusion
  letI : IsIso m := hm
  letI : IsIso m.left := (Over.forget _).map_isIso m
  letI : Smooth U.group.X.hom := hU.1.1
  have hq' : i.hom.hom ≫ q.hom.hom = 𝟙 T.group.X :=
    congrArg (fun f : T.group ⟶ T.group => f.hom.hom) hq
  have hzero : U.inclusion.hom.hom ≫ q.hom.hom = 1 := hk.w
  have he : m ≫ q.hom.hom = fst _ _ := by
    simp only [m, multiplyFactors, MonObj.mul_comp, Category.assoc, hq',
      Category.comp_id, hzero, MonObj.comp_one, mul_one]
  have hl : m.left ≫ q.hom.hom.left = (fst T.group.X U.group.X).left :=
    congrArg Over.Hom.left he
  letI : Smooth (fst T.group.X U.group.X).left :=
    MorphismProperty.of_isPullback (P := @Smooth)
      (isPullback_tensor_structure T.group.X U.group.X).flip inferInstance
  letI : Smooth q.hom.hom.left := by
    rw [show q.hom.hom.left = inv m.left ≫ (fst T.group.X U.group.X).left by
      rw [← hl, IsIso.inv_hom_id_assoc]]
    infer_instance
  have hs : Surjective q.hom.hom.left := by
    constructor
    intro x
    refine ⟨i.hom.hom.left x, ?_⟩
    change (i.hom.hom.left ≫ q.hom.hom.left) x = x
    rw [show i.hom.hom.left ≫ q.hom.hom.left = 𝟙 _ from congrArg Over.Hom.left hq']
    rfl
  exact Unipotent.represented_quotient_of_kernel (G := closedSubgroupAlgebraicGroup B)
    (Q := closedSubgroupAlgebraicGroup T) q U hk
    (inferInstanceAs (Flat q.hom.hom.left)) hs
    (inferInstanceAs (LocallyOfFinitePresentation q.hom.hom.left))

theorem semisimpleTorusRepresentatives : SemisimpleTorusRepresentatives.{u} := by
  intro k _ _ G P x s v hx
  obtain ⟨g, b, hg⟩ := conjugate_into_borel G P s
  let B := closedSubgroupAlgebraicGroup P.negative
  let T := closedSubgroupAlgebraicGroup P.torus
  let j : B.val ⟶ G.val := P.negative.inclusion
  obtain ⟨_, _, _, _, _, _, hrad⟩ :=
    RootData.BorelPositivity.borelPositivity G P.reductive P.torus P.split P.maximal
  obtain ⟨U, i, q, hU, _, hi, hiq, hk, hm, _⟩ := hrad P.negative P.negativeBorel P.inNegative
  have hp := borelProjectionQuotient U i q hU hiq hk hm
  have hb : SemisimplePoint B b := by
    apply semisimple_of_map B G j (Unipotent.onPoints_injective j P.negative.isClosedImmersion _)
    change SemisimplePoint G (pointHom P.negative.inclusion b)
    rw [← hg]
    exact semisimple_conjugate G (semisimple_factor G hx) g
  let t : RationalPoints P.torus.group := pointHom q b
  have ht : SemisimplePoint B (pointHom i t) :=
    semisimple_map T B i (splitTorusJordan T P.split t)
  have hq : pointHom q b = pointHom q (pointHom i t) := by
    rw [← pointHom_comp, hiq]
    exact (Category.comp_id (t : Points P.torus.group.X (groundTest k))).symm
  obtain ⟨h, hh⟩ := conjugate_into_split_factor B T U q hp P.split hU.1.1 hU.1.2.1 hU.2.1 hb ht hq
  let r := pointHom P.negative.inclusion h
  refine ⟨r * g, t, ?_⟩
  rw [show (r * g) * s * (r * g)⁻¹ = r * (g * s * g⁻¹) * r⁻¹ by group, hg]
  let j₀ := pointHom j
  let b₀ : RationalPoints B.val := b
  change j₀ h * j₀ b₀ * (j₀ h)⁻¹ = pointHom P.torus.inclusion t
  calc
    _ = j₀ (h * b₀ * h⁻¹) := by simp only [map_mul, map_inv]
    _ = j₀ (pointHom i t) := congrArg j₀ hh
    _ = _ := by
      change pointHom P.negative.inclusion (pointHom i t) = _
      rw [← pointHom_comp, hi]

end GeometricConjugacy

theorem geometricFibres : GeometricFibres.{u} :=
  geometricFibresFromTorusRepresentatives semisimpleTorusRepresentatives

end
end LinearAlgebraicGroups.Arithmetic.SteinbergGeometricFibres
