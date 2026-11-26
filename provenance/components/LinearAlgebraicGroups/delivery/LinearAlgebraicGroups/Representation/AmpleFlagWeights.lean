import Specs.LinearAlgebraicGroups.Representation.AmpleFlagWeights
import LinearAlgebraicGroups.Representation.ParabolicLineWeights
import LinearAlgebraicGroups.Representation.FlagLineBundle
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Module
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj TensorProduct BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

universe u

namespace LinearAlgebraicGroups.Representation.AmpleFlagWeights

open LinearAlgebraicGroups.Specs
open Specs.AmpleFlagWeights
open Specs.AbstractPairing (Datum)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character)
open Specs.ParabolicLineWeights (LineWeightData rationalCharacter rationalCorootPairing)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

open private rationalCharacter_injective rationalCharacter_prod rationalCharacter_pow
  rationalCorootPairing_character from LinearAlgebraicGroups.Representation.ParabolicLineWeights

private theorem rationalCharacter_inv {T : ClosedSubgroup G.val} (χ : Character T.group) :
    rationalCharacter χ⁻¹ = -rationalCharacter χ := by
  change ((TensorProduct.mk ℤ ℚ (Additive (Character T.group))) 1)
    (-Additive.ofMul χ) = _
  exact map_neg _ _

/-- Choose one common multiple of the parabolic degrees and multiply each
factor by the corresponding strict simple-coroot pairing. -/
theorem characterPowerDecomposition : CharacterPowerDecomposition.{u} := by
  classical
  intro k _ G T B Bneg comm pos neg e hopp χ hχ
  let m := ∏ j : neg.base.support, neg.degree j
  have hm : 0 < m := Finset.prod_pos fun j _ ↦ (neg.lineWeight j).1
  have hdiv (j : neg.base.support) : neg.degree j ∣ m :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  let a (i : pos.base.support) := (pos.datum.rootDatum.coroot' i.val (Additive.ofMul χ)).toNat
  have ha (i : pos.base.support) :
      (a i : ℤ) = pos.datum.rootDatum.coroot' i.val (Additive.ofMul χ) :=
    Int.toNat_of_nonneg (hχ i).le
  let r (j : neg.base.support) := (m / neg.degree j) * a (e.symm j)
  have hr (j : neg.base.support) : r j * neg.degree j = m * a (e.symm j) := by
    dsimp only [r]
    rw [mul_right_comm, Nat.div_mul_cancel (hdiv j)]
  refine ⟨m, r, hm, ?_, ?_⟩
  · intro j
    have hj : 0 < a (e.symm j) := by
      have h : (0 : ℤ) < (a (e.symm j) : ℤ) := by simpa only [ha] using hχ (e.symm j)
      exact_mod_cast h
    have hp : 0 < r j * neg.degree j := hr j ▸ Nat.mul_pos hm hj
    exact Nat.pos_of_ne_zero (fun h ↦ hp.ne' (by simp [h]))
  · apply rationalCharacter_injective pos.datum
    apply sub_eq_zero.mp
    apply pos.separates
    intro i
    rw [map_sub, rationalCharacter_prod, map_sum, rationalCharacter_inv, map_neg,
      rationalCharacter_pow, map_smul, rationalCorootPairing_character]
    have hterm (j : neg.base.support) :
        rationalCorootPairing pos.datum i.val (rationalCharacter ((neg.line j).weight ^ r j)) =
          -((r j : ℚ) * (neg.degree j : ℚ) * (if j = e i then 1 else 0)) := by
      have hω : neg.fundamentalWeight j = -pos.fundamentalWeight (e.symm j) := by
        simpa only [Equiv.apply_symm_apply] using hopp (e.symm j)
      rw [rationalCharacter_pow, (neg.lineWeight j).2, hω, map_smul, map_smul, map_neg,
        pos.fundamentalPairing]
      simp only [e.symm_apply_eq, smul_eq_mul, mul_neg, mul_assoc]
    simp only [hterm]
    rw [Finset.sum_eq_single (e i)]
    · simp only [ite_true, mul_one]
      have hex : (r (e i) : ℚ) * (neg.degree (e i) : ℚ) = (m : ℚ) * (a i : ℚ) := by
        have h := hr (e i)
        rw [Equiv.symm_apply_apply] at h
        exact_mod_cast h
      rw [hex, smul_eq_mul, ← ha]
      push_cast
      ring
    · intro j _ hj
      simp [hj]
    · simp

open Specs.ProjectiveSpaces (LineFamily LineRepresentation projectiveSpace)
open Specs.QuotientEmbedding (Presentation)
open Specs.RootWeightAction (act extendVector)
open Specs.ParabolicLineWeights (ParabolicLine)

open private subgroupSections_of_affine from LinearAlgebraicGroups.Flag.QuotientEmbedding
open private normalizedLine normalizedLine_span extendVector_tmul
  from LinearAlgebraicGroups.Flag.ProjectiveSpaces
open private orbitMap_comp from LinearAlgebraicGroups.Flag.SmoothOrbit

private theorem span_eq_iff_unit_scalar {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {v w : M} (hv : Function.Injective (fun r : R ↦ r • v)) :
    Submodule.span R {w} = Submodule.span R {v} ↔ ∃ a : Rˣ, w = (a : R) • v := by
  constructor
  · intro h
    have hw : w ∈ Submodule.span R {v} := h ▸ Submodule.mem_span_singleton_self w
    have hv' : v ∈ Submodule.span R {w} := h.symm ▸ Submodule.mem_span_singleton_self v
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hv'
    have hba : b * a = 1 := hv (by
      change (b * a) • v = (1 : R) • v
      rw [mul_smul, ha, hb, one_smul])
    exact ⟨⟨a, b, by rwa [mul_comm], hba⟩, ha.symm⟩
  · rintro ⟨a, rfl⟩
    exact Submodule.span_singleton_smul_eq a.isUnit v

private theorem extendVector_smul_injective {I : Type u} {v : I → k} (hv : v ≠ 0)
    (R : TestAlgebra k) : Function.Injective (fun a : R ↦ a • extendVector R v) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : I, v i ≠ 0 := by
    by_contra! hz
    exact hv (funext hz)
  intro a b hab
  have h := congrFun hab i
  change a * algebraMap k R (v i) = b * algebraMap k R (v i) at h
  exact (IsUnit.mk0 (v i) hi |>.map (algebraMap k R)).mul_right_cancel h

private def basisLine {J W : Type u} [Finite J] [AddCommGroup W] [Module k W]
    (b : Basis J k W) (i : J) : LineFamily k W (𝟙_ (SchemeOver k)) where
  line R _ := (normalizedLine k b i R ⟨1 ⊗ₜ[k] b i, by simp⟩).val
  compatible := by
    intro R S a _
    simp only [normalizedLine_span]
    change Submodule.span S {1 ⊗ₜ[k] b i} =
      Specs.ProjectiveSpaces.changeLineSubmodule k W a (Submodule.span R {1 ⊗ₜ[k] b i})
    rw [ProjectiveSpaces.changeLineSubmodule_span, Set.image_singleton, extendVector_tmul, map_one]

private def vectorLine {W : Type u} [AddCommGroup W] [Module k W] [Module.Finite k W]
    {v : W} (hv : v ≠ 0) : LineFamily k W (𝟙_ (SchemeOver k)) := by
  classical
  let h : LinearIndepOn k id ({v} : Set W) := (linearIndepOn_singleton_iff k).mpr hv
  let b := Basis.extend h
  let i : h.extend (Set.subset_univ _) := ⟨v, Basis.subset_extend h (Set.mem_singleton v)⟩
  haveI : Finite (h.extend (Set.subset_univ _)) := Module.Finite.finite_basis b
  exact basisLine b i

private theorem vectorLine_span {W : Type u} [AddCommGroup W] [Module k W] [Module.Finite k W]
    {v : W} (hv : v ≠ 0) (R : TestAlgebra k) (t : Points (𝟙_ (SchemeOver k)) R) :
    ((vectorLine hv).line R t).submodule = Submodule.span R {1 ⊗ₜ[k] v} := by
  unfold vectorLine basisLine
  simp only [normalizedLine_span, Basis.extend_apply_self]
  rfl

private theorem vectorCoordinates_tmul {I : Type u} [Fintype I] [DecidableEq I]
    (R : TestAlgebra k) (v : I → k) :
    vectorCoordinates R (1 ⊗ₜ[k] v) = extendVector R v := by
  ext i
  simp [vectorCoordinates, extendVector, Basis.equivFun_apply, Basis.baseChange_repr_tmul,
    Algebra.smul_def]

private theorem vectorCoordinates_transport {I : Type u} [Fintype I] [DecidableEq I]
    (R : TestAlgebra k) (A : Matrix.GeneralLinearGroup I R) (w : R ⊗[k] (I → k)) :
    vectorCoordinates R (Specs.PluckerEmbedding.matrixTransport (Pi.basisFun k I) R A w) =
      A.val.mulVec (vectorCoordinates R w) := by
  let e := vectorCoordinates R (I := I)
  change e (e.symm (A.val.mulVec (e w))) = _
  exact e.apply_symm_apply _

private theorem matrixTransport_orbitVector {T B : ClosedSubgroup G.val}
    {U : ClosedSubgroup B.group} {H : ClosedSubgroup G.val}
    (L : ParabolicLine (T := T) U H) (R : TestAlgebra k) (g : Points G.val.X R) :
    letI := L.finite
    letI := L.decidable
    Specs.PluckerEmbedding.matrixTransport (Pi.basisFun k L.index) R
      (L.representation.app R g) (1 ⊗ₜ[k] L.vector) = orbitVector L R g := by
  letI := L.finite
  letI := L.decidable
  apply (vectorCoordinates R).injective
  rw [vectorCoordinates_transport, vectorCoordinates_tmul]
  exact ((vectorCoordinates R).apply_symm_apply _).symm

/-- The projective orbit of the given parabolic line is the same right
quotient by the scheme stabilizer. Properness then closes the orbit. -/
theorem parabolicOrbitEmbeddings : ParabolicOrbitEmbeddings.{u} := by
  intro k _ G hs T B U H hH L Q ρ
  letI := L.finite
  letI := L.decidable
  let W := L.index → k
  let M := LinearAlgebraicGroups.StandardGroups.generalLinearGroup k L.index
  let E := LinearAlgebraicGroups.StandardGroups.generalLinearGroupPointsIso k L.index
  let F := LinearAlgebraicGroups.groupHomEquiv G.val M.val G.property.1
  let f := F.symm (L.representation ≫ E.inv)
  have hf (R : TestAlgebra k) (g : Points G.val.X R) :
      E.hom.app R (g ≫ f.hom.hom) = L.representation.app R g := by
    have hF : (groupPointsFunctor k).map f = L.representation ≫ E.inv :=
      F.apply_symm_apply (L.representation ≫ E.inv)
    let g₀ : GroupPoints G.val R := g
    have h := congrArg (fun z ↦ z.app R g₀) hF
    change g ≫ f.hom.hom = E.inv.app R (L.representation.app R g) at h
    rw [h]
    exact (E.app R).inv_hom_id_apply _
  let L₀ : LineFamily k W (𝟙_ (SchemeOver k)) := vectorLine (k := k) L.primitive.1
  let x := (ρ.points _).symm L₀
  obtain ⟨a, O, hact, hstab⟩ :=
    LinearAlgebraicGroups.SmoothOrbit.linearProjectiveOrbit k W L.index (Pi.basisFun k L.index)
      G M.val E f ρ L₀ hs
  have heq (R : TestAlgebra k) (g : Points G.val.X R) :
      g ∈ SubgroupSections O.stabilizer ((testSpec k).obj (op R)) ↔
        g ∈ SubgroupSections H ((testSpec k).obj (op R)) := by
    rw [hstab, vectorLine_span, hf, Submodule.map_span, Set.image_singleton]
    let v := Specs.PluckerEmbedding.matrixTransport (Pi.basisFun k L.index) R
      (L.representation.app R g) (1 ⊗ₜ[k] L.vector)
    have hv : v = orbitVector L R g := matrixTransport_orbitVector L R g
    change Submodule.span R {v} = Submodule.span R {1 ⊗ₜ[k] L.vector} ↔ _
    rw [hv,
      ← (Submodule.map_injective_of_injective (vectorCoordinates R).injective).eq_iff,
      Submodule.map_span, Submodule.map_span, Set.image_singleton, Set.image_singleton]
    change Submodule.span R {vectorCoordinates R (orbitVector L R g)} =
      Submodule.span R {vectorCoordinates R (1 ⊗ₜ[k] L.vector)} ↔ _
    have hvec : vectorCoordinates R (orbitVector L R g) =
        act L.representation R g (extendVector R L.vector) :=
      (vectorCoordinates R).apply_symm_apply _
    rw [vectorCoordinates_tmul, hvec]
    exact (span_eq_iff_unit_scalar (extendVector_smul_injective L.primitive.1 R)).trans
      (L.stabilizer R g)
  have hHstab : RepresentsSubgroup H (fun _ g ↦ Stabilizes a.smul x g) := by
    intro S g
    exact (O.representsStabilizer S g).trans
      (subgroupSections_of_affine G.property.1 heq S g)
  let i := O.openInClosure ≫ Specs.SmoothOrbit.closureInclusion a x
  haveI : IsOpenImmersion O.openInClosure.left := O.isOpen
  haveI : IsImmersion i.left := by
    change IsImmersion (O.openInClosure.left ≫ (Specs.SmoothOrbit.orbitMap a x).left.imageι)
    infer_instance
  have hi : O.projection ≫ i = Specs.SmoothOrbit.orbitMap a x := by
    apply Over.OverMorphism.ext
    change O.projection.left ≫
      (O.openInClosure.left ≫ (Specs.SmoothOrbit.orbitMap a x).left.imageι) = _
    rw [← Category.assoc, O.factors, Scheme.Hom.toImage_imageι]
  obtain ⟨e, he⟩ := LinearAlgebraicGroups.SmoothOrbit.orbitQuotient k G.val _ _ a x i
    O.projection H (Over.mono_of_mono_left i) hi O.flat O.surjective O.finitePresentation hHstab
  let Q' : Presentation H := ⟨O.orbit,
    ⟨W, inferInstance, inferInstance, inferInstance, i, inferInstance⟩,
    O.projection, O.flat, O.surjective, O.finitePresentation, e, he⟩
  obtain ⟨iso, hiso, _⟩ := LinearAlgebraicGroups.HomogeneousQuotient.quotientUniqueness Q Q'
  let j := iso.hom ≫ i
  have hj : Q.projection ≫ j = Specs.SmoothOrbit.orbitMap a x := by
    rw [← Category.assoc, hiso, hi]
  haveI : IsImmersion j.left := by
    change IsImmersion (iso.hom.left ≫ i.left)
    infer_instance
  haveI : IsProper (projectiveSpace k W).hom :=
    LinearAlgebraicGroups.ProjectiveSpaces.projectiveSpaceProper k W
  haveI : IsProper (j.left ≫ (projectiveSpace k W).hom) :=
    Over.w j ▸ ((LinearAlgebraicGroups.ProjectiveFlags.smoothProjectiveQuotient k G H hH).2 Q).2.1
  haveI : IsProper j.left := IsProper.of_comp j.left (projectiveSpace k W).hom
  refine ⟨j, IsClosedImmersion.of_isPreimmersion j.left j.left.isClosedMap.isClosed_range, ?_⟩
  intro R g
  let y : Points (projectiveSpace k W) R := toUnit _ ≫ x
  have hy : ((ρ.points _ y).line R (𝟙 _)).submodule = Submodule.span R {1 ⊗ₜ[k] L.vector} := by
    dsimp only [y, x]
    rw [ρ.naturality, Equiv.apply_symm_apply]
    exact vectorLine_span L.primitive.1 R (toUnit ((testSpec k).obj (op R)))
  have hn : ((ρ.points _ j).line R (g ≫ Q.projection)).submodule =
      ((ρ.points _ ((g ≫ Q.projection) ≫ j)).line R (𝟙 _)).submodule := by
    have h := congrArg (fun M : LineFamily k W ((testSpec k).obj (op R)) ↦
      (M.line R (𝟙 _)).submodule) (ρ.naturality (g ≫ Q.projection) j)
    simpa only [LineFamily.pullback, Category.id_comp] using h.symm
  have hg : g ≫ Specs.SmoothOrbit.orbitMap a x = lift g y ≫ a.smul := orbitMap_comp a x g
  change ((ρ.points _ j).line R (g ≫ Q.projection)).submodule = _
  rw [hn, Category.assoc, hj, hg, hact, hy, hf, Submodule.map_span, Set.image_singleton]
  exact congrArg (fun w ↦ Submodule.span R {w}) (matrixTransport_orbitVector L R g)

open Specs.CharacterDescent (Cocharacter)
open LinearAlgebraicGroups.CocharacterDynamics
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.BorelsAndChambers (IsRegular positiveRoots)
open Specs.FlagLineBundle (OppositeBorelPair)

open private evalLaurent orbit_eval polynomialConstants polynomialConstants_laurent
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

/-- A polynomial family in an affine scheme that lands in a closed subscheme
on the punctured line already lands in it over the whole line. -/
private theorem polynomial_factors {H : ClosedSubgroup G.val} {R : TestAlgebra k}
    (y : GroupPoints G.val (polynomialAlgebra R))
    (h : ∃ z : GroupPoints H.group (laurentAlgebra R),
      z ≫ H.inclusion.hom.hom = mapPoints (polynomialToLaurent R) y) :
    ∃ z : GroupPoints H.group (polynomialAlgebra R), z ≫ H.inclusion.hom.hom = y := by
  letI := G.property.1
  letI := H.isClosedImmersion
  have ha : IsAffine H.group.X.left := isAffine_of_isAffineHom H.inclusion.hom.hom.left
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr G.property.1
  obtain ⟨D, ⟨d⟩⟩ := (essImage_algSpec (R := CommRingCat.of k)).mpr ha
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let f : A.unop ⟶ D.unop := (F.preimage (d.hom ≫ H.inclusion.hom.hom ≫ e.inv)).unop
  let g : A.unop ⟶ polynomialAlgebra R := (F.preimage (y ≫ e.inv)).unop
  have hf : (testSpec k).map f.op = d.hom ≫ H.inclusion.hom.hom ≫ e.inv := F.map_preimage _
  have hg : (testSpec k).map g.op = y ≫ e.inv := F.map_preimage _
  let q := CommRingCat.ofHom f.hom.toRingHom
  haveI : IsClosedImmersion (Spec.map q) := by
    change IsClosedImmersion ((testSpec k).map f.op).left
    rw [hf]
    change IsClosedImmersion (d.hom.left ≫ H.inclusion.hom.hom.left ≫ e.inv.left)
    infer_instance
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map q)).2
  have he : (Scheme.ΓSpecIso _).inv ≫ (Spec.map q).appTop ≫ (Scheme.ΓSpecIso _).hom = q := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hfs : Function.Surjective f.hom := by
    change Function.Surjective q
    rw [← he]
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of D.unop)).hom).2.comp
      (hs.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A.unop)).inv).2)
  obtain ⟨z, hz⟩ := h
  let z' : D.unop ⟶ laurentAlgebra R := (F.preimage (z ≫ d.inv)).unop
  have hz' : (testSpec k).map z'.op = z ≫ d.inv := F.map_preimage _
  have hc : f ≫ z' = g ≫ polynomialToLaurent R := by
    apply Quiver.Hom.op_inj
    apply F.map_injective
    simp only [op_comp, Functor.map_comp, hf, hg, hz', Category.assoc, Iso.inv_hom_id_assoc]
    change z ≫ H.inclusion.hom.hom ≫ e.inv = (mapPoints (polynomialToLaurent R) y) ≫ e.inv
    rw [← Category.assoc, hz]
  have hk : RingHom.ker f.hom.toRingHom ≤ RingHom.ker g.hom.toRingHom := by
    intro a ha
    apply Polynomial.toLaurent_injective
    change (g ≫ polynomialToLaurent R).hom a = Polynomial.toLaurent 0
    rw [← hc, map_zero]
    change z'.hom (f.hom a) = 0
    rw [show f.hom a = 0 from ha, map_zero]
  let w : D.unop ⟶ polynomialAlgebra R :=
    CommAlgCat.ofHom (AlgHom.liftOfSurjective f.hom hfs g.hom hk)
  have hw : f ≫ w = g := CommAlgCat.hom_ext (AlgHom.liftOfSurjective_comp _ _ _ _)
  refine ⟨(testSpec k).map w.op ≫ d.hom, ?_⟩
  apply (cancel_mono e.inv).mp
  simp only [Category.assoc, ← hf, ← Functor.map_comp, ← op_comp, hw, hg]

private def diagonalPolynomial (R : TestAlgebra k) :
    polynomialAlgebra (polynomialAlgebra R) ⟶ polynomialAlgebra R :=
  CommAlgCat.ofHom ((Polynomial.aeval (Polynomial.X : Polynomial R)).restrictScalars k)

private theorem diagonalPolynomial_compare (R : TestAlgebra k) :
    diagonalPolynomial R ≫ polynomialToLaurent R =
      polynomialToLaurent (polynomialAlgebra R) ≫
        evalLaurent (polynomialToLaurent R) (laurentParameter R) := by
  apply CommAlgCat.hom_ext
  apply Polynomial.algHom_ext'
  · apply AlgHom.ext
    intro a
    change Polynomial.toLaurent (Polynomial.aeval (Polynomial.X : Polynomial R) (Polynomial.C a)) =
      LaurentPolynomial.eval₂ Polynomial.toLaurent (laurentParameter R)
        (Polynomial.toLaurent (Polynomial.C a))
    simp only [Polynomial.aeval_C, Polynomial.toLaurent_C, LaurentPolynomial.eval₂_C,
      Algebra.algebraMap_self_apply]
  · change Polynomial.toLaurent (Polynomial.aeval (Polynomial.X : Polynomial R) Polynomial.X) =
      LaurentPolynomial.eval₂ Polynomial.toLaurent (laurentParameter R)
        (Polynomial.toLaurent Polynomial.X)
    simp only [Polynomial.aeval_X, Polynomial.toLaurent_X, LaurentPolynomial.eval₂_T, zpow_one]
    rfl

private theorem cocharacterPoint_product {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] (c d : Cocharacter T.group) (R : TestAlgebra k) (s : Rˣ) :
    cocharacterPoint ((c * d) ≫ T.inclusion) R s =
      cocharacterPoint (c ≫ T.inclusion) R s * cocharacterPoint (d ≫ T.inclusion) R s := by
  let t := unitPoint R s
  let h := ((groupPointsFunctor k).map T.inclusion).app R
  change h (t ≫ (c * d).hom.hom) = h (t ≫ c.hom.hom) * h (t ≫ d.hom.hom)
  rw [← map_mul]
  exact congrArg h (MonObj.comp_mul t c.hom.hom d.hom.hom)

private theorem cocharacterPoint_commute {T : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] (c d : Cocharacter T.group) (R : TestAlgebra k) (s : Rˣ) :
    Commute (cocharacterPoint (c ≫ T.inclusion) R s)
      (cocharacterPoint (d ≫ T.inclusion) R s) := by
  rw [Commute, SemiconjBy, ← cocharacterPoint_product, ← cocharacterPoint_product, mul_comm c d]

/-- Regularity of conjugation along the factors in a split torus implies
regularity along their product. The second extension takes the first
polynomial family as a point over the first polynomial ring. -/
private theorem hasExtension_product {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (c d : Cocharacter T.group) (D : LimitDecomposition (d ≫ T.inclusion))
    (hTP : IsSubgroupOf T D.parabolic) (R : TestAlgebra k) (g : GroupPoints G.val R)
    (hc : HasExtension (c ≫ T.inclusion) g) (hd : HasExtension (d ≫ T.inclusion) g) :
    HasExtension ((c * d) ≫ T.inclusion) g := by
  obtain ⟨j, hj⟩ := hTP
  obtain ⟨x, hx⟩ := (D.parabolic_points R g).mp hd
  obtain ⟨_, y, hy, _⟩ := hc
  let S := laurentAlgebra R
  let s := laurentParameter R
  let t := cocharacterPoint (c ≫ j) S s
  let x' : GroupPoints D.parabolic.group S := mapPoints (laurentConstants R) x
  let z : GroupPoints D.parabolic.group S := t * x' * t⁻¹
  have hz : z ≫ D.parabolic.inclusion.hom.hom = mapPoints (polynomialToLaurent R) y := by
    rw [hy]
    let f := ((groupPointsFunctor k).map D.parabolic.inclusion).app S
    change f (t * x' * t⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    have ht : f t = cocharacterPoint (c ≫ T.inclusion) S s := by
      change (unitPoint S s ≫ c.hom.hom ≫ j.hom.hom) ≫ D.parabolic.inclusion.hom.hom =
        unitPoint S s ≫ c.hom.hom ≫ T.inclusion.hom.hom
      have h := congrArg (fun b : T.group ⟶ G.val ↦ b.hom.hom) hj
      change j.hom.hom ≫ D.parabolic.inclusion.hom.hom = T.inclusion.hom.hom at h
      simp only [Category.assoc, h]
    have hx' : f x' = mapPoints (laurentConstants R) g := by
      change x ≫ D.parabolic.inclusion.hom.hom = g at hx
      change (mapPoints (laurentConstants R) x) ≫ D.parabolic.inclusion.hom.hom = _
      simpa only [mapPoints, Category.assoc] using congrArg (mapPoints (laurentConstants R)) hx
    rw [ht, hx']
    rfl
  obtain ⟨yp, hyp⟩ := polynomial_factors y ⟨z, hz⟩
  have hdy : HasExtension (d ≫ T.inclusion) y :=
    (D.parabolic_points _ _).mpr ⟨yp, hyp⟩
  obtain ⟨_, w, hw, _⟩ := hdy
  let v := mapPoints (diagonalPolynomial R) w
  refine ⟨mapPoints (polynomialEvaluate R 0) v, v, ?_, rfl⟩
  rw [← mapPoints_comp, diagonalPolynomial_compare, mapPoints_comp, hw, orbit_eval, hy]
  let a := cocharacterPoint (c ≫ T.inclusion) S s
  let b := cocharacterPoint (d ≫ T.inclusion) S s
  let ab := cocharacterPoint ((c * d) ≫ T.inclusion) S s
  let xS : GroupPoints G.val S := mapPoints (laurentConstants R) g
  change b * (a * xS * a⁻¹) * b⁻¹ = ab * xS * ab⁻¹
  have hab : ab = a * b := cocharacterPoint_product c d S s
  rw [hab]
  calc
    _ = (b * a) * xS * (b * a)⁻¹ := by simp only [mul_inv_rev, mul_assoc]
    _ = _ := by rw [(cocharacterPoint_commute d c S s).eq]

open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.CharacterPairing (pairing)
open Specs.SimpleRoots (evaluate)
open Specs.StandardParabolicLevi (HasFace leviRoots)
open private evaluate_root from LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

private theorem subgroupSections_mono {H J : ClosedSubgroup G.val} (h : IsSubgroupOf H J)
    {S : SchemeOver k} {g : S ⟶ G.val.X} (hg : g ∈ SubgroupSections H S) :
    g ∈ SubgroupSections J S := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨x, hx⟩ := hg
  refine ⟨x ≫ i.hom.hom, ?_⟩
  change x ≫ H.inclusion.hom.hom = g at hx
  change (x ≫ i.hom.hom) ≫ J.inclusion.hom.hom = g
  have he : i.hom.hom ≫ J.inclusion.hom.hom = H.inclusion.hom.hom :=
    congrArg (fun f : H.group ⟶ G.val ↦ f.hom.hom) hi
  rw [Category.assoc, he, hx]

private theorem regular_for_positive_simple_pairings {T B : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] (L : LineWeightData T B) (c : Cocharacter T.group)
    (hc : ∀ i : L.base.support, 0 < pairing T.group i.val.val c) :
    IsRegular T c ∧ positiveRoots T c = subgroupRoots T B := by
  have hf : HasFace L.base ∅ c := by
    refine ⟨by simp, fun i hi ↦ hc ⟨i, hi.1⟩⟩
  have hl : leviRoots L.datum ∅ = ∅ := by
    ext i
    simp [leviRoots, L.datum.rootDatum.ne_zero i]
  refine ⟨?_, ?_⟩
  · intro i hi
    have hz := (LinearAlgebraicGroups.Flag.StandardParabolicLevi.face_root_signs
      L.positive L.isBase hf i).1.mp hi
    simp only [hl, Set.mem_empty_iff_false] at hz
  · simpa only [hl, Set.sdiff_empty] using
      LinearAlgebraicGroups.Flag.StandardParabolicLevi.face_positive_roots
        L.regular L.positive L.isBase hf

/-- The intersection of the omitted-simple-root standard parabolics is the
Borel, checked on every affine test and hence on arbitrary base schemes. -/
private theorem parabolic_intersection {T B : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] (L : LineWeightData T B)
    (hG : Specs.GeometricRadicals.IsReductive G)
    (hT : Specs.GeometricRadicals.IsSplitTorus T.group)
    (hTm : Specs.RankOneFlag.IsGeometricallyMaximal T)
    (hB : Specs.GeometricBorelConjugacy.IsKBorel B) (hTB : IsSubgroupOf T B)
    {S : SchemeOver k} (g : S ⟶ G.val.X) :
    (∀ i, g ∈ SubgroupSections (L.parabolic i).limitGroups.parabolic S) ↔
      g ∈ SubgroupSections B S := by
  classical
  let c (i : L.base.support) := (L.parabolic i).cocharacter
  let d := ∏ i : L.base.support, c i
  have hd (i : L.base.support) : 0 < pairing T.group i.val.val d := by
    have hsum : pairing T.group i.val.val d =
        ∑ j : L.base.support, pairing T.group i.val.val (c j) := by
      simp only [d, ← evaluate_root L.datum]
      let f := L.datum.rootDatum.toLinearMap (L.datum.rootDatum.root i.val)
      change f (Additive.ofMul (∏ j, c j)) = ∑ j, f (Additive.ofMul (c j))
      rw [ofMul_prod, map_sum]
    rw [hsum, Finset.sum_eq_single i]
    · apply (L.parabolic i).face.2 i.val
      exact ⟨i.property, fun h ↦ h.2 rfl⟩
    · intro j _ hji
      exact (L.parabolic j).face.1 i.val ⟨i.property, fun h ↦ hji (Subtype.ext h.symm)⟩
    · simp
  have ⟨hdreg, hdpos⟩ := regular_for_positive_simple_pairings L d hd
  obtain ⟨D⟩ := existsLimitDecomposition G (d ≫ T.inclusion)
  obtain ⟨_, hD, hTD, hDroots, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel G hG T hT hTm d hdreg D
  have hpos := (RootData.BorelsAndChambers.positiveSystemsFromCocharacters G hG T hT hTm _).2
    ⟨d, hdreg, hdpos⟩
  obtain ⟨B₀, _, _, hr₀, hb₀⟩ :=
    ((RootData.BorelsAndChambers.borelsThroughT G hG T hT hTm).2 _).1 hpos
  have hDB := subgroupOf_trans (hb₀ D.parabolic hD hTD (hDroots.trans hdpos)).2
    (hb₀ B hB hTB rfl).1
  refine ⟨?_, fun h i ↦ subgroupSections_mono (L.parabolic i).containsBorel h⟩
  intro h
  rw [← show (∃ p : S ⟶ B.group.X, p ≫ B.inclusion.hom.hom = g) ↔
    g ∈ SubgroupSections B S from Iff.rfl]
  apply (factorsThroughClosed_iff B.inclusion.hom.hom B.isClosedImmersion g).2
  intro R a
  let x : GroupPoints G.val R := a ≫ g
  have hfactor (i : L.base.support) :
      HasExtension (c i ≫ T.inclusion) x := by
    obtain ⟨q, hq⟩ := h i
    change q ≫ (L.parabolic i).limitGroups.parabolic.inclusion.hom.hom = g at hq
    exact ((L.parabolic i).limitGroups.parabolic_points R x).2
      ⟨a ≫ q, by
        change (a ≫ q) ≫ (L.parabolic i).limitGroups.parabolic.inclusion.hom.hom = a ≫ g
        rw [Category.assoc, hq]⟩
  have hp (s : Finset L.base.support) :
      HasExtension ((∏ i ∈ s, c i) ≫ T.inclusion) x := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.prod_empty]
        let v : GroupPoints G.val (polynomialAlgebra R) := mapPoints (polynomialConstants R) x
        refine ⟨mapPoints (polynomialEvaluate R 0) v, v, ?_, rfl⟩
        rw [← mapPoints_comp, polynomialConstants_laurent]
        let S := laurentAlgebra R
        let s := laurentParameter R
        have hone : cocharacterPoint ((1 : Cocharacter T.group) ≫ T.inclusion) S s = 1 := by
          change unitPoint S s ≫ (1 : Cocharacter T.group).hom.hom ≫
            T.inclusion.hom.hom = (1 : GroupPoints G.val S)
          rw [← Category.assoc, show (1 : Cocharacter T.group).hom.hom = 1 from rfl,
            MonObj.comp_one, MonObj.one_comp]
        let z : GroupPoints G.val S := mapPoints (laurentConstants R) x
        let t := cocharacterPoint ((1 : Cocharacter T.group) ≫ T.inclusion) S s
        change z = t * z * t⁻¹
        rw [show t = 1 from hone, one_mul, inv_one, mul_one]
    | insert i s hi ih =>
        rw [Finset.prod_insert hi, mul_comm]
        exact hasExtension_product _ _ (L.parabolic i).limitGroups
          (subgroupOf_trans hTB (L.parabolic i).containsBorel) R x ih (hfactor i)
  exact subgroupSections_mono hDB ((D.parabolic_points R x).1 (hp Finset.univ))

theorem oppositeParabolicIntersection : OppositeParabolicIntersection.{u} := by
  intro k _ G P _ neg S g
  exact parabolic_intersection neg P.reductive P.split P.maximal P.negativeBorel P.inNegative g

open private quotientMapExists from LinearAlgebraicGroups.Reductive.BorelProper
open private projection_eq_iff from LinearAlgebraicGroups.Flag.QuotientEmbedding

private theorem quotient_pullback_epi {H : ClosedSubgroup G.val} (Q : Presentation H)
    {S : SchemeOver k} (a : S ⟶ Q.scheme) : Epi (pullback.snd Q.projection a) := by
  let f := pullback.snd Q.projection a
  have hp := (IsPullback.of_hasPullback Q.projection a).map (Over.forget _)
  haveI : Flat f.left := MorphismProperty.of_isPullback (P := @Flat) hp Q.flat
  haveI : Surjective f.left := MorphismProperty.of_isPullback (P := @Surjective) hp Q.surjective
  haveI : LocallyOfFinitePresentation f.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hp Q.finitePresentation
  haveI : Epi f.left := inferInstance
  exact Over.epi_of_epi_left f

/-- If the quotients on the factors separate the cosets on every test scheme,
their product is a monomorphism. -/
private theorem quotient_product_mono {I : Type u} [Finite I] {H : ClosedSubgroup G.val}
    (Q : Presentation H) (J : I → ClosedSubgroup G.val) (D : ∀ i, Presentation (J i))
    {X : I → SchemeOver k}
    (q : ∀ i, Q.scheme ⟶ (D i).scheme)
    (hq : ∀ i, Q.projection ≫ q i = (D i).projection)
    (j : ∀ i, (D i).scheme ⟶ X i) (hj : ∀ i, Mono (j i))
    (h : ∀ (S : SchemeOver k) (g : S ⟶ G.val.X),
      (∀ i, g ∈ SubgroupSections (J i) S) → g ∈ SubgroupSections H S) :
    Mono (Limits.Pi.lift (fun i ↦ q i ≫ j i)).left := by
  let f : Q.scheme ⟶ ∏ᶜ X := Limits.Pi.lift (fun i ↦ q i ≫ j i)
  haveI : Mono f := by
    constructor
    intro S a b hab
    let u : pullback Q.projection a ⟶ S := pullback.snd Q.projection a
    let v : pullback Q.projection (u ≫ b) ⟶ pullback Q.projection a :=
      pullback.snd Q.projection (u ≫ b)
    haveI : Epi u := quotient_pullback_epi Q a
    haveI : Epi v := quotient_pullback_epi Q (u ≫ b)
    let c := v ≫ pullback.fst Q.projection a
    let d := pullback.fst Q.projection (u ≫ b)
    have hc : c ≫ Q.projection = v ≫ u ≫ a := by
      rw [Category.assoc, pullback.condition]
    have hd : d ≫ Q.projection = v ≫ u ≫ b := by
      exact pullback.condition
    apply (cancel_epi u).mp
    apply (cancel_epi v).mp
    rw [← hc, ← hd]
    apply (projection_eq_iff Q c d).2
    apply h
    intro i
    apply (projection_eq_iff (D i) c d).1
    have hi : a ≫ q i = b ≫ q i := by
      haveI := hj i
      apply (cancel_mono (j i)).mp
      have hπ : f ≫ Limits.Pi.π X i = q i ≫ j i := Limits.Pi.lift_comp_π _ _
      have he := congrArg (fun w ↦ w ≫ Limits.Pi.π X i) hab
      simpa only [Category.assoc, hπ] using he
    rw [← hq i, ← Category.assoc c, ← Category.assoc d, hc, hd]
    simp only [Category.assoc, hi]
  exact (inferInstance : Mono f.left)

open Specs.FlagLineBundle (BorelProjection)
open Specs.CharacterPairing (characterValue)
open Specs.RootWeightAction (mem_fixedSpace mem_weightSpace)
open private characterValue_restrict characterValue_unit from LinearAlgebraicGroups.Representation.ParabolicLineWeights
open private characterValue_mul characterValue_one characterValue_natural act_mul act_smul
  act_extend_natural
  from LinearAlgebraicGroups.Representation.RootWeightAction
open private unitEquiv from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private theorem characterValue_inv {H : GroupScheme k} (χ : Character H)
    (R : TestAlgebra k) (t : GroupPoints H R) :
    characterValue χ⁻¹ R t = characterValue χ R t⁻¹ := by
  rw [characterValue_unit, characterValue_unit]
  congr 1
  rw [show (χ⁻¹).hom.hom = χ.hom.hom⁻¹ from rfl, GrpObj.comp_inv, GrpObj.inv_comp]

private theorem characterValue_mul_points {H : GroupScheme k} (χ : Character H)
    (R : TestAlgebra k) (g h : GroupPoints H R) :
    characterValue χ R (g * h) = characterValue χ R g * characterValue χ R h := by
  rw [characterValue_unit, characterValue_unit, characterValue_unit]
  rw [MonObj.mul_comp, map_mul, Units.val_mul]

private theorem characterValue_prod {I : Type*} {H : GroupScheme k}
    (s : Finset I) (α : I → Character H) (R : TestAlgebra k) (t : GroupPoints H R) :
    characterValue (∏ i ∈ s, α i) R t = ∏ i ∈ s, characterValue (α i) R t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [characterValue_one]
  | insert i s hi ih =>
      simp [Finset.prod_insert hi, characterValue_mul, ih]

/-- The primitive vector for the negative Borel transforms by the character
of its torus weight pulled back along the specified split projection. -/
private theorem oppositeBorel_scalar {P : OppositeBorelPair G}
    [IsCommMonObj P.torus.group.X] (L : LineWeightData P.torus P.negative)
    (p : BorelProjection P) (i : L.base.support) (R : TestAlgebra k)
    (b : GroupPoints P.negative.group R) :
    letI := (L.line i).finite
    letI := (L.line i).decidable
    act (L.line i).representation R (b ≫ P.negative.inclusion.hom.hom)
      (extendVector R (L.line i).vector) =
      characterValue (p.projection ≫ (L.line i).weight) R b •
        extendVector R (L.line i).vector := by
  let l := L.line i
  letI := l.finite
  letI := l.decidable
  let t : GroupPoints P.torus.group R := b ≫ p.projection.hom.hom
  let s : GroupPoints P.negative.group R := t ≫ p.inclusion.hom.hom
  let x := s⁻¹ * b
  have hx : x ≫ p.projection.hom.hom = toUnit _ ≫ η[P.torus.group.X] := by
    change x ≫ p.projection.hom.hom = 1
    rw [show x = s⁻¹ * b from rfl, MonObj.mul_comp, GrpObj.inv_comp]
    have hs : s ≫ p.projection.hom.hom = t := by
      have h : p.inclusion.hom.hom ≫ p.projection.hom.hom = 𝟙 P.torus.group.X :=
        congrArg (fun f : P.torus.group ⟶ P.torus.group ↦ f.hom.hom) p.section_projection
      change (t ≫ p.inclusion.hom.hom) ≫ p.projection.hom.hom = t
      rw [Category.assoc, h, Category.comp_id]
    rw [hs, ← show t = b ≫ p.projection.hom.hom from rfl, inv_mul_cancel]
  let u := p.isKernel.lift x (toUnit _) hx
  have hu : u ≫ p.radical.inclusion.hom.hom = x := p.isKernel.lift_fst _ _ _
  obtain ⟨r, hr⟩ := L.isRadical.2.2 p.radical p.isRadical.1 p.isRadical.2.1
  have hfix := (mem_fixedSpace.mp l.primitive.2.1) R (u ≫ r.hom.hom)
  have he : r ≫ L.radical.inclusion ≫ P.negative.inclusion =
      p.radical.inclusion ≫ P.negative.inclusion := by rw [← Category.assoc, hr]
  have hfix' : act l.representation R (x ≫ P.negative.inclusion.hom.hom)
      (extendVector R l.vector) = extendVector R l.vector := by
    have ht := congrArg (fun z : p.radical.group ⟶ G.val ↦ u ≫ z.hom.hom) he
    change u ≫ r.hom.hom ≫ (L.radical.inclusion ≫ P.negative.inclusion).hom.hom =
        u ≫ p.radical.inclusion.hom.hom ≫ P.negative.inclusion.hom.hom at ht
    rw [← Category.assoc u _ _, ← Category.assoc u _ _, hu] at ht
    rwa [ht] at hfix
  have ht : s ≫ P.negative.inclusion.hom.hom = t ≫ P.torus.inclusion.hom.hom := by
    have h : p.inclusion.hom.hom ≫ P.negative.inclusion.hom.hom = P.torus.inclusion.hom.hom :=
      congrArg (fun f : P.torus.group ⟶ G.val ↦ f.hom.hom) p.inclusion_comp
    change (t ≫ p.inclusion.hom.hom) ≫ P.negative.inclusion.hom.hom = _
    rw [Category.assoc, h]
  have hb : b = s * x := by simp [x]
  change act l.representation R _ _ = _
  conv_lhs => rw [hb]
  rw [MonObj.mul_comp, act_mul, hfix', ht, characterValue_restrict]
  exact mem_weightSpace.mp l.primitive.2.2 R t

open Specs.ProjectiveSpaces (projectiveProduct tensorSpace)
open LinearAlgebraicGroups.ProjectiveSpaces (lineRepresentation segreMorphism segreClosedImmersion)
open private tensorVector tensorChangeEquiv tensorLineSubmodule_singleton
  tensorVector_baseChange segreMorphism_apply tensorLine_submodule product_proper
  affinePointEquiv projectiveBasis
  from LinearAlgebraicGroups.Flag.ProjectiveSpaces
open private baseSimpleRoot datum_coroot_eq datum_pairing_eq cocharacter_eq_zero_of_simple_roots
  from LinearAlgebraicGroups.Representation.ParabolicLineWeights

private theorem vectorCoordinates_changeVector {I : Type u} [Fintype I] [DecidableEq I]
    {R S : TestAlgebra k} (a : R ⟶ S) (v : R ⊗[k] (I → k)) :
    vectorCoordinates S (changeVector a v) = fun i ↦ a.hom (vectorCoordinates R v i) := by
  induction v using TensorProduct.inductionOn with
  | tmul r v =>
    ext i
    have h (R : TestAlgebra k) (r : R) :
        vectorCoordinates R (r ⊗ₜ[k] v) = r • extendVector R v := by
      rw [← vectorCoordinates_tmul R v, ← map_smul, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
    change vectorCoordinates S (a.hom r ⊗ₜ[k] v) i =
      a.hom (vectorCoordinates R (r ⊗ₜ[k] v) i)
    simp only [h, Pi.smul_apply, smul_eq_mul, map_mul, extendVector, AlgHom.commutes]
  | add v w hv hw =>
    ext i
    simp only [map_add, hv, hw, Pi.add_apply]

private theorem orbitVector_natural {T B : ClosedSubgroup G.val} {U : ClosedSubgroup B.group}
    {H : ClosedSubgroup G.val} (L : ParabolicLine (T := T) U H)
    {R S : TestAlgebra k} (a : R ⟶ S) (g : GroupPoints G.val R) :
    orbitVector L S (mapPoints a g) = changeVector a (orbitVector L R g) := by
  letI := L.finite
  letI := L.decidable
  apply (vectorCoordinates S).injective
  rw [vectorCoordinates_changeVector]
  simpa only [orbitVector, LinearEquiv.apply_symm_apply] using
    act_extend_natural L.representation a g L.vector

private theorem orbitVector_unimodular {T B : ClosedSubgroup G.val} {U : ClosedSubgroup B.group}
    {H : ClosedSubgroup G.val} (L : ParabolicLine (T := T) U H)
    (R : TestAlgebra k) (g : GroupPoints G.val R) :
    ∃ f : R ⊗[k] (L.index → k) →ₗ[R] R, f (orbitVector L R g) = 1 := by
  classical
  letI := L.finite
  letI := L.decidable
  obtain ⟨i, hi⟩ : ∃ i : L.index, L.vector i ≠ 0 := by
    by_contra! h
    exact L.primitive.1 (funext h)
  let e := Specs.PluckerEmbedding.matrixTransport (Pi.basisFun k L.index) R
    (L.representation.app R g)
  have he : e (1 ⊗ₜ[k] L.vector) = orbitVector L R g := matrixTransport_orbitVector L R g
  let f : (L.index → R) →ₗ[R] R := algebraMap k R ((L.vector i)⁻¹) • LinearMap.proj i
  refine ⟨f.comp ((vectorCoordinates R).toLinearMap.comp e.symm.toLinearMap), ?_⟩
  rw [← he]
  change f (vectorCoordinates R (e.symm (e (1 ⊗ₜ[k] L.vector)))) = 1
  rw [LinearEquiv.symm_apply_apply, vectorCoordinates_tmul]
  change algebraMap k R ((L.vector i)⁻¹) * algebraMap k R (L.vector i) = 1
  rw [← map_mul, inv_mul_cancel₀ hi, map_one]

private theorem orbitVector_right {P : OppositeBorelPair G} [IsCommMonObj P.torus.group.X]
    (N : LineWeightData P.torus P.negative) (p : BorelProjection P) (i : N.base.support)
    (R : TestAlgebra k) (g : Points G.val.X R) (b : Points P.negative.group.X R) :
    orbitVector (N.line i) R (g * (b ≫ P.negative.inclusion.hom.hom)) =
      characterValue (p.projection ≫ (N.line i).weight) R b • orbitVector (N.line i) R g := by
  letI := (N.line i).finite
  letI := (N.line i).decidable
  let g' : GroupPoints G.val R := g
  let b' : GroupPoints G.val R := b ≫ P.negative.inclusion.hom.hom
  let e := vectorCoordinates R (I := (N.line i).index)
  let v := extendVector R (N.line i).vector
  let c := characterValue (p.projection ≫ (N.line i).weight) R b
  change e.symm (act (N.line i).representation R (g' * b') v) =
    c • e.symm (act (N.line i).representation R g' v)
  have hb : act (N.line i).representation R b' v = c • v := oppositeBorel_scalar N p i R b
  rw [act_mul, hb, act_smul, map_smul]

private theorem tensorVector_unimodular {I : Type u} [Fintype I] (W : I → Type u)
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] [∀ i, Module.Finite k (W i)]
    (R : TestAlgebra k) (w : ∀ i, R ⊗[k] W i)
    (h : ∀ i, ∃ f : R ⊗[k] W i →ₗ[R] R, f (w i) = 1) :
    Function.Injective (fun r : R ↦ r • tensorVector W R w) := by
  choose f hf using h
  let g := PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra R I R).compLinearMap f)
  let p := g.comp (tensorChangeEquiv W R).symm.toLinearMap
  have hp : p (tensorVector W R w) = 1 := by
    simp [p, g, tensorVector, hf]
  intro a b hab
  simpa only [map_smul, hp, smul_eq_mul, mul_one] using congrArg p hab

private theorem tensorVector_smul {I : Type u} [Fintype I] (W : I → Type u)
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)] [∀ i, Module.Finite k (W i)]
    (R : TestAlgebra k) (w : ∀ i, R ⊗[k] W i) (c : I → R) :
    tensorVector W R (fun i ↦ c i • w i) = (∏ i, c i) • tensorVector W R w := by
  unfold tensorVector
  rw [(PiTensorProduct.tprod R).map_smul_univ, map_smul]

/-- The repeated factors in the Segre product realize a positive power
of the bundle of a strictly dominant character. -/
theorem strictDominanceImpliesAmple : StrictDominanceImpliesAmple.{u} := by
  classical
  intro k _ G P hss comm D χ hχ Q p
  obtain ⟨comm', pos, hneg⟩ := ParabolicLineWeights.lineWeights G P.reductive hss P.torus P.positive
    P.split P.maximal P.positiveBorel P.inPositive
  have heq : comm' = comm := Subsingleton.elim _ _
  subst comm'
  obtain ⟨neg, e, he⟩ := hneg P.negative P.negativeBorel P.inNegative P.opposite
  have hposχ (i : pos.base.support) :
      0 < pos.datum.rootDatum.coroot' i.val (Additive.ofMul χ) := by
    obtain ⟨j, hj⟩ := (baseSimpleRoot pos.positive pos.isBase i.val).1 i.property
    have hcor := datum_coroot_eq (D := pos.datum) (b := pos.base) D
      (cocharacter_eq_zero_of_simple_roots P.reductive hss P.split) i.val
    change 0 < pos.datum.rootDatum.toLinearMap (Additive.ofMul χ) (pos.datum.rootDatum.coroot i.val)
    rw [← hcor, ← hj, datum_pairing_eq pos.datum D]
    exact hχ j
  obtain ⟨m, r, hm, hr, hχm⟩ := characterPowerDecomposition pos neg e (fun i ↦ (he i).2.1) χ hposχ
  let I := Σ i : neg.base.support, Fin (r i)
  let H (i : I) := (neg.parabolic i.1).limitGroups.parabolic
  let W (i : I) := (neg.line i.1).index → k
  letI (i : I) : Fintype (neg.line i.1).index := (neg.line i.1).finite
  letI (i : I) : DecidableEq (neg.line i.1).index := (neg.line i.1).decidable
  letI (i : I) : Module.Finite k (W i) := inferInstanceAs (Module.Finite k ((neg.line i.1).index → k))
  have hpar (i : I) : Specs.BorelProper.IsParabolic G (H i) := (neg.parabolic i.1).parabolic
  have hnonempty (i : I) :=
    (LinearAlgebraicGroups.ProjectiveFlags.smoothProjectiveQuotient k G (H i) (hpar i)).1
  let Qs (i : I) : Presentation (H i) := (hnonempty i).some
  have hπ (i : I) := quotientMapExists Q (Qs i) (neg.parabolic i.1).containsBorel
  choose π hπ' using hπ
  have hj (i : I) := parabolicOrbitEmbeddings G P.reductive.1 (H i) (hpar i)
    (neg.line i.1) (Qs i) (lineRepresentation k (W i))
  choose j hj' using hj
  let f : Q.scheme ⟶ projectiveProduct W := Limits.Pi.lift (fun i ↦ π i ≫ j i)
  have hfmono : Mono f.left := quotient_product_mono Q H Qs π hπ' j
    (fun i ↦ by
      haveI := (hj' i).1
      exact Over.mono_of_mono_left (j i))
    (fun S g hg ↦ (parabolic_intersection neg P.reductive P.split P.maximal
      P.negativeBorel P.inNegative g).1 (fun i ↦ hg ⟨i, ⟨0, hr i⟩⟩))
  have hY : IsProper Q.scheme.hom := ((LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G P).2.2 Q).2.1
  haveI : IsProper (projectiveProduct W).hom :=
    product_proper _ (fun i ↦ LinearAlgebraicGroups.ProjectiveSpaces.projectiveSpaceProper k (W i))
  haveI : IsProper (f.left ≫ (projectiveProduct W).hom) := Over.w f ▸ hY
  have hf : IsClosedImmersion f.left := (IsClosedImmersion.iff_isProper_and_mono (f := f.left)).mpr
    ⟨IsProper.of_comp _ (projectiveProduct W).hom, hfmono⟩
  let V := tensorSpace (k := k) W
  let J := f ≫ segreMorphism W
  have hjclosed : IsClosedImmersion J.left := by
    letI := hf
    letI := segreClosedImmersion (k := k) W
    change IsClosedImmersion (f.left ≫ (segreMorphism W).left)
    infer_instance
  let w (R : TestAlgebra k) (g : GroupPoints G.val R) (i : I) := orbitVector (neg.line i.1) R g
  let frame (R : TestAlgebra k) (g : GroupPoints G.val R) := tensorVector W R (w R g)
  refine ⟨m, hm, V, inferInstance, inferInstance, inferInstance, lineRepresentation k V, J,
    hjclosed, frame, ?_, ?_, ?_⟩
  · intro R g
    refine ⟨?_, tensorVector_unimodular W R (w R g) (fun i ↦ orbitVector_unimodular _ R g)⟩
    let a := g ≫ Q.projection ≫ f
    have he (i : I) :
        (affinePointEquiv (projectiveBasis k (W i)) R (a ≫ Limits.Pi.π _ i)).submodule =
          Submodule.span R {w R g i} := by
      have hπf : f ≫ Limits.Pi.π _ i = π i ≫ j i := Limits.Pi.lift_comp_π _ _
      have ha : a ≫ Limits.Pi.π _ i = (g ≫ (Qs i).projection) ≫ j i := by
        simp only [a, Category.assoc, hπf]
        rw [← Category.assoc Q.projection, hπ' i]
      rw [ha]
      exact (hj' i).2 R g
    change (affinePointEquiv (projectiveBasis k V) R ((g ≫ Q.projection) ≫ J)).submodule =
      Submodule.span R {tensorVector W R (w R g)}
    rw [show (g ≫ Q.projection) ≫ J = a ≫ segreMorphism W by
      simp only [J, a, Category.assoc], segreMorphism_apply, tensorLine_submodule,
      funext he, tensorLineSubmodule_singleton]
  · intro R S a g
    calc
      frame S (mapPoints a g) =
          tensorVector W S (fun i ↦ changeVector a (w R g i)) :=
        congrArg (tensorVector W S) (funext fun i ↦ orbitVector_natural (neg.line i.1) a g)
      _ = changeVector a (frame R g) := (tensorVector_baseChange W a _).symm
  · intro R g b
    let z : Points G.val.X R := g * (b ≫ P.negative.inclusion.hom.hom)
    let c (i : I) := characterValue (p.projection ≫ (neg.line i.1).weight) R b
    have hw : w R z = fun i ↦ c i • w R g i :=
      funext fun i ↦ orbitVector_right neg p i.1 R g b
    change tensorVector W R (w R z) = _
    rw [hw, tensorVector_smul]
    have hweights : (∏ i : I, (neg.line i.1).weight) = (χ ^ m)⁻¹ := by
      rw [Fintype.prod_sigma]
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hχm
    let t : GroupPoints P.torus.group R := b ≫ p.projection.hom.hom
    have hc : (∏ i, c i) = characterValue (p.projection ≫ χ ^ m) R b⁻¹ := by
      calc
        _ = ∏ i : I, characterValue (neg.line i.1).weight R t := by
          apply Finset.prod_congr rfl
          intro i _
          exact characterValue_restrict p.projection (neg.line i.1).weight R b
        _ = characterValue (∏ i : I, (neg.line i.1).weight) R t :=
          (characterValue_prod Finset.univ (fun i : I ↦ (neg.line i.1).weight) R t).symm
        _ = _ := by
          rw [hweights, characterValue_inv, characterValue_restrict p.projection]
          exact congrArg (characterValue (χ ^ m) R) (GrpObj.inv_comp b p.projection.hom.hom).symm
    rw [hc]

open Specs.GeometricRadicals (IsSplitTorus)
open private lattice_torus_of_split from LinearAlgebraicGroups.RootData.RankOneFlag
open private maximalTorus_of_geometricallyMaximal
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private fppf_epi from LinearAlgebraicGroups.Representation.FlagLineBundle

private theorem splitTorus_borelIso (P : OppositeBorelPair G) (hG : IsSplitTorus G.val) :
    IsIso P.negative.inclusion := by
  let A : ClosedSubgroup G.val :=
    ⟨G.val, 𝟙 _, inferInstanceAs (IsClosedImmersion (𝟙 G.val.X.left))⟩
  have hm := maximalTorus_of_geometricallyMaximal G P.torus
    (lattice_torus_of_split P.split) P.maximal
  obtain ⟨s, hs⟩ := hm.2 A (lattice_torus_of_split hG)
    ⟨P.torus.inclusion, Category.comp_id _⟩
  obtain ⟨i, hi⟩ := P.inNegative
  let r : G.val ⟶ P.negative.group := s ≫ i
  have hr : r ≫ P.negative.inclusion = 𝟙 G.val := by
    rw [Category.assoc, hi]
    exact hs
  haveI : Mono P.negative.inclusion := by
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
    haveI : IsClosedImmersion (F.map P.negative.inclusion) := P.negative.isClosedImmersion
    exact F.mono_of_mono_map inferInstance
  exact ⟨⟨r, (cancel_mono P.negative.inclusion).mp
    (by rw [Category.assoc, hr, Category.comp_id, Category.id_comp]), hr⟩⟩

private theorem quotient_isPoint {H : ClosedSubgroup G.val} (Q : Presentation H)
    [IsIso H.inclusion] : IsIso Q.scheme.hom := by
  let e : 𝟙_ (SchemeOver k) ⟶ Q.scheme := η[G.val.X] ≫ Q.projection
  have hq : (𝟙 G.val.X) ≫ Q.projection = (1 : G.val.X ⟶ G.val.X) ≫ Q.projection := by
    apply (projection_eq_iff Q _ _).2
    let g : G.val.X ⟶ G.val.X := (𝟙 G.val.X)⁻¹ * 1
    refine ⟨g ≫ (inv H.inclusion).hom.hom, ?_⟩
    change g ≫ (inv H.inclusion ≫ H.inclusion).hom.hom = g
    rw [IsIso.inv_hom_id]
    exact Category.comp_id g
  have hq' : Q.projection = toUnit G.val.X ≫ e := by
    change (𝟙 G.val.X) ≫ Q.projection = (toUnit _ ≫ η[G.val.X]) ≫ Q.projection at hq
    simpa only [Category.id_comp, Category.assoc] using hq
  letI := Q.flat
  letI := Q.surjective
  letI := Q.finitePresentation
  haveI := fppf_epi Q.projection
  have he : toUnit Q.scheme ≫ e = 𝟙 Q.scheme :=
    (cancel_epi Q.projection).mp (by rw [← Category.assoc, comp_toUnit, Category.comp_id, hq'])
  exact ⟨⟨e.left, congrArg Over.Hom.left he, Over.w e⟩⟩

/-- Over a split torus the opposite Borel is the whole group. Its flag is the
base point and the line bundle of every character has a very ample first power. -/
theorem splitTorusPointCase : SplitTorusPointCase.{u} := by
  intro k _ G P hG Q p χ
  letI := splitTorus_borelIso P hG
  letI := quotient_isPoint Q
  refine ⟨inferInstance, 1, Nat.one_pos, k, inferInstance, inferInstance, inferInstance, ?_⟩
  let ρ := lineRepresentation k k
  let x : 𝟙_ (SchemeOver k) ⟶ projectiveSpace k k :=
    (ρ.points _).symm (vectorLine (one_ne_zero : (1 : k) ≠ 0))
  let j := toUnit Q.scheme ≫ x
  haveI : IsIso (projectiveSpace k k).hom :=
    (ProjectiveSpaces.oneDimensionalProjectiveSpace k k (Module.finrank_self k)).2
  haveI : IsIso j.left :=
    IsIso.of_isIso_fac_right (Over.w j)
  refine ⟨ρ, j, inferInstance, ?_⟩
  rw [pow_one]
  let ψ : Character G.val := inv P.negative.inclusion ≫ (p.projection ≫ χ)
  let frame (R : TestAlgebra k) (g : Points G.val.X R) : R ⊗[k] k :=
    characterValue ψ R g⁻¹ • ((1 : R) ⊗ₜ[k] (1 : k))
  refine ⟨frame, ?_, ?_, ?_⟩
  · intro R g
    have hunit : IsUnit (characterValue ψ R g⁻¹) := by
      rw [characterValue_unit]
      exact Units.isUnit _
    constructor
    · have hj : j = toUnit Q.scheme ≫ x := rfl
      rw [hj, ρ.naturality]
      change ((ρ.points _ x).line R _).submodule = _
      rw [show ρ.points _ x = vectorLine (one_ne_zero : (1 : k) ≠ 0)
        from (ρ.points _).apply_symm_apply _, vectorLine_span]
      exact (Submodule.span_singleton_smul_eq hunit _).symm
    · intro a b hab
      have h := congrArg (TensorProduct.AlgebraTensorModule.rid k R R) hab
      change _ = _ at h
      simp only [frame, map_smul, TensorProduct.AlgebraTensorModule.rid_tmul,
        one_smul, smul_eq_mul, mul_one] at h
      exact hunit.mul_right_cancel h
  · intro R S a g
    change characterValue ψ S (mapPoints a g)⁻¹ • _ =
      changeVector a (characterValue ψ R g⁻¹ • _)
    rw [← show mapPoints a g⁻¹ = (mapPoints a g)⁻¹ from GrpObj.comp_inv _ _,
      characterValue_natural]
    simp only [changeVector, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      TensorProduct.map_tmul, LinearMap.id_apply]
    rfl
  · intro R g b
    change characterValue ψ R (g * (b ≫ P.negative.inclusion.hom.hom))⁻¹ • _ =
      characterValue (p.projection ≫ χ) R b⁻¹ • (characterValue ψ R g⁻¹ • _)
    rw [mul_inv_rev, ← GrpObj.inv_comp, characterValue_mul_points, ← mul_smul, ← characterValue_restrict]
    simp only [ψ, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

end

end LinearAlgebraicGroups.Representation.AmpleFlagWeights
