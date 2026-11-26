import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RationalStronglyRegularElements
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SteinbergGeometricFibres
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriExist
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalDensity
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor (LaxMonoidal OplaxMonoidal)
open scoped TensorProduct CategoryTheory.MonObj CategoryTheory.Obj

universe u

namespace LinearAlgebraicGroups.Arithmetic.RationalStronglyRegularElements

open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals
open Specs.SteinbergGeometricFibres (IsPointCentralizer pointHom)
open Specs.SubtorusCentralizer (IsCentralizer)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.CharacterDescent (StandardLattice)
open _root_.LinearAlgebraicGroups.Affine (RationalPoints IsRationalJordanDecomposition)
open Specs.Relative.RationalDensity (rationalPointOver)
open DiagonalizableFixedLocus
open WeightDecomposition

open private conjugationAction isFixedBy_conjugation_iff reflectAction coordinateCoaction
  reflectAction_fixed hom_of_weight
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
open private prodComparison_inv_fst prodComparison_inv_snd centralizes_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private factor_of_baseChange baseChangeProjection_naturality
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private groupPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private splitPresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private isSplitTorus_of_isAlgClosed from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.NontrivialRationalTorus
open private rationalSpec_hom from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SplitFixedPoint

noncomputable section

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

private theorem identity_conjugationAction (G : GroupScheme k) :
    (conjugationAction (𝟙 G)).smul = GrpObj.conj G.X := by
  change ((𝟙 G.X) ▷ G.X) ≫ GrpObj.conj G.X = _
  rw [id_whiskerRight, Category.id_comp]

private theorem stabilizes_conjugation_iff {G : GroupScheme k}
    (y : 𝟙_ (SchemeOver k) ⟶ G.X) {Y : SchemeOver k} (g : Y ⟶ G.X) :
    Stabilizes (conjugationAction (𝟙 G)).smul y g ↔ Commute g (toUnit Y ≫ y) := by
  have he : lift g (toUnit Y ≫ y) ≫ (conjugationAction (𝟙 G)).smul =
      g * (toUnit Y ≫ y) * g⁻¹ := by
    rw [identity_conjugationAction, GrpObj.conj]
    simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd]
  rw [Stabilizes, he, mul_inv_eq_iff_eq_mul]
  rfl

private theorem pointCentralizerExists (G : AffineAlgebraicGroup k)
    (y : 𝟙_ (SchemeOver k) ⟶ G.val.X) :
    ∃ C : ClosedSubgroup G.val, IsPointCentralizer C y := by
  let : IsAffine G.val.X.left := G.property.1
  obtain ⟨C, hC⟩ := stabilizerScheme k G.val G.val.X (conjugationAction (𝟙 G.val))
    y inferInstance G.property.2.1 G.property.2.2
  exact ⟨C, fun Y g => (stabilizes_conjugation_iff y g).symm.trans (hC Y g)⟩

private theorem baseChange_conjugationAction (K : Type u) [Field K] [Algebra k K]
    (G : GroupScheme k) :
    baseChangeAction K (conjugationAction (𝟙 G)).smul =
      (conjugationAction (𝟙 ((groupBaseChange k K).obj G))).smul := by
  let F := baseChange k K
  let : GrpObj (F.obj G.X) := ((groupBaseChange k K).obj G).grp
  rw [identity_conjugationAction, identity_conjugationAction]
  change (prodComparisonIso F G.X G.X).inv ≫ F.map (GrpObj.conj G.X) =
    GrpObj.conj (F.obj G.X)
  simp only [GrpObj.conj, F.map_mul, F.map_inv', MonObj.comp_mul, GrpObj.comp_inv]
  rw [prodComparison_inv_fst K G.X G.X, prodComparison_inv_snd K G.X G.X]

/-- The full centralizer of a rational point commutes with scalar extension. -/
theorem pointCentralizerBaseChange (K : Type u) [Field K] [Algebra k K]
    {G : GroupScheme k} (C : ClosedSubgroup G) {y : 𝟙_ (SchemeOver k) ⟶ G.X}
    (hC : IsPointCentralizer C y) :
    ∃ h, IsPointCentralizer (scalarExtendedSubgroup K C h) (scalarExtendedRationalPoint K y) := by
  obtain ⟨h, hK⟩ := stabilizerSchemeBaseChange k K (conjugationAction (𝟙 G)).smul y C
    (fun Y g => (stabilizes_conjugation_iff y g).trans (hC Y g))
  rw [baseChange_conjugationAction] at hK
  exact ⟨h, fun Y g => (stabilizes_conjugation_iff _ g).symm.trans (hK Y g)⟩

local instance (k : Type u) [Field k] : (testSpec k).Braided :=
  braidedAlgSpec (R := CommRingCat.of k)

private abbrev spectrum (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A] :=
  (testSpec k).obj (op (CommAlgCat.of k A))

private abbrev spectrumMap {A R : Type u} [CommRing A] [Algebra k A]
    [CommRing R] [Algebra k R] (x : A →ₐ[k] R) : spectrum k R ⟶ spectrum k A :=
  (testSpec k).map (CommAlgCat.ofHom x).op

private abbrev sectionOfEvaluation {B : Type u} [CommRing B] [Algebra k B]
    (p : B →ₐ[k] k) : 𝟙_ (SchemeOver k) ⟶ spectrum k B :=
  LaxMonoidal.ε (testSpec k) ≫ spectrumMap p

private theorem sectionOfEvaluation_constant {B R : Type u}
    [CommRing B] [Algebra k B] [CommRing R] [Algebra k R] (p : B →ₐ[k] k) :
    toUnit (spectrum k R) ≫ sectionOfEvaluation p = spectrumMap ((Algebra.ofId k R).comp p) := by
  rw [← Category.assoc, Functor.Monoidal.toUnit_ε, ← Functor.map_comp]
  rfl

section Weights

variable {M A : Type u} [CommGroup M] [Group.FG M] [CommRing A] [Algebra k A]

local notation "B" => MonoidAlgebra k M
local notation "χ" => MonoidAlgebra.of k M

private abbrev actionCoaction
    (a : ModObj (Specs.DiagonalizableGroups.diagonalGroup k M).val.X (spectrum k A)) :=
  coordinateCoaction (reflectAction (testSpec k)
    (algSpec.fullyFaithful (R := CommRingCat.of k))
    (op (CommAlgCat.of k B)) (op (CommAlgCat.of k A)) a)

private theorem specialize_action {R : Type u} [CommRing R] [Algebra k R]
    (a : ModObj (Specs.DiagonalizableGroups.diagonalGroup k M).val.X (spectrum k A))
    (p : B →ₐ[k] k) (x : A →ₐ[k] R) :
    let q : B →ₐ[k] R := (Algebra.ofId k R).comp p
    let l : A ⊗[k] B →ₐ[k] R := Algebra.TensorProduct.lift x q (fun _ _ => Commute.all _ _)
    lift (toUnit (spectrum k R) ≫ sectionOfEvaluation p) (spectrumMap x) ≫ a.smul =
      spectrumMap (l.comp (actionCoaction a).hom) := by
  dsimp only
  rw [sectionOfEvaluation_constant]
  let F := testSpec k
  let D := op (CommAlgCat.of k B)
  let X := op (CommAlgCat.of k A)
  let q := (CommAlgCat.ofHom ((Algebra.ofId k R).comp p)).op
  let z := (CommAlgCat.ofHom x).op
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a' := reflectAction F ff D X a
  have hLift : F.map (lift q z) ≫ OplaxMonoidal.δ F D X = lift (F.map q) (F.map z) := by
    rw [OplaxMonoidal.δ_of_cartesianMonoidalCategory]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, CartesianMonoidalCategory.prodComparison_fst, ← F.map_comp]
      erw [lift_fst q z, lift_fst (F.map q) (F.map z)]
    · rw [Category.assoc, CartesianMonoidalCategory.prodComparison_snd, ← F.map_comp]
      erw [lift_snd q z, lift_snd (F.map q) (F.map z)]
  have ha' : F.map a'.smul = OplaxMonoidal.δ F D X ≫ a.smul := ff.map_preimage _
  change lift (F.map q) (F.map z) ≫ a.smul = _
  rw [← hLift, Category.assoc, ← ha', ← F.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  let l : B ⊗[k] A →ₐ[k] R := (lift q z).unop.hom
  let r : A ⊗[k] B →ₐ[k] R :=
    Algebra.TensorProduct.lift x ((Algebra.ofId k R).comp p) (fun _ _ => Commute.all _ _)
  have he (v : B ⊗[k] A) : l v = r (Algebra.TensorProduct.comm k B A v) := by
    induction v using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul b a =>
      change ((Algebra.ofId k R).comp p) b * x a = r (Algebra.TensorProduct.comm k B A (b ⊗ₜ[k] a))
      rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.lift_tmul, mul_comm]
  ext v
  exact he (a'.smul.unop.hom v)

/-- The weight components of finitely many algebra generators suffice to test
whether a point fixed by one torus element is fixed by the entire torus. -/
private theorem exists_finite_weights_for_fixed_points
    (a : ModObj (Specs.DiagonalizableGroups.diagonalGroup k M).val.X (spectrum k A))
    (hA : Algebra.FiniteType k A) :
    ∃ S : Finset M, ∀ (p : B →ₐ[k] k), (∀ m ∈ S, m ≠ 1 → p (χ m) ≠ 1) →
      ∀ (R : Type u) [CommRing R] [Algebra k R] (x : A →ₐ[k] R),
        lift (toUnit (spectrum k R) ≫ sectionOfEvaluation p) (spectrumMap x) ≫ a.smul =
          spectrumMap x → IsFixedBy a.smul (spectrumMap x) := by
  classical
  let ρ := actionCoaction a
  let w := weightSpace ρ.toRightComodule
  obtain ⟨s, hs⟩ := hA.out
  have hdec (b : A) : ∃ f : M →₀ A, (∀ m, f m ∈ w m) ∧ (f.sum fun _ z => z) = b := by
    apply (Submodule.mem_iSup_iff_exists_finsupp w b).mp
    rw [(weightDecomposition ρ.toRightComodule).submodule_iSup_eq_top]
    exact Submodule.mem_top
  choose f hw hsum using hdec
  refine ⟨s.biUnion (fun b => (f b).support), ?_⟩
  intro p hp R _ _ x h
  rw [specialize_action] at h
  have hcoord := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective h
  have hval (b : A) := congrArg (fun g => g.unop.hom b) hcoord
  let q := (Algebra.ofId k R).comp p
  let l := Algebra.TensorProduct.lift x q (fun _ _ => Commute.all _ _)
  have hzero (m : M) (hpm : p (χ m) ≠ 1) (b : A) (hb : b ∈ w m) :
      x b = 0 := by
    have h' : l (ρ.hom b) = x b := hval b
    rw [hom_of_weight ρ hb, Algebra.TensorProduct.lift_tmul] at h'
    have he : x b * algebraMap k R (p (χ m) - 1) = 0 := by
      rw [map_sub, map_one, mul_sub, mul_one]
      exact sub_eq_zero.mpr h'
    have hu : IsUnit (algebraMap k R (p (χ m) - 1)) :=
      (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hpm)).map (algebraMap k R)
    obtain ⟨u, hu⟩ := hu
    rw [← hu] at he
    have := congrArg (fun z : R => z * ↑u⁻¹) he
    simpa [mul_assoc] using this
  rw [reflectAction_fixed]
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  let left : A →ₐ[k] B ⊗[k] R :=
    (Algebra.TensorProduct.map (AlgHom.id k B) x).comp
      (reflectAction (testSpec k) (algSpec.fullyFaithful (R := CommRingCat.of k))
        (op (CommAlgCat.of k B)) (op (CommAlgCat.of k A)) a).smul.unop.hom
  let right : A →ₐ[k] B ⊗[k] R := Algebra.TensorProduct.includeRight.comp x
  change left = right
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro b hb
  have hterm (m : M) (hm : m ∈ (f b).support) : left (f b m) = right (f b m) := by
    have hl : (reflectAction (testSpec k) (algSpec.fullyFaithful (R := CommRingCat.of k))
        (op (CommAlgCat.of k B)) (op (CommAlgCat.of k A)) a).smul.unop.hom (f b m) =
          χ m ⊗ₜ[k] (f b m) := by
      apply (Algebra.TensorProduct.comm k B A).injective
      change ρ.hom (f b m) = _
      rw [hom_of_weight ρ (hw b m), Algebra.TensorProduct.comm_tmul]
    change (Algebra.TensorProduct.map (AlgHom.id k B) x) _ = (1 : B) ⊗ₜ[k] x (f b m)
    erw [hl]
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    by_cases h : m = 1
    · rw [h, map_one]
    · rw [hzero m (hp m (Finset.mem_biUnion.mpr ⟨b, hb, hm⟩) h) _ (hw b m)]
      simp
  rw [← hsum b]
  simp only [Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl hterm

end Weights

private theorem scalarExtendedRationalPoint_value (K : Type u) [Field K] [Algebra k K]
    {X : SchemeOver k} (t : 𝟙_ (SchemeOver k) ⟶ X) :
    (scalarExtendedRationalPoint K t).left (IsLocalRing.closedPoint K) =
      rationalPointOver K t := by
  apply congrArg (fun f : Spec (CommRingCat.of K) ⟶ ((baseChange k K).obj X).left =>
    f (IsLocalRing.closedPoint K))
  let F := baseChange k K
  let ε := LaxMonoidal.ε F
  change (ε ≫ F.map t).left = _
  have he : ε.left ≫ pullback.fst (𝟙 (Spec (CommRingCat.of k))) (fieldSpecMap k K) =
      fieldSpecMap k K := by
    have h : ε.left ≫ pullback.snd (𝟙 (Spec (CommRingCat.of k))) (fieldSpecMap k K) =
        𝟙 (Spec (CommRingCat.of K)) := Over.w ε
    rw [← Category.comp_id (pullback.fst _ _), pullback.condition, ← Category.assoc, h]
    exact Category.id_comp _
  apply pullback.hom_ext
  · change (ε.left ≫ (F.map t).left) ≫ pullback.fst X.hom (fieldSpecMap k K) =
      _ ≫ pullback.fst X.hom (fieldSpecMap k K)
    rw [Category.assoc, baseChangeProjection_naturality, ← Category.assoc]
    erw [he, pullback.lift_fst]
  · change (ε ≫ F.map t).left ≫ ((F.obj X).hom) = _
    rw [Over.w, pullback.lift_snd]
    rfl

private theorem spectrum_sectionOfEvaluation {B : Type u} [CommRing B] [Algebra k B]
    (s : 𝟙_ (SchemeOver k) ⟶ spectrum k B) :
    ∃ p : B →ₐ[k] k, sectionOfEvaluation p = s := by
  let F := testSpec k
  let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
  let f := ff.preimage (toUnit (spectrum k k) ≫ s)
  refine ⟨f.unop.hom, ?_⟩
  change LaxMonoidal.ε F ≫ F.map f = s
  rw [ff.map_preimage (toUnit (spectrum k k) ≫ s), ← Category.assoc]
  have he : LaxMonoidal.ε F ≫ toUnit (spectrum k k) = 𝟙 _ := toUnit_unique _ _
  rw [he, Category.id_comp]

private theorem sectionOfEvaluation_value {B : Type u} [CommRing B] [Algebra k B]
    (p : B →ₐ[k] k) :
    (sectionOfEvaluation p).left (IsLocalRing.closedPoint k) =
      PrimeSpectrum.comap p.toRingHom (IsLocalRing.closedPoint k) := by
  have he : (LaxMonoidal.ε (testSpec k)).left = 𝟙 (Spec (CommRingCat.of k)) := by
    have h := Over.w (LaxMonoidal.ε (testSpec k))
    change (LaxMonoidal.ε (testSpec k)).left ≫ fieldSpecMap k k = 𝟙 _ at h
    have hr : fieldSpecMap k k = 𝟙 (Spec (CommRingCat.of k)) := rationalSpec_hom k
    rw [hr] at h
    erw [Category.comp_id] at h
    exact h
  change ((LaxMonoidal.ε (testSpec k)).left ≫ Spec.map (CommRingCat.ofHom p.toRingHom))
    (IsLocalRing.closedPoint k) = _
  erw [he, Category.id_comp]
  rfl

/-- Geometric density gives a ground-field section in the basic open defined
by the product of the specified nontrivial characters minus one. -/
private theorem choose_rational_evaluation [Infinite k] {X : SchemeOver k}
    {M : Type u} [CommGroup M]
    (e : spectrum (AlgebraicClosure k) (MonoidAlgebra (AlgebraicClosure k) M) ≅
      (baseChange k (AlgebraicClosure k)).obj X)
    [IsDomain (MonoidAlgebra (AlgebraicClosure k) M)]
    (hd : Specs.Relative.RationalDensity.GeometricallyDenseRationalPoints X) (S : Finset M) :
    ∃ (t : 𝟙_ (SchemeOver k) ⟶ X)
      (p : MonoidAlgebra (AlgebraicClosure k) M →ₐ[AlgebraicClosure k] AlgebraicClosure k),
      sectionOfEvaluation p ≫ e.hom = scalarExtendedRationalPoint (AlgebraicClosure k) t ∧
      ∀ m ∈ S, m ≠ 1 → p (MonoidAlgebra.of (AlgebraicClosure k) M m) ≠ 1 := by
  classical
  let K := AlgebraicClosure k
  let B := MonoidAlgebra K M
  let χ := MonoidAlgebra.of K M
  let f : B := ∏ m ∈ S.filter (· ≠ 1), (χ m - 1)
  have hf : f ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro m hm
    apply sub_ne_zero.mpr
    intro he
    have hinj : Function.Injective χ := MonoidAlgebra.of_injective
    exact (Finset.mem_filter.mp hm).2 (hinj (he.trans (map_one χ).symm))
  let U := (e.inv.left) ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum B))
  have huo : IsOpen U := PrimeSpectrum.isOpen_basicOpen.preimage e.inv.left.continuous
  have hun : U.Nonempty := by
    let z : PrimeSpectrum B := ⟨⊥, Ideal.isPrime_bot⟩
    refine ⟨e.hom.left z, ?_⟩
    change e.inv.left (e.hom.left z) ∈ PrimeSpectrum.basicOpen f
    have h := congrArg (fun g : spectrum K B ⟶ spectrum K B => g.left z) e.hom_inv_id
    change e.inv.left (e.hom.left z) = z at h
    rw [h, PrimeSpectrum.mem_basicOpen]
    exact hf
  obtain ⟨t, ht⟩ := DenseRange.exists_mem_open hd huo hun
  let q := scalarExtendedRationalPoint K t
  obtain ⟨p, hp⟩ := spectrum_sectionOfEvaluation (q ≫ e.inv)
  refine ⟨t, p, by rw [hp, Category.assoc, e.inv_hom_id, Category.comp_id], ?_⟩
  change e.inv.left (rationalPointOver K t) ∈ PrimeSpectrum.basicOpen f at ht
  rw [← scalarExtendedRationalPoint_value, ← Scheme.Hom.comp_apply] at ht
  change (q ≫ e.inv).left (IsLocalRing.closedPoint K) ∈ PrimeSpectrum.basicOpen f at ht
  rw [← hp, sectionOfEvaluation_value, PrimeSpectrum.mem_basicOpen] at ht
  have hpf : p f ≠ 0 := by
    intro h
    apply ht
    change p f ∈ (IsLocalRing.closedPoint K).asIdeal
    rw [h]
    exact Ideal.zero_mem _
  intro m hms hm h
  apply hpf
  rw [show p f = ∏ j ∈ S.filter (· ≠ 1), p (χ j - 1) from map_prod p _ _]
  apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨hms, hm⟩)
  rw [map_sub, h, map_one, sub_self]

private abbrev schemeMap {G H : GroupScheme k} (f : G ⟶ H) : G.X ⟶ H.X :=
  f.hom.hom

private theorem schemeMap_comp {G H L : GroupScheme k} (f : G ⟶ H) (g : H ⟶ L) :
    schemeMap (f ≫ g) = schemeMap f ≫ schemeMap g := rfl

private theorem specialized_conjugation {T G : GroupScheme k} (i : T ⟶ G)
    (t : 𝟙_ (SchemeOver k) ⟶ T.X) {Y : SchemeOver k} (g : Y ⟶ G.X)
    (hc : Commute g (toUnit Y ≫ t ≫ schemeMap i)) :
    lift (toUnit Y ≫ t) g ≫ (conjugationAction i).smul = g := by
  change lift (toUnit Y ≫ t) g ≫ (schemeMap i ▷ G.X) ≫ GrpObj.conj G.X = g
  rw [← Category.assoc, lift_whiskerRight, GrpObj.conj]
  simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, Category.assoc]
  exact mul_inv_eq_iff_eq_mul.mpr hc.symm.eq

private theorem centralizes_of_coordinates {D T X G : GroupScheme k}
    (e : D ≅ T) (f : X ≅ G) (i : T ⟶ G) {Y : SchemeOver k} (x : Y ⟶ X.X)
    (h : Centralizes (e.hom ≫ i ≫ f.inv) x) :
    Centralizes i (x ≫ schemeMap f.hom) := by
  rw [centralizes_iff] at h ⊢
  intro U q z
  have hc := (h U q (z ≫ schemeMap e.inv)).map
    (IsMonHom.monoidHom (schemeMap f.hom) U)
  change Commute ((q ≫ x) ≫ schemeMap f.hom)
    (((z ≫ schemeMap e.inv) ≫ schemeMap (e.hom ≫ i ≫ f.inv)) ≫ schemeMap f.hom) at hc
  have he := (Grp.forget (SchemeOver k)).congr_map e.inv_hom_id
  have hf := (Grp.forget (SchemeOver k)).congr_map f.inv_hom_id
  change schemeMap e.inv ≫ schemeMap e.hom = 𝟙 _ at he
  change schemeMap f.inv ≫ schemeMap f.hom = 𝟙 _ at hf
  simp only [schemeMap_comp, Category.assoc, hf, Category.comp_id, ← Category.assoc (schemeMap e.inv), he, Category.id_comp] at hc
  simpa only [Category.assoc] using hc


private theorem scalarExtendedRationalPoint_comp (K : Type u) [Field K] [Algebra k K]
    {X Y : SchemeOver k} (t : 𝟙_ (SchemeOver k) ⟶ X) (f : X ⟶ Y) :
    scalarExtendedRationalPoint K (t ≫ f) =
      scalarExtendedRationalPoint K t ≫ (baseChange k K).map f := by
  simp only [scalarExtendedRationalPoint, Functor.map_comp, Category.assoc]

private theorem exists_point_with_torus_centralizer [Infinite k]
    (H : AffineAlgebraicGroup k) (T : ClosedSubgroup H.val)
    (hT : IsTorus T.group)
    (hTK : IsClosedImmersion
      ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left)
    (hsplit : IsSplitTorus (baseChangedSubgroup (AlgebraicClosure k) T hTK).group)
    (hcentral : IsCentralizer T T) :
    ∃ t : 𝟙_ (SchemeOver k) ⟶ T.group.X, IsPointCentralizer T (t ≫ schemeMap T.inclusion) := by
  let K := AlgebraicClosure k
  let HK := GeometricGroup H
  let TK := baseChangedSubgroup K T hTK
  let i := TK.inclusion
  have hcTK : IsCentralizer TK TK := by
    obtain ⟨_, hc⟩ := centralizerSchemeBaseChange k K T.inclusion T hcentral
    exact hc
  obtain ⟨r, ⟨eT⟩⟩ := splitPresentation hsplit
  obtain ⟨A, hA, ⟨eH⟩⟩ := groupPresentation HK
  let M := StandardLattice.{u} r
  let B := MonoidAlgebra K M
  let : UniqueProds Specs.DiagonalizableGroups.IntegerCharacters.{u} :=
    MulEquiv.ulift.uniqueProds_iff.mpr (inferInstance : UniqueProds (Multiplicative ℤ))
  let : IsDomain B := inferInstanceAs (IsDomain (MonoidAlgebra K M))
  let D := (Specs.DiagonalizableGroups.diagonalGroup K M).val
  let d : D ⟶ specGroup A := eT.hom ≫ i ≫ eH.inv
  let a := conjugationAction d
  obtain ⟨S, hS⟩ := exists_finite_weights_for_fixed_points a hA
  have hd := _root_.LinearAlgebraicGroups.Relative.RationalDensity.torusRationalPointsDense
    k (closedSubgroupAlgebraicGroup T) hT
  let e := (Grp.forget (SchemeOver K)).mapIso eT
  obtain ⟨t, p, hp, hpS⟩ := choose_rational_evaluation
    (show spectrum K B ≅ (baseChange k K).obj T.group.X from e) hd S
  let y := t ≫ schemeMap T.inclusion
  obtain ⟨C, hC⟩ := pointCentralizerExists H y
  obtain ⟨hCK, hcCK⟩ := pointCentralizerBaseChange K C hC
  -- Test the geometric point centralizer on its own universal point.
  let CK := scalarExtendedSubgroup K C hCK
  obtain ⟨R, _, ⟨eC⟩⟩ := groupPresentation (closedSubgroupAlgebraicGroup (G := HK) CK)
  let c := schemeMap (eC.hom ≫ CK.inclusion)
  have hc : Commute c (toUnit (spectrum K R) ≫ scalarExtendedRationalPoint K y) :=
    (hcCK _ c).mpr ⟨schemeMap eC.hom, rfl⟩
  let v := c ≫ schemeMap eH.inv
  let ff := algSpec.fullyFaithful (R := CommRingCat.of K)
  let z := ff.preimage v
  let x : A →ₐ[K] R := z.unop.hom
  have hx : spectrumMap x = v := ff.map_preimage v
  have htK : sectionOfEvaluation p ≫ schemeMap d =
      scalarExtendedRationalPoint K y ≫ schemeMap eH.inv := by
    change sectionOfEvaluation p ≫ schemeMap eT.hom ≫ schemeMap i ≫ schemeMap eH.inv = _
    rw [← Category.assoc (sectionOfEvaluation p) (schemeMap eT.hom)]
    change (sectionOfEvaluation p ≫ e.hom) ≫ schemeMap i ≫ schemeMap eH.inv = _
    rw [hp, scalarExtendedRationalPoint_comp]
    exact (Category.assoc _ _ _).symm
  have hcomm := hc.map (IsMonHom.monoidHom (schemeMap eH.inv) (spectrum K R))
  have hcomm' : Commute (spectrumMap x) (toUnit (spectrum K R) ≫
      sectionOfEvaluation p ≫ schemeMap d) := by
    erw [hx, htK]
    change Commute (c ≫ schemeMap eH.inv)
      ((toUnit (spectrum K R) ≫ scalarExtendedRationalPoint K y) ≫ schemeMap eH.inv) at hcomm
    rwa [Category.assoc] at hcomm
  have hfix := hS p hpS R x
    (specialized_conjugation d (sectionOfEvaluation p) (spectrumMap x) hcomm')
  have hv : Centralizes d v := by
    rw [← hx]
    exact (isFixedBy_conjugation_iff d _).mp hfix
  have hcv : v ≫ schemeMap eH.hom = c := by
    have he := (Grp.forget (SchemeOver K)).congr_map eH.inv_hom_id
    change schemeMap eH.inv ≫ schemeMap eH.hom = 𝟙 _ at he
    change (c ≫ schemeMap eH.inv) ≫ schemeMap eH.hom = c
    rw [Category.assoc, he]
    exact Category.comp_id _
  obtain ⟨g, hg⟩ := (hcTK _ _).mp (centralizes_of_coordinates eT eH i v hv)
  rw [hcv] at hg
  have hKg : (schemeMap eC.inv ≫ g) ≫ schemeMap i = schemeMap CK.inclusion := by
    have he := (Grp.forget (SchemeOver K)).congr_map eC.inv_hom_id
    change schemeMap eC.inv ≫ schemeMap eC.hom = 𝟙 _ at he
    rw [Category.assoc, hg]
    change schemeMap eC.inv ≫ schemeMap eC.hom ≫ schemeMap CK.inclusion = _
    rw [← Category.assoc, he, Category.id_comp]
  -- The resulting factorization through the torus descends along the field extension.
  let := T.isClosedImmersion
  let : Mono (schemeMap T.inclusion).left := inferInstance
  obtain ⟨f, hf⟩ := factor_of_baseChange K (schemeMap C.inclusion) (schemeMap T.inclusion)
    (schemeMap eC.inv ≫ g) hKg
  refine ⟨t, fun Y u => ⟨?_, ?_⟩⟩
  · intro hu
    obtain ⟨b, hb⟩ := (hC Y u).mp hu
    exact ⟨b ≫ f, by rw [Category.assoc, hf, hb]⟩
  · rintro ⟨b, hb⟩
    have hh := (centralizes_iff T.inclusion u).mp ((hcentral Y u).mpr ⟨b, hb⟩)
      Y (𝟙 Y) (toUnit Y ≫ t)
    simpa only [Category.id_comp, Category.assoc] using hh

/-- Over an infinite field a connected reductive group has a rational point
with geometrically maximal torus centralizer and trivial geometric unipotent part. -/
theorem existsRationalStronglyRegularElement :
    Specs.RationalStronglyRegularElements.ExistsRationalStronglyRegularElement.{u} := by
  intro k _ _ H hH
  let := hH.2.1
  have hconn : ConnectedSpace H.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := H.val.X.hom)
  obtain ⟨T, hT, hTK, hmax⟩ := MaximalToriExist.geometricallyMaximalTorusExists H hH.1 hconn
  let K := AlgebraicClosure k
  let HK := GeometricGroup H
  let TK := baseChangedSubgroup K T hTK
  have hs : IsSplitTorus TK.group := isSplitTorus_of_isAlgClosed (G := HK) TK hmax.1
  have hc := Reductive.TorusCentralizer.maximalTorusCentralizer H hH T hT ⟨hTK, hmax⟩
  obtain ⟨t, ht⟩ := exists_point_with_torus_centralizer H T hT hTK hs hc
  let y := t ≫ schemeMap T.inclusion
  refine ⟨T, hT, ⟨hTK, hmax⟩, t, y, rfl, ht, fun L _ _ => pointCentralizerBaseChange L T ht, ?_⟩
  let Talg := closedSubgroupAlgebraicGroup (G := HK) TK
  let tbar : RationalPoints TK.group := toUnit _ ≫ scalarExtendedRationalPoint K t
  let ybar : RationalPoints HK.val := toUnit _ ≫ scalarExtendedRationalPoint K y
  have htbar := SteinbergGeometricFibres.splitTorusJordan Talg hs tbar
  have hybar := Affine.rationalJordanDecompositionFunctorial Talg HK TK.inclusion htbar
  change IsRationalJordanDecomposition ⟨HK.val, HK.property.1⟩
    (pointHom TK.inclusion tbar) (pointHom TK.inclusion tbar) (pointHom TK.inclusion 1) at hybar
  have he : pointHom TK.inclusion tbar = ybar := by
    change (toUnit _ ≫ scalarExtendedRationalPoint K t) ≫ schemeMap TK.inclusion =
      toUnit _ ≫ scalarExtendedRationalPoint K y
    rw [scalarExtendedRationalPoint_comp K t (schemeMap T.inclusion), Category.assoc]
    rfl
  rw [he, map_one] at hybar
  exact hybar

end
end LinearAlgebraicGroups.Arithmetic.RationalStronglyRegularElements
