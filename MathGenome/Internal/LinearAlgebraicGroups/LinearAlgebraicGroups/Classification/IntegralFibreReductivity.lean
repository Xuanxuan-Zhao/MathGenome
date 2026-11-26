import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralFibreReductivity
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RationalRealization
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.LinearCombination

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory Matrix BigOperators

universe u

namespace LinearAlgebraicGroups.IntegralFibreReductivity

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup GroupScheme Lie)
open Specs.IntegralFibreReductivity
open Specs.Pinning (BasedRootDatum)
open Specs.RootGroups (rootPoint)
open Specs.RationalRealization (diagonalTorus)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.GeometricRadicals (IsTrivialSubgroup identitySubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup IsUnipotent)
open Specs.OrderedRootProducts (product)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The simple coroots form a basis under the coroot-lattice hypothesis.
Reflection induction transports the basis functionals to all coroots. -/
theorem primitiveCoroots (D : Specs.Pinning.BasedRootDatum.{u})
    (hspan : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) :
    ∀ a : D.I, ∃ w : D.X, D.datum.coroot' a w = 1 := by
  classical
  let : Finite D.I := D.finiteRoots
  let : D.datum.IsReduced := D.reduced
  have hs : Submodule.span ℤ (Set.range (fun i : D.base.support ↦ D.datum.coroot i)) = ⊤ := by
    have hr : Set.range (fun i : D.base.support ↦ D.datum.coroot i) =
        D.datum.coroot '' (D.base.support : Set D.I) := by
      ext y
      exact ⟨fun ⟨i, hi⟩ ↦ ⟨i.val, i.property, hi⟩,
        fun ⟨i, hi, hiy⟩ ↦ ⟨⟨i, hi⟩, hiy⟩⟩
    rw [hr, D.base.span_int_coroot_support, hspan]
  let b := Module.Basis.mk D.base.linearIndepOn_coroot hs.ge
  have hreflect (a j : D.I) (ha : ∃ w : D.X, D.datum.coroot' a w = 1) :
      ∃ w : D.X, D.datum.coroot' (D.datum.reflectionPerm j a) w = 1 := by
    obtain ⟨w, hw⟩ := ha
    let e := RootPairing.Equiv.reflection D.datum j
    exact ⟨e.weightEquiv w, (e.coroot'_weightEquiv a w).trans hw⟩
  intro a
  refine D.base.induction_reflect a (fun i hi ↦ hreflect i i hi) ?_
    (fun i j hi _ ↦ hreflect i j hi)
  intro i hi
  let j : D.base.support := ⟨i, hi⟩
  let x := D.datum.toLinearMap.toPerfPair.symm (b.coord j)
  use x
  change D.datum.toLinearMap x (D.datum.coroot j) = 1
  change D.datum.toLinearMap.toPerfPair x (D.datum.coroot j) = 1
  rw [show D.datum.toLinearMap.toPerfPair x = b.coord j from
    LinearEquiv.apply_symm_apply _ _]
  exact Module.Basis.mk_coord_apply_eq j


section WeightIsolation

variable {k V I P : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- A stable subspace contains each summand of a sum of joint eigenvectors
whose characters are distinct. -/
private theorem summand_mem_of_stable {S : Submodule k V} {A : P → V →ₗ[k] V}
    {χ : I → P → k} {e : I → V}
    (hA : ∀ t x, x ∈ S → A t x ∈ S)
    (he : ∀ t j, A t (e j) = χ j t • e j)
    (hsep : ∀ i j, i ≠ j → ∃ t, χ i t ≠ χ j t)
    (s : Finset I) (c : I → k) (i : I) (hi : i ∈ s)
    (h : (∑ j ∈ s, c j • e j) ∈ S) : c i • e i ∈ S := by
  classical
  induction s using Finset.strongInductionOn generalizing c with
  | _ s ih =>
    by_cases hs : s = {i}
    · simpa [hs] using h
    · have hex : ∃ j ∈ s, j ≠ i := by
        by_contra! hh
        exact hs (Finset.Subset.antisymm (fun j hj => Finset.mem_singleton.mpr (hh j hj))
          (Finset.singleton_subset_iff.mpr hi))
      obtain ⟨j, hj, hji⟩ := hex
      obtain ⟨t, ht⟩ := hsep i j hji.symm
      let d : I → k := fun x => c x * (χ x t - χ j t)
      have hd : (∑ x ∈ s.erase j, d x • e x) ∈ S := by
        have hdiff := S.sub_mem (hA t _ h) (S.smul_mem (χ j t) h)
        rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib] at hdiff
        simp only [LinearMap.map_smul, he, smul_smul, ← sub_smul] at hdiff
        have hd' : (∑ x ∈ s, d x • e x) ∈ S := by
          simpa only [d, mul_sub, mul_comm (χ j t)] using hdiff
        rwa [← Finset.sum_erase_add _ _ hj, show d j • e j = 0 by simp [d], add_zero] at hd'
      have hdi := S.smul_mem ((χ i t - χ j t)⁻¹)
        (ih (s.erase j) (Finset.erase_ssubset hj) d (Finset.mem_erase.mpr ⟨hji.symm, hi⟩) hd)
      rw [smul_smul, show (χ i t - χ j t)⁻¹ * d i = c i by
        dsimp [d]; field_simp [sub_ne_zero.mpr ht]] at hdi
      exact hdi

/-- Subtracting the identity from the torus action first removes the fixed term. -/
private theorem summand_mem_of_fixed_add_sum {S : Submodule k V} {A : P → V →ₗ[k] V}
    {χ : I → P → k} {e : I → V}
    (hA : ∀ t x, x ∈ S → A t x ∈ S)
    (he : ∀ t j, A t (e j) = χ j t • e j)
    (hsep : ∀ i j, i ≠ j → ∃ t, χ i t ≠ χ j t)
    {z : V} (hz : ∀ t, A t z = z) (s : Finset I) (c : I → k) (i : I) (hi : i ∈ s)
    (h : ∀ t, A t (z + ∑ j ∈ s, c j • e j) - (z + ∑ j ∈ s, c j • e j) ∈ S)
    (hn : ∃ t, χ i t ≠ 1) : c i • e i ∈ S := by
  obtain ⟨t, ht⟩ := hn
  let d : I → k := fun j => c j * (χ j t - 1)
  have hd := h t
  rw [map_add, hz, add_sub_add_left_eq_sub, map_sum, ← Finset.sum_sub_distrib] at hd
  simp only [LinearMap.map_smul, he, smul_smul, ← sub_smul] at hd
  have hsum : (∑ j ∈ s, d j • e j) ∈ S := by
    simpa only [d, mul_sub, mul_one] using hd
  have hh := S.smul_mem ((χ i t - 1)⁻¹) (summand_mem_of_stable hA he hsep s d i hi hsum)
  rw [smul_smul, show (χ i t - 1)⁻¹ * d i = c i by
    dsimp [d]; field_simp [sub_ne_zero.mpr ht]] at hh
  exact hh

end WeightIsolation

section Chart

open Specs.RootGroups (AdditiveLine)
open RootData.RootGroups (additivePoints)
open private additivePoints_natural rootPoint_eq rootPoint_zero
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

variable {k : Type u} [Field k] {D : BasedRootDatum.{u}} {G : GroupScheme k}

private abbrev rootDomain (A : AdditiveLine k) (l : List D.I) :=
  product (fun _ : D.I => A.group.X) l

private def rootListPoint (A : AdditiveLine k) (R : TestAlgebra k) (c : D.I → R) :
    (l : List D.I) → Points (rootDomain A l) R
  | [] => (isTerminalTensorUnit (C := SchemeOver k)).from _
  | i :: l => lift (additivePoints A R (c i)) (rootListPoint A R c l)

private theorem rootListPoint_congr (A : AdditiveLine k) (R : TestAlgebra k) (c d : D.I → R)
    (l : List D.I) (h : ∀ i ∈ l, c i = d i) :
    rootListPoint A R c l = rootListPoint A R d l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [rootListPoint, h i (List.mem_cons_self ..)]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]

private theorem rootListPoint_exists (A : AdditiveLine k) (R : TestAlgebra k)
    (l : List D.I) (hl : l.Nodup) (p : Points (rootDomain A l) R) :
    ∃ c : D.I → R, rootListPoint A R c l = p := by
  classical
  induction l with
  | nil => exact ⟨0, (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _⟩
  | cons i l ih =>
    have hn := List.nodup_cons.mp hl
    let q : Points (rootDomain A l) R := p ≫ snd _ _
    obtain ⟨d, hd⟩ := ih hn.2 q
    let z := (additivePoints A R).symm (p ≫ fst _ _)
    let c := Function.update d i z
    refine ⟨c, ?_⟩
    change lift (additivePoints A R (c i)) (rootListPoint A R c l) = p
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]; simp only [c, Function.update_self, z, Equiv.apply_symm_apply]
    · rw [lift_snd, rootListPoint_congr A R c d l ?_, hd]
      intro j hj
      have hji : j ≠ i := by
        intro h
        subst j
        exact hn.1 hj
      exact Function.update_of_ne hji _ _

private theorem rootListPoint_coordinates (A : AdditiveLine k) (R : TestAlgebra k)
    (l : List D.I) (c d : D.I → R) (h : rootListPoint A R c l = rootListPoint A R d l) :
    ∀ i ∈ l, c i = d i := by
  induction l with
  | nil => simp
  | cons j l ih =>
    intro i hi
    change lift (additivePoints A R (c j)) (rootListPoint A R c l) =
      lift (additivePoints A R (d j)) (rootListPoint A R d l) at h
    rcases List.mem_cons.mp hi with rfl | hi
    · apply (additivePoints A R).injective
      simpa only [lift_fst] using congrArg (fun q => q ≫ fst _ _) h
    · exact ih (by simpa only [lift_snd] using congrArg (fun q => q ≫ snd _ _) h) _ hi

private theorem rootListPoint_map (A : AdditiveLine k) {R S : TestAlgebra k} (f : R ⟶ S)
    (c : D.I → R) (l : List D.I) :
    mapPoints f (rootListPoint A R c l) = rootListPoint A S (fun i => f.hom (c i)) l := by
  induction l with
  | nil => exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  | cons i l ih =>
    change (testSpec k).map f.op ≫ lift (additivePoints A R (c i)) (rootListPoint A R c l) =
      lift (additivePoints A S (f.hom (c i))) (rootListPoint A S (fun j => f.hom (c j)) l)
    rw [comp_lift, ← additivePoints_natural A f (c i), ← ih]

private def chartPoint (M : Marking D G) (R : TestAlgebra k) (c d : D.I → R)
    (t : GroupPoints (diagonalTorus k D).val R) :
    Points (rootDomain M.line M.negative ⊗
      ((diagonalTorus k D).val.X ⊗ rootDomain M.line M.positive)) R :=
  lift (rootListPoint M.line R c M.negative) (lift t (rootListPoint M.line R d M.positive))

private theorem chartPoint_map (M : Marking D G) {R S : TestAlgebra k} (f : R ⟶ S)
    (c d : D.I → R) (t : GroupPoints (diagonalTorus k D).val R) :
    mapPoints f (chartPoint M R c d t) =
      chartPoint M S (fun i => f.hom (c i)) (fun i => f.hom (d i)) (mapPoints f t) := by
  unfold chartPoint
  change (testSpec k).map f.op ≫ lift _ (lift _ _) = _
  rw [comp_lift, comp_lift, ← rootListPoint_map _ f, ← rootListPoint_map _ f]

private theorem rootListPoint_eval (M : Marking D G) (R : TestAlgebra k) (c : D.I → R)
    (l : List D.I) :
    rootListPoint M.line R c l ≫ rootProduct M.line M.root l =
      (l.map (fun i => rootPoint (M.root i) R (c i))).prod := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons i l ih =>
    simp only [rootListPoint, rootProduct, MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd,
      List.map_cons, List.prod_cons, rootPoint_eq, ih]

private theorem chartPoint_eval (M : Marking D G) (R : TestAlgebra k) (c d : D.I → R)
    (t : GroupPoints (diagonalTorus k D).val R) :
    let g := (((groupPointsFunctor k).map M.torus).app R).hom t
    chartPoint M R c d t ≫ cellMap M.line M.torus M.root M.negative M.positive =
      (M.negative.map (fun i => rootPoint (M.root i) R (c i))).prod *
        (g * (M.positive.map (fun i => rootPoint (M.root i) R (d i))).prod) := by
  dsimp only
  simp only [chartPoint, cellMap, MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd,
    rootListPoint_eval]
  rfl

private theorem chartPoint_identity (M : Marking D G) (R : TestAlgebra k) :
    chartPoint M R 0 0 1 ≫ cellMap M.line M.torus M.root M.negative M.positive = 1 := by
  rw [chartPoint_eval]
  have h (l : List D.I) : (l.map (fun _ => (1 : GroupPoints G R))).prod = 1 := by
    induction l with
    | nil => rfl
    | cons i l ih => rw [List.map_cons, List.prod_cons, ih, mul_one]
  simp only [Pi.zero_apply, rootPoint_zero, map_one, h, mul_one]

private theorem chartPoint_exists (M : Marking D G) (R : TestAlgebra k)
    (p : Points (rootDomain M.line M.negative ⊗
      ((diagonalTorus k D).val.X ⊗ rootDomain M.line M.positive)) R) :
    ∃ c d t, chartPoint M R c d t = p := by
  obtain ⟨c, hc⟩ := rootListPoint_exists M.line R M.negative M.negativeOrder.1 (p ≫ fst _ _)
  let q := p ≫ snd _ _
  obtain ⟨d, hd⟩ := rootListPoint_exists M.line R M.positive M.positiveOrder.1 (q ≫ snd _ _)
  refine ⟨c, d, q ≫ fst _ _, ?_⟩
  simp only [chartPoint, hc, hd, lift_comp_fst_snd, q]

/-- A point over a one-point test algebra lifts to the chart as soon as its
residue point is the identity. -/
private theorem chart_lift (M : Marking D G) {R S : TestAlgebra k} (f : R ⟶ S)
    [Subsingleton (PrimeSpectrum R)] [Nonempty (PrimeSpectrum S)]
    (p : GroupPoints G R) (hp : mapPoints f p = 1) :
    ∃ (c d : D.I → R) (t : GroupPoints (diagonalTorus k D).val R),
      chartPoint M R c d t ≫ cellMap M.line M.torus M.root M.negative M.positive = p ∧
      (∀ i ∈ M.negative, f.hom (c i) = 0) ∧ (∀ i ∈ M.positive, f.hom (d i) = 0) ∧
      mapPoints f t = 1 := by
  let j := cellMap M.line M.torus M.root M.negative M.positive
  let : IsOpenImmersion j.left := M.openCell
  have hrange : Set.range p.left ⊆ Set.range j.left := by
    rintro _ ⟨x, rfl⟩
    let s : PrimeSpectrum S := Classical.choice (inferInstance : Nonempty (PrimeSpectrum S))
    have h' : ((testSpec k).map f.op).left ≫ p.left = (1 : GroupPoints G S).left :=
      congrArg (fun a : GroupPoints G S => a.left) hp
    have h'' : (chartPoint M S 0 0 1).left ≫ j.left = (1 : GroupPoints G S).left :=
      congrArg (fun a : GroupPoints G S => a.left) (chartPoint_identity M S)
    refine ⟨(chartPoint M S 0 0 1).left s, ?_⟩
    change ((chartPoint M S 0 0 1).left ≫ j.left) s = p.left x
    rw [h'', ← h']
    have eq : (((testSpec k).map f.op).left s : PrimeSpectrum R) = (x : PrimeSpectrum R) :=
      @Subsingleton.elim (PrimeSpectrum R) inferInstance _ _
    exact congrArg (fun x : PrimeSpectrum R => p.left x) eq
  let a := IsOpenImmersion.lift j.left p.left hrange
  have ha : a ≫ j.left = p.left := IsOpenImmersion.lift_fac _ _ _
  let q : Points _ R := Over.homMk a (by rw [← j.w, ← Category.assoc, ha]; exact p.w)
  have hq : q ≫ j = p := Over.OverMorphism.ext ha
  obtain ⟨c, d, t, he⟩ := chartPoint_exists M R q
  have hc : chartPoint M R c d t ≫ j = p := by rw [he, hq]
  have hred : mapPoints f (chartPoint M R c d t) = chartPoint M S 0 0 1 := by
    let : Mono j := Over.mono_of_mono_left _
    apply (cancel_mono j).mp
    change ((testSpec k).map f.op ≫ chartPoint M R c d t) ≫ j = _
    rw [Category.assoc, hc, chartPoint_identity]
    exact hp
  rw [chartPoint_map] at hred
  change lift _ (lift (mapPoints f t) _) = lift (rootListPoint M.line S 0 M.negative) (lift _ _) at hred
  have hn := congrArg (fun x => x ≫ fst _ _) hred
  have hpos := congrArg (fun x => x ≫ snd _ _) hred
  simp only [lift_fst, lift_snd] at hn hpos
  have ht := congrArg (fun x => x ≫ fst _ _) hpos
  have hpp := congrArg (fun x => x ≫ snd _ _) hpos
  simp only [lift_fst, lift_snd] at ht hpp
  exact ⟨c, d, t, hc, rootListPoint_coordinates _ _ _ _ _ hn,
    rootListPoint_coordinates _ _ _ _ _ hpp, ht⟩

end Chart

section PointsOverExtensions

open private rootPoint_natural rootPoint_zero from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open Specs.DiagonalizableGroups (groupAlgebra)

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {D : BasedRootDatum.{u}} {G : GroupScheme k}

private abbrev extendGroup (K : Type u) [Field K] [Algebra k K] (H : GroupScheme k) :=
  (groupBaseChange k K).obj H

private abbrev extendedPoints (K : Type u) [Field K] [Algebra k K] (H : GroupScheme k)
    (R : TestAlgebra K) :=
  baseChangePointGroupEquiv K H R

private theorem extendedPoints_map (H : GroupScheme k) {R S : TestAlgebra K} (a : R ⟶ S)
    (p : GroupPoints (extendGroup K H) R) :
    extendedPoints K H S (mapPoints a p) =
      mapPoints ((restrictTestAlgebra k K).map a) (extendedPoints K H R p) :=
  baseChangePointsNaturality k K H.X a p

private theorem extendedPoints_postcomp {H J : GroupScheme k} (i : H ⟶ J) (R : TestAlgebra K)
    (p : GroupPoints (extendGroup K H) R) :
    extendedPoints K J R (p ≫ ((groupBaseChange k K).map i).hom.hom) =
      extendedPoints K H R p ≫ i.hom.hom :=
  baseChangePointsSchemeNaturality k K i.hom.hom R p

private abbrev fibreRoot (M : Marking D G) (i : D.I) (R : TestAlgebra K) (a : R) :
    GroupPoints (extendGroup K G) R :=
  (extendedPoints K G R).symm (rootPoint (M.root i) ((restrictTestAlgebra k K).obj R) a)

private theorem fibreRoot_map (M : Marking D G) (i : D.I) {R S : TestAlgebra K}
    (f : R ⟶ S) (a : R) :
    mapPoints f (fibreRoot M i R a) = fibreRoot M i S (f.hom a) := by
  apply (extendedPoints K G S).injective
  rw [extendedPoints_map, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, rootPoint_natural]
  rfl

private theorem fibreRoot_zero (M : Marking D G) (i : D.I) (R : TestAlgebra K) :
    fibreRoot M i R 0 = 1 := by
  rw [fibreRoot, rootPoint_zero, map_one]

private abbrev fibreTorus (M : Marking D G) :
    ClosedSubgroup (extendGroup K G) :=
  Specs.GeometricRadicals.baseChangedSubgroup K M.subgroup
    (baseChangeClosedSubgroup k K M.torus M.torusClosed)

private abbrev fibreTorusPoint (D : BasedRootDatum.{u}) (R : TestAlgebra K)
    (t : TorusValues D R) : GroupPoints (extendGroup K (diagonalTorus k D).val) R :=
  (extendedPoints K (diagonalTorus k D).val R).symm
    (torusPoint D ((restrictTestAlgebra k K).obj R) t)

private theorem torusPoint_map (D : BasedRootDatum.{u}) {R S : TestAlgebra k}
    (f : R ⟶ S) (t : TorusValues D R) :
    mapPoints f (torusPoint D R t) = torusPoint D S ((Units.map f.hom.toMonoidHom).comp t) := by
  change (testSpec k).map f.op ≫ (testSpec k).map _ = (testSpec k).map _
  rw [← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply MonoidAlgebra.algHom_ext
  · intro m
    change f.hom (MonoidAlgebra.lift k R (Multiplicative D.X)
      ((Units.coeHom R).comp t) (MonoidAlgebra.of k (Multiplicative D.X) m)) =
      MonoidAlgebra.lift k S (Multiplicative D.X)
        ((Units.coeHom S).comp ((Units.map f.hom.toMonoidHom).comp t))
        (MonoidAlgebra.of k (Multiplicative D.X) m)
    rw [MonoidAlgebra.lift_of, MonoidAlgebra.lift_of]
    rfl
  · ext

private theorem fibreTorusPoint_map (D : BasedRootDatum.{u}) {R S : TestAlgebra K}
    (f : R ⟶ S) (t : TorusValues D R) :
    mapPoints f (fibreTorusPoint (k := k) D R t) =
      fibreTorusPoint (k := k) D S ((Units.map f.hom.toMonoidHom).comp t) := by
  apply (extendedPoints K (diagonalTorus k D).val S).injective
  rw [extendedPoints_map, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, torusPoint_map]
  rfl

private theorem torusPoint_injective (D : BasedRootDatum.{u}) (R : TestAlgebra k) :
    Function.Injective (torusPoint D R) := by
  intro a b hab
  have h := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective hab
  have h' := Quiver.Hom.op_inj h
  apply MonoidHom.ext
  intro m
  apply Units.ext
  have hval := congrArg (fun f : CommAlgCat.of k (MonoidAlgebra k (Multiplicative D.X)) ⟶ R =>
    f.hom (MonoidAlgebra.of k (Multiplicative D.X) m)) h'
  rw [CommAlgCat.hom_ofHom, CommAlgCat.hom_ofHom,
    MonoidAlgebra.lift_of, MonoidAlgebra.lift_of] at hval
  exact hval

private theorem torusPoint_one (D : BasedRootDatum.{u}) (R : TestAlgebra k) :
    torusPoint D R 1 = 1 := by
  let A := groupAlgebra k (Multiplicative D.X)
  let e := hopfSpecPointIso A
  change e.hom.app R (WithConv.toConv (MonoidAlgebra.lift k R (Multiplicative D.X)
    ((Units.coeHom R).comp (1 : TorusValues D R)))) = _
  rw [← map_one (e.hom.app R).hom]
  congr 1
  apply WithConv.ofConv_injective
  apply MonoidAlgebra.algHom_ext
  · intro m
    change MonoidAlgebra.lift k R (Multiplicative D.X)
      ((Units.coeHom R).comp (1 : TorusValues D R)) (MonoidAlgebra.of k (Multiplicative D.X) m) = _
    rw [MonoidAlgebra.lift_of]
    change (1 : R) = algebraMap k R (Coalgebra.counit (R := k) (A := A)
      (MonoidAlgebra.of k (Multiplicative D.X) m))
    rw [(MonoidAlgebra.isGroupLikeElem_of m).counit_eq_one, map_one]
  · ext

private theorem fibreTorusPoint_injective (D : BasedRootDatum.{u}) (R : TestAlgebra K) :
    Function.Injective (fibreTorusPoint (k := k) D R) :=
  (extendedPoints K (diagonalTorus k D).val R).symm.injective.comp (torusPoint_injective D _)

private theorem fibreTorusPoint_one (D : BasedRootDatum.{u}) (R : TestAlgebra K) :
    fibreTorusPoint (k := k) D R 1 = 1 := by
  change (extendedPoints K (diagonalTorus k D).val R).symm
    (torusPoint D ((restrictTestAlgebra k K).obj R) 1) = 1
  rw [torusPoint_one, map_one]

private theorem fibre_conjugation (M : Marking D G) (R : TestAlgebra K)
    (t : TorusValues D R) (i : D.I) (a : R) :
    let g : GroupPoints (extendGroup K G) R :=
      fibreTorusPoint (k := k) D R t ≫ (fibreTorus (K := K) M).inclusion.hom.hom
    g * fibreRoot M i R a * g⁻¹ =
      fibreRoot M i R ((t (Multiplicative.ofAdd (D.datum.root i)) : R) * a) := by
  dsimp only
  apply (extendedPoints K G R).injective
  rw [map_mul, map_mul, map_inv]
  erw [extendedPoints_postcomp (K := K) M.torus]
  simp only [fibreRoot, fibreTorusPoint, MulEquiv.apply_symm_apply]
  exact M.conjugation ((restrictTestAlgebra k K).obj R) t i a

private def fibreRankOne (M : Marking D G) (i : D.I) (R : TestAlgebra K) :
    Matrix.SpecialLinearGroup (Fin 2) R →* GroupPoints (extendGroup K G) R :=
  (extendedPoints K G R).symm.toMonoidHom.comp
    ((M.rankOne i).app ((restrictTestAlgebra k K).obj R)).hom

private theorem fibreRankOne_upper (M : Marking D G) (i : D.I) (R : TestAlgebra K) (a : R) :
    fibreRankOne M i R (Specs.IntegralRootRelations.upper a) = fibreRoot M i R a :=
  congrArg (extendedPoints K G R).symm (M.rankOneUpper i ((restrictTestAlgebra k K).obj R) a)

private theorem fibreRankOne_lower (M : Marking D G) (i : D.I) (R : TestAlgebra K) (a : R) :
    fibreRankOne M i R (Specs.IntegralRootRelations.lower a) =
      fibreRoot M (D.datum.reflectionPerm i i) R a :=
  congrArg (extendedPoints K G R).symm (M.rankOneLower i ((restrictTestAlgebra k K).obj R) a)

private theorem fibreRankOne_diagonal (M : Marking D G) (i : D.I) (R : TestAlgebra K) (a : Rˣ) :
    fibreRankOne M i R (Specs.IntegralRootRelations.diagonal a) =
      fibreTorusPoint (k := k) D R (cocharacter D (D.datum.coroot i) R a) ≫
        (fibreTorus (K := K) M).inclusion.hom.hom := by
  let e := extendedPoints K G R
  let t := fibreTorusPoint (k := k) D R (cocharacter D (D.datum.coroot i) R a)
  apply e.injective
  change e (e.symm ((M.rankOne i).app ((restrictTestAlgebra k K).obj R)
    (Specs.IntegralRootRelations.diagonal a))) =
      e (t ≫ ((groupBaseChange k K).map M.torus).hom.hom)
  refine (e.apply_symm_apply _).trans ?_
  refine (M.rankOneDiagonal i ((restrictTestAlgebra k K).obj R) a).trans ?_
  rw [extendedPoints_postcomp (K := K) M.torus R t]
  exact congrArg (fun z => z ≫ M.torus.hom.hom)
    ((extendedPoints K (diagonalTorus k D).val R).apply_symm_apply _).symm

end PointsOverExtensions

section Tangents

open Specs.AdjointRepresentation (constants)
open private split_torus_sections_commute from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {D : BasedRootDatum.{u}} {G : GroupScheme k}

private abbrev basicTest (K : Type u) [Field K] := CommAlgCat.of K K
private abbrev dualTest (K : Type u) [Field K] := CommAlgCat.of K (DualNumber K)

private theorem dualSpectrumSubsingleton (K : Type u) [Field K] :
    Subsingleton (PrimeSpectrum (DualNumber K)) := by
  have h (P : PrimeSpectrum (DualNumber K)) (z : DualNumber K) :
      z ∈ P.asIdeal ↔ z.fst = 0 := by
    constructor
    · intro hz
      by_contra hn
      exact P.isPrime.ne_top (P.asIdeal.eq_top_of_isUnit_mem hz
        (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hn)))
    · intro hz
      apply P.isPrime.mem_of_pow_mem 2
      have he : z ^ 2 = 0 := by
        rw [pow_two]
        apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, hz]
      rw [he]
      exact P.asIdeal.zero_mem
  exact ⟨fun P Q => PrimeSpectrum.ext (Ideal.ext fun z => (h P z).trans (h Q z).symm)⟩

private def rootTangent (M : Marking D G) (i : D.I) (a : K) : Lie K (extendGroup K G) := by
  refine ⟨fibreRoot M i (dualTest K) (TrivSqZeroExt.inr a), ?_⟩
  change mapPoints (dualReduction K) (fibreRoot M i (dualTest K) (TrivSqZeroExt.inr a)) = 1
  rw [fibreRoot_map, show (dualReduction K).hom (TrivSqZeroExt.inr a) = 0 from rfl,
    fibreRoot_zero]

private theorem tangent_add_val {H : GroupScheme K} (v w : Lie K H) :
    (v + w).toMul.val = v.toMul.val * w.toMul.val := rfl

private theorem tangent_zero_val {H : GroupScheme K} :
    (0 : Lie K H).toMul.val = 1 := rfl

private theorem tangent_scale_val {H : GroupScheme K} (a : K) (v : Lie K H) :
    (a • v).toMul.val = mapPoints (CommAlgCat.ofHom (dualNumberScale a)) v.toMul.val := rfl

private theorem rootTangent_smul (M : Marking D G) (i : D.I) (a : K) :
    a • rootTangent M i 1 = rootTangent M i a := by
  apply Subtype.ext
  change (a • rootTangent M i (1 : K)).toMul.val = _
  rw [tangent_scale_val, show (rootTangent M i (1 : K)).toMul.val =
    fibreRoot M i (dualTest K) (TrivSqZeroExt.inr (1 : K)) from rfl, fibreRoot_map]
  congr 1
  change dualNumberScale a (DualNumber.eps : DualNumber K) = TrivSqZeroExt.inr a
  exact (dualNumberScaling K a).trans (DualNumber.inr_eq_smul_eps a).symm

private abbrev pointMap {H J : GroupScheme K} (f : H ⟶ J) (R : TestAlgebra K) :
    GroupPoints H R →* GroupPoints J R :=
  (((groupPointsFunctor K).map f).app R).hom

private abbrev mapTest {H : GroupScheme K} {R S : TestAlgebra K} (f : R ⟶ S) :
    GroupPoints H R →* GroupPoints H S :=
  (((groupPointsFunctor K).obj H).map f).hom

private theorem pointMap_mapTest {H J : GroupScheme K} (f : H ⟶ J)
    {R S : TestAlgebra K} (a : R ⟶ S) (p : GroupPoints H R) :
    pointMap f S (mapTest a p) = mapTest a (pointMap f R p) := by
  change ((testSpec K).map a.op ≫ p) ≫ f.hom.hom =
    (testSpec K).map a.op ≫ (p ≫ f.hom.hom)
  exact Category.assoc _ _ _

private theorem mapTest_mapTest {H : GroupScheme K} {R S T : TestAlgebra K}
    (a : R ⟶ S) (b : S ⟶ T) (p : GroupPoints H R) :
    mapTest b (mapTest a p) = mapTest (a ≫ b) p := by
  exact (congrArg (fun f => GrpCat.Hom.hom f p)
    (((groupPointsFunctor K).obj H).map_comp a b)).symm

private def conjugateTangent {H : GroupScheme K} (g : GroupPoints H (basicTest K))
    (v : Lie K H) : Lie K H := by
  let c : GroupPoints H (dualTest K) := mapTest (constants (basicTest K)) g
  refine ⟨c * v.toMul.val * c⁻¹, ?_⟩
  change mapTest (dualReduction K) (c * v.toMul.val * c⁻¹) = 1
  have hv : mapTest (dualReduction K) v.toMul.val = 1 := v.toMul.property
  rw [map_mul, map_mul, map_inv, hv, mul_one, mul_inv_cancel]

private def adjointOperator {H : GroupScheme K} [IsAffine H.X.left]
    (g : GroupPoints H (basicTest K)) :
    Lie K H →ₗ[K] Lie K H := by
  let c : GroupPoints H (dualTest K) := mapTest (constants (basicTest K)) g
  refine { toFun := conjugateTangent g, map_add' := ?_, map_smul' := ?_ }
  · intro v w
    apply Subtype.ext
    change c * (v + w).toMul.val * c⁻¹ = (conjugateTangent g v + conjugateTangent g w).toMul.val
    rw [tangent_add_val, tangent_add_val]
    change c * (v.toMul.val * w.toMul.val) * c⁻¹ =
      (c * v.toMul.val * c⁻¹) * (c * w.toMul.val * c⁻¹)
    group
  · intro a v
    apply Subtype.ext
    change c * (a • v).toMul.val * c⁻¹ = (a • conjugateTangent g v).toMul.val
    rw [tangent_scale_val, tangent_scale_val]
    let f := CommAlgCat.ofHom (dualNumberScale a)
    change c * mapTest f v.toMul.val * c⁻¹ = mapTest f (c * v.toMul.val * c⁻¹)
    have hc : mapTest f c = c := by
      change mapTest f (mapTest (constants (basicTest K)) g) = _
      rw [mapTest_mapTest, show constants (basicTest K) ≫ f = constants (basicTest K) by
        apply CommAlgCat.hom_ext
        apply AlgHom.ext
        intro x
        change dualNumberScale a (algebraMap K (DualNumber K) x) = algebraMap K (DualNumber K) x
        exact (dualNumberScale a).commutes x]
    rw [map_mul, map_mul, map_inv, hc]

private abbrev torusOperator (M : Marking D G) [IsAffine (extendGroup K G).X.left]
    (t : TorusValues D (basicTest K)) :=
  adjointOperator (pointMap (fibreTorus (K := K) M).inclusion (basicTest K)
    (fibreTorusPoint (k := k) D (basicTest K) t))

private theorem torusOperator_root (M : Marking D G) [IsAffine (extendGroup K G).X.left]
    (t : TorusValues D (basicTest K)) (i : D.I) :
    torusOperator M t (rootTangent M i 1) =
      (t (Multiplicative.ofAdd (D.datum.root i)) : K) • rootTangent M i 1 := by
  rw [rootTangent_smul M]
  apply Subtype.ext
  let f := constants (basicTest K)
  let T := fibreTorus (K := K) M
  let e := pointMap T.inclusion (dualTest K)
  let t' := (Units.map f.hom.toMonoidHom).comp t
  have hg : mapTest f (pointMap T.inclusion (basicTest K)
      (fibreTorusPoint (k := k) D (basicTest K) t)) = e (fibreTorusPoint (k := k) D (dualTest K) t') := by
    change mapPoints f (fibreTorusPoint (k := k) D (basicTest K) t ≫ T.inclusion.hom.hom) = _
    rw [show mapPoints f (fibreTorusPoint (k := k) D (basicTest K) t ≫ T.inclusion.hom.hom) =
      mapPoints f (fibreTorusPoint (k := k) D (basicTest K) t) ≫ T.inclusion.hom.hom
      from (Category.assoc ..).symm, fibreTorusPoint_map]
    rfl
  change (mapTest f _ * fibreRoot M i (dualTest K) (TrivSqZeroExt.inr (1 : K))) *
      (mapTest f _)⁻¹ = fibreRoot M i (dualTest K)
        (TrivSqZeroExt.inr (t (Multiplicative.ofAdd (D.datum.root i)) : K))
  rw [hg]
  refine (fibre_conjugation M (dualTest K) t' i _).trans ?_
  congr 1
  apply TrivSqZeroExt.ext
  · simp [TrivSqZeroExt.fst_mul]
  · change (t (Multiplicative.ofAdd (D.datum.root i)) : K) * 1 + 0 * 0 =
      (t (Multiplicative.ofAdd (D.datum.root i)) : K)
    simp

private theorem torusOperator_torus (M : Marking D G) [IsAffine (extendGroup K G).X.left]
    (hT : Specs.GeometricRadicals.IsSplitTorus (fibreTorus (K := K) M).group)
    (t : TorusValues D (basicTest K)) (v : Lie K (fibreTorus (K := K) M).group) :
    torusOperator M t (mapPointKernel (fibreTorus (K := K) M).inclusion v) =
      mapPointKernel (fibreTorus (K := K) M).inclusion v := by
  apply Subtype.ext
  let T := fibreTorus (K := K) M
  let f := pointMap T.inclusion (dualTest K)
  let a := (mapTest (constants (basicTest K))) (fibreTorusPoint (k := k) D (basicTest K) t)
  change f a * f v.toMul.val * (f a)⁻¹ = f v.toMul.val
  rw [← map_inv, ← map_mul, ← map_mul, (split_torus_sections_commute hT a v.toMul.val).eq,
    mul_inv_cancel_right]

private theorem rootSum_val (M : Marking D G)
    (l : List D.I) (c : D.I → K) :
    ((l.map fun i => rootTangent M i (c i)).sum).toMul.val =
      (l.map fun i => fibreRoot M i (dualTest K) (TrivSqZeroExt.inr (c i))).prod := by
  induction l with
  | nil => exact tangent_zero_val
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons, List.prod_cons, tangent_add_val, ih]
    rfl

/-- The pointed open chart gives the linear spanning relation for the full
identity tangent kernel over every extension field. -/
private theorem tangent_decomposition (M : Marking D G) [IsAffine (extendGroup K G).X.left]
    [Fintype D.I] (p : Lie K (extendGroup K G)) :
    ∃ (t : Lie K (fibreTorus (K := K) M).group) (c : D.I → K),
      p = mapPointKernel (fibreTorus (K := K) M).inclusion t +
        ∑ i, c i • rootTangent M i 1 := by
  classical
  let Q := dualTest K
  let R := (restrictTestAlgebra k K).obj Q
  let S := (restrictTestAlgebra k K).obj (basicTest K)
  let f : R ⟶ S := (restrictTestAlgebra k K).map (dualReduction K)
  let : Subsingleton (PrimeSpectrum R) := dualSpectrumSubsingleton K
  let : Nonempty (PrimeSpectrum S) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  let q := extendedPoints K G Q p.toMul.val
  have hq : mapPoints f q = 1 := by
    rw [← extendedPoints_map]
    change extendedPoints K G (basicTest K) (reduceTangentPoints (extendGroup K G) p.toMul.val) = 1
    rw [p.toMul.property, map_one]
  obtain ⟨a, b, v, he, ha, hb, hv⟩ := chart_lift M f q hq
  rw [chartPoint_eval] at he
  let t₀ := (extendedPoints K (diagonalTorus k D).val Q).symm v
  let t : Lie K (fibreTorus (K := K) M).group := ⟨t₀, by
    change mapPoints (dualReduction K) t₀ = 1
    apply (extendedPoints K (diagonalTorus k D).val (basicTest K)).injective
    rw [extendedPoints_map, map_one, show extendedPoints K (diagonalTorus k D).val Q t₀ = v
      from MulEquiv.apply_symm_apply _ _]
    exact hv⟩
  let c : D.I → K := fun i => if i ∈ M.negative then (a i).snd else (b i).snd
  have hdisj (i : D.I) (hn : i ∈ M.negative) (hp : i ∈ M.positive) : False :=
    (M.negativeOrder.2 i).mp hn ((M.positiveOrder.2 i).mp hp)
  have ha' (i : D.I) (hi : i ∈ M.negative) : a i = TrivSqZeroExt.inr (c i) := by
    apply TrivSqZeroExt.ext
    · exact ha i hi
    · change (a i).snd = c i
      exact (ite_eq_left hi).symm
  have hb' (i : D.I) (hi : i ∈ M.positive) : b i = TrivSqZeroExt.inr (c i) := by
    apply TrivSqZeroExt.ext
    · exact hb i hi
    · change (b i).snd = c i
      exact (ite_eq_right fun hn => hdisj i hn hi).symm
  have hn : (M.negative ++ M.positive).Nodup := by
    rw [List.nodup_append]
    exact ⟨M.negativeOrder.1, M.positiveOrder.1, fun i hi j hj eq => hdisj i hi (eq ▸ hj)⟩
  have hall : (M.negative ++ M.positive).toFinset = Finset.univ := by
    ext i
    simp only [List.mem_toFinset, List.mem_append, Finset.mem_univ, iff_true]
    by_cases hi : D.base.IsPos i
    · exact Or.inr ((M.positiveOrder.2 i).mpr hi)
    · exact Or.inl ((M.negativeOrder.2 i).mpr hi)
  refine ⟨t, c, ?_⟩
  rw [show (∑ i, c i • rootTangent M i (1 : K)) = (∑ i, rootTangent M i (c i)) from
    Finset.sum_congr rfl fun i _ => rootTangent_smul M i (c i),
    ← hall, List.sum_toFinset _ hn, List.map_append, List.sum_append,
    ← add_assoc, add_comm (mapPointKernel _ t), add_assoc]
  apply Subtype.ext
  let n := (M.negative.map fun i => rootTangent M i (c i)).sum
  let p' := (M.positive.map fun i => rootTangent M i (c i)).sum
  let q' := mapPointKernel (fibreTorus (K := K) M).inclusion t
  change p.toMul.val = (n + (q' + p')).toMul.val
  rw [tangent_add_val n (q' + p'), tangent_add_val q' p']
  rw [show n.toMul.val = _ from rootSum_val M M.negative c,
    show p'.toMul.val = _ from rootSum_val M M.positive c]
  let e := extendedPoints K G Q
  have hprod (l : List D.I) (r : D.I → R)
      (hr : ∀ i ∈ l, r i = TrivSqZeroExt.inr (c i)) :
      e (l.map (fun i => fibreRoot M i Q (TrivSqZeroExt.inr (c i)))).prod =
        (l.map (fun i => rootPoint (M.root i) R (r i))).prod := by
    rw [map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    change e (e.symm _) = _
    rw [e.apply_symm_apply, hr i hi]
  have ht : e q'.toMul.val = pointMap M.torus R v := by
    change e (t₀ ≫ ((groupBaseChange k K).map M.torus).hom.hom) = _
    have h := extendedPoints_postcomp (K := K) M.torus Q t₀
    refine h.trans ?_
    exact congrArg (fun w => w ≫ M.torus.hom.hom)
      ((extendedPoints K (diagonalTorus k D).val Q).apply_symm_apply v)
  apply e.injective
  rw [map_mul, map_mul, hprod M.negative a ha', hprod M.positive b hb', ht]
  exact he.symm

end Tangents

section CharacterSeparation

variable {K : Type u} [Field K] [Infinite K]

private theorem exists_unit_pow_ne_one (n : ℕ) (hn : n ≠ 0) :
    ∃ t : Kˣ, t ^ n ≠ 1 := by
  by_contra! h
  let p : Polynomial K := Polynomial.X * (Polynomial.X ^ n - 1)
  have hp : ∀ a : K, p.eval a = 0 := by
    intro a
    by_cases ha : a = 0
    · simp [p, ha]
    · have he := congrArg Units.val (h (Units.mk0 a ha))
      change a ^ n = 1 at he
      simp [p, he]
  have hz : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    convert Set.infinite_univ (α := K) using 1
    ext a
    simp [Polynomial.IsRoot, hp]
  exact (mul_ne_zero Polynomial.X_ne_zero
    (by simpa only [Polynomial.C_1] using (Polynomial.monic_X_pow_sub_C (1 : K) hn).ne_zero)) hz

private theorem exists_unit_zpow_ne_one (n : ℤ) (hn : n ≠ 0) :
    ∃ t : Kˣ, t ^ n ≠ 1 := by
  cases n with
  | ofNat n =>
    obtain ⟨t, ht⟩ := exists_unit_pow_ne_one (K := K) n (by simpa using hn)
    exact ⟨t, by simpa using ht⟩
  | negSucc n =>
    obtain ⟨t, ht⟩ := exists_unit_pow_ne_one (K := K) (n + 1) (Nat.succ_ne_zero n)
    exact ⟨t, by simpa [zpow_negSucc] using ht⟩

private theorem separates_characters (D : BasedRootDatum.{u}) {x y : D.X} (h : x ≠ y) :
    ∃ t : TorusValues D (basicTest K),
      (t (Multiplicative.ofAdd x) : K) ≠ (t (Multiplicative.ofAdd y) : K) := by
  let := D.freeX
  let := D.finiteX
  let b := Module.finBasis ℤ D.X
  have hrepr : b.repr x ≠ b.repr y := fun h' => h (b.repr.injective h')
  have hs : ∃ j, b.repr x j ≠ b.repr y j := by
    by_contra! hz
    exact hrepr (Finsupp.ext hz)
  obtain ⟨j, hj⟩ := hs
  obtain ⟨a, ha⟩ := exists_unit_zpow_ne_one (K := K) (b.repr x j - b.repr y j)
    (sub_ne_zero.mpr hj)
  let t : TorusValues D (basicTest K) := {
    toFun z := a ^ b.repr z.toAdd j
    map_one' := by simp
    map_mul' := fun z w => by
      change a ^ b.repr (z.toAdd + w.toAdd) j = _
      rw [map_add, Finsupp.add_apply, zpow_add] }
  refine ⟨t, fun hval => ha ?_⟩
  have he : a ^ b.repr x j = a ^ b.repr y j := Units.ext hval
  rw [zpow_sub, he, mul_inv_cancel]

end CharacterSeparation

section Radical

open Specs.IntegralRootRelations (upper lower diagonal)
open InfinitesimalCommutator (TwoVariables liftS liftT)
open Specs.GeometricRadicals (IsSplitTorus)
open private diagonalBaseChange diagonalSplit from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RationalRealization
open private isIso_of_closedImmersion_of_differential
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {D : BasedRootDatum.{u}} {G : AffineAlgebraicGroup k}

private theorem fibreTorus_split (M : Marking D G.val) :
    IsSplitTorus (fibreTorus (K := K) M).group := by
  obtain ⟨r, ⟨e⟩⟩ := diagonalSplit K D
  exact ⟨r, ⟨diagonalBaseChange k K (Multiplicative D.X) ≪≫ e⟩⟩

private abbrev IsMultiplicativeType (H : AffineAlgebraicGroup K) :=
  (Specs.CharacterDescent.multiplicativeTypeSpecFunctor K).essImage H

private theorem fibreTorus_multiplicativeType (M : Marking D G.val) :
    IsMultiplicativeType (closedSubgroupAlgebraicGroup (G := Specs.Unipotent.baseChangedAlgebraicGroup K G)
      (fibreTorus (K := K) M)) := by
  let : Module.Finite ℤ D.X := D.finiteX
  let : Group.FG (Multiplicative D.X) :=
    GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp D.finiteX)
  let N : Specs.DiagonalizableGroups.FGAbelianGroup.{u} :=
    ⟨CommGrpCat.of (Multiplicative D.X), inferInstance⟩
  apply (CharacterDescent.multiplicativeTypeGroupCriterion _).mpr
  let e := diagonalBaseChange k K (Multiplicative D.X)
  exact ⟨K, inferInstance, inferInstance, inferInstance, N,
    ⟨(groupBaseChange K K).mapIso e ≪≫ diagonalBaseChange K K (Multiplicative D.X)⟩⟩

/-- The trivial intersection applies to sections over arbitrary test rings. -/
private theorem eq_one_of_unipotent_and_torus_point {H : AffineAlgebraicGroup K}
    (U T : ClosedSubgroup H.val) (hU : IsUnipotent (closedSubgroupAlgebraicGroup U))
    (hT : IsMultiplicativeType (closedSubgroupAlgebraicGroup T)) (R : TestAlgebra K)
    (u : GroupPoints U.group R) (t : GroupPoints T.group R)
    (h : pointMap U.inclusion R u = pointMap T.inclusion R t) : u = 1 ∧ t = 1 := by
  let P := pullback U.inclusion T.inclusion
  let a := pullback.fst U.inclusion T.inclusion
  let b := pullback.snd U.inclusion T.inclusion
  let hp := IsPullback.of_hasPullback U.inclusion T.inclusion
  let hX := hp.map (Grp.forget (SchemeOver K))
  have hP : IsZero P := Unipotent.unipotentMultiplicativeTypeIntersection H U T a b hp hU hT
  let e := (Grp.forget (SchemeOver K)).mapIso (hP.iso (Grp.isZero_trivial (SchemeOver K)))
  have hterm : IsTerminal P.X := (isTerminalTensorUnit (C := SchemeOver K)).ofIso e.symm
  let z : GroupPoints P R := hX.lift u t h
  have hz : z = 1 := hterm.hom_ext _ _
  have hu : pointMap a R z = u := hX.lift_fst _ _ _
  have ht : pointMap b R z = t := hX.lift_snd _ _ _
  rw [hz, map_one] at hu ht
  exact ⟨hu.symm, ht.symm⟩

private def infinitesimalUnit {R : Type*} [CommRing R] (x : R) (hx : x * x = 0) : Rˣ where
  val := 1 + x
  inv := 1 - x
  val_inv := by linear_combination -hx
  inv_val := by linear_combination -hx

/-- Commuting two independent first-order transvections gives the mixed
coroot unit, with coefficient one in every characteristic. -/
private theorem mixedRankOneIdentity {R : Type*} [CommRing R] (x y : R)
    (hx : x * x = 0) (hy : y * y = 0) :
    upper x * lower y * (upper x)⁻¹ * (lower y)⁻¹ =
      diagonal (infinitesimalUnit (x * y) (by rw [mul_mul_mul_comm, hx, hy, zero_mul])) := by
  let s := infinitesimalUnit (x * y) (by rw [mul_mul_mul_comm, hx, hy, zero_mul])
  have h : upper x * lower y = diagonal s * (lower y * upper x) := by
    apply Subtype.ext
    change (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) R) * !![1, 0; y, 1] =
      (!![(s : R), 0; 0, (↑s⁻¹ : R)] : Matrix (Fin 2) (Fin 2) R) *
        (!![1, 0; y, 1] * !![1, x; 0, 1])
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, s, infinitesimalUnit]
    · linear_combination -y * hx
    · linear_combination x * hy
    · linear_combination y ^ 2 * hx
  change _ = diagonal s
  rw [h]
  group

private theorem fibreRoot_commutator (M : Marking D G.val) (i : D.I) (R : TestAlgebra K)
    (x y : R) (hx : x * x = 0) (hy : y * y = 0) :
    let X := fibreRoot M i R x
    let Y := fibreRoot M (D.datum.reflectionPerm i i) R y
    let s := infinitesimalUnit (x * y) (by rw [mul_mul_mul_comm, hx, hy, zero_mul])
    X * Y * X⁻¹ * Y⁻¹ = pointMap (fibreTorus (K := K) M).inclusion R
      (fibreTorusPoint (k := k) D R (cocharacter D (D.datum.coroot i) R s)) := by
  dsimp only
  rw [show pointMap (fibreTorus (K := K) M).inclusion R _ = _ from
    (fibreRankOne_diagonal M i R _).symm]
  have h := congrArg (fibreRankOne M i R) (mixedRankOneIdentity x y hx hy)
  simp only [map_mul, map_inv] at h
  rw [fibreRankOne_upper M i R x, fibreRankOne_lower M i R y] at h
  exact h

private theorem root_tangent_excluded (M : Marking D G.val)
    (U : ClosedSubgroup (extendGroup K G.val))
    (hU : IsUnipotent (closedSubgroupAlgebraicGroup
      (G := Specs.Unipotent.baseChangedAlgebraicGroup K G) U))
    (hN : Specs.IsNormalSubgroup U.inclusion) (i : D.I) (w : D.X)
    (hw : D.datum.coroot' i w = 1) :
    rootTangent M i (1 : K) ∉ Set.range (mapPointKernel U.inclusion) := by
  rintro ⟨p, hp⟩
  let R := CommAlgCat.of K (TwoVariables K)
  let Q := dualTest K
  let a : Q ⟶ R := CommAlgCat.ofHom (liftS K)
  let x : TwoVariables K := liftS K DualNumber.eps
  let y : TwoVariables K := liftT K DualNumber.eps
  have hx : x * x = 0 := by
    change liftS K _ * liftS K _ = 0
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hy : y * y = 0 := by
    change liftT K _ * liftT K _ = 0
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  let s : (TwoVariables K)ˣ :=
    infinitesimalUnit (x * y) (by rw [mul_mul_mul_comm x y x y, hx, hy, zero_mul])
  let e := pointMap U.inclusion R
  let v : GroupPoints U.group R := mapTest a p.toMul.val
  let X := fibreRoot M i R x
  let Y := fibreRoot M (D.datum.reflectionPerm i i) R y
  have hX : e v = X := by
    have h := congrArg (fun z : Lie K (extendGroup K G.val) => z.toMul.val) hp
    change pointMap U.inclusion Q p.toMul.val = fibreRoot M i Q (TrivSqZeroExt.inr (1 : K)) at h
    change pointMap U.inclusion R (mapTest a p.toMul.val) = X
    rw [pointMap_mapTest, h]
    change mapPoints a (fibreRoot M i Q (TrivSqZeroExt.inr (1 : K))) = _
    rw [fibreRoot_map]
    rfl
  obtain ⟨b₀, hb⟩ := normalSubgroup_conjugate_sections hN Y v
  let b : GroupPoints U.group R := b₀
  let u : GroupPoints U.group R := v * b⁻¹
  have hu : e u = X * Y * X⁻¹ * Y⁻¹ := by
    change e (v * b⁻¹) = _
    have hb' : e b = Y * e v * Y⁻¹ := hb
    rw [map_mul, map_inv, hb', hX]
    group
  let t := fibreTorusPoint (k := k) D R (cocharacter D (D.datum.coroot i) R s)
  have ht : X * Y * X⁻¹ * Y⁻¹ = pointMap (fibreTorus (K := K) M).inclusion R t :=
    fibreRoot_commutator M i R x y hx hy
  have ht' := (eq_one_of_unipotent_and_torus_point
    (H := Specs.Unipotent.baseChangedAlgebraicGroup K G)
    U (fibreTorus (K := K) M) hU (fibreTorus_multiplicativeType M) R u t (hu.trans ht)).2
  have ht1 : cocharacter D (D.datum.coroot i) R s = 1 :=
    fibreTorusPoint_injective (k := k) D R (ht'.trans (fibreTorusPoint_one (k := k) D R).symm)
  have ha := congrArg (fun q : TorusValues D R => q (Multiplicative.ofAdd w)) ht1
  change s ^ D.datum.coroot' i w = 1 at ha
  rw [hw, zpow_one] at ha
  have hm := congrArg (fun q : Rˣ => q.val.snd.snd) ha
  change (1 + x * y : TwoVariables K).snd.snd = 0 at hm
  have hn : (1 + x * y : TwoVariables K).snd.snd = 1 := by
    have hx' : x = (((0, 1) : DualNumber K), 0) := rfl
    have hy' : y = (0, ((1, 0) : DualNumber K)) := rfl
    rw [hx', hy']
    simp
  exact one_ne_zero (hn.symm.trans hm)

/-- A smooth connected closed subgroup with zero tangent is the identity. -/
private theorem trivial_of_zero_tangent {H : AffineAlgebraicGroup K}
    (U : ClosedSubgroup H.val) (hs : Smooth U.group.X.hom) (hc : ConnectedSpace U.group.X.left)
    (h : ∀ p : Lie K U.group, p = 0) : IsTrivialSubgroup U := by
  let V := closedSubgroupAlgebraicGroup U
  let A := closedSubgroupAlgebraicGroup (identitySubgroup V)
  let i := (identitySubgroup V).inclusion
  have hclosed : IsClosedImmersion i.hom.hom.left := (identitySubgroup V).isClosedImmersion
  have hAs : Smooth A.val.X.hom := inferInstanceAs (Smooth (𝟙 (Spec (CommRingCat.of K))))
  have hAc : ConnectedSpace A.val.X.left := inferInstanceAs (ConnectedSpace (PrimeSpectrum K))
  have hsurj : Function.Surjective (mapPointKernel i) := fun p => ⟨0, (h _).trans (h p).symm⟩
  let := isIso_of_closedImmersion_of_differential (A := A) (B := V) i hclosed hAs hAc hs hc hsurj
  exact ⟨(asIso i).symm⟩

end Radical

section GeometricConclusions

open Specs.AdjointRepresentation (constants)
open Specs.GeometricRadicals (IsMaximalTorus IsSplitTorus)
open private torus_has_split_coordinates split_torus_sections_commute
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private isTorus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private subgroupOf_of_lieImage splitTorus_connected
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private splitTorusSmooth from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {D : BasedRootDatum.{u}} {G : AffineAlgebraicGroup k}

private theorem pointMap_injective {H J : GroupScheme K} (f : H ⟶ J)
    (hf : IsClosedImmersion f.hom.hom.left) (R : TestAlgebra K) :
    Function.Injective (pointMap f R) := by
  let := hf
  let : Mono f.hom.hom := Over.mono_of_mono_left _
  exact fun a b h => (cancel_mono f.hom.hom).mp h

private theorem normal_tangent_image_stable {H J : GroupScheme K}
    (f : H ⟶ J) (hf : IsClosedImmersion f.hom.hom.left) (hn : Specs.IsNormalSubgroup f)
    (g : GroupPoints J (basicTest K)) (p : Lie K H) :
    conjugateTangent g (mapPointKernel f p) ∈ Set.range (mapPointKernel f) := by
  let Q := dualTest K
  let B := basicTest K
  let c : GroupPoints J Q := mapTest (constants B) g
  let v := conjugateTangent g (mapPointKernel f p)
  obtain ⟨q, hq⟩ := normalSubgroup_conjugate_sections hn c p.toMul.val
  have h : pointMap f Q q = v.toMul.val := hq
  let q' : Lie K H := ⟨q, by
    change mapTest (dualReduction K) q = 1
    apply pointMap_injective f hf B
    rw [pointMap_mapTest, h, map_one]
    exact v.toMul.property⟩
  exact ⟨q', Subtype.ext h⟩

private theorem root_summand_mem [Infinite K] [Fintype D.I] (M : Marking D G.val)
    [IsAffine (extendGroup K G.val).X.left]
    (hT : IsSplitTorus (fibreTorus (K := K) M).group)
    (t : Lie K (fibreTorus (K := K) M).group) (c : D.I → K) (i : D.I) :
    ∀ S : Submodule K (Lie K (extendGroup K G.val)),
      (∀ (g : TorusValues D (basicTest K)) v, v ∈ S → torusOperator M g v ∈ S) →
      (∀ g, let v := mapPointKernel (fibreTorus (K := K) M).inclusion t +
          ∑ a, c a • rootTangent M a 1
        torusOperator M g v - v ∈ S) →
      c i • rootTangent M i 1 ∈ S := by
  intro S hstable h
  refine summand_mem_of_fixed_add_sum hstable (torusOperator_root M) ?_
    (fun g => torusOperator_torus M hT g t) Finset.univ c i (Finset.mem_univ _) h ?_
  · intro a b hab
    exact separates_characters (K := K) D (fun eq => hab (D.datum.root.injective eq))
  · obtain ⟨g, hg⟩ := separates_characters (K := K) D (D.datum.ne_zero i)
    refine ⟨g, ?_⟩
    simpa only [show Multiplicative.ofAdd (0 : D.X) = 1 from rfl, map_one, Units.val_one] using hg

private theorem radical_trivial [Infinite K] [Fintype D.I]
    (M : Marking D G.val) (hprim : ∀ i : D.I, ∃ w : D.X, D.datum.coroot' i w = 1)
    (U : ClosedSubgroup (extendGroup K G.val))
    (hs : Smooth U.group.X.hom) (hc : ConnectedSpace U.group.X.left)
    (hn : Specs.IsNormalSubgroup U.inclusion)
    (hU : IsUnipotent (closedSubgroupAlgebraicGroup
      (G := Specs.Unipotent.baseChangedAlgebraicGroup K G) U)) : IsTrivialSubgroup U := by
  let H := Specs.Unipotent.baseChangedAlgebraicGroup K G
  let U' := closedSubgroupAlgebraicGroup (G := H) U
  let hT := fibreTorus_split (K := K) M
  let : IsAffine U.group.X.left := U'.property.1
  let : IsAffine (extendGroup K G.val).X.left := H.property.1
  let d := lieMap U.inclusion
  let S := LinearMap.range d
  have hS : (S : Set (Lie K (extendGroup K G.val))) = Set.range (mapPointKernel U.inclusion) := rfl
  have hstable g (z : Lie K (extendGroup K G.val)) (hz : z ∈ S) :
      torusOperator M g z ∈ S := by
    have hz' : z ∈ Set.range (mapPointKernel U.inclusion) := hS ▸ hz
    obtain ⟨p, rfl⟩ := hz'
    change torusOperator M g (mapPointKernel U.inclusion p) ∈
      (S : Set (Lie K (extendGroup K G.val)))
    rw [hS]
    exact normal_tangent_image_stable U.inclusion U.isClosedImmersion hn _ p
  apply trivial_of_zero_tangent (H := H) U hs hc
  intro p
  let v := mapPointKernel U.inclusion p
  have hv : v ∈ S := ⟨p, rfl⟩
  obtain ⟨t, c, he⟩ := tangent_decomposition M v
  have hz (i : D.I) : c i = 0 := by
    by_contra hi
    have hsum := root_summand_mem M hT t c i S hstable (fun g => by
      dsimp only
      rw [← he]
      exact S.sub_mem (hstable g v hv) hv)
    have hroot : rootTangent M i (1 : K) ∈ S := (S.smul_mem_iff hi).mp hsum
    obtain ⟨w, hw⟩ := hprim i
    have hmem : rootTangent M i (1 : K) ∈ Set.range (mapPointKernel U.inclusion) :=
      hS ▸ hroot
    exact root_tangent_excluded M U hU hn i w hw hmem
  have hp : mapPointKernel U.inclusion p = mapPointKernel (fibreTorus (K := K) M).inclusion t := by
    have hsum : (∑ i, c i • rootTangent M i (1 : K)) = 0 :=
      Finset.sum_eq_zero fun i _ => (by rw [hz i, zero_smul])
    rw [hsum, add_zero] at he
    exact he
  have hp' := congrArg (fun v : Lie K (extendGroup K G.val) => v.toMul.val) hp
  have h1 := (eq_one_of_unipotent_and_torus_point (H := H) U (fibreTorus (K := K) M)
    hU (fibreTorus_multiplicativeType M) (dualTest K) p.toMul.val t.toMul.val hp').1
  exact Subtype.ext h1

private theorem containing_torus_fixed (M : Marking D G.val)
    [IsAffine (extendGroup K G.val).X.left]
    (A : ClosedSubgroup (extendGroup K G.val)) (hA : IsSplitTorus A.group)
    (j : (fibreTorus (K := K) M).group ⟶ A.group)
    (hj : j ≫ A.inclusion = (fibreTorus (K := K) M).inclusion)
    (g : TorusValues D (basicTest K)) (v : Lie K A.group) :
    torusOperator M g (mapPointKernel A.inclusion v) = mapPointKernel A.inclusion v := by
  apply Subtype.ext
  let Q := dualTest K
  let B := basicTest K
  let a := fibreTorusPoint (k := k) D B g
  let b : GroupPoints A.group Q := mapTest (constants B) (pointMap j B a)
  let f := pointMap A.inclusion Q
  have hb : mapTest (constants B)
      (pointMap (fibreTorus (K := K) M).inclusion B a) = f b := by
    rw [pointMap_mapTest]
    congr 1
    change a ≫ (fibreTorus (K := K) M).inclusion.hom.hom =
      (a ≫ j.hom.hom) ≫ A.inclusion.hom.hom
    rw [Category.assoc, ← hj]
    rfl
  let g' := mapTest (constants B) (pointMap (fibreTorus (K := K) M).inclusion B a)
  change g' * f v.toMul.val * (g')⁻¹ = f v.toMul.val
  have hcomm : b * v.toMul.val * b⁻¹ = v.toMul.val := by
    rw [(split_torus_sections_commute hA b v.toMul.val).eq, mul_inv_cancel_right]
  rw [show g' = f b from hb]
  simpa only [map_mul, map_inv] using congrArg f hcomm

private theorem fibreTorus_maximal [IsAlgClosed K] [Fintype D.I] (M : Marking D G.val) :
    IsMaximalTorus (fibreTorus (K := K) M) := by
  let H := Specs.Unipotent.baseChangedAlgebraicGroup K G
  let : IsAffine (extendGroup K G.val).X.left := H.property.1
  let T := fibreTorus (K := K) M
  let hT := fibreTorus_split (K := K) M
  refine ⟨isTorus_of_split hT, ?_⟩
  intro A hA hTA
  have hA' := torus_has_split_coordinates (G := H) A hA
  have hlie : Set.range (mapPointKernel A.inclusion) ⊆ Set.range (mapPointKernel T.inclusion) := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨j, hj⟩ := hTA
    let v' := mapPointKernel A.inclusion v
    obtain ⟨t, c, he⟩ := tangent_decomposition M v'
    have hz (i : D.I) : c i • rootTangent M i (1 : K) = 0 := by
      apply (Submodule.mem_bot K).mp
      apply root_summand_mem M hT t c i ⊥
      · intro g z hz
        rw [(Submodule.mem_bot K).mp hz, map_zero]
        exact Submodule.zero_mem _
      · intro g
        dsimp only
        rw [← he]
        change torusOperator M g (mapPointKernel A.inclusion v) -
          mapPointKernel A.inclusion v ∈ (⊥ : Submodule K (Lie K (extendGroup K G.val)))
        rw [containing_torus_fixed M A hA' j hj g v, sub_self]
        exact Submodule.zero_mem _
    have hsum : (∑ i, c i • rootTangent M i (1 : K)) = 0 :=
      Finset.sum_eq_zero fun i _ => hz i
    rw [hsum, add_zero] at he
    exact ⟨t, he.symm⟩
  exact subgroupOf_of_lieImage (A := H) hTA (splitTorusSmooth hT) (splitTorus_connected hT)
    (splitTorusSmooth hA') (splitTorus_connected hA') hlie

end GeometricConclusions

/-- Reductivity and maximality of the marked split torus in every field fibre. -/
theorem fibreReductivity : Statement.{u} := by
  intro k _ D _ hspan G hs hc M
  classical
  let := D.finiteRoots
  let := Fintype.ofFinite D.I
  let K := AlgebraicClosure k
  let U := GeometricRadicals.geometricUnipotentRadical G
  have hU := GeometricRadicals.geometricUnipotentRadicalLargest G
  exact ⟨⟨hs, hc, radical_trivial (K := K) M (primitiveCoroots D hspan) U
    hU.1.1 hU.1.2.1 hU.1.2.2 hU.2.1⟩,
    ⟨baseChangeClosedSubgroup k K M.torus M.torusClosed, fibreTorus_maximal (K := K) M⟩⟩

end

end LinearAlgebraicGroups.IntegralFibreReductivity
