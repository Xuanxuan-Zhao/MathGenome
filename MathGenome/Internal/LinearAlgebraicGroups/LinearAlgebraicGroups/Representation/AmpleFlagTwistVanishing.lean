import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.AmpleFlagTwistVanishing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AssociatedFlagLineSheaves
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe u

noncomputable section

namespace LinearAlgebraicGroups.AmpleFlagTwistVanishing

open LinearAlgebraicGroups.Specs
open Specs.CharacterDescent (Character)
open Specs.FlagCohomology (FlagKernelPair flagCohomology flagLineSheaf)
open Specs.FlagLineBundle (BorelProjection OppositeBorelPair AssociatedBundle)
open Specs.QuotientEmbedding (Presentation)

section Monomials

open ProjectiveFiniteness
open private monomialComplex extendMonomialCochain extendMonomialCochain_support
  deletionDifferential_extend_of_cycle monomialCochainOfFamily monomialComponentAt
  tupleFinset card_tupleFinset extendMonomialCochain_tuple extendMonomialCochain_ofFamily
  monomialComplex_d_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness

variable {k Index : Type u} [Field k] [LinearOrder Index] [Fintype Index] [Nonempty Index]

/-- In nonnegative total degree, every exponent vector in the projective
Čech complex has a coordinate that can be inserted as a contracting pivot. -/
private theorem exists_nonnegative_exponent {d : ℤ} (hd : 0 ≤ d) (a : Exponents Index d) :
    ∃ p, p ∉ negativeSupport a := by
  classical
  by_contra! h
  have ha : ∀ p : Index, a.val p < 0 := fun p => (Finset.mem_filter.mp (h p)).2
  have hsum : (∑ p : Index, a.val p) < 0 :=
    Finset.sum_neg (fun p _ => ha p) Finset.univ_nonempty
  rw [a.property] at hsum
  exact (not_lt_of_ge hd) hsum

/-- The ordered Čech complex of a nonnegative hyperplane twist has zero
homology in every positive degree. -/
private theorem isZero_monomial_homology (d : ℤ) (hd : 0 ≤ d) (n : ℕ) :
    IsZero ((monomialComplex (k := k) («ι» := Index) d).homology (n + 1)) := by
  classical
  let C := monomialComplex (k := k) («ι» := Index) d
  apply ExactAt.isZero_homology
  apply (C.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp [CochainComplex.next])).mpr
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro z hz
  obtain ⟨w, hw, hprimitive, _⟩ :=
    exists_primitive_off_exceptional_exponents negativeSupport (fun _ => False)
      (fun a _ => exists_nonnegative_exponent hd a) (extendMonomialCochain z) (n + 1)
      (extendMonomialCochain_support z) (deletionDifferential_extend_of_cycle z hz)
  let v := monomialCochainOfFamily (n := n) w (fun s a _ h => hw s a (Or.inr h))
  refine ⟨v, ?_⟩
  change C.d n (n + 1) v = z
  funext e
  apply Subtype.ext
  apply Finsupp.ext
  intro a
  change (monomialComponentAt (C.d n (n + 1) v) e).val a = (monomialComponentAt z e).val a
  rw [monomialComplex_d_apply, ← extendMonomialCochain_tuple z e,
    ← hprimitive (tupleFinset e) a (not_false)]
  apply Finset.sum_congr rfl
  intro j hj
  have hs : ((tupleFinset e).erase j).card = n + 1 := by
    rw [Finset.card_erase_of_mem hj, card_tupleFinset]
    omega
  change _ * extendMonomialCochain v _ a = _ * w ((tupleFinset e).erase j) a
  rw [extendMonomialCochain_ofFamily w _ hs]

variable [DecidableEq Index]

open Specs.ProjectiveTwistChartModules (ChartGeometry)
open private projectiveTwists chartCech cechIso_of_chartIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness

private theorem isZero_chartTwist_homology
    [IsLocallyNoetherian (Specs.ProjectiveSpaces.coordinateProjectiveSpace k Index).left]
    (G : ChartGeometry k Index) (d : ℤ) (hd : 0 ≤ d) (n : ℕ) :
    IsZero ((chartCech ((projectiveTwists G).diagram d)).homology (n + 1)) := by
  let T := ProjectiveTwistChartModules.twistDiagram G d
  let e : chartCech ((projectiveTwists G).diagram d) ≅ monomialComplex (k := k) ( «ι» := Index) d :=
    cechIso_of_chartIso (ProjectiveTwistChartModules.groundDiagramIso G d T) ≪≫
      (ProjectiveTwistChartModules.orderedLaurentComparison (k := k) ( «ι» := Index) d).iso
  exact (isZero_monomial_homology d hd n).of_iso
    ((homologyFunctor (ModuleCat.{u} k) (.up ℕ) (n + 1)).mapIso e)

end Monomials

section DimensionShifting

variable {k : Type u} [Field k]

/-- A family with a uniform upper cohomological bound has eventual vanishing
in positive degrees if its presentation terms do, with the presentation
kernels again belonging to the family of coefficients. -/
private theorem eventually_isZero_of_resolution
    {A : Type*} (C : A → ℕ → CochainComplex (ModuleCat.{u} k) ℕ) (bound : ℕ)
    (cutoff : ∀ a t n, bound ≤ n → IsZero ((C a t).homology n))
    (resolve : ∀ a, ∃ (b : A) (T : ℕ → CochainComplex (ModuleCat.{u} k) ℕ) (N : ℕ), ∀ t, N ≤ t →
      ∃ S : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ),
        S.ShortExact ∧ Nonempty (S.X₁ ≅ C b t) ∧
          Nonempty (S.X₂ ≅ T t) ∧ Nonempty (S.X₃ ≅ C a t) ∧
          ∀ n, 0 < n → IsZero ((T t).homology n))
    (a : A) :
    ∃ N : ℕ, ∀ t, N ≤ t → ∀ n, 0 < n → IsZero ((C a t).homology n) := by
  suffices step : ∀ depth a, ∃ N : ℕ, ∀ t, N ≤ t →
      ∀ n, 0 < n → bound ≤ n + depth → IsZero ((C a t).homology n) by
    obtain ⟨N, h⟩ := step bound a
    exact ⟨N, fun t ht n hn => h t ht n hn (by omega)⟩
  intro depth
  induction depth with
  | zero =>
    intro a
    exact ⟨0, fun t _ n _ h => cutoff a t n (by omega)⟩
  | succ depth ih =>
    intro a
    obtain ⟨b, T, N, hN⟩ := resolve a
    obtain ⟨M, hM⟩ := ih b
    refine ⟨max N M, fun t ht n hn hbound => ?_⟩
    obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩, hT⟩ := hN t ((le_max_left _ _).trans ht)
    let H (degree : ℕ) := homologyFunctor (ModuleCat.{u} k) (.up ℕ) degree
    have h₁ : IsZero (S.X₁.homology (n + 1)) :=
      (hM t ((le_max_right _ _).trans ht) (n + 1) (by omega) (by omega)).of_iso
        ((H (n + 1)).mapIso e₁)
    have h₂ : IsZero (S.X₂.homology n) := (hT n hn).of_iso ((H n).mapIso e₂)
    exact ((hS.homology_exact₃ n (n + 1) rfl).isZero_of_both_isZero h₂ h₁).of_iso
      ((H n).mapIso e₃).symm

end DimensionShifting

section ChartShift

open Specs.ProjectiveFiniteChartPresentations (Chart ChartRings Twists product)
open Specs.ProjectiveFiniteChartPresentations renaming kernel → chartKernel
open Specs.ProjectiveFiniteChartPresentations.ChartRings (ratioUnit)
open scoped ModuleCat.Algebra

variable {k Index : Type u} [Field k] [DecidableEq Index]
variable (D : ChartRings k Index)

private noncomputable def chartIndex (S : Chart Index) : Index :=
  S.nonempty.choose

omit [DecidableEq Index] in
private theorem chartIndex_mem (S : Chart Index) : chartIndex S ∈ S.indices :=
  S.nonempty.choose_spec

private def chartFactor {S T : Chart Index} (f : S ⟶ T) :
    (D.rings.obj T)ˣ :=
  D.ratioUnit T (Chart.subset f (chartIndex_mem S)) (chartIndex_mem T)

private theorem chartFactor_id (S : Chart Index) : chartFactor D (𝟙 S) = 1 :=
  Units.ext (D.ratio_self S (chartIndex S) (chartIndex_mem S))

private theorem chartFactor_comp {S T V : Chart Index} (f : S ⟶ T) (g : T ⟶ V) :
    chartFactor D (f ≫ g) =
      Units.map (D.rings.map g).hom.toMonoidHom (chartFactor D f) * chartFactor D g := by
  apply Units.ext
  change D.ratio V (chartIndex S) (chartIndex V) _ =
    D.rings.map g (D.ratio T (chartIndex S) (chartIndex T) _) *
      D.ratio V (chartIndex T) (chartIndex V) _
  rw [D.ratio_map, D.ratio_mul]

private theorem chartFactor_zpow_comp (d : ℤ) {S T V : Chart Index}
    (f : S ⟶ T) (g : T ⟶ V) :
    (↑(chartFactor D (f ≫ g) ^ d) : D.rings.obj V) =
      D.rings.map g (↑(chartFactor D f ^ d) : D.rings.obj T) *
        (↑(chartFactor D g ^ d) : D.rings.obj V) := by
  rw [chartFactor_comp, mul_zpow, ← map_zpow]
  rfl

private abbrev chartRestrict {M : D.Modules} {S T : Chart Index}
    (f : S ⟶ T) (x : M.obj S) : M.obj T := M.map f x

private theorem chartRestrict_smul {M : D.Modules} {S T : Chart Index}
    (f : S ⟶ T) (r : D.rings.obj S) (x : M.obj S) :
    chartRestrict D f (r • x) = (D.rings.map f r : D.rings.obj T) • chartRestrict D f x :=
  M.map_smul f r x

set_option backward.isDefEq.respectTransparency false in
/-- The chart diagram after tensoring by the coordinate twist. The module on
each chart is written in the frame at its chosen inverted coordinate. -/
private def shiftDiagram (M : D.Modules) (d : ℤ) : D.Modules where
  obj := M.obj
  map {S T} f := ModuleCat.ofHom (X := M.obj S)
    (Y := (ModuleCat.restrictScalars (D.rings.map f).hom).obj (M.obj T))
    { toFun := fun x => (↑(chartFactor D f ^ d) : D.rings.obj T) • chartRestrict D f x
      map_add' x y := by
        change (↑(chartFactor D f ^ d) : D.rings.obj T) • chartRestrict D f (x + y) =
          (↑(chartFactor D f ^ d) : D.rings.obj T) • chartRestrict D f x +
          (↑(chartFactor D f ^ d) : D.rings.obj T) • chartRestrict D f y
        rw [show chartRestrict D f (x + y) = chartRestrict D f x + chartRestrict D f y
          from map_add (M.map f).hom x y, smul_add]
      map_smul' r x := by
        change (↑(chartFactor D f ^ d) : D.rings.obj T) • chartRestrict D f (r • x) =
          (D.rings.map f r : D.rings.obj T) •
            ((↑(chartFactor D f ^ d) : D.rings.obj T) • chartRestrict D f x)
        rw [chartRestrict_smul, smul_comm] }
  map_id S := by
    apply ModuleCat.hom_ext
    ext x : 1
    change (↑(chartFactor D (𝟙 S) ^ d) : D.rings.obj S) • chartRestrict D (𝟙 S) x = x
    rw [chartFactor_id, one_zpow, Units.val_one, one_smul]
    change M.map (𝟙 S) x = x
    rw [PresheafOfModules.map_id]
    rfl
  map_comp {S T V} f g := by
    apply ModuleCat.hom_ext
    ext x : 1
    change (↑(chartFactor D (f ≫ g) ^ d) : D.rings.obj V) • chartRestrict D (f ≫ g) x =
      (↑(chartFactor D g ^ d) : D.rings.obj V) •
        chartRestrict D g ((↑(chartFactor D f ^ d) : D.rings.obj T) • chartRestrict D f x)
    rw [show chartRestrict D (f ≫ g) x = chartRestrict D g (chartRestrict D f x)
      from M.map_comp_apply f g x, chartRestrict_smul, chartFactor_zpow_comp, mul_smul, smul_comm]

set_option backward.isDefEq.respectTransparency false in
private def shiftMap {M N : D.Modules} (f : M ⟶ N) (d : ℤ) :
    shiftDiagram D M d ⟶ shiftDiagram D N d where
  app := f.app
  naturality {S T} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let x' : M.obj S := x
    let c : D.rings.obj T := ↑(chartFactor D g ^ d)
    have h₁ := (f.app T).hom.map_smul c (chartRestrict D g x')
    have h₂ := congrArg (fun y : N.obj T => c • y)
      (PresheafOfModules.naturality_apply f g x')
    exact h₁.trans h₂

set_option backward.isDefEq.respectTransparency false in
private theorem twist_coord_map (L : Twists D) (d : ℤ) {S T : Chart Index}
    (f : S ⟶ T) (x : (L.diagram d).obj S) :
    (L.basis d T (chartIndex T) (chartIndex_mem T)).symm ((L.diagram d).map f x) =
      (↑(chartFactor D f ^ d) : D.rings.obj T) *
        D.rings.map f ((L.basis d S (chartIndex S) (chartIndex_mem S)).symm x) := by
  let bS := L.basis d S (chartIndex S) (chartIndex_mem S)
  let bT := L.basis d T (chartIndex T) (chartIndex_mem T)
  have hx : x = bS.symm x • bS 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.apply_symm_apply]
  conv_lhs => rw [hx]
  change bT.symm ((L.diagram d).map f (bS.symm x • bS 1)) = _
  change bT.symm (chartRestrict D f (bS.symm x • bS 1)) = _
  rw [chartRestrict_smul, map_smul]
  change _ * bT.symm ((L.diagram d).map f (L.basis d S (chartIndex S) (chartIndex_mem S) 1)) = _
  rw [L.basis_map, L.basis_transition d T
    (chartIndex S) (chartIndex T) (Chart.subset f (chartIndex_mem S)) (chartIndex_mem T),
    map_smul, LinearEquiv.symm_apply_apply]
  simp [bS, smul_eq_mul, chartFactor, mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- Choosing the same coordinate frames identifies the shifted finite product
of twists with the product whose degrees are increased by the shift. -/
private def shiftProductTwistIso (L : Twists D) {J : Type} (a : J → ℤ) (t : ℤ) :
    shiftDiagram D (product (fun j => L.diagram (a j))) t ≅
      product (fun j => L.diagram (a j + t)) := by
  let e (S : Chart Index) (j : J) :=
    (L.basis (a j) S (chartIndex S) (chartIndex_mem S)).symm.trans
      (L.basis (a j + t) S (chartIndex S) (chartIndex_mem S))
  refine PresheafOfModules.isoMk (fun S => (LinearEquiv.piCongrRight (e S)).toModuleIso) ?_
  intro S T f
  apply ModuleCat.hom_ext
  ext x : 1
  funext j
  apply (L.basis (a j + t) T (chartIndex T) (chartIndex_mem T)).symm.injective
  change (L.basis (a j + t) T (chartIndex T) (chartIndex_mem T)).symm
    (e T j ((↑(chartFactor D f ^ t) : D.rings.obj T) • chartRestrict D (M := L.diagram (a j)) f (x j))) =
    (L.basis (a j + t) T (chartIndex T) (chartIndex_mem T)).symm
      ((L.diagram (a j + t)).map f (e S j (x j)))
  simp only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_smul]
  rw [twist_coord_map D L (a j), twist_coord_map D L (a j + t),
    LinearEquiv.symm_apply_apply, zpow_add, Units.val_mul]
  simp only [smul_eq_mul]
  ac_rfl

set_option backward.isDefEq.respectTransparency false in
private def shiftKernelIso {M N : D.Modules}
    (q : M ⟶ N) (t : ℤ) : chartKernel (shiftMap D q t) ≅ shiftDiagram D (chartKernel q) t := by
  refine PresheafOfModules.isoMk (fun _ => Iso.refl _) ?_
  intro S T f
  apply ModuleCat.hom_ext
  ext x : 1
  apply Subtype.ext
  rfl

end ChartShift

section ChartVanishing

open Specs.ProjectiveFiniteChartPresentations (Chart ChartRings Twists product)
open Specs.ProjectiveFiniteChartPresentations renaming kernel → chartKernel
open Specs.ProjectiveTwistChartModules (ChartGeometry groundDiagram)
open private projectiveChartRings projectiveTwists chartCech groundKernelSequence groundChartMap
  shortExact_groundKernelSequence cechFunctor extendChartMap chartCechProductIso
  isZero_orderedCech_homology_of_card_le singletonCoordinates chartExtension
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness

variable {k Index : Type u} [Field k] [LinearOrder Index] [Fintype Index] [Nonempty Index]
variable [DecidableEq Index]
variable [IsLocallyNoetherian (Specs.ProjectiveSpaces.coordinateProjectiveSpace k Index).left]

private def groundChartIso (G : ChartGeometry k Index)
    {M N : (projectiveChartRings G).Modules} (e : M ≅ N) :
    groundDiagram M ≅ groundDiagram N where
  hom := groundChartMap e.hom
  inv := groundChartMap e.inv
  hom_inv_id := by
    ext S : 2
    apply ModuleCat.hom_ext
    ext x : 1
    exact ConcreteCategory.congr_hom (congrArg (fun f : M ⟶ M => f.app S) e.hom_inv_id) x
  inv_hom_id := by
    ext S : 2
    apply ModuleCat.hom_ext
    ext x : 1
    exact ConcreteCategory.congr_hom (congrArg (fun f : N ⟶ N => f.app S) e.inv_hom_id) x

private def chartCechIso (G : ChartGeometry k Index)
    {M N : (projectiveChartRings G).Modules} (e : M ≅ N) :
    chartCech M ≅ chartCech N := by
  let a := groundChartIso G e
  let b : chartExtension (groundDiagram M) ≅ chartExtension (groundDiagram N) :=
    { hom := extendChartMap a.hom
      inv := extendChartMap a.inv
      hom_inv_id := by
        ext S : 2
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        funext hx
        exact ConcreteCategory.congr_hom (congrArg (fun f => f.app _) a.hom_inv_id) (x hx)
      inv_hom_id := by
        ext S : 2
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        funext hx
        exact ConcreteCategory.congr_hom (congrArg (fun f => f.app _) a.inv_hom_id) (x hx) }
  exact (cechFunctor singletonCoordinates).mapIso b

private theorem isZero_homology_product {J : Type} [Finite J] (C : J → CochainComplex (ModuleCat.{u} k) ℕ)
    (n : ℕ) (h : ∀ j, IsZero ((C j).homology n)) :
    IsZero ((∏ᶜ C).homology n) := by
  classical
  let _ := Fintype.ofFinite J
  let e := PreservesProduct.iso (homologyFunctor (ModuleCat.{u} k) (.up ℕ) n) C ≪≫
    ModuleCat.piIsoPi (fun j => (C j).homology n)
  have (j : J) : Subsingleton ((C j).homology n) := ModuleCat.isZero_iff_subsingleton.mp (h j)
  exact (ModuleCat.isZero_of_subsingleton _).of_iso e

set_option backward.isDefEq.respectTransparency false in
private theorem eventually_isZero_chartCech (G : ChartGeometry k Index)
    (M : (projectiveChartRings G).Modules)
    (hM : (projectiveChartRings G).FiniteOnSingletons M)
    (hLoc : (projectiveChartRings G).Localizes M) :
    ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      ∀ n, 0 < n → IsZero ((chartCech (shiftDiagram (projectiveChartRings G) M t)).homology n) := by
  let D := projectiveChartRings G
  let L := projectiveTwists G
  let A := {M : D.Modules // D.FiniteOnSingletons M ∧ D.Localizes M}
  let C (a : A) (t : ℕ) := chartCech (shiftDiagram D a.val t)
  have cutoff (a : A) (t n : ℕ) (hn : Fintype.card Index ≤ n) : IsZero ((C a t).homology n) :=
    isZero_orderedCech_homology_of_card_le singletonCoordinates
      (chartExtension (groundDiagram (shiftDiagram D a.val t))) n hn
  refine eventually_isZero_of_resolution C (Fintype.card Index) cutoff ?_ ⟨M, hM, hLoc⟩
  intro a
  obtain ⟨m, d, q, hq, _, _, hker, hLocKer⟩ :=
    ProjectiveFiniteChartPresentations.finiteChartPresentations k Index D L a.val a.prop.1 a.prop.2
  let N : ℕ := ∑ j, (-(d j)).toNat
  let P (t : ℕ) := fun j : Fin m => L.diagram (d j + t)
  refine ⟨⟨chartKernel q, hker, hLocKer⟩, fun t => ∏ᶜ (fun j => chartCech (P t j)), N, ?_⟩
  intro t ht
  let q' := shiftMap D q (t : ℤ)
  let S := (groundKernelSequence q').map (cechFunctor singletonCoordinates)
  have e₁ : S.X₁ ≅ chartCech (shiftDiagram D (chartKernel q) t) :=
    chartCechIso G (shiftKernelIso D q t)
  have e₂ : S.X₂ ≅ chartCech (product (P t)) :=
    chartCechIso G (shiftProductTwistIso D L d t)
  refine ⟨S, shortExact_groundKernelSequence q' hq, ⟨e₁⟩,
    ⟨e₂ ≪≫ chartCechProductIso (P t)⟩, ⟨Iso.refl _⟩, ?_⟩
  intro n hn
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  apply isZero_homology_product
  intro j
  have hj : (-(d j)).toNat ≤ N :=
    Finset.single_le_sum (f := fun i => (-(d i)).toNat)
      (fun i (_ : i ∈ Finset.univ) => Nat.zero_le _) (Finset.mem_univ j)
  have hdegree : 0 ≤ d j + (t : ℤ) := by omega
  exact isZero_chartTwist_homology G _ hdegree n

end ChartVanishing

section ProjectiveVanishing

/-- Combining the finitely many residual powers of an ample line. -/
private theorem eventually_of_residues (P : ℕ → Prop) (m : ℕ) (hm : 0 < m)
    (h : ∀ a : Fin m, ∃ N : ℕ, ∀ t ≥ N, P (a.val + m * t)) :
    ∃ N : ℕ, ∀ n ≥ N, P n := by
  classical
  choose bounds hbounds using h
  let N := ∑ a, bounds a
  refine ⟨m * N, fun n hn => ?_⟩
  let a : Fin m := ⟨n % m, Nat.mod_lt _ hm⟩
  have ha : bounds a ≤ N :=
    Finset.single_le_sum (f := bounds) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  have hn' : N ≤ n / m := (Nat.le_div_iff_mul_le hm).mpr (by simpa [Nat.mul_comm] using hn)
  have he : a.val + m * (n / m) = n := Nat.mod_add_div n m
  simpa only [he] using hbounds a (n / m) (ha.trans hn')

end ProjectiveVanishing

section HyperplaneFrames

open Specs.AmpleFlagWeights (changeVector)
open Specs.AssociatedFlagLineSheaves (IsCovariantOn characterFunction evalOn lineCoordinate)
open Specs.FlagLineBundle (affineLine linePoint)
open Specs.ProjectiveSpaces (LineRepresentation projectiveSpace chartRing coordinateRatio)
open private exists_of_affineTests extendVector_coord projectiveBasis chartPoint chartLine_span
  affinePointEquiv affinePointEquiv_chartPoint chartVector chartVector_coord ratio_self
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.ProjectiveSpaces
open private linePoint_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagLineBundle
open private lineCoordinate_comp lineCoordinate_linePoint regularFunction_ext evalOn_restrict
  pullCharacterFunction characterFunction_point
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AssociatedFlagLineSheaves
open scoped TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

/-- Changing the natural representation of the line functor amounts to a
projective scheme automorphism. -/
private theorem projectiveIso_of_lineRepresentations [Module.Finite k V]
    (ρ τ : LineRepresentation k V) :
    ∃ e : projectiveSpace k V ≅ projectiveSpace k V,
      ∀ (S : SchemeOver k) (f : S ⟶ projectiveSpace k V), τ.points S (f ≫ e.hom) = ρ.points S f := by
  let T := projectiveSpace k V
  let f : T ⟶ T := (τ.points T).symm (ρ.points T (𝟙 T))
  let g : T ⟶ T := (ρ.points T).symm (τ.points T (𝟙 T))
  have hf {S : SchemeOver k} (q : S ⟶ T) : τ.points S (q ≫ f) = ρ.points S q := by
    have he : τ.points T f = ρ.points T (𝟙 T) := Equiv.apply_symm_apply _ _
    rw [τ.naturality, he, ← ρ.naturality, Category.comp_id]
  have hg {S : SchemeOver k} (q : S ⟶ T) : ρ.points S (q ≫ g) = τ.points S q := by
    have he : ρ.points T g = τ.points T (𝟙 T) := Equiv.apply_symm_apply _ _
    rw [ρ.naturality, he, ← τ.naturality, Category.comp_id]
  refine ⟨⟨f, g, ?_, ?_⟩, fun S q => hf q⟩
  · exact (ρ.points T).injective ((hg f).trans (Equiv.apply_symm_apply _ _))
  · exact (τ.points T).injective ((hf g).trans (Equiv.apply_symm_apply _ _))

/-- Each coordinate of a frame natural on affine test algebras is a
regular function on the original scheme. -/
private theorem exists_frame_coordinate {X : SchemeOver k} {I : Type u}
    (B : Module.Basis I k V) (i : I)
    (frame : ∀ R : TestAlgebra k, Points X R → R ⊗[k] V)
    (natural : ∀ {R S : TestAlgebra k} (a : R ⟶ S) (x : Points X R),
      frame S (mapPoints a x) = changeVector a (frame R x)) :
    ∃ c : Γ(X.left, ⊤), ∀ (R : TestAlgebra k) (x : Points X R),
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom (x.left.appTop c) =
        (B.baseChange R).coord i (frame R x) := by
  let m (R : TestAlgebra k) (x : Points X R) : Points (affineLine k) R :=
    linePoint R ((B.baseChange R).coord i (frame R x))
  have hm {R S : TestAlgebra k} (a : R ⟶ S) (x : Points X R) :
      m S (mapPoints a x) = mapPoints a (m R x) := by
    dsimp only [m]
    rw [natural a x, show (B.baseChange S).coord i (changeVector a (frame R x)) =
      a.hom ((B.baseChange R).coord i (frame R x)) from extendVector_coord B i a (frame R x)]
    exact (linePoint_comp a.hom _).symm
  obtain ⟨f, hf⟩ := exists_of_affineTests m hm
  refine ⟨lineCoordinate f, fun R x => ?_⟩
  rw [← lineCoordinate_comp, hf, lineCoordinate_linePoint]

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}

/-- A coordinate of the frame has the inverse-character covariance on
every quotient open. -/
private theorem isCovariantOn_frame_coordinate {I : Type u}
    (B : Module.Basis I k V) (i : I) (Q : Presentation P.negative)
    (p : BorelProjection P) (ampleWeight : Character P.torus.group)
    (frame : ∀ R : TestAlgebra k, Points G.val.X R → R ⊗[k] V)
    (transition : ∀ (R : TestAlgebra k) (g : Points G.val.X R) (b : Points P.negative.group.X R),
      frame R (g * (b ≫ P.negative.inclusion.hom.hom)) =
        Specs.CharacterPairing.characterValue (p.projection ≫ ampleWeight) R (b⁻¹) • frame R g)
    (c : Γ(G.val.X.left, ⊤))
    (hc : ∀ (R : TestAlgebra k) (x : Points G.val.X R),
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom (x.left.appTop c) =
        (B.baseChange R).coord i (frame R x)) (U : Q.scheme.left.Opens) :
    IsCovariantOn Q p ampleWeight U (G.val.X.left.presheaf.map
      (homOfLE (show Q.projection.left ⁻¹ᵁ U ≤ ⊤ from le_top)).op c) := by
  intro T g b h h'
  rw [evalOn_restrict, evalOn_restrict]
  apply regularFunction_ext
  intro R x
  let e := Scheme.ΓSpecIso (CommRingCat.of R)
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  have mulEval (y z : Γ(T.left, ⊤)) :
      e.hom (x.left.appTop (y * z)) = e.hom (x.left.appTop y) * e.hom (x.left.appTop z) :=
    map_mul (x.left.appTop ≫ e.hom).hom y z
  have eval (g' : T ⟶ G.val.X) :
      e.hom (x.left.appTop (g'.left.appTop c)) = (B.baseChange R).coord i (frame R (x ≫ g')) := by
    change e.hom ((g'.left.appTop ≫ x.left.appTop) c) = _
    rw [← Scheme.Hom.comp_appTop]
    exact hc R (x ≫ g')
  rw [mulEval, eval, eval, pullCharacterFunction, GrpObj.comp_inv, characterFunction_point,
    MonObj.comp_mul, ← Category.assoc x b P.negative.inclusion.hom.hom]
  rw [transition, map_smul, smul_eq_mul]
  rfl

variable [Module.Finite k V]

/-- A generator of the tautological line has an invertible pivot coordinate
on the corresponding affine projective chart. All its other coordinates
are that pivot times the normalized coordinates on the chart. -/
private theorem frameCoordinates_of_chartPoint (Q : Presentation P.negative)
    (j : Q.scheme ⟶ projectiveSpace k V) {R : TestAlgebra k} (g : Points G.val.X R)
    (i : ULift.{u} (Fin (Module.finrank k V)))
    (a : chartRing k _ i →ₐ[k] R) (ha : (g ≫ Q.projection) ≫ j = chartPoint i a)
    (v : R ⊗[k] V)
    (hv : (((LinearAlgebraicGroups.ProjectiveSpaces.lineRepresentation k V).points _ j).line
        R (g ≫ Q.projection)).submodule = Submodule.span R {v}) :
    let B := (projectiveBasis k V).baseChange R
    IsUnit (B.coord i v) ∧ ∀ l, B.coord l v = a (coordinateRatio k _ i l) * B.coord i v := by
  dsimp only
  let B := projectiveBasis k V
  let w := chartVector B i a
  have hspan : Submodule.span R {v} = Submodule.span R {w} := by
    rw [← hv]
    let ρ := LinearAlgebraicGroups.ProjectiveSpaces.lineRepresentation k V
    have he := congrArg (fun L => (L.line R (𝟙 _)).submodule) (ρ.naturality (g ≫ Q.projection) j)
    change ((ρ.points _ ((g ≫ Q.projection) ≫ j)).line R (𝟙 _)).submodule =
      ((ρ.points _ j).line R (𝟙 _ ≫ (g ≫ Q.projection))).submodule at he
    rw [Category.id_comp, ha] at he
    rw [← he]
    change (affinePointEquiv B R (𝟙 _ ≫ chartPoint i a)).submodule = _
    rw [Category.id_comp, affinePointEquiv_chartPoint]
    exact chartLine_span B i a
  have hwi : (B.baseChange R).coord i w = 1 := by
    rw [show (B.baseChange R).coord i w = a (coordinateRatio k _ i i)
      from chartVector_coord B i i a, ratio_self, map_one]
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp
    (hspan ▸ Submodule.mem_span_singleton_self (R := R) v)
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp
    (hspan.symm ▸ Submodule.mem_span_singleton_self (R := R) w)
  have hri : (B.baseChange R).coord i v = r := by
    rw [← hr, map_smul, hwi, smul_eq_mul, mul_one]
  have hsr : s * r = 1 := by
    rw [← hri, ← smul_eq_mul, ← map_smul, hs, hwi]
  constructor
  · rw [hri]
    exact ⟨⟨r, s, (mul_comm r s).trans hsr, hsr⟩, rfl⟩
  · intro l
    rw [hri, ← hr, map_smul, show (B.baseChange R).coord l w = a (coordinateRatio k _ i l)
      from chartVector_coord B i l a, smul_eq_mul, mul_comm]

end HyperplaneFrames

section LocalTwists

open Specs.AssociatedFlagLineSheaves (IsCovariantOn SectionRealization characterFunction evalOn)
open private characterFunction_projected_product characterFunction_isUnit functionsOver_smul
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AssociatedFlagLineSheaves

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {Q : Presentation P.negative} (p : BorelProjection P)

private theorem characterFunction_projected_pow (weight : Character P.torus.group)
    {T : SchemeOver k} (b : T ⟶ P.negative.group.X) (t : ℕ) :
    characterFunction (p.projection ≫ weight ^ t) b = characterFunction (p.projection ≫ weight) b ^ t := by
  induction t with
  | zero =>
    simp only [pow_zero]
    have he := characterFunction_projected_product p weight 1 b
    rw [mul_one] at he
    exact (characterFunction_isUnit (p.projection ≫ weight) b).mul_left_cancel
      (he.symm.trans (mul_one _).symm)
  | succ t ih => simp only [pow_succ, characterFunction_projected_product, ih]

set_option backward.isDefEq.respectTransparency false in
/-- An invertible regular covariant function on the torsor shifts the
character of local covariants by its weight. -/
private theorem isCovariantOn_mul_unit_pow_iff
    (weight baseWeight : Character P.torus.group) (U : Q.scheme.left.Opens)
    (c : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)ˣ)
    (hc : IsCovariantOn Q p weight U c) (t : ℕ)
    (z : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)) :
    IsCovariantOn Q p (baseWeight * weight ^ t) U ((↑c : Γ(G.val.X.left, _)) ^ t * z) ↔
      IsCovariantOn Q p baseWeight U z := by
  let V := Q.projection.left ⁻¹ᵁ U
  have test (T : SchemeOver k) (g : T ⟶ G.val.X) (b : T ⟶ P.negative.group.X)
      (h : (⊤ : T.left.Opens) ≤ g.left ⁻¹ᵁ V)
      (h' : (⊤ : T.left.Opens) ≤
        (g * (b ≫ P.negative.inclusion.hom.hom)).left ⁻¹ᵁ V) :
      let gb := g * (b ≫ P.negative.inclusion.hom.hom)
      evalOn gb.left V h' ((↑c : Γ(G.val.X.left, V)) ^ t * z) =
          characterFunction (p.projection ≫ (baseWeight * weight ^ t)) b⁻¹ *
            evalOn g.left V h ((↑c : Γ(G.val.X.left, V)) ^ t * z) ↔
        evalOn gb.left V h' z = characterFunction (p.projection ≫ baseWeight) b⁻¹ *
          evalOn g.left V h z := by
    dsimp only
    have he := hc T g b h h'
    let s := (g.left.appLE V ⊤ h).hom (c : Γ(G.val.X.left, V))
    let a := characterFunction (p.projection ≫ weight) b⁻¹
    let b₀ := characterFunction (p.projection ≫ baseWeight) b⁻¹
    have hu : IsUnit (a ^ t * s ^ t) :=
      ((characterFunction_isUnit (p.projection ≫ weight) b⁻¹).pow t).mul
        ((c.isUnit.map (g.left.appLE V ⊤ h).hom).pow t)
    unfold evalOn at he ⊢
    simp only [map_mul, map_pow, characterFunction_projected_product, characterFunction_projected_pow]
    change (g * (b ≫ P.negative.inclusion.hom.hom)).left.appLE V ⊤ h' (c : Γ(G.val.X.left, V)) =
      a * s at he
    rw [he, mul_pow]
    change (a ^ t * s ^ t) * _ = b₀ * a ^ t * (s ^ t * _) ↔ _ = b₀ * _
    rw [show ∀ x : Γ(T.left, ⊤), b₀ * a ^ t * (s ^ t * x) = (a ^ t * s ^ t) * (b₀ * x)
      by intro x; ac_rfl, IsUnit.mul_right_inj hu]
  exact ⟨fun h T g b h₀ h₁ => (test T g b h₀ h₁).mp (h T g b h₀ h₁),
    fun h T g b h₀ h₁ => (test T g b h₀ h₁).mpr (h T g b h₀ h₁)⟩

variable {a : ModObj G.val.X Q.scheme}

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by a power of a covariant unit identifies the local
section modules with the indicated shift of the character. -/
private theorem exists_twistSectionEquiv {weight baseWeight : Character P.torus.group}
    (t : ℕ) {L : AssociatedBundle Q a p baseWeight}
    {L' : AssociatedBundle Q a p (baseWeight * weight ^ t)}
    (M : SectionRealization L) (N : SectionRealization L') (U : Q.scheme.left.Opens)
    (c : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)ˣ) (hc : IsCovariantOn Q p weight U c) :
    ∃ e : Γ(M.sheaf, U) ≃ₗ[Γ(Q.scheme.left, U)] Γ(N.sheaf, U),
      ∀ x, N.functionVal U (e x) =
        (↑c : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)) ^ t * M.functionVal U x := by
  let u : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)ˣ := c ^ t
  have twist (x : Γ(M.sheaf, U)) :
      (u : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)) * M.functionVal U x ∈
        Set.range (N.functions.app U) := by
    apply (N.functions_range U _).mpr
    exact (isCovariantOn_mul_unit_pow_iff p weight baseWeight U c hc t _).mpr
      ((M.functions_range U _).mp ⟨x, rfl⟩)
  let f (x : Γ(M.sheaf, U)) := (twist x).choose
  have hf (x : Γ(M.sheaf, U)) : N.functionVal U (f x) =
      (u : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)) *
      M.functionVal U x := (twist x).choose_spec
  let F : Γ(M.sheaf, U) →ₗ[Γ(Q.scheme.left, U)] Γ(N.sheaf, U) :=
    { toFun := f
      map_add' := by
        intro x y
        apply N.functions_injective
        rw [map_add]
        change N.functionVal U (f (x + y)) = N.functionVal U (f x) + N.functionVal U (f y)
        rw [hf, hf, hf]
        simp only [SectionRealization.functionVal, map_add, mul_add]
      map_smul' := by
        intro r x
        apply N.functions_injective
        rw [Scheme.Modules.Hom.app_smul, functionsOver_smul]
        change N.functionVal U (f (r • x)) = Q.projection.left.app U r * N.functionVal U (f x)
        rw [hf, hf]
        simp only [SectionRealization.functionVal, Scheme.Modules.Hom.app_smul, functionsOver_smul]
        exact mul_left_comm _ _ _ }
  have inj : Function.Injective F := by
    intro x y he
    apply M.functions_injective
    apply u.isUnit.mul_left_cancel
    rw [← hf, ← hf]
    exact congrArg (N.functions.app U) he
  have surj : Function.Surjective F := by
    intro y
    let z : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U) := ↑u⁻¹ * N.functionVal U y
    have hz : (u : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)) * z = N.functionVal U y := by
      change (u : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)) *
        ((↑u⁻¹ : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)) * N.functionVal U y) = _
      rw [← mul_assoc, Units.mul_inv, one_mul]
    have hcov : IsCovariantOn Q p baseWeight U z := by
      apply (isCovariantOn_mul_unit_pow_iff p weight baseWeight U c hc t z).mp
      have he := (N.functions_range U _).mp ⟨y, rfl⟩
      change IsCovariantOn Q p (baseWeight * weight ^ t) U
        ((↑u : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)) * z)
      simpa only [hz] using he
    obtain ⟨x, hx⟩ := (M.functions_range U _).mpr hcov
    refine ⟨x, N.functions_injective U ?_⟩
    change N.functionVal U (f x) = N.functionVal U y
    rw [hf]
    exact (congrArg ((u : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)) * ·) hx).trans hz
  exact ⟨LinearEquiv.ofBijective F ⟨inj, surj⟩, hf⟩

end LocalTwists

section Flag

open private exists_associatedBundle from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- The covariance sheaf is coherent by its local rank-one trivializations. -/
private theorem flagLineSheaf_coherent (P : OppositeBorelPair G)
    (Q : Presentation P.negative) (b : BorelProjection P) (χ : Character P.torus.group)
    (h : FlagKernelPair Q) :
    (flagLineSheaf Q b χ h).IsFinitePresentation ∧ (flagLineSheaf Q b χ h).IsQuasicoherent := by
  obtain ⟨_, _, _, _, _, _, _, a, _, _, ha⟩ :=
    (LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G P).2.2 Q
  obtain ⟨L⟩ := exists_associatedBundle Q b χ a ha
  obtain ⟨hqc, hlocal, _⟩ := Representation.FlagCohomology.flagLineSheafIdentification Q b χ h L
  refine ⟨?_, hqc⟩
  choose U hU e using hlocal
  exact ProjectiveFiniteness.isFinitePresentation_of_local_rank_one_restrict
    _ U (top_unique fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hU y⟩)
    (fun y => (e y).some.symm)

end Flag

section AssociatedCoefficients

open Specs.AssociatedFlagLineSheaves (SectionRealization)
open Specs.FlagCohomology (flagLineData CovarianceData)
open LinearAlgebraicGroups.AssociatedFlagLineSheaves (realizeSections)
open private covarianceDifference from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.AssociatedFlagLineSheaves

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
variable {b : BorelProjection P} {χ : Character P.torus.group}

set_option backward.isDefEq.respectTransparency false in
private theorem covarianceDifference_eq (h : FlagKernelPair Q) :
    covarianceDifference Q b χ = (flagLineData Q b χ h).covariance := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext f : 1
  change (covarianceDifference Q b χ).app U.unop f = (flagLineData Q b χ h).covariance.app U.unop f
  unfold CovarianceData.covariance
  rw [Representation.FlagCohomology.covarianceMap_app]
  let X := (G.val.X ⨯ P.negative.group.X).left
  let V := ((prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X) ≫ Q.projection).left ⁻¹ᵁ U.unop
  let R := Γ(X, V)
  have hComm (x y : R) : x * y = y * x := mul_comm x y
  exact congrArg (fun t : R => _ - t) (hComm _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The section realization used by Steinberg pushforward has the same
coefficient sheaf as the flag covariance kernel. -/
private theorem exists_associatedFlagSheafIso (L : AssociatedBundle Q a b χ) (h : FlagKernelPair Q) :
    ∃ e : (realizeSections L).sheaf ≅ flagLineSheaf Q b χ h,
      ∀ U x, (flagLineData Q b χ h).inclusion.app U (e.hom.app U x) =
        (realizeSections L).functionVal U x := by
  let M := realizeSections L
  let D := flagLineData Q b χ h
  have hz : M.functions ≫ D.covariance = 0 := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext x : 1
    change D.covariance.app U.unop (M.functions.app U.unop x) = 0
    rw [← covarianceDifference_eq h]
    exact x.property
  let f : M.sheaf ⟶ D.sheaf := kernel.lift D.covariance M.functions hz
  have hcomp (U : Q.scheme.left.Opens) (x : Γ(M.sheaf, U)) :
      D.inclusion.app U (f.app U x) = M.functions.app U x :=
    ConcreteCategory.congr_hom (congrArg (fun a => a.app U)
      (kernel.lift_ι D.covariance M.functions hz)) x
  have hf : IsIso f := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    constructor
    · intro x y hxy
      apply M.functions_injective U
      rw [← hcomp, ← hcomp, hxy]
    · intro y
      let x : Γ(M.sheaf, U) := ⟨D.inclusion.app U y, by
        change (covarianceDifference Q b χ).app U (D.inclusion.app U y) = 0
        rw [covarianceDifference_eq h]
        exact ConcreteCategory.congr_hom (congrArg (fun a => a.app U) (kernel.condition D.covariance)) y⟩
      refine ⟨x, ?_⟩
      let E := SheafOfModules.evaluation Q.scheme.left.ringCatSheaf (op U)
      have hmono : Mono (E.map D.inclusion) := E.map_mono D.inclusion
      apply (ModuleCat.mono_iff_injective (E.map D.inclusion)).mp hmono
      change D.inclusion.app U (f.app U x) = D.inclusion.app U y
      exact hcomp U x
  exact ⟨asIso f, hcomp⟩

end AssociatedCoefficients

section CoordinateRatios

open Specs.ProjectiveSpaces (coordinateProjectiveSpace coordinateOpen coordinate_mem_degree_one
  grading coordinateRatio chartInclusion)
open Specs.ProjectiveTwistChartModules
open Specs.ProjectiveFiniteChartPresentations (Chart)
open private polynomialToLaurent_monomial
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveTwistChartModules

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]

private def coordinateSection (j i : I) : Γ((coordinateProjectiveSpace k I).left,
    coordinateOpen k I j) :=
  Proj.awayToSection (grading k I) (MvPolynomial.X j) (coordinateRatio k I j i)

omit [Fintype I] [DecidableEq I] in
private theorem singleton_product (j : I) : coordinateProduct k I {j} = MvPolynomial.X j := by
  simp [coordinateProduct]

omit [Fintype I] in
private theorem singleton_exponent (j : I) :
    coordinateProductExponent {j} = coordinateExponent j := by
  funext i
  simp [coordinateProductExponent, coordinateExponent]

omit [Fintype I] [DecidableEq I] in
private theorem awaySection_congr {p q a : MvPolynomial I k} (e : p = q)
    (hp : p ∈ grading k I 1) (hq : q ∈ grading k I 1) (ha : a ∈ grading k I 1) :
    Proj.awayToSection (grading k I) p (HomogeneousLocalization.Away.mk _ hp 1 a (by simpa using ha)) =
      (coordinateProjectiveSpace k I).left.presheaf.map
        (eqToHom (congrArg (Proj.basicOpen (grading k I)) e)).op
        (Proj.awayToSection (grading k I) q
          (HomogeneousLocalization.Away.mk _ hq 1 a (by simpa using ha))) := by
  subst q
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem ratio_singleton (D : ChartGeometry k I) (i j : I) :
    D.ratio ⟨{j}, Finset.singleton_nonempty j⟩ i j (Finset.mem_singleton_self j) =
      (coordinateProjectiveSpace k I).left.presheaf.map
        (eqToHom (show chartOpen k {j} = coordinateOpen k I j by
          exact congrArg (Proj.basicOpen (grading k I)) (singleton_product j))).op
        (coordinateSection j i) := by
  let S : ChartIndex I := ⟨{j}, Finset.singleton_nonempty j⟩
  let hp : MvPolynomial.X i ∈ grading k I (1 • S.val.card) := by
    simpa [S] using coordinate_mem_degree_one k I i
  have hf : chartFraction S 1 (MvPolynomial.X i) hp =
      (coordinateProjectiveSpace k I).left.presheaf.map
        (eqToHom (show chartOpen k {j} = coordinateOpen k I j by
          exact congrArg (Proj.basicOpen (grading k I)) (singleton_product j))).op
        (coordinateSection j i) := by
    change Proj.awayToSection (grading k I) (coordinateProduct k I {j})
      (HomogeneousLocalization.Away.mk _ (coordinateProduct_degree k I {j}) 1 _ hp) = _
    exact awaySection_congr (singleton_product j) _ _ (coordinate_mem_degree_one k I i)
  rw [← hf]
  apply D.injective S
  rw [D.ratio_coeff, D.fraction_coeff, one_smul]
  change _ = polynomialToLaurent (MvPolynomial.X i) *
    AddMonoidAlgebra.single (-coordinateProductExponent {j}) 1
  rw [singleton_exponent, MvPolynomial.X, polynomialToLaurent_monomial,
    AddMonoidAlgebra.single_mul_single, mul_one, ratioExponent, sub_eq_add_neg]
  congr 2
  funext l
  simp [polynomialExponent, coordinateExponent, Finsupp.single_apply, eq_comm]

set_option backward.isDefEq.respectTransparency false in
private theorem ratio_eq_restriction (D : ChartGeometry k I) (S : Chart I)
    (i j : I) (hj : j ∈ S.indices) :
    D.ratio (indexOf S) i j hj = (coordinateProjectiveSpace k I).left.presheaf.map
      (homOfLE (show chartOpen k S.indices ≤ coordinateOpen k I j by
        rw [chartOpen_eq_inf]; exact Finset.inf_le hj)).op (coordinateSection j i) := by
  let f : Chart.single j ⟶ S := Chart.fromSingle hj
  have he := D.ratio_restrict f i j (Finset.mem_singleton_self j)
  change (chartRings k I).map f
    (D.ratio ⟨{j}, Finset.singleton_nonempty j⟩ i j (Finset.mem_singleton_self j)) = _ at he
  rw [← he, ratio_singleton]
  change ((coordinateProjectiveSpace k I).left.presheaf.map
    (homOfLE (chartOpen_anti (Chart.subset f))).op)
      ((coordinateProjectiveSpace k I).left.presheaf.map _ (coordinateSection j i)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

omit [Fintype I] [DecidableEq I] in
/-- The affine spectrum of a projective chart's section ring maps to the
projective space by the standard chart immersion. -/
private theorem specMap_coordinateSections_away (j : I)
    (hU : IsAffineOpen (coordinateOpen k I j)) :
    Spec.map (Proj.awayToSection (grading k I) (MvPolynomial.X j)) ≫
      chartInclusion k I j = hU.fromSpec := by
  let U := coordinateOpen k I j
  let e := Proj.basicOpenIsoSpec (grading k I) _ (coordinate_mem_degree_one k I j) Nat.one_pos
  change Spec.map _ ≫ e.inv ≫ U.ι = hU.isoSpec.inv ≫ U.ι
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change _ = hU.isoSpec.inv ≫ U.toSpecΓ ≫ Spec.map _
  rw [hU.isoSpec_inv_toSpecΓ_assoc]

end CoordinateRatios

section TorsorCharts

open Specs.ProjectiveSpaces (projectiveSpace coordinateProjectiveSpace coordinateOpen
  chartInclusion coordinateRatio grading coordinate_mem_degree_one)
open LinearAlgebraicGroups.ProjectiveSpaces (coordinateAffineCharts)
open Specs.ProjectiveTwistChartModules (ChartGeometry chartOpen chartOpen_eq_inf indexOf)
open Specs.ProjectiveFiniteChartPresentations (Chart)
open private projectiveBasis chartPoint point_has_chart
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.ProjectiveSpaces
open private flagTorsor_affine from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
open TopologicalSpace
open scoped TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]

private abbrev Index (k V : Type u) [Field k] [AddCommGroup V] [Module k V] :=
  ULift.{u} (Fin (Module.finrank k V))

private abbrev chartOnFlag {Q : Presentation P.negative} (j : Q.scheme ⟶ projectiveSpace k V)
    (S : Chart (Index k V)) : Q.scheme.left.Opens :=
  j.left ⁻¹ᵁ chartOpen k S.indices

private abbrev restrictGlobal {X : Scheme.{u}} (U : X.Opens) (c : Γ(X, ⊤)) : Γ(X, U) :=
  X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op c

set_option backward.isDefEq.respectTransparency false in
private theorem fromSpec_evaluate {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (c : Γ(X, ⊤)) :
    (Scheme.ΓSpecIso Γ(X, U)).hom (hU.fromSpec.appTop c) = restrictGlobal U c := by
  have he := hU.fromSpec_app_of_le ⊤ le_top
  change hU.fromSpec.appTop =
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map (homOfLE le_top).op at he
  have hid : (homOfLE le_top : (⊤ : (Spec Γ(X, U)).Opens) ⟶ ⊤).op = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [hid, (Spec Γ(X, U)).presheaf.map_id, Category.comp_id] at he
  rw [he, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem torsorChart_coordinates (Q : Presentation P.negative)
    (j : Q.scheme ⟶ projectiveSpace k V) [IsClosedImmersion j.left]
    (D : ChartGeometry k (Index k V)) (S : Chart (Index k V))
    (frame : ∀ (R : TestAlgebra k), Points G.val.X R → R ⊗[k] V)
    (hframe : ∀ R g,
      (((LinearAlgebraicGroups.ProjectiveSpaces.lineRepresentation k V).points _ j).line
        R (g ≫ Q.projection)).submodule = Submodule.span R {frame R g})
    (c : Index k V → Γ(G.val.X.left, ⊤))
    (hc : ∀ i (R : TestAlgebra k) (x : Points G.val.X R),
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom (x.left.appTop (c i)) =
        ((projectiveBasis k V).baseChange R).coord i (frame R x))
    (l : Index k V) (hl : l ∈ S.indices) :
    let U := Q.projection.left ⁻¹ᵁ chartOnFlag j S
    IsUnit (restrictGlobal U (c l)) ∧
      ∀ i, restrictGlobal U (c i) =
        Q.projection.left.app (chartOnFlag j S)
          (j.left.app (chartOpen k S.indices) (D.ratio (indexOf S) i l hl)) *
        restrictGlobal U (c l) := by
  dsimp only
  let X := G.val.X.left
  let Y := (projectiveSpace k V).left
  let W := chartOpen k S.indices
  let U := Q.projection.left ⁻¹ᵁ chartOnFlag j S
  let f : X ⟶ Y := Q.projection.left ≫ j.left
  have hU : IsAffineOpen U := by
    let := flagTorsor_affine Q
    exact ((D.affine (indexOf S)).preimage j.left).preimage Q.projection.left
  let φ : CommRingCat.of k ⟶ Γ(X, U) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ G.val.X.hom.appLE ⊤ U (by simp)
  let : Algebra k Γ(X, U) := φ.hom.toAlgebra
  let R : TestAlgebra k := CommAlgCat.of k Γ(X, U)
  let g : Points G.val.X R := Over.homMk hU.fromSpec (by
    change hU.fromSpec ≫ G.val.X.hom = Spec.map φ
    dsimp only [φ]
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
    exact (IsAffineOpen.SpecMap_appLE_fromSpec G.val.X.hom (isAffineOpen_top _) hU _).symm)
  let p : Points (projectiveSpace k V) R := (g ≫ Q.projection) ≫ j
  have hW : W ≤ coordinateOpen k (Index k V) l := by
    dsimp only [W]
    rw [chartOpen_eq_inf]
    exact Finset.inf_le hl
  have hle : U ≤ f ⁻¹ᵁ coordinateOpen k (Index k V) l := by
    rw [Scheme.Hom.comp_preimage]
    exact (Opens.map Q.projection.left.base).monotone
      ((Opens.map j.left.base).monotone hW)
  obtain ⟨a, ha⟩ := point_has_chart p (i := l) (by
    rw [(coordinateAffineCharts k (Index k V) l).2]
    rintro _ ⟨x, rfl⟩
    apply hle
    change hU.fromSpec x ∈ (U : Set X)
    rw [← hU.range_fromSpec]
    exact Set.mem_range_self x)
  have heval (i : Index k V) :
      restrictGlobal U (c i) = ((projectiveBasis k V).baseChange R).coord i (frame R g) :=
    (fromSpec_evaluate hU (c i)).symm.trans (hc i R g)
  obtain ⟨hu, hr⟩ := frameCoordinates_of_chartPoint Q j g l a ha (frame R g) (hframe R g)
  refine ⟨by rw [heval l]; exact hu, fun i => ?_⟩
  have hU₀ := Proj.isAffineOpen_basicOpen (grading k (Index k V)) _
    (coordinate_mem_degree_one k (Index k V) l) Nat.one_pos
  let U₀ := coordinateOpen k (Index k V) l
  let s := Proj.awayToSection (grading k (Index k V)) (MvPolynomial.X l)
  have hs : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ chartInclusion k (Index k V) l =
      hU.fromSpec ≫ f := by
    have hh := congrArg (fun q : Points (projectiveSpace k V) R => q.left) ha
    exact hh.symm.trans (Category.assoc _ _ _)
  have he : s ≫ f.appLE U₀ U hle = CommRingCat.ofHom a.toRingHom := by
    apply Spec.map_inj.mp
    apply (cancel_mono (chartInclusion k (Index k V) l)).mp
    rw [Spec.map_comp, Category.assoc, specMap_coordinateSections_away l hU₀, hs,
      IsAffineOpen.SpecMap_appLE_fromSpec f hU₀ hU hle]
  have hv : a (coordinateRatio k (Index k V) l i) =
      f.appLE U₀ U hle (coordinateSection l i) :=
    (ConcreteCategory.congr_hom he (coordinateRatio k (Index k V) l i)).symm
  calc
    restrictGlobal U (c i) =
        a (coordinateRatio k (Index k V) l i) * restrictGlobal U (c l) := by
      rw [heval i, heval l, hr]
    _ = _ := by
      congr 1
      rw [hv, ratio_eq_restriction D S i l hl]
      change f.appLE U₀ U hle (coordinateSection l i) =
        f.app W (Y.presheaf.map (homOfLE hW).op (coordinateSection l i))
      rw [← ConcreteCategory.comp_apply, f.app_eq_appLE, Scheme.Hom.map_appLE]
      rfl

end TorsorCharts

section Comparison

open Specs.AmpleFlagWeights (IsHyperplanePullback)
open Specs.AssociatedFlagLineSheaves (IsCovariantOn)
open Specs.FlagCohomology (flagLineData)
open Specs.ProjectiveSpaces (LineRepresentation projectiveSpace)
open Specs.ProjectiveFiniteChartPresentations (Chart)
open Specs.ProjectiveTwistChartModules (ChartGeometry chartOpen chartOpen_anti indexOf)
open LinearAlgebraicGroups.AssociatedFlagLineSheaves (realizeSections)
open private projectiveBasis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.ProjectiveSpaces
open private exists_associatedBundle from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
open private projectiveChartRings sheafChartModules from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness
open Scheme.Modules
open scoped TensorProduct

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {Q : Presentation P.negative} (b : BorelProjection P) (h : FlagKernelPair Q)

private abbrev sectionFunction (χ : Character P.torus.group) (U : Q.scheme.left.Opens) :
    Γ(flagLineSheaf Q b χ h, U) → Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U) :=
  (flagLineData Q b χ h).inclusion.app U

set_option backward.isDefEq.respectTransparency false in
private theorem sectionFunction_injective (χ : Character P.torus.group)
    (U : Q.scheme.left.Opens) : Function.Injective (sectionFunction b h χ U) := by
  let E := SheafOfModules.evaluation Q.scheme.left.ringCatSheaf (op U)
  have : Mono (E.map (flagLineData Q b χ h).inclusion) :=
    E.map_mono (flagLineData Q b χ h).inclusion
  exact (ModuleCat.mono_iff_injective (E.map (flagLineData Q b χ h).inclusion)).mp this

set_option backward.isDefEq.respectTransparency false in
private theorem exists_flagTwistSectionEquiv
    {a : ModObj G.val.X Q.scheme} (ha : μ[G.val.X] ≫ Q.projection =
      (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
    (weight χ : Character P.torus.group) (t : ℕ) (U : Q.scheme.left.Opens)
    (c : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)ˣ) (hc : IsCovariantOn Q b weight U c) :
    ∃ e : Γ(flagLineSheaf Q b χ h, U) ≃ₗ[Γ(Q.scheme.left, U)]
        Γ(flagLineSheaf Q b (χ * weight ^ t) h, U),
      ∀ x, sectionFunction b h (χ * weight ^ t) U (e x) =
        (↑c : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)) ^ t * sectionFunction b h χ U x := by
  obtain ⟨L⟩ := exists_associatedBundle Q b χ a ha
  obtain ⟨L'⟩ := exists_associatedBundle Q b (χ * weight ^ t) a ha
  obtain ⟨e, he⟩ := exists_associatedFlagSheafIso L h
  obtain ⟨e', he'⟩ := exists_associatedFlagSheafIso L' h
  obtain ⟨E, hE⟩ := exists_twistSectionEquiv b t (realizeSections L) (realizeSections L') U c hc
  let F := SheafOfModules.evaluation Q.scheme.left.ringCatSheaf (op U)
  let A : Γ((realizeSections L).sheaf, U) ≃ₗ[Γ(Q.scheme.left, U)] Γ(flagLineSheaf Q b χ h, U) :=
    (F.mapIso e).toLinearEquiv
  let B : Γ((realizeSections L').sheaf, U) ≃ₗ[Γ(Q.scheme.left, U)]
      Γ(flagLineSheaf Q b (χ * weight ^ t) h, U) := (F.mapIso e').toLinearEquiv
  refine ⟨A.symm.trans (E.trans B), fun x => ?_⟩
  have hA : (realizeSections L).functionVal U (A.symm x) = sectionFunction b h χ U x := by
    rw [← he U (A.symm x)]
    change sectionFunction b h χ U (A (A.symm x)) = _
    rw [A.apply_symm_apply]
  change sectionFunction b h (χ * weight ^ t) U (B (E (A.symm x))) = _
  rw [show sectionFunction b h (χ * weight ^ t) U (B (E (A.symm x))) =
      (realizeSections L').functionVal U (E (A.symm x)) from he' U _, hE, hA]

variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
variable [IsLocallyNoetherian (projectiveSpace k V).left]

private abbrev flagChartModules (D : ChartGeometry k (Index k V))
    (j : Q.scheme ⟶ projectiveSpace k V) (χ : Character P.torus.group) :
    (projectiveChartRings D).Modules :=
  sheafChartModules D ((pushforward j.left).obj (flagLineSheaf Q b χ h))

set_option backward.isDefEq.respectTransparency false in
private theorem twistChartIso
    (j : Q.scheme ⟶ projectiveSpace k V) [IsClosedImmersion j.left]
    (D : ChartGeometry k (Index k V)) (weight χ : Character P.torus.group)
    (a : ModObj G.val.X Q.scheme)
    (ha : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul)
    (hw : IsHyperplanePullback Q b weight j (LinearAlgebraicGroups.ProjectiveSpaces.lineRepresentation k V))
    (t : ℕ) :
    Nonempty (shiftDiagram (projectiveChartRings D) (flagChartModules b h D j χ) t ≅
      flagChartModules b h D j (χ * weight ^ t)) := by
  classical
  obtain ⟨frame, hf, hnatural, htransition⟩ := hw
  choose c hc using fun i : Index k V =>
    exists_frame_coordinate (projectiveBasis k V) i frame hnatural
  let X := G.val.X.left
  let U (S : Chart (Index k V)) := chartOnFlag j S
  let W (S : Chart (Index k V)) := Q.projection.left ⁻¹ᵁ U S
  have hcoord S := torsorChart_coordinates Q j D S frame (fun R g => (hf R g).1) c hc
    (chartIndex S) (chartIndex_mem S)
  choose u hu using fun S => (hcoord S).1
  have hcov S : IsCovariantOn Q b weight (U S) (u S) := by
    rw [hu S]
    exact isCovariantOn_frame_coordinate (projectiveBasis k V) (chartIndex S)
      Q b weight frame htransition (c (chartIndex S)) (hc (chartIndex S)) (U S)
  choose e he using fun S => exists_flagTwistSectionEquiv b h ha weight χ t (U S) (u S) (hcov S)
  let E (S : Chart (Index k V)) :=
    (ModuleCat.restrictScalars (j.left.app (chartOpen k S.indices)).hom).mapIso (e S).toModuleIso
  refine ⟨PresheafOfModules.isoMk E ?_⟩
  intro S T f
  apply ModuleCat.hom_ext
  ext x : 1
  let wt := χ * weight ^ t
  let r : Γ((projectiveSpace k V).left, chartOpen k (Chart.indices T)) :=
    D.ratio (indexOf T) (chartIndex S) (chartIndex T) (chartIndex_mem T)
  let i : U T ⟶ U S := homOfLE ((TopologicalSpace.Opens.map j.left.base).monotone
    (chartOpen_anti (Chart.subset f)))
  let res := X.presheaf.map ((TopologicalSpace.Opens.map Q.projection.left.base).map i).op
  have res_glob (c₀ : Γ(X, ⊤)) :
      res (restrictGlobal (W S) c₀) = restrictGlobal (W T) c₀ := by
    change (X.presheaf.map _ ≫ X.presheaf.map _) c₀ = _
    rw [← Functor.map_comp]
    rfl
  have hres (ψ : Character P.torus.group) (y : (flagChartModules b h D j ψ).obj S) :
      sectionFunction b h ψ (U T) ((flagChartModules b h D j ψ).map f y) =
        res (sectionFunction b h ψ (U S) y) :=
    PresheafOfModules.naturality_apply (flagLineData Q b ψ h).inclusion.val i.op y
  have hsc (q : Γ((projectiveSpace k V).left, chartOpen k (Chart.indices T)))
      (y : Γ(flagLineSheaf Q b χ h, U T)) :
      sectionFunction b h χ (U T) (q • (show (flagChartModules b h D j χ).obj T from y)) =
        Q.projection.left.app (U T) (j.left.app (chartOpen k (Chart.indices T)) q) *
          sectionFunction b h χ (U T) y := by
    change sectionFunction b h χ (U T) (j.left.app (chartOpen k (Chart.indices T)) q • y) = _
    rw [sectionFunction, Scheme.Modules.Hom.app_smul]
    rfl
  have hratio :
      res (↑(u S) : Γ(X, W S)) =
        Q.projection.left.app (U T) (j.left.app (chartOpen k (Chart.indices T)) r) * (u T : Γ(X, W T)) := by
    rw [hu S, hu T, res_glob]
    exact (hcoord T).2 (chartIndex S)
  change e T ((↑(chartFactor (projectiveChartRings D) f ^ (t : ℤ)) :
      (projectiveChartRings D).rings.obj T) •
      (show (flagChartModules b h D j χ).obj T from (flagChartModules b h D j χ).map f x)) =
      (flagChartModules b h D j wt).map f (e S x)
  apply sectionFunction_injective b h wt (U T)
  rw [he T, hres, he S, map_mul res.hom, map_pow res.hom, hratio, mul_pow, ← hres,
    hsc, zpow_natCast, Units.val_pow_eq_pow_val]
  change _ * (Q.projection.left.app (U T) (j.left.app (chartOpen k (Chart.indices T)) (r ^ t)) * _) = _
  rw [map_pow (j.left.app (chartOpen k (Chart.indices T))).hom, map_pow (Q.projection.left.app (U T)).hom]
  ac_rfl

end Comparison

section Vanishing

open Specs.AmpleFlagWeights (IsHyperplanePullback)
open Specs.ProjectiveSpaces (LineRepresentation projectiveSpace)
open Specs.ProjectiveTwistChartModules (ChartGeometry)
open private chartCech projectiveChartRings finite_sheafChartModules_pushforward
  localizes_sheafChartModules_pushforward cohomologyIso_chartCech
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]

private theorem exists_standard_hyperplane_embedding
    (Q : Presentation P.negative) (b : BorelProjection P) (weight : Character P.torus.group)
    (ρ : LineRepresentation k V) (j : Q.scheme ⟶ projectiveSpace k V) [IsClosedImmersion j.left]
    (hw : IsHyperplanePullback Q b weight j ρ) :
    ∃ j' : Q.scheme ⟶ projectiveSpace k V, IsClosedImmersion j'.left ∧
      IsHyperplanePullback Q b weight j' (LinearAlgebraicGroups.ProjectiveSpaces.lineRepresentation k V) := by
  let τ := LinearAlgebraicGroups.ProjectiveSpaces.lineRepresentation k V
  obtain ⟨e, he⟩ := projectiveIso_of_lineRepresentations ρ τ
  refine ⟨j ≫ e.hom, IsClosedImmersion.comp j.left e.hom.left, ?_⟩
  obtain ⟨frame, hf, hn, ht⟩ := hw
  refine ⟨frame, ?_, hn, ht⟩
  intro R g
  change (((τ.points Q.scheme (j ≫ e.hom)).line R (g ≫ Q.projection)).submodule =
    Submodule.span R {frame R g}) ∧ Function.Injective (fun r : R => r • frame R g)
  rw [he]
  exact hf R g

variable {Q : Presentation P.negative} (b : BorelProjection P) (h : FlagKernelPair Q)
variable (j : Q.scheme ⟶ projectiveSpace k V) [IsClosedImmersion j.left]

private theorem eventually_isZero_shiftedFlagChartCech
    [IsLocallyNoetherian (projectiveSpace k V).left] [Nonempty (Index k V)]
    (D : ChartGeometry k (Index k V)) (χ : Character P.torus.group) :
    ∃ N : ℕ, ∀ t : ℕ, N ≤ t → ∀ n : ℕ, 0 < n →
      IsZero ((chartCech (shiftDiagram (projectiveChartRings D) (flagChartModules b h D j χ) t)).homology n) := by
  obtain ⟨hfp, hqc⟩ := flagLineSheaf_coherent P Q b χ h
  let : (flagLineSheaf Q b χ h).IsFinitePresentation := hfp
  let : (flagLineSheaf Q b χ h).IsQuasicoherent := hqc
  have hfin := finite_sheafChartModules_pushforward D j.left (flagLineSheaf Q b χ h)
  have hloc := localizes_sheafChartModules_pushforward D j.left (flagLineSheaf Q b χ h)
  exact eventually_isZero_chartCech D (flagChartModules b h D j χ) hfin hloc

private theorem isZero_flagCohomology_of_chartCech
    [IsLocallyNoetherian (projectiveSpace k V).left] [Nonempty (Index k V)]
    (D : ChartGeometry k (Index k V)) (χ : Character P.torus.group) (n : ℕ)
    (hn : IsZero ((chartCech (flagChartModules b h D j χ)).homology n)) :
    IsZero (flagCohomology Q b χ h n) := by
  let : (flagLineSheaf Q b χ h).IsQuasicoherent := (flagLineSheaf_coherent P Q b χ h).2
  exact hn.of_iso (cohomologyIso_chartCech j D (flagLineSheaf Q b χ h) n)

private theorem vanishing_of_standard_hyperplane
    [IsLocallyNoetherian (projectiveSpace k V).left] [Nonempty (Index k V)]
    (weight χ : Character P.torus.group)
    (hw : IsHyperplanePullback Q b weight j (LinearAlgebraicGroups.ProjectiveSpaces.lineRepresentation k V)) :
    ∃ N : ℕ, ∀ t : ℕ, N ≤ t → ∀ n : ℕ, 0 < n →
      IsZero (flagCohomology Q b (χ * weight ^ t) h n) := by
  let D : ChartGeometry k (Index k V) := ProjectiveTwistChartModules.chartGeometry
  obtain ⟨N, hN⟩ := eventually_isZero_shiftedFlagChartCech b h j D χ
  obtain ⟨_, _, _, _, _, _, _, a, _, _, ha⟩ :=
    (LinearAlgebraicGroups.FlagLineBundle.oppositeFlagGeometry k G P).2.2 Q
  refine ⟨N, fun t ht n hn => ?_⟩
  obtain ⟨E⟩ := twistChartIso b h j D weight χ a ha hw t
  let H := homologyFunctor (ModuleCat.{u} k) (.up ℕ) n
  have hz : IsZero ((chartCech (flagChartModules b h D j (χ * weight ^ t))).homology n) :=
    (hN t ht n hn).of_iso (H.mapIso (chartCechIso D E).symm)
  exact isZero_flagCohomology_of_chartCech b h j D (χ * weight ^ t) n hz

omit [IsClosedImmersion j.left] in
private theorem vanishing_of_hyperplane
    (weight χ : Character P.torus.group) (ρ : LineRepresentation k V)
    (hj : IsClosedImmersion j.left) (hw : IsHyperplanePullback Q b weight j ρ) :
    ∃ N : ℕ, ∀ t : ℕ, N ≤ t → ∀ n : ℕ, 0 < n →
      IsZero (flagCohomology Q b (χ * weight ^ t) h n) := by
  by_cases hz : Module.finrank k V = 0
  · let := ProjectiveFiniteness.isEmpty_of_projective_finrank_zero j hz
    exact ⟨0, fun t _ n _ => ProjectiveFiniteness.isZero_cohomology_of_isEmpty Q.scheme
      (flagLineSheaf Q b (χ * weight ^ t) h) n⟩
  let : IsClosedImmersion j.left := hj
  obtain ⟨j', _, hw'⟩ := exists_standard_hyperplane_embedding Q b weight ρ j hw
  let : Nonempty (Index k V) := ⟨⟨⟨0, Nat.pos_of_ne_zero hz⟩⟩⟩
  let : IsProper (projectiveSpace k V).hom :=
    LinearAlgebraicGroups.ProjectiveSpaces.projectiveSpaceProper k V
  let : IsLocallyNoetherian (projectiveSpace k V).left :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpace k V).hom
  exact vanishing_of_standard_hyperplane b h j' weight χ hw'

end Vanishing

/-- Serre vanishing for the actual associated character sheaves on a split flag. -/
theorem ampleFlagTwistVanishing : Specs.AmpleFlagTwistVanishing.EventualVanishing.{u} := by
  intro k _ G P Q b h θ χ hamp
  obtain ⟨m, hm, V, _, _, _, ρ, j, hj, hw⟩ := hamp
  apply eventually_of_residues _ m hm
  intro r
  obtain ⟨N, hN⟩ := vanishing_of_hyperplane b h j (θ ^ m) (χ * θ ^ r.val) ρ hj hw
  exact ⟨N, fun t ht n hn => by simpa only [pow_add, pow_mul, mul_assoc] using hN t ht n hn⟩

end LinearAlgebraicGroups.AmpleFlagTwistVanishing
