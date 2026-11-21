import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.AlgebraicCovering
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.FiniteExceptionalSet
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.SimpleRootBranches
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.GermsContinuation
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.CoveringPaths
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Homotopy.Lifting

/-! The algebraic covering over the complement of the determinant exceptional set.
The argument specializes the accepted simultaneous root branches, builds open graph
sheets in the original subspace topology, and transports actual holomorphic germs
along covering lifts. No connectedness of the total space is used. -/

noncomputable section
open Polynomial Set
open D12Complex
open D12Complex.SimpleRootBranches
namespace D12Complex.AlgebraicCovering

lemma familyPolynomial_fiber (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hdeg : P.natDegree = d) (z : ℂ) :
    familyPolynomial d (fun j z => (P.coeff j).eval z) z = fiber P z := by
  have h := congrArg (fun q : Polynomial (Polynomial ℂ) => q.map (Polynomial.evalRingHom z))
    P.as_sum_range.symm
  simpa only [familyPolynomial, fiber, Specs.D12Complex.Ch21.FiniteExceptionalSet.fiber_value, Polynomial.map_sum, Polynomial.map_monomial,
    Polynomial.coe_evalRingHom, hdeg] using h

private lemma branch_data (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (a : ℂ) (ha : a ∉ exceptionalSet P) :
    ∃ (b : Fin d → ℂ) (r : ℝ) (f : Fin d → ℂ → ℂ) (V : Fin d → Set ℂ),
      0 < r ∧ Metric.ball a r ⊆ (exceptionalSet P)ᶜ ∧
      (∀ i, IsOpen (V i) ∧ b i ∈ V i) ∧
      Pairwise (fun i j => Disjoint (V i) (V j)) ∧
      (∀ i, HolomorphicOn (Metric.ball a r) (f i) ∧ f i a = b i ∧
        MapsTo (f i) (Metric.ball a r) (V i)) ∧
      (∀ z ∈ Metric.ball a r, ∀ i, ∀ w ∈ V i,
        (fiber P z).eval w = 0 ↔ w = f i z) ∧
      (∀ z ∈ Metric.ball a r,
        (fiber P z).natDegree = d ∧
        Function.Injective (fun i => f i z) ∧
        ∀ w : ℂ, (fiber P z).eval w = 0 ↔ ∃ i, w = f i z) := by
  classical
  obtain ⟨_, hfinite, hfiber⟩ := D12Complex.Ch21.FiniteExceptionalSet.finite_exceptional_set P d hP hdeg hd
  change (exceptionalSet P).Finite at hfinite
  change ∀ z, z ∉ exceptionalSet P → _ at hfiber
  obtain ⟨_, _, hcard, hmem, _⟩ := hfiber a ha
  change (fiber P a).roots.toFinset.card = d at hcard
  change ∀ w, w ∈ (fiber P a).roots.toFinset ↔ (fiber P a).eval w = 0 at hmem
  let e := (fiber P a).roots.toFinset.equivFinOfCardEq hcard
  let b : Fin d → ℂ := fun i => (e.symm i).val
  have hb : Function.Injective b := Subtype.val_injective.comp e.symm.injective
  have hroot : ∀ i, (familyPolynomial d (fun j z => (P.coeff j).eval z) a).eval (b i) = 0 := by
    intro i
    rw [familyPolynomial_fiber P d hdeg]
    exact (hmem _).mp (e.symm i).property
  have hlead : (P.coeff d).eval a ≠ 0 := by
    have h : (P.leadingCoeff * D12Complex.Ch21.FiniteExceptionalSet.resultantPolynomial P).eval a ≠ 0 := ha
    rw [Polynomial.eval_mul] at h
    simpa [Polynomial.leadingCoeff, hdeg] using (mul_ne_zero_iff.mp h).1
  have hA : ∀ j ≤ d, HolomorphicOn (exceptionalSet P)ᶜ (fun z => (P.coeff j).eval z) := by
    intro j _
    exact ⟨hfinite.isClosed.isOpen_compl, fun z _ => (P.coeff j).differentiableAt⟩
  obtain ⟨r, f, V, hr, hball, hV, hdisj, hf, hlocal, hall⟩ :=
    all_simple_root_branches d (fun j z => (P.coeff j).eval z)
      (exceptionalSet P)ᶜ a b hd hfinite.isClosed.isOpen_compl ha hA hlead hb hroot
  refine ⟨b, r, f, V, hr, hball, hV, hdisj, hf, ?_, ?_⟩
  · simpa only [familyPolynomial_fiber P d hdeg] using hlocal
  · simpa only [familyPolynomial_fiber P d hdeg] using hall

private lemma fiber_root_equiv (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (a : ℂ) (ha : a ∉ exceptionalSet P) :
    Nonempty ({w : ℂ // (fiber P a).eval w = 0} ≃ Fin d) := by
  classical
  obtain ⟨_, _, hfiber⟩ := D12Complex.Ch21.FiniteExceptionalSet.finite_exceptional_set P d hP hdeg hd
  change ∀ z, z ∉ exceptionalSet P → _ at hfiber
  obtain ⟨_, _, hcard, hmem, _⟩ := hfiber a ha
  change (fiber P a).roots.toFinset.card = d at hcard
  change ∀ w, w ∈ (fiber P a).roots.toFinset ↔ (fiber P a).eval w = 0 at hmem
  exact ⟨(Equiv.subtypeEquivRight (fun w => (hmem w).symm)).trans
    ((fiber P a).roots.toFinset.equivFinOfCardEq hcard)⟩

theorem base_domain (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d) :
    IsDomain (baseSet P) := by
  obtain ⟨_, hfinite, _⟩ := D12Complex.Ch21.FiniteExceptionalSet.finite_exceptional_set P d hP hdeg hd
  change (exceptionalSet P).Finite at hfinite
  have hconn := hfinite.countable.isConnected_compl_of_one_lt_rank (by simp)
  exact ⟨hconn.nonempty, hfinite.isClosed.isOpen_compl, hconn.isPreconnected⟩


theorem local_branches : Specs.D12Complex.Ch21.AlgebraicCovering.local_branches_type := by
  intro P d hP hdeg hd a ha
  obtain ⟨b, r, f, V, hr, hball, hV, hdisj, hf, hlocal, hall⟩ :=
    branch_data P d hP hdeg hd a ha
  exact ⟨{
    radius := r
    radius_pos := hr
    base_subset := hball
    branch := f
    V := V
    open_V := fun i => (hV i).1
    center_mem := fun i => by rw [(hf i).2.1]; exact (hV i).2
    disjoint := hdisj
    holomorphic := fun i => (hf i).1
    mapsTo := fun i => (hf i).2.2
    unique := hlocal
    exhaustive := fun z hz => (hall z hz).2.2
    injective := fun z hz => (hall z hz).2.1
  }⟩

/-- The fiber of the literal projection is equivalent to the original polynomial roots. -/
def projectionFiberEquivRoots (P : Polynomial (Polynomial ℂ)) (a : Base P) :
    (projection P ⁻¹' {a}) ≃ {w : ℂ // (fiber P a).eval w = 0} where
  toFun x := ⟨x.val.val.2, by
    have hx : projection P x.val = a := x.property
    have hz := congrArg Subtype.val hx
    simpa only [projection] using hz ▸ x.val.property.2⟩
  invFun w := ⟨⟨((a : ℂ), w.val), a.property, w.property⟩, rfl⟩
  left_inv x := by
    have hx : projection P x.val = a := x.property
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val hx).symm rfl
  right_inv w := rfl

lemma fiber_cardinality (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (a : Base P) : Nonempty ((projection P ⁻¹' {a}) ≃ Fin d) := by
  obtain ⟨e⟩ := fiber_root_equiv P d hP hdeg hd a a.property
  exact ⟨(projectionFiberEquivRoots P a).trans e⟩

end D12Complex.AlgebraicCovering

noncomputable section
open Set Topology
open scoped Topology
namespace D12Complex.AlgebraicCovering
abbrev Poly := Polynomial (Polynomial ℂ)
def sheet (P : Poly) (U V : Set ℂ) : Set (Curve P) := {x | x.val.1 ∈ U ∧ x.val.2 ∈ V}
def baseU (P : Poly) (U : Set ℂ) : Set (Base P) := {z | (z:ℂ) ∈ U}
lemma sheet_open (P : Poly) {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) :
  IsOpen (sheet P U V) := by
  exact (hU.preimage (continuous_subtype_val.fst)).inter (hV.preimage (continuous_subtype_val.snd))
lemma baseU_open (P : Poly) {U : Set ℂ} (hU : IsOpen U) : IsOpen (baseU P U) :=
  hU.preimage continuous_subtype_val

def graphHomeomorph (P : Poly) (U V : Set ℂ) (f : ℂ → ℂ)
    (hUΩ : U ⊆ baseSet P) (hf : ContinuousOn f U) (hmaps : MapsTo f U V)
    (hroot : ∀ z ∈ U, (fiber P z).eval (f z) = 0)
    (hunique : ∀ z ∈ U, ∀ w ∈ V, (fiber P z).eval w = 0 → w = f z) :
    sheet P U V ≃ₜ baseU P U where
  toFun x := ⟨⟨x.val.val.1,x.val.property.1⟩,x.property.1⟩
  invFun z := ⟨⟨((z.val:ℂ),f z.val),hUΩ z.property,hroot _ z.property⟩,z.property,hmaps z.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change (x.val.val.1, f x.val.val.1) = x.val.val
    apply Prod.ext
    · rfl
    · exact (hunique _ x.property.1 _ x.property.2 x.val.property.2).symm
  right_inv z := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).fst.subtype_mk _).subtype_mk _
  continuous_invFun := by
    have hc : Continuous (fun z : baseU P U => f (z.val:ℂ)) := by
      exact hf.comp_continuous ((continuous_subtype_val.comp continuous_subtype_val)) (fun z => z.property)
    exact (((continuous_subtype_val.comp continuous_subtype_val).prodMk hc).subtype_mk _).subtype_mk _

theorem covering_of_localGraphs (P : Poly) (d : ℕ)
    (hlocal : ∀ a : Base P, ∃ (U : Set ℂ) (f : Fin d → ℂ → ℂ) (V : Fin d → Set ℂ),
      (a:ℂ) ∈ U ∧ IsOpen U ∧ U ⊆ baseSet P ∧
      (∀ i, IsOpen (V i)) ∧ Pairwise (fun i j => Disjoint (V i) (V j)) ∧
      (∀ i, ContinuousOn (f i) U ∧ MapsTo (f i) U (V i)) ∧
      (∀ z ∈ U, ∀ i, (fiber P z).eval (f i z) = 0) ∧
      (∀ z ∈ U, ∀ i, ∀ w ∈ V i, (fiber P z).eval w = 0 → w = f i z) ∧
      (∀ z ∈ U, ∀ w, (fiber P z).eval w = 0 → ∃ i, w = f i z)) :
    D12Complex.Ch20.IsCovering (projection P) := by
  intro a
  obtain ⟨U,f,V,haU,hU,hUΩ,hV,hdisj,hf,hroot,hunique,hall⟩ := hlocal a
  refine ⟨baseU P U,haU,baseU_open P hU,Set.range (fun i => sheet P U (V i)),?_,?_,?_,?_⟩
  · rintro _ ⟨i,rfl⟩
    exact sheet_open P hU (hV i)
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ hneq
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hneq rfl
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact Set.disjoint_left.mp (hdisj hij) hxi.2 hxj.2
  · ext x
    constructor
    · intro hx
      obtain ⟨W,⟨i,rfl⟩,hx⟩ := Set.mem_sUnion.mp hx
      exact hx.1
    · intro hx
      obtain ⟨i,hi⟩ := hall x.val.1 hx x.val.2 x.property.2
      apply Set.mem_sUnion.mpr
      refine ⟨sheet P U (V i),⟨i,rfl⟩,hx,?_⟩
      rw [hi]
      exact (hf i).2 hx
  · rintro _ ⟨i,rfl⟩
    refine ⟨graphHomeomorph P U (V i) (f i) hUΩ (hf i).1 (hf i).2
      (fun z hz => hroot z hz i) (fun z hz w hw => hunique z hz i w hw),?_⟩
    intro x
    rfl

def graphChart (P : Poly) (U V : Set ℂ) (f : ℂ → ℂ) (x₀ : Curve P)
    (hU : IsOpen U) (hV : IsOpen V)
    (hUΩ : U ⊆ baseSet P) (hf : ContinuousOn f U) (hmaps : MapsTo f U V)
    (hroot : ∀ z ∈ U, (fiber P z).eval (f z) = 0)
    (hunique : ∀ z ∈ U, ∀ w ∈ V, (fiber P z).eval w = 0 → w = f z) :
    OpenPartialHomeomorph (Curve P) ℂ := by
  classical
  exact {
  toFun x := x.val.1
  invFun z := if hz : z ∈ U then ⟨(z,f z),hUΩ hz,hroot z hz⟩ else x₀
  source := sheet P U V
  target := U
  map_source' x hx := hx.1
  map_target' z hz := by
    simp only [dite_eq_left hz]
    exact ⟨hz,hmaps hz⟩
  left_inv' x hx := by
    simp only [dite_eq_left hx.1]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (hunique _ hx.1 _ hx.2 x.property.2).symm
  right_inv' z hz := by simp only [dite_eq_left hz]
  continuousOn_toFun := continuous_subtype_val.fst.continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun z : U => f (z:ℂ)) := hf.domRestrict
    have hgraph : Continuous (fun z : U => (⟨((z:ℂ),f z),hUΩ z.property,hroot _ z.property⟩ : Curve P)) :=
      (continuous_subtype_val.prodMk hc).subtype_mk _
    convert hgraph using 1
    funext z
    simp [Set.domRestrict, z.property]
  open_source := sheet_open P hU hV
  open_target := hU }

theorem covering_of_local_branches (P : Poly) (d : ℕ)
    (hlocal : ∀ a ∈ baseSet P, Nonempty (LocalBranches P d a)) :
    D12Complex.Ch20.IsCovering (projection P) := by
  classical
  apply covering_of_localGraphs P d
  intro a
  let L := Classical.choice (hlocal (a:ℂ) a.property)
  refine ⟨Metric.ball (a:ℂ) L.radius,L.branch,L.V,Metric.mem_ball_self L.radius_pos,
    Metric.isOpen_ball,L.base_subset,L.open_V,L.disjoint,?_,?_,?_,?_⟩
  · intro i
    exact ⟨fun z hz => ((L.holomorphic i).2 z hz).continuousAt.continuousWithinAt,L.mapsTo i⟩
  · intro z hz i
    exact (L.unique z hz i _ (L.mapsTo i hz)).mpr rfl
  · intro z hz i w hw hroot
    exact (L.unique z hz i w hw).mp hroot
  · intro z hz w hroot
    exact (L.exhaustive z hz w).mp hroot

lemma graphChart_holomorphic_snd (P : Poly) (U V : Set ℂ) (f : ℂ → ℂ) (x₀ : Curve P)
    (hU : IsOpen U) (hV : IsOpen V)
    (hUΩ : U ⊆ baseSet P) (hf : ContinuousOn f U) (hmaps : MapsTo f U V)
    (hroot : ∀ z ∈ U, (fiber P z).eval (f z) = 0)
    (hunique : ∀ z ∈ U, ∀ w ∈ V, (fiber P z).eval w = 0 → w = f z)
    (hhol : HolomorphicOn U f) :
    HolomorphicOn (graphChart P U V f x₀ hU hV hUΩ hf hmaps hroot hunique).target
      (fun z => ((graphChart P U V f x₀ hU hV hUΩ hf hmaps hroot hunique).symm z).val.2) := by
  classical
  refine ⟨hU,?_⟩
  intro z hz
  apply (hhol.2 z hz).congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hz] with y hy
  simp [graphChart, hy]

lemma projection_charts_compatible (P : Poly)
    (e f : Surfaces.ComplexChart (Curve P))
    (he : ∀ x ∈ e.val.source, e.val x = x.val.1)
    (hf : ∀ x ∈ f.val.source, f.val x = x.val.1) :
    Surfaces.CompatibleCharts e f := by
  have hid (e f : Surfaces.ComplexChart (Curve P))
      (he : ∀ x ∈ e.val.source, e.val x = x.val.1)
      (hf : ∀ x ∈ f.val.source, f.val x = x.val.1) :
      ∀ z ∈ (e.val.symm.trans f.val).source, (e.val.symm.trans f.val) z = z := by
    intro z hz
    change f.val (e.val.symm z) = z
    calc
      _ = (e.val.symm z).val.1 := hf _ hz.2
      _ = e.val (e.val.symm z) := (he _ (e.val.map_target hz.1)).symm
      _ = z := e.val.right_inv hz.1
  let t := e.val.symm.trans f.val
  refine ⟨⟨t.open_source,?_⟩,⟨t.open_target,?_⟩,t.mapsTo,t.symm.mapsTo,t.leftInvOn,t.rightInvOn⟩
  · intro z hz
    apply differentiableAt_id.congr_of_eventuallyEq
    filter_upwards [t.open_source.mem_nhds hz] with y hy
    exact (hid e f he hf y hy)
  · intro z hz
    apply differentiableAt_id.congr_of_eventuallyEq
    filter_upwards [t.open_target.mem_nhds hz] with y hy
    exact (hid f e hf he y hy)


theorem complex_atlas_of_local_branches (P : Poly) (d : ℕ)
    (hlocal : ∀ a ∈ baseSet P, Nonempty (LocalBranches P d a)) :
    T2Space (Curve P) ∧ SecondCountableTopology (Curve P) ∧
      ∃ A : Set (Surfaces.ComplexChart (Curve P)), Surfaces.IsAtlas A ∧
        ∀ e ∈ A,
          (∀ x ∈ e.val.source, e.val x = x.val.1) ∧
          HolomorphicOn e.val.target (fun z => (e.val.symm z).val.2) := by
  classical
  refine ⟨inferInstance,inferInstance,?_⟩
  let A : Set (Surfaces.ComplexChart (Curve P)) := {e |
    (∀ x ∈ e.val.source, e.val x = x.val.1) ∧
      HolomorphicOn e.val.target (fun z => (e.val.symm z).val.2)}
  refine ⟨A,⟨?_,?_⟩,fun e he => he⟩
  · intro x
    let L := Classical.choice (hlocal x.val.1 x.property.1)
    have ha : x.val.1 ∈ Metric.ball x.val.1 L.radius := Metric.mem_ball_self L.radius_pos
    obtain ⟨i,hi⟩ := (L.exhaustive _ ha x.val.2).mp x.property.2
    have hc : ContinuousOn (L.branch i) (Metric.ball x.val.1 L.radius) :=
      fun z hz => ((L.holomorphic i).2 z hz).continuousAt.continuousWithinAt
    have hroot : ∀ z ∈ Metric.ball x.val.1 L.radius, (fiber P z).eval (L.branch i z) = 0 :=
      fun z hz => (L.unique z hz i _ (L.mapsTo i hz)).mpr rfl
    have hunique : ∀ z ∈ Metric.ball x.val.1 L.radius, ∀ w ∈ L.V i,
        (fiber P z).eval w = 0 → w = L.branch i z :=
      fun z hz w hw => (L.unique z hz i w hw).mp
    let e := graphChart P (Metric.ball x.val.1 L.radius) (L.V i) (L.branch i) x
      Metric.isOpen_ball (L.open_V i) L.base_subset hc (L.mapsTo i) hroot hunique
    have hd : IsDomain e.target :=
      ⟨⟨x.val.1,ha⟩,Metric.isOpen_ball,Metric.isPreconnected_ball⟩
    let c : Surfaces.ComplexChart (Curve P) := ⟨e,hd⟩
    refine ⟨c,?_,?_
    ⟩
    · refine ⟨fun y hy => rfl,?_⟩
      exact graphChart_holomorphic_snd P (Metric.ball x.val.1 L.radius) (L.V i) (L.branch i) x
        Metric.isOpen_ball (L.open_V i) L.base_subset hc (L.mapsTo i) hroot hunique (L.holomorphic i)
    · change x.val.1 ∈ Metric.ball x.val.1 L.radius ∧ x.val.2 ∈ L.V i
      refine ⟨ha,?_⟩
      rw [hi]
      exact L.mapsTo i ha
  · intro e he f hf
    exact projection_charts_compatible P e f he.1 hf.1

end D12Complex.AlgebraicCovering


open Set Filter unitInterval
open scoped Topology
noncomputable section
namespace D12Complex.AlgebraicCovering

theorem germ_eq_of_local_zero_graph
    (F : ℂ → ℂ → ℂ) (a : ℂ) (U V : Set ℂ) (b : ℂ → ℂ)
    (hU : IsOpen U) (haU : a ∈ U) (hV : IsOpen V)
    (hunique : ∀ z ∈ U, ∀ w ∈ V, F z w = 0 ↔ w = b z)
    (g h : HolomorphicGerm a)
    (hg : ∃ (W : Set ℂ) (f : ℂ → ℂ) (hf : HolomorphicOn W f) (ha : a ∈ W),
      HolomorphicGerm.ofFunction f hf ha = g ∧ ∀ z ∈ W, F z (f z) = 0)
    (hh : ∃ (W : Set ℂ) (f : ℂ → ℂ) (hf : HolomorphicOn W f) (ha : a ∈ W),
      HolomorphicGerm.ofFunction f hf ha = h ∧ ∀ z ∈ W, F z (f z) = 0)
    (hgv : g.value ∈ V) (hhv : h.value ∈ V) : g = h := by
  obtain ⟨G, f, hf, haf, hfg, hfzero⟩ := hg
  obtain ⟨H, k, hk, hak, hkh, hkzero⟩ := hh
  have hfa : f a = g.value := by rw [← hfg]; rfl
  have hka : k a = h.value := by rw [← hkh]; rfl
  have hfV : ∀ᶠ z in 𝓝 a, f z ∈ V :=
    ((hf.2 a haf).continuousAt).preimage_mem_nhds (hV.mem_nhds (hfa ▸ hgv))
  have hkV : ∀ᶠ z in 𝓝 a, k z ∈ V :=
    ((hk.2 a hak).continuousAt).preimage_mem_nhds (hV.mem_nhds (hka ▸ hhv))
  have heq : f =ᶠ[𝓝 a] k := by
    filter_upwards [hU.mem_nhds haU, hf.1.mem_nhds haf, hk.1.mem_nhds hak, hfV, hkV]
      with z hzU hzG hzH hzV hzV'
    exact ((hunique z hzU (f z) hzV).mp (hfzero z hzG)).trans
      ((hunique z hzU (k z) hzV').mp (hkzero z hzH)).symm
  calc
    g = HolomorphicGerm.ofFunction f hf haf := hfg.symm
    _ = HolomorphicGerm.ofFunction k hk hak :=
      D12Complex.germOfFunction_congr a G H f k hf hk haf hak heq
    _ = h := hkh


theorem rootGerm_value_root {P : Polynomial (Polynomial ℂ)} {a : ℂ}
    (g : RootGerm P a) : (fiber P a).eval g.val.value = 0 := by
  obtain ⟨U, f, hf, ha, heq, hzero⟩ := g.property
  rw [← heq]
  exact hzero a ha

def localBranchGerm {P : Polynomial (Polynomial ℂ)} {d : ℕ} {a z : ℂ}
    (L : LocalBranches P d a) (i : Fin d) (hz : z ∈ Metric.ball a L.radius) :
    RootGerm P z :=
  ⟨HolomorphicGerm.ofFunction (L.branch i) (L.holomorphic i) hz,
    Metric.ball a L.radius, L.branch i, L.holomorphic i, hz, rfl,
    fun w hw => (L.unique w hw i (L.branch i w) (L.mapsTo i hw)).mpr rfl⟩

theorem rootGerm_ext {P : Polynomial (Polynomial ℂ)} {d : ℕ} {a : ℂ}
    (L : LocalBranches P d a) (g h : RootGerm P a)
    (hvalue : g.val.value = h.val.value) : g = h := by
  have ha : a ∈ Metric.ball a L.radius := Metric.mem_ball_self L.radius_pos
  obtain ⟨i, hi⟩ := (L.exhaustive a ha g.val.value).mp (rootGerm_value_root g)
  have hgV : g.val.value ∈ L.V i := hi ▸ L.center_mem i
  have hhV : h.val.value ∈ L.V i := hvalue ▸ hgV
  apply Subtype.ext
  exact germ_eq_of_local_zero_graph (fun z w => (fiber P z).eval w) a
    (Metric.ball a L.radius) (L.V i) (L.branch i)
    Metric.isOpen_ball ha (L.open_V i)
    (fun z hz w hw => L.unique z hz i w hw) g.val h.val g.property h.property hgV hhV

def rootGermToFiber {P : Polynomial (Polynomial ℂ)} (a : Base P)
    (g : RootGerm P (a : ℂ)) : projection P ⁻¹' {a} :=
  ⟨⟨((a : ℂ), g.val.value), a.property, rootGerm_value_root g⟩, rfl⟩

def rootGermFiberEquiv {P : Polynomial (Polynomial ℂ)} {d : ℕ}
    (a : Base P) (L : LocalBranches P d (a : ℂ)) :
    RootGerm P (a : ℂ) ≃ (projection P ⁻¹' {a}) := by
  apply Equiv.ofBijective (rootGermToFiber a)
  constructor
  · intro g h heq
    apply rootGerm_ext L g h
    exact congrArg (fun e => e.val.val.2) heq
  · intro e
    have he : e.val.val.1 = (a : ℂ) := congrArg Subtype.val e.property
    have hzero : (fiber P (a : ℂ)).eval e.val.val.2 = 0 := he ▸ e.val.property.2
    have ha : (a : ℂ) ∈ Metric.ball (a : ℂ) L.radius := Metric.mem_ball_self L.radius_pos
    obtain ⟨i, hi⟩ := (L.exhaustive (a : ℂ) ha e.val.val.2).mp hzero
    refine ⟨localBranchGerm L i ha, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext he.symm hi.symm

@[simp] theorem rootGermFiberEquiv_value {P : Polynomial (Polynomial ℂ)} {d : ℕ}
    (a : Base P) (L : LocalBranches P d (a : ℂ)) (g : RootGerm P (a : ℂ)) :
    (rootGermFiberEquiv a L g).val.val.2 = g.val.value := rfl

theorem root_germs_from_local_branches
    (hlocal : Specs.D12Complex.Ch21.AlgebraicCovering.local_branches_type) :
    Specs.D12Complex.Ch21.AlgebraicCovering.root_germs_type := by
  intro P d hP hd hpos a
  exact ⟨rootGermFiberEquiv a (Classical.choice (hlocal P d hP hd hpos a a.property)),
    fun _ => rfl⟩


@[simp] theorem holomorphicGerm_value_cast {a b : ℂ} (h : a = b)
    (g : HolomorphicGerm a) : (h ▸ g).value = g.value := by
  cases h
  rfl

@[simp] theorem rootGerm_value_cast {P : Polynomial (Polynomial ℂ)} {a b : ℂ}
    (h : a = b) (g : RootGerm P a) : (h ▸ g).val.value = g.val.value := by
  cases h
  rfl

theorem locallyRepresented_of_root_values
    {P : Polynomial (Polynomial ℂ)} {d : ℕ}
    (hlocal : ∀ a ∈ baseSet P, Nonempty (LocalBranches P d a))
    (γ w : I → ℂ) (hγ : Continuous γ) (hw : Continuous w)
    (hγΩ : ∀ t, γ t ∈ baseSet P) (Φ : GermFamily γ)
    (hroot : ∀ t, IsRootGerm P (γ t) (Φ t))
    (hvalue : ∀ t, (Φ t).value = w t) : LocallyRepresented γ Φ := by
  intro s
  let L := Classical.choice (hlocal (γ s) (hγΩ s))
  have hsball : γ s ∈ Metric.ball (γ s) L.radius := Metric.mem_ball_self L.radius_pos
  have hsroot : (fiber P (γ s)).eval (w s) = 0 := by
    rw [← hvalue s]
    exact rootGerm_value_root ⟨Φ s, hroot s⟩
  obtain ⟨i, hi⟩ := (L.exhaustive (γ s) hsball (w s)).mp hsroot
  let J : Set I := γ ⁻¹' Metric.ball (γ s) L.radius ∩ w ⁻¹' L.V i
  have hJ : IsOpen J := (Metric.isOpen_ball.preimage hγ).inter ((L.open_V i).preimage hw)
  have hsJ : s ∈ J := ⟨hsball, show w s ∈ L.V i from hi ▸ L.center_mem i⟩
  refine ⟨Metric.ball (γ s) L.radius, L.branch i, J, hJ, hsJ, L.holomorphic i, ?_⟩
  intro t ht
  refine ⟨ht.1, ?_⟩
  let k := localBranchGerm L i ht.1
  have heq : Φ t = k.val := by
    apply germ_eq_of_local_zero_graph (fun z w => (fiber P z).eval w) (γ t)
      (Metric.ball (γ s) L.radius) (L.V i) (L.branch i)
      Metric.isOpen_ball ht.1 (L.open_V i)
      (fun z hz w hw => L.unique z hz i w hw) (Φ t) k.val (hroot t) k.property
    · rw [hvalue t]
      exact ht.2
    · exact L.mapsTo i ht.1
  exact congrArg Subtype.val heq

/-- A continuous selection of polynomial root values determines an actual
locally represented holomorphic germ continuation, including both endpoints. -/
theorem continuation_of_root_selection
    {P : Polynomial (Polynomial ℂ)} {d : ℕ}
    (hΩ : IsDomain (baseSet P))
    (hlocal : ∀ a ∈ baseSet P, Nonempty (LocalBranches P d a))
    (γ w : I → ℂ) (hγ : Continuous γ) (hw : Continuous w)
    (hγΩ : ∀ t, γ t ∈ baseSet P)
    (hzero : ∀ t, (fiber P (γ t)).eval (w t) = 0)
    (g : RootGerm P (γ 0)) (hinit : w 0 = g.val.value) :
    ∃ Φ : GermFamily γ,
      IsContinuation (baseSet P) γ g.val Φ ∧
      (∀ t, IsRootGerm P (γ t) (Φ t)) ∧
      ∀ t, (Φ t).value = w t := by
  let L : ∀ t : I, LocalBranches P d (γ t) :=
    fun t => Classical.choice (hlocal (γ t) (hγΩ t))
  let a : I → Base P := fun t => ⟨γ t, hγΩ t⟩
  let e : ∀ t : I, projection P ⁻¹' {a t} :=
    fun t => ⟨⟨(γ t, w t), hγΩ t, hzero t⟩, rfl⟩
  let G : ∀ t : I, RootGerm P (γ t) :=
    fun t => (rootGermFiberEquiv (a t) (L t)).symm (e t)
  have hvalue (t : I) : (G t).val.value = w t := by
    have he := congrArg (fun q => q.val.val.2)
      ((rootGermFiberEquiv (a t) (L t)).apply_symm_apply (e t))
    exact (rootGermFiberEquiv_value (a t) (L t) (G t)).symm.trans he
  let Φ : GermFamily γ := fun t => (G t).val
  have hroot : ∀ t, IsRootGerm P (γ t) (Φ t) := fun t => (G t).property
  have hg : Φ 0 = g.val := by
    exact congrArg Subtype.val (rootGerm_ext (L 0) (G 0) g ((hvalue 0).trans hinit))
  refine ⟨Φ, ⟨hΩ, hγ, hγΩ, hg, ?_⟩, hroot, hvalue⟩
  exact locallyRepresented_of_root_values hlocal γ w hγ hw hγΩ Φ hroot hvalue


@[simp] theorem rootGerm_cast_val {P : Polynomial (Polynomial ℂ)} {a b : ℂ}
    (h : a = b) (g : RootGerm P a) : (h ▸ g).val = (h ▸ g.val) := by
  cases h
  rfl

theorem branch_continuation_from_covering
    (hbase : Specs.D12Complex.Ch21.AlgebraicCovering.base_domain_type)
    (hlocal : Specs.D12Complex.Ch21.AlgebraicCovering.local_branches_type)
    (hcover : Specs.D12Complex.Ch21.AlgebraicCovering.covering_type) :
    Specs.D12Complex.Ch21.AlgebraicCovering.branch_continuation_type := by
  intro P d hP hd hpos a b γ g
  let e₀ : Curve P := (rootGermToFiber a g).val
  have he₀ : projection P e₀ = γ 0 := by
    change a = γ 0
    exact γ.source.symm
  obtain ⟨Γ, hΓ, _⟩ := Ch20.CoveringPaths.path_lifting
    (projection P) (hcover P d hP hd hpos).1 γ γ.continuous e₀ he₀
  have hproj (t : I) : (Γ t).val.1 = (γ t : ℂ) :=
    congrArg Subtype.val (congrFun hΓ.2.2 t)
  have hzero (t : I) : (fiber P (γ t : ℂ)).eval (Γ t).val.2 = 0 := by
    rw [← hproj t]
    exact (Γ t).property.2
  let g₀ : RootGerm P (γ 0 : ℂ) :=
    (congrArg Subtype.val γ.source).symm ▸ g
  have hinit : (Γ 0).val.2 = g₀.val.value := by
    rw [hΓ.2.1]
    simp only [g₀, rootGerm_value_cast]
    rfl
  obtain ⟨Φ, hΦ, hr, _⟩ := continuation_of_root_selection
    (hbase P d hP hd hpos) (hlocal P d hP hd hpos)
    (fun t => (γ t : ℂ)) (fun t => (Γ t).val.2)
    (continuous_subtype_val.comp γ.continuous)
    (continuous_snd.comp (continuous_subtype_val.comp hΓ.1))
    (fun t => (γ t).property) hzero g₀ hinit
  refine ⟨Φ, ?_, hr⟩
  simpa only [g₀, rootGerm_cast_val] using hΦ

end D12Complex.AlgebraicCovering

open unitInterval
noncomputable section
namespace D12Complex.AlgebraicCovering
universe u v
variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B} (cov : IsCoveringMap p)

def fiberTransport {a b : B} (γ : Path a b) :
    (p ⁻¹' {a}) ≃ (p ⁻¹' {b}) :=
  Equiv.ofBijective (cov.monodromy (.mk γ)) (cov.monodromy_bijective (.mk γ))

@[simp] theorem fiberTransport_apply {a b : B} (γ : Path a b) (e : p ⁻¹' {a}) :
    fiberTransport cov γ e = cov.monodromy (.mk γ) e := rfl

theorem fiberTransport_homotopic {a b : B} (γ η : Path a b) (h : γ.Homotopic η) :
    fiberTransport cov γ = fiberTransport cov η := by
  have hh : Path.Homotopic.Quotient.mk γ = .mk η := Path.Homotopic.Quotient.eq.mpr h
  unfold fiberTransport
  simp only [hh]

theorem fiberTransport_trans {a b c : B} (γ : Path a b) (η : Path b c)
    (e : p ⁻¹' {a}) :
    fiberTransport cov (γ.trans η) e = fiberTransport cov η (fiberTransport cov γ e) :=
  cov.monodromy_trans_apply (.mk γ) (.mk η) e

theorem fiberTransport_symm_apply {a b : B} (γ : Path a b) (e : p ⁻¹' {b}) :
    fiberTransport cov γ.symm e = (fiberTransport cov γ).symm e := by
  apply (fiberTransport cov γ).injective
  rw [Equiv.apply_symm_apply]
  change cov.monodromy (.mk γ) (cov.monodromy (.mk γ.symm) e) = e
  rw [← cov.monodromy_trans_apply, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.symm_trans, cov.monodromy_refl]
  rfl

def loopPermutation {a : B} (γ : Path a a) : Equiv.Perm (p ⁻¹' {a}) :=
  fiberTransport cov γ

theorem loopPermutation_symm {a : B} (γ : Path a a) :
    loopPermutation cov γ.symm = (loopPermutation cov γ)⁻¹ := by
  apply Equiv.ext
  intro e
  exact fiberTransport_symm_apply cov γ e

theorem loopPermutation_trans {a : B} (γ η : Path a a) :
    loopPermutation cov (γ.trans η) = loopPermutation cov η * loopPermutation cov γ := by
  apply Equiv.ext
  intro e
  exact fiberTransport_trans cov γ η e

end D12Complex.AlgebraicCovering

namespace D12Complex.AlgebraicCovering
variable {G F : Type*}
def germPermutation (e : G ≃ F) (perm : Equiv.Perm F) : Equiv.Perm G :=
  (e.trans perm).trans e.symm
@[simp] theorem germPermutation_apply (e : G ≃ F) (perm : Equiv.Perm F) (g : G) :
    germPermutation e perm g = e.symm (perm (e g)) := rfl
lemma germPermutation_mul (e : G ≃ F) (perm perm2 : Equiv.Perm F) :
    germPermutation e (perm * perm2) = germPermutation e perm * germPermutation e perm2 := by
  apply Equiv.ext
  intro g
  simp [germPermutation]
lemma germPermutation_inv (e : G ≃ F) (perm : Equiv.Perm F) :
    germPermutation e perm⁻¹ = (germPermutation e perm)⁻¹ := by
  apply Equiv.ext
  intro g
  rfl
end D12Complex.AlgebraicCovering
namespace D12Complex.AlgebraicCovering

theorem covering : Specs.D12Complex.Ch21.AlgebraicCovering.covering_type := by
  intro P d hP hd hpos
  exact ⟨covering_of_local_branches P d (local_branches P d hP hd hpos),
    fiber_cardinality P d hP hd hpos⟩

theorem complex_atlas : Specs.D12Complex.Ch21.AlgebraicCovering.complex_atlas_type := by
  intro P d hP hd hpos
  exact complex_atlas_of_local_branches P d (local_branches P d hP hd hpos)

theorem root_germs : Specs.D12Complex.Ch21.AlgebraicCovering.root_germs_type :=
  root_germs_from_local_branches local_branches

theorem branch_continuation : Specs.D12Complex.Ch21.AlgebraicCovering.branch_continuation_type :=
  branch_continuation_from_covering base_domain local_branches covering

end D12Complex.AlgebraicCovering

open Set Filter unitInterval
open scoped Topology
noncomputable section
namespace D12Complex.AlgebraicCovering

theorem monodromy_from_covering
    (hbase : Specs.D12Complex.Ch21.AlgebraicCovering.base_domain_type)
    (hlocal : Specs.D12Complex.Ch21.AlgebraicCovering.local_branches_type)
    (hcover : Specs.D12Complex.Ch21.AlgebraicCovering.covering_type) :
    Specs.D12Complex.Ch21.AlgebraicCovering.monodromy_type := by
  intro P d hP hd hpos a
  let cov := Ch20.CoveringPaths.covering_bridge (projection P) (hcover P d hP hd hpos).1
  let L := Classical.choice (hlocal P d hP hd hpos (a : ℂ) a.property)
  let e := rootGermFiberEquiv a L
  let M : Path a a → Equiv.Perm (RootGerm P (a : ℂ)) :=
    fun γ => germPermutation e (loopPermutation cov γ)
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · intro γ η h
    change germPermutation e (fiberTransport cov γ) = germPermutation e (fiberTransport cov η)
    rw [fiberTransport_homotopic cov γ η h]
  · intro γ
    change germPermutation e (loopPermutation cov γ.symm) = (germPermutation e (loopPermutation cov γ))⁻¹
    rw [loopPermutation_symm, germPermutation_inv]
  · intro γ η
    change germPermutation e (loopPermutation cov (γ.trans η)) =
      germPermutation e (loopPermutation cov η) * germPermutation e (loopPermutation cov γ)
    rw [loopPermutation_trans, germPermutation_mul]
  · intro γ g
    let Γ := cov.liftPath γ (e g).val (γ.source.trans (e g).property.symm)
    have hΓ : Continuous Γ := Γ.continuous
    have hΓzero : Γ 0 = (e g).val := cov.liftPath_zero ..
    have hΓproj : projection P ∘ Γ = γ := cov.liftPath_lifts ..
    have hproj (t : I) : (Γ t).val.1 = (γ t : ℂ) :=
      congrArg Subtype.val (congrFun hΓproj t)
    have hzero (t : I) : (fiber P (γ t : ℂ)).eval (Γ t).val.2 = 0 := by
      rw [← hproj t]
      exact (Γ t).property.2
    let g₀ : RootGerm P (γ 0 : ℂ) :=
      (congrArg Subtype.val γ.source).symm ▸ g
    have hinit : (Γ 0).val.2 = g₀.val.value := by
      rw [hΓzero]
      simp only [g₀, rootGerm_value_cast]
      exact rootGermFiberEquiv_value a L g
    obtain ⟨Φ, hΦ, hr, hvalue⟩ := continuation_of_root_selection
      (hbase P d hP hd hpos) (hlocal P d hP hd hpos)
      (fun t => (γ t : ℂ)) (fun t => (Γ t).val.2)
      (continuous_subtype_val.comp γ.continuous)
      (continuous_snd.comp (continuous_subtype_val.comp hΓ))
      (fun t => (γ t).property) hzero g₀ hinit
    refine ⟨Φ, ?_, hr, ?_⟩
    · simpa only [g₀, rootGerm_cast_val] using hΦ
    · let g₁ : RootGerm P (a : ℂ) :=
        congrArg Subtype.val γ.target ▸ (⟨Φ 1, hr 1⟩ : RootGerm P (γ 1 : ℂ))
      have hEnd : (fiberTransport cov γ (e g)).val = Γ 1 :=
        cov.coe_monodromy_mk γ (e g)
      have hM : e (M γ g) = fiberTransport cov γ (e g) := by
        simp only [M, germPermutation_apply, Equiv.apply_symm_apply]
        rfl
      have hvalues : g₁.val.value = (M γ g).val.value := by
        have hc : g₁.val.value = (Φ 1).value :=
          rootGerm_value_cast (congrArg Subtype.val γ.target)
            (⟨Φ 1, hr 1⟩ : RootGerm P (γ 1 : ℂ))
        rw [hc, hvalue 1]
        have hevalue := rootGermFiberEquiv_value a L (M γ g)
        change (e (M γ g)).val.val.2 = (M γ g).val.value at hevalue
        rw [hM, hEnd] at hevalue
        exact hevalue
      have heq : g₁ = M γ g := rootGerm_ext L g₁ (M γ g) hvalues
      exact (rootGerm_cast_val (congrArg Subtype.val γ.target)
        (⟨Φ 1, hr 1⟩ : RootGerm P (γ 1 : ℂ))).symm.trans (congrArg Subtype.val heq)

end D12Complex.AlgebraicCovering

namespace D12Complex.AlgebraicCovering
/-- The based loop action on all actual algebraic branch germs. -/
theorem monodromy : Specs.D12Complex.Ch21.AlgebraicCovering.monodromy_type :=
  monodromy_from_covering base_domain local_branches covering
end D12Complex.AlgebraicCovering
