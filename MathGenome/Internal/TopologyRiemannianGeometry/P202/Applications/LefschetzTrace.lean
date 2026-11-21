import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Applications.LefschetzTrace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! Hopf trace formula (paper.tex, 2916–2923). We first split invariant-subspace
traces, identify the two quotients equivariantly, and then telescope the boundary
traces. The result uses the categorical homology map of the same chain complex. -/

open CategoryTheory
open HomologicalComplex hiding cycles
open scoped BigOperators

universe u v
noncomputable section
namespace P202.LefschetzTrace
open P202Specs.LefschetzTrace

/-- Splitting the quotient as vector spaces suffices; the splitting need not
commute with the endomorphism. -/
theorem invariant_trace {K : Type u} [Field K] : InvariantTraceType.{u,v} (K := K) := by
  intro V _ _ _ f p hp
  obtain ⟨s, hs⟩ := p.mkQ.exists_rightInverse_of_surjective p.range_mkQ
  let r : V →ₗ[K] p := (LinearMap.id - s.comp p.mkQ).codRestrict p (by
    intro x
    apply (Submodule.Quotient.mk_eq_zero p).mp
    change p.mkQ (x - s (p.mkQ x)) = 0
    rw [map_sub, show p.mkQ (s (p.mkQ x)) = p.mkQ x from congr($hs (p.mkQ x))]
    exact sub_self _)
  have hdecomp : p.subtype.comp r + s.comp p.mkQ = LinearMap.id := by
    ext x
    change (x - s (p.mkQ x)) + s (p.mkQ x) = x
    abel
  have hleft : r.comp (f.comp p.subtype) = f.restrict hp := by
    ext x
    change f x - s (p.mkQ (f x)) = f x
    rw [show p.mkQ (f x) = 0 from (Submodule.Quotient.mk_eq_zero p).mpr (hp x x.property),
      map_zero, sub_zero]
  have hright : p.mkQ.comp (f.comp s) = p.mapQ p f hp := by
    apply LinearMap.ext
    intro x
    change p.mkQ (f (s x)) = p.mapQ p f hp x
    calc
      _ = p.mapQ p f hp (p.mkQ (s x)) := rfl
      _ = _ := congrArg (p.mapQ p f hp) (show p.mkQ (s x) = x from congr($hs x))
  calc
    LinearMap.trace K V f = LinearMap.trace K V (f.comp (p.subtype.comp r + s.comp p.mkQ)) := by
      rw [hdecomp, LinearMap.comp_id]
    _ = LinearMap.trace K V ((f.comp p.subtype).comp r) +
        LinearMap.trace K V ((f.comp s).comp p.mkQ) := by
      rw [LinearMap.comp_add, map_add, LinearMap.comp_assoc, LinearMap.comp_assoc]
    _ = LinearMap.trace K p (r.comp (f.comp p.subtype)) +
        LinearMap.trace K (V ⧸ p) (p.mkQ.comp (f.comp s)) := by
      rw [LinearMap.trace_comp_comm' r, LinearMap.trace_comp_comm' p.mkQ]
    _ = _ := by rw [hleft, hright]

/-- Equivariantly isomorphic endomorphisms have equal traces. -/
theorem trace_equivariant {K : Type*} [Field K]
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (h : ∀ x, e (f x) = g (e x)) : LinearMap.trace K V f = LinearMap.trace K W g := by
  have he : e.conj f = g := by
    apply LinearMap.ext
    intro x
    simpa using h (e.symm x)
  rw [← he, LinearMap.trace_conj']

/-- Alternating boundary contributions telescope on any finite interval. -/
theorem alternating_telescope {K : Type*} [Field K] (b : ℤ → K) (a : ℤ) (N : ℕ) :
    (∑ j ∈ Finset.range N, (-1 : K) ^ (a + (j : ℤ)) *
      (b (a + (j : ℤ)) + b (a + (j : ℤ) - 1))) =
    (-1 : K) ^ (a + (N : ℤ) - 1) * b (a + (N : ℤ) - 1) -
      (-1 : K) ^ (a - 1) * b (a - 1) := by
  have hsign (n : ℤ) : (-1 : K) ^ (n - 1) = -((-1 : K) ^ n) := by
    rw [zpow_sub₀ (by simp), zpow_one, div_neg, div_one]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show a + ((N : ℤ) + 1) - 1 = a + (N : ℤ) by omega, hsign]
    ring

section Complex
variable {K : Type u} [Field K] (C : ChainComplex (ModuleCat.{v} K) ℤ) (F : C ⟶ C)

/-- The first isomorphism theorem for the differential, with its chain-map action. -/
theorem boundary_quotient : BoundaryQuotientType C F := by
  intro n
  have hb : boundaries C (n - 1) = LinearMap.range (C.d n (n - 1)).hom := by
    exact congrArg (fun i => LinearMap.range (C.d i (n - 1)).hom)
      (show n - 1 + 1 = n by omega)
  let e := (C.d n (n - 1)).hom.quotKerEquivRange.trans
    (LinearEquiv.ofEq _ _ hb.symm)
  refine ⟨e, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      apply Subtype.ext
      exact congr($(F.comm n (n - 1)) x)

/-- Moving boundaries into the cycle subspace preserves their endomorphism. -/
def boundaryCyclesEquiv (n : ℤ) : boundaryCycles C n ≃ₗ[K] boundaries C n :=
  LinearEquiv.ofBijective
    ((cycles C n).subtype.comp (boundaryCycles C n).subtype |>.codRestrict
      (boundaries C n) (by
        intro x
        obtain ⟨y, hy⟩ := x.property
        exact ⟨y, congrArg Subtype.val hy⟩))
    ⟨by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : boundaries C n => (z : C.X n)) h, by
      rintro ⟨x, y, rfl⟩
      exact ⟨⟨toCycles C n y, ⟨y, rfl⟩⟩, rfl⟩⟩

theorem boundaryCyclesEquiv_comm (n : ℤ) (x : boundaryCycles C n) :
    boundaryCyclesEquiv C n ((onCycles C F n).restrict
      (preserves_boundaryCycles C F n) x) =
      onBoundaries C F n (boundaryCyclesEquiv C n x) := rfl

/-- The kernel/image model and the categorical homology carry the same map. -/
theorem homology_quotient : HomologyQuotientType C F := by
  intro n
  let S := C.sc' (n + 1) n (n - 1)
  let φ : S ⟶ S := (shortComplexFunctor' (ModuleCat K) (ComplexShape.down ℤ)
    (n + 1) n (n - 1)).map F
  let h := S.moduleCatLeftHomologyData
  let γ : ShortComplex.LeftHomologyMapData φ h h :=
    { φK := ModuleCat.ofHom (onCycles C F n)
      φH := ModuleCat.ofHom (onHomology C F n)
      commi := by rfl
      commf' := by
        ext x
        apply Subtype.ext
        exact congr($(F.comm (n + 1) n) x).symm
      commπ := by rfl }
  let i := C.isoSc' (n + 1) n (n - 1) (by simp) (by simp)
  let e₁ := ShortComplex.homologyMapIso i
  let e₂ := S.moduleCatHomologyIso
  refine ⟨(e₁ ≪≫ e₂).toLinearEquiv, ?_⟩
  intro x
  have hn : homologyMap F n ≫ e₁.hom = e₁.hom ≫ ShortComplex.homologyMap φ := by
    change ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap i.hom =
      ShortComplex.homologyMap i.hom ≫ ShortComplex.homologyMap φ
    rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
    have hi : (shortComplexFunctor (ModuleCat K) (ComplexShape.down ℤ) n).map F ≫ i.hom =
        i.hom ≫ φ :=
      (natIsoSc' (ModuleCat K) (ComplexShape.down ℤ) (n + 1) n (n - 1)
        (by simp) (by simp)).hom.naturality F
    exact congrArg (fun f : C.sc n ⟶ S => ShortComplex.homologyMap f) hi

  have hh : ShortComplex.homologyMap φ ≫ e₂.hom =
      e₂.hom ≫ ModuleCat.ofHom (onHomology C F n) := γ.homologyMap_comm
  exact (congr($(hn) x) |> congrArg e₂.hom).trans (congr($(hh) (e₁.hom x)))

variable [∀ n, FiniteDimensional K (C.X n)]

/-- Each chain-group trace is the homology trace plus the adjacent boundary traces. -/
theorem degree_trace : DegreeTraceType C F := by
  intro n
  let hp : ∀ x ∈ cycles C n, (F.f n).hom x ∈ cycles C n :=
    fun x hx => (onCycles C F n ⟨x, hx⟩).property
  have hc := invariant_trace (K := K) (C.X n) (F.f n).hom (cycles C n) hp
  change LinearMap.trace K (C.X n) (F.f n).hom =
    LinearMap.trace K (cycles C n) (onCycles C F n) +
    LinearMap.trace K (C.X n ⧸ cycles C n) ((cycles C n).mapQ _ (F.f n).hom hp) at hc
  have hz := invariant_trace (K := K) (cycles C n) (onCycles C F n)
    (boundaryCycles C n) (preserves_boundaryCycles C F n)
  obtain ⟨eb, _, heb⟩ := boundary_quotient C F n
  have hb := trace_equivariant eb _ _ heb
  have hbc := trace_equivariant (boundaryCyclesEquiv C n) _ _
    (boundaryCyclesEquiv_comm C F n)
  obtain ⟨eh, heh⟩ := homology_quotient C F n
  have hh := trace_equivariant eh _ _ heh
  change LinearMap.trace K (C.homology n) (homologyMap F n).hom =
    LinearMap.trace K (Homology C n) (onHomology C F n) at hh
  rw [hc, hz, hbc, hb]
  change _ = LinearMap.trace K (C.homology n) (homologyMap F n).hom + _ + _
  rw [hh]
  change _ + LinearMap.trace K (Homology C n) (onHomology C F n) + _ = _
  ring

/-- Hopf's trace formula for every finite chain complex and every chain endomorphism. -/
theorem trace_identity : TraceIdentityType C F := by
  intro a N hsupport
  let b (n : ℤ) := LinearMap.trace K (boundaries C n) (onBoundaries C F n)
  have hbottom : b (a - 1) = 0 := by
    let : Subsingleton (C.X (a - 1)) := hsupport _ (Or.inl (by omega))
    have hz : onBoundaries C F (a - 1) = 0 := Subsingleton.elim _ _
    exact (congrArg (LinearMap.trace K _) hz).trans (map_zero _)
  have htop : b (a + (N : ℤ) - 1) = 0 := by
    let n := a + (N : ℤ) - 1
    let : Subsingleton (C.X (n + 1)) := hsupport _ (Or.inr (by dsimp [n]; omega))
    have hb : boundaries C n = ⊥ := by
      apply LinearMap.range_eq_bot.mpr
      exact Subsingleton.elim _ _
    have : Subsingleton (boundaries C n) := by rw [hb]; infer_instance
    have hz : onBoundaries C F n = 0 := Subsingleton.elim _ _
    exact (congrArg (LinearMap.trace K _) hz).trans (map_zero _)
  have ht := alternating_telescope b a N
  rw [htop, hbottom, mul_zero, mul_zero, sub_zero] at ht
  calc
    _ = (∑ j ∈ Finset.range N, (-1 : K) ^ (a + (j : ℤ)) *
          LinearMap.trace K (C.homology (a + (j : ℤ)))
            (homologyMap F (a + (j : ℤ))).hom) +
        ∑ j ∈ Finset.range N, (-1 : K) ^ (a + (j : ℤ)) *
          (b (a + (j : ℤ)) + b (a + (j : ℤ) - 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [degree_trace C F]
      dsimp [b]
      ring
    _ = _ := by rw [ht, add_zero]

end Complex
end P202.LefschetzTrace
