module

public import Erlang.program
public import MapUpdateKr

@[expose] public section

-- The gradual guarantee: operations on less precise types give less precise results.
namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The gradual guarantee: operations on less precise types give less precise results. -/

section
variable {t : Term} {n : Nat}

/-- `precise?/2` holds when the lower bound of the second is in the first's, and the upper bound of the first in the
second's. -/
theorem precise_true {m : Nat} (hm : (level t n).K + 23 ≤ m) {a b : Term} (ga : GC (level t n) a)
    (gb : GC (level t n) b) (lo : SubN t n (lower b) (lower a)) (up : SubN t n (upper a) (upper b)) :
    «precise?/2» (D m) a b = .ok (.atom "true") := by
  unfold «precise?/2»
  simp only [lower_bound_run ga.shape, lower_bound_run gb.shape, upper_bound_run ga.ub, upper_bound_run gb.ub,
    Lynx.Except.ok_bind, next_sub gb.low_tc ga.low_tc hm, next_sub ga.up_tc gb.up_tc hm, bp_true.mpr lo,
    bp_true.mpr up]
  rfl

/-- Bounds of less precise types: their lower bounds shrink and their upper bounds grow. -/
theorem prec_bounds {m : Nat} (hm : (level t n).K + 23 ≤ m) {a a₂ : Term} (ga : GD t n a) (ga₂ : GD t n a₂)
    (h : «precise?/2» (D m) a a₂ = .ok (.atom "true")) :
    (∀ v : PN t n, denD a₂ v → denD a v) ∧ ∀ v : PN t n, denD (upper a) v → denD (upper a₂) v := by
  obtain ⟨lo, up⟩ := precise_ok hm ga ga₂ h
  exact ⟨fun v hv => (denD_lower a v).mp (lo v ((denD_lower a₂ v).mpr hv)), up⟩

/-- A result is at least as precise as another when its points include the other's, and its upper bound's points are
in the other's. -/
theorem precise_of {m : Nat} (hm : (level t n).K + 23 ≤ m) {c c₂ : Term} (gc : GC (level t n) c)
    (gc₂ : GC (level t n) c₂) (lo : ∀ v : PN t n, denD c₂ v → denD c v)
    (up : ∀ v : PN t n, denD (upper c) v → denD (upper c₂) v) : «precise?/2» (D m) c c₂ = .ok (.atom "true") :=
  precise_true hm gc gc₂ (fun v h => (denD_lower c v).mpr (lo v ((denD_lower c₂ v).mp h))) up

variable {m : Nat} (hm : (level t n).K + 23 ≤ m) {a b a₂ b₂ : Term} (ga : GD t n a) (gb : GD t n b)
  (ga₂ : GD t n a₂) (gb₂ : GD t n b₂) (pa : «precise?/2» (D m) a a₂ = .ok (.atom "true"))
  (pb : «precise?/2» (D m) b b₂ = .ok (.atom "true"))
include hm ga gb ga₂ gb₂ pa pb

theorem union_prec : ∃ c c₂, Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c ∧
    Elixir.Module.Types.Descr.«bare_union/2» (D m) a₂ b₂ = .ok c₂ ∧ «precise?/2» (D m) c c₂ = .ok (.atom "true") := by
  obtain ⟨la, ua⟩ := prec_bounds hm ga ga₂ pa
  obtain ⟨lb, ub⟩ := prec_bounds hm gb gb₂ pb
  obtain ⟨c, gc, rc, sc⟩ := gc_union ga.1 gb.1 (m := m) (by omega)
  obtain ⟨c₂, gc₂, rc₂, sc₂⟩ := gc_union ga₂.1 gb₂.1 (m := m) (by omega)
  refine ⟨c, c₂, rc, rc₂, precise_of hm gc gc₂ (fun v h => ?_) (fun v h => ?_)⟩
  · exact (sc.1 v).mpr (((sc₂.1 v).mp h).imp (la v) (lb v))
  · exact (sc₂.2 v).mpr (((sc.2 v).mp h).imp (ua v) (ub v))

theorem inter_prec : ∃ c c₂, Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c ∧
    Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a₂ b₂ = .ok c₂ ∧
    «precise?/2» (D m) c c₂ = .ok (.atom "true") := by
  obtain ⟨la, ua⟩ := prec_bounds hm ga ga₂ pa
  obtain ⟨lb, ub⟩ := prec_bounds hm gb gb₂ pb
  obtain ⟨c, gc, rc, sc, -⟩ := gc_inter ga.1 gb.1 (m := m) (by omega)
  obtain ⟨c₂, gc₂, rc₂, sc₂, -⟩ := gc_inter ga₂.1 gb₂.1 (m := m) (by omega)
  refine ⟨c, c₂, rc, rc₂, precise_of hm gc gc₂ (fun v h => ?_) (fun v h => ?_)⟩
  · exact (sc.1 v).mpr (((sc₂.1 v).mp h).imp (la v) (lb v))
  · exact (sc₂.2 v).mpr (((sc.2 v).mp h).imp (ua v) (ub v))

theorem diff_prec : ∃ c c₂, Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c ∧
    Elixir.Module.Types.Descr.«bare_difference/2» (D m) a₂ b₂ = .ok c₂ ∧
    «precise?/2» (D m) c c₂ = .ok (.atom "true") := by
  obtain ⟨la, ua⟩ := prec_bounds hm ga ga₂ pa
  obtain ⟨lb, ub⟩ := prec_bounds hm gb gb₂ pb
  obtain ⟨c, gc, rc, sc⟩ := gc_diff ga.1 gb.1 (m := m) (by omega)
  obtain ⟨c₂, gc₂, rc₂, sc₂⟩ := gc_diff ga₂.1 gb₂.1 (m := m) (by omega)
  refine ⟨c, c₂, rc, rc₂, precise_of hm gc gc₂ (fun v h => ?_) (fun v h => ?_)⟩
  · obtain ⟨h₁, h₂⟩ := (sc₂.1 v).mp h
    exact (sc.1 v).mpr ⟨la v h₁, fun h' => h₂ (ub v h')⟩
  · obtain ⟨h₁, h₂⟩ := (sc.2 v).mp h
    exact (sc₂.2 v).mpr ⟨ua v h₁, fun h' => h₂ (lb v h')⟩

omit gb gb₂ pb in
theorem neg_prec : ∃ c c₂, Elixir.Module.Types.Descr.«bare_negation/1» (D m) a = .ok c ∧
    Elixir.Module.Types.Descr.«bare_negation/1» (D m) a₂ = .ok c₂ ∧ «precise?/2» (D m) c c₂ = .ok (.atom "true") := by
  obtain ⟨la, ua⟩ := prec_bounds hm ga ga₂ pa
  obtain ⟨c, gc, rc, sc⟩ := gc_neg ga.1 (m := m) (by omega)
  obtain ⟨c₂, gc₂, rc₂, sc₂⟩ := gc_neg ga₂.1 (m := m) (by omega)
  refine ⟨c, c₂, rc, rc₂, precise_of hm gc gc₂ (fun v h => ?_) (fun v h => ?_)⟩
  · exact (sc.1 v).mpr fun h' => (sc₂.1 v).mp h (ua v h')
  · exact (sc₂.2 v).mpr fun h' => (sc.2 v).mp h (la v h')

end

section
variable {t : Term} {d : Nat}

theorem vals_grad_run {X : List (Term × Term)} (gX : GC (level t (d + 1)) (.map X)) {Dy : Term}
    (hD : mapLookup X (.atom "dynamic") = some Dy) {m : Nat} (hm : (level t (d + 1)).K + 26 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_values/1» (D m) (.map X) = .ok r ∧
      (r ≠ .atom "badtuple" ↔ (∀ v : PN t (d + 1), ¬denD (.map (rmT (rmDyn X))) v) ∧
        ∃ w, denD Dy (tpt (t := t) (n := d + 1) w)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have hK := level_K t d
  have hK' := level_K t (d + 1)
  have ef := (level t (d + 1)).ef
  obtain ⟨dDy, sS, inc⟩ : DE (level t (d + 1)).E Dy ∧ DescrC (FunA (level t (d + 1)).E) (TField (level t (d + 1)).E)
      (LF (level t (d + 1)).E) (MField (level t (d + 1)).E) (rmDyn X) ∧
      ∀ v : PN t (d + 1), denD (.map X) v → denD Dy v := by
    rcases gX with (h | ⟨X', e, sX⟩) | ⟨X', Dy', e, hD', tD, sS, inc⟩
    · cases h
    · simp only [Term.map.injEq] at e; subst e; rw [sX.static] at hD; cases hD
    · simp only [Term.map.injEq] at e; subst e; rw [hD] at hD'; cases hD'; exact ⟨tD, sS, inc⟩
  have dS : DE (level t (d + 1)).E (.map (rmDyn X)) := Or.inr ⟨_, rfl, sS⟩
  obtain ⟨dR, -⟩ := rest_tuple dS
  have rto := next_empty dR (m := k + 3) (by omega)
  -- The values of the static part.
  obtain ⟨b₂, get₂, fb₂, sb₂⟩ : ∃ b₂, Elixir.Map.«get/3» (.map (rmDyn X)) (.atom "tuple") (.atom "bdd_bot") = .ok b₂ ∧
      TField (level t (d + 1)).E b₂ ∧
      ∀ w, TT t (d + 1) (rmDyn X) w ↔ denTF (level t (d + 1)).E (level t (d + 1)).den b₂ w = Bool.true := by
    cases hb : mapLookup (rmDyn X) (.atom "tuple") with
    | none =>
      refine ⟨.atom "bdd_bot", by simp [Elixir.Map.«get/3», getMapKeys_single, hb, pure, Except.pure], Or.inr Bdd.bot,
        fun w => ?_⟩
      rw [denTF_bdd Bdd.bot w]; simp [TT, hb]
    | some b₂ =>
      exact ⟨b₂, by simp [Elixir.Map.«get/3», getMapKeys_single, hb, pure, Except.pure],
        fieldC_tuple (sS.fields "tuple" b₂ hb), fun w => by simp [TT, hb]⟩
  obtain ⟨r₂, er₂, rr₂, sr₂⟩ := proc_vals fb₂ (m := k + 3) (by omega)
  have ne : Erlang.erlang.«==/2» (.map X) (.map []) = .ok (.atom "false") := by
    have : X ≠ [] := by intro h; subst h; simp [mapLookup] at hD
    simp [Erlang.erlang.«==/2»]; intro h; exact this (by cases X <;> simp_all)
  rw [Elixir.Module.Types.Descr.«tuple_values/1».eq_def]
  simp [ne, Erlang.maps.«take/2», hD, Elixir.Module.Types.Descr.«tuple_only?/1», Erlang.maps.«remove/2»]
  simp only [filter_tdyn, rto]
  by_cases to : ∀ v : PN t (d + 1), ¬denD (.map (rmT (rmDyn X))) v
  rotate_left
  · rw [bp_false.mpr to]
    simp [boolAtom, Lynx.Except.andAlso, Elixir.Module.Types.Descr.«-tuple_values/1-fun-0-/1», pure, Except.pure]
    intro h
    exact absurd (fun v => by obtain ⟨⟨a, b, c, e⟩, hv⟩ := v; exact h a b c e hv) to
  rw [bp_true.mpr to]
  -- The tuple field of the dynamic part.
  rcases dDy with rfl | ⟨DX, rfl, sDX⟩
  case' inl =>
    obtain ⟨T, hT, hTt⟩ : ∃ T, Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T) ∧
        mapLookup T (.atom "tuple") = some (.tuple #[.integer 61102469, .atom "open", .nil]) :=
      ⟨_, rfl, by simp [mapLookup]⟩
    simp [boolAtom, Lynx.Except.andAlso, Elixir.Module.Types.Descr.«descr_key?/2», hT, getMapKeys_single, hTt]
    have fb : TField (level t (d + 1)).E (.tuple #[.integer 61102469, .atom "open", .nil]) := Or.inl ⟨_, rfl⟩
    have sb : ∀ w, denD (.atom "term") (tpt (t := t) (n := d + 1) w) ↔
        denTF (level t (d + 1)).E (level t (d + 1)).den (.tuple #[.integer 61102469, .atom "open", .nil]) w = Bool.true :=
      fun w => by simp [denD_term, denTF_top]
    generalize (Term.tuple #[.integer 61102469, .atom "open", .nil]) = b at fb sb ⊢
  case' inr =>
    cases hk : mapLookup DX (.atom "tuple")
    case none =>
      simp [boolAtom, Lynx.Except.andAlso, Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2»,
        any_key, hk, Elixir.Module.Types.Descr.«-tuple_values/1-fun-0-/1», pure, Except.pure]
      intro _ w hw
      rw [denD_tpt] at hw
      simp [TT, hk] at hw
    rename_i b
    have fb : TField (level t (d + 1)).E b := fieldC_tuple (sDX.fields "tuple" b hk)
    have sb : ∀ w, denD (.map DX) (tpt (t := t) (n := d + 1) w) ↔
        denTF (level t (d + 1)).E (level t (d + 1)).den b w = Bool.true := fun w => by rw [denD_tpt]; simp [TT, hk]
    simp [boolAtom, Lynx.Except.andAlso, Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2»,
      any_key, hk, getMapKeys_single]
  all_goals
    obtain ⟨bE, rbE, sbE⟩ := tuple_empty_exact ef fb []
    rw [rbE (k + 3) (by omega)]
    have sbE := sbE (lh b + 1) (Nat.lt_succ_self _) (safeT_nil _)
    cases bE
    case true =>
      simp [boolAtom, Elixir.Module.Types.Descr.«-tuple_values/1-fun-0-/1», pure, Except.pure]
      intro _ w hw
      have := sbE.mp rfl w
      rw [(sb w).mp hw] at this
      cases this
    have get₂' : Elixir.Map.«get/3» (.map (List.filter (fun entry => !decide (compareExact ((Term.atom "dynamic").fuel entry.fst)
        (.atom "dynamic") entry.fst = Ordering.eq)) X)) (.atom "tuple") (.atom "bdd_bot") = .ok b₂ := get₂
    obtain ⟨r₁, er₁, rr₁, sr₁⟩ := proc_vals fb (m := k + 3) (by omega)
    obtain ⟨c₁, hc₁, sc₁, cases₁⟩ := el_canon er₁
    obtain ⟨R, rR, gR, -, -⟩ := dyn_el_union hc₁ er₂ (m := k + 3) (by omega)
    refine ⟨R, ?_, ?_⟩
    · rcases cases₁ with ⟨de, rfl⟩ | ⟨hn, rfl⟩
      · rcases de with rfl | ⟨Z, rfl, sZ⟩
        · simp [boolAtom, rr₁, getMapKeys, get₂', rr₂, rR]
        · simp [boolAtom, rr₁, getMapKeys_single, sZ.static, get₂', rr₂, rR]
      · obtain ⟨q, SS, rfl⟩ := node_tuple hn
        have ex := expand_isT hn (k + 2)
        obtain ⟨Y, eY, sY⟩ := expN_map (.tuple #[.reference q, .map SS, gen]) (keyOf (level t d).nd)
        rw [eY] at ex rR
        have dY : Elixir.Module.Types.Descr.«dynamic/1» (D (k + 3)) (.map Y) =
            .ok (.map [(.atom "dynamic", .map Y)]) := by
          unfold Elixir.Module.Types.Descr.«dynamic/1»; simp [getMapKeys_single, sY]
        have gt : getMapKeys [Term.atom "dynamic"] (.tuple #[.reference q, .map SS, gen]) = [] := by simp [getMapKeys]
        simp [boolAtom, rr₁, gt, ex, unfold_map, dY, get₂', rr₂, rR]
    · have nR : R ≠ .atom "badtuple" := by rcases gR.shape with h | ⟨_, h⟩ <;> rw [h] <;> simp
      refine ⟨fun _ => ⟨fun a b c e h => to ⟨(a, b, c, e), h⟩, ?_⟩, fun _ => nR⟩
      refine Classical.byContradiction fun none => ?_
      have := sbE.mpr fun w => by
        cases h : denTF (level t (d + 1)).E (level t (d + 1)).den b w
        · rfl
        · exact absurd ⟨w, (sb w).mpr h⟩ none
      cases this


/-- `tuple_values/1` on a gradual type of tuples: it gives a type exactly when the lower bound holds only tuples and the
upper bound holds some, and then the bounds of its values are the values of the tuples of the bounds. -/
theorem vals_sem {X : List (Term × Term)} (gX : GC (level t (d + 1)) (.map X)) {m : Nat}
    (hm : (level t (d + 1)).K + 26 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_values/1» (D m) (.map X) = .ok r ∧
      (r ≠ .atom "badtuple" ↔ (∀ v : PN t (d + 1), denD (lower (.map X)) v → v.1.1 = "tuple") ∧
        ∃ w, denD (upper (.map X)) (tpt (t := t) (n := d + 1) w)) ∧
      (r ≠ .atom "badtuple" → ∃ lr ur, Elixir.Module.Types.Descr.«lower_bound/1» (D m) r = .ok lr ∧
        Elixir.Module.Types.Descr.«upper_bound/1» (D m) r = .ok ur ∧ DE (level t d).E lr ∧ DE (level t d).E ur ∧
        (∀ y : PN t d, denD lr y ↔ ∃ w, denD (lower (.map X)) (tpt (t := t) (n := d + 1) w) ∧ y ∈ w) ∧
        ∀ y : PN t d, denD ur y ↔ ∃ w, denD (upper (.map X)) (tpt (t := t) (n := d + 1) w) ∧ y ∈ w) := by
  cases hD : mapLookup X (.atom "dynamic") with
  | none =>
    have dX := GC.static gX hD
    have lX : lower (.map X) = .map X := by simp [lower, rmDyn_static hD]
    have uX : upper (.map X) = .map X := by simp [upper, hD]
    rw [lX, uX]
    obtain ⟨res, run, ⟨rfl, nT⟩ | ⟨tO, eres, -⟩⟩ := values_cases dX (m := m) (by omega)
    · refine ⟨_, run, ⟨fun h => absurd rfl h, fun ⟨h₁, w, h₂⟩ => absurd ⟨h₁, w, (denD_tpt w).mp h₂⟩ nT⟩,
        fun h => absurd rfl h⟩
    have nb : res ≠ .atom "badtuple" := by
      rintro rfl
      rcases eres with (h | ⟨_, h, -⟩) | hn
      · simp at h
      · cases h
      · rw [level_nd] at hn
        obtain ⟨_, _, h⟩ := node_tuple (t := t) (d := d) (by rw [level_nd]; exact hn)
        cases h
    obtain ⟨-, sres⟩ := vals_static dX (m := m) (by omega) run nb
    obtain ⟨c, hc, sc, ub, lb, -, -⟩ := el_ops eres (m - 1)
    have em : m - 1 + 1 = m := by omega
    rw [em] at ub lb
    refine ⟨res, run, ⟨fun _ => ⟨tO.1, tO.2.elim fun w h => ⟨w, (denD_tpt w).mpr h⟩⟩, fun _ => nb⟩,
      fun _ => ⟨c, c, lb, ub, hc, hc, fun y => ?_, fun y => ?_⟩⟩ <;>
      exact (sc y).symm.trans ((sres y).trans (exists_congr fun w => and_congr (denD_tpt w).symm Iff.rfl))
  | some Dy =>
    obtain ⟨r, run, iff⟩ := vals_grad_run gX hD hm
    have uX : upper (.map X) = Dy := by simp [upper, hD]
    rw [uX]
    have cnv : (∀ v : PN t (d + 1), ¬denD (.map (rmT (rmDyn X))) v) ↔
        ∀ v : PN t (d + 1), denD (lower (.map X)) v → v.1.1 = "tuple" := by
      obtain ⟨-, rt⟩ := rest_tuple (t := t) (n := d + 1) gX.low_tc
      constructor
      · intro h v hv
        exact Classical.byContradiction fun ne => h v ((rt v).mpr ⟨hv, ne⟩)
      · intro h v hv
        exact ((rt v).mp hv).2 (h v ((rt v).mp hv).1)
    refine ⟨r, run, iff.trans (and_congr cnv Iff.rfl), fun nb => ?_⟩
    obtain ⟨gR, sl, su⟩ := vals_grad gX hD hm run nb
    refine ⟨lower r, upper r, lower_bound_run gR.shape, upper_bound_run gR.ub, gR.low_tc, gR.up_tc, fun y => ?_,
      fun y => su y⟩
    rw [denD_lower]
    exact (sl y).trans (exists_congr fun w => and_congr (denD_tpt w).symm Iff.rfl)


/-- `precise?/2` holds when the lower bound of the second is in the first's, and the upper bound of the first in the
second's, from their bounds. -/
theorem precise_of_bounds {n m : Nat} (hm : (level t n).K + 23 ≤ m) {a b la ua lb ub : Term}
    (lA : Elixir.Module.Types.Descr.«lower_bound/1» (D m) a = .ok la)
    (uA : Elixir.Module.Types.Descr.«upper_bound/1» (D m) a = .ok ua)
    (lB : Elixir.Module.Types.Descr.«lower_bound/1» (D m) b = .ok lb)
    (uB : Elixir.Module.Types.Descr.«upper_bound/1» (D m) b = .ok ub)
    (dla : DE (level t n).E la) (dua : DE (level t n).E ua) (dlb : DE (level t n).E lb) (dub : DE (level t n).E ub)
    (lo : SubN t n lb la) (up : SubN t n ua ub) : «precise?/2» (D m) a b = .ok (.atom "true") := by
  unfold «precise?/2»
  simp only [lA, uA, lB, uB, Lynx.Except.ok_bind, next_sub dlb dla hm, next_sub dua dub hm, bp_true.mpr lo,
    bp_true.mpr up]
  rfl

/-- The values of less precise tuples are less precise. -/
theorem values_prec {X : List (Term × Term)} {a₂ : Term} (gX : GC (level t (d + 1)) (.map X))
    (g₂ : GC (level t (d + 1)) a₂) {m : Nat} (hm : (level t (d + 1)).K + 26 ≤ m)
    (lo : ∀ v : PN t (d + 1), denD a₂ v → denD (.map X) v)
    (up : ∀ v : PN t (d + 1), denD (upper (.map X)) v → denD (upper a₂) v) {r : Term}
    (run : Elixir.Module.Types.Descr.«tuple_values/1» (D m) (.map X) = .ok r) (nb : r ≠ .atom "badtuple") :
    ∃ r₂, Elixir.Module.Types.Descr.«tuple_values/1» (D m) a₂ = .ok r₂ ∧ r₂ ≠ .atom "badtuple" ∧
      «precise?/2» (D m) r r₂ = .ok (.atom "true") := by
  obtain ⟨r', run', iff, bnd⟩ := vals_sem gX hm
  rw [run] at run'; cases run'
  obtain ⟨only, w, hw⟩ := iff.mp nb
  have only' : ∀ v : PN t (d + 1), denD (lower (.map X)) v → v.1.1 = "tuple" := only
  -- The less precise type is a map type, as its points are tuples.
  obtain ⟨X₂, rfl⟩ : ∃ X₂, a₂ = .map X₂ := by
    rcases g₂.shape with rfl | ⟨X₂, rfl⟩
    · have := only' bitPt ((denD_lower _ _).mpr (lo bitPt (denD_term _)))
      simp [bitPt] at this
    · exact ⟨X₂, rfl⟩
  obtain ⟨r₂, run₂, iff₂, bnd₂⟩ := vals_sem g₂ hm
  have nb₂ : r₂ ≠ .atom "badtuple" := iff₂.mpr
    ⟨fun v h => only' v ((denD_lower _ _).mpr (lo v ((denD_lower _ _).mp h))), w, up _ hw⟩
  obtain ⟨lr, ur, lb, ub, dl, du, sl, su⟩ := bnd nb
  obtain ⟨lr₂, ur₂, lb₂, ub₂, dl₂, du₂, sl₂, su₂⟩ := bnd₂ nb₂
  refine ⟨r₂, run₂, nb₂, precise_of_bounds (n := d) (by rw [level_K] at hm ⊢; omega) lb ub lb₂ ub₂ dl du dl₂ du₂
    (fun y h => ?_) (fun y h => ?_)⟩
  · obtain ⟨w, hw, my⟩ := (sl₂ y).mp h
    exact (sl y).mpr ⟨w, (denD_lower _ _).mpr (lo _ ((denD_lower _ _).mp hw)), my⟩
  · obtain ⟨w, hw, my⟩ := (su y).mp h
    exact (su₂ y).mpr ⟨w, up _ hw, my⟩

end

section
variable {t : Term} {n : Nat}

theorem size_check1_iff {S : List (Term × Term)} (hS : DE (level t n).E (.map S)) (i : Nat) {m : Nat}
    (hm : (level t n).K + 1 ≤ m) :
    ∃ sz : Bool, Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D m) (.map S)
        (.integer ((i : Int) + 1)) = .ok (boolAtom sz) ∧ (sz = Bool.true ↔ ∀ w, TT t n S w → i < List.length w) := by
  have sS := de_map hS
  cases hb : mapLookup S (.atom "tuple") with
  | none =>
    refine ⟨Bool.true, ?_, ⟨fun _ w hw => by simp [TT, hb] at hw, fun _ => rfl⟩⟩
    unfold Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2»
    simp [getMapKeys_single, hb, boolAtom]
  | some b =>
    have fb : TField (level t n).E b := fieldC_tuple (sS.fields "tuple" b hb)
    obtain ⟨sz, rs, ss⟩ := size_at_least (level t n).ef (m := m) (by omega) fb (i + 1) (by omega)
    refine ⟨sz, by rw [size_map _ hb]; simpa using rs, ?_⟩
    rw [ss]
    exact ⟨fun h w hw => h w (by simpa [TT, hb] using hw), fun h w hw => h w (by simpa [TT, hb] using hw)⟩

theorem del_grad_run {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {Dy : Term}
    (hD : mapLookup X (.atom "dynamic") = some Dy) (i : Nat) {m : Nat}
    (hm : (level t n).K + 26 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_delete_at/2» (D m) (.map X) (.integer i) = .ok r ∧
      ((∃ R, r = .map R) ↔ (∀ v : PN t n, ¬denD (.map (rmT (rmDyn X))) v) ∧
        (∀ u, TT t n (rmDyn X) u → i < List.length u) ∧ ∃ u, denD Dy (tpt (t := t) (n := n) u) ∧ i < List.length u) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  obtain ⟨dDy, sS⟩ : DE (level t n).E Dy ∧ DescrC (FunA (level t n).E) (TField (level t n).E) (LF (level t n).E)
      (MField (level t n).E) (rmDyn X) := by
    rcases gX with (h | ⟨X', e, sX⟩) | ⟨X', Dy', e, hD', tD, sS, -⟩
    · cases h
    · simp only [Term.map.injEq] at e; subst e; rw [sX.static] at hD; cases hD
    · simp only [Term.map.injEq] at e; subst e; rw [hD] at hD'; cases hD'; exact ⟨tD, sS⟩
  have inc : ∀ v : PN t n, denD (.map X) v → denD Dy v := by
    rcases gX with (h | ⟨X', e, sX⟩) | ⟨X', Dy', e, hD', -, -, inc⟩
    · cases h
    · simp only [Term.map.injEq] at e; subst e; rw [sX.static] at hD; cases hD
    · simp only [Term.map.injEq] at e; subst e; rw [hD] at hD'; cases hD'; exact inc
  have dS : DE (level t n).E (.map (rmDyn X)) := Or.inr ⟨_, rfl, sS⟩
  obtain ⟨dR, sR⟩ := rest_tuple dS
  obtain ⟨kd, rkd, skd⟩ : ∃ kd : Bool, Elixir.Module.Types.Descr.«descr_key?/2» Dy (.atom "tuple") = .ok (boolAtom kd) ∧
      (kd = Bool.false → ∀ u, ¬denD Dy (tpt (t := t) (n := n) u)) := by
    rcases dDy with rfl | ⟨DX, rfl, -⟩
    · exact ⟨Bool.true, rfl, fun h => by cases h⟩
    · refine ⟨(mapLookup DX (.atom "tuple")).isSome, ?_, fun h u hu => ?_⟩
      · cases h : (mapLookup DX (.atom "tuple")).isSome <;>
          simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, boolAtom, h]
      · rw [denD_tpt] at hu
        obtain ⟨b, hb, -⟩ := hu
        rw [hb] at h; cases h
  have rto := next_empty dR (m := k + 3) (by omega)
  obtain ⟨sz, rsz, ssz⟩ := size_check1_iff dS i (m := k + 3) (by omega)
  rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def]
  simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare,
    Erlang.maps.«take/2», hD, Elixir.Module.Types.Descr.«tuple_only?/1», Erlang.maps.«remove/2»]
  simp only [filter_dyn, filter_tdyn, rkd, rto, rsz]
  by_cases to : ∀ v : PN t n, ¬denD (.map (rmT (rmDyn X))) v
  rotate_left
  · rw [bp_false.mpr to]
    cases kd <;> cases sz <;> simp [boolAtom, Erlang.erlang.«/=/2»] <;> intro h <;> exact (to (fun ⟨⟨a, b, c, e⟩, hv⟩ => h a b c e hv)).elim
  rw [bp_true.mpr to]
  cases kd
  · simp [boolAtom, Erlang.erlang.«/=/2»]
    intro _ _ u hu
    exact absurd hu (skd rfl u)
  cases sz
  · simp [boolAtom, Erlang.erlang.«/=/2»]
    intro _ long
    exact absurd (ssz.mpr long) (by simp)
  have long := ssz.mp rfl
  -- The static part.
  obtain ⟨YS, rS, dYS, oYS, tYS⟩ := del_any dS i long (m := k + 3) (by omega)
  -- The long enough tuples of the dynamic part.
  obtain ⟨kz, rZ, dZ, oZ, tZ⟩ := sizeT_run (t := t) (n := n) (i + 1)
  have rZ' : Elixir.Module.Types.Descr.«tuple_of_size_at_least/1» (.integer ((i : Int) + 1)) =
      .ok (.map [(.atom "tuple", .tuple #[.integer kz, .atom "open", Term.list (List.replicate (i + 1) (.atom "term"))])]) := by
    simpa using rZ
  obtain ⟨c, dc, rc, sc⟩ := (ef_next t n).opt_inter [] dDy dZ (m := k + 3) (by omega)
  obtain ⟨C, rfl⟩ : ∃ C, c = .map C := by
    rcases dc with rfl | ⟨C, rfl, -⟩
    · exfalso
      have := oZ _ ((sc (aPt (t := t) (n := n) (.atom "a"))).mp (denD_term _)).2
      simp [aPt] at this
    · exact ⟨C, rfl⟩
  have tC : ∀ u, TT t n C u ↔ denD Dy (tpt (t := t) (n := n) u) ∧ i < List.length u := fun u => by
    rw [← denD_tpt, sc, denD_tpt, tZ]
    exact ⟨fun ⟨a, b⟩ => ⟨a, by omega⟩, fun ⟨a, b⟩ => ⟨a, by omega⟩⟩
  obtain ⟨YA, rA, dYA, oYA, tYA⟩ := del_any dc i (fun u h => ((tC u).mp h).2) (m := k + 3) (by omega)
  have eC := next_empty dc (m := k + 3) (by omega)
  have eS := next_empty dS (m := k + 3) (by omega)
  have wrapA : getMapKeys [.atom "dynamic"] (.map YA) = [] := by
    simp [getMapKeys_single, (de_map dYA).static]
  obtain ⟨R', rR', ⟨U, eU⟩, gR', sR', uR'⟩ := gout dYA dYS (m := k + 3) (by omega)
  simp only [boolAtom, Erlang.erlang.«/=/2», Lynx.Except.tryWith, rS, rZ',
    Elixir.Module.Types.Descr.«opt_intersection/2», rc, eC, eS, rA, wrapA, rR', Lynx.Except.ok_bind, equal_eq_decide]
  -- Tuples of the static part, which the dynamic part holds.
  have stat : ∀ v : PN t n, denD (.map (rmDyn X)) v → ∃ u, denD Dy (tpt (t := t) (n := n) u) ∧ i < List.length u := by
    intro v hv
    have tv : v.1.1 = "tuple" := Classical.byContradiction fun ne => to v ((sR v).mpr ⟨hv, ne⟩)
    obtain ⟨w, hw⟩ := pt_tuple_de v tv
    have hw' := (hw _ dS).mp hv
    exact ⟨w, (hw _ dDy).mp (inc v ((denD_rmDyn X v).mp hv)), long w ((denD_tpt w).mp hw')⟩
  have dyn : ∀ v : PN t n, denD (.map C) v → ∃ u, denD Dy (tpt (t := t) (n := n) u) ∧ i < List.length u := by
    intro v hv
    have tv : v.1.1 = "tuple" := oZ _ ((sc v).mp hv).2
    obtain ⟨w, hw⟩ := pt_tuple_de v tv
    exact ⟨w, (tC w).mp ((denD_tpt w).mp ((hw _ dc).mp hv))⟩
  by_cases both : (∀ v : PN t n, ¬denD (.map C) v) ∧ ∀ v : PN t n, ¬denD (.map (rmDyn X)) v
  · rw [bp_true.mpr both.1, bp_true.mpr both.2]
    simp [Term.true]
    intro _ _ u hu
    exact Nat.le_of_not_lt fun lu => both.1 _ ((denD_tpt u).mpr ((tC u).mpr ⟨hu, lu⟩))
  have ex : ∃ u, denD Dy (tpt (t := t) (n := n) u) ∧ i < List.length u := by
    by_cases ec : ∀ v : PN t n, ¬denD (.map C) v
    · have es : ¬∀ v : PN t n, ¬denD (.map (rmDyn X)) v := fun es => both ⟨ec, es⟩
      obtain ⟨v, hv⟩ := Classical.not_forall.mp es
      exact stat v (Classical.not_not.mp hv)
    · obtain ⟨v, hv⟩ := Classical.not_forall.mp ec
      exact dyn v (Classical.not_not.mp hv)
  subst eU
  refine ⟨.map U, ?_, ⟨fun _ => ⟨fun a b c e h => to ⟨(a, b, c, e), h⟩, long, ex⟩, fun _ => ⟨U, rfl⟩⟩⟩
  by_cases ec : ∀ v : PN t n, ¬denD (.map C) v <;> by_cases es : ∀ v : PN t n, ¬denD (.map (rmDyn X)) v
  · exact absurd ⟨ec, es⟩ both
  all_goals
    first
    | rw [bp_true.mpr ec, bp_false.mpr es]
    | rw [bp_false.mpr ec, bp_true.mpr es]
    | rw [bp_false.mpr ec, bp_false.mpr es]
    simp [Term.true]



/-- `tuple_delete_at/2` on a gradual type of tuples gives a type exactly when the lower bound holds only tuples, all
longer than the index, and the upper bound holds one. -/
theorem del_sem {X : List (Term × Term)} (gX : GC (level t n) (.map X)) (i : Nat) {m : Nat}
    (hm : (level t n).K + 26 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_delete_at/2» (D m) (.map X) (.integer i) = .ok r ∧
      ((∃ R, r = .map R) ↔ (∀ v : PN t n, denD (lower (.map X)) v → v.1.1 = "tuple") ∧
        (∀ u, denD (lower (.map X)) (tpt (t := t) (n := n) u) → i < List.length u) ∧
        ∃ u, denD (upper (.map X)) (tpt (t := t) (n := n) u) ∧ i < List.length u) := by
  cases hD : mapLookup X (.atom "dynamic") with
  | none =>
    have dX := GC.static gX hD
    have lX : lower (.map X) = .map X := by simp [lower, rmDyn_static hD]
    have uX : upper (.map X) = .map X := by simp [upper, hD]
    rw [lX, uX]
    obtain ⟨res, run, ⟨rfl, nT⟩ | ⟨rfl, tO, sh⟩ | ⟨tO, nsh, r, rfl, -⟩⟩ := delete_cases dX i (m := m) (by omega)
    · refine ⟨_, run, ⟨fun ⟨_, h⟩ => (by cases h), fun ⟨h₁, _, w, h₂, _⟩ => absurd ⟨h₁, w, (denD_tpt w).mp h₂⟩ nT⟩⟩
    · refine ⟨_, run, ⟨fun ⟨_, h⟩ => (by cases h), fun ⟨_, long, _⟩ => ?_⟩⟩
      obtain ⟨w, hw, lw⟩ := sh
      exact absurd (long w ((denD_tpt w).mpr hw)) (by omega)
    · refine ⟨_, run, ⟨fun _ => ⟨tO.1, fun u hu => ?_, ?_⟩, fun _ => ⟨_, rfl⟩⟩⟩
      · exact Nat.lt_of_not_le fun le => nsh ⟨u, (denD_tpt u).mp hu, le⟩
      · obtain ⟨w, hw⟩ := tO.2
        exact ⟨w, (denD_tpt w).mpr hw, Nat.lt_of_not_le fun le => nsh ⟨w, hw, le⟩⟩
  | some Dy =>
    obtain ⟨r, run, iff⟩ := del_grad_run gX hD i hm
    have uX : upper (.map X) = Dy := by simp [upper, hD]
    rw [uX]
    obtain ⟨-, rt⟩ := rest_tuple (t := t) (n := n) gX.low_tc
    refine ⟨r, run, iff.trans ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨fun v hv => ?_, fun u hu => h₂ u ((denD_tpt u).mp hu), h₃⟩,
      fun ⟨h₁, h₂, h₃⟩ => ⟨fun v hv => ((rt v).mp hv).2 (h₁ v ((rt v).mp hv).1),
        fun u hu => h₂ u ((denD_tpt u).mpr hu), h₃⟩⟩⟩
    exact Classical.byContradiction fun ne => h₁ v ((rt v).mpr ⟨hv, ne⟩)

theorem tdelAt_mono {P P' : List (level t n).V → Prop} {i : Nat} (h : ∀ u, P u → P' u) {p : PN t n}
    (hp : TDelAt P i p) : TDelAt P' i p := by
  obtain ⟨w, hw, v₁, y, v₂, e, len, hP⟩ := hp
  exact ⟨w, hw, v₁, y, v₂, e, len, h _ hP⟩

/-- Deleting an element of less precise tuples gives less precise tuples. -/
theorem delete_prec {X : List (Term × Term)} {a₂ : Term} (gX : GC (level t n) (.map X))
    (g₂ : GC (level t n) a₂) (i : Nat) {m : Nat} (hm : (level t n).K + 26 ≤ m)
    (lo : ∀ v : PN t n, denD a₂ v → denD (.map X) v)
    (up : ∀ v : PN t n, denD (upper (.map X)) v → denD (upper a₂) v) {R : List (Term × Term)}
    (run : Elixir.Module.Types.Descr.«tuple_delete_at/2» (D m) (.map X) (.integer i) = .ok (.map R)) :
    ∃ R₂, Elixir.Module.Types.Descr.«tuple_delete_at/2» (D m) a₂ (.integer i) = .ok (.map R₂) ∧
      «precise?/2» (D m) (.map R) (.map R₂) = .ok (.atom "true") := by
  obtain ⟨r', run', iff⟩ := del_sem gX i hm
  rw [run] at run'; cases run'
  obtain ⟨only, long, w, hw, lw⟩ := iff.mp ⟨R, rfl⟩
  obtain ⟨X₂, rfl⟩ : ∃ X₂, a₂ = .map X₂ := by
    rcases g₂.shape with rfl | ⟨X₂, rfl⟩
    · have := only bitPt ((denD_lower _ _).mpr (lo bitPt (denD_term _)))
      simp [bitPt] at this
    · exact ⟨X₂, rfl⟩
  obtain ⟨r₂, run₂, iff₂⟩ := del_sem g₂ i hm
  obtain ⟨R₂, rfl⟩ := iff₂.mpr ⟨fun v h => only v ((denD_lower _ _).mpr (lo v ((denD_lower _ _).mp h))),
    fun u hu => long u ((denD_lower _ _).mpr (lo _ ((denD_lower _ _).mp hu))), w, up _ hw, lw⟩
  obtain ⟨gR, sR, uR, -, -⟩ := del_pts gX i (by omega) run
  obtain ⟨gR₂, sR₂, uR₂, -, -⟩ := del_pts g₂ i (by omega) run₂
  refine ⟨R₂, run₂, precise_true (by omega) gR gR₂ (fun p h => ?_) (fun p h => ?_)⟩
  · rw [denD_lower] at h ⊢
    refine (sR p).mpr (tdelAt_mono (fun u hu => ?_) ((sR₂ p).mp h))
    exact (denD_tpt u).mp ((denD_rmDyn X _).mpr (lo _ ((denD_rmDyn X₂ _).mp ((denD_tpt u).mpr hu))))
  · refine (uR₂ p).mpr (tdelAt_mono (fun u hu => ?_) ((uR p).mp h))
    rcases hu with ⟨hu, lu⟩ | hu
    · exact Or.inl ⟨up _ hu, lu⟩
    · exact Or.inl ⟨up _ (gX.inv _ ((denD_rmDyn X _).mp ((denD_tpt u).mpr hu))), long u ((denD_tpt u).mpr hu)⟩

end

section
variable {t : Term} {n : Nat}

theorem size_check_iff {S : List (Term × Term)} (hS : DE (level t n).E (.map S)) (i : Nat) {m : Nat}
    (hm : (level t n).K + 1 ≤ m) :
    ∃ sz : Bool, Lynx.Except.orElse (Erlang.erlang.«==/2» (.integer i) (.integer 0))
        (Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D m) (.map S) (.integer i)) = .ok (boolAtom sz) ∧
      (sz = Bool.true ↔ ∀ w, TT t n S w → i ≤ List.length w) := by
  by_cases z : i = 0
  · subst z
    exact ⟨Bool.true, by simp [Lynx.Except.orElse, Erlang.erlang.«==/2», boolAtom], by simp⟩
  have eq0 : Erlang.erlang.«==/2» (.integer (i : Int)) (.integer 0) = .ok (.atom "false") := by
    simp [Erlang.erlang.«==/2»]; omega
  rw [eq0]
  simp only [Lynx.Except.orElse]
  have sS := de_map hS
  cases hb : mapLookup S (.atom "tuple") with
  | none =>
    refine ⟨Bool.true, ?_, ⟨fun _ w hw => by simp [TT, hb] at hw, fun _ => rfl⟩⟩
    unfold Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2»
    simp [getMapKeys_single, hb, boolAtom]
  | some b =>
    have fb : TField (level t n).E b := fieldC_tuple (sS.fields "tuple" b hb)
    obtain ⟨sz, rs, ss⟩ := size_at_least (level t n).ef (m := m) (by omega) fb i (by omega)
    refine ⟨sz, by rw [size_map _ hb]; exact rs, ?_⟩
    rw [ss]
    exact ⟨fun h w hw => h w (by simpa [TT, hb] using hw), fun h w hw => h w (by simpa [TT, hb] using hw)⟩

theorem ins_grad_run {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {Dy : Term}
    (hD : mapLookup X (.atom "dynamic") = some Dy) {x : Term} (hx : (level t n).E x) (i : Nat) {m : Nat}
    (hm : (level t n).K + 26 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (D m) (.map X) (.integer i) x = .ok r ∧
      ((∃ R, r = .map R) ↔ (∀ v : PN t n, ¬denD (.map (rmT (rmDyn X))) v) ∧
        (∀ u, TT t n (rmDyn X) u → i ≤ List.length u) ∧ ∃ u, denD Dy (tpt (t := t) (n := n) u) ∧ i ≤ List.length u) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  obtain ⟨dDy, sS⟩ : DE (level t n).E Dy ∧ DescrC (FunA (level t n).E) (TField (level t n).E) (LF (level t n).E)
      (MField (level t n).E) (rmDyn X) := by
    rcases gX with (h | ⟨X', e, sX⟩) | ⟨X', Dy', e, hD', tD, sS, -⟩
    · cases h
    · simp only [Term.map.injEq] at e; subst e; rw [sX.static] at hD; cases hD
    · simp only [Term.map.injEq] at e; subst e; rw [hD] at hD'; cases hD'; exact ⟨tD, sS⟩
  have inc : ∀ v : PN t n, denD (.map X) v → denD Dy v := by
    rcases gX with (h | ⟨X', e, sX⟩) | ⟨X', Dy', e, hD', -, -, inc⟩
    · cases h
    · simp only [Term.map.injEq] at e; subst e; rw [sX.static] at hD; cases hD
    · simp only [Term.map.injEq] at e; subst e; rw [hD] at hD'; cases hD'; exact inc
  have dS : DE (level t n).E (.map (rmDyn X)) := Or.inr ⟨_, rfl, sS⟩
  obtain ⟨dR, sR⟩ := rest_tuple dS
  obtain ⟨kd, rkd, skd⟩ : ∃ kd : Bool, Elixir.Module.Types.Descr.«descr_key?/2» Dy (.atom "tuple") = .ok (boolAtom kd) ∧
      (kd = Bool.false → ∀ u, ¬denD Dy (tpt (t := t) (n := n) u)) := by
    rcases dDy with rfl | ⟨DX, rfl, -⟩
    · exact ⟨Bool.true, rfl, fun h => by cases h⟩
    · refine ⟨(mapLookup DX (.atom "tuple")).isSome, ?_, fun h u hu => ?_⟩
      · cases h : (mapLookup DX (.atom "tuple")).isSome <;>
          simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, boolAtom, h]
      · rw [denD_tpt] at hu
        obtain ⟨b, hb, -⟩ := hu
        rw [hb] at h; cases h
  have rto := next_empty dR (m := k + 3) (by omega)
  obtain ⟨sz, rsz, ssz⟩ := size_check_iff dS i (m := k + 3) (by omega)
  unfold Elixir.Module.Types.Descr.«tuple_insert_at_checked/3»
  simp only [Erlang.maps.«take/2», hD, Elixir.Module.Types.Descr.«tuple_only?/1», Erlang.maps.«remove/2», equalExact_eq_decide]
  simp only [filter_dyn, filter_t, rkd, rto, rsz, Lynx.Except.ok_bind]
  by_cases to : ∀ v : PN t n, ¬denD (.map (rmT (rmDyn X))) v
  rotate_left
  · rw [bp_false.mpr to]
    cases kd <;> cases sz <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2»] <;> intro h <;>
      exact (to (fun ⟨⟨a, b, c, e⟩, hv⟩ => h a b c e hv)).elim
  rw [bp_true.mpr to]
  cases sz
  · cases kd <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2»] <;> intro _ long <;>
      exact absurd (ssz.mpr long) (by simp)
  cases kd
  · simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2»]
    intro _ _ u hu
    exact absurd hu (skd rfl u)
  have onlyS : ∀ v : PN t n, denD (.map (rmDyn X)) v → v.1.1 = "tuple" := fun v hv =>
    Classical.byContradiction fun h => to v ((sR v).mpr ⟨hv, h⟩)
  have long := ssz.mp rfl
  obtain ⟨YS, rS, dYS, oYS, tYS⟩ := ins_any dS onlyS hx i (m := k + 3) (by omega)
  obtain ⟨kz, rZ, dZ, oZ, tZ⟩ := sizeT_run (t := t) (n := n) i
  obtain ⟨c, dc, rc, sc⟩ := (ef_next t n).opt_inter [] dDy dZ (m := k + 3) (by omega)
  obtain ⟨C, rfl⟩ : ∃ C, c = .map C := by
    rcases dc with rfl | ⟨C, rfl, -⟩
    · exfalso
      have := oZ _ ((sc (aPt (t := t) (n := n) (.atom "a"))).mp (denD_term _)).2
      simp [aPt] at this
    · exact ⟨C, rfl⟩
  have oC : ∀ v : PN t n, denD (.map C) v → v.1.1 = "tuple" := fun v hv => oZ v ((sc v).mp hv).2
  have tC : ∀ u, TT t n C u ↔ denD Dy (tpt (t := t) (n := n) u) ∧ i ≤ List.length u := fun u => by
    rw [← denD_tpt, sc, denD_tpt, tZ]
  obtain ⟨YA, rA, dYA, oYA, tYA⟩ := ins_any dc oC hx i (m := k + 3) (by omega)
  have eC := next_empty dc (m := k + 3) (by omega)
  have eS := next_empty dS (m := k + 3) (by omega)
  have wrapA : getMapKeys [.atom "dynamic"] (.map YA) = [] := by
    simp [getMapKeys_single, (de_map dYA).static]
  obtain ⟨R', rR', ⟨U, eU⟩, gR', sR', uR'⟩ := gout dYA dYS (m := k + 3) (by omega)
  simp only [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2», Lynx.Except.guard, rS, rZ,
    Elixir.Module.Types.Descr.«opt_intersection/2», rc, eC, eS, rA, wrapA, Lynx.Except.ok_bind, equal_eq_decide]
  have stat : ∀ v : PN t n, denD (.map (rmDyn X)) v → ∃ u, denD Dy (tpt (t := t) (n := n) u) ∧ i ≤ List.length u := by
    intro v hv
    obtain ⟨w, hw⟩ := pt_tuple_de v (onlyS v hv)
    have hw' := (hw _ dS).mp hv
    exact ⟨w, (hw _ dDy).mp (inc v ((denD_rmDyn X v).mp hv)), long w ((denD_tpt w).mp hw')⟩
  have dyn : ∀ v : PN t n, denD (.map C) v → ∃ u, denD Dy (tpt (t := t) (n := n) u) ∧ i ≤ List.length u := by
    intro v hv
    obtain ⟨w, hw⟩ := pt_tuple_de v (oC v hv)
    exact ⟨w, (tC w).mp ((denD_tpt w).mp ((hw _ dc).mp hv))⟩
  by_cases both : (∀ v : PN t n, ¬denD (.map C) v) ∧ ∀ v : PN t n, ¬denD (.map (rmDyn X)) v
  · rw [bp_true.mpr both.1, bp_true.mpr both.2]
    simp [Lynx.Term.isMember, Term.true]
    intro _ _ u hu
    exact Nat.lt_of_not_le fun lu => both.1 _ ((denD_tpt u).mpr ((tC u).mpr ⟨hu, lu⟩))
  have ex : ∃ u, denD Dy (tpt (t := t) (n := n) u) ∧ i ≤ List.length u := by
    by_cases ec : ∀ v : PN t n, ¬denD (.map C) v
    · have es : ¬∀ v : PN t n, ¬denD (.map (rmDyn X)) v := fun es => both ⟨ec, es⟩
      obtain ⟨v, hv⟩ := Classical.not_forall.mp es
      exact stat v (Classical.not_not.mp hv)
    · obtain ⟨v, hv⟩ := Classical.not_forall.mp ec
      exact dyn v (Classical.not_not.mp hv)
  subst eU
  refine ⟨.map U, ?_, ⟨fun _ => ⟨to, long, ex⟩, fun _ => ⟨U, rfl⟩⟩⟩
  by_cases ec : ∀ v : PN t n, ¬denD (.map C) v <;> by_cases es : ∀ v : PN t n, ¬denD (.map (rmDyn X)) v
  · exact absurd ⟨ec, es⟩ both
  all_goals
    first
    | rw [bp_true.mpr ec, bp_false.mpr es]
    | rw [bp_false.mpr ec, bp_true.mpr es]
    | rw [bp_false.mpr ec, bp_false.mpr es]
    simp [Lynx.Term.isMember, Term.true, rR']


/-- `tuple_insert_at_checked/3` on a static type gives a type exactly when it holds only tuples, all at least as long as
the index. -/
theorem ins_static_run {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {x : Term} (hx : (level t n).E x)
    (i : Nat) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (D m) (.map X) (.integer i) x = .ok r ∧
      ((∃ Y, r = .map Y) ↔ TOnly t n X ∧ ∀ w, TT t n X w → i ≤ List.length w) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have sX := de_map hX
  unfold Elixir.Module.Types.Descr.«tuple_insert_at_checked/3»
  simp only [Erlang.maps.«take/2», sX.static, Lynx.Except.ok_bind]
  cases hb : mapLookup X (.atom "tuple") with
  | none =>
    have noT : ¬TOnly t n X := fun ⟨_, w, hw⟩ => by simp [TT, hb] at hw
    have sz : Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D (k + 3)) (.map X) (.integer i) =
        .ok (.atom "true") := by
      unfold Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2»
      simp [getMapKeys_single, hb]
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso,
      Lynx.Except.guard]
    by_cases z : i = 0 <;> simp [z, sz, Erlang.erlang.«/=/2»] <;> first | exact noT | exact fun h => absurd h noT
  | some b =>
    have fb : TField (level t n).E b := fieldC_tuple (sX.fields "tuple" b hb)
    obtain ⟨dR, sR⟩ := rest_tuple hX
    have rE := next_empty dR (m := k + 3) (by omega)
    obtain ⟨eb, reb, seb⟩ := tuple_empty_exact (level t n).ef fb []
    have seb := seb (lh b + 1) (by omega) (safeT_nil _)
    have tt : ∀ w, TT t n X w ↔ denTF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [TT, hb]
    have only : TOnly t n X ↔ (∀ v : PN t n, ¬denD (.map (rmT X)) v) ∧ eb = Bool.false := by
      constructor
      · rintro ⟨h₁, w, hw⟩
        refine ⟨fun v hv => ((sR v).mp hv).2 (h₁ v ((sR v).mp hv).1), ?_⟩
        cases eb
        · rfl
        · have := seb.mp rfl w; rw [(tt w).mp hw] at this; cases this
      · rintro ⟨h₁, h₂⟩
        refine ⟨fun v hv => Classical.byContradiction fun ne => h₁ v ((sR v).mpr ⟨hv, ne⟩), ?_⟩
        obtain ⟨w, hw⟩ := Classical.not_forall.mp (mt seb.mpr (by simp [h₂]))
        exact ⟨w, (tt w).mpr (by simpa using hw)⟩
    have nonEmpty : Elixir.Module.Types.Descr.«non_empty_tuple_only?/1» (D (k + 3)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) && !eb)) := by
      simp only [Elixir.Module.Types.Descr.«non_empty_tuple_only?/1», Erlang.maps.«take/2», hb, equalExact_eq_decide]
      rw [show (List.filter (fun entry => !decide (compareExact (fuel (.atom "tuple") entry.fst) (.atom "tuple") entry.fst = .eq)) X) = rmT X from rfl]
      simp only [Lynx.Except.ok_bind, rE, reb (k + 3) (by omega)]
      cases bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) <;> cases eb <;>
        simp [Lynx.Except.andAlso, Erlang.erlang.«not/1», boolAtom]
    have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "tuple") = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
    obtain ⟨sz, rsz, ssz⟩ := size_check_iff hX i (m := k + 3) (by omega)
    obtain ⟨c, rc, sc⟩ : ∃ c : Bool, Elixir.Module.Types.Descr.«non_empty_tuple_only?/1» (D (k + 3)) (.map X) =
        .ok (boolAtom c) ∧ (c = Bool.true ↔ TOnly t n X) := by
      refine ⟨_, nonEmpty, ?_⟩
      rw [only]
      simp only [Bool.and_eq_true, bp_true, Bool.not_eq_true']
    simp only [key, rc, rsz]
    cases c <;> cases sz
    · simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2», pure, Except.pure]
      exact fun h => absurd (sc.mpr h) (by simp)
    · simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2», pure, Except.pure]
      exact fun h => absurd (sc.mpr h) (by simp)
    · simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2», pure, Except.pure]
      exact fun _ => Classical.byContradiction fun ne =>
        absurd (ssz.mpr fun w hw => Nat.le_of_not_lt fun lt => ne ⟨w, hw, lt⟩) (by simp)
    · obtain ⟨Y, rY, -⟩ := ins_any hX (sc.mp rfl).1 hx i (m := k + 3) (by omega)
      simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2», pure, Except.pure, rY]
      exact ⟨sc.mp rfl, ssz.mp rfl⟩


/-- `tuple_insert_at_checked/3` on a gradual type of tuples gives a type exactly when the lower bound holds only
tuples, all at least as long as the index, and the upper bound holds one. -/
theorem ins_sem {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {x : Term} (hx : (level t n).E x) (i : Nat)
    {m : Nat} (hm : (level t n).K + 26 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (D m) (.map X) (.integer i) x = .ok r ∧
      ((∃ R, r = .map R) ↔ (∀ v : PN t n, denD (lower (.map X)) v → v.1.1 = "tuple") ∧
        (∀ u, denD (lower (.map X)) (tpt (t := t) (n := n) u) → i ≤ List.length u) ∧
        ∃ u, denD (upper (.map X)) (tpt (t := t) (n := n) u) ∧ i ≤ List.length u) := by
  cases hD : mapLookup X (.atom "dynamic") with
  | none =>
    have dX := GC.static gX hD
    have lX : lower (.map X) = .map X := by simp [lower, rmDyn_static hD]
    have uX : upper (.map X) = .map X := by simp [upper, hD]
    rw [lX, uX]
    obtain ⟨r, run, iff⟩ := ins_static_run dX hx i (m := m) (by omega)
    refine ⟨r, run, iff.trans ⟨fun ⟨⟨h₁, w, hw⟩, long⟩ => ⟨h₁, fun u hu => long u ((denD_tpt u).mp hu),
      w, (denD_tpt w).mpr hw, long w hw⟩, fun ⟨h₁, h₂, w, hw, _⟩ => ⟨⟨h₁, w, (denD_tpt w).mp hw⟩,
      fun u hu => h₂ u ((denD_tpt u).mpr hu)⟩⟩⟩
  | some Dy =>
    obtain ⟨r, run, iff⟩ := ins_grad_run gX hD hx i hm
    have uX : upper (.map X) = Dy := by simp [upper, hD]
    rw [uX]
    obtain ⟨-, rt⟩ := rest_tuple (t := t) (n := n) gX.low_tc
    refine ⟨r, run, iff.trans ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨fun v hv => ?_, fun u hu => h₂ u ((denD_tpt u).mp hu), h₃⟩,
      fun ⟨h₁, h₂, h₃⟩ => ⟨fun v hv => ((rt v).mp hv).2 (h₁ v ((rt v).mp hv).1),
        fun u hu => h₂ u ((denD_tpt u).mpr hu), h₃⟩⟩⟩
    exact Classical.byContradiction fun ne => h₁ v ((rt v).mpr ⟨hv, ne⟩)


theorem insAt_mono {P P' : List (level t n).V → Prop} {i : Nat} {Q Q' : (level t n).V → Prop}
    (hP : ∀ u, P u → P' u) (hQ : ∀ y, Q y → Q' y) {p : PN t n} (h : InsAt P i Q p) : InsAt P' i Q' p := by
  obtain ⟨w, hw, w₁, y, w₂, e, len, hy, hP'⟩ := h
  exact ⟨w, hw, w₁, y, w₂, e, len, hQ y hy, hP _ hP'⟩

end

section
variable {t : Term} {n : Nat}

/-- `tuple_insert_at/3` of a gradual value into a gradual type of tuples gives a type exactly when
`tuple_insert_at_checked/3` does, and then its lower bound holds the tuples of the lower bound with a value of the
value's lower bound inserted. -/
theorem ins_top {X : List (Term × Term)} (gX : GC (level t (n + 1)) (.map X)) {v : Term} (gv : GC (level t n) v)
    (dlo : DE (level t n).E (lower v)) (dup : DE (level t n).E (upper v)) (i : Nat) {m : Nat}
    (hm : (level t (n + 1)).K + 26 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«tuple_insert_at/3» (D m) (.map X) (.integer i) v = .ok r ∧
      ((∃ R, r = .map R) ↔ (∀ q : PN t (n + 1), denD (lower (.map X)) q → q.1.1 = "tuple") ∧
        (∀ u, denD (lower (.map X)) (tpt (t := t) (n := n + 1) u) → i ≤ List.length u) ∧
        ∃ u, denD (upper (.map X)) (tpt (t := t) (n := n + 1) u) ∧ i ≤ List.length u) ∧
      ∀ R, r = .map R → ∀ p : PN t (n + 1), denD (.map R) p ↔
        InsAt (TT t (n + 1) (rmDyn X)) i ((level t (n + 1)).den (lower v)) p := by
  -- A static value inserts with tuple_insert_at_checked/3.
  have static : ∀ {x : Term}, (x = .atom "term" ∨ ∃ Z, x = .map Z ∧ mapLookup Z (.atom "dynamic") = none) →
      DE (level t n).E x → lower x = x →
      ∃ r, Elixir.Module.Types.Descr.«tuple_insert_at/3» (D m) (.map X) (.integer i) x = .ok r ∧
        ((∃ R, r = .map R) ↔ (∀ q : PN t (n + 1), denD (lower (.map X)) q → q.1.1 = "tuple") ∧
          (∀ u, denD (lower (.map X)) (tpt (t := t) (n := n + 1) u) → i ≤ List.length u) ∧
          ∃ u, denD (upper (.map X)) (tpt (t := t) (n := n + 1) u) ∧ i ≤ List.length u) ∧
        ∀ R, r = .map R → ∀ p : PN t (n + 1), denD (.map R) p ↔
          InsAt (TT t (n + 1) (rmDyn X)) i ((level t (n + 1)).den (lower x)) p := by
    intro x sx dx lx
    rw [insert_at_static _ _ _ sx, lx]
    have hx : (level t (n + 1)).E x := Or.inl dx
    obtain ⟨r, run, iff⟩ := ins_sem gX hx i hm
    refine ⟨r, run, iff, fun R e p => ?_⟩
    subst e
    exact (ins_checked_pts gX hx i hm run).2.2.2.1 p
  rcases gv.cases with rfl | ⟨V, rfl, hV⟩ | ⟨V, rfl, hV⟩ | ⟨V, Y, rfl, hV, hY⟩
  · exact static (Or.inl rfl) (Or.inl rfl) rfl
  · have lV : lower (.map V) = .map V := by simp [lower, rmDyn_static hV]
    exact static (Or.inr ⟨V, rfl, hV⟩) (lV ▸ dlo) lV
  all_goals
    obtain ⟨Dv, hD⟩ : ∃ Dv, mapLookup V (.atom "dynamic") = some Dv := ⟨_, hV⟩
    have uV : upper (.map V) = Dv := upper_dyn hD
    rw [uV] at dup
    have hx₁ : (level t (n + 1)).E Dv := Or.inl dup
    have hx₂ : (level t (n + 1)).E (.map (rmDyn V)) := Or.inl dlo
    obtain ⟨r₁, run₁, iff₁⟩ := ins_sem gX hx₁ i hm
    by_cases C : (∀ q : PN t (n + 1), denD (lower (.map X)) q → q.1.1 = "tuple") ∧
        (∀ u, denD (lower (.map X)) (tpt (t := t) (n := n + 1) u) → i ≤ List.length u) ∧
        ∃ u, denD (upper (.map X)) (tpt (t := t) (n := n + 1) u) ∧ i ≤ List.length u
    rotate_left
    · obtain h : r₁ = .atom "badindex" ∨ r₁ = .atom "badtuple" := by
        rcases ins_shape gX hx₁ i hm run₁ with h | h | ⟨R₁, rfl⟩
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd (iff₁.mp ⟨R₁, rfl⟩) C
      have e : Elixir.Module.Types.Descr.«tuple_insert_at/3» (D m) (.map X) (.integer i) (.map V) = .ok r₁ := by
        rw [Elixir.Module.Types.Descr.«tuple_insert_at/3».eq_def]
        rcases h with rfl | rfl <;>
          simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare,
            Erlang.maps.«take/2», hD, run₁, Erlang.erlang.«is_map/1», Erlang.erlang.«==/2», Lynx.Except.orElse]
      exact ⟨r₁, e, ⟨fun ⟨R, h'⟩ => absurd (iff₁.mp ⟨R, h'⟩) C, fun h' => absurd h' C⟩,
        fun R h' => absurd (iff₁.mp ⟨R, h'⟩) C⟩
    obtain ⟨R₁, rfl⟩ := iff₁.mpr C
    obtain ⟨gR₁, -, -, -, -⟩ := ins_checked_pts gX hx₁ i hm run₁
    obtain ⟨gW, nW, uW⟩ := wrap_gc gR₁
    have eS := next_empty dlo (m := m) (by rw [level_K] at hm ⊢; omega)
    simp only [lower] at eS
    by_cases es : ∀ p : PN t n, ¬denD (.map (rmDyn V)) p
    · have e : Elixir.Module.Types.Descr.«tuple_insert_at/3» (D m) (.map X) (.integer i) (.map V) =
          .ok (.map [(.atom "dynamic", upper (.map R₁))]) := by
        rw [Elixir.Module.Types.Descr.«tuple_insert_at/3».eq_def]
        simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare,
          Erlang.maps.«take/2», hD, run₁]
        cases hR : mapLookup R₁ (.atom "dynamic")
        case' none =>
          have e : upper (.map R₁) = .map R₁ := by simp [upper, hR]
          simp [Erlang.erlang.«is_map/1», Lynx.Except.orElse, Lynx.Except.tryWith, getMapKeys_single, hR, filter_dyn]
          rw [show Term.map [(.atom "dynamic", .map R₁)] = Term.map [(.atom "dynamic", upper (.map R₁))] by rw [e]]
        case' some d =>
          have e : upper (.map R₁) = d := upper_dyn hR
          simp [Erlang.erlang.«is_map/1», Lynx.Except.orElse, Lynx.Except.tryWith, getMapKeys_single, hR, filter_dyn]
          rw [← e]
        all_goals
          rw [eS, bp_true.mpr es]
          simp [boolAtom]
      refine ⟨_, e, ⟨fun _ => C, fun _ => ⟨_, rfl⟩⟩, fun R e' p => ?_⟩
      cases e'
      refine ⟨fun h => absurd h (nW p), fun ⟨w, _, w₁, y, w₂, _, _, hy, _⟩ => ?_⟩
      exact absurd ((den_succ dlo y).mp hy) (es y)
    · obtain ⟨r₂, run₂, iff₂⟩ := ins_sem gX hx₂ i hm
      obtain ⟨R₂, rfl⟩ := iff₂.mpr C
      obtain ⟨gR₂, -, -, sR₂, -⟩ := ins_checked_pts gX hx₂ i hm run₂
      obtain ⟨c, gc, rc, lo, -⟩ := gc_opt_union gW gR₂ [] (m := m) (by rw [level_K] at hm ⊢; omega)
      have e : Elixir.Module.Types.Descr.«tuple_insert_at/3» (D m) (.map X) (.integer i) (.map V) = .ok c := by
        rw [Elixir.Module.Types.Descr.«tuple_insert_at/3».eq_def]
        simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare,
          Erlang.maps.«take/2», hD, run₁]
        cases hR : mapLookup R₁ (.atom "dynamic")
        case' none =>
          have e : upper (.map R₁) = .map R₁ := by simp [upper, hR]
          simp [Erlang.erlang.«is_map/1», Lynx.Except.orElse, Lynx.Except.tryWith, getMapKeys_single, hR, filter_dyn]
          rw [show Term.map [(.atom "dynamic", .map R₁)] = Term.map [(.atom "dynamic", upper (.map R₁))] by rw [e]]
        case' some d =>
          have e : upper (.map R₁) = d := upper_dyn hR
          simp [Erlang.erlang.«is_map/1», Lynx.Except.orElse, Lynx.Except.tryWith, getMapKeys_single, hR, filter_dyn]
          rw [← e]
        all_goals
          rw [eS, bp_false.mpr es]
          simp [boolAtom, run₂, Elixir.Module.Types.Descr.«opt_union/2», rc]
      have sem : ∀ p : PN t (n + 1), denD c p ↔
          InsAt (TT t (n + 1) (rmDyn X)) i ((level t (n + 1)).den (lower (.map V))) p := fun p =>
        (lo p).trans ⟨fun h => h.elim (fun h => absurd h (nW p)) (sR₂ p).mp, fun h => Or.inr ((sR₂ p).mpr h)⟩
      obtain ⟨R, rfl⟩ : ∃ R, c = .map R := by
        rcases gc.shape with rfl | ⟨R, rfl⟩
        · obtain ⟨w, hw, -⟩ := (sem bitPt).mp (denD_term _)
          have := (hw [(.atom "tuple", .tuple #[.integer 61102469, .atom "open", .nil])]).mpr (by
            simp [TT, mapLookup, denTF_top])
          simp [bitPt, denD_map, mapLookup, dn_none] at this
        · exact ⟨R, rfl⟩
      exact ⟨_, e, ⟨fun _ => C, fun _ => ⟨R, rfl⟩⟩, fun R' e' p => by cases e'; exact sem p⟩


/-- Inserting less precise values into less precise tuples gives less precise tuples. -/
theorem insert_prec {X : List (Term × Term)} {a₂ v v₂ : Term} (gX : GC (level t (n + 1)) (.map X))
    (g₂ : GC (level t (n + 1)) a₂) (gv : GD t n v) (gv₂ : GD t n v₂) (i : Nat) {m : Nat}
    (hm : (level t (n + 1)).K + 26 ≤ m)
    (lo : ∀ q : PN t (n + 1), denD a₂ q → denD (.map X) q)
    (up : ∀ q : PN t (n + 1), denD (upper (.map X)) q → denD (upper a₂) q)
    (lov : ∀ y : PN t n, denD v₂ y → denD v y) (upv : ∀ y : PN t n, denD (upper v) y → denD (upper v₂) y)
    {R : List (Term × Term)}
    (run : Elixir.Module.Types.Descr.«tuple_insert_at/3» (D m) (.map X) (.integer i) v = .ok (.map R)) :
    ∃ R₂, Elixir.Module.Types.Descr.«tuple_insert_at/3» (D m) a₂ (.integer i) v₂ = .ok (.map R₂) ∧
      «precise?/2» (D m) (.map R) (.map R₂) = .ok (.atom "true") := by
  obtain ⟨r', run', iff, low⟩ := ins_top gX gv.1 gv.2.1 gv.2.2 i hm
  rw [run] at run'; cases run'
  obtain ⟨only, long, w, hw, lw⟩ := iff.mp ⟨R, rfl⟩
  obtain ⟨X₂, rfl⟩ : ∃ X₂, a₂ = .map X₂ := by
    rcases g₂.shape with rfl | ⟨X₂, rfl⟩
    · have := only bitPt ((denD_lower _ _).mpr (lo bitPt (denD_term _)))
      simp [bitPt] at this
    · exact ⟨X₂, rfl⟩
  obtain ⟨r₂, run₂, iff₂, low₂⟩ := ins_top g₂ gv₂.1 gv₂.2.1 gv₂.2.2 i hm
  obtain ⟨R₂, rfl⟩ := iff₂.mpr ⟨fun q h => only q ((denD_lower _ _).mpr (lo q ((denD_lower _ _).mp h))),
    fun u hu => long u ((denD_lower _ _).mpr (lo _ ((denD_lower _ _).mp hu))), w, up _ hw, lw⟩
  obtain ⟨gR, uR, -⟩ := ins_at gX gv.1 gv.2.1 gv.2.2 i hm run
  obtain ⟨gR₂, uR₂, -⟩ := ins_at g₂ gv₂.1 gv₂.2.1 gv₂.2.2 i hm run₂
  refine ⟨R₂, run₂, precise_true (by omega) gR gR₂ (fun p h => ?_) (fun p h => ?_)⟩
  · rw [denD_lower] at h ⊢
    refine (low R rfl p).mpr (insAt_mono (fun u hu => ?_) (fun y hy => ?_) ((low₂ R₂ rfl p).mp h))
    · exact (denD_tpt u).mp ((denD_rmDyn X _).mpr (lo _ ((denD_rmDyn X₂ _).mp ((denD_tpt u).mpr hu))))
    · exact (den_succ gv.2.1 y).mpr ((denD_lower _ _).mpr (lov y ((denD_lower _ _).mp ((den_succ gv₂.2.1 y).mp hy))))
  · refine (uR₂ p).mpr (insAt_mono (fun u hu => ?_) (fun y hy => ?_) ((uR p).mp h))
    · rcases hu with ⟨hu, lu⟩ | hu
      · exact Or.inl ⟨up _ hu, lu⟩
      · exact Or.inl ⟨up _ (gX.inv _ ((denD_rmDyn X _).mp ((denD_tpt u).mpr hu))),
          long u ((denD_tpt u).mpr hu)⟩
    · exact (den_succ gv₂.2.2 y).mpr (upv y ((den_succ gv.2.2 y).mp hy))

end

section
variable {t : Term} {n : Nat}

/-- `tuple_replace_at/3` deletes the element and inserts the value, when deleting gives a map. -/
theorem rep_join {X R₁ : List (Term × Term)} (i : Nat) (v r : Term) {m : Nat}
    (hd : Elixir.Module.Types.Descr.«tuple_delete_at/2» (D m) (.map X) (.integer i) = .ok (.map R₁))
    (hi : Elixir.Module.Types.Descr.«tuple_insert_at/3» (D m) (.map R₁) (.integer i) v = .ok r) :
    Elixir.Module.Types.Descr.«tuple_replace_at/3» (D m) (.map X) (.integer i) v = .ok r := by
  simp [Elixir.Module.Types.Descr.«tuple_replace_at/3», Lynx.Except.andAlso, Erlang.erlang.«is_integer/1»,
    Erlang.erlang.«>=/2», Int.isGE_compare, hd, Lynx.Except.orElse, Erlang.erlang.«is_map/1», hi]

/-- Replacing with less precise values in less precise tuples gives less precise tuples. -/
theorem replace_prec {X : List (Term × Term)} {a₂ v v₂ : Term} (gX : GC (level t (n + 1)) (.map X))
    (g₂ : GC (level t (n + 1)) a₂) (gv : GD t n v) (gv₂ : GD t n v₂) (i : Nat) {m : Nat}
    (hm : (level t (n + 1)).K + 26 ≤ m)
    (lo : ∀ q : PN t (n + 1), denD a₂ q → denD (.map X) q)
    (up : ∀ q : PN t (n + 1), denD (upper (.map X)) q → denD (upper a₂) q)
    (lov : ∀ y : PN t n, denD v₂ y → denD v y) (upv : ∀ y : PN t n, denD (upper v) y → denD (upper v₂) y)
    {R : List (Term × Term)}
    (run : Elixir.Module.Types.Descr.«tuple_replace_at/3» (D m) (.map X) (.integer i) v = .ok (.map R)) :
    ∃ R₂, Elixir.Module.Types.Descr.«tuple_replace_at/3» (D m) a₂ (.integer i) v₂ = .ok (.map R₂) ∧
      «precise?/2» (D m) (.map R) (.map R₂) = .ok (.atom "true") := by
  obtain ⟨R₁, hd, hi⟩ := rep_split gX i v hm run
  obtain ⟨R₁₂, hd₂, pd⟩ := delete_prec gX g₂ i hm lo up hd
  obtain ⟨gR₁, -, -, -, -⟩ := del_pts gX i hm hd
  obtain ⟨X₂, rfl⟩ : ∃ X₂, a₂ = .map X₂ := by
    rcases g₂.shape with rfl | ⟨X₂, rfl⟩
    · simp [Elixir.Module.Types.Descr.«tuple_delete_at/2»] at hd₂
    · exact ⟨X₂, rfl⟩
  obtain ⟨gR₁₂, -, -, -, -⟩ := del_pts g₂ i hm hd₂
  obtain ⟨lo₁, up₁⟩ := prec_bounds (by omega) ⟨gR₁, gR₁.low_tc, gR₁.up_tc⟩ ⟨gR₁₂, gR₁₂.low_tc, gR₁₂.up_tc⟩ pd
  obtain ⟨R₂, hi₂, pr⟩ := insert_prec gR₁ gR₁₂ gv gv₂ i hm lo₁ up₁ lov upv hi
  exact ⟨R₂, rep_join i v₂ _ hd₂ hi₂, pr⟩

end

section
variable {t : Term} {d : Nat}

/-- `tuple_fetch/2` on a gradual type gives a type when its lower bound holds only tuples and its upper bound one with a
value at the index. -/
theorem fetch_grad_ok {X : List (Term × Term)} (gX : GC (level t (d + 1)) (.map X)) {Dy : Term}
    (hD : mapLookup X (.atom "dynamic") = some Dy) (i : Nat) {m : Nat} (hm : (level t (d + 1)).K + 26 ≤ m)
    (only : ∀ v : PN t (d + 1), denD (lower (.map X)) v → v.1.1 = "tuple")
    (ne : ∃ v₁ y v₂, List.length v₁ = i ∧ denD Dy (tpt (t := t) (n := d + 1) (v₁ ++ y :: v₂))) :
    ∃ fl ty, Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map X) (.integer i) = .ok (.tuple #[fl, ty]) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have hK := level_K t d
  have hK' := level_K t (d + 1)
  have ef := (level t (d + 1)).ef
  obtain ⟨dDy, sS⟩ : DE (level t (d + 1)).E Dy ∧ DescrC (FunA (level t (d + 1)).E) (TField (level t (d + 1)).E)
      (LF (level t (d + 1)).E) (MField (level t (d + 1)).E) (rmDyn X) := by
    rcases gX with (h | ⟨X', e, sX⟩) | ⟨X', Dy', e, hD', tD, sS, -⟩
    · cases h
    · simp only [Term.map.injEq] at e; subst e; rw [sX.static] at hD; cases hD
    · simp only [Term.map.injEq] at e; subst e; rw [hD] at hD'; cases hD'; exact ⟨tD, sS⟩
  have dS : DE (level t (d + 1)).E (.map (rmDyn X)) := Or.inr ⟨_, rfl, sS⟩
  obtain ⟨dR, rt⟩ := rest_tuple dS
  have rto := next_empty dR (m := k + 3) (by omega)
  obtain ⟨dt, dO, rdt, sdt⟩ := fetch_static_sem dDy i (m := k + 3) (by omega)
  obtain ⟨st, sO, rst, sst⟩ := fetch_static_sem dS i (m := k + 3) (by omega)
  obtain ⟨eb, reb, seb⟩ := ef.empty_pub sdt.1
  obtain ⟨c₁, hc₁, sc₁, cases₁⟩ := el_canon sdt.1
  obtain ⟨R, rR, gR, s₁, s₂⟩ := dyn_el_union hc₁ sst.1 (m := k + 3) (by omega)
  obtain ⟨v₁, y, v₂, len, hy⟩ := ne
  have rkd : Elixir.Module.Types.Descr.«descr_key?/2» Dy (.atom "tuple") = .ok (boolAtom Bool.true) := by
    rcases dDy with rfl | ⟨DX, rfl, -⟩
    · rfl
    · rw [denD_tpt] at hy
      obtain ⟨b, e, -⟩ := hy
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, boolAtom, e]
  have to : ∀ v : PN t (d + 1), ¬denD (.map (rmT (rmDyn X))) v := fun v hv =>
    ((rt v).mp hv).2 (only v (by simpa [lower] using ((rt v).mp hv).1))
  have eb_f : eb = Bool.false := by
    cases eb
    · rfl
    · exact absurd (sdt.2.1 v₁ y v₂ len hy) (seb.mp rfl y)
  subst eb_f
  rw [Elixir.Module.Types.Descr.«tuple_fetch/2».eq_def]
  simp [Erlang.erlang.«</2», Int.compare_eq_lt, Erlang.maps.«take/2», hD, Elixir.Module.Types.Descr.«tuple_only?/1»,
    Erlang.maps.«remove/2»]
  simp only [filter_tdyn, filter_dyn, rto, rkd, rdt, rst, bp_true.mpr to]
  have reb' := reb (k + 3) (by omega)
  simp only [boolAtom, Lynx.Except.andAlso]
  simp only [reb', Lynx.Except.ok_bind]
  rcases cases₁ with ⟨de, rfl⟩ | ⟨hn, rfl⟩
  · rcases de with rfl | ⟨Z, rfl, sZ⟩
    · cases sO <;> cases dO <;> simp [boolAtom, Lynx.Except.orElse, getMapKeys, rR]
    · cases sO <;> cases dO <;>
        simp [boolAtom, Lynx.Except.orElse, getMapKeys_single, sZ.static, rR]
  · obtain ⟨q, SS, rfl⟩ := node_tuple hn
    have ex := expand_isT hn (k + 2)
    obtain ⟨Y, eY, sY⟩ := expN_map (.tuple #[.reference q, .map SS, gen]) (keyOf (level t d).nd)
    rw [eY] at ex rR
    have dY : Elixir.Module.Types.Descr.«dynamic/1» (D (k + 3)) (.map Y) =
        .ok (.map [(.atom "dynamic", .map Y)]) := by
      unfold Elixir.Module.Types.Descr.«dynamic/1»; simp [getMapKeys_single, sY]
    have gt : getMapKeys [Term.atom "dynamic"] (.tuple #[.reference q, .map SS, gen]) = [] := by simp [getMapKeys]
    cases sO <;> cases dO <;>
      simp [boolAtom, Lynx.Except.orElse, gt, ex, unfold_map, dY, rR]

/-- `tuple_fetch/2` on a gradual type, when it gives a type: the lower bound holds only tuples, the upper bound some with
a value at the index, it is optional exactly when the upper bound holds a shorter tuple, and the bounds of its type are
the values at the index of the tuples of the bounds. -/
theorem fetch_bounds {X : List (Term × Term)} (gX : GC (level t (d + 1)) (.map X)) (i : Nat) {m : Nat}
    (hm : (level t (d + 1)).K + 26 ≤ m) {fl ty : Term}
    (run : Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map X) (.integer i) = .ok (.tuple #[fl, ty])) :
    (∀ v : PN t (d + 1), denD (lower (.map X)) v → v.1.1 = "tuple") ∧
      (∃ v₁ y v₂, List.length v₁ = i ∧ denD (upper (.map X)) (tpt (t := t) (n := d + 1) (v₁ ++ y :: v₂))) ∧
      (fl = .atom "true" ↔ ∃ w, denD (upper (.map X)) (tpt (t := t) (n := d + 1) w) ∧ List.length w ≤ i) ∧
      (fl = .atom "true" ∨ fl = .atom "false") ∧ (mapLookup X (.atom "dynamic") = none → fl = .atom "false") ∧
      ∃ lr ur, Elixir.Module.Types.Descr.«lower_bound/1» (D m) ty = .ok lr ∧
        Elixir.Module.Types.Descr.«upper_bound/1» (D m) ty = .ok ur ∧ DE (level t d).E lr ∧ DE (level t d).E ur ∧
        (∀ y : (level t (d + 1)).V, denD lr y ↔ ∃ v₁ v₂ : List (level t (d + 1)).V, v₁.length = i ∧
          denD (lower (.map X)) (tpt (t := t) (n := d + 1) (v₁ ++ y :: v₂))) ∧
        ∀ y : (level t (d + 1)).V, denD ur y ↔ ∃ v₁ v₂ : List (level t (d + 1)).V, v₁.length = i ∧
          denD (upper (.map X)) (tpt (t := t) (n := d + 1) (v₁ ++ y :: v₂)) := by
  cases hD : mapLookup X (.atom "dynamic") with
  | none =>
    have dX := GC.static gX hD
    have lX : lower (.map X) = .map X := by simp [lower, rmDyn_static hD]
    have uX : upper (.map X) = .map X := by simp [upper, hD]
    rw [lX, uX]
    obtain ⟨res, run', ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨e, rfl, he, tonly, long, sE, bE⟩⟩ :=
      fetch_tuple (t := t) (n := d + 1) dX i (m := m) (by omega)
    · rw [run] at run'; cases run'
    · rw [run] at run'; cases run'
    rw [run] at run'
    simp only [Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at run'
    obtain ⟨rfl, rfl⟩ := run'
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    obtain ⟨c, hc, sc, ub, lb, -, -⟩ := el_ops he k
    have sem : ∀ y : (level t (d + 1)).V, denD c y ↔ ∃ v₁ v₂ : List (level t (d + 1)).V, v₁.length = i ∧
        denD (.map X) (tpt (t := t) (n := d + 1) (v₁ ++ y :: v₂)) := fun y => by
      rw [← sc y]
      constructor
      · intro h
        obtain ⟨v₁, v₂, len, h⟩ := bE y h
        exact ⟨v₁, v₂, len, (denD_tpt _).mpr h⟩
      · rintro ⟨v₁, v₂, len, h⟩
        exact sE v₁ y v₂ len ((denD_tpt _).mp h)
    obtain ⟨w, hw⟩ := tonly.2
    have lw := long w hw
    obtain ⟨v₁, y, v₂, rfl, len⟩ : ∃ v₁ y v₂, w = v₁ ++ y :: v₂ ∧ List.length v₁ = i := by
      refine ⟨w.take i, w[i]'lw, w.drop (i + 1), ?_, by simp; omega⟩
      simp
    refine ⟨tonly.1, ⟨v₁, y, v₂, len, (denD_tpt _).mpr hw⟩, ⟨fun h => (by simp at h), ?_⟩,
      Or.inr rfl, fun _ => rfl, c, c, lb, ub, hc, hc, sem, sem⟩
    rintro ⟨w, hw, l⟩
    have := long w ((denD_tpt w).mp hw); omega
  | some Dy =>
    obtain ⟨dt, dO, st, sO, sdt, sst, ⟨y₀, hy₀⟩, rfl, gR, sR, su, only⟩ := fetch_grad gX hD i hm run
    have sub : ∀ v : PN t (d + 1), denD (.map X) v → denD Dy v := by
      rcases gX with (h | ⟨X', e, sX⟩) | ⟨X', Dy', e, hD', -, -, sub⟩
      · cases h
      · simp only [Term.map.injEq] at e; subst e; rw [sX.static] at hD; cases hD
      · simp only [Term.map.injEq] at e; subst e; rw [hD] at hD'; cases hD'; exact sub
    have toDy : ∀ w, TT t (d + 1) (rmDyn X) w → denD Dy (tpt (t := t) (n := d + 1) w) := fun w h =>
      sub _ ((denD_rmDyn X _).mp ((denD_tpt w).mpr h))
    have lX : lower (.map X) = .map (rmDyn X) := by simp [lower]
    rw [lX, upper_dyn hD]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    obtain ⟨w₁, w₂, wl, hw⟩ := sdt.2.2.2 y₀ hy₀
    refine ⟨only, ⟨w₁, y₀, w₂, wl, hw⟩, ?_, by cases sO <;> cases dO <;> simp [boolAtom], fun h => (by simp at h),
      lower ty, upper ty, lower_bound_run gR.shape, upper_bound_run gR.ub, gR.low_tc, gR.up_tc, fun y => ?_,
      fun y => ?_⟩
    · constructor
      · intro h
        cases sO
        · cases dO
          · simp [boolAtom] at h
          · exact sdt.2.2.1.mp rfl
        · obtain ⟨w, hw, l⟩ := sst.2.2.1.mp rfl
          exact ⟨w, toDy w hw, l⟩
      · intro h
        have : dO = Bool.true := sdt.2.2.1.mpr h
        subst this; cases sO <;> rfl
    · refine (denD_lower ty y).trans ((sR y).trans ?_)
      constructor
      · intro h
        obtain ⟨v₁, v₂, len, h⟩ := sst.2.2.2 y h
        exact ⟨v₁, v₂, len, (denD_tpt _).mpr h⟩
      · rintro ⟨v₁, v₂, len, h⟩
        exact sst.2.1 v₁ y v₂ len ((denD_tpt _).mp h)
    · refine (su y).trans ?_
      constructor
      · rintro (h | h)
        · exact sdt.2.2.2 y h
        · obtain ⟨v₁, v₂, len, h⟩ := sst.2.2.2 y h
          exact ⟨v₁, v₂, len, toDy _ h⟩
      · rintro ⟨v₁, v₂, len, h⟩
        exact Or.inl (sdt.2.1 v₁ y v₂ len h)

/-- `tuple_fetch/2` gives a type when the lower bound holds only tuples, the upper bound one with a value at the index,
and a static type no shorter tuple. -/
theorem fetch_ok {X : List (Term × Term)} (gX : GC (level t (d + 1)) (.map X)) (i : Nat) {m : Nat}
    (hm : (level t (d + 1)).K + 26 ≤ m) (only : ∀ v : PN t (d + 1), denD (lower (.map X)) v → v.1.1 = "tuple")
    (ne : ∃ v₁ y v₂, List.length v₁ = i ∧ denD (upper (.map X)) (tpt (t := t) (n := d + 1) (v₁ ++ y :: v₂)))
    (long : mapLookup X (.atom "dynamic") = none →
      ∀ w, denD (upper (.map X)) (tpt (t := t) (n := d + 1) w) → i < List.length w) :
    ∃ fl ty, Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map X) (.integer i) = .ok (.tuple #[fl, ty]) := by
  cases hD : mapLookup X (.atom "dynamic") with
  | some Dy =>
    rw [upper_dyn hD] at ne
    exact fetch_grad_ok gX hD i hm only ne
  | none =>
    have dX := GC.static gX hD
    have lX : lower (.map X) = .map X := by simp [lower, rmDyn_static hD]
    have uX : upper (.map X) = .map X := by simp [upper, hD]
    rw [lX] at only; rw [uX] at ne long
    obtain ⟨v₁, y, v₂, -, hy⟩ := ne
    obtain ⟨res, run, ⟨rfl, nT⟩ | ⟨rfl, -, w, hw, l⟩ | ⟨e, rfl, -⟩⟩ :=
      fetch_tuple (t := t) (n := d + 1) dX i (m := m) (by omega)
    · exact absurd ⟨only, _, (denD_tpt _).mp hy⟩ nT
    · have := long hD w ((denD_tpt w).mpr hw); omega
    · exact ⟨_, _, run⟩

/-- The fetches of less precise tuples are less precise. -/
theorem fetch_prec {X : List (Term × Term)} {a₂ : Term} (gX : GC (level t (d + 1)) (.map X))
    (g₂ : GC (level t (d + 1)) a₂) (i : Nat) {m : Nat} (hm : (level t (d + 1)).K + 26 ≤ m)
    (lo : ∀ v : PN t (d + 1), denD a₂ v → denD (.map X) v)
    (up : ∀ v : PN t (d + 1), denD (upper (.map X)) v → denD (upper a₂) v)
    (kd : mapLookup X (.atom "dynamic") ≠ none → ∃ X₂, a₂ = .map X₂ ∧ mapLookup X₂ (.atom "dynamic") ≠ none)
    {fl ty : Term} (run : Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) (.map X) (.integer i) = .ok (.tuple #[fl, ty])) :
    ∃ fl₂ ty₂, Elixir.Module.Types.Descr.«tuple_fetch/2» (D m) a₂ (.integer i) = .ok (.tuple #[fl₂, ty₂]) ∧
      (fl = .atom "true" ∨ fl = .atom "false") ∧ (fl₂ = .atom "true" ∨ fl₂ = .atom "false") ∧
      (fl = .atom "true" → fl₂ = .atom "true") ∧ «precise?/2» (D m) ty ty₂ = .ok (.atom "true") := by
  obtain ⟨onlyA, neA, flA, bA, stA, lrA, urA, lA, uA, dlA, duA, slA, suA⟩ := fetch_bounds gX i hm run
  have lo' : ∀ v : PN t (d + 1), denD (lower a₂) v → denD (lower (.map X)) v := fun v h =>
    (denD_lower _ _).mpr (lo v ((denD_lower _ _).mp h))
  obtain ⟨X₂, rfl⟩ : ∃ X₂, a₂ = .map X₂ := by
    rcases g₂.shape with rfl | ⟨X₂, rfl⟩
    · have := onlyA bitPt (lo' bitPt (by simp [lower, denD_term]))
      simp [bitPt] at this
    · exact ⟨X₂, rfl⟩
  have long : mapLookup X₂ (.atom "dynamic") = none →
      ∀ w, denD (upper (.map X₂)) (tpt (t := t) (n := d + 1) w) → i < List.length w := by
    -- A static less precise type holds the tuples of a static precise type.
    intro hD₂ w hw
    have hA : mapLookup X (.atom "dynamic") = none := Classical.byContradiction fun h => by
      obtain ⟨X₂', e, h'⟩ := kd h
      simp only [Term.map.injEq] at e; subst e; exact h' hD₂
    have uX₂ : upper (.map X₂) = .map X₂ := by simp [upper, hD₂]
    have uX : upper (.map X) = .map X := by simp [upper, hA]
    have lX₂ : lower (.map X₂) = .map X₂ := by simp [lower, rmDyn_static hD₂]
    have lX : lower (.map X) = .map X := by simp [lower, rmDyn_static hA]
    rw [uX₂] at hw
    have hA' := lo' _ (by rw [lX₂]; exact hw)
    rw [lX] at hA'
    refine Classical.byContradiction fun l => ?_
    have := flA.mpr ⟨w, by rw [uX]; exact hA', by omega⟩
    rw [stA hA] at this; simp at this
  obtain ⟨v₁, y, v₂, len, hn⟩ := neA
  obtain ⟨fl₂, ty₂, run₂⟩ := fetch_ok g₂ i hm (fun v h => onlyA v (lo' v h)) ⟨v₁, y, v₂, len, up _ hn⟩ long
  obtain ⟨-, -, flB, bB, -, lrB, urB, lB, uB, dlB, duB, slB, suB⟩ := fetch_bounds g₂ i hm run₂
  refine ⟨fl₂, ty₂, run₂, bA, bB, fun h => flB.mpr (have ⟨w, hw, l⟩ := flA.mp h; ⟨w, up _ hw, l⟩),
    precise_of_bounds (n := d) (by rw [level_K] at hm ⊢; omega) lA uA lB uB dlA duA dlB duB
      (fun y h => ?_) (fun y h => ?_)⟩
  · obtain ⟨v₁, v₂, len, h⟩ := (slB y).mp h
    exact (slA y).mpr ⟨v₁, v₂, len, lo' _ h⟩
  · obtain ⟨v₁, v₂, len, h⟩ := (suA y).mp h
    exact (suB y).mpr ⟨v₁, v₂, len, up _ h⟩

end

section
variable {t : Term} {n : Nat}

theorem sdel {Z : List (Term × Term)} (hZ : DE (level t n).E (.map Z)) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {md : String} (hmd : Mode md) (st : Bool)
    {m : Nat} (hm : (level t n).K + 26 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map Z)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true") (boolAtom st) =
        .ok res ∧
      (((res = .atom "badmap" ∨ res = .tuple #[.map [], .map [], .nil, .atom "false"]) ∧ ∀ w, ¬MT t n Z w) ∨
        (∃ w, MT t n Z w) ∧ ∃ (T : Term) (Y : List (Term × Term)) (er : List Term) (f : Bool), res = .tuple #[T, .map Y, Term.list er, boolAtom f] ∧ (level t n).E T ∧
          (∀ x, (level t n).den T x ↔ ∃ w, MT t n Z w ∧
            ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧ w κ = some x) ∧
          DE (level t n).E (.map Y) ∧ (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          (∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨ KindHeld (MT t n Z) d)) ∧
            ∀ w, MT t n Y w ↔ UpdSemD (level t n).den (MT t n Z) rk neg Dm md w) ∧
          (f = Bool.true ↔ FoundS (MT t n Z) rk neg Ds md st)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  have sZ := de_map hZ
  cases hb : mapLookup Z (.atom "map") with
  | none =>
    refine ⟨_, ?_, Or.inl ⟨Or.inr rfl, fun w h => by simp [MT, hb] at h⟩⟩
    unfold Elixir.Module.Types.Descr.«map_update_static/5»
    simp [getMapKeys_single, hb]
  | some b =>
    have fb : MField (level t n).E b := fieldC_map (sZ.fields "map" b hb)
    have mt : ∀ w, MT t n Z w ↔ denMF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [MT, hb]
    have conv : (fun u => denMF (level t n).E (level t n).den b u = Bool.true) = MT t n Z :=
      funext fun u => propext (mt u).symm
    obtain ⟨r1, run1, h1⟩ := del_update_static (st := st) (level t n).ef (n := k) (by omega) hmd ok nr hNa hb fb
    obtain ⟨r0, run0, h0⟩ := del_update_static (st := Bool.true) (level t n).ef (n := k) (by omega) hmd ok nr hNa hb fb
    have run0' : Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 6)) (.map Z)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (.tuple #[.tuple #[.atom "constant", .tuple #[.map [], .atom "true"]], .atom md])
        (.atom "true") (.atom "true") = .ok r0 := run0
    rcases h1 with ⟨rfl, emp⟩ | ⟨T, Y, er, f, rfl, ⟨w₀, hw₀⟩, Dm, mDm, hY⟩
    · exact ⟨_, run1, Or.inl ⟨Or.inl rfl, fun w h => by rw [mt, emp w] at h; cases h⟩⟩
    -- The old values, from the static run.
    rcases val_old_static (level t n).ef (n := k) (by omega) _ md hmd
        (fun lines hl bd a r h => del_key (level t n).ef (n := k + 2) (by omega) lines hl md hmd bd a r h) ok nr hb fb
        r0 run0' with rfl | ⟨T0, Y0, er0, f0, rfl, -, hT0, sT0⟩
    · rcases h0 with ⟨-, emp0⟩ | ⟨_, _, _, _, e, -⟩
      · rw [emp0 w₀] at hw₀; cases hw₀
      · cases e
    have eT : T = T0 := by
      rcases static_rel (k + 5) _ _ _ _ _ _ run1 run0 with e | ⟨v, bd, e₁, f₁, e₂, f₂, h₁, h₂⟩
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e ⊢; exact e.1
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at h₁ h₂; rw [h₁.1, h₂.1]
    subst eT
    -- The found flag.
    rcases static_found (level t n).ef (n := k) (by omega) (.tuple #[.map [], .atom "true"]) hmd st
        (fun lines hl bd a => hk_del (level t n).ef (n := k + 2) (by omega) hmd lines hl bd a) ok nr hb fb _ run1 with
      e | ⟨T', Y', er', f', e, -, hf⟩
    · cases e
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
    obtain ⟨-, rfl, rfl, rfl⟩ := e
    rw [conv] at hY mDm hf
    rcases hY with ⟨rfl, emp⟩ | ⟨r, rfl, fr, sr⟩
    · refine ⟨_, run1, Or.inr ⟨⟨w₀, (mt w₀).mpr hw₀⟩, T, [], er', f', rfl, hT0, fun x => by rw [sT0]; simp only [mt],
        Or.inr ⟨_, rfl, descrC_nil⟩, fun q hq => ?_, ⟨Dm, mDm, fun w => ?_⟩, hf⟩⟩
      · rw [denD_map] at hq
        simp [mapLookup, dn_none] at hq
      · simp only [MT, mapLookup, List.find?_nil, Option.map_none, reduceCtorEq, false_and, exists_false, false_iff, equalExact_eq_decide]
        exact emp w
    · refine ⟨_, run1, Or.inr ⟨⟨w₀, (mt w₀).mpr hw₀⟩, T, _, er', f', rfl, hT0, fun x => by rw [sT0]; simp only [mt],
        Or.inr ⟨_, rfl, descrC_map fr⟩, fun q hq => ?_, ⟨Dm, mDm, fun w => ?_⟩, hf⟩⟩
      · rw [denD_map] at hq
        by_cases e : q.1.1 = "map"
        · exact e
        · simp [mapLookup, e, dn_none] at hq
      · rw [← sr]; simp [MT, mapLookup]

end
section
variable {t : Term} {d : Nat}

/-- `opt_union/2` of an element and a type with only a dynamic part: the element, with the dynamic part in the upper
bound. -/
theorem el_dyn_union {c₁ : Term} (hc₁ : DE (level t d).E c₁) {e : Term} (he : (level t (d + 1)).E e) {m : Nat}
    (hm : (level t d).K + 14 ≤ m) :
    ∃ R, Elixir.Module.Types.Descr.«opt_union/2» (D m) e (.map [(.atom "dynamic", c₁)]) = .ok R ∧
      GC (level t d) R ∧ (∀ v : PN t d, denD R v ↔ (level t (d + 1)).den e v) ∧
      ∀ v : PN t d, denD (upper R) v ↔ (level t (d + 1)).den e v ∨ denD c₁ v := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have gA : GC (level t d) (.map [(.atom "dynamic", c₁)]) := by
    refine Or.inr ⟨_, c₁, rfl, by simp [mapLookup], hc₁, ?_, fun v hv => ?_⟩
    · rw [show rmDyn [(Term.atom "dynamic", c₁)] = [] by simp [rmDyn]]; exact descrC_nil
    · rw [← denD_rmDyn, show rmDyn [(Term.atom "dynamic", c₁)] = [] by simp [rmDyn]] at hv
      simp [denD_map, mapLookup, dn_none] at hv
  have noA : ∀ v : PN t d, ¬denD (.map [(.atom "dynamic", c₁)]) v := fun v hv => by
    rw [← denD_rmDyn, show rmDyn [(Term.atom "dynamic", c₁)] = [] by simp [rmDyn]] at hv
    simp [denD_map, mapLookup, dn_none] at hv
  have upA : upper (.map [(.atom "dynamic", c₁)]) = c₁ := by simp [upper, mapLookup]
  obtain ⟨c, hc, sem, h⟩ := el_canon he
  rcases h with ⟨de, rfl⟩ | ⟨hn, rfl⟩
  · obtain ⟨R, gR, run, s₁, s₂⟩ := gc_opt_union (GC.tc de) gA [] (m := k + 2) hm
    refine ⟨R, run, gR, fun v => ?_, fun v => ?_⟩
    · rw [s₁, sem]; exact ⟨fun h => h.resolve_right (noA v), Or.inl⟩
    · rw [s₂, upA, sem, upper_tc de]
  · obtain ⟨r, S, rfl⟩ := node_tuple hn
    have ex := expand_isT hn (k + 1)
    obtain ⟨Y, eY, sY⟩ := expN_map (.tuple #[.reference r, .map S, gen]) (keyOf (level t d).nd)
    rw [eY] at ex sem hc
    have hY : GC (level t d) (.map Y) := GC.tc hc
    obtain ⟨R, gR, run, lo, up, -⟩ := merge_aligned (opt_union_op (n := k + 1) (by omega) [])
      (opt_union_dyn_op (n := k) (by omega) []) (fun x y => opt_union_dyn _ x y _) hY gA
    refine ⟨R, ?_, gR, fun v => ?_, fun v => ?_⟩
    · rw [← run]
      unfold Elixir.Module.Types.Descr.«opt_union/2» Elixir.Module.Types.Descr.«opt_union/3»
      have hA : mapLookup [(Term.atom "dynamic", c₁)] (.atom "dynamic") = some c₁ := by simp [mapLookup]
      have gN : getMapKeys [Term.atom "dynamic"] (.tuple #[.reference r, .map S, gen]) = [] := by simp [getMapKeys]
      have cm : Term.compare (Term.fuel (.tuple #[.reference r, .map S, gen]) (.map [])) (.tuple #[.reference r, .map S, gen])
          (.map []) ≠ .eq := by
        rw [Term.compare_step]; simp [Compare.compareStep]
      simp [getMapKeys_single, Erlang.erlang.«==/2», sY, hA, ex, unfold_map, Erlang.maps.«put/3», alignT, cm]
    · rw [lo, sem]; exact ⟨fun h => h.resolve_right (noA v), Or.inl⟩
    · rw [up, upA, sem, upper_tc hc]

end

section
variable {t : Term} {d : Nat}

/-- The maps of deleting a key from the maps of a type. -/
def DelS (t : Term) (n : Nat) (M : MW (level t n).V → Prop) (rk : List String) (neg : Term) (Ds : List String)
    (md : String) (w : MW (level t n).V) : Prop :=
  ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨ KindHeld M d)) ∧
    UpdSemD (level t n).den M rk neg Dm md w

/-- The values the maps of a type hold at the keys of a split. -/
def OldS {V : Type} (M : MW V → Prop) (rk : List String) (neg : Term) (Ds : List String) (x : V) : Prop :=
  ∃ w, M w ∧ ∃ κ, SplitKey (rk.map Term.atom) neg (Ds.map Term.atom) κ ∧ w κ = some x

theorem mt_dynL' {a : Term} (ha : TC (level t d) a) (u : MW (level t d).V) :
    MT t d (dynL a) u ↔ denD a (mpt (t := t) (n := d) u) := by
  rcases ha with rfl | ⟨Y, rfl, -⟩
  · exact ⟨fun _ => denD_term _, fun _ => mt_top u⟩
  · exact (denD_mpt u).symm

/-- Deleting a key from a gradual map type of the next level, asking for the old values: it gives a type exactly when the
static part holds only maps and the dynamic part some map, and the update of the dynamic part finds a key; then the
deletions from the static maps, with those from the dynamic maps in the upper bound, and the same for the old values. -/
theorem gdel {X : List (Term × Term)} (gX : GC (level t (d + 1)) (.map X)) {Dy : Term}
    (hD : mapLookup X (.atom "dynamic") = some Dy) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {md : String} (hmd : Mode md) {m : Nat}
    (hm : (level t (d + 1)).K + 30 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true") = .ok r ∧
      ((∃ T R er, r = .tuple #[T, R, er]) ↔ (∀ q : PN t (d + 1), denD (.map (rmDyn X)) q → q.1.1 = "map") ∧
        (∃ w, MT t (d + 1) (dynL Dy) w) ∧ FoundS (MT t (d + 1) (dynL Dy)) rk neg Ds md Bool.false) ∧
      ∀ T R er, r = .tuple #[T, R, er] → GC (level t (d + 1)) R ∧
        (∀ q : PN t (d + 1), denD (upper R) q → q.1.1 = "map") ∧
        (∀ w, denD R (mpt (t := t) (n := d + 1) w) ↔ (∃ u, MT t (d + 1) (rmDyn X) u) ∧
          DelS t (d + 1) (MT t (d + 1) (rmDyn X)) rk neg Ds md w) ∧
        (∀ w, denD (upper R) (mpt (t := t) (n := d + 1) w) ↔ ((∃ u, MT t (d + 1) (rmDyn X) u) ∧
          DelS t (d + 1) (MT t (d + 1) (rmDyn X)) rk neg Ds md w) ∨
          DelS t (d + 1) (MT t (d + 1) (dynL Dy)) rk neg Ds md w) ∧
        ∃ lt ut, Elixir.Module.Types.Descr.«lower_bound/1» (D m) T = .ok lt ∧
          Elixir.Module.Types.Descr.«upper_bound/1» (D m) T = .ok ut ∧ DE (level t d).E lt ∧ DE (level t d).E ut ∧
          (∀ x : PN t d, denD lt x ↔ OldS (MT t (d + 1) (rmDyn X)) rk neg Ds x) ∧
          ∀ x : PN t d, denD ut x ↔ OldS (MT t (d + 1) (rmDyn X)) rk neg Ds x ∨
            OldS (MT t (d + 1) (dynL Dy)) rk neg Ds x := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
  have hK := level_K t d
  have hK' := level_K t (d + 1)
  rcases gX with tX | ⟨X', Dy', e, hD', tD, dS, incl⟩
  · rcases tX with h | ⟨X', e, sX'⟩
    · cases h
    · simp only [Term.map.injEq] at e; subst e; rw [sX'.static] at hD; cases hD
  simp only [Term.map.injEq] at e; subst e
  rw [hD] at hD'; cases hD'
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def]
  simp only [Erlang.maps.«take/2», hD, equalExact_eq_decide]
  have eS : (X.filter fun entry => !decide (compareExact ((Term.atom "dynamic").fuel entry.fst) (Term.atom "dynamic") entry.fst = .eq)) = rmDyn X := rfl
  rw [eS]
  simp only [Lynx.Except.ok_bind]
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 8))
      (.function false "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-1-" 1 #[]) #[r] =
        Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1» r := fun r => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-1-/1».pure]
  have dSt : DE (level t (d + 1)).E (.map (rmDyn X)) := Or.inr ⟨_, rfl, dS⟩
  obtain ⟨dR, sRm⟩ := rest_map dSt
  have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 8)) (.map (rmDyn X)) =
      .ok (boolAtom (bp (∀ q : PN t (d + 1), ¬denD (.map (rmM (rmDyn X))) q))) := by
    simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
    exact next_empty dR (by omega)
  have dDy : DE (level t (d + 1)).E (.map (dynL Dy)) := by
    rcases tD with rfl | ⟨Y, rfl, sY⟩
    · exact mapTop_de
    · exact Or.inr ⟨Y, rfl, sY⟩
  have stD : ∀ st, Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 8)) Dy
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true") st =
      Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 8)) (.map (dynL Dy))
      (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true") st := by
    intro st
    rcases tD with rfl | ⟨Y, rfl, -⟩
    · conv => lhs; rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def]
      simp [Lynx.Term.getMapKeys, dynL, topM]
    · rfl
  have keyD : Elixir.Module.Types.Descr.«descr_key?/2» Dy (.atom "map") =
      .ok (boolAtom (mapLookup (dynL Dy) (.atom "map")).isSome) := by
    rcases tD with rfl | ⟨Y, rfl, -⟩
    · simp [Elixir.Module.Types.Descr.«descr_key?/2», dynL, topM, mapLookup, boolAtom, pure, Except.pure]
    · cases h : mapLookup Y (.atom "map") <;>
        simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, dynL, h, boolAtom]
  rw [stD]
  have onlyIff : (∀ q : PN t (d + 1), ¬denD (.map (rmM (rmDyn X))) q) ↔
      ∀ q : PN t (d + 1), denD (.map (rmDyn X)) q → q.1.1 = "map" :=
    ⟨fun h q hq => Classical.byContradiction fun nq => h q ((sRm q).mpr ⟨hq, nq⟩),
      fun h q hq => ((sRm q).mp hq).2 (h q ((sRm q).mp hq).1)⟩
  rcases Classical.em (¬∀ q : PN t (d + 1), ¬denD (.map (rmM (rmDyn X))) q) with hmo | hmo
  · rw [bp_false.mpr hmo] at mo
    refine ⟨.atom "badmap", ?_, ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨h, _⟩ => absurd (onlyIff.mpr h) hmo⟩,
      fun _ _ _ h => by cases h⟩
    cases hk : (mapLookup (dynL Dy) (.atom "map")).isSome <;>
      simp [keyD, hk, mo, Lynx.Except.andAlso, boolAtom, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1»]
  rw [bp_true.mpr (Classical.not_not.mp hmo)] at mo
  have onlyS := onlyIff.mp (Classical.not_not.mp hmo)
  rcases Classical.em ((mapLookup (dynL Dy) (.atom "map")).isSome = Bool.false) with hbm | hbm
  · refine ⟨.atom "badmap", ?_, ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨_, ⟨w, b, hb, _⟩, _⟩ => (by simp [hb] at hbm)⟩,
      fun _ _ _ h => by cases h⟩
    simp [keyD, hbm, Lynx.Except.andAlso, boolAtom, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1»]
  have kt : Elixir.Module.Types.Descr.«descr_key?/2» Dy (.atom "map") = .ok (.atom "true") := by
    simp only [Bool.not_eq_false] at hbm
    simp [keyD, hbm, boolAtom]
  -- The static part, as the gradual update sees it.
  obtain ⟨rS, rrS, hS⟩ := sdel (t := t) (n := d + 1) dSt ok nr hNa hmd Bool.true (m := k + 8) (by omega)
  simp only [boolAtom, ↓reduceIte] at rrS
  obtain ⟨sv, Sd, se, eS', hsv, ssv, dSd, oSd, sSd⟩ : ∃ (sv : Term) (Sd : List (Term × Term)) (se : List Term),
      ((rS = .atom "badmap" ∧ sv = .map [] ∧ Sd = [] ∧ se = []) ∨
        ∃ fs, rS = .tuple #[sv, .map Sd, Term.list se, fs]) ∧
      (level t (d + 1)).E sv ∧ (∀ x, (level t (d + 1)).den sv x ↔ OldS (MT t (d + 1) (rmDyn X)) rk neg Ds x) ∧
      DE (level t (d + 1)).E (.map Sd) ∧ (∀ q : PN t (d + 1), denD (.map Sd) q → q.1.1 = "map") ∧
      ∀ w, denD (.map Sd) (mpt (t := t) (n := d + 1) w) ↔ (∃ u, MT t (d + 1) (rmDyn X) u) ∧
        DelS t (d + 1) (MT t (d + 1) (rmDyn X)) rk neg Ds md w := by
    have ef := (level t (d + 1)).ef
    have emp : ∀ (hno : ∀ w, ¬MT t (d + 1) (rmDyn X) w), (level t (d + 1)).E (.map []) ∧
        (∀ x, (level t (d + 1)).den (.map []) x ↔ OldS (MT t (d + 1) (rmDyn X)) rk neg Ds x) ∧
        DE (level t (d + 1)).E (.map []) ∧ (∀ q : PN t (d + 1), denD (.map []) q → q.1.1 = "map") ∧
        ∀ w, denD (.map []) (mpt (t := t) (n := d + 1) w) ↔ (∃ u, MT t (d + 1) (rmDyn X) u) ∧
          DelS t (d + 1) (MT t (d + 1) (rmDyn X)) rk neg Ds md w := fun hno =>
      ⟨ef.none, fun x => ⟨fun h => absurd h (ef.den_none x), fun ⟨w, hw, _⟩ => absurd hw (hno w)⟩,
        Or.inr ⟨_, rfl, descrC_nil⟩, fun q h => by simp [denD_map, mapLookup, dn_none] at h,
        fun w => ⟨fun h => by simp [denD_map, mapLookup, dn_none] at h, fun ⟨⟨u, hu⟩, _⟩ => absurd hu (hno u)⟩⟩
    rcases hS with ⟨hrS | hrS, hno⟩ | ⟨exS, TS, YS, erS, fS, rfl, hTS, sTS, dYS, oYS, ⟨DmS, mDmS, sYS⟩, -⟩
    · exact ⟨.map [], [], [], Or.inl ⟨hrS, rfl, rfl, rfl⟩, emp hno⟩
    · exact ⟨.map [], [], [], Or.inr ⟨_, by rw [hrS]⟩, emp hno⟩
    · refine ⟨TS, YS, erS, Or.inr ⟨_, rfl⟩, hTS, fun x => (sTS x).trans Iff.rfl, dYS, oYS, fun w => ?_⟩
      rw [denD_mpt, sYS]
      exact ⟨fun h => ⟨exS, DmS, mDmS, h⟩, fun ⟨_, Dm, mDm, h⟩ =>
        del_mono (level t (d + 1)).ef.den_none (fun u h => h) hmd ok ok nr (fun κ h => h) mDm mDmS h⟩
  -- The static block of the gradual branch.
  -- The dynamic part.
  obtain ⟨rd, rrd, hd⟩ := sdel (t := t) (n := d + 1) dDy ok nr hNa hmd Bool.false (m := k + 8) (by omega)
  simp only [boolAtom, Bool.false_eq_true, ↓reduceIte] at rrd
  simp only [kt, mo, boolAtom, ↓reduceIte, Lynx.Except.andAlso, rrd, Lynx.Except.ok_bind]
  rcases hd with ⟨hrd | hrd, noD⟩ | ⟨exD, Td, Yd, erd, fd, rfl, hTd, sTd, dYd, oYd, ⟨Dmd, mDmd, sYd⟩, hfd⟩
  · subst hrd
    exact ⟨.atom "badmap", by simp [bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1»],
      ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨_, ⟨w, hw⟩, _⟩ => absurd hw (noD w)⟩, fun _ _ _ h => by cases h⟩
  · subst hrd
    refine ⟨.tuple #[.atom "error", Term.list se], ?_,
      ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨_, ⟨w, hw⟩, _⟩ => absurd hw (noD w)⟩, fun _ _ _ h => by cases h⟩
    rcases eS' with ⟨rfl, rfl, rfl, rfl⟩ | ⟨fs, rfl⟩ <;>
      simp [rrS, Lynx.Term.isMember, app_nil_r, app_nil0, Term.list]
  have dmS : ∀ {M : MW (level t (d + 1)).V → Prop} {Dm : List String},
      (∀ d', d' ∈ Dm ↔ d' ∈ Ds ∧ (md ≠ "reject" ∨ KindHeld M d')) →
      ∀ w, DelS t (d + 1) M rk neg Ds md w ↔ UpdSemD (level t (d + 1)).den M rk neg Dm md w := fun mDm w =>
    ⟨fun ⟨Dm', mDm', h⟩ => del_mono (level t (d + 1)).ef.den_none (fun u h => h) hmd ok ok nr (fun κ h => h) mDm' mDm h,
      fun h => ⟨_, mDm, h⟩⟩
  cases fd
  · have nf : ¬FoundS (MT t (d + 1) (dynL Dy)) rk neg Ds md Bool.false := fun h => by
      have := hfd.mpr h; cases this
    refine ⟨.tuple #[.atom "error", Term.list (se ++ erd)], ?_,
      ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨_, _, h⟩ => absurd h nf⟩, fun _ _ _ h => by cases h⟩
    rcases eS' with ⟨rfl, rfl, rfl, rfl⟩ | ⟨fs, rfl⟩ <;>
      simp [rrS, Lynx.Term.isMember, append_list, app_nil_l, boolAtom]
  have fd' : FoundS (MT t (d + 1) (dynL Dy)) rk neg Ds md Bool.false := hfd.mp rfl
  -- The union of the static deletions and the dynamic ones.
  have fin : ∃ c, Elixir.Module.Types.Descr.«opt_union/2» (D (k + 8)) (.map Sd) (.map [(.atom "dynamic", .map Yd)]) =
        .ok c ∧ GC (level t (d + 1)) c ∧ (∀ q : PN t (d + 1), denD (upper c) q → q.1.1 = "map") ∧
      (∀ q : PN t (d + 1), denD c q ↔ denD (.map Sd) q) ∧
      ∀ q : PN t (d + 1), denD (upper c) q ↔ denD (.map Sd) q ∨ denD (.map Yd) q := by
    have noP : ∀ q : PN t (d + 1), ¬denD (.map [(.atom "dynamic", .map Yd)]) q := fun q h => by
      have := (denD_rmDyn [(.atom "dynamic", .map Yd)] q).mpr h
      rw [rmDyn_cons_dyn] at this
      simp [rmDyn, denD_map, mapLookup, dn_none] at this
    have gY : GC (level t (d + 1)) (.map [(.atom "dynamic", .map Yd)]) :=
      Or.inr ⟨_, .map Yd, rfl, by simp [mapLookup], dYd, by rw [rmDyn_cons_dyn]; exact descrC_nil,
        fun q h => absurd h (noP q)⟩
    obtain ⟨c, gc, rc, sc₁, sc₂⟩ := gc_opt_union (GC.tc dSd) gY [] (m := k + 8) (by omega)
    have uS : upper (.map Sd) = .map Sd := upper_tc dSd
    have uY : upper (.map [(.atom "dynamic", .map Yd)]) = .map Yd := upper_dyn (by simp [mapLookup])
    refine ⟨c, by simpa [Elixir.Module.Types.Descr.«opt_union/2»] using rc, gc, fun q h => ?_, fun q => ?_,
      fun q => ?_⟩
    · rw [sc₂, uS, uY] at h
      rcases h with h | h
      · exact oSd q h
      · exact oYd q h
    · rw [sc₁]; simp [noP q]
    · rw [sc₂, uS, uY]
  obtain ⟨c, rc, gc, oc, sc₁, sc₂⟩ := fin
  -- The union of the static old values and the dynamic ones.
  obtain ⟨c₁, hc₁, sc₁', cases₁⟩ := el_canon hTd
  obtain ⟨RT, rRT, gRT, lRT, uRT⟩ := el_dyn_union hc₁ hsv (m := k + 8) (by omega)
  refine ⟨.tuple #[RT, c, Term.list (se ++ erd)], ?_, ⟨fun _ => ⟨onlyS, exD, fd'⟩, fun _ => ⟨_, _, _, rfl⟩⟩,
    fun T R er e => ?_⟩
  · have sYd : mapLookup Yd (.atom "dynamic") = none := (de_map dYd).static
    have fY : (Yd.find? fun entry => decide (compareExact ((Term.atom "dynamic").fuel entry.fst) (Term.atom "dynamic")
        entry.fst = Ordering.eq)) = none := by
      simpa [mapLookup] using sYd
    rcases cases₁ with ⟨de, rfl⟩ | ⟨hn, rfl⟩
    · rcases de with rfl | ⟨Z, rfl, sZ⟩
      · rcases eS' with ⟨rfl, rfl, rfl, rfl⟩ | ⟨fs, rfl⟩ <;>
          simp [rrS, boolAtom, Lynx.Term.isMember, getMapKeys, fY, rRT, rc, append_list, app_nil_l]
      · rcases eS' with ⟨rfl, rfl, rfl, rfl⟩ | ⟨fs, rfl⟩ <;>
          simp [rrS, boolAtom, Lynx.Term.isMember, getMapKeys_single, sZ.static, sYd, rRT, rc, append_list, app_nil_l]
    · obtain ⟨q, SS, rfl⟩ := node_tuple hn
      have ex := expand_isT hn (k + 7)
      obtain ⟨Y, eY, sY⟩ := expN_map (.tuple #[.reference q, .map SS, gen]) (keyOf (level t d).nd)
      rw [eY] at ex rRT
      have dY : Elixir.Module.Types.Descr.«dynamic/1» (D (k + 8)) (.map Y) =
          .ok (.map [(.atom "dynamic", .map Y)]) := by
        unfold Elixir.Module.Types.Descr.«dynamic/1»; simp [getMapKeys_single, sY]
      have gt : getMapKeys [Term.atom "dynamic"] (.tuple #[.reference q, .map SS, gen]) = [] := by simp [getMapKeys]
      rcases eS' with ⟨rfl, rfl, rfl, rfl⟩ | ⟨fs, rfl⟩ <;>
        simp [rrS, boolAtom, Lynx.Term.isMember, gt, ex, unfold_map, dY, getMapKeys_single, sYd, rRT, rc, append_list,
          app_nil_l]
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  refine ⟨gc, oc, fun w => (sc₁ _).trans (sSd w), fun w => ?_, lower RT, upper RT, lower_bound_run gRT.shape,
    upper_bound_run gRT.ub, gRT.low_tc, gRT.up_tc, fun x => (denD_lower RT x).trans ((lRT x).trans (ssv x)),
    fun x => (uRT x).trans (or_congr (ssv x) ((sc₁' x).symm.trans (sTd x)))⟩
  rw [sc₂, sSd, denD_mpt, sYd, dmS mDmd]

end

section
variable {t : Term} {d : Nat}

/-- `map_update/5` deleting a static key type from a gradual map type of the next level, asking for the old values: it
gives a type exactly when the lower bound holds only maps and the upper bound some, and the update of the upper bound
finds a key (as a static update when the type is static); then the deletions from the maps of the lower bound, with
those of the upper bound in its upper bound, and the same for the old values. -/
theorem gdel_sem {X : List (Term × Term)} (gX : GC (level t (d + 1)) (.map X)) {key : Term} {rk Ds : List String}
    {neg : Term} {m : Nat}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key =
      .ok (splitT (rk.map Term.atom) neg (Ds.map Term.atom)))
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {md : String} (hmd : Mode md)
    (hm : (level t (d + 1)).K + 30 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key (.atom "delete") (.atom md) (.atom "true") =
        .ok r ∧
      ((∃ T R er, r = .tuple #[T, R, er]) ↔ (∀ q : PN t (d + 1), denD (lower (.map X)) q → q.1.1 = "map") ∧
        (∃ w, MT t (d + 1) (dynL (upper (.map X))) w) ∧
        FoundS (MT t (d + 1) (dynL (upper (.map X)))) rk neg Ds md (mapLookup X (.atom "dynamic")).isNone) ∧
      ∀ T R er, r = .tuple #[T, R, er] → GC (level t (d + 1)) R ∧
        (∀ q : PN t (d + 1), denD (upper R) q → q.1.1 = "map") ∧
        (∀ w, denD R (mpt (t := t) (n := d + 1) w) ↔ (∃ u, MT t (d + 1) (rmDyn X) u) ∧
          DelS t (d + 1) (MT t (d + 1) (rmDyn X)) rk neg Ds md w) ∧
        (∀ w, denD (upper R) (mpt (t := t) (n := d + 1) w) ↔ ((∃ u, MT t (d + 1) (rmDyn X) u) ∧
          DelS t (d + 1) (MT t (d + 1) (rmDyn X)) rk neg Ds md w) ∨
          DelS t (d + 1) (MT t (d + 1) (dynL (upper (.map X)))) rk neg Ds md w) ∧
        ∃ lt ut, Elixir.Module.Types.Descr.«lower_bound/1» (D m) T = .ok lt ∧
          Elixir.Module.Types.Descr.«upper_bound/1» (D m) T = .ok ut ∧ DE (level t d).E lt ∧ DE (level t d).E ut ∧
          (∀ x : PN t d, denD lt x ↔ OldS (MT t (d + 1) (rmDyn X)) rk neg Ds x) ∧
          ∀ x : PN t d, denD ut x ↔ OldS (MT t (d + 1) (rmDyn X)) rk neg Ds x ∨
            OldS (MT t (d + 1) (dynL (upper (.map X)))) rk neg Ds x := by
  rw [upd5_del (.map X) hk hmd]
  cases hD : mapLookup X (.atom "dynamic") with
  | some Dy =>
    have lX : lower (.map X) = .map (rmDyn X) := by simp [lower]
    rw [lX, upper_dyn hD]
    simpa using gdel gX hD ok nr hNa hmd hm
  | none =>
    have hX := GC.static gX hD
    have sX := de_map hX
    have eX : rmDyn X = X := rmDyn_static hD
    have lX : lower (.map X) = .map X := by simp [lower, eX]
    have uX : upper (.map X) = .map X := by simp [upper, hD]
    rw [lX, uX, eX]
    simp only [dynL, Option.isNone_none]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
    rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def]
    simp only [Erlang.maps.«take/2», sX.static, Lynx.Except.ok_bind]
    have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 8))
        (.function false "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-0-" 1 #[]) #[r] =
          Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1» r := fun r => by
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-0-/1».pure]
    have dmS : ∀ {M : MW (level t (d + 1)).V → Prop} {Dm : List String},
        (∀ d', d' ∈ Dm ↔ d' ∈ Ds ∧ (md ≠ "reject" ∨ KindHeld M d')) →
        ∀ w, DelS t (d + 1) M rk neg Ds md w ↔ UpdSemD (level t (d + 1)).den M rk neg Dm md w := fun mDm w =>
      ⟨fun ⟨Dm', mDm', h⟩ => del_mono (level t (d + 1)).ef.den_none (fun u h => h) hmd ok ok nr (fun κ h => h) mDm' mDm h,
        fun h => ⟨_, mDm, h⟩⟩
    cases hb : mapLookup X (.atom "map") with
    | none =>
      refine ⟨.atom "badmap", ?_, ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨_, ⟨w, b, e, _⟩, _⟩ => by rw [hb] at e; cases e⟩,
        fun _ _ _ h => by cases h⟩
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso,
        bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
    | some b =>
      obtain ⟨dR, sR⟩ := rest_map hX
      have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "map") = .ok (.atom "true") := by
        simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
      have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 8)) (.map X) =
          .ok (boolAtom (bp (∀ v : PN t (d + 1), ¬denD (.map (rmM X)) v))) := by
        simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
        exact next_empty dR (by omega)
      have onlyIff : (∀ q : PN t (d + 1), ¬denD (.map (rmM X)) q) ↔
          ∀ q : PN t (d + 1), denD (.map X) q → q.1.1 = "map" :=
        ⟨fun h q hq => Classical.byContradiction fun nq => h q ((sR q).mpr ⟨hq, nq⟩),
          fun h q hq => ((sR q).mp hq).2 (h q ((sR q).mp hq).1)⟩
      by_cases restE : ∀ v : PN t (d + 1), ¬denD (.map (rmM X)) v
      rotate_left
      · rw [bp_false.mpr restE] at mo
        refine ⟨.atom "badmap", ?_, ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨h, _⟩ => absurd (onlyIff.mpr h) restE⟩,
          fun _ _ _ h => by cases h⟩
        simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1», boolAtom]
      rw [bp_true.mpr restE] at mo
      obtain ⟨rS, rrS, hS⟩ := sdel (t := t) (n := d + 1) hX ok nr hNa hmd Bool.true (m := k + 8) (by omega)
      simp only [boolAtom, ↓reduceIte] at rrS
      rcases hS with ⟨hrS | hrS, noS⟩ | ⟨exS, T, Y, er, f, rfl, hT, sT, dY, oY, ⟨Dm, mDm, sY⟩, hf⟩
      · subst hrS
        refine ⟨.atom "badmap", ?_, ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨_, ⟨w, hw⟩, _⟩ => absurd hw (noS w)⟩,
          fun _ _ _ h => by cases h⟩
        simp [key, mo, rrS, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
      · subst hrS
        refine ⟨.tuple #[.atom "error", .nil], ?_,
          ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨_, ⟨w, hw⟩, _⟩ => absurd hw (noS w)⟩, fun _ _ _ h => by cases h⟩
        simp [key, mo, rrS, Lynx.Except.andAlso, Lynx.Term.isMember]
      cases f
      · have nf : ¬FoundS (MT t (d + 1) X) rk neg Ds md Bool.true := fun h => by
          have := hf.mpr h; cases this
        refine ⟨.tuple #[.atom "error", Term.list er], ?_,
          ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨_, _, h⟩ => absurd h nf⟩, fun _ _ _ h => by cases h⟩
        simp [key, mo, rrS, Lynx.Except.andAlso, Lynx.Term.isMember, boolAtom]
      refine ⟨.tuple #[T, .map Y, Term.list er], ?_,
        ⟨fun _ => ⟨(onlyIff.mp restE), exS, hf.mp rfl⟩, fun _ => ⟨_, _, _, rfl⟩⟩, fun T' R er' e => ?_⟩
      · simp [key, mo, rrS, Lynx.Except.andAlso, Lynx.Term.isMember, boolAtom]
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      obtain ⟨c, hc, sc, ub, lb, -, -⟩ := el_ops hT (k + 7)
      have uY : upper (.map Y) = .map Y := upper_tc dY
      have sem : ∀ w, denD (.map Y) (mpt (t := t) (n := d + 1) w) ↔ (∃ u, MT t (d + 1) X u) ∧
          DelS t (d + 1) (MT t (d + 1) X) rk neg Ds md w := fun w => by
        rw [denD_mpt, sY, dmS mDm]; exact ⟨fun h => ⟨exS, h⟩, fun h => h.2⟩
      refine ⟨GC.tc dY, fun q h => oY q (by rwa [uY] at h), sem, fun w => ?_, c, c, lb, ub, hc, hc,
        fun x => (sc x).symm.trans (sT x), fun x => ((sc x).symm.trans (sT x)).trans (or_self_iff).symm⟩
      rw [uY, sem]
      exact ⟨Or.inl, fun h => h.elim id fun h => ⟨exS, h⟩⟩

end

section
variable {t : Term} {d : Nat}

theorem delS_mono {M₁ M₂ : MW (level t (d + 1)).V → Prop} (hM : ∀ u, M₁ u → M₂ u) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = []) {md : String}
    (hmd : Mode md) {w : MW (level t (d + 1)).V} (h : DelS t (d + 1) M₁ rk neg Ds md w) :
    DelS t (d + 1) M₂ rk neg Ds md w := by
  classical
  obtain ⟨Dm₁, mDm₁, h⟩ := h
  have mDm₂ : ∀ d', d' ∈ Ds.filter (fun d' => decide (md ≠ "reject" ∨ KindHeld M₂ d')) ↔
      d' ∈ Ds ∧ (md ≠ "reject" ∨ KindHeld M₂ d') := fun d' => by simp
  exact ⟨_, mDm₂, del_mono (level t (d + 1)).ef.den_none hM hmd ok ok nr (fun κ h => h) mDm₁ mDm₂ h⟩

theorem oldS_mono {V : Type} {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {rk Ds : List String} {neg : Term}
    {x : V} (h : OldS M₁ rk neg Ds x) : OldS M₂ rk neg Ds x :=
  let ⟨w, hw, κ, hκ, e⟩ := h; ⟨w, hM w hw, κ, hκ, e⟩

theorem foundS_weak {V : Type} {M : MW V → Prop} {rk Ds : List String} {neg : Term} {md : String} {st : Bool}
    (h : FoundS M rk neg Ds md st) : FoundS M rk neg Ds md Bool.false := by
  rcases h with h | h | ⟨a, b, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨a, b, h.imp id fun ⟨a', ma, h1, _⟩ => ⟨a', ma, h1, fun e => by cases e⟩⟩)

theorem foundS_mono {V : Type} {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {rk Ds : List String} {neg : Term}
    {md : String} (h : FoundS M₁ rk neg Ds md Bool.false) : FoundS M₂ rk neg Ds md Bool.false := by
  rcases h with h | ⟨a, b, x, w, hw, h⟩ | ⟨a, b, h | ⟨a', ma, ⟨w, x, hw, e⟩, -⟩⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨a, b, x, w, hM w hw, h⟩)
  · obtain ⟨s, ms, w, hw, hk⟩ := h
    exact Or.inr (Or.inr ⟨a, b, Or.inl ⟨s, ms, w, hM w hw, hk⟩⟩)
  · exact Or.inr (Or.inr ⟨a, b, Or.inr ⟨a', ma, ⟨w, x, hM w hw, e⟩, fun e => by cases e⟩⟩)

theorem foundS_congr {V : Type} {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u ↔ M₂ u) {rk Ds : List String} {neg : Term}
    {md : String} {st : Bool} (h : FoundS M₁ rk neg Ds md st) : FoundS M₂ rk neg Ds md st := by
  have e : M₁ = M₂ := funext fun u => propext (hM u)
  exact e ▸ h

/-- Inclusions of map types follow from their maps. -/
theorem via_mpt {a b : Term} (ha : a = .atom "term" ∨ ∃ Y, a = .map Y) (hb : b = .atom "term" ∨ ∃ Y, b = .map Y)
    (only : ∀ q : PN t (d + 1), denD a q → q.1.1 = "map")
    (h : ∀ w, denD a (mpt (t := t) (n := d + 1) w) → denD b (mpt (t := t) (n := d + 1) w)) :
    ∀ v : PN t (d + 1), denD a v → denD b v := by
  intro v hv
  obtain ⟨w, hw⟩ := pt_map v (only v hv)
  rcases ha with rfl | ⟨Y, rfl⟩
  · have := only bitPt (denD_term _); simp [bitPt] at this
  have hb' := h w ((denD_mpt w).mpr ((hw Y).mp hv))
  rcases hb with rfl | ⟨Y', rfl⟩
  · exact denD_term _
  · exact (hw Y').mpr ((denD_mpt w).mp hb')

/-- Deleting from less precise maps is less precise, as is the old type. -/
theorem del_prec {X : List (Term × Term)} {a₂ : Term} (gX : GC (level t (d + 1)) (.map X))
    (g₂ : GC (level t (d + 1)) a₂) {key : Term} {rk Ds : List String} {neg : Term} {m : Nat}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key =
      .ok (splitT (rk.map Term.atom) neg (Ds.map Term.atom)))
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {md : String} (hmd : Mode md)
    (hm : (level t (d + 1)).K + 30 ≤ m)
    (lo : ∀ v : PN t (d + 1), denD a₂ v → denD (.map X) v)
    (up : ∀ v : PN t (d + 1), denD (upper (.map X)) v → denD (upper a₂) v)
    (kd : mapLookup X (.atom "dynamic") ≠ none → ∃ X₂, a₂ = .map X₂ ∧ mapLookup X₂ (.atom "dynamic") ≠ none)
    {T R er : Term}
    (run : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key (.atom "delete") (.atom md) (.atom "true") =
      .ok (.tuple #[T, R, er])) :
    ∃ T₂ R₂ er₂, Elixir.Module.Types.Descr.«map_update/5» (D m) a₂ key (.atom "delete") (.atom md) (.atom "true") =
        .ok (.tuple #[T₂, R₂, er₂]) ∧ «precise?/2» (D m) T T₂ = .ok (.atom "true") ∧
      «precise?/2» (D m) R R₂ = .ok (.atom "true") := by
  obtain ⟨r, run', iffA, semA⟩ := gdel_sem gX hk ok nr hNa hmd hm
  rw [run] at run'; cases run'
  obtain ⟨onlyA, neA, fA⟩ := iffA.mp ⟨_, _, _, rfl⟩
  have lo' : ∀ v : PN t (d + 1), denD (lower a₂) v → denD (lower (.map X)) v := fun v h =>
    (denD_lower _ _).mpr (lo v ((denD_lower _ _).mp h))
  obtain ⟨X₂, rfl⟩ : ∃ X₂, a₂ = .map X₂ := by
    rcases g₂.shape with rfl | ⟨X₂, rfl⟩
    · have := onlyA bitPt (lo' bitPt (by simp [lower, denD_term]))
      simp [bitPt] at this
    · exact ⟨X₂, rfl⟩
  -- The maps of the bounds.
  have muA : ∀ w, MT t (d + 1) (dynL (upper (.map X))) w → MT t (d + 1) (dynL (upper (.map X₂))) w := fun w h =>
    (mt_dynL' g₂.up_tc w).mpr (up _ ((mt_dynL' gX.up_tc w).mp h))
  have msB : ∀ w, MT t (d + 1) (rmDyn X₂) w → MT t (d + 1) (rmDyn X) w := fun w h =>
    (denD_mpt w).mp ((denD_rmDyn X _).mpr (lo _ ((denD_rmDyn X₂ _).mp ((denD_mpt w).mpr h))))
  have msA : ∀ w, MT t (d + 1) (rmDyn X) w → MT t (d + 1) (dynL (upper (.map X))) w := fun w h =>
    (mt_dynL' gX.up_tc w).mpr (GC.inv gX _ ((denD_rmDyn X _).mp ((denD_mpt w).mpr h)))
  -- The less precise type succeeds.
  have fB : FoundS (MT t (d + 1) (dynL (upper (.map X₂)))) rk neg Ds md (mapLookup X₂ (.atom "dynamic")).isNone := by
    cases hD₂ : mapLookup X₂ (.atom "dynamic") with
    | some _ => exact foundS_mono muA (foundS_weak fA)
    | none =>
      have hA : mapLookup X (.atom "dynamic") = none := Classical.byContradiction fun h => by
        obtain ⟨X₂', e, h'⟩ := kd h
        simp only [Term.map.injEq] at e; subst e; exact h' hD₂
      rw [hA] at fA
      refine foundS_congr (fun u => ⟨muA u, fun h => ?_⟩) fA
      have uX₂ : upper (.map X₂) = .map X₂ := by simp [upper, hD₂]
      have uX : upper (.map X) = .map X := by simp [upper, hA]
      rw [uX₂] at h; rw [uX]
      simp only [dynL] at h ⊢
      have := msB u (by rwa [rmDyn_static hD₂])
      rwa [rmDyn_static hA] at this
  obtain ⟨r₂, run₂, iffB, semB⟩ := gdel_sem g₂ hk ok nr hNa hmd hm
  obtain ⟨T₂, R₂, er₂, rfl⟩ := iffB.mpr ⟨fun q h => onlyA q (lo' q h),
    let ⟨w, hw⟩ := neA; ⟨w, muA w hw⟩, fB⟩
  obtain ⟨gR, oR, lR, uR, lt, ut, lA, uA, dlA, duA, slA, suA⟩ := semA T R er rfl
  obtain ⟨gR₂, oR₂, lR₂, uR₂, lt₂, ut₂, lB, uB, dlB, duB, slB, suB⟩ := semB T₂ R₂ er₂ rfl
  have hm' : (level t d).K + 23 ≤ m := by rw [level_K] at hm ⊢; omega
  refine ⟨T₂, R₂, er₂, run₂, precise_of_bounds (n := d) hm' lA uA lB uB dlA duA dlB duB
    (fun x h => (slA x).mpr (oldS_mono msB ((slB x).mp h)))
    (fun x h => (suB x).mpr (((suA x).mp h).elim (fun h => Or.inr (oldS_mono (fun u h => muA u (msA u h)) h))
      (fun h => Or.inr (oldS_mono muA h)))), precise_of (n := d + 1) (by omega) gR gR₂ ?_ ?_⟩
  · refine via_mpt gR₂.shape gR.shape (fun q h => oR₂ q (GC.inv gR₂ q h)) fun w h => ?_
    obtain ⟨⟨u, hu⟩, h⟩ := (lR₂ w).mp h
    exact (lR w).mpr ⟨⟨u, msB u hu⟩, delS_mono msB ok nr hmd h⟩
  · refine via_mpt (Or.imp id (fun ⟨Y, e, _⟩ => ⟨Y, e⟩) gR.up_tc) (Or.imp id (fun ⟨Y, e, _⟩ => ⟨Y, e⟩) gR₂.up_tc)
      oR fun w h => ?_
    refine (uR₂ w).mpr (Or.inr ?_)
    rcases (uR w).mp h with ⟨-, h⟩ | h
    · exact delS_mono (fun u h => muA u (msA u h)) ok nr hmd h
    · exact delS_mono muA ok nr hmd h

end


section
variable {t : Term} {n : Nat}

theorem ptKind_mem (v : PN t n) : ptKind v ∈ domainKinds := by
  obtain ⟨⟨name, i, _, _⟩, mem, ok⟩ := v
  unfold ptKind
  simp only
  split
  · rename_i h
    have hi : i < 8 := ok.2.1 h
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
    all_goals first | (simp [bitKind, domainKinds]) | omega
  · rename_i h
    simp [names] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [domainKinds]

/-- A pair point. -/
def PairW (p : PN t (n + 1)) (k x : (level t (n + 1)).V) : Prop :=
  ∀ Y, denD (.map Y) p ↔ TT t (n + 1) Y [k, x]

/-- The pairs `map_to_list/1` gives, from the maps of a type: the values at named atoms with those atoms, the values at
keys of other kinds with keys of their kind, and the values at infinitely many atoms with any atom. -/
def InnerX (t : Term) (n : Nat) (M : MW (level t (n + 1)).V → Prop) (p : PN t (n + 1)) : Prop :=
  (∃ s k x, PairW p k x ∧ (level t (n + 1)).den (atomT s) k ∧ ∃ w, M w ∧ w (.atom s) = some x) ∨
  (∃ kk i k x, PairW p k x ∧ (level t (n + 1)).den (dkdT (domKind kk)) k ∧ ∃ w, M w ∧ w (.dom kk i) = some x) ∨
  (∃ k x, PairW p k x ∧ (level t (n + 1)).den (dkdT "atom") k ∧
    ∀ F : List String, ∃ w, M w ∧ ∃ c, c ∉ F ∧ w (.atom c) = some x)

theorem innerX_mono {M₁ M₂ : MW (level t (n + 1)).V → Prop} (hM : ∀ u, M₁ u → M₂ u) {p : PN t (n + 1)}
    (h : InnerX t n M₁ p) : InnerX t n M₂ p := by
  rcases h with ⟨s, k, x, pw, hk, w, hw, e⟩ | ⟨kk, i, k, x, pw, hk, w, hw, e⟩ | ⟨k, x, pw, hk, hF⟩
  · exact Or.inl ⟨s, k, x, pw, hk, w, hM w hw, e⟩
  · exact Or.inr (Or.inl ⟨kk, i, k, x, pw, hk, w, hM w hw, e⟩)
  · exact Or.inr (Or.inr ⟨k, x, pw, hk, fun F => let ⟨w, hw, c, hc, e⟩ := hF F; ⟨w, hM w hw, c, hc, e⟩⟩)

theorem pairW_den {inner : Term} (dI : DE (level t (n + 1)).E inner) {p : PN t (n + 1)} {k x : (level t (n + 1)).V}
    (pw : PairW p k x) : denD inner p ↔ denD inner (tpt (t := t) (n := n + 1) [k, x]) := by
  rcases dI with rfl | ⟨Y, rfl, -⟩
  · simp [denD_term]
  · exact (pw Y).trans (denD_tpt _).symm

theorem atoms_out (F : List String) {c : String}
    (h : mapLookup ((F.map Term.atom).map (·, Term.nil)) (.atom c) = none) : c ∉ F := fun mc => by
  have := (lookup_nil_pairs (F.map Term.atom) (fun a ma => let ⟨s, _, e⟩ := List.mem_map.mp ma; ⟨s, e.symm⟩)
    (.atom c)).mpr (List.mem_map_of_mem mc)
  rw [h] at this; cases this

/-- The values a line's tag allows at atoms are at infinitely many atoms of its maps. -/
theorem atom_vals {L : Term} (hL : MLine (level t (n + 1)).E L) (ne : ∃ w, InMLine (level t (n + 1)).den L w)
    {x : (level t (n + 1)).V} (hx : LineTag (level t (n + 1)).den L "atom" x) (F : List String) :
    ∃ w, InMLine (level t (n + 1)).den L w ∧ ∃ c, c ∉ F ∧ w (.atom c) = some x := by
  obtain ⟨w, hw, κ, hκ, wκ⟩ := tag_witness (level t (n + 1)).ef hL ne (by simp [domainKinds]) hx
    ((F.map Term.atom).map (·, Term.nil))
  rcases hκ with ⟨-, c, rfl, hc⟩ | ⟨k, i, e, -⟩
  · exact ⟨w, hw, c, atoms_out F hc, wκ⟩
  · exact absurd e.symm (domKind_ne_atom k)

/-- `map_to_list_static/3` on the lines of a map field: exactly the pairs `InnerX` gives. -/
theorem inner_exact {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) {b : Term} (fb : MField (level t (n + 1)).E b)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine (level t (n + 1)).E L ∧ ∃ w, InMLine (level t (n + 1)).den L w)
    (sl : ∀ w, denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true ↔
      ∃ L ∈ lines, InMLine (level t (n + 1)).den L w) :
    ∃ inner, Elixir.Module.Types.Descr.«map_to_list_static/3» (D (M + 5)) b (Term.list lines) mtlF = .ok inner ∧
      DE (level t (n + 1)).E inner ∧ InnerSem t n b inner ∧
      ∀ p, denD inner p ↔ InnerX t n (fun w => denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true) p := by
  have ef := (level t (n + 1)).ef
  have hl' : ∀ L ∈ lines, MLine (level t (n + 1)).E L := fun L m => (hl L m).1
  have hnone : ∀ x, ¬(level t (n + 1)).den (.map []) x := fun x h => ef.den_none x h
  obtain ⟨inner, run, dI, sIs⟩ := inner_run hM fb lines hl sl
  refine ⟨inner, run, dI, sIs, fun p => ?_⟩
  have dA := (dkdT_run (t := t) (n := n) (d := "atom") (by simp [domainKinds])).2
  rcases mtl_static3 hM fb lines hl with ⟨L, mL, ⟨l, negs, eL⟩, P, rP, dP, sP⟩ |
    ⟨no, S, inner', run', hS, named, dI', sI⟩
  · rw [run] at rP; cases rP
    rw [sP]
    obtain ⟨tag, l', negs', e, g, -, -⟩ := hl' L mL
    subst e
    obtain ⟨rfl, -, -⟩ := tuple3_inj eL
    have tagAny : ∀ d x, LineTag (level t (n + 1)).den (.tuple #[.atom "open", fieldsTerm l', Term.list negs']) d x :=
      fun d x => ⟨_, l', negs', rfl, by simp [tagType]; exact ef.den_term x⟩
    constructor
    · rintro ⟨w', hw', k, x, rfl, -, -⟩
      by_cases ka : (toPN k).1.1 = "atom"
      · refine Or.inr (Or.inr ⟨k, x, hw', (den_succ dA.de (toPN k)).mpr (dA.atoms rfl _ ka), fun F => ?_⟩)
        obtain ⟨w, hw, c, hc, wc⟩ := atom_vals (hl' _ mL) (hl _ mL).2 (tagAny "atom" x) F
        exact ⟨w, (sl w).mpr ⟨_, mL, hw⟩, c, hc, wc⟩
      · have da : ptKind (toPN k) ≠ "atom" := by
          unfold ptKind; split
          · rename_i hb; generalize (toPN k).1.2.1 = i
            rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [bitKind]
          · exact ka
        obtain ⟨w, hw, κ, hκ, wκ⟩ := tag_witness ef (hl' _ mL) (hl _ mL).2 (ptKind_mem (toPN k))
          (tagAny _ x) []
        rcases hκ with ⟨h, -⟩ | ⟨kk, i, e, rfl⟩
        · exact absurd h da
        have dT := (dkdT_run (t := t) (n := n) (domKind_mem kk)).2
        exact Or.inr (Or.inl ⟨kk, i, k, x, hw', (den_succ dT.de (toPN k)).mpr (dT.kinds (domKind_ne_atom kk) _ e),
          w, (sl w).mpr ⟨_, mL, hw⟩, wκ⟩)
    · rintro (⟨s, k, x, pw, -⟩ | ⟨kk, i, k, x, pw, -⟩ | ⟨k, x, pw, -⟩) <;>
        exact ⟨[k, x], pw, k, x, rfl, ef.den_term k, ef.den_term x⟩
  · rw [run] at run'; cases run'
    rw [sI]
    constructor
    · rintro (⟨L, mL, dl, l, negs, rfl, d, v, mem, md, -, w', hw', k, x, rfl, hk, hvx⟩ |
        ⟨s, -, w', hw', k, x, rfl, hk, L, mL, w, hL, hws⟩)
      · obtain ⟨tag, l', negs', e, g, -, -⟩ := (hl _ mL).1
        obtain ⟨e₁, -, -⟩ := tuple3_inj e
        have dv : DomsV (level t (n + 1)).E dl := by
          rcases g with rfl | rfl | ⟨dl', rfl, dv⟩
          · exact absurd e₁ (fieldsTerm_ne_atom dl "open")
          · exact absurd e₁ (fieldsTerm_ne_atom dl "closed")
          · rwa [fieldsTerm_inj e₁]
        have lt : LineTag (level t (n + 1)).den (.tuple #[fieldsTerm dl, fieldsTerm l, Term.list negs]) d x :=
          ⟨fieldsTerm dl, l, negs, rfl, by rw [tagType_dom, dom_lookup_of_mem dv mem]; exact hvx⟩
        by_cases da : d = "atom"
        · subst da
          refine Or.inr (Or.inr ⟨k, x, hw', hk, fun F => ?_⟩)
          obtain ⟨w, hw, c, hc, wc⟩ := atom_vals (hl _ mL).1 (hl _ mL).2 lt F
          exact ⟨w, (sl w).mpr ⟨_, mL, hw⟩, c, hc, wc⟩
        · obtain ⟨w, hw, κ, hκ, wκ⟩ := tag_witness ef (hl _ mL).1 (hl _ mL).2 md lt []
          rcases hκ with ⟨h, -⟩ | ⟨kk, i, rfl, rfl⟩
          · exact absurd h da
          exact Or.inr (Or.inl ⟨kk, i, k, x, hw', hk, w, (sl w).mpr ⟨_, mL, hw⟩, wκ⟩)
      · exact Or.inl ⟨s, k, x, hw', hk, w, (sl w).mpr ⟨L, mL, hL⟩, hws⟩
    · rintro (⟨s, k, x, pw, hk, w, hw, hx⟩ | ⟨kk, i, k, x, pw, hk, w, hw, hx⟩ | ⟨k, x, pw, hk, hF⟩)
      · rw [← sI, pairW_den dI pw]
        exact sIs.1 w hw s x hx k hk
      · obtain ⟨L, mL, hL⟩ := (sl w).mp hw
        obtain ⟨tag, l, negs, rfl, g, -, -⟩ := hl' L mL
        have hd := (inMLine_iff.mp hL).1.doms kk i
        rw [hx] at hd
        rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
        · exact absurd ⟨_, _, rfl⟩ (no _ mL)
        · simp [TagSem] at hd
        · rw [tagSem_dom_iff hnone] at hd
          obtain ⟨v, T, ev, hT, hvT⟩ := hd.resolve_left (by simp)
          cases ev
          exact Or.inl ⟨_, mL, dl, l, negs, rfl, domKind kk, T, dom_mem_of_lookup hT, domKind_mem kk, ⟨x, hvT⟩,
            [k, x], pw, k, x, rfl, hk, hvT⟩
      · let F : List String := S.map fun e => match e.1 with | .atom s => s | _ => ""
        obtain ⟨w, hw, c, hc, wc⟩ := hF F
        have cS : (Term.atom c, Term.nil) ∉ S := fun m => hc (List.mem_map.mpr ⟨_, m, rfl⟩)
        have notR : ∀ a, Term.atom a ∈ S.map Prod.fst → (Term.atom a, Term.nil) ∈ S := fun a h => by
          obtain ⟨e, me, he⟩ := List.mem_map.mp h
          obtain ⟨s', rfl⟩ := hS e me
          simp only [Term.atom.injEq] at he
          subst he
          exact me
        obtain ⟨L, mL, tag, l, negs, rfl, hx'⟩ := unnamed_tag ef (N := []) (R := S.map Prod.fst) lines hl' sl
          (fun s' c' _ _ ns nc w => swap_seen ef named (fun h => ns (List.mem_map.mpr ⟨_, h, rfl⟩))
            (fun h => nc (List.mem_map.mpr ⟨_, h, rfl⟩)) w) (by simp [mapLookup]) (fun h => cS (notR c h)) hw wc
        obtain ⟨tag', l', negs', e, g, -, -⟩ := hl' _ mL
        obtain ⟨rfl, -, -⟩ := tuple3_inj e
        rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
        · exact absurd ⟨_, _, rfl⟩ (no _ mL)
        · simp [tagType] at hx'; exact absurd hx' (hnone x)
        · rw [tagType_dom] at hx'
          cases hv : mapLookup dl (.atom "atom") with
          | none => rw [hv] at hx'; exact absurd hx' (hnone x)
          | some v =>
            rw [hv] at hx'
            exact Or.inl ⟨_, mL, dl, l, negs, rfl, "atom", v, dom_mem_of_lookup hv, by simp [domainKinds],
              ⟨x, hx'⟩, [k, x], pw, k, x, rfl, hk, hx'⟩

/-- The list types of `map_to_list/1`: the empty list when there are no pairs, otherwise lists of the pairs, holding
the empty list exactly when the maps hold the empty map. -/
def ListX (t : Term) (n : Nat) (M : MW (level t (n + 1)).V → Prop) (L : Term) : Prop :=
  (L = nilT ∧ (∀ p, ¬InnerX t n M p) ∧ ∀ w, M w → w = wNone) ∨
  ∃ nil k inner, L = lTy nil k inner ∧ DE (level t (n + 1)).E inner ∧ (∀ p, denD inner p ↔ InnerX t n M p) ∧
    (nil = Bool.true ↔ M wNone)

/-- `map_to_list_static/2` with the pair function on a static map type of the level above. -/
theorem tls {Z : List (Term × Term)} (hZ : DE (level t (n + 1)).E (.map Z)) {m : Nat}
    (hm : (level t (n + 1)).K + 30 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_to_list_static/2» (D m) (.map Z) mtlF = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, ¬MT t (n + 1) Z w) ∨
        (∃ w, MT t (n + 1) Z w) ∧ ∃ L, res = .tuple #[.atom "ok", L] ∧ ListX t n (MT t (n + 1) Z) L) := by
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 5 := ⟨m - 5, by omega⟩
  have sX := de_map hZ
  have ef := (level t (n + 1)).ef
  cases hb : mapLookup Z (.atom "map") with
  | none =>
    refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w ⟨b, e, _⟩ => by rw [hb] at e; cases e⟩⟩
    simp [Elixir.Module.Types.Descr.«map_to_list_static/2», getMapKeys_single, hb]
  | some b =>
    have fb : MField (level t (n + 1)).E b := fieldC_map (sX.fields "map" b hb)
    have wb : Bdd (MapLitV (level t (n + 1)).E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact Bdd.leaf_iff.mpr ⟨k, .atom "open", [], rfl, Or.inl rfl, ⟨by simp, by simp⟩⟩
      · exact wb.mono fun _ h => h.1
    obtain ⟨lines, rl, hl, sl⟩ := dnf_lit_map (den := (level t (n + 1)).den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl
      (m := M + 5) (by omega) wb
    have inB : ∀ w, denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true ↔
        ∃ L ∈ lines, InMLine (level t (n + 1)).den L w := by
      intro w
      rw [← sl w]
      rcases fb with ⟨k, rfl⟩ | wb'
      · have lit : MapLitV (level t (n + 1)).E (.tuple #[.integer k, .atom "open", fieldsTerm []]) :=
          ⟨k, .atom "open", [], rfl, Or.inl rfl, ⟨by simp, by simp⟩⟩
        have v := (valM_iff (w := w) ef.mopsE ef.mdopsE ef.semR lit).mpr (nsem_lit.mpr (msem_open_nil w))
        rw [denMF_top, eval_leaf]
        exact ⟨fun _ => v, fun _ => rfl⟩
      · rw [denMF_bdd wb']
    have mt : ∀ w, MT t (n + 1) Z w ↔ denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true :=
      fun w => by simp [MT, hb]
    have conv : (fun w => denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true) = MT t (n + 1) Z :=
      funext fun w => propext (mt w).symm
    cases lines with
    | nil =>
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w hw => ?_⟩⟩
      · simp [Elixir.Module.Types.Descr.«map_to_list_static/2», getMapKeys_single, hb, rl, Term.list]
      · simpa using (inB w).mp ((mt w).mp hw)
    | cons L₀ rest =>
      obtain ⟨w₀, h₀⟩ := (hl L₀ List.mem_cons_self).2
      have ex : ∃ w, MT t (n + 1) Z w := ⟨w₀, (mt w₀).mpr ((inB w₀).mpr ⟨L₀, List.mem_cons_self, h₀⟩)⟩
      obtain ⟨inner, ri, di, si, sx⟩ := inner_exact (M := M) (by omega) fb (L₀ :: rest) hl inB
      rw [conv] at sx
      by_cases ce : Term.compare (Term.fuel inner (.map [])) inner (.map []) = .eq
      · have emp : ∀ p : PN t (n + 1), ¬denD inner p := fun p hp => by
          have := (ef_next t (n + 1)).resp de_none di (Lynx.Term.compare_eq_symm ce) hp
          simp [denD_map, mapLookup, dn_none] at this
        refine ⟨_, ?_, Or.inr ⟨ex, nilT, rfl, Or.inl ⟨rfl, fun p hp => emp p ((sx p).mpr hp),
          fun w hw => (inner_empty_iff si).mp emp w ((mt w).mp hw)⟩⟩⟩
        simp [Elixir.Module.Types.Descr.«map_to_list_static/2», getMapKeys_single, hb,
          rl, ri, Erlang.erlang.«==/2», ce, Elixir.Module.Types.Descr.«empty_list/0», nilT]
      · obtain ⟨hb', rh, sh⟩ := has_empty (den := (level t (n + 1)).den) (L₀ :: rest) (fun L m => (hl L m).1) (M + 2)
        obtain ⟨k, rlist, rnel⟩ := list_run ((ef_next t (n + 1)).static di) (M + 5)
        refine ⟨_, ?_, Or.inr ⟨ex, lTy hb' k inner, rfl, Or.inr ⟨hb', k, inner, rfl, di, sx, ?_⟩⟩⟩
        · cases hb' <;> simp [Elixir.Module.Types.Descr.«map_to_list_static/2»,
            getMapKeys_single, hb, rl, ri, Erlang.erlang.«==/2», ce, rh, rlist, rnel, lTy]
        · rw [sh, mt, inB]

/-- All pairs are pairs of the maps of the top map type. -/
theorem innerX_top {p : PN t (n + 1)} {k x : (level t (n + 1)).V} (pw : PairW p k x) :
    InnerX t n (MT t (n + 1) topM) p := by
  have dA := (dkdT_run (t := t) (n := n) (d := "atom") (by simp [domainKinds])).2
  by_cases ka : (toPN k).1.1 = "atom"
  · refine Or.inr (Or.inr ⟨k, x, pw, (den_succ dA.de (toPN k)).mpr (dA.atoms rfl _ ka), fun F => ?_⟩)
    obtain ⟨c, hc⟩ := fresh_str F
    exact ⟨fun κ => if κ = .atom c then some x else none, mt_top _, c, hc, by simp⟩
  · have da : ptKind (toPN k) ≠ "atom" := by
      unfold ptKind; split
      · generalize (toPN k).1.2.1 = i
        rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [bitKind]
      · exact ka
    obtain ⟨kk, e⟩ := domKind_of (ptKind_mem (toPN k)) da
    have dT := (dkdT_run (t := t) (n := n) (domKind_mem kk)).2
    exact Or.inr (Or.inl ⟨kk, 0, k, x, pw, (den_succ dT.de (toPN k)).mpr (dT.kinds (domKind_ne_atom kk) _ e.symm),
      fun κ => if κ = .dom kk 0 then some x else none, mt_top _, by simp⟩)

/-- `map_to_list_static/2` on the top type: lists of all pairs, the pairs of the maps of the top map type. -/
theorem tls_term (m : Nat) :
    ∃ L, Elixir.Module.Types.Descr.«map_to_list_static/2» (D (m + 1)) (.atom "term") mtlF = .ok (.tuple #[.atom "ok", L]) ∧
      ListX t n (MT t (n + 1) topM) L := by
  have ef := (level t (n + 1)).ef
  obtain ⟨P, rP, dP, sP⟩ := mtl_pair (t := t) (n := n + 1) ef.term ef.term (Or.inl rfl) (Or.inl rfl) (m + 1)
  obtain ⟨k, rlist, -⟩ := list_run ((ef_next t (n + 1)).static dP) (m + 1)
  refine ⟨lTy Bool.true k P, ?_, Or.inr ⟨Bool.true, k, P, rfl, dP, fun p => ?_, ⟨fun _ => mt_top _, fun _ => rfl⟩⟩⟩
  · rw [Elixir.Module.Types.Descr.«map_to_list_static/2».eq_def]
    simp [rP, rlist, lTy, getMapKeys]
  · rw [sP]
    constructor
    · rintro ⟨w', hw', k, x, rfl, -, -⟩
      exact innerX_top hw'
    · rintro (⟨s, k, x, pw, -⟩ | ⟨kk, i, k, x, pw, -⟩ | ⟨k, x, pw, -⟩) <;>
        exact ⟨[k, x], pw, k, x, rfl, ef.den_term k, ef.den_term x⟩

theorem listX_mono {M₁ M₂ : MW (level t (n + 1)).V → Prop} (hM : ∀ u, M₁ u → M₂ u) (ne : ∃ u, M₁ u)
    {L₁ L₂ : Term} (h₁ : ListX t n M₁ L₁) (h₂ : ListX t n M₂ L₂) : SubN t (n + 2) L₁ L₂ := by
  rcases h₁ with ⟨rfl, -, e₁⟩ | ⟨nil₁, k₁, i₁, rfl, d₁, s₁, n₁⟩ <;>
    rcases h₂ with ⟨rfl, x₂, -⟩ | ⟨nil₂, k₂, i₂, rfl, d₂, s₂, n₂⟩
  · exact fun q h => h
  · obtain ⟨u, hu⟩ := ne
    have := e₁ u hu; subst this
    exact (nilT_sub_lTy d₂ nil₂ k₂).mpr (n₂.mpr (hM _ hu))
  · exact (lTy_nil_sub d₁ nil₁ k₁).mpr fun p hp => x₂ p (innerX_mono hM ((s₁ p).mp hp))
  · exact lTy_mono d₁ d₂ (fun p hp => (s₂ p).mpr (innerX_mono hM ((s₁ p).mp hp)))
      (fun h => n₂.mpr (hM _ (n₁.mp h))) k₁ k₂

theorem listX_de {M : MW (level t (n + 1)).V → Prop} {L : Term} (h : ListX t n M L) :
    DE (level t (n + 2)).E L ∧ mapLookup (match L with | .map Y => Y | _ => []) (.atom "dynamic") = none ∧
      ∃ Y, L = .map Y := by
  rcases h with ⟨rfl, -, -⟩ | ⟨nil, k, i, rfl, d, -, -⟩
  · exact ⟨nilT_de, by simp [nilT, mapLookup], _, rfl⟩
  · refine ⟨lTy_de nil k d, ?_, ?_⟩ <;> cases nil <;> simp [lTy, mapLookup]

theorem listX_runs {M : MW (level t (n + 1)).V → Prop} {L : Term} (h : ListX t n M L) (m : Nat) :
    Elixir.Module.Types.Descr.«lower_bound/1» (D m) L = .ok L ∧ Elixir.Module.Types.Descr.«upper_bound/1» (D m) L = .ok L ∧
      GC (level t (n + 2)) L := by
  obtain ⟨dL, sL, Y, rfl⟩ := listX_de h
  simp only at sL
  have gL : GC (level t (n + 2)) (.map Y) := GC.tc dL
  refine ⟨?_, ?_, gL⟩
  · rw [lower_bound_run (Or.inr ⟨Y, rfl⟩)]; simp [lower, rmDyn_static sL]
  · rw [upper_bound_run gL.ub, upper_tc dL]

/-- `map_to_list/2` with the pair function on a gradual map type of the level above: it gives a type exactly when the
lower bound holds only maps and the upper bound some map; then the lists of the static maps, with those of the dynamic
maps in the upper bound. -/
theorem tl_sem {X : List (Term × Term)} (gX : GC (level t (n + 1)) (.map X)) {m : Nat}
    (hm : (level t (n + 1)).K + 38 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«map_to_list/2» (D m) (.map X) mtlF = .ok r ∧
      ((∃ L, r = .tuple #[.atom "ok", L]) ↔ (∀ q : PN t (n + 1), denD (lower (.map X)) q → q.1.1 = "map") ∧
        ∃ w, MT t (n + 1) (dynL (upper (.map X))) w) ∧
      ∀ L, r = .tuple #[.atom "ok", L] → ∃ lo up sl dl, Elixir.Module.Types.Descr.«lower_bound/1» (D m) L = .ok lo ∧
        Elixir.Module.Types.Descr.«upper_bound/1» (D m) L = .ok up ∧ DE (level t (n + 2)).E lo ∧
        DE (level t (n + 2)).E up ∧
        (((∀ q : PN t (n + 2), ¬denD lo q) ∧ ∀ w, ¬MT t (n + 1) (rmDyn X) w) ∨
          (∃ w, MT t (n + 1) (rmDyn X) w) ∧ ListX t n (MT t (n + 1) (rmDyn X)) sl ∧
            ∀ q : PN t (n + 2), denD lo q ↔ denD sl q) ∧
        ListX t n (MT t (n + 1) (dynL (upper (.map X)))) dl ∧ (∃ w, MT t (n + 1) (dynL (upper (.map X))) w) ∧
        ∀ q : PN t (n + 2), denD up q ↔ denD lo q ∨ denD dl q := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have dSt : DE (level t (n + 1)).E (.map (rmDyn X)) := gX.low_tc
  obtain ⟨dR, sRm⟩ := rest_map dSt
  have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 1)) (.map (rmDyn X)) =
      .ok (boolAtom (bp (∀ q : PN t (n + 1), ¬denD (.map (rmM (rmDyn X))) q))) := by
    simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
    exact next_empty dR (by omega)
  have onlyIff : (∀ q : PN t (n + 1), ¬denD (.map (rmM (rmDyn X))) q) ↔
      ∀ q : PN t (n + 1), denD (.map (rmDyn X)) q → q.1.1 = "map" :=
    ⟨fun h q hq => Classical.byContradiction fun nq => h q ((sRm q).mpr ⟨hq, nq⟩),
      fun h q hq => ((sRm q).mp hq).2 (h q ((sRm q).mp hq).1)⟩
  have lX : lower (.map X) = .map (rmDyn X) := by simp [lower]
  rw [lX]
  cases hD : mapLookup X (.atom "dynamic") with
  | none =>
    have eX : rmDyn X = X := rmDyn_static hD
    have uX : upper (.map X) = .map X := by simp [upper, hD]
    have hX : DE (level t (n + 1)).E (.map X) := GC.static gX hD
    rw [eX] at mo onlyIff
    rw [uX, eX]
    simp only [dynL]
    rw [Elixir.Module.Types.Descr.«map_to_list/2».eq_def]
    have sX := de_map hX
    have mo' : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 1)) (.map X) =
        .ok (boolAtom (bp (∀ q : PN t (n + 1), ¬denD (.map (rmM X)) q))) := mo
    simp only [Erlang.maps.«take/2», sX.static, mo']
    by_cases restE : ∀ q : PN t (n + 1), ¬denD (.map (rmM X)) q
    rotate_left
    · rw [bp_false.mpr restE]
      refine ⟨.atom "badmap", by simp [boolAtom, Lynx.Term.isMember], ⟨fun ⟨_, h⟩ => (by cases h),
        fun ⟨h, _⟩ => absurd (onlyIff.mpr h) restE⟩, fun _ h => by cases h⟩
    rw [bp_true.mpr restE]
    obtain ⟨res, run, ⟨rfl, emp⟩ | ⟨ex, L, rfl, hL⟩⟩ := tls hX (m := k + 1) (by omega)
    · refine ⟨.atom "badmap", by simp [boolAtom, Lynx.Term.isMember, run],
        ⟨fun ⟨_, h⟩ => (by cases h), fun ⟨_, w, hw⟩ => absurd hw (emp w)⟩, fun _ h => by cases h⟩
    refine ⟨_, by simp [boolAtom, Lynx.Term.isMember, run], ⟨fun _ => ⟨onlyIff.mp restE, ex⟩, fun _ => ⟨L, rfl⟩⟩,
      fun L' e => ?_⟩
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true, true_and] at e
    subst e
    obtain ⟨lb, ub, gL⟩ := listX_runs hL (k + 1)
    exact ⟨L, L, L, L, lb, ub, (listX_de hL).1, (listX_de hL).1, Or.inr ⟨ex, hL, fun q => Iff.rfl⟩, hL, ex,
      fun q => (or_self_iff).symm⟩
  | some Dy =>
    obtain ⟨tD, incl⟩ : TC (level t (n + 1)) Dy ∧ ∀ q : TP (level t (n + 1)), denD (.map X) q → denD Dy q := by
      rcases gX with tX | ⟨X', Dy', e, hD', tD, dS, incl⟩
      · rcases tX with h | ⟨X', e, sX'⟩
        · cases h
        · simp only [Term.map.injEq] at e; subst e; rw [sX'.static] at hD; cases hD
      · simp only [Term.map.injEq] at e; subst e; rw [hD] at hD'; cases hD'; exact ⟨tD, incl⟩
    rw [upper_dyn hD]
    rw [Elixir.Module.Types.Descr.«map_to_list/2».eq_def]
    simp only [Erlang.maps.«take/2», hD, equalExact_eq_decide]
    have eS : (X.filter fun entry => !decide (compareExact ((Term.atom "dynamic").fuel entry.fst) (Term.atom "dynamic")
      entry.fst = .eq)) = rmDyn X := rfl
    rw [eS]
    simp only [Lynx.Except.ok_bind]
    obtain ⟨rd, rrd, hd⟩ : ∃ rd, Elixir.Module.Types.Descr.«map_to_list_static/2» (D (k + 1)) Dy mtlF = .ok rd ∧
        ((rd = .atom "badmap" ∧ ∀ w, ¬MT t (n + 1) (dynL Dy) w) ∨
          (∃ w, MT t (n + 1) (dynL Dy) w) ∧ ∃ L, rd = .tuple #[.atom "ok", L] ∧ ListX t n (MT t (n + 1) (dynL Dy)) L) := by
      rcases tD with rfl | ⟨DX, rfl, sDX⟩
      · obtain ⟨L, rL, hL⟩ := tls_term (t := t) (n := n) k
        exact ⟨_, rL, Or.inr ⟨⟨_, mt_top wNone⟩, L, rfl, hL⟩⟩
      · exact tls (Or.inr ⟨DX, rfl, sDX⟩) (m := k + 1) (by omega)
    rcases Classical.em (∀ q : PN t (n + 1), ¬denD (.map (rmM (rmDyn X))) q) with restE | restE
    rotate_left
    · rw [bp_false.mpr restE] at mo
      refine ⟨.atom "badmap", by simp [mo, boolAtom, Lynx.Term.isMember], ⟨fun ⟨_, h⟩ => (by cases h),
        fun ⟨h, _⟩ => absurd (onlyIff.mpr h) restE⟩, fun _ h => by cases h⟩
    rw [bp_true.mpr restE] at mo
    rcases hd with ⟨rfl, noD⟩ | ⟨exD, dl, rfl, hdl⟩
    · refine ⟨.atom "badmap", by simp [mo, boolAtom, Lynx.Term.isMember, rrd],
        ⟨fun ⟨_, h⟩ => (by cases h), fun ⟨_, w, hw⟩ => absurd hw (noD w)⟩, fun _ h => by cases h⟩
    obtain ⟨dDl, sDl, Yl, rfl⟩ := listX_de hdl
    simp only at sDl
    have noP : ∀ q : PN t (n + 2), ¬denD (.map [(.atom "dynamic", .map Yl)]) q := fun q h => by
      have := (denD_rmDyn [(.atom "dynamic", .map Yl)] q).mpr h
      rw [rmDyn_cons_dyn] at this
      simp [rmDyn, denD_map, mapLookup, dn_none] at this
    have gY : GC (level t (n + 2)) (.map [(.atom "dynamic", .map Yl)]) :=
      Or.inr ⟨_, .map Yl, rfl, by simp [mapLookup], dDl, by rw [rmDyn_cons_dyn]; exact descrC_nil,
        fun q h => absurd h (noP q)⟩
    have uY : upper (.map [(.atom "dynamic", .map Yl)]) = .map Yl := upper_dyn (by simp [mapLookup])
    have dyn : (match getMapKeys [Term.atom "dynamic"] (Term.map Yl) with
        | [_29] => (pure (Term.map [(.atom "dynamic", _29)]) : Except Lynx.Exception Term)
        | _ => pure (Term.map [(.atom "dynamic", Term.map Yl)])) = .ok (.map [(.atom "dynamic", .map Yl)]) := by
      simp [getMapKeys_single, sDl]
    obtain ⟨rS, rrS, hS⟩ := tls dSt (m := k + 1) (by omega)
    rcases hS with ⟨rfl, noS⟩ | ⟨exS, sl, rfl, hsl⟩
    · refine ⟨.tuple #[.atom "ok", .map [(.atom "dynamic", .map Yl)]], ?_,
        ⟨fun _ => ⟨onlyIff.mp restE, exD⟩, fun _ => ⟨_, rfl⟩⟩, fun L e => ?_⟩
      · simp [mo, boolAtom, Lynx.Term.isMember, rrd, rrS, getMapKeys_single, sDl]
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true, true_and] at e
      subst e
      refine ⟨_, _, nilT, .map Yl, lower_bound_run gY.shape, upper_bound_run gY.ub, gY.low_tc, gY.up_tc,
        Or.inl ⟨fun q h => noP q ((denD_lower _ q).mp h), noS⟩, hdl, exD, fun q => ?_⟩
      rw [uY]
      exact ⟨Or.inr, fun h => h.elim (fun h => absurd ((denD_lower _ q).mp h) (noP q)) id⟩
    obtain ⟨dSl, sSl, Ys, rfl⟩ := listX_de hsl
    obtain ⟨c, gc, rc, sc₁, sc₂⟩ := gc_opt_union (GC.tc dSl) gY [] (m := k + 1) (by rw [level_K] at hm ⊢; omega)
    have uS : upper (.map Ys) = .map Ys := upper_tc dSl
    refine ⟨.tuple #[.atom "ok", c], ?_, ⟨fun _ => ⟨onlyIff.mp restE, exD⟩, fun _ => ⟨_, rfl⟩⟩, fun L e => ?_⟩
    · have rc' : Elixir.Module.Types.Descr.«opt_union/2» (D (k + 1)) (.map Ys) (.map [(.atom "dynamic", .map Yl)]) =
          .ok c := rc
      simp [mo, boolAtom, Lynx.Term.isMember, rrd, rrS, getMapKeys_single, sDl, rc']
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true, true_and] at e
    subst e
    refine ⟨_, _, .map Ys, .map Yl, lower_bound_run gc.shape, upper_bound_run gc.ub, gc.low_tc, gc.up_tc,
      Or.inr ⟨exS, hsl, fun q => ?_⟩, hdl, exD, fun q => ?_⟩
    · rw [denD_lower, sc₁]; exact ⟨fun h => h.resolve_right (noP q), Or.inl⟩
    · rw [sc₂, uS, uY, denD_lower, sc₁]
      exact ⟨fun h => h.imp_left Or.inl, fun h => h.imp_left fun h => h.resolve_right (noP q)⟩

theorem mt_dynL2 {a : Term} (ha : TC (level t n) a) (u : MW (level t n).V) :
    MT t n (dynL a) u ↔ denD a (mpt (t := t) (n := n) u) := by
  rcases ha with rfl | ⟨Y, rfl, -⟩
  · exact ⟨fun _ => denD_term _, fun _ => mt_top u⟩
  · exact (denD_mpt u).symm

/-- The lists of less precise maps are less precise. -/
theorem tl_prec {X : List (Term × Term)} {a₂ : Term} (gX : GC (level t (n + 1)) (.map X))
    (g₂ : GC (level t (n + 1)) a₂) {m : Nat} (hm : (level t (n + 1)).K + 47 ≤ m)
    (lo : ∀ v : PN t (n + 1), denD a₂ v → denD (.map X) v)
    (up : ∀ v : PN t (n + 1), denD (upper (.map X)) v → denD (upper a₂) v) {L : Term}
    (run : Elixir.Module.Types.Descr.«map_to_list/2» (D m) (.map X) mtlF = .ok (.tuple #[.atom "ok", L])) :
    ∃ L₂, Elixir.Module.Types.Descr.«map_to_list/2» (D m) a₂ mtlF = .ok (.tuple #[.atom "ok", L₂]) ∧
      «precise?/2» (D m) L L₂ = .ok (.atom "true") := by
  obtain ⟨r, run', iffA, semA⟩ := tl_sem gX (m := m) (by omega)
  rw [run] at run'; cases run'
  obtain ⟨onlyA, neA⟩ := iffA.mp ⟨_, rfl⟩
  have lo' : ∀ v : PN t (n + 1), denD (lower a₂) v → denD (lower (.map X)) v := fun v h =>
    (denD_lower _ _).mpr (lo v ((denD_lower _ _).mp h))
  obtain ⟨X₂, rfl⟩ : ∃ X₂, a₂ = .map X₂ := by
    rcases g₂.shape with rfl | ⟨X₂, rfl⟩
    · have := onlyA bitPt (lo' bitPt (by simp [lower, denD_term]))
      simp [bitPt] at this
    · exact ⟨X₂, rfl⟩
  have muA : ∀ w, MT t (n + 1) (dynL (upper (.map X))) w → MT t (n + 1) (dynL (upper (.map X₂))) w := fun w h =>
    (mt_dynL2 g₂.up_tc w).mpr (up _ ((mt_dynL2 gX.up_tc w).mp h))
  have msB : ∀ w, MT t (n + 1) (rmDyn X₂) w → MT t (n + 1) (rmDyn X) w := fun w h =>
    (denD_mpt w).mp ((denD_rmDyn X _).mpr (lo _ ((denD_rmDyn X₂ _).mp ((denD_mpt w).mpr h))))
  have msA : ∀ w, MT t (n + 1) (rmDyn X) w → MT t (n + 1) (dynL (upper (.map X))) w := fun w h =>
    (mt_dynL2 gX.up_tc w).mpr (GC.inv gX _ ((denD_rmDyn X _).mp ((denD_mpt w).mpr h)))
  obtain ⟨r₂, run₂, iffB, semB⟩ := tl_sem g₂ (m := m) (by omega)
  obtain ⟨L₂, rfl⟩ := iffB.mpr ⟨fun q h => onlyA q (lo' q h), let ⟨w, hw⟩ := neA; ⟨w, muA w hw⟩⟩
  obtain ⟨lA, uA, sA, dA, rlA, ruA, dlA, duA, hlA, hdA, neUA, suA⟩ := semA L rfl
  obtain ⟨lB, uB, sB, dB, rlB, ruB, dlB, duB, hlB, hdB, neUB, suB⟩ := semB L₂ rfl
  have hm' : (level t (n + 2)).K + 23 ≤ m := by rw [level_K] at hm ⊢; omega
  refine ⟨L₂, run₂, precise_of_bounds (n := n + 2) hm' rlA ruA rlB ruB dlA duA dlB duB (fun q h => ?_) (fun q h => ?_)⟩
  · rcases hlB with ⟨noB, -⟩ | ⟨neSB, hsB, eB⟩
    · exact absurd h (noB q)
    obtain ⟨u, hu⟩ := neSB
    rcases hlA with ⟨-, noA⟩ | ⟨-, hsA, eA⟩
    · exact absurd (msB u hu) (noA u)
    exact (eA q).mpr (listX_mono msB ⟨u, hu⟩ hsB hsA q ((eB q).mp h))
  · refine (suB q).mpr (Or.inr ?_)
    rcases (suA q).mp h with h | h
    · rcases hlA with ⟨noA, -⟩ | ⟨neSA, hsA, eA⟩
      · exact absurd h (noA q)
      exact listX_mono (fun u h => muA u (msA u h)) neSA hsA hdB q ((eA q).mp h)
    · exact listX_mono muA neUA hdA hdB q h

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem get_domains1 (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L) (ds : List Term) (hd : ∀ d ∈ ds, ∃ s, d = .atom s) {acc : Term} (ha : E acc) :
    ∃ T, Erlang.lists.«foldl/3» (D (n + 4))
        (.function false "Elixir.Module.Types.Descr" "-map_get_static_dnf/3-fun-1-" 2 #[Term.list lines]) acc (Term.list ds) =
          .ok T ∧ E T ∧ ∀ x, den T x ↔ den acc x ∨ ∃ s, .atom s ∈ ds ∧ ∃ L ∈ lines, LineTag den L s x := by
  obtain ⟨T, ⟨hT, sT⟩, run⟩ := foldl_rel_at (m := n + 4) "Elixir.Module.Types.Descr" "-map_get_static_dnf/3-fun-1-"
    #[Term.list lines] (fun pre a => E a ∧ ∀ x, den a x ↔ den acc x ∨ ∃ s, .atom s ∈ pre ∧ ∃ L ∈ lines, LineTag den L s x)
    ds (fun pre r a mr ⟨ha', sa⟩ => by
      obtain ⟨s, rfl⟩ := hd r mr
      obtain ⟨c, ⟨hc, sc⟩, rc⟩ := foldl_rel_at (m := n + 3) "Elixir.Module.Types.Descr" "-map_get_domain/3-fun-0-"
        #[.atom s] (fun pre' a' => E a' ∧ ∀ x, den a' x ↔ den a x ∨ ∃ L ∈ pre', LineTag den L s x) lines
        (fun pre' L b mL ⟨hb, sb⟩ => by
          obtain ⟨tag, l, negs, rfl, g, -, -⟩ := hl L mL
          have hty := tagType_value ef.mopsE g s
          obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] hty hb (m := n + 2) (by omega)
          refine ⟨c, ⟨hc, fun x => ?_⟩, ?_⟩
          · rw [sc, sb]
            simp only [List.mem_append, List.mem_singleton]
            constructor
            · rintro (h | h | ⟨L', m', h⟩)
              · exact Or.inr ⟨_, Or.inr rfl, tag, l, negs, rfl, h⟩
              · exact Or.inl h
              · exact Or.inr ⟨L', Or.inl m', h⟩
            · rintro (h | ⟨L', m' | e, h⟩)
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr ⟨L', m', h⟩)
              · subst e
                obtain ⟨tag', l', negs', e', h'⟩ := h
                obtain ⟨rfl, -, -⟩ := tuple3_inj e'
                exact Or.inl h'
          · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_get_domain/3-fun-0-/2».pure,
              tag_type_run g s, Elixir.Module.Types.Descr.«opt_union/2», rc])
        a ⟨ha', fun x => by simp⟩
      refine ⟨c, ⟨hc, fun x => ?_⟩, ?_⟩
      · rw [sc, sa]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro ((h | ⟨s', m', h⟩) | h)
          · exact Or.inl h
          · exact Or.inr ⟨s', Or.inl m', h⟩
          · exact Or.inr ⟨s, Or.inr rfl, h⟩
        · rintro (h | ⟨s', m' | e, h⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr ⟨s', m', h⟩)
          · cases e; exact Or.inr h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_get_static_dnf/3-fun-1-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-map_get_static_dnf/3-fun-1-/3», Elixir.Module.Types.Descr.«map_get_domain/3»]
          using rc)
    acc ⟨ha, fun x => by simp⟩
  exact ⟨T, run, hT, sT⟩

/-- `map_get_static_dnf/3` on the non-empty lines of a map type and the split of a gradual key type of the laws: the
values its maps hold at the keys of the split. -/
theorem gget_dnf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {b : Term} (fb : MField E b) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (sl : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {s : Term} {KP : MKey → Prop}
    (hs : GForm s KP) :
    ∃ T, Elixir.Module.Types.Descr.«map_get_static_dnf/3» (D (n + 4)) b (Term.list lines) s = .ok T ∧ E T ∧
      ∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, KP κ ∧ w κ = some x := by
  have hl' : ∀ L ∈ lines, MLine E L := fun L m => (hl L m).1
  have fold1 : ∀ acc, Erlang.lists.«foldl/3» (D (n + 4))
      (.function false "Elixir.Module.Types.Descr" "-map_get_static_dnf/3-fun-1-" 2 #[Term.list lines]) acc .nil =
        .ok acc := fun acc => by simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  -- A split with required and optional atoms besides a split of keys and domains unites the values of both.
  have gen : ∀ (Rs Os : List String) (neg : Term) (Ds Ds' : List Term), SplitOk [] neg (Ds ++ Ds') →
      ∃ T, Elixir.Module.Types.Descr.«map_get_static_dnf/3» (D (n + 4)) b (Term.list lines)
          (.tuple #[Term.list (Rs.map Term.atom), Term.list (Os.map Term.atom), neg, Term.list Ds, Term.list Ds']) =
          .ok T ∧ E T ∧
        ∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧
          ∃ κ, ((∃ s, (s ∈ Rs ∨ s ∈ Os) ∧ κ = .atom s) ∨ SplitKey [] neg (Ds ++ Ds') κ) ∧ w κ = some x := by
    intro Rs Os neg Ds Ds' hs
    have ha : ∀ (A : List String), ∀ r ∈ A.map Term.atom, ∃ s, r = .atom s :=
      fun A r mr => let ⟨s, _, e⟩ := List.mem_map.mp mr; ⟨s, e.symm⟩
    obtain ⟨T₂, r₂, h₂, s₂⟩ := get_keys ef hn lines hl (Rs.map Term.atom) (ha Rs) ef.none
    obtain ⟨T₃, r₃, h₃, s₃⟩ := get_keys ef hn lines hl (Os.map Term.atom) (ha Os) h₂
    obtain ⟨R, rR, hR, swR⟩ := neg_keys_split ef fb (n + 3) hs
    obtain ⟨T₄, r₄, h₄, s₄⟩ := get_keys ef hn lines hl R (fun r mr => let ⟨s, e, _⟩ := hR r mr; ⟨s, e⟩) h₃
    have hd : ∀ d ∈ Ds ++ Ds', ∃ s, d = .atom s := fun d md => let ⟨s, _, e⟩ := hs.hds d md; ⟨s, e⟩
    obtain ⟨T₅, r₅, h₅, s₅⟩ := get_domains ef hn lines hl' Ds (fun d md => hd d (List.mem_append_left _ md)) h₄
    obtain ⟨T₆, r₆, h₆, s₆⟩ := get_domains1 ef hn lines hl' Ds' (fun d md => hd d (List.mem_append_right _ md)) h₅
    refine ⟨T₆, ?_, h₆, fun x => ?_⟩
    · simp [Elixir.Module.Types.Descr.«map_get_static_dnf/3», r₂, r₃, rR, r₄, r₅, r₆]
    have pe := pieces_sem ef lines hl sl hs hR swR x
    have lm := fun a o => longM_iff (E := E) (den := den) sl a o
    rw [s₆, s₅, s₄, s₃, s₂]
    simp only [ef.den_none x, false_or, List.not_mem_nil, false_and, exists_false] at pe ⊢
    constructor
    · rintro ((((⟨s, m, h⟩ | ⟨s, m, h⟩) | h) | ⟨k, m, h⟩) | ⟨k, m, h⟩)
      · obtain ⟨s', ms', e⟩ := List.mem_map.mp m; cases e
        obtain ⟨w, hw, e⟩ := (lm s (some x)).mp h
        exact ⟨w, hw, .atom s, Or.inl ⟨s, Or.inl ms', rfl⟩, e⟩
      · obtain ⟨s', ms', e⟩ := List.mem_map.mp m; cases e
        obtain ⟨w, hw, e⟩ := (lm s (some x)).mp h
        exact ⟨w, hw, .atom s, Or.inl ⟨s, Or.inr ms', rfl⟩, e⟩
      · obtain ⟨w, hw, κ, k, e⟩ := pe.mp (Or.inl h); exact ⟨w, hw, κ, Or.inr k, e⟩
      · obtain ⟨w, hw, κ, k, e⟩ := pe.mp (Or.inr ⟨k, List.mem_append_left _ m, h⟩); exact ⟨w, hw, κ, Or.inr k, e⟩
      · obtain ⟨w, hw, κ, k, e⟩ := pe.mp (Or.inr ⟨k, List.mem_append_right _ m, h⟩); exact ⟨w, hw, κ, Or.inr k, e⟩
    · rintro ⟨w, hw, κ, ⟨s, ms | ms, rfl⟩ | k, e⟩
      · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨s, List.mem_map_of_mem ms, (lm s (some x)).mpr ⟨w, hw, e⟩⟩)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨s, List.mem_map_of_mem ms, (lm s (some x)).mpr ⟨w, hw, e⟩⟩)))
      · rcases pe.mpr ⟨w, hw, κ, k, e⟩ with h | ⟨kd, m, h⟩
        · exact Or.inl (Or.inl (Or.inr h))
        · rcases List.mem_append.mp m with m | m
          · exact Or.inl (Or.inr ⟨kd, m, h⟩)
          · exact Or.inr ⟨kd, m, h⟩
  -- Atoms of a split are its keys.
  have atoms : ∀ (Rs : List Term) (neg : Term) (ds : List Term), SplitOk Rs neg ds →
      ∃ A : List String, Rs = A.map Term.atom ∧ SplitOk [] neg ds ∧ ∀ κ, SplitKey Rs neg ds κ ↔
        ((∃ s, s ∈ A ∧ κ = .atom s) ∨ SplitKey [] neg ds κ) := by
    intro Rs neg ds ok
    obtain ⟨A, rfl⟩ := atoms_of ok.hrs
    refine ⟨A, rfl, ⟨by simp, ok.hneg, ok.hds, ok.hatom⟩, fun κ => ?_⟩
    cases κ with
    | atom s => simp [SplitKey]
    | dom k i => simp [SplitKey]
  rcases hs with ⟨Rs, Os, Ds, Ds', rfl, ok, kp⟩ | ⟨N, Ds, Ds', rfl, ok, -, kp⟩ |
    ⟨A, N, Ds, Ds', rfl, ok, -, -, kp⟩
  · obtain ⟨A, eA, ok', sk⟩ := atoms (Rs ++ Os) _ _ ok
    obtain ⟨Ra, rfl⟩ := atoms_of fun r mr => ok.hrs r (List.mem_append_left _ mr)
    obtain ⟨Oa, rfl⟩ := atoms_of fun r mr => ok.hrs r (List.mem_append_right _ mr)
    obtain ⟨T, r, h, sT⟩ := gen Ra Oa _ Ds Ds' ok'
    refine ⟨T, r, h, fun x => (sT x).trans (exists_congr fun w => and_congr Iff.rfl
      (exists_congr fun κ => and_congr ?_ Iff.rfl))⟩
    rw [← kp κ, sk κ]
    have : ∀ s, s ∈ A ↔ s ∈ Ra ∨ s ∈ Oa := fun s => by
      rw [← List.map_append] at eA
      have := congrArg (fun l => Term.atom s ∈ l) eA
      simp at this; simpa [List.mem_append] using this.symm
    simp only [this]
  · obtain ⟨T, r, h, sT⟩ := gen [] [] _ Ds Ds' (by simpa using ok)
    refine ⟨T, by simpa [Term.list] using r, h, fun x => (sT x).trans (exists_congr fun w => and_congr Iff.rfl
      (exists_congr fun κ => and_congr ?_ Iff.rfl))⟩
    rw [← kp κ]; simp
  · obtain ⟨T, r, h, sT⟩ := gen A [] _ Ds Ds' ok
    refine ⟨T, by simpa [Term.list] using r, h, fun x => (sT x).trans (exists_congr fun w => and_congr Iff.rfl
      (exists_congr fun κ => and_congr ?_ Iff.rfl))⟩
    rw [← kp κ]
    constructor
    · rintro (⟨s, ms | ms, rfl⟩ | k)
      · exact Or.inl ⟨s, ms, rfl⟩
      · cases ms
      · exact Or.inr k
    · rintro (⟨s, ms, rfl⟩ | k)
      · exact Or.inl ⟨s, Or.inl ms, rfl⟩
      · exact Or.inr k

/-- `map_get_static/2` on a map field and a split of static keys: `:badmap` when it is empty, otherwise the union of
the values its maps hold at the keys the split selects. -/
theorem gstatic_get (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {X : List (Term × Term)} {b : Term}
    (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) {s : Term} {KP : MKey → Prop} (hs : GForm s KP) :
    ∃ res, Elixir.Module.Types.Descr.«map_get_static/2» (D (n + 4)) (.map X) s = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        (∃ T, res = .tuple #[.atom "ok", T] ∧ E T ∧ (∃ w, denMF E den b w = Bool.true) ∧
          ∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, KP κ ∧ w κ = some x)) := by
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, run⟩ := init_total ef.mopsE ef.mdopsE ef.jopsU [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 4)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := run (n + 4) (by omega)
    cases e
    · -- Not empty: a map of the literal.
      have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := run.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ (m := n + 4) (by omega) rfl g sl (negs := []) (by simp)
          fun w hw => absurd ⟨w, hw⟩ none)
        simp [boolAtom] at this
      obtain ⟨w₀, h₀⟩ := ne
      have line : ∀ w, InMLine den (.tuple #[tag, fieldsTerm l, Term.list []]) w ↔ MSem den tag l w := fun w => by
        rw [inMLine_iff]; simp
      obtain ⟨T, rT, hT, sT⟩ := gget_dnf ef hn fb [.tuple #[tag, fieldsTerm l, Term.list []]]
        (fun L mL => by
          simp only [List.mem_singleton] at mL
          subst mL
          exact ⟨⟨tag, l, [], rfl, g, sl, by simp⟩, w₀, (line w₀).mpr h₀⟩)
        (fun w => by simp [sem, line]) hs
      refine ⟨_, ?_, Or.inr ⟨T, rfl, hT, ⟨w₀, (sem w₀).mpr h₀⟩, sT⟩⟩
      unfold Elixir.Module.Types.Descr.«map_get_static/2»
      simp only [Term.list] at rT
      simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
        Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom, rT]
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_get_static/2»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      · cases h : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w
        · rfl
        · obtain ⟨N, mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ ef.jopsU (m := n + 4) (by omega) rfl g sl (negs := []) (by simp) run w
            ((sem w).mp h)
          simp at mN
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl (m := n + 4) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
    cases lines with
    | nil =>
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_get_static/2»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Term.list]
        · simp [getMapKeys_single, hb, rl, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Term.list]
      · cases h : denMF E den b w
        · rfl
        · simpa using (inB w).mp h
    | cons L rest =>
      obtain ⟨T, rT, hT, sT⟩ := gget_dnf ef hn fb (L :: rest) hl inB hs
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨_, ?_, Or.inr ⟨T, rfl, hT, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, sT⟩⟩
      unfold Elixir.Module.Types.Descr.«map_get_static/2»
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
      · simp [getMapKeys_single, hb, rl, rT, Term.list]
      · simp [getMapKeys_single, hb, rl, rT, Term.list]
      · exact absurd ⟨_, _, _, rfl⟩ three
      · simp [getMapKeys_single, hb, rl, rT, Term.list]

end

section
variable {t : Term} {n : Nat}

/-- The values the maps of a type hold at the keys of a key predicate. -/
def Vals {V : Type} (M : MW V → Prop) (KP : MKey → Prop) (x : V) : Prop := ∃ w, M w ∧ ∃ κ, KP κ ∧ w κ = some x

/-- `map_get_static/2` on a static map type, or the top type as the top map type. -/
theorem gget_static {Dy : Term} (tD : TC (level t n) Dy) {s : Term} {KP : MKey → Prop} (hs : GForm s KP) {m : Nat}
    (hm : (level t n).K + 4 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_get_static/2» (D (m + 4)) Dy s = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, ¬MT t n (dynL Dy) w) ∨
        ∃ T, res = .tuple #[.atom "ok", T] ∧ (level t n).E T ∧ (∀ x, (level t n).den T x ↔ Vals (MT t n (dynL Dy)) KP x) ∧
          ((Dy ≠ .atom "term" ∧ mapLookup (dynL Dy) (.atom "map") = none) ∨ ∃ w, MT t n (dynL Dy) w)) := by
  have ef := (level t n).ef
  have main : ∀ Z : List (Term × Term), DE (level t n).E (.map Z) →
      ∃ res, Elixir.Module.Types.Descr.«map_get_static/2» (D (m + 4)) (.map Z) s = .ok res ∧
        ((res = .atom "badmap" ∧ ∀ w, ¬MT t n Z w) ∨
          ∃ T, res = .tuple #[.atom "ok", T] ∧ (level t n).E T ∧ (∀ x, (level t n).den T x ↔ Vals (MT t n Z) KP x) ∧
            (mapLookup Z (.atom "map") = none ∨ ∃ w, MT t n Z w)) := by
    intro Z hZ
    have sZ := de_map hZ
    cases hb : mapLookup Z (.atom "map") with
    | none =>
      refine ⟨.tuple #[.atom "ok", .map []], ?_, Or.inr ⟨_, rfl, ef.none, fun x => ⟨fun h => absurd h (ef.den_none x),
        fun ⟨w, ⟨b, e, _⟩, _⟩ => by rw [hb] at e; cases e⟩, Or.inl rfl⟩⟩
      unfold Elixir.Module.Types.Descr.«map_get_static/2»
      simp [getMapKeys_single, hb]
    | some b =>
      have fb : MField (level t n).E b := fieldC_map (sZ.fields "map" b hb)
      have mt : ∀ w, MT t n Z w ↔ denMF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [MT, hb]
      obtain ⟨res, run, ⟨rfl, emp⟩ | ⟨T, rfl, hT, ⟨w₀, h₀⟩, sT⟩⟩ := gstatic_get ef (n := m) hm hb fb hs
      · exact ⟨_, run, Or.inl ⟨rfl, fun w h => by rw [mt, emp w] at h; cases h⟩⟩
      · refine ⟨_, run, Or.inr ⟨T, rfl, hT, fun x => (sT x).trans ?_, Or.inr ⟨w₀, (mt w₀).mpr h₀⟩⟩⟩
        exact exists_congr fun w => and_congr (mt w).symm Iff.rfl
  rcases tD with rfl | ⟨Z, rfl, sZ⟩
  · obtain ⟨res, run, h⟩ := main topM mapTop_de
    refine ⟨res, ?_, ?_⟩
    · rw [Elixir.Module.Types.Descr.«map_get_static/2».eq_def]; simpa [Lynx.Term.getMapKeys] using run
    · rcases h with h | ⟨T, e, hT, sT, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨T, e, hT, sT, Or.inr ⟨_, mt_top wNone⟩⟩
  · obtain ⟨res, run, h⟩ := main Z (Or.inr ⟨Z, rfl, sZ⟩)
    refine ⟨res, run, ?_⟩
    rcases h with h | ⟨T, e, hT, sT, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨T, e, hT, sT, h.imp (fun h => ⟨by simp, h⟩) id⟩

end

section
variable {t : Term} {d : Nat}

/-- `map_get/2` on a gradual map type of the next level, at the split of a key type of the laws: `:badmap` unless the
lower bound holds only maps and the upper bound some map, `:error` when those hold no value at the keys, and otherwise
the values of the static maps, with those of the dynamic maps in the upper bound. -/
theorem gget_sem {X : List (Term × Term)} (gX : GC (level t (d + 1)) (.map X)) {key s : Term} {KP : MKey → Prop}
    {m : Nat} (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s) (hs : GForm s KP)
    (hm : (level t (d + 1)).K + 30 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«map_get/2» (D m) (.map X) key = .ok r ∧
      (r = .atom "badmap" ∨ r = .atom "error" ∨ ∃ T, r = .tuple #[.atom "ok", T]) ∧
      (r = .atom "badmap" ↔ ¬((∀ q : PN t (d + 1), denD (lower (.map X)) q → q.1.1 = "map") ∧
        ∃ w, MT t (d + 1) (dynL (upper (.map X))) w)) ∧
      (r = .atom "error" ↔ (∀ q : PN t (d + 1), denD (lower (.map X)) q → q.1.1 = "map") ∧
        (∃ w, MT t (d + 1) (dynL (upper (.map X))) w) ∧ ∀ x, ¬Vals (MT t (d + 1) (dynL (upper (.map X)))) KP x) ∧
      ∀ T, r = .tuple #[.atom "ok", T] → ∃ lt ut, Elixir.Module.Types.Descr.«lower_bound/1» (D m) T = .ok lt ∧
        Elixir.Module.Types.Descr.«upper_bound/1» (D m) T = .ok ut ∧ DE (level t d).E lt ∧ DE (level t d).E ut ∧
        (∀ x : PN t d, denD lt x ↔ Vals (MT t (d + 1) (rmDyn X)) KP x) ∧
        (∀ x : PN t d, denD ut x ↔ Vals (MT t (d + 1) (rmDyn X)) KP x ∨
          Vals (MT t (d + 1) (dynL (upper (.map X)))) KP x) ∧
        ((mapLookup X (.atom "dynamic") = none ∧ (level t (d + 1)).E T ∧
            ∀ x, (level t (d + 1)).den T x ↔ Vals (MT t (d + 1) (rmDyn X)) KP x) ∨
          mapLookup X (.atom "dynamic") ≠ none ∧ GC (level t d) T ∧
            (∀ x : PN t d, denD T x ↔ Vals (MT t (d + 1) (rmDyn X)) KP x) ∧ ∀ x : PN t d, denD (upper T) x ↔ Vals (MT t (d + 1) (rmDyn X)) KP x ∨
              Vals (MT t (d + 1) (dynL (upper (.map X)))) KP x) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
  have hK := level_K t d
  have hK' := level_K t (d + 1)
  have ef := (level t (d + 1)).ef
  have dSt : DE (level t (d + 1)).E (.map (rmDyn X)) := gX.low_tc
  obtain ⟨dR, sRm⟩ := rest_map dSt
  have onlyIff : (∀ q : PN t (d + 1), ¬denD (.map (rmM (rmDyn X))) q) ↔
      ∀ q : PN t (d + 1), denD (.map (rmDyn X)) q → q.1.1 = "map" :=
    ⟨fun h q hq => Classical.byContradiction fun nq => h q ((sRm q).mpr ⟨hq, nq⟩),
      fun h q hq => ((sRm q).mp hq).2 (h q ((sRm q).mp hq).1)⟩
  have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 8)) (.map (rmDyn X)) =
      .ok (boolAtom (bp (∀ q : PN t (d + 1), ¬denD (.map (rmM (rmDyn X))) q))) := by
    simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
    exact next_empty dR (by omega)
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 8))
      (.function false "Elixir.Module.Types.Descr" "-map_get/2-fun-0-" 1 #[]) #[r] =
        Elixir.Module.Types.Descr.«-map_get/2-fun-0-/1» r := fun r => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_get/2-fun-0-/1».pure]
  have bad1 : ∀ r, Lynx.Dispatcher.pure (D (k + 8))
      (.function false "Elixir.Module.Types.Descr" "-map_get/2-fun-1-" 1 #[]) #[r] =
        Elixir.Module.Types.Descr.«-map_get/2-fun-1-/1» r := fun r => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_get/2-fun-1-/1».pure]
  have lX : lower (.map X) = .map (rmDyn X) := by simp [lower]
  rw [lX]
  rw [Elixir.Module.Types.Descr.«map_get/2».eq_def]
  simp only [hk, Lynx.Except.ok_bind, Erlang.maps.«take/2», equalExact_eq_decide]
  cases hD : mapLookup X (.atom "dynamic") with
  | none =>
    have eX : rmDyn X = X := rmDyn_static hD
    have uX : upper (.map X) = .map X := by simp [upper, hD]
    have hX : DE (level t (d + 1)).E (.map X) := GC.static gX hD
    rw [eX] at mo onlyIff ⊢
    rw [uX]
    simp only [dynL, Lynx.Except.ok_bind]
    cases hb : mapLookup X (.atom "map") with
    | none =>
      have noM : ∀ w, ¬MT t (d + 1) X w := fun w ⟨b, e, _⟩ => by rw [hb] at e; cases e
      refine ⟨.atom "badmap", ?_, Or.inl rfl, ⟨fun _ => fun ⟨_, w, hw⟩ => noM w hw, fun _ => rfl⟩,
        ⟨fun h => (by simp at h), fun ⟨_, ⟨w, hw⟩, _⟩ => absurd hw (noM w)⟩, fun _ h => by cases h⟩
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso,
        bad, Elixir.Module.Types.Descr.«-map_get/2-fun-0-/1»]
    | some b =>
      have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "map") = .ok (.atom "true") := by
        simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
      by_cases restE : ∀ q : PN t (d + 1), ¬denD (.map (rmM X)) q
      rotate_left
      · rw [bp_false.mpr restE] at mo
        refine ⟨.atom "badmap", ?_, Or.inl rfl, ⟨fun _ => fun ⟨h, _⟩ => restE (onlyIff.mpr h), fun _ => rfl⟩,
          ⟨fun h => (by simp at h), fun ⟨h, _⟩ => absurd (onlyIff.mpr h) restE⟩, fun _ h => by cases h⟩
        simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_get/2-fun-0-/1», boolAtom]
      rw [bp_true.mpr restE] at mo
      obtain ⟨res, run, ⟨rfl, emp⟩ | ⟨T, rfl, hT, sT, ne⟩⟩ :=
        gget_static (t := t) (n := d + 1) (Or.inr ⟨X, rfl, de_map hX⟩) hs (m := k + 4) (by omega)
      · simp only [dynL] at emp
        refine ⟨.atom "badmap", ?_, Or.inl rfl, ⟨fun _ => fun ⟨_, w, hw⟩ => emp w hw, fun _ => rfl⟩,
          ⟨fun h => (by simp at h), fun ⟨_, ⟨w, hw⟩, _⟩ => absurd hw (emp w)⟩, fun _ h => by cases h⟩
        simp [key, mo, run, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_get/2-fun-0-/1», boolAtom]
      simp only [dynL] at sT ne
      have exM : ∃ w, MT t (d + 1) X w := by
        rcases ne with ⟨-, h⟩ | h
        · rw [hb] at h; cases h
        · exact h
      obtain ⟨eb, reb, seb⟩ := ef.empty_pub hT
      cases eb
      · have ne' : ∃ x, Vals (MT t (d + 1) X) KP x := Classical.byContradiction fun h =>
          absurd (seb.mpr fun x hx => h ⟨x, (sT x).mp hx⟩) (by simp)
        refine ⟨.tuple #[.atom "ok", T], ?_, Or.inr (Or.inr ⟨_, rfl⟩), ⟨fun h => (by simp at h), fun h => absurd ⟨onlyIff.mp restE, exM⟩ h⟩,
          ⟨fun h => (by simp at h), fun ⟨_, _, h⟩ => absurd ne' fun ⟨x, hx⟩ => h x hx⟩, fun T' e => ?_⟩
        · simp [key, mo, run, Lynx.Except.andAlso, reb (k + 8) (by omega), Lynx.Term.isMember, boolAtom]
        simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true, true_and] at e
        subst e
        obtain ⟨c, hc, sc, ub, lb, -, -⟩ := el_ops hT (k + 7)
        exact ⟨c, c, lb, ub, hc, hc, fun x => (sc x).symm.trans (sT x),
          fun x => ((sc x).symm.trans (sT x)).trans or_self_iff.symm, Or.inl ⟨trivial, hT, sT⟩⟩
      · have noV : ∀ x, ¬Vals (MT t (d + 1) X) KP x := fun x hx => seb.mp rfl x ((sT x).mpr hx)
        refine ⟨.atom "error", ?_, Or.inr (Or.inl rfl), ⟨fun h => (by simp at h), fun h => absurd ⟨onlyIff.mp restE, exM⟩ h⟩,
          ⟨fun _ => ⟨onlyIff.mp restE, exM, noV⟩, fun _ => rfl⟩, fun _ h => by cases h⟩
        simp [key, mo, run, Lynx.Except.andAlso, reb (k + 8) (by omega), Lynx.Term.isMember, boolAtom]
  | some Dy =>
    obtain ⟨tD, incl⟩ : TC (level t (d + 1)) Dy ∧ ∀ q : TP (level t (d + 1)), denD (.map X) q → denD Dy q := by
      rcases gX with tX | ⟨X', Dy', e, hD', tD, dS, incl⟩
      · rcases tX with h | ⟨X', e, sX'⟩
        · cases h
        · simp only [Term.map.injEq] at e; subst e; rw [sX'.static] at hD; cases hD
      · simp only [Term.map.injEq] at e; subst e; rw [hD] at hD'; cases hD'; exact ⟨tD, incl⟩
    rw [upper_dyn hD]
    have eS : (X.filter fun entry => !decide (compareExact ((Term.atom "dynamic").fuel entry.fst) (Term.atom "dynamic")
      entry.fst = .eq)) = rmDyn X := rfl
    simp only [eS, Lynx.Except.ok_bind]
    have keyD : Elixir.Module.Types.Descr.«descr_key?/2» Dy (.atom "map") =
        .ok (boolAtom (mapLookup (dynL Dy) (.atom "map")).isSome) := by
      rcases tD with rfl | ⟨Y, rfl, -⟩
      · simp [Elixir.Module.Types.Descr.«descr_key?/2», dynL, topM, mapLookup, boolAtom, pure, Except.pure]
      · cases h : mapLookup Y (.atom "map") <;>
          simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, dynL, h, boolAtom]
    by_cases restE : ∀ q : PN t (d + 1), ¬denD (.map (rmM (rmDyn X))) q
    rotate_left
    · rw [bp_false.mpr restE] at mo
      refine ⟨.atom "badmap", ?_, Or.inl rfl, ⟨fun _ => fun ⟨h, _⟩ => restE (onlyIff.mpr h), fun _ => rfl⟩,
        ⟨fun h => (by simp at h), fun ⟨h, _⟩ => absurd (onlyIff.mpr h) restE⟩, fun _ h => by cases h⟩
      cases hk : (mapLookup (dynL Dy) (.atom "map")).isSome <;>
        simp [keyD, hk, mo, Lynx.Except.andAlso, boolAtom, bad1, Elixir.Module.Types.Descr.«-map_get/2-fun-1-/1»]
    rw [bp_true.mpr restE] at mo
    have onlyS := onlyIff.mp restE
    rcases Classical.em ((mapLookup (dynL Dy) (.atom "map")).isSome = Bool.false) with hbm | hbm
    · have noD : ∀ w, ¬MT t (d + 1) (dynL Dy) w := fun w ⟨b, e, _⟩ => by simp [e] at hbm
      refine ⟨.atom "badmap", ?_, Or.inl rfl, ⟨fun _ => fun ⟨_, w, hw⟩ => noD w hw, fun _ => rfl⟩,
        ⟨fun h => (by simp at h), fun ⟨_, ⟨w, hw⟩, _⟩ => absurd hw (noD w)⟩, fun _ h => by cases h⟩
      simp [keyD, hbm, Lynx.Except.andAlso, boolAtom, bad1, Elixir.Module.Types.Descr.«-map_get/2-fun-1-/1»]
    have kt : Elixir.Module.Types.Descr.«descr_key?/2» Dy (.atom "map") = .ok (.atom "true") := by
      simp only [Bool.not_eq_false] at hbm
      simp [keyD, hbm, boolAtom]
    obtain ⟨rd, rrd, hd⟩ := gget_static (t := t) (n := d + 1) tD hs (m := k + 4) (by omega)
    simp only [kt, mo, boolAtom, ↓reduceIte, Lynx.Except.andAlso, rrd, Lynx.Except.ok_bind]
    rcases hd with ⟨rfl, noD⟩ | ⟨dt, rfl, hdt, sdt, ne⟩
    · refine ⟨.atom "badmap", ?_, Or.inl rfl, ⟨fun _ => fun ⟨_, w, hw⟩ => noD w hw, fun _ => rfl⟩,
        ⟨fun h => (by simp at h), fun ⟨_, ⟨w, hw⟩, _⟩ => absurd hw (noD w)⟩, fun _ h => by cases h⟩
      simp [bad1, Elixir.Module.Types.Descr.«-map_get/2-fun-1-/1»]
    have exD : ∃ w, MT t (d + 1) (dynL Dy) w := by
      rcases ne with ⟨-, h⟩ | h
      · simp [h] at hbm
      · exact h
    -- The static part, or none.
    obtain ⟨rs, rrs, st, ers, hst, sst⟩ : ∃ rs, Elixir.Module.Types.Descr.«map_get_static/2» (D (k + 8))
        (.map (rmDyn X)) s = .ok rs ∧ ∃ st, ((rs = .atom "badmap" ∧ st = .map []) ∨ rs = .tuple #[.atom "ok", st]) ∧
        (level t (d + 1)).E st ∧ ∀ x, (level t (d + 1)).den st x ↔ Vals (MT t (d + 1) (rmDyn X)) KP x := by
      obtain ⟨rs, rrs, hrs⟩ := gget_static (t := t) (n := d + 1) (Or.inr ⟨_, rfl, de_map dSt⟩) hs (m := k + 4) (by omega)
      refine ⟨rs, rrs, ?_⟩
      rcases hrs with ⟨rfl, noS⟩ | ⟨st, rfl, hst, sst, -⟩
      · exact ⟨.map [], Or.inl ⟨rfl, rfl⟩, ef.none, fun x => ⟨fun h => absurd h (ef.den_none x),
          fun ⟨w, hw, _⟩ => absurd hw (noS w)⟩⟩
      · exact ⟨st, Or.inr rfl, hst, sst⟩
    obtain ⟨eb, reb, seb⟩ := ef.empty_pub hdt
    have reb' := reb (k + 8) (by omega)
    cases eb
    rotate_left
    · have noV : ∀ x, ¬Vals (MT t (d + 1) (dynL Dy)) KP x := fun x hx => seb.mp rfl x ((sdt x).mpr hx)
      refine ⟨.atom "error", ?_, Or.inr (Or.inl rfl), ⟨fun h => (by simp at h), fun h => absurd ⟨onlyS, exD⟩ h⟩,
        ⟨fun _ => ⟨onlyS, exD, noV⟩, fun _ => rfl⟩, fun _ h => by cases h⟩
      rcases ers with ⟨rfl, rfl⟩ | rfl <;> simp [rrs, reb', Lynx.Term.isMember, boolAtom]
    have ne' : ∃ x, Vals (MT t (d + 1) (dynL Dy)) KP x := Classical.byContradiction fun h =>
      absurd (seb.mpr fun x hx => h ⟨x, (sdt x).mp hx⟩) (by simp)
    obtain ⟨c₁, hc₁, sc₁, cases₁⟩ := el_canon hdt
    obtain ⟨R, rR, gR, s₁, s₂⟩ := dyn_el_union hc₁ hst (m := k + 8) (by omega)
    refine ⟨.tuple #[.atom "ok", R], ?_, Or.inr (Or.inr ⟨_, rfl⟩), ⟨fun h => (by simp at h), fun h => absurd ⟨onlyS, exD⟩ h⟩,
      ⟨fun h => (by simp at h), fun ⟨_, _, h⟩ => absurd ne' fun ⟨x, hx⟩ => h x hx⟩, fun T e => ?_⟩
    · rcases cases₁ with ⟨de, rfl⟩ | ⟨hn, rfl⟩
      · rcases de with rfl | ⟨Z, rfl, sZ⟩
        · rcases ers with ⟨rfl, rfl⟩ | rfl <;>
            simp [rrs, reb', Lynx.Term.isMember, boolAtom, getMapKeys, rR]
        · rcases ers with ⟨rfl, rfl⟩ | rfl <;>
            simp [rrs, reb', Lynx.Term.isMember, boolAtom, getMapKeys_single, sZ.static, rR]
      · obtain ⟨q, SS, rfl⟩ := node_tuple hn
        have ex := expand_isT hn (k + 7)
        obtain ⟨Y, eY, sY⟩ := expN_map (.tuple #[.reference q, .map SS, gen]) (keyOf (level t d).nd)
        rw [eY] at ex rR
        have dY : Elixir.Module.Types.Descr.«dynamic/1» (D (k + 8)) (.map Y) =
            .ok (.map [(.atom "dynamic", .map Y)]) := by
          unfold Elixir.Module.Types.Descr.«dynamic/1»; simp [getMapKeys_single, sY]
        have gt : getMapKeys [Term.atom "dynamic"] (.tuple #[.reference q, .map SS, gen]) = [] := by simp [getMapKeys]
        rcases ers with ⟨rfl, rfl⟩ | rfl <;>
          simp [rrs, reb', Lynx.Term.isMember, boolAtom, gt, ex, unfold_map, dY, rR]
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true, true_and] at e
    subst e
    refine ⟨lower R, upper R, lower_bound_run gR.shape, upper_bound_run gR.ub, gR.low_tc, gR.up_tc,
      fun x => (denD_lower R x).trans ((s₁ x).trans (sst x)), fun x => (s₂ x).trans ?_, ?_⟩
    · rw [← sc₁]
      exact (or_congr (sdt x) (sst x)).trans or_comm
    refine Or.inr ⟨by simp, gR, fun x => (s₁ x).trans (sst x), fun x => (s₂ x).trans ?_⟩
    rw [← sc₁]
    exact (or_congr (sdt x) (sst x)).trans or_comm

end

section
variable {t : Term} {d : Nat}

theorem vals_mono {V : Type} {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {KP : MKey → Prop} {x : V}
    (h : Vals M₁ KP x) : Vals M₂ KP x :=
  let ⟨w, hw, κ, hκ, e⟩ := h; ⟨w, hM w hw, κ, hκ, e⟩

/-- Getting from less precise maps is less precise. -/
theorem get_prec {X : List (Term × Term)} {a₂ : Term} (gX : GC (level t (d + 1)) (.map X))
    (g₂ : GC (level t (d + 1)) a₂) {key s : Term} {KP : MKey → Prop} {m : Nat}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s) (hs : GForm s KP)
    (hm : (level t (d + 1)).K + 30 ≤ m)
    (lo : ∀ v : PN t (d + 1), denD a₂ v → denD (.map X) v)
    (up : ∀ v : PN t (d + 1), denD (upper (.map X)) v → denD (upper a₂) v) {T : Term}
    (run : Elixir.Module.Types.Descr.«map_get/2» (D m) (.map X) key = .ok (.tuple #[.atom "ok", T])) :
    ∃ T₂, Elixir.Module.Types.Descr.«map_get/2» (D m) a₂ key = .ok (.tuple #[.atom "ok", T₂]) ∧
      «precise?/2» (D m) T T₂ = .ok (.atom "true") := by
  obtain ⟨r, run', -, bA, eA, semA⟩ := gget_sem gX hk hs hm
  rw [run] at run'; cases run'
  obtain ⟨onlyA, neA⟩ : (∀ q : PN t (d + 1), denD (lower (.map X)) q → q.1.1 = "map") ∧
      ∃ w, MT t (d + 1) (dynL (upper (.map X))) w := Classical.byContradiction fun h => by
    have := bA.mpr h; simp at this
  obtain ⟨x₀, hx₀⟩ : ∃ x, Vals (MT t (d + 1) (dynL (upper (.map X)))) KP x := Classical.byContradiction fun h => by
    have := eA.mpr ⟨onlyA, neA, fun x hx => h ⟨x, hx⟩⟩; simp at this
  have lo' : ∀ v : PN t (d + 1), denD (lower a₂) v → denD (lower (.map X)) v := fun v h =>
    (denD_lower _ _).mpr (lo v ((denD_lower _ _).mp h))
  obtain ⟨X₂, rfl⟩ : ∃ X₂, a₂ = .map X₂ := by
    rcases g₂.shape with rfl | ⟨X₂, rfl⟩
    · have := onlyA bitPt (lo' bitPt (by simp [lower, denD_term]))
      simp [bitPt] at this
    · exact ⟨X₂, rfl⟩
  have muA : ∀ w, MT t (d + 1) (dynL (upper (.map X))) w → MT t (d + 1) (dynL (upper (.map X₂))) w := fun w h =>
    (mt_dynL2 g₂.up_tc w).mpr (up _ ((mt_dynL2 gX.up_tc w).mp h))
  have msB : ∀ w, MT t (d + 1) (rmDyn X₂) w → MT t (d + 1) (rmDyn X) w := fun w h =>
    (denD_mpt w).mp ((denD_rmDyn X _).mpr (lo _ ((denD_rmDyn X₂ _).mp ((denD_mpt w).mpr h))))
  have msA : ∀ w, MT t (d + 1) (rmDyn X) w → MT t (d + 1) (dynL (upper (.map X))) w := fun w h =>
    (mt_dynL2 gX.up_tc w).mpr (GC.inv gX _ ((denD_rmDyn X _).mp ((denD_mpt w).mpr h)))
  obtain ⟨r₂, run₂, sh₂, bB, eB, semB⟩ := gget_sem g₂ hk hs hm
  have onlyB : ∀ q : PN t (d + 1), denD (lower (.map X₂)) q → q.1.1 = "map" := fun q h => onlyA q (lo' q h)
  have neB : ∃ w, MT t (d + 1) (dynL (upper (.map X₂))) w := let ⟨w, hw⟩ := neA; ⟨w, muA w hw⟩
  rcases sh₂ with rfl | rfl | ⟨T₂, rfl⟩
  · exact absurd ⟨onlyB, neB⟩ (bB.mp rfl)
  · exact absurd (vals_mono muA hx₀) ((eB.mp rfl).2.2 x₀)
  obtain ⟨lt, ut, lA, uA, dlA, duA, slA, suA, -⟩ := semA T rfl
  obtain ⟨lt₂, ut₂, lB, uB, dlB, duB, slB, suB, -⟩ := semB T₂ rfl
  have hm' : (level t d).K + 23 ≤ m := by rw [level_K] at hm ⊢; omega
  refine ⟨T₂, run₂, precise_of_bounds (n := d) hm' lA uA lB uB dlA duA dlB duB
    (fun x h => (slA x).mpr (vals_mono msB ((slB x).mp h))) (fun x h => (suB x).mpr (Or.inr ?_))⟩
  rcases (suA x).mp h with h | h
  · exact vals_mono (fun u h => muA u (msA u h)) h
  · exact vals_mono muA h

end

section
variable {t : Term} {d : Nat}

/-- Two keys whose splits select the same keys get the same results. -/
theorem get_same {X : List (Term × Term)} (gX : GC (level t (d + 1)) (.map X)) {k₁ k₂ s₁ s₂ : Term}
    {KP : MKey → Prop} {m : Nat}
    (hk₁ : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k₁ = .ok s₁) (hs₁ : GForm s₁ KP)
    (hk₂ : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k₂ = .ok s₂) (hs₂ : GForm s₂ KP)
    (hm : (level t (d + 1)).K + 30 ≤ m) :
    ∃ r₁ r₂, Elixir.Module.Types.Descr.«map_get/2» (D m) (.map X) k₁ = .ok r₁ ∧
      Elixir.Module.Types.Descr.«map_get/2» (D m) (.map X) k₂ = .ok r₂ ∧
      ((∃ T₁ T₂, r₁ = .tuple #[.atom "ok", T₁] ∧ r₂ = .tuple #[.atom "ok", T₂] ∧
          Elixir.Module.Types.Descr.«equal?/2» (D m) T₁ T₂ = .ok (.atom "true")) ∨
        (r₁ = r₂ ∧ (r₁ = .atom "badmap" ∨ r₁ = .atom "error"))) := by
  obtain ⟨r₁, run₁, sh₁, b₁, e₁, sem₁⟩ := gget_sem gX hk₁ hs₁ hm
  obtain ⟨r₂, run₂, sh₂, b₂, e₂, sem₂⟩ := gget_sem gX hk₂ hs₂ hm
  refine ⟨r₁, r₂, run₁, run₂, ?_⟩
  rcases sh₁ with rfl | rfl | ⟨T₁, rfl⟩ <;> rcases sh₂ with rfl | rfl | ⟨T₂, rfl⟩
  · exact Or.inr ⟨rfl, Or.inl rfl⟩
  · exact absurd (b₁.mp rfl) (fun h => h ⟨(e₂.mp rfl).1, (e₂.mp rfl).2.1⟩)
  · exact absurd (b₁.mp rfl) (fun h => h (Classical.byContradiction fun h' => by
      have := b₂.mpr h'; simp at this))
  · exact absurd (b₂.mp rfl) (fun h => h ⟨(e₁.mp rfl).1, (e₁.mp rfl).2.1⟩)
  · exact Or.inr ⟨rfl, Or.inr rfl⟩
  · have := e₁.mp rfl
    exact absurd (e₂.mpr this) (by simp)
  · exact absurd (b₂.mp rfl) (fun h => h (Classical.byContradiction fun h' => by
      have := b₁.mpr h'; simp at this))
  · have := e₂.mp rfl
    exact absurd (e₁.mpr this) (by simp)
  refine Or.inl ⟨T₁, T₂, rfl, rfl, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, k₁'⟩ := sem₁ T₁ rfl
  obtain ⟨-, -, -, -, -, -, -, -, k₂'⟩ := sem₂ T₂ rfl
  rcases k₁' with ⟨hD, hT₁, sT₁⟩ | ⟨nD, gT₁, lT₁, uT₁⟩ <;> rcases k₂' with ⟨hD', hT₂, sT₂⟩ | ⟨nD', gT₂, lT₂, uT₂⟩
  · exact elem_equal (level t (d + 1)).ef hT₁ hT₂ (fun v => (sT₁ v).trans (sT₂ v).symm) (by omega)
  · exact absurd hD nD'
  · exact absurd hD' nD
  · exact gc_equal gT₁ gT₂ (by rw [level_K] at hm ⊢; omega) (fun v => (lT₁ v).trans (lT₂ v).symm)
      (fun v => (uT₁ v).trans (uT₂ v).symm)

end

section

/-- A static split is a gradual one with no optional keys. -/
theorem gform_splitT {rs : List Term} {neg : Term} {ds : List Term} (ok : SplitOk rs neg ds)
    (nr : ∀ N, neg = .map N → rs = []) (na : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {KP : MKey → Prop} (kp : ∀ κ, SplitKey rs neg ds κ ↔ KP κ) : GForm (splitT rs neg ds) KP := by
  rcases ok.hneg with rfl | ⟨N, rfl⟩
  · exact Or.inl ⟨rs, [], ds, [], by simp [splitT, Term.list], by simpa using ok, fun κ => by simpa using kp κ⟩
  · obtain rfl := nr N rfl
    exact Or.inr (Or.inl ⟨N, ds, [], by simp [splitT, Term.list], by simpa using ok, na N rfl,
      fun κ => by simpa using kp κ⟩)

end


section
variable {t : Term} {n : Nat}

theorem upd_static_g' {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) {s neg : Term}
    {P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop}
    (hP : DnfPuts s neg P)
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {m : Nat}
    (hm : (level t n).K + 27 ≤ m) (st : Bool) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X) (s) (forceOp v)
        (.atom "false") (boolAtom st) = .ok res ∧
      (((res = .atom "badmap" ∨ (res = .tuple #[.map [], .map [], .nil, .atom "false"] ∧
          mapLookup X (.atom "map") = none)) ∧ ∀ w, ¬MT t n X w) ∨
        (∃ w, MT t n X w) ∧ ∃ Y f, res = .tuple #[.map [], .map Y, .nil, f] ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          (∀ w, MT t n Y w ↔ P (level t n).den (MT t n X) v w) ∧
          (f = .atom "true" ∨ ∀ w, ¬P (level t n).den (MT t n X) v w)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 7 := ⟨m - 7, by omega⟩
  have flag : Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 7)) (.map X) (s) (forceOp v)
      (.atom "false") (boolAtom st) = Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 6 + 1)) (.map X)
      (s) (forceOp v) (.atom "false") (.atom "true") := by
    cases st
    · exact update_static_flag (k + 6) _ _ _ _
    · rfl
  rw [flag]
  have sX := de_map hX
  cases hb : mapLookup X (.atom "map") with
  | none =>
    refine ⟨_, ?_, Or.inl ⟨Or.inr ⟨rfl, rfl⟩, fun w ⟨b, h, _⟩ => by rw [hb] at h; cases h⟩⟩
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def]
    simp [getMapKeys_single, hb, pure, Except.pure]
  | some b =>
    have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
    have mt : ∀ w, MT t n X w ↔ denMF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [MT, hb]
    have conv : (fun u => denMF (level t n).E (level t n).den b u = Bool.true) = MT t n X :=
      funext fun u => propext (mt u).symm
    obtain ⟨res, run, ⟨rfl, emp⟩ | ⟨Y, f, rfl, ⟨w₀, hw₀⟩, hf, hY⟩⟩ :=
      dput_update_static_g hP hNa (level t n).ef (n := k + 1) (by rw [level_K] at hm ⊢; omega) hv sv hb fb
    · exact ⟨_, run, Or.inl ⟨Or.inl rfl, fun w hw => by have := emp w; rw [(mt w).mp hw] at this; cases this⟩⟩
    simp only [conv] at hY hf
    refine ⟨_, run, Or.inr ⟨⟨w₀, (mt w₀).mpr hw₀⟩, ?_⟩⟩
    rcases hY with ⟨rfl, emp⟩ | ⟨r, rfl, fr, sr⟩
    · refine ⟨[], f, rfl, Or.inr ⟨_, rfl, descrC_nil⟩, fun q hq => ?_, fun w => ?_, hf⟩
      · rw [denD_map] at hq; simp [mapLookup, dn_none] at hq
      · simp only [MT, mapLookup, List.find?_nil, Option.map_none, reduceCtorEq, false_and, exists_false, false_iff, equalExact_eq_decide]
        exact emp w
    · refine ⟨_, f, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, fun q hq => ?_, fun w => ?_, hf⟩
      · rw [denD_map] at hq
        by_cases e : q.1.1 = "map"
        · exact e
        · simp [mapLookup, e, dn_none] at hq
      · rw [← sr]; simp [MT, mapLookup]

theorem gupd_g' {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {Dy : Term}
    (hD : mapLookup X (.atom "dynamic") = some Dy) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) {s neg : Term}
    {P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop}
    (hP : DnfPuts s neg P)
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {m : Nat}
    (hm : (level t n).K + 30 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X) (s) (forceOp v)
        (.atom "false") = .ok res ∧
      ((res = .atom "badmap" ∧ ¬((∀ q : PN t n, denD (.map (rmDyn X)) q → q.1.1 = "map") ∧ ∃ w, MT t n (dynL Dy) w)) ∨
        (∃ er, res = .tuple #[.atom "error", er] ∧ (∀ w, ¬PutOfP P t n (dynL Dy) v w) ∧
          (∀ q : PN t n, denD (.map (rmDyn X)) q → q.1.1 = "map") ∧ ∃ w, MT t n (dynL Dy) w) ∨
        ∃ T R er, res = .tuple #[T, R, er] ∧ GC (level t n) R ∧
          (∀ q : PN t n, denD (upper R) q → q.1.1 = "map") ∧
          (∀ q : PN t n, denD (.map (rmDyn X)) q → q.1.1 = "map") ∧
          (∀ w, denD R (mpt (t := t) (n := n) w) ↔ PutOfP P t n (rmDyn X) v w) ∧
          (∀ w, denD (upper R) (mpt (t := t) (n := n) w) ↔
            PutOfP P t n (rmDyn X) v w ∨ PutOfP P t n (dynL Dy) v w) ∧ ∃ w, MT t n (dynL Dy) w) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
  rcases gX with tX | ⟨X', Dy', e, hD', tD, dS, incl⟩
  · rcases tX with h | ⟨X', e, sX'⟩
    · cases h
    · simp only [Term.map.injEq] at e; subst e; rw [sX'.static] at hD; cases hD
  simp only [Term.map.injEq] at e; subst e
  rw [hD] at hD'; cases hD'
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def]
  simp only [Erlang.maps.«take/2», hD, equalExact_eq_decide]
  have eS : (X.filter fun entry => !decide (compareExact ((Term.atom "dynamic").fuel entry.fst) (Term.atom "dynamic") entry.fst = .eq)) = rmDyn X := rfl
  rw [eS]
  simp only [Lynx.Except.ok_bind]
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 8))
      (.function false "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-1-" 1 #[]) #[r] =
        Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1» r := fun r => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-1-/1».pure]
  have dSt : DE (level t n).E (.map (rmDyn X)) := Or.inr ⟨_, rfl, dS⟩
  obtain ⟨dR, sRm⟩ := rest_map dSt
  have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 8)) (.map (rmDyn X)) =
      .ok (boolAtom (bp (∀ q : PN t n, ¬denD (.map (rmM (rmDyn X))) q))) := by
    simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
    exact next_empty dR (by omega)
  have dDy : DE (level t n).E (.map (dynL Dy)) := by
    rcases tD with rfl | ⟨Y, rfl, sY⟩
    · exact mapTop_de
    · exact Or.inr ⟨Y, rfl, sY⟩
  have stD : ∀ st, Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 8)) Dy (s) (forceOp v)
      (.atom "false") st = Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 8)) (.map (dynL Dy))
      (s) (forceOp v) (.atom "false") st := by
    intro st
    rcases tD with rfl | ⟨Y, rfl, -⟩
    · conv => lhs; rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def]
      simp [Lynx.Term.getMapKeys, dynL, topM]
    · rfl
  have keyD : Elixir.Module.Types.Descr.«descr_key?/2» Dy (.atom "map") =
      .ok (boolAtom (mapLookup (dynL Dy) (.atom "map")).isSome) := by
    rcases tD with rfl | ⟨Y, rfl, -⟩
    · simp [Elixir.Module.Types.Descr.«descr_key?/2», dynL, topM, mapLookup, boolAtom, pure, Except.pure]
    · cases h : mapLookup Y (.atom "map") <;>
        simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, dynL, h, boolAtom]
  rw [stD]
  rcases Classical.em (¬∀ q : PN t n, ¬denD (.map (rmM (rmDyn X))) q) with hmo | hmo
  · rw [bp_false.mpr hmo] at mo
    refine ⟨_, ?_, Or.inl ⟨rfl, fun ⟨h, _⟩ => hmo fun q hq => ((sRm q).mp hq).2 (h q ((sRm q).mp hq).1)⟩⟩
    cases hk : (mapLookup (dynL Dy) (.atom "map")).isSome <;>
      simp [keyD, hk, mo, Lynx.Except.andAlso, boolAtom, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1»]
  rw [bp_true.mpr (Classical.not_not.mp hmo)] at mo
  rcases Classical.em ((mapLookup (dynL Dy) (.atom "map")).isSome = Bool.false) with hbm | hbm
  · refine ⟨_, ?_, Or.inl ⟨rfl, fun ⟨_, w, b, hb, _⟩ => by rw [hb] at hbm; cases hbm⟩⟩
    simp [keyD, hbm, Lynx.Except.andAlso, boolAtom, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1»]
  have kt : Elixir.Module.Types.Descr.«descr_key?/2» Dy (.atom "map") = .ok (.atom "true") := by
    simp only [Bool.not_eq_false] at hbm
    simp [keyD, hbm, boolAtom]
  -- The static part: its maps put, or none.
  obtain ⟨rS, rrS, hS⟩ := upd_static_g dSt hv sv hP hNa (m := k + 8) (by omega) Bool.true
  simp only [boolAtom, ↓reduceIte] at rrS
  -- The union of a static part with the dynamic part of the maps of a put.
  have fin : ∀ Sd Yd : List (Term × Term), DE (level t n).E (.map Sd) → DE (level t n).E (.map Yd) →
      (∀ q : PN t n, denD (.map Sd) q → q.1.1 = "map") → (∀ q : PN t n, denD (.map Yd) q → q.1.1 = "map") →
      ∃ c, Elixir.Module.Types.Descr.«opt_union/2» (D (k + 8)) (.map Sd) (.map [(.atom "dynamic", .map Yd)]) =
          .ok c ∧ GC (level t n) c ∧ (∀ q : PN t n, denD (upper c) q → q.1.1 = "map") ∧
        (∀ q : PN t n, denD c q ↔ denD (.map Sd) q) ∧
        ∀ q : PN t n, denD (upper c) q ↔ denD (.map Sd) q ∨ denD (.map Yd) q := by
    intro Sd Yd dSd dYd oS oY
    have noP : ∀ q : PN t n, ¬denD (.map [(.atom "dynamic", .map Yd)]) q := fun q h => by
      have := (denD_rmDyn [(.atom "dynamic", .map Yd)] q).mpr h
      rw [rmDyn_cons_dyn] at this
      simp [rmDyn, denD_map, mapLookup, dn_none] at this
    have gY : GC (level t n) (.map [(.atom "dynamic", .map Yd)]) :=
      Or.inr ⟨_, .map Yd, rfl, by simp [mapLookup], dYd, by rw [rmDyn_cons_dyn]; exact descrC_nil,
        fun q h => absurd h (noP q)⟩
    obtain ⟨c, gc, rc, sc₁, sc₂⟩ := gc_opt_union (GC.tc dSd) gY [] (m := k + 8) (by rw [level_K] at hm ⊢; omega)
    have uS : upper (.map Sd) = .map Sd := upper_tc dSd
    have uY : upper (.map [(.atom "dynamic", .map Yd)]) = .map Yd := upper_dyn (by simp [mapLookup])
    refine ⟨c, by simpa [Elixir.Module.Types.Descr.«opt_union/2»] using rc, gc, fun q h => ?_, fun q => ?_,
      fun q => ?_⟩
    · rw [sc₂, uS, uY] at h
      rcases h with h | h
      · exact oS q h
      · exact oY q h
    · rw [sc₁]; simp [noP q]
    · rw [sc₂, uS, uY]
  -- The static part, as the gradual update sees it.
  obtain ⟨Sd, fs, eS, dSd, oSd, sSd⟩ : ∃ Sd fs, ((rS = .atom "badmap" ∧ Sd = [] ∧ fs = .atom "false") ∨
      rS = .tuple #[.map [], .map Sd, .nil, fs]) ∧ DE (level t n).E (.map Sd) ∧
      (∀ q : PN t n, denD (.map Sd) q → q.1.1 = "map") ∧
      ∀ w, denD (.map Sd) (mpt (t := t) (n := n) w) ↔ PutOfP P t n (rmDyn X) v w := by
    rcases hS with ⟨hrS, noS⟩ | ⟨exS, Ys, fs, rfl, dYs, onlyYs, semYs, -⟩
    · refine ⟨[], .atom "false", by rcases hrS with rfl | rfl <;> simp, Or.inr ⟨_, rfl, descrC_nil⟩,
        fun q h => by simp [denD_map, mapLookup, dn_none] at h, fun w => ?_⟩
      simp only [denD_map, mapLookup, List.find?_nil, Option.map_none, equalExact_eq_decide]
      constructor
      · intro h; simp [mpt, dn_none] at h
      · rintro ⟨⟨u, hu⟩, -⟩; exact absurd hu (noS u)
    · refine ⟨Ys, fs, Or.inr rfl, dYs, onlyYs, fun w => ?_⟩
      rw [denD_mpt, semYs]
      exact ⟨fun h => ⟨exS, h⟩, fun h => h.2⟩
  obtain ⟨rd, rrd, hd⟩ := upd_static_g' dDy hv sv hP hNa (m := k + 8) (by omega) Bool.false
  simp only [boolAtom, Bool.false_eq_true, ↓reduceIte] at rrd
  simp only [kt, mo, boolAtom, ↓reduceIte, Lynx.Except.andAlso, rrd, rrS, Lynx.Except.ok_bind]
  rcases hd with ⟨hrd | ⟨hrd, nk⟩, noD⟩ | ⟨exD, Yd, fd, rfl, dYd, onlyYd, semYd, hfd⟩
  · subst hrd
    exact ⟨_, by simp [bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1»],
      Or.inl ⟨rfl, fun ⟨_, w, hw⟩ => noD w hw⟩⟩
  · exfalso
    rw [nk] at hbm
    exact hbm rfl
  · by_cases fe : fd = .atom "false" ∨ fd = .atom "nil"
    · have emp : ∀ w, ¬PutOfP P t n (dynL Dy) v w := by
        rcases hfd with rfl | h
        · rcases fe with h | h <;> simp at h
        · exact fun w ⟨_, hw⟩ => h w hw
      refine ⟨.tuple #[.atom "error", .nil], ?_, Or.inr (Or.inl ⟨_, rfl, emp, fun q hq => Classical.byContradiction
        fun nq => Classical.not_not.mp hmo q ((sRm q).mpr ⟨hq, nq⟩), exD⟩)⟩
      rcases eS with ⟨rfl, rfl, rfl⟩ | rfl <;> rcases fe with rfl | rfl <;>
        simp [Lynx.Term.isMember, Erlang.erlang.«++/2», pure, Except.pure]
    · have fe' := not_or.mp fe
      have fm : Lynx.Term.isMember fd [.atom "false", .atom "nil"] = .atom "false" := by
        simp [Lynx.Term.isMember, compareExact_eq_atom, fe'.1, fe'.2]
      obtain ⟨c, rc, gc, oc, sc₁, sc₂⟩ := fin Sd Yd dSd dYd oSd onlyYd
      have sYd : mapLookup Yd (.atom "dynamic") = none := (de_map dYd).static
      have fY : (Yd.find? fun entry => decide (compareExact ((Term.atom "dynamic").fuel entry.fst) (Term.atom "dynamic")
          entry.fst = Ordering.eq)) = none := by
        simpa [mapLookup] using sYd
      have rc' : Elixir.Module.Types.Descr.«opt_union/2» (D (k + 8)) (.map Sd) (.map [(.atom "dynamic", .map Yd)]) =
          .ok c := rc
      have rv : Elixir.Module.Types.Descr.«opt_union/2» (D (k + 8)) (.map []) (.map [(.atom "dynamic", .map [])]) =
          .ok (.map [(.atom "dynamic", .map [])]) := by
        simp [Elixir.Module.Types.Descr.«opt_union/2», opt_union_nil_l]
      refine ⟨.tuple #[.map [(.atom "dynamic", .map [])], c, .nil], ?_,
        Or.inr (Or.inr ⟨_, c, _, rfl, gc, oc, fun q hq => Classical.byContradiction fun nq =>
          Classical.not_not.mp hmo q ((sRm q).mpr ⟨hq, nq⟩), fun w => (sc₁ _).trans (sSd w), fun w => ?_, ?_⟩)⟩
      · rcases eS with ⟨rfl, rfl, rfl⟩ | rfl <;>
          simp [fm, getMapKeys_single, mapLookup, fY, rv, rc', Erlang.erlang.«++/2», pure,
            Except.pure]
      · rw [sc₂, sSd, denD_mpt, semYd]
        exact ⟨fun h => h.imp id fun h => ⟨exD, h⟩, fun h => h.imp id fun h => h.2⟩
      · exact exD


theorem mt_dynL {a : Term} (ha : TC (level t n) a) (u : MW (level t n).V) :
    MT t n (dynL a) u ↔ denD a (mpt (t := t) (n := n) u) := by
  rcases ha with rfl | ⟨Y, rfl, -⟩
  · exact ⟨fun _ => denD_term _, fun _ => mt_top u⟩
  · exact (denD_mpt u).symm

theorem gput_sem_g {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {Dy : Term}
    (hD : mapLookup X (.atom "dynamic") = some Dy) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) {s neg : Term}
    {P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop} (hP : DnfPuts s neg P)
    (hmono : ∀ M₁ M₂ : MW (level t n).V → Prop, (∀ u, M₁ u → M₂ u) → ∀ w, P (level t n).den M₁ v w →
      P (level t n).den M₂ v w)
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {m : Nat}
    (hm : (level t n).K + 30 ≤ m) :
    ∃ res, (do
        let r ← Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X) s (forceOp v)
          (.atom "false")
        putRes r) = .ok res ∧
      (res ≠ .atom "badmap" ↔ (∀ q : PN t n, denD (.map (rmDyn X)) q → q.1.1 = "map") ∧ ∃ w, MT t n (dynL Dy) w) ∧
      ∀ R, res = .tuple #[.atom "ok", R] → GC (level t n) R ∧ (∀ q : PN t n, denD (upper R) q → q.1.1 = "map") ∧
        (∀ w, denD R (mpt (t := t) (n := n) w) ↔ PutOfP P t n (rmDyn X) v w) ∧
        ∀ w, denD (upper R) (mpt (t := t) (n := n) w) ↔ PutOfP P t n (dynL Dy) v w := by
  obtain ⟨tD, incl⟩ : TC (level t n) Dy ∧ ∀ q : TP (level t n), denD (.map X) q → denD Dy q := by
    rcases gX with tX | ⟨X', Dy', e, hD', tD, -, incl⟩
    · rcases tX with h | ⟨X', e, sX'⟩
      · cases h
      · simp only [Term.map.injEq] at e; subst e; rw [sX'.static] at hD; cases hD
    · simp only [Term.map.injEq] at e; subst e
      rw [hD] at hD'; cases hD'
      exact ⟨tD, incl⟩
  have up : ∀ w, PutOfP P t n (rmDyn X) v w → PutOfP P t n (dynL Dy) v w :=
    fun w ⟨⟨u, hu⟩, h⟩ => ⟨⟨u, static_in_dyn tD incl u hu⟩, hmono _ _ (static_in_dyn tD incl) w h⟩
  obtain ⟨res, run, ⟨rfl, nc⟩ | ⟨er, rfl, emp, only, ex⟩ | ⟨T, R, er, rfl, gR, oR, oS, s₁, s₂, ex⟩⟩ :=
    gupd_g' (P := P) gX hD hv sv hP hNa hm
  · exact ⟨_, by simp [run, putRes], ⟨fun h => absurd rfl h, fun c => absurd c nc⟩, fun R e => by cases e⟩
  · refine ⟨.tuple #[.atom "ok", .map []], by simp [run, putRes, pure, Except.pure], ⟨fun _ => ⟨only, ex⟩,
      fun _ => by simp⟩, fun R e => ?_⟩
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true, true_and] at e
    subst e
    refine ⟨GC.tc (Or.inr ⟨[], rfl, descrC_nil⟩), fun q h => by simp [upper, mapLookup, denD_map, dn_none] at h,
      fun w => ?_, fun w => ?_⟩
    · simp only [denD_map, mapLookup, List.find?_nil, Option.map_none, equalExact_eq_decide]
      exact ⟨fun h => by simp [mpt, dn_none] at h, fun h => absurd (up w h) (emp w)⟩
    · simp only [upper, mapLookup, List.find?_nil, Option.map_none, Option.getD_none, denD_map, equalExact_eq_decide]
      exact ⟨fun h => by simp [mpt, dn_none] at h, fun h => absurd h (emp w)⟩
  · refine ⟨.tuple #[.atom "ok", R], by simp [run, putRes, pure, Except.pure], ⟨fun _ => ⟨oS, ex⟩, fun _ => by simp⟩,
      fun R' e => ?_⟩
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true, true_and] at e
    subst e
    refine ⟨gR, oR, s₁, fun w => ?_⟩
    rw [s₂]
    exact ⟨fun h => h.elim (up w) id, Or.inr⟩



end
section
variable {t : Term} {n : Nat}

/-- `map_put/3` at the split of a key type of the laws: it gives a type exactly when the map type's lower bound holds
only maps and its upper bound some map; the result holds, for a static value, the puts at the maps of the lower
bound, and in its upper bound the puts of the value's upper bound at the maps of the upper bound. -/
theorem put_all_g {X : List (Term × Term)} (gX : GC (level t (n + 1)) (.map X)) {v : Term} (gv : GC (level t n) v)
    (dup : DE (level t n).E (upper v)) {key s neg : Term}
    {P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop} {m : Nat}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s) (hP : DnfPuts s neg P)
    (hmono : ∀ x (M₁ M₂ : MW (level t (n + 1)).V → Prop), (∀ u, M₁ u → M₂ u) → ∀ w,
      P (level t (n + 1)).den M₁ x w → P (level t (n + 1)).den M₂ x w)
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) (hm : (level t (n + 1)).K + 30 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_put/3» (D m) (.map X) key v = .ok res ∧
      (res ≠ .atom "badmap" ↔ (∀ q : PN t (n + 1), denD (lower (.map X)) q → q.1.1 = "map") ∧
        ∃ w, MT t (n + 1) (dynL (upper (.map X))) w) ∧
      ∀ R, res = .tuple #[.atom "ok", R] → GC (level t (n + 1)) R ∧
        (∀ q : PN t (n + 1), denD (upper R) q → q.1.1 = "map") ∧
        (∀ w, denD R (mpt (t := t) (n := n + 1) w) ↔ upper v = v ∧ PutOfP P t (n + 1) (rmDyn X) v w) ∧
        ∀ w, denD (upper R) (mpt (t := t) (n := n + 1) w) ↔
          PutOfP P t (n + 1) (dynL (upper (.map X))) (upper v) w := by
  have static : ∀ {x : Term}, (x = .atom "term" ∨ ∃ Z, x = .map Z ∧ mapLookup Z (.atom "dynamic") = none) →
      DE (level t n).E x →
      ∃ res, Elixir.Module.Types.Descr.«map_put/3» (D m) (.map X) key x = .ok res ∧
        (res ≠ .atom "badmap" ↔ (∀ q : PN t (n + 1), denD (lower (.map X)) q → q.1.1 = "map") ∧
          ∃ w, MT t (n + 1) (dynL (upper (.map X))) w) ∧
        ∀ R, res = .tuple #[.atom "ok", R] → GC (level t (n + 1)) R ∧
          (∀ q : PN t (n + 1), denD (upper R) q → q.1.1 = "map") ∧
          (∀ w, denD R (mpt (t := t) (n := n + 1) w) ↔ PutOfP P t (n + 1) (rmDyn X) x w) ∧
          ∀ w, denD (upper R) (mpt (t := t) (n := n + 1) w) ↔ PutOfP P t (n + 1) (dynL (upper (.map X))) x w := by
    intro x sx dx
    have hx : (level t (n + 1)).E x := Or.inl dx
    have sx' : x = .atom "term" ∨ ∃ Z, x = .map Z := sx.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
    cases hD : mapLookup X (.atom "dynamic") with
    | none =>
      have dX := GC.static gX hD
      have lX : lower (.map X) = .map X := by simp [lower, rmDyn_static hD]
      have uX : upper (.map X) = .map X := by simp [upper, hD]
      rw [lX, uX, rmDyn_static hD]
      obtain ⟨res, run, ⟨rfl, nO⟩ | ⟨Y, rfl, onlyX, dY, onlyY, semY⟩⟩ :=
        dput_g (t := t) (n := n + 1) dX hk hP hNa hx sx (by omega)
      · exact ⟨_, run, ⟨fun h => absurd rfl h, fun ⟨h₁, w, hw⟩ => absurd ⟨h₁, w, hw⟩ nO⟩, fun R e => by cases e⟩
      refine ⟨_, run, ⟨fun _ => ⟨onlyX.1, onlyX.2⟩, fun _ => by simp⟩, fun R e => ?_⟩
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true, true_and] at e
      subst e
      have uY := upper_tc dY
      refine ⟨GC.tc dY, fun q h => onlyY q (by rwa [uY] at h), fun w => ?_, fun w => ?_⟩
      · rw [denD_mpt, semY]; exact ⟨fun h => ⟨onlyX.2, h⟩, fun h => h.2⟩
      · rw [uY, denD_mpt, semY]; exact ⟨fun h => ⟨onlyX.2, h⟩, fun h => h.2⟩
    | some Dy =>
      have uX : upper (.map X) = Dy := upper_dyn hD
      rw [uX, put_static_value_g hk sx]
      exact gput_sem_g gX hD hx sx' hP (hmono x) hNa hm
  rcases gv.cases with rfl | ⟨V, rfl, hV⟩ | ⟨V, rfl, hV⟩ | ⟨V, Y, rfl, hV, hY⟩
  · obtain ⟨res, run, iff, sem⟩ := static (Or.inl rfl) (Or.inl rfl)
    exact ⟨res, run, iff, fun R e =>
      let ⟨g, o, l, u⟩ := sem R e; ⟨g, o, fun w => (l w).trans ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩, u⟩⟩
  · have uV : upper (.map V) = .map V := by simp [upper, hV]
    rw [uV]
    obtain ⟨res, run, iff, sem⟩ := static (Or.inr ⟨V, rfl, hV⟩) (uV ▸ dup)
    exact ⟨res, run, iff, fun R e =>
      let ⟨g, o, l, u⟩ := sem R e; ⟨g, o, fun w => (l w).trans ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩, u⟩⟩
  all_goals
    obtain ⟨Dv, hD⟩ : ∃ Dv, mapLookup V (.atom "dynamic") = some Dv := ⟨_, hV⟩
    have uV : upper (.map V) = Dv := upper_dyn hD
    rw [uV] at dup ⊢
    have notS : Dv ≠ .map V := fun e => by
      rcases dup with h | ⟨Z, h, sZ⟩
      · rw [e] at h; cases h
      · rw [e] at h; cases h; rw [sZ.static] at hD; cases hD
    have hx : (level t (n + 1)).E Dv := Or.inl dup
    have sx : Dv = .atom "term" ∨ ∃ Z, Dv = .map Z := by
      rcases dup with h | ⟨Z, h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨Z, h⟩
    have lX : lower (.map X) = .map (rmDyn X) := by simp [lower]
    rw [lX]
    rcases put_gradual_cases gX (m := m) (by omega) hk hD with ⟨hmo, onlyS⟩ | ⟨hb, nS⟩
    rotate_left
    · exact ⟨_, hb, ⟨fun h => absurd rfl h, fun ⟨h, _⟩ => absurd h nS⟩, fun R e => by cases e⟩
    have gG : GC (level t (n + 1)) (.map (dynG X)) :=
      Or.inr ⟨_, upper (.map X), rfl, by simp [dynG, mapLookup, upper], gX.up_tc,
        by simp only [dynG, rmDyn_cons_dyn]; exact descrC_nil, fun q h => by
          have := (denD_rmDyn _ q).mpr h
          simp [dynG, rmDyn, denD_map, mapLookup, Elixir.STTDescrProofsTest.dn_none] at this⟩
    have hDG : mapLookup (dynG X) (.atom "dynamic") = some (upper (.map X)) := by
      simp [dynG, mapLookup, upper]
    have rG : rmDyn (dynG X) = [] := by simp [dynG, rmDyn]
    rw [put_gradual_value_g hk hD hmo]
    obtain ⟨res, run, iff, sem⟩ := gput_sem_g gG hDG hx sx hP (hmono Dv) hNa hm
    rw [rG] at iff sem
    refine ⟨res, run, iff.trans ⟨fun h => ⟨onlyS, h.2⟩, fun h => ⟨fun q hq => ?_, h.2⟩⟩, fun R e => ?_⟩
    · simp [denD_map, mapLookup, dn_none] at hq
    obtain ⟨g, o, l, u⟩ := sem R e
    refine ⟨g, o, fun w => (l w).trans ⟨fun ⟨⟨u, hu⟩, _⟩ => ?_, fun h => absurd h.1 notS⟩, u⟩
    simp [MT, mapLookup] at hu

end

section
variable {t : Term} {n : Nat}


theorem put_shape {m : Nat} {X : List (Term × Term)} {key v res : Term}
    (h : Elixir.Module.Types.Descr.«map_put/3» (D m) (.map X) key v = .ok res) :
    res = .atom "badmap" ∨ ∃ R, res = .tuple #[.atom "ok", R] := by
  unfold Elixir.Module.Types.Descr.«map_put/3» Elixir.Module.Types.Descr.«map_put_shared/3» at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩)

/-- Putting less precise values into less precise maps is less precise. -/
theorem put_prec {X : List (Term × Term)} {a₂ v v₂ : Term} (gX : GC (level t (n + 1)) (.map X))
    (g₂ : GC (level t (n + 1)) a₂) (gv : GC (level t n) v) (gv₂ : GC (level t n) v₂)
    (dup : DE (level t n).E (upper v)) (dup₂ : DE (level t n).E (upper v₂)) {key s neg : Term}
    {P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop} {m : Nat}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s) (hP : DnfPuts s neg P)
    (hmono : ∀ x₁ x₂ (M₁ M₂ : MW (level t (n + 1)).V → Prop), (∀ u, M₁ u → M₂ u) →
      (∀ y, (level t (n + 1)).den x₁ y → (level t (n + 1)).den x₂ y) → ∀ w,
      P (level t (n + 1)).den M₁ x₁ w → P (level t (n + 1)).den M₂ x₂ w)
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) (hm : (level t (n + 1)).K + 30 ≤ m)
    (lo : ∀ q : PN t (n + 1), denD a₂ q → denD (.map X) q)
    (up : ∀ q : PN t (n + 1), denD (upper (.map X)) q → denD (upper a₂) q)
    (lov : ∀ y : PN t n, denD v₂ y → denD v y) (upv : ∀ y : PN t n, denD (upper v) y → denD (upper v₂) y)
    (kd : upper v₂ = v₂ → upper v = v) {R : Term}
    (run : Elixir.Module.Types.Descr.«map_put/3» (D m) (.map X) key v = .ok (.tuple #[.atom "ok", R])) :
    ∃ R₂, Elixir.Module.Types.Descr.«map_put/3» (D m) a₂ key v₂ = .ok (.tuple #[.atom "ok", R₂]) ∧
      «precise?/2» (D m) R R₂ = .ok (.atom "true") := by
  have hm' : ∀ x M₁ M₂, (∀ u, M₁ u → M₂ u) → ∀ w, P (level t (n + 1)).den M₁ x w → P (level t (n + 1)).den M₂ x w :=
    fun x M₁ M₂ h w => hmono x x M₁ M₂ h (fun _ h => h) w
  obtain ⟨r, run', iffA, semA⟩ := put_all_g gX gv dup hk hP hm' hNa hm
  rw [run] at run'; cases run'
  obtain ⟨onlyA, neA⟩ := iffA.mp (by simp)
  have lo' : ∀ q : PN t (n + 1), denD (lower a₂) q → denD (lower (.map X)) q := fun q h =>
    (denD_lower _ _).mpr (lo q ((denD_lower _ _).mp h))
  obtain ⟨X₂, rfl⟩ : ∃ X₂, a₂ = .map X₂ := by
    rcases g₂.shape with rfl | ⟨X₂, rfl⟩
    · have := onlyA bitPt (lo' bitPt (by simp [lower, denD_term]))
      simp [bitPt] at this
    · exact ⟨X₂, rfl⟩
  have muA : ∀ w, MT t (n + 1) (dynL (upper (.map X))) w → MT t (n + 1) (dynL (upper (.map X₂))) w := fun w h =>
    (mt_dynL2 g₂.up_tc w).mpr (up _ ((mt_dynL2 gX.up_tc w).mp h))
  have msB : ∀ w, MT t (n + 1) (rmDyn X₂) w → MT t (n + 1) (rmDyn X) w := fun w h =>
    (denD_mpt w).mp ((denD_rmDyn X _).mpr (lo _ ((denD_rmDyn X₂ _).mp ((denD_mpt w).mpr h))))
  obtain ⟨r₂, run₂, iffB, semB⟩ := put_all_g g₂ gv₂ dup₂ hk hP hm' hNa hm
  have okB : r₂ ≠ .atom "badmap" := iffB.mpr ⟨fun q h => onlyA q (lo' q h), let ⟨w, hw⟩ := neA; ⟨w, muA w hw⟩⟩
  obtain ⟨R₂, rfl⟩ : ∃ R₂, r₂ = .tuple #[.atom "ok", R₂] := (put_shape run₂).resolve_left okB
  obtain ⟨gR, oR, lR, uR⟩ := semA R rfl
  obtain ⟨gR₂, oR₂, lR₂, uR₂⟩ := semB R₂ rfl
  refine ⟨R₂, run₂, precise_of (n := n + 1) (by omega) gR gR₂ ?_ ?_⟩
  · refine via_mpt gR₂.shape gR.shape (fun q h => oR₂ q (GC.inv gR₂ q h)) fun w h => ?_
    obtain ⟨e₂, ⟨u, hu⟩, h⟩ := (lR₂ w).mp h
    have e := kd e₂
    have dv₂ : DE (level t n).E v₂ := e₂ ▸ dup₂
    have dv : DE (level t n).E v := e ▸ dup
    exact (lR w).mpr ⟨e, ⟨u, msB u hu⟩, hmono v₂ v _ _ msB
      (fun y hy => (den_succ dv y).mpr (lov y ((den_succ dv₂ y).mp hy))) w h⟩
  · refine via_mpt (Or.imp id (fun ⟨Y, e, _⟩ => ⟨Y, e⟩) gR.up_tc) (Or.imp id (fun ⟨Y, e, _⟩ => ⟨Y, e⟩) gR₂.up_tc)
      oR fun w h => ?_
    obtain ⟨⟨u, hu⟩, h⟩ := (uR w).mp h
    exact (uR₂ w).mpr ⟨⟨u, muA u hu⟩, hmono _ _ _ _ muA
      (fun y hy => (den_succ dup₂ y).mpr (upv y ((den_succ dup y).mp hy))) w h⟩

end


section
variable {t : Term} {n : Nat}

/-- Putting at keys whose puts are among those of other keys gives a subtype. -/
theorem put_sub {X : List (Term × Term)} {v : Term} (gX : GC (level t (n + 1)) (.map X)) (gv : GC (level t n) v)
    (dup : DE (level t n).E (upper v)) {k₁ k₂ s₁ s₂ neg₁ neg₂ : Term}
    {P₁ P₂ : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop} {m : Nat}
    (hk₁ : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k₁ = .ok s₁) (hP₁ : DnfPuts s₁ neg₁ P₁)
    (hmono₁ : ∀ x (M₁ M₂ : MW (level t (n + 1)).V → Prop), (∀ u, M₁ u → M₂ u) → ∀ w,
      P₁ (level t (n + 1)).den M₁ x w → P₁ (level t (n + 1)).den M₂ x w)
    (hNa₁ : ∀ N, neg₁ = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    (hk₂ : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k₂ = .ok s₂) (hP₂ : DnfPuts s₂ neg₂ P₂)
    (hmono₂ : ∀ x (M₁ M₂ : MW (level t (n + 1)).V → Prop), (∀ u, M₁ u → M₂ u) → ∀ w,
      P₂ (level t (n + 1)).den M₁ x w → P₂ (level t (n + 1)).den M₂ x w)
    (hNa₂ : ∀ N, neg₂ = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    (h12 : ∀ x (M : MW (level t (n + 1)).V → Prop) w, P₁ (level t (n + 1)).den M x w → P₂ (level t (n + 1)).den M x w)
    (hm : (level t (n + 1)).K + 30 ≤ m) {R : Term}
    (run : Elixir.Module.Types.Descr.«map_put/3» (D m) (.map X) k₁ v = .ok (.tuple #[.atom "ok", R])) :
    ∃ R₂, Elixir.Module.Types.Descr.«map_put/3» (D m) (.map X) k₂ v = .ok (.tuple #[.atom "ok", R₂]) ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) R R₂ = .ok (.atom "true") := by
  obtain ⟨r, run', iff₁, sem₁⟩ := put_all_g gX gv dup hk₁ hP₁ hmono₁ hNa₁ hm
  rw [run] at run'; cases run'
  obtain ⟨r₂, run₂, iff₂, sem₂⟩ := put_all_g gX gv dup hk₂ hP₂ hmono₂ hNa₂ hm
  obtain ⟨R₂, rfl⟩ : ∃ R₂, r₂ = .tuple #[.atom "ok", R₂] :=
    (put_shape run₂).resolve_left (iff₂.mpr (iff₁.mp (by simp)))
  obtain ⟨gR, oR, lR, uR⟩ := sem₁ R rfl
  obtain ⟨gR₂, oR₂, lR₂, uR₂⟩ := sem₂ R₂ rfl
  refine ⟨R₂, run₂, gc_sub gR gR₂ (by omega) ?_ ?_⟩
  · refine via_mpt gR.shape gR₂.shape (fun q h => oR q (GC.inv gR q h)) fun w h => ?_
    obtain ⟨e, ne, h⟩ := (lR w).mp h
    exact (lR₂ w).mpr ⟨e, ne, h12 _ _ w h⟩
  · refine via_mpt (Or.imp id (fun ⟨Y, e, _⟩ => ⟨Y, e⟩) gR.up_tc) (Or.imp id (fun ⟨Y, e, _⟩ => ⟨Y, e⟩) gR₂.up_tc)
      oR fun w h => ?_
    obtain ⟨ne, h⟩ := (uR w).mp h
    exact (uR₂ w).mpr ⟨ne, h12 _ _ w h⟩

end

/-- List difference of atoms keeps atoms of the first list, and all of those not in the second. -/
theorem minus_atoms (ks B : List String) : ∃ ks' : List String,
    Erlang.erlang.«--/2» (Term.list (ks.map Term.atom)) (Term.list (B.map Term.atom)) = .ok (Term.list (ks'.map Term.atom)) ∧
    (∀ s ∈ ks', s ∈ ks) ∧ ∀ s ∈ ks, s ∉ B → s ∈ ks' := by
  have step : ∀ (B : List String) (L : List String), ∃ L' : List String,
      List.foldl (fun acc y => List.eraseP (fun x => decide (compareExact (x.fuel y) x y = .eq)) acc)
        (L.map Term.atom) (B.map Term.atom) = L'.map Term.atom ∧
      (∀ s ∈ L', s ∈ L) ∧ ∀ s ∈ L, s ∉ B → s ∈ L' := by
    intro B
    induction B with
    | nil => intro L; exact ⟨L, rfl, fun _ h => h, fun _ h _ => h⟩
    | cons b B ih =>
      intro L
      have e : List.eraseP (fun x => decide (compareExact (x.fuel (.atom b)) x (.atom b) = .eq)) (L.map Term.atom) =
          (L.eraseP (fun s => decide (s = b))).map Term.atom := by
        rw [List.eraseP_map]
        simp [Function.comp_def, compareExact_eq_atom]
      obtain ⟨L', e', s₁, s₂⟩ := ih (L.eraseP (fun s => decide (s = b)))
      refine ⟨L', ?_, fun s ms => List.mem_of_mem_eraseP (s₁ s ms), fun s ms nb => s₂ s ?_ fun m => nb (List.mem_cons_of_mem _ m)⟩
      · simp only [List.map_cons, List.foldl_cons]; rw [e]; exact e'
      · have nb' : ¬decide (s = b) = Bool.true := by simpa using fun h : s = b => nb (h ▸ List.mem_cons_self)
        exact (List.mem_eraseP_of_neg (p := fun x => decide (x = b)) (a := s) nb').mpr ms
  obtain ⟨ks', e, s₁, s₂⟩ := step B ks
  exact ⟨ks', by simp [Erlang.erlang.«--/2», Term.properList?_list, e], s₁, s₂⟩


section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `map_update_static_dnf/6` for a constant, asking for the old values: when it succeeds, the old values are the values
at the keys. -/
theorem dnf_val_g (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (fld : Term) (md : String)
    (hmd : md = "force" ∨ md = "keep" ∨ md = "reject") (bdd : Term)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (rk Os : List String)
    (neg : Term) (Ds Do : List String) (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (R : List String)
    (st : Term) (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) neg bdd = .ok (Term.list (R.map Term.atom)))
    (hk : ∀ (bd : Bool) a r, Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 5)) (Term.list lines) (.atom a)
      (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (boolAtom bd) (.atom "true") = .ok r →
      ∃ bdds F, r = .tuple #[bdds, F] ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o)
    (r : Term)
    (h : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
      (.tuple #[Term.list (rk.map Term.atom), Term.list (Os.map Term.atom), neg, Term.list (Ds.map Term.atom),
        Term.list (Do.map Term.atom)]) (.tuple #[.tuple #[.atom "constant", fld], .atom md])
      (.atom "true") st = .ok r) :
    ∃ T Y er f, r = .tuple #[T, Y, er, f] ∧ E T ∧
      ∀ x, den T x ↔ (∃ s, (s ∈ Ds ∨ s ∈ Do) ∧ ∃ L ∈ lines, LineTag den L s x) ∨
        ∃ a, (a ∈ rk ∨ a ∈ Os ∨ a ∈ R) ∧ ∃ L ∈ lines, LongM den L a (some x) := by
  classical
  obtain ⟨R1, m₀, R1s, R1c⟩ := minus_atoms R Os
  obtain ⟨R2, m₁, R2s, R2c⟩ := minus_atoms R1 rk
  have m₂ : Erlang.erlang.«++/2» (Term.list (R2.map Term.atom)) (Term.list (Os.map Term.atom)) =
      .ok (Term.list (R2.map Term.atom ++ Os.map Term.atom)) := by
    exact append_list (R2.map Term.atom) (Os.map Term.atom)
  have m₃ : Erlang.erlang.«++/2» (Term.list (Ds.map Term.atom)) (Term.list (Do.map Term.atom)) =
      .ok (Term.list (Ds.map Term.atom ++ Do.map Term.atom)) := by
    exact append_list (Ds.map Term.atom) (Do.map Term.atom)
  obtain ⟨c, hc⟩ := any_named_ok ef (n := n) (by omega) lines hl (rk ++ (R2 ++ Os))
  have hcb : (D (n + 5)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[Term.list lines, Term.list (R2.map Term.atom ++ Os.map Term.atom), Term.list (rk.map Term.atom)]) #[] = .ok (boolAtom c) := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simpa [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3», append_list] using hc
  obtain ⟨f₁, val₁, mis₁, T₁, r₁, hT₁, sT₁, -, mD₁⟩ := upd_domains ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ ⟨c, hcb⟩ Ds ef.none
  obtain ⟨errs, rE⟩ := domain_errors_ok (n + 5) mis₁ fun d md => by
    obtain ⟨s, ms, rfl⟩ := mD₁ d md; exact ⟨s, hDs s ms, rfl⟩
  have r₁' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Ds.map Term.atom)) (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, Term.list (R2.map Term.atom ++ Os.map Term.atom),
          Term.list (rk.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₁, Term.list val₁, Term.list mis₁, T₁]) := r₁
  obtain ⟨f₂, val₂, mis₂, T₂, r₂, hT₂, sT₂, -, -⟩ := upd_domains ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ ⟨c, hcb⟩ Do hT₁
  have r₂' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Do.map Term.atom)) T₁ (.atom "true") (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, Term.list (R2.map Term.atom ++ Os.map Term.atom),
          Term.list (rk.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₂, Term.list val₂, Term.list mis₂, T₂]) := r₂
  have rE' : Erlang.lists.«map/2» (D (n + 6))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list mis₁) =
      .ok (Term.list errs) := rE
  have mv : Erlang.erlang.«++/2» (Term.list val₁) (Term.list val₂) = .ok (Term.list (val₁ ++ val₂)) :=
    append_list val₁ val₂
  have sem : ∀ T' T'' : Term, (∀ x, den T' x ↔ den T₂ x ∨ ∃ a ∈ rk, ∃ L ∈ lines, LongM den L a (some x)) →
      (∀ x, den T'' x ↔ den T' x ∨ ∃ a ∈ R2 ++ Os, ∃ L ∈ lines, LongM den L a (some x)) →
      ∀ x, den T'' x ↔ (∃ s, (s ∈ Ds ∨ s ∈ Do) ∧ ∃ L ∈ lines, LineTag den L s x) ∨
        ∃ a, (a ∈ rk ∨ a ∈ Os ∨ a ∈ R) ∧ ∃ L ∈ lines, LongM den L a (some x) := fun T' T'' s' s'' x => by
    rw [s'', s', sT₂, sT₁]
    simp only [ef.den_none x, false_or, List.mem_append]
    constructor
    · rintro (((⟨s, ms, hh⟩ | ⟨s, ms, hh⟩) | ⟨a, ma, hh⟩) | ⟨a, ma | ma, hh⟩)
      · exact Or.inl ⟨s, Or.inl ms, hh⟩
      · exact Or.inl ⟨s, Or.inr ms, hh⟩
      · exact Or.inr ⟨a, Or.inl ma, hh⟩
      · exact Or.inr ⟨a, Or.inr (Or.inr (R1s a (R2s a ma))), hh⟩
      · exact Or.inr ⟨a, Or.inr (Or.inl ma), hh⟩
    · rintro (⟨s, ms | ms, hh⟩ | ⟨a, ma | ma | ma, hh⟩)
      · exact Or.inl (Or.inl (Or.inl ⟨s, ms, hh⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨s, ms, hh⟩))
      · exact Or.inl (Or.inr ⟨a, ma, hh⟩)
      · exact Or.inr ⟨a, Or.inr ma, hh⟩
      · by_cases ao : a ∈ Os
        · exact Or.inr ⟨a, Or.inr ao, hh⟩
        by_cases ar : a ∈ rk
        · exact Or.inl (Or.inr ⟨a, ar, hh⟩)
        · exact Or.inr ⟨a, Or.inl (R2c a (R1c a ma ao) ar), hh⟩
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h
  rcases hmd with rfl | rfl | rfl <;>
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», hR, m₀, m₁, m₂, m₃, mv,
      r₁', r₂', rE', Lynx.Except.andAlso] at h
  all_goals
    obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨X, hX, h⟩ := bind_ok h
    have hb : X.2 = .atom "false" ∨ X.2 = .atom "true" := by
      clear h
      simp only [bind, Except.bind, Except.tryWith] at hX
      repeat' split at hX
      all_goals first | (cases hX; done) | (injection hX with hX; subst hX; simp) | skip
      all_goals done
    obtain ⟨B96, -, h⟩ := bind_ok h
    obtain ⟨r97, h97, h⟩ := bind_ok h
    obtain ⟨T', B', Er', F', rfl, hT', sT'⟩ := named_val ef (n := n + 2) (by omega) lines fld _ (by simp) _ _ _
      (hk Bool.true) rk _ _ _ _ _ hT₂ h97
    obtain ⟨bd, ebd⟩ : ∃ bd : Bool, X.2 = boolAtom bd := by
      rcases hb with hb | hb
      · exact ⟨Bool.false, hb⟩
      · exact ⟨Bool.true, hb⟩
    rw [ebd] at h
    obtain ⟨r5, h5, h⟩ := bind_ok h
    obtain ⟨T'', B'', Er'', F'', rfl, hT'', sT''⟩ := named_val ef (n := n + 2) (by omega) lines fld _ (by simp) _ _ _
      (hk bd) (R2 ++ Os) _ _ _ _ _ hT' (by simpa using h5)
    obtain ⟨u, -, h⟩ := bind_ok h
    split at h <;> (simp only [Except.ok.injEq] at h; subst h; exact ⟨T'', _, _, _, rfl, hT'', sem T' T'' sT' sT''⟩)

theorem dnf_flag_g (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (fld : Term) {md : String} (hmd : Mode md) (st : Bool)
    (bdd : Term) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (rk Os : List String)
    (neg : Term) (Ds Do : List String) (hDs : ∀ s ∈ Ds, s ∈ domainKinds) (hDo : ∀ s ∈ Do, s ∈ domainKinds)
    (R : List String)
    (hR : Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) neg bdd = .ok (Term.list (R.map Term.atom)))
    (hk : ∀ (bd : Bool) a, ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 5))
      (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", fld], .atom md]) (boolAtom bd) (.atom "true") =
        .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧ ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o)
    (r : Term)
    (h : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
      (.tuple #[Term.list (rk.map Term.atom), Term.list (Os.map Term.atom), neg, Term.list (Ds.map Term.atom),
        Term.list (Do.map Term.atom)]) (.tuple #[.tuple #[.atom "constant", fld], .atom md])
      (.atom "true") (boolAtom st) = .ok r) :
    ∃ (T Y : Term) (el : List Term) (f : Bool), r = .tuple #[T, Y, Term.list el, boolAtom f] ∧
      (md ≠ "force" → (f = Bool.true ↔ (∃ s, (s ∈ Ds ∨ s ∈ Do) ∧ ∃ L ∈ lines, ∃ x, LineTag den L s x) ∨
        ("atom" ∈ Ds ++ Do ∧ ∃ a, (a ∈ rk ∨ a ∈ Os ∨ a ∈ R) ∧ ∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∨
        ∃ a, (a ∈ rk ∨ a ∈ Os ∨ a ∈ R) ∧ (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∧
          (st = Bool.true → ¬∃ L ∈ lines, LongM den L a none))) ∧
      (md = "force" → (f = Bool.true ↔ Ds ++ Do ≠ [] ∨ rk ≠ [] ∨ Os ≠ [] ∨ R ≠ [])) := by
  classical
  obtain ⟨R1, m₀, R1s, R1c⟩ := minus_atoms R Os
  obtain ⟨R2, m₁, R2s, R2c⟩ := minus_atoms R1 rk
  have m₂ : Erlang.erlang.«++/2» (Term.list (R2.map Term.atom)) (Term.list (Os.map Term.atom)) =
      .ok (Term.list (R2.map Term.atom ++ Os.map Term.atom)) := append_list _ _
  have m₃ : Erlang.erlang.«++/2» (Term.list (Ds.map Term.atom)) (Term.list (Do.map Term.atom)) =
      .ok (Term.list (Ds.map Term.atom ++ Do.map Term.atom)) := append_list _ _
  obtain ⟨c, hc, sc⟩ := any_named_sem ef (n := n) (by omega) lines hl (rk ++ (R2 ++ Os))
  have hcb : (D (n + 5)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[Term.list lines, Term.list (R2.map Term.atom ++ Os.map Term.atom), Term.list (rk.map Term.atom)]) #[] =
        .ok (boolAtom c) := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simpa [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3», append_list] using hc
  obtain ⟨f₁, val₁, mis₁, T₁, r₁, fD₁, mD₁⟩ := upd_found ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ c hcb Ds ef.none
  obtain ⟨f₁', val₁', mis₁', T₁', r₁', hT₁, -, -, -⟩ := upd_domains ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ ⟨c, hcb⟩ Ds ef.none
  have eT : T₁' = T₁ := by
    have := r₁.symm.trans r₁'
    simp only [Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at this
    exact this.2.2.2.1.symm
  rw [eT] at hT₁
  clear r₁' eT
  obtain ⟨f₂, val₂, mis₂, T₂, r₂, fD₂, -⟩ := upd_found ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ c hcb Do hT₁
  obtain ⟨f₂', val₂', mis₂', T₂', r₂'', hT₂, -, -, -⟩ := upd_domains ef (n := n + 2) (by omega) lines
    (fun L mL => (hl L mL).1) _ ⟨c, hcb⟩ Do hT₁
  have eT₂ : T₂' = T₂ := by
    have := r₂.symm.trans r₂''
    simp only [Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at this
    exact this.2.2.2.1.symm
  rw [eT₂] at hT₂
  clear r₂'' eT₂
  -- The atoms the named keys hold: required, optional and those outside a negated set.
  have memK : ∀ a, a ∈ rk ++ (R2 ++ Os) ↔ a ∈ rk ∨ a ∈ Os ∨ a ∈ R := fun a => by
    simp only [List.mem_append]
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (R1s a (R2s a h)))
      · exact Or.inr (Or.inl h)
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · by_cases ao : a ∈ Os
        · exact Or.inr (Or.inr ao)
        by_cases ar : a ∈ rk
        · exact Or.inl ar
        · exact Or.inr (Or.inl (R2c a (R1c a h ao) ar))
  have rE' : Erlang.lists.«map/2» (D (n + 6))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list mis₁) =
      .ok (Term.list (mis₁.map bdErr)) := by
    refine map_list _ _ _ _ bdErr _ fun x mx => ?_
    obtain ⟨s, ms, rfl, -⟩ := (mD₁ x).mp mx
    obtain ⟨y, hy⟩ := domain_descr_ok (hDs s ms)
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-1-/1».pure]
    simp [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-1-/1», hy, bdErr, domDescr]
  have r₁'' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Ds.map Term.atom)) (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, Term.list (R2.map Term.atom ++ Os.map Term.atom),
          Term.list (rk.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₁, Term.list val₁, Term.list mis₁, T₁]) := r₁
  have r₂' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Do.map Term.atom)) T₁ (.atom "true") (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, Term.list (R2.map Term.atom ++ Os.map Term.atom),
          Term.list (rk.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₂, Term.list val₂, Term.list mis₂, T₂]) := r₂
  have mv : Erlang.erlang.«++/2» (Term.list val₁) (Term.list val₂) = .ok (Term.list (val₁ ++ val₂)) :=
    append_list val₁ val₂
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6» at h
  have hmd₀ := hmd
  obtain ⟨md', hmd'⟩ : ∃ m, m = md := ⟨md, rfl⟩
  rcases hmd with rfl | rfl | rfl <;>
  simp [Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», hR, m₀, m₁, m₂, m₃, mv,
      r₁'', r₂', rE', Lynx.Except.andAlso] at h
  all_goals
    obtain ⟨v44, h44, h⟩ := bind_ok h
    obtain ⟨v51, h51, h⟩ := bind_ok h
    -- The found flag the named keys start with.
    obtain ⟨f₀, rfl, ef₀, ff₀⟩ : ∃ f₀ : Bool, v51 = boolAtom f₀ ∧
        (md' ≠ "force" → (f₀ = Bool.true ↔ (f₁ || f₂) = Bool.true)) ∧
        (md' = "force" → (f₀ = Bool.true ↔ Ds ++ Do ≠ [] ∨ (f₁ || f₂) = Bool.true)) := by
      subst hmd'
      clear h hk hcb hc r₁'' r₂' rE' r₁ r₂
      have hl : (Term.list (List.map Term.atom Ds ++ List.map Term.atom Do) = Term.nil) ↔ Ds ++ Do = [] := by
        rcases Ds with _ | ⟨_, _⟩ <;> rcases Do with _ | ⟨_, _⟩ <;> simp [Term.list]
      generalize (f₁ || f₂) = b at h44 h51 ⊢
      by_cases hE : Ds ++ Do = []
      all_goals
        cases b <;> (try simp only [hl, hE] at h44) <;> (try (split at h44 <;> rename_i hq <;> simp at hq)) <;>
          simp [Lynx.Except.orElse, boolAtom] at h44 <;> subst h44 <;>
          simp [Lynx.Except.orElse, boolAtom] at h51 <;> subst h51 <;>
          first
          | exact ⟨Bool.true, rfl, by simp, by simp [hE]⟩
          | exact ⟨Bool.false, rfl, by simp, by simp [hE]⟩
    obtain ⟨X, hX, h⟩ := bind_ok h
    have hb : X.2 = .atom "false" ∨ X.2 = .atom "true" := by
      clear h
      simp only [bind, Except.bind, Except.tryWith] at hX
      repeat' split at hX
      all_goals first | (cases hX; done) | (injection hX with hX; subst hX; simp) | skip
      all_goals done
    obtain ⟨B96, -, h⟩ := bind_ok h
    obtain ⟨r97, h97, h⟩ := bind_ok h
    obtain ⟨T', B', extra, f₃, e97, hT', hx₁, hf₃⟩ := named_flag ef (n := n + 2) (by omega) lines fld hmd₀ Bool.true st
      (.atom "true") (fun a => hk Bool.true a) rk T₂ B96 (mis₁.map bdErr) f₀ hT₂
    have e₁ := h97.symm.trans e97
    cases e₁
    obtain ⟨bd, ebd⟩ : ∃ bd : Bool, X.2 = boolAtom bd := by
      rcases hb with hb | hb
      · exact ⟨Bool.false, hb⟩
      · exact ⟨Bool.true, hb⟩
    rw [ebd] at h
    obtain ⟨r5, h5, h⟩ := bind_ok h
    obtain ⟨T'', B'', extra', f₄, e5, -, -, hf₄⟩ := named_flag ef (n := n + 2) (by omega) lines fld hmd₀ Bool.false st
      (boolAtom bd) (fun a => hk bd a) (R2 ++ Os) T' B' (extra ++ mis₁.map bdErr) f₃ hT'
    have e₂ := h5.symm.trans (by simpa using e5)
    cases e₂
    obtain ⟨u, -, h⟩ := bind_ok h
    subst hmd'
    split at h <;> (simp only [Except.ok.injEq] at h; subst h)
    all_goals
      refine ⟨T'', _, _, f₄, rfl, ?_, ?_⟩
      all_goals first | (intro nf; exact absurd rfl nf) | (intro hf; simp at hf; done) | skip
    all_goals
      first
      | (intro hf
         have fD : (f₁ || f₂) = Bool.true → Ds ++ Do ≠ [] := fun h1 => by
           rcases Bool.or_eq_true _ _ ▸ h1 with h1 | h1
           · rcases fD₁.mp h1 with ⟨s, ms, -⟩ | ⟨ms, -⟩ <;> exact List.ne_nil_of_mem (List.mem_append_left _ ms)
           · rcases fD₂.mp h1 with ⟨s, ms, -⟩ | ⟨ms, -⟩ <;> exact List.ne_nil_of_mem (List.mem_append_right _ ms)
         have r2os : R2 ++ Os ≠ [] → Os ≠ [] ∨ R ≠ [] := fun h => by
           obtain ⟨a, ma⟩ := List.exists_mem_of_ne_nil _ h
           rcases List.mem_append.mp ma with m | m
           · exact Or.inr (List.ne_nil_of_mem (R1s a (R2s a m)))
           · exact Or.inl (List.ne_nil_of_mem m)
         rw [hf₄, hf₃, ff₀ hf]
         simp only [true_and]
         constructor
         · rintro (((h0 | h1) | h2 | ⟨a, ma, -⟩) | h3 | ⟨a, ma, -⟩)
           · exact Or.inl h0
           · exact Or.inl (fD h1)
           · exact Or.inr (Or.inl h2)
           · exact Or.inr (Or.inl (List.ne_nil_of_mem ma))
           · exact Or.inr (Or.inr (r2os h3))
           · exact Or.inr (Or.inr (r2os (List.ne_nil_of_mem ma)))
         · rintro (h0 | h2 | h3 | h4)
           · exact Or.inl (Or.inl (Or.inl h0))
           · exact Or.inl (Or.inr (Or.inl h2))
           · exact Or.inr (Or.inl fun e => h3 (List.append_eq_nil_iff.mp e).2)
           · obtain ⟨a, ma⟩ := List.exists_mem_of_ne_nil _ h4
             rcases List.mem_append.mp ((memK a).mpr (Or.inr (Or.inr ma))) with m | m
             · exact Or.inl (Or.inr (Or.inl (List.ne_nil_of_mem m)))
             · exact Or.inr (Or.inl (List.ne_nil_of_mem m)))
      | (intro nf
         rw [hf₄, hf₃, ef₀ nf, Bool.or_eq_true, fD₁, fD₂, sc]
         simp only [nf, false_and, false_or]
         constructor
         · rintro (((((h | ⟨ha, hc'⟩) | (h | ⟨ha, hc'⟩)) | ⟨a, ma, hh⟩) | ⟨a, ma, hh⟩))
           · obtain ⟨s, ms, h⟩ := h; exact Or.inl ⟨s, Or.inl ms, h⟩
           · obtain ⟨a, ma, h⟩ := hc'; exact Or.inr (Or.inl ⟨List.mem_append_left _ ha, a, (memK a).mp ma, h⟩)
           · obtain ⟨s, ms, h⟩ := h; exact Or.inl ⟨s, Or.inr ms, h⟩
           · obtain ⟨a, ma, h⟩ := hc'; exact Or.inr (Or.inl ⟨List.mem_append_right _ ha, a, (memK a).mp ma, h⟩)
           · exact Or.inr (Or.inr ⟨a, (memK a).mp (List.mem_append_left _ ma), hh⟩)
           · exact Or.inr (Or.inr ⟨a, (memK a).mp (List.mem_append_right _ ma), hh⟩)
         · rintro (⟨s, ms | ms, h⟩ | ⟨ha, a, ma, h⟩ | ⟨a, ma, hh⟩)
           · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨s, ms, h⟩)))
           · exact Or.inl (Or.inl (Or.inr (Or.inl ⟨s, ms, h⟩)))
           · rcases List.mem_append.mp ha with ha | ha
             · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨ha, a, (memK a).mpr ma, h⟩)))
             · exact Or.inl (Or.inl (Or.inr (Or.inr ⟨ha, a, (memK a).mpr ma, h⟩)))
           · rcases List.mem_append.mp ((memK a).mpr ma) with m | m
             · exact Or.inl (Or.inr ⟨a, m, hh⟩)
             · exact Or.inr ⟨a, m, hh⟩)

end



/-- The split of a key type of the laws as `map_split_keys_and_domains/1` returns it. -/
def gsT (rk Os : List String) (neg : Term) (Ds Do : List String) : Term :=
  .tuple #[Term.list (rk.map Term.atom), Term.list (Os.map Term.atom), neg, Term.list (Ds.map Term.atom),
    Term.list (Do.map Term.atom)]

/-- Splits of gradual key types: atoms it requires and those it may hold, the negated set, and the required and
optional kinds, with atoms either named or outside the negated set, which holds the required ones. -/
structure GSplit (rk Os : List String) (neg : Term) (Ds Do : List String) : Prop where
  ok : SplitOk [] neg ((Ds ++ Do).map Term.atom)
  os : ∀ N, neg = .map N → Os = []
  na : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s
  rk : ∀ N, neg = .map N → ∀ a ∈ rk, mapLookup N (.atom a) ≠ none

/-- The keys of a split. -/
def GKey (rk Os : List String) (neg : Term) (Ds Do : List String) (κ : MKey) : Prop :=
  (∃ a, (a ∈ rk ∨ a ∈ Os) ∧ κ = .atom a) ∨ SplitKey [] neg ((Ds ++ Do).map Term.atom) κ

theorem atoms_strs : ∀ {rs : List Term}, (∀ r ∈ rs, ∃ s, r = .atom s) → ∃ A : List String, rs = A.map Term.atom
  | [], _ => ⟨[], rfl⟩
  | r :: rs, h => by
    obtain ⟨s, rfl⟩ := h r List.mem_cons_self
    obtain ⟨A, rfl⟩ := atoms_strs fun x m => h x (List.mem_cons_of_mem _ m)
    exact ⟨s :: A, rfl⟩

theorem gform_strs {s : Term} {KP : MKey → Prop} (hs : GForm s KP) :
    ∃ rk Os neg Ds Do, s = gsT rk Os neg Ds Do ∧ GSplit rk Os neg Ds Do ∧ ∀ κ, GKey rk Os neg Ds Do κ ↔ KP κ := by
  rcases hs with ⟨Rs, Os, Ds, Ds', rfl, ok, sk⟩ | ⟨N, Ds, Ds', rfl, ok, na, sk⟩ | ⟨A, N, Ds, Ds', rfl, ok, na, hA, sk⟩
  · obtain ⟨rk, rfl⟩ := atoms_strs fun r m => ok.hrs r (List.mem_append_left _ m)
    obtain ⟨os, rfl⟩ := atoms_strs fun r m => ok.hrs r (List.mem_append_right _ m)
    obtain ⟨D₁, rfl⟩ := atoms_strs fun r m => let ⟨s, _, e⟩ := ok.hds r (List.mem_append_left _ m); ⟨s, e⟩
    obtain ⟨D₂, rfl⟩ := atoms_strs fun r m => let ⟨s, _, e⟩ := ok.hds r (List.mem_append_right _ m); ⟨s, e⟩
    refine ⟨rk, os, _, D₁, D₂, rfl, ⟨⟨by simp, ok.hneg, fun d m => ok.hds d (by simpa using m),
      by simpa using ok.hatom⟩, fun N e => (by cases e), fun N e => (by cases e), fun N e => (by cases e)⟩,
      fun κ => (Iff.trans ?_ (sk κ))⟩
    cases κ with
    | atom a => simp [GKey, SplitKey]
    | dom k i => simp [GKey, SplitKey]
  · obtain ⟨D₁, rfl⟩ := atoms_strs fun r m => let ⟨s, _, e⟩ := ok.hds r (List.mem_append_left _ m); ⟨s, e⟩
    obtain ⟨D₂, rfl⟩ := atoms_strs fun r m => let ⟨s, _, e⟩ := ok.hds r (List.mem_append_right _ m); ⟨s, e⟩
    refine ⟨[], [], _, D₁, D₂, rfl, ⟨by simpa using ok, fun _ _ => rfl, fun N' e => (by cases e; exact na),
      fun _ _ a m => (by simp at m)⟩, fun κ => (Iff.trans ?_ (sk κ))⟩
    cases κ with
    | atom a => simp [GKey, SplitKey]
    | dom k i => simp [GKey, SplitKey]
  · obtain ⟨D₁, rfl⟩ := atoms_strs fun r m => let ⟨s, _, e⟩ := ok.hds r (List.mem_append_left _ m); ⟨s, e⟩
    obtain ⟨D₂, rfl⟩ := atoms_strs fun r m => let ⟨s, _, e⟩ := ok.hds r (List.mem_append_right _ m); ⟨s, e⟩
    refine ⟨A, [], _, D₁, D₂, rfl, ⟨by simpa using ok, fun _ _ => rfl, fun N' e => (by cases e; exact na),
      fun N' e => (by cases e; exact hA)⟩, fun κ => (Iff.trans ?_ (sk κ))⟩
    cases κ with
    | atom a => simp [GKey, SplitKey]
    | dom k i => simp [GKey, SplitKey]

/-- Whether an update finds a key, from the maps of a type: when forcing, whether the split has a key; otherwise,
whether some map holds a value at a key outside the named atoms, or at a named atom when the split has all atoms
outside a set, or at a named atom every map holds on static types. -/
def FoundG {V : Type} (M : MW V → Prop) (rk Os : List String) (neg : Term) (Ds Do : List String) (md : String)
    (st : Bool) : Prop :=
  (md = "force" ∧ (Ds ++ Do ≠ [] ∨ rk ≠ [] ∨ Os ≠ [])) ∨
  (md ≠ "force" ∧ ((∃ x w, M w ∧ ∃ κ, SplitKey [] neg ((Ds ++ Do).map Term.atom) κ ∧ w κ = some x) ∨
    ("atom" ∈ Ds ++ Do ∧ ∃ a, (a ∈ rk ∨ a ∈ Os) ∧ ∃ w x, M w ∧ w (.atom a) = some x) ∨
    ∃ a, (a ∈ rk ∨ a ∈ Os) ∧ (∃ w x, M w ∧ w (.atom a) = some x) ∧
      (st = Bool.true → ∀ w, M w → w (.atom a) ≠ none)))


section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `map_update_static_dnf/6` updating a non-empty static value at the split of a gradual key, asking for the old
values: the old values are those the maps hold at the keys, and the found flag is `FoundG` of the maps. -/
theorem dnf_gvf (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v) (vne : ∃ x, den v x)
    {b : Term} (fb : MField E b) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (sl : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {rk Os : List String} {neg : Term}
    {Ds Do : List String} (gs : GSplit rk Os neg Ds Do) {md : String} (hmd : Mode md) (st : Bool) {r : Term}
    (h : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list lines) (gsT rk Os neg Ds Do)
      (cOp v Bool.false md) (.atom "true") (boolAtom st) = .ok r) :
    ∃ T Y el f, r = .tuple #[T, Y, Term.list el, boolAtom f] ∧ E T ∧
      (∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, GKey rk Os neg Ds Do κ ∧ w κ = some x) ∧
      (f = Bool.true ↔ FoundG (fun u => denMF E den b u = Bool.true) rk Os neg Ds Do md st) := by
  have hD : ∀ s ∈ Ds ++ Do, s ∈ domainKinds := fun s ms => by
    obtain ⟨s', ms', e⟩ := gs.ok.hds _ (List.mem_map_of_mem ms); cases e; exact ms'
  have hk : ∀ (bd : Bool) a, ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5»
      (D (n + 5)) (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", .tuple #[v, boolAtom Bool.false]],
        .atom md]) (boolAtom bd) (.atom "true") = .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧
      ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o := fun bd a => by
    rcases hmd with rfl | rfl | rfl
    · exact hk_force ef (n := n + 2) (by omega) hv lines hl bd a
    · exact hk_val ef (n := n + 2) (by omega) hv vne Bool.true lines hl bd a
    · exact hk_val ef (n := n + 2) (by omega) hv vne Bool.false lines hl bd a
  obtain ⟨R, rR, hR, swR⟩ := neg_keys_split ef fb (n + 5) gs.ok
  obtain ⟨R', rfl⟩ := atoms_strs fun r mr => let ⟨s, e, _⟩ := hR r mr; ⟨s, e⟩
  obtain ⟨T, Y, er, f, rfl, hT, sT⟩ := dnf_val_g ef hn (.tuple #[v, boolAtom Bool.false]) md hmd b lines hl rk Os neg
    Ds Do (fun s ms => hD s (List.mem_append_left _ ms)) R' (boolAtom st) rR
    (fun bd a r hr => by
      obtain ⟨ba, F, e, hF, sF⟩ := hk bd a
      rw [e] at hr; cases hr; exact ⟨_, F, rfl, hF, sF⟩) r h
  obtain ⟨T', Y', el, f', e, nf, ff⟩ := dnf_flag_g ef hn (.tuple #[v, boolAtom Bool.false]) hmd st b lines hl rk Os
    neg Ds Do (fun s ms => hD s (List.mem_append_left _ ms)) (fun s ms => hD s (List.mem_append_right _ ms)) R' rR
    hk _ h
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  have pe := fun x => pieces_sem ef lines hl sl gs.ok hR swR x
  have lm := fun a o => longM_iff (E := E) (den := den) sl a o
  -- An atom outside the negated set means the split holds the atom kind.
  have rAt : ∀ a ∈ R', "atom" ∈ Ds ++ Do := fun a ma => by
    obtain ⟨s, e, N, eN, -⟩ := hR _ (List.mem_map_of_mem ma)
    obtain ⟨s', ms', e'⟩ := List.mem_map.mp (gs.ok.hatom.mpr ⟨N, eN⟩)
    cases e'; exact ms'
  have gk : ∀ x, (∃ w, denMF E den b w = Bool.true ∧ ∃ κ, GKey rk Os neg Ds Do κ ∧ w κ = some x) ↔
      (∃ a, (a ∈ rk ∨ a ∈ Os) ∧ ∃ L ∈ lines, LongM den L a (some x)) ∨
        ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, SplitKey [] neg ((Ds ++ Do).map Term.atom) κ ∧ w κ = some x := by
    intro x
    constructor
    · rintro ⟨w, hw, κ, ⟨a, ma, rfl⟩ | hκ, e⟩
      · exact Or.inl ⟨a, ma, (lm a _).mpr ⟨w, hw, e⟩⟩
      · exact Or.inr ⟨w, hw, κ, hκ, e⟩
    · rintro (⟨a, ma, h⟩ | ⟨w, hw, κ, hκ, e⟩)
      · obtain ⟨w, hw, e⟩ := (lm a _).mp h
        exact ⟨w, hw, _, Or.inl ⟨a, ma, rfl⟩, e⟩
      · exact ⟨w, hw, κ, Or.inr hκ, e⟩
  have pe' : ∀ x, ((∃ s ∈ R', ∃ L ∈ lines, LongM den L s (some x)) ∨
      ∃ kind, (kind ∈ Ds ∨ kind ∈ Do) ∧ ∃ L ∈ lines, LineTag den L kind x) ↔
      ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, SplitKey [] neg ((Ds ++ Do).map Term.atom) κ ∧ w κ = some x := by
    intro x
    rw [← pe x]
    simp only [List.mem_map, Term.atom.injEq, exists_eq_right, List.not_mem_nil, false_and, exists_false, false_or,
      List.mem_append]
  refine ⟨T, Y, el, f', rfl, hT, fun x => (sT x).trans ?_, ?_⟩
  · rw [gk, ← pe']
    constructor
    · rintro (⟨s, ms, hh⟩ | ⟨a, (ma | ma | ma), hh⟩)
      · exact Or.inr (Or.inr ⟨s, ms, hh⟩)
      · exact Or.inl ⟨a, Or.inl ma, hh⟩
      · exact Or.inl ⟨a, Or.inr ma, hh⟩
      · exact Or.inr (Or.inl ⟨a, ma, hh⟩)
    · rintro (⟨a, ma, hh⟩ | ⟨a, ma, hh⟩ | ⟨s, ms, hh⟩)
      · exact Or.inr ⟨a, ma.imp_right Or.inl, hh⟩
      · exact Or.inr ⟨a, Or.inr (Or.inr ma), hh⟩
      · exact Or.inl ⟨s, ms, hh⟩
  · by_cases hf : md = "force"
    · subst hf
      rw [ff rfl]
      simp only [FoundG, true_and, ne_eq, not_true_eq_false, false_and, or_false]
      constructor
      · rintro (h | h | h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · obtain ⟨a, ma⟩ := List.exists_mem_of_ne_nil _ h
          exact Or.inl (List.ne_nil_of_mem (rAt a ma))
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
    · rw [nf hf]
      simp only [FoundG, hf, false_and, false_or, ne_eq, not_false_eq_true, true_and]
      have none_iff : ∀ a, (¬∃ L ∈ lines, LongM den L a none) ↔
          ∀ w, denMF E den b w = Bool.true → w (.atom a) ≠ none := fun a => by
        rw [lm a none]; simp
      have some_iff : ∀ a, (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ↔
          ∃ w x, denMF E den b w = Bool.true ∧ w (.atom a) = some x := fun a => by
        constructor
        · rintro ⟨L, mL, x, h⟩
          obtain ⟨w, hw, e⟩ := (lm a _).mp ⟨L, mL, h⟩; exact ⟨w, x, hw, e⟩
        · rintro ⟨w, x, hw, e⟩
          obtain ⟨L, mL, h⟩ := (lm a _).mpr ⟨w, hw, e⟩; exact ⟨L, mL, x, h⟩
      have s1 : (∃ x w, denMF E den b w = Bool.true ∧ ∃ κ, SplitKey [] neg ((Ds ++ Do).map Term.atom) κ ∧
          w κ = some x) ↔ (∃ a ∈ R', ∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∨
          ∃ s, (s ∈ Ds ∨ s ∈ Do) ∧ ∃ L ∈ lines, ∃ x, LineTag den L s x := by
        constructor
        · rintro ⟨x, hx⟩
          rcases (pe' x).mpr hx with ⟨a, ma, L, mL, h⟩ | ⟨s, ms, L, mL, h⟩
          · exact Or.inl ⟨a, ma, L, mL, x, h⟩
          · exact Or.inr ⟨s, ms, L, mL, x, h⟩
        · rintro (⟨a, ma, L, mL, x, h⟩ | ⟨s, ms, L, mL, x, h⟩)
          · exact ⟨x, (pe' x).mp (Or.inl ⟨a, ma, L, mL, h⟩)⟩
          · exact ⟨x, (pe' x).mp (Or.inr ⟨s, ms, L, mL, h⟩)⟩
      rw [s1]
      constructor
      · rintro (h | ⟨hat, a, (ma | ma | ma), h⟩ | ⟨a, (ma | ma | ma), h, hn⟩)
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inl ⟨hat, a, Or.inl ma, (some_iff a).mp h⟩)
        · exact Or.inr (Or.inl ⟨hat, a, Or.inr ma, (some_iff a).mp h⟩)
        · exact Or.inl (Or.inl ⟨a, ma, h⟩)
        · exact Or.inr (Or.inr ⟨a, Or.inl ma, (some_iff a).mp h, fun e => (none_iff a).mp (hn e)⟩)
        · exact Or.inr (Or.inr ⟨a, Or.inr ma, (some_iff a).mp h, fun e => (none_iff a).mp (hn e)⟩)
        · exact Or.inl (Or.inl ⟨a, ma, h⟩)
      · rintro ((⟨a, ma, h⟩ | h) | ⟨hat, a, ma, h⟩ | ⟨a, ma, h, hn⟩)
        · exact Or.inr (Or.inl ⟨rAt a ma, a, Or.inr (Or.inr ma), h⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨hat, a, ma.imp_right Or.inl, (some_iff a).mpr h⟩)
        · exact Or.inr (Or.inr ⟨a, ma.imp_right Or.inl, (some_iff a).mpr h, fun e => (none_iff a).mpr (hn e)⟩)

end


section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `map_update_named_keys/8` asking for the old values succeeds when each key gives maps of fields and an old field. -/
theorem named_fold_ok (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) (lines : List Term) {nt : Term}
    {nopt : Bool} {md : String} (hmd : Mode md) (req st bd : Bool)
    (pk : ∀ a, ∃ (ba : List Term) (t : Term) (o : Bool), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3))
      (Term.list lines) (.atom a) (cOp nt nopt md) (boolAtom bd) (.atom "true") =
        .ok (.tuple #[Term.list ba, .tuple #[t, boolAtom o]]) ∧ E t ∧ ∀ b ∈ ba, MField E b) :
    ∀ (ks : List String) (B : List Term) (f : Bool) (T Er : Term), E T → (∀ b ∈ B, MField E b) →
      ∃ (B' : List Term) (f' : Bool) (T' Er' : Term),
        Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (n + 4)) (.tuple #[T, Term.list B, Er, boolAtom f])
          (Term.list lines) (Term.list (ks.map Term.atom)) (cOp nt nopt md) (boolAtom req) (boolAtom st)
          (.atom "true") (boolAtom bd) = .ok (.tuple #[T', Term.list B', Er', boolAtom f']) ∧ E T' ∧
        ∀ b ∈ B', MField E b := by
  have loop : ∀ (ks : List String) (B : List Term) (f : Bool) (T Er : Term), E T → (∀ b ∈ B, MField E b) →
      ∃ (B' : List Term) (f' : Bool) (T' Er' : Term),
        Erlang.lists.«foldl_1/3» (D (n + 4))
          (.function false "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
            #[Term.list lines, cOp nt nopt md, boolAtom req, boolAtom st, boolAtom bd, .atom "true",
              boolAtom (decide (md = "force"))])
          (.tuple #[T, Term.list B, Er, boolAtom f]) (Term.list (ks.map Term.atom)) =
          .ok (.tuple #[T', Term.list B', Er', boolAtom f']) ∧ E T' ∧ ∀ b ∈ B', MField E b := by
    intro ks
    induction ks with
    | nil =>
      intro B f T Er hT fB
      exact ⟨B, f, T, Er, by simp [Erlang.lists.«foldl_1/3», Term.list], hT, fB⟩
    | cons a rest ih =>
      intro B f T Er hT fB
      obtain ⟨ba, t, o, rb, ht, fba⟩ := pk a
      obtain ⟨e, re, se⟩ := ef.empty1 (m := n + 3) (by omega) ht
      obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] ht hT (m := n + 3) (by omega)
      obtain ⟨f₁, T₁, Er₁, step, hT₁⟩ : ∃ (f₁ : Bool) (T₁ Er₁ : Term),
          (D (n + 4)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_named_keys/8-fun-0-" 2
            #[Term.list lines, cOp nt nopt md, boolAtom req, boolAtom st, boolAtom bd, .atom "true",
              boolAtom (decide (md = "force"))]) #[.atom a, .tuple #[T, Term.list B, Er, boolAtom f]] =
            .ok (.tuple #[T₁, Term.list (ba ++ B), Er₁, boolAtom f₁]) ∧ E T₁ := by
        simp only [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
          Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9»]
        rw [rb]
        rcases hmd with rfl | rfl | rfl <;> cases e <;> cases o <;> cases req <;> cases f <;> cases st <;>
          simp [re, Lynx.Term.isMember, Elixir.Module.Types.Descr.«opt_union/2», ru, boolAtom, Lynx.Except.andAlso,
            Lynx.Except.orElse, Erlang.erlang.«not/1», append_list] <;>
          first
          | exact ⟨_, _, _, ⟨rfl, rfl, rfl, rfl⟩, hu⟩
          | exact ⟨_, _, _, ⟨rfl, rfl, rfl, rfl⟩, hT⟩
          | exact ⟨_, _, _, rfl, hu⟩
          | exact ⟨_, _, _, rfl, hT⟩
          | exact hu
          | exact hT
      obtain ⟨B', f', T', Er', r₁, hT', fB'⟩ := ih (ba ++ B) f₁ T₁ Er₁ hT₁ fun b mb => by
        rcases List.mem_append.mp mb with mb | mb
        · exact fba b mb
        · exact fB b mb
      refine ⟨B', f', T', Er', ?_, hT', fB'⟩
      rw [Erlang.lists.«foldl_1/3».eq_def]
      simp only [Term.list, List.map] at r₁ ⊢
      simp at step
      simp [step, r₁]
  intro ks B f T Er hT fB
  obtain ⟨B', f', T', Er', r₁, hT', fB'⟩ := loop ks B f T Er hT fB
  refine ⟨B', f', T', Er', ?_, hT', fB'⟩
  rcases hmd with rfl | rfl | rfl
  all_goals
    simp [Elixir.Module.Types.Descr.«map_update_named_keys/8», Erlang.erlang.«element/2», Erlang.erlang.«==/2»,
      Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Lynx.Except.orElse, boolAtom]
    rcases ks with _ | ⟨k, t⟩
    · simp [Term.list, Erlang.lists.«foldl_1/3»] at r₁ ⊢
      simpa [boolAtom] using r₁
    · simp only [Term.list, List.map] at r₁ ⊢; rw [Erlang.lists.«foldl_1/3».eq_def] at r₁; simpa [boolAtom] using r₁

/-- Each key of a constant update gives maps of fields and an old field. -/
theorem pk_val (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v) (vne : ∃ x, den v x)
    {md : String} (hmd : Mode md) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (bd : Bool)
    (a : String) : ∃ (ba : List Term) (t : Term) (o : Bool), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3))
      (Term.list lines) (.atom a) (cOp v Bool.false md) (boolAtom bd) (.atom "true") =
        .ok (.tuple #[Term.list ba, .tuple #[t, boolAtom o]]) ∧ E t ∧ ∀ b ∈ ba, MField E b := by
  obtain ⟨F, rF, hF, -⟩ := mdnf_fetch ef hn a lines hl
  cases bd
  · obtain ⟨t, o, rfl, ht⟩ := hF
    exact ⟨[], t, o, by simp [Elixir.Module.Types.Descr.«map_update_named_key/5», boolAtom, Lynx.Term.isMember,
      Term.list, rF], ht, by simp⟩
  · rcases hmd with rfl | rfl | rfl
    · obtain ⟨ba, rba, fba, -⟩ := put_lines ef hn a (leafPut_put ef a hv) lines hl
      obtain ⟨t, o, rfl, ht⟩ := hF
      exact ⟨ba, t, o, by simpa [boolAtom, cOp] using rba Bool.true _ fun _ => rF, ht, fba⟩
    · obtain ⟨ba, F', rb, fba, hF', -⟩ := keep_lines ef hn a hv vne Bool.true lines hl (.atom "true")
      obtain ⟨t, o, rfl, ht⟩ := hF'
      exact ⟨ba, t, o, by simpa [modeT, cOp, boolAtom] using rb, ht, fba⟩
    · obtain ⟨ba, F', rb, fba, hF', -⟩ := keep_lines ef hn a hv vne Bool.false lines hl (.atom "true")
      obtain ⟨t, o, rfl, ht⟩ := hF'
      exact ⟨ba, t, o, by simpa [modeT, cOp, boolAtom] using rb, ht, fba⟩

/-- Each key of a delete gives maps of fields and an old field. -/
theorem pk_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {md : String} (hmd : Mode md)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (bd : Bool)
    (a : String) : ∃ (ba : List Term) (t : Term) (o : Bool), Elixir.Module.Types.Descr.«map_update_named_key/5» (D (n + 3))
      (Term.list lines) (.atom a) (cOp (.map []) Bool.true md) (boolAtom bd) (.atom "true") =
        .ok (.tuple #[Term.list ba, .tuple #[t, boolAtom o]]) ∧ E t ∧ ∀ b ∈ ba, MField E b := by
  obtain ⟨ba, F, rb, hF, b0, b1⟩ := del_key_sem ef hn lines hl hmd a bd
  obtain ⟨t, o, rfl, ht⟩ := hF
  refine ⟨ba, t, o, rb, ht, fun b mb => ?_⟩
  cases bd
  · rw [b0 rfl] at mb; simp at mb
  · exact (b1 rfl).1 b mb


theorem ex_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} (a : α) (hx : x = .ok a)
    (hf : ∃ r, f a = .ok r) : ∃ r, (x >>= f) = .ok r := by
  obtain ⟨r, hr⟩ := hf; exact ⟨r, by rw [hx]; exact hr⟩

theorem atom_ite_bool (b : Bool) : Term.atom (if b = Bool.true then "true" else "false") = boolAtom b := by
  cases b <;> rfl

theorem cmp_list_nil (l : List Term) :
    Term.compare ((Term.list l).fuel .nil) (Term.list l) .nil = .eq ↔ l = [] := by
  cases l with
  | nil => simp [Term.list, Term.compare_self]
  | cons a l => rw [Lynx.Term.compare_step]; simp [Lynx.Term.Compare.compareStep]

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
/-- `map_update_static_dnf/6` of a constant at the split of a gradual key, asking for the old values, succeeds on the
non-empty lines of a map field, given that each key gives maps of fields and an old field. -/
theorem dnf_ok_g (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {nt : Term} (hnt : E nt)
    (snt : nt = .atom "term" ∨ ∃ Z, nt = .map Z) (nopt : Bool) {md : String} (hmd : Mode md)
    {bdd : Term} (fbd : MField E bdd) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (sbd : ∀ w, denMF E den bdd w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w)
    {rk Os : List String} {neg : Term} {Ds Do : List String} (ok : SplitOk [] neg ((Ds ++ Do).map Term.atom))
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) (st : Bool)
    (pk : ∀ (bd : Bool) a, ∃ (ba : List Term) (t : Term) (o : Bool), Elixir.Module.Types.Descr.«map_update_named_key/5»
      (D (n + 5)) (Term.list lines) (.atom a) (cOp nt nopt md) (boolAtom bd) (.atom "true") =
        .ok (.tuple #[Term.list ba, .tuple #[t, boolAtom o]]) ∧ E t ∧ ∀ b ∈ ba, MField E b) :
    ∃ r, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
      (gsT rk Os neg Ds Do) (cOp nt nopt md) (.atom "true") (boolAtom st) = .ok r := by
  have hD : ∀ s ∈ Ds ++ Do, s ∈ domainKinds := fun s ms => by
    obtain ⟨s', ms', e⟩ := ok.hds _ (List.mem_map_of_mem ms); cases e; exact ms'
  have hDs : ∀ s ∈ Ds, s ∈ domainKinds := fun s ms => hD s (List.mem_append_left _ ms)
  have hDo : ∀ s ∈ Do, s ∈ domainKinds := fun s ms => hD s (List.mem_append_right _ ms)
  have hl' : ∀ L ∈ lines, MLine E L := fun L mL => (hl L mL).1
  obtain ⟨R, rR, hR, -⟩ := neg_keys_split ef fbd (n + 5) ok
  obtain ⟨R', rfl⟩ := atoms_strs fun r mr => let ⟨s, e, _⟩ := hR r mr; ⟨s, e⟩
  obtain ⟨R1, m₀, -, -⟩ := minus_atoms R' Os
  obtain ⟨R2, m₁, -, -⟩ := minus_atoms R1 rk
  have m₂ : Erlang.erlang.«++/2» (Term.list (R2.map Term.atom)) (Term.list (Os.map Term.atom)) =
      .ok (Term.list (R2.map Term.atom ++ Os.map Term.atom)) := append_list _ _
  have m₃ : Erlang.erlang.«++/2» (Term.list (Ds.map Term.atom)) (Term.list (Do.map Term.atom)) =
      .ok (Term.list (Ds.map Term.atom ++ Do.map Term.atom)) := append_list _ _
  obtain ⟨c, hc⟩ := any_named_ok ef (n := n) (by omega) lines hl (rk ++ (R2 ++ Os))
  have hcb : (D (n + 5)).pure (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-0-" 0
      #[Term.list lines, Term.list (R2.map Term.atom ++ Os.map Term.atom), Term.list (rk.map Term.atom)]) #[] =
        .ok (boolAtom c) := by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-0-/0».pure]
    simpa [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-0-/3», append_list] using hc
  obtain ⟨f₁, val₁, mis₁, T₁, r₁, hT₁, -, -, mD₁, vD₁, vf₁⟩ := upd_domains2 ef (n := n + 2) (by omega) lines hl' _
    ⟨c, hcb⟩ Ds ef.none
  obtain ⟨f₂, val₂, mis₂, T₂, r₂, hT₂, -, -, -, vD₂, vf₂⟩ := upd_domains2 ef (n := n + 2) (by omega) lines hl' _
    ⟨c, hcb⟩ Do hT₁
  have rE' : Erlang.lists.«map/2» (D (n + 6))
      (.function false "Elixir.Module.Types.Descr" "-map_update_static_dnf/6-fun-1-" 1 #[]) (Term.list mis₁) =
      .ok (Term.list (mis₁.map bdErr)) := by
    refine map_list _ _ _ _ bdErr _ fun x mx => ?_
    obtain ⟨s, ms, rfl⟩ := mD₁ x mx
    obtain ⟨y, hy⟩ := domain_descr_ok (hDs s ms)
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_static_dnf/6-fun-1-/1».pure]
    simp [Elixir.Module.Types.Descr.«-map_update_static_dnf/6-fun-1-/1», hy, bdErr, domDescr]
  have r₁' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Ds.map Term.atom)) (.map []) (.atom "true") (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, Term.list (R2.map Term.atom ++ Os.map Term.atom),
          Term.list (rk.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₁, Term.list val₁, Term.list mis₁, T₁]) := r₁
  have r₂' : Elixir.Module.Types.Descr.«map_update_get_domains/5» (D (n + 6)) (Term.list lines)
      (Term.list (Do.map Term.atom)) T₁ (.atom "true") (.function false "Elixir.Module.Types.Descr"
        "-map_update_static_dnf/6-fun-0-" 0 #[Term.list lines, Term.list (R2.map Term.atom ++ Os.map Term.atom),
          Term.list (rk.map Term.atom)]) =
      .ok (.tuple #[boolAtom f₂, Term.list val₂, Term.list mis₂, T₂]) := r₂
  have mv : Erlang.erlang.«++/2» (Term.list val₁) (Term.list val₂) = .ok (Term.list (val₁ ++ val₂)) :=
    append_list val₁ val₂
  -- The kinds updated: all of them unless rejecting, then those found.
  obtain ⟨Dm, eDm, hDm⟩ : ∃ Dm : List String, ((md ≠ "reject" → Dm = Ds ++ Do) ∧
      (md = "reject" → Dm.map Term.atom = val₁ ++ val₂)) ∧ ∀ s ∈ Dm, s ∈ Ds ++ Do := by
    by_cases hr : md = "reject"
    · obtain ⟨A, eA⟩ := atoms_strs (rs := val₁ ++ val₂) fun d md' => by
        rcases List.mem_append.mp md' with m | m
        · obtain ⟨s, -, rfl, -⟩ := (vD₁ d).mp m; exact ⟨s, rfl⟩
        · obtain ⟨s, -, rfl, -⟩ := (vD₂ d).mp m; exact ⟨s, rfl⟩
      refine ⟨A, ⟨fun h => absurd hr h, fun _ => eA.symm⟩, fun s ms => ?_⟩
      have : Term.atom s ∈ val₁ ++ val₂ := eA ▸ List.mem_map_of_mem ms
      rcases List.mem_append.mp this with m | m
      · obtain ⟨s', ms', e, -⟩ := (vD₁ _).mp m; cases e; exact List.mem_append_left _ ms'
      · obtain ⟨s', ms', e, -⟩ := (vD₂ _).mp m; cases e; exact List.mem_append_right _ ms'
    · exact ⟨Ds ++ Do, ⟨fun _ => rfl, fun h => absurd h hr⟩, fun s m => m⟩
  have fDm : md = "reject" → Dm ≠ [] → (f₁ || f₂) = Bool.true := fun hr ne => by
    have e := eDm.2 hr
    cases hv : val₁ with
    | cons _ _ => simp [vf₁ (by simp [hv])]
    | nil =>
      cases hv2 : val₂ with
      | cons _ _ => simp [vf₂ (by simp [hv2])]
      | nil => rw [hv, hv2] at e; cases Dm with
        | nil => exact absurd rfl ne
        | cons _ _ => simp at e
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  rcases hmd with rfl | rfl | rfl <;>
  simp [gsT, cOp, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Term.isMember, Erlang.erlang.«not/1», rR, m₀, m₁,
      m₂, m₃, mv, r₁', r₂', rE', Lynx.Except.andAlso, Erlang.erlang.«element/2»]
  · rw [show List.map Term.atom Ds ++ List.map Term.atom Do = Dm.map Term.atom by rw [eDm.1 (by decide)]; simp]
    refine ex_bind (boolAtom (decide (Dm ≠ []))) (by
      by_cases e0 : Dm = []
      · subst e0; simp [Term.list, boolAtom]
      · have e0' : List.map Term.atom Dm ≠ [] := by simpa using e0
        simp only [equal_eq_decide, decide_eq_true_eq, cmp_list_nil, e0', ↓reduceIte]
        first
        | (have := fDm rfl e0; simp [this, boolAtom, e0, Lynx.Except.orElse])
        | (cases f₁ <;> cases f₂ <;> simp [boolAtom, e0, Lynx.Except.orElse])) ?_
    rcases ok.hneg with rfl | ⟨N, rfl⟩
    · generalize (f₁ || f₂) = g
      by_cases e0 : Dm = [] <;> cases g <;> simp [e0, boolAtom, Lynx.Except.orElse]
      all_goals simp only [atom_ite_bool]
      · first
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
      · first
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
      all_goals
        have na : "atom" ∉ Dm := fun m => by
          have := ok.hatom.mp (List.mem_map_of_mem (hDm _ m)); obtain ⟨N, e⟩ := this; cases e
        obtain ⟨Ks, rKs, mKs, -, subKs, -⟩ := kinds_usort (Dm.map Term.atom) fun d md' => by
          obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md'; exact ⟨s, hD s (hDm s ms), rfl⟩
        have naK : "atom" ∉ Ks := fun m => na (by simpa using (mKs _).mp m)
        obtain ⟨R, rW, mR⟩ := widen_run_gen ef (n := n + 1) (by omega) hnt nopt (md := "force") (by simp [Mode]) Ks naK subKs lines hl'
        simp only [cOp] at rW
        simp only [rKs, rW, Lynx.Except.ok_bind]
        rcases mapsD_cases mR with ⟨rfl, -⟩ | ⟨c, neR, lc, fc, -⟩
        · simp [Term.compare_self]
          first
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
        · simp [neR, getMapKeys_single, lc, Option.toList]
          first
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
    · have keysN := setStrs_keys (hNa N rfl)
      obtain ⟨AKt, rR', -, mR'⟩ := usort_atoms (R2.map Term.atom ++ (Os.map Term.atom ++ (setStrs N).map Term.atom))
        (fun k mk => by simp only [List.mem_append, List.mem_map] at mk; rcases mk with (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩ | ⟨s, -, rfl⟩) <;> exact ⟨s, rfl⟩)
      obtain ⟨AK, rfl⟩ := atoms_strs fun r mr => by
        have := (mR' r).mp mr
        simp only [List.mem_append, List.mem_map] at this
        rcases this with (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩ | ⟨s, -, rfl⟩) <;> exact ⟨s, rfl⟩
      have dne : Dm ≠ [] := by
        rw [eDm.1 (by decide)]
        intro e
        have := ok.hatom.mpr ⟨N, rfl⟩
        rw [e] at this; simp at this
      generalize (f₁ || f₂) = g
      by_cases e0 : Dm = [] <;> cases g <;> simp [e0, boolAtom, Lynx.Except.orElse, Erlang.sets.«to_list/1»,
        Erlang.maps.«keys/1», keysN, append_list, rR']
      all_goals simp only [atom_ite_bool]
      all_goals first | exact absurd e0 dne | skip
      all_goals
        obtain ⟨Ks, rKs, -, -, subKs, -⟩ := kinds_usort (Dm.map Term.atom) fun d md' => by
          obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md'; exact ⟨s, hD s (hDm s ms), rfl⟩
        have lenK : Erlang.erlang.«length/1» (Term.list (Ks.map Term.atom)) = .ok (.integer (Ks.length : Int)) := by
          simpa using length_list (Ks.map Term.atom)
        have part := partition_atom (n + 5) Ks
        simp only [rKs, Lynx.Except.ok_bind]
        try simp only [lenK, Lynx.Except.ok_bind]
        by_cases full : (Ks.length : Int) = 12
        · simp [Lynx.Term.compare_integers, full]
          obtain ⟨_, _, res, rb, _, _, _, _, X, eX, mX⟩ := box_runG ef (n := n + 2) (by omega) lines bdd hl fbd sbd hnt
            snt nopt (md := "force") (by simp [Mode]) (R2 ++ Os) AK Ks subKs
          subst eX
          simp only [cOp, List.map_append] at rb
          simp [rb, Term.list]
          rcases mapsD_cases mX with ⟨rfl, -⟩ | ⟨c, neU, lc, fc, -⟩
          · simp [Term.compare_self]
            first
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
          · simp [neU, getMapKeys_single, lc, Option.toList]
            first
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
        · simp [Lynx.Term.compare_integers, full, part]
          obtain ⟨_, _, res, rb, _, _, _, _, X, eX, mX⟩ := box_runG ef (n := n + 2) (by omega) lines bdd hl fbd sbd hnt
            snt nopt (md := "force") (by simp [Mode]) (R2 ++ Os) AK (Ks.filter (· = "atom"))
            (fun d m => subKs d (List.mem_filter.mp m).1)
          subst eX
          simp only [cOp, List.map_append] at rb
          simp only [rb, Lynx.Except.ok_bind]
          by_cases wn : Ks.filter (· ≠ "atom") = []
          · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by simpa using wn
            simp [wn', Term.list]
            rcases mapsD_cases mX with ⟨rfl, -⟩ | ⟨c, neU, lc, fc, -⟩
            · simp [Term.compare_self]
              first
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
            · simp [neU, getMapKeys_single, lc, Option.toList]
              first
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
          · obtain ⟨W, rW, mW⟩ := widen_run_gen ef (n := n + 1) (by omega) hnt nopt (md := "force") (by simp [Mode])
              (Ks.filter (· ≠ "atom")) (fun m => by simpa using (List.mem_filter.mp m).2)
              (fun d m => subKs d (List.mem_filter.mp m).1) lines hl'
            obtain ⟨U, rU, mU⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) mX mW
            have wsCmp : ¬(Term.list ((Ks.filter (· ≠ "atom")).map Term.atom) = .nil) := by
              cases h : Ks.filter (· ≠ "atom") with
              | nil => exact absurd h wn
              | cons d ds => simp [Term.list]
            simp only [cOp] at rW
            simp at wsCmp rW
            simp [wsCmp, rW, rU]
            rcases mapsD_cases mU with ⟨rfl, -⟩ | ⟨c, neU, lc, fc, -⟩
            · simp [Term.compare_self]
              first
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
            · simp [neU, getMapKeys_single, lc, Option.toList]
              first
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
  · rw [show List.map Term.atom Ds ++ List.map Term.atom Do = Dm.map Term.atom by rw [eDm.1 (by decide)]; simp]
    refine ex_bind (boolAtom (decide (Dm ≠ []))) (by
      by_cases e0 : Dm = []
      · subst e0; simp [Term.list, boolAtom]
      · have e0' : List.map Term.atom Dm ≠ [] := by simpa using e0
        simp only [equal_eq_decide, decide_eq_true_eq, cmp_list_nil, e0', ↓reduceIte]
        first
        | (have := fDm rfl e0; simp [this, boolAtom, e0, Lynx.Except.orElse])
        | (cases f₁ <;> cases f₂ <;> simp [boolAtom, e0, Lynx.Except.orElse])) ?_
    rcases ok.hneg with rfl | ⟨N, rfl⟩
    · generalize (f₁ || f₂) = g
      by_cases e0 : Dm = [] <;> cases g <;> simp [e0, boolAtom, Lynx.Except.orElse]
      all_goals simp only [atom_ite_bool]
      · first
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
      · first
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
      all_goals
        have na : "atom" ∉ Dm := fun m => by
          have := ok.hatom.mp (List.mem_map_of_mem (hDm _ m)); obtain ⟨N, e⟩ := this; cases e
        obtain ⟨Ks, rKs, mKs, -, subKs, -⟩ := kinds_usort (Dm.map Term.atom) fun d md' => by
          obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md'; exact ⟨s, hD s (hDm s ms), rfl⟩
        have naK : "atom" ∉ Ks := fun m => na (by simpa using (mKs _).mp m)
        obtain ⟨R, rW, mR⟩ := widen_run_gen ef (n := n + 1) (by omega) hnt nopt (md := "keep") (by simp [Mode]) Ks naK subKs lines hl'
        simp only [cOp] at rW
        simp only [rKs, rW, Lynx.Except.ok_bind]
        rcases mapsD_cases mR with ⟨rfl, -⟩ | ⟨c, neR, lc, fc, -⟩
        · simp [Term.compare_self]
          first
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
        · simp [neR, getMapKeys_single, lc, Option.toList]
          first
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
    · have keysN := setStrs_keys (hNa N rfl)
      obtain ⟨AKt, rR', -, mR'⟩ := usort_atoms (R2.map Term.atom ++ (Os.map Term.atom ++ (setStrs N).map Term.atom))
        (fun k mk => by simp only [List.mem_append, List.mem_map] at mk; rcases mk with (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩ | ⟨s, -, rfl⟩) <;> exact ⟨s, rfl⟩)
      obtain ⟨AK, rfl⟩ := atoms_strs fun r mr => by
        have := (mR' r).mp mr
        simp only [List.mem_append, List.mem_map] at this
        rcases this with (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩ | ⟨s, -, rfl⟩) <;> exact ⟨s, rfl⟩
      have dne : Dm ≠ [] := by
        rw [eDm.1 (by decide)]
        intro e
        have := ok.hatom.mpr ⟨N, rfl⟩
        rw [e] at this; simp at this
      generalize (f₁ || f₂) = g
      by_cases e0 : Dm = [] <;> cases g <;> simp [e0, boolAtom, Lynx.Except.orElse, Erlang.sets.«to_list/1»,
        Erlang.maps.«keys/1», keysN, append_list, rR']
      all_goals simp only [atom_ite_bool]
      all_goals first | exact absurd e0 dne | skip
      all_goals
        obtain ⟨Ks, rKs, -, -, subKs, -⟩ := kinds_usort (Dm.map Term.atom) fun d md' => by
          obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md'; exact ⟨s, hD s (hDm s ms), rfl⟩
        have lenK : Erlang.erlang.«length/1» (Term.list (Ks.map Term.atom)) = .ok (.integer (Ks.length : Int)) := by
          simpa using length_list (Ks.map Term.atom)
        have part := partition_atom (n + 5) Ks
        simp only [rKs, Lynx.Except.ok_bind]
        try simp only [lenK, Lynx.Except.ok_bind]
        simp [part]
        obtain ⟨_, _, res, rb, _, _, _, _, X, eX, mX⟩ := box_runG ef (n := n + 2) (by omega) lines bdd hl fbd sbd hnt
          snt nopt (md := "keep") (by simp [Mode]) (R2 ++ Os) AK (Ks.filter (· = "atom"))
          (fun d m => subKs d (List.mem_filter.mp m).1)
        subst eX
        simp only [cOp, List.map_append] at rb
        simp only [rb, Lynx.Except.ok_bind]
        by_cases wn : Ks.filter (· ≠ "atom") = []
        · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by simpa using wn
          simp [wn', Term.list]
          rcases mapsD_cases mX with ⟨rfl, -⟩ | ⟨c, neU, lc, fc, -⟩
          · simp [Term.compare_self]
            first
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
          · simp [neU, getMapKeys_single, lc, Option.toList]
            first
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
        · obtain ⟨W, rW, mW⟩ := widen_run_gen ef (n := n + 1) (by omega) hnt nopt (md := "keep") (by simp [Mode])
            (Ks.filter (· ≠ "atom")) (fun m => by simpa using (List.mem_filter.mp m).2)
            (fun d m => subKs d (List.mem_filter.mp m).1) lines hl'
          obtain ⟨U, rU, mU⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) mX mW
          have wsCmp : ¬(Term.list ((Ks.filter (· ≠ "atom")).map Term.atom) = .nil) := by
            cases h : Ks.filter (· ≠ "atom") with
            | nil => exact absurd h wn
            | cons d ds => simp [Term.list]
          simp only [cOp] at rW
          simp at wsCmp rW
          simp [wsCmp, rW, rU]
          rcases mapsD_cases mU with ⟨rfl, -⟩ | ⟨c, neU, lc, fc, -⟩
          · simp [Term.compare_self]
            first
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
          · simp [neU, getMapKeys_single, lc, Option.toList]
            first
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
  · rw [show val₁ ++ val₂ = Dm.map Term.atom from (eDm.2 rfl).symm]
    refine ex_bind (boolAtom (decide (Dm ≠ []))) (by
      by_cases e0 : Dm = []
      · subst e0; simp [Term.list, boolAtom]
      · have e0' : List.map Term.atom Dm ≠ [] := by simpa using e0
        simp only [equal_eq_decide, decide_eq_true_eq, cmp_list_nil, e0', ↓reduceIte]
        first
        | (have := fDm rfl e0; simp [this, boolAtom, e0, Lynx.Except.orElse])
        | (cases f₁ <;> cases f₂ <;> simp [boolAtom, e0, Lynx.Except.orElse])) ?_
    rcases ok.hneg with rfl | ⟨N, rfl⟩
    · generalize hg : (f₁ || f₂) = g
      by_cases e0 : Dm = [] <;> cases g
      rotate_left 2
      · exact absurd (hg ▸ fDm rfl e0) (by simp)
      rotate_left 1
      all_goals simp [e0, boolAtom, Lynx.Except.orElse]
      all_goals simp only [atom_ite_bool]
      · first
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
      · first
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
        | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
            obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
              (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
            simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
              show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
            simp [Term.list] at n₁;
            simp [n₁, n₂];
            obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
              fun w => Iff.rfl;
            rw [ru];
            simp only [Lynx.Except.ok_bind];
            split <;> exact ⟨_, rfl⟩)
      all_goals
        have na : "atom" ∉ Dm := fun m => by
          have := ok.hatom.mp (List.mem_map_of_mem (hDm _ m)); obtain ⟨N, e⟩ := this; cases e
        obtain ⟨Ks, rKs, mKs, -, subKs, -⟩ := kinds_usort (Dm.map Term.atom) fun d md' => by
          obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md'; exact ⟨s, hD s (hDm s ms), rfl⟩
        have naK : "atom" ∉ Ks := fun m => na (by simpa using (mKs _).mp m)
        obtain ⟨R, rW, mR⟩ := widen_run_gen ef (n := n + 1) (by omega) hnt nopt (md := "reject") (by simp [Mode]) Ks naK subKs lines hl'
        simp only [cOp] at rW
        simp only [rKs, rW, Lynx.Except.ok_bind]
        rcases mapsD_cases mR with ⟨rfl, -⟩ | ⟨c, neR, lc, fc, -⟩
        · simp [Term.compare_self]
          first
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
        · simp [neR, getMapKeys_single, lc, Option.toList]
          first
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
          | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
              obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
              simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
              simp [Term.list] at n₁;
              simp [n₁, n₂];
              obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                fun w => Iff.rfl;
              rw [ru];
              simp only [Lynx.Except.ok_bind];
              split <;> exact ⟨_, rfl⟩)
    · have keysN := setStrs_keys (hNa N rfl)
      obtain ⟨AKt, rR', -, mR'⟩ := usort_atoms (R2.map Term.atom ++ (Os.map Term.atom ++ (setStrs N).map Term.atom))
        (fun k mk => by simp only [List.mem_append, List.mem_map] at mk; rcases mk with (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩ | ⟨s, -, rfl⟩) <;> exact ⟨s, rfl⟩)
      obtain ⟨AK, rfl⟩ := atoms_strs fun r mr => by
        have := (mR' r).mp mr
        simp only [List.mem_append, List.mem_map] at this
        rcases this with (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩ | ⟨s, -, rfl⟩) <;> exact ⟨s, rfl⟩
      generalize hg : (f₁ || f₂) = g
      by_cases e0 : Dm = [] <;> cases g
      rotate_left 2
      · exact absurd (hg ▸ fDm rfl e0) (by simp)
      rotate_left 1
      all_goals simp [e0, boolAtom, Lynx.Except.orElse, Erlang.sets.«to_list/1», Erlang.maps.«keys/1», keysN,
        append_list, rR']
      all_goals simp only [atom_ite_bool]
      · obtain rfl : Dm = [] := e0
        have l0 := length_list ([] : List Term)
        have p0 := partition_atom (n + 5) []
        simp only [List.map_nil, List.filter_nil, List.length_nil] at l0 p0
        simp only [Term.list] at l0 p0
        simp only [l0, Lynx.Except.ok_bind]
        have c12 : Term.compare ((Term.integer ((0 : Nat) : Int)).fuel (.integer 12)) (.integer ((0 : Nat) : Int))
            (.integer 12) ≠ .eq := by simp [Lynx.Term.compare_integers]
        simp only [c12, ↓reduceIte]
        rw [show n + 5 + 1 = n + 6 from rfl] at p0
        simp only [p0, Lynx.Except.ok_bind]
        obtain ⟨_, _, res, rb, _, _, _, _, X, eX, mX⟩ := box_runG ef (n := n + 2) (by omega) lines bdd hl fbd sbd hnt
          snt nopt (md := "reject") (by simp [Mode]) (R2 ++ Os) AK [] (by simp)
        subst eX
        simp only [cOp, List.map_append, List.map_nil, Term.list] at rb
        simp only [rb, Lynx.Except.ok_bind, Term.compare_self, ↓reduceIte]
        rcases mapsD_cases mX with ⟨rfl, -⟩ | ⟨c, neU, lc, fc, -⟩
        · simp [Term.compare_self]
          first
            | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                  show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                simp [Term.list] at n₁;
                simp [n₁, n₂];
                obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                  fun w => Iff.rfl;
                rw [ru];
                simp only [Lynx.Except.ok_bind];
                split <;> exact ⟨_, rfl⟩)
            | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                  show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                simp [Term.list] at n₁;
                simp [n₁, n₂];
                obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                  fun w => Iff.rfl;
                rw [ru];
                simp only [Lynx.Except.ok_bind];
                split <;> exact ⟨_, rfl⟩)
            | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                  show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                simp [Term.list] at n₁;
                simp [n₁, n₂];
                obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                  fun w => Iff.rfl;
                rw [ru];
                simp only [Lynx.Except.ok_bind];
                split <;> exact ⟨_, rfl⟩)
            | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                  show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                simp [Term.list] at n₁;
                simp [n₁, n₂];
                obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                  fun w => Iff.rfl;
                rw [ru];
                simp only [Lynx.Except.ok_bind];
                split <;> exact ⟨_, rfl⟩)
        · simp [neU, getMapKeys_single, lc, Option.toList]
          first
            | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                  show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                simp [Term.list] at n₁;
                simp [n₁, n₂];
                obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                  fun w => Iff.rfl;
                rw [ru];
                simp only [Lynx.Except.ok_bind];
                split <;> exact ⟨_, rfl⟩)
            | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                  show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                simp [Term.list] at n₁;
                simp [n₁, n₂];
                obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                  fun w => Iff.rfl;
                rw [ru];
                simp only [Lynx.Except.ok_bind];
                split <;> exact ⟨_, rfl⟩)
            | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                  show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                simp [Term.list] at n₁;
                simp [n₁, n₂];
                obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                  fun w => Iff.rfl;
                rw [ru];
                simp only [Lynx.Except.ok_bind];
                split <;> exact ⟨_, rfl⟩)
            | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                  show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                simp [Term.list] at n₁;
                simp [n₁, n₂];
                obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                  fun w => Iff.rfl;
                rw [ru];
                simp only [Lynx.Except.ok_bind];
                split <;> exact ⟨_, rfl⟩)
      · obtain rfl : Dm = [] := e0
        have l0 := length_list ([] : List Term)
        have p0 := partition_atom (n + 5) []
        simp only [List.map_nil, List.filter_nil, List.length_nil] at l0 p0
        simp only [Term.list] at l0 p0
        simp only [l0, Lynx.Except.ok_bind]
        have c12 : Term.compare ((Term.integer ((0 : Nat) : Int)).fuel (.integer 12)) (.integer ((0 : Nat) : Int))
            (.integer 12) ≠ .eq := by simp [Lynx.Term.compare_integers]
        simp only [c12, ↓reduceIte]
        rw [show n + 5 + 1 = n + 6 from rfl] at p0
        simp only [p0, Lynx.Except.ok_bind]
        obtain ⟨_, _, res, rb, _, _, _, _, X, eX, mX⟩ := box_runG ef (n := n + 2) (by omega) lines bdd hl fbd sbd hnt
          snt nopt (md := "reject") (by simp [Mode]) (R2 ++ Os) AK [] (by simp)
        subst eX
        simp only [cOp, List.map_append, List.map_nil, Term.list] at rb
        simp only [rb, Lynx.Except.ok_bind, Term.compare_self, ↓reduceIte]
        rcases mapsD_cases mX with ⟨rfl, -⟩ | ⟨c, neU, lc, fc, -⟩
        · simp [Term.compare_self]
          first
            | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                  show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                simp [Term.list] at n₁;
                simp [n₁, n₂];
                obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                  fun w => Iff.rfl;
                rw [ru];
                simp only [Lynx.Except.ok_bind];
                split <;> exact ⟨_, rfl⟩)
            | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                  show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                simp [Term.list] at n₁;
                simp [n₁, n₂];
                obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                  fun w => Iff.rfl;
                rw [ru];
                simp only [Lynx.Except.ok_bind];
                split <;> exact ⟨_, rfl⟩)
            | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                  show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                simp [Term.list] at n₁;
                simp [n₁, n₂];
                obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                  fun w => Iff.rfl;
                rw [ru];
                simp only [Lynx.Except.ok_bind];
                split <;> exact ⟨_, rfl⟩)
            | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                  show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                simp [Term.list] at n₁;
                simp [n₁, n₂];
                obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                  fun w => Iff.rfl;
                rw [ru];
                simp only [Lynx.Except.ok_bind];
                split <;> exact ⟨_, rfl⟩)
        · simp [neU, getMapKeys_single, lc, Option.toList]
          first
            | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                  show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                simp [Term.list] at n₁;
                simp [n₁, n₂];
                obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                  fun w => Iff.rfl;
                rw [ru];
                simp only [Lynx.Except.ok_bind];
                split <;> exact ⟨_, rfl⟩)
            | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                  show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                simp [Term.list] at n₁;
                simp [n₁, n₂];
                obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                  fun w => Iff.rfl;
                rw [ru];
                simp only [Lynx.Except.ok_bind];
                split <;> exact ⟨_, rfl⟩)
            | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                  show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                simp [Term.list] at n₁;
                simp [n₁, n₂];
                obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                  fun w => Iff.rfl;
                rw [ru];
                simp only [Lynx.Except.ok_bind];
                split <;> exact ⟨_, rfl⟩)
            | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                  (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                  show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                simp [Term.list] at n₁;
                simp [n₁, n₂];
                obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                  fun w => Iff.rfl;
                rw [ru];
                simp only [Lynx.Except.ok_bind];
                split <;> exact ⟨_, rfl⟩)
      all_goals
        obtain ⟨Ks, rKs, -, -, subKs, -⟩ := kinds_usort (Dm.map Term.atom) fun d md' => by
          obtain ⟨s, ms, rfl⟩ := List.mem_map.mp md'; exact ⟨s, hD s (hDm s ms), rfl⟩
        have lenK : Erlang.erlang.«length/1» (Term.list (Ks.map Term.atom)) = .ok (.integer (Ks.length : Int)) := by
          simpa using length_list (Ks.map Term.atom)
        have part := partition_atom (n + 5) Ks
        simp only [rKs, Lynx.Except.ok_bind]
        try simp only [lenK, Lynx.Except.ok_bind]
        by_cases full : (Ks.length : Int) = 12
        · simp [Lynx.Term.compare_integers, full]
          obtain ⟨_, _, res, rb, _, _, _, _, X, eX, mX⟩ := box_runG ef (n := n + 2) (by omega) lines bdd hl fbd sbd hnt
            snt nopt (md := "reject") (by simp [Mode]) (R2 ++ Os) AK Ks subKs
          subst eX
          simp only [cOp, List.map_append] at rb
          simp [rb, Term.list]
          rcases mapsD_cases mX with ⟨rfl, -⟩ | ⟨c, neU, lc, fc, -⟩
          · simp [Term.compare_self]
            first
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
          · simp [neU, getMapKeys_single, lc, Option.toList]
            first
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
              | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                  obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                    (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                  simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                    show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                  simp [Term.list] at n₁;
                  simp [n₁, n₂];
                  obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                    fun w => Iff.rfl;
                  rw [ru];
                  simp only [Lynx.Except.ok_bind];
                  split <;> exact ⟨_, rfl⟩)
        · simp [Lynx.Term.compare_integers, full, part]
          obtain ⟨_, _, res, rb, _, _, _, _, X, eX, mX⟩ := box_runG ef (n := n + 2) (by omega) lines bdd hl fbd sbd hnt
            snt nopt (md := "reject") (by simp [Mode]) (R2 ++ Os) AK (Ks.filter (· = "atom"))
            (fun d m => subKs d (List.mem_filter.mp m).1)
          subst eX
          simp only [cOp, List.map_append] at rb
          simp only [rb, Lynx.Except.ok_bind]
          by_cases wn : Ks.filter (· ≠ "atom") = []
          · have wn' : List.filter (fun x => !decide (x = "atom")) Ks = [] := by simpa using wn
            simp [wn', Term.list]
            rcases mapsD_cases mX with ⟨rfl, -⟩ | ⟨c, neU, lc, fc, -⟩
            · simp [Term.compare_self]
              first
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
            · simp [neU, getMapKeys_single, lc, Option.toList]
              first
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
          · obtain ⟨W, rW, mW⟩ := widen_run_gen ef (n := n + 1) (by omega) hnt nopt (md := "reject") (by simp [Mode])
              (Ks.filter (· ≠ "atom")) (fun m => by simpa using (List.mem_filter.mp m).2)
              (fun d m => subKs d (List.mem_filter.mp m).1) lines hl'
            obtain ⟨U, rU, mU⟩ := mapsD_union (den := den) ef (m := n + 5) (by omega) mX mW
            have wsCmp : ¬(Term.list ((Ks.filter (· ≠ "atom")).map Term.atom) = .nil) := by
              cases h : Ks.filter (· ≠ "atom") with
              | nil => exact absurd h wn
              | cons d ds => simp [Term.list]
            simp only [cOp] at rW
            simp at wsCmp rW
            simp [wsCmp, rW, rU]
            rcases mapsD_cases mU with ⟨rfl, -⟩ | ⟨c, neU, lc, fc, -⟩
            · simp [Term.compare_self]
              first
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simp);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
            · simp [neU, getMapKeys_single, lc, Option.toList]
              first
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.false T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.true (pk Bool.true) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)
                | (obtain ⟨B₁, f₁', T₁', Er₁', n₁, hT₁', fB₁⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.true st Bool.true (pk Bool.true) rk [c] Bool.true T₂ (Term.list (mis₁.map bdErr)) hT₂ (by simpa using fc);
                    obtain ⟨B₂, f₂', T₂', Er₂', n₂, hT₂', fB₂⟩ := named_fold_ok ef (n := n + 2) (by omega) lines
                      (by simp [Mode]) Bool.false st Bool.false (pk Bool.false) (R2 ++ Os) B₁ f₁' T₁' Er₁' hT₁' fB₁;
                    simp only [List.map_append, cOp, show boolAtom Bool.true = .atom "true" from rfl,
                      show boolAtom Bool.false = .atom "false" from rfl] at n₁ n₂;
                    simp [Term.list] at n₁;
                    simp [n₁, n₂];
                    obtain ⟨u, ru, -⟩ := union_Y ef (m := n + 6) (by omega) B₂ fB₂ (S := fun w => ∃ b ∈ B₂, denMF E den b w = Bool.true)
                      fun w => Iff.rfl;
                    rw [ru];
                    simp only [Lynx.Except.ok_bind];
                    split <;> exact ⟨_, rfl⟩)

end



section
variable {t : Term} {d : Nat}

/-- Static-level semantics of an update at a split, on the static map types of a level: without maps `:badmap` or no
result, otherwise the old values `OV`, the maps `S` and the found flag `F` of the maps of the type. -/
def SUpd (t : Term) (n : Nat) (s op : Term) (OV : (MW (level t n).V → Prop) → (level t n).V → Prop)
    (S : (MW (level t n).V → Prop) → MW (level t n).V → Prop) (F : (MW (level t n).V → Prop) → Bool → Prop) : Prop :=
  ∀ Z, DE (level t n).E (.map Z) → ∀ (st : Bool) (m : Nat), (level t n).K + 30 ≤ m → ∃ res,
    Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map Z) s op (.atom "true") (boolAtom st) = .ok res ∧
      (((res = .atom "badmap" ∨ res = .tuple #[.map [], .map [], .nil, .atom "false"]) ∧ ∀ w, ¬MT t n Z w) ∨
        (∃ w, MT t n Z w) ∧ ∃ (T : Term) (Y : List (Term × Term)) (er : List Term) (f : Bool),
          res = .tuple #[T, .map Y, Term.list er, boolAtom f] ∧ (level t n).E T ∧
          (∀ x, (level t n).den T x ↔ OV (MT t n Z) x) ∧
          DE (level t n).E (.map Y) ∧ (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          (∀ w, MT t n Y w ↔ S (MT t n Z) w) ∧ (f = Bool.true ↔ F (MT t n Z) st))

/-- An update of a gradual map type of the next level at a split with static-level semantics: it gives a type exactly
when the static part holds only maps and the dynamic part some map, and the update of the dynamic part finds a key;
then the updates of the static maps, with those of the dynamic maps in the upper bound, and the same for old values. -/
theorem gupd_gen {X : List (Term × Term)} (gX : GC (level t (d + 1)) (.map X)) {Dy : Term}
    (hD : mapLookup X (.atom "dynamic") = some Dy) {s op : Term}
    {OV : (MW (level t (d + 1)).V → Prop) → (level t (d + 1)).V → Prop}
    {S : (MW (level t (d + 1)).V → Prop) → MW (level t (d + 1)).V → Prop}
    {F : (MW (level t (d + 1)).V → Prop) → Bool → Prop} (hS : SUpd t (d + 1) s op OV S F)
    (ovE : ∀ M x, OV M x → ∃ w, M w) {m : Nat} (hm : (level t (d + 1)).K + 30 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X) s op (.atom "true") = .ok r ∧
      ((∃ T R er, r = .tuple #[T, R, er]) ↔ (∀ q : PN t (d + 1), denD (.map (rmDyn X)) q → q.1.1 = "map") ∧
        (∃ w, MT t (d + 1) (dynL Dy) w) ∧ F (MT t (d + 1) (dynL Dy)) Bool.false) ∧
      ∀ T R er, r = .tuple #[T, R, er] → GC (level t (d + 1)) R ∧
        (∀ q : PN t (d + 1), denD (upper R) q → q.1.1 = "map") ∧
        (∀ w, denD R (mpt (t := t) (n := d + 1) w) ↔ (∃ u, MT t (d + 1) (rmDyn X) u) ∧
          S (MT t (d + 1) (rmDyn X)) w) ∧
        (∀ w, denD (upper R) (mpt (t := t) (n := d + 1) w) ↔ ((∃ u, MT t (d + 1) (rmDyn X) u) ∧
          S (MT t (d + 1) (rmDyn X)) w) ∨ S (MT t (d + 1) (dynL Dy)) w) ∧
        ∃ lt ut, Elixir.Module.Types.Descr.«lower_bound/1» (D m) T = .ok lt ∧
          Elixir.Module.Types.Descr.«upper_bound/1» (D m) T = .ok ut ∧ DE (level t d).E lt ∧ DE (level t d).E ut ∧
          (∀ x : PN t d, denD lt x ↔ OV (MT t (d + 1) (rmDyn X)) x) ∧
          (∀ x : PN t d, denD ut x ↔ OV (MT t (d + 1) (rmDyn X)) x ∨ OV (MT t (d + 1) (dynL Dy)) x) ∧
          GC (level t d) T ∧ (∀ x : PN t d, denD T x ↔ OV (MT t (d + 1) (rmDyn X)) x) ∧
          ∀ x : PN t d, denD (upper T) x ↔ OV (MT t (d + 1) (rmDyn X)) x ∨ OV (MT t (d + 1) (dynL Dy)) x := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
  have hK := level_K t d
  have hK' := level_K t (d + 1)
  rcases gX with tX | ⟨X', Dy', e, hD', tD, dS, incl⟩
  · rcases tX with h | ⟨X', e, sX'⟩
    · cases h
    · simp only [Term.map.injEq] at e; subst e; rw [sX'.static] at hD; cases hD
  simp only [Term.map.injEq] at e; subst e
  rw [hD] at hD'; cases hD'
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def]
  simp only [Erlang.maps.«take/2», hD, equalExact_eq_decide]
  have eS : (X.filter fun entry => !decide (compareExact ((Term.atom "dynamic").fuel entry.fst) (Term.atom "dynamic") entry.fst = .eq)) = rmDyn X := rfl
  rw [eS]
  simp only [Lynx.Except.ok_bind]
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 8))
      (.function false "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-1-" 1 #[]) #[r] =
        Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1» r := fun r => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-1-/1».pure]
  have dSt : DE (level t (d + 1)).E (.map (rmDyn X)) := Or.inr ⟨_, rfl, dS⟩
  obtain ⟨dR, sRm⟩ := rest_map dSt
  have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 8)) (.map (rmDyn X)) =
      .ok (boolAtom (bp (∀ q : PN t (d + 1), ¬denD (.map (rmM (rmDyn X))) q))) := by
    simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
    exact next_empty dR (by omega)
  have dDy : DE (level t (d + 1)).E (.map (dynL Dy)) := by
    rcases tD with rfl | ⟨Y, rfl, sY⟩
    · exact mapTop_de
    · exact Or.inr ⟨Y, rfl, sY⟩
  have stD : ∀ st, Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 8)) Dy
      s op (.atom "true") st =
      Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 8)) (.map (dynL Dy))
      s op (.atom "true") st := by
    intro st
    rcases tD with rfl | ⟨Y, rfl, -⟩
    · conv => lhs; rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def]
      simp [Lynx.Term.getMapKeys, dynL, topM]
    · rfl
  have keyD : Elixir.Module.Types.Descr.«descr_key?/2» Dy (.atom "map") =
      .ok (boolAtom (mapLookup (dynL Dy) (.atom "map")).isSome) := by
    rcases tD with rfl | ⟨Y, rfl, -⟩
    · simp [Elixir.Module.Types.Descr.«descr_key?/2», dynL, topM, mapLookup, boolAtom, pure, Except.pure]
    · cases h : mapLookup Y (.atom "map") <;>
        simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, dynL, h, boolAtom]
  rw [stD]
  have onlyIff : (∀ q : PN t (d + 1), ¬denD (.map (rmM (rmDyn X))) q) ↔
      ∀ q : PN t (d + 1), denD (.map (rmDyn X)) q → q.1.1 = "map" :=
    ⟨fun h q hq => Classical.byContradiction fun nq => h q ((sRm q).mpr ⟨hq, nq⟩),
      fun h q hq => ((sRm q).mp hq).2 (h q ((sRm q).mp hq).1)⟩
  rcases Classical.em (¬∀ q : PN t (d + 1), ¬denD (.map (rmM (rmDyn X))) q) with hmo | hmo
  · rw [bp_false.mpr hmo] at mo
    refine ⟨.atom "badmap", ?_, ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨h, _⟩ => absurd (onlyIff.mpr h) hmo⟩,
      fun _ _ _ h => by cases h⟩
    cases hk : (mapLookup (dynL Dy) (.atom "map")).isSome <;>
      simp [keyD, hk, mo, Lynx.Except.andAlso, boolAtom, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1»]
  rw [bp_true.mpr (Classical.not_not.mp hmo)] at mo
  have onlyS := onlyIff.mp (Classical.not_not.mp hmo)
  rcases Classical.em ((mapLookup (dynL Dy) (.atom "map")).isSome = Bool.false) with hbm | hbm
  · refine ⟨.atom "badmap", ?_, ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨_, ⟨w, b, hb, _⟩, _⟩ => (by simp [hb] at hbm)⟩,
      fun _ _ _ h => by cases h⟩
    simp [keyD, hbm, Lynx.Except.andAlso, boolAtom, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1»]
  have kt : Elixir.Module.Types.Descr.«descr_key?/2» Dy (.atom "map") = .ok (.atom "true") := by
    simp only [Bool.not_eq_false] at hbm
    simp [keyD, hbm, boolAtom]
  -- The static part, as the gradual update sees it.
  obtain ⟨rS, rrS, hS'⟩ := hS (rmDyn X) dSt Bool.true (k + 8) (by omega)
  simp only [boolAtom, ↓reduceIte] at rrS
  obtain ⟨sv, Sd, se, eS', hsv, ssv, dSd, oSd, sSd⟩ : ∃ (sv : Term) (Sd : List (Term × Term)) (se : List Term),
      ((rS = .atom "badmap" ∧ sv = .map [] ∧ Sd = [] ∧ se = []) ∨
        ∃ fs, rS = .tuple #[sv, .map Sd, Term.list se, fs]) ∧
      (level t (d + 1)).E sv ∧ (∀ x, (level t (d + 1)).den sv x ↔ OV (MT t (d + 1) (rmDyn X)) x) ∧
      DE (level t (d + 1)).E (.map Sd) ∧ (∀ q : PN t (d + 1), denD (.map Sd) q → q.1.1 = "map") ∧
      ∀ w, denD (.map Sd) (mpt (t := t) (n := d + 1) w) ↔ (∃ u, MT t (d + 1) (rmDyn X) u) ∧
        S (MT t (d + 1) (rmDyn X)) w := by
    have ef := (level t (d + 1)).ef
    have emp : ∀ (hno : ∀ w, ¬MT t (d + 1) (rmDyn X) w), (level t (d + 1)).E (.map []) ∧
        (∀ x, (level t (d + 1)).den (.map []) x ↔ OV (MT t (d + 1) (rmDyn X)) x) ∧
        DE (level t (d + 1)).E (.map []) ∧ (∀ q : PN t (d + 1), denD (.map []) q → q.1.1 = "map") ∧
        ∀ w, denD (.map []) (mpt (t := t) (n := d + 1) w) ↔ (∃ u, MT t (d + 1) (rmDyn X) u) ∧
          S (MT t (d + 1) (rmDyn X)) w := fun hno =>
      ⟨ef.none, fun x => ⟨fun h => absurd h (ef.den_none x), fun h => let ⟨w, hw⟩ := ovE _ x h; absurd hw (hno w)⟩,
        Or.inr ⟨_, rfl, descrC_nil⟩, fun q h => by simp [denD_map, mapLookup, dn_none] at h,
        fun w => ⟨fun h => by simp [denD_map, mapLookup, dn_none] at h, fun ⟨⟨u, hu⟩, _⟩ => absurd hu (hno u)⟩⟩
    rcases hS' with ⟨hrS | hrS, hno⟩ | ⟨exS, TS, YS, erS, fS, rfl, hTS, sTS, dYS, oYS, sYS, -⟩
    · exact ⟨.map [], [], [], Or.inl ⟨hrS, rfl, rfl, rfl⟩, emp hno⟩
    · exact ⟨.map [], [], [], Or.inr ⟨_, by rw [hrS]⟩, emp hno⟩
    · refine ⟨TS, YS, erS, Or.inr ⟨_, rfl⟩, hTS, fun x => (sTS x).trans Iff.rfl, dYS, oYS, fun w => ?_⟩
      rw [denD_mpt, sYS]
      exact ⟨fun h => ⟨exS, h⟩, fun ⟨_, h⟩ => h⟩
  -- The static block of the gradual branch.
  -- The dynamic part.
  obtain ⟨rd, rrd, hd⟩ := hS (dynL Dy) dDy Bool.false (k + 8) (by omega)
  simp only [boolAtom, Bool.false_eq_true, ↓reduceIte] at rrd
  simp only [kt, mo, boolAtom, ↓reduceIte, Lynx.Except.andAlso, rrd, Lynx.Except.ok_bind]
  rcases hd with ⟨hrd | hrd, noD⟩ | ⟨exD, Td, Yd, erd, fd, rfl, hTd, sTd, dYd, oYd, sYd, hfd⟩
  · subst hrd
    exact ⟨.atom "badmap", by simp [bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1»],
      ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨_, ⟨w, hw⟩, _⟩ => absurd hw (noD w)⟩, fun _ _ _ h => by cases h⟩
  · subst hrd
    refine ⟨.tuple #[.atom "error", Term.list se], ?_,
      ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨_, ⟨w, hw⟩, _⟩ => absurd hw (noD w)⟩, fun _ _ _ h => by cases h⟩
    rcases eS' with ⟨rfl, rfl, rfl, rfl⟩ | ⟨fs, rfl⟩ <;>
      simp [rrS, Lynx.Term.isMember, app_nil_r, app_nil0, Term.list]
  cases fd
  · have nf : ¬F (MT t (d + 1) (dynL Dy)) Bool.false := fun h => by
      have := hfd.mpr h; cases this
    refine ⟨.tuple #[.atom "error", Term.list (se ++ erd)], ?_,
      ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨_, _, h⟩ => absurd h nf⟩, fun _ _ _ h => by cases h⟩
    rcases eS' with ⟨rfl, rfl, rfl, rfl⟩ | ⟨fs, rfl⟩ <;>
      simp [rrS, Lynx.Term.isMember, append_list, app_nil_l, boolAtom]
  have fd' : F (MT t (d + 1) (dynL Dy)) Bool.false := hfd.mp rfl
  -- The union of the static deletions and the dynamic ones.
  have fin : ∃ c, Elixir.Module.Types.Descr.«opt_union/2» (D (k + 8)) (.map Sd) (.map [(.atom "dynamic", .map Yd)]) =
        .ok c ∧ GC (level t (d + 1)) c ∧ (∀ q : PN t (d + 1), denD (upper c) q → q.1.1 = "map") ∧
      (∀ q : PN t (d + 1), denD c q ↔ denD (.map Sd) q) ∧
      ∀ q : PN t (d + 1), denD (upper c) q ↔ denD (.map Sd) q ∨ denD (.map Yd) q := by
    have noP : ∀ q : PN t (d + 1), ¬denD (.map [(.atom "dynamic", .map Yd)]) q := fun q h => by
      have := (denD_rmDyn [(.atom "dynamic", .map Yd)] q).mpr h
      rw [rmDyn_cons_dyn] at this
      simp [rmDyn, denD_map, mapLookup, dn_none] at this
    have gY : GC (level t (d + 1)) (.map [(.atom "dynamic", .map Yd)]) :=
      Or.inr ⟨_, .map Yd, rfl, by simp [mapLookup], dYd, by rw [rmDyn_cons_dyn]; exact descrC_nil,
        fun q h => absurd h (noP q)⟩
    obtain ⟨c, gc, rc, sc₁, sc₂⟩ := gc_opt_union (GC.tc dSd) gY [] (m := k + 8) (by omega)
    have uS : upper (.map Sd) = .map Sd := upper_tc dSd
    have uY : upper (.map [(.atom "dynamic", .map Yd)]) = .map Yd := upper_dyn (by simp [mapLookup])
    refine ⟨c, by simpa [Elixir.Module.Types.Descr.«opt_union/2»] using rc, gc, fun q h => ?_, fun q => ?_,
      fun q => ?_⟩
    · rw [sc₂, uS, uY] at h
      rcases h with h | h
      · exact oSd q h
      · exact oYd q h
    · rw [sc₁]; simp [noP q]
    · rw [sc₂, uS, uY]
  obtain ⟨c, rc, gc, oc, sc₁, sc₂⟩ := fin
  -- The union of the static old values and the dynamic ones.
  obtain ⟨c₁, hc₁, sc₁', cases₁⟩ := el_canon hTd
  obtain ⟨RT, rRT, gRT, lRT, uRT⟩ := el_dyn_union hc₁ hsv (m := k + 8) (by omega)
  refine ⟨.tuple #[RT, c, Term.list (se ++ erd)], ?_, ⟨fun _ => ⟨onlyS, exD, fd'⟩, fun _ => ⟨_, _, _, rfl⟩⟩,
    fun T R er e => ?_⟩
  · have sYd : mapLookup Yd (.atom "dynamic") = none := (de_map dYd).static
    have fY : (Yd.find? fun entry => decide (compareExact ((Term.atom "dynamic").fuel entry.fst) (Term.atom "dynamic")
        entry.fst = Ordering.eq)) = none := by
      simpa [mapLookup] using sYd
    rcases cases₁ with ⟨de, rfl⟩ | ⟨hn, rfl⟩
    · rcases de with rfl | ⟨Z, rfl, sZ⟩
      · rcases eS' with ⟨rfl, rfl, rfl, rfl⟩ | ⟨fs, rfl⟩ <;>
          simp [rrS, boolAtom, Lynx.Term.isMember, getMapKeys, fY, rRT, rc, append_list, app_nil_l]
      · rcases eS' with ⟨rfl, rfl, rfl, rfl⟩ | ⟨fs, rfl⟩ <;>
          simp [rrS, boolAtom, Lynx.Term.isMember, getMapKeys_single, sZ.static, sYd, rRT, rc, append_list, app_nil_l]
    · obtain ⟨q, SS, rfl⟩ := node_tuple hn
      have ex := expand_isT hn (k + 7)
      obtain ⟨Y, eY, sY⟩ := expN_map (.tuple #[.reference q, .map SS, gen]) (keyOf (level t d).nd)
      rw [eY] at ex rRT
      have dY : Elixir.Module.Types.Descr.«dynamic/1» (D (k + 8)) (.map Y) =
          .ok (.map [(.atom "dynamic", .map Y)]) := by
        unfold Elixir.Module.Types.Descr.«dynamic/1»; simp [getMapKeys_single, sY]
      have gt : getMapKeys [Term.atom "dynamic"] (.tuple #[.reference q, .map SS, gen]) = [] := by simp [getMapKeys]
      rcases eS' with ⟨rfl, rfl, rfl, rfl⟩ | ⟨fs, rfl⟩ <;>
        simp [rrS, boolAtom, Lynx.Term.isMember, gt, ex, unfold_map, dY, getMapKeys_single, sYd, rRT, rc, append_list,
          app_nil_l]
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  refine ⟨gc, oc, fun w => (sc₁ _).trans (sSd w), fun w => ?_, lower RT, upper RT, lower_bound_run gRT.shape,
    upper_bound_run gRT.ub, gRT.low_tc, gRT.up_tc, fun x => (denD_lower RT x).trans ((lRT x).trans (ssv x)),
    fun x => (uRT x).trans (or_congr (ssv x) ((sc₁' x).symm.trans (sTd x))), gRT, fun x => (lRT x).trans (ssv x),
    fun x => (uRT x).trans (or_congr (ssv x) ((sc₁' x).symm.trans (sTd x)))⟩
  rw [sc₂, sSd, denD_mpt, sYd]


/-- An update at a split with static-level semantics of a map type of the next level: it gives a type exactly when
the lower bound holds only maps and the upper bound some, and the update of the upper bound finds a key (as a static
update when the type is static); then the updates of the maps of the lower bound, with those of the upper bound in its
upper bound, and the same for the old values. -/
theorem gupd_un {X : List (Term × Term)} (gX : GC (level t (d + 1)) (.map X)) {s op : Term}
    {OV : (MW (level t (d + 1)).V → Prop) → (level t (d + 1)).V → Prop}
    {S : (MW (level t (d + 1)).V → Prop) → MW (level t (d + 1)).V → Prop}
    {F : (MW (level t (d + 1)).V → Prop) → Bool → Prop} (hS : SUpd t (d + 1) s op OV S F)
    (ovE : ∀ M x, OV M x → ∃ w, M w) {m : Nat} (hm : (level t (d + 1)).K + 30 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X) s op (.atom "true") = .ok r ∧
      ((∃ T R er, r = .tuple #[T, R, er]) ↔ (∀ q : PN t (d + 1), denD (lower (.map X)) q → q.1.1 = "map") ∧
        (∃ w, MT t (d + 1) (dynL (upper (.map X))) w) ∧
        F (MT t (d + 1) (dynL (upper (.map X)))) (mapLookup X (.atom "dynamic")).isNone) ∧
      ∀ T R er, r = .tuple #[T, R, er] → GC (level t (d + 1)) R ∧
        (∀ q : PN t (d + 1), denD (upper R) q → q.1.1 = "map") ∧
        (∀ w, denD R (mpt (t := t) (n := d + 1) w) ↔ (∃ u, MT t (d + 1) (rmDyn X) u) ∧
          S (MT t (d + 1) (rmDyn X)) w) ∧
        (∀ w, denD (upper R) (mpt (t := t) (n := d + 1) w) ↔ ((∃ u, MT t (d + 1) (rmDyn X) u) ∧
          S (MT t (d + 1) (rmDyn X)) w) ∨ S (MT t (d + 1) (dynL (upper (.map X)))) w) ∧
        ∃ lt ut, Elixir.Module.Types.Descr.«lower_bound/1» (D m) T = .ok lt ∧
          Elixir.Module.Types.Descr.«upper_bound/1» (D m) T = .ok ut ∧ DE (level t d).E lt ∧ DE (level t d).E ut ∧
          (∀ x : PN t d, denD lt x ↔ OV (MT t (d + 1) (rmDyn X)) x) ∧
          (∀ x : PN t d, denD ut x ↔ OV (MT t (d + 1) (rmDyn X)) x ∨ OV (MT t (d + 1) (dynL (upper (.map X)))) x) ∧
          ((mapLookup X (.atom "dynamic") = none ∧ (level t (d + 1)).E T ∧
              ∀ x, (level t (d + 1)).den T x ↔ OV (MT t (d + 1) (rmDyn X)) x) ∨
            (mapLookup X (.atom "dynamic") ≠ none ∧ GC (level t d) T ∧
              (∀ x : PN t d, denD T x ↔ OV (MT t (d + 1) (rmDyn X)) x) ∧
              ∀ x : PN t d, denD (upper T) x ↔ OV (MT t (d + 1) (rmDyn X)) x ∨
                OV (MT t (d + 1) (dynL (upper (.map X)))) x)) := by
  cases hD : mapLookup X (.atom "dynamic") with
  | some Dy =>
    have lX : lower (.map X) = .map (rmDyn X) := by simp [lower]
    rw [lX, upper_dyn hD]
    obtain ⟨r, run, iff, sem⟩ := gupd_gen gX hD hS ovE hm
    refine ⟨r, run, by simpa using iff, fun T R er e => ?_⟩
    obtain ⟨g, o, l, u, lt, ut, rl, ru, dl, du, sl, su, gT, lT, uT⟩ := sem T R er e
    exact ⟨g, o, l, u, lt, ut, rl, ru, dl, du, sl, su, Or.inr ⟨by simp, gT, lT, uT⟩⟩
  | none =>
    have hX := GC.static gX hD
    have sX := de_map hX
    have eX : rmDyn X = X := rmDyn_static hD
    have lX : lower (.map X) = .map X := by simp [lower, eX]
    have uX : upper (.map X) = .map X := by simp [upper, hD]
    rw [lX, uX, eX]
    simp only [dynL, Option.isNone_none]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
    rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def]
    simp only [Erlang.maps.«take/2», sX.static, Lynx.Except.ok_bind]
    have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 8))
        (.function false "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-0-" 1 #[]) #[r] =
          Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1» r := fun r => by
      rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-0-/1».pure]
    cases hb : mapLookup X (.atom "map") with
    | none =>
      refine ⟨.atom "badmap", ?_, ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨_, ⟨w, b, e, _⟩, _⟩ => by rw [hb] at e; cases e⟩,
        fun _ _ _ h => by cases h⟩
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso,
        bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
    | some b =>
      obtain ⟨dR, sR⟩ := rest_map hX
      have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "map") = .ok (.atom "true") := by
        simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
      have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 8)) (.map X) =
          .ok (boolAtom (bp (∀ v : PN t (d + 1), ¬denD (.map (rmM X)) v))) := by
        simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
        exact next_empty dR (by omega)
      have onlyIff : (∀ q : PN t (d + 1), ¬denD (.map (rmM X)) q) ↔
          ∀ q : PN t (d + 1), denD (.map X) q → q.1.1 = "map" :=
        ⟨fun h q hq => Classical.byContradiction fun nq => h q ((sR q).mpr ⟨hq, nq⟩),
          fun h q hq => ((sR q).mp hq).2 (h q ((sR q).mp hq).1)⟩
      by_cases restE : ∀ v : PN t (d + 1), ¬denD (.map (rmM X)) v
      rotate_left
      · rw [bp_false.mpr restE] at mo
        refine ⟨.atom "badmap", ?_, ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨h, _⟩ => absurd (onlyIff.mpr h) restE⟩,
          fun _ _ _ h => by cases h⟩
        simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1», boolAtom]
      rw [bp_true.mpr restE] at mo
      obtain ⟨rS, rrS, hS'⟩ := hS X hX Bool.true (k + 8) (by omega)
      simp only [boolAtom, ↓reduceIte] at rrS
      rcases hS' with ⟨hrS | hrS, noS⟩ | ⟨exS, T, Y, er, f, rfl, hT, sT, dY, oY, sY, hf⟩
      · subst hrS
        refine ⟨.atom "badmap", ?_, ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨_, ⟨w, hw⟩, _⟩ => absurd hw (noS w)⟩,
          fun _ _ _ h => by cases h⟩
        simp [key, mo, rrS, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
      · subst hrS
        refine ⟨.tuple #[.atom "error", .nil], ?_,
          ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨_, ⟨w, hw⟩, _⟩ => absurd hw (noS w)⟩, fun _ _ _ h => by cases h⟩
        simp [key, mo, rrS, Lynx.Except.andAlso, Lynx.Term.isMember]
      cases f
      · have nf : ¬F (MT t (d + 1) X) Bool.true := fun h => by
          have := hf.mpr h; cases this
        refine ⟨.tuple #[.atom "error", Term.list er], ?_,
          ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨_, _, h⟩ => absurd h nf⟩, fun _ _ _ h => by cases h⟩
        simp [key, mo, rrS, Lynx.Except.andAlso, Lynx.Term.isMember, boolAtom]
      refine ⟨.tuple #[T, .map Y, Term.list er], ?_,
        ⟨fun _ => ⟨(onlyIff.mp restE), exS, hf.mp rfl⟩, fun _ => ⟨_, _, _, rfl⟩⟩, fun T' R er' e => ?_⟩
      · simp [key, mo, rrS, Lynx.Except.andAlso, Lynx.Term.isMember, boolAtom]
      simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      obtain ⟨c, hc, sc, ub, lb, -, -⟩ := el_ops hT (k + 7)
      have uY : upper (.map Y) = .map Y := upper_tc dY
      have sem : ∀ w, denD (.map Y) (mpt (t := t) (n := d + 1) w) ↔ (∃ u, MT t (d + 1) X u) ∧
          S (MT t (d + 1) X) w := fun w => by
        rw [denD_mpt, sY]; exact ⟨fun h => ⟨exS, h⟩, fun h => h.2⟩
      refine ⟨GC.tc dY, fun q h => oY q (by rwa [uY] at h), sem, fun w => ?_, c, c, lb, ub, hc, hc,
        fun x => (sc x).symm.trans (sT x), fun x => ((sc x).symm.trans (sT x)).trans (or_self_iff).symm,
        Or.inl ⟨by first | trivial | exact hD, hT, sT⟩⟩
      rw [uY, sem]
      exact ⟨Or.inl, fun h => h.elim id fun h => ⟨exS, h⟩⟩

end


section
variable {t : Term} {n : Nat}

/-- The maps of `:keep` and `:reject` at a static split, with required atoms `A` inside a negated set: the updates at
the split, at the kinds of `Ds` held unless rejecting, and at each atom of `A`. -/
def KRS {V : Type} (den : Term → V → Prop) (M : MW V → Prop) (rs : List String) (neg : Term) (Ds A : List String)
    (v : Term) (keep : Bool) (w : MW V) : Prop :=
  ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (keep = Bool.true ∨ KindHeld M d)) ∧
    (UpdSemKR den M rs neg Dm v keep w ∨ ∃ a ∈ A, KeepSemM den M v keep a w)

/-- Splits of static keys, with required atoms `A` inside a negated set, and their keys. -/
def KSplit (rs : List String) (neg : Term) (Ds A : List String) (KP : MKey → Prop) : Prop :=
  SplitOk (rs.map Term.atom) neg (Ds.map Term.atom) ∧ (∀ N, neg = .map N → rs = []) ∧
    (∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ (neg = .atom "nil" → A = []) ∧
    (∀ N, neg = .map N → ∀ a ∈ A, mapLookup N (.atom a) ≠ none) ∧
    ∀ κ, ((∃ a ∈ A, κ = .atom a) ∨ SplitKey (rs.map Term.atom) neg (Ds.map Term.atom) κ) ↔ KP κ

/-- `:keep` and `:reject` of a static value at a gradual split, on a static map type, for either flag: the maps of a
static split of the same keys, fixed by the split. -/
theorem kr_gx {s : Term} {KP : MKey → Prop} (hs : GForm s KP) (keep : Bool) :
    ∃ (rs : List String) (neg : Term) (Ds A : List String), KSplit rs neg Ds A KP ∧
      ∀ {X : List (Term × Term)}, DE (level t n).E (.map X) → ∀ {v : Term}, (level t n).E v →
        (v = .atom "term" ∨ ∃ Z, v = .map Z) → (∃ x, (level t n).den v x) → ∀ (st : Term) {m : Nat},
        (level t n).K + 30 ≤ m → ∀ {T Y er f : Term},
        Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X) s (keepOp v keep) (.atom "true") st =
          .ok (.tuple #[T, Y, er, f]) →
        ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (Y' = [] ∨ ∃ r, Y' = [(.atom "map", r)]) ∧
          ((∃ u, MT t n X u) → ∀ w, MT t n Y' w ↔ KRS (level t n).den (MT t n X) rs neg Ds A v keep w) := by
  have hmd : Mode (if keep then "keep" else "reject") := by cases keep <;> simp [Mode]
  obtain ⟨s', hs', HR⟩ := dnf_gform_relB hs _ hmd
  -- The static split and its shape.
  obtain ⟨rs, neg, Ds, A, ks, es⟩ : ∃ (rs : List String) (neg : Term) (Ds A : List String), KSplit rs neg Ds A KP ∧
      s' = splitT ((rs ++ A).map Term.atom) neg (Ds.map Term.atom) := by
    rcases hs' with ⟨rs, Ds, rfl, ok, sk⟩ | ⟨N, Ds, rfl, ok, na, sk⟩ | ⟨A, N, Ds, rfl, ok, na, hA, sk⟩
    · obtain ⟨rs', rfl⟩ := strs_of ok.hrs
      obtain ⟨Ds', rfl, -⟩ := ds_of ok.hds
      refine ⟨rs', _, Ds', [], ⟨ok, ?_, ?_, fun _ => rfl, ?_, fun κ => by simpa using sk κ⟩, by simp⟩
      · intro N e; cases e
      · intro N e; cases e
      · intro N e; cases e
    · obtain ⟨Ds', rfl, -⟩ := ds_of ok.hds
      refine ⟨[], _, Ds', [], ⟨by simpa using ok, fun _ _ => rfl, ?_, ?_, ?_, fun κ => by simpa using sk κ⟩, by simp⟩
      · intro N' e; cases e; exact na
      · intro e; cases e
      · intro _ _ a m; simp at m
    · obtain ⟨Ds', rfl, -⟩ := ds_of ok.hds
      refine ⟨[], _, Ds', A, ⟨by simpa using ok, fun _ _ => rfl, ?_, ?_, ?_, fun κ => by simpa using sk κ⟩, by simp⟩
      · intro N' e; cases e; exact na
      · intro e; cases e
      · intro N' e; cases e; exact hA
  refine ⟨rs, neg, Ds, A, ks, ?_⟩
  obtain ⟨ok, nr, na, hA0, hA, -⟩ := ks
  subst es
  intro X hX v hv sv vne st m hm T Y er f run
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
  have ef := (level t n).ef
  have sX := de_map hX
  have eop : keepOp v keep = .tuple #[.tuple #[.atom "constant", .tuple #[v, .atom "false"]],
      .atom (if keep then "keep" else "reject")] := rfl
  have conv : ∀ {b : Term}, mapLookup X (.atom "map") = some b →
      (fun u => denMF (level t n).E (level t n).den b u = Bool.true) = MT t n X := fun hb =>
    funext fun u => propext (by simp [MT, hb])
  have hDs : ∀ s ∈ Ds, s ∈ domainKinds := fun s ms => by
    obtain ⟨s', ms', e⟩ := ok.hds _ (List.mem_map_of_mem ms); cases e; exact ms'
  -- The updates for a list of kinds with the same members agree.
  have dmEq : ∀ {Dm Dm' : List String}, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (keep = Bool.true ∨ KindHeld (MT t n X) d)) →
      (∀ d, d ∈ Dm' ↔ d ∈ Ds ∧ (keep = Bool.true ∨ KindHeld (MT t n X) d)) → ∀ w,
      UpdSemKR (level t n).den (MT t n X) rs neg Dm' v keep w → UpdSemKR (level t n).den (MT t n X) rs neg Dm v keep w :=
    fun mDm mDm' w h => upd_mono (fun u h => h) (fun x h => h) vne ok ok nr (fun κ h => h) mDm' mDm h
  cases hb : mapLookup X (.atom "map") with
  | none =>
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at run
    simp [getMapKeys_single, hb] at run
    obtain ⟨-, rfl, -⟩ := run
    exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun ⟨u, hu⟩ => by simp [MT, hb] at hu⟩
  | some b =>
  have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
  have rel := fun {r} (h : Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 8)) (.map X)
      (splitT ((rs ++ A).map Term.atom) neg (Ds.map Term.atom)) (keepOp v keep)
      (.atom "true") (.atom "true") = .ok r) => static_split_rel (k + 6) (.map X) s _ (keepOp v keep) st (.atom "true")
        (fun bdd dnf r₁ r₂ h₁ h₂ => HR (k + 6) bdd dnf _ st (.atom "true") (by rw [eop] at h₁; exact h₁)
          (by rw [eop] at h₂; exact h₂)) run h
  have toY : ∀ {r Yr : Term} {S : MW (level t n).V → Prop}, (.tuple #[T, Y, er, f] = r ∨ RelB (.tuple #[T, Y, er, f]) r) →
      (∃ T' er' f', r = .tuple #[T', Yr, er', f']) → MapsY (level t n).E (level t n).den Yr S →
      (∀ w, S w ↔ KRS (level t n).den (MT t n X) rs neg Ds A v keep w) →
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (Y' = [] ∨ ∃ r, Y' = [(.atom "map", r)]) ∧
        ((∃ u, MT t n X u) → ∀ w, MT t n Y' w ↔ KRS (level t n).den (MT t n X) rs neg Ds A v keep w) := by
    rintro r Yr S hr ⟨T', er', f', rfl⟩ hY hS
    have eY : Yr = Y := by
      rcases hr with e | ⟨_, bd, _, _, _, _, _, e₁, e₂⟩
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e; exact e.2.1.symm
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e₁ e₂; rw [e₂.2.1, ← e₁.2.1]
    subst eY
    rcases hY with ⟨rfl, emp⟩ | ⟨r', rfl, fr, sr⟩
    · exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun _ w =>
        ⟨fun h => by simp [MT, mapLookup] at h, fun h => absurd ((hS w).mpr h) (emp w)⟩⟩
    · refine ⟨_, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, Or.inr ⟨_, rfl⟩, fun _ w => ?_⟩
      rw [← hS w, ← sr w]
      simp [MT, mapLookup]
  rcases ok.hneg with rfl | ⟨N, rfl⟩
  · obtain rfl := hA0 rfl
    obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
      kr_update_static ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hv sv vne keep ok nr na hb fb
    · rcases rel (by simpa [show k + 2 + 6 = k + 8 by omega] using rr) with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
    · rw [conv hb] at hY mDm
      exact toY (rel (by simpa [show k + 2 + 6 = k + 8 by omega] using rr)) ⟨_, _, _, rfl⟩ hY fun w =>
        ⟨fun h => ⟨Dm, mDm, Or.inl h⟩, fun ⟨Dm', mDm', h⟩ => h.elim (dmEq mDm mDm' w) fun ⟨a, ma, _⟩ => by simp at ma⟩
  · have hat : "atom" ∈ Ds := by
      obtain ⟨s, ms, e⟩ := List.mem_map.mp (ok.hatom.mpr ⟨N, rfl⟩); cases e; exact ms
    obtain rfl := nr N rfl
    obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
      kr_update_static_req ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hv sv vne keep (A := A) rfl hDs hat
        (hA N rfl) na hb fb
    · rcases rel (by simpa [show k + 2 + 6 = k + 8 by omega] using rr) with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
    · rw [conv hb] at hY mDm
      exact toY (rel (by simpa [show k + 2 + 6 = k + 8 by omega] using rr)) ⟨_, _, _, rfl⟩ hY fun w =>
        ⟨fun h => ⟨Dm, mDm, h⟩, fun ⟨Dm', mDm', h⟩ => h.imp_left (dmEq mDm mDm' w)⟩

end


section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `map_update_static/5` on a map field: `:badmap` when it holds no map, otherwise a run of
`map_update_static_dnf/6` on its non-empty lines. -/
theorem static_lift (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {s op rt st : Term}
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) (Q : Term → Prop)
    (hQ : ∀ lines : List Term, (∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) → lines ≠ [] →
      (∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) →
      ∃ r, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list lines) s op rt st = .ok r ∧
        Q r) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X) s op rt st = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨ ((∃ w, denMF E den b w = Bool.true) ∧ Q res)) := by
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, ri⟩ := init_total ef.mopsE ef.mdopsE ef.jopsU [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have ri : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 6)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := ri (n + 6) (by omega)
    cases e
    · have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := ri.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ (m := n + 6) (by omega) rfl g sl
          (negs := []) (by simp) fun w hw => absurd ⟨w, hw⟩ none)
        simp [boolAtom] at this
      obtain ⟨w₀, h₀⟩ := ne
      have hl : ∀ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], MLine E L ∧ ∃ w, InMLine den L w := by
        intro L mL
        rw [List.mem_singleton] at mL; subst mL
        exact ⟨⟨tag, l, [], rfl, g, sl, by simp⟩, w₀, inMLine_iff.mpr ⟨h₀, fun N mN => by simp at mN⟩⟩
      have inB : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔
          ∃ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], InMLine den L w := fun w => by
        rw [sem]
        simp only [List.mem_singleton, exists_eq_left]
        exact ⟨fun h => inMLine_iff.mpr ⟨h, fun N mN => by simp at mN⟩, fun h => (inMLine_iff.mp h).1⟩
      have unf : Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X) s op rt st =
          Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) (.tuple #[.integer k, tag, fieldsTerm l])
            (Term.list [Term.tuple #[tag, fieldsTerm l, Term.list []]]) s op rt st := by
        unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», ri, Lynx.Term.isMember, boolAtom, Term.list]
      obtain ⟨r, rr, qr⟩ := hQ _ hl (by simp) inB
      exact ⟨r, by rw [unf]; exact rr, Or.inr ⟨⟨w₀, (sem w₀).mpr h₀⟩, qr⟩⟩
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», ri, Lynx.Term.isMember, boolAtom]
      · cases hw : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w
        · rfl
        · obtain ⟨N', mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ ef.jopsU (m := n + 6) (by omega) rfl g sl
            (negs := []) (by simp) ri w ((sem w).mp hw)
          simp at mN
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl
      (m := n + 6) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
    cases lines with
    | nil =>
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Term.list]
        · simp [getMapKeys_single, hb, rl, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Term.list]
      · cases hw : denMF E den b w
        · rfl
        · obtain ⟨L, mL, -⟩ := (inB w).mp hw; simp at mL
    | cons L rest =>
      have unf : Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X) s op rt st =
          Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list (L :: rest)) s op rt st := by
        unfold Elixir.Module.Types.Descr.«map_update_static/5»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Term.list]
        · simp [getMapKeys_single, hb, rl, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Term.list]
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      obtain ⟨r, rr, qr⟩ := hQ _ hl (by simp) inB
      exact ⟨r, by rw [unf]; exact rr, Or.inr ⟨⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, qr⟩⟩

end



section
variable {t : Term} {n : Nat}

/-- An update of a static value at the split of a gradual key, on the static map types of a level: the old values at
the keys, the found flag `FoundG`, and the maps a hypothesis gives. -/
theorem supd_val {rk Os : List String} {ng : Term} {Ds Do : List String} (gs : GSplit rk Os ng Ds Do)
    {KP : MKey → Prop} (hk : ∀ κ, GKey rk Os ng Ds Do κ ↔ KP κ) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) (vne : ∃ x, (level t n).den v x) {md : String} (hmd : Mode md)
    {S : (MW (level t n).V → Prop) → MW (level t n).V → Prop}
    (hY : ∀ X : List (Term × Term), DE (level t n).E (.map X) → ∀ (st : Bool) (m : Nat), (level t n).K + 30 ≤ m →
      ∀ T Y er f, Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X) (gsT rk Os ng Ds Do)
        (cOp v Bool.false md) (.atom "true") (boolAtom st) = .ok (.tuple #[T, Y, er, f]) →
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (∀ q : PN t n, denD (.map Y') q → q.1.1 = "map") ∧
        ((∃ u, MT t n X u) → ∀ w, MT t n Y' w ↔ S (MT t n X) w)) :
    SUpd t n (gsT rk Os ng Ds Do) (cOp v Bool.false md) (fun M x => Vals M KP x) S
      (fun M st => FoundG M rk Os ng Ds Do md st) := by
  intro Z hZ st m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
  have ef := (level t n).ef
  have sZ := de_map hZ
  cases hb : mapLookup Z (.atom "map") with
  | none =>
    refine ⟨_, ?_, Or.inl ⟨Or.inr rfl, fun w h => by simp [MT, hb] at h⟩⟩
    unfold Elixir.Module.Types.Descr.«map_update_static/5»
    simp [getMapKeys_single, hb]
  | some b =>
  have fb : MField (level t n).E b := fieldC_map (sZ.fields "map" b hb)
  have conv : (fun u => denMF (level t n).E (level t n).den b u = Bool.true) = MT t n Z :=
    funext fun u => propext (by simp [MT, hb])
  obtain ⟨res, run, hres⟩ := static_lift ef (n := k + 2) (by omega) (s := gsT rk Os ng Ds Do)
    (op := cOp v Bool.false md) (rt := .atom "true") (st := boolAtom st) hb fb
    (fun r => ∃ T Y el f, r = .tuple #[T, Y, Term.list el, boolAtom f] ∧ (level t n).E T ∧
      (∀ x, (level t n).den T x ↔ ∃ w, denMF (level t n).E (level t n).den b w = Bool.true ∧
        ∃ κ, GKey rk Os ng Ds Do κ ∧ w κ = some x) ∧
      (f = Bool.true ↔ FoundG (fun u => denMF (level t n).E (level t n).den b u = Bool.true) rk Os ng Ds Do md st))
    fun lines hl hne sl => by
      obtain ⟨r, rr⟩ := dnf_ok_g ef (n := k + 2) (by omega) hv sv Bool.false hmd fb lines hl sl gs.ok gs.na st
        fun bd a => pk_val ef (n := k + 4) (by omega) hv vne hmd lines hl bd a
      exact ⟨r, rr, dnf_gvf ef (n := k + 2) (by omega) hv vne fb lines hl sl gs hmd st rr⟩
  refine ⟨res, run, ?_⟩
  rcases hres with ⟨rfl, emp⟩ | ⟨ex, T, Y, el, f, rfl, hT, sT, sf⟩
  · exact Or.inl ⟨Or.inl rfl, fun w h => by simp [MT, hb, emp w] at h⟩
  obtain ⟨Y', rfl, dY, shY, sY⟩ := hY Z hZ _ _ hm _ _ _ _ run
  rw [conv] at sf
  have mt : ∀ w, MT t n Z w ↔ denMF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [MT, hb]
  have ex' : ∃ w, MT t n Z w := let ⟨w, hw⟩ := ex; ⟨w, (mt w).mpr hw⟩
  refine Or.inr ⟨ex', T, Y', el, f, rfl, hT, fun x => (sT x).trans ?_, dY, shY, sY ex', sf⟩
  exact ⟨fun ⟨w, hw, κ, hκ, e⟩ => ⟨w, (mt w).mpr hw, κ, (hk κ).mp hκ, e⟩,
    fun ⟨w, hw, κ, hκ, e⟩ => ⟨w, (mt w).mp hw, κ, (hk κ).mpr hκ, e⟩⟩


/-- The maps of `:keep` and `:reject` at a gradual split, as `supd_val` takes them. -/
theorem kr_hY {s : Term} {KP : MKey → Prop} (hs : GForm s KP) (keep : Bool) :
    ∃ (rs : List String) (neg : Term) (Ds A : List String), KSplit rs neg Ds A KP ∧
      ∀ {v : Term}, (level t n).E v → (v = .atom "term" ∨ ∃ Z, v = .map Z) → (∃ x, (level t n).den v x) →
      ∀ X : List (Term × Term), DE (level t n).E (.map X) → ∀ (st : Bool) (m : Nat), (level t n).K + 30 ≤ m →
      ∀ T Y er f, Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X) s
        (cOp v Bool.false (modeS keep)) (.atom "true") (boolAtom st) = .ok (.tuple #[T, Y, er, f]) →
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (∀ q : PN t n, denD (.map Y') q → q.1.1 = "map") ∧
        ((∃ u, MT t n X u) → ∀ w, MT t n Y' w ↔ KRS (level t n).den (MT t n X) rs neg Ds A v keep w) := by
  obtain ⟨rs, neg, Ds, A, ks, h⟩ := kr_gx (t := t) (n := n) hs keep
  refine ⟨rs, neg, Ds, A, ks, fun hv sv vne X hX st m hm T Y er f run => ?_⟩
  rw [← keepOp_cOp] at run
  obtain ⟨Y', e, dY, shY, sY⟩ := h hX hv sv vne _ hm run
  exact ⟨Y', e, dY, single_map_only shY, sY⟩

/-- The maps of forcing at a split putting with `P`, as `supd_val` takes them. -/
theorem force_hY {Rk Ok neg' Rd Od neg : Term} {P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop}
    (hP : DnfPuts (.tuple #[Rk, Ok, neg', Rd, Od]) neg P) (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {v : Term} (hv : (level t n).E v) (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) :
    ∀ X : List (Term × Term), DE (level t n).E (.map X) → ∀ (st : Bool) (m : Nat), (level t n).K + 30 ≤ m →
      ∀ T Y er f, Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X) (.tuple #[Rk, Ok, neg', Rd, Od])
        (cOp v Bool.false "force") (.atom "true") (boolAtom st) = .ok (.tuple #[T, Y, er, f]) →
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (∀ q : PN t n, denD (.map Y') q → q.1.1 = "map") ∧
        ((∃ u, MT t n X u) → ∀ w, MT t n Y' w ↔ P (level t n).den (MT t n X) v w) := by
  intro X hX st m hm T Y er f run
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨res, run₂, h₂⟩ := upd_static_g' hX hv sv hP hNa (m := k + 2) (by omega) st
  have rel := static_rt_rel k (.map X) Rk Ok neg' Rd Od _ (boolAtom st) (boolAtom st) run run₂
  rcases h₂ with ⟨(rfl | ⟨rfl, -⟩), no⟩ | ⟨ex, Y₂, f₂, rfl, dY, oY, sY, -⟩
  · rcases rel with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
  · have eY : Y = .map [] := by
      rcases rel with e | ⟨_, bd, _, _, _, _, _, e₁, e₂⟩
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e; exact e.2.1
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e₁ e₂; rw [e₁.2.1, e₂.2.1]
    subst eY
    exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, fun q h => by simp [denD_map, mapLookup, dn_none] at h,
      fun ⟨u, hu⟩ => absurd hu (no u)⟩
  · have eY : Y = .map Y₂ := by
      rcases rel with e | ⟨_, bd, _, _, _, _, _, e₁, e₂⟩
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e; exact e.2.1
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e₁ e₂; rw [e₁.2.1, e₂.2.1]
    exact ⟨Y₂, eY, dY, oY, fun _ => sY⟩


/-- `map_only?/1` of the static part of a gradual map type, as whether it holds only maps. -/
theorem mo_cases {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    (Elixir.Module.Types.Descr.«map_only?/1» (D m) (.map (rmDyn X)) = .ok (.atom "true") ∧
      ∀ q : PN t n, denD (.map (rmDyn X)) q → q.1.1 = "map") ∨
    (Elixir.Module.Types.Descr.«map_only?/1» (D m) (.map (rmDyn X)) = .ok (.atom "false") ∧
      ¬∀ q : PN t n, denD (.map (rmDyn X)) q → q.1.1 = "map") := by
  obtain ⟨dR, sR⟩ := rest_map (t := t) (n := n) gX.low_tc
  have mo : Elixir.Module.Types.Descr.«map_only?/1» (D m) (.map (rmDyn X)) =
      .ok (boolAtom (bp (∀ q : PN t n, ¬denD (.map (rmM (rmDyn X))) q))) := by
    simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
    exact next_empty dR hm
  have iff : (∀ q : PN t n, ¬denD (.map (rmM (rmDyn X))) q) ↔ ∀ q : PN t n, denD (.map (rmDyn X)) q → q.1.1 = "map" :=
    ⟨fun h q hq => Classical.byContradiction fun nq => h q ((sR q).mpr ⟨hq, nq⟩),
      fun h q hq => ((sR q).mp hq).2 (h q ((sR q).mp hq).1)⟩
  by_cases h : ∀ q : PN t n, ¬denD (.map (rmM (rmDyn X))) q
  · rw [bp_true.mpr h] at mo
    exact Or.inl ⟨by simpa [boolAtom] using mo, iff.mp h⟩
  · rw [bp_false.mpr h] at mo
    exact Or.inr ⟨by simpa [boolAtom] using mo, fun h' => h (iff.mpr h')⟩

end


section
variable {V : Type} {den : Term → V → Prop}

theorem krs_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {v₁ v₂ : Term}
    (hv : ∀ x, den v₁ x → den v₂ x) (vne : ∃ x, den v₁ x) {keep : Bool}
    {rs₁ rs₂ Ds₁ Ds₂ A₁ A₂ : List String} {neg₁ neg₂ : Term}
    (ok₁ : SplitOk (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom)) (ok₂ : SplitOk (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom))
    (nr₂ : ∀ N, neg₂ = .map N → rs₂ = [])
    (hK : ∀ κ, SplitKey (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom) κ →
      SplitKey (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom) κ)
    (hA : ∀ a ∈ A₁, a ∈ A₂ ∨ SplitKey (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom) (.atom a)) {w : MW V}
    (h : KRS den M₁ rs₁ neg₁ Ds₁ A₁ v₁ keep w) : KRS den M₂ rs₂ neg₂ Ds₂ A₂ v₂ keep w := by
  classical
  obtain ⟨Dm₁, mDm₁, h⟩ := h
  have mDm₂ : ∀ d, d ∈ Ds₂.filter (fun d => decide (keep = Bool.true ∨ KindHeld M₂ d)) ↔
      d ∈ Ds₂ ∧ (keep = Bool.true ∨ KindHeld M₂ d) := fun d => by simp
  refine ⟨_, mDm₂, ?_⟩
  rcases h with h | ⟨a, ma, h⟩
  · exact Or.inl (upd_mono hM hv vne ok₁ ok₂ nr₂ hK mDm₁ mDm₂ h)
  · rcases hA a ma with m | k
    · exact Or.inr ⟨a, m, keepSemM_mono hM hv h⟩
    · left
      have ok₀ : SplitOk ([a].map Term.atom) (.atom "nil") (([] : List String).map Term.atom) :=
        ⟨by simp, Or.inl rfl, by simp, by simp⟩
      refine upd_mono (Dm₁ := []) hM hv vne ok₀ ok₂ nr₂ (fun κ hκ => ?_) (fun d => by simp) mDm₂
        (Or.inl ⟨rfl, Or.inl ⟨a, by simp, h⟩⟩)
      cases κ with
      | atom c =>
        rcases hκ with hκ | ⟨N, e, -⟩
        · simp at hκ; subst hκ; exact k
        · cases e
      | dom k' i => simp [SplitKey] at hκ

theorem foundG_weak {M : MW V → Prop} {rk Os : List String} {neg : Term} {Ds Do : List String} {md : String}
    {st : Bool} (h : FoundG M rk Os neg Ds Do md st) : FoundG M rk Os neg Ds Do md Bool.false := by
  rcases h with h | ⟨nf, h | h | ⟨a, ma, hv, -⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨nf, Or.inl h⟩
  · exact Or.inr ⟨nf, Or.inr (Or.inl h)⟩
  · exact Or.inr ⟨nf, Or.inr (Or.inr ⟨a, ma, hv, fun e => by cases e⟩)⟩

theorem foundG_mono {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u → M₂ u) {rk Os : List String} {neg : Term}
    {Ds Do : List String} {md : String} (h : FoundG M₁ rk Os neg Ds Do md Bool.false) :
    FoundG M₂ rk Os neg Ds Do md Bool.false := by
  rcases h with h | ⟨nf, ⟨x, w, hw, h⟩ | ⟨at', a, ma, w, x, hw, e⟩ | ⟨a, ma, ⟨w, x, hw, e⟩, -⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨nf, Or.inl ⟨x, w, hM w hw, h⟩⟩
  · exact Or.inr ⟨nf, Or.inr (Or.inl ⟨at', a, ma, w, x, hM w hw, e⟩)⟩
  · exact Or.inr ⟨nf, Or.inr (Or.inr ⟨a, ma, ⟨w, x, hM w hw, e⟩, fun e => by cases e⟩)⟩

theorem foundG_congr {M₁ M₂ : MW V → Prop} (hM : ∀ u, M₁ u ↔ M₂ u) {rk Os : List String} {neg : Term}
    {Ds Do : List String} {md : String} {st : Bool} (h : FoundG M₁ rk Os neg Ds Do md st) :
    FoundG M₂ rk Os neg Ds Do md st := by
  have e : M₁ = M₂ := funext fun u => propext (hM u)
  exact e ▸ h

end

section
variable {t : Term} {d : Nat}

/-- `map_update/5` of a value at a split with static-level semantics for every static value, on a gradual map type
of the next level: it gives a type exactly when the lower bound holds only maps and the upper bound some, and the
update of the upper bound finds a key (as a static update when the map type and the value are static); then the lower
bound holds, for a static value, the updates of the maps of the lower bound, the upper bound those of the value's
upper bound at the maps of the upper bound, and the same for the old values. -/
theorem upd_all_g {X : List (Term × Term)} (gX : GC (level t (d + 1)) (.map X)) {v : Term} (gv : GC (level t d) v)
    (dup : DE (level t d).E (upper v)) (vne : ∃ y : PN t d, denD (upper v) y) {key s : Term} {md : String} {m : Nat}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s) (hmd : Mode md)
    {OV : (MW (level t (d + 1)).V → Prop) → (level t (d + 1)).V → Prop}
    {S : Term → (MW (level t (d + 1)).V → Prop) → MW (level t (d + 1)).V → Prop}
    {F : (MW (level t (d + 1)).V → Prop) → Bool → Prop}
    (hS : ∀ x, DE (level t d).E x → (x = .atom "term" ∨ ∃ Z, x = .map Z) → (∃ y : PN t d, denD x y) →
      SUpd t (d + 1) s (cOp x Bool.false md) OV (S x) F)
    (ovE : ∀ M x, OV M x → ∃ w, M w)
    (ovm : ∀ M₁ M₂ : MW (level t (d + 1)).V → Prop, (∀ u, M₁ u → M₂ u) → ∀ x, OV M₁ x → OV M₂ x)
    (hSm : ∀ x (M₁ M₂ : MW (level t (d + 1)).V → Prop), DE (level t d).E x → (∃ y : PN t d, denD x y) →
      (∀ u, M₁ u → M₂ u) → ∀ w,
      S x M₁ w → S x M₂ w)
    (hm : (level t (d + 1)).K + 30 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key v (.atom md) (.atom "true") = .ok r ∧
      ((∃ T R er, r = .tuple #[T, R, er]) ↔ (∀ q : PN t (d + 1), denD (lower (.map X)) q → q.1.1 = "map") ∧
        (∃ w, MT t (d + 1) (dynL (upper (.map X))) w) ∧
        F (MT t (d + 1) (dynL (upper (.map X)))) ((mapLookup X (.atom "dynamic")).isNone && @decide (upper v = v) (Classical.propDecidable _))) ∧
      ∀ T R er, r = .tuple #[T, R, er] → GC (level t (d + 1)) R ∧
        (∀ q : PN t (d + 1), denD (upper R) q → q.1.1 = "map") ∧
        (∀ w, denD R (mpt (t := t) (n := d + 1) w) ↔ upper v = v ∧ (∃ u, MT t (d + 1) (rmDyn X) u) ∧
          S v (MT t (d + 1) (rmDyn X)) w) ∧
        (∀ w, denD (upper R) (mpt (t := t) (n := d + 1) w) ↔ S (upper v) (MT t (d + 1) (dynL (upper (.map X)))) w) ∧
        ∃ lt ut, Elixir.Module.Types.Descr.«lower_bound/1» (D m) T = .ok lt ∧
          Elixir.Module.Types.Descr.«upper_bound/1» (D m) T = .ok ut ∧ DE (level t d).E lt ∧ DE (level t d).E ut ∧
          (∀ x : PN t d, denD lt x ↔ upper v = v ∧ OV (MT t (d + 1) (rmDyn X)) x) ∧
          (∀ x : PN t d, denD ut x ↔ OV (MT t (d + 1) (dynL (upper (.map X)))) x) ∧
          ((mapLookup X (.atom "dynamic") = none ∧ upper v = v ∧ (level t (d + 1)).E T ∧
              ∀ x, (level t (d + 1)).den T x ↔ OV (MT t (d + 1) (rmDyn X)) x) ∨
            (¬(mapLookup X (.atom "dynamic") = none ∧ upper v = v) ∧ GC (level t d) T ∧
              (∀ x : PN t d, denD T x ↔ upper v = v ∧ OV (MT t (d + 1) (rmDyn X)) x) ∧
              ∀ x : PN t d, denD (upper T) x ↔ OV (MT t (d + 1) (dynL (upper (.map X)))) x)) := by
  have hmode : Term.atom md = .atom "force" ∨ Term.atom md = .atom "keep" ∨ Term.atom md = .atom "reject" := by
    rcases hmd with rfl | rfl | rfl <;> simp
  -- The static part's maps are among those of the upper bound.
  have inc : ∀ u, MT t (d + 1) (rmDyn X) u → MT t (d + 1) (dynL (upper (.map X))) u := fun u h =>
    (mt_dynL' gX.up_tc u).mpr (GC.inv gX _ ((denD_rmDyn X _).mp ((denD_mpt u).mpr h)))
  -- A static value updates the map type as it is.
  have static : ∀ {x : Term}, (x = .atom "term" ∨ ∃ Z, x = .map Z ∧ mapLookup Z (.atom "dynamic") = none) →
      DE (level t d).E x → (∃ y : PN t d, denD x y) →
      ∃ r, Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key x (.atom md) (.atom "true") = .ok r ∧
        ((∃ T R er, r = .tuple #[T, R, er]) ↔ (∀ q : PN t (d + 1), denD (lower (.map X)) q → q.1.1 = "map") ∧
          (∃ w, MT t (d + 1) (dynL (upper (.map X))) w) ∧
          F (MT t (d + 1) (dynL (upper (.map X)))) (mapLookup X (.atom "dynamic")).isNone) ∧
        ∀ T R er, r = .tuple #[T, R, er] → GC (level t (d + 1)) R ∧
          (∀ q : PN t (d + 1), denD (upper R) q → q.1.1 = "map") ∧
          (∀ w, denD R (mpt (t := t) (n := d + 1) w) ↔ (∃ u, MT t (d + 1) (rmDyn X) u) ∧
            S x (MT t (d + 1) (rmDyn X)) w) ∧
          (∀ w, denD (upper R) (mpt (t := t) (n := d + 1) w) ↔ S x (MT t (d + 1) (dynL (upper (.map X)))) w) ∧
          ∃ lt ut, Elixir.Module.Types.Descr.«lower_bound/1» (D m) T = .ok lt ∧
            Elixir.Module.Types.Descr.«upper_bound/1» (D m) T = .ok ut ∧ DE (level t d).E lt ∧ DE (level t d).E ut ∧
            (∀ x : PN t d, denD lt x ↔ OV (MT t (d + 1) (rmDyn X)) x) ∧
            (∀ x : PN t d, denD ut x ↔ OV (MT t (d + 1) (dynL (upper (.map X)))) x) ∧
            ((mapLookup X (.atom "dynamic") = none ∧ (level t (d + 1)).E T ∧
                ∀ x, (level t (d + 1)).den T x ↔ OV (MT t (d + 1) (rmDyn X)) x) ∨
              (mapLookup X (.atom "dynamic") ≠ none ∧ GC (level t d) T ∧
                (∀ x : PN t d, denD T x ↔ OV (MT t (d + 1) (rmDyn X)) x) ∧
                ∀ x : PN t d, denD (upper T) x ↔ OV (MT t (d + 1) (dynL (upper (.map X)))) x)) := by
    intro x sx dx nx
    have sx' : x = .atom "term" ∨ ∃ Z, x = .map Z := sx.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
    rw [upd5_val (.map X) hk hmode sx]
    obtain ⟨r, run, iff, sem⟩ := gupd_un gX (hS x dx sx' nx) ovE hm
    refine ⟨r, run, iff, fun T R er e => ?_⟩
    obtain ⟨g, o, l, u, lt, ut, rl, ru, dl, du, sl, su, kd⟩ := sem T R er e
    refine ⟨g, o, l, fun w => (u w).trans ⟨fun h => h.elim (fun ⟨_, h⟩ => hSm x _ _ dx nx inc w h) id, Or.inr⟩,
      lt, ut, rl, ru, dl, du, sl, fun y => (su y).trans ⟨fun h => h.elim (ovm _ _ inc y) id, Or.inr⟩,
      kd.imp id fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, fun y => (h₄ y).trans ⟨fun h => h.elim (ovm _ _ inc y) id,
        Or.inr⟩⟩⟩
  -- A static value: its upper bound is itself.
  have ofStatic : ∀ {x : Term}, upper x = x → (x = .atom "term" ∨ ∃ Z, x = .map Z ∧ mapLookup Z (.atom "dynamic") = none) →
      v = x → ∃ r, Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key v (.atom md) (.atom "true") = .ok r ∧
      ((∃ T R er, r = .tuple #[T, R, er]) ↔ (∀ q : PN t (d + 1), denD (lower (.map X)) q → q.1.1 = "map") ∧
        (∃ w, MT t (d + 1) (dynL (upper (.map X))) w) ∧
        F (MT t (d + 1) (dynL (upper (.map X)))) ((mapLookup X (.atom "dynamic")).isNone &&
          @decide (upper v = v) (Classical.propDecidable _))) ∧
      ∀ T R er, r = .tuple #[T, R, er] → GC (level t (d + 1)) R ∧
        (∀ q : PN t (d + 1), denD (upper R) q → q.1.1 = "map") ∧
        (∀ w, denD R (mpt (t := t) (n := d + 1) w) ↔ upper v = v ∧ (∃ u, MT t (d + 1) (rmDyn X) u) ∧
          S v (MT t (d + 1) (rmDyn X)) w) ∧
        (∀ w, denD (upper R) (mpt (t := t) (n := d + 1) w) ↔ S (upper v) (MT t (d + 1) (dynL (upper (.map X)))) w) ∧
        ∃ lt ut, Elixir.Module.Types.Descr.«lower_bound/1» (D m) T = .ok lt ∧
          Elixir.Module.Types.Descr.«upper_bound/1» (D m) T = .ok ut ∧ DE (level t d).E lt ∧ DE (level t d).E ut ∧
          (∀ x : PN t d, denD lt x ↔ upper v = v ∧ OV (MT t (d + 1) (rmDyn X)) x) ∧
          (∀ x : PN t d, denD ut x ↔ OV (MT t (d + 1) (dynL (upper (.map X)))) x) ∧
          ((mapLookup X (.atom "dynamic") = none ∧ upper v = v ∧ (level t (d + 1)).E T ∧
              ∀ x, (level t (d + 1)).den T x ↔ OV (MT t (d + 1) (rmDyn X)) x) ∨
            (¬(mapLookup X (.atom "dynamic") = none ∧ upper v = v) ∧ GC (level t d) T ∧
              (∀ x : PN t d, denD T x ↔ upper v = v ∧ OV (MT t (d + 1) (rmDyn X)) x) ∧
              ∀ x : PN t d, denD (upper T) x ↔ OV (MT t (d + 1) (dynL (upper (.map X)))) x)) := by
    intro x ux sx ev
    subst ev
    have e : @decide (upper v = v) (Classical.propDecidable _) = Bool.true := @decide_eq_true _ (Classical.propDecidable _) ux
    rw [e, Bool.and_true]
    obtain ⟨r, run, iff, sem⟩ := static sx (ux ▸ dup) (ux ▸ vne)
    refine ⟨r, run, iff, fun T R er e => ?_⟩
    obtain ⟨g, o, l, u, lt, ut, rl, ru, dl, du, sl, su, kd⟩ := sem T R er e
    refine ⟨g, o, fun w => (l w).trans ⟨fun h => ⟨ux, h⟩, fun h => h.2⟩, fun w => ux.symm ▸ u w,
      lt, ut, rl, ru, dl, du, fun y => (sl y).trans ⟨fun h => ⟨ux, h⟩, fun h => h.2⟩, su, ?_⟩
    rcases kd with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃, h₄⟩
    · exact Or.inl ⟨h₁, ux, h₂, h₃⟩
    · exact Or.inr ⟨fun h => h₁ h.1, h₂, fun y => (h₃ y).trans ⟨fun h => ⟨ux, h⟩, fun h => h.2⟩, h₄⟩
  rcases gv.cases with rfl | ⟨V, rfl, hV⟩ | ⟨V, rfl, hV⟩ | ⟨V, Y, rfl, hV, hY⟩
  · exact ofStatic rfl (Or.inl rfl) rfl
  · exact ofStatic (by simp [upper, hV]) (Or.inr ⟨V, rfl, hV⟩) rfl
  all_goals
    obtain ⟨Dv, hD⟩ : ∃ Dv, mapLookup V (.atom "dynamic") = some Dv := ⟨_, hV⟩
    have uV : upper (.map V) = Dv := upper_dyn hD
    have notS : upper (.map V) ≠ .map V := fun e => by
      have dup' := dup
      rw [uV] at dup' e
      rcases dup' with h | ⟨Z, h, sZ⟩
      · rw [e] at h; cases h
      · rw [e] at h; cases h; rw [sZ.static] at hD; cases hD
    have e : @decide (upper (.map V) = .map V) (Classical.propDecidable _) = Bool.false :=
      @decide_eq_false _ (Classical.propDecidable _) notS
    rw [e, Bool.and_false]
    have hdv : DE (level t d).E Dv := uV ▸ dup
    have sx : Dv = .atom "term" ∨ ∃ Z, Dv = .map Z := by
      rcases hdv with h | ⟨Z, h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨Z, h⟩
    have nx : ∃ y : PN t d, denD Dv y := uV ▸ vne
    have lowIff : (∀ q : PN t (d + 1), denD (lower (.map X)) q → q.1.1 = "map") ↔
        ∀ q : PN t (d + 1), denD (.map (rmDyn X)) q → q.1.1 = "map" :=
      ⟨fun h q hq => h q ((denD_lower _ _).mpr ((denD_rmDyn X q).mp hq)),
        fun h q hq => h q ((denD_rmDyn X q).mpr ((denD_lower _ _).mp hq))⟩
    rcases mo_cases gX (m := m) (by omega) with ⟨hmo, onlyS⟩ | ⟨hmo, nS⟩
    · rw [upd5_gval X hk hmode hD hmo]
      have gG : GC (level t (d + 1)) (.map (dynG X)) :=
        Or.inr ⟨_, upper (.map X), rfl, by simp [dynG, mapLookup, upper], gX.up_tc,
          by simp only [dynG, rmDyn_cons_dyn]; exact descrC_nil, fun q h => by
            have := (denD_rmDyn _ q).mpr h
            simp [dynG, rmDyn, denD_map, mapLookup, Elixir.STTDescrProofsTest.dn_none] at this⟩
      have hDG : mapLookup (dynG X) (.atom "dynamic") = some (upper (.map X)) := by
        simp [dynG, mapLookup, upper]
      have rG : rmDyn (dynG X) = [] := by simp [dynG, rmDyn]
      have uG : upper (.map (dynG X)) = upper (.map X) := upper_dyn hDG
      have noM : ∀ u, ¬MT t (d + 1) [] u := fun u h => by simp [MT, mapLookup] at h
      obtain ⟨r, run, iff, sem⟩ := gupd_un gG (hS Dv hdv sx nx) ovE hm
      rw [uG, hDG] at iff
      rw [uG, rG] at sem
      simp only [Option.isNone_some] at iff
      refine ⟨r, run, iff.trans ⟨fun ⟨_, h₂, h₃⟩ => ⟨lowIff.mpr onlyS, h₂, h₃⟩,
        fun ⟨_, h₂, h₃⟩ => ⟨fun q hq => ?_, h₂, h₃⟩⟩, fun T R er e' => ?_⟩
      · have := (denD_lower _ _).mp hq
        rw [← denD_rmDyn, rG] at this
        simp [denD_map, mapLookup, dn_none] at this
      obtain ⟨g, o, l, u, lt, ut, rl, ru, dl, du, sl, su, kd⟩ := sem T R er e'
      refine ⟨g, o, fun w => (l w).trans ⟨fun ⟨⟨u, hu⟩, _⟩ => absurd hu (noM u), fun h => absurd h.1 notS⟩,
        fun w => (u w).trans ?_, lt, ut, rl, ru, dl, du,
        fun y => (sl y).trans ⟨fun h => absurd (ovE _ _ h).choose_spec (noM _), fun h => absurd h.1 notS⟩,
        fun y => (su y).trans ⟨fun h => h.elim (fun h => absurd (ovE _ _ h).choose_spec (noM _)) id, Or.inr⟩, ?_⟩
      · rw [uV]
        exact ⟨fun h => h.elim (fun ⟨⟨u, hu⟩, _⟩ => absurd hu (noM u)) id, Or.inr⟩
      rcases kd with ⟨h₁, -⟩ | ⟨-, h₂, h₃, h₄⟩
      · simp [dynG, mapLookup] at h₁
      · exact Or.inr ⟨fun h => notS h.2, h₂,
          fun y => (h₃ y).trans ⟨fun h => absurd (ovE _ _ h).choose_spec (noM _), fun h => absurd h.1 notS⟩,
          fun y => (h₄ y).trans ⟨fun h => h.elim (fun h => absurd (ovE _ _ h).choose_spec (noM _)) id, Or.inr⟩⟩
    · rw [upd5_gval_bad X hk hmode hD hmo]
      exact ⟨_, rfl, ⟨fun ⟨_, _, _, h⟩ => (by cases h), fun ⟨h, _⟩ => absurd (lowIff.mp h) nS⟩,
        fun _ _ _ h => by cases h⟩


/-- Updating less precise maps with less precise values at a split with static-level semantics is less precise, as is
the old type. -/
theorem upd_prec {X : List (Term × Term)} {a₂ v v₂ : Term} (gX : GC (level t (d + 1)) (.map X))
    (g₂ : GC (level t (d + 1)) a₂) (gv : GC (level t d) v) (gv₂ : GC (level t d) v₂)
    (dup : DE (level t d).E (upper v)) (dup₂ : DE (level t d).E (upper v₂)) (vne : ∃ y : PN t d, denD (upper v) y)
    {key s : Term} {md : String} {m : Nat}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s) (hmd : Mode md)
    {OV : (MW (level t (d + 1)).V → Prop) → (level t (d + 1)).V → Prop}
    {S : Term → (MW (level t (d + 1)).V → Prop) → MW (level t (d + 1)).V → Prop}
    {F : (MW (level t (d + 1)).V → Prop) → Bool → Prop}
    (hS : ∀ x, DE (level t d).E x → (x = .atom "term" ∨ ∃ Z, x = .map Z) → (∃ y : PN t d, denD x y) →
      SUpd t (d + 1) s (cOp x Bool.false md) OV (S x) F)
    (ovE : ∀ M x, OV M x → ∃ w, M w)
    (ovm : ∀ M₁ M₂ : MW (level t (d + 1)).V → Prop, (∀ u, M₁ u → M₂ u) → ∀ x, OV M₁ x → OV M₂ x)
    (hmono : ∀ x₁ x₂ (M₁ M₂ : MW (level t (d + 1)).V → Prop), DE (level t d).E x₁ → DE (level t d).E x₂ →
      (∃ y : PN t d, denD x₁ y) → (∀ u, M₁ u → M₂ u) → (∀ y : PN t d, denD x₁ y → denD x₂ y) → ∀ w,
      S x₁ M₁ w → S x₂ M₂ w)
    (hSm : ∀ x (M₁ M₂ : MW (level t (d + 1)).V → Prop), DE (level t d).E x → (∃ y : PN t d, denD x y) →
      (∀ u, M₁ u → M₂ u) → ∀ w,
      S x M₁ w → S x M₂ w)
    (Fw : ∀ (M : MW (level t (d + 1)).V → Prop) st, F M st → F M Bool.false)
    (Fm : ∀ M₁ M₂ : MW (level t (d + 1)).V → Prop, (∀ u, M₁ u → M₂ u) → F M₁ Bool.false → F M₂ Bool.false)
    (Fc : ∀ M₁ M₂ : MW (level t (d + 1)).V → Prop, (∀ u, M₁ u ↔ M₂ u) → ∀ st, F M₁ st → F M₂ st)
    (hm : (level t (d + 1)).K + 30 ≤ m)
    (lo : ∀ q : PN t (d + 1), denD a₂ q → denD (.map X) q)
    (up : ∀ q : PN t (d + 1), denD (upper (.map X)) q → denD (upper a₂) q)
    (lov : ∀ y : PN t d, denD v₂ y → denD v y) (upv : ∀ y : PN t d, denD (upper v) y → denD (upper v₂) y)
    (kd : mapLookup X (.atom "dynamic") ≠ none → ∃ X₂, a₂ = .map X₂ ∧ mapLookup X₂ (.atom "dynamic") ≠ none)
    (kdv : upper v₂ = v₂ → upper v = v) {T R er : Term}
    (run : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key v (.atom md) (.atom "true") =
      .ok (.tuple #[T, R, er])) :
    ∃ T₂ R₂ er₂, Elixir.Module.Types.Descr.«map_update/5» (D m) a₂ key v₂ (.atom md) (.atom "true") =
        .ok (.tuple #[T₂, R₂, er₂]) ∧ «precise?/2» (D m) T T₂ = .ok (.atom "true") ∧
      «precise?/2» (D m) R R₂ = .ok (.atom "true") := by
  obtain ⟨r, run', iffA, semA⟩ := upd_all_g gX gv dup vne hk hmd hS ovE ovm hSm hm
  rw [run] at run'; cases run'
  obtain ⟨onlyA, neA, fA⟩ := iffA.mp ⟨_, _, _, rfl⟩
  have lo' : ∀ q : PN t (d + 1), denD (lower a₂) q → denD (lower (.map X)) q := fun q h =>
    (denD_lower _ _).mpr (lo q ((denD_lower _ _).mp h))
  obtain ⟨X₂, rfl⟩ : ∃ X₂, a₂ = .map X₂ := by
    rcases g₂.shape with rfl | ⟨X₂, rfl⟩
    · have := onlyA bitPt (lo' bitPt (by simp [lower, denD_term]))
      simp [bitPt] at this
    · exact ⟨X₂, rfl⟩
  have muA : ∀ w, MT t (d + 1) (dynL (upper (.map X))) w → MT t (d + 1) (dynL (upper (.map X₂))) w := fun w h =>
    (mt_dynL' g₂.up_tc w).mpr (up _ ((mt_dynL' gX.up_tc w).mp h))
  have msB : ∀ w, MT t (d + 1) (rmDyn X₂) w → MT t (d + 1) (rmDyn X) w := fun w h =>
    (denD_mpt w).mp ((denD_rmDyn X _).mpr (lo _ ((denD_rmDyn X₂ _).mp ((denD_mpt w).mpr h))))
  have vne₂ : ∃ y : PN t d, denD (upper v₂) y := let ⟨y, hy⟩ := vne; ⟨y, upv y hy⟩
  -- The less precise update finds a key.
  have fB : F (MT t (d + 1) (dynL (upper (.map X₂))))
      ((mapLookup X₂ (.atom "dynamic")).isNone && @decide (upper v₂ = v₂) (Classical.propDecidable _)) := by
    by_cases st₂ : ((mapLookup X₂ (.atom "dynamic")).isNone && @decide (upper v₂ = v₂) (Classical.propDecidable _)) =
        Bool.true
    · rw [st₂]
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at st₂
      obtain ⟨hD₂, ev₂⟩ := st₂
      have ev₂' : upper v₂ = v₂ := @of_decide_eq_true _ (Classical.propDecidable _) ev₂
      have hA : mapLookup X (.atom "dynamic") = none := Classical.byContradiction fun h => by
        obtain ⟨X₂', e, h'⟩ := kd h
        simp only [Term.map.injEq] at e; subst e; exact h' hD₂
      have st₁ : ((mapLookup X (.atom "dynamic")).isNone && @decide (upper v = v) (Classical.propDecidable _)) =
          Bool.true := by
        simp [hA, kdv ev₂']
      rw [st₁] at fA
      refine Fc _ _ (fun u => ⟨muA u, fun h => ?_⟩) _ fA
      have uX₂ : upper (.map X₂) = .map X₂ := by simp [upper, hD₂]
      have uX : upper (.map X) = .map X := by simp [upper, hA]
      rw [uX₂] at h; rw [uX]
      simp only [dynL] at h ⊢
      have := msB u (by rwa [rmDyn_static hD₂])
      rwa [rmDyn_static hA] at this
    · simp only [Bool.not_eq_true] at st₂
      rw [st₂]
      exact Fm _ _ muA (Fw _ _ fA)
  obtain ⟨r₂, run₂, iffB, semB⟩ := upd_all_g g₂ gv₂ dup₂ vne₂ hk hmd hS ovE ovm hSm hm
  obtain ⟨T₂, R₂, er₂, rfl⟩ := iffB.mpr ⟨fun q h => onlyA q (lo' q h), let ⟨w, hw⟩ := neA; ⟨w, muA w hw⟩, fB⟩
  obtain ⟨gR, oR, lR, uR, lt, ut, lA, uA, dlA, duA, slA, suA, -⟩ := semA T R er rfl
  obtain ⟨gR₂, oR₂, lR₂, uR₂, lt₂, ut₂, lB, uB, dlB, duB, slB, suB, -⟩ := semB T₂ R₂ er₂ rfl
  have hm' : (level t d).K + 23 ≤ m := by rw [level_K] at hm ⊢; omega
  refine ⟨T₂, R₂, er₂, run₂, precise_of_bounds (n := d) hm' lA uA lB uB dlA duA dlB duB
    (fun x h => (slA x).mpr (let ⟨e, h⟩ := (slB x).mp h; ⟨kdv e, ovm _ _ msB x h⟩))
    (fun x h => (suB x).mpr (ovm _ _ muA x ((suA x).mp h))), precise_of (n := d + 1) (by omega) gR gR₂ ?_ ?_⟩
  · refine via_mpt gR₂.shape gR.shape (fun q h => oR₂ q (GC.inv gR₂ q h)) fun w h => ?_
    obtain ⟨e₂, ⟨u, hu⟩, h⟩ := (lR₂ w).mp h
    have ne₂ : ∃ y : PN t d, denD v₂ y := let ⟨y, hy⟩ := vne₂; ⟨y, e₂ ▸ hy⟩
    exact (lR w).mpr ⟨kdv e₂, ⟨u, msB u hu⟩, hmono v₂ v _ _ (e₂ ▸ dup₂) (kdv e₂ ▸ dup) ne₂ msB lov w h⟩
  · refine via_mpt (Or.imp id (fun ⟨Y, e, _⟩ => ⟨Y, e⟩) gR.up_tc) (Or.imp id (fun ⟨Y, e, _⟩ => ⟨Y, e⟩) gR₂.up_tc)
      oR fun w h => ?_
    exact (uR₂ w).mpr (hmono _ _ _ _ dup dup₂ vne muA upv w ((uR w).mp h))


/-- `map_update/5` at a gradual key type of the laws: less precise maps and values give a less precise result and old
type. -/
theorem upd_prec_key {X : List (Term × Term)} {a₂ v v₂ : Term} (gX : GC (level t (d + 1)) (.map X))
    (g₂ : GC (level t (d + 1)) a₂) (gv : GC (level t d) v) (gv₂ : GC (level t d) v₂)
    (dup : DE (level t d).E (upper v)) (dup₂ : DE (level t d).E (upper v₂)) (vne : ∃ y : PN t d, denD (upper v) y)
    {key : Term} {md : String} {m : Nat} (hmk : (level t d).K + 23 ≤ m)
    (hk' : «arrows_gradual?/2» (D (m + 1)) key (.tuple #[.integer d, t]) = .ok (.atom "true")) (hmd : Mode md)
    (hm : (level t (d + 1)).K + 30 ≤ m + 1)
    (lo : ∀ q : PN t (d + 1), denD a₂ q → denD (.map X) q)
    (up : ∀ q : PN t (d + 1), denD (upper (.map X)) q → denD (upper a₂) q)
    (lov : ∀ y : PN t d, denD v₂ y → denD v y) (upv : ∀ y : PN t d, denD (upper v) y → denD (upper v₂) y)
    (kd : mapLookup X (.atom "dynamic") ≠ none → ∃ X₂, a₂ = .map X₂ ∧ mapLookup X₂ (.atom "dynamic") ≠ none)
    (kdv : upper v₂ = v₂ → upper v = v) {T R er : Term}
    (run : Elixir.Module.Types.Descr.«map_update/5» (D (m + 1)) (.map X) key v (.atom md) (.atom "true") =
      .ok (.tuple #[T, R, er])) :
    ∃ T₂ R₂ er₂, Elixir.Module.Types.Descr.«map_update/5» (D (m + 1)) a₂ key v₂ (.atom md) (.atom "true") =
        .ok (.tuple #[T₂, R₂, er₂]) ∧ «precise?/2» (D (m + 1)) T T₂ = .ok (.atom "true") ∧
      «precise?/2» (D (m + 1)) R R₂ = .ok (.atom "true") := by
  obtain ⟨s, hk, hs⟩ := key_gform (t := t) (n := d) hmk hk'
  obtain ⟨rk, Os, ng, Ds, Do, rfl, gs, hkey⟩ := gform_strs hs
  have ef := (level t (d + 1)).ef
  have ovE : ∀ (M : MW (level t (d + 1)).V → Prop) x, Vals M (KeyPt t d (upper key)) x → ∃ w, M w :=
    fun M x ⟨w, hw, _⟩ => ⟨w, hw⟩
  have ovm : ∀ M₁ M₂ : MW (level t (d + 1)).V → Prop, (∀ u, M₁ u → M₂ u) → ∀ x,
      Vals M₁ (KeyPt t d (upper key)) x → Vals M₂ (KeyPt t d (upper key)) x := fun M₁ M₂ h x => vals_mono h
  have dn : ∀ {x : Term}, DE (level t d).E x → ∀ y, (level t (d + 1)).den x y ↔ denD x y := fun dx y => den_succ dx y
  have toE : ∀ {x : Term}, DE (level t d).E x → (level t (d + 1)).E x := fun dx => Or.inl dx
  have toS : ∀ {x : Term}, DE (level t d).E x → x = .atom "term" ∨ ∃ Z, x = .map Z := fun dx => by
    rcases dx with h | ⟨Z, h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨Z, h⟩
  rcases hmd with rfl | rfl | rfl
  · obtain ⟨s', neg, Ss, rk', na, hP, oks, -⟩ := key_gsplit (t := t) (n := d) hmk hk'
    rw [hk] at rk'; cases rk'
    refine upd_prec gX g₂ gv gv₂ dup dup₂ vne hk (Or.inl rfl)
      (S := fun x M w => PutAny Ss (level t (d + 1)).den M x w)
      (fun x dx sx ⟨y, hy⟩ => supd_val gs hkey (toE dx) sx ⟨y, (dn dx y).mpr hy⟩ (Or.inl rfl)
        (force_hY hP na (toE dx) sx)) ovE ovm ?_ ?_ (fun M st h => foundG_weak h) (fun M₁ M₂ h f => foundG_mono h f)
      (fun M₁ M₂ h st f => foundG_congr h f) hm lo up lov upv kd kdv run
    · intro x₁ x₂ M₁ M₂ d₁ d₂ _ hM hv w ⟨sp, msp, h⟩
      exact ⟨sp, msp, put_mono hM (fun y hy => (dn d₂ y).mpr (hv y ((dn d₁ y).mp hy))) (oks sp msp).1 (oks sp msp).1
        (oks sp msp).2 (fun _ h => h) h⟩
    · intro x M₁ M₂ _ _ hM w ⟨sp, msp, h⟩
      exact ⟨sp, msp, put_mono hM (fun y hy => hy) (oks sp msp).1 (oks sp msp).1 (oks sp msp).2 (fun _ h => h) h⟩
  · obtain ⟨rs, neg, D2, A, ⟨ok2, nr2, -⟩, hY⟩ := kr_hY (t := t) (n := d + 1) hs Bool.true
    refine upd_prec gX g₂ gv gv₂ dup dup₂ vne hk (Or.inr (Or.inl rfl))
      (S := fun x M w => KRS (level t (d + 1)).den M rs neg D2 A x Bool.true w)
      (fun x dx sx ⟨y, hy⟩ => supd_val gs hkey (toE dx) sx ⟨y, (dn dx y).mpr hy⟩ (mode_modeS Bool.true)
        (hY (toE dx) sx ⟨y, (dn dx y).mpr hy⟩)) ovE ovm ?_ ?_ (fun M st h => foundG_weak h)
      (fun M₁ M₂ h f => foundG_mono h f) (fun M₁ M₂ h st f => foundG_congr h f) hm lo up lov upv kd kdv run
    · intro x₁ x₂ M₁ M₂ d₁ d₂ ⟨y, hy⟩ hM hv w h
      exact krs_mono hM (fun y hy => (dn d₂ y).mpr (hv y ((dn d₁ y).mp hy))) ⟨y, (dn d₁ y).mpr hy⟩ ok2 ok2 nr2
        (fun κ h => h) (fun a m => Or.inl m) h
    · intro x M₁ M₂ dx ⟨y, hy⟩ hM w h
      exact krs_mono hM (fun y hy => hy) ⟨y, (dn dx y).mpr hy⟩ ok2 ok2 nr2 (fun κ h => h) (fun a m => Or.inl m) h
  · obtain ⟨rs, neg, D2, A, ⟨ok2, nr2, -⟩, hY⟩ := kr_hY (t := t) (n := d + 1) hs Bool.false
    refine upd_prec gX g₂ gv gv₂ dup dup₂ vne hk (Or.inr (Or.inr rfl))
      (S := fun x M w => KRS (level t (d + 1)).den M rs neg D2 A x Bool.false w)
      (fun x dx sx ⟨y, hy⟩ => supd_val gs hkey (toE dx) sx ⟨y, (dn dx y).mpr hy⟩ (mode_modeS Bool.false)
        (hY (toE dx) sx ⟨y, (dn dx y).mpr hy⟩)) ovE ovm ?_ ?_ (fun M st h => foundG_weak h)
      (fun M₁ M₂ h f => foundG_mono h f) (fun M₁ M₂ h st f => foundG_congr h f) hm lo up lov upv kd kdv run
    · intro x₁ x₂ M₁ M₂ d₁ d₂ ⟨y, hy⟩ hM hv w h
      exact krs_mono hM (fun y hy => (dn d₂ y).mpr (hv y ((dn d₁ y).mp hy))) ⟨y, (dn d₁ y).mpr hy⟩ ok2 ok2 nr2
        (fun κ h => h) (fun a m => Or.inl m) h
    · intro x M₁ M₂ dx ⟨y, hy⟩ hM w h
      exact krs_mono hM (fun y hy => hy) ⟨y, (dn dx y).mpr hy⟩ ok2 ok2 nr2 (fun κ h => h) (fun a m => Or.inl m) h

end



section
variable {t : Term} {n : Nat}

/-- The maps of a delete at a static split, with required atoms `A` inside a negated set: the deletions at the split,
at the kinds of `Ds` held unless rejecting, and at each atom of `A`. -/
def DRS {V : Type} (den : Term → V → Prop) (M : MW V → Prop) (rs : List String) (neg : Term) (Ds A : List String) (md : String) (w : MW V) :
    Prop :=
  ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨ KindHeld M d)) ∧
    (UpdSemD den M rs neg Dm md w ∨ ∃ a ∈ A, DelAt M md a w)

/-- Deleting at a gradual split, on a static map type, for either flag: the maps of a static split of the same keys,
fixed by the split. -/
theorem dl_gx {s : Term} {KP : MKey → Prop} (hs : GForm s KP) {md : String} (hmd : Mode md) :
    ∃ (rs : List String) (neg : Term) (Ds A : List String), KSplit rs neg Ds A KP ∧
      ∀ {X : List (Term × Term)}, DE (level t n).E (.map X) → ∀ (st : Term) {m : Nat},
        (level t n).K + 30 ≤ m → ∀ {T Y er f : Term},
        Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X) s (cOp (.map []) Bool.true md) (.atom "true") st =
          .ok (.tuple #[T, Y, er, f]) →
        ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (Y' = [] ∨ ∃ r, Y' = [(.atom "map", r)]) ∧
          ((∃ u, MT t n X u) → ∀ w, MT t n Y' w ↔ DRS (level t n).den (MT t n X) rs neg Ds A md w) := by
  obtain ⟨s', hs', HR⟩ := dnf_gform_relB hs _ hmd
  -- The static split and its shape.
  obtain ⟨rs, neg, Ds, A, ks, es⟩ : ∃ (rs : List String) (neg : Term) (Ds A : List String), KSplit rs neg Ds A KP ∧
      s' = splitT ((rs ++ A).map Term.atom) neg (Ds.map Term.atom) := by
    rcases hs' with ⟨rs, Ds, rfl, ok, sk⟩ | ⟨N, Ds, rfl, ok, na, sk⟩ | ⟨A, N, Ds, rfl, ok, na, hA, sk⟩
    · obtain ⟨rs', rfl⟩ := strs_of ok.hrs
      obtain ⟨Ds', rfl, -⟩ := ds_of ok.hds
      refine ⟨rs', _, Ds', [], ⟨ok, ?_, ?_, fun _ => rfl, ?_, fun κ => by simpa using sk κ⟩, by simp⟩
      · intro N e; cases e
      · intro N e; cases e
      · intro N e; cases e
    · obtain ⟨Ds', rfl, -⟩ := ds_of ok.hds
      refine ⟨[], _, Ds', [], ⟨by simpa using ok, fun _ _ => rfl, ?_, ?_, ?_, fun κ => by simpa using sk κ⟩, by simp⟩
      · intro N' e; cases e; exact na
      · intro e; cases e
      · intro _ _ a m; simp at m
    · obtain ⟨Ds', rfl, -⟩ := ds_of ok.hds
      refine ⟨[], _, Ds', A, ⟨by simpa using ok, fun _ _ => rfl, ?_, ?_, ?_, fun κ => by simpa using sk κ⟩, by simp⟩
      · intro N' e; cases e; exact na
      · intro e; cases e
      · intro N' e; cases e; exact hA
  refine ⟨rs, neg, Ds, A, ks, ?_⟩
  obtain ⟨ok, nr, na, hA0, hA, -⟩ := ks
  subst es
  intro X hX st m hm T Y er f run
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
  have ef := (level t n).ef
  have sX := de_map hX
  have eop : cOp (.map []) Bool.true md = .tuple #[.tuple #[.atom "constant", .tuple #[.map [], .atom "true"]],
      .atom md] := rfl
  have conv : ∀ {b : Term}, mapLookup X (.atom "map") = some b →
      (fun u => denMF (level t n).E (level t n).den b u = Bool.true) = MT t n X := fun hb =>
    funext fun u => propext (by simp [MT, hb])
  have hDs : ∀ s ∈ Ds, s ∈ domainKinds := fun s ms => by
    obtain ⟨s', ms', e⟩ := ok.hds _ (List.mem_map_of_mem ms); cases e; exact ms'
  -- The updates for a list of kinds with the same members agree.
  have dmEq : ∀ {Dm Dm' : List String}, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (md ≠ "reject" ∨ KindHeld (MT t n X) d)) →
      (∀ d, d ∈ Dm' ↔ d ∈ Ds ∧ (md ≠ "reject" ∨ KindHeld (MT t n X) d)) → ∀ w,
      UpdSemD (level t n).den (MT t n X) rs neg Dm' md w → UpdSemD (level t n).den (MT t n X) rs neg Dm md w :=
    fun mDm mDm' w h => del_mono (level t n).ef.den_none (fun u h => h) hmd ok ok nr (fun κ h => h) mDm' mDm h
  cases hb : mapLookup X (.atom "map") with
  | none =>
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at run
    simp [getMapKeys_single, hb] at run
    obtain ⟨-, rfl, -⟩ := run
    exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun ⟨u, hu⟩ => by simp [MT, hb] at hu⟩
  | some b =>
  have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
  have rel := fun {r} (h : Elixir.Module.Types.Descr.«map_update_static/5» (D (k + 8)) (.map X)
      (splitT ((rs ++ A).map Term.atom) neg (Ds.map Term.atom)) (cOp (.map []) Bool.true md)
      (.atom "true") (.atom "true") = .ok r) => static_split_rel (k + 6) (.map X) s _ (cOp (.map []) Bool.true md) st (.atom "true")
        (fun bdd dnf r₁ r₂ h₁ h₂ => HR (k + 6) bdd dnf _ st (.atom "true") (by rw [eop] at h₁; exact h₁)
          (by rw [eop] at h₂; exact h₂)) run h
  have toY : ∀ {r Yr : Term} {S : MW (level t n).V → Prop}, (.tuple #[T, Y, er, f] = r ∨ RelB (.tuple #[T, Y, er, f]) r) →
      (∃ T' er' f', r = .tuple #[T', Yr, er', f']) → MapsY (level t n).E (level t n).den Yr S →
      (∀ w, S w ↔ DRS (level t n).den (MT t n X) rs neg Ds A md w) →
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (Y' = [] ∨ ∃ r, Y' = [(.atom "map", r)]) ∧
        ((∃ u, MT t n X u) → ∀ w, MT t n Y' w ↔ DRS (level t n).den (MT t n X) rs neg Ds A md w) := by
    rintro r Yr S hr ⟨T', er', f', rfl⟩ hY hS
    have eY : Yr = Y := by
      rcases hr with e | ⟨_, bd, _, _, _, _, _, e₁, e₂⟩
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e; exact e.2.1.symm
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e₁ e₂; rw [e₂.2.1, ← e₁.2.1]
    subst eY
    rcases hY with ⟨rfl, emp⟩ | ⟨r', rfl, fr, sr⟩
    · exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, Or.inl rfl, fun _ w =>
        ⟨fun h => by simp [MT, mapLookup] at h, fun h => absurd ((hS w).mpr h) (emp w)⟩⟩
    · refine ⟨_, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, Or.inr ⟨_, rfl⟩, fun _ w => ?_⟩
      rw [← hS w, ← sr w]
      simp [MT, mapLookup]
  rcases ok.hneg with rfl | ⟨N, rfl⟩
  · obtain rfl := hA0 rfl
    obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
      del_update_static ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hmd Bool.true ok nr na hb fb
    · rcases rel (by simpa [show k + 2 + 6 = k + 8 by omega] using rr) with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
    · rw [conv hb] at hY mDm
      exact toY (rel (by simpa [show k + 2 + 6 = k + 8 by omega] using rr)) ⟨_, _, _, rfl⟩ hY fun w =>
        ⟨fun h => ⟨Dm, mDm, Or.inl h⟩, fun ⟨Dm', mDm', h⟩ => h.elim (dmEq mDm mDm' w) fun ⟨a, ma, _⟩ => by simp at ma⟩
  · have hat : "atom" ∈ Ds := by
      obtain ⟨s, ms, e⟩ := List.mem_map.mp (ok.hatom.mpr ⟨N, rfl⟩); cases e; exact ms
    obtain rfl := nr N rfl
    obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
      del_update_static_req ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hmd (A := A) rfl hDs hat
        (hA N rfl) na hb fb
    · rcases rel (by simpa [show k + 2 + 6 = k + 8 by omega] using rr) with e | ⟨_, _, _, _, _, _, _, -, e⟩ <;> cases e
    · rw [conv hb] at hY mDm
      exact toY (rel (by simpa [show k + 2 + 6 = k + 8 by omega] using rr)) ⟨_, _, _, rfl⟩ hY fun w =>
        ⟨fun h => ⟨Dm, mDm, h⟩, fun ⟨Dm', mDm', h⟩ => h.imp_left (dmEq mDm mDm' w)⟩


end


section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem dnf_gvf_del (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n)
    {b : Term} (fb : MField E b) (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w)
    (sl : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {rk Os : List String} {neg : Term}
    {Ds Do : List String} (gs : GSplit rk Os neg Ds Do) {md : String} (hmd : Mode md) (st : Bool) {r : Term}
    (h : Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) b (Term.list lines) (gsT rk Os neg Ds Do)
      (cOp (.map []) Bool.true md) (.atom "true") (boolAtom st) = .ok r) :
    ∃ T Y el f, r = .tuple #[T, Y, Term.list el, boolAtom f] ∧ E T ∧
      (∀ x, den T x ↔ ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, GKey rk Os neg Ds Do κ ∧ w κ = some x) ∧
      (f = Bool.true ↔ FoundG (fun u => denMF E den b u = Bool.true) rk Os neg Ds Do md st) := by
  have hD : ∀ s ∈ Ds ++ Do, s ∈ domainKinds := fun s ms => by
    obtain ⟨s', ms', e⟩ := gs.ok.hds _ (List.mem_map_of_mem ms); cases e; exact ms'
  have hk : ∀ (bd : Bool) a, ∃ (ba : List Term) (F : Term), Elixir.Module.Types.Descr.«map_update_named_key/5»
      (D (n + 5)) (Term.list lines) (.atom a) (.tuple #[.tuple #[.atom "constant", .tuple #[.map [], boolAtom Bool.true]],
        .atom md]) (boolAtom bd) (.atom "true") = .ok (.tuple #[Term.list ba, F]) ∧ FieldValue E F ∧
      ∀ o, FieldSem den F o ↔ ∃ L ∈ lines, LongM den L a o := fun bd a =>
    hk_del ef (n := n + 2) (by omega) hmd lines hl bd a
  obtain ⟨R, rR, hR, swR⟩ := neg_keys_split ef fb (n + 5) gs.ok
  obtain ⟨R', rfl⟩ := atoms_strs fun r mr => let ⟨s, e, _⟩ := hR r mr; ⟨s, e⟩
  obtain ⟨T, Y, er, f, rfl, hT, sT⟩ := dnf_val_g ef hn (.tuple #[.map [], boolAtom Bool.true]) md hmd b lines hl rk Os neg
    Ds Do (fun s ms => hD s (List.mem_append_left _ ms)) R' (boolAtom st) rR
    (fun bd a r hr => by
      obtain ⟨ba, F, e, hF, sF⟩ := hk bd a
      rw [e] at hr; cases hr; exact ⟨_, F, rfl, hF, sF⟩) r h
  obtain ⟨T', Y', el, f', e, nf, ff⟩ := dnf_flag_g ef hn (.tuple #[.map [], boolAtom Bool.true]) hmd st b lines hl rk Os
    neg Ds Do (fun s ms => hD s (List.mem_append_left _ ms)) (fun s ms => hD s (List.mem_append_right _ ms)) R' rR
    hk _ h
  simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, and_true] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  have pe := fun x => pieces_sem ef lines hl sl gs.ok hR swR x
  have lm := fun a o => longM_iff (E := E) (den := den) sl a o
  -- An atom outside the negated set means the split holds the atom kind.
  have rAt : ∀ a ∈ R', "atom" ∈ Ds ++ Do := fun a ma => by
    obtain ⟨s, e, N, eN, -⟩ := hR _ (List.mem_map_of_mem ma)
    obtain ⟨s', ms', e'⟩ := List.mem_map.mp (gs.ok.hatom.mpr ⟨N, eN⟩)
    cases e'; exact ms'
  have gk : ∀ x, (∃ w, denMF E den b w = Bool.true ∧ ∃ κ, GKey rk Os neg Ds Do κ ∧ w κ = some x) ↔
      (∃ a, (a ∈ rk ∨ a ∈ Os) ∧ ∃ L ∈ lines, LongM den L a (some x)) ∨
        ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, SplitKey [] neg ((Ds ++ Do).map Term.atom) κ ∧ w κ = some x := by
    intro x
    constructor
    · rintro ⟨w, hw, κ, ⟨a, ma, rfl⟩ | hκ, e⟩
      · exact Or.inl ⟨a, ma, (lm a _).mpr ⟨w, hw, e⟩⟩
      · exact Or.inr ⟨w, hw, κ, hκ, e⟩
    · rintro (⟨a, ma, h⟩ | ⟨w, hw, κ, hκ, e⟩)
      · obtain ⟨w, hw, e⟩ := (lm a _).mp h
        exact ⟨w, hw, _, Or.inl ⟨a, ma, rfl⟩, e⟩
      · exact ⟨w, hw, κ, Or.inr hκ, e⟩
  have pe' : ∀ x, ((∃ s ∈ R', ∃ L ∈ lines, LongM den L s (some x)) ∨
      ∃ kind, (kind ∈ Ds ∨ kind ∈ Do) ∧ ∃ L ∈ lines, LineTag den L kind x) ↔
      ∃ w, denMF E den b w = Bool.true ∧ ∃ κ, SplitKey [] neg ((Ds ++ Do).map Term.atom) κ ∧ w κ = some x := by
    intro x
    rw [← pe x]
    simp only [List.mem_map, Term.atom.injEq, exists_eq_right, List.not_mem_nil, false_and, exists_false, false_or,
      List.mem_append]
  refine ⟨T, Y, el, f', rfl, hT, fun x => (sT x).trans ?_, ?_⟩
  · rw [gk, ← pe']
    constructor
    · rintro (⟨s, ms, hh⟩ | ⟨a, (ma | ma | ma), hh⟩)
      · exact Or.inr (Or.inr ⟨s, ms, hh⟩)
      · exact Or.inl ⟨a, Or.inl ma, hh⟩
      · exact Or.inl ⟨a, Or.inr ma, hh⟩
      · exact Or.inr (Or.inl ⟨a, ma, hh⟩)
    · rintro (⟨a, ma, hh⟩ | ⟨a, ma, hh⟩ | ⟨s, ms, hh⟩)
      · exact Or.inr ⟨a, ma.imp_right Or.inl, hh⟩
      · exact Or.inr ⟨a, Or.inr (Or.inr ma), hh⟩
      · exact Or.inl ⟨s, ms, hh⟩
  · by_cases hf : md = "force"
    · subst hf
      rw [ff rfl]
      simp only [FoundG, true_and, ne_eq, not_true_eq_false, false_and, or_false]
      constructor
      · rintro (h | h | h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · obtain ⟨a, ma⟩ := List.exists_mem_of_ne_nil _ h
          exact Or.inl (List.ne_nil_of_mem (rAt a ma))
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
    · rw [nf hf]
      simp only [FoundG, hf, false_and, false_or, ne_eq, not_false_eq_true, true_and]
      have none_iff : ∀ a, (¬∃ L ∈ lines, LongM den L a none) ↔
          ∀ w, denMF E den b w = Bool.true → w (.atom a) ≠ none := fun a => by
        rw [lm a none]; simp
      have some_iff : ∀ a, (∃ L ∈ lines, ∃ x, LongM den L a (some x)) ↔
          ∃ w x, denMF E den b w = Bool.true ∧ w (.atom a) = some x := fun a => by
        constructor
        · rintro ⟨L, mL, x, h⟩
          obtain ⟨w, hw, e⟩ := (lm a _).mp ⟨L, mL, h⟩; exact ⟨w, x, hw, e⟩
        · rintro ⟨w, x, hw, e⟩
          obtain ⟨L, mL, h⟩ := (lm a _).mpr ⟨w, hw, e⟩; exact ⟨L, mL, x, h⟩
      have s1 : (∃ x w, denMF E den b w = Bool.true ∧ ∃ κ, SplitKey [] neg ((Ds ++ Do).map Term.atom) κ ∧
          w κ = some x) ↔ (∃ a ∈ R', ∃ L ∈ lines, ∃ x, LongM den L a (some x)) ∨
          ∃ s, (s ∈ Ds ∨ s ∈ Do) ∧ ∃ L ∈ lines, ∃ x, LineTag den L s x := by
        constructor
        · rintro ⟨x, hx⟩
          rcases (pe' x).mpr hx with ⟨a, ma, L, mL, h⟩ | ⟨s, ms, L, mL, h⟩
          · exact Or.inl ⟨a, ma, L, mL, x, h⟩
          · exact Or.inr ⟨s, ms, L, mL, x, h⟩
        · rintro (⟨a, ma, L, mL, x, h⟩ | ⟨s, ms, L, mL, x, h⟩)
          · exact ⟨x, (pe' x).mp (Or.inl ⟨a, ma, L, mL, h⟩)⟩
          · exact ⟨x, (pe' x).mp (Or.inr ⟨s, ms, L, mL, h⟩)⟩
      rw [s1]
      constructor
      · rintro (h | ⟨hat, a, (ma | ma | ma), h⟩ | ⟨a, (ma | ma | ma), h, hn⟩)
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inl ⟨hat, a, Or.inl ma, (some_iff a).mp h⟩)
        · exact Or.inr (Or.inl ⟨hat, a, Or.inr ma, (some_iff a).mp h⟩)
        · exact Or.inl (Or.inl ⟨a, ma, h⟩)
        · exact Or.inr (Or.inr ⟨a, Or.inl ma, (some_iff a).mp h, fun e => (none_iff a).mp (hn e)⟩)
        · exact Or.inr (Or.inr ⟨a, Or.inr ma, (some_iff a).mp h, fun e => (none_iff a).mp (hn e)⟩)
        · exact Or.inl (Or.inl ⟨a, ma, h⟩)
      · rintro ((⟨a, ma, h⟩ | h) | ⟨hat, a, ma, h⟩ | ⟨a, ma, h, hn⟩)
        · exact Or.inr (Or.inl ⟨rAt a ma, a, Or.inr (Or.inr ma), h⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨hat, a, ma.imp_right Or.inl, (some_iff a).mpr h⟩)
        · exact Or.inr (Or.inr ⟨a, ma.imp_right Or.inl, (some_iff a).mpr h, fun e => (none_iff a).mpr (hn e)⟩)


end


section
variable {t : Term} {n : Nat}

/-- A delete at the split of a gradual key, on the static map types of a level: the old values at the keys, the found
flag `FoundG`, and the maps a hypothesis gives. -/
theorem supd_del {rk Os : List String} {ng : Term} {Ds Do : List String} (gs : GSplit rk Os ng Ds Do)
    {KP : MKey → Prop} (hk : ∀ κ, GKey rk Os ng Ds Do κ ↔ KP κ) {md : String} (hmd : Mode md)
    {S : (MW (level t n).V → Prop) → MW (level t n).V → Prop}
    (hY : ∀ X : List (Term × Term), DE (level t n).E (.map X) → ∀ (st : Bool) (m : Nat), (level t n).K + 30 ≤ m →
      ∀ T Y er f, Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X) (gsT rk Os ng Ds Do)
        (cOp (.map []) Bool.true md) (.atom "true") (boolAtom st) = .ok (.tuple #[T, Y, er, f]) →
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (∀ q : PN t n, denD (.map Y') q → q.1.1 = "map") ∧
        ((∃ u, MT t n X u) → ∀ w, MT t n Y' w ↔ S (MT t n X) w)) :
    SUpd t n (gsT rk Os ng Ds Do) (cOp (.map []) Bool.true md) (fun M x => Vals M KP x) S
      (fun M st => FoundG M rk Os ng Ds Do md st) := by
  intro Z hZ st m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
  have ef := (level t n).ef
  have sZ := de_map hZ
  cases hb : mapLookup Z (.atom "map") with
  | none =>
    refine ⟨_, ?_, Or.inl ⟨Or.inr rfl, fun w h => by simp [MT, hb] at h⟩⟩
    unfold Elixir.Module.Types.Descr.«map_update_static/5»
    simp [getMapKeys_single, hb]
  | some b =>
  have fb : MField (level t n).E b := fieldC_map (sZ.fields "map" b hb)
  have conv : (fun u => denMF (level t n).E (level t n).den b u = Bool.true) = MT t n Z :=
    funext fun u => propext (by simp [MT, hb])
  obtain ⟨res, run, hres⟩ := static_lift ef (n := k + 2) (by omega) (s := gsT rk Os ng Ds Do)
    (op := cOp (.map []) Bool.true md) (rt := .atom "true") (st := boolAtom st) hb fb
    (fun r => ∃ T Y el f, r = .tuple #[T, Y, Term.list el, boolAtom f] ∧ (level t n).E T ∧
      (∀ x, (level t n).den T x ↔ ∃ w, denMF (level t n).E (level t n).den b w = Bool.true ∧
        ∃ κ, GKey rk Os ng Ds Do κ ∧ w κ = some x) ∧
      (f = Bool.true ↔ FoundG (fun u => denMF (level t n).E (level t n).den b u = Bool.true) rk Os ng Ds Do md st))
    fun lines hl hne sl => by
      obtain ⟨r, rr⟩ := dnf_ok_g ef (n := k + 2) (by omega) ef.none (Or.inr ⟨[], rfl⟩) Bool.true hmd fb lines hl sl gs.ok
        gs.na st fun bd a => pk_del ef (n := k + 4) (by omega) hmd lines hl bd a
      exact ⟨r, rr, dnf_gvf_del ef (n := k + 2) (by omega) fb lines hl sl gs hmd st rr⟩
  refine ⟨res, run, ?_⟩
  rcases hres with ⟨rfl, emp⟩ | ⟨ex, T, Y, el, f, rfl, hT, sT, sf⟩
  · exact Or.inl ⟨Or.inl rfl, fun w h => by simp [MT, hb, emp w] at h⟩
  obtain ⟨Y', rfl, dY, shY, sY⟩ := hY Z hZ _ _ hm _ _ _ _ run
  rw [conv] at sf
  have mt : ∀ w, MT t n Z w ↔ denMF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [MT, hb]
  have ex' : ∃ w, MT t n Z w := let ⟨w, hw⟩ := ex; ⟨w, (mt w).mpr hw⟩
  refine Or.inr ⟨ex', T, Y', el, f, rfl, hT, fun x => (sT x).trans ?_, dY, shY, sY ex', sf⟩
  exact ⟨fun ⟨w, hw, κ, hκ, e⟩ => ⟨w, (mt w).mpr hw, κ, (hk κ).mp hκ, e⟩,
    fun ⟨w, hw, κ, hκ, e⟩ => ⟨w, (mt w).mp hw, κ, (hk κ).mpr hκ, e⟩⟩


end


section
variable {t : Term} {n : Nat}

/-- The maps of deleting at a gradual split, as `supd_del` takes them. -/
theorem dl_hY {s : Term} {KP : MKey → Prop} (hs : GForm s KP) {md : String} (hmd : Mode md) :
    ∃ (rs : List String) (neg : Term) (Ds A : List String), KSplit rs neg Ds A KP ∧
      ∀ X : List (Term × Term), DE (level t n).E (.map X) → ∀ (st : Bool) (m : Nat), (level t n).K + 30 ≤ m →
      ∀ T Y er f, Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X) s
        (cOp (.map []) Bool.true md) (.atom "true") (boolAtom st) = .ok (.tuple #[T, Y, er, f]) →
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (∀ q : PN t n, denD (.map Y') q → q.1.1 = "map") ∧
        ((∃ u, MT t n X u) → ∀ w, MT t n Y' w ↔ DRS (level t n).den (MT t n X) rs neg Ds A md w) := by
  obtain ⟨rs, neg, Ds, A, ks, h⟩ := dl_gx (t := t) (n := n) hs hmd
  refine ⟨rs, neg, Ds, A, ks, fun X hX st m hm T Y er f run => ?_⟩
  obtain ⟨Y', e, dY, shY, sY⟩ := h hX _ hm run
  exact ⟨Y', e, dY, single_map_only shY, sY⟩

end


section
variable {t : Term} {n : Nat}

/-- The maps of a static map type of `map_update_static/5`, from those of a field. -/
theorem mapsY_of {Y : Term} {S : MW (level t n).V → Prop}
    (hY : MapsY (level t n).E (level t n).den Y S) :
    ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (∀ q : PN t n, denD (.map Y') q → q.1.1 = "map") ∧
      ∀ w, MT t n Y' w ↔ S w := by
  rcases hY with ⟨rfl, emp⟩ | ⟨r', rfl, fr, sr⟩
  · exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, fun q h => by simp [denD_map, mapLookup, dn_none] at h,
      fun w => ⟨fun h => by simp [MT, mapLookup] at h, fun h => absurd h (emp w)⟩⟩
  · refine ⟨_, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, single_map_only (Or.inr ⟨_, rfl⟩), fun w => ?_⟩
    rw [← sr w]
    simp [MT, mapLookup]

/-- The maps of `:keep` and `:reject` at a static split, as `supd_val` takes them. -/
theorem kr_static_hY {rs Ds : List String} {neg : Term} (ok : SplitOk (rs.map Term.atom) neg (Ds.map Term.atom))
    (nr : ∀ N, neg = .map N → rs = []) (na : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    (keep : Bool) {v : Term} (hv : (level t n).E v) (sv : v = .atom "term" ∨ ∃ Z, v = .map Z)
    (vne : ∃ x, (level t n).den v x) :
    ∀ X : List (Term × Term), DE (level t n).E (.map X) → ∀ (st : Bool) (m : Nat), (level t n).K + 30 ≤ m →
      ∀ T Y er f, Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X)
        (splitT (rs.map Term.atom) neg (Ds.map Term.atom)) (cOp v Bool.false (modeS keep)) (.atom "true")
        (boolAtom st) = .ok (.tuple #[T, Y, er, f]) →
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (∀ q : PN t n, denD (.map Y') q → q.1.1 = "map") ∧
        ((∃ u, MT t n X u) → ∀ w, MT t n Y' w ↔ KRS (level t n).den (MT t n X) rs neg Ds [] v keep w) := by
  intro X hX st m hm T Y er f run
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
  have ef := (level t n).ef
  have sX := de_map hX
  rw [← keepOp_cOp] at run
  cases hb : mapLookup X (.atom "map") with
  | none =>
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at run
    simp [getMapKeys_single, hb] at run
    obtain ⟨-, rfl, -⟩ := run
    exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, fun q h => by simp [denD_map, mapLookup, dn_none] at h,
      fun ⟨u, hu⟩ => by simp [MT, hb] at hu⟩
  | some b =>
  have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
  have conv : (fun u => denMF (level t n).E (level t n).den b u = Bool.true) = MT t n X :=
    funext fun u => propext (by simp [MT, hb])
  obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
    kr_update_static ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hv sv vne keep ok nr na hb fb
  · rcases static_rel (k + 7) (.map X) _ _ _ _ _ run rr with e | ⟨_, _, _, _, _, _, -, e⟩ <;> cases e
  · have eY : Y = Y' := by
      rcases static_rel (k + 7) (.map X) _ _ _ _ _ run rr with e | ⟨_, bd, _, _, _, _, e₁, e₂⟩
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e; exact e.2.1
      · simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at e₁ e₂; rw [e₁.2.1, e₂.2.1]
    subst eY
    rw [conv] at hY mDm
    obtain ⟨Y'', e, dY, oY, sY⟩ := mapsY_of hY
    refine ⟨Y'', e, dY, oY, fun _ w => (sY w).trans ⟨fun h => ⟨Dm, mDm, Or.inl h⟩, fun ⟨Dm', mDm', h⟩ => ?_⟩⟩
    rcases h with h | ⟨a, ma, _⟩
    · exact upd_mono (fun u h => h) (fun x h => h) vne ok ok nr (fun κ h => h) mDm' mDm h
    · simp at ma

/-- The maps of deleting at a static split, as `supd_del` takes them. -/
theorem dl_static_hY {rs Ds : List String} {neg : Term} (ok : SplitOk (rs.map Term.atom) neg (Ds.map Term.atom))
    (nr : ∀ N, neg = .map N → rs = []) (na : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {md : String} (hmd : Mode md) :
    ∀ X : List (Term × Term), DE (level t n).E (.map X) → ∀ (st : Bool) (m : Nat), (level t n).K + 30 ≤ m →
      ∀ T Y er f, Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X)
        (splitT (rs.map Term.atom) neg (Ds.map Term.atom)) (cOp (.map []) Bool.true md) (.atom "true")
        (boolAtom st) = .ok (.tuple #[T, Y, er, f]) →
      ∃ Y', Y = .map Y' ∧ DE (level t n).E (.map Y') ∧ (∀ q : PN t n, denD (.map Y') q → q.1.1 = "map") ∧
        ((∃ u, MT t n X u) → ∀ w, MT t n Y' w ↔ DRS (level t n).den (MT t n X) rs neg Ds [] md w) := by
  intro X hX st m hm T Y er f run
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
  have ef := (level t n).ef
  have sX := de_map hX
  cases hb : mapLookup X (.atom "map") with
  | none =>
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def] at run
    simp [getMapKeys_single, hb] at run
    obtain ⟨-, rfl, -⟩ := run
    exact ⟨[], rfl, Or.inr ⟨_, rfl, descrC_nil⟩, fun q h => by simp [denD_map, mapLookup, dn_none] at h,
      fun ⟨u, hu⟩ => by simp [MT, hb] at hu⟩
  | some b =>
  have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
  have conv : (fun u => denMF (level t n).E (level t n).den b u = Bool.true) = MT t n X :=
    funext fun u => propext (by simp [MT, hb])
  obtain ⟨res, rr, ⟨rfl, -⟩ | ⟨T', Y', er', f', rfl, -, Dm, mDm, hY⟩⟩ :=
    del_update_static ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) hmd st ok nr na hb fb
  · rw [show k + 2 + 6 = k + 8 by omega] at rr; rw [rr] at run; cases run
  · rw [show k + 2 + 6 = k + 8 by omega] at rr; rw [rr] at run
    simp only [Except.ok.injEq, Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at run
    obtain ⟨-, rfl, -⟩ := run
    rw [conv] at hY mDm
    obtain ⟨Y'', e, dY, oY, sY⟩ := mapsY_of hY
    refine ⟨Y'', e, dY, oY, fun _ w => (sY w).trans ⟨fun h => ⟨Dm, mDm, Or.inl h⟩, fun ⟨Dm', mDm', h⟩ => ?_⟩⟩
    rcases h with h | ⟨a, ma, _⟩
    · exact del_mono ef.den_none (fun u h => h) hmd ok ok nr (fun κ h => h) mDm' mDm h
    · simp at ma

end



section
variable {V : Type}

/-- Keys of a split with a negated set are among those of another split only if it has one too. -/
theorem neg_of_keys {rk₁ Os₁ Ds₁ Do₁ rk₂ Os₂ Ds₂ Do₂ : List String} {N₁ : List (Term × Term)} {neg₂ : Term}
    (g₂ : GSplit rk₂ Os₂ neg₂ Ds₂ Do₂)
    (hK : ∀ κ, GKey rk₁ Os₁ (.map N₁) Ds₁ Do₁ κ → GKey rk₂ Os₂ neg₂ Ds₂ Do₂ κ) : ∃ N₂, neg₂ = .map N₂ := by
  rcases g₂.ok.hneg with rfl | h
  · obtain ⟨c, hc⟩ := fresh_str (keyStrs N₁ ++ rk₂ ++ Os₂)
    have h₁ : GKey rk₁ Os₁ (.map N₁) Ds₁ Do₁ (.atom c) :=
      Or.inr (Or.inr ⟨N₁, rfl, lookup_fresh' fun m => hc (by simp [m])⟩)
    rcases hK _ h₁ with ⟨a, ma, e⟩ | h | ⟨N, e, -⟩
    · cases e; exact absurd (by rcases ma with m | m <;> simp [m]) hc
    · simp at h
    · cases e
  · exact h

theorem foundG_key {M : MW V → Prop} {rk₁ Os₁ Ds₁ Do₁ rk₂ Os₂ Ds₂ Do₂ : List String} {neg₁ neg₂ : Term}
    (g₁ : GSplit rk₁ Os₁ neg₁ Ds₁ Do₁) (g₂ : GSplit rk₂ Os₂ neg₂ Ds₂ Do₂)
    (hK : ∀ κ, GKey rk₁ Os₁ neg₁ Ds₁ Do₁ κ → GKey rk₂ Os₂ neg₂ Ds₂ Do₂ κ) (os₂ : Os₂ = [])
    (nr₂ : ∀ N, neg₂ = .map N → rk₂ = []) {md : String} {st : Bool} (h : FoundG M rk₁ Os₁ neg₁ Ds₁ Do₁ md st) :
    FoundG M rk₂ Os₂ neg₂ Ds₂ Do₂ md st := by
  subst os₂
  -- The atom kind of a split means a negated set, and the atoms outside of it.
  have atomNeg : ∀ {rk Os neg Ds Do}, GSplit rk Os neg Ds Do → "atom" ∈ Ds ++ Do → ∃ N, neg = .map N := fun g m =>
    g.ok.hatom.mp (List.mem_map_of_mem m)
  have negAtom : ∀ {rk Os N Ds Do}, GSplit rk Os (.map N) Ds Do → "atom" ∈ Ds ++ Do := fun g => by
    obtain ⟨s, ms, e⟩ := List.mem_map.mp (g.ok.hatom.mpr ⟨_, rfl⟩); cases e; exact ms
  -- A key of the first split that is a key of the second as split keys or required atoms.
  have toB : ∀ κ, GKey rk₁ Os₁ neg₁ Ds₁ Do₁ κ →
      SplitKey [] neg₂ ((Ds₂ ++ Do₂).map Term.atom) κ ∨ ∃ a ∈ rk₂, κ = .atom a ∧ neg₂ = .atom "nil" := by
    intro κ hκ
    rcases hK κ hκ with ⟨a, ma | ma, rfl⟩ | h
    · rcases g₂.ok.hneg with e | ⟨N, e⟩
      · exact Or.inr ⟨a, ma, rfl, e⟩
      · rw [nr₂ N e] at ma; simp at ma
    · simp at ma
    · exact Or.inl h
  rcases h with ⟨hf, h⟩ | ⟨nf, ⟨x, w, hw, κ, hκ, e⟩ | ⟨hat, a, ma, w, x, hw, e⟩ | ⟨a, ma, hv, hst⟩⟩
  · refine Or.inl ⟨hf, ?_⟩
    -- Some key of the first split.
    obtain ⟨κ, hκ⟩ : ∃ κ, GKey rk₁ Os₁ neg₁ Ds₁ Do₁ κ := by
      rcases h with h | h | h
      · obtain ⟨d, md⟩ := List.exists_mem_of_ne_nil _ h
        by_cases da : d = "atom"
        · subst da
          obtain ⟨N, rfl⟩ := atomNeg g₁ md
          obtain ⟨c, hc⟩ := fresh_str (keyStrs N)
          exact ⟨.atom c, Or.inr (Or.inr ⟨N, rfl, lookup_fresh' hc⟩)⟩
        · have hd : d ∈ domainKinds := by
            obtain ⟨s', ms', e⟩ := g₁.ok.hds _ (List.mem_map_of_mem md); cases e; exact ms'
          obtain ⟨k, rfl⟩ := domKind_of hd da
          exact ⟨.dom k 0, Or.inr (List.mem_map_of_mem md)⟩
      · obtain ⟨a, ma⟩ := List.exists_mem_of_ne_nil _ h
        exact ⟨_, Or.inl ⟨a, Or.inl ma, rfl⟩⟩
      · obtain ⟨a, ma⟩ := List.exists_mem_of_ne_nil _ h
        exact ⟨_, Or.inl ⟨a, Or.inr ma, rfl⟩⟩
    rcases toB κ hκ with h | ⟨a, ma, -, -⟩
    · cases κ with
      | atom c =>
        rcases h with h | ⟨N, e, -⟩
        · simp at h
        · subst e; exact Or.inl (List.ne_nil_of_mem (negAtom g₂))
      | dom k i => exact Or.inl fun e => by simp [SplitKey, e] at h
    · exact Or.inr (Or.inl (List.ne_nil_of_mem ma))
  · refine Or.inr ⟨nf, ?_⟩
    rcases toB κ (Or.inr hκ) with h | ⟨a, ma, rfl, en⟩
    · exact Or.inl ⟨x, w, hw, κ, h, e⟩
    · exfalso
      rcases hκ with hκ | ⟨N, rfl, -⟩
      · simp at hκ
      · obtain ⟨N₂, e₂⟩ := neg_of_keys g₂ hK
        rw [en] at e₂; cases e₂
  · refine Or.inr ⟨nf, Or.inl ⟨x, w, hw, .atom a, ?_, e⟩⟩
    obtain ⟨N, rfl⟩ := atomNeg g₁ hat
    obtain ⟨N₂, rfl⟩ := neg_of_keys g₂ hK
    rcases toB _ (Or.inl ⟨a, ma, rfl⟩) with h | ⟨a', ma', -, e⟩
    · exact h
    · cases e
  · refine Or.inr ⟨nf, ?_⟩
    rcases toB _ (Or.inl ⟨a, ma, rfl⟩) with h | ⟨a', ma', e, -⟩
    · obtain ⟨w, x, hw, e⟩ := hv
      exact Or.inl ⟨x, w, hw, .atom a, h, e⟩
    · cases e
      exact Or.inr (Or.inr ⟨a, Or.inl ma', hv, hst⟩)


theorem drs_mono {den : Term → V → Prop} (nn : ∀ x, ¬den (.map []) x) {M₁ M₂ : MW V → Prop}
    (hM : ∀ u, M₁ u → M₂ u) {md : String} (hmd : Mode md) {rs₁ rs₂ Ds₁ Ds₂ A₁ A₂ : List String} {neg₁ neg₂ : Term}
    (ok₁ : SplitOk (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom)) (ok₂ : SplitOk (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom))
    (nr₂ : ∀ N, neg₂ = .map N → rs₂ = [])
    (hK : ∀ κ, SplitKey (rs₁.map Term.atom) neg₁ (Ds₁.map Term.atom) κ →
      SplitKey (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom) κ)
    (hA : ∀ a ∈ A₁, a ∈ A₂ ∨ SplitKey (rs₂.map Term.atom) neg₂ (Ds₂.map Term.atom) (.atom a)) {w : MW V}
    (h : DRS den M₁ rs₁ neg₁ Ds₁ A₁ md w) : DRS den M₂ rs₂ neg₂ Ds₂ A₂ md w := by
  classical
  obtain ⟨Dm₁, mDm₁, h⟩ := h
  have mDm₂ : ∀ d, d ∈ Ds₂.filter (fun d => decide (md ≠ "reject" ∨ KindHeld M₂ d)) ↔
      d ∈ Ds₂ ∧ (md ≠ "reject" ∨ KindHeld M₂ d) := fun d => by simp
  refine ⟨_, mDm₂, ?_⟩
  rcases h with h | ⟨a, ma, h⟩
  · exact Or.inl (del_mono nn hM hmd ok₁ ok₂ nr₂ hK mDm₁ mDm₂ h)
  · rcases hA a ma with m | k
    · exact Or.inr ⟨a, m, delAt_mono hM h⟩
    · left
      have ok₀ : SplitOk ([a].map Term.atom) (.atom "nil") (([] : List String).map Term.atom) :=
        ⟨by simp, Or.inl rfl, by simp, by simp⟩
      refine del_mono (Dm₁ := []) nn hM hmd ok₀ ok₂ nr₂ (fun κ hκ => ?_) (fun d => by simp) mDm₂
        (Or.inl ⟨rfl, Or.inl ⟨a, by simp, h⟩⟩)
      cases κ with
      | atom c =>
        rcases hκ with hκ | ⟨N, e, -⟩
        · simp at hκ; subst hκ; exact k
        · cases e
      | dom k' i => simp [SplitKey] at hκ

end


section
variable {t : Term} {d : Nat}

/-- Two old types of updates of the same map type: elements, or gradual types, with values that are included. -/
theorem old_sub {X : List (Term × Term)} {v T₁ T₂ : Term} {OV : (MW (level t (d + 1)).V → Prop) → (level t (d + 1)).V → Prop}
    {m : Nat} (hm : (level t (d + 1)).K + 30 ≤ m)
    (k₁ : (mapLookup X (.atom "dynamic") = none ∧ upper v = v ∧ (level t (d + 1)).E T₁ ∧
        ∀ x, (level t (d + 1)).den T₁ x ↔ OV (MT t (d + 1) (rmDyn X)) x) ∨
      (¬(mapLookup X (.atom "dynamic") = none ∧ upper v = v) ∧ GC (level t d) T₁ ∧
        (∀ x : PN t d, denD T₁ x ↔ upper v = v ∧ OV (MT t (d + 1) (rmDyn X)) x) ∧
        ∀ x : PN t d, denD (upper T₁) x ↔ OV (MT t (d + 1) (dynL (upper (.map X)))) x))
    (k₂ : (mapLookup X (.atom "dynamic") = none ∧ upper v = v ∧ (level t (d + 1)).E T₂ ∧
        ∀ x, (level t (d + 1)).den T₂ x ↔ OV (MT t (d + 1) (rmDyn X)) x) ∨
      (¬(mapLookup X (.atom "dynamic") = none ∧ upper v = v) ∧ GC (level t d) T₂ ∧
        (∀ x : PN t d, denD T₂ x ↔ upper v = v ∧ OV (MT t (d + 1) (rmDyn X)) x) ∧
        ∀ x : PN t d, denD (upper T₂) x ↔ OV (MT t (d + 1) (dynL (upper (.map X)))) x)) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) T₁ T₂ = .ok (.atom "true") := by
  rcases k₁ with ⟨h₁, u₁, e₁, s₁⟩ | ⟨n₁, g₁, l₁, v₁⟩ <;> rcases k₂ with ⟨h₂, u₂, e₂, s₂⟩ | ⟨n₂, g₂, l₂, v₂⟩
  · exact (level t (d + 1)).ef.subc e₁ e₂ (fun x h => (s₂ x).mpr ((s₁ x).mp h)) m (by omega)
  · exact absurd ⟨h₁, u₁⟩ n₂
  · exact absurd ⟨h₂, u₂⟩ n₁
  · exact gc_sub g₁ g₂ (by rw [level_K] at hm ⊢; omega) (fun x h => (l₂ x).mpr ((l₁ x).mp h))
      (fun x h => (v₂ x).mpr ((v₁ x).mp h))

/-- Updating at keys whose maps and found flags are among those of other keys of the same values gives subtypes. -/
theorem upd_gsub {X : List (Term × Term)} {v : Term} (gX : GC (level t (d + 1)) (.map X)) (gv : GC (level t d) v)
    (dup : DE (level t d).E (upper v)) (vne : ∃ y : PN t d, denD (upper v) y) {k₁ k₂ s₁ s₂ : Term} {md : String}
    {m : Nat} (hk₁ : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k₁ = .ok s₁)
    (hk₂ : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k₂ = .ok s₂) (hmd : Mode md)
    {OV : (MW (level t (d + 1)).V → Prop) → (level t (d + 1)).V → Prop}
    {S₁ S₂ : Term → (MW (level t (d + 1)).V → Prop) → MW (level t (d + 1)).V → Prop}
    {F₁ F₂ : (MW (level t (d + 1)).V → Prop) → Bool → Prop}
    (hS₁ : ∀ x, DE (level t d).E x → (x = .atom "term" ∨ ∃ Z, x = .map Z) → (∃ y : PN t d, denD x y) →
      SUpd t (d + 1) s₁ (cOp x Bool.false md) OV (S₁ x) F₁)
    (hS₂ : ∀ x, DE (level t d).E x → (x = .atom "term" ∨ ∃ Z, x = .map Z) → (∃ y : PN t d, denD x y) →
      SUpd t (d + 1) s₂ (cOp x Bool.false md) OV (S₂ x) F₂)
    (ovE : ∀ M x, OV M x → ∃ w, M w)
    (ovm : ∀ M₁ M₂ : MW (level t (d + 1)).V → Prop, (∀ u, M₁ u → M₂ u) → ∀ x, OV M₁ x → OV M₂ x)
    (hSm₁ : ∀ x (M₁ M₂ : MW (level t (d + 1)).V → Prop), DE (level t d).E x → (∃ y : PN t d, denD x y) →
      (∀ u, M₁ u → M₂ u) → ∀ w, S₁ x M₁ w → S₁ x M₂ w)
    (hSm₂ : ∀ x (M₁ M₂ : MW (level t (d + 1)).V → Prop), DE (level t d).E x → (∃ y : PN t d, denD x y) →
      (∀ u, M₁ u → M₂ u) → ∀ w, S₂ x M₁ w → S₂ x M₂ w)
    (h12 : ∀ x M w, DE (level t d).E x → (∃ y : PN t d, denD x y) → S₁ x M w → S₂ x M w)
    (f12 : ∀ M st, F₁ M st → F₂ M st) (hm : (level t (d + 1)).K + 30 ≤ m) {T R er : Term}
    (run : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) k₁ v (.atom md) (.atom "true") =
      .ok (.tuple #[T, R, er])) :
    ∃ T₂ R₂ er₂, Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) k₂ v (.atom md) (.atom "true") =
        .ok (.tuple #[T₂, R₂, er₂]) ∧ Elixir.Module.Types.Descr.«subtype?/2» (D m) T T₂ = .ok (.atom "true") ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) R R₂ = .ok (.atom "true") := by
  obtain ⟨r, run', iffA, semA⟩ := upd_all_g gX gv dup vne hk₁ hmd hS₁ ovE ovm hSm₁ hm
  rw [run] at run'; cases run'
  obtain ⟨onlyA, neA, fA⟩ := iffA.mp ⟨_, _, _, rfl⟩
  obtain ⟨r₂, run₂, iffB, semB⟩ := upd_all_g gX gv dup vne hk₂ hmd hS₂ ovE ovm hSm₂ hm
  obtain ⟨T₂, R₂, er₂, rfl⟩ := iffB.mpr ⟨onlyA, neA, f12 _ _ fA⟩
  obtain ⟨gR, oR, lR, uR, -, -, -, -, -, -, -, -, kA⟩ := semA T R er rfl
  obtain ⟨gR₂, oR₂, lR₂, uR₂, -, -, -, -, -, -, -, -, kB⟩ := semB T₂ R₂ er₂ rfl
  refine ⟨T₂, R₂, er₂, run₂, old_sub hm kA kB, gc_sub gR gR₂ (by rw [level_K] at hm ⊢; omega) ?_ ?_⟩
  · refine via_mpt gR.shape gR₂.shape (fun q h => oR q (GC.inv gR q h)) fun w h => ?_
    obtain ⟨e, ne, h⟩ := (lR w).mp h
    exact (lR₂ w).mpr ⟨e, ne, h12 _ _ w (e ▸ dup) (e ▸ vne) h⟩
  · refine via_mpt (Or.imp id (fun ⟨Y, e, _⟩ => ⟨Y, e⟩) gR.up_tc) (Or.imp id (fun ⟨Y, e, _⟩ => ⟨Y, e⟩) gR₂.up_tc)
      oR fun w h => ?_
    exact (uR₂ w).mpr (h12 _ _ w dup vne ((uR w).mp h))

end


section
variable {t : Term} {d : Nat}

/-- Deleting at keys whose maps and found flags are among those of other keys gives subtypes. -/
theorem del_gsub {X : List (Term × Term)} (gX : GC (level t (d + 1)) (.map X)) {k₁ k₂ s₁ s₂ : Term} {md : String}
    {m : Nat} (hk₁ : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k₁ = .ok s₁)
    (hk₂ : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) k₂ = .ok s₂) (hmd : Mode md)
    {OV : (MW (level t (d + 1)).V → Prop) → (level t (d + 1)).V → Prop}
    {S₁ S₂ : (MW (level t (d + 1)).V → Prop) → MW (level t (d + 1)).V → Prop}
    {F₁ F₂ : (MW (level t (d + 1)).V → Prop) → Bool → Prop}
    (hS₁ : SUpd t (d + 1) s₁ (cOp (.map []) Bool.true md) OV S₁ F₁)
    (hS₂ : SUpd t (d + 1) s₂ (cOp (.map []) Bool.true md) OV S₂ F₂)
    (ovE : ∀ M x, OV M x → ∃ w, M w) (h12 : ∀ M w, S₁ M w → S₂ M w) (f12 : ∀ M st, F₁ M st → F₂ M st)
    (hm : (level t (d + 1)).K + 30 ≤ m) {T R er : Term}
    (run : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) k₁ (.atom "delete") (.atom md) (.atom "true") =
      .ok (.tuple #[T, R, er])) :
    ∃ T₂ R₂ er₂, Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) k₂ (.atom "delete") (.atom md) (.atom "true") =
        .ok (.tuple #[T₂, R₂, er₂]) ∧ Elixir.Module.Types.Descr.«subtype?/2» (D m) T T₂ = .ok (.atom "true") ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) R R₂ = .ok (.atom "true") := by
  rw [upd5_del (.map X) hk₁ hmd] at run
  rw [upd5_del (.map X) hk₂ hmd]
  obtain ⟨r, run', iffA, semA⟩ := gupd_un gX hS₁ ovE hm
  rw [run] at run'; cases run'
  obtain ⟨onlyA, neA, fA⟩ := iffA.mp ⟨_, _, _, rfl⟩
  obtain ⟨r₂, run₂, iffB, semB⟩ := gupd_un gX hS₂ ovE hm
  obtain ⟨T₂, R₂, er₂, rfl⟩ := iffB.mpr ⟨onlyA, neA, f12 _ _ fA⟩
  obtain ⟨gR, oR, lR, uR, -, -, -, -, -, -, -, -, kA⟩ := semA T R er rfl
  obtain ⟨gR₂, oR₂, lR₂, uR₂, -, -, -, -, -, -, -, -, kB⟩ := semB T₂ R₂ er₂ rfl
  refine ⟨T₂, R₂, er₂, run₂, ?_, gc_sub gR gR₂ (by rw [level_K] at hm ⊢; omega) ?_ ?_⟩
  · rcases kA with ⟨h₁, e₁, s₁⟩ | ⟨n₁, g₁, l₁, v₁⟩ <;> rcases kB with ⟨h₂, e₂, s₂⟩ | ⟨n₂, g₂, l₂, v₂⟩
    · exact (level t (d + 1)).ef.subc e₁ e₂ (fun x h => (s₂ x).mpr ((s₁ x).mp h)) m (by omega)
    · exact absurd h₁ n₂
    · exact absurd h₂ n₁
    · exact gc_sub g₁ g₂ (by rw [level_K] at hm ⊢; omega) (fun x h => (l₂ x).mpr ((l₁ x).mp h))
        (fun x h => (v₂ x).mpr ((v₁ x).mp h))
  · refine via_mpt gR.shape gR₂.shape (fun q h => oR q (GC.inv gR q h)) fun w h => ?_
    obtain ⟨ne, h⟩ := (lR w).mp h
    exact (lR₂ w).mpr ⟨ne, h12 _ w h⟩
  · refine via_mpt (Or.imp id (fun ⟨Y, e, _⟩ => ⟨Y, e⟩) gR.up_tc) (Or.imp id (fun ⟨Y, e, _⟩ => ⟨Y, e⟩) gR₂.up_tc)
      oR fun w h => ?_
    exact (uR₂ w).mpr ((uR w).mp h |>.imp (fun ⟨ne, h⟩ => ⟨ne, h12 _ w h⟩) (h12 _ w))

end


section

/-- The gradual form of a static split: its atoms, no optional ones, and none required with a negated set. -/
theorem splitT_strs {rs : List Term} {neg : Term} {ds : List Term} (ok : SplitOk rs neg ds)
    (nr : ∀ N, neg = .map N → rs = []) (na : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {KP : MKey → Prop} (kp : ∀ κ, SplitKey rs neg ds κ ↔ KP κ) :
    ∃ (rk : List String) (Ds : List String), splitT rs neg ds = gsT rk [] neg Ds [] ∧ GSplit rk [] neg Ds [] ∧
      (∀ κ, GKey rk [] neg Ds [] κ ↔ KP κ) ∧ (∀ N, neg = .map N → rk = []) ∧ rs = rk.map Term.atom ∧
      ds = Ds.map Term.atom := by
  obtain ⟨rk, rfl⟩ := atoms_strs ok.hrs
  obtain ⟨Ds, rfl⟩ := atoms_strs fun r m => let ⟨s, _, e⟩ := ok.hds r m; ⟨s, e⟩
  have nr' : ∀ N, neg = .map N → rk = [] := fun N e => by have := nr N e; cases rk <;> simp_all
  refine ⟨rk, Ds, by simp [splitT, gsT, Term.list], ⟨⟨by simp, ok.hneg, by simpa using ok.hds, by simpa using ok.hatom⟩,
    fun _ _ => rfl, na, fun N e a m => ?_⟩,
    fun κ => ?_, nr', rfl, rfl⟩
  · rw [nr' N e] at m; simp at m
  · rw [← kp κ]
    cases κ with
    | atom a => simp [GKey, SplitKey]
    | dom k i => simp [GKey, SplitKey]

end


section
variable {t : Term} {d : Nat}

/-- `map_update/5` at a gradual key type of the laws gives a subtype of the update at the key type's upper bound. -/
theorem upd_key_inst {X : List (Term × Term)} {v : Term} (gX : GC (level t (d + 1)) (.map X)) (gv : GC (level t d) v)
    (dup : DE (level t d).E (upper v)) (vne : ∃ y : PN t d, denD (upper v) y) {key : Term} {md : String} {m : Nat}
    (hmk : (level t d).K + 23 ≤ m)
    (hk' : «arrows_gradual?/2» (D (m + 1)) key (.tuple #[.integer d, t]) = .ok (.atom "true")) (hmd : Mode md)
    (hm : (level t (d + 1)).K + 30 ≤ m + 1) {T R er : Term}
    (run : Elixir.Module.Types.Descr.«map_update/5» (D (m + 1)) (.map X) key v (.atom md) (.atom "true") =
      .ok (.tuple #[T, R, er])) :
    ∃ T₂ R₂ er₂, Elixir.Module.Types.Descr.«map_update/5» (D (m + 1)) (.map X) (upper key) v (.atom md) (.atom "true") =
        .ok (.tuple #[T₂, R₂, er₂]) ∧ Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) T T₂ = .ok (.atom "true") ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) R R₂ = .ok (.atom "true") := by
  obtain ⟨s, hk, hs⟩ := key_gform (t := t) (n := d) hmk hk'
  obtain ⟨rk, Os, ng, Ds, Do, rfl, gs, hkey⟩ := gform_strs hs
  obtain ⟨s', neg, Ss, rk', na, hP, oks, rs₂, neg₂, ds₂, rku, oku, nru, nau, sk, sku⟩ :=
    key_gsplit (t := t) (n := d) hmk hk'
  rw [hk] at rk'; cases rk'
  obtain ⟨rk₂, Ds₂, e₂, gs₂, hkey₂, nr₂, rfl, rfl⟩ := splitT_strs oku nru nau sku
  rw [e₂] at rku
  have ovE : ∀ (M : MW (level t (d + 1)).V → Prop) x, Vals M (KeyPt t d (upper key)) x → ∃ w, M w :=
    fun M x ⟨w, hw, _⟩ => ⟨w, hw⟩
  have ovm : ∀ M₁ M₂ : MW (level t (d + 1)).V → Prop, (∀ u, M₁ u → M₂ u) → ∀ x,
      Vals M₁ (KeyPt t d (upper key)) x → Vals M₂ (KeyPt t d (upper key)) x := fun M₁ M₂ h x => vals_mono h
  have dn : ∀ {x : Term}, DE (level t d).E x → ∀ y, (level t (d + 1)).den x y ↔ denD x y := fun dx y => den_succ dx y
  have toE : ∀ {x : Term}, DE (level t d).E x → (level t (d + 1)).E x := fun dx => Or.inl dx
  have F12 : ∀ (M : MW (level t (d + 1)).V → Prop) st, FoundG M rk Os ng Ds Do md st →
      FoundG M rk₂ [] neg₂ Ds₂ [] md st := fun M st h =>
    foundG_key gs gs₂ (fun κ h => (hkey₂ κ).mpr ((hkey κ).mp h)) rfl nr₂ h
  rcases hmd with rfl | rfl | rfl
  · have hP₂ := dnfPuts_split oku nru
    rw [e₂] at hP₂
    refine upd_gsub gX gv dup vne hk rku (Or.inl rfl)
      (S₁ := fun x M w => PutAny Ss (level t (d + 1)).den M x w)
      (S₂ := fun x M w => PutSem (level t (d + 1)).den M (rk₂.map Term.atom) neg₂ (Ds₂.map Term.atom) x w)
      (fun x dx sx ⟨y, hy⟩ => supd_val gs hkey (toE dx) sx ⟨y, (dn dx y).mpr hy⟩ (Or.inl rfl)
        (force_hY hP na (toE dx) sx))
      (fun x dx sx ⟨y, hy⟩ => supd_val gs₂ hkey₂ (toE dx) sx ⟨y, (dn dx y).mpr hy⟩ (Or.inl rfl)
        (force_hY hP₂ nau (toE dx) sx)) ovE ovm ?_ ?_ ?_ F12 hm run
    · intro x M₁ M₂ _ _ hM w ⟨sp, msp, h⟩
      exact ⟨sp, msp, put_mono hM (fun y hy => hy) (oks sp msp).1 (oks sp msp).1 (oks sp msp).2 (fun _ h => h) h⟩
    · intro x M₁ M₂ _ _ hM w h
      exact put_mono hM (fun y hy => hy) oku oku nru (fun _ h => h) h
    · intro x M w _ _ ⟨sp, msp, h⟩
      exact put_mono (fun _ h => h) (fun _ h => h) (oks sp msp).1 oku nru (fun κ hκ => (sk κ).mp ⟨sp, msp, hκ⟩) h
  · obtain ⟨rs, neg1, D2, A, ⟨ok2, nr2, -, -, -, kp1⟩, hY⟩ := kr_hY (t := t) (n := d + 1) hs Bool.true
    have hY₂ := fun {x : Term} (hx : (level t (d + 1)).E x) (sx : x = .atom "term" ∨ ∃ Z, x = .map Z)
        (nx : ∃ y, (level t (d + 1)).den x y) =>
      kr_static_hY (t := t) (n := d + 1) oku nr₂ nau Bool.true hx sx nx
    rw [e₂] at hY₂
    refine upd_gsub gX gv dup vne hk rku (Or.inr (Or.inl rfl))
      (S₁ := fun x M w => KRS (level t (d + 1)).den M rs neg1 D2 A x Bool.true w)
      (S₂ := fun x M w => KRS (level t (d + 1)).den M rk₂ neg₂ Ds₂ [] x Bool.true w)
      (fun x dx sx ⟨y, hy⟩ => supd_val gs hkey (toE dx) sx ⟨y, (dn dx y).mpr hy⟩ (mode_modeS Bool.true)
        (hY (toE dx) sx ⟨y, (dn dx y).mpr hy⟩))
      (fun x dx sx ⟨y, hy⟩ => supd_val gs₂ hkey₂ (toE dx) sx ⟨y, (dn dx y).mpr hy⟩ (mode_modeS Bool.true)
        (hY₂ (toE dx) sx ⟨y, (dn dx y).mpr hy⟩)) ovE ovm ?_ ?_ ?_ F12 hm run
    · intro x M₁ M₂ dx ⟨y, hy⟩ hM w h
      exact krs_mono hM (fun y hy => hy) ⟨y, (dn dx y).mpr hy⟩ ok2 ok2 nr2 (fun κ h => h) (fun a m => Or.inl m) h
    · intro x M₁ M₂ dx ⟨y, hy⟩ hM w h
      exact krs_mono hM (fun y hy => hy) ⟨y, (dn dx y).mpr hy⟩ oku oku nr₂ (fun κ h => h) (fun a m => Or.inl m) h
    · intro x M w dx ⟨y, hy⟩ h
      exact krs_mono (fun u h => h) (fun y hy => hy) ⟨y, (dn dx y).mpr hy⟩ ok2 oku nr₂
        (fun κ hκ => (sku κ).mpr ((kp1 κ).mp (Or.inr hκ)))
        (fun a ma => Or.inr ((sku _).mpr ((kp1 _).mp (Or.inl ⟨a, ma, rfl⟩)))) h
  · obtain ⟨rs, neg1, D2, A, ⟨ok2, nr2, -, -, -, kp1⟩, hY⟩ := kr_hY (t := t) (n := d + 1) hs Bool.false
    have hY₂ := fun {x : Term} (hx : (level t (d + 1)).E x) (sx : x = .atom "term" ∨ ∃ Z, x = .map Z)
        (nx : ∃ y, (level t (d + 1)).den x y) =>
      kr_static_hY (t := t) (n := d + 1) oku nr₂ nau Bool.false hx sx nx
    rw [e₂] at hY₂
    refine upd_gsub gX gv dup vne hk rku (Or.inr (Or.inr rfl))
      (S₁ := fun x M w => KRS (level t (d + 1)).den M rs neg1 D2 A x Bool.false w)
      (S₂ := fun x M w => KRS (level t (d + 1)).den M rk₂ neg₂ Ds₂ [] x Bool.false w)
      (fun x dx sx ⟨y, hy⟩ => supd_val gs hkey (toE dx) sx ⟨y, (dn dx y).mpr hy⟩ (mode_modeS Bool.false)
        (hY (toE dx) sx ⟨y, (dn dx y).mpr hy⟩))
      (fun x dx sx ⟨y, hy⟩ => supd_val gs₂ hkey₂ (toE dx) sx ⟨y, (dn dx y).mpr hy⟩ (mode_modeS Bool.false)
        (hY₂ (toE dx) sx ⟨y, (dn dx y).mpr hy⟩)) ovE ovm ?_ ?_ ?_ F12 hm run
    · intro x M₁ M₂ dx ⟨y, hy⟩ hM w h
      exact krs_mono hM (fun y hy => hy) ⟨y, (dn dx y).mpr hy⟩ ok2 ok2 nr2 (fun κ h => h) (fun a m => Or.inl m) h
    · intro x M₁ M₂ dx ⟨y, hy⟩ hM w h
      exact krs_mono hM (fun y hy => hy) ⟨y, (dn dx y).mpr hy⟩ oku oku nr₂ (fun κ h => h) (fun a m => Or.inl m) h
    · intro x M w dx ⟨y, hy⟩ h
      exact krs_mono (fun u h => h) (fun y hy => hy) ⟨y, (dn dx y).mpr hy⟩ ok2 oku nr₂
        (fun κ hκ => (sku κ).mpr ((kp1 κ).mp (Or.inr hκ)))
        (fun a ma => Or.inr ((sku _).mpr ((kp1 _).mp (Or.inl ⟨a, ma, rfl⟩)))) h

end


section
variable {t : Term} {d : Nat}

/-- Deleting a gradual key type of the laws gives a subtype of deleting the key type's upper bound. -/
theorem del_key_inst {X : List (Term × Term)} (gX : GC (level t (d + 1)) (.map X)) {key : Term} {md : String} {m : Nat}
    (hmk : (level t d).K + 23 ≤ m)
    (hk' : «arrows_gradual?/2» (D (m + 1)) key (.tuple #[.integer d, t]) = .ok (.atom "true")) (hmd : Mode md)
    (hm : (level t (d + 1)).K + 30 ≤ m + 1) {T R er : Term}
    (run : Elixir.Module.Types.Descr.«map_update/5» (D (m + 1)) (.map X) key (.atom "delete") (.atom md) (.atom "true") =
      .ok (.tuple #[T, R, er])) :
    ∃ T₂ R₂ er₂, Elixir.Module.Types.Descr.«map_update/5» (D (m + 1)) (.map X) (upper key) (.atom "delete") (.atom md)
        (.atom "true") = .ok (.tuple #[T₂, R₂, er₂]) ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) T T₂ = .ok (.atom "true") ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) R R₂ = .ok (.atom "true") := by
  obtain ⟨s, hk, hs⟩ := key_gform (t := t) (n := d) hmk hk'
  obtain ⟨rk, Os, ng, Ds, Do, rfl, gs, hkey⟩ := gform_strs hs
  obtain ⟨-, -, -, -, -, -, -, rs₂, neg₂, ds₂, rku, oku, nru, nau, -, sku⟩ := key_gsplit (t := t) (n := d) hmk hk'
  obtain ⟨rk₂, Ds₂, e₂, gs₂, hkey₂, nr₂, rfl, rfl⟩ := splitT_strs oku nru nau sku
  rw [e₂] at rku
  have ovE : ∀ (M : MW (level t (d + 1)).V → Prop) x, Vals M (KeyPt t d (upper key)) x → ∃ w, M w :=
    fun M x ⟨w, hw, _⟩ => ⟨w, hw⟩
  obtain ⟨rs, neg1, D2, A, ⟨ok2, -, -, -, -, kp1⟩, hY⟩ := dl_hY (t := t) (n := d + 1) hs hmd
  have hY₂ := dl_static_hY (t := t) (n := d + 1) oku nr₂ nau hmd
  rw [e₂] at hY₂
  exact del_gsub gX hk rku hmd
    (supd_del gs hkey hmd (S := fun M w => DRS (level t (d + 1)).den M rs neg1 D2 A md w) hY)
    (supd_del gs₂ hkey₂ hmd (S := fun M w => DRS (level t (d + 1)).den M rk₂ neg₂ Ds₂ [] md w) hY₂) ovE
    (fun M w h => drs_mono (level t (d + 1)).ef.den_none (fun u h => h) hmd ok2 oku nr₂
      (fun κ hκ => (sku κ).mpr ((kp1 κ).mp (Or.inr hκ)))
      (fun a ma => Or.inr ((sku _).mpr ((kp1 _).mp (Or.inl ⟨a, ma, rfl⟩)))) h)
    (fun M st h => foundG_key gs gs₂ (fun κ h => (hkey₂ κ).mpr ((hkey κ).mp h)) rfl nr₂ h) hm run

end



section
variable {t : Term} {d : Nat}

/-- Deleting at a split with static-level semantics from less precise maps is less precise, as is the old type. -/
theorem del_gprec {X : List (Term × Term)} {a₂ : Term} (gX : GC (level t (d + 1)) (.map X))
    (g₂ : GC (level t (d + 1)) a₂) {key s : Term} {md : String} {m : Nat}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok s) (hmd : Mode md)
    {OV : (MW (level t (d + 1)).V → Prop) → (level t (d + 1)).V → Prop}
    {S : (MW (level t (d + 1)).V → Prop) → MW (level t (d + 1)).V → Prop}
    {F : (MW (level t (d + 1)).V → Prop) → Bool → Prop}
    (hS : SUpd t (d + 1) s (cOp (.map []) Bool.true md) OV S F) (ovE : ∀ M x, OV M x → ∃ w, M w)
    (ovm : ∀ M₁ M₂ : MW (level t (d + 1)).V → Prop, (∀ u, M₁ u → M₂ u) → ∀ x, OV M₁ x → OV M₂ x)
    (hSm : ∀ M₁ M₂ : MW (level t (d + 1)).V → Prop, (∀ u, M₁ u → M₂ u) → ∀ w, S M₁ w → S M₂ w)
    (Fw : ∀ (M : MW (level t (d + 1)).V → Prop) st, F M st → F M Bool.false)
    (Fm : ∀ M₁ M₂ : MW (level t (d + 1)).V → Prop, (∀ u, M₁ u → M₂ u) → F M₁ Bool.false → F M₂ Bool.false)
    (Fc : ∀ M₁ M₂ : MW (level t (d + 1)).V → Prop, (∀ u, M₁ u ↔ M₂ u) → ∀ st, F M₁ st → F M₂ st)
    (hm : (level t (d + 1)).K + 30 ≤ m)
    (lo : ∀ q : PN t (d + 1), denD a₂ q → denD (.map X) q)
    (up : ∀ q : PN t (d + 1), denD (upper (.map X)) q → denD (upper a₂) q)
    (kd : mapLookup X (.atom "dynamic") ≠ none → ∃ X₂, a₂ = .map X₂ ∧ mapLookup X₂ (.atom "dynamic") ≠ none)
    {T R er : Term}
    (run : Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key (.atom "delete") (.atom md) (.atom "true") =
      .ok (.tuple #[T, R, er])) :
    ∃ T₂ R₂ er₂, Elixir.Module.Types.Descr.«map_update/5» (D m) a₂ key (.atom "delete") (.atom md) (.atom "true") =
        .ok (.tuple #[T₂, R₂, er₂]) ∧ «precise?/2» (D m) T T₂ = .ok (.atom "true") ∧
      «precise?/2» (D m) R R₂ = .ok (.atom "true") := by
  rw [upd5_del (.map X) hk hmd] at run
  obtain ⟨r, run', iffA, semA⟩ := gupd_un gX hS ovE hm
  rw [run] at run'; cases run'
  obtain ⟨onlyA, neA, fA⟩ := iffA.mp ⟨_, _, _, rfl⟩
  have lo' : ∀ q : PN t (d + 1), denD (lower a₂) q → denD (lower (.map X)) q := fun q h =>
    (denD_lower _ _).mpr (lo q ((denD_lower _ _).mp h))
  obtain ⟨X₂, rfl⟩ : ∃ X₂, a₂ = .map X₂ := by
    rcases g₂.shape with rfl | ⟨X₂, rfl⟩
    · have := onlyA bitPt (lo' bitPt (by simp [lower, denD_term]))
      simp [bitPt] at this
    · exact ⟨X₂, rfl⟩
  rw [upd5_del (.map X₂) hk hmd]
  have muA : ∀ w, MT t (d + 1) (dynL (upper (.map X))) w → MT t (d + 1) (dynL (upper (.map X₂))) w := fun w h =>
    (mt_dynL' g₂.up_tc w).mpr (up _ ((mt_dynL' gX.up_tc w).mp h))
  have msB : ∀ w, MT t (d + 1) (rmDyn X₂) w → MT t (d + 1) (rmDyn X) w := fun w h =>
    (denD_mpt w).mp ((denD_rmDyn X _).mpr (lo _ ((denD_rmDyn X₂ _).mp ((denD_mpt w).mpr h))))
  have msA : ∀ w, MT t (d + 1) (rmDyn X) w → MT t (d + 1) (dynL (upper (.map X))) w := fun w h =>
    (mt_dynL' gX.up_tc w).mpr (GC.inv gX _ ((denD_rmDyn X _).mp ((denD_mpt w).mpr h)))
  have fB : F (MT t (d + 1) (dynL (upper (.map X₂)))) (mapLookup X₂ (.atom "dynamic")).isNone := by
    cases hD₂ : mapLookup X₂ (.atom "dynamic") with
    | some _ => exact Fm _ _ muA (Fw _ _ fA)
    | none =>
      have hA : mapLookup X (.atom "dynamic") = none := Classical.byContradiction fun h => by
        obtain ⟨X₂', e, h'⟩ := kd h
        simp only [Term.map.injEq] at e; subst e; exact h' hD₂
      rw [hA] at fA
      refine Fc _ _ (fun u => ⟨muA u, fun h => ?_⟩) _ fA
      have uX₂ : upper (.map X₂) = .map X₂ := by simp [upper, hD₂]
      have uX : upper (.map X) = .map X := by simp [upper, hA]
      rw [uX₂] at h; rw [uX]
      simp only [dynL] at h ⊢
      have := msB u (by rwa [rmDyn_static hD₂])
      rwa [rmDyn_static hA] at this
  obtain ⟨r₂, run₂, iffB, semB⟩ := gupd_un g₂ hS ovE hm
  obtain ⟨T₂, R₂, er₂, rfl⟩ := iffB.mpr ⟨fun q h => onlyA q (lo' q h), let ⟨w, hw⟩ := neA; ⟨w, muA w hw⟩, fB⟩
  obtain ⟨gR, oR, lR, uR, lt, ut, lA, uA, dlA, duA, slA, suA, -⟩ := semA T R er rfl
  obtain ⟨gR₂, oR₂, lR₂, uR₂, lt₂, ut₂, lB, uB, dlB, duB, slB, suB, -⟩ := semB T₂ R₂ er₂ rfl
  have hm' : (level t d).K + 23 ≤ m := by rw [level_K] at hm ⊢; omega
  refine ⟨T₂, R₂, er₂, run₂, precise_of_bounds (n := d) hm' lA uA lB uB dlA duA dlB duB
    (fun x h => (slA x).mpr (ovm _ _ msB x ((slB x).mp h)))
    (fun x h => (suB x).mpr (((suA x).mp h).elim (fun h => Or.inr (ovm _ _ (fun u h => muA u (msA u h)) x h))
      (fun h => Or.inr (ovm _ _ muA x h)))), precise_of (n := d + 1) (by omega) gR gR₂ ?_ ?_⟩
  · refine via_mpt gR₂.shape gR.shape (fun q h => oR₂ q (GC.inv gR₂ q h)) fun w h => ?_
    obtain ⟨⟨u, hu⟩, h⟩ := (lR₂ w).mp h
    exact (lR w).mpr ⟨⟨u, msB u hu⟩, hSm _ _ msB w h⟩
  · refine via_mpt (Or.imp id (fun ⟨Y, e, _⟩ => ⟨Y, e⟩) gR.up_tc) (Or.imp id (fun ⟨Y, e, _⟩ => ⟨Y, e⟩) gR₂.up_tc)
      oR fun w h => ?_
    refine (uR₂ w).mpr (Or.inr ?_)
    rcases (uR w).mp h with ⟨-, h⟩ | h
    · exact hSm _ _ (fun u h => muA u (msA u h)) w h
    · exact hSm _ _ muA w h

/-- Deleting a gradual key type of the laws from less precise maps is less precise, as is the old type. -/
theorem del_prec_key {X : List (Term × Term)} {a₂ : Term} (gX : GC (level t (d + 1)) (.map X))
    (g₂ : GC (level t (d + 1)) a₂) {key : Term} {md : String} {m : Nat} (hmk : (level t d).K + 23 ≤ m)
    (hk' : «arrows_gradual?/2» (D (m + 1)) key (.tuple #[.integer d, t]) = .ok (.atom "true")) (hmd : Mode md)
    (hm : (level t (d + 1)).K + 30 ≤ m + 1)
    (lo : ∀ q : PN t (d + 1), denD a₂ q → denD (.map X) q)
    (up : ∀ q : PN t (d + 1), denD (upper (.map X)) q → denD (upper a₂) q)
    (kd : mapLookup X (.atom "dynamic") ≠ none → ∃ X₂, a₂ = .map X₂ ∧ mapLookup X₂ (.atom "dynamic") ≠ none)
    {T R er : Term}
    (run : Elixir.Module.Types.Descr.«map_update/5» (D (m + 1)) (.map X) key (.atom "delete") (.atom md) (.atom "true") =
      .ok (.tuple #[T, R, er])) :
    ∃ T₂ R₂ er₂, Elixir.Module.Types.Descr.«map_update/5» (D (m + 1)) a₂ key (.atom "delete") (.atom md) (.atom "true") =
        .ok (.tuple #[T₂, R₂, er₂]) ∧ «precise?/2» (D (m + 1)) T T₂ = .ok (.atom "true") ∧
      «precise?/2» (D (m + 1)) R R₂ = .ok (.atom "true") := by
  obtain ⟨s, hk, hs⟩ := key_gform (t := t) (n := d) hmk hk'
  obtain ⟨rk, Os, ng, Ds, Do, rfl, gs, hkey⟩ := gform_strs hs
  obtain ⟨rs, neg1, D2, A, ⟨ok2, nr2, -, -, -, -⟩, hY⟩ := dl_hY (t := t) (n := d + 1) hs hmd
  exact del_gprec gX g₂ hk hmd
    (supd_del gs hkey hmd (S := fun M w => DRS (level t (d + 1)).den M rs neg1 D2 A md w) hY)
    (fun M x ⟨w, hw, _⟩ => ⟨w, hw⟩) (fun M₁ M₂ h x => vals_mono h)
    (fun M₁ M₂ hM w h => drs_mono (level t (d + 1)).ef.den_none hM hmd ok2 ok2 nr2 (fun κ h => h)
      (fun a m => Or.inl m) h)
    (fun M st h => foundG_weak h) (fun M₁ M₂ h f => foundG_mono h f) (fun M₁ M₂ h st f => foundG_congr h f)
    hm lo up kd run

end


end Elixir.STTDescrProofsTest.Nest
