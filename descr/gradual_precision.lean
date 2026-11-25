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
        (.integer ((i : Int) + 1)) = .ok (boolAtom sz) ∧ (sz = Bool.true ↔ ∀ w, TT t n S w → i < w.length) := by
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
        (∀ u, TT t n (rmDyn X) u → i < u.length) ∧ ∃ u, denD Dy (tpt (t := t) (n := n) u) ∧ i < u.length) := by
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
  have tC : ∀ u, TT t n C u ↔ denD Dy (tpt (t := t) (n := n) u) ∧ i < u.length := fun u => by
    rw [← denD_tpt, sc, denD_tpt, tZ]
    exact ⟨fun ⟨a, b⟩ => ⟨a, by omega⟩, fun ⟨a, b⟩ => ⟨a, by omega⟩⟩
  obtain ⟨YA, rA, dYA, oYA, tYA⟩ := del_any dc i (fun u h => ((tC u).mp h).2) (m := k + 3) (by omega)
  have eC := next_empty dc (m := k + 3) (by omega)
  have eS := next_empty dS (m := k + 3) (by omega)
  have wrapA : getMapKeys [.atom "dynamic"] (.map YA) = [] := by
    simp [getMapKeys_single, (de_map dYA).static]
  obtain ⟨R', rR', ⟨U, eU⟩, gR', sR', uR'⟩ := gout dYA dYS (m := k + 3) (by omega)
  simp only [boolAtom, Erlang.erlang.«/=/2», Lynx.Except.tryWith, rS, rZ',
    Elixir.Module.Types.Descr.«opt_intersection/2», rc, eC, eS, rA, wrapA, rR', Lynx.Except.ok_bind]
  -- Tuples of the static part, which the dynamic part holds.
  have stat : ∀ v : PN t n, denD (.map (rmDyn X)) v → ∃ u, denD Dy (tpt (t := t) (n := n) u) ∧ i < u.length := by
    intro v hv
    have tv : v.1.1 = "tuple" := Classical.byContradiction fun ne => to v ((sR v).mpr ⟨hv, ne⟩)
    obtain ⟨w, hw⟩ := pt_tuple_de v tv
    have hw' := (hw _ dS).mp hv
    exact ⟨w, (hw _ dDy).mp (inc v ((denD_rmDyn X v).mp hv)), long w ((denD_tpt w).mp hw')⟩
  have dyn : ∀ v : PN t n, denD (.map C) v → ∃ u, denD Dy (tpt (t := t) (n := n) u) ∧ i < u.length := by
    intro v hv
    have tv : v.1.1 = "tuple" := oZ _ ((sc v).mp hv).2
    obtain ⟨w, hw⟩ := pt_tuple_de v tv
    exact ⟨w, (tC w).mp ((denD_tpt w).mp ((hw _ dc).mp hv))⟩
  by_cases both : (∀ v : PN t n, ¬denD (.map C) v) ∧ ∀ v : PN t n, ¬denD (.map (rmDyn X)) v
  · rw [bp_true.mpr both.1, bp_true.mpr both.2]
    simp [Term.true]
    intro _ _ u hu
    exact Nat.le_of_not_lt fun lu => both.1 _ ((denD_tpt u).mpr ((tC u).mpr ⟨hu, lu⟩))
  have ex : ∃ u, denD Dy (tpt (t := t) (n := n) u) ∧ i < u.length := by
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
        (∀ u, denD (lower (.map X)) (tpt (t := t) (n := n) u) → i < u.length) ∧
        ∃ u, denD (upper (.map X)) (tpt (t := t) (n := n) u) ∧ i < u.length) := by
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
      (sz = Bool.true ↔ ∀ w, TT t n S w → i ≤ w.length) := by
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
        (∀ u, TT t n (rmDyn X) u → i ≤ u.length) ∧ ∃ u, denD Dy (tpt (t := t) (n := n) u) ∧ i ≤ u.length) := by
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
  simp only [Erlang.maps.«take/2», hD, Elixir.Module.Types.Descr.«tuple_only?/1», Erlang.maps.«remove/2»]
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
  have tC : ∀ u, TT t n C u ↔ denD Dy (tpt (t := t) (n := n) u) ∧ i ≤ u.length := fun u => by
    rw [← denD_tpt, sc, denD_tpt, tZ]
  obtain ⟨YA, rA, dYA, oYA, tYA⟩ := ins_any dc oC hx i (m := k + 3) (by omega)
  have eC := next_empty dc (m := k + 3) (by omega)
  have eS := next_empty dS (m := k + 3) (by omega)
  have wrapA : getMapKeys [.atom "dynamic"] (.map YA) = [] := by
    simp [getMapKeys_single, (de_map dYA).static]
  obtain ⟨R', rR', ⟨U, eU⟩, gR', sR', uR'⟩ := gout dYA dYS (m := k + 3) (by omega)
  simp only [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2», Lynx.Except.guard, rS, rZ,
    Elixir.Module.Types.Descr.«opt_intersection/2», rc, eC, eS, rA, wrapA, Lynx.Except.ok_bind]
  have stat : ∀ v : PN t n, denD (.map (rmDyn X)) v → ∃ u, denD Dy (tpt (t := t) (n := n) u) ∧ i ≤ u.length := by
    intro v hv
    obtain ⟨w, hw⟩ := pt_tuple_de v (onlyS v hv)
    have hw' := (hw _ dS).mp hv
    exact ⟨w, (hw _ dDy).mp (inc v ((denD_rmDyn X v).mp hv)), long w ((denD_tpt w).mp hw')⟩
  have dyn : ∀ v : PN t n, denD (.map C) v → ∃ u, denD Dy (tpt (t := t) (n := n) u) ∧ i ≤ u.length := by
    intro v hv
    obtain ⟨w, hw⟩ := pt_tuple_de v (oC v hv)
    exact ⟨w, (tC w).mp ((denD_tpt w).mp ((hw _ dc).mp hv))⟩
  by_cases both : (∀ v : PN t n, ¬denD (.map C) v) ∧ ∀ v : PN t n, ¬denD (.map (rmDyn X)) v
  · rw [bp_true.mpr both.1, bp_true.mpr both.2]
    simp [Lynx.Term.isMember, Term.true]
    intro _ _ u hu
    exact Nat.lt_of_not_le fun lu => both.1 _ ((denD_tpt u).mpr ((tC u).mpr ⟨hu, lu⟩))
  have ex : ∃ u, denD Dy (tpt (t := t) (n := n) u) ∧ i ≤ u.length := by
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
      ((∃ Y, r = .map Y) ↔ TOnly t n X ∧ ∀ w, TT t n X w → i ≤ w.length) := by
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
      simp only [Elixir.Module.Types.Descr.«non_empty_tuple_only?/1», Erlang.maps.«take/2», hb]
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
        (∀ u, denD (lower (.map X)) (tpt (t := t) (n := n) u) → i ≤ u.length) ∧
        ∃ u, denD (upper (.map X)) (tpt (t := t) (n := n) u) ∧ i ≤ u.length) := by
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
        (∀ u, denD (lower (.map X)) (tpt (t := t) (n := n + 1) u) → i ≤ u.length) ∧
        ∃ u, denD (upper (.map X)) (tpt (t := t) (n := n + 1) u) ∧ i ≤ u.length) ∧
      ∀ R, r = .map R → ∀ p : PN t (n + 1), denD (.map R) p ↔
        InsAt (TT t (n + 1) (rmDyn X)) i ((level t (n + 1)).den (lower v)) p := by
  -- A static value inserts with tuple_insert_at_checked/3.
  have static : ∀ {x : Term}, (x = .atom "term" ∨ ∃ Z, x = .map Z ∧ mapLookup Z (.atom "dynamic") = none) →
      DE (level t n).E x → lower x = x →
      ∃ r, Elixir.Module.Types.Descr.«tuple_insert_at/3» (D m) (.map X) (.integer i) x = .ok r ∧
        ((∃ R, r = .map R) ↔ (∀ q : PN t (n + 1), denD (lower (.map X)) q → q.1.1 = "tuple") ∧
          (∀ u, denD (lower (.map X)) (tpt (t := t) (n := n + 1) u) → i ≤ u.length) ∧
          ∃ u, denD (upper (.map X)) (tpt (t := t) (n := n + 1) u) ∧ i ≤ u.length) ∧
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
        (∀ u, denD (lower (.map X)) (tpt (t := t) (n := n + 1) u) → i ≤ u.length) ∧
        ∃ u, denD (upper (.map X)) (tpt (t := t) (n := n + 1) u) ∧ i ≤ u.length
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
    (ne : ∃ v₁ y v₂, v₁.length = i ∧ denD Dy (tpt (t := t) (n := d + 1) (v₁ ++ y :: v₂))) :
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
      (∃ v₁ y v₂, v₁.length = i ∧ denD (upper (.map X)) (tpt (t := t) (n := d + 1) (v₁ ++ y :: v₂))) ∧
      (fl = .atom "true" ↔ ∃ w, denD (upper (.map X)) (tpt (t := t) (n := d + 1) w) ∧ w.length ≤ i) ∧
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
    obtain ⟨v₁, y, v₂, rfl, len⟩ : ∃ v₁ y v₂, w = v₁ ++ y :: v₂ ∧ v₁.length = i := by
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
    (ne : ∃ v₁ y v₂, v₁.length = i ∧ denD (upper (.map X)) (tpt (t := t) (n := d + 1) (v₁ ++ y :: v₂)))
    (long : mapLookup X (.atom "dynamic") = none →
      ∀ w, denD (upper (.map X)) (tpt (t := t) (n := d + 1) w) → i < w.length) :
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
      ∀ w, denD (upper (.map X₂)) (tpt (t := t) (n := d + 1) w) → i < w.length := by
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
      · simp only [MT, mapLookup, List.find?_nil, Option.map_none, reduceCtorEq, false_and, exists_false, false_iff]
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
  simp only [Erlang.maps.«take/2», hD]
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
    simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind]
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
        simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind]
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
    simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind]
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
    simp only [Erlang.maps.«take/2», hD]
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

end Elixir.STTDescrProofsTest.Nest
