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

end Elixir.STTDescrProofsTest.Nest
