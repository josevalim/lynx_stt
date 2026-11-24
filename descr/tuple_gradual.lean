namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-! Tuple operations on gradual types: the dynamic part and the static part are each updated as static types. -/

/-- `tuple_of_size_at_least/1`: the tuples at least that long. -/
theorem sizeT_run (i : Nat) : ∃ k : Int,
    Elixir.Module.Types.Descr.«tuple_of_size_at_least/1» (.integer i) =
      .ok (.map [(.atom "tuple", .tuple #[.integer k, .atom "open", Term.list (List.replicate i (.atom "term"))])]) ∧
    DE (level t n).E (.map [(.atom "tuple", .tuple #[.integer k, .atom "open", Term.list (List.replicate i (.atom "term"))])]) ∧
    (∀ v : PN t n, denD (.map [(.atom "tuple", .tuple #[.integer k, .atom "open",
      Term.list (List.replicate i (.atom "term"))])]) v → v.1.1 = "tuple") ∧
    ∀ w, TT t n [(.atom "tuple", .tuple #[.integer k, .atom "open", Term.list (List.replicate i (.atom "term"))])] w ↔
      i ≤ w.length := by
  obtain ⟨k, run, key⟩ := leaf_new_key "open" (Or.inl rfl) (List.replicate i (.atom "term"))
  refine ⟨k, ?_, fused_de (Or.inl rfl) (fun e me => by rw [List.eq_of_mem_replicate me]; exact (level t n).ef.term) key,
    fun v hv => ?_, tt_open i k⟩
  · have ge : (Ord.compare (i : Int) 0).isGE = Bool.true := by
      rw [Ordering.isGE_iff_ne_lt]; intro h; rw [Int.compare_eq_lt] at h; omega
    simp [Elixir.Module.Types.Descr.«tuple_of_size_at_least/1», Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2»,
      dup_nat, Elixir.Module.Types.Descr.«tuple_new/2», run, Lynx.Except.guard, Lynx.Except.andAlso, ge]
  · rw [denD_map] at hv
    by_cases h : v.1.1 = "tuple"
    · exact h
    · simp [mapLookup, h, dn_none] at hv

/-- `tuple_insert_static/3` on a static type of the next level holding only tuples: the tuples with a value inserted. -/
theorem ins_any {X : List (Term × Term)} (hX : DE (level t n).E (.map X))
    (onlyX : ∀ v : PN t n, denD (.map X) v → v.1.1 = "tuple") {x : Term} (hx : (level t n).E x) (i : Nat) {m : Nat}
    (hm : (level t n).K + 3 ≤ m) :
    ∃ Y, Elixir.Module.Types.Descr.«tuple_insert_static/3» (D m) (.map X) (.integer i) x = .ok (.map Y) ∧
      DE (level t n).E (.map Y) ∧ (∀ v : PN t n, denD (.map Y) v → v.1.1 = "tuple") ∧
      ∀ w, TT t n Y w ↔ Ins (TT t n X) i ((level t n).den x) w := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have sX := de_map hX
  cases hb : mapLookup X (.atom "tuple") with
  | none =>
    refine ⟨[], ?_, Or.inr ⟨_, rfl, descrC_nil⟩, fun v hv => by simp [denD_map, mapLookup, dn_none] at hv,
      fun w => ?_⟩
    · unfold Elixir.Module.Types.Descr.«tuple_insert_static/3»
      simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«none/0»]
    · simp only [TT, mapLookup, List.find?_nil, Option.map_none, reduceCtorEq, false_and, exists_false, false_iff]
      rintro ⟨w₁, y, w₂, -, -, -, b, hb', -⟩
      rw [hb] at hb'; cases hb'
  | some b =>
    have fb : TField (level t n).E b := fieldC_tuple (sX.fields "tuple" b hb)
    obtain ⟨res, rres⟩ := insert_static_ok (den := (level t n).den) (level t n).ef (n := k) (by omega) hb fb hx i
    obtain ⟨b', rfl, tb', sb'⟩ := insert_static (den := (level t n).den) (level t n).ef (n := k) (by omega) hb fb hx i rres
    have tt : ∀ w, TT t n X w ↔ denTF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [TT, hb]
    have ttY : ∀ w, TT t n ((.atom "tuple", b') :: X) w ↔ denTF (level t n).E (level t n).den b' w = Bool.true :=
      fun w => by simp [TT, lookup_put]
    refine ⟨_, rres, Or.inr ⟨_, rfl, descrC_put sX tb'⟩, fun v hv => ?_, fun w => ?_⟩
    · by_cases h : v.1.1 = "tuple"
      · exact h
      · apply onlyX v
        rw [denD_map] at hv ⊢
        rwa [lookup_put, ite_eq_right h] at hv
    · rw [ttY, sb']
      exact ins_congr fun u => (tt u).symm

/-- A static result as the dynamic part united with a static one: a gradual type with the static one as lower bound
and both as upper bound. -/
theorem gout {A B : List (Term × Term)} (dA : DE (level t n).E (.map A)) (dB : DE (level t n).E (.map B)) {m : Nat}
    (hm : (level t n).K + 14 ≤ m) :
    ∃ R, Elixir.Module.Types.Descr.«opt_union/2» (D m) (.map [(.atom "dynamic", .map A)]) (.map B) = .ok R ∧
      (∃ U, R = .map U) ∧ GC (level t n) R ∧ (∀ v : PN t n, denD R v ↔ denD (.map B) v) ∧
      ∀ v : PN t n, denD (upper R) v ↔ denD (.map A) v ∨ denD (.map B) v := by
  have gA : GC (level t n) (.map [(.atom "dynamic", .map A)]) := by
    refine Or.inr ⟨_, .map A, rfl, by simp [mapLookup], dA, ?_, fun v hv => ?_⟩
    · rw [show rmDyn [(Term.atom "dynamic", Term.map A)] = [] by simp [rmDyn]]; exact descrC_nil
    · rw [← denD_rmDyn, show rmDyn [(Term.atom "dynamic", Term.map A)] = [] by simp [rmDyn]] at hv
      simp [denD_map, mapLookup, dn_none] at hv
  obtain ⟨R, gR, run, s₁, s₂⟩ := gc_opt_union gA (GC.tc dB) [] (m := m) hm
  have shape : ∃ U, R = .map U := by
    by_cases nB : B = []
    · subst nB
      rw [opt_union_nil_r] at run
      exact ⟨_, (Except.ok.inj run).symm⟩
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    obtain ⟨c, -, run', -, -, U, rfl, -⟩ := merge_aligned (opt_union_op (L := level t n) (n := k + 1) (by omega) [])
      (opt_union_dyn_op (n := k) (by omega) []) (fun x y => opt_union_dyn _ x y _) gA (GC.tc dB)
    rw [opt_union_run_grad _ _ (by simp) nB (Or.inl (by simp [mapLookup]))] at run
    exact ⟨U, Except.ok.inj (run.symm.trans run')⟩
  refine ⟨R, by simpa [Elixir.Module.Types.Descr.«opt_union/2»] using run, shape, gR, fun v => ?_, fun v => ?_⟩
  · rw [s₁]
    have : ¬denD (.map [(.atom "dynamic", .map A)]) v := by
      rw [← denD_rmDyn, show rmDyn [(Term.atom "dynamic", Term.map A)] = [] by simp [rmDyn]]
      simp [denD_map, mapLookup, dn_none]
    simp [this]
  · rw [s₂, upper_dyn (Dy := .map A) (by simp [mapLookup]), upper_tc dB]

/-- The filters `tuple_insert_at_checked/3` applies to a gradual type: its static part, and that without tuples. -/
theorem filter_dyn (X : List (Term × Term)) :
    List.filter (fun entry => compareExact ((Term.atom "dynamic").fuel entry.fst) (.atom "dynamic") entry.fst != Ordering.eq) X =
      rmDyn X := rfl

theorem filter_t (Y : List (Term × Term)) :
    List.filter (fun entry => compareExact ((Term.atom "tuple").fuel entry.fst) (.atom "tuple") entry.fst != Ordering.eq) Y =
      rmT Y := rfl

theorem filter_tdyn (X : List (Term × Term)) :
    List.filter (fun a => compareExact ((Term.atom "tuple").fuel a.fst) (.atom "tuple") a.fst != Ordering.eq &&
      compareExact ((Term.atom "dynamic").fuel a.fst) (.atom "dynamic") a.fst != Ordering.eq) X = rmT (rmDyn X) := by
  simp [rmT, rmDyn, List.filter_filter, Bool.and_comm]

/-- The static size check of a static type: when it holds, every tuple is long enough. -/
theorem size_check {S : List (Term × Term)} (hS : DE (level t n).E (.map S)) (i : Nat) {m : Nat}
    (hm : (level t n).K + 1 ≤ m) :
    ∃ sz : Bool, Lynx.Except.orElse (Erlang.erlang.«==/2» (.integer i) (.integer 0))
        (Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D m) (.map S) (.integer i)) = .ok (boolAtom sz) ∧
      (sz = Bool.true → ∀ w, TT t n S w → i ≤ w.length) := by
  by_cases z : i = 0
  · subst z
    exact ⟨Bool.true, by simp [Lynx.Except.orElse, Erlang.erlang.«==/2», boolAtom], fun _ w _ => Nat.zero_le _⟩
  have eq0 : Erlang.erlang.«==/2» (.integer (i : Int)) (.integer 0) = .ok (.atom "false") := by
    simp [Erlang.erlang.«==/2»]; omega
  rw [eq0]
  simp only [Lynx.Except.orElse]
  have sS := de_map hS
  cases hb : mapLookup S (.atom "tuple") with
  | none =>
    refine ⟨Bool.true, ?_, fun _ w hw => by simp [TT, hb] at hw⟩
    unfold Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2»
    simp [getMapKeys_single, hb, boolAtom]
  | some b =>
    have fb : TField (level t n).E b := fieldC_tuple (sS.fields "tuple" b hb)
    obtain ⟨sz, rs, ss⟩ := size_at_least (level t n).ef (m := m) (by omega) fb i (by omega)
    exact ⟨sz, by rw [size_map _ hb]; exact rs, fun h w hw => ss.mp h w (by simpa [TT, hb] using hw)⟩

/-- The gradual branch of `tuple_insert_at_checked/3`: when it gives a map, the static part holds only tuples, long
enough, and the result is gradual, with the static part's tuples with a value inserted as lower bound, and those and
the long enough tuples of the dynamic part with a value inserted as upper bound. -/
theorem ins_grad {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {Dy : Term}
    (hD : mapLookup X (.atom "dynamic") = some Dy) {x : Term} (hx : (level t n).E x) (i : Nat) {m : Nat}
    (hm : (level t n).K + 26 ≤ m) {r : Term}
    (run : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (D m) (.map X) (.integer i) x = .ok r) :
    r = .atom "badindex" ∨ r = .atom "badtuple" ∨ ∃ R, r = .map R ∧ GC (level t n) (.map R) ∧ (∀ v : PN t n, denD (.map (rmDyn X)) v → v.1.1 = "tuple") ∧
      (∀ w, TT t n (rmDyn X) w → i ≤ w.length) ∧
      ∃ YS YA : List (Term × Term), DE (level t n).E (.map YS) ∧ DE (level t n).E (.map YA) ∧
        (∀ v : PN t n, denD (.map YS) v → v.1.1 = "tuple") ∧ (∀ v : PN t n, denD (.map YA) v → v.1.1 = "tuple") ∧
        (∀ w, TT t n YS w ↔ Ins (TT t n (rmDyn X)) i ((level t n).den x) w) ∧
        (∀ w, TT t n YA w ↔ Ins (fun u => denD Dy (tpt (t := t) (n := n) u) ∧ i ≤ u.length) i ((level t n).den x) w) ∧
        (∀ v : PN t n, denD (.map R) v ↔ denD (.map YS) v) ∧
        ∀ v : PN t n, denD (upper (.map R)) v ↔ denD (.map YA) v ∨ denD (.map YS) v := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  -- The parts of the gradual type.
  obtain ⟨dDy, sS⟩ : DE (level t n).E Dy ∧ DescrC (FunA (level t n).E) (TField (level t n).E) (LF (level t n).E)
      (MField (level t n).E) (rmDyn X) := by
    rcases gX with (h | ⟨X', e, sX⟩) | ⟨X', Dy', e, hD', tD, sS, -⟩
    · cases h
    · simp only [Term.map.injEq] at e; subst e; rw [sX.static] at hD; cases hD
    · simp only [Term.map.injEq] at e; subst e; rw [hD] at hD'; cases hD'; exact ⟨tD, sS⟩
  have dS : DE (level t n).E (.map (rmDyn X)) := Or.inr ⟨_, rfl, sS⟩
  obtain ⟨dR, sR⟩ := rest_tuple dS
  -- The checks.
  obtain ⟨kd, rkd⟩ : ∃ kd : Bool, Elixir.Module.Types.Descr.«descr_key?/2» Dy (.atom "tuple") = .ok (boolAtom kd) := by
    rcases dDy with rfl | ⟨DX, rfl, -⟩
    · exact ⟨Bool.true, rfl⟩
    · refine ⟨(mapLookup DX (.atom "tuple")).isSome, ?_⟩
      cases h : (mapLookup DX (.atom "tuple")).isSome <;>
        simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, boolAtom, h]
  have rto := next_empty dR (m := k + 3) (by omega)
  obtain ⟨sz, rsz, ssz⟩ := size_check dS i (m := k + 3) (by omega)
  unfold Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» at run
  simp only [Erlang.maps.«take/2», hD, Elixir.Module.Types.Descr.«tuple_only?/1», Erlang.maps.«remove/2»] at run
  simp only [filter_dyn, filter_t, rkd, rto, rsz, Lynx.Except.ok_bind] at run
  -- Failed checks give an atom.
  by_cases to : ∀ v : PN t n, ¬denD (.map (rmT (rmDyn X))) v
  rotate_left
  · rw [bp_false.mpr to] at run
    cases kd <;> cases sz <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2», Lynx.Except.guard] at run <;>
      subst run <;> simp
  rw [bp_true.mpr to] at run
  cases sz
  · cases kd <;> simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2», Lynx.Except.guard] at run <;>
      subst run <;> simp
  cases kd
  · simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2», Lynx.Except.guard] at run
    subst run; simp
  have onlyS : ∀ v : PN t n, denD (.map (rmDyn X)) v → v.1.1 = "tuple" := fun v hv =>
    Classical.byContradiction fun h => to v ((sR v).mpr ⟨hv, h⟩)
  have long := ssz rfl
  -- The static part.
  obtain ⟨YS, rS, dYS, oYS, tYS⟩ := ins_any dS onlyS hx i (m := k + 3) (by omega)
  -- The long enough tuples of the dynamic part.
  obtain ⟨kz, rZ, dZ, oZ, tZ⟩ := sizeT_run (t := t) (n := n) i
  obtain ⟨c, dc, rc, sc⟩ := (ef_next t n).opt_inter [] dDy dZ (m := k + 3) (by omega)
  obtain ⟨C, rfl⟩ : ∃ C, c = .map C := by
    rcases dc with rfl | ⟨C, rfl, -⟩
    · exfalso
      have := oZ _ ((sc (aPt (t := t) (n := n) (.atom "a"))).mp (denD_term _)).2
      simp [aPt] at this
    · exact ⟨C, rfl⟩
  have oC : ∀ v : PN t n, denD (.map C) v → v.1.1 = "tuple" := fun v hv => oZ v ((sc v).mp hv).2
  obtain ⟨YA, rA, dYA, oYA, tYA⟩ := ins_any dc oC hx i (m := k + 3) (by omega)
  have eC := next_empty dc (m := k + 3) (by omega)
  have eS := next_empty dS (m := k + 3) (by omega)
  have wrapA : getMapKeys [.atom "dynamic"] (.map YA) = [] := by
    simp [getMapKeys_single, (de_map dYA).static]
  obtain ⟨R', rR', ⟨U, eU⟩, gR', sR', uR'⟩ := gout dYA dYS (m := k + 3) (by omega)
  simp only [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2», Lynx.Except.guard, rS, rZ,
    Elixir.Module.Types.Descr.«opt_intersection/2», rc, eC, eS, rA, wrapA, rR', Lynx.Except.ok_bind] at run
  by_cases both : (∀ v : PN t n, ¬denD (.map C) v) ∧ ∀ v : PN t n, ¬denD (.map (rmDyn X)) v
  · rw [bp_true.mpr both.1, bp_true.mpr both.2] at run
    simp [Lynx.Term.isMember, Term.true, Term.false] at run
    subst run; simp
  have eR : R' = r := by
    by_cases ec : ∀ v : PN t n, ¬denD (.map C) v <;> by_cases es : ∀ v : PN t n, ¬denD (.map (rmDyn X)) v
    · exact absurd ⟨ec, es⟩ both
    all_goals
      first
      | rw [bp_true.mpr ec, bp_false.mpr es] at run
      | rw [bp_false.mpr ec, bp_true.mpr es] at run
      | rw [bp_false.mpr ec, bp_false.mpr es] at run
      simp [Lynx.Term.isMember, Term.true, Term.false, getMapKeys_single, (de_map dYA).static] at run
      exact Except.ok.inj (rR'.symm.trans run)
  subst eR eU
  right; right
  refine ⟨U, rfl, ?_⟩
  refine ⟨gR', onlyS, long, YS, YA, dYS, dYA, oYS, oYA, tYS, fun w => ?_, sR', uR'⟩
  rw [tYA]
  refine ins_congr fun u => ?_
  rw [← denD_tpt, sc, denD_tpt, tZ]


/-- `tuple_insert_at_checked/3` on a static or gradual type of the next level, when it gives a map: the static part
holds only tuples, long enough, and the result is gradual, with the static part's tuples with a value inserted as lower
bound, and those and the long enough tuples of the upper bound with a value inserted as upper bound. -/
theorem ins_checked {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {x : Term} (hx : (level t n).E x)
    (i : Nat) {m : Nat} (hm : (level t n).K + 26 ≤ m) {R : List (Term × Term)}
    (run : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (D m) (.map X) (.integer i) x = .ok (.map R)) :
    GC (level t n) (.map R) ∧ (∀ v : PN t n, denD (.map (rmDyn X)) v → v.1.1 = "tuple") ∧
      (∀ w, TT t n (rmDyn X) w → i ≤ w.length) ∧
      ∃ YS YA : List (Term × Term), DE (level t n).E (.map YS) ∧ DE (level t n).E (.map YA) ∧
        (∀ v : PN t n, denD (.map YS) v → v.1.1 = "tuple") ∧ (∀ v : PN t n, denD (.map YA) v → v.1.1 = "tuple") ∧
        (∀ w, TT t n YS w ↔ Ins (TT t n (rmDyn X)) i ((level t n).den x) w) ∧
        (∀ w, TT t n YA w ↔ Ins (fun u => denD (upper (.map X)) (tpt (t := t) (n := n) u) ∧ i ≤ u.length) i
          ((level t n).den x) w) ∧
        (∀ v : PN t n, denD (.map R) v ↔ denD (.map YS) v) ∧
        ∀ v : PN t n, denD (upper (.map R)) v ↔ denD (.map YA) v ∨ denD (.map YS) v := by
  cases hD : mapLookup X (.atom "dynamic") with
  | some Dy =>
    rw [upper_dyn hD]
    rcases ins_grad gX hD hx i hm run with h | h | ⟨R', e, h⟩
    · cases h
    · cases h
    · cases e; exact h
  | none =>
    have dX : DE (level t n).E (.map X) := GC.static gX hD
    obtain ⟨onlyX, long, dY, onlyY, ttY⟩ := insert_tuple dX hx i (by omega) run
    have e : rmDyn X = X := rmDyn_static hD
    have uX : upper (.map X) = .map X := upper_tc dX
    have uR : upper (.map R) = .map R := upper_tc dY
    rw [e, uX, uR]
    refine ⟨GC.tc dY, onlyX.1, long, R, R, dY, dY, onlyY, onlyY, ttY, fun w => ?_, fun v => Iff.rfl,
      fun v => (or_self_iff).symm⟩
    rw [ttY]
    exact ins_congr fun u => by rw [denD_tpt]; exact ⟨fun h => ⟨h, long u h⟩, fun h => h.1⟩

/-- `tuple_insert_at_checked/3` on a static type gives an index error, a tuple error, or a map. -/
theorem ins_static_shape {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {x : Term} (hx : (level t n).E x)
    (i : Nat) {m : Nat} (hm : (level t n).K + 25 ≤ m) {r : Term}
    (run : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (D m) (.map X) (.integer i) x = .ok r) :
    r = .atom "badindex" ∨ r = .atom "badtuple" ∨ ∃ Y, r = .map Y := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have sX := de_map hX
  have ef := (level t n).ef
  unfold Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» at run
  simp only [Erlang.maps.«take/2», sX.static, Lynx.Except.ok_bind] at run
  cases hb : mapLookup X (.atom "tuple") with
  | none =>
    right; left
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso,
      Lynx.Except.guard] at run
    split at run
    · simp [Erlang.erlang.«/=/2»] at run; exact run.symm
    · cases h : Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D (k + 3)) (.map X) (.integer i) <;>
        simp [h, Erlang.erlang.«/=/2»] at run <;> exact run.symm
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
      rw [show (List.filter (fun entry => compareExact (fuel (.atom "tuple") entry.fst) (.atom "tuple") entry.fst != Ordering.eq) X) = rmT X from rfl]
      simp only [Lynx.Except.ok_bind, rE, reb (k + 3) (by omega)]
      cases bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) <;> cases eb <;>
        simp [Lynx.Except.andAlso, Erlang.erlang.«not/1», boolAtom]
    have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "tuple") = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
    -- The size check.
    obtain ⟨sz, rsz, ssz⟩ : ∃ sz : Bool, Lynx.Except.orElse (Erlang.erlang.«==/2» (.integer i) (.integer 0))
        (Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D (k + 3)) (.map X) (.integer i)) = .ok (boolAtom sz) ∧
        (sz = Bool.true → ∀ w, TT t n X w → i ≤ w.length) := by
      by_cases z : i = 0
      · subst z
        exact ⟨Bool.true, by simp [Lynx.Except.orElse, Erlang.erlang.«==/2», boolAtom], fun _ w _ => Nat.zero_le _⟩
      · obtain ⟨sz, rs, ss⟩ := size_at_least (level t n).ef (m := k + 3) (by omega) fb i (by omega)
        refine ⟨sz, ?_, fun h w hw => ss.mp h w ((tt w).mp hw)⟩
        have eq0 : Erlang.erlang.«==/2» (.integer (i : Int)) (.integer 0) = .ok (.atom "false") := by
          simp [Erlang.erlang.«==/2»]; omega
        rw [size_map _ hb, eq0]
        simpa [Lynx.Except.orElse] using rs
    obtain ⟨c, rc, sc⟩ : ∃ c : Bool, Elixir.Module.Types.Descr.«non_empty_tuple_only?/1» (D (k + 3)) (.map X) =
        .ok (boolAtom c) ∧ (c = Bool.true → TOnly t n X) := by
      refine ⟨_, nonEmpty, fun h => only.mpr ?_⟩
      simp only [Bool.and_eq_true, bp_true, Bool.not_eq_true'] at h
      exact h
    simp only [key, rc, rsz] at run
    cases c <;> cases sz <;>
      simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2», pure, Except.pure] at run
    all_goals first
      | (subst run; simp)
      | (obtain ⟨b', e, -, -⟩ := insert_static (den := (level t n).den) (level t n).ef (n := k) (by omega) hb fb hx i run
         exact Or.inr (Or.inr ⟨_, e⟩))

/-- `tuple_insert_at_checked/3` on a static or gradual type gives an index error, a tuple error, or a map. -/
theorem ins_shape {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {x : Term} (hx : (level t n).E x)
    (i : Nat) {m : Nat} (hm : (level t n).K + 26 ≤ m) {r : Term}
    (run : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (D m) (.map X) (.integer i) x = .ok r) :
    r = .atom "badindex" ∨ r = .atom "badtuple" ∨ ∃ Y, r = .map Y := by
  cases hD : mapLookup X (.atom "dynamic") with
  | none => exact ins_static_shape (GC.static gX hD) hx i (by omega) run
  | some Dy =>
    rcases ins_grad gX hD hx i hm run with h | h | ⟨R, e, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨R, e⟩)

/-- Points of tuples with a value inserted. -/
def InsAt (P : List (level t n).V → Prop) (i : Nat) (Q : (level t n).V → Prop) (p : PN t n) : Prop :=
  ∃ w, (∀ Y : List (Term × Term), denD (.map Y) p ↔ TT t n Y w) ∧ Ins P i Q w

/-- A type of tuples only, with a value inserted: the points `InsAt` gives. -/
theorem inSat {Y : List (Term × Term)} (oY : ∀ p : PN t n, denD (.map Y) p → p.1.1 = "tuple")
    {P : List (level t n).V → Prop} {i : Nat} {Q : (level t n).V → Prop} (tY : ∀ w, TT t n Y w ↔ Ins P i Q w)
    (p : PN t n) : denD (.map Y) p ↔ InsAt P i Q p := by
  by_cases hp : p.1.1 = "tuple"
  · obtain ⟨w₀, h₀⟩ := pt_tuple p hp
    constructor
    · intro h; exact ⟨w₀, h₀, (tY w₀).mp ((h₀ Y).mp h)⟩
    · rintro ⟨w, hw, hi⟩; exact (hw Y).mpr ((tY w).mpr hi)
  · refine ⟨fun h => absurd (oY p h) hp, fun ⟨w, hw, _⟩ => ?_⟩
    have := (hw [(.atom "tuple", .tuple #[.integer 0, .atom "open", Term.list (List.replicate 0 (.atom "term"))])]).mpr
      ((tt_open 0 0 w).mpr (Nat.zero_le _))
    rw [denD_map] at this
    simp [mapLookup, hp, dn_none] at this

theorem insAt_or {P P' : List (level t n).V → Prop} {i : Nat} {Q : (level t n).V → Prop} {p : PN t n} :
    InsAt (fun u => P u ∨ P' u) i Q p ↔ InsAt P i Q p ∨ InsAt P' i Q p := by
  constructor
  · rintro ⟨w, hw, hi⟩
    rcases ins_or.mp hi with h | h
    · exact Or.inl ⟨w, hw, h⟩
    · exact Or.inr ⟨w, hw, h⟩
  · rintro (⟨w, hw, h⟩ | ⟨w, hw, h⟩)
    · exact ⟨w, hw, ins_or.mpr (Or.inl h)⟩
    · exact ⟨w, hw, ins_or.mpr (Or.inr h)⟩

theorem insAt_q {P : List (level t n).V → Prop} {i : Nat} {Q Q' : (level t n).V → Prop} (hQ : ∀ y, Q y → Q' y)
    {p : PN t n} (h : InsAt P i Q p) : InsAt P i Q' p :=
  let ⟨w, hw, w₁, y, w₂, e, len, hy, hp⟩ := h
  ⟨w, hw, w₁, y, w₂, e, len, hQ y hy, hp⟩

theorem insAt_qor {P : List (level t n).V → Prop} {i : Nat} {Q Q' : (level t n).V → Prop} {p : PN t n} :
    InsAt P i (fun y => Q y ∨ Q' y) p ↔ InsAt P i Q p ∨ InsAt P i Q' p := by
  constructor
  · rintro ⟨w, hw, w₁, y, w₂, e, len, hy | hy, hp⟩
    · exact Or.inl ⟨w, hw, w₁, y, w₂, e, len, hy, hp⟩
    · exact Or.inr ⟨w, hw, w₁, y, w₂, e, len, hy, hp⟩
  · rintro (h | h)
    · exact insAt_q (fun y h => Or.inl h) h
    · exact insAt_q (fun y h => Or.inr h) h

theorem insAt_congr {P P' : List (level t n).V → Prop} {i : Nat} {Q : (level t n).V → Prop} (h : ∀ u, P u ↔ P' u)
    {p : PN t n} : InsAt P i Q p ↔ InsAt P' i Q p := by
  simp only [InsAt, ins_congr h]

/-- `ins_checked` as points: the bounds of the result. -/
theorem ins_checked_pts {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {x : Term} (hx : (level t n).E x)
    (i : Nat) {m : Nat} (hm : (level t n).K + 26 ≤ m) {R : List (Term × Term)}
    (run : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (D m) (.map X) (.integer i) x = .ok (.map R)) :
    GC (level t n) (.map R) ∧ (∀ v : PN t n, denD (.map (rmDyn X)) v → v.1.1 = "tuple") ∧
      (∀ w, TT t n (rmDyn X) w → i ≤ w.length) ∧
      (∀ p : PN t n, denD (.map R) p ↔ InsAt (TT t n (rmDyn X)) i ((level t n).den x) p) ∧
      ∀ p : PN t n, denD (upper (.map R)) p ↔ InsAt (fun u => (denD (upper (.map X)) (tpt (t := t) (n := n) u) ∧
        i ≤ u.length) ∨ TT t n (rmDyn X) u) i ((level t n).den x) p := by
  obtain ⟨gR, oS, long, YS, YA, -, -, oYS, oYA, tYS, tYA, sR, uR⟩ := ins_checked gX hx i hm run
  refine ⟨gR, oS, long, fun p => (sR p).trans (inSat oYS tYS p), fun p => ?_⟩
  rw [uR, inSat oYA tYA, inSat oYS tYS, insAt_or]

end

section
variable {t : Term} {n : Nat}

/-- The dynamic wrapper of a gradual result: its upper bound as dynamic part. -/
theorem wrap_gc {R : List (Term × Term)} (gR : GC (level t n) (.map R)) :
    GC (level t n) (.map [(.atom "dynamic", upper (.map R))]) ∧
      (∀ p : PN t n, ¬denD (.map [(.atom "dynamic", upper (.map R))]) p) ∧
      upper (.map [(.atom "dynamic", upper (.map R))]) = upper (.map R) := by
  have e : rmDyn [(Term.atom "dynamic", upper (.map R))] = [] := by simp [rmDyn]
  have none : ∀ p : PN t n, ¬denD (.map [(.atom "dynamic", upper (.map R))]) p := fun p h => by
    rw [← denD_rmDyn, e] at h
    simp [denD_map, mapLookup, dn_none] at h
  refine ⟨Or.inr ⟨_, _, rfl, by simp [mapLookup], gR.up_tc, by rw [e]; exact descrC_nil,
    fun p h => absurd h (none p)⟩, none, upper_dyn (by simp [mapLookup])⟩

/-- `tuple_insert_at/3` of a static or gradual value into a static or gradual type of tuples, when it gives a map: a
gradual type whose upper bound holds the long enough tuples of the upper bound and the tuples of the static part with
a value of the value's upper bound inserted, and, for a static value, whose static part holds the tuples of the static
part with a value inserted. -/
theorem ins_at {X : List (Term × Term)} (gX : GC (level t (n + 1)) (.map X)) {v : Term} (gv : GC (level t n) v)
    (dlo : DE (level t n).E (lower v)) (dup : DE (level t n).E (upper v)) (i : Nat) {m : Nat}
    (hm : (level t (n + 1)).K + 26 ≤ m) {R : List (Term × Term)}
    (run : Elixir.Module.Types.Descr.«tuple_insert_at/3» (D m) (.map X) (.integer i) v = .ok (.map R)) :
    GC (level t (n + 1)) (.map R) ∧
      (∀ p : PN t (n + 1), denD (upper (.map R)) p ↔ InsAt (fun u => (denD (upper (.map X))
        (tpt (t := t) (n := n + 1) u) ∧ i ≤ u.length) ∨ TT t (n + 1) (rmDyn X) u) i
        ((level t (n + 1)).den (upper v)) p) ∧
      (upper v = v → ∀ p : PN t (n + 1), denD (.map R) p ↔ InsAt (TT t (n + 1) (rmDyn X)) i
        ((level t (n + 1)).den v) p) := by
  -- A static value.
  have static : (v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) → upper v = v →
      GC (level t (n + 1)) (.map R) ∧
      (∀ p : PN t (n + 1), denD (upper (.map R)) p ↔ InsAt (fun u => (denD (upper (.map X))
        (tpt (t := t) (n := n + 1) u) ∧ i ≤ u.length) ∨ TT t (n + 1) (rmDyn X) u) i
        ((level t (n + 1)).den (upper v)) p) ∧
      (upper v = v → ∀ p : PN t (n + 1), denD (.map R) p ↔ InsAt (TT t (n + 1) (rmDyn X)) i
        ((level t (n + 1)).den v) p) := by
    intro sv uv
    rw [insert_at_static _ _ _ sv] at run
    have hx : (level t (n + 1)).E v := Or.inl (uv ▸ dup)
    obtain ⟨gR, -, -, sR, uR⟩ := ins_checked_pts gX hx i hm run
    rw [uv]
    exact ⟨gR, uR, fun _ => sR⟩
  rcases gv.cases with rfl | ⟨V, rfl, hV⟩ | ⟨V, rfl, hV⟩ | ⟨V, Y, rfl, hV, hY⟩
  · exact static (Or.inl rfl) rfl
  · exact static (Or.inr ⟨V, rfl, hV⟩) (by simp [upper, hV])
  all_goals
    obtain ⟨Dv, hD⟩ : ∃ Dv, mapLookup V (.atom "dynamic") = some Dv := ⟨_, hV⟩
    have uV : upper (.map V) = Dv := upper_dyn hD
    rw [uV] at dup ⊢
    have hx₁ : (level t (n + 1)).E Dv := Or.inl dup
    have notS : Dv ≠ .map V := fun e => by
      rcases dup with h | ⟨Z, h, sZ⟩
      · rw [e] at h; cases h
      · rw [e] at h; cases h; rw [sZ.static] at hD; cases hD
    -- The values of the static part are values of the dynamic part.
    have sub : ∀ y, (level t (n + 1)).den (lower (.map V)) y → (level t (n + 1)).den Dv y := fun y hy => by
      have h₁ : denD (.map (rmDyn V)) y := (denN_of dlo.notT).mp hy
      have h₂ : denD (upper (.map V)) y := gv.inv y ((denD_rmDyn V y).mp h₁)
      rw [uV] at h₂
      exact (denN_of dup.notT).mpr h₂
    rw [Elixir.Module.Types.Descr.«tuple_insert_at/3».eq_def] at run
    simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare,
      Erlang.maps.«take/2», hD] at run
    cases hr1 : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (D m) (.map X) (.integer i) Dv with
    | error e => simp [hr1] at run
    | ok r₁ =>
    rw [hr1] at run
    rcases ins_shape gX hx₁ i hm hr1 with rfl | rfl | ⟨R₁, rfl⟩
    · simp [Erlang.erlang.«is_map/1», Erlang.erlang.«==/2», Lynx.Except.orElse, Lynx.Except.tryWith] at run
    · simp [Erlang.erlang.«is_map/1», Erlang.erlang.«==/2», Lynx.Except.orElse, Lynx.Except.tryWith] at run
    obtain ⟨gR₁, -, -, -, uR₁⟩ := ins_checked_pts gX hx₁ i hm hr1
    obtain ⟨gW, nW, uW⟩ := wrap_gc gR₁
    have eS := next_empty dlo (m := m) (by rw [level_K] at hm ⊢; omega)
    simp only [lower] at eS
    have hx₂ : (level t (n + 1)).E (.map (rmDyn V)) := Or.inl dlo
    cases hR : mapLookup R₁ (.atom "dynamic") with
    | none =>
      have e : upper (.map R₁) = .map R₁ := by simp [upper, hR]
      simp [Erlang.erlang.«is_map/1», Lynx.Except.orElse, Lynx.Except.tryWith, getMapKeys_single, hR, filter_dyn] at run
      rw [show Term.map [(.atom "dynamic", .map R₁)] = Term.map [(.atom "dynamic", upper (.map R₁))] by rw [e]] at run
      rw [eS] at run
      by_cases es : ∀ p : PN t n, ¬denD (.map (rmDyn V)) p
      · rw [bp_true.mpr es] at run
        simp [boolAtom] at run
        rw [← run]
        exact ⟨gW, fun p => by rw [uW, uR₁], fun h => absurd h notS⟩
      · rw [bp_false.mpr es] at run
        simp [boolAtom] at run
        cases hr2 : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (D m) (.map X) (.integer i)
            (.map (rmDyn V)) with
        | error e => simp [hr2] at run
        | ok r₂ =>
        rw [hr2] at run
        rcases ins_shape gX hx₂ i hm hr2 with rfl | rfl | ⟨R₂, rfl⟩
        · simp [Erlang.erlang.«==/2»] at run
        · simp [Erlang.erlang.«==/2»] at run
        obtain ⟨gR₂, -, -, -, uR₂⟩ := ins_checked_pts gX hx₂ i hm hr2
        obtain ⟨c, gc, rc, -, sc⟩ := gc_opt_union gW gR₂ [] (m := m) (by rw [level_K] at hm ⊢; omega)
        simp [Elixir.Module.Types.Descr.«opt_union/2», rc] at run
        subst run
        refine ⟨gc, fun p => ?_, fun h => absurd h notS⟩
        rw [sc, uW, uR₁, uR₂]
        exact ⟨fun h' => h'.elim id (insAt_q sub), Or.inl⟩
    | some d =>
      have e : upper (.map R₁) = d := upper_dyn hR
      simp [Erlang.erlang.«is_map/1», Lynx.Except.orElse, Lynx.Except.tryWith, getMapKeys_single, hR, filter_dyn] at run
      rw [← e] at run
      rw [eS] at run
      by_cases es : ∀ p : PN t n, ¬denD (.map (rmDyn V)) p
      · rw [bp_true.mpr es] at run
        simp [boolAtom] at run
        rw [← run]
        exact ⟨gW, fun p => by rw [uW, uR₁], fun h => absurd h notS⟩
      · rw [bp_false.mpr es] at run
        simp [boolAtom] at run
        cases hr2 : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (D m) (.map X) (.integer i)
            (.map (rmDyn V)) with
        | error e => simp [hr2] at run
        | ok r₂ =>
        rw [hr2] at run
        rcases ins_shape gX hx₂ i hm hr2 with rfl | rfl | ⟨R₂, rfl⟩
        · simp [Erlang.erlang.«==/2»] at run
        · simp [Erlang.erlang.«==/2»] at run
        obtain ⟨gR₂, -, -, -, uR₂⟩ := ins_checked_pts gX hx₂ i hm hr2
        obtain ⟨c, gc, rc, -, sc⟩ := gc_opt_union gW gR₂ [] (m := m) (by rw [level_K] at hm ⊢; omega)
        simp [Elixir.Module.Types.Descr.«opt_union/2», rc] at run
        subst run
        refine ⟨gc, fun p => ?_, fun h => absurd h notS⟩
        rw [sc, uW, uR₁, uR₂]
        exact ⟨fun h' => h'.elim id (insAt_q sub), Or.inl⟩

end

section
variable {V : Type}

/-- Lists with the element at an index removed. -/
def Del (P : List V → Prop) (i : Nat) (w : List V) : Prop :=
  ∃ v₁ y v₂, w = v₁ ++ v₂ ∧ v₁.length = i ∧ P (v₁ ++ y :: v₂)

theorem del_congr {P P' : List V → Prop} {i : Nat} {w : List V} (h : ∀ u, P u ↔ P' u) : Del P i w ↔ Del P' i w := by
  simp only [Del, h]

theorem del_or {P P' : List V → Prop} {i : Nat} {w : List V} :
    Del (fun u => P u ∨ P' u) i w ↔ Del P i w ∨ Del P' i w := by
  constructor
  · rintro ⟨v₁, y, v₂, e, len, h | h⟩
    · exact Or.inl ⟨v₁, y, v₂, e, len, h⟩
    · exact Or.inr ⟨v₁, y, v₂, e, len, h⟩
  · rintro (⟨v₁, y, v₂, e, len, h⟩ | ⟨v₁, y, v₂, e, len, h⟩)
    · exact ⟨v₁, y, v₂, e, len, Or.inl h⟩
    · exact ⟨v₁, y, v₂, e, len, Or.inr h⟩

end

section
variable {t : Term} {n : Nat}

/-- Points of tuples with an element removed. -/
def TDelAt (P : List (level t n).V → Prop) (i : Nat) (p : PN t n) : Prop :=
  ∃ w, (∀ Y : List (Term × Term), denD (.map Y) p ↔ TT t n Y w) ∧ Del P i w

theorem tdelSat {Y : List (Term × Term)} (oY : ∀ p : PN t n, denD (.map Y) p → p.1.1 = "tuple")
    {P : List (level t n).V → Prop} {i : Nat} (tY : ∀ w, TT t n Y w ↔ Del P i w) (p : PN t n) :
    denD (.map Y) p ↔ TDelAt P i p := by
  by_cases hp : p.1.1 = "tuple"
  · obtain ⟨w₀, h₀⟩ := pt_tuple p hp
    constructor
    · intro h; exact ⟨w₀, h₀, (tY w₀).mp ((h₀ Y).mp h)⟩
    · rintro ⟨w, hw, hi⟩; exact (hw Y).mpr ((tY w).mpr hi)
  · refine ⟨fun h => absurd (oY p h) hp, fun ⟨w, hw, _⟩ => ?_⟩
    have := (hw [(.atom "tuple", .tuple #[.integer 0, .atom "open", Term.list (List.replicate 0 (.atom "term"))])]).mpr
      ((tt_open 0 0 w).mpr (Nat.zero_le _))
    rw [denD_map] at this
    simp [mapLookup, hp, dn_none] at this

theorem tdelAt_or {P P' : List (level t n).V → Prop} {i : Nat} {p : PN t n} :
    TDelAt (fun u => P u ∨ P' u) i p ↔ TDelAt P i p ∨ TDelAt P' i p := by
  constructor
  · rintro ⟨w, hw, hi⟩
    rcases del_or.mp hi with h | h
    · exact Or.inl ⟨w, hw, h⟩
    · exact Or.inr ⟨w, hw, h⟩
  · rintro (⟨w, hw, h⟩ | ⟨w, hw, h⟩)
    · exact ⟨w, hw, del_or.mpr (Or.inl h)⟩
    · exact ⟨w, hw, del_or.mpr (Or.inr h)⟩

theorem tdelAt_congr {P P' : List (level t n).V → Prop} {i : Nat} (h : ∀ u, P u ↔ P' u) {p : PN t n} :
    TDelAt P i p ↔ TDelAt P' i p := by
  simp only [TDelAt, del_congr h]

/-- `tuple_delete_static/2` on a static type of the next level with long tuples: those tuples without the element. -/
theorem del_any {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (i : Nat)
    (long : ∀ w, TT t n X w → i < w.length) {m : Nat} (hm : (level t n).K + 4 ≤ m) :
    ∃ Y, Elixir.Module.Types.Descr.«tuple_delete_static/2» (D m) (.map X) (.integer i) = .ok (.map Y) ∧
      DE (level t n).E (.map Y) ∧ (∀ v : PN t n, denD (.map Y) v → v.1.1 = "tuple") ∧
      ∀ w, TT t n Y w ↔ Del (TT t n X) i w := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have sX := de_map hX
  cases hb : mapLookup X (.atom "tuple") with
  | none =>
    refine ⟨[], ?_, Or.inr ⟨_, rfl, descrC_nil⟩, fun v hv => by simp [denD_map, mapLookup, dn_none] at hv,
      fun w => ?_⟩
    · unfold Elixir.Module.Types.Descr.«tuple_delete_static/2»
      simp [getMapKeys_single, hb]
    · simp only [TT, mapLookup, List.find?_nil, Option.map_none, reduceCtorEq, false_and, exists_false, false_iff]
      rintro ⟨v₁, y, v₂, -, -, b, hb', -⟩
      rw [hb] at hb'; cases hb'
  | some b =>
    have fb : TField (level t n).E b := fieldC_tuple (sX.fields "tuple" b hb)
    have tt : ∀ w, TT t n X w ↔ denTF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [TT, hb]
    have wb : Bdd (TLit (level t n).E) b := by
      rcases fb with ⟨k', rfl⟩ | wb
      · have := long [] ((tt []).mpr (denTF_top _ _)); simp at this
      · exact wb
    obtain ⟨r, rr, tr, sr⟩ := delete_static (den := (level t n).den) (level t n).ef (n := k) (by omega) hb wb i
      fun v hv => long v ((tt v).mpr hv)
    refine ⟨_, rr, Or.inr ⟨_, rfl, descrC_put descrC_nil tr⟩, fun v hv => ?_, fun w => ?_⟩
    · rw [denD_map] at hv
      by_cases h : v.1.1 = "tuple"
      · exact h
      · simp [mapLookup, h, dn_none] at hv
    · simp only [TT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some,
        Option.some.injEq, exists_eq_left', sr]
      simp only [Del, tt]

/-- The static size check after the deleted element. -/
theorem size_check1 {S : List (Term × Term)} (hS : DE (level t n).E (.map S)) (i : Nat) {m : Nat}
    (hm : (level t n).K + 1 ≤ m) :
    ∃ sz : Bool, Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D m) (.map S)
        (.integer ((i : Int) + 1)) = .ok (boolAtom sz) ∧ (sz = Bool.true → ∀ w, TT t n S w → i < w.length) := by
  have sS := de_map hS
  cases hb : mapLookup S (.atom "tuple") with
  | none =>
    refine ⟨Bool.true, ?_, fun _ w hw => by simp [TT, hb] at hw⟩
    unfold Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2»
    simp [getMapKeys_single, hb, boolAtom]
  | some b =>
    have fb : TField (level t n).E b := fieldC_tuple (sS.fields "tuple" b hb)
    obtain ⟨sz, rs, ss⟩ := size_at_least (level t n).ef (m := m) (by omega) fb (i + 1) (by omega)
    exact ⟨sz, by rw [size_map _ hb]; simpa using rs, fun h w hw => ss.mp h w (by simpa [TT, hb] using hw)⟩

end

section
variable {t : Term} {n : Nat}

/-- The gradual branch of `tuple_delete_at/2`: when it gives something else than an error, the static part holds only
tuples, long enough, and the result is gradual, with the static part's tuples without the element as lower bound, and
those and the long enough tuples of the dynamic part without the element as upper bound. -/
theorem del_grad {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {Dy : Term}
    (hD : mapLookup X (.atom "dynamic") = some Dy) (i : Nat) {m : Nat}
    (hm : (level t n).K + 26 ≤ m) {r : Term}
    (run : Elixir.Module.Types.Descr.«tuple_delete_at/2» (D m) (.map X) (.integer i) = .ok r) :
    r = .atom "badindex" ∨ r = .atom "badtuple" ∨ ∃ R, r = .map R ∧ GC (level t n) (.map R) ∧
      ∃ YS YA : List (Term × Term), DE (level t n).E (.map YS) ∧ DE (level t n).E (.map YA) ∧
        (∀ v : PN t n, denD (.map YS) v → v.1.1 = "tuple") ∧ (∀ v : PN t n, denD (.map YA) v → v.1.1 = "tuple") ∧
        (∀ w, TT t n YS w ↔ Del (TT t n (rmDyn X)) i w) ∧
        (∀ w, TT t n YA w ↔ Del (fun u => denD Dy (tpt (t := t) (n := n) u) ∧ i < u.length) i w) ∧
        (∀ v : PN t n, denD (.map R) v ↔ denD (.map YS) v) ∧
        ∀ v : PN t n, denD (upper (.map R)) v ↔ denD (.map YA) v ∨ denD (.map YS) v := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  obtain ⟨dDy, sS⟩ : DE (level t n).E Dy ∧ DescrC (FunA (level t n).E) (TField (level t n).E) (LF (level t n).E)
      (MField (level t n).E) (rmDyn X) := by
    rcases gX with (h | ⟨X', e, sX⟩) | ⟨X', Dy', e, hD', tD, sS, -⟩
    · cases h
    · simp only [Term.map.injEq] at e; subst e; rw [sX.static] at hD; cases hD
    · simp only [Term.map.injEq] at e; subst e; rw [hD] at hD'; cases hD'; exact ⟨tD, sS⟩
  have dS : DE (level t n).E (.map (rmDyn X)) := Or.inr ⟨_, rfl, sS⟩
  obtain ⟨dR, sR⟩ := rest_tuple dS
  obtain ⟨kd, rkd⟩ : ∃ kd : Bool, Elixir.Module.Types.Descr.«descr_key?/2» Dy (.atom "tuple") = .ok (boolAtom kd) := by
    rcases dDy with rfl | ⟨DX, rfl, -⟩
    · exact ⟨Bool.true, rfl⟩
    · refine ⟨(mapLookup DX (.atom "tuple")).isSome, ?_⟩
      cases h : (mapLookup DX (.atom "tuple")).isSome <;>
        simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, boolAtom, h]
  have rto := next_empty dR (m := k + 3) (by omega)
  obtain ⟨sz, rsz, ssz⟩ := size_check1 dS i (m := k + 3) (by omega)
  rw [Elixir.Module.Types.Descr.«tuple_delete_at/2».eq_def] at run
  simp [Lynx.Except.andAlso, Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Int.isGE_compare,
    Erlang.maps.«take/2», hD, Elixir.Module.Types.Descr.«tuple_only?/1», Erlang.maps.«remove/2»] at run
  simp only [filter_dyn, filter_t, filter_tdyn, rkd, rto, rsz] at run
  by_cases to : ∀ v : PN t n, ¬denD (.map (rmT (rmDyn X))) v
  rotate_left
  · rw [bp_false.mpr to] at run
    cases kd <;> cases sz <;> simp [boolAtom, Erlang.erlang.«/=/2», Lynx.Except.tryWith] at run <;>
      subst run <;> simp
  rw [bp_true.mpr to] at run
  cases kd
  · simp [boolAtom, Erlang.erlang.«/=/2», Lynx.Except.tryWith] at run; subst run; simp
  cases sz
  · simp [boolAtom, Erlang.erlang.«/=/2», Lynx.Except.tryWith] at run; subst run; simp
  have long := ssz rfl
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
    Elixir.Module.Types.Descr.«opt_intersection/2», rc, eC, eS, rA, wrapA, rR', Lynx.Except.ok_bind] at run
  by_cases both : (∀ v : PN t n, ¬denD (.map C) v) ∧ ∀ v : PN t n, ¬denD (.map (rmDyn X)) v
  · rw [bp_true.mpr both.1, bp_true.mpr both.2] at run
    simp [Lynx.Term.isMember, Term.true, Term.false] at run
    subst run; simp
  have eR : R' = r := by
    by_cases ec : ∀ v : PN t n, ¬denD (.map C) v <;> by_cases es : ∀ v : PN t n, ¬denD (.map (rmDyn X)) v
    · exact absurd ⟨ec, es⟩ both
    all_goals
      first
      | rw [bp_true.mpr ec, bp_false.mpr es] at run
      | rw [bp_false.mpr ec, bp_true.mpr es] at run
      | rw [bp_false.mpr ec, bp_false.mpr es] at run
      simp [Lynx.Term.isMember, Term.true, Term.false, getMapKeys_single, (de_map dYA).static, rR'] at run
      exact run
  subst eR eU
  right; right
  refine ⟨U, rfl, gR', YS, YA, dYS, dYA, oYS, oYA, tYS, fun w => ?_, sR', uR'⟩
  rw [tYA]
  exact del_congr tC

end

section
variable {t : Term} {n : Nat}

/-- The static result of `tuple_delete_at/2` as a type of tuples. -/
theorem del_static_pts {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (i : Nat) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) {R : List (Term × Term)}
    (run : Elixir.Module.Types.Descr.«tuple_delete_at/2» (D m) (.map X) (.integer i) = .ok (.map R)) :
    TOnly t n X ∧ (∀ w, TT t n X w → i < w.length) ∧ DE (level t n).E (.map R) ∧
      (∀ v : PN t n, denD (.map R) v → v.1.1 = "tuple") ∧ ∀ w, TT t n R w ↔ Del (TT t n X) i w := by
  obtain ⟨res, rres, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨only, short, r, rfl, tr, sr⟩⟩ := delete_cases hX i hm
  · rw [run] at rres; cases rres
  · rw [run] at rres; cases rres
  rw [run] at rres
  cases rres
  have long : ∀ w, TT t n X w → i < w.length := fun w hw =>
    Classical.byContradiction fun h => short ⟨w, hw, by omega⟩
  refine ⟨only, long, Or.inr ⟨_, rfl, descrC_put descrC_nil tr⟩, fun v hv => ?_, fun w => ?_⟩
  · rw [denD_map] at hv
    by_cases h : v.1.1 = "tuple"
    · exact h
    · simp [mapLookup, h, dn_none] at hv
  · simp only [TT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some,
      Option.some.injEq, exists_eq_left', sr]
    rfl

/-- `tuple_delete_at/2` on a static or gradual type of tuples, when it gives a map: a gradual type whose static part
holds the tuples of the static part without the element, and whose upper bound holds those and the long enough tuples
of the upper bound without the element. -/
theorem del_pts {X : List (Term × Term)} (gX : GC (level t n) (.map X)) (i : Nat) {m : Nat}
    (hm : (level t n).K + 26 ≤ m) {R : List (Term × Term)}
    (run : Elixir.Module.Types.Descr.«tuple_delete_at/2» (D m) (.map X) (.integer i) = .ok (.map R)) :
    GC (level t n) (.map R) ∧ (∀ p : PN t n, denD (.map R) p ↔ TDelAt (TT t n (rmDyn X)) i p) ∧
      (∀ p : PN t n, denD (upper (.map R)) p ↔ TDelAt (fun u => (denD (upper (.map X)) (tpt (t := t) (n := n) u) ∧
        i < u.length) ∨ TT t n (rmDyn X) u) i p) ∧
      (∀ u, denD (.map R) (tpt (t := t) (n := n) u) ↔ Del (TT t n (rmDyn X)) i u) ∧
      ∀ u, denD (upper (.map R)) (tpt (t := t) (n := n) u) ↔ Del (fun u => (denD (upper (.map X))
        (tpt (t := t) (n := n) u) ∧ i < u.length) ∨ TT t n (rmDyn X) u) i u := by
  cases hD : mapLookup X (.atom "dynamic") with
  | none =>
    have dX : DE (level t n).E (.map X) := GC.static gX hD
    obtain ⟨-, long, dR, oR, tR⟩ := del_static_pts dX i (by omega) run
    rw [rmDyn_static hD, upper_tc dX, upper_tc dR]
    have pq : ∀ u, TT t n X u ↔ (denD (.map X) (tpt (t := t) (n := n) u) ∧ i < u.length) ∨ TT t n X u := fun u => by
      rw [denD_tpt]; exact ⟨fun h => Or.inr h, fun h => h.elim (·.1) id⟩
    refine ⟨GC.tc dR, tdelSat oR tR, fun p => ?_, fun u => by rw [denD_tpt, tR], fun u => ?_⟩
    · rw [tdelSat oR tR]
      exact tdelAt_congr pq
    · rw [denD_tpt, tR]
      exact del_congr pq
  | some Dy =>
    rw [upper_dyn hD]
    rcases del_grad gX hD i hm run with h | h | ⟨R', e, gR, YS, YA, -, -, oYS, oYA, tYS, tYA, sR, uR⟩
    · cases h
    · cases h
    cases e
    refine ⟨gR, fun p => (sR p).trans (tdelSat oYS tYS p), fun p => ?_, fun u => ?_, fun u => ?_⟩
    · rw [uR, tdelSat oYA tYA, tdelSat oYS tYS, tdelAt_or]
    · rw [sR, denD_tpt, tYS]
    · rw [uR, denD_tpt, denD_tpt, tYA, tYS, del_or]

end

section
variable {t : Term} {n : Nat}

/-- `tuple_delete_at/2` on a static or gradual type gives an index error, a tuple error, or a map. -/
theorem del_shape {X : List (Term × Term)} (gX : GC (level t n) (.map X)) (i : Nat) {m : Nat}
    (hm : (level t n).K + 26 ≤ m) {r : Term}
    (run : Elixir.Module.Types.Descr.«tuple_delete_at/2» (D m) (.map X) (.integer i) = .ok r) :
    r = .atom "badindex" ∨ r = .atom "badtuple" ∨ ∃ Y, r = .map Y := by
  cases hD : mapLookup X (.atom "dynamic") with
  | none =>
    obtain ⟨res, rres, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, r', rfl, -⟩⟩ := delete_cases (GC.static gX hD) i (m := m) (by omega)
    · rw [run] at rres; cases rres; exact Or.inr (Or.inl rfl)
    · rw [run] at rres; cases rres; exact Or.inl rfl
    · rw [run] at rres; cases rres; exact Or.inr (Or.inr ⟨_, rfl⟩)
  | some Dy =>
    rcases del_grad gX hD i hm run with h | h | ⟨R, e, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨R, e⟩)

/-- A successful `tuple_replace_at/3` deletes the element and inserts the value. -/
theorem rep_split {X : List (Term × Term)} (gX : GC (level t n) (.map X)) (i : Nat) (v : Term) {m : Nat}
    (hm : (level t n).K + 26 ≤ m) {R : List (Term × Term)}
    (run : Elixir.Module.Types.Descr.«tuple_replace_at/3» (D m) (.map X) (.integer i) v = .ok (.map R)) :
    ∃ R₁, Elixir.Module.Types.Descr.«tuple_delete_at/2» (D m) (.map X) (.integer i) = .ok (.map R₁) ∧
      Elixir.Module.Types.Descr.«tuple_insert_at/3» (D m) (.map R₁) (.integer i) v = .ok (.map R) := by
  cases hd : Elixir.Module.Types.Descr.«tuple_delete_at/2» (D m) (.map X) (.integer i) with
  | error e =>
    simp [Elixir.Module.Types.Descr.«tuple_replace_at/3», Lynx.Except.andAlso, Erlang.erlang.«is_integer/1»,
      Erlang.erlang.«>=/2», Int.isGE_compare, hd] at run
  | ok r₁ =>
    rcases del_shape gX i hm hd with rfl | rfl | ⟨R₁, rfl⟩
    · simp [Elixir.Module.Types.Descr.«tuple_replace_at/3», Lynx.Except.andAlso, Erlang.erlang.«is_integer/1»,
        Erlang.erlang.«>=/2», Int.isGE_compare, hd, Lynx.Except.orElse, Erlang.erlang.«is_map/1»,
        Erlang.erlang.«==/2», pure, Except.pure] at run
    · simp [Elixir.Module.Types.Descr.«tuple_replace_at/3», Lynx.Except.andAlso, Erlang.erlang.«is_integer/1»,
        Erlang.erlang.«>=/2», Int.isGE_compare, hd, Lynx.Except.orElse, Erlang.erlang.«is_map/1»,
        Erlang.erlang.«==/2», pure, Except.pure] at run
    refine ⟨R₁, rfl, ?_⟩
    simpa [Elixir.Module.Types.Descr.«tuple_replace_at/3», Lynx.Except.andAlso, Erlang.erlang.«is_integer/1»,
      Erlang.erlang.«>=/2», Int.isGE_compare, hd, Lynx.Except.orElse, Erlang.erlang.«is_map/1»] using run

/-- `tuple_replace_at/3` on a static type, when it gives a map: the tuples with the element at the index removed and
a value inserted there. -/
theorem rep_static {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) (i : Nat) {x : Term}
    (hx : (level t n).E x) (sx : x = .atom "term" ∨ ∃ Z, x = .map Z ∧ mapLookup Z (.atom "dynamic") = none) {m : Nat}
    (hm : (level t n).K + 25 ≤ m) {Y : List (Term × Term)}
    (run : Elixir.Module.Types.Descr.«tuple_replace_at/3» (D m) (.map X) (.integer i) x = .ok (.map Y)) :
    (∀ w, TT t n X w → i < w.length) ∧ DE (level t n).E (.map Y) ∧ (∀ v : PN t n, denD (.map Y) v → v.1.1 = "tuple") ∧
      ∀ w, TT t n Y w ↔ Ins (Del (TT t n X) i) i ((level t n).den x) w := by
  rcases replace_cases hX i sx hm with ⟨e, -⟩ | ⟨e, -⟩ | ⟨onlyX, short, r, tr, sr, e⟩
  · rw [e] at run; cases run
  · rw [e] at run; cases run
  rw [e] at run
  have dZ : DE (level t n).E (.map [(.atom "tuple", r)]) := Or.inr ⟨_, rfl, descrC_put descrC_nil tr⟩
  obtain ⟨-, -, dY, onlyY, ttY⟩ := insert_tuple dZ hx i hm run
  refine ⟨fun w hw => Classical.byContradiction fun h => short ⟨w, hw, by omega⟩, dY, onlyY, fun w => ?_⟩
  rw [ttY]
  exact ins_congr fun u => by rw [tt_single, sr]; rfl

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop}

/-- The values of literals without negations are the values in their tuples. -/
theorem piece_vals {P : List Term} (tP : ∀ p ∈ P, Piece E p) {Q : List V → Prop}
    (sP : ∀ w, (∃ p ∈ P, PieceIn den p w) ↔ Q w) (y : V) :
    (∃ p ∈ P, PieceVal den p y) ↔ ∃ w, Q w ∧ y ∈ w := by
  constructor
  · rintro ⟨p, mp, tag, l, rfl, ne, h⟩
    obtain ⟨tag', l', e, g, -⟩ := tP _ mp
    simp only [Lynx.Term.tuple.injEq, Array.mk.injEq, List.cons.injEq, Lynx.Term.atom.injEq, and_true] at e
    obtain ⟨rfl, -⟩ := e
    by_cases op : tag = "open"
    · subst op
      obtain ⟨w, hw, -⟩ := inT_witness_open y ne 0
      refine ⟨w ++ [y], (sP _).mp ⟨_, mp, pieceIn_iff.mpr ?_⟩, by simp⟩
      simpa using InT.open_append [y] hw
    · have cl : tag = "closed" := g.resolve_left op
      subst cl
      obtain ⟨e, me, he⟩ := h.resolve_left (by simp)
      obtain ⟨w, hw, j, hj⟩ := inT_witness_closed ne me he
      exact ⟨w, (sP _).mp ⟨_, mp, pieceIn_iff.mpr (by simpa using hw)⟩, List.mem_of_getElem? hj⟩
  · rintro ⟨w, hw, my⟩
    obtain ⟨p, mp, hp⟩ := (sP w).mpr hw
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp my
    exact ⟨p, mp, pieceIn_val (tP p mp) hp hj⟩

end

section
variable {t : Term} {n : Nat}

/-- `process_tuples_values/1` on a tuple field: the values in its tuples. -/
theorem proc_vals {b : Term} (fb : TField (level t n).E b) {m : Nat} (hm : (level t n).K + 25 ≤ m) :
    ∃ r, (level t n).E r ∧ Elixir.Module.Types.Descr.«process_tuples_values/1» (D m) b = .ok r ∧
      ∀ y, (level t n).den r y ↔ ∃ w, denTF (level t n).E (level t n).den b w = Bool.true ∧ y ∈ w := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  have ef := (level t n).ef
  obtain ⟨P, rP, tP, sP⟩ : ∃ P : List Term, Elixir.Module.Types.Descr.«tuple_bdd_to_dnf_no_negations/1» (D (k + 4)) b =
      .ok (Term.list P) ∧ (∀ p ∈ P, Piece (level t n).E p) ∧
      ∀ w, (∃ p ∈ P, PieceIn (level t n).den p w) ↔ denTF (level t n).E (level t n).den b w = Bool.true := by
    rcases fb with ⟨k', rfl⟩ | wb
    · have e : k - 6 + 10 = k + 4 := by rw [level_K] at hm; omega
      refine ⟨_, by simpa [e] using dnf_top k' (k - 6), fun p mp => ?_, fun w => ?_⟩
      · simp at mp; subst mp; exact ⟨"open", [], rfl, Or.inl rfl, by simp⟩
      · rw [denTF_top]
        simp only [List.mem_singleton, exists_eq_left, iff_true]
        exact ⟨"open", [], rfl, InT.open_nil w⟩
    · obtain ⟨P, rP, tP, sP⟩ := no_negs (den := (level t n).den) ef (n := k + 1) (by rw [level_K] at hm ⊢; omega) wb
      exact ⟨P, rP, tP, fun w => by rw [sP, denTF_bdd wb]⟩
  obtain ⟨r, hr, rr, sr⟩ := values_pieces ef (n := k + 2) (by rw [level_K] at hm ⊢; omega) P tP
  refine ⟨r, hr, ?_, fun y => (sr y).trans (piece_vals tP sP y)⟩
  simp [Elixir.Module.Types.Descr.«process_tuples_values/1», rP, rr]

end

section
variable {t : Term} {d : Nat}

/-- The union of a type with only a dynamic part and an element type of the level above: the element type, with the
dynamic part in its upper bound. -/
theorem dyn_el_union {c₁ : Term} (hc₁ : DE (level t d).E c₁) {e : Term} (he : (level t (d + 1)).E e) {m : Nat}
    (hm : (level t d).K + 14 ≤ m) :
    ∃ R, Elixir.Module.Types.Descr.«opt_union/2» (D m) (.map [(.atom "dynamic", c₁)]) e = .ok R ∧
      GC (level t d) R ∧ (∀ v : PN t d, denD R v ↔ (level t (d + 1)).den e v) ∧
      ∀ v : PN t d, denD (upper R) v ↔ denD c₁ v ∨ (level t (d + 1)).den e v := by
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
  · obtain ⟨R, gR, run, s₁, s₂⟩ := gc_opt_union gA (GC.tc de) [] (m := k + 2) hm
    refine ⟨R, run, gR, fun v => ?_, fun v => ?_⟩
    · rw [s₁, sem]; exact ⟨fun h => h.resolve_left (noA v), Or.inr⟩
    · rw [s₂, upA, sem, upper_tc de]
  · obtain ⟨r, S, rfl⟩ := node_tuple hn
    have ex := expand_isT hn (k + 1)
    obtain ⟨Y, eY, sY⟩ := expN_map (.tuple #[.reference r, .map S, gen]) (keyOf (level t d).nd)
    rw [eY] at ex sem hc
    have hY : GC (level t d) (.map Y) := GC.tc hc
    obtain ⟨R, gR, run, lo, up, -⟩ := merge_aligned (opt_union_op (n := k + 1) (by omega) [])
      (opt_union_dyn_op (n := k) (by omega) []) (fun x y => opt_union_dyn _ x y _) gA hY
    refine ⟨R, ?_, gR, fun v => ?_, fun v => ?_⟩
    · rw [← run]
      unfold Elixir.Module.Types.Descr.«opt_union/2» Elixir.Module.Types.Descr.«opt_union/3»
      have hA : mapLookup [(Term.atom "dynamic", c₁)] (.atom "dynamic") = some c₁ := by simp [mapLookup]
      have gN : getMapKeys [Term.atom "dynamic"] (.tuple #[.reference r, .map S, gen]) = [] := by simp [getMapKeys]
      have cm : Term.compare (Term.fuel (.tuple #[.reference r, .map S, gen]) (.map [])) (.tuple #[.reference r, .map S, gen])
          (.map []) ≠ .eq := by
        rw [Term.compare_step]; simp [Compare.compareStep]
      simp [getMapKeys_single, Erlang.erlang.«==/2», sY, hA, gN, ex, unfold_map, Erlang.maps.«put/3», alignT, cm]
    · rw [lo, sem]; exact ⟨fun h => h.resolve_left (noA v), Or.inr⟩
    · rw [up, upA, sem, upper_tc hc]

end

section
variable {t : Term} {d : Nat}

/-- `tuple_values/1` on a gradual type, when it gives a type: the values in the tuples of its static part, with those
of its dynamic part in its upper bound. -/
theorem vals_grad {X : List (Term × Term)} (gX : GC (level t (d + 1)) (.map X)) {Dy : Term}
    (hD : mapLookup X (.atom "dynamic") = some Dy) {m : Nat} (hm : (level t (d + 1)).K + 26 ≤ m) {r : Term}
    (run : Elixir.Module.Types.Descr.«tuple_values/1» (D m) (.map X) = .ok r) (nb : r ≠ .atom "badtuple") :
    GC (level t d) r ∧
      (∀ y : PN t d, denD r y ↔ ∃ w, TT t (d + 1) (rmDyn X) w ∧ y ∈ w) ∧
      ∀ y : PN t d, denD (upper r) y ↔ ∃ w, denD Dy (tpt (t := t) (n := d + 1) w) ∧ y ∈ w := by
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
  rw [Elixir.Module.Types.Descr.«tuple_values/1».eq_def] at run
  simp [ne, Erlang.maps.«take/2», hD, Elixir.Module.Types.Descr.«tuple_only?/1», Erlang.maps.«remove/2»] at run
  simp only [filter_tdyn, rto] at run
  by_cases to : ∀ v : PN t (d + 1), ¬denD (.map (rmT (rmDyn X))) v
  rotate_left
  · rw [bp_false.mpr to] at run
    simp [boolAtom, Lynx.Except.andAlso, Elixir.Module.Types.Descr.«-tuple_values/1-fun-0-/1», pure, Except.pure] at run
    exact absurd run.symm nb
  rw [bp_true.mpr to] at run
  -- The tuple field of the dynamic part.
  rcases dDy with rfl | ⟨DX, rfl, sDX⟩
  case' inl =>
    obtain ⟨T, hT, hTt⟩ : ∃ T, Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T) ∧
        mapLookup T (.atom "tuple") = some (.tuple #[.integer 61102469, .atom "open", .nil]) :=
      ⟨_, rfl, by simp [mapLookup]⟩
    simp [boolAtom, Lynx.Except.andAlso, Elixir.Module.Types.Descr.«descr_key?/2», hT, getMapKeys_single, hTt] at run
    have fb : TField (level t (d + 1)).E (.tuple #[.integer 61102469, .atom "open", .nil]) := Or.inl ⟨_, rfl⟩
    have sb : ∀ w, denD (.atom "term") (tpt (t := t) (n := d + 1) w) ↔
        denTF (level t (d + 1)).E (level t (d + 1)).den (.tuple #[.integer 61102469, .atom "open", .nil]) w = Bool.true :=
      fun w => by simp [denD_term, denTF_top]
    generalize (Term.tuple #[.integer 61102469, .atom "open", .nil]) = b at run fb sb
  case' inr =>
    obtain ⟨b, hk⟩ : ∃ b, mapLookup DX (.atom "tuple") = some b := by
      cases hk : mapLookup DX (.atom "tuple") with
      | none =>
        simp [boolAtom, Lynx.Except.andAlso, Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2»,
          any_key, hk, Elixir.Module.Types.Descr.«-tuple_values/1-fun-0-/1», pure, Except.pure] at run
        exact absurd run.symm nb
      | some b => exact ⟨b, rfl⟩
    have fb : TField (level t (d + 1)).E b := fieldC_tuple (sDX.fields "tuple" b hk)
    have sb : ∀ w, denD (.map DX) (tpt (t := t) (n := d + 1) w) ↔
        denTF (level t (d + 1)).E (level t (d + 1)).den b w = Bool.true := fun w => by rw [denD_tpt]; simp [TT, hk]
    simp [boolAtom, Lynx.Except.andAlso, Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key,
      hk, getMapKeys_single] at run
  all_goals
    obtain ⟨bE, rbE, sbE⟩ := tuple_empty_exact ef fb []
    rw [rbE (k + 3) (by omega)] at run
    cases bE
    case true =>
      simp [boolAtom, Elixir.Module.Types.Descr.«-tuple_values/1-fun-0-/1», pure, Except.pure] at run
      exact absurd run.symm nb
    have get₂' : Elixir.Map.«get/3» (.map (List.filter (fun entry => compareExact ((Term.atom "dynamic").fuel entry.fst)
        (.atom "dynamic") entry.fst != Ordering.eq) X)) (.atom "tuple") (.atom "bdd_bot") = .ok b₂ := get₂
    obtain ⟨r₁, er₁, rr₁, sr₁⟩ := proc_vals fb (m := k + 3) (by omega)
    obtain ⟨c₁, hc₁, sc₁, cases₁⟩ := el_canon er₁
    obtain ⟨R, rR, gR, s₁, s₂⟩ := dyn_el_union hc₁ er₂ (m := k + 3) (by omega)
    have ok : R = r := by
      rcases cases₁ with ⟨de, rfl⟩ | ⟨hn, rfl⟩
      · rcases de with rfl | ⟨Z, rfl, sZ⟩
        · simpa [boolAtom, rr₁, getMapKeys, get₂', rr₂, rR] using run
        · simpa [boolAtom, rr₁, getMapKeys_single, sZ.static, get₂', rr₂, rR] using run
      · obtain ⟨q, SS, rfl⟩ := node_tuple hn
        have ex := expand_isT hn (k + 2)
        obtain ⟨Y, eY, sY⟩ := expN_map (.tuple #[.reference q, .map SS, gen]) (keyOf (level t d).nd)
        rw [eY] at ex rR
        have dY : Elixir.Module.Types.Descr.«dynamic/1» (D (k + 3)) (.map Y) =
            .ok (.map [(.atom "dynamic", .map Y)]) := by
          unfold Elixir.Module.Types.Descr.«dynamic/1»; simp [getMapKeys_single, sY]
        have gt : getMapKeys [Term.atom "dynamic"] (.tuple #[.reference q, .map SS, gen]) = [] := by simp [getMapKeys]
        simpa [boolAtom, rr₁, gt, ex, unfold_map, dY, get₂', rr₂, rR] using run
    subst ok
    refine ⟨gR, fun y => ?_, fun y => ?_⟩
    · exact (s₁ y).trans ((sr₂ y).trans (exists_congr fun w => and_congr (sb₂ w).symm Iff.rfl))
    · refine (s₂ y).trans ((or_congr ((sc₁ y).symm.trans (sr₁ y)) (sr₂ y)).trans ?_)
      constructor
      · rintro (⟨w, hw, my⟩ | ⟨w, hw, my⟩)
        · exact ⟨w, (sb w).mpr hw, my⟩
        · exact ⟨w, inc _ ((denD_rmDyn X _).mp ((denD_tpt w).mpr ((sb₂ w).mpr hw))), my⟩
      · rintro ⟨w, hw, my⟩
        exact Or.inl ⟨w, (sb w).mp hw, my⟩

end

section
variable {t : Term} {d : Nat}

/-- `tuple_values/1` on a static type of tuples, when it gives a type: the values in its tuples. -/
theorem vals_static {X : List (Term × Term)} (hX : DE (level t (d + 1)).E (.map X)) {m : Nat}
    (hm : (level t (d + 1)).K + 25 ≤ m) {r : Term}
    (run : Elixir.Module.Types.Descr.«tuple_values/1» (D m) (.map X) = .ok r) (nb : r ≠ .atom "badtuple") :
    (level t (d + 1)).E r ∧ ∀ y : PN t d, (level t (d + 1)).den r y ↔ ∃ w, TT t (d + 1) X w ∧ y ∈ w := by
  obtain ⟨res, run', ⟨rfl, -⟩ | ⟨-, hres, P, tP, sP, sr⟩⟩ := values_cases hX hm
  · rw [run] at run'; cases run'; exact absurd rfl nb
  rw [run] at run'; cases run'
  exact ⟨hres, fun y => (sr y).trans (piece_vals tP sP y)⟩

/-- The bounds of a gradual type of the level `d`, as element types of the level above. -/
theorem gc_el {a : Term} (ha : GC (level t d) a) :
    (level t (d + 1)).E (upper a) ∧ (level t (d + 1)).E (lower a) ∧
      (∀ v : PN t d, (level t (d + 1)).den (upper a) v ↔ denD (upper a) v) ∧
      ∀ v : PN t d, (level t (d + 1)).den (lower a) v ↔ denD a v :=
  ⟨e_succ ha.up_tc, e_succ ha.low_tc, fun v => den_succ ha.up_tc v,
    fun v => (den_succ ha.low_tc v).trans (denD_lower a v)⟩

end

end Elixir.STTDescrProofsTest.Nest
