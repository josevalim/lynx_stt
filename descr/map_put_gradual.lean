namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Forced updates do not read whether the type is static, so the dynamic part of a gradual type is put like a
static one. -/

theorem foldl1_congr (d : Dispatcher) (f g : Term) (h : ∀ x a, d.pure f #[x, a] = d.pure g #[x, a]) :
    ∀ (l acc : Term), Erlang.lists.«foldl_1/3» d f acc l = Erlang.lists.«foldl_1/3» d g acc l
  | .cons x l, acc => by
    rw [Erlang.lists.«foldl_1/3».eq_def, Erlang.lists.«foldl_1/3».eq_def]
    simp only [h]
    cases d.pure g #[x, acc] with
    | error e => rfl
    | ok a => simpa using foldl1_congr d f g h l a
  | .nil, acc => by rw [Erlang.lists.«foldl_1/3».eq_def, Erlang.lists.«foldl_1/3».eq_def]
  | .atom _, _ | .integer _, _ | .float _, _ | .tuple _, _ | .map _, _ | .bitstring _ _ _, _
  | .function _ _ _ _ _, _ | .pid _, _ | .reference _, _ => by
    rw [Erlang.lists.«foldl_1/3».eq_def, Erlang.lists.«foldl_1/3».eq_def]

theorem foldl_congr (d : Dispatcher) {mo nm : String} {c₁ c₂ : Array Term}
    (h : ∀ x a, d.pure (.function false mo nm 2 c₁) #[x, a] = d.pure (.function false mo nm 2 c₂) #[x, a]) (l acc : Term) :
    Erlang.lists.«foldl/3» d (.function false mo nm 2 c₁) acc l = Erlang.lists.«foldl/3» d (.function false mo nm 2 c₂) acc l := by
  simp only [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]
  cases l with
  | cons x l =>
    simp only [h]
    cases d.pure (.function false mo nm 2 c₂) #[x, acc] with
    | error e => simp
    | ok a => simpa [Lynx.Except.guard] using foldl1_congr d _ _ h l a
  | _ => simp

/-- The step of `map_update_named_keys/8` does not read whether the type is static when forcing. -/
theorem named_step_static (d : Dispatcher) (dnf op req build ov key acc : Term) :
    Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req (.atom "false") build ov (.atom "true")
        key acc =
      Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9» d dnf op req (.atom "true") build ov (.atom "true")
        key acc := by
  simp [Elixir.Module.Types.Descr.«-map_update_named_keys/8-fun-0-/9»]

/-- `map_update_named_keys/8` forcing gives the same result whether the type is static or not. -/
theorem named_keys_static (m : Nat) (acc dnf keys v req rt build : Term) :
    Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) acc dnf keys (forceOp v) req (.atom "false") rt build =
      Elixir.Module.Types.Descr.«map_update_named_keys/8» (D (m + 1)) acc dnf keys (forceOp v) req (.atom "true") rt
        build := by
  simp only [Elixir.Module.Types.Descr.«map_update_named_keys/8», forceOp, Erlang.erlang.«element/2»,
    Erlang.erlang.«==/2»]
  simp
  congr 1
  funext ov
  refine foldl_congr _ (fun x a => ?_) keys acc
  rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure,
    Erlang.program.«Elixir.Module.Types.Descr:-map_update_named_keys/8-fun-0-/2».pure, named_step_static]

/-- `map_update_static_dnf/6` forcing gives the same result whether the type is static or not. -/
theorem dnf_static (m : Nat) (bdd dnf split v rt : Term) :
    Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 1)) bdd dnf split (forceOp v) rt (.atom "false") =
      Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (m + 1)) bdd dnf split (forceOp v) rt (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«map_update_static_dnf/6»
  simp only [named_keys_static]

theorem update_static_flag_ne (m : Nat) (descr split v rt : Term) (h : descr ≠ .atom "term") :
    Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split (forceOp v) rt (.atom "false") =
      Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split (forceOp v) rt (.atom "true") := by
  rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def, Elixir.Module.Types.Descr.«map_update_static/5».eq_def]
  cases descr with
  | map X =>
    simp only
    cases getMapKeys [.atom "map"] (.map X) with
    | nil => rfl
    | cons b rest =>
      cases rest with
      | cons c rest => rfl
      | nil =>
        simp only
        split <;> rename_i heq <;> simp only [dnf_static] <;> (try rfl) <;> simp_all
  | atom a =>
    by_cases ha : a = "term"
    · subst ha; exact absurd rfl h
    · simp [Lynx.Term.getMapKeys]
  | _ => rfl

/-- `map_update_static/5` forcing gives the same result whether the type is static or not. -/
theorem update_static_flag (m : Nat) (descr split v rt : Term) :
    Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split (forceOp v) rt (.atom "false") =
      Elixir.Module.Types.Descr.«map_update_static/5» (D (m + 1)) descr split (forceOp v) rt (.atom "true") := by
  by_cases h : descr = .atom "term"
  · subst h
    rw [Elixir.Module.Types.Descr.«map_update_static/5».eq_def, Elixir.Module.Types.Descr.«map_update_static/5».eq_def]
    simp only
    exact update_static_flag_ne m _ split v rt (by simp)
  · exact update_static_flag_ne m descr split v rt h

section
variable {t : Term} {n : Nat}

/-- `map_update_static/5` forcing a static value at a split of static keys, on a static map type of the next level,
for either flag: types without maps give no map; others the maps of the puts, and whether some put holds. -/
theorem upd_static_g {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) {s neg : Term}
    {P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop}
    (hP : DnfPuts s neg P)
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {m : Nat}
    (hm : (level t n).K + 27 ≤ m) (st : Bool) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X) (s) (forceOp v)
        (.atom "false") (boolAtom st) = .ok res ∧
      (((res = .atom "badmap" ∨ res = .tuple #[.map [], .map [], .nil, .atom "false"]) ∧ ∀ w, ¬MT t n X w) ∨
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
    refine ⟨_, ?_, Or.inl ⟨Or.inr rfl, fun w ⟨b, h, _⟩ => by rw [hb] at h; cases h⟩⟩
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
      · simp only [MT, mapLookup, List.find?_nil, Option.map_none, reduceCtorEq, false_and, exists_false, false_iff]
        exact emp w
    · refine ⟨_, f, rfl, Or.inr ⟨_, rfl, descrC_map fr⟩, fun q hq => ?_, fun w => ?_, hf⟩
      · rw [denD_map] at hq
        by_cases e : q.1.1 = "map"
        · exact e
        · simp [mapLookup, e, dn_none] at hq
      · rw [← sr]; simp [MT, mapLookup]

theorem upd_static {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) {rs : List Term} {neg : Term} {ds : List Term}
    (ok : SplitOk rs neg ds) (nr : ∀ N, neg = .map N → rs = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {m : Nat}
    (hm : (level t n).K + 27 ≤ m) (st : Bool) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D m) (.map X) (splitT rs neg ds) (forceOp v)
        (.atom "false") (boolAtom st) = .ok res ∧
      (((res = .atom "badmap" ∨ res = .tuple #[.map [], .map [], .nil, .atom "false"]) ∧ ∀ w, ¬MT t n X w) ∨
        (∃ w, MT t n X w) ∧ ∃ Y f, res = .tuple #[.map [], .map Y, .nil, f] ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          (∀ w, MT t n Y w ↔ PutSem (level t n).den (MT t n X) rs neg ds v w) ∧
          (f = .atom "true" ∨ ∀ w, ¬PutSem (level t n).den (MT t n X) rs neg ds v w)) :=
  upd_static_g (P := fun den M v w => PutSem den M rs neg ds v w) hX hv sv (dnfPuts_split ok nr) hNa hm st


end

section
variable {t : Term} {n : Nat}

/-- The top map type. -/
abbrev topM : List (Term × Term) := [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])]

/-- The fields of the maps a static type holds as a map type: those of a map, or every map for the top type. -/
def dynL (a : Term) : List (Term × Term) :=
  match a with
  | .map Y => Y
  | _ => topM

/-- The maps of the puts at a static map type, if it holds maps. -/
def PutOf (t : Term) (n : Nat) (Y : List (Term × Term)) (rs : List Term) (neg : Term) (ds : List Term) (v : Term)
    (w : MW (level t n).V) : Prop :=
  (∃ u, MT t n Y u) ∧ PutSem (level t n).den (MT t n Y) rs neg ds v w

/-- The maps of the updates `P` gives at a static map type, if it holds maps. -/
def PutOfP (P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop) (t : Term) (n : Nat)
    (Y : List (Term × Term)) (v : Term) (w : MW (level t n).V) : Prop :=
  (∃ u, MT t n Y u) ∧ P (level t n).den (MT t n Y) v w

theorem mt_top (w : MW (level t n).V) : MT t n topM w := by
  have := (mapTop_den (t := t) (n := n) (mpt w)).mpr rfl
  exact (denD_mpt w).mp this

/-- `map_update_unchecked/4` forcing a static value at a split of static keys, on a gradual map type of the next
level: the puts at the static maps, and in the upper bound also at the dynamic maps. -/
theorem gupd_g {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {Dy : Term}
    (hD : mapLookup X (.atom "dynamic") = some Dy) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) {s neg : Term}
    {P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop}
    (hP : DnfPuts s neg P)
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {m : Nat}
    (hm : (level t n).K + 30 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X) (s) (forceOp v)
        (.atom "false") = .ok res ∧
      (res = .atom "badmap" ∨
        (∃ er, res = .tuple #[.atom "error", er] ∧ ∀ w, ¬PutOfP P t n (dynL Dy) v w) ∨
        ∃ T R er, res = .tuple #[T, R, er] ∧ GC (level t n) R ∧
          (∀ q : PN t n, denD (upper R) q → q.1.1 = "map") ∧
          (∀ q : PN t n, denD (.map (rmDyn X)) q → q.1.1 = "map") ∧
          (∀ w, denD R (mpt (t := t) (n := n) w) ↔ PutOfP P t n (rmDyn X) v w) ∧
          ∀ w, denD (upper R) (mpt (t := t) (n := n) w) ↔
            PutOfP P t n (rmDyn X) v w ∨ PutOfP P t n (dynL Dy) v w) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 8 := ⟨m - 8, by omega⟩
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
  have dSt : DE (level t n).E (.map (rmDyn X)) := Or.inr ⟨_, rfl, dS⟩
  obtain ⟨dR, sRm⟩ := rest_map dSt
  have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 8)) (.map (rmDyn X)) =
      .ok (boolAtom (bp (∀ q : PN t n, ¬denD (.map (rmM (rmDyn X))) q))) := by
    simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind]
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
    refine ⟨_, ?_, Or.inl rfl⟩
    cases hk : (mapLookup (dynL Dy) (.atom "map")).isSome <;>
      simp [keyD, hk, mo, Lynx.Except.andAlso, boolAtom, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1»]
  rw [bp_true.mpr (Classical.not_not.mp hmo)] at mo
  rcases Classical.em ((mapLookup (dynL Dy) (.atom "map")).isSome = Bool.false) with hbm | hbm
  · refine ⟨_, ?_, Or.inl rfl⟩
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
      simp only [denD_map, mapLookup, List.find?_nil, Option.map_none]
      constructor
      · intro h; simp [mpt, dn_none] at h
      · rintro ⟨⟨u, hu⟩, -⟩; exact absurd hu (noS u)
    · refine ⟨Ys, fs, Or.inr rfl, dYs, onlyYs, fun w => ?_⟩
      rw [denD_mpt, semYs]
      exact ⟨fun h => ⟨exS, h⟩, fun h => h.2⟩
  obtain ⟨rd, rrd, hd⟩ := upd_static_g dDy hv sv hP hNa (m := k + 8) (by omega) Bool.false
  simp only [boolAtom, Bool.false_eq_true, ↓reduceIte] at rrd
  simp only [kt, mo, boolAtom, ↓reduceIte, Lynx.Except.andAlso, rrd, rrS, Lynx.Except.ok_bind]
  rcases hd with ⟨hrd | hrd, noD⟩ | ⟨exD, Yd, fd, rfl, dYd, onlyYd, semYd, hfd⟩
  · subst hrd
    exact ⟨_, by simp [bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-1-/1»], Or.inl rfl⟩
  · subst hrd
    refine ⟨.tuple #[.atom "error", .nil], ?_, Or.inr (Or.inl ⟨_, rfl, fun w ⟨⟨u, hu⟩, _⟩ => noD u hu⟩)⟩
    rcases eS with ⟨rfl, rfl, rfl⟩ | rfl <;>
      simp [Lynx.Term.isMember, Erlang.erlang.«++/2», pure, Except.pure]
  · by_cases fe : fd = .atom "false" ∨ fd = .atom "nil"
    · have emp : ∀ w, ¬PutOfP P t n (dynL Dy) v w := by
        rcases hfd with rfl | h
        · rcases fe with h | h <;> simp at h
        · exact fun w ⟨_, hw⟩ => h w hw
      refine ⟨.tuple #[.atom "error", .nil], ?_, Or.inr (Or.inl ⟨_, rfl, emp⟩)⟩
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
          Classical.not_not.mp hmo q ((sRm q).mpr ⟨hq, nq⟩), fun w => (sc₁ _).trans (sSd w), fun w => ?_⟩)⟩
      · rcases eS with ⟨rfl, rfl, rfl⟩ | rfl <;>
          simp [fm, getMapKeys_single, mapLookup, fY, rv, rc', Erlang.erlang.«++/2», pure,
            Except.pure]
      · rw [sc₂, sSd, denD_mpt, semYd]
        exact ⟨fun h => h.imp id fun h => ⟨exD, h⟩, fun h => h.imp id fun h => h.2⟩

theorem gupd {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {Dy : Term}
    (hD : mapLookup X (.atom "dynamic") = some Dy) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) {rs : List Term} {neg : Term} {ds : List Term}
    (ok : SplitOk rs neg ds) (nr : ∀ N, neg = .map N → rs = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {m : Nat}
    (hm : (level t n).K + 30 ≤ m) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X) (splitT rs neg ds) (forceOp v)
        (.atom "false") = .ok res ∧
      (res = .atom "badmap" ∨
        (∃ er, res = .tuple #[.atom "error", er] ∧ ∀ w, ¬PutOf t n (dynL Dy) rs neg ds v w) ∨
        ∃ T R er, res = .tuple #[T, R, er] ∧ GC (level t n) R ∧
          (∀ q : PN t n, denD (upper R) q → q.1.1 = "map") ∧
          (∀ q : PN t n, denD (.map (rmDyn X)) q → q.1.1 = "map") ∧
          (∀ w, denD R (mpt (t := t) (n := n) w) ↔ PutOf t n (rmDyn X) rs neg ds v w) ∧
          ∀ w, denD (upper R) (mpt (t := t) (n := n) w) ↔
            PutOf t n (rmDyn X) rs neg ds v w ∨ PutOf t n (dynL Dy) rs neg ds v w) :=
  gupd_g (P := fun den M v w => PutSem den M rs neg ds v w) gX hD hv sv (dnfPuts_split ok nr) hNa hm


/-- The type `dynamic/1` gives a map type: its dynamic part, or the whole type. -/
def dynG (X : List (Term × Term)) : List (Term × Term) :=
  [(.atom "dynamic", (mapLookup X (.atom "dynamic")).getD (.map X))]

/-- The result `map_put/3` gives from the update of `map_put_shared/3`. -/
def putRes (r : Term) : Except Lynx.Exception Term :=
  match r with
  | .tuple ⟨[_, d, _]⟩ => pure (.tuple #[.atom "ok", d])
  | .tuple ⟨[.atom "error", _]⟩ => pure (.tuple #[.atom "ok", .map []])
  | .atom "badmap" => pure (.atom "badmap")
  | x => .error (.error (.tuple #[.atom "case_clause", x]))

theorem put_static_value {m : Nat} {X : List (Term × Term)} {key v : Term} {rs : List Term} {neg : Term}
    {ds : List Term} (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok (splitT rs neg ds))
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) :
    Elixir.Module.Types.Descr.«map_put/3» (D m) (.map X) key v = (do
      let r ← Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X) (splitT rs neg ds) (forceOp v)
        (.atom "false")
      putRes r) := by
  unfold Elixir.Module.Types.Descr.«map_put/3» Elixir.Module.Types.Descr.«map_put_shared/3»
  rcases sv with rfl | ⟨Z, rfl, sZ⟩
  · simp [hk, putRes]
    rfl
  · simp [hk, getMapKeys_single, sZ, putRes]
    rfl

theorem put_gradual_value {m : Nat} {X : List (Term × Term)} {key : Term} {Zv : List (Term × Term)} {Dv : Term}
    {rs : List Term} {neg : Term} {ds : List Term}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key = .ok (splitT rs neg ds))
    (hZ : mapLookup Zv (.atom "dynamic") = some Dv) :
    Elixir.Module.Types.Descr.«map_put/3» (D m) (.map X) key (.map Zv) = (do
      let r ← Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map (dynG X)) (splitT rs neg ds) (forceOp Dv)
        (.atom "false")
      putRes r) := by
  unfold Elixir.Module.Types.Descr.«map_put/3» Elixir.Module.Types.Descr.«map_put_shared/3»
  cases hX : mapLookup X (.atom "dynamic") <;>
    simp [hk, getMapKeys_single, hZ, hX, dynG, putRes] <;> rfl

/-- The maps of a gradual map type's static part are maps of its dynamic part. -/
theorem static_in_dyn {X : List (Term × Term)} {Dy : Term} (tD : TC (level t n) Dy)
    (incl : ∀ q : TP (level t n), denD (.map X) q → denD Dy q) (u : MW (level t n).V) (hu : MT t n (rmDyn X) u) :
    MT t n (dynL Dy) u := by
  have h := incl (mpt u) ((denD_rmDyn X (mpt u)).mp ((denD_mpt u).mpr hu))
  rcases tD with rfl | ⟨Y, rfl, -⟩
  · exact mt_top u
  · exact (denD_mpt u).mp h

theorem putOf_mono {Y Y' : List (Term × Term)} (sub : ∀ u, MT t n Y u → MT t n Y' u) {rs : List Term} {neg : Term}
    {ds : List Term} (ok : SplitOk rs neg ds) (nr : ∀ N, neg = .map N → rs = []) {v : Term} {w : MW (level t n).V}
    (h : PutOf t n Y rs neg ds v w) : PutOf t n Y' rs neg ds v w :=
  ⟨let ⟨u, hu⟩ := h.1; ⟨u, sub u hu⟩, put_mono sub (fun _ h => h) ok ok nr (fun _ h => h) h.2⟩

/-- `map_put/3` of a static value at static keys of a gradual map type: `:badmap`, or a gradual type holding the puts
at the static maps, whose upper bound holds the puts at the dynamic maps. -/
theorem gres_g {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {Dy : Term}
    (hD : mapLookup X (.atom "dynamic") = some Dy) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) {s neg : Term}
    {P : ∀ {V : Type}, (Term → V → Prop) → (MW V → Prop) → Term → MW V → Prop}
    (hP : DnfPuts s neg P)
    (hmono : ∀ M₁ M₂ : MW (level t n).V → Prop, (∀ u, M₁ u → M₂ u) → ∀ w, P (level t n).den M₁ v w → P (level t n).den M₂ v w)
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {m : Nat}
    (hm : (level t n).K + 30 ≤ m) :
    ∃ res, (do
        let r ← Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X) (s) (forceOp v)
          (.atom "false")
        putRes r) = .ok res ∧
      (res = .atom "badmap" ∨ ∃ R, res = .tuple #[.atom "ok", R] ∧ GC (level t n) R ∧
        (∀ q : PN t n, denD (upper R) q → q.1.1 = "map") ∧
        ((∀ q : PN t n, denD (.map (rmDyn X)) q → q.1.1 = "map") ∨ ∀ w, ¬PutOfP P t n (rmDyn X) v w) ∧
        (∀ w, denD R (mpt (t := t) (n := n) w) ↔ PutOfP P t n (rmDyn X) v w) ∧
        ∀ w, denD (upper R) (mpt (t := t) (n := n) w) ↔ PutOfP P t n (dynL Dy) v w) := by
  obtain ⟨tD, incl⟩ : TC (level t n) Dy ∧ ∀ q : TP (level t n), denD (.map X) q → denD Dy q := by
    rcases gX with tX | ⟨X', Dy', e, hD', tD, -, incl⟩
    · rcases tX with h | ⟨X', e, sX'⟩
      · cases h
      · simp only [Term.map.injEq] at e; subst e; rw [sX'.static] at hD; cases hD
    · simp only [Term.map.injEq] at e; subst e
      rw [hD] at hD'; cases hD'
      exact ⟨tD, incl⟩
  have up : ∀ w, PutOfP P t n (rmDyn X) v w → PutOfP P t n (dynL Dy) v w :=
    fun w h => ⟨let ⟨u, hu⟩ := h.1; ⟨u, static_in_dyn tD incl u hu⟩, hmono _ _ (static_in_dyn tD incl) w h.2⟩
  obtain ⟨res, run, rfl | ⟨er, rfl, emp⟩ | ⟨T, R, er, rfl, gR, oR, oS, s₁, s₂⟩⟩ := gupd_g gX hD hv sv hP hNa hm
  · exact ⟨_, by simp [run, putRes], Or.inl rfl⟩
  · refine ⟨_, by simp [run, putRes, pure, Except.pure], Or.inr ⟨_, rfl, GC.tc (Or.inr ⟨[], rfl, descrC_nil⟩),
      fun q h => by simp [upper, mapLookup, denD_map, dn_none] at h, Or.inr fun w h => emp w (up w h), fun w => ?_,
      fun w => ?_⟩⟩
    · simp only [denD_map, mapLookup, List.find?_nil, Option.map_none]
      exact ⟨fun h => by simp [mpt, dn_none] at h, fun h => absurd (up w h) (emp w)⟩
    · simp only [upper, mapLookup, List.find?_nil, Option.map_none, Option.getD_none, denD_map]
      exact ⟨fun h => by simp [mpt, dn_none] at h, fun h => absurd h (emp w)⟩
  · refine ⟨_, by simp [run, putRes, pure, Except.pure], Or.inr ⟨R, rfl, gR, oR, Or.inl oS, s₁, fun w => ?_⟩⟩
    rw [s₂]
    exact ⟨fun h => h.elim (up w) id, Or.inr⟩

theorem gres {X : List (Term × Term)} (gX : GC (level t n) (.map X)) {Dy : Term}
    (hD : mapLookup X (.atom "dynamic") = some Dy) {v : Term} (hv : (level t n).E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) {rs : List Term} {neg : Term} {ds : List Term}
    (ok : SplitOk rs neg ds) (nr : ∀ N, neg = .map N → rs = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) {m : Nat}
    (hm : (level t n).K + 30 ≤ m) :
    ∃ res, (do
        let r ← Elixir.Module.Types.Descr.«map_update_unchecked/4» (D m) (.map X) (splitT rs neg ds) (forceOp v)
          (.atom "false")
        putRes r) = .ok res ∧
      (res = .atom "badmap" ∨ ∃ R, res = .tuple #[.atom "ok", R] ∧ GC (level t n) R ∧
        (∀ q : PN t n, denD (upper R) q → q.1.1 = "map") ∧
        ((∀ q : PN t n, denD (.map (rmDyn X)) q → q.1.1 = "map") ∨ ∀ w, ¬PutOf t n (rmDyn X) rs neg ds v w) ∧
        (∀ w, denD R (mpt (t := t) (n := n) w) ↔ PutOf t n (rmDyn X) rs neg ds v w) ∧
        ∀ w, denD (upper R) (mpt (t := t) (n := n) w) ↔ PutOf t n (dynL Dy) rs neg ds v w) :=
  gres_g (P := fun den M v w => PutSem den M rs neg ds v w) gX hD hv sv (dnfPuts_split ok nr)
    (fun _ _ sub _ h => put_mono sub (fun _ h => h) ok ok nr (fun _ h => h) h) hNa hm


end

end Elixir.STTDescrProofsTest.Nest
