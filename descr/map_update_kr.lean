namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `map_update_static_dnf/6` for `:keep` and `:reject` of a value at a split of keys. -/
theorem upd_dnf_kr (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) (vne : ∃ x, den v x) (keep : Bool) (bdd : Term) (fbd : MField E bdd)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (hne : lines ≠ [])
    (sbd : ∀ w, denMF E den bdd w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hneg : ∀ N, neg = .map N → (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ ∃ ks : List String,
      Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) bdd =
        .ok (Term.list (ks.map Term.atom)) ∧ (∀ s ∈ ks, mapLookup N (.atom s) = none) ∧
      ∀ L ∈ lines, ∀ s, LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks) :
    ∃ T Y er f, Elixir.Module.Types.Descr.«map_update_static_dnf/6» (D (n + 6)) bdd (Term.list lines)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") =
        .ok (.tuple #[T, Y, er, f]) ∧
      ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (keep = Bool.true ∨
          KindHeld (fun u => ∃ L ∈ lines, InMLine den L u) d)) ∧
        MapsY E den Y (UpdSemKR den (fun u => ∃ L ∈ lines, InMLine den L u) rk neg Dm v keep) := by
  have hDs : ∀ s ∈ Ds, s ∈ domainKinds := fun s ms => by
    obtain ⟨s', ms', e⟩ := ok.hds _ (List.mem_map_of_mem ms); cases e; exact ms'
  rcases ok.hneg with rfl | ⟨N, rfl⟩
  · have hna : "atom" ∉ Ds := fun m => by
      obtain ⟨N, e⟩ := ok.hatom.mp (List.mem_map_of_mem m); cases e
    exact upd_dnf_nil ef hn hv sv vne keep bdd lines hl hne rk Ds hDs hna
  · obtain rfl := nr N rfl
    obtain ⟨hNa, ks, hR, hks, lnKS⟩ := hneg N rfl
    have hat : "atom" ∈ Ds := by
      have := ok.hatom.mpr ⟨N, rfl⟩
      obtain ⟨s, ms, e⟩ := List.mem_map.mp this; cases e; exact ms
    exact upd_dnf_neg ef hn hv sv vne keep bdd fbd lines hl hne sbd N hNa ks hR hks lnKS Ds hDs hat

/-- `map_update_static/5` for `:keep` and `:reject` of a static value at a split of keys, asking for the old values. -/
theorem kr_update_static (ef : EF nd E V den tl K) {n : Nat} (hn : K + 4 ≤ n) {v : Term} (hv : E v)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z) (vne : ∃ x, den v x) (keep : Bool) {rk Ds : List String} {neg : Term}
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "map") = some b) (fb : MField E b) :
    ∃ res, Elixir.Module.Types.Descr.«map_update_static/5» (D (n + 6)) (.map X)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (keepOp v keep) (.atom "true") (.atom "true") = .ok res ∧
      ((res = .atom "badmap" ∧ ∀ w, denMF E den b w = Bool.false) ∨
        ∃ T Y er f, res = .tuple #[T, Y, er, f] ∧ (∃ w, denMF E den b w = Bool.true) ∧
          ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (keep = Bool.true ∨
              KindHeld (fun u => denMF E den b u = Bool.true) d)) ∧
            MapsY E den Y (UpdSemKR den (fun u => denMF E den b u = Bool.true) rk neg Dm v keep)) := by
  -- For negated sets, the keys outside the set, and the literals of the field naming only those or the set's.
  have negInfo : ∀ N, neg = .map N → ∃ ks : List String,
      Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) b =
        .ok (Term.list (ks.map Term.atom)) ∧ (∀ s ∈ ks, mapLookup N (.atom s) = none) ∧
      ∀ wb : Bdd (MLit E) b, Bdd (fun t => MLit E t ∧ LitIn (fun s => mapLookup N (.atom s) ≠ none ∨ s ∈ ks) t) b := by
    intro N _
    obtain ⟨R, rR, hR, -⟩ := neg_keys (den := den) ef N (n + 5) fb
    obtain ⟨ks, rfl⟩ : ∃ ks : List String, R = ks.map Term.atom := by
      clear rR
      induction R with
      | nil => exact ⟨[], rfl⟩
      | cons r rs ih =>
        obtain ⟨s, rfl, -⟩ := hR r List.mem_cons_self
        obtain ⟨B, rfl⟩ := ih fun x mx => hR x (List.mem_cons_of_mem _ mx)
        exact ⟨s :: B, rfl⟩
    refine ⟨ks, rR, fun s ms => ?_, fun wb => ?_⟩
    · obtain ⟨s', e, h⟩ := hR _ (List.mem_map_of_mem ms); cases e; exact h
    · obtain ⟨R', rR', -, lits, -⟩ := neg_keys_lits (den := den) ef N (n + 5) wb
      have e : R' = ks.map Term.atom := list_inj (Except.ok.inj (rR'.symm.trans rR))
      subst e
      exact lits.mono fun t ⟨lt, it⟩ => ⟨lt, fun k tag l et s ms => (it k tag l et s ms).imp id (by simp)⟩
  -- The semantics over the field.
  have conv : ∀ {lines : List Term}, (∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w) →
      (fun u => ∃ L ∈ lines, InMLine den L u) = (fun u => denMF E den b u = Bool.true) := fun h =>
    funext fun u => propext (h u).symm
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, sl⟩ := mfield_three fb e₀
    have sem : ∀ w, denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w = Bool.true ↔ MSem den tag l w :=
      fun w => denMF_leaf ef sl g w
    obtain ⟨e, run⟩ := init_total ef.mopsE ef.mdopsE ef.jopsU [] g.plain (fun e me => (sl.1 e me).2) (negs := []) (by simp)
    have run : Elixir.Module.Types.Descr.«init_map_line_empty?/4» (D (n + 6)) tag (fieldsTerm l) .nil (.map []) =
        .ok (boolAtom e) := run (n + 6) (by omega)
    cases e
    · have ne : ∃ w, MSem den tag l w := Classical.byContradiction fun none => by
        have := run.symm.trans (init_val ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ (m := n + 6) (by omega) rfl g sl
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
      have hneg : ∀ N, neg = .map N → (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ ∃ ks : List String,
          Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N)
            (.tuple #[.integer k, tag, fieldsTerm l]) = .ok (Term.list (ks.map Term.atom)) ∧
          (∀ s ∈ ks, mapLookup N (.atom s) = none) ∧ ∀ L ∈ [Term.tuple #[tag, fieldsTerm l, Term.list []]], ∀ s,
            LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks := by
        intro N eN
        obtain ⟨ks, hR, hks, litsQ⟩ := negInfo N eN
        have names : ∀ s ∈ keyStrs l, mapLookup N (.atom s) ≠ none ∨ s ∈ ks := by
          rcases fb with ⟨k', e'⟩ | wb
          · intro s ms
            obtain ⟨-, -, e₃⟩ := tuple3_inj e'
            have : l = [] := fieldsTerm_inj (l' := []) e₃
            subst this; simp [keyStrs] at ms
          · exact (Bdd.leaf_iff.mp (litsQ wb)).2 k tag l rfl
        refine ⟨hNa N eN, ks, hR, hks, fun L mL s ⟨tag', l', negs', e', h⟩ => ?_⟩
        rw [List.mem_singleton] at mL; subst mL
        obtain ⟨-, e₂, e₃⟩ := tuple3_inj e'
        rw [← fieldsTerm_inj e₂] at h
        rcases h with h | ⟨N', mN', -⟩
        · exact names s h
        · rw [← list_inj e₃] at mN'; simp at mN'
      obtain ⟨T, Y, er, f, rY, Dm, mDm, hY⟩ := upd_dnf_kr ef hn hv sv vne keep (.tuple #[.integer k, tag, fieldsTerm l])
        fb _ hl (by simp) inB ok nr hneg
      rw [conv inB] at hY mDm
      refine ⟨_, ?_, Or.inr ⟨T, Y, er, f, rfl, ⟨w₀, (sem w₀).mpr h₀⟩, Dm, mDm, hY⟩⟩
      unfold Elixir.Module.Types.Descr.«map_update_static/5»
      simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
        Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      simpa [Term.list] using rY
    · refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        simp [getMapKeys_single, hb, Elixir.Module.Types.Descr.«map_leaf_empty?/1»,
          Elixir.Module.Types.Descr.«init_map_line_empty?/3», run, Lynx.Term.isMember, boolAtom]
      · cases h : denMF E den (.tuple #[.integer k, tag, fieldsTerm l]) w
        · rfl
        · obtain ⟨N', mN, -⟩ := init_sound ef.mopsE ef.mdopsE ef.msemZ ef.jopsU (m := n + 6) (by omega) rfl g sl
            (negs := []) (by simp) run w ((sem w).mp h)
          simp at mN
  · have wb : Bdd (MLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨lines, rl, hl, sl⟩ := dnf_neg_map (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl
      (m := n + 6) (by omega) wb
    have inB : ∀ w, denMF E den b w = Bool.true ↔ ∃ L ∈ lines, InMLine den L w := fun w => by
      rw [denMF_bdd wb]; exact sl w
    have hneg : ∀ N, neg = .map N → (∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s) ∧ ∃ ks : List String,
        Elixir.Module.Types.Descr.«map_keys_from_negated_set/2» (D (n + 6)) (.map N) b =
          .ok (Term.list (ks.map Term.atom)) ∧ (∀ s ∈ ks, mapLookup N (.atom s) = none) ∧
        ∀ L ∈ lines, ∀ s, LineNames L s → mapLookup N (.atom s) ≠ none ∨ s ∈ ks := by
      intro N eN
      obtain ⟨ks, hR, hks, litsQ⟩ := negInfo N eN
      obtain ⟨lines', rl', nl'⟩ := dnf_neg_names (den := den) ef.mopsE ef.mdopsE ef.msemZ ef.jopsU ef.jsemZ rfl
        (m := n + 6) (by omega) _ (litsQ wb)
      have e : lines' = lines := list_inj (Except.ok.inj (rl'.symm.trans rl))
      subst e
      exact ⟨hNa N eN, ks, hR, hks, nl'⟩
    cases lines with
    | nil =>
      refine ⟨.atom "badmap", ?_, Or.inl ⟨rfl, fun w => ?_⟩⟩
      · unfold Elixir.Module.Types.Descr.«map_update_static/5»
        rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
        · simp [getMapKeys_single, hb, rl, Term.list]
        · simp [getMapKeys_single, hb, rl, Term.list]
        · exact absurd ⟨_, _, _, rfl⟩ three
        · simp [getMapKeys_single, hb, rl, Term.list]
      · cases h : denMF E den b w
        · rfl
        · simpa using (inB w).mp h
    | cons L rest =>
      obtain ⟨T, Y, er, f, rY, Dm, mDm, hY⟩ := upd_dnf_kr ef hn hv sv vne keep b fb (L :: rest) hl (by simp) inB ok nr
        hneg
      rw [conv inB] at hY mDm
      obtain ⟨w₀, h₀⟩ := (hl L List.mem_cons_self).2
      refine ⟨_, ?_, Or.inr ⟨T, Y, er, f, rfl, ⟨w₀, (inB w₀).mpr ⟨L, List.mem_cons_self, h₀⟩⟩, Dm, mDm, hY⟩⟩
      unfold Elixir.Module.Types.Descr.«map_update_static/5»
      rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h', lit, c, u, d, rfl⟩
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY
      · exact absurd ⟨_, _, _, rfl⟩ three
      · simpa [getMapKeys_single, hb, rl, Term.list] using rY


end

section
variable {t : Term} {n : Nat}

/-- `map_update/5` for `:keep` and `:reject` of a static value at a static key type, asking for the old values, in
static types of the next level: `:badmap`, an error, or the maps `UpdSemKR` gives. -/
theorem kr_update {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {key : Term} {rk Ds : List String}
    {neg : Term} {m : Nat}
    (hk : Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D m) key =
      .ok (splitT (rk.map Term.atom) neg (Ds.map Term.atom)))
    (ok : SplitOk (rk.map Term.atom) neg (Ds.map Term.atom)) (nr : ∀ N, neg = .map N → rk = [])
    (hNa : ∀ N, neg = .map N → ∀ e ∈ mapEntries N, ∃ s, e.1 = .atom s)
    {v : Term} (hv : (level t n).E v) (vne : ∃ x, (level t n).den v x)
    (sv : v = .atom "term" ∨ ∃ Z, v = .map Z ∧ mapLookup Z (.atom "dynamic") = none) (keep : Bool)
    (hm : (level t n).K + 26 ≤ m) :
    ∃ r, Elixir.Module.Types.Descr.«map_update/5» (D m) (.map X) key v (modeT keep) (.atom "true") = .ok r ∧
      (r = .atom "badmap" ∨ (∃ er, r = .tuple #[.atom "error", er]) ∨
        ∃ T Y er, r = .tuple #[T, .map Y, er] ∧ MOnly t n X ∧ DE (level t n).E (.map Y) ∧
          (∀ q : PN t n, denD (.map Y) q → q.1.1 = "map") ∧
          ∃ Dm : List String, (∀ d, d ∈ Dm ↔ d ∈ Ds ∧ (keep = Bool.true ∨ KindHeld (MT t n X) d)) ∧
            ∀ w, MT t n Y w ↔ UpdSemKR (level t n).den (MT t n X) rk neg Dm v keep w) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  have sv' : v = .atom "term" ∨ ∃ Z, v = .map Z := sv.imp id fun ⟨Z, e, _⟩ => ⟨Z, e⟩
  have upd : Elixir.Module.Types.Descr.«map_update/5» (D (k + 6)) (.map X) key v (modeT keep) (.atom "true") =
      Elixir.Module.Types.Descr.«map_update_unchecked/4» (D (k + 6)) (.map X)
        (splitT (rk.map Term.atom) neg (Ds.map Term.atom)) (keepOp v keep) (.atom "true") := by
    unfold Elixir.Module.Types.Descr.«map_update/5»
    rcases sv with rfl | ⟨Z, rfl, sZ⟩
    · cases keep <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», hk,
        Lynx.Term.getMapKeys, modeT, keepOp]
    · cases keep <;> simp [Lynx.Term.isMember, Erlang.erlang.«is_boolean/1», Erlang.erlang.«=:=/2», hk,
        getMapKeys_single, sZ, modeT, keepOp]
  rw [upd]
  have sX := de_map hX
  rw [Elixir.Module.Types.Descr.«map_update_unchecked/4».eq_def]
  simp only [Erlang.maps.«take/2», sX.static]
  have bad : ∀ r, Lynx.Dispatcher.pure (D (k + 6))
      (.function false "Elixir.Module.Types.Descr" "-map_update_unchecked/4-fun-0-" 1 #[]) #[r] =
        Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1» r := fun r => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-map_update_unchecked/4-fun-0-/1».pure]
  cases hb : mapLookup X (.atom "map") with
  | none =>
    refine ⟨.atom "badmap", ?_, Or.inl rfl⟩
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso, bad,
      Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
  | some b =>
    have fb : MField (level t n).E b := fieldC_map (sX.fields "map" b hb)
    obtain ⟨dR, sR⟩ := rest_map hX
    have rE := next_empty dR (m := k + 6) (by omega)
    have mt : ∀ w, MT t n X w ↔ denMF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [MT, hb]
    have only : MOnly t n X ↔ (∀ v : PN t n, ¬denD (.map (rmM X)) v) ∧
        ∃ w, denMF (level t n).E (level t n).den b w = Bool.true := by
      constructor
      · rintro ⟨h₁, w, hw⟩
        exact ⟨fun v hv => ((sR v).mp hv).2 (h₁ v ((sR v).mp hv).1), w, (mt w).mp hw⟩
      · rintro ⟨h₁, w, hw⟩
        exact ⟨fun v hv => Classical.byContradiction fun ne => h₁ v ((sR v).mpr ⟨hv, ne⟩), w, (mt w).mpr hw⟩
    have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "map") = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
    have mo : Elixir.Module.Types.Descr.«map_only?/1» (D (k + 6)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmM X)) v))) := by
      simp only [Elixir.Module.Types.Descr.«map_only?/1», Erlang.maps.«remove/2», Lynx.Except.ok_bind, equalExact_eq_decide]
      exact rE
    have conv : (fun u => denMF (level t n).E (level t n).den b u = Bool.true) = MT t n X :=
      funext fun u => propext (mt u).symm
    by_cases restE : ∀ v : PN t n, ¬denD (.map (rmM X)) v
    · rw [bp_true.mpr restE] at mo
      obtain ⟨res, run, ⟨rfl, -⟩ | ⟨T, Y, er, f, rfl, ⟨w₀, hw₀⟩, Dm, mDm, hY⟩⟩ :=
        kr_update_static (level t n).ef (n := k) (by omega) hv sv' vne keep ok nr hNa hb fb
      · refine ⟨.atom "badmap", ?_, Or.inl rfl⟩
        simp [key, mo, run, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1»]
      rw [conv] at hY mDm
      have mOnly := only.mpr ⟨restE, w₀, hw₀⟩
      by_cases fe : f = .atom "false" ∨ f = .atom "nil"
      · refine ⟨.tuple #[.atom "error", er], ?_, Or.inr (Or.inl ⟨er, rfl⟩)⟩
        rcases fe with rfl | rfl <;> simp [key, mo, run, Lynx.Except.andAlso, Lynx.Term.isMember]
      · have fe' := not_or.mp fe
        have fm : Lynx.Term.isMember f [.atom "false", .atom "nil"] = .atom "false" := by
          simp [Lynx.Term.isMember, compareExact_eq_atom, fe'.1, fe'.2]
        rcases hY with ⟨rfl, emp⟩ | ⟨r, rfl, fr, sr⟩
        · refine ⟨_, ?_, Or.inr (Or.inr ⟨T, [], er, rfl, mOnly, Or.inr ⟨_, rfl, descrC_nil⟩, fun q hq => ?_, Dm, mDm,
            fun w => ?_⟩)⟩
          · simp [key, mo, run, Lynx.Except.andAlso, fm]
          · rw [denD_map] at hq
            simp [mapLookup, dn_none] at hq
          · simp only [MT, mapLookup, List.find?_nil, Option.map_none, reduceCtorEq, false_and, exists_false, false_iff, equalExact_eq_decide]
            exact emp w
        · refine ⟨_, ?_, Or.inr (Or.inr ⟨T, _, er, rfl, mOnly, Or.inr ⟨_, rfl, descrC_map fr⟩, fun q hq => ?_, Dm, mDm,
            fun w => ?_⟩)⟩
          · simp [key, mo, run, Lynx.Except.andAlso, fm]
          · rw [denD_map] at hq
            by_cases e : q.1.1 = "map"
            · exact e
            · simp [mapLookup, e, dn_none] at hq
          · rw [← sr]; simp [MT, mapLookup]
    · rw [bp_false.mpr restE] at mo
      refine ⟨.atom "badmap", ?_, Or.inl rfl⟩
      simp [key, mo, Lynx.Except.andAlso, bad, Elixir.Module.Types.Descr.«-map_update_unchecked/4-fun-0-/1», boolAtom]

end

end Elixir.STTDescrProofsTest.Nest
